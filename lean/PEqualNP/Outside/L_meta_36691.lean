import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36691.Model
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


end PEqualNP.Outside.L_meta_36691.Model

namespace PEqualNP.Outside.L_meta_36691
open PEqualNP.Outside.L_meta_36691.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36691

namespace PEqualNP.Outside.L_meta_36691
open PEqualNP.Outside.L_meta_36691.Model
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
end PEqualNP.Outside.L_meta_36691
namespace PEqualNP.Outside.L_meta_36691
open PEqualNP.Outside.L_meta_36691.Model
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
  | 2 => 0x7f01fff80fffe07fe07e0f83ff07fe07f44e73
  | 3 => 0x7ffe03fff01fff81ff800ffc1ff83ff818739c
  | 4 => 0x800003ffffe00001fffff0001fffc0001f83e0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x108100881024000028a1104220842a28194a5
  | 2 => 0x2aa529946a548ae8f0548aa35546b415544a52
  | 3 => 0x4c954aa528d91a2b75410ce919d23950586318
  | 4 => 0x68d9b3464c91d34db9e7a8421ee710619e83e0
  | 5 => 0x70e1c3878f1e1c71de79cf73908421861f7c00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36691
namespace PEqualNP.Outside.L_meta_36691
open PEqualNP.Outside.L_meta_36691.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x9478400003004e9180858b8a9b0074e0d00855032e6000b1201496347cc800a00887204c00e04897800029880500062b00516a33c8090000000004c00080001620006000000602000050004082ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31f731fe31fd31fc31f431ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x22000004e9c8008c0a80086600028c34560e1d4601e2b8007c47001dc003b3605c000021000da3c4b1747a08009f84c863d034944e281105c6729a6d267831801027b000003e383809c004c0b0bcc882159708c3139a685a341fa900074050a51245000011a003b0013c613e949285a4f84442390c0801c834e2543290098d86654421ac0c001d1e4447c11800009100134008f3780000092782cca281b84000a138874002500000fe6203944cc2a060c9305e028d5248e50050dc412016c1e4942890b0871600116024b800aa6840000001b3484932482f8111403259a8b2a2001986078200800384008484888f810302008002898780848100028083000000010000830a068180800585802601008208800700000388dd94743baa8e873e5390e7aa521cf546439f28487775150ee8a2a1cf94c43cf298873d5210e7aa221cf94043bb28e857551d0a7ca7a16d947429ea8e85b551d0a6aa3a14f943429eaa4853c5350b5ea4a14fd45429e282853e5410a7ea9994f153329f2a4653d548caeca3195d546329faa2653c544caeea2995d14532bda826578504ca7ca8194f550329f29e833d52d067ca1a0cf55241afa9a835c535073ea6a0cf14d41ce29a831c535067ea4a0edd45419e282833e541067ea998cf15331dba0e63b541cc76ea998ed15331db21e63b443cc76e8598ed50b319f2a4633d548c7388718dd946319faa2633c544c67ca818cf55031ce21863b7410c76a8218ed95031daaa06376530c7aca618f5d0c31db21863b4430c7a88618e510c31dba1063b5420c7ae6418f54c8319f2a6433d54c86bca790d754f21daa0e433e548867aa910cf951219eaa2433e540867aa810ed504219f29c813d529027aa3206dcc640da18c813e50902eca2205d544409f298813d521036ca2204f54440daa888135511036e62206d0c4409f28081ba501027ca9984f553309f2a4613d548c2eca3185d54630ea18c613f544c278a8985bd4930b62926177514c2e8a2984fd50309e2a061d4310c27ca9904f553209faa4413c548827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310daa0e213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b629221b5414427ca8084f55010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x4879c1a00d801b580138e201c62b7465a3576e598104a000a0081300462508000c8585081970024214ad60500132c000183e5578d004510038dd8833a3cba5541c043010c1820008086a7001008100540038dd855290e3561942439518d51d0a1c6354742a518d51d0b1763547428d18d51d0b1463547428518d51d0a3561141428d58454cca356195032c5d84535071453d45418b58854cc69663d5331a598c54cc6a562153318d99742cc61d6510c31a598e430c6976510c31a5594430c6956210c31a5980430c63565d0831a518d420c69464cc831a5191320c6d0604c831a518d41c871653507218d586544861c63551218e181544869463504218dd855290316530c6409518d511021c6354440a518d511031763544408d18d511031463544408518d511023765cc4408d59431102356195330c5950318c22d62150308d584540c314540c4308d58654c82356115220a518d41c421e63d52108d19541442946350510c514d41443245250510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x40000290013a4c01880000000020a39ac228285419cb6114d4190ae5b288618c1473586544860b39ec2a9481415c8540c430828e6b0ca99041473584548820a3b0a6a0a218118c5250510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (912+((h/16+packedAt s2K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s2K4 (4895+((h/55+packedAt s2K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s2K3 (2420+((h/20+packedAt s2K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s2K2 (505+((h/3+packedAt s2K2 (490+(h % 3)*5) 5) % 19)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 1 => 0xfc07ffe03ffe07fe0fc0f81ffc3ff01d8ce7c
  | 3 => 0xffffffffc0fffffff000ffffffc1fffe0ff8f
  | 4 => 0xf0007ffffff0007ffffff001ffffe001ff0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2045088c48824408052c9292500529540b50b5
  | 1 => 0x6493391439248cb9605585b0b6435a0cd8c65c
  | 3 => 0x890a522090691852aa0209652aa814a960ab0a
  | 4 => 0xcc2c64492241d164d39b2041cd328031b50de0
  | 5 => 0xe307871c38e1e7f1ce3ce780e2318c1fef000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00eeaaaa00ee88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36691
namespace PEqualNP.Outside.L_meta_36691
open PEqualNP.Outside.L_meta_36691.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c3eca3185d94630bea8c61f5518c2eaa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ee62887d0c510fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f7cca31ee994637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831bea9063df320c7ba6418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fb20e43f541c87ee6390fd0c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087ec8210fd50421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x9c42b9af1684880008b27e790c68000001d00010500000000000326000000000000000017400084c0015b0000010b8011d8000001f900013d4580034e02c000000000004020d2e2000000000000012784b000000000a925a3291f9a2000000000003420c0000002520002209c282000cc24a000000000000000000000000000000000488000000000003c0d014a0005e8000004d08712a8000000000012a000570f4229306000fea1a33ea04ed9ba0000000027849c09c000004bc0009817d000000eb925404000b20000000003314317000124800000000b08563ac000dca513328948a88e4c2000000830005dc00033466000000980009c90b000144594320001b6038000002a61e4879f61aa0006c1fc0009e4000004d24283d8002a83bc710005180003a80014800000000000000a38004d8380300002680c4621e621c0007d8001341c02609347ca51440002d0054a885000000106000000940f90860180000022f0008c5400000001b53397b0002c80023413e7c0001a61d60003d0730000109900024e880209b33dc4f8668000000001115d03c6d4c88fa1a4000fb800000a080003c4b4220000000002bc0013c112000000004b66c46f0002c066c000000744e89b80027a00000000000000858000009ed398ea0000001216749a6a43e000000000db000000000000000006dc030000ba6544c80021a19c08800000228d20083ce28c2002f06407ca91ef0020080080400000a0040001600000404005000014028070040000080b0040180000500200c000030160340001100602800004002014000000020000000100e0500000000200002802000000010040140100081500001c018050040000080300a0040500000000000004004008028020000040100000400801804006000088030020000080300000000000010008030010100100000200402000000002000000010000040100b0000080080200a00c0000000a0000000200a000000100100140080200c00000000000008000090000380680003800806001004008000020080200000101200800807000000028070060040080201201c0000900200403000000000008040020080200101e0040180000800c0580000000002802000010000010000000080900e0080180000600c01003bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e85f651d0aeca3a15f54742faa8e857551d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857
  | 3 => 0x35000000000000cd11240a000d68d33a29d8001104ba0d00d80024c3f0860000006254503b0005e0000000000000000052473000185000000000d1000000500cc00070cc580031e000b100009a000bf87652a90c810003d28881f9962be0009c0d9000015238d6276770f58253a41c4899243281a00000003200000000000768000ff0000000000000092cba91f0dc8646f988172254f60dc00000000000000000001e00000011c85f0007188b8e324610cf180017c5680016d000001428000ee00000000162000000000004640000018a6fcb582c07c000001ed0aa0007880048029c001d53003f94680038a53c0000019600147000000210000003e62a0b180000000901a831863742502a18ea18ea00000072000000038000000003e20000000000077c001c20006a000000436000d5810000000f12081808dc648070004441317e040308819a341e5c8de885000000001d92ac0000000034a000000004da11cb50000003680016919c5f02d0f23f09ac908d72008f4e3a6509065c3f05b46a000988f40006c8b327006aa1009a124580b4cf0004742d8e518708c89d168003b00005aa15000000001ac0d2450a30000000001c8ac000001108e10004a14b0e64cc9e8481730a60000a2570006d0599440000003fa0700064800000000578000ab23a838a800037c000002300000008e14d4a86a9378030000012b0000a894c002932aa4e4ce0004b04d93000001e6c00000025e0003e8e431c7411702110e41c7a9b84700745e9181f22045e19d422000fd1de2922e8c505c44c3e0768491ca8910a1d30005152311b2b205d35023000a1c00000234000001e12b02a84e9082800d8a4242498294e00000a40008486100000099a774903cc170004c8000228090001b0b79f51040e05300000025c001820001440009b402000c61c90009f94ba36208734002630c66b8001dd1a00010594b2988ac1422a2dc000a700025c5e5142003fe000001f44460000021d1902fc960a1000000001900d45c04a00043e068461573f64ad3a8004a44040009e376000c226e000964000000000002f000000000e588f464000b60000004780003d4c49f0090c119e000e22062ec4587ba4115a1614827406e7a8738bb0ca3d8f2a1815c2c14882b30c0003900a11a00102000122000000001dc0006323c000000271c137882800000000a3d3e8e80b2188a106b16e73837a5f12c0000b000000000830e926a000000783fc8252e000420878001cf0006040c0290000007e920000000000000849fd44a3b0009144900d00
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x153c82776154f209d18553c823e6414f208f59053c823e64947208f59251c825e63952209758e548827661152209d584548823e64d4e208f593538827661d4e209d587538823e6494e208f592538823f64546208f191518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d209ed81534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d614f204836451881209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c755153083586054c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083655188420d654f3008279650c0209bd9520082e461480209ed9520082d863480209798c54c425d63153108fd9153c423c6454f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b10b518d41c42b5640c710ad59221c425e63d52109758f548423e64d4e108f593538423e6494e108f592538423f6454a108f191528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d10d5587534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452443345490510d914a41442746550510b518d414436452505109d997314433454cc510d914b31442b5640c510cd1503144357530c510d914831442766588510ad592214436452885109d19521443645248510d914a104423d65950108f990540427661150108f993530423d64d4c109d987530423e6414c108f590530426e6214c109b588530423e64d48108f593520423e64148108f590520425e63148109758c520427661148109d597210433554c84109d59421043355408410cd553100427965840109dd9510043355444010b9189100427b6544010
  | 1 => 0x63f6550441a718d41106776550441b518d411066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc67a60152319e580548c63e6494a318f592528c69c644ca31b6181328c63f64542318f191508c63e649513197d8d544c67761551318f994544c73454cc531c7152314c63d6595031c718d540c73461550318f990540c71d54d0c3197594430c71d54cc831a7191320c71d544c831b5d85320c6d8604c831cd553410c79743d04319d594410c794431043197d95310c69c644c4319dd95310c6b4644c4319798f54c865d63d5321cd58654c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c87576154f218f99053c863d6414f21cd95241c86d46350721cd95331c86b5640c721cd95031c8755530c7218f993538863d64d4e219e983538867960d4e218f990538863d6414e21cd5532188675619512197d8d544865c63551219ed81544867860551218fd91534863c6454d219dd85534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520863e64944218f59251086756590421b518d4108675650c421ad59031086e5620c421ad592210866f65484219dd95210863f64540218f191500865f63540219718d50086776154f409d18553d03576154f40d518553d031d5390f40c754c43d031d53d0b40ad58742d031d5350b40c754f41d029c6350740c754d41d02b46150e409dd8552902746154a40a758c429029d63d02408f994435025e63149409758c525023e65d0940ad587425023e65d0540a718d415023f6550c40ad185431023d6590840a758c421025f63544409718d51103576354440d518d51103374354440cd50d51103364254440cd109511023d6590440cd54641103355110440a758f401033551d00408fd95401033551500409ed95401031d54ccb30c755132cc2d8604cb309d987548c27561d5230c758e548c27661152309d584548c31e5490e30b5185438c29d640ca30cd952518c3355494630cd951518c3355454630c7952318c29d640c630c7950318c355510c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d641493097997324c2d8604c9308f990514c23d64145309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2d46150c308fd91520c23c64548309dd85520c274615483097596320c29d640c8308fd91510c23c6454430a7590310c2d9600c4308f992500c23d6494030a7593300c25f654c0309ed95300c27661953209d58654c825e63153209758c54c823f6454f208f19
  | 2 => 0x6354550a81062924c8349e3328708549be0000001d0003ae5f82116a410000f411c3527bc000dc1ba434e30130001d8a09b731e8640013c380068d280012846c5b9ec3c8120f800000000000000012000000000b8000001b42204306d02b15613c00000000000f69560f80006996319a574ce0002726c44b1430005907099712082ccf80022811cf880824873cef0af364300af9273a885c7d80025040c000c826c4640000027c1d41a0362b8764448ef4283a8ca8173920ec001351302200020e3b80805f8a2096500130d61ce1c0002180b25482b9790a20000004d0004c43588518c4b800040138784000000de000001b800000016800000000031370665106b9a72d65c0fe17700a17c00a0a23e2808711e3343a45200034c3a0fc1a830a08c090980c0140100003014020780400800018000600403c1101c0300002004010440103000014010180f0040900004030010640d0081c058010480a004150140d01c09040091081002c03000020240103400000040280a01c0304c00000190540c0200f0080001803000010100000804000230000204c01028140141c00c0400000008080400505c010043b0040202415008030240101c1301c030140401c2400400028220901f070030180c004030000f0040200403000000080303c080e0000000904c010d8000300c0000102404034000180b000020000103c1000000026776154a439d1855290e7661942439d5865090f574314543cd90c5150e3f6550c43ad1854310e5f6550c43b51854310eb46150f4297d8d51d0a5c6354742d5d8d51d0b546354742cdd0d51d0b354354742ad5874290a5f63542429718d5090a3e65d0d42ad1854350a7661141429d5845050a776154c429d1855310b576154c42d51855310a3d6590c42c754e4310b1d5310c42c754f4210ab561d08428fd954210b1d53508429bd954210a7661153329d58454ccad46150f328fd9151cca3c64547328f99250cca3d64943329d98650cca7561943329d987548ca7561d52328f992518ca3d64946328fd91508ca3c64542328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132c758c544cb1c5490d3297195434cad46150d32cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb705114132d690c504cb594314132d68c8504ca3d65950328f990540ca5e6315032c7553320ca5f654c832c7551320cad8604c8329bd95320cab46150f41a758c42d065e6394a419758e52906b561d0a4197d8d509065c63542418f997435071c53d0d41c714d43506b46150d41c714e425063e6510941a758c425071c5310941d514f415071c53905418f59643106b561d08418fd95421
  | 3 => 0x418003745c8e89961700a40000e04e0b8b9800050000618003822d02e8f03c4390700e5024000308b1366000000f624a4fcb69903d25340015b25e000001a3000598e901b420000581fe0206f4ac94b1327285e9160000581782c0722188d1800420007b8e312e308659780aa868409d636c6908e98d2944d06c0a335e808050370ca000bd0bb0b6568b499840071c961602663b8908c70fe80c00030314000671b900064c399c40882b42f00d42a030f00c11cc350dd92a28e7d8a9a070b0044ba9bf1b63e49d8fc0d07ccf318e198730f59d341a70c1c1302aa624811173ce720468ac360294011cb28a1582298621e5a0c6192240414d01dd0005bcf90671a4760808820f2054fa91233c000da9380003d4000ed1be608840d019400000000000000fc80003a284a1000000104be9c52261b00000024c21c300031784f49d0220e43c4531f4000188c0a1119e3fcbd8b90002780f1461d6128f28840a07b84712d12648c761d5230050541fb4021184d8b33d45b03303d0e2000000c4046544e814f09c2743d15e122734bb1ad3424880019106a314d71113fe2e81520408606000148000148d110a000410ac17f0002480001c0dc7e8b3a0920e1307f0d500e674368f31540f831800000424fe9882562b8de00b01e4003c01922a0c4121da0b41d0ab88a0fa000248d11003f4b714e2e25d08598b42c66c1e03f4183d07d0000a6818c38002ca268a620f3066b0648f23560006f0a704a07c000003ee5880205412a1f871000426190458f813e5f10906a0000c83b8d9000000ed99940a00000000000000000be11823cb092916a000e70b20f6610ef8b
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8c18a0c000000d1c04c144f0002d411500800524000e5d800049058102082486003451c55310c42c2aa6b0e84215147158c544caa838a862826586550604c832928e6b0e8420e1463185540c60e3b2a89906386550604c831a28e6b0ca990c357695031c868a38aa621e818554d61d0b40a2ae6212a22051473544411030ab1aa3a008186550604cb30a28e2b1ca91841d76950318c28a39ac22a2219118c525051086aec2a06288625641483144312b20a510a21895506244010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x201908148754d61d08428148754d61d0b40814865cc42544408148758d51d0040
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | 2 => packedAt s3K2 (i*60) 60
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20359+((h/221+packedAt s3K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xff80fff80fff83fe0fc0ffe0ffc3fe0363ce7c
  | 2 => 0xfffffffff03ffffff000fffffffc1fff83ff8f
  | 4 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 5 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x290a22312209208052c92909280532a82e10b5
  | 1 => 0x43266450e492259605585b285a43541962c65c
  | 2 => 0x8414888241a4422aa020945294a80952816b0a
  | 4 => 0x1658d12489074b4d39b20610e7328063d40de0
  | 5 => 0x1860e1c70e3873f1ce3ce79c06231183fbb000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0e8e8a0a0eaeae0e0e8e8a0a0eaeae0e0e8e8a0a0eaeae0e0e8e8a0a0eaeae0e0e8e8a0a0eaeae0e0e8e8a0a0eaeae0e0e8e8a0a0eaeae0e0e8e8a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36691
namespace PEqualNP.Outside.L_meta_36691
open PEqualNP.Outside.L_meta_36691.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb304024a144000a700c02004bf43bd43be42bc42be41bc41f721f421bf40bd40f710f510
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x60040109a28a871d5310a3aa7a05914910
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
  | 4 => packedAt s4K4 (208+((h/4+packedAt s4K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 1 => 0xf81ffe03f03f07fc3e07ff07fc3e0781b3cecc
  | 2 => 0xfffffffc003fffffc007ffffffc007ffc3ff0f
  | 3 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x90444448820841008a494848805294a4161055
  | 1 => 0x32cc8c3926524b2c16c2d943a434350cb2c6cc
  | 2 => 0x4191109068a484554104a2954a804259416b0a
  | 3 => 0x651a21224c06969a6590308673296011e80da0
  | 5 => 0x861c39c38f38e7e3b9e73ce062318461ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36691
namespace PEqualNP.Outside.L_meta_36691
open PEqualNP.Outside.L_meta_36691.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x2044600008c022287028650000210000b022478b80027c0001e75000000000000000094e00599361c184520000010012a42a000004c00000000000000007131468c0000006800000280020400000040c000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe81bd43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740df20e81bc41d02faa9205f94e40bea9c817e52902faa5205f94640fb28c817651902faa3207d54640baa8c81be419037883205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940dfa1281bd42502fea2a05f14540df20a81bc41503f680a06f90140bf2a0817e53102faa6205f94840bea90817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc2fca5985f54b30ef99661dd32cc2fca3985f54730df20e61bc41cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3186f90630de20c61de318c3b863185f94230ef98461fb308c2fea8985f95130beaa2617c544c2fea4985f14930ef99261dd324c2fea2985f14530df20a61bc414c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861be410c3788218778c430ee188617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83dc65907b4cb20bf28e417d51c837c83906f10720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106f90620de20c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc64907b4c920bfa8a417c514837c82906f10520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841be410837882107b88420f6108417e50083de40107e88020f690041f920082fea9885f95310beaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c43ee83886f90710de20e21f441c436883887d8c710fa98e21f621c43ea43885fd5210bf2a421be548427ca9085f55210deaa4213d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf294217d52842f8a5085f54610df20c21bc41842fca1087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53443bea68857d4d10bf29a217d53442f8a6887714d10ae29a217f52443dea4885bd4910bf292217d52442f8a4887b14910b629221f7414437c82886f10510fa20a21b441443ec62887d4c510fb10a21f521443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821be410437882085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf54ccafca9995f55332be2a665de43ccbba87995f94732bea8e657e50ccafaa1995fd5232bf2a4657d548caf8a9195f54e32bf29465ee428cbda851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265de434cbba86997b90932f6a1265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32bf29065df320cbdc6419774c832f699065cd320cafca2195f54432bf280657d500cafca7a0df54f41bf296837d52d06fca1a0df54341beaa4837e53906faa720efd0e41df21c83bd43907788720df94a41bea9483bf429077c8520ef50a41de214837e519077e8320fdd0641bf284837d509077ea720ef94e41dea9c83bc539077ea520ef94a41dea9483bc529077e6520ef8ca41de99483bc329067ca320efd4241df28483bd5090778a120dfd4d41be29a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef90c41dea1883bc43106fca420df54841dfa1083be421077a8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020efd4c41df29883bd5310778a620efd4841df29083bd5210778a420efcc841df19083bd32107786420ef944419f28883b6511077ea020ef94041dea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598fb94b31b7296637d52cc7daa598db54b31fba0e63be41cc7788398fd10731da20e637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31bf294637d528c7be6518f74ca31bf28c63be418c7788318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898dfd4931be29263be414c7788298fdcc531ef18a637f504c6f8a098dfd5031bf2a0637d540c6f8a818df94c31bf290637d520c7be6418f74c831bf28863f7410c77c8218ef10431fa20863b4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fba0e43be41c87788390fd10721da20e437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21f719443ed32886fca310ef90621de20c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43be41487788290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821f719043ed32086fca210fdd0421df20843bc41087e88210ed10421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40dfa1
  | 2 => 0x40000000000150a011e80012e1707e000000679361a4000aac000000000000006209e00137000000000000750009d91f96c0000000000011c0ac001650001983d0322d000120a7429c98d2d0000000012d9c70006888584d0003d042a2420600034a2c1020d4001fe00011400000000000001c9000000001163b01cc00000000550e7a94000000d000000000000000000000000942dc835181c00a82540019d0000013009107637d5321b1860002d8000000001c1e1000000001b403e128d387e000184a10002f64155203319e3b0000000005340021100019c000003080004f10a0001541e88400081c36a3b4524200000010092c0028d1900007b9574f20006f000560910b20002861ac768000000009280013600000000420a7c0000042a0011029c41c72c2980000039400159492000af0370741bc0008b3e098800051000000000002609cc000f800034444807114a38dc2543cc5b4751603a80112b1503a69c5231350a41395191a174a74001d25546682480000000000189000105508d9000914000000000000000000300000c02800000008000020000040580500400801813002008068000040000880100e000008140000000000600000804000004010050010000080380300000002000008020018120020000300100400000003000000040000000000180200000400800000000000000060000000000c0000280000c0000101a01400400803010004078000100100100000000001002004008040060040140100000200c0100000400003805002010010010220140100100600000006000004000000000000080300000001004008004000000000000000400c000000010000000580600200002807000000000010040000000e000000000000060180000500000c01806002000008010000000000d0060000180202e04000000000000008040040000000900000800800004000000000020040080100401800000000014070010017e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150feea2a1ddd4543be28a87f45150ee8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843f7290876e5210efaa421fb54843b6a90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7a86a17bd0942df212857f5150beea2a15dd4542be28a85f45150ae8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857
  | 3 => 0x2c800000000001440001c00025128088c0015b4f400126048366575529782e000000000000000001e4000894370ef000000000001c2448e08002d60000000010e4812f80022a00000000000960001340002400011e1560d0e2a5943e4cd2e00000047c000003c6995200000004dc118000008b8002040000000000049482c000000006700000006c000000400005889d8d0306621142a73f4001548a600000000000000000000000005e55b0000007e486000434000000ee000000000000004bc000000000189500004c000000002928087105827800d51000464a480000036e000000000000007580018e000000004320000015200000000000000a30001be4fea44ebab8468a60000fd00000000000000aa1420000000009d00f0005280000003284c0003f000768c99c4000ae8000000004e1178280008740029b3fa01543a6d3de6fc3da904062d4049612727b00000018c3e40027c0008893a9d526c51c01000000598db1c605403800000000284000005681f4d49413dc48cbb8003246f400039000adc000860000000024f3749f49faae4d6000868000006ec0000012444400242256984002b3000000000000000000000013489846297328758c0000000000ba80045a2b0c30001046f1479e80ba0011a87748e0000000024844c6a800322001060004de000000000006080025d3ec000c38000262b88700046ea0d1e0004a000000000000000000000000000000000000000000000000000000c60000011d4ae0010400047000000000040000000a214a35c0000008846c000001f64712198d3b62f4721ce000604dc9d1000ac8e80002ec060000560000005d93e526000000bc3b2000cc8005405593f270428871409f50009c8789b10007b42f0830007880018e000000ff81600000008000000000000001a60000019b00087915800354000a2800000000000000184a0660004f63342f9000002906e2553640000009600029c0000014638cbe98c430ac40e84211e10c7b27735c338c500020c050002b54660012f10f0a08a9450743941c4f8800016000000000000007d1af16c5fcf4a88000000fd8002021e0c58000000000f0c0000000e60680100c093951000361030d22520005f29e220a187387f00000054a0a17e00000000182190000b11fe001078c21d0000000000000000021602a3a45b8760f20940e0c92129a8bf09c000044651ad0000684680044294d4d000052934989180d8260ef00000000000000000824168cb1683981e14b3be0000000002e0011d18f00006c0013200000000000000000930004d02cc000000004b4f90001b445c000000003c8350003ba7cd410a004e0014a800000000000000000003000020e000000aa46c00000000000000000005325a95c9981ea520f58b840a2c80000032a000000f
  | 4 => 0x2641a8000f384c3e870d56000000000001530020014284b42e7949719f2086840014c0000000015c2ce000178000002bc00000024000f50000008f8aa8b00000000002e00068cc800008e0340000000057c000000000001880028c000ba28b2e4000d5a52402000a7a670000008c8b9048000000000b4000000000007085699630a000d3000000000000000004f50917c1b6000d612c01465c4f82c1fc5cc6b24e1c0084441fc4d2a2557a96000000d41f7242780000930ae00000122000000ac0000000011c800000000ee0001ba000b18720f8000002270000000017a3f00013c0f336a6c0ad00039a9984c8002285c4001022d20015689d34a088621c808c0f8002480005bc6280046219400
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f590534826c654c920d314d32482e8604c9208f993514823d64d4520cdd44414833451105209798f540825d63d50209d987540827561d50208f596540823e61950208f185540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d58453083365494420cd55251083565394420d554e51083376494420cd192510823f64544208f19151083365454420cd55151083565354420d554d51083376454420cd191510823f65904208f596410831e5390420c754e41083365190420cd546410823f65104208f594410831e5310420c754c41083365110420cd544410834d5388420d9546210834d5308420e910421082e96008420d354f200826f6548020d354d200827b65480208f99253c423d6494f109b98a53c426d6294f108f99252c423d6494b109798e52c425d6394b10cd99441c43356510710cd94c41c43345310710cd94841c43345210710ec98041c43b16010710ad19131c42b464487108f993538423d64d4e108f990538423d6414e109b988538426d6214e108f993528423d64d4a108f990528423d6414a109798c528425d6314a10cd953108433561d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f984544423c6115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524436561149109d997414435453d0510d914b41442f260d05108f996414431f5390510c714e414432f5290510cb14a41442b661905108f994414431f5310510c714c414432f5210510cb14841443375410510d514c41443645210510ad99441443366510510e5d4c41443365310510cd14c41443945310510c514c41443a75210510cd94841443345210510e914841443245210510d514e3144274654c510ad191314436452885109d19521442b46448510ec10710442b664841109d987540425e63150109758c540426e62150109b588540423e6414c108f590530426e6214c109b58853042766114c108f990520423d64148109798c520425d63148109d984520433651104108f992500423d64940109e596100427765440109ed9510043b24144010
  | 1 => 0xc7356510431e598c410c7956310431cd94c410c7365210431e5cc8410c7953210431b358b310c79441cc43197d95310c677654c431ad191310c73441540319798f54c865d63d5321cdd8554c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c875653d0721c794e41c871d5390721c794c41c871d5310721cd55041c87565310721ad59441c87356510721cd94c41c87965310721c594c41c87955310721cd14c41c873441543218f992538863d6494e21d394d32886cd63c86218f992508863d64942218f992544867761551218f994544863e6494d218f592534866d6294d218fd91534863c6454d219ed8153486786054d218f996414863e6510521cd153214865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520866d658c821d314d32086b661904219d59441087366510421cd59441087365310421cd14c41087a66210421e958841087365210421e98c841087a53210421b358f21087a441c84219bd9521086776548421ad19121087344154021ad18543d02b46150b40cd94441d03376494640cd94641903355110640cd947409026e6214d409b588535031c5350d40ad185435025e63149409758c525032c5250940ad18542503345190540ae98241502b66190140cd94441103355110440ae580411023f65500409ed95401027761553309d18554cc26e62153309b58854cc23f64547308f19151cc27661d52309d587548c23f64546308f191518c26f62546309b189518c3365110630cd544418c394410c6309bd89544c26c62551309dd85544c27461551308f990524c23d6414930d3149324c2d8604c9308f993514c23d64d4530cdd44414c33451105309b98b540c26d62d50309d987540c27561d50308f596540c23e61950308f185540c23e64150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c3655294430cdd92510c33464944308fd91510c23c6454430cd951510c3355454430d9949510c3655254430cdd91510c33464544308fd96410c23d6590430cb94a410c32d5290430cd946410c33551904308fd94410c23d6510430cb948410c32d5210430cd944410c3355110430d354a310c355518c430d3548310c394410c430b6580310c34d52cc03097d95300c34d524c0309ed95300c27761553209d18554c825e63153209758c54c823e6414f208f59053c834c534cb208fd9151c823c64547209d987548827561d52208f990538823d6414e209d98453882756114e208fd91518823c645462097d8d518825c6354620cd94441883355110620e9104218825f63551209718
  | 2 => 0x10140001801018000300300800020110140600c030240501403000050340202804004030300801000000000000c0000004002030040180000003000030000500c00008040140900001008000140500400008090000400800014000080102809000039d98650d0e756194343cdd905150f3643145438fd954310eb46150c4397d954310f2f4354843d390d5210f2d4354843d350d5210eb46150f429d98650d0a756194342ad1854350b376414542cdd0c5150b354314542cd9085150b1d53d0842d354e4210a3f6550842c754d4210ab461508429bd954210b4d53508429d98754cca7561d5332b518543cca3f64547328f19151cca7661d52329d587548cae46150a328fd91518ca3c64546329dd85544ca7461551329ed81544ca78605513297195434cacc6250d32b5185434ca6c6550932b318d424cb8d4350932b9185424ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca3d65950328f986540ca7761550329d185540cab46155032cdd85540ca3c6155032cd185540ca3461550328f990540ca5e63150329b988540cb1d54cc832cb552320cacd638c83297d95320cb1d544c8329bd95320cb2d544c832b3d95320cb4f654c832d3d51320cb8e544c832d3551320cb8d544c832c3551320cb4d32944328fd91510ca3c6454432d34c9500ca6e6294e419b58a539071e5350e41ab98843906ad6210e419798e529065d6394a41cb949429069e6310a41a758c42906b661d4e41c7d4e53906ae6294e41ab58a53906b66114e41ad987529069e6394a41a758e529072f5294a41ad984529063e650ca418f594329078d320ca41ced4250906b561d0c41add85431071d5310c41ab98843106ad6210c41ad58742106b76150841a798c421069d6310841cb548421063f65504419dd9541106b661d4c41c754c53106ae6214c41ab58853106b66114c41ae98053106b96014c41ad987521069e6314841a758c521072d5214841ad98452106ba6014841ae58052106b661cc841ad58732106b6618c841ad58632106b7614c841ad185321063e650c8418f594321078d320c841cd98651106b66394441ad98a51106b56094441a798c501069d6314041ab98850106ad6214041ce540501066e62d53319b58b54cc73761553319b98854cc66d6215331cb95252cc72d5494b31cb95152cc72d5454b31d994b41cc72e5290731cb54a41cc72e5210731cb54841cc7355410731d994841cc6b56510731cd59441cc7365210731e994841cc7265210731e954841cc73441543318f992528c63d6494a31d3949328c6cd62cc6318f992508c63d64942318f992544c67761551318f994544c63e65905318f994414c73454cc5319b988540c66d62150319e980540c67960150318f992530c63d6494c31ad986410c6756510431cd994410
  | 3 => 0x12f8000fe4d80019d4c2668ac92e0003005180021a0002d800404924708000d0208001424b04684e8002f2000b400016487c000ce2b0001170b800034c0006d23e3c04d0003d2958b908a3fe0002e9b733c0000005000001800000000000469c047807ccc8002f60c80001c0005551988f0002c00020704c7cc000001ba000e2a3622c2d01f24f3de8fc001d3000001290004d0001332211fe39c760522906140417041a8412f1434161a91a1df1ee3086900037a5c43da6c0004512d1b406a0002580025a3400000000000014800112000db00021e4700024e3943d81d14f122478861d40009046a2530003290995f3c43a5018cc000001129d800e0ac0003b3020000000d000000000001a2000898002fc0000020c0000000000035e768000c534e640288004747312e07a00000000000000738001a61500004c8001bc0b83c10900067d110b60424740001840a2f8001c6008418322184e0000060000009751419c1f600000000000240548a540c8909f8000000f42ca2601c000000003180000e8f51c0934af0123464e0000003ea0000027143405493000000000638bf0ae280050000b46c871875000000cd93e000858f39b923609c048111b88ac0017c000000000001584a03a0002d60006a800000000000000000012a8000504601b952000870000000000010201605a1acb79c82a21787e03c2945d40c96500000000000000204a60cd000000011193543652223b3b20780016e000964fe17d0000000016d276000c180015456c2a153496749231a444e82489111472900000c83ec30cef23046e000b08313041c8871d62569302698b22e9bc5e9300ce000840951308f8d42503e0128710a13920000000043604000000000000001ad000848732320d8000d01cd0de6f8000714da0000006131013c1200024a00000001324000000871b6000000001e6000d70b34d43b86d1a54c0740102571485751c03430c000768002b47f8001b12880000026700011c001d10aa48c0017f3220000010119e4c87d0002546e8000002168b481a43000238851cb3c6480c487c02855cfc1e43847c8000690004e41f92c000000f00000002b5178000003e0000000008c44b1984944e80014509c804000a2000000001e1440601328ba43c000c20000000000023d1e2158f58304d21240000022075c000003dc000001663821cc6315c2ce0482800403000000000000005004020400600003008010180200c0000000004000000100001008010000d040000000500807044050080001c160000500c030080201000010000000101800000010000502001000000340200406000030400000001010000000000c000080400007000060000000c0200c050281a0440203405000010080000806008030000000804000000180100c0103003000070040000403020
  | 4 => 0x4228d4f882c1de6345a9ec086524001f40000cc2f870082198fb80000000000000000000001bc1247e4000053fa2b86596212865cdc0eb0722e4df8762689b857a2a3443912114e18809460a0e000000150fd00000093a1700000042000000220ab2000005347517836a1084d8e81ae298300001ac7992a0401180680005841e0007a0bc0004a4c78450001f8b0000156000fda630000004193d116000000000f20e12d9cf036000b526432c4147c800000000000a738e1dccaa1d000000001d510a0bc6c15400627c821c30001190a0000007749a8000000000000045205c11941446200002152785ccc500026e6ec000441ca3c8588970005b0c985c000400ed9690000010c89e0c6590ee1153d04bd050002e803c3e800026650a31fa0008200000048e120001e54c437c00177000920920000449447f16331c7b45b8001260003109c0006a4a397a000000431763d44c4d090230e4880000b0000002600020e2ec1b1ac2420000014b266540370002806ad358000006c1228531926cce20650008b
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xe94930217121d990000000000128011000d80000b24a022941f9604199c80019ea38e00209b8f8b80089d15000a80000000078c0d000025240589000300071f219396839a80159b181e21001a0a09a20ca317881c000502860f00000010848100188000000010118000800687810000083000c000000c00010000130c00604020805247150d5210f0aa98c2a1085611c54350932d0a8630a849951471553320ca9238aa919065451c5544c832a48e2aa2641950d75951320caa238aa899065611c5544c832e0ee2aa2641950c71551320cb8238aa899065411c5544c832a1ae529a8720d0d73949429068b38ea729c8383d4d6294e41c1ac7a94a520d2671d4a529070732a64194838354d6210c41c1ac6a908420e0d53588531070ca9ac0298838358d5214841c52a4b00a420e0d654c83210653394c728883259ce6294441c32c6a80a020e29625405010686ba4a499463a158841cc431a1ae929a6510d0d7414d32086a4b80a6990430d5d85310421a62e02988210d16739484108692bac6420843c114d3210421d0ac620e4210d0d7214d435030a298c2a1a81435cc5250940c48a430a84a052472544418c21a38ac829261435d0524c930a2aea208621870552104310c324a92c018861a4105600c430868e2b20a79050d7414d32c828a39aa220c410d1c56414d20a1ae829a6490525751042108382a9882108419254d6008420d4082b0042105267294c41c428b39ca420e21451d16114d10a48e8b08a4885167394c4144293394a620a21c114f5210510a2ce72908288526729484144383a98a420a21c114c5210510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xe448c000218b500c2094012800a0681d4d6294e41c05639c75294a41a058614d3210421b018014d3210421a058214c6150d40a05831486150940904815d0524c930a1185105600c430e0152105600c430904815d0534cb20904815d0534c920a21851056008420e01531056008420
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 6 => packedAt s5K6 (770+((h/14+packedAt s5K6 (672+(h % 14)*7) 7) % 80)*7) 7
  | 5 => packedAt s5K5 (21436+((h/233+packedAt s5K5 (18873+(h % 233)*11) 11) % 1226)*11) 11
  | 4 => packedAt s5K4 (25868+((h/208+packedAt s5K4 (23788+(h % 208)*10) 10) % 909)*11) 11
  | 3 => packedAt s5K3 (3850+((h/25+packedAt s5K3 (3675+(h % 25)*7) 7) % 110)*8) 8
  | 2 => packedAt s5K2 (800+((h/4+packedAt s5K2 (780+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81fffe0fffffff03fe1ff0ffe1fffffa31f1ff
  | 1 => 0xfe07fff01f87e1fc3fe1ff0ffe1c0e05ce7ecc
  | 2 => 0xfff83fffe007ffffc001fff1ffe00ffe0f8f0f
  | 3 => 0x3ffffff801fffffe0001fffff007f00ff0
  | 4 => 0xffffc000000001fffffffffe00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa4100222440100008a0250122025229010b055
  | 1 => 0xcb18461c90a422c1620b104e2086430c656cc
  | 2 => 0x1062a8848354915541112aa1554089660b0b0a
  | 3 => 0x594531091240d59a655408819992c047600da0
  | 4 => 0x618621ce1c6719e3b999ccc811030187bde000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0eee8eaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36691
namespace PEqualNP.Outside.L_meta_36691
open PEqualNP.Outside.L_meta_36691.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c18001ffd5007fe5401ff55007fc54017fd4c057f53017f94c05fd53015f54c05fc53017fd0c05fe43017f50c05fc4301ffd4803fe5201ff54803fc52007fd0803fe42007f50803fc42017fcc803fe32017f4c803fc3201ffd4407fe5101ff54407fc51007fd0401fe41007f50401fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50007fd0001fe40007f50001fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84200cffd9510065feca880037f65440013fb2a200cff9951001dfcca88033fd65440197eb2a200cff1951001df8ca880337c65440073e32a2000ffd9110005fec888003bf64440015fb222000ff9911004dfcc888003fd64440017eb222000ff1911004df8c888003bc64440015e322200cffd5110067fca888033fd5444019fe2a2200bffd8d1005dfec688003df63440016fb1a200bff98d10015fcc68802ffd63440177eb1a200bff18d10015f8c68802fdc63440056e31a200bffd4d1005efea68802ffe5344017fea9a200bdf54d1005ff8a68802fff4344017ff21a200bff50d1005ff88688003ff62440017fb122000fbd8910005dec48802bfe62440037f3122000ff58910005fac48802bfc62440037e3122000fb1891000dd8c488033ff5244015ff292200cff54910057f8a488003ff4244015ff2122000ff50910057f8848802fff3244015ff192200bff4c910057f86488033ff5144019ff28a200cfd94510067faa288033f55144019fe28a2000ffd0510007ee8288003fe4144001fea0a2000ff10510007e8828802fff3144017ff18a200bfd8c51005ffa628802ff53144017fe18a200affc8510007fc4288003f62144001fe90a2000fd48510057f84288033ff5044009ff282200cff54110027f8a088003ff4044009ff2022000ff50110027f8808802fff3044009ff182200bff4c110027f8608802bff2044009ff1022000ff48110027f84088003ff1044001fd8822004ff84110027ec2088013ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff5941003dfaca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff9901004dfcc808013fd64040017eb202004ff19010025f8c80801fff540400fff2a02007ff5501003ff8a808013ff63040097fb182004ff98c10015fcc608013fd630400d7eb182004ff18c10025f8c60801bff530400dbfa982006ff94c10037faa60801b7d530400dfe2982006ffd0c10037fc860801bfd430400dfe2182004ffd8810025fec408013fe62040037f3102004ff58810005fac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902000ffd081002ffc8408003fd420400bfe2102006ffcc81002ffc640801bfd320400bfe1902008bf9841003ffea20801ffe510400ffea882007ff14410007fe8208003fe4104001fea082000ff10410037fe620801bfe310400dfe9882006ff0c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x3fc4148025ff98a4012ff8c520097fa629004bfc3148003ff90a4001ff8852000ffa4290007fc21480037fb024013ffd4120027fca09004ffd5048009fe2824000ffd0120027fc8090003fd4048009fe2024012ffcc120027fc609004bfd3048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048023ffb2e2011bfd971008ffccb8800efe65c4023feb2e2011bf5971008ff8cb8800efc65c4001ffb262000bfd9310007fcc988026fe64c4001feb262000bf59310007f8c988026fc64c4023ffaa62011ff9531008ffaa988047fc54c4011ffb1e2008bfd8f10047fcc78800afe63c4011feb1e2008bf58f10047f8c78800afc63c4011ffa9e2008dfd4f10047fca788023fd53c4011bea9e2008ff14f10047fe8788023fe43c4011fea1e2008ff10f10007fec588002ff62c4021ff3162001bf98b10007fac588002fd62c4021fe3162001bf18b1008ffea588043fe52c4023fea962010ff14b10007fe8588043fe42c4001fea162010ff10b10047fe6588043fe32c4011fe9962010ff0cb1008ffea388047fe51c4023fb28e2011ff5471008feaa388047fc51c4001ffa0e2000fdd0710007fc8388003fd41c4001fe20e2000fd10710047fe6388023fe31c4011fb18e2008ff4c710047ea6388023fc31c4021ff90e2000ff88710007ec4388003fd21c4001fa90e2010ff0871008ffea188013fe50c4023fea862004ff14310007fe8188013fe40c4001fea062004ff10310047fe6188013fe30c4011fe9862004ff0c310087fe4188013fe20c4001fe9062004ff08310027fecb08012ff6584009ff32c2003bf99610027facb0803efd6584009fe32c2004bf19610027fec908012ff6484009ff3242009bf99210027fac908002fd6484009fe3242004bf1921007ffea90803ffe548401ffeaa4200fff15210027fec708012ff6384009ff31c2002bf98e10027fac70803afd6384009fe31c2004bf18e10077fea70803b7f538401dff29c200eff54e10076faa70803bfc538401dffa1c200eff90e10077fa870803bfc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc628401fffa94200dff94a1007ffaa508037fc5284001ffa14200dff90a10007fa8508037fc428401dff994200dff8ca10077fa6508037fc32840177eb0c200fffd461007ffca30803ffd518401ffe28c2000ffd0610007fc8308003fd4184001fe20c200effcc610077fc630803bfd318401dfe18c200dffc8610007fc4308003fd218401bfe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fe9042004ff08210027fe2108013f71084001fd8
  | 2 => 0x40027fac420002fd6210009fe3108004bf188400c7fea42005bfe5210031fea908016ff1484004ffe8420027fe4210013fea108009ff108400bffe642005bfe321002ffe9908016ff0c840027fec220013fe61100017f3088004ff58440005fac220013fc6110031ffa888018ff944400c7faa220063fc5110013ffa088009ff904400077c8220027fd4110013fe2088009ef104400bffe622005ffe311002ffe9888017ff0c4400b7fe4220003fe2110001fe9088016ff08440025fcc020013ff5010009ff2808004ff54040027f8a020013ff4010009dfa008004ff90040027f48020013fd4010009dea008009fe50040027fe6020013fe3010009fe9808004ff0c040027fe4020013fc2010009ffb2c4004bfd9620027fccb1000efe6588009feb2c4015bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc910026fe6488009feb244000bf59220027f8c910012fc648802bffaa44015ff952200affaa910057fc5488009ffb1c4004bfd8e20027fcc71000afe6388009feb1c4014bf58e20027f8c710012fc6388029ffa9c4014dfd4e200a7fca710053fd5388029bea9c4014ff14e200a7fe8710053fe4388029fea1c4014ff10e2000dfac510007ff5288003ff2944001ff54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510013ff6188009ff30c4000bf98620027fac310002fd6188009fe30c4015ffd46200affca310057fd518802bfe28c4000ffd0620007fc8310003fd4188001fe20c4014ffcc6200a7fc6310053fd3188029fe18c4001ffc862000ffc4310003ee2188003fe90c4001ff0862000fd84310012fe6088009ffa844004ff94220027faa110013fc5088009ffa044004ff90220027fa8110013fc4088009ff9844004ff8c220027fa6110013fc3088009ff9044004fbc822000ff64110013fc2088009fc1044013ffd952009dfeca900037f65480013fb2a4013ff9952001dfcca9004ffd65480277eb2a4013ff1952001df8ca9004f7c65480073e32a4000ffd9120005fec890003fe64480137f3224000ff59120005fac890003fc64480137e3224013ffd512009ffca89004ffd5448027fe2a24012ffd8d20095fec69004bfe63480057f31a4012ff58d20095fac69004bfc63480057e31a4012ffd4d20096fea69004bfe5348025fea9a4012df54d20097f8a69004bff4348025ff21a4012ff50d20097f88690012ff6248003ffa924001ff9492000ffaa490007fc5248003ffa124001ff9092000ffa8490007fc4248003ff9924001ff8c92000fdc6490007fd3248025f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148027ffa8a4013ff9452009ffaa29004ffc5148001ffa0a4000ff90520007fa829000
  | 3 => 0xe186801fffc8340027f841a0013ff65900097fb2c8004ff9964001dfccb200137e65900073f32c8004ff596400f5facb200137d65900013eb2c8004ff19640025f8cb2006afd649003dffaa48009ff952400f7faa920027fc5490009ffb1c8004bfd8e40027fcc72000afe6390009feb1c801dbf58e40027f8c720012fc639003bffa9c801ddfd4e400effca720077fd539003bbea9c801dff14e4004ffe8720077fe439003bfea1c8009ff10e40027fec520013fe62900037f3148004ff58a40005fac520013fc62900097e314801effd4a400e7fca52007bfd5290039fe2948009ffd0a400e7fc8520003fd4290013fe214801dffcca400e7fc6520077fd3290039fe1948004ffd8640027fcc320002fe6190009fb30c8000bd98640027fac320002fd6190009fab0c8000bd58640027f8c32007bff519003dff28c801eff546400f7f8a320027ff4190001ff20c8000ef90640007fa8320027fc4190001de20c801dffcc6400effc6320077fd319003bfe18c801cffc8640007fc4320003fd2190039fe10c8004bf98240027fea120013fe5090009fea848004ff14240027fe8120013bf4090013fda048004ffcc240027fc6120013fd3090009fe1848004ffc8240027f8412006fff65500377fb2a801bff9954001dfccaa006ffd65500377eb2a801bff1954001df8caa006fff5450013ff2a2801bff5514004ff8a8a006bff63500357fb1a801aff98d40015fcc6a006bfd63500357eb1a801aff18d40015f8c6a006bff5350035bfa9a801aff94d400d7faa6a006b7d5350035fe29a8009ffd0d400d77e86a006bfe4350035fea1a801aef50d4004ff886a0003ff62500017fb128019ff9894000dfcc4a0003fd6250033fe3128001bf189400dffea4a0067fe5250037fea928019ff1494004ffe84a0003bf4250033ff2128000ff509400077a84a0027fc4250035ff9928019ff8c9400d7fa64a0067fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf185400dffea2a006ffe5150037fea8a801bff1454004ffe82a0003fe4150001fea0a8009ff105400d7fe62a006bfe3150035fe98a801aff0c5400cffe42a0003fe2150001fe90a8019ff085400dffea0a0013fe5050037fea828004ff1414004ffe80a0027fb4050009ff2028004ef901400d7fe60a0013fe3050035fe9828004ff0c1400cffe40a0013fc2050009ffb288004bfd9440027fcca2000efe6510009feb288018bf59440027f8ca20012fc65100137f3208009ffd504004ffca820027fd5410013fe2a08004ffd8c40025fec620013fe63100057f3188004ff58c400bdfac620013fc63100097e3188017ffd4c400befea62005ffe531002ffea988017df54c400bff8a620027ff4310013ff2188009ff50c4004ff88620013ff6210009ff3108001bf988
  | 4 => 0x807fe5288403fea944201ff14a2100ffe8510807fe4288403fea144201ff10a2100ffe6510807fe3288403f71944201ff4ca21127da6510807fc32884037f30c4225ffd462112ffca310897fd518844bfe28c4200ffd0621007fc8310803fd4188401fe20c4224ffcc621127fc6310893fd3188449fe18c4201ffc862100fde4310807f72188403fe10c4201fd08621007fec110803fe60884097f3044200ff58221005fac110803fc608844bffa844225ff9422112ffaa110897fc5088449ff9844224ff8c221127fa6110893fc3088403ff9044201ff0822100fd8411088fff65484477fb2a4223ff9952101dfcca9088ffd65484477eb2a4223ff1952101df8ca90803ff64484017fb224200ff9912104dfcc890803fd64484017eb224200ff1912104df8c89088fff5448447ff2a24223ff5512111ff8a89088bff63484457fb1a4222ff98d21015fcc69088bfd63484457eb1a4222ff18d21015f8c69088bff5348445bfa9a4222ff94d21117faa69088b7d5348445fe29a4222ffd0d21117fc869088bfd4348445fe21a4201bfd892100ffea490807fe5248403fea924201ff1492100ffe8490807fe4248403fea124201ff1092100ffe6490807fe3248403fe9924201ff0c92100dfec29088fff5148447ff28a4223ff5452111ff8a290803ff4148401ff20a4200ff50521007f8829088bff3148445ff18a4222ff4c521117f86290807ff2148403fb90a4201ff88521007dc4290807fc2148403f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090812fc6048447ffa824223ff9412111ffaa09088ffc5048445ff9824222ff8c121117fa609088bfc3048403ff9024201ff0812104ffecba0026ff65d0013ff32e8003bf9974004efccba000e7e65d0013feb2e8021bf5974004efacba00027d65d0013fe32e8009bf1974004ffea9a0027fe54d0013feaa68009ff1534004ffec7a0026ff63d0013ff31e8002bf98f4004ffac7a0082fd63d0013fe31e8002bf18f40107fea7a00837f53d0041ff29e8020ff54f40106faa7a0083fc53d0013ffa1e8009efd0f4004ffc87a0027fd43d0041dea1e8009ff10f4004ffec5a0027fe62d00037f3168009ff58b40005fac5a0027fc62d00037e3168021ffd4b400fffca5a0087fd52d003ffe2968009ffd0b4004f7e85a0027fe42d0013fea168000ef50b4004ff885a0083ff32d003fff1968020ff4cb400fff865a0027ff61d0013ff30e8000bf9874004ffac3a0002fd61d0013fe30e8021ffd474010ffca3a0087fd51d0043fe28e8009ffd074004ffc83a0027fd41d0013fe20e8020ffcc740107fc63a0083fd31d0041fe18e801fffc8740007fc43a0003fd21d003ffe10e8021ffd4340027fca1a0087fd50d0009fe2868020ffcc340027fc61a0083fd30d0009f
  | 5 => 0x9541006fecaa08027f6550459ff32a8203bf99541167facaa08b2fd6550459fe32a8203bf19541166f8caa080e7c6550459ffaa28209ff95141167faa8a0827fc5450457ffb1a822bbfd8d4115ffcc6a080afe6350457feb1a822bbf58d4115ff8c6a080afc6350457ffa9a822bdfd4d4115ffca6a08affd5350457bea9a822bff14d4104ffe86a08affe4350457fea1a8209ff10d41007fec4a0802ff6250455ff3128201bf98941007fac4a08abfc62504037e312822cffd4941157fca4a08b3fd5250455fe2928209ffd0941157fc84a0803fd4250413fe212822bffcc941157fc64a08affd3250455fe192822cffd4541167fca2a08b3fd5150459fe28a8209ffd054104fee82a0803fe4150401df20a822bffcc54115ffc62a08affd3150457fe18a822affc8541157f842a0803ff60504017fb028200ff98141007fac0a0803fc60504097e302822cffd4141167fca0a08b3fd5050459fe282822bffcc14115ffc60a08affd3050457fe182822affc8141157f840a0827ff65104137fb288209ff9944101dfcca208277e65104073f3288209ff59441145faca208277d65104013eb288209ff1944104df8ca20826fe6410413ffaa08228efd504104ffca820827fd5410413fe2a08209ef1504104ffec620826ff6310413ff3188202bf98c4104ffac62089efd6310413fe3188202bf18c4113ffea62089f7f531044fff2988227ff54c4113efaa62089ffc5310413ffa188209efd0c4104ffc8620827fd431044fdea188209ff10c4104ffec420827fe62104037f3108209ff58841005fac420827fc62104037e3108228ffd4841137fca4208a3fd521044dfe2908209ffd084104f7e8420827fe4210413fea108200ef5084104ff8842089fff321044dff1908227ff4c841137f864208a6fe6110451ffa888228ff94441147faa2208a3fc5110413ffa088209efd044104ffc8220827f64110413fea088200ef5044104fea822089fff311044fff1888227ff4c44113ff8622089bff211044dfb9088226ff08441137e84220827ff6010413ff3008204bf9804104ffac020802fd6010413fe3008228ffd4041147fca0208a3fd5010451fe2808227ffcc04113ffc602089ffd301044ffe1808226ffc8041137f84020897ff658844b7fb2c4225ff9962101dfccb108977e65884073f32c4225ff5962112dfacb108037d65884013eb2c4225ff1962101df8cb10803ff64884017fb244200ff9922104dfcc910803fd64884017eb244200ff1922104df8c910897ff548844bff2a44225ff5522112ff8a910893ff63884497fb1c4224ff98e21015fcc710893fd63884497eb1c4224ff18e21015f8c710893ff5388449bfa9c4224ff94e21127faa7108937d5388449fe29c4224ffd0e21127fc8710893fd4388449fe21c4201bf58a2100ffea510
  | 6 => 0x5fea1a8432ef50d4204ff886a1006ff6250803ffa928401ff9494200ffaa4a1007fc5250803ffa128409fbd094200ffc84a1007be4250803fe2128401ef1094200fd884a1007ff3250803ff1928401fb8c94200ffa64a10cbed3250803fe1928400ffd8542005fec2a1003f761508017bb0a8400ff98542007fac2a1003fc61508017e30a8400fd18542005e8c2a10cfff5150867ff28a8433ff5454219ff8a2a10cbff3150865ff18a8432ff4c542197f862a1007ff2150803fe10a8400ffd8142005fec0a1003fe6050801feb028400ff18142025f8c0a10cfff5050867ff2828433ff5414219ff8a0a10cbff3050865ff1828432ff4c142197f860a1007ff2050803fe1028409ffd974104dfecba0827fe65d04077f32e8209ff5974118dfacba0827fc65d04137e32e8209ffd534104ffca9a0827fd54d0413fe2a68209ffd8f4104dfec7a0827fe63d04057f31e8209ff58f41185fac7a0827fc63d04057e31e8230ffd4f41186fea7a08c3fe53d0461fea9e8230df54f41187f8a7a0827ff43d0413ff21e8209ff50f4104ff887a0827ff62d0413ff3168201bf98b4104ffac5a0802fd62d0413fe3168201bf18b4118ffea5a08bffe52d0463fea96822fff14b4104ffe85a0827fe42d0413fea168209ff10b41187fe65a08bffe32d0461fe996822fff0cb4118ffea3a08c7fe51d0463fea8e8231ff14741187fe63a08c3fe31d0461fe98e8230ff0c74117ffe43a08bff721d045ffe10e822ffd0874104ffec1a0827fe60d04097f3068209ff58341005fac1a0827fc60d0463ffa868231ff9434118ffaa1a08c7fc50d0461ff9868230ff8c341187fa61a08c3fc30d045fff906822fff08341177fecb208baff659045dff32c8203bf99641177facb208bafd659045dfe32c8203bf1964115dfac9208bbff549045ddfaa48209ff95241177faa920827fc549045dde2a48229ffd8e4114dfec7208a7fe63904057f31c8229ff58e4114dfac7208a7fc63904057e31c8229ffd4e4114efea7208a7fe5390453fea9c8229df54e4114ff8a720827ff4390453dfa1c8229ff90e4114ffa87208a7bd4390413fe21c8200ffd8a4116ffcc520806fe6290401feb148200bf58a4116ff8c520806fc629045dffa94822dff94a41177faa5208b7fc5290413ffa148200efd0a4116ffc8520803fd4290401dea148209ff10a4114ffe65208b7fe3290453fe994822dff0ca4104dfcc3208bbff519045dff28c822eff54641177f8a320827ff4190401dfa0c8209fdd064114ffe63208a7fe3190453fe98c8229ff0c64116ffe43208b7fc2190401ffb048200ff98241025fcc120803fd60904017eb048200ff18241177fea1208bbfe509045dfea84822eff1424114ffe61208a7fe3090453fe9848229ff0c24116ffe41208b7fc2090459ffb2a822cbfd
  | 7 => 0x160040000100000002006000000030010000cc0000004e0040400900200c020110060000d00e00000000056002008000020180100500e0060100180101600001000006000028000020540982a018000000010080200080d000044018000100240b8030000000000001c00000000010010010000100380280800001800805020000040030040000080a01e004048000020340100f0020240a818048018000000080002300500000c0400301e008120300020080000f0060080100a00a02c01011032004068020140080100000204c0101702403c0280f0000340000000e00002003000048030030040280000100005c0380f0040082180d02e020018050440100100601803800001002044000000040040c00400201002800006004000080040080d00603605c0380b05a0201501b02a05c068030060780400204a0100000a0aa0000000402400000000000014000000160140000000400c00000000000108030640a0010010000000080000e01400000000000000000220000000e01c010010030460040201100c0000481701c0080700400001004801008000020000080040100100603c02804002040008060340040000a0280000080e00c024000040020080080100001c0000800200009009000040008010bc004030040000000500100c01403027ff65d08137fb2e8409ff9974201dfccba1027fd65d086b7eb2e8409ff1974204df8cba1006fe64d0813ffaa68409ff9534204f7ca9a1027fd54d086bdeaa68409ff1534204ffec7a1026ff63d0813ff31e8402bf98f4204ffac7a10d2fd63d0813fe31e8402bf18f421a7fea7a10d37f53d0869ff29e8434ff54f421a6faa7a10d3fc53d0813ffa1e8409efd0f4204ffc87a1027fd43d0869dea1e8409ff10f4200dfac5a1007ff52d0803ff2968401ff54b4200ff8a5a1007fe42d0803df2168401fb90b4200ff885a1007bc42d0803ff9968401ff8cb4200ffa65a1007fc32d0813ffb0e8409ff98742005fcc3a1027fd61d08017eb0e8409ff187421affea3a10d7fe51d086bfea8e8435ff147421a7fe63a10d3fe31d0869fe98e8434ff0c74200ffe43a1007fc21d0813ffb068409ff98342025fcc1a1027fd60d08017eb068409ff183421affea1a10d7fe50d086bfea868435ff143421a7fe61a10d3fe30d0869fe9868434ff0c34200ffe41a1007fc20d0867ffb2a8433bfd9542006fecaa10027f6550867ff32a8403bf9954219ffacaa10cefd6550867fe32a8403bf1954219ef8caa100e7c65508037fb228433ffd514204ffca8a10cfbe5450867feaa28433ef5514204ff8a8a10cbff63508657fb1a8432ff98d42015fcc6a10cbfd63508657eb1a8432ff18d42015f8c6a10cbff5350865bfa9a8432ff94d42197faa6a10cb7d5350865fe29a8409ffd0d421977e86a10cbfe435086
  | 8 => 0xc5440005f23ea708158950000218c760009925480009be00000000074864200000050a000000000c822020008584148aab24cf000a30c754aec0842b618e3ba33022a56282836eb8e86279e6b4cc8c683dec18958118000246a64988a660ae00005a99a99016e4860005e60000668ec2e68bac8ebae00015c00093cae81e49409e4bc0b186bca2cbbc84641e49671c58c0b485c95cca03dccc4930276ada7e228c7107a24d875a16c7b0c4662812ecac5fac7c55c794432b9009ac14c1e96482a240be49521ca6260008c653e86a2eeb267f676ca8a3600001600005504e874c00045ac1a0003103866d83d63c27e65140003e46ce7ae2e01b4bd41ac924b56cca6960323d044859026a75e320b922065061b0374b2813a9d021a83c2266ac9622d855684272e14e47425e478cbeacc34acce01864c73ea1a1cea3cb5aa4892a65220ac002a0b4453a3721948405029d2c54932ac2000a40a8e1043b0c9ab52a76a12ae2b407dea1eb649c284ac2093ea5a008b688da848b0846e28a2640fa00031e000054af89e831a6fccaebe813e470bfe536a92152b3649ea22576ad2936cba4265547a04a81a229001ca680b8260574420b6600052a338068534afe5de6c837a63e0000942c20000003b40000e0b6a32648000025a4da000058c2487448a8b6ace000000ba20000006543f2000000b3c9f066844a546142428000c02c602c80009446ec48c000a2609054aba482c5f6b420000d091267262a2d418059a000c101d61cc7ee14812810e9a03b824c00000000081e650728d022e439c2aabc878814c0000008f80006a2000a948cc0e44e07ea0008603f012cad46c013cc3c4080004de604c6a1768acac8a2a22085a52c21c3a86f018c5e80be2be1ba7f27d60a680e0008440042fe000a02bf4740116000ca63028be8d27da21201aac60008e695a40487a00027c6a672ca0e24265c58e2ec4ae612ad82500000240b01a8000c3800084c7c48fa40acd89d6c6e4babb02887708e04be000aa8000cbc38cab88780006d400004e0040003100205c0680200a0140080100404c020000140080001b0060000380d00a0080100600602c018110000400681c01400c0080100e0280480100200402800000018088030020181180b00e0140a000002000028130000000380a04e0380000103804401803002098038000000000080400207c0600100402c01012000028128170060000800501a00400017004004008010140140c81604000005000008008018000080180c00001c0240481d0060040100200201c0100900016c038030020100200c00000c0080f00002c0400a002000040020020000280d01a01c090000000080281800c074000000400040c80302203809001002014010130000080000703a0180100206402c0300000400400000022034030000
  | 9 => 0xb2c000cd29160000000005a259c4d435a5800002fa5e0a4a000cea0001b6910c5e99eab476860207ebf2b7a184cd6c0622c2d08300f0bf07bc87ece0b3a4065aa08204e4027220009389ca5640004648f61dc0000009780002dc0004948ca3da00051ea809140aa6f410296685e77a0000000009025a4afc23c3906e0ac055abbe0003a068a000974000c40000c2892c3e217a12a0006462a6a7007a70202a4688c0c2c000342558a18000ceca060004420009fa38415e30a3ce44646052206e91e0fca9e50872a58229c6cac721e215a4fcb22124000866500670af0a1c00051a798aa0a5808abe23bc8e896c8de79a75c0783c0b968fc000430746638c883f84f675693ac9e97aaae834282718782344a5232a000000000a2e4e6000000336000ca8c7ab1432e000816000bf8352a32bb8156bce0000008a01984aa000000c42b3e43603080600000000000043c1be00097eb7043e724cc60f26869a47c878e2ca4ec67a2b01c68384444f4cccc96000750adc3965d01c0096ae01660008d40005942860000003d494e35c4feb304a08e26f6000bfa0000cc2de7648d80009bc48e74a8543fc0006d20000000002cea6216a36c95e56c9cc4f854cbdcac4cc0614b7400000000c0006e2000000000000a466ae96ac1c692c78c220f689c6b21ec0002380145884903981aab6000e0000004181b2000c747aa9e2c52000cf462086ca720000009fe6fa0000005da0009bacd488c2b80000000004d08223ee1ae3b2af6b7852e504c844ca3823b6cf80000007ce530000b6242c000228b9cbc68f2192c16b50244000a8879cb5c0b25bcca2000a281de5ca08603ab9a0d4000000bba6dc69a90463aa249f87cc284000c5a30eaa40000003328c20dc0007fc6c68b861c8bc0d64b6000c2a8f028e2540003ae00000042e30881800064a4668a8becad0a9c0003280005f8c3a6e86001f20006e6ad61c852035e5fc7d4cfc0007b8274c369486180000ac4e467e60aa30a20c6417441c3be6baa7c4169081f06a8bcaa3a00080049a334a365702d602c106162826960b4a9ce22e000314000a4e3e65604ccb0c89294c6a4312632c6632c0a2c806640001b8c3402eb16760856aca0707040000400008d02242682da4d60002e23640000b614600017e14a80401629a44c000a74322ce6bde5e2232cd025c2bc450a540928727e82c403e1f8ade58a2d261076a17cb0618a9de33e07c45683e4b24627526a0c8a3c8cee0f4894bac59808e51c66c51063cbaa5b07ac4a41e07f477cb1ab009562a22aca5e6768aeb5e1866240de99800083ab4eabca8400011027a0003485c06f87b21bccfece233a9dc8b21a66b0888236098c3074e47e9063ca6060000460809c0258340cc258470ac4e98a10c48220c5ae7580002b4000bd0c44c262c00000005ba6ea5e
  | 10 => 0x8292e9fcaee6444220001fcc6c8b403639a2f47420002f82c60001f6778000738a00c5c9c8a5601089800079624898219a000c4a986bee5f4a104b08100f87744dc49800062c000a6e24e76eb86138790aa28a461a000b3443a03c11a3ccb0e5c455e1507be042aba1220001308f4b4804a40ca504f2784b545d42f0bb20004c873c438000716c08ce88ee5fe0007120004c0b887324ee0ba2221d421e4723ec294aa66160008c40001000000000d867c3f65380449eeb020006400005b43accb80007f03000000ce630abe0007c090c15414034e00000059200099c70000010ab7c000000680690b80c901a484e00019e88e358000c94440000bc2112476c0a02266ea90000926be600011e0004a28249c6c3e29800053c00070c0c0ab0634706484720a6006a4fa6da0a80001e6af294a4920027a49ac3e0c8660c5b614421433c30657a114c9c714000346000000000c0e3a27b6000bd60000c23faa6c890bda0003d20000009b856e97670e54e00078a47a97c94200026eb1e1d245e000062b943c4540c8c852256b8a7c2622a166b8a083a68a6aaac560005be0ea7e0a4481a0007ec17837c000c92000896bcc1d85182ea9aa46ab3827e62e38027857e03439e9b60000002724546b60c85d60005c2000970000524636000b8c5b8a0cb4cab20009f27805e4a04532bc4000af400036ac50bd20005b29f60a402090e24a000000000000b7680800080c000a7ab72210000a3eb826be2040002fc000c62bd89849ea9d4026b46ab6a420002a8a149e042a78c6886085521360006c49a8196a965280009d8370000a9a77249caac4e2ae4376000a380fe000b84864000850a3400007448881200040e0005cc674b6e37ea4c3786d00004c2920a866988ea73ab2ed049e623abea6fecf668c0520e823e00000005e188c58b0465e7a6000684572662cda9a657cb0a0001d00761c49f4b200000000003f48200ee00000045800082e29677e586000000000088b7e000a8c65812089e7c645c64871acb65c69ec51288a31846c452ba6412cf2000b6c6f26562b20068cea988c85ce356000678000a5c000cb24c608c0bc7e430444e52690000028069e5164d281cc321da5dc01219c8fe126b3201e60e86e2521322aeba864e7fe9da0008829b48a2c987dc0500ca3c62f289a38acb0886744802c70c0c000000000aea7261081ea6600007344ac4a665a00000038e77698e5d2000000000cde66a000c0487092879298083211c3625c84b82082e85a8000424ae606c5ac164c7e000762b12c489b250e1680287863a4ce4cfa2ba0a050c6d68dc368afa0c42f60da7fa596ca4b2abb6230000038cb4000400c2e172410234200766b1000098c0007a8c4ca0a6c20e687c8768140007ba1a041a9723540003d80004c488496856800000083600000005680a
  | 11 => 0x5a05ee0009a23662165781fa4b400096e0006de4bc6e400000090a0006aa91c000000316392caa0001fe7f8be020e00069434c09c9b073606059ea787ca7d029299468e0c609ebf63fe91a5ea0e25421908686820ec0004f08d66eea7e47c43426cd009967d84ceb582a41e86cc1eebb48b00000003e888056ac121701c29c44ea0009222668e431c064a6a000bfcb9e0000489460007d23942cc9ae954934000388cdc04c66627005c0d27b49185a626261e69cb985f0730b1c3240005d83500001f400071e29e0001825663aaba0134072a
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe31594100067d31594100067c31594100067f21594100067c21594100267f70594100267e70594100267d70594100267c70594100267f40594100267e40594100267d40594100267c40594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267710594100267e10594100267d10594100267510594100267c1059410004ff755901001cfe7559010004fd755901001cfc7559010026bf7459010004ff7359010014fe7359010004fd7359010014fc73590100067f53590100067d5359010006bf4359010006bd4359010004ff725901000cfe725901000cfc725901004cff715901004cfd7159010024ff7059010024fe7059010024fd7059010024fc7059010026be4059010026bc4059010004ff755881001cfe7558810004fd755881001cfc7558810004ff745881004cfc7458810004ff7358810014fe7358810004fd7358810014fc73588100067f53588100067d5358810026ef725881002eee425881002eee3258810006ed325881000cff715881000cfd715881002cfc715881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f5105881004cff76d0810024fe76d0810004fd76d0810024fc76d08101ae7e65d08100067d65d081004ebe64d0810006bd64d0810004ff7650810024fe7650810004fd7650810024fc76508100057f755081003d7c755081019e7e65508100067d655081004ebe6450810006bd645081000eee6250810006ed6250810005f77150810005f47150810004fd76d041018e7e65d04100067d65d04101cef661d0410004ff769041004cfd76904101767e65904100067d659041004ebe6490410006bd6490410025fa7090410005f97090410004ff76504100057f755041003d7c75504101667e65504100067d655041004cff7610410024fe7610410004fd7610410024fc761041003d7e75104100057d75104101467e65104100067d651041004ebe6410410006bd64104101cef66110410025fa7010410005f97010410084ff7688410024fe768841000cfd7688410024fc768841003d7e75884100057d758841012e7e65884100067d658841000eee6288410006ed6288410086f66188410025fa7088410005f97088410084ff764841011e7e65484100067d6548410086f66148410025fb7644010006fb7644010004fb76440100077b75440101b77875440100277a6544010027796544010007bb7444010007b87444010007db73440101c7d873440101c77b53440101c7795344010007eb7244010007e87244010025fb7144010027f371440101befa6144010027f261440101b7f251440101b7f15144010007f24144010007f14144010
  | 1 => 0x85100057575885100077765885102277465885101f5f674885101f5f47488510007b76488510007b4648851021df7738851021df57388510007d76388510217d46388510217775388510217755388510055f57288510007e7628851000ef6628851000ef46288510057e4628851000ee46288510057e63288510217e53288510025f67088510025f4708851020fe6208851020fe42088510024fc76485100067f654851011e7c6548510006bf6448510006bc6448510006df6348510116dc6348510006ef624851000eec6248510005fb7048510025f87048510025f4764851000ef47648510024f47648510205f77548510205f575485100077765485101ff7465485101f5f674485101f5f47448510007b76448510007b464485101edf773485101edf57348510007d763485101e7d463485101e77753485101e7755348510055f77248510007e77248510007e7624851000ef6624851000ef46248510057e46248510007f37048510025f67048510025f47048510007f07048510004fe76d01100657e75d01100057d75d01100067f65d011010e7c65d0110006bf64d011004ebc64d0110006df63d0110106dc63d0110006ef62d01100feec62d0110005f671d0110005f571d011004cff7650110004fd765011004cfc76501100067f65501100de7c6550110006bf645011004ebc6450110006df63501100d6dc6350110006ef62501100ceec6250110005f77150110005f47150110027b84050110027f0105011000cff7648110054fd764811000cfc76481100057f75481100657c75481100067f654811009e7c6548110006bf6448110006bc6448110006df6348110096dc6348110006ef624811000eec6248110005f77148110005f47148110027e820481100067f65c411008e7c65c4110006bf64c4110006bc64c4110006df63c4110046dc63c4110006ef62c4110086ec62c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41101df7865c4110007bb64c4110007b864c4110007db63c41101d7d863c41101d77b53c41101d77953c4110007eb62c4110007e862c4110025fa71c4110026fb61c4110027f361c41101dff251c41101dff151c4110007f341c4110007f041c41101d7f231c41101d7f131c4110007f221c4110007f121c41100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067e42594100067c42594100067f32594100067e32594100067d32594100067c325941003e7f71594100067e715941003e7d715941003e7c71594100067f31594100067
  | 2 => 0x6ec6318910007cc6318910006cc63189100076f53189100076d5318910057e5711891027eef6118910007e65118910007e55118910007e63118910007e5311891027fe6101891027fe4101891004cff76d0910004fe76d0910004fd76d091004cfc76d09100067f65d09101ae7c65d0910006bf64d091004ebc64d0910006df63d09101a6dc63d0910006ef62d091000eec62d0910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100657c75509100067f655091019e7c6550910006bf645091004ebc6450910006df6350910196dc6350910006ef625091000eec6250910005f77150910005f47150910024fe76d0510024fc76d05100067f65d051018e7c65d0510006bf64d051004ebc64d0510006df63d0510186dc63d0510006ef62d051017eec62d0510025fa70d0510005f970d0510025f676d05101f6f676d0510024f676d05101f5f775d0510275f575d05100077765d051026f7465d05101f6f764d0510007b764d05101f6f564d05101f7b464d05101f5f773d0510265f573d0510007d763d051025fd463d051025f7753d051025f7553d0510005f572d0510007e762d051017ef662d051017ef462d0510007e462d051017ee462d0510025f670d05101f7f270d0510025f270d05101f7f170d0510025f470d0510004fe76905100067f65905101767c6590510006bf649051004ebc6490510006df639051014edc6390510006ef629051016eec62905101f5f67190510024fc76505100057f75505100657c75505100067f65505101667c6550510006bf645051004ebc6450510006df635051015edc6350510006ef6250510156ec6250510005fb7050510025f87050510004fe76105100657e75105100057d75105100067f65105101467c6510510006bf641051004ebc6410510006df631051013edc6310510006ef6210510136ec6210510007b54110510005f676105101f6f676105101f5f775105101f7767510510255f575105101f775751051000575751051000777651051024f7465105101f5f674105101f7b674105101f6f76410510007b76410510006b764105101f6f564105101f7b4641051024fb754105101f7b454105101f5f77310510245f57310510007d7631051023fd4631051023f77531051023f7553105101f7b7431051023fb54310510005f57210510007e76210510136f66210510136f46210510007e46210510136e462105101f7b74210510007b54210510025f67010510025f47010510237b64010510237b4401051006cfe76885100657e75885100057d75885100067f658851012e7c6588510006bf6488510006bc6488510006df6388510126dc6388510006ef628851000eec6288510005f6768851006ef6768851022df7758851022776758851022df5758851000775758
  | 3 => 0xd52d8910056ec52d8910056ee42d8910056ec42d8910006ef32d8910056ee32d8910006ed32d8910056ec32d891000cfe71d8910024fd71d891000cfc71d8910056ef21d8910024fe70d8910054fd70d8910024fc70d8910056ef20d8910055ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d891020fe771d8910007e651d8910007e551d8910007e631d8910007e531d891020fe610d891020fe410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d891020eef71d8910056ee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d891020eee70d8910006ed70d891020eec70d8910006ef50d891020eee50d8910006ed50d891020eec50d891020eee40d891020eec40d8910006ef30d891020eee30d8910006ed30d891020eec30d891020eee10d891020eec10d89100057f75589100657c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df735891005ddc7358910006df6358910006dc6358910056ec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf745891004cfc7458910006bc745891004cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc73589100067f53589100067d5358910054ff7258910006ef725891006cff7158910006f77158910084ff7058910006fb7058910005ee7618910056ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910
  | 4 => 0x91100079c63191100069c63191100073f53191100073d5319110006be6219110006bc6219110237b77119110007b65119110007b55119110007b63119110007b53119110237b61019110237b4101911004ebf751911004ebe751911004ebd751911004ebc751911004ebf731911004ebe731911004ebd731911004ebc7319110006bf53191100063f5319110006be5319110006bd53191100063d5319110006bc531911004ebf721911004ebe721911004ebd721911004ebc7219110006bf5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bd3219110006bc321911004ebf711911004ebd7119110006bf5119110006be5119110006bd5119110006bc5119110006bf3119110006be3119110006bd3119110006bc3119110006bf2119110006bc211911004ebf701911004ebe701911004ebd701911004ebc7019110006bf5019110236be5019110006bd5019110236bc5019110006bf3019110236be3019110006bd3019110236bc3019110006bf2019110236be2019110236bc2019110236be1019110006bd1019110236bc101911005dde76d8d1005ede76d8d10014de76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10287d771d8d1005fd471d8d10007d651d8d10007d551d8d10287d610d8d10287d410d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006de42d8d10006dc42d8d10286df71d8d1005ede71d8d1005edd71d8d1005edc71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df21d8d10006dc21d8d10006df70d8d10286de70d8d1005edd70d8d10286dc70d8d10006df50d8d10286de50d8d10006dd50d8d10286dc50d8d10286de40d8d10286dc40d8d10006df20d8d10286de20d8d10286dc20d8d10286de10d8d1005edd10d8d10286dc10d8d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910056ee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d891004cfe74d8910004fd74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910006ef52d8910056ee52d8910006e
  | 5 => 0x14fe73d9110004fd73d9110014fc73d91100067f53d91100067d53d9110006bf43d9110006be43d9110006bd43d9110006bc43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110006bc42d911004cfe71d9110006f571d911004cfc71d9110024fe70d9110024fc70d911004cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d91100073f53d91100073d53d9110006be62d9110006bc62d9110007b571d9110007b651d9110007b551d9110007b631d9110007b531d911028fb610d911028fb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d911028ebf71d9110006bd71d9110006b571d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d911028ebe70d9110006bd70d911028ebc70d9110006bf50d911028ebe50d9110006bd50d911028ebc50d9110006bf30d911028ebe30d9110006bd30d911028ebc30d9110006bf20d911028ebe20d911028ebc20d911028ebe10d911028ebc10d91100657e75991100057d75991100067f65991100067c6599110006bf649911005dde7399110005dd7399110006dc6399110055ee7299110005ed72991100057f75591100657c75591100067f65591100067c6559110005df735911005ddc7359110006dc6359110005ef7259110055ec7259110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110006df7359110004df7359110014fe7359110004fd7359110014fc7359110006dc7359110014dc73591100067f53591100067d5359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c651911004ebe6419110006bd6419110006dc6319110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc631
  | 6 => 0xe7359210004fd7359210014fc73592100067f53592100067d5359210006bf4359210006bd4359210004ff725921000cfe725921000cfc7259210024fc7059210026be4059210026bc4059210004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a1004cfc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a100067f5358a100067d5358a10026ef7258a1006eee3258a10006ed3258a1006eef2158a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a1004cff76d0a10024fe76d0a10004fd76d0a10024fc76d0a1004ebe64d0a10006bd64d0a10004ff7650a10024fe7650a10004fd7650a10024fc7650a100057f7550a1007d7c7550a1004ebe6450a10006bd6450a10005f77150a10005f47150a1004ebe64d0610006bd64d0610025fa70d0610005f970d061028ebf649061004ebc649061004cff76506100057f755061007d7c755061004ebe6450610006bd6450610005fb7050610025f8705061007d7e75106100057d7510610236bf641061004ebc6410610054fd768861007d7e75886100057d758861020eef628861000eec628861000cff7648610024fc764861000eee6248610006ed6248610005fb7048610025f87048610025f976c4210006f976c42102a77b53c42102a77953c4210027f271c421029ff251c421029ff151c42100657e76d95100667e76d951001c7e76d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100067e62d95100067c62d95102977771d95100677471d95100077631d95100077531d95102977610d95102977410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067e42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95102967f71d95100667e71d95100667d71d95100667c71d95100067f31d95100067e31d95100067d31d95100067c31d95100067f21d95100067c21d95100067f70d95102967e70d95100667d70d95102967c70d95102967e40d95102967c40d95100067f30d95102967e30d95100067d30d95102967c30d95100067f20d95102967e20d95102967c20d95102967e10d95100667d10d95102967c10d951004cfe76d91100067f65d91100067c65d9110006dc63d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110004ff73d9110
  | 7 => 0x8b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b1004cfc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b100067f5358b100067d5358b10006ef7258b10024fc7158b10086ec2158b10086ef2058b1004cff76d0b10004fe76d0b10004fd76d0b1004cfc76d0b10006bf64d0b1004ebc64d0b10004ff7650b10004fe7650b10004fd7650b10004fc7650b100057f7550b1008d7c7550b10006bf6450b1004ebc6450b10005f77150b10005f47150b10005f576d07101cef576d07101cdf775d0710315f575d07101cef764d07101cef564d07101cdf773d071030df573d07103077753d07103077553d0710005f572d071017ef662d071017ef462d0710025f670d0710025f470d0710024fd769071004ebe6490710006bd6490710025fa7090710005f970907100057f755071008d7c7550710024fd761071008d7e75107100057d751071004ebe6410710006bd6410710007b54110710025fa7010710005f97010710025f576107101cef57610710024f576107101cdf775107101cf7675107102fdf575107101cf7575107100057575107101cfb674107101cef764107101cfb664107101cef56410710007b564107102f7b754107101cfb454107101cdf773107102edf573107102e77753107102e77553107101cfb743107102e7b54310710005f57210710136f66210710136f462107101cfb74210710007b54210710025f670107101cff270107101cff17010710025f47010710237b64010710237b44010710024fd768871008d7e75887100057d758871000eee6288710006ed6288710025fa7088710005f97088710025f5768871000ef57688710024f576887102d5f775887102df7675887102d5f575887100077575887100057575887101cdf674887101cdf474887102cdf773887102cdf573887102c77753887102c775538871000ef66288710087e66288710007e5628871000ef46288710087e632887102c7e53288710025f67088710007f27088710007f17088710025f4708871020fe6208871020fe4208871002cff7648710005f7764871002ef776487102bdf775487102bdf575487101cdf674487101cdf474487102b5f773487102b5f573487102af7753487102af755348710007e7724871000ef6624871000ef46248710025f67048710025f4704871008d7e75d03100057d75d031004ebe64d0310006bd64d0310005f671d0310005f571d031004cff765031004ebe6450310006bd6450310005f77150310005f4715031000cff764831000cfc76483100057f754831008d7c754831000eee6248310006ed6248310005f77148310005f47148310004ff755921001cfe7559210004fd755921001cfc7559210026bf7459210006bf5459210006bc5459210004ff7359210014f
  | 8 => 0x57d75985200067f65985200067c6598520006f76198520055f970985200057f755852009d7c75585200067f65585200067c6558520005bf7458520005bc7458520005df7358520095dc7358520085fb70585200067f65185200067c6518520006f56118520004ff751852001cfe7518520004fd751852001cfc751852004cfe7418520004fd7418520004ff7318520014fe7318520004fd7318520014fc73185200067f53185200067d5318520024fd721852002eee3218520006ed3218520006f73118520006f4311852002ef6211852002ef52118520024fe7018520024fc701852027eee201852027eec2018520004fe76d0520004fd76d052004cfc76d05200067f65d052018e7c65d0520006f761d0520006f461d0520004fe7690520004fd7690520004fc76905200067f65905201767c6590520006bf649052004ebc6490520004ff7650520004fe7650520004fc76505200057f755052009d7c75505200067f65505201667c6550520004fe7610520004fd761052004cfc761052009d7e75105200057d75105200067f65105201467c6510520006bf641052004ebc641052000dee7210520005ed7210520006f76110520006f46110520025fa7010520005f9701052000cfe76d012000cfc76d012009d7e75d01200057d75d01200067f65d012010e7c65d0120006bf64d012004ebc64d012000dee72d0120005ed72d012004cff765012000cfe76501200ccfd765012000cfc76501200067f65501200de7c6550120006bf645012004ebc6450120005ef725012000dec7250120004ff75d931001cfe75d9310004fd75d931001cfc75d9310004ff73d9310014fe73d9310004fd73d9310014fc73d93100067f53d93100067d53d9310006bf43d9310006bd43d931000cfe72d9310004fd72d931000cfc72d9310006f671d9310006f970d931028ebe40d931028ebc40d9310004fd7699310006bf649931004cff76593100057f755931008d7c7559310004ff75593100067f75593100047f755931001cfe7559310004fd755931001cfc75593100067c755931001c7c7559310006bf7459310004ff7359310014fe7359310004fd7359310014fc73593100067f53593100067d5359310004ff725931000cfe725931000cfc7259310006f4715931008d7e75193100057d751931004ebe6419310006bd641931008d7e75d8b100057d75d8b10086ee62d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b1004cfe74d8b10004fd74d8b10004ff73d8b10014fe73d8b10004fd73d8b10014fc73d8b100067f53d8b100067d53d8b10084fd72d8b10086ee32d8b10006ed32d8b10006f671d8b10006f970d8b1020eee20d8b1020eec20d8b1000cff7658b10086ec625
  | 9 => 0xd7088620007e9708862000eee608862000fea608862032d7e76d952009e7e76d952001c7e76d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95203276e32d95200076d32d95203277b20d952031f6e20d952031f6c20d95203277820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d952031e7f72d95203267e72d95203267d72d95203267c72d95203267f42d95203267e42d95203267d42d95203267c42d95203267f32d95203267e32d95203267d32d95203267c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d95203267f21d95203267e21d95203267d21d95203267c21d95203267f70d952031e7e70d95203267d70d952031e7c70d952031e7e40d952031e7c40d95200067f30d952031e7e30d95200067d30d952031e7c30d95203267f20d952031e7e20d95203267d20d952031e7c20d952031e7e10d952031e7c10d952004cfe76d91200067f65d91200067c65d9120004ff75d912001cfe75d9120004fd75d912001cfc75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d91200067f53d91200067d53d9120006be43d9120006bc43d9120024ff72d912000cfe72d9120024fd72d912000cfc72d91200e6bf42d91200e6bd42d91200e6ee32d9120006ed32d9120004fe71d9120004fd71d912009d7e75991200057d75991200067f65991200067c6599120006bf64991200cdf970991200057f755912009d7c75591200067f65591200067c6559120005df7359120095dc7359120005f77159120005f471591200fdfb7059120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c7559120006bf7459120004ff7359120006df7359120004df7359120014fe7359120004fd7359120014fc7359120006dc7359120014dc73591200067f53591200067d5359120006bf4359120006bd43591200ccff7259120006ef72591200ceee3259120006ed3259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f471591200fcff7059120006fb70591200e4fe76191200067f65191200067c651912004ebe6419120006bd64191200067f65d85200067c65d8520004ff75d852001cfe75d8520004fd75d852001cfc75d852004cfe74d8520004fd74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d8520024fd72d8520006f731d8520006f431d852006ef621d852006ef521d852009d7e7598520
  | 10 => 0x8440014fc73584400067f53584400067d5358440004ff725844000cfe725844000cfc7258440026f77158440006f65158440006f5515844004ef7415844004ebc415844004ef4415844004eb44158440006f63158440006f53158440026f61058440026f4105844004dbd7690440006bd7690440176be659044004ebc659044004ebf6390440346bd63904403473f53904403473d5390440006bd629044004dbe719044004fb67190440006bd619044028dbd709044028ebe609044004fba6090440004ff7688440024fe7688440004fd76884400c57e75884400057d7588440006f66188440006f56188440004ff7648440004fd7648440024fc7648440005bf744844004dbc744844000eee6248440006ed6248440006f66148440006f56148440004ff755922001cfe7559220004fd755922001cfc7559220026bf7459220004ff7359220014fe7359220004fd7359220014fc73592200067f53592200067d5359220006bf4359220006bd43592200cebf42592200cebd4259220004ff7159220004fc7159220024fe7059220024fc7059220026be4059220026bc4059220004ff759862001cfe7598620004fd759862001cfc759862004cfe7498620004fd7498620004ff7398620014fe7398620004fd7398620014fc73986200067f53986200067d5398620026f67198620006f65198620006f55198620006f63198620006f53198620086f62198620086f52198620024fe7098620026f61098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7458620006bf7458620004bf745862004cfc7458620006bc745862004cbc7458620004ff7358620006df7358620004df7358620014fe7358620004fd7358620014fc7358620006dc7358620014dc73586200067f53586200067d5358620026f77158620006f65158620006f55158620006f63158620006f53158620056f62158620056f52158620056ec2158620024fc7058620026f61058620026f4105862004cff76d0620024fe76d0620004fd76d062000dee72d0620005ed72d0620006f661d0620006f561d062017fe421d0620004ff7690620024fe7690620004fd769062028ebf649062004ebc6490620004ff7650620004fd7650620024fc76506200057f75506200ad7c7550620005ef725062000dec725062004cff7610620024fe7610620004fd76106200ad7e75106200057d7510620236bf641062004ebc6410620006f66110620006f56110620137e42110620025fa7010620005f9701062033f6e75886200076d758862020eef6388620336ed63886203376f53886203376d538862000dee718862000fe6718862020fe66188620006ed618862020fe5618862020fea708862020de
  | 11 => 0x5fb7050940025f87050940025bc765094000ebc7650940024bc76509400073f755094035f3c755094035ebf655094035ebd6550940355bf7350940355bd735094034ebf635094034ebd635094034f3f535094034f3d535094004dbf725094004faf7250940007af625094000ebe625094000ebc62509400cfac625094000eac62509400cfae325094034fad3250940007b77150940007b47150940007bb7050940025be7050940025bc7050940007b8705094004ebf605094004fbb6050940004ff75d854001cfe75d8540004fd75d854001cfc75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d85400067f53d85400067d53d854000cfe72d8540004fd72d854000cfc72d8540006f721d8540006f421d8540006f761985400057f75585400dd7c7558540005df73585400d5dc7358540005ef72585400cdec72585400dd7e75185400057d7518540006f56118540004ff751854001cfe75185400067e751854001c7e7518540004fd75185400067d75185400047d751854001cfc7518540004ff7318540014fe7318540004fd7318540014fc73185400067f53185400067d5318540006bf4318540006bd431854000cfe7218540004fd721854000cfc7218540006bf4218540006bd4218540006f72118540006f42118540236be4018540236bc4018540024fe7690540006f76190540006f46190540025fa7090540005f97090540024fc76505400057f75505400dd7c7550540006f76150540006f4615054004fb44150540005fb7050540025f8705054004fb84050540004fe7688540004fd7688540004fc76885400dd7e75885400057d7588540006ef628854000eec6288540004ff7648540004fe7648540004fc7648540004ff75588400067f75588400047f755884001cfe7558840004fd755884001cfc75588400067c755884001c7c755884000cfd7458840004ff7358840014fe7358840004fd7358840014fc73588400067f53588400067d5358840024ff7258840026ef72588400b6ee5258840006ed525884004eef425884004eec42588400b6ee3258840006ed3258840004ff7158840004fc715884004ebc41588400b6ef2158840024fc7058840026bf4058840026bd4058840026ee2058840026ec2058840004ff759844001cfe7598440004fd759844001cfc7598440004ff7398440014fe7398440004fd7398440014fc73984400067f53984400067d539844000cfe7298440004fd729844000cfc7298440026f67198440006f65198440006f5519844004ef7419844004ef44198440006f63198440006f53198440026f61098440026f41098440004ff75584400067f75584400047f755844001cfe7558440004fd755844001cfc75584400067c755844001c7c7558440004ff7358440014fe7358440004fd735
  | 12 => 0x75358640006f65358640006f55358640006755358640006f453586401f6f74358640006f64358640006f543586401f6f44358640006f77258640006f67258640006f57258640006f47258640006f75258640006f65258640006f55258640006f452586401f6f74258640006f64258640006f542586401f6f44258640006f73258640006f63258640006f53258640006f43258640026f77058640026f67058640026f47058640026f75058640026f65058640026f55058640026f45058640026f74058640026f64058640026f54058640026f44058640026f73058640026f63058640026f53058640026f43058640026f72058640026f62058640026f52058640026f420586401767e65906400067d6590640006f66190640006f56190640025fa7090640005f97090640176be659064028f3e65906401763e659064028f3d659064028ebc659064028ebf639064038ebd639064038f3f539064038f3d5390640006bd629064004dbe719064028fb66190640006bd619064028fb5619064028fba709064028dbd7090640007b9709064004ebe60906400057f75506400f57c75506401667e65506400067d6550640006f66150640006f56150640005fb7050640025f87050640235bd761064004ebd761064004f3e751064004f3d7510640146be65106402373e65106401463e65106402373d6510640236bc6510640236bf6310640386bd63106403873f53106403873d5310640006bd621064004fb67110640237b66110640006bd6110640237b56110640006b5611064037fb7211064037fb4211064004dbf7010640235bd701064004fba6010640004ff7688640024fe7688640004fd76886400f57e75886400057d758864012e7e65886400067d6588640006f66188640006f56188640004ff7648640004fd7648640024fc764864011e7e65486400067d6548640005bf744864004dbc7448640006f66148640006f5614864000cfe76d89400ceee62d8940004ff75d894001cfe75d8940004fd75d894001cfc75d8940024fd74d894000cfc74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400067f53d89400067d53d8940006bf43d8940006bd43d89400ceee42d8940004fe71d8940004fd71d89400ceec21d894004cfd70d89400ceef20d89400057f75589400dd7c7558940005df73589400d5dc73589400ceec6258940005f77158940005f47158940005be76d094004ebe76d0940376bf65d0940376bd65d094004dbf73d094036dbd73d0940366bf63d0940366bd63d09403673f53d09403673d53d09400cdbd72d094000ebe62d094000ebc62d0940025be70d0940025bc70d094004ebf60d094004fbb60d0940024fc76509400057f75509400dd7c7550940006ef625094000eec6250940005f77150940005f47150940
  | 13 => 0x96400267c30596400267f20596400267e20596400267d20596400267c20596400267f10596400267e10596400267d10596400267c1059640004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40004ff7358a40014fe7358a40004fd7358a40014fc7358a400067f5358a400067d5358a40026ef7258a400e6ee4258a400e6ee3258a40006ed3258a40004ff7158a40004fc7158a40024fc7058a40026bf4058a40026bd4058a40026ee2058a40026ec2058a4000cff7650a400057f7550a400f57c7550a4019e7e6550a400067d6550a4000eee6250a40006ed6250a4004fac4250a40005f77150a40005f47150a40005fb7050a40025f87050a40004ff759864001cfe7598640004fd759864001cfc7598640004ff7398640014fe7398640004fd7398640014fc73986400067f53986400067d539864000cfe7298640004fd729864000cfc7298640026f67198640006f75198640006f65198640006f55198640006f45198640006f73198640006f63198640006f53198640006f43198640006f72198640006f42198640024fe7098640026f61098640026f41098640006f77598640006f67598640006f57598640006f47598640006f774986401cef67498640006f754986401cef65498640006f554986401cef45498640006f77398640006f67398640006f57398640006f47398640006f75398640006775398640006f65398640006f55398640006755398640006f453986401cef74398640006f64398640006f543986401cef44398640006f77298640006f67298640006f57298640006f47298640006f75298640006f65298640006f55298640006f452986401cef74298640006f64298640006f542986401cef44298640006f73298640006f63298640006f53298640006f43298640026f67098640026f57098640026f47098640026f75098640026f65098640026f55098640026f45098640026f74098640026f64098640026f54098640026f44098640026f73098640026f63098640026f53098640026f43098640026f72098640026f62098640026f52098640026f42098640004ff755864001cfe7558640004fd755864001cfc7558640004ff7358640014fe7358640004fd7358640014fc73586400067f53586400067d5358640004ff725864000cfe725864000cfc7258640026f77158640006f75158640006f65158640006f55158640006f45158640006f73158640006f63158640006f53158640006f43158640006f72158640006f42158640024fc7058640026f61058640026f41058640006f77558640006f67558640006f57558640006f47558640006f574586401f6f47458640006f754586401f6f65458640006f554586401f6f45458640006f77358640006f67358640006f57358640006f47358640006f753586400067
  | 14 => 0x67f31597400067e31597400067d31597400067c31597400067f21597400067c215974010e7f70597403b67e70597400067d70597403b67c705974004e7f405974004e7e405974004e7d405974004e7c40597400067f30597403b67e30597400067d30597403b67c30597400067f20597403b67e20597403b67c20597403b67e10597403b67c1059740004ff7558b4001cfe7558b40004fd7558b4001cfc7558b40024fc7458b40004ff7358b40014fe7358b40004fd7358b40014fc7358b400067f5358b400067d5358b4004ebf4358b40006bd4358b4004eef7258b4004eef4258b4004eec4258b400feee3258b40006ed3258b40004ff7158b40004fc7158b400feec2158b400feef2058b4004dbf7650b400b6bf7650b400073f7550b403af3c7550b4004ebf6550b4004f3e6550b403aebd6550b4004f3d6550b400063d6550b403a5bf7350b403a5bd7350b4004ebf6350b4039ebd6350b4039f3f5350b4039f3d5350b4004faf7250b4000ebe6250b4000ebc6250b400ffae3250b4039fad3250b40007b77150b40007b47150b40025be7050b40025bc7050b40004ff759874001cfe7598740004fd759874001cfc7598740024fe7498740004ff7398740014fe7398740004fd7398740014fc73987400067f53987400067d539874004ebf4398740006bd439874000cfe7298740004fd729874000cfc729874004ebf4298740006bd429874004ef6719874004ef7419874004ef4419874028ebe409874004ebc4098740004ff755874001cfe7558740004fd755874001cfc7558740024fc7458740004ff7358740014fe7358740004fd7358740014fc73587400067f53587400067d5358740004ff725874000cfe725874000cfc725874004ef7715874004ef7415874004ef44158740004ff768874004cfe7688740004fd768874010d7e75887400057d758874012e7e65887400067d658874000eee6288740006ed6288740004ff7648740004fd764874004cfc764874011e7e65487400067d65487400f67f74596403967e74596400067d74596403967c74596400067f73596400047f73596400067e73596400067d73596400047d73596400067c73596403967f43596400067e43596400067d43596403967c43596400067f72596400067e72596400067d72596400067c72596403967f42596400067e42596403967c42596400067f32596400067e32596400067d32596400067c32596400067f71596400067e71596400067d71596400067c71596403967f41596403967c41596400067f31596400067e31596400067d31596400067c31596400067f21596400067c21596400267f70596400267e70596400267d70596400267c70596400267f40596400267e40596400267d40596400267c40596400267f30596400267e30596400267d305
  | 15 => 0xd755822101cfc7558221004ff745822104cfc7458221004ff7358221014fe7358221004fd7358221014fc73582210067f53582210067d5358221056ee3258221006ed3258221056fa205822120eec205822112d7e75182210057d75182210067e65182210067d6518221026fa6018221006f9601822104cfe76d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121006bf54d9121006bc54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d91210067f53d91210067d53d9121006bf43d9121006bd43d912116cff72d912116cfd72d912116ebf42d912116ebd42d9121024fe70d9121004fd70d9121006bf6499121155f5719912117ef761991210057f755912111d7c755912117df77159121004ff75591210067f75591210047f755912101cfe7559121004fd755912101cfc75591210067c755912101c7c7559121006bf7459121004ff7359121014fe7359121004fd7359121014fc73591210067f53591210067d5359121154ff7259121006ef725912117cff7159121006f7715912117cf77159121004ff7059121024fc705912116cfe761912111d7e75191210057d751912104ebe6419121006bd6419121136f7611912100cfe76d052100cfc76d0521006bf64d052104ebc64d052100dee72d0521005ed72d052117ef761d0521134fe769052104ebe6490521006bd649052104cff765052100cfe7650521154fd765052100cfc76505210057f755052111d7c7550521006bf645052104ebc6450521005ef725052100dec725052116cfe761052111d7e75105210057d751052104ebe6410521006bd6410521136f761105213c76e75885210076d75885213beef63885213beed63885213bf6f53885213bf6d538852100dee718852100fe6718852100eef618852100fe76188521004ff75d812101cfe75d8121004fd75d812101cfc75d812104cfe74d8121004fd74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d8121086fa20d8121006fb60981210057f755812111d7c7558121005bf7458121005bc7458121005df7358121115dc735812111d7e75181210057d751812120eef6218121026fa6018121006f9601812104e7f745974004e7e745974004e7d745974004e7c74597400067f73597400047f73597400067e73597400067d73597400047d73597400067c735974004e7f435974004e7e435974004e7d435974004e7c43597400067f72597400067e72597400067d72597400067c725974004e7f425974004e3f425974004e7e425974004e7d425974004e7c42597400067f32597400067e32597400067d32597400067c32597400067f71597400067e71597400067d71597400067c715974004e7f415974004e7e415974004e7d415974004e7c4159740
  | 16 => 0x804104eb84058041006fa3058041006f930580413d57f765962112e7f765962101c7f76596210057f73596210057d73596210067f63596210067e63596210067d63596210067c63596213cf6e32596210076d32596213cf6f21596213cf7721596213cf7421596213cf6c20596210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210067e43596210067d43596210067c43596213ce7f72596213ce7e72596213ce7d72596213ce7c72596213ce7f42596213ce7e42596213ce7d42596213ce7c42596213ce7f32596213ce7e32596213ce7d32596213ce7c325962112e7f71596213ce7e71596213ce7d71596213ce7c71596210067f31596210067e31596210067d31596210067c31596213ce7f21596213ce7e21596213ce7d21596213ce7c21596210067f70596210067e70596210067d70596210067c70596210067f30596210067e30596210067d30596210067c30596213ce7f20596213ce7e20596213ce7d20596213ce7c205962112d7e75d92210057d75d92210067e65d92210067d65d9221135f671d9221004ff75d922101cfe75d92210067e75d922101c7e75d9221004fd75d92210067d75d92210047d75d922101cfc75d9221004ff73d9221014fe73d9221004fd73d9221014fc73d92210067f53d92210067d53d9221006bf43d9221006bd43d9221006ed72d922116eee32d9221006ed32d9221134fe71d9221006f671d9221134f671d9221024fe70d9221004fd70d9221154fd76992210067e65992210067d6599221006bf649922117ef6619922104cff76592210067e65592210067d6559221004ff755922101cfe7559221004fd755922101cfc7559221006bf7459221004ff7359221014fe7359221004fd7359221014fc73592210067f53592210067d5359221156bf4259221156bd4259221156ee3259221006ed3259221004ff7059221024fc705922112d7e75192210057d75192210067e65192210067d651922104ebe6419221006bd641922116df67119221136f66119221154fd76d062118e7e65d06210067d65d062117ef661d062100cff769062100cfd76906211767e65906210067d659062104ebe6490621006bd649062100dee7290621005ed729062117cff76506210057f755062112d7c75506211667e65506210067d655062100cff761062100cfd761062104cfc761062112d7e75106210057d75106211467e65106210067d651062104ebe6410621006bd641062100dee7210621005ed7210621136f6611062112d7e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb60982210067e65582210067d6558221004ff755822101cfe7558221004f
  | 17 => 0x67c6558141005df735814115ddc7358141005ef7258141155ec72581410067f65181410067c651814128ebf6418141026fa6018141006f9601814104e7f74594411463f745944104e7e745944104e7d745944104e7c745944104e3c74594410067f73594410047f73594410067e73594410067d73594410047d73594410067c735944104e7f435944104e7e435944104e7d435944104e7c43594410067f72594410067e72594410067d72594410067c725944104e7f425944104e3f425944104e7e425944104e7d425944104e7c42594410067f32594410067e32594410067d32594410067c32594411467f71594410067e71594411467d71594411467c715944104e7f415944104e7e415944104e7d415944104e7c41594410067f31594410067e31594410067d31594410067c31594410067f21594410067c21594410067f70594410067e70594410067d70594410067c705944104e7f405944104e7e405944104e7d405944104e7c40594410067f30594410067e30594410067d30594410067c30594410067f20594410067c2059441004ff755884101cfe7558841004fd755884101cfc7558841004ff7358841014fe7358841004fd7358841014fc73588410067f53588410067d535884104ebf4358841006bd435884104eef725884104eef425884104eec4258841136ee3258841006ed3258841136f47158841136f72158841136ec2158841136f42158841004ff7058841024fc7058841136ef205884104dbf765084117ebf76508410073f7550841145be7550841145bc75508414173c75508411453c755084104ebf655084104f3e6550841416bd655084104f3d65508410063d655084140dbf735084140dbd735084104ebf6350841406bd63508414073f53508414073d535084104dbf725084104faf725084100ebe625084100ebc6250841137ae3250841407ad3250841005bf7150841007b77150841005b77150841137b4715084116ebe615084104fb66150841137b72150841137b42150841235bc705084104dbf7650441006bf7650441004bf76504410073f7550441145be7550441145bc75504413ef3c75504411453c755044104f3e655044104f3d65504413fdbf73504413fdbd73504413e73f53504413e73d5350441005bf725044104dbf715044104fb771504413f6be615044104fb661504413efb651504413efb551504413e7b731504413e7b431504413dfb721504413dfb42150441235bc7050441004ff755804101cfe7558041004fd755804101cfc7558041004ff7358041014fe7358041004fd7358041014fc73580410067f53580410067d535804104ebf4358041006bd4358041004ff725804100cfe725804100cfc725804104ebf4258041006bd425804104efb705804104efb405804104ebc405804104ef8405
  | 18 => 0xf75582411757c7558241004ff75582410067f75582410047f755824101cfe7558241004fd755824101cfc75582410067c755824101c7c7558241004ff7358241014fe7358241004fd7358241014fc73582410067f53582410067d5358241006bf4358241006bd4358241004ff725824100cfe725824100cfc7258241006bf4258241006bd42582411f6f741582411f6f441582411757e75182410057d7518241026fa6018241006f960182411657e76d95411667e76d954101c7e76d95410057f73d95410057d73d95410067f63d95410067e63d95410067d63d95410067c63d95410067e62d95410067c62d954142f7741d954142f7441d95410067f74d954142e7e74d95411667d74d954142e7c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d954142e7f43d95410067e43d95410067d43d954142e7c43d95410067f72d95410067e72d95410067d72d95410067c72d954142e7f42d95410067e42d954142e7c42d95410067f32d95410067e32d95410067d32d95410067c32d954142e7f71d95411667e71d95411667d71d95411667c71d954142e7f41d95411667d41d954142e7c41d95410067f31d95410067e31d95410067d31d95410067c31d95410067f21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d954142e7f40d954142e7c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f20d95410067c20d954100cfe76d89410067f65d89410067c65d8941156ee62d8941004ff75d894101cfe75d8941004fd75d894101cfc75d8941004ff73d8941014fe73d8941004fd73d8941014fc73d89410067f53d89410067d53d8941156ee42d8941156ee32d8941006ed32d894104cfd71d8941156ef21d8941024fe70d8941004fd70d8941156ec20d89410057f75589411657c75589410067f65589410067c6558941156ec625894100cfc76509410057f75509411657c75509410067f655094119e7c6550941006ef625094100eec625094104fac4250941005f77150941005f471509410067f65905411767c659054104df6719054104ef761905410073f6590541176be6590541176bc65905414273c65905411763c659054141ebf639054141ebd639054141f3f539054141f3d5390541006bf629054104dbe719054104ebf619054104fb761905410067f65d81410067c65d8141004ff75d814101cfe75d8141004fd75d814101cfc75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d81410067f53d81410067d53d814100cfe72d8141004fd72d814100cfc72d81411cef741d81411cef441d81411657e75981410057d75981410067f65981410067c6598141006fb60981410057f75581411657c75581410067f6558141
  | 19 => 0x8142006bf43d8142006bd43d814204cfd72d81420feee32d8142006ed32d8142004fe71d8142004fd71d8142006fb30d8142006f830d81420fefa20d814219d7e75981420057d75981420067f65981420067c6598142005f67198142005f57198142006f76198142006f46198142006fb60981420057f755814219d7c75581420067f65581420067c6558142005df7358142195dc7358142005f77158142005f47158142006f76158142006f461581420067f65181420067c6518142006f76118142006f46118142026fa6018142006f96018142004ff7558b410067f7558b410047f7558b4101cfe7558b41004fd7558b4101cfc7558b410067c7558b4101c7c7558b41004ff7358b41014fe7358b41004fd7358b41014fc7358b410067f5358b410067d5358b4104eef7258b4117eee5258b41006ed5258b4104eef4258b4104eec4258b4117eee3258b41006ed3258b4117ef77158b4104ebc4158b4117eef2158b4117ef72158b4117ef42158b41004ff7058b41024fc7058b4117eec2058b41004ff755834101cfe7558341004fd755834101cfc7558341004ff7358341014fe7358341004fd7358341014fc73583410067f53583410067d5358341004ff725834100cfe725834100cfc725834104efb705834104efb405834104ef840583411757e75d8a410057d75d8a4116eee62d8a4100cff7658a4116eec6258a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41004ff7358a41014fe7358a41004fd7358a41014fc7358a410067f5358a410067d5358a41006bf4358a41006bd4358a4116eee4258a4104cfc7158a4116eec2158a41004ff7058a41024fc7058a41005bd76d0a4104ebd76d0a41175be75d0a4104dbc75d0a41476bf65d0a41476bd65d0a4104dbf73d0a4146dbd73d0a41466bf63d0a41466bd63d0a414673f53d0a414673d53d0a4100ebe62d0a4100ebc62d0a41005bd71d0a4104fb661d0a4128dbe70d0a4100cff7650a410057f7550a411757c7550a4100eee6250a41006ed6250a41005f77150a41005f47150a4116dbf7650a4100ebf7650a4100cbf7650a410073f7550a41175be7550a41175bc7550a4145f3c7550a411753c7550a4145ebf6550a4145ebd6550a41455bf7350a41455bd7350a4144ebf6350a4144ebd6350a4144f3f5350a4144f3d5350a4104dbf7250a4104faf7250a4100ebe6250a4116fae6250a4100eae6250a41007ad6250a4100ebc6250a4116fae3250a4144fad3250a41005bf7150a41007b77150a41007b47150a4104ebe6150a4128dbc7050a41005bd76d064104ebd76d0641175be75d064104dbc75d064104dbf73d0641445bd73d064143f3f53d064143f3d53d0641005bd72d064104fb661d0641437b651d0641437b551d064128dbe70d0641006fb60982410057
  | 20 => 0x17ef752d854217ef652d854217ef552d854217ef452d854217ef742d854217ef642d854217ef442d854217ef732d854217ef632d854217ef532d854217ef432d8542006f770d8542006f670d8542006f570d8542006f470d8542006f750d8542006f650d8542006f550d8542006f450d8542486f740d8542486f440d8542006f730d8542006f630d8542006f530d8542006f430d854217ef720d854217ef620d854217ef520d854217ef420d854219d7e75985420057d75985420067f65985420067c6598542006f761985420057f755854219d7c75585420067f65585420067c65585420067f65185420067c6518542006f56118542004ff751854201cfe7518542004fd751854201cfc7518542004ff7318542014fe7318542004fd7318542014fc73185420067f53185420067d5318542006bf4318542006bd431854204cfd7218542136ee3218542006ed3218542006f75118542006f65118542006f55118542006f45118542006f73118542006f63118542006f53118542006f43118542136f52118542024fe7018542004fd701854217df67618542006f67618542006f76518542007776518542006776518542006f66518542006f56518542006f46518542007746518542006746518542137b77418542007b65418542007b55418542006f76318542006f66318542006f56318542006f46318542007775318542007755318542007b74318542007b5431854247fe74218542137b64218542137b44218542137e44218542137e63218542007e53218542006f77518542006f67518542006f57518542006f47518542136f7741854247ef67418542136f57418542136f47418542006f7541854247ef65418542006f5541854247ef45418542006f77318542006f67318542006f57318542006f47318542006f75318542006775318542006f65318542006f55318542006755318542006f4531854247ef74318542006b74318542006f64318542006f54318542006b5431854247ef44318542136f77218542136f67218542136f47218542136f75218542136f65218542136f55218542136f45218542136f74218542136f64218542136f54218542136f44218542136f73218542136f63218542136e63218542136f53218542006e53218542136f43218542006f77018542006f67018542006f57018542006f47018542006f75018542006f65018542006f55018542006f4501854247ef7401854247ef44018542006f73018542006f63018542006f53018542006f43018542136f72018542136f62018542136f52018542136f420185420067f65d81420067c65d8142006f761d8142006f461d8142004ff75d814201cfe75d8142004fd75d814201cfc75d8142004ff73d8142014fe73d8142004fd73d8142014fc73d81420067f53d81420067d53d
  | 21 => 0xe7558342004fd755834201cfc755834200cfc7458342004ff7358342014fe7358342004fd7358342014fc73583420067f53583420067d535834204ebf4358342006bd4358342004ff7158342004fc715834204efb705834204efb405834204ef840583420cefa205834249d7e76d954219e7e76d954201c7e76d954248f3f74d954248f3c74d95420057f73d95420057d73d95420067f63d95420067e63d95420067d63d95420067c63d95420073f43d95420073d43d95424976f42d954248f3e42d954248f3c42d954248f6c42d954248f6e32d95420076d32d954248e7f74d95424967e74d954248e7d74d954248e7c74d95420067f73d95420047f73d95420067e73d95420067d73d95420047d73d95420067c73d95424967f43d95420067e43d95420067d43d95424967c43d954248e7f72d954248e7e72d954248e7d72d954248e7c72d954248e7f42d954248e7e42d954248e7d42d954248e7c42d954248e7f32d954248e7e32d954248e7d32d954248e7c32d95420067f71d95420067e71d95420067d71d95420067c71d95424967f41d95424967c41d95420067f31d95420067e31d95420067d31d95420067c31d954248e7f21d954248e7e21d954248e7d21d954248e7c21d95420067f70d95420067e70d95420067d70d95420067c70d95424967f40d95424967c40d95420067f30d95420067e30d95420067d30d95420067c30d954248e7f20d954248e7e20d954248e7d20d954248e7c20d95420067f65d85420067c65d8542004ff75d854201cfe75d8542004fd75d854201cfc75d854217ebd74d8542004ff73d8542014fe73d8542004fd73d8542014fc73d85420067f53d85420067d53d854204cfd72d8542006f751d8542006f651d8542006f551d8542006f451d8542006f731d8542006f631d8542006f531d8542006f431d854217ef621d8542024fe70d8542004fd70d8542006f765d85420077765d85420067765d8542006f665d8542006f565d8542006f465d85420077465d85420067465d854217fb574d8542007b654d8542007b554d8542006f763d8542006f663d8542006f563d8542006f463d85420077753d85420077553d8542007b743d8542007b543d8542487e742d854217fb642d854217fb442d854217fe442d854217fe632d8542007e532d8542006f775d8542006f675d8542006f575d8542006f475d854217ef774d8542486f674d854217ef574d854217eb574d854217ef474d8542006f754d8542486f654d8542006f554d8542486f454d8542006f773d8542006f673d8542006f573d8542006f473d8542006f753d85420067753d8542006f653d8542006f553d85420067553d8542006f453d8542486f743d8542006f643d8542006f543d8542486f443d854217ef772d854217ef672d854217ef472d8542
  | 22 => 0xa0070000034000004002804c00a0010088000002001000803402000300f800001000100e00180000000008000002001000000400000000c001c000000009000c04600900a80040060170048004000000002802400400000e0004000000000002802e00100000180140000028008010000004800400001f00b800c004019000801800e00b0080020004000010002c02000b00280040000090078000000002000000c00c00b000801004800600f804c016000008000001800200680240000010018014054005001003001e01a002000400200000200500000230040088014000003000800800200100000080120018008032000000003801000300080000040050070000000002004811400000d00d004000000300400080000070010010008000017000006800600b0000002000006002c01e0060020048000006005800000001b0078004036002004000006000500f0020002003003803800a028006800402600e004800401c000000804c0040000040030012002000800000001401500040c6006006800001c007000001400e02500000140000000030004006000000800c020000000004802c017003800004402e00b001000602f0100020002007004000400603a0058028002011000001001a017016004c00000300280040060110000008000011000000810800e001002c00c00b002814402000a014001001e00300300440060110008040014006011803001c00500f000c000012000800403a00e001801000c041004008c008002005802c00400a002001400602a00000240080000010018038000000000007600b000804c054003002804c00a002003006800400a001001c004001008001401400001080000040110000024072010003800001c059000000401c00f001805800a006002000800000001080180280040010018000000008001c00c003000801c0040090060010008000002802400401200180700000020018000008010005800001e009011800000401b002000000c005006800400001d002800806a0000020020002000004ff759874201cfe7598742004fd759874201cfc759874200cfe7498742004ff7398742014fe7398742004fd7398742014fc73987420067f53987420067d539874204ebf4398742006bd439874204ef6719874204ef7419874204ef4419874216ef52198742024fe7098742004fd7098742004ff75587420067f75587420047f755874201cfe7558742004fd755874201cfc75587420067c755874201c7c755874200cfc745874204ebc745874200cbc7458742004ff7358742014fe7358742004fd7358742014fc73587420067f53587420067d535874204ef7715874204ef7415874204ebc415874204ef4415874204eb44158742156f62158742004ff7058742024fc7058742004ff755834201cf
  | 23 => 0x100e80a4008006003004c0120080020038000001003802c030000004801401400500c00000580040000058000004000000003e02600000080240040000010032000008806000600200700200160000000000034001006000000e005005800c0000000000044000001004003801e000009005805c01a000000000000300a000800802900c8010032000001805801200400180b000a000003800c00400500f800c008000000000400000a0028030000010000000000000c000002800400500500080060020000020000003000000800c023009000c00600200a81b0000009001811c00400000b00880080000008078002009000002000000000300000000010058000030001006000002c00100000000000000070000000001007801800400000100100140000000014004017002000c0020010018014028008000018802200d0008068000009002001801800101c807c00400c00200040000030028004044001000000005e0000000000004010003001c000000001800801800c002000003000901c8008018003000000c000009007805401400c00d0014012000000000801e002001800c00a019000005c000000001801c01c00000180000280020008000006000008000002200b00000080080410000070002002000000c00a000001800800001e0008000008000008800c0140000028000000011000802c000014003000000a0000008000004000008802c03600b0008000018000005000c00c006000001c04601b003000c00c003000000c002016006801800001a0120110000008002001000204f004000001400801d00000040060028010016003000800400000000100180000000008000004000004809801000a000003800002b000008800e00e000804400c00b003800c00003d0020000000001002002400e00002a00680200010000000014000005000800600500000140280170090000002006000002c0220040030144008001002003802e002000000400c020004800400600f0050004034002002801000400300500040000010058004002007006800004c022000000c004000005800400e000003801c00a009002800002400f001000801e0010098178008010002001002800d01b000009000900080380000010068014000000002804000002e0000068002009000000c00e00f000000003000300603840000130020000000003002800001e00004280e400400900100100180020018024002002008800400a00002f800c0100000010000012000000804c04c014000000800000000080300280060040000006000002800003000400000000780080018000004001000000000a007001002401e00100200000060020000048008004001001402800800101b0002009001800c0020350028014000003007004000000001180000220020058
  | 24 => 0x6ba068175a1692b3a70486c2b647ba714d9e66f4c4167da3c80420f8900e8e0cc6fe09514a8a5358980014649276a030745ceecf0000001a08e0d0001a8599ac9049d03991d6b8a74b25911e87d75760418aa264016b86e0388e1b2f631b03c657c3aa0e4c1c0a2e254a3e9d14b8d19421581ce0f173690fd20caf525db3041e47511982061b50cce3f5a994fd49696b38a8d5004895b7248000000075d32d8d8c2ff1d90ad40000dc0b5af180009a917d17388f63922b905f54fc91b59934d504accb1bca44477678d0bd80011c4459256334c84c00030db40d2a82cf00017692600002bd2da4000afd46993e984e0000000a9db128b2480800121ed7a0000aa8b725fd0001b1c2d80003f20ab8becd96678b06c924eb75dc23049f0d6e5fc37256025f3000000000000026f33a496c5fa6e325e52766790a7000000024f67530e188296f09d37b02826e40c08001cbc30b00000000005a0567000065835203800007ec02737b2605cec9aa00011d53e2b5b0a7a2dca3a85d3a28b94e9a3646d29755a9882d2dfb6452ba73967c14600bc4eb6e9009071c2c361d2668b1000000014105fa21244197245aa94836006c929c2ca1ee868544c4090002bfc864c88000000010e0003020000a2630218ea5a996e71424227d08f80002da844d39e0000001848000ca500022913384201560001792c5734c80002ca0000000a846340002e99d91a6e3a71c3ac6c216000000274c38a000000225400028200006d865680d00000000003a4259269d2bce295e7800084ec3e00022c005a21b71a8f482300001be0a1d26c7cd72d91ac23400054f0c1138849873b81fd09e0003911904000aac0002fa918a7a313429d5118ab91ad8ed40006a71f9b74c062e32041b72917698a3bc9aed156a5b25b800189c0003eb39640003e61f8000076e92669c2d0000000060b3908e24e3c0d52efc856000000252cf560b1353384c00080a0000001af04c15aa8b689ecb3d00015ed71eabb55a17e55367340000ea40003cb3c20379c6e000529000202c000800000a012003803c0020000110000000001000000400400d00a804c00000000480240020000040028032000001009401e00e000006c03800100300580060050000018000022000000005001d00000d002c0060000004000000002001c06200e01c80080000060000000014000006800c006003000002000200a022001000c0020018018014002003804402000700c800802601200e8004000002003802801200b001000c0100320008058048000004001000e00a00400000480060000004008026005801c00a000006002001a023000801c03201b00680640060000008020002021001000001e0010030000004000001800c00601c0000008000000000000c0060000000008006002003002c00a047000001000c
  | 25 => 0xc000cf56f28000000a74000000034ea254e639e40003c94533b0132c6bc183000142aaba32e06409cc1970d61d680000002d780000c60000000001b4c8f50001dbdaee620731a1acb1847924289b418a37850e9d54000cd40a98000c9c0000002e18cc05e50a20000000000000000000021d0002ff59400ca4d200006322813c608a561600748982f800096d6f0800173071a1f7000194c2860000a8169aad1521a8680006ea65d80000002b14cd8fedcd880c4780c0c7469b15a582a1a8200045a29709ac000000000154a00000025d0a4e32025cb7fc6ba5ca3dcb6c06220004fc34307d084e24580009d20003888d5c000dd500017600004d361a33dd2528ad004b1bc7507321b1b1c00002ec2370000024c9273817a4000d8351a8000f5e0fc21f00004fe3e20001c8000081320d9ff0e90d852c48001afe38668b9bd150e4f500025a1ca4b21265b1c8000d2b26787c596675d000224ce12c020002e5149a23e4b033814749d56548000858bef37834f95de0a40000000eec2d10002b5844800014c00019f400045c91404720006912cf13d6ec90e599e80b6a2a428aa405ba72625e9c2048481975b07f80e200018f99e0000c2d42c0000000000651356c000c5d5378000000a63313880d396b5d00000000000001cd23800001ad69a295dc0e0182bb8ceccfa0000003078a4800000018700000ea5522f44c3c00019a188c00000036f1fbd8920005fc800022c65a0001c58ef60390cb33bca1a0005d7adc068a3bf23ea149d8281c00000000004470aba2f4000a181880e459fa1740ee80011340003340000000000129940cdfa9fb0001a3078c00001ab1e1d840bb5a81d8944e62e0c48c20438b7f1cdb4819fcd6c5ed09c83bc23f000000000084c0b3a1a9cd0b1e23180001180d132200000006b43d920c0000000054b8600009ed3660000b90347194ae315e4000086b73d8c4b364ad9a040267ce000188436ebd53a7b518cc660a2c59570a1408b119000113e6ff08727c824427824080003d6000000223d2e63891d982c007877032129453188b6561048c7003c36213af06180f53cc0350d887174d82e7c00080206d98d4630d0927bba6ca0ae224d287b1abcdf6685b3d9d529ef232084164459d4e49365800cac76836b4fa461d1d1242048236a5539010e1e5b613e1ecd796077171b2e551e10a36733e416864a3999b800006d80c6b1d1c04db91c200c122e7d31f688641be00009a00013b87c500000000000006db17ac000cbc0002228000b2900004e4000bba0001fa4adcb930003178130269112a50405260e00019480004865bd874593a7740000001598e2c2362fb136c6a34f380000000000000000d44d981461df18f8eaa7009b519ceb9d0e1b1a1da4a581c68d08b708d9596b7083a419b51ba49441a16a2e5b9984be983
  | 26 => 0xa225b0ec4661fd3c90e985de9c71601ed04b086339d825d4f4dc10948acd054ad017f32140580401293b39d10d152b825e16128641011ed973c06e655b37033a00025f80014380b2587b5700008ec3a33435a5059832487a11e2d754b1b6e06e01196b02a190421bc0f69cad05ebcd56305e4000d13137983c48e00000000000006003cf80000004a363187ed06a008450235dd58543268b2f9818ce318986f49e8c452e7b6c8670e4d0002660e42b0343a1600770a213e5b4d92d8b020428541906cba12da4483cae5a40e975d16a39d5893468036a3e62d1ab59869c02a4b5edc60d805518d2dbba8616882a846accb559580000006a4583085128cb575d28000170e3a451814028a52003c8b784fc00000018c8000c99000185c39c97000006c47c2d6544b1f6d32acc45408f583a6000191bb1932e37e16d8dc91805c66331448b48c2c206800156e93d42fb2c4d52c6a7132dc8e325595c08001dae13c178ad1d2a48f30f010143303941fd361dac433d0d993ed492b921629ae96d03152de9ee138c15554b8fd18243ad62027913728376ac029512422e03d9644cbcd1674e9ef8128b3a0719ec4790e4f1a2123ce2612802e83a054abbb752a059ab425774ca6c8b4c43b029a11c6aa4882ef33b908639f5cb03b81ba5ef4a205901e6a4515e261024031e54f99546b002e67107b815e2364a398f538492433fa8182bed825f38f815e289b2a816dda1e4151711c4016abd27243ae057aaf470d27fdc3c7bc02c34c1ab24781a68f8cb28ac11d5352c62e0000b004c0fe8b7421d26f1c704e8440adad82e3a10001a94f5c0003f129f1b42bce4199c6c5c0a6c7310000000eb21a4ba7d812e1c47e07cda3698601f18d81a6ecd0251cb47f83d831300001ee0000002fad54ca673578000000b281358000f74000530aae07a81460002cbca8c000296a1a17b20000a921b5a14ac90000000000000554b375a0ac2b0152be83ee4803239a21340e0421201d46822806a999c89e0d944db992c0001d400020454689ab71d85cc9e67990000001b187e04259b2400024e2ee2ac50aa7422fda3294e45e826631617ba06238fa274266c0764b80018ce61f0002b2d8da9f9060160400045a00007c0000000000000000051502a000157c29e71a000000000024d24dc000023656af2800000003e1c8c00000000000000000e935f37d5bfa6284f08000f3c2080081854000000000092cfc26480001a8119a06f75221dd59e4d043a9acc334c2972f9094c5ee86176888c00025a07a2fb48bcde21b691d0c9a42942a201c11ca94675a3a567eaeb15400002ccb7c1b7800175034000026bcd6cdf9000030c190d9a68c2acc0000002838cf80002933a50000000bfb247308000076a53306d5b269f30ba914d01085303394012cc78e54d1d258644993f6863
  | 27 => 0xbdb3ce335cddad0000001e8bf0be023f0000ed844a2212fd0e7030500020490bcdab2858000b0a51a04e915cfbe87168e08f4974adb5a79a6911c1a86cba8480000002f700000006ca233a9fd0fab5e06714fc000d9f6a5222d0fc43448594ecb460000d4ab2905058f3112a214d6536000194c83ce7339d2b8547ed2a403226149ee3e37485e8c22df25c8bab81245d172b0420c0600005037905cc12e10d14b118c4c5761b39439a0f93af941800070427f85f0000000584366dbee00025110480000001be80000008d2666312d630eb54c9905cb626057170000a447d10000000f6a5ed2e0a278a4cbfe224800181c84659385fc000a1f0000000c600000000000fea2bf0000000000a42000113000000000012cc00041453b80310b41623fd21ec00086c02299cc6869f50000388000000193a1080002665fbb99c6be16309620691626ef006b1ed8a891e5a60f3503c0005b290700003b1000143c8860cd56e80001dad4f52201cc0007241a7800010800000036ec0008603ec357c00033c6171b6c880b05000000139cbf32063321a5c5c404791747d468b00cb83cfb2866386ba4c7b46016f8068cfb419900019dd7b09de48a95d8c6e82e000288ca743c70003b10bb630a5ef80014a0760741800000024800021bc6d2b25250ab8caf00004951ff50ec00000000c9cdc76642e01b1ca20002b306200980000002a313c009001b0001c4a0006da38ad68aced665126c0b2bff50f3a056b8bd33a701e0efc9160e0a980ff614333f092971c0913581b74f90adf14ab7b442e1b464688b5b804513198000704c1302e30d80006c8142b39044ec8455800996660011e20000000000000390402ebf20fe1be94368706d502b4f800000432ec5bf400001129e1da88cf4b125ad65c2374eb9a4947200031fa8cc00054a34116189260003478b640000004138000470adc295aa880acbe50000000cccdd900027f95b4c7161213082a86e739895add986aa3572d9d9d84836873aac1388365691c044eacd80343880000ae01e7955d97a00001c169c95ece64f40000e52ebb179ad44204cb24e90000b36b26713a2410560746182ac97461ae70700001aee125b31350d6a103381aa64782e921f63035d68ec56fa2c391a06914e1b23d902b8073f0bd441e3f75ce3a34eca6934372a081b09ee34e21884e8cd047cacc034ae916dfa2fcb641be6d1129162e2ab237aaaced0690021a0e43983612c19a1d6201da2b4898d0889d436291a925672535ebaa19e604921e8149374c98555195882c4c9505869824283b12184d542eb4947412a8dea4940ef8ffc0000001a339c907479300000018dca190322a0ceea136699800187ed3c00019f15a8c871158c718a6c2a6638e29358dcb368b620bea41820727a844019c5239b98df05085f702548b6c7
  | 28 => 0xe95e1000134cb6327c8000e98437705acf80004ad11894a88c46542c11639cfa5c53de8fc456ede009293bcb2c00a40594054ac561366b5d8f12d7e4c4b655ad2c4d211233818ed9916a1918ac8c3d750b9386d6bc504b3584188a92264065407a12607f924574c81b0881798b3890a0f4a27020864c45c2f8dd72226093897999e698453a129174406227b404c681424b937a888ac3c000000000021549f25583d49b54728bc8fcc8975d091cd76ce432c52b3459a8326448dd8e162e826d3554000905000000002a8104970001a0c0000002114c52a552a680000a2c0a00000019280005389388000000588a5253441d80000b840006c2000235000071e11802f571051619ba311b386f31a51000a4267034216792620a70e7bb5523e38162c8000b4424d0f7ba1c00049c44cadc51ac9196a21d2ca5273d21a86ed204cb464f99c4228bab47500002f03d500000015f89670f90265b3cc012a08000bc687a0002b900001d0000253c570b586463015a5ec4f1511cd413ccde459a21546c00000003054bcc03397a67c35e0bf6b22afca6a21e58a1a6d452ae225f32556709e32e6b099caecc66a813a97bc54c3ff08441d676d100ac814d2dc45bd0c98c62e19643097405ee4b010039130429a53c900cf50e953f2b5e540ec5c4f31e1cabab85230205cf8c538072826c9ce0ef7178b39926e451d813704a241a0c282b963895114eb9746cc4312a5b1d8eb23503a1aad45a638817820f039210545e02892dc0f001f9aa07063db37f00597ac0d549a9de8ee68d139637f872cb75414b57563ee083980c59d7a8220612b9c50827b4249780004be100037c59f81e262832840000006142774c867056de000000062c0239500b5cc1a24639fc0000000000001a90a001d02390732c43000268d62c5326189f05782bf50000a7d1225731308001c6c7d42bf2b158aab9532faa5871633129e00000000002d98001ae48c30a50fe51c263a51eb2c098c07d6838b9145e6c171f9dfcb8003b13298e03c88800002b982960004f2a5ec27699272e154dae029b1de2c34c30894504a47089c37520cb14828e3a55bf0ca91dcddb19faba1d38d6d00010046365a817700449a4d734ba8000b24dfb6d48c483b23b46470a0d23ade932e8d880009d970a00017a8873232b36403e76914436bc00055a1ce371cc1ab9915f143049201a00014c104c7905de30842b895f00000009beb6d0b099ed6949df6be90b437426a43e0b30de23ca0000000fc6cf212329d9ce87570001e84000410486b3c000027d7689cf099c28a13c94dd20e0001c81adc6b406d000000000028f164966409ea132aa2de00001e7316b9c4a38ca8044817d48c7e70000000bce0002f880013f4e154b8800000000000000105acba72df0f950e40002388000b8467616e369199218a00000
  | 29 => 0xbdc0000006f7800110437117a0001a4e000083ac28602bbd14c898054c4a035f98180009ae71536280007f12d511040007ee4328001c92a8435c01f9da626c3bc0ff8d3e6d92ad9f28b687720ad385c5a0ca400013c4bfe00000000015e028b4438000a722590000db99e883e045148c000c820000000dca36755709301d84d522fa0142de2440348688cae1fa0000000ed61826920a40cb2b5a4422401cf040a02a9cdc0000000001a584ce7d04661c540008670b405c54c800019d26ed7d2511502800085c53149e0000e387cc4073315798de354290e1a9ce8e2cab24484269d7650f6537c1b950a3270000b0700000000003c500027f0000da30001a193b60ab5df33015220007500be16debc731d8000f7678f2bf8a49aa8e7c31ca63cfd0377115168557a5251cc0001b204e522330d40002ea000273400065146e2758000945000198800092134195d00004ca549800149600058d348c32200043c3308872d921ae250c000bc337e3818000e0020995f5bb09385d60a71d20000000127564800000016b5a3a000253163400013143ca37d5e6000473345000040736d0601c140002a41b5d85e9807531cfc7cea5d000052009abc02a13384000b000c91f3c8544963e1151dad45976f3002cbfc4334f10000000dcd24fa52840053e00038583ec0372390000000000315000065e00053e99a80000007282410d723853429d48aca727144adf58c0ea236f860c6b29573562dcd89028e0002c65bd6170640000125a98571c8da09b61d72118ee800000020780000000004e40f40ee29d04cf05580d4c654550c3c0003e47118001a86ea35d4b7a1c5a00000017f131ac372058001cd290c4ad0b08fbabb065fa535aace4402b80000006140a88ce4fee0001640c1c0000000000000000000000000135a1ff5008000a3222250b000000000012b184cb56dc8753ab6479c29721e3759a52000138827c28060811423d9cf68f22ea1409b0282415794b9aa4d4d191375c42ce616ef17759b68fd4feba004088cb684138c1748860003a78c1834e13200002b600048823b400033226bbab4000db30000000d1c00001d20b0000d323c18eb0bc46d02f22051ca6ac73d81d7038e17e10307e09b07951deb26ce0eaea4963744bb2044444b11941000023b95c443e791040082c39402525c15a8cca4b50fa0000ba46e85c80000000c253cd9858000000434a469cd4d8d72ab5093701173831e0400000011a9f71cb00001b62cd5cc0aa0139a4bdaf80003d28118f107360001fb0d0000050612a1d16b834a10b7c1928db5d01ca0000dd04f6076c0008ef0002ba4eee00074a11a12127441af04b4f4ee1f3309e88b786246dd24c8d9694c3eaad201ac18465724cc96800061c91fcf4016e0ee0b058e6afb37b947c084be43f9843db3a0b70000861b8a3
  | 30 => 0xaed73d2ee582a8c805b2640b981d669d8dd047685b57cbac50009f70fc8f0902a90354589dc5d6797604311041867503034084b83ae08e1e287fae6f0c3262c06623c11d0000d1a54452604540004c45db80000009d1044153c00083d154ba116ee0000000fbc3285456c300018081243c00000000cfb57b256525045569ea968b608e35050d20200b4610734e4642e4628d91e9a5a22c4c73041470a4875f2024442a0f3338de89c00cf06c931c2021e65a733fd7a097736aab000ece896078f4cca0bd7186b6b1368dd4226800069875006808d04a0d3100000000004f25c3800000000006d31dc0007947599f78de400049a0000000a590f099b19a4a2435900018ac0006198000ce8000000157c0007f60001554000000608996052c00021404dc7ae5586b7a97d828bb20001a7955049702d0001a8e6692179d8c0000004440000000e316d701041a45845d51b714f67ff00012f156c8d568c9208000e850e338f430e00009c28c000052f0ac800000082000000000003650000084a7a8a20551e1433c20566f8b2d33a6020000000000a405020431734b846a48001d7e87f0000445588dda371800039014d53505b52fa0006518dfdd5e4ae704b11c0567183e38475a7e7f239f28ac41412a63f28a064a19f30d10740008ff1e62a387f000054a981c23c0005169c00f489916b1b1f40008fb2942d088607b70000700bbea4a0001db8bac3af49c9e752285d004d347cc78bae536a7d8050bfa1972c8d8949bd2f816b08a89505a22651a424ee0468120d861c25da2684da48482529df491ab6000eb731816b8b446b49541c2c437732bc3aa2132ba97dd83882315a236151401c0003a6000004e05e0ee568227a71988bdc3a97f4d993b00ca0b32582ed5788abc3ab317c7ea4526c5a5843604870391d9c00076100003e9b0880f17b9d797cc33358a95a15cae974ed18f81f083f73297a8f9254e2602375a240b95012b4db1e8386b30fc8d56b9b24f1c3914256d2dda5e862879609f8ef9a740a3557996c5a4cd65a9aa340005875100e300d6803049a3680004b16d389b8c4a6954912dd9ceaca756f1bad65872e1cf314566e8c7418a6a153044465524392a648a12aa9881c27c36b5a9cc02830e5b12004abc5f201a1c0858cda008dbb20a66c234561bec00ad452539ac5c0628d586319010218c0890f44e80db11b993902e4c6b2619ea837e2b915d355d92cb825341a514e0dce05619ac72e4706b40aec292a2c270b1d42bab974ac04ac8c25106f99b58ff28414ec21017444cd5088b1c27a8a53a98915c5015e63f95897f846d28b9bb05f8c9a59a22f866ae4a1aa38419b46e222e1eb0a68e6b0332554be8ce816c1c291520f65d984f95b03c0336a324aa4e4c17b170dd3404b07f34b0ade37b63cada8e822b060fad647be000234a
  | 31 => 0x7e800035600000f07d4fe09180001a5c00068a2d2904400000000000017ec0005a900012ecdb54c395800c29231310d4d53861000037717e2bdc59cb184a3cbe820124fc8ac39500015e40008590bb22b92f878b47f28350ae81f4f48bec0009bf0c5ae907bca3c00000001f6b2a61100009fa00015685dc000cd500038900000003dfb06580c0002c9b79c000000000306000012f27e0c01b860007478000c8a495000000c00079a0531c7558659a3d329386a2b793d680388ccb5f0410eac0006190000000ad80004738000000af80000a505d295c6c700198d275b0c72595a22ddf2c81e08564ad5000047dc0a4486fc003c7b866e000064d9162762d4a6644129f02480001d8ea3b255aa24e18a100002135c22a3159da0d115e4581848560f0ce4756b93f9d04dbd17ca8883485560000001608e401b000000000002848000000000305ac755fce646f72d90000c4c3e20ed92fcac8520b544ff0aee36984248ecb310000cd8ac60003448a901960007108fac000b89276800000029100038310a0b542e380000006f90000000c56be20000000000ecb00036dc000d266df000000038f54eaf20b740000002308dc24dd47c316d914b5633200008100000000cb400000000000014dcd7146f39516d80c6746280cf52cb80003ac00007580002fc155a6090003b58000b4328732782645e1668a7284e00003951450c9e0004a022a040e0a119205316c2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ef825d940440031d904bb280880033918b7150110004bac28e2a022000cb7641c540440019c8c438a80880021fa1b75481100062e31eea9022064c6c62dd520440cb0fd0fb2a40881921f21f654811029734106ca9022000c3f75d912044001878ebb2240880030fdd464481100061e3a8c89022000c5f75d8d20440018b8ebb1a40880031bdd76248110006363aec49022000cb464dc520440019a8c7b8a40880032d19071481100066a318e29022000ce7621c520440a58f4edb2e208814b9cd8765c411028e5d3b6c98822009cba7619310440a19b4edb1e20881073a9db62c411000e753b0c58822000b718510710440016e30b10e20880030fdd274594104b63b886e6b282096c7510dcd650412f0fb0f39aca0800317dce73594100062fc1ae6b282097c77105cd650412f8ea20b9aca0825a1fa1c73594100043f43c86b28200087d8790d65040010fd0e21aca080021f61c43594100053741086b282000a6d8210d650400147d08392ca080028f61072594100052f418e4b282000a5d831c965040010fd0e212ca080021f61c42594100052f41884b282000a5d8310965040010fd0f992ca080021f61f32594100062eb9e64b282000c5d734c965040014ef02992ca080029d20532594100043f43864b28200087d870c9650400147d08192ca080028f61032594100072699064b282095a79809c5650400f0fd0f98aca080021f61f31594100051f42662b282000a3d84cc565040014dd0598aca080029b60b31594100043f43862b28200087d870c5650400f0fd0f90aca080021f61f21594100051f42642b282000a3d84c8565040014bd0790aca080029760f21594100253d40042b282000a798008565040091790ea1ac8080023d20573588100247643a64b102002ccc734c96204001c9aa6992c40800e1f21776508100043fc2aeca10200387c855d9420405f1ef02bb284080021f61b75508100043f43acaa10200087c8759542040091790eb2284080123b21d62508100063b32ee2a102000c7565dc542040011eb0c38a84080031d99471508100063ab28e2a10208fcb6641c5420400196ac838a840809b3998871508100265d382c9208200387c85dd941040590fb0dbaa82080021fa1d655041003c3e43acaa08200387e855d841040010ff0cba882080e71d98575104100043fc3aca208200087d8759441040010ff0cbac42082531d98575884103d43fc3acb108207987d8759621040091df0eb1442080133a9c162884100063c3aeec8802000cd873dd910040018f70bbb220080031e21776440100063da9eec8802000c7953dd910040019e4a3bb220080033c54776440100063dbb6ea8802000cbb76dd11004001976ec3a2200800336ddb734401000675bb6e48802000ceb761c910040015e70ca0a2008002dce154144010
  | 1 => 0xd0db168288107399db62d051020ef1386c5a0a204fce67618b4144001cceca31682880039919462d051000752320c5a0a2000ec76318b4144001d88c6316828813f789c062d05101f65b38ec920a209a87e86dd5414410b878c9baa82880031718f755051000636316eaa0a209987e87d9541440a50f90fb2a82880030fdd764505100061e3aec8a0a2051cb870d9141440018beebb1a8288003171d7635051000637baec4a0a2000c6c75d8941440070f90b3b082880a21f219751051004e1e322ea20a2000c5c635d441440018d8c4ba882880021fe1f65105100643ec3eca20a2000c3e75d90414400187aebb208288003179d763105100062ebaec620a2000c6e75d8841440018daebb108288026ad219411051024d9a42a8220a2000e376550441440f9d28c6a0882881efa918941105101f65a324ec20a204a974865d44144093a6f08ba882880fb4d21175105101f69a322ea20a2000977835d441440012eb06ba882880035518d75105101f69ba12ea20a200097787d944144001a6aebb2082880038dd9764105100071a32ec820a2000e9463d90414408d56b0fb2082881472d61f64105101f71b3aec820a203ee3575d904144001c6ea7b2082880038d54f6410510006aabaec620a2000e9764d8c414404d1e90cb90828809ab9a1b6210510006b2baec420a2000ea764d884144001acaea310828800399d94621051000732328c420a2000ea7641884144001d48c83108288003b1d8c621051000762318c420a2000ab48650841440936690aa1082880034d5d54210510137523128420a202587c865d621440018b8c6bac42881e71b18975885100043fc3ecb10a200c87d87d96214400187cebb2442880030f5d764885100061f3a8c910a2000c3d7519221440018bcebb1c4288003175d76388510006373aec510a2000c6d75d8a21440019a8c73b442881e799189758851022cba432eb10a2000977835d621440012eb06bac42880035518d75885104c6b2312eb10a200097787d962144001cc8c5b2c42880034d5d7648851000752316c910a2000cb6761922144001a6aea3244288003a91886488510006aabaec710a2000ec462d8e21440035cd0db144288003399db6288510006b2baec510a2041ce870d8921440a58e8edb2a42880039918b654851028e5a3b6c890a2046cb4761912144001d48c43224288143351db634851000e723b6e490a2041ce476d892144083bc6e4382428800e1f21676d01100043e432eba022009c3c645d740440018b8c6bae80880031b18975d01100043fc3ecba02200087d87d97404400187cebb2680880030f5d764d01100062f3aec7a022000c5d75d8f40440018dcebb1680880031b5d762d011004e5a324e3a02200087f855d940440070f90abb2808800237e0d76501100146e41aeca022000
  | 2 => 0xe64189100053742cc83122000a6d85990624400155d09320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400155d0c320c4880032b9d8641891000717b28c83122000e2c651906244139d4f02320c488003a95c464189104e753080c8312209cea410190624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c48800393e1763189100072642ec63122000ec571d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c488002b3a0e631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000ae78158c62440014dd0a318c4880029b614631891000567430c63122000cce7618c6244001c9eca318c48800393194631891000747b20c63122000e8c6418c6244001c9d0a318c48800393614631891000762c08c63122000ec67118c6244001d8ae2318c48826fb184063189104df62080c63122000a6e86d4c62440014d90da98c4880031b9db531891000717b26a63122000e2c64d4c6244001c9ec7a98c4880039318f531891000537432a63122000a6c8654c62440018dceca98c4880038bd91531891000716322a63122000e4f6354c6244001c98c6a98c48800399196511891000752324a23122000ec463944624409f5c90ca88c488002e9211511891000752322a23122000ec46354462440015cd0d188c488003a919231189100076231c62312204fae4864c46244001d48c8988c488003b118d31189100247ac0ceda12203ecb4419db42440010ff0abb6848800e1f21576d091000c5e422eda1220008df835db42440051b906bb6848800e1fa1776509100043ec2eeca1220028de83dd942440011bb07bb2848800e1fa1676509100043ec2ceca12200087f855d942440070f90abb284880022fe1176509100046fc1aeca1220028dc835d942440011ef02bb2848800e1f21476509101347a408eca12200087e86dd54244125878c9baa84880031718f755091048e36316eaa12200087e87d9542440010f90fb2a84880062fa1f64509100061fbaec8a122000c3c75d9142440018beebb1a8488003171d7635091004c7743ec4a122000c6f75d8942440018d8ebb1284880123da1b71509100063bb2ee2a122000c7465dc54244121968c9b8a848800335d8f71509100066a31ee2a12202fce462dc542440018eeca38a84880031d19471509100065bb20e2a12208fcb4641c542440019aec638a84880033518c715091000673b10e2a122026ce4621c542440a58ecedb2e828814b5c9c365d05100071bb2ec9a0a2051db270d9341440a19acedb1e8288143749c363d0510004bbc2ae5a0a202fce4625cb414405f5c
  | 3 => 0x7b122000a6d8590f62440011dd0e21ec4880023b61c43d89100053742887b122000a6d8510f62440014df0ab8ec4880029b21571d891000557c22e3b122000aac845c7624400159f06b8ec488002b320d71d891000733a8ca3b122000aaf84547624400155908a8ec4881063ba1f31d891000476c3e63b122000a6e85cc762440014db0b98ec488002aba1331d891000556c2663b122000a6e850c762440014db0a18ec4880029ba1770d891000536c2ee1b122000a6e85cc362440014db0b986c48800e1fa1b755891000636316eab12200087e87d9562440018b8e7b2ac4880021fa1c65589100062e398cab122000c3f65dd16244001878cbba2c4880032b18b74589100061fb28e8b122000c3c651d16244001958c43a2c4880022fa1f64589100061fbaec8b122000c3c75d916244001938e7b22c4880022fa1c64589100061fba8c8b122000c3c751916244001938e6322c48800a37a1b73589100062fb2ee6b122000c5c65dcd624400193ec9b9ac48800327193735891000666316e6b1220008de87d8d62440018beebb1ac488003171d763589100064fba6c6b122000c9c74d8d62440011bd0e31ac48800317dd463589100062e3a8c6b122000c9f7418d6244001938e831ac48800e1fa1f75589100043ec1eeab1220008bf845d5624401317908baac48800237e0d75589100146e41aeab1220008ef825d562440010fd0e3aac4880262fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100146f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f85dcd62440018b90bb9ac4880021fe15735891001c3e42ae6b1220008bf845cd624401317908b9ac4880023be0973589100047bc0ae6b1220008de871cd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd62440010fd0fa9ac48800e1f21f53589100061fba6a6b12209ec3c74d4d62440018bee7a9ac48800b171cf53589100043f43aa6b12200087c8754d624400187ee8a9ac4882770f1d153589100062fb9aa6b122002c5c7354d62440018deebb92c4880031b1d7725891000657ba6e4b122000cac74dc9624400199ee7b92c488003331cf72589100065a3a6e2b122000cd473dc562440018dcedb28c4880029b60f651891000732b8eca31220008ed8799462440014dd0b328c488002aba12651891000556c24ca3122000ace83994624400159b07328c4880023be1d651891000557c22ca3122000aac84594624400159f06b28c488002b320d651891000537430ca3122000c6e7619462440014db06328c48800399604651891000733388ca3122000e6571194624400195cedb20c4880038bd9764189100071632ec83122000ea581d906244001d4ae3b20c4880023b61
  | 4 => 0x34400159b053a6c68800297e1574d8d100052e42ae9b1a2000e1f5495363440018beebb96c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c68800333dca72d8d100052fc2ae5b1a2000a5c855cb63440018beeab96c68810eb5a0472d8d102856ac08e5b1a20008de8714b63440011bb0e296c688002a7a1052d8d100054ec20a5b1a20008de8710b63440011bb0e216c68800297a1442d8d100052ec2885b1a2000e5751947634400153f08a8ec688002a721151d8d102846f43e43b1a20008dd87c8763440014bd0b90ec6880029761721d8d100054f42643b1a2000a9d84c8763440715ad03b86c6881439694350d8d1000666196e7b122000c5f7354f62440058b8e6a9ec488002b960752d891001c77c3aa5b122000a6e85ccb62440014db0b996c4880039354f32d891001477c3a65b122002cce734cb6244001c9aa6996c4880029b60f65d891000557424cbb122000aad84997624400159d0732ec488002b360e65d891000557c22cbb122000aac84597624400159f06b2ec488002b320d65d891000536c18cbb122000e65811976244001c5ecbb26c4880038b19764d891000752c0ec9b122000a6e8599362440014db0b326c488002b3a0e64d891000566c1cc9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000e2f651936244001c58ca326c48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec48800393e1763d89100072642ec7b122000a6e8598f62440014db0b31ec488002aba1263d891000556c24c7b122000a6f8558f62440014d90ab1ec488002abe1163d891000556422c7b122000a6e8518f62440014db0a31ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec48800393a1463d891000726c28c7b122000ec58118f62440014dd0da9ec4880029b21b53d8910506373b6a7b122000e2f64d4f6244001c58c9a9ec48800393d8f53d89100072631ea7b122000a6e8654f62440014d90ca9ec48827f1b9d953d891000717b22a7b122000e2c6454f6244001c9ec6a9ec4880039318d53d89100073232ca3b122041ae486547624400174908a8ec488003b118e31d891020d7243263b122000aae849d7624400155b093aec488002b3a0e75d891000566c1cebb122000ae6811d762440835cb023aec4880029ba1774d891000536c2ee9b122041ae581dd362440014dd0b3a6c4880029b61674d89100056741ce9b122000acd839d36244001c5ea92a6c4880029ba1673d891000536c2ce7b122000aae849cf624400155b0939ec48800333dce73d891000537428e7b122000a6d851cf62440015cd0239ec488106b960473d891000727a9ca7b122000e4f8354f6244001c9ee6a9ec488003931cd53d89100053742c8
  | 5 => 0x80028f616631911000557414c63222000aad8298c644400117f0eb18c8880028fe1563191100051e42ac63222000aaf8258c644400155904b18c8880028fa1463191100051ec28c63222000e1f6518c6444001c38ca318c88800387a1463191100070ec28c63222000e958118c644400147d0da98c8880028f21b53191100061f3b6a63222000e1f63d4c6444001c38c7a98c8880028fa1953191100051e432a63222000c3e7654c6444001c3ec6a98c8880038718d53191100051f42cc43222000a3d85988644400153d07310c888002a760e62191100071a32ca232220469b487544644408d5690ca88c888003a518e31191102355a432623222000e94634c4644413b47b0b298c88800387d4e53191100070fc1aa6322209ea3e8514c644400156d03a90c888002ad607521911004c5f438a432220008bd87148644400153d06290c888002a760c52191100051f42e643222000a3d85cc86444001c3aa7990c888002ada0732191100055ac0e643222000e1d534c8644401317d0e190c8880022f61c32191100051f428643222000a3d850c86444001d1a64190c8880038dd4651191101745fc3aa232220098bc87544644401317d0f988c8880022f61f31191100051f42e623222000a3d85cc4644400155d05988c888002ab60b31191100051f428623222000a3d850c4644401317d0f908c8880022f61f21191100051f42e423222000a3d85c84644400153d07908c888002a760f21191100051f42e603222000a3d85cc0644400147f0a880c8880028f21510191100052f436ebb1a2000c5e76dd763440014bd0c3aec688003179d875d8d100062f3b6cbb1a20008dd8799763440014bd0b32ec688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec68800237e1d65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052f430cbb1a2000c5e761976344001cab0232ec688003279db64d8d100070fb2ec9b1a2000e1c65d936344001c3eebb26c688003871d764d8d100074ac0ec9b1a20008dd8799363440014bd0b326c6880029761664d8d100054f424c9b1a2000ace82993634400159b05326c68800237e1d64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100054f430c9b1a2000c9e761936344001c3eca326c6880038719464d8d100070fba8c9b1a2000e1c7519363440014bd0b316c6880029761662d8d100054f424c5b1a2000a9d8498b6344001ca8cb28ec688142b521951d8d10005ca422a3b1a2000a5e859d763440018baea3aec688286b5a0475d8d102856ac08ebb1a2000a5e871d763440018bd0e3aec68800395a0475d8d100072ac08ebb1a2048ad681dd363440a15ab03ba6c68800297a1674d8d100052ec2ce9b1a2000ace829d36
  | 6 => 0x54ec18a5b222000a3e85ccb644400147b0b996c8880038754f32d91100070ea9a65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000e8d320cb6444001c6ea6b8ec8880038d54d71d91100071ba8ca3b2220288bf8754764440a31790ea8ec8881462fa1f31d91100045ec3e63b222000a3e85cc7644400147b0b98ec888002aba0b31d911000556c1663b222000a3e850c7644400147b0a18ec8881462fa1f21d91100045ec3e43b222000a3e85c87644400147b0b90ec888002a7a0f21d91100054ec1e43b222000a3f855c364440014790ab86c8881478e94350d91100051f42e61b222000a3d85cc36444013878c8bacc888003179cf659911000637396cb3222000c5e7319664440018dce432cc8880030f9d764991100061ebaec93222000c9e73d92644400195ce5b24c88800317d9573991100062e32ae73222000c9f645ce6444013938c8b9cc888003179d463991100062eba8c73222000cce7218e64440018decab94c8880031b195729911000657b22e53222009cac645ca6444001998c6b94c8880021fa1f65591100062e39ecab222000c6c72d9564440010fd0e32ac888003171cc655911000636390cab222000c5f65dcd64440018b8cbb9ac88800317dd463591100062e3a8c6b222000ccc7218d64440018decbb92c8880031b19772591100066631ee4b22200087d83dd5644400117f08baac88800237e0d75591100146e41aeab2220008ef825d564440031d904baac8880030fdd774591100061e3aee8b222000c5f75dcd64440018b8ebb9ac88800327dd373591100062fc2ee6b222000c5c85dcd64440010ff0ab9ac88800e1f21573591100045fc22e6b2220008ef825cd64440031d904b9ac88800317dd473591100062e3a8e6b222000c9f741cd64440010fd0fa9ac88800e1f21f53591100062fb9ea6b222002c5c73d4d64441418d8e5a9ac8880021fa1d53591100043e43aa6b222000c5f7354d64440058b8e6a9ac88827f1b1c9535911000637baee4b222000c6c75dc9644400195ee9b92c88800333dcf72591100066639ee4b222000c6f53dc964440018daa7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000672396e2b2220048f5819d8644400117f0eb20c8880028fe1564191100051e42ac83222000a9f83590644400153906b20c888002abe09641911000556412c83222046ab5819d8644400187cedb28c8880028f60f65191100045ec3cca3222000a9e83994644400153b07328c888002aba0a651911000556c14ca32220008bf87594644400153f06b28c888002a720d651911000557c12ca3222000aac82594644400187cec328c8880028f60c65191100071ac08ca32220008bd8798c644400147d0b318c88
  | 7 => 0x75811cf65440010fd0f21eca880021f61e43d95100043f43887b2a200087d8710f65440014dd0421eca880029b60843d95100051f424e5b2a2000a3d849cb65440014bd07396ca880029760e72d951022d3b408e5b2a2052a75811cb65440010fd0e216ca880021f61c42d95100052f41885b2a2000a5d8310b65440010fd0f996ca880021f61f32d95100062fb9e65b2a2000c5f734cb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb6544001c9a64196ca8814a1fa1f31d95100043ec3e63b2a2000a3e84cc7654400147b0998eca880029ba0b31d951000536c1663b2a200087e870c765440190fb0e18eca8814a1fa1f21d95100043ec3e43b2a2000a3e84c87654400147b0990eca8800297a0f21d95100052ec1e43b2a2036a7681dc365440010fd0f986ca880021f61f30d95104d63ab88cbb2220a2cd57118f64440091eb03baec8880030f5d754d91100055ac0ea9b222003c3c75953644400717f0eaa6c8880123d60773d91104b63ab8ea7b222097c757154f644400147d0b21ec8880028f61643d91100145fc3a87b222000a3e8510f644400147b0a21ec888002aba0843d911000556c1087b222000a3e8510b644400147b0a216c888002a7a0c42d91100054ec1885b222000a3d83d97644400153d0732ec888002a760e65d911000557414cbb222000aad82997644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147b0632ec8880038d60465d91100051f42cc7b222000a3d8598f644400155d0531ec888002ab60a63d91100051fc2ac7b222000a3c8558f644400155f04b1ec888002ab20963d91100051f428c7b222000a3d8518f6444001c3eca31ec8880038719463d91100070f428c7b222000e1d8518f6444001d2b0231ec8880028fa1b53d91100051e436a7b222000e1f63d4f6444001c38c7a9ec8880028fa1953d91100051e432a7b222000e1f6354f6444001c38c6a9ec8880028fa1662d91100051ec2cc5b222000a9e8398b644400153b07316c8880038dd9571d91100071a32ae3b222000e94635c76444001c68cb28ec88812a6de1d51d911028d5a432a3b222000e94638c764440a35690c98ec888002ada0775d911028d5ac0eebb222000c3d751d7644400156d023aec888146ad60475d91100055b40ee7b222051ab581dcf644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf644400147d0a39ec8880028f61473d91100055b408e7b222051ab5811cf6444001c3ea729ec88800387e0d53d91100051f42ee5b222000a3d85dcb64440a356b03b96c8880028fa1672d91100051ec2ce5b222000a9e839cb644400153b07396c888002ada0472d911028d5ac08e5b2220008be8714b644400117b0e296c888002a7a0c52d91100
  | 8 => 0xc8b8082900033c185701052032c3e432eba02406487f87d9740480010fb0fb2e80900272b19172d01200162f39aa7b262000c5d7354f64c400517f0ea1ec98800b279cd43d93100247a40aed326200387e87dd564c40010fb07baac9880123d20575593100043f438eab26200087f855cd64c40070f90ab9ac9880123d20573593100043f43ea6b26200387c87d4d64c412d8e8e3a9ac9880021fa1d53593100043e43aa6b262097c747154d64c40018eeea38ac9880031d1d471593100045fc3ac8326200087d879d762c40070ff0ebaec5880021fe0d75d8b1001c3f42ee7b16200087d85dcf62c401317d09b9ec5880022f61373d8b1001c3fc3ea7b16200087d87d4f62c40010ff0ea9ec5880021f61d53d8b1001477c3a65b162002cce734cb62c4001c9aa6996c5880021fe1576d0b1001c3e42aeda1620018bc845db42c40091e902bb685880e72d10576d0b1001c3f42ceca16200087d859d942c40051bd073b285880023760e7650b100043fc2aeca16200387c855d942c400317d0fb228588006aba0b6450b100247ac30e2a162000977855db41c405f1ef0cb9683880025de1572d07101751e42ac920e2028a3c8559041c40bd6690aa0883880272e99170107102f69bc22ea20e2039d34845d441c40012ef06ba883880025d60d75107101ce9ba12ea20e205eb348559041c400156f0ca10838817acd21542107100069abaa8420e2079c75765d621c40012ef06bac43880025d60d7588710006b8bace110e2000d71755c221c40012eb0bbb243881462fe1d64d0310004bac28e2a0620048be87d51648400187eebaa2c9080122f21d43592100164e39a86b24200387e87dd562840010fb07baac50818f1dc437558a1031e3a886eab14206387e871d562840010ff0ab9ac50800e1f2157358a100043f43ea6b14200387c87d4d62840010fd0ea9ac5080021f21d5358a100247643a64b142002ccc734c96284001c9aa6992c5080021fe157650a1001c3e42aeca1420048bc875914284001878eab228508006ab2096450a104865b326e2a1420468bf875934184001878eab2283080fb1d58575106104c63ab0aeb10c200087e86dcf65440070ff0fb1eca88003175cf63d95100043ec3cc7b2a2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a200087f8758f654400147f08b1eca880028f21163d951000537c12c7b2a2000a6c8258f65440190fb0e31eca88003175cc63d95100062ec38c7b2a2000e558118f654400147d09316ca880028f61262d95100052f41cc5b2a2000a5d8398b6544001ca8c718eca8814a9d21931d95100072a31a63b2a204aa7681dd365440a54eb03ba6ca880030f5d074d95100043ec3ce7b2a2000c5f835cf65440010fd0e39eca88003175cc73d951051d3b408e7b2a2052a
  | 9 => 0x43d95203253741087b2a4000a6d8210f654800147d09b8eca900028f61371d95200063ab88e3b2a400087e87cc765480010fb0f98eca900028fa1331d95200051ec2663b2a4064a6e82cc765480014db0598eca900021fa1c31d95200043ec3863b2a406487e87cc365480010fb0f986ca90002ab60843d91200166639a65b224000e4d534cb6448001d1c86996c89000e1fa1671d91200043ec2ce3b22400087e87d9564480018b8e7b2ac8900021fa1c65591200062e398cab224000c5f65dcd64480018b8cbb9ac8900031dd9771591200063a32ee2b224000c77651c564480018e8ca38ac89000e1fa1f75591200043ec1eeab2240008df835d564480051b906baac8900023de0575591200047a40aeab22400087e871d564480051bd0fb9ac89000317dd773591200062e3aee6b224000c5f85dcd64480018b90bb9ac8900021fe15735912001c3e42ae6b2240008bf845cd64480011ef02b9ac8900023d20573591200047dc02e6b2240008de871cd64480018beea39ac890003171d473591200064fba0e6b22400087e87d4d64480070f90fa9ac89000317dcf53591200162e39ea6b22400087e8754d64480010f90ea9ac89000317dcd53591200162e39aa6b2240008be87d0d6448005938e7a1ac89000a2f21d43591200164e39a86b2240028ec874c96448005998e6992c8900039354d325912000746a1a64b224000c7775dc564480018e8ebb8ac89000335dcf71591200066a39ee2b224000c7753dc564480018eaa7b8ac8900031ddd471591200063a3a8e2b224000cb7741c564480019aee638ac890003351cc715912000673b90e2b224000c77531c564480018eaa638ac8900032dd0c71591200065aa18e2b224000ce6321c564480019ca6438ac890003361cf70591200045fc3ac83224000a9c83590644800156902b20c8900262fa1375d85200045ec26ebb0a4000ab684cc761480070fd0dbaac29018e1f21b75585200043f43ecab0a4000c5c73d9561480010fd0e32ac290003171cc65585200061fb2ee8b0a4000c3c65dd1614800187eca3a2c2900030f19474585200062fb2ee6b0a4000c5c65dcd61480011ef0eb08c290002ad21161185200056a41ac230a400087f855d061480070f90aba0c29000b331cd321852000726a9a6430a4000ab684cc461480015cb05988c290003b14c831185200043fc2aeda0a400387c855db41480010ff0abb4829000e1f215769052001c3f42eeca0a400087d85dd941480070fd0b3b282900021f616765052001c3e428eca0a400087e86dd541480010fd0fb2a82900021f21f655052001c3e42cec20a400087f855d841480070f90abb0829000237e0d76105200146e41aec20a400087c865d441480010ff0fb2882900021f61f651052004e56322e420a40018f8865c04148013970
  | 10 => 0x3088003c7675946611001356908a8cc2200123d61e319844001c3f43eeab088085c3c74dd5611010bc6883baac2200021f60f75584401745fc22eab0880098bc845d56110133878e83aac2202678d10475584400043fc2ae6b08800387c855cd611001317908b9ac2200021fa1f535844001c3e43ea6b08809ee3441d4d61100010fd0ea9ac2200021f21d53584404ef1a20aa6b088003c747594561100091e90ea8ac220026ad21151584400247a43a62b088009ab4844c5611005d4790abb482200272d9c576904401751e42ac5208802ea3c8558641100070fd0bbb442200021f61776884400247ac3cc31088000c757598621100018eaeab0c42200021fe15764844001c3e42aec90880048f4875852110013968e8b0a422000317dcd53592200162e39aa6b2440048bc8750d6488005938e6a1ac91000e1fa1471592200043ec28e2b24400087f855d261880070f90aba4c3100123d61e519862001e3b3aca330c4000ab48454661880091eb0f18cc31000e1fa1f75586200043ec1eeab0c40008bf845d5618801317908baac31000237e0d75586200146e41aeab0c4000c3f75dd16188001878ebba2c3101472d60774586200061fba8e8b0c4000c3c751d161880051bd0fb9ac31000317dd773586200062e3aee6b0c4000c9f74dcd6188001938e9b9ac31000317e1773586200062e42ee6b0c4000ccc21dcd61880010ff0ab9ac31000e1f21573586200045fc22e6b0c40098bc845cd61880018beea39ac310003171d473586200064fba0e6b0c4000c9c741cd61880010fd0fa9ac31000e1f21f53586200061fba6a6b0c409ec3c74d4d61880018bee7a9ac31000b171cf53586200043f43aa6b0c400087c8754d618800187ee8a9ac3102770f1d153586200062fb9aa6b0c4002c5c7354d61880078e8eb28ac3100123d21d51586200055a422a2b0c4002cd4738c561880091e90e98ac3100021fe15769062001c3e42aed20c400087f855d941880070f90abb2831000237e0d76506200146e41aeca0c4000c757598441880018eaeab088310002ade11611062004e5c322e020c404f8ef87586218800159f06b0c43100035a5d570886200043f436e7b2a400387f87d8f65480018bae7b1eca900021f61e63d95200043fc3ac7b2a4000a3f8458f654800147908b1eca900029de0563d95200053a40ac7b2a401387d8718f654800147d0831eca900028f61063d95200062eb98c7b2a4063a6c864cb6548001a9ee6996ca900039318d32d952031db440265b2a4000c3d741d365480018be65b9eca90003174cb73d95200043ec3ce7b2a4000c5f835cf65480010fd0e39eca900028fa1073d95200051ec20e7b2a4000c5d731cf65480c94dd0439eca9018e9b60873d95200043f43c87b2a400087d8790f65480010fd0e21eca900021f61c
  | 11 => 0x900014eb0b39ac3200faada1273586400055ac24e6b0c8000ae6829cd61900015cb0539ac320002ade1173586401f55a422e6b0c8000a76851cd61900014eb0a39ac32000395d4e53586400072bc1aa6b0c8000e577354d6190001ca8e6a9ac3200029da1643586400053ac2c86b0c803ee944350d61900014ed0bb92c3200029d61772586400053b42ce4b0c8000a75859c9619007d56d09392c320002ad61272586400056b41ce4b0c8000ad5839c9619000156f08b92c3200faada1052586400055ac20a4b0c8000ad68314961900015ab06292c3200be3de1d42586401347a43a84b0c8000a778550961900014e90aa12c3200fba910942586400053b42e64b0c8000a7585cc96190001caaa7992c3200039554d32586400053b42864b0c8000a75850c9619007d56d08192c320002ad61032586400076299064b0c8000cf2615c2419007db64e2b8483200021f61b75506400043e43acaa0c8000c777598541900018e8eb30a83200031ddd561506400063a3aac2a0c8000cf161dc1419000156f02b1083200fb8d9d561106401f71abaac220c8000e37535844190001c6aa6b08832000e1fa1776886400043ec2eed10c800387e855da21900010ff0cbac43200021fe1d65886400043ec3acb10c80048f58798621900018eceb30c43200031d5d661886400063b3aac310c8000c7575586219000187ccbba243200123d21d61486401f65a3a2c290c8000c5f7354f62500058b8e6a9ec4a000b271cd43d89400043fc2ae3b12800387c855c7625000317908b8ec4a000237e0d71d89400146e41ae3b128000ce4621c562500019cec438a84a009b39188715094048e1e3b6eaa128091e2c62dd5425000355d0db1284a00bf2d1db715094017f52316e2a128026cb4761c54250001a68ea38a84a009ba918871509400069dba8e0a128000db3711c142500010ff0ab96c2a000e1f21572d85400047bc3ac230a8000ae482584615001317908ba8c2a00030fe1175185400061e422ea30a800087f835d461500070fd0bb98c2a00021f617731854001c3fc3ea630a800087d87d4c61500010ff0ea98c2a00021f61d53185400061ebae8430a8000c3d75508615000156b09908c2a00fa3d61f61905401cc7b438c2a0a800387e851da21500010fb0a3b442a000e1fa1476485400043ec28ec90a800387e87dd562100010fb07baac42018e1fa1c75588400052ec18eab10800087f855cd62100070f90ab9ac4200262f21173588400047bc0ae6b1080008f4815cd62100091f100b9ac4200021fa1f535884001c3e43ea6b10800087e8754d62100010f90ea9ac42000b179cd53588400062eb9aa6b1080048ec8754962100091d90e992c42000b331cd325884000726a9a64b108004ae8804c9621000317b09b8ac4202432d10771588400247ac3ca3
  | 12 => 0x21fa1c32596400043ec3864b2c8072a3e840c9659000147b08192cb20003934c832596400063bb8ce2b2c8000a3f845c565900e547908b8acb200021fa1f31596400043ec3e62b2c8072a3e84cc5659000147b0998acb200029ba0b315964000536c1662b2c800087e870c565900010fb0e18acb200021fa1f21596400043ec3e42b2c8072a3e84c85659000147b0990acb2000297a0f21596400052ec1e42b2c8004a7a8008565900014f30010acb200123b21d3258a400166639a64b148000e4d534c962900070fd0bb8ac5200021f6177158a400043ec36eaa14809187e8759542901270f90eb2a85201cb8b1096550a400047ac36e2a148000c7665dc542900018eacbb8a85200023d6187150a400063b328e2a148000c75651c542900018eeeba8cc3200123d61e519864001e3b3aca330c8000ab78454661900014ed0b98cc3200029d61731986400055ac266330c8000ae682cc661900015cb0598cc3200123d61e31986400053b4286330c8000a75850c661900014ed0b90cc3200029d61721986400055ac264330c8000ad683c8661900015ab0790cc3200031ddd675986400055bc22eb30c8039ab4845d66190073c6ca9aa4c3200029da1673986400053ac2ce730c8039ab6849ce619000156b0939cc320002b9a0a739864000572c14e730c8000a76851ce61900014eb0a39cc320012bca00739864000578c00e730c8000e575394e6190001caf06a9cc3200029da1643986400053ac2c8730c8000a7685dca61900014eb0bb94c3200029da1672986400053ac2ce530c8039ab6849ca619000156b09394c320002b5a0e72986400056ac1ce530c8004af2801ca61900015e300394c3200e6ada1052986400055ac20a530c8000ad68314a61900015ab06294c3200be3de1d42986401347a43a8530c8000a778550a61900014e90aa14c3200029da1732986400053ac2e6530c8000e5553cca6190001caaa6994c3200029da1432986400053ac286530c8039ab6840ca619000156b08194c320003b14c832986400062fb9aa6b0c8002c5c7354d61900070fd0bb92c3200021f61772586400063bbaea2b0c8000ab584d4561900078eceb28ac3200123d21d51586400053b42e62b0c8000a7585cc5619000156b0998ac320002b9a0b315864000572c1662b0c80048f4874c561900014ed0a18ac3200029d61431586400053b42e42b0c8000a7585c85619000156b0990ac320002b5a0f21586400056ac1e42b0c8000c77759d5619007d56d093aac320002ad61275586400056b41ceab0c8000ad5839d561900015cd053aac320002b960a75586400055bc22eab0c803eab4845d561900014ef0aba2c3200029d21574586400056bc1ae8b0c8000ad4835d161900015cf04ba2c320002b920974586401f71b2a6a8b0c8000a76859cd61
  | 13 => 0xc3fc32ea304420087d8799460884010ff0eb28c110a531d9c565182210047dc3ac03044200c3d75d53644840517f0ea1ec89080b279cd43d91210043fc2ae1b22420387c855c364484070fd0fbaac8908021f60f75591210045fc22eab2242008f7815d564484010fd0e3aac8908030f1d774591210043fc2ae6b22420387c855cd64484011ef02b9ac8908023ee0173591210247c402e6b22420087e87d4d64484070f90fa9ac890aaf1ddc753591210043f43aa6b22420087c8754d64485558eee2a9ac8908031ddd771591210063a3aee2b2242008bf8759064484014790ab20c890a42ade0564191211751e42ac920a4200c3c75d91414840117f0eb2082908a28f21564105214855bc0ac820a4279c6e765d621484010ff0aba6c09080e1f21574d81210047dc3ac0302429ec3f42dcd65d013b0fb0f39acba00268fa12735974054d1ec24e6b2e8000c5f739cd65d00018bf06b9acba02770fd0973597404f43f438e6b2e8009a3e849c965d015147b09392cba00268fa10725974010d1ec20e4b2e8000a5e831c965d00014bb06392cba00021fa1f32597400043ec3e64b2e8000c5d73cc965d001347d09192cba00028f61232597400062eb9a64b2e800087e870c965d00010fb0e192cba00268fa1032597400051ec2064b2e8000e4d320c965d00018eee338acba029e8fe11715974004d1e422e2b2e800087e87cc565d00010fb0f98acba00268fa1331597400051ec2662b2e8000a6e82cc565d00014db0598acba00021fa1c31597400043ec3862b2e800087e87c8565d00010fb0f90acba00268fa1321597400051ec2642b2e8000a5e83c8565d00014bb0790acba00268fa1021597400051ec2042b2e80a6a3f845c165d00010fd0f982cba00021f61f30597400051fc2260b2e8009a3c844c165d001347d09902cba00028f61320597400147643a64b168002ccc734c962d0001c9aa6992c5a0003a350d3258b4001c3f42ee2b16800087d85dc562d00051bd07b8ac5a00023760f7158b400051f43acaa168075a3c8759542d000147f06b2a85a00028f60d6550b4004e1fb92caa168009e2f7259542d0001c5c64b2a85a00038b4c96550b400071ab2ee2a1680a5cb7761c542d0001a68ea38a85a00038d5947150b400164f39a8730e8001cae7250a61d000917908baac3a000e1fa1772587400043ec2ee4b0e800387e85dda21d00010fb0bbb443a000e1fa1576887400043fc32eb10e800087f8759621d00010fb0eb2c43a02929ee0174596404bc3ec3ce6b2c8000c5f739cd65900018bf06b9acb2025a1fa1c73596400043f43c86b2c800087d8790d65900e5c3886a1acb201ca8fa1072596400051ec20e4b2c8000a5e831c965900014bb06392cb200021fa1f32596400043ec3e64b2c8000c5d73cc965900018bae6992cb20
  | 14 => 0x565dc5421044d36b0db8a84208bf2d61b71508414869b32ee2a108290d3565dc54210401a6ea7b8a84208034d54f71508410061e3aeeca088200c3f85dd941104018790bbb282208030fd4f76504410061ea9eeca088200cb651dd9411040196aa3bb28220a664fa1f75504410061fbb6eaa0882099b581dc9411053dc7081a9ac02080317dcd53580410162e39aa6b00829de384054d601048d1790ea1ac02080b271cd43580412355c40286b0082468bc875096010403958e4a12c02091aae201425804104d5c42460b0082028f8874c1601041357108982c0208021fe1973596210043f43ec6b2c42b1a7681d8d658844b0fd0f31acb108028fa1263596210051ec24c6b2c4200c5f7398d65884070fd0eb1acb1080317dcd63596210043f438c6b2c4200d4d734c96588401c9cc6992cb108030fdd274596210061eba0e8b2c420087d879cd658840147d0939acb108028f61273596210062fb9ce6b2c4279a6e829cd65884014db0539acb1080317e0d73596210062f992e6b2c4200c5d325cd65884010fd0e39acb108021fa1e43596210043ec3c86b2c420087e8710d65884010fb0e21acb109e69ba08435962100536c1086b2c422587e87cc565884010fb0f98acb108028fa1331596210051ec2662b2c4279a6e82cc565884014db0598acb108021fa1c31596213cc3ec3862b2c4200a3e849c1658840147b09382cb109e69da0670596212253ac0ce0b2c4200a6f825c165884f34d904b82cb10a529da04705962112d3ac08e0b2c420087e87cc165884010fb0f982cb108029da0630596210053ac0c60b2c420087e870c165884010fb0e182cb108028fa1030596210051ec2060b2c4279a6e820c165884014db04182cb108029da0430596210053ac0860b2c42b0c7671997648855f8ece2b2ec9108023da0775d92210043ec3cebb24420387f875d764884010ff06baec91080e1fa1773d92210043ec2ee7b2442008f681dcf64884091f501b9ec9108023e60373d922101c3fc3ea7b24420087d87d4f648855d8ece3a9ec9108021fe1d53d92210043ec3aa7b2442adc767154f648851f96ce3a1ec91080a2fe1d43d92210164f39a87b2442accb67150f64884051df0e996c91080b339cd32d922100726a9a65b244200e8d434cb648844d9cce2996c9108031d9d671d92210063abace3b24428fab681d9264884f756d03ba2c91080b339cd325922100726a9a64b24420387e85dc164884010fb0bb82c9108021f61e65192210043fc3aca32442008bf8759064884590fb0dbaa83108021fa1d655062112c3e43acaa0c427a87f865d441884010ff0eb2883109e61f61d651062104e57322e420c427ac767199660884070fd0bba2c1108021f61774582210062fb9aa6b044202c5c7354d608840599ce6992c1108039354d325822101
  | 15 => 0xfb2a84a0a178b10b65509410063bb2ee2a128200c7465dc5425045f9c8c5b8a84a08031dd9471509410063a328e2a12822ea3e86d96415050bc6ec3b2c82a080e1fa1b755814142c3e436eab02820087e87d9560504018b8e7b2ac0a08031b1cb65581410043f438cab028200c5c7319560504018d8e432ac0a080317d9773581410062e32ee6b028200c6f65dc960504018d8cbb92c0a08023ee1d60181414f61e3a6e6b28829ec3f42dcd651053b0fb0f39aca208268fa1273594415e51ec24e6b288200c5f739cd651057747f08b9aca208268f21173594414ee1e3a2e6b2882baa77815cd65104014e902b9aca208030fe1173594414ee1e422e6b288200c5f835cd651053b87e84b9aca208031de0573594410063a40ae6b28829e87e871cd651041347909b92ca208268fa1272594415cd1ec24e4b288292c3c749c9651057147f08b92ca208268f21172594415bd3bc0ae4b288200a74815c9651041347d08392ca208a28f61072594415961e3a0e4b288200a5e831c965104014bb06392ca208021fa1f32594410043ec3e64b288200c5d73cc9651041347d09192ca208028f61232594410062eb9a64b288200a77814c965104014e902992ca208021fa1c32594410043ec3864b288209a3e840c9651040147b08192ca20803934c832594415b51ec24e2b288285c3c749c565104510fd0f98aca208021f61f315944104d1f42662b288200a3d84cc565104014dd0598aca208029b60b31594410043f43862b28820087d870c565104510fd0f90aca208021f61f215944104d1f42642b288200a3d84c8565104014bd0790aca208029760f215944104d1f42042b288200a3d84085651056b878e9b82ca208268fa1270594415a51ec24e0b288200a76819c165104934eb03382ca20ace8fe11705944104d1e422e0b288272c3c745c165104014ed02382ca208a29d60470594410043f43e60b28820087d87cc165104014ed03182ca208029d60630594410051fc2260b288209a3c844c165104010fd0e182ca208021f61c305944104d1f42060b288200a3d840c165104014dd04182ca208029b60830594410053b40860b288200a75810c1651041347d09902ca208028f61320594410043f43840b28820087d87081651041347d08102ca208028f61020594410052f41840b288200a5d8308165104014ed02102ca208029d604205944104c5e422eab1082028ec874c96210405998e6992c4208039354d325884100746a1a64b108200ae4814c9621056527d0fbaa84208a30fe1d65508410051f43acaa108282a3c8759542104518790eb2a84208a20f21d65508410051fc1acaa108200a3d83595421041387ee4b2a84208278bdc9655084100717192caa108200e2d325954210401c68e2b2a84208034ddd771508410069a3aee2a108200e3
  | 16 => 0x3581420063bb2ee2b028400c7465dc560508018eeca38ac0a10031d19471581420047b43ec2b028400c7775d8560508018e8ebb0ac0a100335dcf61581420066a39ec2b0284008f68718560508018eeea30ac0a10031d1d4615814237e5bba0c2b028400cd77318560508019a8e630ac0a124f0f5d065181420047dc3ac03028400ad88358060508070fd0fbaac5a08031ddc77558b410043ec1eeab16829287e871d562d04014bb063aac5a08031ddc47558b410043fc2ae6b16820387c855cd62d04010fd0fa9ac5a080e1f21f5358b410043f43aa6b16820087c8754d62d04058bce6a9ac5a0803175cd5358b4104c7643aa4b1682028ec874c962d0405998e6992c5a08039354d3258b410164f39a86b14822e93c855db429041396cc2bb685208ba4f21571d0a4113673310e2a14822e93e87dd5429052387eedbaa8520a478b98b7550a4100d57c32c4a148200d3775dc5429045fd4cc5b8a852089b2ddd87150a410069a3a8e2a148226ea6621c5429045d2790abb683208ba4f21572d06410043ec1eeab04820087f855cd60904070f90ab9ac1208021fa1f535824101c3e43ea6b04820087e8754d60904010f90ea9ac1209462fa1f435824128c5f43e84b048200c3f75d09609040187eeaa12c1208023ee1d60182410043f436e7b2a820387f87d8f65504018bae7b1ecaa08021f61e63d954100537414c7b2a8200a6d8298f65504010ff0eb1ecaa08b21f61c63d95410062eb98c7b2a8200a5e8398b65504014bb07316caa09f69da0774d95410043ec3ce7b2a8200c5f835cf65504010fd0e39ecaa0803175cc73d95410043f43c87b2a820087d8790f655050bc3886a1ecaa0a168fa1272d95410051ec24e5b2a8200a5e839cb65504014bb07396caa08021fa1f32d95410043ec3e65b2a8200c5f73ccb65504018bee6996caa08021fa1c32d95410043ec3865b2a8285a3e840cb655040147b08196caa0803934c832d954142c3f43e63b2a820087d87cc7655050b47d0998ecaa08028f61331d95410053741663b2a8200a6d82cc765504010fd0e18ecaa08b21f61c31d954142c3f43e43b2a820087d87c87655050b47d0990ecaa08028f61321d95410052f41e43b2a8200a5d83c8765504594ed03386caa08029d60670d95410063cb80e1b2a820087e87cc365504010fb0f986caa08021fa1c30d95410043ec3861b2a8285a3e840c3655040147b08186caa08029ba0830d954100536c1061b2a8200a76810c365504014eb02186caa08021fa1c20d95410043ec3841b2a8285a3e84083655040147b08106caa080297a0c20d95410052ec1841b2a8200a768108365504014eb02106caa080a3be1d32d89410166739a65b128200e4d534cb62504010fd0fb2ac4a08021fa1c65589410043f436eaa12829387e87d9542505230f90
  | 17 => 0xa8400a768518c61508014eb0a318c2a10029da1b53185420053a436a630a8400a768654c61508014e90ca98c2a10038dd9743185420071a32e8630a8426ab48650c6150801c6ecaa18c2a10038d19543185420074bb1a8630a848fae4864c86150801cceca990c2a100399195321854200763b1a6430a8400ec4634c86150801e8aa6990c2a1003e150d32185420063bbacea30a84bfab7845d4615091f56908ba8c2a123eada1075185421355ac20ea30a848fe3654d50615091fc68a8aa0c2a10029da1673185420053ac2ce630a848fab6849cc615097d56b09398c2a109ab9a0a731854200572c14e630a8400a76851cc61508014eb0a398c2a123eada1073185421355ac20e630a8426ae6821cc615091f5cb04398c2a1002bca00731854200578c00e630a84aee6632d4c615091f56d09298c2a1002ad61253185420072ba9ca630a8426ae68294c61508015cb05298c2a100395e0d531854256f2b992a630a84ade663254c615095bcaa64a98c2a123eada1053185420055ac20a630a8426ae68214c61508015cb04298c2a10038dd4f43185420071aa9e8630a84bdea632d0c61508014ed0b218c2a10029d6164318542135734148630a8400ae58290c615091fd2f06a18c2a10038dd4d43185420071aa9a8630a84ace973250c6150959d4c64a18c2a12b3a54c9431854213573c1a6430a8426ec7834c86150801d8ee6990c2a1003b11cd321854200733a9a6430a8400ec6534c86150801ccaa6990c2a1003b154d321854200722a9a6430a8400ea7434c86150801d8c86990c2a1003a950d321854200762a1a6430a8400e85434c861508014ef0ab80c2a10029d215701854237d5bc22e030a8400ad7835c061508015a906b80c2a1002b9e0970185420053b428e030a8400a75851c0615084d56b08380c2a1002b5a0c70185420056ac18e030a848fae5821c0615091f56d09a80c2a1002ad613501854247d5b424a030a8400ab58494061508011ed0e280c2a10023d61c50185420053b42e6030a8400a7585cc0615091f56d09980c2a1002ad6133018542135734166030a8400ae582cc06150801d8a65980c2a1003b14c930185420047b4386030a84008f5870c061508014ed0a180c2a10029d614301854247d5b4206030a8400ab5840c0615084d5cd04180c2a1002b960830185420166639a65b028400e4d534cb6050801d1a86996c0a100e1fa1671d81420043ec2ce3b028400ec932cc3605080157308186c0a1002ba60830d81420063bb2ce33028400c74659c660508018eecab8cc0a10031d19571981420063b3aec33028400c7575d8660508018ecea30cc0a10031d5d4619814201c3f436eab02849187c86dd560508010fd0fb2ac0a1003171cf65581420043f438cab028400c5c7319560508018becbb9ac0a1003171977
  | 18 => 0x8014ed0a18ec2a10029d61431d854262f1aba6cbb0a8400a7583d976150985c6b0832ec2a130b8d5d065d85420053ac18cbb0a8400e3465953615085f5690caa6c2a10029da1663d85420053ac2cc7b0a8400a778558f61508014e90ab1ec2a1002bce0163d854200578402c7b0a8400a768518f61508014eb0a31ec2a10029da1b53d85420053a436a7b0a8400a768654f61508014e90ca9ec2a10bead21943d85420074a31a87b0a8490ae4864cb6150801d88c6996c2a1003d154d32d8542007c2a1a65b0a8490ab684dd7615085f56b09baec2a10031d5d475d85424855b420ebb0a842fab5841d761508015ad063aec2a1002b560c75d854217d73410ebb0a8490ae5821d76150921c6ca9aa6c2a1242ada1373d854217d5ac26e7b0a8400a76859cf61508014eb0b39ec2a10029da1473d85420053ac28e7b0a8490ab6841cf615085f56b0839ec2a10beb9a0873d854248572c10e7b0a84abe3574d4f6150801caea729ec2a12ab8d5d153d85420072bc1aa7b0a8400e567354f6150801caae6a9ec2a12ab95cc953d85425572a992a7b0a8400a768590f61508014eb0b21ec2a1243a510d43d85420053b42ee1b0a8400a7585dc3615085f56b09b86c2a1002b5a0f70d85420056ac1ee1b0a8490ae582dc361508014ed0b386c2a10029d61670d854217d5ac20e1b0a84008f68714361508011eb0e286c2a10029da1730d85420053ac2e61b0a84008f6870c361508011eb0e186c2a10029da1430d85420053ac2861b0a8490ab6840c3615080156b08186c2a10beb9a0830d854200572c1061b0a8400c7675d8661508018eaebb0cc2a10021fa1f65585420043f438cab0a84c6c3f7419561508011ef0eb08c2a10029de1561185420053a42ac230a8402ccc734c86150801c9aa6990c2a1003a350d32185420063bbaea230a84038f58794461508078eceb288c2a1002ade1151185420055ac20a230a8400a7685cc461508014eb0b988c2a1002ad613311854200572c166230a84028f5878c46150801d8a65188c2a10029da1431185420053ac286230a8400ab5840c461508015cb04188c2a1003b14c831185420043fc2ae030a840387c855c061508011bf06b80c2a100a3720d701854262e3b3b6ca30a8400a7583d946150989ccc65b28c2a10023d61e65185426053b42cca30a84008f787594615097f56f08b28c2a130e9da1865185426163b3b0ca30a84c1e35841946150983c6ee8328c2a13078d1d065185420053ac18ca30a84c1e36421946150983c6884328c2a1307998c865185426055b434a830a8400e3465950615084d5690caa0c2a10038d19554185420047ac3cc630a8400a768598c61508014eb0b318c2a12faad61263185420047bc3ac630a8400a778558c61508014e90ab18c2a1002bce01631854200578402c63
  | 19 => 0x20010028004048016002000000400100000040000010018038000002001803400c0000000018008004001801000200100100080000000048014002000001800c010002002000c002004003800c0040010000008000002000000400000c001800000e00d000000400c001003800000c0130020004006002000000c0000000008000000000002800c00400f00000100080000000000000000006001400400b00000080120040010004000008001000000000100080280040030058004006001000001c00c001000000400e001000801800c0000040008022012001001c00a0090048000002000000000000200a000000000600400300040080050000000014008005000801000600580000060020010000000000002800c0000010010020000002000000000000200680000020010164f39a8730e840087f855c261d08070f90ab84c3a100e1fa1f755874242e1e3a6eab0e8485e3441dd561d08010fb07baac3a10062f21175587424ce1e3a0eab0e8499e34411d561d08010ff0ab9ac3a100e1f215735874200c5e422e6b0e840087e87d4d61d08070f90fa9ac3a12830f1d353587424f71a20ea6b0e840087e8754d61d08010f90ea9ac3a127f0f1d153587424ef1a20aa6b0e8400c5f7354d60d08058b8e6a9ac1a100b271cd435834201c3f428e2b06840087d851c560d08010fd0db9ecaa100e1fe1f63d95420062eb9ec7b2a840087d8798f65508014ed0331ecaa10029d60663d95420043fc3ac7b2a8400a778158f65508014e902b1ecaa10029ee0163d95420053c402c7b2a843387d8718f65508018bae631ecaa12468f21943d95420070e31a87b2a8492a6c864cb6550801a9ee6996caa10039318d32d954200786a1a65b2a8400c5f32dcf65508018ba65b9ecaa10021f61e73d95420062fc1ae7b2a840087e871cf655092547d0839ecaa12468f61073d95420062eb98e7b2a8491a6e821cf65509254db0439ecaa12461fa1e43d95420043ec3c87b2a8492e1c4350f655092547d09b8ecaa12468f61371d95420063ab88e3b2a840087e87cc765508010fb0f98ecaa124a8fa1331d95420051ec2663b2a8491a6e82cc765508014db0598ecaa10021fa1c31d95420043ec3863b2a8400a76819c365508014eb03386caa124a8fa1070d954248d1ec20e1b2a840087e87cc365508010fb0f986caa10021fa1c30d95420043ec3861b2a8492a3e840c3655080147b08186caa12469ba0830d954200536c1061b2a8400a76810c365508014eb02186caa124f0f5d065d854200c5ec26ebb0a84018bd84dcf615094187ae9a9ec2a127f0f5d153d85420162f39aa7b0a8400c5d7354f61508018eaeba8ec2a1002ad61351d854200572c16a3b0a8403c747594761508071ef0ea8ec2a10029da1731d85420053ac2e63b0a84028f7874c7615
  | 20 => 0x80040060010000044002001000000000a0080008000008001000000000200f000800000e00300100340160000028000000001000800c0040080028008020000006800000400100000000060030008000000000002000400a002000800002400600080280020070000000002000000800000200800100040080000000004006000001000c000003000004c008000002800800c0050010008002007001800802200000080040000020000000002001000800800000400000000280090000024008007000000800800000180000220060000000002000000000c0000000028004010000000000c00a000001001401601200180140000000000000006003006800000a0010038000004001002803400a000000000c002000000009c008003001001003a00000000000000000008004014002000000c004000001801c00000000000040080020000000006001001000000a001003804c00400000000040000060028000018002000001800a0030018000002006004000800000100280000000050008000000006000000400a0000000014012001001000400000600400040000000000000002000002800c00e000001000000000000400000080080000008004014004801000000100000000000000000000000001000000c002000002800800400100400000020000000008000001001800c012001000000000400000000140020020000008006001002800000000e000001c00e0000020014004001001800000400700a8014002005001001800000e001800801c0000000014008002004800c0020050050008004000002800001000200100040060010000000006001000800c002000000000400c00200280100080000150004016009004800400a0090000014000000000805800200500480040000030008010012000005800000000400100100000000060008000005001000c0000020008000000000004000000600f001800c00001200080200120000018008000008003801800000100000040000050010000002000000002400400500100080040000000004000001001801000c0010040020000000000002803600c002800000000b005800000a000002000000c001001002000000200280380040080010004004000003002400e003002800401000000300180000050000000010003002003000e010006001c00200c00980000000070058000000001000802800a005000800000000000500080020060000014002005000000003600a00000040000010000000000005005800000e0080030000002001001801000000c00000040000010010000012012002800400200200f000000000000080200040020028000000009000800000000900000180020020068000010000000000000400d0000004008002000802402e00000080e4002000000000c
  | 21 => 0xf3a00053d926012c11540500000eaa4a085262cbbe94f401800150a6db000000000004d371170148c706000000007000000000000008da000113400087a0cb80009165b8000000115c8a50000000000173203a07c00000000000014fe8de51d8000000000000000000092404b8fa0cba33300aaa642f000000000006da0001cc800038600000000000002a23ec00013bc0c12d392943509bc1191d8c3469ce000000000000000015d400000000b09940006ba44e95444c4aa03a18000746a21000174d45a4693429d6400000045d00008369bf27a800000059325d0000cd600000000000006811ed80004ae04900000000005185558cb40000004980000f6898700000001f8213000291d27a000000142882049b4139c540000001742a30efc72a00024b80000000000000000a9350c063c00078600021b000026c0000000bfc0001e380000000000000000ea294e15da01000087e0b600d00b27e30000bb800061f0002a00c0e00000000012549d314e8d08a800004c0800000000000000010fa3f3108870940c00000015dce820004c98fe83f617a0508c24adea764e924248f097f4dd800000092254a17cc0008130001b8c38e72044d0f9074e0002df0a1947c00055400014d80000408c311c20000000f9c39a03f3f219685860543938000fce0004fd0318000000000094464a0002ab00010520a806906dc35e05b1810b049b24a40020000000000000000014e0000000000ae40000fb80000003fe35c1980ccc632483000037000054786f8000a3f0000000000000000000000005201594e85fe5d0165000138400018b00005d8000074000096c0003318f4800074f06380000008a63b796200000002f4a4c800000000026580180004b88000e620000000000ff0690000000000080829380000003f90000d7c00036f1a48834b9a6200001c8538618d2cb0000ffc60e000000000000000013f40006f748f800000008a000226d10653d482000000000000000009ec0000001b740007501828000ec0000000000000092d111000000000550092109ac0004cf9268000a7d4858000000198503a2b0ab837b217240c00000000725210e84fa00010754140fd32900704820004608f941e285427a0000b06367000000000002201f0394c100000b49654000a41356235ca4a00036589ec0009e300000000000002ee8f08000000800800200000200000040000010004000000002803800200000680000000000010004002007001800003c0000008000002001000000400600000200040000010018004002008005000801000200000000060000010000000000001800400a000002000400000200080040020060000008004000007800001000100480000040000030010000000002802400000200100100040000030004002003
  | 22 => 0x66d4000019515e5ae00019e00000003de8000a54000247a0540000aa0001f506483211a50000e4c2440000000000063000000000051400024814f029502f89d4000a2422780000001dc0bfa29c5c017c00ca0781189f84faa38017858126a9b7cf80000043938d4546272fd06d90f81bc14900001b64f348823e8d4885a2db0de810445719e8d002868ed12c0fa81d808f00004189c20000000da00001d6101247926850237d0d14b426c2278aa8c8102af0000df8000294320985c1d4a591e4a874000928000000000076d0001fa8000000000249c0006720000001420a9c10900009626fc2e70000a725090000ca00006ce000238848000038d00012f03e13c41a204a04af0561c3876012f2800b347d270f534a84c0004ec3410c6cb5e8a4467a900a9416e000248c1e86c03c480000000000002a453589973d1800000000015a800017c2d903496f4456009356824839e78720a8aac26e01309b00006d8000000000022e90a30e03140000000000000000000000000034e000000249400000000020b0000000000180000000000016440000004e206240000b750a0f800003b8000038c724a1f08d0fd86260002ea245c0007ef00014200000000000000f380001f59310cde3f152f289cc28860000239400000054f8000000a9825498d00009d93c09ee46dc49c000000017a00000010c800000000000000002774be000070a89e555029466c0003ed80004b2000000062c0008660d5a9f0d441d20000b6088a4340a30f54ce87cb4aca9a08b61cc49300008140003dc09e00000000001c24134000000000000000000000000007d54398000ae8a8108100000001de0a400007381a9504026400053b2fe000007a00023e000000007400000000000000dd80011fa0eb46820ac38c6a33791bec8866933fa1314000000149917000089800001cd0ce7e20000074e4636a0b902bc67877026700005203f516f8000000000000000029a000000257d29aa1622a134506ea8852a0f613ec1b11ef0000a467d74b9834d20e91600029acfda0bf0000300f2c86216400000008790000000324000046a00400000000000008cc6300000119352a5a1451a680003a9240a608e8c91d00005d0b4a0000430e1950e0000ef9b1d4c60000000000cb251a1cd8b9805c000000000094268e3d28628f1c3ca23a8eb0e320004c48000000000000000090000000000000000000001d311260000e88d2133200000000000000000002328aae319000000000000035400000000000000000000000000000000016f3260c385189cf13195e94cc6034c310f90a643c3a700000008394871e8871c14407b000000000026382e09a000000010050606e000006100005432d5255c00009119300000000001970d7400075a04a000074807600000000000001b9940c000000000
  | 23 => 0x68000000983000277d18c000142000023aaa23709e7d54c00030d1f4c59600000018a883831e0f90644b448333dd000100c2711051cac00036b1e41a1000049518a96b43608ce19d1bc0024377329800000000000012b482e09512fa6e4d2e0003a2a2b4cc22f6000000105a9e706d29809767c64bf1898cda8f81370000afc000000276000050c423a0b80006f90000d9414c0003d580005621120000fd0e300002f0089ce502bf00000000007b200000000001ba119963400000021b945c000000259800041000000000004b4a583b404ac5360672b302b899632b24ea94804a96f000000109a6af52400002b6000000000015a20027725d80003be0ad15fc17246533f1d985520001350378fcc000000000048c16327502d13ae8a00001b58eb00f3000000121a6443efa0ec000a393f4000000040600007b45b600044100000000140928000000000201883024ca1a3478000ce200000029dc1be93e0ae297c9bc00000026e119a0002270000fd870500000009b88b500589d101a99b00008188d40002f8138061e1e00838b5c4bc9bd4ed9b44e740000001710fb86fe0138f0c000000000000155e00046f800045a000000098520257600000013e274a1ad952cdbc23f16ea27d484a8d31b09f823c73b147a24135c9f400010c44f8a9b4f991c122218e0652238798611000000000000001a90146d2724000000117c6f517680000007bf0b5a9d41f66875220ea83e806a00001c4f2000001d80900009da4e30000cb00883f905a13d24e452e17d41f40002b715801127f553a190d4580000000c0cab44d33051c88bce3b41f103f87dc5d20000000000000275a4fd35e000000109c00000000000000000005420000000a9500019c13d46350000000ab680941f1ef80003f70260000eaa9ca2e6027d4ae8f005b0d812c646411a82c00003ef03580000006b71670000bd873c0000000000000000000106800000012980000002c50a68a640003bb95380002f404203410aa0000000c800002b210788e92ea4f7028908c0006c900028e10ba1fe0000798d8a000553a109020000189256c3326401c9a6702300004740cf84623763e7872c0000000f7a364e2064f17128dc0008eb000000000000044e0d700000000000a0cb3e00015a1ecc0002c411780000004d41528b3ca32a1e3a9a1a80000000000000000000352835444a9ba0de8be40000000190a20dfa000000000063e3d33582194f88000386000000088844580000007f3000000000000002c192d3440004810658000000000114926a000000128c0008503c008e069c0f83c998bc0008ff15c23d81ea00047320000000003e811b4ace7042db920c00017110a00000900000000001154a0e15180000008685522610ef80000000000c9c0001dd0000aa800034b0c046520000770270d1
  | 24 => 0xe24c24111bd00000002a600000000000e092508fa3a13840000000000000225c2ca0644391ded0b87b500009d821e57b46928bc4580004129fad52c7f600021840008920000001156000000068477873e35d84352d083f15e06b8058aa53570000000000389800006069500028013d600000016ac00000000000000000000000000000000000000000086b3f8a30043a52e000000048600039625985f09f71ad000022000018319cc91800000026d00000003b2026c2e03ec25ba2a000002f0000dfc2807bb40a00012265ff139835c73a96b0002544fd200000000008583da02aa4609900000000cc408086e000078c00000000008052920000341a2404c84c12e0598e709a73ae98f4ffe00023380000000004460feccd88202739e488b250d000161000000000000006e2000000059096a0000000000b1c00000000000008762d493ec00039f0002a0829e11b0001a2814860b2e8944005a8cc4ff800000088450a8eac87a0281a7a6dc00002300000000000000000000f1a00000000007ae000132052c83200a1d320f4b8c8a318c1a180008bf000242134a00000000000000003db1af00009ef292118c00000037780012ee6ab2f6824c186000073a7700f00000a484ec00000000000000004fe3f2a54000000002ea6209980005088000bcc0e4437946c00042100016cc0000000002144ed863c00000005a2000000000000096100018940302215191ad80742c90d014cc000000000000131e42d00000000004ed1ee000000000000000000000000000eb800000051e28c400016100000000ae67c46200000000000000000c246641d78000000848000000000000000000000008dc000283146a0002fca100000aa9450800042a39e28f800000018750919f535a000000181025c0000000c440000000000ff000067900000008e40070000044000000000141d3803a2000059c00000038a087c00000000008a40004a200012e4294479000191400000013680000000001120dc035a1e54d917f505466536600000000000000d502b08e92c4823864e00000007548982913fd8000bb84220000274b200000ec00000000001c39f0955844800016910b0000477800121e1c509a00000045263ef27f8ac23bb0c129c491000000000012f656934c13fc000000000000000000013786e4e6e62151800001a80003310f340000003cd21a471000007100001c254d50693940006ff01b0ced4b67670da144d4381422c1204951494c32a888caf06e9000022cb167390001ec060ea0900028984fe6d022a84b40005492500ce00000000828000f5094b0001df40c22b93160bacc8e0004c700000000002e1259028e00004f111cf8aa4b29680012ce84611e923800000000000005e600012ea95400000045c800001a6e606b0dd0614a4c42b80000000ab53
  | 25 => 0x468000000000000000014080000000000000000bc4000425000081a0004c285782180000991218c0c84e000000000000034f00000003b21248b542008c52f712e0d40a3429110a456c5a60a2828c2b21952eb000c64435600009a00005bc413000088003753500000004b00000000c7055f26780012884e200003bc8e60005119f58000699000000000058719ba6c400041400000007824e824996c94f20b100000006865f148d172d1ac28715525d0b464f24d9a80d06c703207860cac60002dca3600000000ed91c4000000411a1d50f6000000000000038d00010012ac00028f04e8f6200016a293cdc80004590000000000064236cb3400000000000007013de2044634000000000081c00000000000000000af80000002e7000000053000045490792a844a00026a134098d431988872c8160001590eea9d44b6057549a56a000063000000000000013da6b400000003023fd23a0e54000000000000000000000000001640002dd831119200000017840005580000ab4e6c00016b0078000702023800135600053780008165982aa951c9f80003d60e6008a9121aca7a0f16382000000000000000002149de4bf3c18000e7a80254186193e04531d68000000000461a2f0de24a800022c4fb48b302580002281ce000000000000018808a0f98a641868000b286c443b86fcf9051c31721e0c765e34469dfd2f461b24fa9c13cc6eb4fe22c05f453600011e86f82b04fda0c4bd4a862df983c00031c0c994bc00000000000005a400049d87e0e9000000010080000001f18d4145c00011b92c80000001eb281000043900000004a417520622040ee8f2000000000000050291a13c85f4445000047888036a952013019f2fb917927800000000005845d80000000bde00000019a073471d000000049695a51e9d7c0000000002ab8c940000c800003ba00000000003f40000000cbcd240000f42554e3c9653bc11eccd263100005801fe0000b690e809c000000000000039722806140001031d28000ef25b437b00000000000bf000126229f499912c0000004b80000c72000000000000059e08f80000009c12e419b80009001ab95940008f700000000001a60002084e165704b900000000000009aa948600038b97040001eb00012a92f25061c587f421c69b0001f0ca6219e55092b800081d000000000000049600003a600000029c84763303ca800086a00045a00000006910000000edc65047200000000004430f4512293a00000014a62f038d80000004be3ad972910e0002a080000009b5000000035800000000013928b732d9b940005440000ec45ee5ac29f87404165a8000000000000000000007b200000000c53c40002ac81b08ba1a400000000000000fc90584544dd00000000000000001bb80003df0001b340a65113ab94545
  | 26 => 0x1ea0000000ef40000000000000fc26cf000286c42e000000018872073013300008120000001eb51ce0002da9cb952e4c90a890a139a3c63751ccd0188704cd06200008fb35898309044e906e8e50d7c05e3d7176cff20bb0a817a0b4056831d01bc0005f82908000c6e00021026000006d94ca000007877a00d96302627a13a200004f20082b61f3911e00010c1b281c00001018adc97883c03e1f2400000000000000004a70000a78dce000000000126e12c041a994ca80000000e0040e3911e003b4e923643c280000005c30001a7400030400006cd28c0000000a00bd653400000000000004f900004840000000a24b7480e15993e4ceaa0b0000c50ee62e9000018063a0003f0014092227d0b1245019c00042c9d3400000031f800000013c3ba1110b920b322c000000052c0000068000613054930027e14100027f522a7161719c7c40a6d329c19d8e6487f17f107c6e468012a00010300000002a4000000000000012362d00000d880001390001dc8f9a00000018540004f00000c2108281b00007680000001ff800000095814104c000013800022647083170001a8483429700000000000001f80000000000379a99c5328dd05000000ac0c9403a8cc00080b46a0000df09363d799702ee92b000000000061900000000000000001d480005de24b096c6960003460de51d8a9d315a5a40002204f600000000000002464000562512a6280008f41022888000000000217cd5200051b0000b327d900020e00002cc4a10b940fc2f53a3800136000036400000000f938e154c00062912aa354e0047e4641f280001f100000006a62ef000000000000000029740001a21ba98a12b804212980008dc0000eb800142e5794d30d107142e4497937c00000041aa1c41ee00000011840009b600000000004334e3921c8928f14a011bc1447c70000bec7964da000210c00000002e0aa0c92021000000033a0002ea8000000000195203c00038f0000000bca02900013340000001a680010ac0005370600c469290198898e804bd0aa10c0cd48c72cd9c1c000a0f0219a349329913530ed4ca205a000192066a9a121d80013960003cb918068e0000a9800000013347e0000b00000000000070200000006d40000e600008d80000000000000c5a3bf00000000009980000000000000353800000000000000005b48b60000d1800000000005300007fd00025153460d940e0000c04219000206400000000000000000005470d9903499e44b2924000000000000039400020900001e073f2958ae8f0400021c000000015208e00000008f90000cc84d600054d25280000002b99934c124622a2800042c824170800000021e16f1ca50da0004ce8d440006d800006c80000000000d04000000248095816a65736300000005c700000000006164eb00006bc3830
  | 27 => 0x3cd8d8c3340000002714b3a54600000000000000bb055c98c00000000000008c20001e440000001bc00000000000001d880000000002864c0215616e139857c2ae42d892008820e1db1b5c85e0793e926480009c800000000001c000000012a61aa000000107400000001fc0000004e61548d3e592000153c00098c1d0075051a2c526b84a0ad60003618000000000306904520a01f0000001092000000000000000000017640009dd000124800000003300006a41011d407251702c7000000000000000018cc0009e12809090c3c51d21294385d42a612390a8c3048a3bb00810c80000030000f320002c79e7802e5300f71e295241e709091586fa19b28b13608fe56d025000000000023b10fc9569d5000000050a10b00010ac2d453e00025b465847752800004722090000000da40000001e3000007b00000006008450fb1ff03389390f20000cbc0700f10000000000000000000000017921480000000000934a5000008984a4b0a57d000173d2fa000191886d02e8ea1b09e603c257100029580000000001bb424e7a600000004941a514b1a50d661090001cb47669ee0000000a166c14e8800000000000000000006b94e800000007615399d5826a04f08422ec0548f31a601b439099500004f80004971858000000000000000000012200004a8000000068a78047c82f000250c5fa6830fa89a52381d94861ba12d400009e9edc24085e000000000000044a2a78d38000419106000000026900008a200019c8000f4e2d30000000bec46c0001afcb387a42f21af4000000422000024848d0000000e1a00049c29e858c5204a08938e6800006e020088c14e47f1d50000426000000000000000000000000000002a2ca1e72f12609c000033f08b09145380cc133a32cebc7f045e8000712a3a4b008b80005d733d80000002fc00011687cc4890001bb149c0ba2a128a40000001e280000dc00025600002f600000000000006dc33d1448d6a5970000000a5249e26187f07a87d126528811dc62403e8fe0f540000000000c3a00000007fc0003dd00015f079c000000000076e9be1500000b0c7ee3fd0000000000000234c0006671ac0a383e05b025a0fb4db41ec10826a8f5278f0000000a0a00000000007180000001cd4072a610081ac8000441145976800076508226909b60000000000cfea2827c0000cee000000213c000a514fc9dc4000656139033509623000018f82aa48520998400000d81e203c81d22a719a1c491c6646000098155a12306580004383554f29d700002c013d071086c5f23b49e5100a07a54482405580003b51d08aba17d1e780002f2404020997d1447dd06123448be9470001d2d12aa45260a640bf695d15ea9f80e40000000000aa05c50679f040000002210000000a6223587a40007a00000a847a024f0000001
  | 28 => 0x1e95210d1c94abc0004908a90e140004af00000005370000000e2260528204652c453c0000001456000321044511200000000000008852d894d4ed600000006503e6a023fb8ee400000000025b80003f24140000f081ea
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x394a7800000001f8030a19ea08024a11d8e002d2a80221b8000003113901e00092b002baf800000151a8b992d8000000f048880018000002e801a00000c8394000b230297a68016850a2c99980d878aaf24121b040026020125001328001729801f1c1c8310a90d0700258e8009958f92ae000000001880200680160080c1828000004000000045c04101c0010040000244c40082c10000c283c00000c18018344121d535874200513a5b734cb655092360c9650d32d954249683219434cb65508016449654d32d854217da1259434cb6150921a848650d32d854200691615320c46150801a85844c831185420058564c65d0c615080164593195321854200591654634c861508016469654d321854200591259534c8615084d6849650d321854200781d95434c86150801e046550d321854200591654734c8615084d685941cd3218542005b0640734c861508016859494d32185420078154f434c861508016459590d321854200781d4d434c86150801e055350d32185420069161532cc06150801a85844cb30185420061560f711d562d040705c985cd5358b410051325d534c962d0583c26621d47150a4100683611320cb65504018347420573594410060d210815cd651040181c7460c72594411440f25d848c96510401a0d844c832594411440f25d84085651045103e97e1130594411440f25d84c81651056503e97a1d65508410040f25d835954210401a0d834c965508410060d21c71595421040143497597715084100513e59734c9658840160d9498d32596210040fe61741d1658840144f9754d32d922156f119c5534cb648840548f9750d32d922101623e1d434cb6488559c867150d32d922100683611320c965d0001a0d834c96550b400050d25d651c542d0001a0d844c83259640006a1611320ca619000125593a177258640006a1611320c961900014c593188715894060f09188751c5425000103c985d5421854001c172617354d621000144c9754d32588400060d1048754d611000144e96dcd32d952000583650634cb654800144c9754d32591200161321d534c9644800548c9750d32591200162321d434c96448001c45534c871591200072150d321c5644800144f9754d32d8b102fc4d2617550841c400144c9754d3258a1000683611320cb654400188e874c832d91100062361d320c8644400188d84dca72d8d100052365032dcf624400188d84dce73d891000589251811946244001265989c4651891063ca9260645446244001a848418d51189104e7289c06418b41440010749660d751051000615218635d441440014359719764105100051965c651884144001c25751906210510007115d4631884144095134985d542105100060d219755084144001c446218d7588510007095d4621922144001a0d844c83259410
  | 1 => 0x3011272885880c061d2c118022aa2
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80001406d10e8c18e4b288200a0329d834c96550841
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4e
  | 8 => 0x138c
  | 9 => 0x5
  | 10 => 0x94b
  | 11 => 0x94c
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124c
  | 15 => 0x124e
  | 16 => 0x138b
  | 17 => 0x138e
  | 18 => 0x98c
  | 19 => 0x98e
  | 20 => 0x128c
  | 21 => 0x128e
  | 22 => 0x10b
  | 23 => 0x10c
  | 24 => 0x10e
  | 25 => 0xa0b
  | 26 => 0xa0c
  | 27 => 0xa0e
  | 28 => 0x130b
  | 29 => 0x130c
  | 30 => 0x130e
  | 31 => 0x180b
  | 32 => 0x180c
  | 33 => 0x180e
  | 34 => 0xb0c
  | 35 => 0xb0e
  | 36 => 0x140c
  | 37 => 0x140e
  | 38 => 0x28b
  | 39 => 0x28c
  | 40 => 0x28e
  | 41 => 0x148c
  | 42 => 0xb8b
  | 43 => 0xb8c
  | 44 => 0xb8e
  | 45 => 0x148b
  | 46 => 0x148e
  | 47 => 0x184b
  | 48 => 0x184c
  | 49 => 0x184e
  | 50 => 0xd0c
  | 51 => 0xd0e
  | 52 => 0x188c
  | 53 => 0x188e
  | 54 => 0x94056
  | 55 => 0x95394
  | 56 => 0x94054
  | 57 => 0x138d
  | 58 => 0x138954
  | 59 => 0x138956
  | 60 => 0xb0954
  | 61 => 0x94b14
  | 62 => 0x94d
  | 63 => 0xb0956
  | 64 => 0x94b16
  | 65 => 0x1409
  | 66 => 0x140954
  | 67 => 0x95414
  | 68 => 0x140956
  | 69 => 0x95416
  | 70 => 0x289
  | 71 => 0x28954
  | 72 => 0x94294
  | 73 => 0x28956
  | 74 => 0x94296
  | 75 => 0x184954
  | 76 => 0x95854
  | 77 => 0x184956
  | 78 => 0x95856
  | 79 => 0x209
  | 80 => 0x1449
  | 81 => 0x1489
  | 82 => 0x14c9
  | 83 => 0x139256
  | 84 => 0x139254
  | 85 => 0xb1394
  | 86 => 0x138b14
  | 87 => 0x138b16
  | 88 => 0x141394
  | 89 => 0x139414
  | 90 => 0x139416
  | 91 => 0x141396
  | 92 => 0x29394
  | 93 => 0x138294
  | 94 => 0x29396
  | 95 => 0x138296
  | 96 => 0x185394
  | 97 => 0x139854
  | 98 => 0x139856
  | 99 => 0x1649
  | 100 => 0x134b
  | 101 => 0x14b
  | 102 => 0x141294
  | 103 => 0x141296
  | 104 => 0x148114
  | 105 => 0xd0a14
  | 106 => 0xa0d14
  | 107 => 0xd0a16
  | 108 => 0x188a14
  | 109 => 0xa1894
  | 110 => 0x188a16
  | 111 => 0x29313
  | 112 => 0x29314
  | 113 => 0x149314
  | 114 => 0xa4d
  | 115 => 0xd1814
  | 116 => 0x180d14
  | 117 => 0xd1816
  | 118 => 0x1049
  | 119 => 0x140b14
  | 120 => 0x140b16
  | 121 => 0xbcb
  | 122 => 0x19cb
  | 123 => 0xb8293
  | 124 => 0xb8294
  | 125 => 0xb8296
  | 126 => 0xb9494
  | 127 => 0x28b94
  | 128 => 0xd0294
  | 129 => 0x28d14
  | 130 => 0xd0296
  | 131 => 0x148b94
  | 132 => 0x148b96
  | 133 => 0x14cd
  | 134 => 0x185496
  | 135 => 0x185494
  | 136 => 0x149854
  | 137 => 0xd1494
  | 138 => 0x148d14
  | 139 => 0xd1496
  | 140 => 0x189494
  | 141 => 0x149894
  | 142 => 0x189496
  | 143 => 0x20d
  | 144 => 0x154d
  | 145 => 0x194b
  | 146 => 0x164d
  | 147 => 0x74b
  | 148 => 0xbd393
  | 149 => 0x4956
  | 150 => 0x1a49
  | 151 => 0xec9
  | 152 => 0xbc953
  | 153 => 0x2cd
  | 154 => 0x2c9
  | 155 => 0x24211
  | 156 => 0x28211
  | 157 => 0xecd
  | 158 => 0x1a4d
  | 159 => 0xecb
  | 160 => 0x1a4b
  | 161 => 0x954d4
  | 162 => 0x249
  | 163 => 0x95456
  | 164 => 0x131816
  | 165 => 0x28113
  | 166 => 0x181316
  | 167 => 0x181496
  | 168 => 0x180d16
  | 169 => 0x180e96
  | 170 => 0xed853
  | 171 => 0x1a5853
  | 172 => 0xe8293
  | 173 => 0xec293
  | 174 => 0x1a4293
  | 175 => 0xbc293
  | 176 => 0x19c293
  | 177 => 0xbc253
  | 178 => 0x44d
  | 179 => 0x29316
  | 180 => 0x28a16
  | 181 => 0x198d
  | 182 => 0x28b96
  | 183 => 0x29556
  | 184 => 0x29616
  | 185 => 0x28d16
  | 186 => 0x296d6
  | 187 => 0x29796
  | 188 => 0x28e96
  | 189 => 0x18c293
  | 190 => 0x28e93
  | 191 => 0x29a93
  | 192 => 0x28753
  | 193 => 0x74293
  | 194 => 0x75853
  | 195 => 0x29953
  | 196 => 0x194293
  | 197 => 0x195853
  | 198 => 0x75493
  | 199 => 0x20291
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1667
  | 6 => 3800
  | 5 => 2736
  | 4 => 99
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (67784+((h/555+packedAt gbK7 (61679+(h % 555)*11) 11) % 2001)*12) 12
  | 6 => packedAt gbK6 (198858+((h/1266+packedAt gbK6 (182400+(h % 1266)*13) 13) % 4561)*13) 13
  | 5 => packedAt gbK5 (173280+((h/912+packedAt gbK5 (161424+(h % 912)*13) 13) % 4370)*13) 13
  | 4 => packedAt gbK4 (7194+((h/33+packedAt gbK4 (6930+(h % 33)*8) 8) % 143)*8) 8
  | 3 => packedAt gbK3 (164+((h/1+packedAt gbK3 (162+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f01ff80ffc0fffc0fffffffd13f3f1a31f1ff
  | 1 => 0x81fe0fff07ff07fff07c03c02ed8d9e5ce7ecc
  | 2 => 0xfffff00007fff83fff8003fff0e0e1fe0f8f0f
  | 3 => 0x1fffffff800003ffffffc003f00fe07f00ff0
  | 4 => 0x1ffffffffffffc0000000003fff0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1200228009400a4400a54a54800b0b0810b055
  | 1 => 0x901605b102d1069d10681a8186585960c656cc
  | 2 => 0x65ab500844aad02aad00212b30a0a0b60b0b0a
  | 3 => 0x21cd995ad0084033ce52b0023b00f407600da0
  | 4 => 0x41f1ee6ce73ce5008400c00c3df50007bde000
  | 5 => 0x7881007080308603086302303ffeffd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36691
namespace PEqualNP.Outside.L_meta_36691
open PEqualNP.Outside.L_meta_36691.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 60 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_160 : Interval s2Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 165 := (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat bs2_4_96 (concat bs2_4_128 bs2_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 50 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
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
theorem bs3_4_64 : Interval s3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 bs3_4_224))) (concat (concat (concat bs3_4_256 bs3_4_288) (concat bs3_4_320 bs3_4_352)) (concat (concat bs3_4_384 bs3_4_416) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 13 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 75 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_608 : Interval s5Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 626 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 bs5_4_512) (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 699 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 bs5_5_384) (concat bs5_5_416 (concat bs5_5_448 bs5_5_480))) (concat (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)) (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 99 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_2720 : Interval gbAtlas 5 2720 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2736 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)))) (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152))) (concat (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)) (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)))))) (concat (concat (concat (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504))) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)))) (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824))) (concat (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)) (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016))))) (concat (concat (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))) (concat (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)))) (concat (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528))) (concat (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)))))))
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
theorem bgb_6_3776 : Interval gbAtlas 6 3776 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3800 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)) (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)))) (concat (concat (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)))))) (concat (concat (concat (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080))) (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336)))) (concat (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560))) (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816))))) (concat (concat (concat (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)) (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 bgb_6_3040))) (concat (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296)))) (concat (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520))) (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776)))))))
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
theorem bgb_7_1664 : Interval gbAtlas 7 1664 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1667 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0eeeaeae0eee8eaa0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372960 * 2 ^ 32 + 4008241824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36691.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.and,[1,4]⟩,⟨.or,[5,7]⟩,⟨.and,[0,4]⟩,⟨.or,[6,9]⟩,⟨.or,[3,8]⟩,⟨.or,[2,3]⟩,⟨.and,[10,11]⟩,⟨.or,[0,7]⟩,⟨.and,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4008241824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4008241824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36691

open PEqualNP.Outside.L_meta_36691 in
theorem PEqualNP.Outside.L_meta_36691 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4008241824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4008241824) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
