import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36741.Model
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


end PEqualNP.Outside.L_meta_36741.Model

namespace PEqualNP.Outside.L_meta_36741
open PEqualNP.Outside.L_meta_36741.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 6, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36741

namespace PEqualNP.Outside.L_meta_36741
open PEqualNP.Outside.L_meta_36741.Model
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
end PEqualNP.Outside.L_meta_36741
namespace PEqualNP.Outside.L_meta_36741
open PEqualNP.Outside.L_meta_36741.Model
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
  | 2 => 0x3f80ff03f81fffffe07c1f07c0fc1ffff4923f
  | 3 => 0x3fff0003ffe03f81ff801ff800ffe0f818e3cc
  | 4 => 0xc0000003ffffc001ffffe00000ffff001f03f0
  | 5 => 0xfffffffc00000001ffffffffff0000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80840a000800810001842108461421094124d5
  | 2 => 0x1552946594d52a68f059164688a91ad694922a
  | 3 => 0xa64aa6aaa553b42b76c21bd212cf48e0d8e34c
  | 4 => 0x346cd8d3469a274dbb6f508424f39c431f03b0
  | 5 => 0x3870e0e3871c3871dc739ce7388210841ed800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0aaaaaaaaaaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36741
namespace PEqualNP.Outside.L_meta_36741
open PEqualNP.Outside.L_meta_36741.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2a4c480144688d042e6462000000004a00280487c01d1a55080009d680521d613003801b16581801e0009e00000060020010120089804ace0014a004080040018506200010200100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1f650b4e6000003f001c62660000001600491a3932000f485b71630055383c000000005800002a18006f005e0000006923421064002c17194774265661540027000059005200700000000000006e4400226c001b00000072000c136d6b3e0d33430741004a403b6a36011445055f2b241d021235005a082109535c3730730029004d20340a00000e00572f46004c6706045d5015314b1e005100002868112e000000032d3a003d25004f0080830000008184888480010300018202040082000b00038080800200000180020400000d0002db94b43b6a96877651d0eeaa3a1d794f42aea9e857651d0aeaa3a157d4d42ae29a85775150ae8a2a15ed4142bc282857651ccaeaa3995794a32bba8a6574514ca7ca8194f55032cf2a0659d540cabca4197394832e721065cd420cabca7a0d754f41b7296836d52d06dea498db14931ea98863d632c87a86590d794e21aea9c43cc32886eca310d7d4d21ae29a433e540867aa810f30c821db2a043b554086eca410f994821f321043e542087ce6410f58c821ea19043e432087886410e78ca40ce19481b7219036843204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521033c6420670c840db28881b5511036e42206d084409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2eca2185d544309f2a6413d54c837081905794e20aea9c41cc32882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a290730c820f210841b8400827ca9884f553109faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x20050c02201e000900100b0a71602e390620a806a60060024a80000401c0548b1185420cac86050832b1189310c70d540c821b118d42086e06050821b198a32086a5640c821e19903208785640c821e19503208785540c821e10c8219030d535484087594321032552544408d5942110384320844099189510c3443294620d194c21883883210020e8084400824c6254c10
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xc02100a0aeb3206410c85769503208682ba86410881815943208440
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s2K5 (841+((h/15+packedAt s2K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s2K4 (3471+((h/39+packedAt s2K4 (3159+(h % 39)*8) 8) % 170)*8) 8
  | 3 => packedAt s2K3 (960+((h/8+packedAt s2K3 (912+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s2K2 (199+((h/1+packedAt s2K2 (196+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 1 => 0x7f01fc07ffe07fff83e07c1f80fff83fd933c7
  | 3 => 0x7ffe0007fffffffffc007fe000ffffffe1c3ff
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c228e2c42520a561b
  | 1 => 0x2a4c51cb224728e581aa351b1255ca34d932c5
  | 3 => 0x44289a95448a514ab4105b48249a94a961c16e
  | 4 => 0x68b1636689141db35adb021248e36711be03b0
  | 5 => 0x70c183870e1861dc631c639c70038421f5a800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaee008800eeaaaaaaee008800eeaaaaaaee008800eeaaaaaaee008800eeaaaaaaee008800eeaaaaaaee008800eeaaaaaaee008800eeaaaaaaee008800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36741
namespace PEqualNP.Outside.L_meta_36741
open PEqualNP.Outside.L_meta_36741.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x186802c8710120504a1e00de43dd43de32dc32de31dc31f721f421df30dd30f710f510
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x100c10aa28a871d540ca3aa9985914910
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s3K3 (111+((h/1+packedAt s3K3 (108+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fffffc0fffff03ffff83ffffc0fffe7c7e3f
  | 1 => 0xf80fc0fff03f07fc3e07fc3e07ff0781b3b3cc
  | 2 => 0xfff000ffffffffffc007ffc007ffffffc3c3ff
  | 4 => 0xffffc007fffff8000007fff801fc03f0
  | 5 => 0xffffff00000007fffffffffff8000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x10a10804608221004628804a31484c94141615
  | 1 => 0x32629948a3942b2c1aa3a42c52d9450cb1b2cc
  | 2 => 0x4144a2910528845581054a8084a2926942c16a
  | 4 => 0xe58b3ce24a0eb79aedb06229273ce431fc03b0
  | 5 => 0x860c30c38c30c6e331c67331c0308041eb6800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36741
namespace PEqualNP.Outside.L_meta_36741
open PEqualNP.Outside.L_meta_36741.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8000000000018b002474d8000005a24aac01c0030002003930a008c000082138f26a001500695052064198481ca203ca5089007cb911a3120c0004040000240000ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb2603801c05a78019001387a2081180020009909e0e19a39880000e801b95000000000000000000142b251712018000049800209c861680210005002b9d002403291e800000071a248017a1ac02800000042a00001f00000f800ba28a1da6911b1a88a580000013200f00001000000caa800d808009002716128d0c158014ac8680000001001fa88aa300000029a800c00140400040c0000000004080c0c040400041400040410040004001412baa921d794643bba8a87745150f3ea8a1f5d4543ae28a87d45150ea8a2a1d794c43af29e855d53d0b3a87a15d94742baa8e859d4350abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d073a87a0db94b41b6a96835f53506b8a6a0e750d41af298835d53106bea918d755231af28c633e540c67aa818d7d5031cf2a0635d540c73aa818c755031af28863d6510c7ae8218f5104319f2a6433d54c86bca790d754f21ea18e435f53486b8a690f50c421af29e815d53d033a87205794c40aea98819d43102dca4205b54840bb2888175511027ca9984f55330bb28c6175518c27ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb288417551083a863885794e10aea9c213f5444278a88857d4d10ae29a216f52442d8a488750c510
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2e02001e01421239609ca1a106a8a30003098002402c89801000000000204306946150f42c550d51d0a946150d42951855310a946150f41c350d52d061d6595031c5185540c71554d0431b198b410c6556510431a559031c8716540c721875905348695640c4219518553d02946150e40a5185431030d4354840c550d5110295640c710875925384295640c510c51503144344520c510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x900298020028238a86a96838155262d043182aed2a06390d047150d521020abb0a818a2181590520c510
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
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2670+((h/30+packedAt s4K4 (2430+(h % 30)*8) 8) % 143)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s4K2 (302+((h/2+packedAt s4K2 (294+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe03f07ff81ffc3fc3e0ff8781ff87f034ece7c
  | 2 => 0xffc007fffe0fffffc00fff801fff87ff8f0f8f
  | 3 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x428400230400800046110088c50089281050b5
  | 1 => 0xc98a4a451ca5052c1a8748514b48521946c65c
  | 2 => 0x5129488286a2255810a9502129504d28b0b0a
  | 3 => 0x962ce7125143ab9aeda0c4449ce66063f00de0
  | 5 => 0x1830c61c618c33e331cce66700c44083eda000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0eaeaeaeae8a0e8a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36741
namespace PEqualNP.Outside.L_meta_36741
open PEqualNP.Outside.L_meta_36741.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa437c53487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410df94421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea98817e52102faa4205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30bea94617e518c3eca3185d94630bea8c61f5518c2eaa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd20421f940843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ee62887d0c510fb10a21f521443f480887e50110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020fe94041bd280837d50107f2a020de54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f7cca31ee994637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863df430c7b88618df94831bea9063df320c7ba6418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9
  | 2 => 0x134a48689f8163da2b1331b90744e8148fa11489c2da492ce000d20063a8250cd0d347605c789f23961290812600068897a3e2440012704409e0286b00000090c000001a86f06d10c340464b11700fc628b18770007b80e125000001049e10c60000004147e0006900000000119a2f0ea000f998648e478fa1bd2128310422b3d81c4e10dc3c876c1f0000d05fc73a5f11c73cb007c1c4000cd9b81bc404529063e22184f9ca1187d52814e2aa38cef16e310838011350627e0c984e2d691894800478000ca2601880ac8b9c521c32c2a2403c03a08510836c3092b9210760dc3d0fc472325241da3c68c05f005284481288e911e00c6a86a030570af07f4bc82c670ed14e3401aa5b1ca1e0ff91d4ac1090d96a408774228893ce1d0c7232206284308220c80747993634292c642382983d8171121a21f44c1460ae7882e9c03fc2dcd683923e0003580000041cd4a1f19e194d582127c800f2800000000e71b71ea000590fd4a6000001b413857421a120006f84805645a034a50003000004d8a44220005e999134000002023301bcdd04c4c27987c9d012c000120ee48a328f50950007602f9a707e55c500a3160335319403588d0089a5170000be2140ce064510000d82b91d097058710d998c3d6928eb123452054001cc0008740785900e2d09d9c62722c4531fd0128a8c38002648c4899280da3dc151c933c5a480130036000bd0762163d0a0a0128e43c080000008dc579851766a8000d848457c0006923820c77833000000000000002a08d9fa350748c09103122a442a190006c4a288004670c959b22ac9606f8000006c08b0932a44140016c00049c6084d47a1c80023500055055a152e65c8731924422650f1c10903313215a2a04101b0280007c0b30e104a3a8790842ca8a1032553f28804394b2e24602f0790007a11194f13a000000000000000019f1fc2e4bc0b60786fd038000005d0000002fa100a40ad4ba85c5a9bb3aa000000003ec4b8d79ae2044f4330e438e3ac491d70100005981f0000200400020060040001005004020280e014060000004410008020740c0241405801004010580200c0b01803064000880501c010681001415000010000a01c0100c0000000014081181c0340003c010040a03006010010101a0100e010010100101004000000040300003014040581001c1700801014020001604c160480400c05008000600d01c090b800008050002e00004014070040101c010080106000000020000503c06000130000a0280b00006000000103200400054030080400c060040a000000141702c020080300c0008c0101c20014031140100c100040001c0d01401004030040004c0f004041440101c000080d0000004c0101c081500bbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x703a25e46d8000344e0291d3000245310001d85a0ca98d4a807d068bf42c5dc8a0041fe4692225a18c36446800000000000000000009600000002cac9491800e00000005e83ca1a132ec2780005840a0000000000076532a264b293c258002fc6980003444a0c8c8851174720628002f6584c816f26899ccb24d000000001582480012e00c0920c0cb9a3278000da800000870000002547700f046000188552412b6591120001862091705a1783c0c786e3be000869fb22a1cc070dd29a204000140a07f0001cd3384c499800002000002360007dc0002d3de000638000005d4000270244dca98531c0828b691125a3e10c08b0c00811118330411cc218b0aa220a203d0f6001018fb498000000d7000544ce85c4587a4130
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1425023e65d0540a718d415025f63544409718d51103576354440d518d511023d6590440cd54641103355110440ae580411033551d0040dc546401023f6550040cd545401027b6550040dc545401026e62153309b58854cc2d8604cb309d987548c27561d52309d984548c2756115230cd952518c3355494630cd951518c3355454630c7952318c31e540c630d5544318c26f62551309b189544c27761551309d185544c23e64149308f590524c34c524c9309b988540c26d62150309d984540c27561150308fd91510c23c64544308f992500c23d649403097d95300c27b654c0309798c54c825d63153208fd9153c823c6454f209dd8553c82746154f208f99053c823d6414f209d984548827561152208f993538823d64d4e209d987538827561d4e208fd91518823c645462097d8d518825c635462097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d209ed81534825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c20d6181530823e6414c208f590530825e6314c209d98453082756114c20cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420d9546210835953cc0209e594300826f65480209ed95200823f6454f108f19153c423e6494b108f59252c425e6394b109758e52c42d463507109798f548425d63d52108f993538423d64d4e108f990528423d6414a109798c528425d6314a108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110cd58454443396015110c7d53534431c54d4d10d5587534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c52443656114910cd15241442746550510b518d414427665cc510cd153314436452cc510bc9833144334540c510d5d4c3144364520c510d914a21442746548510bc18121443385490110ec90640442786550110ec505404423d65950108f990540427661150109e980540423e64d4c108f593530427661d4c108f990530423d6414c109b988530426d6214c108f993520423d64d48108f990520423d64148109798c520425d63148109d984520433554c40109e596100433954840109dd95100433554440109ed9510043395444010
  | 1 => 0x802010000180c018030100100402004060080401801040090040700c1d000000200e01400000000000202c0300000000010001a00c0001806010020181300c0000c000000a00801038040000100000000019d9865090e756194243d5d0c5150f3643145438fd954310eb46150c4397d954310ed46150c43cbd0d5210f4e4354843cb50d5210f4d4354843ad18543d0a5f63547429718d51d0aad6210e428f9974350ab46150d429d9845050a7561141429dd855310a746154c42d5d855310b546154c428f5964310b1d5390c42c754c4310aad6210c42c754f4210b4d53908428fd954210b1d53508429bd954210b4d5350842b518543cca3f64547328f19151cca3e64943328f59250cca7661943329d58650cca7661d52329d587548ca3e64951329d986544ca7561951329e982544ca7960951329dd85544ca7461551329ed81544ca7860551328f994544cb1d6315132cb588544cb1c5490d3297195434cad46150d32cb152424cb8e43909329b195424cb8d4350932cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb7051141328f596540ca3e64150329798c540ca6e6215032c7553320cb2d548c83297d95320cb1d544c8329bd95320cb2d544c832ab588439065e6394a419758e529075453d0541c714e41506ad6210c41ad587421063f6550441a718d41106776550441b518d411073a4354041ce10d501073b4254041ce509501073b4154041dc90550107394154041dc505501066e62153319b58854cc6f160107318f99250cc63d64943319e980548c6796015231b3588438c63e6494a318f592528c69c644ca31d3949328c6d8604ca318f992544c65f63551319dd85544c63e6515131cd153314c71c548c5319b988540c66d62150319e980540c679601503197594430c6cd6210c31a7191320c6d7614c831b6181320c6756510431e510c410c6f1601043197d95310c69c644c4319dd95310c6b4644c4319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f21d5d8553c863e6414f218f59053c873654cc721cd95031c8755530c7219e980548867960152218f993538863d64d4e219e983538867960d4e2197d8d544865c63551219ed81544867860551218fd91534863c6454d219dd85534867b6054d219e181534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e5208675650c4219bd95210867765484219dd8553d02746154f40c754c43d02ad6210f40a718d41d02b96010640ab588435025e63149409758c525032c5250940ae18
  | 2 => 0x208588f848a6a402321708646300c6916501207a938390000000c2ba38001b4140b20000093a1c00000bb000001b200000001ae0000000242000003fac80010e0a18c7d144928be0e000611bca3aaccd21a659de3294c1fa76c12f6c584664ad8ad32e5e1e0a68000026c8a020000005d31400000001dc00288001120026e00000540e2cb246a02b6ab8000017c621ac63ad4022c00031c7a2f20c072001c28a8000022c2d1260000000000b8800000003633ab280000000a2800618c0159d67b00a25a26200001b1c00016c3700072266181f23500057800910c6692748b914728000008e003220b932000007b8cc9f0ac00200cc800a90007f0001b8000030c878000000000000a60003d800001beb7a3c0c800cc0005580084b10a794a0000020a3a0f80000000210004209c0007a000000023e5080079000000da8131e0000024272002929c1e6731762e2a000252bd3244b81eb1800572242e800719d23ba844d1240022200000000ce668c28dafc6c2a26a972a31a8288129e0882c1d87fa5a3a16a9a000c824812000000003e8fc299a00d8063994e42a564d9980000098a968c040b59da838aa4427a832fe002900000000000011f61505224800b42c22d8004180000000b98160608a671a21d88c828f06280000010000d0002e400000002b80006247954c9898001f80a800000001686a0525ec204a09a86b68bc0023400000ce1b6af0001d0009f800960c40001a282f83b0440029c0393c00000ac2a834ad200000130000031200160ae8580000046800c38000e9ce002dc1f000a500000024750000b2beba00037a54432aa278004a04ebeb367c00010800002b24e92a00000002140001c26a50001a69330a4c000b805e970f45a00059822ca17a0000000000c08645c1b8001fab30000d19e60868789642515a6500299000000a8001483210274220001525faee6eb060000000000b132a0020600000c62a6860a4000004b0700000019a1051aea35a82001580f2607116e000006011cb3af01e0ea9013e64216382023c9040180004400000050140300001020140080000c040080900800008070100900c050000301c0a00c170000000001024020000300007010080340000007000040002501005000030000000800004020000200001014020100607c0b00
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x90405800843004c53512c02885cf0c600001438040701501260014084080583491c54354843a88e2a1aa421d147154c4310a8a38ac62a2658358d6215132b08e2a1a8499494735874210694b9086a80834c5c74254041a30e6a0aa020d50735055010686ba4a499463615c84310431d2086b008218d147154c43d0306a9ac421e81435cc5250940962e230284a0514735444110286ba0a499261451cd6115110c62c2b00a8884b1749833144258ba0c090a21641cd4150110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x80006240a048158d6215132910835c74254041a818210d6010431a048154d6210f40a10835856015110
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (18682+((h/205+packedAt s5K5 (16632+(h % 205)*10) 10) % 740)*11) 11
  | 4 => packedAt s5K4 (17112+((h/138+packedAt s5K4 (15732+(h % 138)*10) 10) % 600)*10) 10
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (304+((h/1+packedAt s5K2 (300+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe07ffc0ffffffe07ff07fe0ffc3ffffb1e31ff
  | 1 => 0xff80fff01fff07f83ff83ff07fc3fc05e3ce7c
  | 2 => 0xffffffffe07fffffc0003ffffffc3ffe03ff8f
  | 3 => 0xffffff8007ffffffc0007fffc007fc0ff0
  | 4 => 0xffff0000000007ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x290a4462441242014b424a84940665510e10b5
  | 1 => 0x432648a1c9244a58154a16942c42a83162c65c
  | 2 => 0x84149104834884aa808425294aa812a6016b0a
  | 3 => 0x1658a249120e9534e6948108733100c6b40de0
  | 4 => 0x1860c38e1c70e7c738e739ce02222307dbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0eee0e8a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36741
namespace PEqualNP.Outside.L_meta_36741
open PEqualNP.Outside.L_meta_36741.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5005fe5401ff55005fc5401ffd4c07fe5301ff54c07fc53017fd0c01fe43007f50c05fc4301ffd4803fe5201ff54803fc52017fd0803fe42007f50803fc42007fcc803fe32007f4c803fc3201ffd4407fe5101ff54407fc51017fd0401fe41007f50405fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50017fd0001fe40007f50005fc40007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ff08210027fe2108013f71084001fd884200cffd9510065feca880037f65440013fb2a200cff9951001dfcca88033fd65440197eb2a200cff1951001df8ca880337c65440073e32a2000ffd9110005fec888003bf64440015fb22200bff99110015fcc888003fd64440017eb22200bff19110015f8c888003bc64440055e322200cffd511005ffca888033fd5444017fe2a22000ffd8d10005fec688003df63440016fb1a2000ff98d1004dfcc688003fd63440017eb1a2000ff18d1004df8c688003dc63440016e31a200cffd4d10067fca688033fd5344019fe29a200bffd0d10007fc8688003fd4344017fe21a2000ffd8910005fec488003ef624400177b12200aff9891000dfcc488003fd62440017eb12200aff1891000df8c488003ec624400376312200cffd4910057fca488033fd5244015fe292200bffd0910057fc8488003fd4244015fe2122000ffcc910057fc6488003fd3244015fe192200cffd4510067fca288033f65144019fea8a200cfd54510067f8a28802fff4144001ff20a2000fd90510007fa8288003f54144017fe20a2000ffcc510007ee6288003fe3144001fe98a2000ff0c510007e8628802bff2144001ff10a2000fd88510007fa4288003f52144015fe10a200cffd4110027fca088033fd5044009fe282200bffd0110027fc8088003fd4044009fe2022000ffcc110027fc6088003fd3044009fe182200affc8110027fc4088003fd2044009fe1022000ffc4110007f62088013fe1044009fb0822004ffd9410025feca08013fe65040077f3282004ff5941003dfaca08013fc65040097e3282004ffd9010025fec808013fe64040057f3202004ef990100157cc808013fd64040017eb202004ef590100057ac808013fc64040097e3202007ffd5010037fca80801ffd540400dfe2a02004ffd8c10025fec608013fe63040137f3182004ff58c10005fac608013fc63040097e3182007ffd4c1003ffca60801ffd530400ffe2982006ffd0c10007fc8608003fd430400dfe2182004ffd8810025fec408013fe62040037f3102004ff58810005fac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902006ffd081002ffc8408003fd420400bfe2102000ffcc81002ffc6408003fd320400bfe1902008bf9841003ffea20801ffe510400ffea882007ff14410037fe8208003fe4104001fea082006ff10410007fe6208003fe3104001fe9882000ff0c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x2fc6148027ffa8a4013ff9452009ffaa29004ffc5148025ffa0a4000ff90520007fa829004bfc4148001ff98a4000ff8c520007fa6290003fc3148003ff90a4001ff8852000ffa4290007fc21480037fb024013ffd4120027fca09004ffd5048009fe2824012ffd0120027fc8090003fd4048009fe2024000ffcc120027fc6090003fd3048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048011ffb2e2008bfd9710047fccb8800efe65c4011feb2e2008bf59710047f8cb8800efc65c4001ffb262000bfd931008ffcc98800afe64c4001feb262000bf5931008ff8c98800afc64c4011ffaa62011ff95310047faa988047fc54c4001ffb1e2000bfd8f10007fcc788026fe63c4001feb1e2000bf58f10007f8c788026fc63c4011ffa9e2008ff94f10047faa788023fc53c4023ffa1e2000ff90f10007fa8788047fc43c4001ffb162000bfd8b10087fcc588006fe62c4001feb162000bf58b10087f8c588006fc62c4011ffa962010ff94b10047faa588043fc52c4023ffa162010ff90b10007fa8588043fc42c4001ff9962010ff8cb10007fa6588043fc32c4011ffa8e2008ff94710047eca388023fd51c4011faa8e2008ff1471008ffe8388003fe41c4001fb20e2000ff50710007ea8388047fc41c4001ff98e2000fdcc710007fc6388003fd31c4001fe18e2000fd0c710087fe4388003fe21c4001fb10e2000ff48710007ea4388043fc21c4011ffa862004ff94310047faa188013fc50c4023ffa062004ff90310007fa8188013fc40c4001ff9862004ff8c310007fa6188013fc30c4021ff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb0800efe6584009feb2c200fbf59610027f8cb08012fc6584009ffb242004bfd9210027fcc90800afe6484009feb242000bf59210027f8c908012fc648401fffaa4200eff9521007ffaa90803bfc5484009ffb1c2004bfd8e10027fcc708026fe6384009feb1c2000bf58e10027f8c708012fc638401fffa9c200fff94e1007ffaa70803ffc538401dffa1c2000ff90e10007fa870803bfc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc628401fffa94200dff94a1007ffaa508037fc528401dffa14200dff90a10007fa8508037fc4284001ff994200dff8ca10007fa6508037fc32840197eb0c200fffd461007ffca30803ffd518401ffe28c200effd0610007fc8308003fd418401dfe20c2000ffcc610007fc6308003fd3184001fe18c200dffc8610007fc4308003fd218401bfe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fe9
  | 2 => 0x3004dfcc618027ff530c013ff2986009ff54c3004ff8a618027ff430c013ff2186009ff50c3004ff88618013ff620c009ff3106001bf98830027fac418002fd620c009fe3106004bf188300c7fea41805bfe520c031fea906016ff148300bffe841805bfe420c001fea106016ff1083004ffe6418027fe320c013fe9906009ff0c830027fec218013fe610c0017f3086004ff58430005fac218013fc610c031ffa886018ff944300c7faa218063fc510c02fffa086000ff90430007fa821805ffc410c013ff9886009ff8c430007bc6218027fd310c013fe1886009f70c4300b7fe4218003fe210c001fe9086016ff08430025fcc018013ff500c009ff2806004ff54030027f8a018013ff400c009ff2006004ff50030027f88018013ff300c009ef9806004ff8c030027f46018013fd300c009ee9806009fe4c030027fe4018013fc200c009ffb2c4004bfd9620027fccb1000efe6588009feb2c4015bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc91000afe6488009feb244000bf59220027f8c910012fc648802bffaa44014ff952200affaa910053fc5488009ffb1c4004bfd8e20027fcc710026fe6388009feb1c4000bf58e20027f8c710012fc638802bffa9c4015ff94e200affaa710057fc5388029ffa1c4000ff90e20007fa8710053fc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944004ffd8620027fcc310002fe6188009feb0c4000bf58620027f8c310057ff518802bff28c4015ff546200aff8a310053ff4188001ff20c4000ff506200a7f88310003ff3188001ff18c4000ff4c620007f86310007ff2188003ff10c4000fb8862000ffa4310007fc2188003f610c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fe9844004ff0c220027fe4110013ef2088003fd9044004ff08220027f0411004fff65480277fb2a4000dfd9520004feca9004ffe65480077f32a4013ff5952009dfaca9004ffc65480077e32a4013df1952001cf8ca90003ff64480017fb224012ff99120015fcc890003fd64480017eb224012ff19120015f8c89004fff5448025ff2a24013ff55120097f8a890003ff63480017fb1a4000ff98d2004dfcc690003fd63480017eb1a4000ff18d2004df8c69004fff5348027ff29a4013ff54d2009ff8a69004bff4348001ff21a4000ff50d20097f88690012ff6248003ffa924001ff9492000fdca490007fd5248027f6a924001ff1492000ffe8490007fe4248003fea124001ff1092000ffe6490007fe3248003fe9924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c29000
  | 3 => 0xf20e6000ff50730107f88398027ff31cc013ff18e6009ff4c73004ff8639807fff21cc001ff10e6000ff487300fff84398087ff50cc009ff2866021ff54330027f8a198083ff40cc009ff2066000ff50330027f8819807fff20cc009fe1066004ffd9630025fecb18013fe658c0077f32c6004ff596300f5facb18013fc658c0097e32c6004ffd9230025fec918013fe648c0057f3246004ef992300157cc918013fd648c0017eb246004ef592300057ac918013fc648c0097e324601effd52300effca91807bfd548c03bfe2a4601bbf58e300f7fea718027fe538c03dfea9c6009ff14e300effe8718027fe438c001fea1c6009ff10e30027fec518013fe628c0037f3146004ff58a30005fac518013fc628c0097e314601effd4a300e7fca51807bfd528c039fe294601dffd0a300e7fc8518003fd428c039fe2146009ffcca300e7fc6518003fd328c013fe1946004ffd8630027fcc318002fe618c009fb30c6000bd98630027fac318002fd618c009fab0c6000bd58630027f8c31807bff518c03dff28c601eff546300f7f8a318077ff418c001ff20c6000ff506300eff88318027ff318c001ff18c6000f78c630007fa6318027fc318c001ee18c601cffc8630007fc4318003fd218c039fe10c6004bf98230027fea118013fe508c009fea846004ff14230027fe8118013fe408c009fea046004ff10230027fe6118013df308c013fd9846004ffc8230027f8411806fff654c0377fb2a601bff9953001dfcca9806ffd654c0377eb2a601bff1953001df8ca98003ff644c0017fb22601aff99130015fcc898003fd644c0017eb22601aff19130015f8c89806fff544c035ff2a2601bff551300d7f8a89806fff534c013ff29a601bf794d300dffaa69806fdd534c013fe29a601affd0d3004ffc8698003fd434c013fe21a6000ffd8930005fec498067fe624c0037f3126000ff589300cff8c498006fc624c037ffa926019ff949300dffaa498067fc524c035ffa126019ff90930007fa8498067fc424c013ff9926000f7cc9300cffc6498003fd324c001ee9926009ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c037ffa8a601bff945300dffaa29806ffc514c035ffa0a6000ff90530007fa829806bfc414c013ff98a6000ff8c530007fa6298027fc314c033ff90a6000ff88530007fa4298067fc214c037ffa826004ff941300dffaa098013fc504c035ffa026004ff90130007fa8098013fc404c013ff9826009fecc130027fc6098013de304c033ff9026004ff08130027feca18012ff650c009ff3286003bf99430027faca18062fd650c009fe3286004bf19430027fec818012ff640c009ff3206002bf99030027fac818002fd640c009fe3206004bf190300c7fea81805ffe540c031feaa06017ff150
  | 4 => 0x2fd6390009fe31c8025ffd4e4012ffca720097fd539004bfe29c8002ffd0e40017fc872000bfd4390005fe21c8004ffd8a40027fcc520006fe6290009feb148000bf58a40027f8c520012fc629004bffa948024ff94a4012ffaa520093fc5290005ffa148002ff90a40017fa852000bfc4290001ff9948024ff8ca40007fa6520093fc3290009ffb0c8004ff98640005fcc320013fd61900017eb0c8004ff1864012ffea320097fe519004bfea8c8025ff14640017fe832000bfe4190001df20c8002ff50640017f8832000bbc4190001ff98c8000ff8c640007fa6320003fc3190049ff90c8000ff88640007fa4320093fc21900097f3048004ffd4240027fca120013fd5090009fe2848004ffd02400277e812000bfb4090009fe2048004fe10240027fe4120013fc2090047ffb2a8023bfd954011ffccaa000efe6550047feb2a8023bf5954011ff8caa000efc65500097fb228002ffd5140017fca8a000bbe5450005feaa28023ef55140017f8a8a0003ff63500017fb1a8000ff98d40007fac6a0003fc63500137e31a8023ffd4d4011ffca6a008ffd5350047fe29a8002ffd0d40017fc86a0003be4350005fea1a8002ff10d400177886a0003ff62500017fb128022ff9894000dfcc4a0003fd6250045fe3128001bf1894011ffea4a008bfe5250047fea928022ff14940017fe84a000bbf4250005ff2128002ff509400077a84a000bfc4250001ff9928022ff8c940007fa64a008bfc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf1854011ffea2a008ffe5150047fea8a8023ff14540017fe82a000bbf4150005ff20a8002ff505400077a82a000bfc4150001ff98a8000ff8c540007fa62a0003fc3150045ff90a8000ff88540007fa42a008bfc21500057fb028023ffd4140027fca0a008ffd5050009fe2828002ffd0140017f680a0013fe4050009df2028004ff101400277880a000bf84050045ff9028004ff0814004ffecb98026ff65cc013ff32e6003bf9973004efccb9800e7e65cc013feb2e6021bf5973004efacb980027d65cc013fe32e6009bf1973004ffec998026ff64cc013ff3266002bf9933004ffac998002fd64cc013fe3266009bf1933010ffea998083fe54cc043feaa66020ff1533004ffea798027fe53cc013ef29e6009ff54f3010fbaa798027fc53cc013ffa1e6009ff90f3004ffa8798027fc43cc013ffb166009ff98b3000dfcc598027fd62cc0017eb166009ff18b3000df8c598087ff52cc03fff2966021ff54b300fff8a598083ff42cc03fff2166000ff50b300fff88598027ff32cc013ef9966009ff8cb3004ffa6598003dd32cc013fe1966009ffd873004ffcc398002fe61cc013feb0e6000bf5873004ff8c398087ff51cc043ff28e6021ff5473010ff8a398083ff41cc001f
  | 5 => 0xc83104ffa6418803dd320c413fe190622dbf98431167fea2188b3fe510c459fea88622cff1443115ffe8218803fe410c401fea08622bff1043104ffe6218827df310c413ff1886209fd8c43104ffa6218803dd310c413fa988622affc8431157ee42188abfc210c455fa1086209ffd803104ffcc018812fe600c413feb006200bf5803104ff8c0188b3ff500c459ff280622cff54031167f8a0188afff400c457fe200622affc8031157f840188a7ff65884537fb2c4229ff9962101dfccb108a7fd65884537eb2c4229ff1962101df8cb10803ff64884017fb244228ff99221015fcc910803fd64884017eb244228ff19221015f8c9108a7ff5488451ff2a44229ff55221147f8a910803ff63884017fb1c4200ff98e2104dfcc710803fd63884017eb1c4200ff18e2104df8c7108a7ff5388453ff29c4229ff54e2114ff8a7108a3ff4388401ff21c4200ff50e21147f88710806fd6288403ffa944201ff94a2100fdca510807fd5288453f6a944201ff14a2100ffe8510807fe4288403fea144201ff10a2100ffe6510807fe3288403fe9944201ff0ca2100dfcc3108a7ff5188453ff28c4229ff5462114ff8a3108a3ff4188401ff20c4200ff50621147f88310803ff3188401ff18c4200ff4c621007f86310807ff2188403f790c4201fdc862100ff84310807f42188401ffb044200ff98221025fcc110803fd60884017eb044200ff1822114ffea1108a7fe5088453fea844229ff14221147fe81108a3fc4088403ff9044201ff0822100fd8411089fff654844f7fb2a4227ff9952101dfcca9089ffd654844f7eb2a4227ff1952101df8ca90803ff64484017fb224226ff99121015fcc890803fd64484017eb224226ff19121015f8c89089fff544844dff2a24227ff55121137f8a890803ff63484017fb1a4200ff98d2104dfcc690803fd63484017eb1a4200ff18d2104df8c69089fff534844fff29a4227ff54d2113ff8a69089bff4348401ff21a4200ff50d21137f88690806ff6248403ffa924201ff9492100ffaa490807fc5248403ffa124201ff9092100ffa8490807fc4248403ff9924201ff8c92100ffa6490807fc32484037fb0a4227ffd452113ffca29089ffd514844ffe28a4226ffd0521007fc8290803fd414844dfe20a4200ffcc521007fc6290803fd3148401fe18a4201ffc852100fee4290807fe2148401f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024204bf1812113ffea09089ffe504844ffea824227ff14121137fe809089bfc4048403ff9024201ff08121027fecb20012ff6590009ff32c8003bf99640027facb20096fd6590009fe32c8004bf19640015fac92000bff5490005ff2a48002ff55240017f8a920013ff6390009ff31c8009bf98e40027fac720
  | 6 => 0xbfea866235ff143311a7fe81988d3fc40cc467ff9066233ff0833116ffecb188b6ff658c45bff32c6203bf9963116ffacb188b6fd658c45bfe32c6203bf19631007fec918802ff648c465ff3246202bf99231007fac918802fd648c465fe3246202bf1923116ffea9188cbfe548c45bfeaa46232ff15231185fac7188b7ff538c413ff29c622df794e3116ffaa7188b7dd538c413fe29c6232ffd0e31197be8718827fe438c401fea1c6209ff10e31197b88718803ff628c463ff3146201bf98a31007fac518802fd628c463fe3146201bf18a3116ffea5188c7fe528c45bfea946231ff14a31197fe85188c7fe428c401fea146231ff10a3104ffe6518803df328c463ff1946200ff4ca31007ba6518827fc328c4137f30c622dffd463116ffca3188b7fd518c45bfe28c6232ffd0631007fc8318803fd418c465fe20c6209ffcc631007be6318827f7318c463ff90c6231ff08631007fec118803fe608c4097f3046200ff58231005fac118803fc608c45bffa84622dff9423116ffaa1188b7fc508c465ffa046232ff1023118ffe41188c7fc208c461ffb2a6230bfd9531187fcca9880efe654c461feb2a6230bf59531187f8ca9880efc654c401ffb226200bfd91310077ec898802bf644c45fff3226202bf99131007fac898802fd644c45ffe3226202bf1913100778c89880abc644c461ffaa2622fff95131187faa8988bffc544c461ffa9a6209ff94d31187faa698827fc534c45fffa1a6209ff90d31007fa8698827fc434c401ffb126200bfd8931177fcc498806fe624c401feb12622eff1893100df8c4988c3ff524c45dff2926230ff54931177f8a4988bfff424c45dff2126200ff50931177f88498827ff324c45dff1926200ff4c93104ff864988c3ff514c461ff28a6230ff54531187f8a2988bfff414c401ff20a6200ff5053117ff88298827ff314c413fb98a6200ff8c531007bc62988bbff214c45dfe10a6200ffd8131005fec098803fe604c401feb026200ff18131025f8c0988c3ff504c461ff2826230ff54131187f8a0988bfff404c45ffe202622effc8131177f84098827ff650c4137fb286209ff9943101dfcca188277e650c4073f3286209ff59431165faca188277d650c4013eb286209ff1943104df8ca18827ff640c4137fb206209ff99031015fcc818827fd640c4017eb206209ff1903104df8c8188b3ff540c457ff2a0622cff5503115ff8a818826fe630c413ffa986209ff94c3104fbca618827fd530c459eea986209ff14c3104ffe86188afdf430c413ff2186209ff50c3104ff88618827dc430c413ffb106209ff9883100dfcc418827fd620c4017eb106209ff1883100df8c4188b3ff520c455ff290622cff54831157f8a4188afff420c455ff2106200ff50831157f88418827ff320c413ef9906209ff8
  | 7 => 0x208e7fd65904737eb2c8239ff1964101df8cb2080afd6490405ffaa48202ff952410177ca92080bfd5490473deaa48202ff15241007fec720803fe63904137f31c8200ff58e41005fac720803fc6390473ffa9c8239ff94e411cffaa7208e7fc5390405ffa1c8202ff90e410077c872080bfd4390405fe21c8202ef10e41007fec5208e3fe62904037f3148200ff58a41005fac5208e3fc62904037e3148239ffd4a411c7fca5208e7fd5290471fe2948202ffd0a410177e852080bfe4290405fea148200ef50a41017f88520803ff3290471ff1948200ff4ca411c7f8652080afe6190473ffa8c8239ff946411cffaa3208e7fc5190405ffa0c8202efd0641017ee832080bfc4190405fa20c8238ffc86411c7f84320803ff6090401ff3048204bf98241007fac120802fd6090401fe3048239ffd42411cffca1208e7fd5090473fe2848202ffd0241017f8812080bbc4090471ff9048238ff082411bffecaa08deff655046fff32a8203bf995411bffacaa08defd655046ffe32a8203bf19541015fec8a080bff5450405ff2a28202ff55141017f8a8a0803ff63504017fb1a8200f7d8d41005bec6a0803fe6350401feb1a8200ff18d4104df8c6a0803dc63504016e31a8237ffd4d411bffca6a08dffd535046ffe29a8202ffd0d41017fc86a080bfd4350405fe21a8200ffd8941005fec4a08dbfe62504037f3128200ff589411b7f8c4a0806fc625046fffa928236ff949411bffaa4a08dbfc5250405ffa128202ff90941017fa84a080bfc4250401ff9928236ff8c941007fa64a08dbfc32504057fb0a8237ffd45411bffca2a08dffd515046ffe28a8202ffd0541017ee82a080bfe4150401df20a8202ff105410177882a080bf4415046dff90a8236ff08541007fec0a0802ff6050401ff3028200ff58141007f8c0a0812fc605046fffa828237ff941411bffaa0a08dffc5050405ffa028202efd0141017f880a08dbff205046dfe1028209ffd973104dfecb98827fe65cc4077f32e6209ff597311adfacb98827fc65cc4137e32e6209ffd933104dfec998827fe64cc4057f3266209ff59331005fac998827fc64cc4137e3266235ffd53311a7fca9988d7fd54cc469fe2a66209ffd4f3104ffca798827fd53cc413fe29e6209ffd0f3104ffc8798827fd43cc413fe21e6209ffd8b3104ffcc598806fe62cc413feb166200bf58b3104ff8c598806fc62cc46bffa966233ff94b311affaa5988cffc52cc469ffa166233ff90b31007fa85988cffc42cc413ff9966209ff8cb3104ffa6598827fc32cc46bffa8e6235ff947311affaa3988d7fc51cc469ffa0e6200ff90731007fa83988d3fc41cc467ff90e6233fdc873119ff843988cff421cc413ffb066209ff98331025fcc198827fd60cc4017eb066209ff183311affea1988d7fe50cc46
  | 8 => 0xf18d421f7fea6a10fbfe535087dfea9a843eff14d42017fe86a100bbf4350805ff21a8402ff50d420077a86a100bfc43508037fb128401ffd494200ffca4a1007fd5250803fe2928401ffd0942017de84a1007fe4250803df2128401ff1094200f7884a1007ec4250803ff1928401fb8c94200ff864a1003ff61508017fb0a8400ff98542007fac2a1003fc61508017e30a843effd45421f7fca2a10fbfd515087dfe28a8402ffd0542017f882a100bbc4150803ff90a8401ff08542007fec0a1002ff6050801ff3028400ff58142007f8c0a1012fc605087dffa82843eff941421f7faa0a10fbfc5050805ffa028402efd0142017f880a1007ff2050803fe1028409ffd973204dfecb99027fe65cc8077f32e6409ff597321edfacb99027fc65cc8137e32e6409ffd933204dfec999027fe64cc8057f3266409ff59332005fac999027fc64cc8137e326643dffd53321e7fca9990f7fd54cc879fe2a66401bf98f3204ffea799027fe53cc813ef29e6409ff54f321efbaa799027fc53cc813ffa1e6409ff90f3204fbc8799027fd43cc801eea1e6409ff10f3200dfac599007ff52cc803ff2966401ff54b3200ff8a599007ff42cc803ff2166401ff50b3200ff88599007fe32cc803ef1966401fb8cb3200ff86599007dc32cc813ffb0e6409ff98732005fcc399027fd61cc8017eb0e6409ff187321effea3990f7fe51cc87bfea8e643dff147321e7fe83990f3fc41cc803ff90e6401ff0873204ffec199027fe60cc8097f3066409ff58332005fac199027fc60cc87bffa86643dff943321effaa1990f7fc50cc879ffa06643cff1033200ffe4199007fc20cc877ffb2a643bbfd95321dffcca9900efe654c877feb2a643bbf595321dff8ca9900efc654c801ffb226400bfd91320077ec899002bf644c875ff3226402bf99132007fac899002fd644c875fe3226402bf1913200778c89900abc644c877ffaa2643aff951321dffaa8990ebfc544c8037fb1a643bffd4d3204ffca6990efde534c877fea9a643bf754d3204ff8a6990ebff434c813ff21a6400f790d32007fa8699003dd434c813fe21a6401bfd893200ffea499007fe524c803fea926401ff1493200ffe8499007fe424c803f72126401ff50932007da8499007fc424c803ff9926409fbcc93200ffc6499007de324c803fe1926401f70c93200fd86499003ff614c8017fb0a6400fdd8532005eec299003fe614c801feb0a6400ff18532005f8c299003f4614c8017a30a643bffd45321dffca2990effd514c877fe28a643affd05321d7f88299007ff214c803fe10a6400ffd8132005fec099003fe604c801feb026400ff18132025f8c0990efff504c877ff282643bff541321dff8a0990ebff404c875fe2026401ffc813200ff840990e7ff65904737fb2c8239ff9964101dfccb
  | 9 => 0x500000401700b00700000200100500300200101000400100100400500100700100100100100d01100000600a00500200100000500600600200201201200500400101100100c00401800200400100000600100002a00200501200500a00000802200100800a00200d00100c00000000f03d00f00001003300600100000d05600300201001100700100001000000400200500000300300900300400000301e02700600900c00800200200200100600200000b02400600000100500300000200000200000400a00500900b01400b00500b00202000c00500c02500200200100100200000100900400800300b00800600300000000900301100b00a00000300400400600d00100201a00000000204ffecb21826ff6590c13ff32c8603bf9964304ffacb2190afd6590c13fe32c8609bf19643015fac92180bff5490c05ff2a48602ef95243017faa92190bbd5490c05fe2a48609bf98e4304ffea721827fe5390c13fea9c8609ff14e4304ffe8721827bf4390c05efa1c8609ff10e4304fb88721827ff6290c13ff3148601bf98a4304ffac521802fd6290c13fe3148601bf18a43217fea521907fe5290c85fea948641ff14a43017fe852180bfe4290c83df2148602ff10a43017788521827fe3290c13fe1948609ffd864304ffcc321802fe6190c13feb0c8600bf5864304ff8c32190bff5190c85ff28c8642ff54643217f8a32180bff4190c05fe20c8602ef1064320ffe4321907fc2190c13ffb048609ff98243025fcc121827fd6090c017eb048609ff18243217fea12190bfe5090c85fea848642ff14243017fe812180bbf4090c05fe2048641ffc824320ff84121903ff6550c817fb2a8640ff9954301dfccaa1903fd6550c817eb2a8640ff1954301df8caa1826ff6450c05ffaa28602ff95143017faa8a180bfc5450c057fb1a8640ffd4d4304ffca6a1903fd5350c13fe29a8602ffd0d43017be86a1827fe4350c13df21a8609ff10d4304f7886a180bdc4350c01ffb128600bfd89431fffcc4a1806fe6250c01feb12863fff1894300df8c4a1903ff5250c7fff2928640ff549431fff8a4a180bff4250c05dfa128602ff90943017f884a18fffe3250c13fe1928600ffd8543005fec2a1803fe6150c01feb0a8600ff18543005f8c2a1903ff5150c81ff28a8640ff54543207f8a2a180bff4150c05fe20a863fffc85431fff842a1803ff6050c017fb028600ff98143007fac0a1803fc6050c097e3028640ffd4143207fca0a1903fd5050c81fe2828602ffd0143017f880a18ffff2050c7ffe102863effd95421f5fecaa10fbfe65508077f32a843eff595421f5facaa10fbfc65508077e32a8401bfd9142017fea8a100bfe5450805df2a28402ff551421f77aa8a100bfc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8409b
  | 10 => 0x52000315000030028a00003f4a701451630b98dd20180e11cdc2fc2ce0eb91b819a0513ad8c8c8060cb1641cf80fa1d42138cb0e2e6760318eccec674316e8df904e3f017800000000b6358854853a0000000c300000003770000aaa20c2cf000069a4ff000000000031a0001734bd24920001a00ea85f500014004900001638c705f40001cd008cea05df2d589a40002f41ee00000005142d20758df080322e0a18da82bb2a502d434008b1f182a80008610cb9de48d42344148a310ae5b1000218c0606613ab82a0c320be1e00000f2c44d1128e58ae001704a00c00200000800100500d00600100100000000002201500000700100a00100000000200201500100001100f00a00100300000100000e00300700400200701f01100300804e02f00c01100c00b01200400000700000000c00000100200207400200100700300300200200600700500b00000001201600a00001f00000101503600600000c01000600a00000100003800101400100d00a02600400e01101707100f00a00000200000100301d00005000000c00100600001500400201100002200000300f00000400000001a00700500a00100301301300b00000600e03c00f01000500500400500000501000700a00b00000000700000001500500500000400100700200301d00000700300000800901200100c00d03001500002400000301d03b00800900200100101900600200000200502b01200000100500600101b01800000900603a00700b00100000101200200100600800000c00b00800200d07600c00100100200901700800601700900800600400000001b00800000000800600300000400503100200101a00100000000000202700000601400000401000700000200f01e00000402101301300105a00400000000400200000000200001000e00000400001500101400200b00008200300000d00000600500500700200a01601300101000100000000200a00400000700001000002000a00100100300101200d00100500000500700900100a01600100200001800000401501b00400702200500400200400502a00000603a00000500b00102800b00400000701201603000200500000200000100000300100d00400102d00100501700000201400205500201200500300000400300700300100000700200000100500000501c00200200200600000a00500100000500201600100b00a00a00000000300f01500000901500000600000000200300d00400000800000a00100000300300000102600401100000400900800603101500801200101c01800d00000000000801000000c00900300200401000101a00101800700401600d00300e00600000900000e00100200900000400100100e00600500a02800000800004200001000200101200a01500000500100a00f001000000
  | 11 => 0xbc9374b0013d3d912746825d419d0130cbe52d0e3a0d4f3a2561cda0f8a5601318f80d413400000007e8c5c26c13097548f418700b9a28b5c7db1a50df0e6832000f9d281de0210d48ea051c6910490ce02802e42939f08db63bc3e892e42aa51a2e3027491c6283250e8c7887ec1909168ede2d10f89d90d4864c39f8eac5526a03d28b4c32443431299c4ad24f527b0340f8036941d86510b08432b71e405d606d2011d4c10654b0431f4079c31211c0a2c7d84e20268d646100003de178467c5580299364f6a000354861432257b07c844c3a27de0dd9e98f4e49f08491e0dc870d3d58434c2a53636a93cce1e3583be848c4785d30ec98c44aa5ef3db8364c0236027a00005dc46242a00006202b135300003e00001da8c3c0000001fc922c4cc09322f80001f40000001e700000cf1021a3c884000400000000e43524f02b8e8c1a207d8014e0218c1b88b8ce4600010a0848568012000079000068709918ec4d65f238f83b863628d3a4918483613b2cd1cbc00062600005108ca73c1d38000bc079333900006a02ea3968088f3244500006bc00028830991507e86ac03800001604da2a29884c0066c2760a40e0670221209c8c4466e425039047c48f0201658dba18102798405e46c20a7a02c1d637f0e40000f460000988ff800028735f121cc2e5ee4298170cc03543ba80507a429932394f80000001a201cc00019f23816d00000003bf800052e708034077811027300013b81ea7220bf817c6da00025009d03963e62fb9e38ff46f13a59bd830c00013292dd0242763340f28c3a498434800000011100013bc0000001a00fa8000409000105c40600000000000007b30d6947c8404f000000a03f00003e2030000062932d1634cea14a22400000000000000ae00000000511bfc38a84d366917400025b00012d486655f1bb9afca6e82f40a0000dd02151cb845805e0c621493f414281909309889103aa2609ef822419000000b09fc00006e9eb871c2c036c130848075231908c4b7800042806700c27691d093e862c66200091287ec42c00000004a863716689b866e20543500006b800000007c80ee1730ac031400082806a1ae40dc3791bc00000006bb39380000001ca3c4110400051c16787b4d0629e000116077445e0b4926800036c00016a0a3c1830e0800079a0000b684b00000002389abc00025000012d8fb057428c10b41045342e18a4c59815c1a4011c85c0d31ca05687687bb09a918081c7211538fc83b41480be8024aca2bc3e5107ce822a125f08d8d6a3631950c9078285d2d383300860f11b514bc00019d20a84bc000000000089ca1810834e9c780005723621f8c5506123b38f4005a52c18a99410464a71478ac0ad622422b10c8c8413e2be0e987626aa1b9933419c0273bd00000004440251298af405a20e00000
  | 12 => 0x3be0af19f837d01e00037f11b016e16f1a880d0ba40002c2966c0000000001ee8c0e04e22589e4eb00953b90960c6017401e1c600000003780bb0b880000001ac8e142c537398144ee7093b7041c1fe09028780944921ce4288244c300a60130d907f838f3bf20c10620460de949509c20d17a948c5b22674311d640323552ce99e0e6a4ed0d218b0bca5cc26e17c06e00792daa024ebc281246145865e75a04712847b04c41a2803c0920a51df130cef808c02c86609ac6fb0000000214000244981800008a0001b5827e4d80c5176c0006da1049c741c038b03d000000000026b953c234760211805881400012980e8000217117800000014e10f80007b43470da1d3498e30740984cc47e81f11606f8bc87b13b89e103c274817110f83a440804c1f14ff616b0b300804364003a79be8cda10037c95705ce46d11d9f9cda24530d30a14c0882a2691fc8aae78b0000860ff247538716844fa219291000000011705a00000000001b7000000030a3ab0000a1c7050a600001c60003de9a3427820b435942c0007c71bd9faca0e5ea1c41ad09be4ab32b0e48a1073d24c89187980562a00f3cd9418e1599fb8876421000186c1940ab12682cc91414b2078d309e4041361a0802327131d496a4a4c37d0bd8160e5221d30612887864842430020d8e2001b113c40001632a380000000c8376881caa2510000031057e1c60000aa80007760b7000049c30600015b400000017080001920e601ea098ffc00023a00000001c32132068bfa3ac06b104c5b40db1c609f8ac421300002c80002941448abc70672c09c831c0ba5780001f4c54800000013a43747700000000000000000000018600000008800006930fa18f40e424324010fc0000000f7940424e55429e8000c9e0003698354bb81250ca96886ba437125859c61c19312d0000102860122194452c00019282c50ac15f0001c4865648d00013300381e33941a70bf82bd28120dc8b600040712b0066319119219c4ae00029a94802a600000002643341d532095183883c83989e24c2233b00020f45ae46300017ccc8c40c299000000084b0a8182c4ba7982e298210be13a3b69954c8812d000000006e07f0b50e1045c06f1c1110c7ba000000169400000007090190705713c28e7105a1b91a703a8d4a57740e863455a0000e017650720002701a308a4666000187000000014d80000fc0003a218fc8223d40000fd492a2ae3ea9e0503645534a90e02ee1aa31c16b089c160131a114d085970cb1bb01e67d92bf96dc12c3eb271964c6262db12c8e7c80a6573069c6437e2d200000003ba6740000000000000415800000054c1079bd490a58e38a0a7d04a59f18c1b000d86e01158f54cfe0660da9ffcf280001700f588a04ca1e394c460a5170bd1604b645332f317747223651f7027903c81c0
  | 13 => 0x1ba9d84ffa7b405000009261410000e88a50282307151026c0de00000000005be00007ec73250900020042305c80d08000f508683d789fc0001a840294e8b740002850000204368270954000000021500005fe31e00020280000000159164b942ef04f83f02ac51307f01d40007a01fb94a489818408581084441ec11514a8ae61b24260cd02ea7f41db8a8c3ea43036708e496841a23b8000e56766000046c00055e043850c1084793bc16985be49b076800000070b0901c58b30490372800101a7a4000000000004b000000000027a00017d07e20002a7000000000e11e81100000000001c109783890001c440c084800000000000003731448ca81fc42f03e0f706fc00014340004ce4170eb8f1e0bd14a874c56a27831b0000b462ac2681dec0000000ed8e180006fd0000a000007a908280000221e90000000dd640d3329a9c6847f51cf0018b8e11c13a80000002f127d90f00003cb00014902c827c0000000e705aa27e1d7039e77716210e4b722233800fa00001612db00007de6163f088cceca50520213dc5d018833f1ca84f65f84198990e0c66900001406bc61e2a41a085bc5cb33e1418bf238015b9314cf62cb03a01a4e4a7cc38d9f043d055b2c58188f3462d3559144cf21702d817b102c3093339270ab463e34a1c40bec56f00198804e283f3c008d50681ff2dd8cf0a7820800004a82283c51c294750482fe30f8524c8a0893350c5c7206ea32186b88d000000019acf5820223e000000038705f873079228325c12ec15800000016b48fc00029f8000e640002818000a8637a1c0913c0ec3bb02400300003350000f902707e92bb04382500154248b6000017834b8dac874000000178cd16000000141085e000000000000016240a9620f7e00016a928c9a2000305194cd3e0e532c93e4f1a00000f1d30000591275183c77243602d85782ba0000001f74fc024128d8aace9c0003dc9f3c6285da07915a05222ca20f12f43920000fc8fb4bd637600000000006e320b1584cc82fd3eb0e7428c10630d062c6045d73cf000876c0000ac8fa47142a534c825ca727ea36600000a40641ef9b486646b608f0000b5e65e364036085615b3ed17880008103e40bb503058c04a1b886504672b21e84a84157128851cd661f62c21708fc48420761650d12751071000003469b2d991900007241f980006081fd3ea0000e746b700021642ca43d10319385ac5790000b501ae68512e18e49bc71c0d299240006b8325a1901e047f11b9c8064c0002a99d14f0e4db00000002063360d986c45ec26a252863c5a02111ed82e065c2c9000210000007c00017c40001dc24b216c0007dc3409e88f243ad1cc00000005d631a963c7f40002e080006021f30120a108d20002ec0a887c000001f202000006b15d1ff00000002e80d68dbe6a30f51aa0
  | 14 => 0x313973877017604e173c69278c3318ac80ce13729713190cc76a339868c242339365904043453033e91ec00020a11095a85726cf25403a0b245673d80fe021800005388782e408d274134c000762224823cc5e65200003d00000f61e8800000067a00013950082683d518245841f703d96e080e69200012c42d80000f11f3807623a1d2a0f078470c2ff95f49f033d2de93006de11d22396805f26f317992a4a9a59901f800071a75d0de07946164d40228c0c0bc12233ba15442c62b311a1182f86e126a9b140004e62b601c40007ef17e0290f3666f03c1e0cb921ee00000010ca19b23b1504aba77412621484da0003e69d7c844000114000000000034f1c1c0008021c985348800001748be086281718e8d5cc6835f41085a043808512f952400034b20e9580f227952ff12e848e3430cf00e4e724ad00804ac4de82c0519fc0e5c1300d391c80004733f88c3497e3e500000005ca5950000368d600dc2a912bc00069000e839cd4448124a0000bda00020087acbf60d20000f84d748222c4970076434f36080e03606241d8133c53078a34c124421e24f2f41f48fca7c32c318f09487730189e5c96411012119c02522300569fa0fec0f73431f7c22a85a30a180cc746ef0920ca4d4284403512a85f60d12411f900004830ec000109e6f20000000db876b1251050ab20551999ccc01a69a00000010740e91b38bdc17835315316406e422d29d9e7c1522be2fd2104fda68e2758664c902a0000144448a2dc2b31b186e87820000ef4d1033002b806c4bc7f72332018d788323e48c9c4027e600019340004190d60e54e4c5bf1290ebc0007301fd800017600023580b80000000a11d5485052142e0000000740108047c84a3e22739eb4ed05de37a0010f6c0362ce00000000000aa20444e03ff1ec88a42a23d71d012c000083632d92b8000446040161c7bc60200500007fa47d2f39f2cf0c58204d8d483ce6d00820a685240001e3000036c29c0e8102c2687f80000000b066ae05d211c77e3a4237915c2023d30000980d2c3002e8878096618232015580ca7470e69b240001fe4038cb406435b40600a80003462ba80009924c80000d8431212e05c932cd7a0000001b5ce840003b61ab466273b39b13900a83561b31970a2a00038d125c36e000000000000020e0dc000000000038a8c8800056300000000006de00018ccafc1e60b880000000000d580007ce7c61130000cba0000000ad80000000610000b146580058304fae51937b90486224181609fccdb22c3
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x51059010026bc1059010004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c10014fe7458c10014fc7458c10026df7358c10006de5358c10006dd5358c10004ff7258c1000cfe7258c1000cfc7258c1004cff7158c1004cfd7158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c1004cff7690c10024fe7690c10004fd7690c10024fc7690c10016be6490c10006bd6490c10004ff7650c10024fe7650c10004fd7650c10024fc7650c10016be6450c10006bd6450c10004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810014fc7458810004ff735881004cfc7358810026ef725881002eee5258810006ed525881002eee325881000cff715881000cfd715881002cfc715881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f51058810004ff7650810024fe7650810004fd7650810024fc7650810016be6450810006bd6450810005f77150810005f4715081004cff76cc810024fe76cc810004fd76cc810024fc76cc8101e6be64cc810006bd64cc81004ede63cc810006dd63cc810004ff764c810024fe764c810004fd764c810024fc764c810005bf744c810035bc744c8101d6be644c810006bd644c81004ede634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c81008cff7690410024fe7690410014fd7690410024fc7690410016be6490410006bd649041008ef66190410025fa7090410005f9709041008cff7650410016be6450410006bd6450410005df7350410005dc735041008ef66150410004fd76cc4101a6be64cc410006bd64cc41022ef661cc410004ff768c41004cfd768c410196be648c410006bd648c41004ede638c410006dd638c410025fa708c410005f9708c410004ff764c410005bf744c410035bc744c41017ebe644c410006bd644c41004cff760c410024fe760c410004fd760c410024fc760c41003d7e750c4100057d750c41015ebe640c410006bd640c41004ede630c410006dd630c41022ef6610c410025fa700c410005f9700c410084ff7688410024fe768841000cfd7688410024fc7688410146be6488410006bd648841000eee6288410006ed6288410086f66188410025fa7088410005f97088410084ff7648410136be6448410006bd6448410086f66148410025fb7644010006fb7644010004fb76440100077b7544010227787544010007bb7444010007b87444010027ba6444010027b96444010007db7344010007d87344010007eb7244010007e87244010025fb7144010027f3714401021efa6144010027f26144010007f24144010007f14144010007f23144010007f13144010
  | 1 => 0x110014fc76501100067f655011011e7c6550110006bf6450110016bc6450110006df6350110006dc6350110006ef6250110116ec6250110005f77150110005f47150110007b54150110027b84050110027f01050110004fe76cc1100657e75cc1100057d75cc1100067f65cc11010e7c65cc110006bf64cc110106bc64cc110006df63cc11004edc63cc110006ef62cc1100feec62cc110005f671cc110005f571cc11004cff764c110004fd764c11004cfc764c1100067f654c1100de7c654c110006bf644c1100d6bc644c110006df634c11004edc634c110006ef624c1100ceec624c110005f7714c110005f4714c110027f0104c11000cff7648110054fd764811000cfc76481100057f75481100657c75481100067f654811009e7c6548110006bf6448110096bc6448110006df6348110006dc6348110006ef624811000eec6248110005f77148110005f471481100067f65c41100467c65c4110006bf64c411008ebc64c4110006df63c4110006dc63c4110006ef62c4110086ec62c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41102377865c4110007bb64c4110007b864c4110007db63c4110007d863c4110007eb62c4110007e862c4110025fa71c4110026fb61c4110027f361c4110237f251c4110237f151c4110007f241c4110007f141c4110007f331c4110007f031c4110007f221c4110007f121c4110004ff755901001cfe7559010004fd755901001cfc7559010026bf7459010006bf5459010036be5459010006bd5459010036bc5459010004ff735901004cfc7359010036bf4359010036bc4359010004ff725901000cfe725901000cfc7259010036bf4259010006be4259010036bc4259010014ff7159010014fd7159010034fc7159010036bc4159010024ff7059010024fe7059010024fd7059010024fc7059010026be4059010026bc4059010026f71059010026f51059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006be3259010006bc3259010036bf7159010006be7159010006bc7159010006bf5159010006be5159010006bd5159010006bc5159010006bf2159010006bc2159010026bf7059010026be7059010026bd7059010026bc7059010026bf5059010026be5059010026bd5059010026bc5059010026bf3059010026be3059010026bd3059010026bc3059010026bf2059010026be2059010026bd2059010026bc2059010026bf1059010026b71059010026be1059010026bd1059010026b
  | 2 => 0x25fa70cc510005f970cc510025f676cc51023ef676cc510024f676cc51023df775cc510295f575cc5100077765cc51028f7465cc51023df774cc510005f574cc510007b764cc510007b464cc51023ef763cc510007d763cc51023ef563cc51023fd463cc510005f572cc510007e762cc51019ef662cc51019ef462cc510007e462cc51019ee462cc510025f670cc51023ff270cc510025f270cc51023ff170cc510025f470cc510004fe768c5100067f658c51016e7c658c510006bf648c510196bc648c510006df638c51004edc638c510006ef628c51018eec628c51023df6718c510024fc764c5100067f654c5101867c654c510005bf744c51005dbc744c510006bf644c51017ebc644c510006df634c51004edc634c510006ef624c510176ec624c510005fb704c510025f8704c510004fe760c5100657e750c5100057d750c5100067f650c5101667c650c510006bf640c51015ebc640c510006df630c51004edc630c510006ef620c510156ec620c510005f6760c51023ef6760c51023df7750c51023f76750c510285f5750c51023f75750c51000575750c51000777650c51027f74650c51023df7740c510005f5740c510007b7640c510007b4640c51023df6730c51023fd6730c51023ef7630c510007d7630c510006d7630c51023ef5630c51023fd4630c51023fd6530c51027fd5530c510277d7430c51023fd4430c510005f5720c510007e7620c510156f6620c510156f4620c510007e4620c510156e4620c51023fd7320c510007d5320c510025f6700c510025f4700c51026fd6300c51026fd4300c51006cfe76885100067f658851014e7c6588510006bf6488510146bc6488510006df6388510006dc6388510006ef628851000eec6288510005f6768851006ef67688510265f77588510265f5758851000777658851025f746588510005f77488510005f57488510007b76488510007b4648851023df6738851023df47388510007d76388510007d46388510055f57288510007e7628851000ef6628851000ef46288510057e4628851000ee46288510057e6528851025fe55288510025f67088510025f47088510257e62088510257e42088510024fc76485100067f654851013e7c6548510006bf6448510136bc6448510006df6348510006dc6348510006ef624851000eec6248510005fb7048510025f87048510025f4764851000ef47648510024f4764851024df7754851024df57548510007776548510247746548510005f77448510005f57448510007b76448510007b4644851023df6734851023df47348510007d76348510007d46348510055f77248510007e77248510007e7624851000ef6624851000ef46248510057e46248510007f37048510025f67048510025f47048510007f07048510014ff765011005cfd765
  | 3 => 0xf735891004cfc7358910006dc735891004cdc7358910054ff7258910006ef725891006cff7158910006f77158910084ff7058910006fb7058910005ee7618910056ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910057e571189102c6ef6118910007e65118910007e551189102c7e610189102c7e41018910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101f67c6550910006bf6450910016bc6450910006df6350910006dc6350910006ef625091000eec625091004cff76cc910004fe76cc910004fd76cc91004cfc76cc9100067f65cc9101ee7c65cc910006bf64cc9101e6bc64cc910006df63cc91004edc63cc910006ef62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101de7c654c910005bf744c91005dbc744c910006bf644c9101d6bc644c910006df634c91004edc634c910006ef624c91000eec624c910005f7714c910005f4714c910074fe76905100067f65905101ce7c6590510006bf6490510016bc6490510006df6390510006dc6390510006ef62905101c6ec6290510005f67690510076f676905102bdf775905102bdf575905100077765905102b774659051005df57490510007b76490510016f66490510016f4649051005fb46490510016b4649051005fb654905102b7b5549051023df67390510007d76390510007d46390510007b6439051005fb44390510005f57290510007e76290510007e4629051005fb74290510007b54290510025f67090510025f470905102afb640905102afb44090510024fc76505100067f65505101be7c6550510006bf6450510016bc6450510005df7350510005dc7350510006df6350510006dc6350510006ef62505101b6ec625051005fb44150510005fb7050510025f87050510025f47650510016f47650510024f476505102a5f775505102a5f5755051000777655051029f74655051005df77450510007b77450510007b76450510016f66450510016f4645051005fb46450510007d7735051023df47350510007d47350510005d47350510007d76350510007d46350510005f77250510007e76250510007e46250510007f37050510025f67050510025f47050510007f0705051005fb74050510024fe76cc510024fc76cc5100067f65cc5101ae7c65cc510006bf64cc5101a6bc64cc510006df63cc51004edc63cc510006ef62cc51019eec62cc510
  | 4 => 0x8d1026ede1018d10006dd1018d1026edc1018d1004cff7690d10004fe7690d10004fd7690d1004cfc7690d100067f6590d102167c6590d10006bf6490d10016bc6490d10006df6390d1004edc6390d1020eec6290d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d102067c6550d10006bf6450d10016bc6450d10006df6350d1004edc6350d101feec6250d10005f77150d10005f47150d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910056ee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d891004cfe73d8910004fd73d8910006ef52d8910056ee52d8910006ed52d8910056ec52d8910006ef42d8910056ee42d8910056ec42d8910056ee32d8910056ec32d891000cfe71d8910024fd71d891000cfc71d8910056ef21d8910024fe70d8910054fd70d8910024fc70d8910056ef20d8910055ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910257e771d8910007e651d8910007e551d8910257e610d8910257e410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910256ef71d8910056ee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ec41d8910006ef70d8910256ee70d8910006ed70d8910256ec70d8910006ef50d8910256ee50d8910006ed50d8910256ec50d8910006ef40d8910256ee40d8910256ec40d8910256ee30d8910256ec30d8910256ee10d8910256ec10d89100057f75589100657c75589100067f65589100067c6558910005bf745891005dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910056ec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004d
  | 5 => 0x6dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d102cedf71d8d10006dd71d8d10006d571d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d102cede70d8d10006dd70d8d102cedc70d8d10006df50d8d102cede50d8d10006dd50d8d102cedc50d8d10006df40d8d102cede40d8d102cedc40d8d10006df20d8d102cede20d8d102cedc20d8d102cede10d8d102cedc10d8d100657e7598d100057d7598d100067f6598d100067c6598d1005dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10055ee7298d10005ed7298d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10005ef7258d10055ec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d1004ede6318d10006dd6318d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d1026fd77118d10007d65118d10007d55118d1026fd61018d1026fd41018d1004edf7518d1004ede7518d1004edd7518d1004edc7518d1004edf7418d1004ede7418d1004edd7418d1004edc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d1004edf7218d1004ede7218d1004edd7218d1004edc7218d10006df5218d10006de5218d10006dd5218d10006dc5218d10006df4218d10006de4218d10006dc4218d1004edf7118d1004edd7118d10006df5118d10006de5118d10006dd5118d10006dc5118d10006df4118d10006dc4118d10006df2118d10006dc2118d1004edf7018d1004ede7018d1004edd7018d1004edc7018d10006df5018d1026ede5018d10006dd5018d1026edc5018d10006df4018d1026ede4018d1026edc4018d10006df2018d1026ede2018d1026edc201
  | 6 => 0xd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d91102afb771d9110007b651d9110007b551d91102afb610d91102afb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006be32d9110006bc32d91102aebf71d911005ebe71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf21d9110006bc21d9110006bf70d91102aebe70d9110006bd70d91102aebc70d9110006bf50d91102aebe50d9110006bd50d91102aebc50d91102aebe30d91102aebc30d9110006bf20d91102aebe20d91102aebc20d91102aebe10d91102aebc10d91100057f75591100657c75591100067f65591100067c655911005ebc6459110005df7359110005dc7359110005ef7259110055ec7259110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c755911005cff7459110006bf7459110004ff7359110006df7359110004df735911004cfc7359110006dc735911004cdc7359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec7259110074ff7159110006f7715911008cff7059110006fb7059110005be761911005ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6219110006bc621911005fb571191102d6bf6119110007b65119110007b551191102d7b610191102d7b4101911004cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df53d8d10006de53d8d10006dd53d8d10006dc53d8d10006df43d8d10006dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d10006dc32d8d1004cfe71d8d10006f571d8d1004cfc71d8d10024fe70d8d10024fc70d8d1004cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d10007d571d8d10007d651d8d10007d551d8d102cfd610d8d102cfd410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10
  | 7 => 0x8a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a10014fe7458a10014fc7458a10004ff7358a1004cfc7358a10026ef7258a1006eee5258a10006ed5258a1006eef2158a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10016be6450a10006bd6450a10005f77150a10005f47150a1004cff76cca10024fe76cca10004fd76cca10024fc76cca1004ede63cca10006dd63cca10004ff764ca10024fe764ca10004fd764ca10024fc764ca10005bf744ca10075bc744ca1004ede634ca10006dd634ca10005f7714ca10005f4714ca1005cfd76906102aebf6490610016bc6490610014ff7650610024fc7650610016be6450610006bd6450610005df7350610005dc7350610005fb7050610025f8705061004ede63cc610006dd63cc610025fa70cc610005f970cc6102cedf638c61004edc638c61004cff764c610005bf744c610075bc744c61004ede634c610006dd634c610005fb704c610025f8704c61007d7e750c6100057d750c61026edf630c61004edc630c610054fd7688610256ef628861000eec628861000cff7648610024fc764861000eee6248610006ed6248610005fb7048610025f87048610025f976c4210006f976c4210027f271c42100657e76d95100667e76d951001c7e76d95100067e64d95100067c64d95100067e62d95100067c62d95102df7771d95100677471d95102df7610d95102df7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067e32d95100067c32d95102de7f71d95100667e71d95100667d71d95100667c71d95100067f41d95100067c41d95100067f21d95100067c21d95100067f70d95102de7e70d95100667d70d95102de7c70d95100067f40d95102de7e40d95102de7c40d95102de7e30d95102de7c30d95100067f20d95102de7e20d95102de7c20d95102de7e10d95100667d10d95102de7c10d9510014fe76d91100067f65d91100067c65d911005ebe64d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d911005ebe54d9110006bd54d911005ebc54d911004cfe73d9110004fd73d911005ebf43d911005ebc43d911000cfe72d9110004fd72d911000cfc72d911005ebf42d9110006be42d911005ebc42d9110014fe71d9110024fd71d9110014fc71d911005ebf41d9110024fe70d911005cfd70d9110024fc70d911005ebf40d911005dbe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006b
  | 8 => 0x22ef576cc71022df775cc710315f575cc71022df774cc710005f574cc71022ef763cc71022ef563cc710005f572cc71019ef662cc71019ef462cc710025f670cc710025f470cc710024fd768c71004ede638c710006dd638c710025fa708c710005f9708c710005bf744c71008dbc744c710024fd760c7100457e750c7100057d750c71004ede630c710006dd630c710025fa700c710005f9700c710025f5760c71022ef5760c710024f5760c71022df7750c71022f76750c71030df5750c71022f75750c71000575750c71022df7740c710005f5740c71022fd6730c71022ef7630c71022fd6630c71022ef5630c710007d5630c71022fd6530c710307d5530c7102ffd7430c71022fd4430c710005f5720c710156f6620c710156f4620c71022fd7320c710007d5320c710025f6700c71022ff2700c71022ff1700c710025f4700c71026fd6300c71026fd4300c710024fd768871000eee6288710006ed6288710025fa7088710005f97088710025f5768871000ef57688710024f576887102f5f775887102f5f57588710005f77488710005f5748871022df6738871022df4738871000ef66288710087e66288710007e5628871000ef46288710087e652887102efe55288710025f67088710007f27088710007f17088710025f47088710257e62088710257e4208871002cff7648710005f7764871002ef776487102e5f775487102e5f57548710005f77448710005f5744871022df6734871022df47348710007e7724871000ef6624871000ef46248710025f67048710025f47048710014ff7650310014fc7650310016be6450310006bd6450310005f77150310005f47150310007b541503100457e75cc3100057d75cc31004ede63cc310006dd63cc310005f671cc310005f571cc31004cff764c31004ede634c310006dd634c310005f7714c310005f4714c31000cff764831000cfc76483100057f75483100457c754831000eee6248310006ed6248310005f77148310005f47148310004ff755921001cfe7559210004fd755921001cfc7559210026bf7459210076be5459210006bd5459210004ff735921004cfc7359210076bc4359210004ff725921000cfe725921000cfc7259210076bf4259210076bf4159210024fc7059210026be4059210026bc4059210026f71059210026f51059210004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e10014fe7458e10014fc7458e10026df7358e10006de5358e10006dd5358e10006df4358e10006dc4358e10004ff7258e1000cfe7258e1000cfc7258e10024fc7058e10026de3058e10026dc3058e1004cff7690e10024fe7690e10004fd7690e10024fc7690e10016be6490e10006bd6490e10004ff7650e10024fe7650e10004fd7650e10024fc7650e10004ff755
  | 9 => 0xf725931000cfe725931000cfc7259310024fc715931008ebc415931008ebf4059310004ff75d8f1001cfe75d8f10004fd75d8f1001cfc75d8f10014fe74d8f10004fd74d8f10014fc74d8f10006de53d8f10006dd53d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006f671d8f10006f970d8f102cede30d8f102cedc30d8f10004fd7698f10006df6398f1004cff7658f10005bf7458f1008dbc7458f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10006bf7458f10004bf7458f10014fe7458f10014fc7458f10006bc7458f10014bc7458f10006df7358f10004ff7258f1000cfe7258f1000cfc7258f10006f47158f100457e7518f100057d7518f1004ede6318f10006dd6318f1004cff7690f10004fe7690f10004fd7690f1004cfc7690f10006bf6490f10016bc6490f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10005f77150f10005f47150f100457e75d8b100057d75d8b10086ee62d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b10014fe74d8b10004fd74d8b10014fc74d8b1004cfe73d8b10004fd73d8b10084fd72d8b10086ee52d8b10006ed52d8b10006f671d8b10006f970d8b10256ee20d8b10256ec20d8b1000cff7658b10086ec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10014fc7458b10004ff7358b1004cfc7358b10006ef7258b10024fc7158b10086ec2158b10086ef2058b10004ff7650b10004fe7650b10004fd7650b10004fc7650b10006bf6450b10016bc6450b1004cff76ccb10004fe76ccb10004fd76ccb1004cfc76ccb10006df63ccb1004edc63ccb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10005bf744cb1008dbc744cb10006df634cb1004edc634cb10005f7714cb10005f4714cb10024fd7690710016be6490710006bd6490710025fa7090710005f97090710025f57690710016f57690710024f5769071032df7759071032df57590710016f6649071008fb66490710007b56490710016f4649071008fb65490710327b5549071022df67390710007b6439071008fb44390710005f5729071008fb74290710007b54290710025f67090710007f27090710007f17090710025f470907102afb640907102afb44090710034ff7650710006bf6450710016bc6450710005df7350710005dc735071008fb44150710005f77650710036f7765071031df7755071031df57550710007b77450710007b76450710016f66450710016f4645071008fb46450710007d7735071022df47350710007d47350710005d47350710005f77250710025f67050710025f4705071008fb74050710005f576cc710
  | 10 => 0xd20016bc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d202067c6550d200067f65d85200067c65d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520014fe74d8520004fd74d8520014fc74d852004cfe73d8520004fd73d8520024fd72d8520006f741d8520006f441d852006ef621d852006ef521d852009d7e75985200057d75985200067f65985200067c6598520006f76198520055f970985200057f755852009d7c75585200067f65585200067c6558520005bf7458520095bc7458520005df7358520005dc7358520085fb70585200067f65185200067c6518520006f56118520004ff751852001cfe7518520004fd751852001cfc7518520014fe7418520004fd7418520014fc741852004cfe7318520004fd7318520024fd721852002eee5218520006ed5218520006f74118520006f4411852002ef6211852002ef52118520024fe7018520024fc70185202c6ee20185202c6ec2018520004fe7690520004fd7690520004fc76905200067f65905201ce7c6590520006bf6490520016bc6490520004ff7650520004fe7650520004fc76505200067f65505201be7c6550520005df7350520005dc7350520004fe76cc520004fd76cc52004cfc76cc5200067f65cc5201ae7c65cc520006f761cc520006f461cc520004fe768c520004fd768c520004fc768c5200067f658c52016e7c658c520006df638c52004edc638c520004ff764c520004fe764c520004fc764c5200067f654c5201867c654c520005bf744c520095bc744c520004fe760c520004fd760c52004cfc760c52009d7e750c5200057d750c5200067f650c5201667c650c520006df630c52004edc630c52000dee720c520005ed720c520006f7610c520006f4610c520025fa700c520005f9700c520014ff765012000cfe7650120114fd765012000cfc76501200067f655012011e7c6550120006bf6450120016bc6450120005ef725012000dec725012000cfe76cc12000cfc76cc12009d7e75cc1200057d75cc1200067f65cc12010e7c65cc120006df63cc12004edc63cc12000dee72cc120005ed72cc12004cff764c12000cfe764c1200ccfd764c12000cfc764c1200067f654c1200de7c654c120006df634c12004edc634c120005ef724c12000dec724c12008ebe64d9310004ff75d931001cfe75d9310004fd75d931001cfc75d931008cfd74d931008ebe54d9310006bd54d931004cfe73d9310004fd73d931008ebc43d931000cfe72d9310004fd72d931000cfc72d931008ebf42d9310006f671d931008ebf41d9310006f970d93102aebe40d93102aebc40d9310014ff765931008ebc6459310004ff755931001cfe7559310004fd755931001cfc7559310006bf7459310004ff735931004cfc7359310004f
  | 11 => 0x3467e72d95203467d72d95203467c72d95203467f42d95203467e42d95203467d42d95203467c42d95203467f32d95203467e32d95203467d32d95203467c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95203467f21d95203467e21d95203467d21d95203467c21d95203467f70d952033e7e70d95203467d70d952033e7c70d95200067f40d952033e7e40d952033e7c40d952033e7e30d952033e7c30d95203467f20d952033e7e20d95203467d20d952033e7c20d952033e7e10d952033e7c10d9520014fe76d91200067f65d91200067c65d9120096be64d9120004ff75d912001cfe75d9120004fd75d912001cfc75d912004cfe73d9120004fd73d9120096bc43d9120024ff72d912000cfe72d9120024fd72d912000cfc72d9120126bf42d9120126bd42d9120004fe71d9120004fd71d9120096bc41d912000cfd70d9120096bf40d91200057f755912009d7c75591200067f65591200067c6559120096bc6459120005df7359120005dc7359120005f77159120005f47159120335fb7059120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c7559120124ff7459120006bf7459120096be5459120006bd5459120004ff7359120006df7359120004df735912004cfc7359120006dc735912004cdc7359120114ff7259120006ef7259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f47159120334ff7059120006fb705912004cfe76d8d200067f65d8d200067c65d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df43d8d20006dc43d8d20024ff72d8d2000cfe72d8d20024fd72d8d2000cfc72d8d200e6df32d8d200e6dd32d8d20004fe71d8d20004fd71d8d2009d7e7598d200057d7598d200067f6598d200067c6598d20006df6398d200cdf97098d200057f7558d2009d7c7558d200067f6558d200067c6558d20005bf7458d20095bc7458d20005f77158d20005f47158d200fdfb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20014fc7458d20006bc7458d20014bc7458d20006df7358d20006de5358d20006dd5358d200ccff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d200fcff7058d20006fb7058d200e4fe7618d200067f6518d200067c6518d2004ede6318d20006dd6318d2004cff7690d20004fe7690d20004fd7690d2004cfc7690d200067f6590d202167c6590d20006bf649
  | 12 => 0xf735922004cfc73592200a6bc4359220116bf4259220116bd4259220004ff7159220004fc71592200a6bf4159220024fe7059220024fc7059220026be4059220026bc4059220004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e20014fe7458e20014fc7458e20026df7358e20006de5358e20006dd5358e200cedf3258e200cedd3258e20004ff7158e20004fc7158e20024fe7058e20024fc7058e20026de3058e20026dc3058e2004cff7690e20024fe7690e20004fd7690e20024fc7690e20016be6490e20006bd6490e20004ff7650e20024fe7650e20004fd7650e20024fc7650e20004ff759862001cfe7598620004fd759862001cfc7598620014fe7498620004fd7498620014fc749862004cfe7398620004fd7398620026f67198620006f65198620006f55198620086f62198620086f52198620024fe7098620026f61098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7458620006bf7458620004bf7458620014fe7458620014fc7458620006bc7458620014bc7458620004ff7358620006df7358620004df735862004cfc7358620006dc735862004cdc7358620026f77158620006f65158620006f55158620056f62158620056f52158620056ec2158620024fc7058620026f61058620026f41058620004ff7690620024fe7690620004fd76906202aebf6490620016bc6490620006f66190620006f56190620004ff7650620004fd7650620024fc7650620016be6450620006bd6450620005df7350620005dc7350620005ef725062000dec7250620006f66150620006f5615062004cff76cc620024fe76cc620004fd76cc62000dee72cc620005ed72cc620006f661cc620006f561cc62019fe421cc620004ff768c620024fe768c620004fd768c6202cedf638c62004edc638c620004ff764c620004fd764c620024fc764c620005bf744c6200a5bc744c620005ef724c62000dec724c62004cff760c620024fe760c620004fd760c6200ad7e750c6200057d750c62026edf630c62004edc630c620006f6610c620006f5610c620157e4210c620025fa700c620005f9700c620256ef6588620356ed658862000dee718862000fe67188620257e66188620006ed6188620257e56188620257ea7088620255ed7088620007e9708862000eee608862000fea608862034d7e76d952009e7e76d952001c7e76d95200067e64d95200067c64d952033f6f72d95203476c72d95203477b20d952033f6e20d952033f6c20d95203477820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067c43d952033e7f72d9520
  | 13 => 0xc530005f9708c530024fc764c530005bf744c5300d5bc744c530006f7614c530006f4614c530005fb704c530025f8704c530004fe7688530004fd7688530004fc7688530006ef628853000eec6288530004ff7648530004fe7648530004fc7648530014ff76501300d4fd765013004cfc7650130006bf6450130016bc6450130005df735013004ddc7350130004ff755903001cfe7559030004fd755903001cfc7559030024ff7459030026bf74590300bebe5459030006bd545903004cff735903004cfe735903004cfd735903004cfc735903004ebe435903004ebc4359030004ff725903000cfe725903000cfc72590300bebf4259030004ff7159030004fc71590300bebf4159030024fe7059030024fc7059030026be4059030026bc4059030004ff755883001cfe7558830004fd755883001cfc7558830004ff7458830014fe7458830014fc745883000cfd7358830024ff7258830026ef72588300b6ee5258830006ed52588300b6ee425883004eef325883004eec3258830004ff7158830004fc715883004edc31588300b6ef2158830024fc7058830026df3058830026dd3058830026ee2058830026ec2058830004ff7650830004fd7650830024fc7650830016be6450830006bd6450830005df735083004ddc735083000eee6250830006ed6250830004ff759843001cfe7598430004fd759843001cfc7598430014fe7498430004fd7498430014fc749843000cfe7298430004fd729843000cfc7298430026f67198430006f65198430006f5519843004ef7319843004ef43198430026f61098430026f41098430004ff755843001cfe7558430004fd755843001cfc7558430004ff7458430006bf7458430004bf7458430014fe7458430014fc7458430006bc7458430014bc7458430004ff725843000cfe725843000cfc7258430026f77158430006f65158430006f5515843004ef7315843004edc315843004ef43158430026f61058430026f41058430004ff7690430024fe7690430004fd76904302aebf6490430016bc6490430006f66190430006f56190430004ff7650430004fd7650430024fc7650430016be6450430006bd6450430005df735043004ddc7350430006f66150430006f5615043004ddd768c430006dd768c43004edf658c43035edd658c430196de648c43004edc648c430006dd628c43004dde718c43004fd6718c430006dd618c4302cddd708c4302cede608c43004fda608c430004ff7688430024fe7688430004fd7688430006f66188430006f56188430004ff7648430004fd7648430024fc7648430005df734843004ddc734843000eee6248430006ed6248430006f66148430006f56148430004ff755922001cfe7559220004fd755922001cfc7559220026bf74592200a6be5459220006bd5459220004f
  | 14 => 0x4cfc73d91300d6bf43d913000cfe72d9130004fd72d913000cfc72d9130006be42d91300d6bc42d9130004fe71d9130004fd71d91300d6bc41d913004cfd70d91300d6bf40d91300d6bc6459130004ff755913001cfe7559130004fd755913001cfc75591300d4ff7459130006bf74591300ecff7359130006df7359130386be4359130386bc4359130004ff725913000cfe725913000cfc72591300d6bf4259130004ff7159130004fc7159130104ff7059130006fb7059130024fc7650d30006bf6450d30016bc6450d30005fb7050d30025f87050d3000cfe76d89300ceee62d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930014fe74d8930004fd74d8930014fc74d8930024fd73d893000cfc73d8930006de53d8930006dd53d89300ceee32d8930004fe71d8930004fd71d89300ceec21d893004cfd70d89300ceef20d89300057f75589300dd7c7558930005bf74589300d5bc74589300ceec6258930005f77158930005f47158930004ff7650930004fe7650930004fc7650930016be6450930006bd6450930005de76cc93004ede76cc93004ddf75cc93037ddd75cc930376df65cc930376dd65cc930006df64cc930006dd64cc9300cddd72cc93000ede62cc93000edc62cc930025de70cc930025dc70cc93004edf60cc93004fdb60cc930024fc764c930005bf744c9300d5bc744c930006ef624c93000eec624c930005f7714c930005f4714c930005fb704c930025f8704c930025dc764c93000edc764c930024dc764c93036ddf754c93036ddd754c930366df654c930366dd654c9300079f744c9300079c744c930006df644c930006dd644c93004ddf724c93004fcf724c930007cf624c93000ede624c93000edc624c9300cfcc624c93000ecc624c9300cfce424c930007cd424c930007d7714c930007d4714c930007db704c930025de704c930025dc704c930007d8704c93004edf604c93004fdb604c930004ff75d853001cfe75d8530004fd75d853001cfc75d8530014fe74d8530004fd74d8530014fc74d853000cfe72d8530004fd72d853000cfc72d8530006f721d8530006f421d8530006f761985300057f75585300dd7c7558530005bf74585300d5bc7458530005ef72585300cdec7258530006f56118530004ff751853001cfe7518530004fd751853001cfc7518530014fe7418530004fd7418530014fc7418530006de5318530006dd531853000cfe7218530004fd721853000cfc7218530006df3218530006dd3218530006f72118530006f4211853026ede301853026edc3018530004fe7690530004fd7690530004fc7690530006bf6490530016bc6490530004ff7650530004fe7650530004fc7650530005df735053004ddc7350530024fe768c530006f7618c530006f4618c530025fa708
  | 15 => 0xd755863001cfc7558630004ff7458630014fe7458630014fc7458630004ff725863000cfe725863000cfc7258630026f77158630006f75158630006f65158630006f55158630006f45158630006f74158630006f44158630006f72158630006f42158630024fc7058630026f61058630026f41058630006f77558630006f67558630006f57558630006f47558630006f77458630006f67458630006f57458630006f47458630006f75458630006f65458630006f55458630006f45458630006f5735863023ef47358630006f7535863023ef65358630006f5535863023ef45358630006f7435863023ef64358630006f5435863023ef44358630006f77258630006f67258630006f57258630006f47258630006f75258630006f65258630006f55258630006f45258630006f74258630006f64258630006f54258630006f4425863023ef73258630006f63258630006f5325863023ef43258630026f77058630026f67058630026f47058630026f75058630026f65058630026f55058630026f45058630026f74058630026f64058630026f54058630026f44058630026f73058630026f63058630026f53058630026f43058630026f72058630026f62058630026f52058630026f42058630004ff7690630024fe7690630004fd7690630016be6490630006bd6490630006f66190630006f56190630004ff7650630004fd7650630024fc7650630016be6450630006bd6450630005df735063004ddc7350630006f66150630006f56150630196be648c630006bd648c630006f6618c630006f5618c630025fa708c630005f9708c6302cedf658c63039edd658c630196de648c6302cf9e648c6301969e648c6302cf9d648c6302cedc648c630006dd628c63004dde718c6302cfd6618c630006dd618c6302cfd5618c6302cfda708c6302cddd708c630007d9708c63004ede608c630005bf744c6300edbc744c63017ebe644c630006bd644c630006f6614c630006f5614c630005fb704c630025f8704c63026ddd760c63004edd760c63004f5e750c63004f5d750c63026edf650c630396dd650c63015ede640c63026f9e640c63015e9e640c63026f9d640c63026edc640c630006dd620c63004fd6710c63026fd6610c630006dd610c63026fd5610c630006d5610c63038fd7210c63038fd4210c63004ddf700c63026ddd700c63004fda600c630004ff7688630024fe7688630004fd7688630146be6488630006bd6488630006f66188630006f56188630004ff7648630004fd7648630024fc7648630136be6448630006bd6448630005df734863004ddc7348630006f66148630006f56148630014fe76d91300d6be64d9130004ff75d913001cfe75d9130004fd75d913001cfc75d91300d6be54d9130006bd54d913004cfe73d9130024fd73d9130
  | 16 => 0x9230006bd5359230386bc5359230006bf7259230006be7259230006bd7259230006bc7259230006bf5259230006be5259230006bd5259230006bc5259230386bf3259230006be3259230386bc3259230006bf7159230006be7159230006bd7159230006bc7159230006bf5159230006be5159230006bd5159230006bc5159230386bf3159230386bc3159230006bf2159230006bc2159230026bf7059230026be7059230026bd7059230026bc7059230026bf5059230026be5059230026bd5059230026bc5059230026bf3059230026be3059230026bd3059230026bc3059230026bf2059230026be2059230026bd2059230026bc2059230026bf1059230026be1059230026bd1059230026bc1059230014ff7650e30024fc7650e30016be6450e30006bd6450e3004f9c4350e30005fb7050e30025f87050e30004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30014fc7458a30026ef7258a300e6ee5258a30006ed5258a300e6ee3258a30004ff7158a30004fc7158a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a30004ff7650a30004fd7650a30024fc7650a30016be6450a30006bd6450a30005df7350a3004ddc7350a3000cff764ca30005bf744ca300edbc744ca301d6be644ca30006bd644ca3000eee624ca30006ed624ca3004fcc324ca30005f7714ca30005f4714ca30005fb704ca30025f8704ca30004ff759863001cfe7598630004fd759863001cfc7598630014fe7498630004fd7498630014fc749863000cfe7298630004fd729863000cfc7298630026f67198630006f75198630006f65198630006f55198630006f45198630006f74198630006f44198630006f72198630006f42198630024fe7098630026f61098630026f41098630006f77598630006f67598630006f57598630006f47598630006f77498630006f67498630006f57498630006f47498630006f75498630006f65498630006f55498630006f45498630006f7739863022ef67398630006f7539863022ef65398630006f5539863022ef45398630006f7439863022ef64398630006f5439863022ef44398630006f77298630006f67298630006f57298630006f47298630006f75298630006f65298630006f55298630006f45298630006f74298630006f64298630006f54298630006f4429863022ef73298630006f63298630006f5329863022ef43298630026f67098630026f57098630026f47098630026f75098630026f65098630026f55098630026f45098630026f74098630026f64098630026f54098630026f44098630026f73098630026f63098630026f53098630026f43098630026f72098630026f62098630026f52098630026f42098630004ff755863001cfe7558630004f
  | 17 => 0x3b67e20597303b67c20597303b67e10597303b67c1059730004ff755933001cfe7559330004fd755933001cfc755933004ebf7459330024fc735933004ebe435933004ebc4359330004ff725933000cfe725933000cfc7259330106bf425933004edf3259330004ff7159330004fc7159330106bc4159330106bf4059330004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30014fe7458b30014fc7458b30024fc7358b3004ede5358b30006dd5358b3004eef7258b300feee4258b3004eef3258b3004eec3258b30004ff7158b30004fc7158b300feec2158b300feef2058b30004ff7650b30004fd7650b3004cfc7650b301f67e6550b300067d6550b30016be6450b30006bd6450b3000eee6250b30006ed6250b3004ddf764cb300b6df764cb303addf754cb303addd754cb3004edf654cb3004f5e654cb303a6dd654cb3004f5d654cb300065d654cb300079f744cb300079c744cb3004edf644cb30006dd644cb3004fcf724cb3000ede624cb3000edc624cb300ffce424cb30007cd424cb30007d7714cb30007d4714cb30025de704cb30025dc704cb30004ff759873001cfe7598730004fd759873001cfc7598730014fe7498730004fd7498730014fc7498730024fe739873004ede5398730006dd539873000cfe7298730004fd729873000cfc729873004edf3298730006dd329873004ef6719873004ef7319873004ef431987302cede309873004edc3098730004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730014fe7458730014fc7458730024fc7358730004ff725873000cfe725873000cfc725873004ef7715873004ef7315873004ef43158730004ff769073004cfe7690730004fd76907301ce7e65907300067d6590730016be6490730006bd6490730004ff7650730004fd765073004cfc76507301be7e65507300067d6550730005df735073004ddc7350730004ff768873004cfe7688730004fd768873014e7e65887300067d658873000eee6288730006ed6288730004ff7648730004fd764873004cfc764873013e7e65487300067d6548730014ff765033004cfc765033011e7e65503300067d6550330016be6450330006bd6450330005df735033004ddc7350330004ff755923001cfe7559230004fd755923001cfc7559230026bf7459230006bf54592300eebe5459230006bd54592300eebc54592300eebf4359230004ff725923000cfe725923000cfc72592300eebf4259230006be42592300eebc4259230004ff7159230004fc71592300eebf41592300eebc4159230024fc7059230026be4059230026bc4059230006bf7559230006be7559230006bd7559230006bc7559230006bf7359230386be7359230006bd7359230386bc7359230006bf5359230386be535
  | 18 => 0xd76cc94004cfc76cc940385bf74cc940015bc74cc94004ede63cc9403879e43cc940004ff764c940004fe764c940004fc764c940005bf744c940015bc744c9400079e434c940007ad424c940005f7714c940005f4714c940004ff75d854001cfe75d8540004fd75d854001cfc75d8540024fd74d854004cfe73d8540004fd73d854000cfe72d8540004fd72d854000cfc72d8540076f641d8540076f541d8540006f721d8540006f421d8540006f7619854005df970985400057f755854011d7c7558540005df7358540005dc7358540005ef7258540115ec725854008dfb7058540006f56118540004ff751854001cfe7518540004fd751854001cfc7518540024fd7418540036be5418540006bd541854004cfe7318540004fd7318540006be4318540036bc431854000cfe7218540004fd721854000cfc7218540036bf4218540006bd4218540036bf4118540036f64118540036f54118540006f72118540006f421185402d6be40185402d6bc4018540024bc76505403bdbf75505403bdbd75505400079f7350540385bc73505400079c73505400059c7350540005bf7250540015bf7150540017b77150540007b76150540006bc6150540007b46150540007bb7050540025be7050540025bc7050540007b87050540016bf6050540017bb6050540004fe76cc540004fd76cc54004cfc76cc540385bf74cc540015bc74cc540004fe768c540004fd768c540004fc768c540015be748c540005bd748c540006df638c54004edc638c5401979c438c540004ff764c540004fe764c540004fc764c540005bf744c540015bc744c540004fe760c540004fd760c54004cfc760c54011d7e750c5400057d750c540015be740c540005bd740c540006df630c54004edc630c5403879c430c540025fa700c540005f9700c540004fe7688540004fd7688540004fc7688540015be7488540005bd7488540006ef628854000eec6288540004ff7648540004fe7648540004fc7648540015be7448540005bd74485400067f74597300067e74597300067d74597300067c745973004e7f735973004e7e735973004e7d735973004e7c735973004e7f435973004e7e435973004e7d435973004e7c43597300067f72597300067e72597300067d72597300067c72597300067f42597300067e42597300067c425973004e7f325973004e5f325973004e7e325973004e7d325973004e7c32597300067f71597300067e71597300067d71597300067c71597300067f41597300067c415973004e7f315973004e7e315973004e7d315973004e7c31597300067f21597300067c215973010e7f70597303b67e70597300067d70597303b67c70597300067f40597303b67e40597303b67c405973004e7f305973004e7e305973004e7d305973004e7c30597300067f2059730
  | 19 => 0x864001cfe7558640004fd755864001cfc7558640004ff735864004cfc7358640004ff725864000cfe725864000cfc7258640026f77158640006f65158640006f5515864005ef6415864005ef5415864005ebc4158640024fc7058640026bf4058640026bd4058640026f61058640026f410586402aebf65906403f6bd65906403eebe6390640006bd6290640015be7190640017b671906402afb66190640006bd61906402afb561906402afba70906402adbd7090640007b97090640016be6090640017ba609064004cff76cc640024fe76cc640004fd76cc640015be74cc640005bd74cc640006f661cc640006f561cc640004ff768c640024fe768c640004fd768c64004ede638c640006dd638c640004ff764c640004fd764c640024fc764c640005bf744c640015bc744c64004cff760c640024fe760c640004fd760c64012d7e750c6400057d750c64004ede630c640006dd630c640006f6610c640006f5610c640025fa700c640005f9700c640004ff7688640024fe7688640004fd7688640006f66188640006f56188640004ff7648640004fd7648640024fc7648640005bf7448640015bc7448640006f66148640006f56148640004ff75d8d4001cfe75d8d40004fd75d8d4001cfc75d8d40024fd74d8d40006de53d8d40006dd53d8d400eede43d8d400eedd43d8d40386bc43d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400eebf42d8d40006de32d8d40006dc32d8d40004fe71d8d40004fd71d8d4011d7e7598d400057d7598d40006df6398d400d5f97098d40105fb7058d4004ede6318d40006dd6318d40024be7690d40385bf7590d403e5bd7590d403debf6590d403debd6590d40015be7390d400179e7390d40386bf6390d400079f6390d403879c6390d40005bd7290d4020ebe6290d4020ebc6290d40005bd7190d40025be7090d40387ba7090d40387b97090d40025bc7090d40016bf6090d40017bb6090d4000cfe76d8940116ee62d8940004ff75d894001cfe75d8940004fd75d894001cfc75d8940024fd74d894000cfc74d89400a6be54d8940006bd54d894004cfe73d8940004fd73d8940116ee42d89400a6ed42d8940004fe71d8940004fd71d8940116ec21d8940014fd70d8940116ef20d89400057f755894011d7c7558940005df7358940005dc7358940116ec6258940005f77158940005f471589403d5fb7058940025bc765094000ebc7650940024bc76509403cdbf75509403cdbd75509403c6bf65509403c6bd6550940385bc7350940006bf6350940015bf7250940017af7250940007af625094000ebe625094000ebc6250940117ac625094000eac6250940117ae3250940005bf7150940007bb7050940025be7050940025bc7050940007b87050940016bf6050940017bb6050940004fe76cc940004f
  | 20 => 0x4ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21006bf7458d21004bf7458d21014fe7458d21014fc7458d21006bc7458d21014bc7458d21006df7358d21174ff7258d21006ef7258d2119cff7158d21006f77158d2119cf77158d21004ff7058d21024fc7058d2118cfe7618d2113d7e7518d210057d7518d2104ede6318d21006dd6318d21156f76118d2104cff7690d21004fe7690d21004fd7690d2104cfc7690d21006bf6490d21016bc6490d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21404fe7690521016be6490521006bd6490521014ff765052100cfe76505211b4fd765052100cfc7650521006bf6450521016bc6450521005df7350521005dc7350521005ef725052100dec725052100cfe76cc52100cfc76cc521006df63cc52104edc63cc52100dee72cc521005ed72cc52119ef761cc521154fe768c52104ede638c521006dd638c52104cff764c52100cfe764c521174fd764c52100cfc764c521005bf744c521135bc744c521006df634c52104edc634c521005ef724c52100dec724c52118cfe760c52113d7e750c5210057d750c52104ede630c521006dd630c521156f7610c5213feef65885213feed658852100dee718852100fe6718852100eef618852100fe76188521004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d812104cfe73d8121004fd73d8121086fa20d8121006fb60981210057f755812113d7c7558121005bf7458121135bc7458121005df7358121005dc7358121135be7418121005bd7418121256ef6218121026fa6018121006f96018121004ff7558e4001cfe7558e40004fd7558e4001cfc7558e40026df7358e40006de5358e40006dd5358e400d6de4358e400d6dd4358e40004ff7258e4000cfe7258e4000cfc7258e40004ff7158e40004fc7158e40024fc7058e40026de3058e40026dc3058e40004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40004ff7358a4004cfc7358a40026ef7258a40126ee5258a40006ed5258a40126ee4258a40096ed4258a40004ff7158a40004fc7158a40096bc4158a40024fe7058a40024fc7058a40026bf4058a40026bd4058a40026ee2058a40026ec2058a4004cff76cca40024fe76cca40004fd76cca4004ede63cca40006dd63cca40004ff764ca40004fd764ca40024fc764ca40005bf744ca40015bc744ca4004ede634ca40006dd634ca40005f7714ca40005f4714ca40004ff759864001cfe7598640004fd759864001cfc759864004cfe7398640004fd739864000cfe7298640004fd729864000cfc7298640026f67198640006f65198640006f5519864008ef6419864008ef54198640024fe7098640026f61098640026f41098640004ff755
  | 21 => 0x671d8e21004ff75d8e2101cfe75d8e21004fd75d8e2101cfc75d8e21014fe74d8e21006be74d8e21014be74d8e21004fd74d8e21006bd74d8e21004bd74d8e21014fc74d8e21006de53d8e21006dd53d8e21006ed72d8e21154fe71d8e21006f671d8e21154f671d8e21024fe70d8e21004fd70d8e21174fd7698e21006df6398e2119ef66198e2104cff7658e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21014fe7458e21014fc7458e21006df7358e21176df3258e21176dd3258e21004ff7058e21024fc7058e2114d7e7518e210057d7518e2104ede6318e21006dd6318e2118df67118e21156f66118e2104cff7690e21004fe7690e21004fd7690e2104cfc7690e21016be6490e21006bd6490e21004ff7650e21004fe7650e21004fd7650e21004fc7650e2100cff7690621014fe769062100cfd7690621016be6490621006bd649062100dee7290621005ed729062140cff7650621005df7350621005dc7350621174fd76cc62119ef661cc62100cff768c62100cfd768c62104ede638c621006dd638c62100dee728c621005ed728c62119cff764c621005bf744c621145bc744c62100cff760c62100cfd760c62104cfc760c62114d7e750c6210057d750c62104ede630c621006dd630c62100dee720c621005ed720c621156f6610c62114d7e75d82210057d75d8221006fb6098221004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221014fe7458221014fc7458221004ff735822104cfc7358221056ee5258221006ed5258221056fa2058221256ec2058221145be7418221005bd7418221026fa6018221006f96018221014fe76d9121136be64d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121136be54d9121006bd54d912104cfe73d9121004fd73d9121136bc43d91211c4ff72d91211c4fd72d91211c6bf42d91211c6bd42d912100cfd71d9121136bf41d9121024fe70d9121004fd70d9121136bc40d9121136bc6459121005df7359121005dc735912140df77159121004ff755912101cfe7559121004fd755912101cfc75591211c4ff7459121006bf7459121004ff7359121006df7359121004df735912104cfc7359121006dc735912104cdc73591211b4ff7259121006ef725912140cff7159121006f77159121136bc4159121004ff7059121024fc7059121136bf405912104cfe76d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21014fe74d8d21004fd74d8d21014fc74d8d21006de53d8d21006dd53d8d21006df43d8d21006dc43d8d2118cff72d8d2118cfd72d8d2118edf32d8d2118edd32d8d21024fe70d8d21004fd70d8d21006df6398d21175f57198d2119ef76198d21005bf7458d21135bc7458d2119df77158d21
  | 22 => 0x903104ebe435903104ebc435903104edc4359031004ff725903100cfe725903100cfc725903115ebf425903104edf325903115cfc715903115ebc4159031004ff7059031024fc705903115ebf4059031004ff755883101cfe7558831004fd755883101cfc7558831004ff7458831014fe7458831014fc745883104ede5358831006dd535883104eef7258831156ee425883104eef325883104eec3258831156f47158831156f72158831156ec2158831156f42158831004ff7058831024fc7058831156ef2058831004ff7650831004fd765083104cfc76508311f67e65508310067d6550831016be6450831006bd6450831005df735083104ddc735083115f9f435083100eee6250831006ed6250831005f77150831005f4715083104ddf764c83119edf764c83143ddf754c83143ddd754c83104edf654c83104f5e654c831436dd654c83104f5d654c8310065d654c8310079f744c83115dde744c83115ddc744c8310079c744c83115d9c744c83104edf644c831006dd644c83104ddf724c83104fcf724c83100ede624c83100edc624c831157ce424c831007cd424c831005df714c831007d7714c831005d7714c831157d4714c83118ede614c83104fd6614c831157d7214c831157d4214c83126ddc704c831194ff769043104cfe7690431014fd769043104cfc76904311ce7e65904310067d6590431016be6490431006bd649043104dde7390431005dd73904313ef9c4390431194ff76504311be7e65504310067d6550431005df735043104ddc735043115fb4415043104ddf764c431006df764c431004df764c43142ddf754c43142ddd754c43104f5e654c43104f5d654c4310079f744c43115dde744c43115ddc744c4310079c744c43115d9c744c431005df724c43104ddf714c43104fd7714c431426de614c43104fd6614c43141fd6514c43141fd5514c431417d7414c431417d4414c43126ddc704c431004ff755803101cfe7558031004fd755803101cfc7558031004ff7458031014fe7458031014fc745803104ede5358031006dd5358031004ff725803100cfe725803100cfc725803104edf3258031006dd325803104efb705803104efb305803104edc305803104ef83058031146be64d9221405f671d9221004ff75d922101cfe75d9221004fd75d922101cfc75d92211b4fd74d9221146be54d9221006bd54d922104cfe73d9221004fd73d9221006ed72d9221404fe71d9221006f671d9221024fe70d9221004fd70d9221014ff7659221146bc6459221004ff755922101cfe7559221004fd755922101cfc7559221006bf7459221004ff735922104cfc7359221146bc43592211b6bf42592211b6bd425922100cfc7159221146bc4159221004ff7059221024fc7059221146bf4059221145be74d8e21005bd74d8e21155f
  | 23 => 0x4be7619131006bf6519131006be6519131006bd6519131006bc6519131006be6219131006bc621913144ebf611913144fb7311913144fb43119131014fc7650d31006bf6450d31016bc6450d31005f77150d31005f47150d3100cfe76d8931006bf64d8931006bc64d8931176ee62d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931014fe74d8931004fd74d8931014fc74d8931176ee52d8931006ed52d8931176ee32d893104cfd71d8931176ef21d8931024fe70d8931004fd70d8931176ec20d8931005bf745893117dbc7458931006bf6458931006bc6458931176ec6258931004ff7650931004fe7650931004fc7650931006bf6450931016bc645093100cfc764c931005bf744c93117dbc744c931006bf644c9311d6bc644c931006ef624c93100eec624c93104fcc324c931005f7714c931005f4714c9311a4fe7690531006bf6490531016bc6490531014ff765053117cfd765053104cfc7650531006bf6450531016bc6450531005df735053104ddc7350531006bf648c531196bc648c53104df6718c53104ef7618c531446df658c531446dd658c5310079f648c531196de648c531196dc648c5310079c648c5311969c648c531006df628c53104dde718c53104edf618c53104fd7618c531006bf64d8131006bc64d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131014fe74d8131004fd74d8131014fc74d813100cfe72d8131004fd72d813100cfc72d813122ef731d813122ef431d813117dbe7498131005bd7498131006bf6498131006bc6498131006fb60981310057f75581311857c7558131005bf745813117dbc7458131006bf6458131006bc6458131005ef7258131175ec7258131006bf6418131006bc64181312cedf6318131026fa6018131006f960181310067f74594310067e74594310067d74594310067c745943104e7f735943104e7e735943104e7d735943104e7c735943104e7f43594310065f435943104e7e435943104e7d435943104e7c435943104e5c43594310067f72594310067e72594310067d72594310067c72594310067f42594310067e42594310067c425943104e7f325943104e5f325943104e7e325943104e7d325943104e7c32594311667f71594310067e71594311667d71594311667c71594310067f41594310067c415943104e7f315943104e7e315943104e7d315943104e7c31594310067f21594310067c21594310067f70594310067e70594310067d70594310067c70594310067f40594310067c405943104e7f305943104e7e305943104e7d305943104e7c30594310067f20594310067c2059431004ff755903101cfe7559031004fd755903101cfc755903104ebf745903104cfe735903104cfc735903104edc735903104cdc735903115edf435
  | 24 => 0xd754ca31466df654ca31466dd654ca310079f744ca31195de744ca31195dc744ca310079c744ca311959c744ca31006df644ca31006dd644ca3104ddf724ca3104fcf724ca3100ede624ca3118fce624ca3100ece624ca31007cd624ca3100edc624ca3118fce424ca31007cd424ca31005df714ca31007d7714ca31007d4714ca3104ede614ca312cddc704ca31014fe769063104cfd7690631016be6490631006bd649063104dde7390631005dd73906311979c439063115cff7650631195df735063104ddc7350631005dd76cc63104edd76cc63104ddf75cc63145ddd75cc631195de74cc63104ddc74cc631005dd72cc63104fd661cc631457d651cc631457d551cc6312cdde70cc631006fb60982310057f755823116d7c7558231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff7458231014fe7458231014fc7458231006de5358231006dd5358231004ff725823100cfe725823100cfc7258231006df3258231006dd325823123ef7315823123ef43158231195be7418231005bd7418231026fa6018231006f96018231014fe76d913117ebe64d9131004ff75d913101cfe75d9131004fd75d913101cfc75d9131006bf54d913117ebe54d9131006bd54d913117ebc54d913117cfd73d913117ebf43d913100cfe72d9131004fd72d913100cfc72d913117ebf42d9131006be42d913117ebc42d913104cfd71d913117ebf41d9131024fe70d9131004fd70d913117ebf40d913117ebc40d913117dbe76d9131014be76d9131006bf65d9131006be65d9131006bd65d9131006bc65d9131006be62d9131006bc62d91313efb731d91313efb431d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d91313eebe73d9131006bd73d91313eebc73d9131006bf53d91313eebe53d9131006bd53d91313eebc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d91313eebf32d9131006be32d91313eebc32d91313eebf71d913117ebe71d9131006bd71d9131006bf51d9131006be51d9131006bd51d9131006bc51d91313eebf31d91313eebc31d9131006bf21d9131006bc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d91313eebf30d91313eebc30d9131006bf20d9131006bc20d913117ebc6459131004ff755913101cfe7559131004fd755913101cfc755913117cff7459131006bf7459131194ff7359131006df7359131194df7359131004ff725913100cfe725913100cfc72591311a4ff7159131006f77159131004ff7059131024fc7059131005be761913117ebe7619131
  | 25 => 0x93311a6be5459331006bd545933104cfc735933104ebe435933104ebc4359331004ff725933100cfe725933100cfc72593311a6bf42593311a6bf4159331004ff7059331024fc70593311a6bc4059331004ff7558b3101cfe7558b31004fd7558b3101cfc7558b31004ff7458b31014fe7458b31014fc7458b3104eef7258b3119eee5258b31006ed5258b3119eee4258b3104eef3258b3104eec3258b3119ef77158b3104edc3158b3119eef2158b3119ef72158b3119ef42158b31004ff7058b31024fc7058b3119eec2058b31004ff7650b31004fd7650b3104cfc7650b31016be6450b31006bd6450b3100eee6250b31006ed6250b31005f77150b31005f47150b3117cfd76907313eebf6490731016bc6490731014ff765073104cfc7650731016be6450731006bd6450731005df735073104ddc73507311a7b44150731004ff755833101cfe7558331004fd755833101cfc7558331004ff7458331014fe7458331014fc7458331004ff725833100cfe725833100cfc725833104efb705833104efb305833104ef83058331196be64d92311979c43d9231004ff75d923101cfe75d9231004fd75d923101cfc75d9231194fd74d9231006dd73d9231196df43d92313eebe43d92313eebc43d9231196dc43d923100cfe72d9231004fd72d923100cfc72d9231196bf42d9231006f671d9231024fe70d9231004fd70d9231014ff7659231196bc645923104ddc73592311979f4359231004ff755923101cfe7559231004fd755923101cfc7559231006bf7459231196be5459231006bd5459231196df7359231196bf4359231196df4359231196dc4359231004ff725923100cfe725923100cfc7259231006be4259231196bc425923104cfc7159231196bc4159231004ff7059231024fc7059231196bf4059231014ff7650e31016be6450e31006bd6450e31195df7350e3104f9c4350e31005f77150e31005f47150e31195be74d8a31005bd74d8a3118eee62d8a3100cff7658a3118eec6258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31014fc7458a31006de5358a31006dd5358a3118eee3258a3104cfc7158a3118eec2158a31004ff7058a31024fc7058a31004ff7650a31004fd7650a31004fc7650a31006bf6450a31016bc6450a31005df7350a3104ddc7350a311979f4350a31005dd76cca3104edd76cca3104ddf75cca3147ddd75cca31476df65cca31476dd65cca31195de74cca3104ddc74cca31006df64cca31006dd64cca3100ede62cca3100edc62cca31005dd71cca3104fd661cca312cdde70cca3100cff764ca31005bf744ca31195bc744ca3100eee624ca31006ed624ca31005f7714ca31005f4714ca3118ddf764ca3100edf764ca3100cdf764ca3146ddf754ca3146dd
  | 26 => 0x6de50d8d41006dd50d8d41006dc50d8d41196df40d8d41196de40d8d41196dd40d8d41196dc40d8d41006df20d8d41006dc20d8d41006df6398d4117df57198d411a5f77158d411bd7e7518d410057d7518d4104ede6318d41006dd6318d41195de7618d41006de7618d410075e7518d410075d7518d41006df6518d41006de6518d41006dd6518d41006dc6518d41006de6218d41006dc6218d4115fd74118d4115f9c4118d4115fd44118d4115f9f4018d4104edf7518d4104ede7518d4104e5e7518d4104edd7518d4104e5d7518d4104edc7518d4104edf7418d4104ede7418d4104edc7418d4115edf5418d4115ede5418d4115edd5418d4115edc5418d4104edf7218d4104ede7218d4104edd7218d4104edc7218d41006df5218d41006de5218d41006dd5218d41006dc5218d4115edf4218d4115ede4218d4115edd4218d4115edc4218d4104edf7118d4104edd7118d41006df5118d41006de5118d41006dd5118d41006dc5118d4115edf4118d4115ede4118d4115edd4118d4115edc4118d4115e9c4118d41006df2118d41006dc2118d4104edf7018d4104ede7018d4104edd7018d4104edc7018d41006df5018d41006de5018d41006dd5018d41006dc5018d4115edf4018d4115e9f4018d4115ede4018d4115edd4018d4115edc4018d41006df2018d41006dc2018d4100cfe76d8941006df63d8941006dc63d89411b6ee62d8941004ff75d894101cfe75d8941004fd75d894101cfc75d894104cfe73d8941004fd73d89411b6ee52d8941006ed52d89411b6ee42d8941146ed42d8941014fd71d8941146bc41d89411b6ef21d8941024fe70d8941004fd70d8941146bf40d89411b6ec20d8941005df7358941005dc7358941006df6358941006dc63589411b6ec625894148df77158941004fe76cc941004fd76cc94104cfc76cc941006df63cc94104edc63cc941004ff764c941004fe764c941004fc764c941005bf744c941015bc744c941006df634c94104edc634c941005f7714c941005f4714c941486bf6590541486bd65905410079f63905413eebc63905410079c63905410069c6390541006bf6290541015be7190541017b67190541016bf6190541017b76190541005bd7090541006df63d8141006dc63d8141004ff75d814101cfe75d8141004fd75d814101cfc75d814104cfe73d8141004fd73d814100cfe72d8141004fd72d814100cfc72d814108efa40d8141005de7398141005dd7398141006df6398141006dc6398141006fb60981410057f75581411bd7c7558141005df7358141005dc7358141006df6358141006dc6358141005ef72581411b5ec72581412aebf6418141006df6318141006dc6318141026fa6018141006f96018141004ff755933101cfe7559331004fd755933101cfc755933104ebf745
  | 27 => 0xe6318e41006dd6318e413ef9c4318e41195f67118e413edbf7590e414b5bd7590e414aebf6590e414aebd6590e41015be7390e410179e7390e413ef9e6390e413eebd6390e410079d6390e41005bd7290e4120ebe6290e4120ebc6290e413efb67190e41005bd7190e413efb57190e41016be6190e41017b66190e412adbe7090e411c6ee62d8a414a5f671d8a4100cff7658a411c6ec6258a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41136be5458a41006bd5458a41004ff7358a4104cfc7358a411c6ee4258a41136ed4258a41014fc7158a411c6ec2158a41004ff7058a41024fc7058a411c5bf7650a4100ebf7650a4100cbf7650a4149dbf7550a4149dbd7550a41496bf6550a41496bd6550a413edbc7350a41006bd6350a41015bf7250a41017af7250a4100ebe6250a411c7ae6250a41007ad6250a4100ebc6250a411c7ae3250a41005bf7150a41007b77150a41007b47150a41016be6150a41017b66150a412adbc7050a4104cff76cca41004fe76cca41004fd76cca413edbf74cca41015bc74cca4104edc63cca413ef9e43cca41004ff764ca41004fd764ca41004fc764ca41005bf744ca41015bc744ca410079e434ca41007ad424ca41005f7714ca41005f4714ca41006fb60982410057f75582411cd7c7558241004ff75582410067f75582410047f755824101cfe7558241004fd755824101cfc75582410067c755824101c7c755824105ebe5458241006bd5458241004ff735824104cfc7358241006be435824105ebc4358241004ff725824100cfe725824100cfc725824105ebf4258241006bd425824105ebf415824105efa40582412aebc4058241026fa6018241006f96018241004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d41006df53d8d41006de53d8d41006dd53d8d41006dc53d8d41196de43d8d41196dd43d8d4100cfe72d8d41004fd72d8d4100cfc72d8d41006de32d8d41006dc32d8d41024fe70d8d41004fd70d8d41006df65d8d41006de65d8d41006dd65d8d41006dc65d8d41006de62d8d41006dc62d8d41197d741d8d411979c41d8d41197d441d8d411979f40d8d41006df75d8d41006de75d8d41006dd75d8d41006dc75d8d41196df74d8d41196de74d8d41196dc74d8d41196df54d8d41196de54d8d41196dd54d8d41196dc54d8d41006df72d8d41006de72d8d41006dd72d8d41006dc72d8d41006df52d8d41006de52d8d41006dd52d8d41006dc52d8d41196df42d8d41196de42d8d41196dd42d8d41196dc42d8d41196df71d8d41196dd71d8d41006df51d8d41006de51d8d41006dd51d8d41006dc51d8d41196df41d8d41196de41d8d41196dc41d8d41006df21d8d41006dc21d8d41006df70d8d41006de70d8d41006dd70d8d41006dc70d8d41006df50d8d41
  | 28 => 0x8532006bf6458532006bc6458532006bf6418532006bc6418532006f56118532004ff751853201cfe7518532004fd751853201cfc7518532014fe7418532004fd7418532014fc7418532006de5318532006dd531853204cfd7218532006f75118532006f65118532006f55118532006f45118532006f74118532006f44118532156f52118532024fe7018532004fd701853219df67618532006f67618532006f76518532006f66518532006f56518532006f46518532006f76418532007b76418532006b76418532006f66418532006f56418532006f46418532007b46418532006b46418532157d77318532007d65318532007d55318532007d64318532007d54318532157e64218532007e542185324bfe73218532157d63218532157d43218532157e43218532006f77518532006f67518532006f57518532006f47518532006f77418532006f67418532006f57418532006f47418532006f75418532006f65418532006f55418532006f45418532156f773185324bef67318532156f57318532156f47318532006f753185324bef65318532006d65318532006f55318532006d553185324bef45318532006f743185324bef64318532006f543185324bef44318532156f77218532156f67218532156f47218532156f75218532156f65218532156f55218532156f45218532156f74218532156f64218532156f54218532156f44218532156f73218532156f63218532156f53218532156f43218532006f77018532006f67018532006f57018532006f47018532006f75018532006f65018532006f55018532006f45018532006f74018532006f440185324bef730185324bef43018532156f72018532156f62018532156f52018532156f42018532006bf64d8132006bc64d8132006f761d8132006f461d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132014fe74d8132004fd74d8132014fc74d8132006de53d8132006dd53d813204cfd72d8132004fe71d8132004fd71d8132006fb50d8132006f850d81320fefa20d81321d5be7498132005bd7498132006bf6498132006bc6498132005f67198132005f57198132006f76198132006f46198132006fb60981320057f75581321dd7c7558132005bf74581321d5bc7458132006bf6458132006bc6458132005f77158132005f47158132006f76158132006f46158132006bf6418132006bc6418132006f76118132006f46118132026fa6018132006f960181321979c43d8e4115df671d8e41006df6398e41004ff7558e4101cfe7558e41004fd7558e4101cfc7558e41006de5358e41006dd5358e4117ede4358e4117edd4358e413eebc4358e41004ff7258e4100cfe7258e4100cfc7258e4117ebf4258e41004ff7058e41024fc7058e411cd7e7518e410057d7518e4104ed
  | 29 => 0x20f9e4290d3220fce4290d3220f8e4290d3220f9c4290d32005de7190d321d79c4190d32005dd7090d321d79f4090d32014ff7650d3200cfe7650d321fcfd7650d3200cfc7650d32006bf6450d32016bc6450d3204f9c4350d32005ef7250d3200dec7250d3204fcc3250d3200ddc7650d32016dc7650d3200cdc7650d324d5df7550d324d5dd7550d3204ddf7450d3204f9f7450d320079f6450d32016de6450d32016dc6450d321d79c6450d32007cf7250d3200dde7250d3200ddc7250d321ffcc7250d3204edf6250d3204fcf6250d321ff9f4250d321ffce4250d321ff9d4250d32005dc7150d32005df7050d3204dec7650932016ec765093204cec765093200def745093200faf7450932007af6450932016ee6450932016ec64509321d7ac64509321d7ae54509324cfad5450932007cf735093204dee735093204dec7350932007cc735093200eef635093200fcf63509324cfce53509324cfcd53509321d7af43509321d7ce4350932007ad43509321d7cd43509320078d43509321d7ac41509321d7af4050932006bf64d8532006bc64d8532004ff75d853201cfe75d8532004fd75d853201cfc75d8532014fe74d8532004fd74d8532014fc74d853219edd73d853204cfd72d8532006f751d8532006f651d8532006f551d8532006f451d8532006f741d8532006f441d853219ef621d8532024fe70d8532004fd70d8532006f765d8532006f665d8532006f565d8532006f465d8532006f764d8532007b764d8532006b764d8532006f664d8532006f564d8532006f464d8532007b464d8532006b464d853219fd573d8532007d653d8532007d553d8532007d643d8532007d543d853219fe642d8532007e542d85324c7e732d853219fd632d853219fd432d853219fe432d8532006f775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d8532006f654d8532006f554d8532006f454d853219ef773d85324c6f673d853219ef573d853219ed573d853219ef473d8532006f753d85324c6f653d8532006f553d85324c6f453d8532006f743d85324c6f643d8532006f543d85324c6f443d853219ef772d853219ef672d853219ef472d853219ef752d853219ef652d853219ef552d853219ef452d853219ef742d853219ef642d853219ef542d853219ef442d853219ef732d853219ef632d853219ef432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f750d8532006f650d8532006f550d8532006f450d8532006f740d8532006f440d85324c6f730d85324c6f430d853219ef720d853219ef620d853219ef520d853219ef420d85321d5be7498532005bd7498532006bf6498532006bc6498532006f76198532005bf74585321d5bc745
  | 30 => 0xc315873204ef43158732176f62158732004ff7058732024fc7058732004ff755833201cfe7558332004fd755833201cfc7558332004ff7458332014fe7458332014fc745833200cfc735833204ede5358332006dd5358332004ff7158332004fc715833204efb705833204efb305833204ef830583320cefa2058332014fe76d91321d6be64d9132004ff75d913201cfe75d9132004fd75d913201cfc75d9132006bf54d91321d6be54d9132006bd54d91321d6bc54d913200cfd73d91321d6bf43d913204cff72d913204cfd72d913220ebf42d913220ebd42d9132004fe71d9132004fd71d91321d6bf41d91321d6bc41d9132024fe70d9132004fd70d91321d6bf40d91321d6bc40d91324edbe76d9132014be76d9132006bf65d9132006be65d9132006bd65d9132006bc65d913220f9f73d91320079e53d91320079d53d9132507af72d913220fac72d9132507af32d913220f9e32d913220f9c32d913220fac32d9132006bf75d9132006be75d9132006bd75d9132006bc75d913220ebf73d9132506be73d913220ebd73d913220ebc73d9132006bf53d9132506be53d9132006bd53d9132506bc53d913220ebf72d913220ebe72d913220ebd72d913220ebc72d913220ebf52d913220ebe52d913220ebd52d913220ebc52d913220ebf32d913220ebe32d913220ebc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d9132506bf31d9132506bc31d913220ebf21d913220ebe21d913220ebd21d913220ebc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d9132506bf30d9132506bc30d913220ebf20d913220ebe20d913220ebd20d913220ebc20d91321d6bc64591324fddf7359132005f77159132005f47159132004ff755913201cfe7559132004fd755913201cfc755913220cff7459132006bf74591324fcff7359132006df73591321fcff7259132006ef7259132004ff7159132006f77159132004f77159132004fc7159132006f47159132004f47159132004ff7059132024fc705913220dbe76191321d6be761913220cbe76191321d73e75191321d73d7519132006bf6519132006be6519132006bd6519132006bc65191324ef9d73191324eebf63191320079e53191320079d53191324efae72191321d7ad72191324eebf62191324f7af32191324ef9e32191324ef9c32191324efac32191324edde7690d3204ede7690d3204ddf7590d324e5dd7590d321fddd7490d3220f9f6490d32016de6490d32016dc6490d321d79c6490d320169c6490d321d79e5490d324df9d5490d3204fcf7290d3200dde7290d3200ddc7290d3204fcc7290d3204edf6290d3204fcf6290d32
  | 31 => 0x8d4201cfc75d8d4200cfd74d8d42006de53d8d42006dd53d8d42526de43d8d42526dd43d8d42014fd72d8d424fedf32d8d42004fe71d8d42004fd71d8d42024fe70d8d42004fd70d8d4220ebf6498d42006df6398d421d5ed7298d421e5ef7258d42005f77158d42005f47158d421f57e7518d420057d7518d424eebf6418d4204ede6318d42006dd6318d4200dbc7650d4204ebc7650d4200cbc7650d4251dbf7550d4251dbd7550d42015bf7350d420179f7350d420079f6350d4204ebe6350d4204ebc6350d420079c6350d42007af7250d4200dbe7250d4200dbc7250d421ffac7250d42016bf6250d42017af6250d421ffae3250d42005bc7150d42005bf7050d42004ff75d854201cfe75d8542004fd75d854201cfc75d854200cfd74d854240ebd74d854204cfe73d8542004fd73d8542014fd72d8542006f651d8542006f551d854248ef641d854248ebc41d854240ef621d8542024fe70d8542004fd70d854248ebf40d8542006f76198542005df7358542005dc7358542006f56118542004ff751854201cfe7518542004fd751854201cfc751854200cfd74185424a6be5418542006bd541854204cfe7318542004fd7318542014fd7218542006f65118542006f551185424a6f54118542406f52118542024fe7018542004fd7018542024fe76d8142004ff75d814201cfe75d8142004fd75d814201cfc75d814200cfd74d81423d6be54d8142006bd54d814204cfe73d8142004fd73d8142014fd72d8142004fe71d8142004fd71d81423d6fa40d8142336fa20d8142006fb60981420057f75581421f57c7558142005df7358142005dc7358142005f77158142005f47158142005f67118142005f57118142026fa6018142006f96018142004ff755933201cfe7559332004fd755933201cfc755933204ebf745933200cfe735933200cfc735933204ebe435933204ebc43593321febf42593321febd425933204eee325933204eed3259332004ff7159332004fc7159332004ff7059332024fc705933204ddf7650f32516df7650f3250ddf7550f3250ddd7550f3204f9f7450f3204f9f6450f32016de6450f3204edc6450f3204f9c6450f3200dde7250f3200ddc7250f321ff9f4250f321ff9d4250f32005dc7150f32005df7050f32004ff759873201cfe7598732004fd759873201cfc7598732014fe7498732004fd7498732014fc749873200cfe739873204ede5398732006dd539873204ef6719873204ef7319873204ef4319873218ef52198732024fe7098732004fd7098732004ff755873201cfe7558732004fd755873201cfc7558732004ff7458732006bf7458732004bf7458732014fe7458732014fc7458732006bc7458732014bc745873200cfc735873204edc735873200cdc735873204ef7715873204ef7315873204ed
  | 32 => 0x20000001c00500180000008008000800200040020004002000c00100100060004002001400000080000000000000c001000c0040000003003400300240000004002000000500100030014004000000c0014000004ff7558a4301cfe7558a43004fd7558a4301cfc7558a431d6be5458a43006bd5458a4304cfe7358a4304cfc7358a4304ebf4358a4304ebd4358a4304eef7258a4320ebe4258a4320eee4258a4320ebc4258a4304eef3258a4304eec3258a43004ff7158a43004fc7158a431d6bc4158a43004ff7058a43024fc7058a431d6bf4058a43004ff759864301cfe7598643004fd759864301cfc7598643196be5498643006bd549864304cfe7398643196df439864304edc439864300cfe7298643004fd729864300cfc729864304edf329864304ef67198643196f5419864304ef7319864304ef43198643024fe7098643004fd7098643004ff755864301cfe7558643004fd755864301cfc755864304cfc7358643004ff725864300cfe725864300cfc725864304ef7715864317ef6415864317ebc415864304ef7315864304ef43158643004ff7058643024fc705864317ebf4058643004ff755824301cfe7558243004fd755824301cfc75582430d6be5458243006bd545824304cfc7358243004ff725824300cfe725824300cfc725824304edf3258243004ff7158243004fc715824304efb70582430d6fa405824304efb305824304ef8305824300cfe76d89431feee62d8943004ff75d894301cfe75d8943004fd75d894301cfc75d894304cfd74d8943014fd73d89431feee42d89431feee32d8943004fe71d8943004fd71d8943024fe70d8943004fd70d89431feec6258943005f77158943005f47158943004ff75d854301cfe75d8543004fd75d854301cfc75d854304cfd74d854300cfe72d8543004fd72d854300cfc72d8543006f751d8543006f451d85431a6f641d8543006f721d8543006f421d8543024fe70d8543004fd70d8543006f76198543006f56118543004ff751854301cfe7518543004fd751854301cfc751854304cfd741854315edf431854344ebe431854344ebc431854315edc431854300cfe7218543004fd721854300cfc721854315ebf4218543006f75118543006f4511854315ef54118543006f72118543006f42118543024fe7018543004fd70185432057e75d81430057d75d8143004ff75d814301cfe75d81430067e75d814301c7e75d8143004fd75d81430067d75d81430047d75d814301cfc75d814304cfd74d814352ebe43d814352ebc43d814300cfe72d8143004fd72d814300cfc72d8143106bf42d8143004fe71d8143004fd71d8143106fa40d8143005f67198143005f57198143006fb6098143026fa6018143006f9601814304cfe76d8d42004ff75d8d4201cfe75d8d42004fd75d
  | 33 => 0x1000c0070020000000800000280040010008000000200040030014008002c00200100030014003000c000002000100000080004003000800500000010004000000000100200060048001000400800100000004001000001000200000000005000800000000000000003000000a000c0040000005000000000040050014010000000200000020008006001c00d000400000040120010001000400200000040000000000000200000000008000000000300000030000000004c0030034000000000000000020004002000400000300000000001000000000000010004007000000200000000018008000c00a00000000018002001000100040060004002000000000040010000005001c002000400300040050018000000000000080000008007000c0070018001000001000000000000000000c000003c002000800a00000000000001000000c00100010000002000400300000000004002000000000000030004003003c00000000020000002001000200000010030009001c00000000020000001000000200080000000005000400000040040000005000c00000000000000009000400a0004001000800b0004000000000100040000000002000400500040080000006000000000300010004003000400100000000004004002000100000030000009000000000b00020020000004800400140050000002000800500100030008001000c00100000040010001000000000040040000000000000000000000008000001800600000000000002002c000000000000380000000006002400100000010004000000400300040040000001000c00300080000018005002000b000000a0000000002000600000000008000000400b00280000014000000800600000000000000001400100100010020000002800000000010010000004400f0004001001c000003000000000000000002000000200140050008005000000200080030000000000000000340000014000000800700000000024002000c00800080000004000000c000000400c0000005004c005000c0000060000000800300140010000007000400c0008001000400000000010004005000400000040030000000000000c000c00100100010004000002400000140000000005000800000040010024000000c0010048006001000d00000000000010000400300000000000000001000e00080060000002000c00100000010008003004800100040010004002000400300240050000001000c00100000010000002000c00000180000018007000000100200270010007000800000180170000003000c01a0000005000c0000010000000000300000000000004000000000340080000001000000100340090014000000c00000040010000001000c002000000c000001d0044000003c00c0054002
  | 34 => 0x400000000000020004000c00000000000024006001c0020000003000000100400020004000000c00000480140000000004400100300010038010001800200040000014001002c006001400400040020034002000000400000010004002003800000380050008001000000600080020004006001800000100020010001000800800000030014000000400100000000004000003800c0000003000c0010000003000400600000040004006000000d004000000100080004000000000000040000040000000400000040000000012003c002001c002001c00100040010034000000000e001800000080030000001000c0090004009001c00900000020020011000400d0004000000c00100100020014001000000300180060000000008c0000000000000000300400000044012001000d00140020004000000400500080080004003000400100080030000000001800000000160004000000800000100090000000001000f00040000010011004000a0000003000000f003c0030000003000c00800100000008003000000200100010000008000000000000020030002000000100040010008004000000000000020000026000400000080000000005000800600040020018001001800300040020010004000000200200140000000000400200000000004001000000000080000008005001c001000000100000030004000001000000080010000011000000000000000000001000000900400000000004000400e0008010000800100000000000006001000e00000040000002000c002002400000080000000000002000500000000000001002c000001c00000000010000000001400400200020024008000800300080010004000000400000000000048002000c006000c000003c00400140000000006000400200000050000004000000100040000008000000c000001000400080000004000000000000000000004001000400000000000010001000000000040010000002001c00200080000014001000800200040040004000000800000100020008011000800300040040028001000800100040010004006000000000000000008001002c001003400c001800100040020024000000000400000000004002000400000000030000007000000400300000000000000400100040000008005000000100000050004005000000300440000004001000400400000010000002000000000000000008004000c0000000002001800a0000009000000200000020000000000c002000000000200000044002000000200000010004004004400000180020000001000400000000050000003002800100040090010004004c008000c0010028001000c00000000080000002000c0030000000000c00000100000000000000000500000000000010002000b000
  | 35 => 0x10000008005000a002c00300200000008000000c009000400c0000000001400200100020024001001000100000000020000000c0000008008001000600040000008000000401d0004000001800000040050000001002401800080010000006001400300100060000000002c0010000000000800800100010008008000000300080000000008000400100100040020006000c004000000000000100028000003c000000800100000070000005000c000000400a00000000014000000c001000800100000000008003000c00600180020000000003c0000000001002c00c0000009003c00000000250000000000000b005000000080010008001000000000080010000001000400800200060000000000c0000004000004c00a002c01b000c00300000000010002000800200000000008001000000300080040008007000000900140020000001000c000000800000040000008000000400a00040000004001002400000040020008000000400100100020000008000001200000030010017000000c00080000040004002800400000030008000001000d000001d00080020020008000000300080010004002000c000001800900000090000002000000100000100004005000c0010014001000000800200030030001000400a000400100040040030000000000300000000000000000c003006c008000001c0000003000400100040020000001000000200100160004004000000400240120074000000400100000000020000000400100000000008000000000100140000000000000800300000010004004000000000000050008000000800400280000008022001400200000020060002000000000180110000000001000500040010004003000000300180010000000000000200000000000004000400000000010004000002c00600000110014004002000a0004001000c0000038000001000100240000000006000400100280020000002000c002000000100000020000001000000400000000000001000000300000000010005000000000100030000006001000100000000000000000000000000020000000000400f00000000000000000400200280050004000000c000000c003008000f00000000024000001000600040020004000000000000080000000003000000100000000000005000c002000000100000000010004003c002000000500040070000000000000000040020048000003c0010008003000000000140000004000001c00200080010018004001400000080040008003000c000000001e003400400200200000001000400200000000000003001400100800010008005002c00c000c00400040010010005000000000100000000000000000300200010000009000800200040030000001003c00700080000000001000000
  | 36 => 0xb20ac1da81350c2e4878e4a2238db0a5b02424a698386afa79c8cc948a00000000001060000212ea46800000014d237b8000a80000000000000298f465a622520001cb42d8878401187a44789f0c25812640a09ab031b895c000243a681965a30900005a50000000000000013ee4e50aec6cb0000000000002e0000104000087a14b67f6144c3e0198e879123800000000a391860000000000264c000062c000000065a80000000000000000000000000000000612263c000000000002ee0001ad0000050e0000ad8a0f2b0200012ac000000023400001fc8000293800000000001b4915c0000adc00028526c521e04e822120000000000000000000005ab98bc9cc800000000008888000777000e65b000069f93669ee00ac00000003c91bc84e000002d3901224c2a585a10c2600026341d380006f1000000019e254b17ca2ef27b440e8916646a4bc9a48772a82025c97a22fc9fb9ec21e4000093c800009c1de600022b00a489f8000000008927007bd000082980000000000285a30a01580000e481cc7550b100000fa200007e24d71d6081c00000000372000016891780000000000000000062789e000024ae6be11ac000000064c0d1aab280000000000000000028c93f25631faa000000000617e20000000ad8000000018700001fd20000b6e000119a07a000000000000000000477000000024441850fb200029fa82a00008850000000000000000000d000000000000000256e7c186a03fea3e20000d8c000000000027f450393dc196a7dc4a20000391a7f658600007a28000000000003f9e5c76ca094000076200006fa00019de0002156000116c001a98aac7a9b0437a048537164e7b28dda701067e0001a5a11a1e843560be6938a3503ca9d7e76024c884b0000000144a546236e00100000002a9e84f1d1e4cc1c2417b8000aa5800061712742a426c68e480000001bb02a00a548e3a9f046c0cda50c9344a152864a85a46018704768d9250e000000000000006ca0000000133a5bd9f2e000034a617a7987049bfe00000004470bd807c000009a85d248880008d700000000c78a968c6821600009531f640001454626000089b998200011f200023ca752195a0000000754000000809764041550000043800012547b200004560000000000056a892e000000000000006769c60000000092980000000000a60800000000009588000551800000000000000a7241fa8be70584f200008e6af400000000000000157a00000000000004000000400080020008000000c015001c000000000100000020000000000400300000020018000000000400040050018000002c00400000000004001000000200000040000006000c005000800b0000004000000c000c00f0004002002800900140030008000000c00100000060004000001c00000
  | 37 => 0x1a0803a9f3000001ba4083d88000081800000023f60000de855c0000000082a5f993ba99d800000001f80fc000001d000000000a052684c61a2000000000008d2aa40a6a023a931127c4ea8000a021ab800000006300a6e81913c800000000002240582a9d2ab1159865028ca0000b90781800076100000738000ad70000000231270200000000000851011600024104d800007fd0000879800006786680000000997000000000000f591b8776847400000000000000995800013e00000000000000000091e0000745218c90794ce8f78000984a02a63284ca00003d066a8a741d904208cf26801e200005320aae01a10c6000153a838983e1b7800091680005f722c200023b84d398560000b12096816e000000067000004810f1c55492ea0430c64770000038086ea346000089080002b0213e000201400000000001aa43bf17a88d017fa0001eda5b406a813b239a00005a498c0bf819e00005ab00000001cfa12182e00000b7087f86967c4061e00000000000000000021e6e480000000000000000085383c26d60276000000051e961463c1b9c88f9a2c595000000000008dd8000152945638780000001ad6a7900000000148000000069a80000000000a3f80c800000003e6000000000004870000000000040fa0c40002096753064c00022cc1b418d8000207a00027c6711a596743000000000000002ac200000002db000067e1be42fc000009480003e592d400000008fe00000000000534122800002408c8800000000001348886341968293080000000d6c000000081d1e7a00000001fe0000a950000a3b800034e17b272f2674000000094d136400000000000000000000000014060000e828c4000000002ac9d7800056d8a4c23b80005f390a6a589d968e8800000000000001c96000000023924026048fec464a72811f22fa6b291d448921244c594ae80b00005ae80000c8089ca1a000000000000b4120a0001f4469c05c2000000000000004bb0eb8000150e10928f20001c2030103b600000003900000000149c4058000000000016e00004c60000000000000000000001e4443728c46e0a62c4d50000000020800000000001cd80000660987000076290ac000255c4b9a37098183060ff1eb0ae7000000000004b100006052b226989fc05178a0295e06ba625800021884420000afa34223ae0001a66000000000000007d0121a0000000000072813808728520ea20001fca00000008da800064e88fe000051c55595fe81598cc2058000465000059b275c65d2a9815e80000002b469920000844288e5de1b500002a9c27ba3362f59bfc37e1cdaae3000000017862b50dc63dc8000793179200012ca39380004c8800000000000000ab2a8d8000388000068b80000000000000000039c00001b88000abe1b423be0d788368b
  | 38 => 0xef02ff800054d892400000001221c563aaa2b40000da60000000000000000000004f69d8200000002928000a011e1200029d80000000000062a458800009eaacc1bf019010c052400c90ce0428000600800000000001af886e00022760002aaa00000009f6983676d06a40df16465fe000001f00001ea10b46b92be2ab90d8200000009798f260000000a7780000000000000000085f0ba81f0abc4055a20424702e6598029e0000a7a27491b20001a3000001faaf78d4863f07d035696506aba04200000003dd29c40001bd252f10f43a1a16e7a59fa25ba1bf455b08882cc1f6c5e727825598ea061920ae0000c7a00001c8576033a0000000000000000000000000000aca117c0000582000207e0000c0c9a88ada14b0000000000010e80000002a0245200004c080000000000190a64eaa2800000012d80000000000079c000180a2b3aa3e0001ab6000014c0002462519216aa4c9d3200000004a0000012406b07b3800034f80000b69b3200029b257087a06441500add24a8a28266a92821260001e184a31fbe1360246000176000000007f3800000027504ad800000011da4dc0000a38000002616be61600006af000000000000002a9a0000c8200005629af126852b0000000000041924140001d7a66791040002a526228b14023078c62680001ed80000000f3cac81fde0000a060002b708dc8000a7d22ee0001738000000062993c26d701420001a440000000000000055b8cb475c000035f09367208734095180867991ae4fb0000206827c14780000000000000112097b80000ff973428aa71470080000000000000000000000008978000818228a84c00000e3a3d228301267ae2bc012927644670000589000080e00000001666000130a90d9cc40001942a6917c600016fc2601248216960c0ba2906373a6ee463000003a14b0115800000013a2044000000000000000000592a71c00011b47fd949e0000000000147e919182800015ac00004e20002576000141c00023f48a19548000084e90494a2a610544000000040711148dfa97a0b180368081eb66bd000060d06fe82b1bd0824053445ba142673132e01c17069dc064815b9240000000032e00003fd92bc4ac875217400004bd8512a52017e4e1a50081f000000000000fc800000012fe00027ce4b3862e5008000000000000000003de8000165138813a8b3a9ae000036e12065cc266013980005a4a3aa42da2c6000030008280000000bec00000007348000a098124000000000000007a60000000149000000005d5a79200000000000000000000000000000000cb200021189ee800089a000032000000000000000000081c9ad800000003358afe000249caab9c287e580009df80000001916000153c1ee2b040000000000091e00000002f685b60001f9c76d98ec85e916a3
  | 39 => 0x32a22640bb000000004b0000190c000000049700000b780001962758000000088c928458d19840000bf600018e435d800088b8000386981c00000000e2113c3910064394a71668120b0000253051200005218f429da18e2536ab1272283642c3a1526139704a87a92a4c69efa31f04d07db968a83514ea08f97c8a5a136a1eb858836d217e22a0e1c45d80006bf167c0000000000000000000000001674000000066d28f44c4299e000297c55390be8eea3785b60b5e5568132000000046594c26c70ece000287c00000000001c3e6881a1c74917e491480000000000000000000000000000000000000000000000000000ab580000000e584f314000001afa3a3a784000232c57283a4a7093b80240e9000003e80001a6e42390b003c8b9612f8000709a55a00000000000000000000000000008d2000000029c03a114663d3800000000000d197a2a479d9287d80000000000171800000000008d19f6200000000000000a8304840000fcc000013000028a600021a475881be0001b167ed80003db179400a00001a725820000c6a6ea00003070a3a2de232a3e3800090fa89a3c8000000027ae000000000000000000a1a0000000000000027a8754a2b80008449f0e906a2f02bf00000002b8a6958f6e1e029f690302fa34e80001b9abb29a30000382930474c1a1a00028200d5293e7c512a2716000086a00000001e4a29c00000002bb0000080a0001d348af80006cd0830749a6160001c6255300000001db8945848c5a7000000000009c3295243080004761d3e2dd0f0e7d8079400021642bb9cac000000057e27229f280000000ce892d059647487063490b5c10d1958a1e2bc2887a650086800000013082498000000000000000000000ce6790059200009e67230000000057200017424bba83e983800065b8000962a494845a92067c80084cc85688da19ee0000e4c24d208c66e23ee00019d43ea10566f5087e13c10e80000000000000000000009ce89f000000009ab00007e90000670800062700008178000000000000026ce000000066c8ee800000007c493a400000000002934271ab3c000227439721dca69a6de7c88a3647f80000000d867c79f663158000aad839a0000d4241a94c09a90a646c000000001f827068000000184c0000000af80c861a400005fb000070c800000021a2ab1800000026be00015f40000000000187815c05c02baaa683b10000166a2920001d0a5c319ae23f00005ac9eac3b32bac1de8de45af0d14a6e80000000000000000000000001f480000c605e4857a1983c48000000175a00000003370836925800054700006fc19a430d175e97204ae00024c6ac2000057680000000fa6000000055080000000e3600000000000ea842a902c00021cc8531f3c00008c40000c20000173e4289ff0acd80000001
  | 40 => 0x1fcc62b9964aad29669a3aa100000000000282800007c005e800000000005ed01f270880004840bb000000000000000000000040987e08cc060a33e800000002144088866834000055e000000000000001e3a0000b8e13d19be76990e60000000000000087a931220404ce38215884c38fb4abb8c8c000209a000127a000064e00007b200019fc92499ce0001f7c00000006650c720000000a7f2226000082613ea4fa28f02582a311a40000000a3400001a515606fb1e4800000be000231e4b6800000000000000000a560396000000000000000001976a7a00009d48000aa80c2805c8000a3680000001cb643b800094400008b6870020480003eb9cee44917d2ac2800083e89b000017625fda2a099f23a488c0c422eaaa76462000000000006cb8000000151a0000000181000085000001e79722000059000012dc82f000000000004f4800000018a4000058e535800027f0000000000050480000000000113800000000006a58000000206c5098e420c38000000000000011080002b96402917e71c0aa406c09322f784ac7ab89749c1000094496ee75aa26c0001c0a9b9a6fc065a158142227c1249cd413a1044a6b80000001c100000000000000000004625ba816003093fe2b4000000024e487ea28e8fb1632a7fa2783a6043c87b80000001d08ab70b56a1591c2000120e5140000a2280009ea0d9000000008ef94105e680009a51c780000000a680000000077cae10baea309e54af1884c00000005dea8ac51c82ce9692a441e4873811600000000c1837083760000fc69c980fc69a14fc88a20929000000a8c0fe00e1909694920ea07fa23c38a8b221b9265889c92768a3287e90808c220e200c07828c027b0000275a0aaa1985c80000c70000000075a000067e975c754aa90000000000001866991c9e00005aa000058a5f589dc80d800000000000000ebc000000000029da8fc0000000000000000005a680001d680003a92b6e00000000000ac400021b49151c68a6214e00000000000084000007b00002320aacab40000000020600000000e7e012800011c9cf08f18e3400010a8000184000009b2000092a5579aa63b5272a4b80000137099a1cfa5504c70b9c092a41c0000000107800091b0c2a4740000757000000021f8000257aa5d0000a8c80005e08000ab2000000001ba0000d664efa2ba00021b6000018c0000000000000000000008ba07fc000000000023ce0000fca7e82aec00000006a0ab926f6923e0000000000000051e07d8000000000000004980f8a0a00000062889400015ba00009da41c00009c4a1da06b800000000006fa25f600007cc28d162e8ac852e19c0a5ca2a95e0283a6387d180d09ec26ca73c9b78000044c25a2b0c36600ea6ab266619420ba42e2b6a92310f08d60d2c5750578000000038a0814
  | 41 => 0x28e0c2273580008b827480000000a2319900001e46000010800000003ba80829638000000114e8e298c400000000ec28122288c766da8cea8a9124a000000000b1e1c5079c5c6e5074c0002502000000062300005700000000000025f00009c6800000025ea0000000abc0c3a8478fc0000171000f914c2fa191200000000001aa84d5a51c82380000ae9c661e6a8d80000000aba8000461289e5060000154978400028c682d28b6734066c24e0360000000000011341d20000000000000022c4000225a064800068f1dd02ee0000000233a000213a4f907fa0001f3042ea42854e122a614a2440001e9a2f90cdea8883aa3a714c698224740f691781ef000028221a012d99687de18d6000000056e21a6000000000017ba00c13b42c11dc423816a828120e4112a3b674385644caaa0a54582845e325fc9760330714957407da8de32480000001e68403800075f08323f727807809d940000c3e000000084322980000000000000000000000000e8a638279650a0f043cd075c0001a1e2f300004f2833c00008b628a1df235124fe44c0782000284400000000bc10ea57a0c3ca0882727a9225c39982c400000000e300003ad00000000000000123c0001aa200000000001d8c2cf9a86710a8402338000694937a4222a7879600009851e927f8800091f91e0142800039213245080b4600000006f30000a9800009cf80009a221ceacd00000390d60a4b0ccc0000000000192e0000fbc000000000020781be1b100000000690a8e20000e8000000000000000000000000000007178000000000000000000000000000021245c09889b5000000005e84db00008c9800048083ec00000006a50df400000007c8000037f1baa8b21fa6ab50000000000000000000000000000000004e853a09e1fc484e068a42295be2d9800037c21ca2bd00000000000acc1a0808c26aa4ea124452a800007600000000000898a30679a89c8a47000000001aa00000002119ecc7598000a1a904a6b70aca49c8c662f292c8af4a5c40b903f8285288680583de6a6183249a800012e225807997a62a380d2056162ca262a2e58583dc7f9a43c8a120be4e30000542863441b1c3c759184453c80005e2800000000000000000000282400000005d3800000000008ff00000001ed25818f5200027340002a8ca7180004ba00000000000000000000026b400000008ce00000000000adb000043516f0737118e000049aa5da75a51f13c60c28da8208237c0001cf4a648af60002a4e68d935000001840000000000000000000007938bb4000000000000e20001258000000000000009ef1c1c24f800000000009c39e620001b0a3941cc20a9a4de62c938e6cda4e826b1150949a95c10609c238e0a920000000000132c85729ac3c600008290000000294c0001d1092a9be6000
  | 42 => 0x96100003538a1c0000000a7c8498a9b0000000000000024a20001b44000001a00000001bc8000000000000000000000000ac9a5fa6889f9a0000000a930b168e61a480001c9c233000000019c6000213200003e640f1946abe84cc12f254200e1a8a00014d46d300002cd16dc79d0bba0001c6e4cf8000000000034a0000000113ea1d03d272386067678a469aba394000038400007ce3b99a4a2eb26f671f800000024cea0a82a209919605d908f06849116a97090e30400000001f9025a9d6e5d1000011a8000575aa2a5590042a3e29ee00014b873a9f6a0000000000103258e001600000001fd81289cb811c6df206e00000006a11f8683080005d21f4e4419a762b7aa720001cf600000008e20d3c3140b3c00026b69632a189dd80005ee26f07d29e525dd1f9256d0f840001e32a40800000000001d180009119e002ef800033d800000000000fd80008740ad26e2a5680001f5073003e077a83683bb1934023a01800000007ca8aaa00014709f20ee06c6800048e8000000064600000000000000000000000000003761b0200000000d58dd0654000030c2532000000000000003fc82188b40000aeaa77a39d253648d9ea68a4204e5740c603b28000000105e94b9242a3711b672c80005149d026d4800015d21d600000009969e1e056828a23e977c6e79b96020145a378a80097389a600029440599fd4000000000026d26c8856a00000006aa89fa0000fc2000042a9171262981200a00000008580152000000069b00000000a669898a4400020982531fee6e100009200698a0621b84881fb25c79b0862d800007d11c048b263e98000000002a6411911fc39b8b00000000029600000001392000000012a24d800010a0a411c9047b1eea0000e6c00008228db0000000254800000007f09358000000000029be117892c00029b4000120c80e800000005bc00017121019a80877a34c57e95e60000000628000a0000b1a6758856000240e13f07e60000000a46211a00009be9f8024e5d4031620312b4000214a2a815b00001eb4261208236d85cc56a2a74000281c9a180009e3a6c85640c52000266e07013acadc9d2a9681a184e400007c9000090e09f60c080000000000303a9ea858a0f48e70a5e00000006630c16000800000000009dc800000024d28c69f528b39e822a788283b9222a9fcaa6222d0e143bf97cc60f2ada00000007ef1d7200000000001cae1b7000072180000000000367000043919ac91a9b8600018862039a509de000000000004aa19e87b1886c571068e0001d122691ee462019d2000000000010fe000289250f0000046272c66016ce91b929886b041c45495c60000bc4000000000000000000966362000005b0000a3d9bde00005d80000000649800025880008ec8dd66ca85582e202c0000000
  | 43 => 0x60345800000000002518994000102a1c5229c0d116c02d513782d125940001920864019889f9e20a25061a1ee80000000000783113898b80004dc80000000e0c0000e7240d00005c9855400000006421c4e1289a546828000a181226000261806e0338935800055c8ffe6dd201c32fa40a0c780000330146abf171800020ca2c800001a79acc1150000994800000008e80000000000000098e800052c82100000000000235e0000000000281600022b63bd80000000ec0000000000025180001a3472116aa8f3111000000006b080000b514a400000003c680000001b48013800071500009130e22301a69c9cd80007d70fe896c164c153a964000000000025860001b4665587360000000031a0c6a14266c0ea00000000d7a3890c9092180000001a88105a17085a000000003ea0000870632299000000002f18a7672600001f700000000e88000085079f00000ae27ea0001da2000136e0000000000141a0001f4288698f247e9714a10800008f1df80000000977a1c666e934678293688451af09ac2a469f9000075da354000000000000000288000000000000000008820000000000000000000000000359000070300000000000000000060380e63f500007a395240be06b46f2838200000000c1105208e10746e908b2410800000000009e78000a350000811805200014faaf3194c2608df222995043e680000001bb800025926529e9c47200000002884479167647781b263b81e225487a21c92bae0000dea52480000000000000000000000000000000177113a82180007f6834e00026d80000d0c000140a0001b6858c134a0001e5a0002a500000000668000000023fa2af910e000274400000007bb1de00000000ab99216738a5e206f1f681f10000199851a0002aa25bb031a3168d7412c8f8c7959534000000000000007b6102027f8440a17199802719d8000000078417bc0000cac3690b9292c17b6a3900007ee800000012e4000000000000004208fdaa8680000000000000000000026625d2800079c80006b7a8460000000000000069d179678a000000022f400007506248000000000071127b6000000051b800095ca16682780008cd1b0c272aac070780000f28a2600012709e1863c7981d880001e26ac392920c4a012713178e000298e78e000000025e00e4104c00014424f9a5c606d00000d8ab3e2741d1a0bd99882002ace0000ac23bd1ed46211ebe0000d8a3408514ade00002941bbe000000000000000000b2433809f40668cce937269000014940000ba2311267e000090600022a20001f7626a234e74800004df0000000299800000000001e1401682dc00024cc00000004f5160e00009586ba000000012f83d2000000019ca000000000015540000ea62ac10a47b700000000000000000070e8000000007a02f000000
  | 44 => 0x60a800058127e800890c400000009c7800092b000050c0e9226d88f875e0f5889518aa8a09cba00000000000000000000022c0000000269a038000025c8e9aaee00007aa0000000000000001ca9bd19c85eaa48a000000000019fe00000000000000000000000000003a300009e200002290000250aaa6000185a00000009d88d5623588bc00027d48a008ec40a2a8e6e02ba00a6938270b95e4230187e1662b6600000ae71e96083e805b2000100c000000082700000000000abc8000365800023280000000a203021a60a9980007220b7e4d480000000c4c52a135e9f09f3e000104e6b100000000d3492918f600011c66cf262a32380002638000a95811244b8944000223815312080000c9c0000ebe305002a7de8000000000000023a0446000000000006b8000008300000000000000159e2a28000000000000020dc0000000a2c1062000000000000007aa800088b000000000008b72628000000000000005560d729db000094f00008ea1baca4a01b630e11f6a44a52c00006ce00000008920948986976a39504c29539dbe4e28000919800000000008980bd400000001cc1bb478d800000018ea96b1fac237a0b86df8000322a2c00000000000000084d867cae680005a0059cac62b2e3a525c2a0c8ba4103aad0a7b00000001dbc893845a0000e781dd18f80fb901e8a5204c00000f04c018e8568800000004c4000000027a152a00025cc8fa000000000002dd800011e0358810252a1991b8c96d2af60000d22a9e800000000003f78000ac42b4a96da314a4007420f39d4e6bb8d9a9549c7c72000581f280008760d3600004a000015e25be9bf633e000000000000000000111aa240000000000020400029f825685ce5bd15d280206c238b00004ef00760a7180654c982600000001b3045246600003689dd66a780000000000af60000000000076600000809afe865a21800009f2000245000000000000000a6896640001602ae510e084700002ff167201716c6a518000000000000000000000000809800023a88e298319921c429cead594de2528144aa2000000000000000db2671000000021c40000000000000000000007be0000962000070c0dbc00011ce000000000011282b1800091600000ad0dbea4d8cd218200781d61ec000007fe0f51e0e0871f740ef1fa88349ac861b29d431b04b47470a304cd2150000200265e8000000000000005f044780006b895bc26327c00c98c0a13200001300fac52580005a300000000e6800026b200027e60000d40000119e290890c00025f275d187c201800000014e248ca6980000000000000000000860000d3060300003f90a2c40206b224100001678000000122e089aaf45e8000095d0000000125691c19222d681205452806347881c000000004180009e9000069f03fa00011
  | 45 => 0xac00000ad418de000000000025f84f41e6c62b009e61c80002f821c0000000079d8000584842c73a00002279c768f9139600000007f800003b4a96aad9000000026d0000000000000001cc8b8400000005361bba00000000002ab8589aad20001d3a9398000a920bc09ce1fe416b01da2df00009528000000000000025d00001ed07ff03cc0002bdc000000065c800072480003f89ce09b90b2c0001024000000000000008d4a702a0b08240000000000000051d97fe58f23164600cd472a07121ab0f92352a78a74017ac4ca037e0000000000000037f800000024b20000000000098a00000003da08f4296a6e000003a069600000000ed677099d053d187a000165c1ba12d2071800032b8bdca9f0000631883e25b800000001d64cd81d23639dae00014be53a000089ea566464191e0000000000000050301de00000003ac94400cd095400006f6000168e6c119dc38c10c853f800046f00003ae9340426014aaf2846c61880ee00006d42de800000003c8000000000008849d818ba20b013e17aaa265b8068c20096fe9d3181a8ba98b400025a21b21ee000010e2000000082200000000000000000000013fa0b3239e9ff84a63f49686662800035a14ba000036e1a895025eb80002e822500000000000128a000070e85c8edcad48000000000059e92c2000045c47118da5502220a0080003289fea00006200002052000167000300006892aa40000000000000000005469a81a7200011a836b00002d4800000000007760000000000000000000000000948144e68c99bc03292ba45a00009e880006d9896400000003ad84705ff00006ef000093c08ba94306aa00000000001ccc00000009c20000000000080d037400029bc000000001980000790000000281a000000009581a6000000082880002079b987ee00000000000000000011b80000001dec00016588ab253a000129608d00006d780005ae13fc5dda7d2000000000000008608f94a17a2f2000000025b0000145981e426a02829a0b089b3000000003a200000000000000160201a000000087b00000d3000064d9f8c0742b1a05429cc5900be279c000000010847051dce000191848500000000c12000000000000000001da451a1bb6aaf906e6c60000000000067d2b2c3c08000000000001c800000000000001e087100000000000000000005f600008af08488518aac00000002a100007cd80000001f8a729800020d000004b1dee0000000a6d85b40000c980000898982ab5a9ba00aa00014620bf15801d823dc9ae857e6bc952600023b40002a3c0000626000073a2c99ab40002940643a6dc27022d45ec20a00001a9a0001b6c000066295f93e209b27c42d0866a61812005f0a324157957ca3a8cb03c20cba6ac9b8e1caa1aa785800000000000002a3a0
  | 46 => 0x12fc00005a653991f84c7800045787be8b900a491e9f989fc224a39d800020b80c40000e6219100f400000006c90b368c60c465df8ddc7fe000083d8000605800000016c290895769f58a48a6e0550000000078f000017d11740e98000000201e15f000000000000000b860000f544d8863076b199c4300c48344800000022a6000047a000000046e8b2e19d2602a2880002e2800008b8616000000043428f0862091086ca5aa70e000086c049e94200005478000000000031d07e8420000009a0bb60000000000000081120de18d800039800001759050114000022e2416564965609104d60000000000068400005f6835801e0000fea0001d9a00000009b1000000000008802bce3279770aa489865b98e7c000155ca54158600007f026624ec4c980000001cf883f206aab800008168000a6180007d3144487c000000000006512a7e094255e45e92a041011f0661a55826f1b121c6a540ab615f6a581f388b4888a6f62a04a0d1484416066e97481340a5037028fa6689d01866000085262fa93800000001460000000000000000005528b3800022fe8f980000000d6200000000d6800000000da1f580000001d36ab782f400024f4a5b800000015a092d8000000000000000002ae842e90126c200016a257781ea00000000000000aa01b380000a600000ca6a758000a22000029f800000020e61af21002b59f724408000197262089a96b62b2114460e995c00000001b694f00000ae613f9bc60000600a5e0000000230c6d5951059b9bee7001b60ad60f9c96425540002a285c0800000023fe00003781c2800024806ae50e9b763b6800060000005b314ec18a1c0654c200e0000000a03000083600000f1052aa0e086800000000000000000000000025a822f8000a0e9e861c800000000000000129400017462da28b84590000000000037100000000000000165e875196600019e02aa1c641198b989b69a0e4d3040aa1e804ca2d0aa20000000a1b97f016a0928317257c246070c0001d4414f8b8279080000000ca4055242a54f80006b000008f09e2a3ddaafe8c70000000000049b2b1c1db800064a97f200023c422400003858fb628b80003b7aae890188d20000000000000000022340001a8cac5800000000000000eac00020b6000000000000003cc0f0a4e68f66000111a000144640e09b837e8c623a780001780000997a8d20000000000203083a00004ac0138000117268a800000013c400000000001fdc16e80407b894820000000a2900000000000000000025000000001cc67b1208a000000000000000000cee00006380000000000168838380009108e325ccab620001600000000000000000000000906000072a8c940000f0678b093c3f59a0c94500000000e122bc948c63d000017e000000000000a8000000014080000
  | 47 => 0x19549be9a1461090f23c328fc77a25a65b515842e322369e68f5001b0c328fc986e697a0f265c013ca078c7e61d9ae65bc933c7290d7005e2b7623c982c000016a63515065b91f484dd9902156818e21e853046f81dc3b0a15a96005fa9e32a70493800000001a2000000083300001c70c4000023424fe042800000005d024560000000a120d5400025c060893e087c8ed8af223d400004040001dfa5cea8720000f9e00017daa42a7667e21d4a99e9f0a76c17680f906e02c09e34000049c000000092606ec5e22b829e5000095c05de0000a946a480ba4eda88230680ec891993e58416a659fa99c03000004401f9e00029107cd169680185a20000922000161ca5f80004fd80006a4193202c9f020501d5e225a7d87c682d8000000000017906a3a63200000005c580003179ed60cb00004a7a99a8d587222d202e2a2586224fc000074b915a00001fc68e27fc000000003524e02d306546ec8000000224c328000033f189407094c400012d6a5c000079b80001c2125254b80009b5874092e1c509bb00000001ba600001c40a91b3a00002bc00027aa7dc01149a78a0a0001aea0001d280000dd49419e7881a01acaed00003518b9a00023d60000892288a2aea2c80006809b4e4fd00001f9011a00015c813b800050900000000f6a37d885c47a22e210694b4000158e8cb8b0624e83282a691cc1eb16c85c90096aaa2b9014d9f2656b81a8ae7a46841719967268a188a6907226e9ce4ab88c548c12a86000000033880004aa92340000b180001ede33c008a96c94a60000000a4200000000882000158a69e82904b7800099015ce3008000000000000000000000000000000000000000001cb8433000000014cc000217400011ee00013742d909cc0000000000000032a800002a00000000000a55800052380009ec887423200002b88000493022ca9787d49300000ae9800000000008e580002f481049c180001bd03c67ae878e6fc8000000249e00028d6000000026800003c88000000000066a000000015dc51d02989be06b8a13000050e1a4e5cd80008be0f5e00020fe000205039e80007ed00004a9000000016de5c28af89cc115470390fc000166a000032eaab27de0000000000000000020800001522000072c0001d6c00009e400010465328000000000021f11560aa000050b8632000000000004aa4688672427061082c80000001b9a0db047e425142a755817c5f1000096e2b7e9e98460a3b0000991210a3681e2e0001d0442196ca97500000b09d5a109a56a9d29a3a3730f8677294141558f4a00028cc2878000a43a3eaa0da82e0001cfc44da81493b8000472833e000000000000007d7a2e6adf000000018ceae21bae000000000025560001a403b42664a2a00000000000a4315440000000948800038fa426298a6c00002154
  | 48 => 0xc6971ad2773069209300481378000000015e0000000000000000000003d813e8899800000000007fa194e00000008f8000088ea8620000cf20000992000130600009d85690000000000092f8b50a161bd65fa1dd21fb8000000000042ba72085e00000000000000000096f000000024d41440d5000006c4a8b00002a191322fc8000a2f248457b8000000076616c000076a8332000000001880000981a0064a146a22316203d31be080f800000009de14e05ec000000000022d8000027465e16b040c0f8800002b20000000271269600000000000a4090b8000004a97234800006b3a80a000000083e00000000f1e00005da0000000000293a307aba40b28d5c728a20e00000009242366479a18400000002c29ca0000185401111a699512461f18c5870a80000000000000000000000de43e80003411520af687aa5be248e0d700006c80000000000055880000000000756151200000000000000000000086500009e800007790000000000092e800000000003d5800057300000001508000000000000000000d840000000000000098900003ca0000aca800022b80008c2063a6858fce0001f7e6f3800094280008dd10b276824ca2d00000000000000011463c0057600025389df0cca108a33e9da80001a0000073203240002b980002942a33875615b00003390000000000000000000eba4d039aabb6000000000023a64ec112608c80000001f5842497be00000000c3000000000009baa8e60000000000000000006d61ed000000000000000000000172a0000f702a21af60000506a16a472000156a5a8161e0001e228089eee0001ad49478902000261ea57800066680003cb905a61a942217f2b4232f1ebc0000ff00000fbe6091b1e0001404184810e1b2aa3884a80003eaa02e6012bba68a20ce00b8ae00989dd40001b400e500008a784029e420f058a00002e00000343806a5181d90a74077e93d85ca83b98b8a9a8dd20d4820019295ec5b1001450d9622a6026425cf25e4794083a3649e9400021ba59886f0450000053e251a5c82b327a8928e4fa827e2c780008a5914a00028802f3800085b000066980003f98b321c0abbc0e0031400010024bc8f2c08880b400000005b6916655a0182000012a41a118a000000000029164f79b3e9411ea04968f901861d2c0e7aa06000000046800002bc03c00ba8000732800000000007ff80006a71f00a4900008eb00000000000022000000000000000cc2379900617c8000000000000008d833d00005f7a98c50580000000000000019c67c0a7c51710906d5221c1f79bdc2e524320001182000253e000000000000005ad08787c11b880000dc8000169e00000000000d1c0fd00000000a000000000000000003e270a2ada1c8000084a00012cc26727746bb130c99c1eb235f9c7474f2830228
  | 49 => 0x14e46579f943c402664848000a0400003b1959c05900000002a1200008ac60605a000700000000000000000063fa7be1b1a4340001e1a00019a2aa1101a6f8907c0150000a4b9d8e02486c00001b620000f7e0000000a49800000001228668d2a00005d40001888000000093f000038ba7f87c200000000000000167838e8dae586aa42000000000000003601dfc00026fe8b780005f800002d280007fb00000000000000000000003b200000000000000000114205d8000ae0099684d00008e1800062396a463e97a417884444860804000000047a80009f41c2c0000c360001282275286c2fe800008aa2ec3f6000072f80007d68f40641053caef9de28f61cec0000b6a0e289704bd000040b8000608176e17fa8ba658800088403ba4d69e9e04baaba00000004f3800019788540000000000000000020c026884f61a1a56c2f223c0000000000000000001c7277f8000294820e000000042f00008408000000248800019520000000569800090b00005200fee0001498000037a0000322000294e000000000021bc000000025380000000ab400000009a9ab8600000000000c963319a3e0000000231800000028e80000000799800014800004488fb00001c5a00000008150000000236000024da7cb0716528273c00008da5b8a384406139c4b8800000000001508b0c5b480007cc8fa44f60a9c6c982ae0eb00003ff0408a79981069e1b9076e8f3234c80007721ffa1ada1080000000641a9300002598000000000013a63ce9850000000078100000000000000272400018b0652000083b218600000000000a9800000006e82448000000000000000001cb059a00000000cfe77d00008010e5e00000003810000026a6f20588ab800000000002106202031c000000041e993c00d00002fa8494000000099e00009a117d00001bea8188c886b6a64a1fb12be14097c02af19ea25e000000000007251644000000010f8b2a00000008bd9e900002176000083c00017ee2c71d22000259a5dc959679fa84e21da9540000526a27000000016360001b068d8800067d82aaa4881ee1619c4800000000001fd087f02d636eaa1403d9ba21d112d0a451d0604d97080000000336018800029aa000000041d92300000b28679000026d1c34ada084477c000014119b6000011e88924ea0d40180750086a3d6800064b000000000006aea2703fe00000000000910175800000009580000245076a000190a2558000284800061d0000163000053d97808789a4c0002382000000088280005c70fba4a724f80001fc800019381e1a03c3fd20c800015fc2ba0000000138400000009a08000000089a4c5238058fa56457c9efe76180000001c363a5800000015f0000000043580000000d263bc00002d6000076700004e623bc895a3d0000112a2fd000008a2ab
  | 50 => 0x827c5800000000004231e648128566000000023d800060b88647459250af5957e0000e64412201062880d835a8000991a18032d80000000000040000077784e4254000038989aa2b3000000029c871280000001d180000f5c25790f66cc18dc16105e62a0899e86781ec00000000002328000000038405603862a1c00000001c623b053b80000000f829fb0000a8807a6624000000000008b5817033b146c73f86d8000000064512f00000000a529efc22aa9e0497891a8e30f640001b6414300000000d52a83901400f259e1489f182f42390000237a50b2528a8d000019491f400000000001846aac0c2c00004da09200000000000000040000000004a40d2e2890000797821601411120000000000000000000000000000751a80e4d21e300c20000000000000018c20001df600002967f5959a00004803c597006a818300001bfa33409ae0000000000065600000003b223020000cc0a24072e1dc097a0002206000000000000000000000000176c883022050faa4aac18482a7880001cf2a6e5a4126e35310001a9897e7ba0288951a5ba66c0528000284a3ab875e3441c6c1048aa6000210e8d6a1926dc0000171000064027fa24280000002b14000000099c800000003660000000000230e6918500000212800000009768c9a733a120594a2aa988ab4c63400003f41c6a3ac276e7d5000038180004dfa216000150c49f8000000000000000001db00000000000000000000000002f080000a18f44000078a00000007e0259c0cd90ec7ce80004ae00000c400006fe000005705be0001b7a00000008f698680001f8e00011aa00000b632109900002ba800010f8000000054a134262a000098da74200000000000000000000000000000000b7280002f200029dc240268a0001f8443680000000000000000000002d24c8000096b997e43600003bc8000000244e0da80000000fc400022888b2a44a98421c200000005cb295a0001e880001fc600000003ee000002525ca0002b2478914880000000000000000003480a30000ad780000000efa00000006f0a02401800004a19f2836aa93c2738000862808465f13ae0000000771800000026e200000001520ae4053a49aae8ab4eace2b4858a87965f50cc40000000000175243280001fa83b80000000000000084100000000000000000097d00000001a103968000000208497580000000000000000000000004198f145cb8000035959491f10360e60f7c0ca81a029e28fa3ce1e3e620a9ca000212214c9f1c000163a00002fe19e82361228a106128174000000000000001de26a80d7a30000000000001fae3f2110a07500000000000000191c0ed0000378000010c80007bd800000007760000f3e000060c6db879890c275621800005161fb00ad80004ec80009d196484e79d42649002400
  | 51 => 0x499800070600001f200000af99ec6dc800000022b801f800073980002788000ace95b20b201a487480000000000220143403e9e80065000000010d290920326c3800086b85ae3700ee29c6074a443274e6b1800000000003cd860e83812fa1c783be0f61ee65c38dde0e707f4415005e00027ac033863e00980001da000000021f4367800040109080d08000863abd45e7ab8e0000a56000220200008d47bc800009b97ea0000000000000000000004758000000000000007042e780000000000097a34434000b0000000000016d6000000035b800000000000001cde312a5ec332049600017548aa2482817067600000004f00000000001000000001a68912342a5fe4a98e000000a6a00000000000dec81618e6000172897c12c66f00414a1d86403138eee7a321be00000001bb8a9603708dc44b0726867109e1890e5612387da0000b6011225dc372ab549f898d24ab9338819971a1031b4a7d58ba6180885e5d328c89d51798a65a9946898a6c150107810d92c015715ea000000059083e22108000040a3c87fc9d3812eab440000d94951287000000009c42b7a00024760000e3c0000f7800013d6aa5000000017f45d9800000020760001b5a000127896f8d5e2fb958200000000002a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87e86dd52044001878c9baa40881a31b18b754811034c3f43eca902206887c87d95204400187eebb2240880030f1d764481100062fbaec69022000c5c75d8d20440018beea31a4088003171d4634811000637baec49022000c6c75d892044001968c9b8a40880033518f71481100065a320e29022000cd4631c520440019cec438a408816f1e9db65c41102ae5d3b6c98822002cba7619310440b39b4edb1e2088027369d863c4110256753b6c58822001cea7618b10440017a106a0e2088002dc61431c41100245f43ea8b202000c3f75d51640400153d07aa2c808002a760f54590100245e43aa8b2020048be87909640400187eeb3aac808002a7a0e75590100054ec1ceab202000a3e851cd640400147b0a39ac808003275cc735901000557410e6b202000aad821cd640400117d0fa9ac8080022f61f53590100070fa9ca6b202000a9f835c9640400153906b92c808002ad20572590100051f428e4b202000a3d851c9640400153d06392c808002a760c725901000717a94a4b2020008be87149640400117b0e292c808002a7a0c52590100054ec18a4b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b2020068be87d45640400117b0fa8ac808002a7a0f51590100054ec1ea2b202000aae82d45640400155b05a8ac8080038dd4651590100255d404a2b202000ab980945640400d17d0f90ac8080022f61f21590100051f42e42b202000a3d85c85640400153d0790ac808002a760f21590100255d40042b202000ab98008564040091b90ea9ac6080122fe1d6490c100245e43ac8a182009a9c8359143040091d90ea92c4080122f21376508100046fc1aeca1020098dc835d942040091790eb2284080023d61b71508100065ab26e2a1020008f5861c5420400196ac838a840800a2f213764c8100045fc22ec99020028bc845d932040671ef02bb264080022f61b744c8100045f43ac899020008bc8759132040091b90eb1a64080123b21d624c8100065b326e29902000cb564dc532040011eb0c38a64080032d990714c8100065ab20e29902097cd6631c532040559ccc438a64080132e9c164904100065cb22e12082032c9e64dcd410400193ac9b9a82080af2799073504100064eb20e6a082045cd6611cd410400517909bb262080be2f61b744c4100045f43ac898820068bc87591310400187cc8ba862080271798d750c41022e3b30aea1882000c3e75590310400187aeab2062080132e9c1640c4100062ebaac61882000cb9645c031040091df0eb1442080031e1d776440100065dc26ec8802000cb884dd910040018f6edbaa20080032eddb74440100065dbb0e88802000cdb76dcd10040019b6ec39a20080033addb724401000675bb0e48802000bd38350510040015e70c98a2008002ece113144010
  | 1 => 0xe7b8282881576cdd07050510006e9b98e0a0a205bc7676d9731440b7ae4e1b2e62881572d9db64cc5102aed9386c998a205acb6761933144001c68ca326628816b6c9c064cc5100072bb2ec798a2059dd270d8f31440679c8c4b9662880ceb9a1b62cc510256733b6c598a204ade270d8b31440b19ccec316628800399d9462cc51000732328c598a2000ea76418b3144001d48c83166288003b118c62cc5102c6f1380c598a2047cd671d8e3144001878e9b2a628816a2fa1b744c5100061fb2ee898a2000c3c65dd131440fb938c7ba262880032b18b744c51044c5f43ec898a20558bc87d91314400193ee9b1a6288003271d3634c5102ce6c386c698a2000caf74d893144001958e9b12628800e1f216760c5101643e432ea18a2000c3c645d431440138b8c6ba862880031b189750c5100043fc3eca18a200c87d87d94314400187cebb2062880030f5d7640c5100062f3aec618a2000c5d75d8c31440018dcebb1062880031b5d7620c51023e6a31cec18a2050974865d4314408faa8c6ba8628800355d0d750c51023eaa21aea18a2047d57325d431440012ef0fb28628811e7520d740c5100069abaec818a2000d35751903144001c68ca3206288003555d7630c5100072bb2ec618a2000e5465d8c3144001d2ec9b186288003a5193630c51026d6ac3ec618a2059cd587d8c314408fcacebb18628811f955d7630c5101547a432e418a202aae686d883144001acaebb106288003b1d8f620c510006b2ba8c418a2000e67651883144001cc8ca3106288003a9d90620c51000752320c418a2000ec7631883144001d88c63106288002b5219320c510006aabaa6418a204eb94844c83144055d88c499062880039918b65885100047b436e910a2000ea462d92214400196cec3244288003a9188648851000762316c710a2000cd67618e2144001d88c431c4288006b9a1b6288510006733b6c510a204ace870d8921440b78e8edb2a42880039918b65485100247a432e890a20479d4835d121440ab968edb22428816b2d1d8644851000752310c890a2059cd476d8d214409b9a8ec31a4288003b1188634851000e723b6e490a204ace476d892144095bc6e438242880033918b71501100065bb20e2a022000ce4621c540440093690ea0a8088012ad2194150110005ca41a82a022004bb08050540440070f90b3b660880021f21975cc1100061e322eb9822009c5c635d730440018d8c4bae60880021fe1f65cc1100043ec3ecb9822000c3e75d93304400187aebb266088003179d763cc1100062ebaec79822000c6e75d8b30440018daebb1660880273518e71cc1100043fc2aec982200387c855d9304400117f08bb2608800a2f211764c11000477c12ec98220018ec825d930440019c8c5b8a608800335d8c714c11000672310e29822000
  | 2 => 0x1631891000567430c63122000cce7618c6244001c9eca318c48800393194631891000747b20c63122000e8c6418c624414fd8f02318c488003b15c4631891053f63080c631220a7ec41018c6244001cc8cb288c488003a919251189100076231ca23122058ae4865446244001d48c8a88c488003b118d511891001c3f42eeca12200087d85dd942440131bd07bb284880023760f76509100043fc2aeca12200387c855d9424400117f08bb2848800237e0d765091004c6e41aeca1220008ef825d942440011ef02bb284880062fa1f64509100147743ec4a1220048f5819db324408f9a8633b664880021fe1576cc91001c3e42aed99220008bf845db324400517908bb664880063720d76cc91001c3f42eec992200087d85dd9324400517d09bb264880022f613764c9100145f424ec99220008bd849d932440010ff0abb2648800e1f215764c9100045fc22ec99220028bc845d932440011bf06bb264880023de05764c9100145e420ec992202a8f4811d93244001878e9b2a64880022fa1b744c9100061fb2ee89922000c3c65dd13244141938c7ba264881072b18b744c9100045f43ec899220008bc87d9132440031bd0fb1a648800327dd3634c9100064e3a6c699220098ee87d89324400195ee9b1264880032b1d3624c9100247b436e29922000c7765dc532440018e8cbb8a64880032dd93714c9100065a326e29922098cd463dc532440679c8c5b8a64880031dd94714c9100063a328e29922000cb7641c53244001968c838a648800335d8c714c9104be6a318e29922000ce7621c532440559c8c438a64880038d19365905100155b436c920a2000cb676d924144001d28c9b1c8288003a519063905100055b4348720a2000ea464d8a41440019ccec3148288003a9190629051000762318c520a2000ab48650a4144001c6883b2a82881572e1c3645051026c6f436e6a0a2000c5f65dcd41440018b8cbb9a828800327d9373505101964e326e6a0a2000ccc62dcd41440b31bd0c39a828800317d9473505100062e328e6a0a2000c9f641cd4144057938c839a8288003331887350510276ca208e6a0a202b8de87d8d41440b31b90fb1a82880ca37a1c635051004c6e438c6a0a2000e944118d414400199ee7b128288003331cf62505102de3a3b6caa0a2000e3464d954144005968edba282881572d1db64505101966a3b6e6a0a202bcd4761cd4144001b2ee839a828816675a18735051023eab428e6a0a2047d55851cd4144001aaeca39a8288003551947350510006cbb20e6a0a204ed94641cd414409db2e8039a828829a75a1f63505102ce6a3b6c6a0a204d9d48718d414409b9a8ec31a8288003a51906350510256723b6c4a0a2000dc473d8941440b19c8ec3128288003a91906250510006e2398c4a0a2000ec4631894144001ba
  | 3 => 0x7b122000a6f855c762440014d90ab8ec488002abe1171d891000556422e3b122000acf835c7624400159906b8ec48812a3ba1f51d891000476c3ea3b122000aae84d47624400155b09a8ec488002b3a0f51d891000566c1ea3b122000a6e85dc362440014db0bb86c4880029ba1740d891000536c2e81b12200387e86dd562440018d8c5baac4880021fa1f65589100061e3a6cab12200087e871956244001878e832ac4880030fd9774589100061e32ee8b122000cac62dd1624400117d0fb22c4880030fdd764589100061e3aec8b1220008be87191624400187eea322c4880030f1d464589100062fb2ee6b122000c5c65dcd624400193ec9b9ac48800327193735891000666316e6b122000c5f651cd62440018b8ca39ac48800327d9073589100064e320e6b122000ccc621cd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d0635891001c3f43eeab1220008bf845d5624400517908baac48800237e0d755891004c6e41aeab1220008ef825d562440010fd0e3aac48800a2fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d4745891004c6f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c6f75dc962440018d8ebb92c4880032bdd37258910006563a6e4b122000ccf73dc96244001998e7b92c4880032d1d371589100066a39ee2b122000c6e76d946244001ccae3b28c4880023b61e65189100053742cca3122000aae84994624400155b09328c488002b3a0e651891000566c1cca31220008ef87594624400155f08b28c488002ab211651891000567c1aca3122000acc8359462440014dd0c328c4880031b9d8651891000732c08ca3122000e66711946244001ccae2328c4880032b9db641891000717b2ec83122000e2c65d906244001d4ae3b20c4880023b61e64189100053742cc83122000a6d85990624400155d09320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400155d0c320c4880032b9d8641891000717b28c83122000e2c651906244001d4b02320c488003a95c4641891054753080c831220a8ea410190624400199cedb18c48800393d9763189100072632ec63122000e8f64d8c6244001d18c9b18c488003b1607631891000762b8ec631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c624400159d07318c4880023be1d631891000537c2ac63122000a6c8558c624400155f08b18c488002ab21
  | 4 => 0x3440014bd0b310c688002976166218d100054f424c431a2000a9d849886344001ca8cb288c688136b52195118d1004c6f43ea831a20008dd87d506344001c3ea92a0c688002b5a075218d100056ac0ea431a2000e4f5294863440131bd0e290c6880023761c5218d100054f420a431a2000a9d8414863440015ad03a10c688002b56074218d1004c6f4388431a20008dd8710863440014bd0a210c688002976144218d1004c6f43ea231a20008dd87d44634400153d09a88c688002a76135118d1000567416a231a2000acd82d4463440131bd0f908c6880023761f2118d100052f42e4231a2000a5d85c84634400153d09908c688002a76132118d100052f42e8031a2000a5d85d0063440014bf0a880c688002972151018d100054fc222031a2000a9c8444063440091eb033b486880021fe157690d1001c3e42aed21a20098dc835da43440011df04bb486880063b2097690d1001c3f42eeca1a200087d85dd943440031dd05bb286880023b60b7650d100043fc2aeca1a200387c855d943440011bf06bb286880023be097650d1000c76412eca1a20098be87d9143440051bd0fb1a86880123da1b7150d100063a32ee2a1a2000ce462dc543440093e501b8a86880031d1947150d100065bb20e2a1a2000cd7631c543440019c8c438a86880031b5d752d891000572c0ea5b1220038ef8754b624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc835976244001ccb0232ec4880038bd9764d89100071632ec9b122000a6e8599362440014db0b326c488002b3a0e64d891000566c1cc9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000e2f651936244001c58ca326c488003a960464d891000727b2ec7b122000e4c65d8f6244001d1ec9b1ec488003a319363d891000762c0ec7b122000a6e8598f62440014db0b31ec488002aba1263d891000556c24c7b122000a6f8558f62440014d90ab1ec488002abe1163d891000556422c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000e646594762440955c90ca8ec488002aba1275d891000556c24ebb122000ace839d7624400159b073aec4880031b5d475d891000573408ebb12204aae5811d762440014dd0b3a6c4880029b61674d89100056741ce9b122000acd839d362440015cd023a6c48812ab960474d89100056741ea9b122000acd83d536244001c5ea92a6c488002aba1373d891000556c26e7b12204aae581dcf62440014dd0b39ec4880029b61673d891000557424e7b122000aad849cf624400155d09a9ec488002ab61353d891000727a9ca7b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c288
  | 5 => 0x800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c688002b5a0472d8d102cd6ac08e5b1a2000e4f5294b63440011bd0e296c6880023761c52d8d100054f420a5b1a2000a9d8414b63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b63440b31bd0fa8ec6880023761f51d8d100054f426a3b1a2000a9d84d47634400159d05a8ec688002b360b51d8d102cc6f43e43b1a20008dd87c8763440014bd0b90ec6880029761721d8d100054f42643b1a2000a9d84c8763440014bf0ab86c6880029721570d8d100052f42e81b1a2000a5d85d0363440138b8c6bacc6880030f9d36598d1000637396cb31a2000c3e7419663440018dce432cc6880030fd957498d100061e32ae931a2009c9c635d2634400187cebb24c6880030f5d76498d1000657396c931a2000c3e75192634400187aea324c6880032b9c86498d100062f3aec731a2000c5d75d8e634400193ce9b1cc688003275d36398d1000667396c731a2000c6f655ca63440018d8cab94c6880032bd917298d1000656322e531a2000ccf635ca6344013998c6b94c6880021fa1f6558d100061e3a6cab1a2000c6c72d9563440010fd0e32ac6880030f1d06558d1000636390cab1a2000c3f65dd16344001878cbba2c6880022fa1f6458d100061fbaec8b1a2000c3c75d916344001958e5b22c6880022fa1c6458d100061fba8c8b1a2000c3c751916344001958e4322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880022fe117558d100145e422eab1a20008df835d563440011df04baac6880063b2097558d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440019c8e5b8ac6880123d6067618d100046fc3ac631a2000a5f8558c63440014b90ab18c688002a7e116318d100054e422c631a2000acf8258c634400159904b18c688136b56067618d100062f3b6ca31a20008dd87994634400153d09328c688002a76126518d1000567414ca31a2000acd8299463440011bf0eb28c688002a7e116518d100054e422ca31a2000acf82594634400159904b28c688003179d86518d100072ac08ca31a2000c9e76d906344001c3ecbb20c688003871976418d100046ec3cc831a2000a5e8599063440014bb0b320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc82590634400193cec320c68800387d946418d100070e328c831a2000e95811906
  | 6 => 0x51ec2e43b222000a9e83c87644400153b0790ec8880028fe1570d91100051e42ae1b222000c3c64dd564440010fd0fb2ac8880031b1cb65591100043f438cab222000c6c7219564440018becbb9ac8880031719773591100064e326e6b222000c5f651cd64440018b8ca39ac88800327190735911000637b2ee4b222000c6c65dc96444001958c9b92c88800e1fa1f75591100045fc22eab2220008df835d564440131b906baac8880023be09755911000c76412eab22200087e871d5644400187eebba2c8880030f1d7745911004c6f43ee6b222000c5f75dcd64440018b8ebb9ac88800327dd373591100062fba8e6b222000c5c751cd644400193ee839ac8880063ba1f725911000637baee4b222000c6c75dc9644400195ee9b92c88800333dcf72591100066639ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440019c8e5b8ac8880030f9db65191100071ab8eca32220008bd87994644400147d0b328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100051f430ca3222000c3e761946444001c6b02328c8880038d9c465191100071ab88ca3222000a3e85988644400147b0b310c888002a7a0e62191100054ec1cc43222000e346594464440b55690ca88c8882a71d5c465d8d100247ac0eebb1a2000c5d75d4f634400153d09a9ec688002a761353d8d100056ac0ea7b1a2003c5c7594f63440071bf0ea9ec68800297a1443d8d100052ec2887b1a2000ace8210f634400159b0421ec68800297a1432d8d100052ec2865b1a2000a9e840cb634400153b08196c688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec6880039560465d8d100070fb2ec9b1a2000e1c65d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc825936344001c3eca326c6880038719464d8d100074ac08c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000e57655c76344001ca8cab8ec688003a5d9171d8d100074a322e3b1a2000e546594763440b35a90ca8ec688002b5a0775d8d102cd6ac0eebb1a2000c5d751d7634400153d083aec688002a761075d8d100056b408ebb1a2059ad5811d763440b35ab03ba6c68800297a1674d8d100052ec2ce9b1a2000ace829d3634400159b053a6c688002b5a0474d8d102cd6ac08e9b1a20008de87d5363440011bb0faa6c68800387d5254d8d100054f426e5b1a2000a9d84dcb63440b35ab03b96c68
  | 7 => 0x9c8458e31c405753908b18638800355d0d750c71022eaa21aea18e2045d57325d431c40bf72908b186388002b5e19320c710006aabaa6418e205fb94844c831c40091eb0dba443880026d613764871022cea41ae890e20049b48750540c400172906a0a818816637e1d63cc3100245e43aa8b2420048dc8754d63840091bd0fa1ac708002976144358e1000566c1086b1c20048bf8759243840091d90ea92c5080122f21d6450a100045fc22ec99420028bc845d932840091b90eb1a6508003271d1634ca1000d66412c69942098cd663dc5328405793cc839a830800327590735061026c6fc3ac798c2000c9c7458d318408f8eac2ba8630800297a0e64d95100052ec1cc9b2a2000a6e8299365440014db05326ca880028fa1262d95100051ec24c5b2a2000a5e8398b65440014bb07316ca8800297e0d74d95100052e41ae9b2a2000c3d741d365440af4ed023a6ca8816e9d60474d95102dd3d400e9b2a2000a79801d365440a14ed03b9eca8816e9d60773d95100051fc22e7b2a2000a3c845cf65440018bae639eca880021fa1c43d95100043ec3887b2a2000a6e8210f65440014db0421eca880028fa1272d95100051ec24e5b2a2000a5e839cb65440014bb07396ca880031b5c872d95102653b408e5b2a205ba75811cb65440010fd0e216ca880021f61c42d95100052f41885b2a2000a5d8310b65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb65440b70fd0f90eca880021f61f21d95100051f42643b2a2000a3d84c8765440014bd0790eca880029760f21d95102253b40ee1b2a200087e87d0365440010fb0fa06ca880030f5d754d91100054f41ea9b222000a9d83d53644400156b03aa6c88800e2fe1d54d91100054f41ccbb222000a9d83997644400155d0532ec888002ab60a65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91100071ac08cbb222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b222000e346594764440ab5690ca8ec8880030f5d475d91100054f418ebb222000a9d831d7644400156d023aec888156ad60475d91102ad5ac0ee7b222000a3e859cf644400147b0b39ec888002aba0a73d911000556c14e7b2220008be87d4f644400117b0fa9ec88800387d4e53d91100051f42ce5b222000a3d859cb644400153d07396c888002a760e72d91100055b408e5b222055ab5811cb6444001c5ea5296c8880022fa1c52d91100045ec38a5b222000a9e8314b644400153b06296c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c8881562fa1f51d91100045ec3ea3b222000a9e83d47644400153b07a8ec888002aba0b51d911000556c16a3b2220558be87c87644400117b0f90ec8880028fa1721d91100
  | 8 => 0xea3a2c690003271d37358d2001e2e3aca6b1a40abc9c7494d63480071b90ea9ac6902ab271d15358d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c563480019aca638ac6900033554c7158d200063c3aee0b1a40008df8758c634800153908b18c690002b52056318d200043fc2aed21a400387c855da43480070fd0bbb286900021f6177650d200043fc2aeca1a400387c855d9434800117f08bb2869000237e0d7650d200047bc0aeca1a40008f4815d943480070fd0dbaac29019e1f21b75585200043f43ecab0a4000c3c74d9561480010fd0e32ac2900030f1d065585200061fb2ee8b0a4000c3c65dd161480018becbb9ac2900031719773585200062fb28e6b0a4000c5c651cd61480011ef0eb08c290002ad21161185200056a41ac230a40008df835d061480131b906ba0c2900022fe1173185200145e422e630a4000af18010461480010ff0abb4829000e1f215769052001c3f42eeca0a400087d85dd941480131bd073b282900023760e76505200062fb2ee6a0a4000c5c65dcd41480018beca39a82900031719473505200043fc2aed98a400387c855db31480010ff0abb4629000e1f215768c52001c3f42eec98a400087d85dd9314800517d093b262900022f612764c5200061e3a6ca98a4000c3f65dd13148001878cbba2629000e1f216760c5200043fc2aec18a400387c855d8314800117f08bb0629000a2f211760c5200043e432ea18a400087f87d9431480010fb0fb2862900273318d720c52000c7c432e018a4000cf0615c031480d30f90cbae60901a21fe1f65cc1200043ec3ecb9824009ccc635cb304800717f0eaa6c98800e37e1d53d8f100247a40aed31e20008bf845d563c400517908baac7880123d2057558f100145f43ee8b1e2000cb7741c563c4001968e838ac78800237e1d6318f100247a40aed21e20008bf845d943c40070fd0a3b287880021f6147650f100247ac30e2a1e200087d879d762c40070ff0ebaec58800e3be1d52d8b1001c3f42ceca16200087d859d942c40131bd073b285880023760e7650b1000c5f43ec8a162001aae82d9142c400117f08bb6658800a2f21176ccb1000c6e41aed99620048f4815db32c408b9a862bb6658800e1fa16764cb100043ec2cec99620028be849d932c400117b093b265880022fe11764cb100145e422ec99620018de87d8d32c400359d05b1a65880123d618714cb100245f43ec8a0e2000c9f641cd41c4057938c839a838817f651047350710005d8c06c8a0e2000d97741cd41c408baad0a39a8388117556147350710006cbb20e6a0e205fd94641cd41c40bfb2e8039a83880026de1176cc71019c7bc32e598e2032a
  | 9 => 0x76484300145e422ec90860048f487585210c0091790eaa2c9100123721d5358e200245fc3ac921c400387e85dd943880010fb0bbb287100022fe1173986200145e422e730c40048f58794661880078eceb28cc31000e1fa1f75586200063610eeab0c40008bf845d5618800517908baac31000237e0d755862004c6e41aeab0c40028be87dd1618800187eebba2c3100030f1d774586200061fba8e8b0c4000c3c751d161880018beebb9ac310003171d773586200064fba6e6b0c4000c9c74dcd61880b39ab03b9ac31000317dd473586200062e3a8e6b0c4000c9f741cd6188001938e839ac31000f1d1d651586200247a43aa2b0c400087f855da41880070f90abb483100123d61e61906200155a422c320c400087f855d941880070f90abb2831000237e0d765062004c6e41aeca0c402bc9e641cd418800193ac839a8310003351ce61506200247a43ac2a0c4000cd47358541880010ff0abb4631000e1f215768c6200043fc2aec98c400387c855d9318800117f08bb2631000a2f211764c6200063abacc218c4000c757558431880015af06b0863101623be1d618862000537c2ac310c4000a5f835d365480014b906ba6ca900030f5d074d95200051fc22e7b2a4000a3c845cf65480018bae639eca900021fa1c43d95200043ec3887b2a4068a6e8210f65480014db0421eca900028fe1171d95200051e422e3b2a4000a5f835c765480014b906b8eca900029be0971d952034536412e3b2a406887e87d0365480010fb0fa06ca900021fa1f65591200043f438cab224000c5f65dcd64480018b8cbb9ac89000317d9473591200062e328e6b224000c9c641cd64480018eecbb8ac8900031d19771591200063bb28e2b224000c74651c56448001968c838ac89000e1fa1f75591200046fc1aeab2240098dc835d564480011ef02baac8900023d20575591200043f438eab2240038bc87551644815b938e6aa2c89002637a1f73591200062fbaee6b224000c5c75dcd64480018beea39ac890003171d473591200064fba0e6b224000c7775dc564480018e8ebb8ac89000335dcf71591200066a39ee2b224000c77751c564480018e8ea38ac8900032ddd071591200066bb98e2b224000cd4731c564480019cee438ac8900032d95071591200065aaa0e2b224000acd8210f63480070fd0b38ec6900021f61671d8d200043f43ecab1a4000c3c74d9563480010fd0e32ac6900030f1d06558d205663db80cab1a4000c3f65dd16348001878cbba2c6900031dd977158d200063a32ee2b1a4000c77651c563480018e8ca38ac69000e1fa1f7558d200045fc22eab1a40028bc845d563480011ef02baac6900023d2057558d200047dc02eab1a400087e871d5634800517d0fba2c6900030fdd77458d200061e3aee8b1a4000c3f751d16348001878
  | 10 => 0xb0c6047ad6839d5618c0015ab073aac318002b9a0a755863000572c14eab0c6000ad7835d5618c08f5a906baac3180029da1674586300053ac2ce8b0c6047ad6839d1618c0015ab073a2c318002b9a0a745863000572c14e8b0c6000ad7835d1618c08f5ad07aa2c318002b560f54586300071baa4a8b0c6000a77855cd618c0014e90ab9ac318002ade1173586300055a422e6b0c6000ae7825cd618c0015c904b9ac318002ada1353586300055ac26a6b0c6047e5653d4d618c0014ed0b392c3180029d61672586300055b424e4b0c6000ab5849c9618c08f5ad07392c318002b560e72586300056bc1ae4b0c6000e6752949618c00156d08292c318002ad610525863023d6b418a4b0c6000ad583149618c0014ed0a212c3180029d614425863023d6b41884b0c6000ad583109618c0671ef0e992c3180aa3d21d32586300055bc2264b0c6000ab4844c9618c08fd8864992c3180123d61e61906300245e426eca0c6070c9c73591418c06593cc9b9a831800335dce615063022e6a39cc2a0c60048f487585418c08f9a8e6b0a83180033c985708c63023ee938ae118c60008bd86dd1318c0011790eb2263180032ddd2614c6300065a3a4c298c6000cb774585318c001968e8b0a63180033c587704c63023f2b3aac218c6047e5575584318c0070fd0bbb443180021f61776886300247ac3cc310c6000c9e64dcd218c0091e90eb0a431811f351cd614863001c5fc3aa9b2260008ef825d5644c0031d904baac8980023de0575591300047a40aeab22600087f855c7624c0070f90ab8ec4980022fe1171d89300145e422e3b1260018dc835c7624c0019c8c438ac4980062f21d645093000d56412c8a1260008df87593324c0019cec438a64980ab39188714c93020e4e3b6e89926041e8c62dd1324c13b938ec3a26498277a3188744c93000d66416c89926000e8e42d91324c0031b90eb226498006b3209644c93000d67436c49926000acc86509324c001d1ac8a1264980cf351db714c93019f62316e2992602acd4761c5324c001b28e838a64980abb1188714c9300047bc3ac230a6000ae482584614c0078bceaa98c298002b560f21185300043fc2aed20a600387c855da414c0131b9063b2829811e3d61f618c53022c7b438c298a60048bc87551640c0091f100baac4180123b21d525883000c6ec1ee2b106098cd431dc5620c0011ef02bb284180023d20576508300245e43ac8a1060048ec87589420c0091eb0f28cc2180022fe1175584300145e422eab0860098dc835d5610c00517d0fba2c2181f7271cf745843044e4e398e8b0860048f487545610c0091eb0f30c821800aad21161904301946fc1aeca086009c9c73591410c0139a8e730a82180123d21d615043004e6a39ac2a086032a9c84586310c0091eb0f30c42180022fe11
  | 11 => 0xcc001d1ac8a12659800395597714cb305766bbb0e29966000e55651c532cc001b28e838a6598007339c932987300246e41aeca0e6009c5c7359541cc0018bccbb9a83980031759773507300145f426ed10e60008bd84dda21cc0138b8e6b2a8198027271cd64503300062eb2ee6a0660048be87d51648c00187eebaa2c918002a760f54592300245e43aa8b246000c3f759d5648c0e153d073aac918002a760e75592300045f43ea6b2460008bd87d4d648c0e1c3ca7a9ac918002a7e0d72592300051f428e4b246000a3d851c9648c0e153d06392c918002a760c725923000656b90e4b246000e2f52949648c00117d0e292c9180022f61c52592303854f418a4b246000a9d83149648c00153f06b8ac9180022fa1f51592300045ec3ea2b246070a9e83d45648c00153b07a8ac918002aba0b515923000556c16a2b2460008be87c85648c00117b0f90ac9180028fa1721592300051ec2e42b246070a9e83c85648c00153b0790ac918012aea0021592300055cc0042b246000cb964dc1438c0091d90ea92c51800a2fa137158a300045ec26e2b1460048bc87591428c0e1938e6b228518006ab2096450a300045ec36e899460418be87591328c13b1790eb2265181c3a30c9644ca300047ac36e29946000cb664dc5328c00196ac9b8a65180023d618714ca300065b320e29946000cb5641c5328c00156d09a8cc318002ad61351986300056ac1ea330c6000ae682d46618c0015cb05a8cc3180123d61e519863001e3b3aca330c6000a7685c86618c0014eb0b90cc318002ada1321986300055ac264330c6000ad583c86618c0018eeeb3acc318002ada1275986300055ac24eb30c6045ad6839d6618c0015ab073acc318002b9a0a759863000572c14eb30c6000ad7835d2618c0014ed0a3a4c3180029d614749863002579400e930c6000af1801d2618c08b5ad07aa4c318002b560f54986300071baa4a930c6000ab684d4e618c00156b09a9cc3181179594f539863022f4a21a8730c6000a7685dca618c0014eb0bb94c3180029da1672986300053ac2ce530c6000ab6849ca618c00156b09394c318116b5a0e72986300056ac1ce530c6004af2801ca618c0015e300394c31800399d4a52986300055b420a530c6000ab58414a618c08b5ad06294c318002b560c52986300056bc1a8530c6045ad48350a618c0014ed0a214c3180029d614429863022d6b4188530c6000ad58310a618c0671ef0e994c3180aa3d21d32986300055bc226530c6000ab4844ca618c0018eeeba8ac318002ada1351586300055ac26a2b0c6000ad583d45618c0015cd05a8ac318002b960b51586300247a43aa2b0c6000a7685c85618c0014eb0b90ac318002ada1321586300055ac2642b0c6000ad583c85618c0018eeeb3aac318002ada1275586300055ac24ea
  | 12 => 0x8023de057650d2100c5fc3ac920a427da9c83592414840193ec839a82908af2719073505211954e422c718a4200c9c74d8d31484011bf0eb1862908aea7211630c5214c56bc0ac618a42008bf845cf604840517908b9ec0908023ee1d60181210246e43aa6b1c80048ec8754962900131bd07b8ac5200023760f7158a400065a20ee2b1480008f7815d932900011e902bb265202832798f744ca400246e43ac69948001acc8258d329012f9acc638a65200033558c714ca400247d406eb30c80048f58794661900078eceb28cc3200123d21d51586402d45fc3ac320c8009c5e635d431900018baeab1863200031d5d6610c6400063abaac218c80048f58798621900091e90eb0a432000e37e1d53d8d400052ec2865b1a8000a9d840cb63500138b8c6bacc6a0003175d76398d400046fc3ac631a805a8bc865c643500010ff0ab8ec4a000e1f21571d894000c5e422e3b1280008df835c762500131b906b8ec4a00033918871589404ec5f43ec6a128070c9c73d8d425000355905b1a84a0003a38cb635094000d57436c4a12805a8be86dc5425000917b093b664a000637a0e76cc9400047b40cec99280008f5819d93250005179083b264a0003271da434c940014d643a849928000cac7650932500011ef0eb08c2a0002b920961185400147cc06ea30a8000ab781508615000156b09908c2a01c347a1473505403868ec28e6a0a80a5c9f601cd4150057b36c039a82a00462fa1c61505400064e398c2a0a8000d9873dc1415000917b093b662a00021fe15768c54001c3e42aed18a80028bc841d931500138b8c6ba862a01c34710d750c540384ce41ae818a8009c9c635d031500018baebb1862a00263e219700c54004e6c31ae018a80048bc865d121500e133906ba242a002697a0f745973010d2ec1ee8b2e6000c3f749d165cc0134bd07392cb981d69760e725973000637b94e4b2e6000a7b805c965cc0ed4f100b92cb980028fa1072597300051ec20e4b2e6009a5e831c965cc0434bb06392cb9802697a0e42597300052ec1c84b2e600087e8710965cc0010fb0e212cb9802697a0c42597300052ec1884b2e6000a3e84dc565cc00147b09b8acb9802697a0f715973010d2ec1ee2b2e6000a6e82dc565cc0014db05b8acb980021fa1f21597300043ec3e42b2e6000a3e84c8565cc00147b0990acb9802697a0f21597300052ec1e42b2e6009a5e8308565cc0014bb0610acb982c297e0d70597300043f43e80b2e600087d87d0165cc0134bd07902cb980029760f205973001e2f3aaa6b16600387e85dc562cc0010fb0bb8ac59800a2fa137158b300045ec26e2b1660018bc8759142cc0131d90eb12859802717dc9654cb3004f27b92ca9966000e4e4259532cc001c3acbba265982bf27dd8744cb300070eb28e89966000e4d6550932
  | 13 => 0xd2f41842b286200a5d83085650c4014ed03382ca1893e9d60670594313952fc1ae0b286209a5c835c1650c40147d08382ca188028f610705943104d2f418e0b28622ca5d831c1650c4014dd04382ca188029b60870594310053b408e0b28622ca75811c1650c4010fd0fa02ca188021f61f405943152f0e21e80b286200a7681101650c4014eb02202ca1882697a0f20594310052ec1e40b28620087e87081650c4010fb0e102ca188028fa1020594310051ec2040b286209a5e83081650c4014bb06102ca188029da0420594310053ac0840b2862098dc835d5640c4011e902baac81880e1fa1770590310043ec2ee0b206203c5e7554d620c4138b8e6b2a841880387d0d655083100c5e43ac8a106200c5d65dcd420c4131d90eb128418827331cd62508310063ab2ee2a106200c75651c5420c40196ac838a84188033958871508310062f3a2ca9906200c5c74595320c401838e8b2a641882717dc9654c83104f27b92ca9906200e4e42595320c401ca8e2b2a6418a7a67a1f744c8310070eb2ee89906200e1d651d1320c567b28e23a264188ae3721d644c83104ce643a849906200e4d65509320c401d1ac8a12641880395597714c831006cbba6e29906200d9474dc5320c4553ab0db8a64188cf3561b714c8314c6ab32ee29906298d5565dc5320c4138bce6b2c82189f78710d65904313ed4e41ac92086200c5d655ce410c4138b8e6b2a82188038d10565504310062f32ee6a086200c5d65dcd410c4019aca3bb2621880335547764c43144ccf43ee89886200c9f76dd1310c40193eec3a262189363721d535803126c6e43a64b006201ccc724c9600c40717f0eaa6c910acaada07745922101c3f42ee0b24420087d85dc1648840517d09baec7108022f61375d8e210047b40eebb1c42048fa80dd763884011f301baec71080a2fe1d74d8e2155e4f3a4a7b1c4297cd67194f63884071bf0ea9ec710aab279d153d8e2158e6b38aa7b1c4200cb6749c7638840196ae938ec710a5eb5a076398e2101c3f42ee0b1c420087d85dc163884011bf0eb18c7108022f6127650e210047b40ceca1c4209cce635c8318840517d09b9ac1108022f61373582210047dc3ac030442038bf8755364484010ff0ab86c89080e1f21570d91210064e320e6b2242008df835d564484131b906baac8908023ee0175591210247c402eab2242098de87dcd644840193ee839ac890803351cf715912101c6fc3aa7b1a4200a5d8510f634840159b0421ec6908021fe1570d8d2101c3e42ae1b1a42008bf845d5634840517908baac6908023de057558d210047dc02eab1a42048f8805d5634840517d0fba2c690803271d37358d210065bba6e2b1a4200cb474dc563484011bf0eb18c690802a72116318d214c56bc0ac631a42008bf845d943484011bf06bb28690
  | 14 => 0xb87580608c40187aebaa6c898802a760f54d913101c5fc3aa9b22620087f855c3644c4070f90ab86c898802aba0a65d913100556c14cbb226200a3e8598b644c40147b0b316c8988030f5d475d91313ed4f418ebb226200a9d831d7644c40117d0fa9ec8988022f61f53d91313ef0f29ea7b226200a3e859cb644c40147b0b396c8989f6a7a0e72d91310054ec1ce5b226200e2f5294b644c40117d0e296c8988022f61c52d91313ed4f418a5b226200a9d8314b644c4fb17d0fa8ec8988022f61f51d91313ed4f41ea3b226200a9d83d47644c40155d05a8ec898802ab60b51d91310071ba8ca3b22627d8be87c87644c40117b0f90ec8988028fa1721d91310051ec2e43b22627da9e83c87644c40153b0790ec8988beada0670d91310055ac0ce1b226200a3f855c3644c4014790ab86c8988022fa1c50d91310045ec38a1b22627da9e83143644c40153b06286c898802aba0850d913100556c10a1b226200ab681143644c40156b02286c8988022fa1c20d91310045ec3841b226200a3e85083644c40147b0a106c8989f6a7a0c20d91310054ec1841b226200ab681083644c40156b02106c8988022fe1175591310046fc1aeab2262008f7815d5644c40117b0f328c898802a760e651913100557414ca3226200aad82994644c40117f0eb28c898802a7e0d65191310055bc0aca3226200a3e85988644c40147b0b310c898802a760e62191310065bb20e2a1a62038ef8754b624c40117d0fb22c4988022fa1c645893100c5f43ec8a1262008be86dd1324c53b17d0fb2264989062f21f644c9313ef46196c89926200cb764dc5324c401968c9b8a64988cf3918b714c9310065bb20e29926200cb4641c5324c4fb938e7b2282988cb2719373505311954f436c918a627d8bc86dd1604c40117d0fb22c0988030fdd764581310061e3aec8b026200cac72d91604c40117d0e322c0988030fdd464581310061e3a8c8b026200cac72191604c40195ec9b92c0988032b19372581310047dc3ac03026209a5e83dd1650c4594bb07ba2ca188030fdd274594315bf0e21ce8b2862b6a5f835d1650c4134b906ba2ca18ab78710d74594315ad3bc0ae8b286200a74815d1650c4134bd09a1aca1882787a1343594310052ec1686b286209a5e839c9650c50f4bb07392ca188031bdca72594315a53bc0ae4b286200a74815c9650c40147d08392ca188028f610725943104d2f418e4b28622ca5d831c9650c4134b907a12ca1880387d0f425943104d2f41c84b286200a5d83909650c541c3887212ca188021fa1c42594310043ec3884b286209a5e83109650c4014bb06212ca18a7b8710c425943142d2ec1ce2b286289e1c43105650c4590fd0f90aca188021f61f21594310051f42642b286200a3d84c85650c4134bd0790aca188029760f215943104
  | 15 => 0x4286c6a0802b5a0450d8d410056ac08a1b1a82008de8708363504011bb0e106c6a080297a1420d8d410052ec2841b1a8232a9e84083635040153b08106c6a0802b5a0420d8d410056ac0841b1a827dc3f645d463504138b8c6ba8c6a080237e1d6318d410062f3b4ea31a8200c5e765d463504011bb0f328c6a0802b3a0a6518d4100566c14ca31a82008df8759463505795af02b28c6a080297a166218d410052ec2cc431a8200e4f5294863504131bd0e290c6a08023761c5218d4115d4f420a431a8200a9d8414863504131bd0fa88c6a08023761f5118d4115d4f426a231a8200a9d84d44635040159d05a88c6a0802b360b5118d410054fc22a231a822ba9c8454463504131bd0f908c6a08023761f2118d410052f42e4231a8200a5d85c84635045753d09908c6a0802a76132118d415df4a20e4231a82bae9441084635045753d09280c6a0802a76125018d410056b40ca031a8200ad58194063504131bd0e280c6a08023761c5018d4115d4f420a031a8200a9d84140635040159d04280c6a0802b36085018d410056b408a031a8200ad58114063504131bd0e100c6a08023761c2018d410052f4284031a8200a5d85080635045753d08100c6a0802a76102018d410056b4084031a8200ad58108063504071df0ea96c4a080237a1f63589410046f438c6b1282b9cd77118d62504031b906bb664a0a832718f744c94100c6f43ec69928232c9c74d8d325040359d05b1a64a080a3da1b714c9414c66a31ee29928200cd7631c5325052f9a8c638a64a09f787a1463905413ef0ec28c720a8289c9e7118e4150457d2ce231c82a080a2f21970905410064e31ae120a8255cb8605c241504ab93ec939cc0a093b355c463981410046f43ec6b028200c5f75d8d60504018b8ebb1ac0a0803331cb63581410046f438c6b028200c5f7518d60504018b8ea31ac0a0803331c8635814100667b1ee4b028200ccc63dc960504011f70eb00c0a08262f21d545933101c3f42ee0b26620087d85dc164cc4131d90ea92c5988062f21d6450b3104c7643ac4a166209c9c7359141cc5719aae738ec9188021fe1570d923101c3e42ae1b2462038bc87551648c40196ac838a8718a276510c7150e3100c5f43ec8a14623299c845db328c4651bf0eb2665188ca6721171cca3115673310e2994623299e87dd1328c48393eedba26518907a398b744ca314ee4fbb0e8994629de8e621d1328c4031bd0fb226518806b3a0b644ca311964e3a2c89946201ace82591328c401d1c84b226518806b3e19624ca3104ce643a849946200acf86509328c401d1ec8a1265188cfb198b714ca311566bbb0e29946200d94741c5328c455d8cc438a651896637a1e535823101e2e3aca6b046203c5c7554d608c4b31bd0f992c11880317dd732582310062fbaa64b0462008f
  | 16 => 0x1853200573c12e030a6400a76851c0614c8014eb0a380c299002ada1070185320055ac20e030a642aad5831c0614c92f5cb04380c29925eb5a0f50185320056ac1ea030a6400e5553940614c8011ed0e280c2990023d61c50185320055b420a030a6400ab584140614c92f5ad06280c299002b560c50185320072aa98a030a642aae682140614c8015cb04280c2990029da1740185320053ac2e8030a6497ad683d00614c8015ab07a00c2990aab9a0b401853200572c168030a64008f687100614c8011eb0e200c29900f179d553d81320145f424e3b0264008bd849c7604c8018f2eba86c099002b660f50d81320056cc18a1b026400e5953143604c8015d304286c0990032dd9271981320065a324e33026400cb7645c6604c801968c8b8cc0990032d9d361981320065aba6c33026400cb674186604c80196ae830cc0991062f21b74581320045f43ec8b026400c3f75d91604c801878ebb22c0990022fa1c64581320061fba8c8b026400c3c75191604c97b93ee6322c0990032dd9371581320065a326e2b026400cb7641c5604c801968c838ac0990023da1f61581320063bbaec2b026400c7475d85604c80196ee9b0ac0990032d1d361581320047b438c2b026400c7775185604c8018e8ea30ac0990032ddd061581320065a3a0c2b026471cd773185604c8011f70eb00c0990029e215601813201c6e43aa6b1c8209c5e635d463904fba3886ba8c72080237e1d6318e410062ebaac631c823299f8758e439051317f0cb8c8720a762f21d6350a411345ec36e2a1482018dc835db329040193eed21a652080a6b21d424ca410147ac30e2994820387e87dd5609040187887baac1208030fd0b755824101e1e3aaa8b048200c9c43dcd609040187eeb21ac1208030fdd542582410047dc3ac03048200c5d75d4f635040153b09a9ec6a080e37e1d53d8d410052f42865b1a8200a5d850cb635040153b08196c6a08021fe1570d8d4101c3e42ae1b1a8200ace82997635040159b0532ec6a080297a1662d8d410052ec2cc5b1a8200c5d751d7635046553d083aec6a0802a761075d8d410054ec26e5b1a8232ad581dcb63504014bd0b396c6a08029761672d8d411954f424e5b1a8200a9d849cb635040199ee5396c6a080393d4a52d8d410046f438a5b1a82008dd8714b635046553d08296c6a0802a761052d8d411946f43ea3b1a82008dd87d47635046553d09a8ec6a0802a761351d8d4100567416a3b1a8200acd82d476350401caea328ec6a08ca37a1f21d8d410046ec3e43b1a8200a5e85c8763504014bb0b90ec6a08caa7a1321d8d410054ec2643b1a8200a5f855c363504014b90ab86c6a0802a761070d8d411956ac08e1b1a82008de8714363504011bb0e286c6a08caa7a1050d8d410054ec20a1b1a8200ace82143635040159b0
  | 17 => 0xa6498ae5821d7614c8675ab07ba6c2990029da1474d85320053ac28e9b0a6498ad6831d3614c8675ab063a6c2990ceb9a0874d85324c572c10e9b0a6498ad683d53614c8015ab07aa6c2990038dd5254d85320055b426a7b0a6400ab584d4f614c931caca7a9ec2990029da1770d85320053ac2ee1b0a6400ab684dc3614c80156b09b86c2990ceb560f70d85324c572c16e1b0a6400ab6849c3614c80156b09386c2990ceb560c70d85320047b438a1b0a64008f587143614c80156d08286c299002ad61050d85324c56b418a1b0a6400ad583143614c8675cd04286c299002b960850d85320053b42e81b0a6400a7585d03614c8011ed0e206c2990023d61c40d85320065b3a6c330a6400cb574d86614c80117d0fb22c2990022fa1c645853262e4fb98c8b0a64008f787584614c80156f08b08c299002ad211611853201e2f3aaa630a6400ab684d44614c80156b09a88c299002b560f51185320072aa9ea230a6400ae582d44614c8071eb0f288c29900f1d9d651185320072aa9aa230a6400ad583144614c8010ff0ab80c29900e1f21570185320045fc22e030a64028bc845c0614c8011eb0f328c299002ada1265185320055ac24ca30a64bfad583994614c8011ef0eb28c299002ade1165185320055a422ca30a6400af380594614c8015e100b28c2993132d9db64185320047ac3cc830a64c1ab684990614c8011ef0eb20c2992fab5e0d64185320053b428c830a6400a7585190614c98756d0c320c29930b2d9d864185320071b428c830a6400e3585190614c967d2b06320c2992cfa5dcc641853259f53410c830a6400ea582190614c967d2c64320c2992cfa50c864185320074bb24a630a6400e946494c614c8555a90ca98c29900395d9553185320074bb22a630a6400e946454c614c9835ad0d218c299003a51924318532607c32148630a642aad48650c614c801d28c8a18c29925eb92194218532007c2a1a8430a6400c77759d4614c80156d093a8c299002ad61275185324bd6b41cea30a64bfad5839d4614c8555cd053a8c299002b960a75185324bd6b418ea30a642aad5831d4614c97d5af06ba0c2990029da1474185320053ac28e830a6497ad6831d0614c8555ab063a0c2990aab9a0874185324bd72c10e830a6400af2801d0614c8015e3003a0c29925eb5a0f54185320056ac1ea830a6400e3754950614c92f5ad062a0c299002b560c541853215573410a830a6400ae582150614c80156d09a98c299002ad61353185324bf2b29ea630a642aae682d4c614c8015cb05a98c29925f95e1553185320072b3aaa630a6400e557554c614c801caea8a98c29900395551531853258f2ba92a630a64b1e555254c614c92fd2886a18c2990029de1570185320053a42ae030a6400ab7845c0614c80156908b80c2991c6b5e0d7
  | 18 => 0x80787ceaaa6c0a10023de0573d81420047a40ae7b0284008fb8758060508070fd0bb82c9990021f6177059332004aec2ee0a1e640087f855c261cc8070f90ab84c3990022fe1175587320145e422eab0e64018dc835d561cc80517d0fba2c3991f7271cf745873244e4e398e8b0e6400c3d75d53644c80153b07aa6c89900e2fe1d54d91320043fc2ae1b22640387c855c3644c80156d0332ec899002ad60665d91320055bc0acbb226400ab481597644c80157700b2ec899002ae20165d913220d4e432a7b2264aac9e7654f644c80187aea3aec899282a7a0c75d913220d4ec18ebb2264418be87d4f644c80117b0fa9ec8992838794f53d913220d4ec1ee3b2264008be87d47644c80117b0fa8ec899282a7a0f51d91320054ec1ea3b226441aae82d47644c80155b05a8ec899002ada0670d91320055ac0ce1b226400a3f855c3644c8014790ab86c899106a760c70d91320045f438a1b2264008bd87143644c94153d06286c899002a760c50d913220d57410a1b226400aad82143644c80156d02286c899002ad60450d91320065a326e2b226400cb4641c5644c80117f08baac8990023de0575591320047a40aeab2264008fb805d5644c8091f100baac8990032ddd371591320065bba0e2b226400cd7731c5644c80117b0f328c89931ea760e65191320055b40cca3226400ab581994644c80117f0eb28c899002ade0565191320055a40aca3226400abb80594644c80157100b28c89927aa7a0c65191324ed4e432a63226400e1f6554c644c865938c938c869900673a0a7190d3200ce6412e121a6441cac72d91434c883938edb228699002576177050d32506563b6c8a126400b4d851cd424c93bb1ee839a84990066b21d435093204e563b286a126409d8c7350d424c8037190ea1a84990276321d435093200dc743286a126401b8c8650d424c805d190ca1a849900ba3dd9435093204ec73b286a126409d8c7650d424c805d18eca1a849931ae3e154350932635c6c2a86a126400b8c8150d424c80171f00a1a84990063760f75d85320063abaea3b0a6400ab684d47614c80156b09a8ec299002b560f51d853200572c16a3b0a64038f787547614c80156d0932ec299002ad61265d85320055bc22cbb0a6400ab484597614c8015e700b2ec299002bc20165d85326274ab9ec9b0a6400a7685193614c8014eb0a326c2990038da1464d85320071ac28c9b0a64c2e9583193614c985d2ae6326c29930ba9a0864d853200752c10c9b0a6400e946494f614c8675a90ca9ec299003a519153d85320074a32487b0a64c4f864290f614c8675a90ca1ec299262b921942d8532007c2a1a85b0a6498ad683dd7614c8675ab07baec2990031d5d475d85320055b420ebb0a6400ab5841d7614c9315ad063aec2990ceb560c75d853219d73410ebb
  | 19 => 0x600000080180000010018010002000000002c006001000002000000a0048000006001002800400600000180200020000010004008005001000c00200000100080140010010014004005000800800000200a80000060030020010006008000800000000700100040060050018008002006001000401a001009000c0000050008000002001000800000a00500200000000000008004000004000005000200a0088004006000000000800200e0000004002000000803000000e00500180180000010024000000000000004600c002800001c0070000018006001004800c014007002800000402c00000340060020068000002003000000000000300480000040000008000000002000001400a0000018008006001001004c02000400000040020010008000012001000002c000002000000400a001001000400400300b80080020000000000000001000002c0020040010054002004001006400a0000030004006000003803c0060000010000008007002801000200600300180000000010014000009006800c01e0050000000006002000805c00400000500000000020000000002015001000c0000120010008000000001000000200000100000000030060000006005000000800a002000005400c00100000080000010080008000000000801402a006000000800e0050030028008000000800800c014001000c002000001000c00c000001800800a000002800400000000000200000000000000014000002802400200c0000000002003000000800200000c800000a0010008004000000001002000000000000080000070000008016000000000006e00600100000160000008004000001004803c002001004001000e0020008028006002000802400a0040000004000000008800c0000010000000002006004800000400000200040060000038004000004000000400400c000800c000000005800002a001000000800000a006000c0060060008000000000001800400000cb441dc56290c010ff0ab84c32180e1f215709864301e1e3aaa8b048600c7575d476150c0156b09a8ec2a1802b560f51d854300573416a3b0a8600a7685c876150c011ef0eb08c2a1b22b5e0d61185430055ac26a230a8600ad583d446150c015cd05a88c2a18029da1721185430055ac264230a8600ad583c846150c0156b08108c2a1802b560c211854301c3fc3aebb028600c3e435d76050c0187886baec0a18030fd0975d81430047dc3ac030286038df8754f63508010ff0ab86c6a100e1f21570d8d420046fc3ac631a84a0a9f8458c63508015a902b18c6a10024f6177050d4200c5ec26ebb0a84038f78754761508011ef0eb08c2a1002b520d611854201c7ac3ca230a8403c767594461508010ff0ab80c2a100e1f21570185420046fc1ae030a84098dc835c0615
  | 20 => 0x63b200000000003a619d400038b000000000029446e8000000000000000050a000000282d1009eb3c800011680000000bd42280a028d0aa80b800000020646240ba437000043040e46486640000000001b580005c016a07cc000000235800000000046d0000a3e00019f8d289ae34700000003fe52e00029c001238f220a4d0ff45ba35116c80000004b680000000ea0801558d74a3535f00009463ef0000000fa8928082800052074100000001a06ae415a038c847f8000218c7cc000038a3cd01a6eb1888000b460180000a4c7b297e0000b3405069b3bc130d1847674c61a5927a56929c800078e0000000000000891000201c0004430eb997c0000001e48ec8000a26000139815e81a1a19820000000000264800000000000014d40fa4c70b380007fb03b000000200200200000000000014004000000007000a000000002c00200100680040040040028014000003000800000200200f001c00200000000100000040008008002000001000c000001000000404c002000000000000100000000000000030000008005004801c008000002000000000200080100000000040038000000000806800200001a0000000007001800c00000d000800800000700000000000010030020006000001000c0180030000000000001000000000000100080240040010000004004018000000800200400180000000020008030004001001000c0000000060020000003000805000600800300000060120028000006000000800000c0050000008008001000000400000300080100000000040004006006000000002200301000000000000000000004004000000000600f004002c000009001800000c00000000080080060010064000001001001001400000800000060000000004008004001801c01800100000000000060000008000003000000000600400080000000000018014002000001000c0000150008020000007000800000e00000000000060020000000046022000804800c000000800000200800180000000000010000004001000001c008004000800400200200000080080020008004002003003000c016000007000c008000000000800000b00000140040020020000002009003000400a001000000000c00e00080140000010028000002000002800000000500000180000080008004008000007805c002003003000000a001000000c002002001000000c002002001800400b000003400200000e80000000000040038000005001000800c0140028004004004000000400000c000800000e00100100040040000000010000000002000000a0000028018000002000800800000000100040080000010000016015003800000800500000000000020028000002002000000000000200000000020030000000000000000000401e00100080000
  | 21 => 0xd8cb4c40d53282cc00000000016a000000000000000000000000000dda0003499b7cb6017f00008dc9b0000000000032449d00013f94e812e17d8aa46d000000000000000002ea00000e600012780000329710000e881da17d3f898fcbb886124d8e090365012aa0000000000000000000000010080006263bb0002354000000000000069a8c637d9228d3c0000000000e146b223229411865753299ca0dfe5d21b319ed13813a076285ca7e00000000007523760d216f08c40df1170e9923a03739496c53900000002300bf492737c835c000000185000123c20600027500000002e505c906a885000022547800000005180005410001184c888140000000000000000000008c000098016105e0a71418dcc00000012fa16c18e00000011bc00060000012000001861c400003e2000000000000000000000000005bd4bf8000c5a89f10a8b791060000000000fec411207911086230e000000026a0000001b9917295427025c000000045d9c3480c00005f8001148000099800006488907f13a49b60982ae00003d60003a69bcd3b4912000198c0000004ba01581bc3f80000fec00000000028ac00000000023c44f80002eb8000e0071143d000092e00000000000002a6183000000032200000000002b24a89c1000000008b167000000000000006b203e35a800024284e0da154114c02c0000e8d1a099738400002c46ee295860cc7a26b10508d0ed886c0000000cf00001991bf40005424e71ec0c3a9f800026dd3805640000894d820da47400f400000000028c07f20002000000c2a67e4130a90000000000000000000005b008400043f000008c15c8580002950c0a31753680008a800000025dc0008450fc02385be0004c41a940003f100002f800000000022740002404cc12410140693dd000000022d43b8000bf66da296a1cc0009ef14d2628fea94d36b996000025300013409f65853708000ffa00000000000000412eb0001164414000000000000035a0ed800000005a800000000033428dd1f0000000000103044d3600000f249db00029091f29cf3f183a088400013995540007b91b38924a3a2112fb14d09ba18f4180d70c304d44021c64f4800000015c80007b100000012587991788ad000038430518d119873d488000044c0000001bbc00092946296606c215e4cf0f58f3645c3d08b2d0b27d71a90bb849058c42a1ee136864a07a1b8c00010310380000bc05f00026753881ac0720df424e8bf367a8ecdc4721219000148c00000024ad32688b39290c01baa0f48a92d00000000000000f0c0003e000000001d03bf124cde20000000000000000277811c1c60001bf00000000004c220908fe3ea1baa6c4c401af1619e7494e8532fb80000000001b2944c0004e500000013a400007e97b400002d157a128d7000015c92a40000
  | 22 => 0x10d000051a304323000138250f000239000000003f800000000000000008663d500018480000003efa9680a63c31221ad910800016b000000000000010040000000002258edc3d852ca04033e29102aa08cdd2230182810105c8ed47d9a0c92c532084a7a0be042900003d40002801cb0000ce05c100001b80000003241ab00006904b998404e44520001dd000000041126e8d9200000028d00007ac0001ea800059704395e0f820004f28000cb24ab024871400063200015acf1c0000000af00001cd13d09f42767984aa8ef4b90a3a303243d36045945695107be8f600000013e000030f80003144fa06d9add2ae7c307d890d1528a50000000e9021d3e606090709d005606f093800027f800011893c1f498e49584ae0fe0a2d2f600f000000000086916b80000e80000000001092000000000000090603300006e800025b9498a2e0001ab09740000000668000000000382800000000046c80013963501b600000002e218417c90aca2213a958000003900001c80007b60d000006d291c0cb800116200009f96dc2e654d17d00bc98468b0001f6c0006ec3e5000000000000000007b40000000000508000000000093000000023bd37600000000012ce94917025800005280001a4800062b00014c4e4400000008780003f019780013000002a280000000002ac800000000013680000009e90000308000a5145994bc0004783d4a3d000000000007d8ca80001b58000d9a00034e00013dc8d800000000007a00001cf04504880000000a8e000000000000057c00006e80001383c08e1c6f263100000008e27870002464000000000000000000002b8c6d0d60000000000f9a00012d91742a84c940a892d0b8a0900000004620003968000000a1a0000000f4c63318e87f80000000530000db600036c9e680004f72a900003940000260000d1000026f0001406614000242cfac00000025a000041d0000b18cc08373ca80000008d2000189c0007e700028f4000000000243934000014f088c0741580000b2453e41f356800117499104d8bd8fc06b34ee9cd400032731700000000002bf16d04280000001588000a2753aa2d4da479600021e407e63048500000000000d89680d3e00000000000de00033e027c2141cf09e8e7078243c37411b000000000000011c20001a2902400000029e958c000000000000000092e2a7800000000029380008169c300004ac0004d240422f476017a46e00000003ad2090b2888c74f43a80000000000000000634a012ca0cecafe96e0b7228000000033b87694407c400028c41b294a3a0062422246533593d90fe2422be95e824401e0000aac1727e64760000ac24a6447879c0002810000000ef495621b995434c66d130953036407713b8ac0d6243d000000000035e0000001086000000160936c2000000
  | 23 => 0x81f89d89ea00d899c00075339f0004dba000000000000011700000000000002160000000000000000031899a00000011f87bc508a54000083f0000fa05b403417f286d0b466911b0500f3800046b0000000000000052879a75a4ca8af80000002b2970ccb8812000000000000053000000880001538ae8ea290d3f290a80002d821790608061a345c000105a0001da80002c629b48b800000000000025f40001fd3e4000144884c00025a81e09bd09882500000001288000000a1544d00013a600037c1a2434270651c911c9f84c650008ec6581c91f99da889c53e4d213313e66aa1f087000007d13378344a7673b0bc800081008148097ac7c40b04b1960400039700000004426a00b6952418212840294890ae33e3f58000e0e0c5000085d372000000000000024c0c21d5400000036a8d5000072b28b000000008843da1f00000000000f2c96ca13210000000000000022bc0009364f227ed2446bb2710d751caa1e24d174c2b63b421c25b00c4002000000000000000000000008ff0000000150a554bc962800084f1cc00006de40500000011cc000246a998b060000001cc50ba00000015a00004251239c813ac6d1000000000018800000012a40000f8000000000000019246700000000000ce4000156044cc5e35a000082c0005e04490000ed200000000000000000000264ec00004ad86600000000001ac0000000000000000089734c00013fa4893c6000000000000000000007e400000001c2640401030c56e8ac20200008e400034d0000bf21610001d8c5ba3264541a8c00000000005980000000000000ef200000000000004700001b0812a3d70001ce884c000465800048c1230000044b9e78a0000ce836c000000000078c00000024501960000b880001a4000000000145839400000000000004c10000b5213201005d4f4637b522001ce3600000000000000000000000bc40004461c38ae261a00010280a00002ed94251c6a4b166061ceec0350000a600000000000b200002e1000000000011a33b0c54000000000000000034002280005fe4a800000000007091571d7864600008900000006cb4ae80000009b817b99e4000932106059c78a1d12c00000000000000000000057700020d00000001cf8e80a527472c900000001042c6a190000000271800107453624a000000011e2ac1e107a000013d80004a480b1b880006be0000001c2cdf881e000299c00070c000000000000025d905d4ac000000000000064100000013ce0ef00000009080000000000a20a6201386684a04530d8156929008527a14193da00048c0b70bc60002e600000000000000000fdaa190000000000000000000000068713200008da97c0000e6c0000c828380c426ca6400004207e88a31be207c0006f0388000103800000000004f093833f8000000
  | 24 => 0xc7c94ef2938a9646e0001d8400000049a800000038c1dc237cbca18526c89b8d725bf0551d24ed60000000e3400015c2b700000009ac1ff800000000000000000000001a4a7d00002ad2a725bc2825e900016d4f1aa5f26d11d09d000020812d42f07930bb0000a58000000180c0007d52868a8459e00d4e68961000a044928000000a14048000000000008ea400f9c5114b90000eb853a0339fdd4b813c00000000000001df000000000000023880006d0000239d1d626f5031610904931000176122c9860000838b32000162123d276000000253c06c0002d9a0a14ec11942882000000001d5000000000000000008369ae00000000000001a726d4000054000200c0000000000000f3e44f4ca0000dc836d4c817f42aa3e512f0ec48049e02ba23e80000001a99a308ae0080e30eb93507502c4971c92214c2a40e481e208d3468639274553000000075e24d3c425d4c2ea100051264b3a6111e88388bd807d1df9a9c3283e70000000b920000000000000000451150c000699032916c46a14811d27d93ee00000021040005dd16c927926600025f0000b960004af0c614ae0000f710904c46ce0000db86200000000000000000233800000012022d000043e00051406e14c288a00220c4c4420f00019b8a4200013a0c3c7b610c0d104f85187ab440800000069505d8a700000000b50000000000211800000000000000000000003e382a40002555038fb52062891aa80000007a7484000126e00034217fc98e9d74f6000000000018e000067861931500000443300000bc90be8170f0989833678900026bcb0c38300009fc00000025c9d5863e98f000182c00047b0000000000000000000000045507e0a641807a2000000000050e000000000064d1d3891516c0002cf03980006c522f8a584a80004220e2800000021ca6fcb366383618f502483b900008350ca8de00005bc0008ae000193c6f40004a728840003cc0001798000000000005c00000033616910661f21bc08e07dc1f5000000000000000000009aa00013f0000a4a7ea3141fa138e95300025945b65d54ee03504069a12f21ffc00083e26785b0000143000217800000000005a41706561fe98040003161a8800141400031f01685e80002039448000a3f48283a413c41e01226889ac463275000000012c2e69f689740000ba145537c3c211c8c045e07d30002518cba0000b4191cf8482c000052d49e61e460928400094c1958000e721e538a8c2c0000001d982743160000001b1c00005d0001948000000119000098a487340800000059a04202c8000331000000023600038d0d2ca165df000000000000007299389b818000000003220000a200000c00000000000000a533dd80014520000000000000000000000000033617c865800000000000000000c900021d8ecc8621ad
  | 25 => 0xb97112882081c48000fba1d50000000a940003a700011d21524b3000022a3ac25ea4c00009c50d593114a45a12600000c4a0000000000eca3ca04326240000000000000000595030800000015d3e307811c04b32461eb400036000018f01b026a00000004668db00000008ec2924d1a5840001e9000000019c00000000000007730be00c0390260112000073c0004651ca821e8930002140b5a5b90000ca807822a00000003b20424a3800000054000000000000004e4800111a64c1500000000000000000000000000000000000004668000e7e0000b800013b28b000004dc0009874951f782920002f40000b2637036603cc7c800000027c454400008302b400063532f000000058e00000000004a500002f4d7e68515182942160003be0000fa086a0870000c04a1800019440000000f78000000a0d0000000000000430134cc388f2000000000000023d0bcc0000001fb074c00022f0000514d3a3a400008f074a48e0808840fd25da00000000000000001a842b43993038001384969000248518800c32b8e0497843552f00003c80003c00000000000000000000080c18011f8d1c00000024447902653c893f4d942c000016881aa1db0f115d819e97615985644088d3316000035a0000000000000181143231ce486820000c640009433e91a982521d41411b507d69e24849efc0000000001c0800098d15c1e2c000a4d0000000e703950000000d7a7b72b780010cc9aa23e24809163240000330618479000000143a50824a877476e0000000000d220000000000dbc000000119800000012b00000004b800006dcb1631e2d79288c129fe0000000000000000000130a8be0000f385c675d00000000000000000670000000000267c0000004a00000fe68160000af46686c800017f88564132bc800067a44b4fd00010120001928a380009a521da6040000000028bf45a60000000000094a4749c80013940003d280000005f326f979c82c0000de89c11ea797000140c0008200000c8549800014400000002f8491984c13400000000009ea0001b200000001c12e8800c00000051500014105050f306a868c4454149c0cc7400025814dce8480601980003f49d500000000007162860aa0dca662000250538c898031828c0001a800026ac684427000028400066600016940000960001df400014e4f300000ea2e8519a4b44ec00000015788d251423aa8711428720001cdccb4000000000000000000013c80006f610d9aa4c420002b80000ede839501023c5c804f38e80000007f900000007a60103d9a858ada6e000023382fc69741e9db41683fe295014539802500002c53661a7000000000000029e027116e73038f81e0c1e9ff183a3dcb0e9593a590640007ae4410000000a253280e190420003b905ecd5e07b2500a5cdfc00006223201e
  | 26 => 0xb255b20a8a949060700f5084c0d05910459984fb28fd1e91f8895474344396b0b7c2c208117388345fc53913843ac23f2ae8d2044e03805ba33c71c4c10a10b1c78019500027c8fe80e00839c5d1fc66443f196c72200000000011d400018a1e3d34e5240098000de434f03608aced08550d711a087446a0e188802be58f0000f808183392dda4bd2f41cb05e0a750ce5a70a796400000001ef29c40767593bf93c03984ca120800000000009500000005ae1c290b54b02c50258ca143e5de502a6a47f802b10e0000000a2e00000a800045e3388000c485c600000000007bd00017e0ae60922241b194d80001761aa13be86d290000000000037a0070e5c1c700000014904a4000000097e0000000000f5063b00000008801533ada7d449c8aa0001d29110836077000000025c0fc9fc000000027c000089812600026c8000a6b3879b9c2c899c41280b8e4c6a441e139000056653181ac00068a131854451e96b03e025c31a1d20c98000ace00000000000b201f000000000000035588480c87823cf0ee8fb04b13e7873828e00000028c800000000000000000000b2800000029539186ec8ac5c50002408abe4ce0dc80011369d143a108445816b347816c00071800000000000000cf266ce3800006b1cc8df44cb4d3000040a97833e9334a040000001d6000093e00000000007440000000ffc00005580000000000000000000827000000000088e525002c00047d51f08a41e40003a2810ce6c5b64201124af6000000000108e00000003fc00000000000000000004930f70fc20002f780000000000fa29153c6000000000061a01400000009a20000000000000a5d421000092411c2f0a430ff82eb24298d80000003699fb024a0000000000ea801600000000007dc0000000e5e0000000aec2300001b103ac56a5aa259204cebe6745248b9c66e88602404b43f684d1f90ba4c4600043780000240000001e500000000001bd4000000000000060600019680000003e3000203c00000034311dc0002e5306a044582a0c0df10a0000000000000000021928010d80009071fba6580004863351c4d48651c00009c409a24a2851e149f20792f71cd090230206e190c0000001e2020c00087111e80000a40003a30000384868000296c0000c648d80011282022e800004cca6f00000004d20000001cb04b267a00010d12c887d13c80000000001c00054be83a14a58000c5200000006a4000551393986c0004e7184800057e00000013c40004ee2fa8000c6e0000000000126000176a120c8a216000260d13200045580740000000000000444377000000000000016823b80006670f61fb8a080000ab1fc8000000065064075000035e0000000268048907085c0000868a280da08a28ca58800089000000005aa5ab2579c78000a691fd0290ee00291a
  | 27 => 0xee0000f7c37f3d7951856c01a2cf800000000000000000000000000000000878190262c0000002dc256128400e4ae18380000004380f3c65200000000006980000000d1145a77539988f90021b50ce9ed00001b33b1246800016052000001440000fb80003be59636e20ec0005c22f894d47340000001d4903a4223c194cc000000000000000000014380003d0999000000000000000000006661bf44a9d5d22684b37b8dc800085229c000093e3ab1faa9b923e0003e2847c66aa361ac076041284648204e4778a0e00000000000e733281a8000000000000026800000001381a600000029cd1a800017793ac00051b00019ccf6456a22806954240000000000000000000000113c0000bba29c6d460404100000007cb46880001f26d800000004ae0000ef28bc0000000000000c1845100020a80006944fe04bc00000041900000004f300000003da0000000000e0234100022f000026c4fc80000007ef534000000000025683e029a0000000000d004c847809680002fc30b00000004ed239a35d27e0000000000ef60000131160000530362000000000038a276000000000000000009e1000078cb100000000e4c000a4100000007200001751ed4a46924000256800071237525140009ad4af94608c039d1eea8e00007710ab91293783ec2b617a82a02d1169044087c51e3bb8ac40f41c43258b9944655707b8cb8b
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x64f37001400000000361ab112a6618d9d60390a32cd451f20d09014c54c290e01000640ca1c180001748bc0381e000085ac402800457044a0000026241004e6958b0100181010204b0f0000018041858008040142d9210d75d8143004c36578050d424c801a258560864d8532616a160d82193614c801a158454f51185320069154d82d44614c801a2585608641853259ea160d82190614c8016159519243185324bea121943508614c801615949d553185320059164a7554c614c8018558754c50185320068561153140614c801a455360850185320069254d82143604c80142d9210f75582410052364843dcd609040188d84dca72d8d4100ca3a6364509328c567c86621d0714ca310068510c815d1650c40181c4361c42594310048725183085650c40181c4361f40594310048725183c81650c54141e97d0d655083100607a6074595320c40181d981d1654c8314f70364874595320c401c0c74909654c8314f607a1d65dd1320c401c1471594744c83104e1321d65509320c401c15651d3714c83100705594741c532cc00188d835c8725923000ca326164509324c00348c97591424c93059f21188741c5324c00105d98194735052000564643641cd41c4001914845d5320c7100058524d71194644400168493604641891000721104621cd4144001c84641cc625051064d3125c63189414414fcc27018c62cc5100050d65c65190314400145597197630c5100051965c651883144001c2575190620c510007115d4631883144001854865d5320c51000645211754c8314400188d736087359010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x20001a000540b4421902ba2ca1880280da210d87109650c401406d1086c3e80b286200c03649981d1654c831
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x138e
  | 9 => 0x4
  | 10 => 0x94b
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124d
  | 15 => 0x124e
  | 16 => 0x138b
  | 17 => 0x138d
  | 18 => 0x98d
  | 19 => 0x98e
  | 20 => 0x128d
  | 21 => 0x128e
  | 22 => 0xcb
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x9cb
  | 26 => 0x9cd
  | 27 => 0x9ce
  | 28 => 0x12cb
  | 29 => 0x12cd
  | 30 => 0x12ce
  | 31 => 0x168b
  | 32 => 0x168d
  | 33 => 0x168e
  | 34 => 0xa0b
  | 35 => 0xa0e
  | 36 => 0x130b
  | 37 => 0x130e
  | 38 => 0xb0d
  | 39 => 0xb0e
  | 40 => 0x140d
  | 41 => 0x140e
  | 42 => 0x24b
  | 43 => 0x24d
  | 44 => 0x24e
  | 45 => 0x144e
  | 46 => 0xb4b
  | 47 => 0xb4d
  | 48 => 0xb4e
  | 49 => 0x144b
  | 50 => 0x144d
  | 51 => 0x16cb
  | 52 => 0x16cd
  | 53 => 0x16ce
  | 54 => 0xb8b
  | 55 => 0xb8e
  | 56 => 0x148b
  | 57 => 0x148e
  | 58 => 0xccd
  | 59 => 0xcce
  | 60 => 0x170d
  | 61 => 0x170e
  | 62 => 0xd0e
  | 63 => 0xe8b
  | 64 => 0xe8e
  | 65 => 0x178b
  | 66 => 0x178e
  | 67 => 0x95396
  | 68 => 0x94056
  | 69 => 0x138c
  | 70 => 0x138956
  | 71 => 0x94c
  | 72 => 0xb0956
  | 73 => 0x94b16
  | 74 => 0x1409
  | 75 => 0x140956
  | 76 => 0x95416
  | 77 => 0x249
  | 78 => 0x24955
  | 79 => 0x24956
  | 80 => 0x94256
  | 81 => 0x16c956
  | 82 => 0x956d6
  | 83 => 0xb8956
  | 84 => 0x94b96
  | 85 => 0x1489
  | 86 => 0x148956
  | 87 => 0x95496
  | 88 => 0x209
  | 89 => 0x1449
  | 90 => 0x289
  | 91 => 0x14c9
  | 92 => 0x138b16
  | 93 => 0x141396
  | 94 => 0x139416
  | 95 => 0x25395
  | 96 => 0x25396
  | 97 => 0x138256
  | 98 => 0x1396d6
  | 99 => 0x138b96
  | 100 => 0x149396
  | 101 => 0x139496
  | 102 => 0x180b
  | 103 => 0x1649
  | 104 => 0x134b
  | 105 => 0x14b
  | 106 => 0x141296
  | 107 => 0x1440d6
  | 108 => 0xcc9d6
  | 109 => 0x9ccd6
  | 110 => 0x1709d6
  | 111 => 0x9d716
  | 112 => 0xa0c
  | 113 => 0x252d3
  | 114 => 0x252d6
  | 115 => 0x1452d6
  | 116 => 0xcd696
  | 117 => 0x168cd6
  | 118 => 0xec9
  | 119 => 0xa0b96
  | 120 => 0xd0a16
  | 121 => 0xa0d16
  | 122 => 0x150d
  | 123 => 0x178a16
  | 124 => 0xa1796
  | 125 => 0x148c
  | 126 => 0x149316
  | 127 => 0x140b16
  | 128 => 0x28b
  | 129 => 0x184b
  | 130 => 0xb4255
  | 131 => 0xb4256
  | 132 => 0xb5456
  | 133 => 0x24b56
  | 134 => 0xcc256
  | 135 => 0x24cd6
  | 136 => 0x144b56
  | 137 => 0x28c
  | 138 => 0x16d456
  | 139 => 0x1456d6
  | 140 => 0xcd456
  | 141 => 0x144cd6
  | 142 => 0x171456
  | 143 => 0x145716
  | 144 => 0x148b96
  | 145 => 0x154d
  | 146 => 0xd1496
  | 147 => 0x148d16
  | 148 => 0x20d
  | 149 => 0x179496
  | 150 => 0x149796
  | 151 => 0x20c
  | 152 => 0x154c
  | 153 => 0xd0cd6
  | 154 => 0xcce96
  | 155 => 0x178cd6
  | 156 => 0xcd796
  | 157 => 0x58b
  | 158 => 0x40c
  | 159 => 0x18cb
  | 160 => 0x160c
  | 161 => 0x170e96
  | 162 => 0x3cd
  | 163 => 0xd0e96
  | 164 => 0x15cd
  | 165 => 0x180c
  | 166 => 0x94255
  | 167 => 0x24211
  | 168 => 0x28211
  | 169 => 0x2c9
  | 170 => 0xecd
  | 171 => 0x17cd
  | 172 => 0x15693
  | 173 => 0x104c
  | 174 => 0x240d3
  | 175 => 0x580d3
  | 176 => 0x1692d6
  | 177 => 0xec253
  | 178 => 0xb8293
  | 179 => 0x58253
  | 180 => 0x25556
  | 181 => 0x25856
  | 182 => 0x258d6
  | 183 => 0x194c
  | 184 => 0x24b55
  | 185 => 0x25555
  | 186 => 0x20255
  | 187 => 0x154255
  | 188 => 0x259d5
  | 189 => 0x592d3
  | 190 => 0x258d3
  | 191 => 0x24ed3
  | 192 => 0x178253
  | 193 => 0x24593
  | 194 => 0x596d3
  | 195 => 0x25793
  | 196 => 0x1796d3
  | 197 => 0x59453
  | 198 => 0xd0cce9e
  | 199 => 0x58ed3
  | 200 => 0x25455
  | 201 => 0x20251
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2156
  | 6 => 5618
  | 5 => 2679
  | 4 => 57
  | 3 => 4
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (88388+((h/718+packedAt gbK7 (79772+(h % 718)*12) 12) % 2588)*13) 13
  | 6 => packedAt gbK6 (295872+((h/1872+packedAt gbK6 (269664+(h % 1872)*14) 14) % 8972)*14) 14
  | 5 => packedAt gbK5 (169670+((h/893+packedAt gbK5 (158061+(h % 893)*13) 13) % 4277)*13) 13
  | 4 => packedAt gbK4 (4123+((h/19+packedAt gbK4 (3990+(h % 19)*7) 7) % 75)*7) 7
  | 3 => packedAt gbK3 (327+((h/1+packedAt gbK3 (324+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffc07ff807ff01ffc0fffffd13e78fb1e31ff
  | 1 => 0xf00ff81fff81ffe07ff07fc02ed9a765e3ce7c
  | 2 => 0xfffe00001ffffffff83fff0e1c78603ff8f
  | 3 => 0xffffffffe00007ffffc003f01f807fc0ff0
  | 4 => 0xfffffffffffff800000003ffe0007fff000
  | 5 => 0xfff0000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x50e400a5841251049400a64a800a08290e10b5
  | 1 => 0x6124580ab490b5242d106a818658a36162c65c
  | 2 => 0x20aad4008212a594aad013530a14586016b0a
  | 3 => 0x44b36735964020873ce50063b01f806b40de0
  | 4 => 0x488fc79c6e79cf9e008422183dfe0007dbb000
  | 5 => 0x8f02040070400c10030840203ff5f6d0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36741
namespace PEqualNP.Outside.L_meta_36741
open PEqualNP.Outside.L_meta_36741.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 24 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 4 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 4 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 57 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2656 : Interval gbAtlas 5 2656 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2679 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)))) (concat (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)))))) (concat (concat (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))) (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)))))))
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
theorem bgb_6_5600 : Interval gbAtlas 6 5600 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5618 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))) (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))))) (concat (concat (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))) (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784))))))) (concat (concat (concat (concat (concat (concat bgb_6_2816 bgb_6_2848) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)))) (concat (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488))))) (concat (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))) (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)))) (concat (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000))) (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)))))) (concat (concat (concat (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352))) (concat (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)))) (concat (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704))) (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896))))) (concat (concat (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056))) (concat (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)))) (concat (concat (concat bgb_6_5280 bgb_6_5312) (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408))) (concat (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504)) (concat bgb_6_5536 (concat bgb_6_5568 bgb_6_5600))))))))
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
theorem bgb_7_2144 : Interval gbAtlas 7 2144 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2156 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 bgb_7_1856))) (concat (concat (concat bgb_7_1888 bgb_7_1920) (concat bgb_7_1952 bgb_7_1984)) (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 (concat bgb_7_2112 bgb_7_2144)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0eeeaeaeaeee0e8a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372970 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36741.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,5]⟩,⟨.or,[3,4]⟩,⟨.or,[2,6]⟩,⟨.and,[0,1]⟩,⟨.or,[5,7]⟩,⟨.and,[1,10]⟩,⟨.or,[0,11]⟩,⟨.or,[4,9]⟩,⟨.and,[3,13]⟩,⟨.or,[8,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36741

open PEqualNP.Outside.L_meta_36741 in
theorem PEqualNP.Outside.L_meta_36741 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
