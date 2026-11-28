import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37161.Model
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


end PEqualNP.Outside.L_meta_37161.Model

namespace PEqualNP.Outside.L_meta_37161
open PEqualNP.Outside.L_meta_37161.Model
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

def SBf (j : Nat) : Nat := [6, 6, 6, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37161

namespace PEqualNP.Outside.L_meta_37161
open PEqualNP.Outside.L_meta_37161.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xc03000072c038d1060000853c004024a01020000009002bf43de43bd43dd439d43bf42bd42df32dd32be41bc41de31dc31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x5800a6102002403300e0408a000031c7552438fa92871c5150e38a0a1c754f428eaa6651d544ca3aa620c7d52318eaa0631d531023ea9184755030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x99000085185544ca18605513286983548c61661d5230
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
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 27)*6) 6
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 20)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffff81ffff83fc1fffc1fff83ffe07e79f3f3
  | 2 => 0xe07fffe07fffc1fe0fffe0fffc1fff819e7cfc
  | 3 => 0xff83ffff83fffffff03fff07ffe0ffffe78f1f
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x430888c51090504052cc09498129212c28b171
  | 2 => 0xc91111432122028a05552092a4124b049254b4
  | 3 => 0x42222080a442114a02252044a409451450a0a
  | 4 => 0x965bc4924876b5e7398318c7739c0619f80fc0
  | 5 => 0x1863871c738739f9ce3b9ce063181861ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37161
namespace PEqualNP.Outside.L_meta_37161
open PEqualNP.Outside.L_meta_37161.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x194041c0049400000000006222c200402be43bc43bf42bd42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x8004308e29a852d52d06b0a098cb54840
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s1K4 (212+((h/4+packedAt s1K4 (192+(h % 4)*5) 5) % 24)*5) 5
  | 3 => packedAt s1K3 (111+((h/1+packedAt s1K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffc0ffffc0ff07ffffc0ff83ffe07e7f33f3
  | 2 => 0xffffff07fffffff81f03fffffc1fffff91fc7f
  | 3 => 0xf81ffff81fff07ffe003ff07ffe1ff81e1cf9c
  | 4 => 0x1fffffe00007fffffc0007fffe0001fe0fe0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x90c44621448941016524c8498123212c2711b1
  | 2 => 0x21088812091082280a41119224144a50906446
  | 3 => 0x52551240d2284d52a0a26a44cb419505618a98
  | 4 => 0x659a249483b2969cd3c8308772980619da0f60
  | 5 => 0x861c38e71c3ce7e71cf3bce063111861fdf000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaf0a0faa0f0a0faaaf0a0faa0f0a0faaaf0a0faa0f0a0faaaf0a0faa0f0a0faaaf0a0faa0f0a0faaaf0a0faa0f0a0faaaf0a0faa0f0a0faaaf0a0faa0f0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37161
namespace PEqualNP.Outside.L_meta_37161
open PEqualNP.Outside.L_meta_37161.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xe0488a62200102c600280084c0be43bc43bf42bd42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1820208e29a852d52d06b0a098cb54840
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (212+((h/4+packedAt s2K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s2K3 (111+((h/1+packedAt s2K3 (108+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ffc0ffffc0ff07ffffc0ff83ffe07e7f33f3
  | 1 => 0xffffff07fffffff81f03fffffc1fffff91fc7f
  | 3 => 0xf81ffff81fff07ffe003ff07ffe1ff81e1cf9c
  | 4 => 0x1fffffe00007fffffc0007fffe0001fe0fe0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x90c44621448941016524c8498123212c2711b1
  | 1 => 0x21088812091082280a41119224144a50906446
  | 3 => 0x52551240d2284d52a0a26a44cb419505618a98
  | 4 => 0x659a249483b2969cd3c8308772980619da0f60
  | 5 => 0x861c38e71c3ce7e71cf3bce063111861fdf000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaacc88ee88cc88eeaacc88ee88cc88eeaacc88ee88cc88eeaacc88ee88cc88eeaacc88ee88cc88eeaacc88ee88cc88eeaacc88ee88cc88eeaacc88ee88cc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37161
namespace PEqualNP.Outside.L_meta_37161
open PEqualNP.Outside.L_meta_37161.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683be42d077885a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41efa9a835f53506f8a6a0f714d41ae29a83bf435077a86a0dfd4941be29283be425077884a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077c8620ef10c41bf290837d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f78cb31ee196637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31ef99463dd328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898f790d31eea1a637f524c6f8a498f78c931ee19263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c7be8618f710c31bf290637d520c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x14a293e4be06c3c8ab29867806a7b000000000000001bc59000000000a19ba0001c0000000fe1842b287000910918350983d8d29c53fe000001cf000000f80001d067095844326638ca17848256800000264478a49603488d0979463909d8250fe222000b91b84469d0b38be306328f423e1da49c9d28e2fe8954a90b3ae40481947000a34bb8f10540ccee80000001cae8571ac464851260005984c0c01d421d1e1211665d4b09523fc710b124922c5c4318504541b127a311680acfba100105602121118661c478ac064994c2a8f4861d45128512e1b4fc21e1c010c1600332a3bd229f60006193d0c132419907a401d66ed0b85d2a017c7d28440e000d49574081951e83803c780c212e2f21d8d713f3b03186aa6941a7048c1f900a8c0ed14d08084c102504243ec392673783408791d0d00014481344c9d52a00b52e7c8c88b12288bc001cb1347180a14b29e6bc2f2833fa1f4db8a547e608000e500000013a68000000699080000ec0020e0e80008380022e32cf9a94234930fa1004f2a65199df3dc58d2ba784ba26cf786914031ca12092a6324da955530a4d009db3ce9f0e907a3622552f11507c2247c88613a47c620c537c640239cd3165109d8480f6298ab26b250365001a70306d9268000004406100043a8880000000092c000000000001a09f0a2870cb0000a8970001974cc2b4f601538e0000022900038882030142160001890007887e8004940007a8003563780020851000040a0a000000b280e0400501400010060040c0000100800004000000002401000050140a0040400800044070400005815018010000b030010001a0200800000020200380101000020000000006c1700000000000044700c020000506c00020000040a07418018040180d00003000000000600c040000d0340a000120141202c0400000028020102200014000040ec03008350240601002028010480000020014050180100c0000c0a068050a03600009044000200e02012090350000b0580003c16000000000007c2807c0002c0002407014020382300825004040240100814000040000500c020000100c1e03c000140f0300701001084060b800090050143004400004020180500800000110180a00400000000000f01c0204c0000afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x5500e2803a4810521905447806e40c8e0898294c200000129000000bf0102ec4341283a48e9186e83c1144c448a1f4fa000b68000008b400000318470579fc52056d4304d07a00000031432000000000006c8cd9f5340098418bb330000000001182a4be0371100005403f2c8330d5174104000830003f6064d6a5939c5b115a481387705d2622d21e09e12a3d69a866a360420243e125148538aa2030d69b50a19f3e282c761e13da248142704c857d1ba282720003226e45c399408004e26d07386a04408c5ca0246a9093ba961a84b0b8136380000d19a80000000b8004423482a8774a2620f28f327019c9e9d611a2c0519810003700020c4fc8e45a8000002f46d00001ea004b19d05c010010b60967550c000022000001d34346fc050002240682e1ca0b6414900b70004d08da922b85bd1da1b1b62b80000008c634c7800000000d110e0005a9488f43662fce18fc1be0d8ec90c2900b4e49b00002e079016178664c512d2121ccdca5b3a88b09aa1519ea087b97b1ae1040027f2e6360000f84d8030000000007a40008400007000000000a29398000000482488b00c4c1271de4b01c4de8001c85f40012413c240e818014e980bd0990c0a300087e4c688022a5a474a2cb594134c7a9292160b43852a99a126090671331c60e5028940a6000e10004640000004f000000fd059244000001ac000000270003c6744a5000448000ac93711c5a07701d4e42000fa534ac791139cc1fe5b9378d13cc684178622bc2
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420d954621083655108420d9547200826f6548020b9185200836551480209ed95200825f63553109718d54c425e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c436452487109798f548425d63d52109798e548425d63952108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766588510d914a21442746548510d9149214436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597210436552c84109d59421043655208410d954b100427965840109dd9510042e46244010d9549100427b6544010
  | 1 => 0xc71c5450d31c7152324c65e650c931a7590324c71c540c931c7152314c63d6595031c718d540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c71d54cc83197d95320c69c644c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e2197d8d544865c63551219ed81544867860551219798c544865d63151218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f990504863d64141219798c504865d631412197d8d540865c63550219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948218f992510863d64944219798e510865d6394421b958a210866f65484219dd9521086e76548421d9d9521086e460484218fd91500863c645402197d8d500865c6354021d9485500871d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d029c6350740c754d41d031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e419029d6310640c794c419029d63d0240c794f409023e6510d409798c525025d63149408f997425029c63509409798c515025d63145408f997415029c6350540a798e405023f6550c4097d8d521025c63548408f596421029d631084097d8d511025c63544408f596411029d6310440a758f401023f65500409ed95401031c6355330c755343cc31d5410f30c755332cc29c644cb30c755132cc31d54cc730a719131cc31d544c730c758e548c31e5490e30c7951438c31e548ca30a7590328c31e540ca30c7952318c29d640c630c7950318c29d64cc230c7953308c25d63951309bd89544c26c62551309dd85544c274615513097997434c25e6510d30c7550434c23e64149308f590524c25e65cc930a7191324c23e64145308f590514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c3097d95430c31c5450c308fd91520c23c645483097596320c29d640c8308fd91510c23c645443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c823f6454f208f19153c823e6414f208f59053c823e64947208f59251c825e63947209758e51c825e63d52209758f548825e63952209758e548823e64d4e208f593538823e6494e208f592538823f64546208f19
  | 2 => 0xe000878e226c884000cc1fe4b40000011e000720001440009c09c19a0ac8893434627caf843072104f20002501e0de0000001acb80002447a4a10000005a800189000000000420000009e83b0000000000000029cc8800354000000aa2ec4c40221b398294000002804dc0000013c7dcac0ab3522084406a220000449cf2266fc921fa3264d4d42080002a40021600e0901600042a480e114300083cca0f70fc6f90d2040a2200cb14f3bc85c8a8d5162861050db2ee000028004265e4e21c10d0000c10e82da19d0280030c100d81ae04c020560180000002c1bb3085690f000380008030000600803000000040b008000000b0000e0041e0200f00000008010240104009040010180c0100500000000000180000400008020280003402000000040001c0401400000030000a02402000050200101c01000000000500007000040340700c0501405010100040501c00014040080800004000090400d00404040130740903400000020300500c03000000000000c0400400004000000300001000000000600000004000180203003004010040e11000000020040e00001000000040000c06004050080701c030140302c1600c050000b01803088030040a0180303802008100069d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9c6150c43a7d814310f1d4354843c750d5110f1d439404397d8d51d0a5c63547429798e50d0a5d63943429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429d98454cca756115332c715143cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c83297d8d52d065c6354b41a758c42d065e63943419758e50d065e6394a419758e529069c6350a4197d8d509065c63542418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c53905418f596431071d5390c41c754c431071d53d08418fd95421069c6350841c754d421071d53d04418fd95411069c6350441c754d411067765504419b98854cc66d6215331c715143cc63f6454b318f19152cc69d640cb318f99250cc63d64943319b98b548c66d62d5231c7d50438c63e6494a318f592528c69c644ca318fd91508c63c64542318f992544c65f63551318f994544c71d631513197996434c71c5490d3197195434
  | 3 => 0x7d8c79c83d4050468000001fc330002de3bc951680f40000000017855c64a1f0001300007c1a45c88c1010004b800000000000780e92182bc1d00021211c1a98d00021c2d9ec00035800123448000e9a093f0204b090b36a410450cb2ca370a894d200244c61e727c7647504d09603c9900d342578061ba1724381a1ab344844278003e22e0928f93c20547601e2ce7b4a089a4247f46205f3aa5981f8492b6668d311c34e00000011160000460ed18e2506b97f2d677c1c1fe13a8400e1b410a318140f60da898000de1360b8c50000002842a0d802c510000000de0005a8952c07b88f94a1be5e8e592902400511169000000000000002986021900000000000000000431d43ca67c001d7000554ec0003e640ce68b20000c8839d12f6530000e5126600e50000000a40509800078cce030140000001d60467a0b7000000874db8e0000000fd8000000000012700000000225000000b88c10d252c000002c466cca8003f8308e2836278870ff8bb27e0007e1bd3cc000380000001c83718b04a5903d8172a62f8d8800404484ed01f1a02e83c91a0123840982f28e25cd614833271cd7a0c0001f4470000008387e8d42107807d9c9036000199b8000000000000000006700028c0006e8003864481522000c1cc8c94916e0009d90600009c5f8f216c0010590d0ee2102e9141247c8c09393c465c3a8f33e8000000000944c0aa0ad1867ac0011d0c0320000201062908f05a2141903106540c1540000020a118b980b0b80000019d0041151187415c0008b1b638c7c00e800032000000e63200002705640074051837340344759ce3b6000bc0003f20f4002030bc0006c82d0204cc2801a34834ca91ad1e8000110000a45402b8f129c2586d0000ec084389632b239cd91260000009d1dd2ea770718fa40e0000012c1200f00000007c60cd986c28a61c0017d1f0000d28b330a6205a19e08800c651b915000000063000804000fe0b27d46299822e5f8001920624ac2418e000000000001323b8ae0000007bc5e9d201c5590680019e574be11b0c28500008b0000007a8002045b0298000000000017425
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2401aa0040a59c8a018009239400000422678c0000180042610c1431c94354843a28e2a1aa221d1b7050e5010e8ab88a8a1e65459c75410e32838ecaa2641950d7215143cc687396a821c63075d8540c931838ecaa26418c1c76551310c60e3b2a899661071d9544c73083aed2a0651841d76950318c20ebb4a998461431c95410d30a28e2aa0869850d72151430c28ab88a8a1861191d95244010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20202+((h/222+packedAt s3K5 (17982+(h % 222)*10) 10) % 800)*11) 11
  | 4 => packedAt s3K4 (22768+((h/183+packedAt s3K4 (20938+(h % 183)*10) 10) % 728)*11) 11
  | 3 => packedAt s3K3 (1064+((h/7+packedAt s3K3 (1029+(h % 7)*5) 5) % 30)*6) 6
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 1 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 2 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 1 => 0x248a48832490612c0a42a429521482a9432652
  | 2 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37161
namespace PEqualNP.Outside.L_meta_37161
open PEqualNP.Outside.L_meta_37161.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x80030410280b320a7024600022bf43bd43be42bc42be41bc41bf40bd40df30fa30dd30f930d930
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x202400400013948a30d6c14030cd94642972948359538c33680986650130cda1a6199434c334a8986655130cd2126198424c33482986610530
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x30420a2189544c2906155130a4986424c28a6290530
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 13
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (228+((h/4+packedAt s4K4 (208+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s4K3 (371+((h/4+packedAt s4K3 (351+(h % 4)*5) 5) % 19)*5) 5
  | 2 => packedAt s4K2 (155+((h/1+packedAt s4K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x8fffe0f87c3fff0f0f0f1ff8f0783fff20f49f
  | 1 => 0xf07fff007ffe1ff00fffe1ff007ff83e3f38f3
  | 2 => 0xff83ffff803fe1fff00ffe1fff803fc1c7cf1c
  | 3 => 0x3ffffffc001fffff0001fffffc001f80fe0
  | 5 => 0xfffc0000000001ffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa2122224924d11038382133092490b19205485
  | 1 => 0x50844112810203004152049011290a40b2832
  | 2 => 0x128885008a002541009440a2500a484458918
  | 3 => 0x4a53128442055589a9a01114ca650109b006c0
  | 5 => 0x6c621ce6733999eecece99808c460631fef000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfce8fce8fca8fca8fce8fce8fca8fca8fce8fce8fca8fca8fce8fce8fca8fca8fce8fce8fca8fca8fce8fce8fca8fca8fce8fce8fca8fca8fce8fce8fca8fca8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37161
namespace PEqualNP.Outside.L_meta_37161
open PEqualNP.Outside.L_meta_37161.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x8437c53086fca410df94421f790843f621087da4210fd48421f2908437e50086faa010df94f40bea9e81be43d037887a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c81de53902bca7205f54e40eea9c815d539037e87206f50e40bf294817d529037c85206f10a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a81be435037886a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6205f54c40dfa1881bd43102fca4205f54840df21081bc42102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a661be54cc27ca9985f55330deaa6613d54cc2f8a99877d0f30ee21e617e52cc2faa59877ccb30ee996617e51cc2faa39877cc730ee98e617f548c2fca9186f952309f2a4617d548c37aa9184f55230be2a4617d538c2fca5185f54a30bf28c617d518c2fca1187ed0230fc20461df308c3f661185fd5130bf2a2617d544c2f8a89877d0d30ee21a617f524c2f8a49877cc930ee992617f514c2f8a29877cc530ee98a61fb404c3f080987ecc130ef182617f540c2fca8185f55030be2a0617e530c2fca4185f54830bf288617d510c2fca01877cc030fd18061dd300c3f26018764c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb10a21f521443f460887e4c110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85be4390b7887215f94a42dfa1485ef4290afca3217d94642bb28c857d5190beaa3215d54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216f90c42de218857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41dfa1e83bd43d06fca5a0df54b41df21683bc42d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52907dca520db94a41bea9483ed52906daa520efd0a41dea14837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83bd43506fea4a0df14941df21283bc42507ee82a0ef90541bfa82837c50506fca820df94c41bea9883be43107788620df94841bea9083bf421077a8420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c7dca418db94831bea9063ed520c6daa418df94431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c87de8590fb10b21f719643ed32c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea94437e51887ee8310fd10621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c53487de8490fb10921f719243ed32487ee8290fd10521fb18a43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea9
  | 2 => 0x1c0000738d305d35e000000f1000000f10000b6610ad22706095d2d15321a92d099bd1543286689b0f42241125334800002122430778af9cf4f21bc6b1761a00000f2773029c1029360b058c001ef4cc5d4f092f00011d3008a1246005625b3e80e4e200d4666444206547e000fe1190007b0811c93ce5790c83100082ccc8000529b055a1f32c59cfa83d4d6874751cd240504fb225000728738f90001a92a91d00001c0a18e0000000018d0a838c6da352e68287a8ba12c348b6a3c00067c6090502429d21a7106e018b909c0005a85d98c436020a00674ac4e53522610e40cce9774623705c8bc316100b00004546b4099130d685c8d02800049d0a2220829a0109c71fa98c3c05c000000000000006f91da103a40b4ed000000440968fa37235cae0b71a6314638b333450ccb90b3f43c0eb08e0e8180220b02c28b41b1dc1348b89810c17a094332001d2000231694ce0f9021bf4184282703536e3851b9d910c168ba0700c83500000000032caa9d12d6774611481ba001092210401ec0021e41c23c001e31de09c5a16600a00000123404144312283743d0d010915e1a5210003d4058440e02ba5e0ab0001300011c06d000938de000000038000001460006480017e000d8a290ec9d4b28a93ca000178004bc5e800093494561192730a60ad121640768bd008000007912f9b232800000000000001222200007cc8b0003e255c9989120c1b89a8fc0789144811b3564e0cc1f73206b08a1c8000528000004220000e8002e2904f30f74107ecda9cc1c81f8d19d01ca5fc3a8a10000004a1a9000754da00c0000001918a4a8538459121bc6cd368a02de3e0c3a5819c001378000000002c88c1b41c4689ee29e4f89a0111e40000020910a8f8318000007a0d38000fa000cf03424a918291112541207706120e0001700f4ca0140b000180140203800018060000200c0000000090080140000c060a40e00c08000190000200800018320e8060083001000008000000a0001f000030042804c040100000c05028010380103c0600004000140000200c0701c04004010bc05000040240500c010740e010010100c004000080001807004000000a0280100004000000280304c1a054000000200000010020000200009054100040000c06064080040502403000110000502007028010140501400000000280a00c020140206403000000000200403008100000d000270040004c1600402000290201b00400014060ec0800c00000020040a0000b00c020000900011028020040300800024070200500c1003405002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf28487fa5090ef4a121df54243fca8487795090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877
  | 3 => 0x3243d928000472178a491e3f213c001d41063b0f81b80d870c6c9ae3501dc9481f4a21590d1324800002a800020544000c61fe290399441fc7f45f07c2a027d0303838a461312161d61145a84c144388008003763b51e9df0386249318f248608210192b6964e58793e433024937000400c41e03da8acce00023e9c8a10820748d00014d19e4b8259544ec2a0618684986189604d21e001279a516c5c00002a00045c25274012000a382330a9748e0e80002549d050000000620000000000002c00017cf4908102454390000000011813f4c810d119b0000588eb93b0000007da47000685290e63268540009e384000001ff4b82b5268971004a0d117e4582b8bc97c0342c84e9c616281c4694632a5640b9c12fa1fc9592121c15d24015000320050001be76c002030008706c1f82f63cca583f30606cb40022a406106a613a64f12480b14a760b70a64dc2e0ff1aa06666cf580041e000001041803540014c36c5b13c1450064c49ea694740911b0260000008089900000000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5544c25e65d0d30b6983434c23e64149308f590524c27661149309d584524c29c644c930b6181324c23e64145308f590514c26e62145309b588514c29c644c530b6181314c27a65d0130b698f404c39843d0130e6d0c404c2ba64cc130a7992304c25e63d50309e983540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c23f64544308f191510c23e64940308f592500c2d9638c03097d95300c27b654c030b6d95300c35b654c030d6951300c358544c030d6549300c359514c0309d98754c827561d53208fd9153c823c6454f208f99053c823d6414f209d98453c82756114f208f99251c823d64947209798f548825d63d52208f993538823d64d4e208f992538823d6494e208fd91518823c6454620d614d308823e64951208f994544823e6494d208f592534823f6454d208f19153482776154d209d185534832c54c8520cb15121483645148520ce1523048278654c120ce1513048358534c1209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c209e98053083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510836551c8020d654e200826f6548020d9545200827b6548020d654d200826e62d53109b58b54c423f6454f108f19153c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6494b108f59252c436452487109798f548425d63d52108f993538423d64d4e108f992538423d6494e108fd91528423c6454a108f990528423d6414a109798c528425d6314a10d614d308423e64951108f994544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524433454885109d19521443345448510d91492144338548c1109e1953044338544c110d614d304425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520436552c40109e596100435953840109dd95100436552440109ed9510043595344010
  | 1 => 0xca3f64542328f191508ca3e64951328f994544ca7661d50329d587540ca7a60d50329e583540ca3d65950328f990540ca7661150329d584540ca7a60150329e580540ca5f654c8329bd95320cb365494432cd552510cb365454432cd551510cb663254432d94c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cb5b3254032d64c9500ca7a6094f419e58253d06b66190b419798e50d065d6394341ae982439072e4394a41cb10e529072e52d0a41cb949429072e52d0641d954b419063e65d0d41ad986425063e6510941ab98a415063d6590c41ae982431063f6550841b958a411063f65504419dd95411067a60d53319e58354cc63f6454b318f19152cc63e64943318f59250cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508c63e64951318f994544c66e62d50319b58b540c67a60d50319e583540c63d65950318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c765528c43197d95310c677654c431d9549310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c75b3154031d64c5500c72c62553218f99353c863d64d4f218f99053c863d6414f219e98053c86796014f21cb55342c86ac644cb21cd185548863e64d4e218f593538863e6414e218f590538867a6014e219e580538873554d0621ad191318872e54c8621ad993218865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534867a6014d219e580534866e65d0921b9987424866c654c921ab19132486e4614c9219d99741486e662d0521e910b41487a742105219d19531486b4644c521b918931486b664c8521ab992214863e64141218f590504865e63141219758c504866e62d50219d987540865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530866e6214c219d984530867a6014c219e580530863e64948218f592520863e64944218f59251086e562884219bd9521086776548421b9d9521087676548421d995121087645448421d9d4d210876553484218fd91500863c6454021d948550086ba6090f409d98652d02756194b409b98a51d026d6294740c794f439031e5350e40c794e42902b66190a40c794c429031e5390640ab98a419031e5310640c794f409035953d0240ae982435023e6510d408f997425023e65d0540a798e405023f6550c408f59642102b661908408f59641102ae6290440b658e401023f65500409ed95401031c6355330c755343cc29c644cb30a719131cc3386055230ce553408c31e54cc230ae993308c26f62551309b189544c27761551309d18
  | 2 => 0x1e800d6800002c09e06601b78bf80034276c01f08b2ca4a0b0971faa210e16b9c64200ab3746f000520001ca5e00000bca7e3880000360000000021ed1248380ce7003400102d7800ce334b40003e9ec59938a98000003a680480019e750d4a00f8003282c884893360000054a1800000c08000027c3c000000388d012002e67a3264f8000000a869ee0028200016000a8001a2208000000000272390a4000be6380014800c200000000c380078000000008700000000000e8882a200000600e6000000000024b62d4b3c4a80000240000c2002ce000a2d41f6ce8005d15873036acb640b2523314245af6779a6a38fcbb22e36070c811e3fa10e3b18e43946ba169501e55ba2db260e13560c22a6d96e001363a800611b05aae00036adcb0a1625a188001a02000330a495a099e217a6813af8000007432e00332000002b1e4848aa0000073856e304c55000e030c42000278005716c0a164000000025600000002ae00000070000680000b1ea1b540031aa429800000001eadf0000034a1b800b08f45da7a00000afac4000240882adeb66a7b222d34cba2627fb1c0bba0c4106000005e03e7cb7eb3112003822e80069370af000660000000000368e68ca00010002f000086000a60000006000aa90000000000001f00030000000001e23823a9c719ac838006e39832132378000020436b920028400000a691a0000061800e19600010400000bf12c00076ba800c92a8001c4960006308a000003ba44b61dab1800908942334e3126c501209380000000ae0b8430009c000020004d074002b41b2d200236528008f000000005e914000c6e2228ca8000023e000002214400000a90001817cc4800d21d600376c58009b8005880000000000000024c001461a930e926a190004f230cfa50e2ac8d009aad97e0240500800004160001300002008020040001c02004040140601c000000201400000000481300c000040000400020010240a0140000c00000000000601401000050100000c030000f0000204c030040000000018000100100012004000000000801014030140401c0000c1700c0000c06028000240702403000000100b010000081000c0203c110000002005000020080000c0500c0e004010080200800000030300200408010000a40100006000040000d00403034000040c0040402c0f0080f02e766194b439d58652d0e6e62947439b58a51d0f3b4394243d6d0d5090eba6090d43b65824310e3f6550c4397d954310e7a6094f429e58253d0a5e63943429758e50d0aba6090e42cd90e5190b344394642cdd0a5190b6742546428f9974350ab661909428f5964310aba6090c42b95864210a3f65508429bd954210a7a60d53329e58354cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548ca3e64946328f592518
  | 3 => 0x24aa3000000000004a830d6488002f342db95e349d253a64461960007e8c9be9180e14226808006d28a4eaf4bb98ab8a06c12d4282dc652747d0000132c00214001ca240b600124668ae530140018249800c19b2001dc000000039e3710a7600099b14d72a00035825ad66a8327f296d18f6b90544708000000be91000044000408280000000821c8001c2888ec001a85c9928e8000f098000f2ac0006ea94032ba001e67e396272da119500012e1085c67168002de0017062000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xc821c0a01400130034b56100014a6993848728c854a9c24394a41a4ce9b2a4210d457315121086b0b80a890843491d15348421c48c890aa010e1653986429030729cc520c81469d3654c030a92e42a2601855171151300c28c3a2a498061461d1514c030
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 634
  | 4 => 467
  | 3 => 14
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (19228+((h/211+packedAt s5K5 (17118+(h % 211)*10) 10) % 761)*11) 11
  | 4 => packedAt s5K4 (19296+((h/155+packedAt s5K4 (17746+(h % 155)*10) 10) % 678)*10) 10
  | 3 => packedAt s5K3 (706+((h/4+packedAt s5K3 (686+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3f8fffc1f1f1ffc3c78fe3fc70707ffc38f49f
  | 1 => 0xc7f07ffe01fff1fc07f1fc7f807ff07cc738f3
  | 2 => 0x7ff83fffe01fe3ff801ff8fff807f8307cf1c
  | 3 => 0xf80003fffffe003ffffe000fffff8003f80fe0
  | 4 => 0xfffffc000000003ffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa2104442426000c182409812121630185485
  | 1 => 0x9105088824a0820c0210a42481252148432832
  | 2 => 0xa2012910a02500550801290525014909058918
  | 3 => 0x4a5225010024a254a4000a4a4a0212a806c0
  | 4 => 0x346c6039c9c9c93ba749d2400c0c0c63f6f000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8fee8fca8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37161
namespace PEqualNP.Outside.L_meta_37161
open PEqualNP.Outside.L_meta_37161.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c180017fd5005fe54017f55005fc5400ffd4c037f5300ff94c03fd5300df54c03fc5300ffd0c03fe4300ff50c03fc43017fd4805fe52017f54805fc52007fd0801fe42007f50801fc4200ffcc803fe3200ff4c803fc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc50007fd0001fe40007f50001fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84200affd9510055feca880037f65440013fb2a200aff99510015fcca8802bfd65440157eb2a200aff19510015f8ca8802b7c65440053e32a2000ffd9110005fec888003bf64440015fb222000ff99110045fcc888003fd64440017eb222000ff19110045f8c888003bc64440015e322200affd5110057fca88802bfd5444015fe2a22009ffd8d1004dfec688027fe63440037f31a2009ff58d1004dfac688027fc63440037e31a2009ffd4d1004efea688027fe5344013fea9a2009df54d1004ff8a688027ff4344013ff21a2009ff50d1004ff88688003ff62440017fb122000ff9891003dfcc488003fd62440017eb122000ff1891003df8c48802bff5244015ff292200aff54910057f8a488003ff4244001ff2122000ff50910007f88488027ff3244013ff1922009ff4c91004ff8648802bff5144007ff28a200aff5451001ff8a288003ff4144007ff20a2000ff5051001ff88288027ff3144007ff18a2009ff4c51001ff86288003ff2144007ff10a2000fd88510007fa4288003f52144007fe10a200affd4110027fca08802bfd5044009fe2822000ffd0110027fc8088003fd4044009fe2022009ffcc110027fc6088027fa3044013fe9822009fe4c110027f86088003ff2044009ff1022000ff48110027f8408800fff1044007fd8822004ff84110027ec2088013ff65040097fb282004ff99410015fcca080137e65040053f3282004ff59410035faca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010045fcc808013be64040015f3202004ff59010005fac808013bd64040015eb202004ff19010025f8c80801bff540400dff2a02006ff55010037f8a808013ff63040097fb182004ff98c1000dfcc608013de63040036f3182004ff58c1002dfac608013dd63040016eb182004ff18c10025f8c608017ff530400bbfa982005ff94c1002ffaa6080177d530400bfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd8810025fec408013fe620400f7f3102004fb98810005dcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102006ffd4810037fca40801bfd520400dfe2902000ffd0810007fc8408003fd4204001fe2102005ffcc81002ffc6408017fd320400bfe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802003fe44010
  | 1 => 0x3fc5108001ffa084000ff90420007fa8210003fc410801fff988400fff8c42007ffa621003ffc310800fff9084007ff8842003ffa421001ffc21080097f3004004ffd4020027fca010013fd5008009fe2804004ffd0020027fc8010013fd4008009fe2004004ffcc020027fc6010013fd3008009fe1804004ffc8020027de4010013fe2008009fd1004004ff48020027da401001ff92008007ffb2e2003bfd971001ffccb8800afe65c4007feb2e200ebf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988022fe64c4007feb262000bf5931001ff8c98800efc64c401dffaa6200eff95310077faa98803bfc54c4007ffb1e2003bfd8f1001ffcc788006fe63c4007feb1e200dbf58f1001ff8c78800efc63c401bffa9e200ddfd4f1006ffca788037fd53c401bbea9e200dff14f1006ffe8788037fe43c401bfea1e200dff10f1001ffec58800eff62c4007ff3162007bf98b1001ffac588002fd62c4007fe3162003bf18b10077fea58803bfe52c401dfea96200eff14b10007fe8588003fe42c4001fea162000ff10b1006ffe6588037fe32c401bfe996200dff0cb1001ffea38800ffe51c4007fea8e2003ff1471001ffe838800ffe41c4007fea0e2003ff1071001ffe638800ffe31c4007fe98e2003ff0c71001ffe438800ffe21c4007fb10e2003ff48710007ea438800ffc21c401dffa862004ff94310077faa188013fc50c4001ffa062004ff90310007fa8188013fc40c401bff9862004ff8c31006ffa6188013fc30c4001ff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb0800afe6584009feb2c200cbf59610027f8cb08012fc6584009ffb242004bfd9210027fcc908022fe6484009feb242000bf59210027f8c908012fc6484019ffaa4200cff95210067faa908033fc5484009ffb1c2004bfd8e10027fcc708006fe6384009feb1c200bbf58e10027f8c708012fc6384017ffa9c200bdfd4e1005ffca70802ffd5384017bea9c200bff14e1005ffe870802ffe4384017fea1c200bff10e10027fec508012ff6284009ff3142007bf98a10027fac508002fd6284009fe3142004bf18a10067fea508033fe5284019fea94200cff14a10007fe8508003fe4284001fea142000ff10a1005ffe650802ffe3284017fe994200bff0ca1004dfac308033ff5184007ff28c200cff5461001ff8a308003ff4184007ff20c2000ff5061001ff8830802fff3184007ff18c200bff4c61001ff86308003ff2184007ff10c2000ff4861001ff84308012fe6084009ffa842004ff94210027faa108013fc5084009ffa042004ff90210027fa8108013fc4084009ff9842004ff8c210027f46108013fd3084017fc9842004ff0c210027fe4108013fe2084009fe9042004ff08210027fe2108013f71084007fd8
  | 2 => 0x2003ff8851004fff328800fff1944013ff4ca2003ff86510013ff6188009ff30c4003bf98620027fac310002fd6188009fe30c4014ffd46200a7fca310053fd5188029fe28c4000ffd0620007fc8310003fd4188001fe20c4013ffcc62009ffc631004ffd3188027fe18c4007ffc8620007fc4310003fd218800ffe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fd1844004ff4c22009ff26110013fc3088009ff9044004fbc822003ff6411004bff65480257fb2a4000dfd9520004feca9004bfe65480057f32a4012ff59520095faca9004bfc65480057e32a4012df19520014f8ca90003ff64480017fb224000efd91200057ec890003fe64480117f3224000ff59120005fac890003fc64480117e3224000ef1912000578c89004bff5448025ff2a24012ff55120097f8a890047ff63480237fb1a4011ff98d2000dfcc690047fd63480237eb1a4011ff18d2000df8c690047ff5348023bfa9a4011ff94d2008ffaa6900477d5348023fe29a4011ffd0d2008ffc8690047fd4348023fe21a4012ffd492003ffca49004bfd524800ffe2924000ffd092003ffc8490003fd424800ffe2124011ffcc92003ffc6490047fd324800ffe1924000ffd8520005fec290003fe6148001feb0a4000ff1852001df8c29004bff5148025ff28a4012ff54520097f8a290003ff4148001ff20a4000ff50520007f88290047ff3148023ff18a4011ff4c52008ff8629001fff2148001f790a4000ff88520007fa4290003ed214800ffe10a4012ffd4120027fca09004bfd5048009fe2824000ffd0120027fc8090003fd4048009fe2024011ffcc120027fc6090047fa3048023fe9824011fe4c120027f8609001fff204800ffd9024004ff88120027dc4090013ff65080097fb284004ff99420015fcca100137e65080053f3284004ff59420085faca100137d65080013eb284004ff19420025f8ca10013ff64080097fb204004ff99020045fcc810013be64080015f3204004ff59020005fac810013bd64080015eb204004ff19020025f8c810043ff5408021ff2a04010ff55020087f8a810013ff63080097fb184004ff98c2000dfcc610013de63080036f3184004ff58c2007dfac610013dd63080016eb184004ff18c20025f8c61003fff530801fbfa98400fff94c2007ffaa61003f7d530801ffe298400fffd0c2007ffc861003ffd430801ffe2184007bf9882003ffea41001ffe520800ffea904007ff1482003ffe841001ffe420800ffea104007ff1082003ffe641001ffe320800ffe9904007ff0c820027fec210013fe61080077f3084004fd98420005ecc210013fd61080017eb084004fd58420005eac210013fc6108021ffa884010ff94420087faa21004
  | 3 => 0xe3288008bf99040047fea820023fe5410011df2a08008ff550400c77aa820023fc5410009ffb188004bfd8c40027fcc620006fe6310009feb188017bf58c40027f8c620012fc631002fffa988017dfd4c400bffca62005ffd531002fbea988017ff14c40047fe8620023bf4310011ff2188008ff50c400bf7a8620023fc4310009ffb108004ff9884003dfcc420013fd62100017eb108004ff188400c7fea420063fe5210031fea908018ff14840047fe8420023fe4210001df2108008ff50840047f88420023bc421002fff9908017ff8c8400bffa642005ffc3210009ffb088004ff9844001dfcc220013fd61100017eb088004ff184400c7fea220063fe5110031fea888018ff14440047fe8220023fe4110001df2088008ff50440047f88220023bc411002fff9888017ff8c4400bffa622005ffc3110001ff9088000ff88440007fa4220003fc21100097f3008004ffd4040027fca020013fd5010009fe2808004ffd00400277e8020013fe4010009fd2008004ff500400277a8020023f94010009ff9808004ff8c040027f46020013fd301002ffc9808004ff0c04003ffecb9001eff65c800fff32e4002bf9972003ffacb9005afd65c800ffe32e4007bf1972003ffec99001eff64c800fff3264008bf9932003ffac990002fd64c800ffe3264007bf193200b7fea99005bfe54c802dfeaa64016ff1532003ffec79001eff63c800fff31e4001bf98f2003ffac790056fd63c800ffe31e4007bf18f200affea7900577f53c802bff29e4015ff54f200aefaa790057fc53c802bffa1e4015ff90f200affa8790057fc43c800fffa964007ff94b2003ffaa59001ffc52c800fffa164007ff90b2003ffa859001ffc42c800fff9964007ff8cb2003ffa659001ffc32c800fffb0e4007ff9872001dfcc39001ffd61c80017eb0e4007ff187200b7fea39005bfe51c802dfea8e4016ff14720007fe8390003fe41c8001fea0e4000ff107200affe6390057fe31c802bfe98e4015ff0c72003ffe439001fef21c800fff10e4007ff48720007da439001ffc21c802dffa864004ff943200b7faa190013fc50c8001ffa064004ff90320007fa8190013fc40c802bff9864004ff8c3200affa6190013fc30c8009ffb2c4004bfd9620027fccb1000afe6588009feb2c4014bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc910022fe6488009feb244000bf59220027f8c910012fc6488029ffaa44014ff952200a7faa910053fc5488009ffb1c4004bfd8e20027fcc710006fe6388009feb1c4013bf58e20027f8c710012fc6388027ffa9c4013dfd4e2009ffca71004ffd5388027bea9c4013ff14e2009ffe871004ffe4388027fea1c4013ff10e2008dfac510053ff528800fff2944014ff54a2003ff8a510003ff428800fff2144000ff50a
  | 4 => 0x23fc61d003dffa8e801eff947400f7faa3a007bfc51d0011ffa0e8008efd0740047fc83a0023fd41d0001dea0e8008ff107400effe63a0077fe31d003bfe98e801dff0c740007fe43a0003fe21d0001fe90e8000ff087400f7fea1a0013fe50d003dfea868004ff143400effe61a0013fe30d003bfd186801dff4c3400eff261a0013fc30d0009ffb2c8004bfd9640027fccb2000afe6590009bf32c80029f99640027facb20072fd6590009beb2c80009f59640027f8cb20012fc65900337eb24801cffd5240047fca920073be5490039feaa4801cef55240047f8a920013ff63900097fb1c8004ff98e4000dfcc720013de63900036f31c8004ff58e400ddfac720013dd63900016eb1c8004ff18e40025f8c72006fff5390037bfa9c801bff94e400dffaa72006f7d5390037fe29c8008ffd0e400df7e872006ffe4390037fea1c801bef50e40047f88720013ff6290009ff3148007bf98a40027fac520002fd6290009fe314801cffd4a400e7fca520073fd5290039fe2948008ffd0a40007fc8520003be4290001fea148008ff10a4000778852006fff3290037ff194801bff4ca400dff86520013ff6190009ff30c8003bf98640027fac320002fd6190009fe30c801cffd46400e7fca320073fd5190039fe28c8008ffd0640007fc8320003be4190001fea0c8008ff1064000778832006fff3190037ff18c801bff4c6400dff86320003ff2190001ff10c8000ff48640007f84320012fe6090009ffa848004ff94240027faa120013fc5090009ffa048004efd0240047f68120013ff3090009ff1848004ff4c240027f8612006bff65500357fb2a801aff99540015fccaa006bfd65500357eb2a801aff19540015f8caa006bff5450011ff2a2801aff55140047f8a8a0067ff63500337fb1a8019ff98d4000dfcc6a0067fd63500337eb1a8019ff18d4000df8c6a0067ff5350033bfa9a8019ff94d400cffaa6a00677d5350033fe29a8008ffd0d400cffc86a0067fd4350011fe21a8000ffd8940005fec4a0003fe6250001feb128000ff1894003df8c4a006bff5250035ff292801aff549400d7f8a4a0023ff4250001dfa128000ff90940007fa84a0003bd4250011fe2128019ffcc9400cffc64a0067fd3250033fe1928000ffd8540005fec2a0003fe6150001feb0a8000ff1854001df8c2a006bff5150035ff28a801aff545400d7f8a2a0023ff4150001dfa0a8000ff90540007fa82a0003bd4150011fe20a8019ffcc5400cffc62a0067fd3150033fe18a8000ffc8540007fc42a0003fd2150001fe10a801affd4140027fca0a006bfd5050009fe2828008ffd0140047f680a0013fe4050009df2028019ffcc140027fc60a0067fd3050009fe1828004ffd9440025feca20013fe65100057f3288004ff594400c5faca20013fc65100097
  | 5 => 0x9521007fec890802ff6448401ff3224208bf99121007fac890802fd6448401fe3224208bf19121117fea89088bfe5448445feaa24222ff1512110ffec690886ff6348443ff31a4201bf98d2110ffac690886fd6348443fe31a4201bf18d2110ffea6908877f5348443ff29a4221ff54d2110efaa690887fc5348443ffa1a4221ff90d2110ffa8690887fc4348445ffa924207ff94921117faa49081ffc5248401ffa124207ff90921007fa849081ffc4248443ff9924207ff8c92110fdc6490887fd3248443f69924207ff0c921117fea29080ffe5148445fea8a4203ff14521007fe829080ffe4148401fea0a4203ff1052110ffe629080ffe3148443fb18a4221ff4c52110fea629080ffc314840fff90a4207fdc852101ffc429080fee2148401ffb024200bfd8121007fcc090803fd6048401fe3024204bf18121117fea09088bfe5048445fea824222ff1412110ffe6090887fe3048443fe9824221ff0c12101ffeca1080eff6508407ff3284202bf9942101ffaca10882fd6508407fe3284203bf1942101ffec81080eff6408407ff3204208bf9902101ffac810802fd6408407fe3204203bf19021107fea810883fe5408441feaa04220ff1502101ffec61080eff6308407ff3184201bf98c2101ffac61087efd6308407fe3184203bf18c210fffea61087f7f530843fff298421fff54c210fefaa61087ffc530843fffa18421fff90c210fffa861087ffc430840f7f3104207ffd482103ffca41081ffd520840ffe2904207ffd082103ffc841081ffd420840ffe2104207ffcc82103ffc641081ffd320840ffe1904203bf9842101ffea21080ffe5108407fea884203ff1442101ffe821080ffe4108407fea084203ff1042101ffe621080ffe3108407fe9884203ff0c42101ffe421080fef2108407ff1084203fd8842101ffa421080fed210840ffa9084200f94842101ffec01080ffe60084097f3004203ff58021005fac01080ffc6008441ffa804220ff94021107faa010883fc500843fff980421fff8c0210fffa601087ffc3008411ffb2e8008bfd9740047fccba000afe65d0011bf32e80029f99740047facba007afd65d0011beb2e80009f59740047f8cba0022fc65d0011ffaa68008ff95340047faa9a0023fc54d0011ffb1e8008bfd8f40047fcc7a0006fe63d0011feb1e801dbf58f40047f8c7a0006fc63d003bffa9e801ddfd4f400effca7a0077fd53d003bbea9e801dff14f40047fe87a0023fe43d0011fea1e8008ff10f40047fec5a0023fe62d000f7f3168008ff58b40005fac5a0023fc62d003dffa96801eff94b400f7faa5a007bfc52d0011ffa168008efd0b40047fc85a0023fd42d0001dea168008ff10b400effe65a0077fe32d003bfe996801dff0cb40047fec3a0023fe61d00077f30e8008ff58740005fac3a0
  | 6 => 0x1fea108200ef50841047f8842089fff321044fff1908227ff4c84113ff8642080efe6110407ffa888203ff9444101ffaa22080ffc5110407ffa088203efd044101ffc822080ff64110407fea088203ef50441047ea822080fff3110407ff1888203ff4c44101ff8622080fff6010407ff3008204bf9804101ffac020802fd6010407fe3008228ffd4041147fca0208a3fd5010451fe2808227ffcc04113ffc602089ffd301044ffe1808207ffd972103dfecb9081ffe65c84057f32e4207df99721014fccb9081ffd65c844d7eb2e4207df59721004facb9081ffc65c840f7e32e4207ffd932103dfec99081ffe64c84117f3264207ef993210057cc99081ffd64c84017eb264207ef593210057ac99081ffc64c840f7e3264226ffd5321137fca99089bfd54c844dfe2a64207ffd8f2103dfec79081ffe63c84037f31e4207ff58f2112dfac79081ffc63c840f7e31e4225ffd4f2112efea790897fe53c844bfea9e4225df54f2112ff8a790897ff43c844bff21e4225ff50f2112ff8879081fff52c840fff2964207ff54b2103ff8a59081fff42c840fff2164207ff50b2103ff8859081fff32c840fff1964207fb8cb2103ffa6590897ed32c840ffe1964226ffd472101ffca39089bfd51c8407fe28e4200ffd072101ffc8390803fd41c8407fe20e4225ffcc72101ffc6390897fd31c8407fe18e4207ffd832103ffcc190812fe60c840ffeb064200bf5832103ff8c19089bff50c844dff2864226ff54321137f8a190897ff30c844bff1864225ff4c32112ff8619080fff65884077fb2c4203ff99621015fccb1080f7e65884053f32c4203ff59621125facb1080f7d65884013eb2c4203ff1962101df8cb1080fff64884077fb244203ff99221045fcc91080fbe64884015f3244203ff59221005fac91080fbd64884015eb244203ff1922101df8c910893ff5488449ff2a44224ff55221127f8a91080fff63884077fb1c4203ff98e2100dfcc71080ffd63884477eb1c4203ff18e2101df8c71088fff5388447bfa9c4223ff94e2111ffaa71088f7d5388447fe29c4223ffd0e2111ffc871088ffd4388447fe21c4221bf58a21127fea51081ffe5288449fea944207ff14a21007fe851081ffe4288401fea144207ff10a2111ffe651081ffe3288447fe9944207ff0ca2101dfcc31080fff5188407ff28c4203ff5462101ff8a31080fff4188407ff20c4203ff5062101ff8831080fff3188407ff18c4203fd8c62101ffa631088ff53188407fe18c4203ffc862101fde431081ff72188407ffb044203ff98221025fcc11080ffd60884017eb044203ff18221127fea110893fe5088449fea844224ff1422111ffe611088ffe3088447fe9844223ff0c221117feca9088aff6548445ff32a4202bf99521117faca9088afd6548445fe32a4202bf1
  | 7 => 0xa0812fe60d0411feb068200bf58341047f8c1a08bbff50d045dff286822eff54341177f8a1a08b7ff30d045bff186822dff4c34116ff861a080fff65904077fb2c8203ff99641015fccb2080ffd65904597eb2c8203ff1964101df8cb208a6fd6490459ffaa48208ff95241167faa920823fc5490407ffb1c8203bfd8e4101ffcc720806fe6390407feb1c822bbf58e4101ff8c72080efc6390457ffa9c822bdfd4e4115ffca7208affd5390457bea9c822bff14e41047fe87208affe4390457fea1c8208ff10e4101ffec52080ffe629040f7f3148203ff58a41005fac52080ffc6290459ffa94822cff94a41167faa5208b3fc5290411ffa148200efd0a41007fc8520803fd4290401dea148208ff10a4115ffe65208affe3290457fe994822bff0ca4101dfcc32080fff5190407ff28c8203ff5464101ff8a32080fff4190407dfa0c8208fdd064101ffe632080ffe3190407fe98c8203ff0c64101ffec12080ffe60904097f3048203ff58241005fac12080ffc6090459ffa84822cff94241167faa1208b3fc5090457ff984822bff8c24115ffa61208affc3090455ffb2a822abfd9541006fecaa08027f6550455ff32a8202bf99541157facaa08aafd6550455fe32a8202bf19541156f8caa080a7c6550455ffaa28208ff951411577ca8a08abfd5450455deaa28208ff1514114ffec6a08a6ff6350453ff31a8201bf98d4114ffac6a08a6fd6350453fe31a8201bf18d4114ffea6a08a77f5350453ff29a8229ff54d4114efaa6a08a7fc5350411ffa1a8229efd0d4114ffc86a08a7fd4350453dea1a8208ff10d41007fec4a0802ff6250401ff3128200ff58941007f8c4a081efc6250455ffa92822aff94941157faa4a08abfc5250411ffa128200ff909410077c84a0803fd4250411fe2128200ef1094114ffe64a08a7fe3250453fe9928229ff0c941157fea2a080ffe5150455fea8a8203ff14541047fe82a0823f74150407ff20a8203ef9054114ffe62a080ffe3150453fe98a8203ff0c541007fec0a0802ff6050401ff3028200ff58141007f8c0a0812fc6050455ffa82822aff94141157faa0a08abfc5050453ff9828229ff8c14114ffa60a08a7fc3050407ffb288203bfd944101ffcca2080afe6510407bf32882029f9944101ffaca208a2fd6510407beb2882009f5944101ff8ca2080efc65104117f3208208ffd5041047fca820823fd5410411fe2a08203ffd8c4101dfec62080ffe63104037f3188203ff58c4113dfac62080ffc63104077e3188227ffd4c4113efea62089ffe531044ffea988227df54c4113ff8a620823ff4310411ff2188208ff50c41047f8862080fff6210407ff3108207bf9884101ffac420802fd6210407fe3108228ffd4841147fca4208a3fd5210451fe2908208ffd08410477e8420823fe421041
  | 8 => 0xf0c242197fecaa10caff6550801bfb2a84009fd9542197fccaa100afe6550865feb2a8432bf59542197f8caa100afc6550865be32a84029f19542197fea8a1023fe5450865df2a28432ff551421977aa8a1023fc5450863ffb1a8431bfd8d4218ffcc6a1006fe6350863feb1a8431bf58d4218ff8c6a1006fc6350863ffa9a8431dfd4d4218ffca6a10c7fd5350863bea9a8431ff14d42047fe86a10c7bf4350863ff21a8431ff50d4218f7a86a1023fc4350865ffa928407ff94942197faa4a101ffc5250811ffa128408fbd094203ffc84a101fbe4250863ff9928407ff8c94218ffa64a101ffc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8403bf18542197fea2a10cbfe5150865fea8a8432ff1454218ffe62a10c7fe3150863fe98a8431ff0c542007fec0a1002ff6050801ff3028400ff58142007f8c0a1012fc6050865ffa828432ff94142197faa0a10cbfc5050863ff9828431ff8c14218ffa60a10c7fc305080fffb288407bfd944203ffcca2100afe651080fbf32884029f9944203ffaca210c2fd651080fbeb2884009f5944203ff8ca2101efc65108117f3208408ffd5042047fca821023fd5410811fe2a08407ffd8c4203dfec62101ffe63108037f3188407ff58c4217dfac62101ffc631080f7e318842fffd4c4217efea6210bffe531085ffea98842fdf54c4217ff8a621023ff4310811ff2188408ff50c42047f8862101efe621080fffa908407ff9484203ffaa42101ffc521080fffa108407efd084203ffc842101fee421080ffea108407ef50842047da842101fff321080fff1908407ff4c84203ff8642101fff611080fff3088403bf9844203ffac221002fd611080ffe3088430ffd4442187fca2210c3fd5110861fe288842fffcc44217ffc62210bffd311085ffe1888407ffd804203ffcc021012fe601080ffeb008400bf5804203ff8c0210c3ff5010861ff2808430ff54042187f8a0210bfff301085fff180842fff4c04217ff86021023ff65d04117fb2e8208ff99741015fccba0823fd65d045d7eb2e8208ff19741045f8cba0823ff54d0411ff2a68208ef95341047faa9a08bbbd54d0411fe2a68208ffd8f41045fec7a0823fe63d04037f31e8208ff58f4116dfac7a0823fc63d04037e31e822dffd4f4116efea7a08b7fe53d045bfea9e822ddf54f4116ff8a7a0823ff43d0411dfa1e8208ff90f41047fa87a08b7bd43d0411fe21e8208ffd8b41047fcc5a081efe62d0411feb168200bf58b41047f8c5a08bbff52d045dff296822eff54b41177f8a5a0823ff42d0411ff2168200ef90b41047fa85a0823fc42d0411de216822dffccb4116ffc65a08b7fd32d045bfe196822effd474101ffca3a08bbfd51d0407fe28e822dffcc74101ffc63a08b7fd31d0407fe18e8208ffd8341047fcc1
  | 9 => 0xa01201203e00803203200e00e06800806002601200600000207e00000200000a00200201802200001800800200600400a03601000000001600000000200c00004600000200a00000800000000400000400000403203e02400000e01a00600000000205400200000001401800600a00e01000a00000e00000603400400000603a00e00401a02600200400401800601600201203a00401e05c01200400800e00207e02001404801000c03200000001600007200c08e01601400000000405c07005c01c01000005001801602400400002600c0000020020180060000000000a200200a02001202001e00002800e00200000200205001c00e00002e00606e01002000801601401400a00a02c00002002400c0120b808800200000000400202000e00602e00200201200002400600c00c01e01600600800400000a03c01a03001002c00000400002a02c00c00400200600000400001a00400400000403a00600007008000200c00200801007600400600005801800e02405a08ffd9742045fecba1023fe65d08057f32e8408ff597421b5facba1023fc65d08117e32e8408ffd5342047fca9a1023be54d0811feaa68436ef55342047f8a9a1023ff63d08117fb1e8408ff98f4200dfcc7a1023fd63d086b7eb1e8408ff18f4200df8c7a10d7ff53d086bbfa9e8435ff94f421affaa7a10d77d53d086bfe29e8408ffd0f420477e87a1023fe43d0811fea1e8435ef50f42047f887a10dbff52d080fff2968436ff54b4203ff8a5a10d7ff32d080fff1968435ff4cb4203ff865a1023ff61d0811ff30e8403bf98742047fac3a1002fd61d0811fe30e8436ffd47421b7fca3a10dbfd51d086dfe28e8435ffcc7421affc63a10d7fd31d086bfe18e8408ffd8342047fcc1a1012fe60d0811feb068400bf58342047f8c1a10dbff50d086dff2868436ff543421b7f8a1a10d7ff30d086bff1868435ff4c3421aff861a101fff659080f7fb2c8407ff99642015fccb2101ffd65908697eb2c8407ff1964203df8cb210c6fd6490869ffaa48408ff952421a7faa921023fc549080fffb1c8407bfd8e4203ffcc721006fe639080ffeb1c8433bf58e4203ff8c72101efc6390867ffa9c8433dfd4e4219ffca7210cffd5390867bea9c8433ff14e42047fe87210cffe4390867fea1c8408ff10e4203dfcc52101fff529080fff2948407ff54a4203ff8a52101fff429080fdfa148408fbd0a4203ffe652101ffe329080ffe9948407ff0ca4203ffec32101ffe61908077f30c8407ff58642005fac32101ffc6190869ffa8c8434ff946421a7faa3210d3fc5190867ff98c8433ff8c64219ffa63210cffc319080fffb048407ff98242025fcc12101ffd60908017eb048407ff182421a7fea1210d3fe5090869fea848434ff1424219ffe61210cffe3090867fe9848433f
  | 10 => 0x48b6e0000001100e40506302877c8746dc14815ac9d635014e1da4a160002e884140904c11729e7482831923980005400000788fd80000000c500000005720cd9ebc8362931b61c080000001be17106f23a306c00d080825d1aa8b400006fc19c04c480e05d136020c3281470dd86982123fe40097fc8444262e517d0e266393f41e2057e7ed16d0000e9015d13514d0af8418024919482a7321b2800013c1840001a349467452d300000007630d4938c86000031419bccb814a3081a60c3214f04b08d0e9a70f00008142664c011581140042261701e2c9f841106f0c8c63e68523a0b10aa821335115c4e705951c596103421c60040a741f64fa0360cb82846902fba054f8081f0d5052c0001da23804b800013c29e02109d42f30bc89885d42f62699f986400f01558000e9c57b29c0f380007fe3c21078fbe81b18b82c8d4e67a38f1ed8428000316890001a01402c03a06200e00a00c01200a00401a00000000800000401401600002c03601c00000200002600800e00a01e00000c01400000800000600403400600001000800000400400400400000202400c00000601c01800200001c00600405a0000060000260000040000020a000a01400c01000000000001000208400c01e00400a01400200402e02202000803800203400602800200003400402a00601401200001600400a00000800400a04c00c01400000001001003402e03c0240000220080be00400001000800000601000402600600600000400201000000204200800800c00e02400001202e01602a00000001203000002208a00600000401200006e00c00000a00c01a00800c00400604202a00600601e00000c00202000200400001a00000203600200000001205400001600600c01201406800c00202000000604001206601a00000200200002402401200400600600404200600205800400000400203000403200000400001205c00000403000600800000600800004800200c04c00000000202601800201601602601802206a03a00403800a00607000400401400203804a01802c01c00403c00400800c01603c00e00000200401201600001e00200200002c01a01400201601804205e00003200000201e01a00e00200002200005400400405000a00205200801600400a00000c00000001400800000800400400000e01a00a00000000200801407600001a00200a00800800002e0000000360040000a800800200200a00000800200008000000000000805200600000001400200001400000400000000000001200200000c0be00000002e00000000800c00000400600000800c00a00400803802400201600600200e00200201403600200001200c00006a01000200401400400c01803c02800001801c00000000801a01600000c00607400200200400800a0a6000000032016
  | 11 => 0x900ee847485e17c2a21e9000078e4091a28cda7ea3d508ccda86d613806688060c919a0a3060e56336506380ee26d18181d84962e83b386484a875c35f1644aae1d92fb04fc22a0333951cac2f0652207a12c3385a92261c94a4633c1e38ec4d2a3bf08895b4f825862860f10e605262fa8350e1a6621ec125c5b20000000428c385bb1848a1c0004640f400000000003c316e0fa612c2d68600fac6042b48000c6800025c800011a000000000026e20400004d00004e72c58b04c425431a89830a5e2d61ad0a68e9e21c39a83a400000038b176cb3a6a10000e88e843880000d1800042100019dcdee27e20500008fa7d90000000da602b0c88388c4a3f93b58300b0a485000000098e78d163986909a0002701018396782171a07874e0380b1905c50235429093e0ee01a718721240007b42941df872468700006e4ab672e3458c48c905d80ad801c4b845a29283e0d54006081848835014815d8000ef480221680010522c33bf92a4bfc06b0958b7850869302b1068b1451e14f9900f782970fa1358d9c00030196e40007e23d48ba400038f2a91f3c2240e52b402f83ce4900a48d488548242728e447c21d800080681ac5ed20e9b5d02035e0518000e7417729599240002393f28ac85e250324c1da85a81c426d0c9c1a484326294d8cea3c10000e1c1ae76640c019d00e67c07319a456010234d02e84d244210199f8bdc19038517a41c62d800000000000000fd1994f36000310000000003e3dd000000000000002e0b1265f14a0000d6a4f906812f07e40000001a0c2de5b13b096004040002ec972cbc24fe00019d865a27b12318c49e23af3a00adce583483be83c8f282ee0000b6c8181d707e8e5c0fc3cc26305d89c222400000000000003500ab036220e13099c8bbc50d1ce025000056700003282a66d12660a600000000d298383e63ac00018bc21608902d93086e81ee0a3083c3126ff03f8ed503a00031600c41e800026b8e848026da0001a8c00024c10c9ac09ec03b0001ee06107893e701a46b01c32e306640000000001520afe0f70f017b00002592d7000000063b0000000fb00003409fb00000c51980000ea20b62312080a1457a23b000050a67f26d9c503f206233e9b480002d120b13ec0942440000000000000053013400000021a00000008522fc1f682102eb07d1a7832a4320b71dec4ce283100a13c31668c32d9ce414e27a1ca9e4847825523a82dcca63d139e1e3c9683df1c0949108e1d631713882bc3ad0de05d430a1161779b8404263334c8fa497a4ab0951fc0f667fc0ed8060a9424518818a400030d3281ab400017a103177c0007261ad8034fc800031e8f787aa36921c80001660000000000ce20001fa00000002dc2f5112902c84214480000f082c12f914c99a2410001598aaa6b200000003308174229c
  | 12 => 0x3040603331cc00d4b9c5fd200000037e59c0b81eac4927dc0001ee403200012c03f89e46c31f014c052257e1278dc10707ff254000103817e07607bcbd60043768728c881383d08c78fec01c31a9f10f6a6b42171aec7c646104e1e6832c385026122463a0532500c44000622145999c8824940548588c9c7933a51454f065940670be05427ac04405b4bae76205703b48880002d60cfc00051c37812984642d737d0df48d401f08d886005a3e61fe1b3070c3ba0000c2cfc00a000000000002ca3d4200027c0000001850ab42a632a0d08be45a70000000d847bd2c80000e521242e40aa846c71d0f8800076844701d12b075000031301400002c5000188c8b800000000010a00002d0015c000000331908cfb606e3ad0b98bcc0000d819b00006d519d11f106c4be0a9196000057d25d1edc9a84df0000ae00005140001f3090809333516d879221727a987c2d84ef030046892c11700012c400000023c91f844608715e1d40e480000000d3c51c5a13732130a4e6f600002300540f62c7800045c32f1bc0fe00003dd3e400584a63800660000f327cd0000bdc00072800003a8e2a8460000b88fea12d14500dc0000001038cc81226fb000000000000000009f07fa27501709e05f87950fc1d640005dd00008848b243f00000a000027919a80008580002d2000000066400016cceec00000000008f600020c800027407202a9aa48bc6c10698d5c71c09735880000000001a5800000026e3b6171400060a0000f209ee4b025d8a94f4e449363089c93c80400007408cc0052c71c682d07fb0e11cd800060133820d4b9a8231240080a6a0a41f40000a643cd0578000a2623a0000dad0765020001b9493200004d8000dd666b3a30db8a3045708c9f2c47a00008096bcac037e376166823c00011882fcc3c49b00a979007a3dc3440b843bc36726a97c489076e1250e68dde2990be800000065a165800000000000f0f94bd000012d8ad00000000000b388d00002598000e981e40001f5ce107bb3ac0c1104a5b40fb90f8b1a7a51a38da02b232c3541cfc00013d1ac86dcec800016309cc1546f12b70c007da12f38e183d00644611d86b804875d0a70498d240d51ca0b3c5f631b3bc02f445a82200007046986960d180000005820c9863c73e14431b1e4078a0a537a91388b07003e1154108070906881040644021570400b4a80e1d51404b3e40b409800000021a000123406c3f730ea0287147d11bd80a4a740cf1411b787a069736282e494218127400000001dc3e4921c0000eb1598000fba17b2720e35074000178118c1dc62a3ba11b101e0001850a3466e0612eb1630c6049a1bb2050b921d32cc96484de5170b59dc8e5e054135951862868900013a4e7c0ef34d9accb020002d1a02c3c632b072027504c56c3431c0474a85403a8b24f7c3
  | 13 => 0x50504500006ba07310912440004c82e3859042a0f53ea07ec3ec15726c8730ba07f7373800050c5493ce11b48a01eb0000000ab84721989f8c0007a02f018186e600003d89f4fdc06f31c192c5e40ab03282184e44f005a000000034a000000000045d000082c73c0002a719346820001e107f442c2421601e983c46a40c3031cd045e50000000ede7ae39b9294eda60041a0190ac85fb05d9fe091077715400006ee5d21f3934499e0003138c54d6c0001538e0800057700019a05fe22f1d20000be66f23ea805cc263ee06c9e14e960130f486b087839605080945847f42348a786f40100e4849c9447980618ec0da02641b6a0bc46e5703718e0cc30161128800000035631f85340003da28716accae2dd0000ae80003cf1081b64b7833e0fa9b24dd248f0860b20fde44f04012bcc2a04b0e69a700163b82e09b7c5a435c22b0e102ca7de28d9b900007103828f4cc1283e1ed80000284c9023156400053f03c8a90824362000000000000021b0000ef200042889386d40390278d980a46513839b2c78620840400004ae00041395083c206d0000240aba7520908e308f043d25515bc0002fd1d49a500000003f391c40006611ff86d8eea81134e88305ea0c21441ec04400f31a29f849fa5e302f93702b032237e85ccd7271825c03701ce02f1281c841f8427363951431a4e63b006ac0b25e719e8cd893e07c1588530dc44f43918ad87a4276393993100c5aa17d0edcba81510668bf8c8c773192129015a59700721041d021d2a7917c36820923d20f02ac13014b07980003d62a081f49003130e88000c2c09a13b9fcc0007a303d00004540001878f2800051900014f8c9e20d1949328cba00918604d40006db0dd164d06454d10516602b843b1a21b2055a071253847cd7e31c25a9f0d07a5533f484c8e5a3610879d10a220002e01bb837c7d03b42128b3c6c420482547c801d38f8160f3c4253c8a1386540000560a8c0006ea3fe8754eaa16032c9a002d26ba3e30c60d9e67828d1c642e86ab1ba88942e41201a714a439049c2b0a0e41904d00201d7814444523397542e218c2cd9fc833e123005022c91611c26e809cab047f36c02f0b6a23828b07c0e860cb37a147cf5a5cf0e005fd00a483176a06876c074370184473256510d8b7c1b43d407098dc96408f006191486e00021007946e41971180eec7e021f3b8800000075f1d31a7c59800000012549d80000e904a0a0e000000165909065e1e594b00000000491abcccc4513df8a8813e81921c2110000000246044c52432125b0000a6e39b3ad98905002f93530facef871b16680000002470b507c80cc222038000000002200008d40000002658fc400027400020b8c8e2b527f80009bc000000000000000033c9588a122be22580000004860018c58b446fe0001e1c0007f10838
  | 14 => 0x1090bf40f90000000ad42b900000004ca06829e970905460b0e393b40c6000215800000000000014b418c0001fd1b00b7482135b9cc46c625a0e7177000000000004a43da6f82c1974ca245000b31ec40003f300000b00006ac1f600003103530001e5c1fe45515e90a4e768333c0a0c107e66e14a8a3c78c3430118d3497e19d2e199580000110540000a1e0000000dc47ae1a4415800028a10d1341ba00000b12571578ce845b1b21af098850408215e44ac70408c06787402f40e280000006dd04716fc47e2d30091134e7a3ab2989c3800014002e00000003d900003100006a52f8020443c3601d990400d404418d18200a20001000000a760000d980f00008531f50000e0c2110001b34b600001290554d2257608a0000d707530f614880000002ba19eceae60d09c80004fe260088000030e7341df000000000030b9a38e8e0002378000bf800013198ac0004ee2a0000080a75628e8000f8e2e431f000086636f0001c5d0620003c011ac306000176057ca204353fd152c26c00032a903809c7331ce9af48c057824900008ee5b2000043849a4ad3860e4cf145da0a18d244bc01b19286880868372971730c841bd2c404947121ff1bf9788b507eb0d002c09b054704c98e82821fc1f10cec7806ae2b986b447c49d37c8c087f678c1739c88fa422900795d416a0002f7800064c05a18314e48500002371d509866431218fd491c82d32519cc92663c0000000000000000155888650829000008101b80ad1e885aa0002fc96f87780003fc92286507960000a6c68079f3190418e0622c00012046720002411d941ba1fe000000055e82822a0d7c75c1cf06d80fd01816720e00002a00000001a3ca980000c100000000004068000000000301133835e0002c38000e8200000015440bc6600001f2800000000020240003bd0701a1083e0001330000de67c506f92dc36400029504ecf642a938580007644d20aa1d241300002af98488a461b02107a804c3ef2068c141043b90ea08a0a660470da90c4e226412de93cc82660718089c410a
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7098810026ef5098810026ee5098810026ed5098810026ec5098810026ef4098810026ee4098810026ed4098810026ec4098810026ef3098810026ee3098810026ed3098810026ec3098810026ef1098810026ee1098810026ed1098810026ec1098810004ff7558810014fe7558810004fd7558810014fc7558810004ff7458810044fc7458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d5358810024ff7258810026ef7258810006ef5258810006ee5258810006ed5258810006ec5258810006ef3258810006ee3258810006ed3258810006ec325881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026f51058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881001eef715881001eee715881001eed715881001eec715881001eef515881001eee515881001eed515881001eec515881001eef415881001eee415881001eed415881001eec415881001eef315881001eee315881001eed315881001eec3158810026ef7058810026ee7058810026ed7058810026ec7058810026ef5058810026ee5058810026ed5058810026ec5058810026ef4058810026ee4058810026ed4058810026ec4058810026ef3058810026ee3058810026ed3058810026ec3058810026ef1058810026e71058810026ee1058810026ed1058810026e51058810026ec1058810044ff76d0810024fe76d0810004fd76d0810024fc76d08101b67e65d08100067d65d0810046be64d0810006bd64d08101aede63d0810006dd63d081003eee62d0810006ed62d081003cff7690810024fe7690810004fd7690810024fc76908101a67e65908100067d6590810046be6490810006bd649081019ede6390810006dd639081003eee6290810006ed6290810004ff7650810024fe7650810004fd7650810024fc76508100057f75508100357c75508101967e65508100067d6550810046be6450810006bd645081018ede6350810006dd635081003eee6250810006ed6250810005fb7050810025f8705081003cff7610810024fe7610810004fd7610810024fc76108100357e75108100057d75108101867e65108100067d6510810046be6410810006bd641081017ede6310810006dd631081003eee6210810006ed6210810
  | 1 => 0x9010024fc7059010026be4059010026bc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901001ebf715901001ebe715901001ebd715901001ebc715901001ebf515901001ebe515901001ebd515901001ebc515901001ebf315901001ebe315901001ebd315901001ebc315901001ebf215901001ebe215901001ebd215901001ebc2159010026bf7059010026be7059010026bd7059010026bc7059010026bf5059010026be5059010026bd5059010026bc5059010026bf3059010026be3059010026bd3059010026bc3059010026bf2059010026be2059010026bd2059010026bc2059010026bf1059010026be1059010026bd1059010026bc1059010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c1001edf7158c1001ede7158c1001edd7158c1001edc7158c1001edf5158c1001ede5158c1001edd5158c1001edc5158c1001edf4158c1001ede4158c1001edd4158c1001edc4158c1001edf2158c1001ede2158c1001edd2158c1001edc2158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de5058c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc2058c10026df1058c10026de1058c10026da1058c10026dd1058c1001ed91058c10026dc1058c1003eef759881003eee759881003eed759881003eec759881003eef749881003eee749881003eed749881003eec7498810006ef5498810006ee5498810006ed5498810006ec549881003eef739881003eee739881003eed739881003eec7398810006ef53988100066f5398810006ee5398810006ed53988100066d5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec439881001eef719881001eee719881001eed719881001eec719881001eef519881001eee519881001eed519881001eec519881001eef419881001eee419881001eed419881001eec419881001eef319881001eee319881001eed319881001eec3198810026ef7098810026ee7098810026ed7098810026e
  | 2 => 0x3eec62c811001df671c8110005f571c8110007e521c811003cff7648110004fd764811001cfc76481100057f75481100557c75481100067f65481100967c6548110005bf7448110005bc7448110006bf6448110006bc6448110006ef624811003eec6248110005f7714811001df47148110007e521481100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f32594100067e32594100067d32594100067c325941001e7f715941001e7e715941001e7d715941001e7c715941001e7f415941001e7e415941001e7d415941001e7c415941001e7f315941001e7e315941001e7d315941001e7c315941001e7f215941001e7e215941001e7d215941001e7c21594100267f70594100267e70594100267d70594100267c70594100267f40594100267e40594100267d40594100267c40594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267e10594100267d10594100267c1059410046bf7599010046be7599010046bd7599010046bc7599010046bf7399010046be7399010046bd7399010046bc7399010006bf53990100063f5399010006be5399010006bd53990100063d5399010006bc5399010046bf7299010046be7299010046bd7299010046bc7299010006bf5299010006be5299010006bd5299010006bc5299010006bf3299010006be3299010006bd3299010006bc329901001ebf719901001ebe719901001ebd719901001ebc719901001ebf519901001ebe519901001ebd519901001ebc519901001ebf319901001ebe319901001ebd319901001ebc319901001ebf219901001ebe219901001ebd219901001ebc2199010026bf7099010026be7099010026bd7099010026bc7099010026bf5099010026be5099010026bd5099010026bc5099010026bf3099010026be3099010026bd3099010026bc3099010026bf2099010026be2099010026bd2099010026bc2099010026bf1099010026be1099010026bd1099010026bc1099010004ff7559010014fe7559010004fd7559010014fc7559010024ff7459010026bf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff735901000cfe7359010004fd735901000cfc73590100067f53590100067d5359010006bf4359010006be4359010006bd4359010006bc4359010004ff725901003cfc725901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc4159010024ff7059010024fe7059010024fd705
  | 3 => 0xa3058910006f93058910004fe76189100067f65189100067c6518910006bf6418910006bc641891003eee6218910006ed6218910044ff76d0910004fe76d0910004fd76d0910044fc76d09100067f65d09101b67c65d0910006bf64d0910046bc64d091003cff7690910004fe7690910004fd769091003cfc76909100067f65909101a67c6590910006bf6490910046bc649091001df67190910005f57190910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100557c75509100067f65509101967c6550910006bf6450910046bc645091003cff7610910004fe7610910004fd761091003cfc76109100557e75109100057d75109100067f65109101867c6510910006bf6410910046bc641091001df67110910005f57110910025fa7010910005f97010910024fe76d0510024fc76d05100067f65d05101767c65d0510006bf64d0510046bc64d0510025fa70d0510005f970d0510024fc76505100057f75505100557c75505100067f65505101567c6550510006bf6450510046bc6450510005fb7050510025f8705051001ff01050510024fe76c8510024fc76c85100557e75c85100057d75c85100067f65c85101367c65c8510005be74c8510005bd74c8510006bf64c8510006bc64c8510006ef62c851003eec62c8510025fa70c8510005f970c8510005f6768851001ef6768851001f76758851001f7575885100077765885101df74658851001fb6748851001fb57488510007b76488510007b464885101cef763885101cef563885101cf7753885101cf7553885101d5f5728851003ef6628851003ef46288510025f67088510025f4708851001ef7608851001ff360885101cff230885101cff13088510024fc76485100067f65485101167c6548510006bf6448510006bc6448510006ef624851003eec624851001fe42148510005fb7048510025f87048510025f4764851003ef47648510024f476485100077765485101c7746548510007b76448510007b464485101bef763485101bef563485101bf7753485101bf75534851001df7724851001fe77248510007e7624851003ef6624851003ef46248510007e4624851003ee462485101bfe632485101bfe53248510007f37048510025f67048510025f47048510007f0704851001ef7604851001ff360485101bff230485101bff1304851001cfe76d011001cfc76d01100557e75d01100057d75d01100067f65d01100f67c65d0110006bf64d0110046bc64d011001df671d0110005f571d0110044ff7650110004fd765011001cfc76501100067f65501100d67c6550110006bf6450110046bc6450110005f7715011001df47150110027f0105011001cfe76c811001cfc76c81100067f65c81100b67c65c8110006bf64c8110006bc64c8110006ef62c8110
  | 4 => 0x911000cfc73591100067f53591100067d5359110004ff725911003cfc7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c6519110046be6419110006bd6419110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100073f53191100073d5319110007ba3019110007b930191101efbb10191101e7b610191101e7b410191101efb81019110046bf7519110046be7519110046bd7519110046bc7519110046bf7319110046be7319110046bd7319110046bc7319110006bf53191100063f5319110006be5319110006bd53191100063d5319110006bc5319110046bf7219110046be7219110046bd7219110046bc7219110006bf5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bd3219110006bc3219110046bf7119110046be7119110046bd7119110046bc7119110006bf51191101eebe5119110006bd51191101eebc5119110006bf31191101eebe3119110006bd31191101eebc31191101eebe21191101eebc2119110046bf7019110046be7019110046bd7019110046bc7019110006bf50191101e6be5019110006bd50191101e6bc5019110006bf30191101e6be3019110006ba3019110006bd3019110006b930191101e6bc30191101e6be20191101e6bc20191101eebf10191101e6be1019110006bd10191101e6bc101911003cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910004ff75d8910014fe75d8910004fd75d8910014fc75d8910044fe74d8910004fd74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006ef32d8910006ec32d891001cfe71d891001cfc71d8910024fe70d8910024fc70d8910006fa30d8910006f930d89100557e75989100057d75989100067f65989100067c6598910005be7498910005bd7498910006bf6498910006bc6498910006ef62989100057f75589100557c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df735891004ddc7358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf7458910044fc7458910006bc7458910044bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910006f
  | 5 => 0x47f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067d32d95100067c32d95102067f71d951020e7e71d95100567d71d951020e7c71d951020e7e41d951020e7c41d95100067f31d951020e7e31d95100067d31d951020e7c31d951020e7e21d951020e7c21d951020e7f70d95102067e70d95100567d70d95102067c70d95102067e40d95102067c40d95100067f30d95102067e30d95100067d30d95102067c30d95102067e20d95102067c20d951020e7f10d95102067e10d95100567d10d95102067c10d9510044fe76d91100067f65d91100067c65d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d91100067f53d91100067d53d9110006bf43d9110006be43d9110006bd43d9110006bc43d911003cfe72d9110004fd72d911001cfe71d911001cfc71d9110024fe70d9110024fc70d9110044be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100073f53d91100073d53d9110007ba30d9110007b930d91101ffbb10d91101f7b610d91101f7b410d91101ffb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91101f6bf71d91101febe71d9110006bd71d91101febc71d9110006bf51d91101febe51d9110006bd51d91101febc51d9110006bf31d91101febe31d9110006bd31d91101febc31d91101febe21d91101febc21d91101febf70d91101f6be70d9110006bd70d91101f6bc70d9110006bf50d91101f6be50d9110006bd50d91101f6bc50d9110006bf30d91101f6be30d9110006bd30d91101f6bc30d91101f6be20d91101f6bc20d91101febf10d91101f6be10d91101f6bc10d91100557e75991100057d75991100067f65991100067c6599110006bf64991100057f75591100557c75591100067f65591100067c6559110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf7459110004ff735911000cfe7359110004fd735
  | 6 => 0xf7610b1001cfe7610b10004fd7610b1001cfc7610b100757e7510b100057d7510b10046be6410b10006bd6410b1001df67110b10005f57110b1001df77648710006f7764871001ef76348710226f5634871022777534871022775534871001fe7724871001fe7624871003ef6624871001ef4624871001fe4624871001ee46248710227e63248710227e53248710025f67048710025f470487100757e75d03100057d75d0310046be64d0310006bd64d031001df671d0310005f571d0310044ff7650310046be6450310006bd6450310005f7715031001df4715031003eee62c8310006ed62c831001df671c8310005f571c8310007e521c831003cff76483100057f75483100757c7548310005bf7448310005bc744831003eee6248310006ed6248310005f7714831001df47148310007e52148310004ff7559210014fe7559210004fd7559210014fc7559210026bf7459210004ff735921000cfe7359210004fd735921000cfc73592100067f53592100067d5359210004ff725921003cfc7259210024fc7059210026be4059210026bc4059210004ff7558a100067f7558a100047f7558a10014fe7558a10004fd7558a10014fc7558a100067c7558a100147c7558a10004ff7458a10006bf7458a10004bf7458a10044fc7458a10006bc7458a10044bc7458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a100067f5358a100067d5358a10026ef7258a10024fc7058a10026fa3058a10006f93058a10026ee2058a10026ec2058a10026f71058a10026f51058a10044ff76d0a10024fe76d0a10004fd76d0a10024fc76d0a10046be64d0a10006bd64d0a1003cff7690a10024fe7690a10004fd7690a10024fc7690a1021ebf6490a10046bc6490a10004ff7650a10024fe7650a10004fd7650a10024fc7650a100057f7550a100657c7550a10046be6450a10006bd6450a1003cff7610a10024fe7610a10004fd7610a10024fc7610a100657e7510a100057d7510a10216bf6410a10046bc6410a10025fa7010a10005f97010a10046be64d0610006bd64d0610025fa70d0610005f970d0610044ff76506100057f75506100657c7550610046be6450610006bd6450610005fb7050610025f870506100657e75c86100057d75c8610005be74c8610005bd74c861003eee62c8610006ed62c8610025fa70c8610005f970c861003cff764861003eee6248610006ed624861001fe42148610005fb7048610025f870486100557e76d95100567e76d95100147e76d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100077a30d95100077930d951020f7b10d95102077610d95102077410d951020f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d9510
  | 7 => 0x8420006f75458420006f65458420006f55458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006775358420006f65358420006f55358420006755358420006f45358420006f74358420006f64358420006f54358420006f4435842003ef7725842003ef6725842003ef4725842003ef7525842003ef6525842003ef5525842003ef4525842003ef7425842003ef6425842003ef5425842003ef4425842003ef7325842003ef6325842003ef5325842003ef43258420026f77058420026f67058420026f47058420026f75058420026f65058420026f55058420026f45058420026f74058420026f64058420026f54058420026f44058420026f73058420026f63058420026f53058420026f43058420026f72058420026e72058420026f62058420026f52058420026e52058420026f42058420044ff76d0420024fe76d0420004fd76d04201767e65d04200067d65d0420046be64d0420006bd64d042016ede63d0420006dd63d042001ef661d0420006f561d042001cff7690420024fe7690420004fd76904201667e65904200067d6590420046be6490420006bd649042015ede6390420006dd639042001ef66190420006f56190420004ff7650420004fd7650420024fc76504200057f75504200857c75504201567e65504200067d6550420046be6450420006bd645042014ede6350420006dd635042001ef66150420006f56150420005fb7050420025f8705042001cff7610420024fe7610420004fd76104200857e75104200057d75104201467e65104200067d6510420046be6410420006bd641042013ede6310420006dd631042001ef66110420006f56110420004ff75593100067f75593100047f7559310014fe7559310004fd7559310014fc75593100067c75593100147c755931001ebf7459310006be5459310006bd5459310004ff735931000cfe7359310004fd735931000cfc73593100067f53593100067d5359310006bf4359310006bd4359310004ff725931003cfc7259310024fc715931001ebe415931001ebc4159310004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b10044fc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b1001eef7258b10006ee3258b10006ed3258b10024fc7158b1001eee2158b1001eec2158b10044ff76d0b1001cfe76d0b10004fd76d0b1001cfc76d0b10236bf64d0b10046bc64d0b1003cff7690b1001cfe7690b10004fd7690b1001cfc7690b10046be6490b10006bd6490b1001df67190b10005f57190b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b100057f7550b100757c7550b1022ebf6450b10046bc6450b10005fb7050b10025f87050b1003cf
  | 8 => 0x26bf3059020026be3059020026bd3059020026bc3059020026bf2059020026be2059020026bd2059020026bc2059020026bf1059020026be1059020026bd1059020026bc1059020006df7558c20006de7558c200065e7558c20006dd7558c200065d7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006de5458c20006dd5458c20006dc5458c2003edf7258c2003ede7258c2003edd7258c2003edc7258c2003edf5258c2003ede5258c2003edd5258c2003edc5258c2003edf4258c2003ede4258c2003edd4258c2003edc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c20006de5158c20006dd5158c20006dc5158c2003edf2158c2003ede2158c2003edd2158c2003edc2158c20026df7058c20026de7058c20026dd7058c20026dc7058c20026df5058c20026de5058c20026dd5058c20026dc5058c20026df4058c20026de4058c20026dd4058c20026dc4058c20026df2058c20026de2058c20026da2058c20026dd2058c2003ed92058c20026dc2058c20026df1058c20026de1058c20026dd1058c20026dc1058c2001ef7759842001ef6759842001ef5759842001ef4759842001ef7749842001ef6749842001ef5749842001ef47498420006f75498420006f65498420006f55498420006f4549842001ef7739842001ef6739842001ef5739842001ef47398420006f75398420006775398420006f65398420006f55398420006755398420006f45398420006f74398420006f64398420006f54398420006f4439842001ef7729842001ef6729842001ef5729842001ef4729842003ef7529842003ef6529842003ef5529842003ef4529842003ef7429842003ef6429842003ef5429842003ef4429842003ef7329842003ef6329842003ef5329842003ef43298420026f77098420026f67098420026f57098420026f47098420026f75098420026f65098420026f55098420026f45098420026f74098420026f64098420026f54098420026f44098420026f73098420026f63098420026f53098420026f43098420026f72098420026f62098420026f52098420026f42098420004ff7558420014fe7558420004fd7558420014fc7558420004ff7458420044fc7458420004ff735842000cfe7358420004fd735842000cfc73584200067f53584200067d5358420026f77158420006f75158420006f65158420006f55158420006f45158420006f73158420006f63158420006f53158420006f4315842003ef7215842003ef42158420024ff7058420024fd7058420026ef2058420026ed2058420026f61058420026f41058420006f77558420006f67558420006f57558420006f47558420006f77458420006f67458420006f57458420006f4745
  | 9 => 0xe31594200067d31594200067c315942003e7f215942003e7e215942003e7d215942003e7c21594200267f70594200267e70594200267d70594200267c70594200267f40594200267e40594200267d40594200267c40594200267f30594200267e30594200267d30594200267c30594200267f20594200267e20594200267d20594200267c20594200267f10594200267e10594200267d10594200267c1059420046bf7599020046be7599020046bd7599020046bc7599020046bf7399020046be7399020046bd7399020046bc7399020006bf53990200063f5399020006be5399020006bd53990200063d5399020006bc539902003ebf729902003ebe729902003ebd729902003ebc729902003ebf529902003ebe529902003ebd529902003ebc529902003ebf329902003ebe329902003ebd329902003ebc3299020046bf7199020046be7199020046bd7199020046bc7199020006bf5199020006be5199020006bd5199020006bc5199020006bf3199020006be3199020006bd3199020006bc319902003ebf219902003ebe219902003ebd219902003ebc2199020026bf7099020026be7099020026bd7099020026bc7099020026bf5099020026be5099020026bd5099020026bc5099020026bf3099020026be3099020026bd3099020026bc3099020026bf2099020026be2099020026bd2099020026bc2099020026bf1099020026be1099020026bd1099020026bc1099020004ff7559020014fe7559020004fd7559020014fc7559020024ff7459020026bf7459020006bf5459020006be5459020006bd5459020006bc5459020004ff735902000cfe7359020004fd735902000cfc73590200067f53590200067d5359020006bf4359020006be4359020006bd4359020006bc435902003cff725902003cfe725902003cfd725902003cfc725902003ebe425902003ebc4259020004ff715902001cfc7159020024fe7059020024fc7059020026be4059020026bc4059020006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf53590200063f5359020006be5359020006bd53590200063d5359020006bc535902003ebf725902003ebe725902003ebd725902003ebc725902003ebf525902003ebe525902003ebd525902003ebc525902003ebf325902003ebe325902003ebd325902003ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006be5159020006bd5159020006bc5159020006bf3159020006be3159020006bd3159020006bc315902003ebf215902003ebe215902003ebd215902003ebc2159020026bf7059020026be7059020026bd7059020026bc7059020026bf5059020026be5059020026bd5059020026bc5059020
  | 10 => 0x8520006bc6458520005df735852008ddc73585200067f65185200067c6518520006bf6418520006bc641852001ef66118520006f56118520004fe76d0520004fd76d0520044fc76d05200067f65d05201767c65d0520006bf64d0520046bc64d0520004fe7690520004fd769052001cfc76905200067f65905201667c6590520006bf6490520046bc649052003dee7290520005ed7290520004ff7650520004fe7650520004fc76505200057f75505200957c75505200067f65505201567c6550520006bf6450520046bc6450520004fe7610520004fd761052001cfc76105200957e75105200057d75105200067f65105201467c6510520006bf6410520046bc641052003dee7210520005ed7210520025fa7010520005f97010520005ee76c852003eee76c852003f6e75c852003f6d75c85200076f65c852025f6c65c852003fae74c852003fad74c8520007af64c8520007ac64c8520256ef63c8520256ed63c85202576f53c85202576d53c852001eee61c852001eec61c8520025ee70c8520025ec70c852003eef60c852003feb60c8520257ea30c8520257e930c8520024fe76885200957e75885200057d75885200067f65885201267c6588520005be7488520005bd7488520006bf6488520006bc648852024ded7288520006f7618852001ef46188520025fa7088520005f97088520024fc76485200067f65485201167c6548520006bf6448520006bc6448520006f7614852001ef4614852003fe42148520005fb7048520025f87048520024ec76485200076f65485202476c6548520007af6448520007ac644852023eef634852023eed634852023f6f534852023f6d534852003def714852003fe77148520007e7614852001eee614852001eec6148520007e4614852001ee4614852023fe6314852023fe53148520007eb7048520025ee7048520025ec7048520007e8704852003eef604852003feb604852023fea304852023fe9304852003cfe76d012003cfc76d01200957e75d01200057d75d01200067f65d01200f67c65d0120006bf64d0120046bc64d012003dee72d0120005ed72d0120044ff7650120004fd765012003cfc76501200067f65501200d67c6550120006bf6450120046bc6450120005ef725012003dec7250120027e820501200067f74594200067e74594200067d74594200067c74594200067f73594200047f73594200067e73594200067d73594200047d73594200067c73594200067f43594200067e43594200067d43594200067c435942003e7f725942003e7e725942003e7d725942003e7c725942003e7f425942003e7e425942003e7d425942003e7c425942003e7f325942003e7e325942003e7d325942003e7c32594200067f71594200067e71594200067d71594200067c71594200067f31594200067
  | 11 => 0x67c6599120006bf64991200057f75591200957c75591200067f65591200067c6559120004ff75591200067f75591200047f7559120014fe7559120004fd7559120014fc75591200067c75591200147c7559120006bf7459120004ff735912000cfe7359120004fd735912000cfc73591200067f53591200067d5359120004ff7259120006ef7259120004ff715912001cfc7159120004ff7059120006fb7059120004fe76191200067f65191200067c6519120046be6419120006bd6419120005be7619120006be7619120004be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c6519120006bf6319120006be6319120006bd6319120006bc63191200073f53191200073d5319120007ba3019120007b93019120267bb2019120217ae2019120217ac2019120267b82019120046bf7519120046be7519120046bd7519120046bc7519120046bf7319120046be7319120046bd7319120046bc7319120006bf53191200063f5319120006be5319120006bd53191200063d5319120006bc5319120046bf7219120046be7219120046bd7219120046bc7219120006bf5219120266be5219120006bd5219120266bc5219120006bf3219120266be3219120006bd3219120266bc3219120046bf7119120046be7119120046bd7119120046bc7119120006bf5119120006be5119120006bd5119120006bc5119120006bf3119120006be3119120006bd3119120006bc3119120266bf2119120266bc2119120046bf7019120046be7019120046bd7019120046bc7019120006bf5019120216be5019120006bd5019120216bc5019120006bf3019120216be3019120006ba3019120006bd3019120006b93019120216bc3019120266bf2019120216be2019120006bd2019120216bc2019120216be1019120216bc1019120024fe76d0920024fc76d09200067f65d09201b67c65d0920006bf64d0920046bc64d0920025fa70d0920005f970d0920024fc76509200057f75509200957c75509200067f65509201967c6550920006bf6450920046bc6450920005fb7050920025f8705092003fe820509200067f65d85200067c65d8520006bf64d8520006bc64d8520004ff75d8520014fe75d8520004fd75d8520014fc75d8520044fe74d8520004fd74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d8520006f731d8520006f431d8520024fe70d8520024fc70d8520006fa30d8520006f930d85200957e75985200057d75985200067f65985200067c6598520005be7498520005bd7498520006bf6498520006bc6498520006f761985200057f75585200957c75585200067f65585200067c6558520005bf7458520005bc7458520006bf645
  | 12 => 0xe76d95200967e76d95200147e76d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200077a30d95200077930d952027f7b20d95202776e20d95202776c20d952027f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95202767f72d952027e7e72d95200967d72d952027e7c72d952027e7e42d952027e7c42d95200067f32d952027e7e32d95200067d32d952027e7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d952027e7f21d952027e7c21d952027e7f70d95202767e70d95200967d70d95202767c70d95202767e40d95202767c40d95200067f30d95202767e30d95200067d30d95202767c30d952027e7f20d95202767e20d95200967d20d95202767c20d95202767e10d95202767c10d9520044fe76d91200067f65d91200067c65d9120004ff75d9120014fe75d9120004fd75d9120014fc75d9120006bf54d9120006be54d9120006bd54d9120006bc54d9120004ff73d912000cfe73d9120004fd73d912000cfc73d91200067f53d91200067d53d9120006bf43d9120006be43d9120006bd43d9120006bc43d912003cfe72d912003cfc72d912001cfe71d9120004fd71d9120044be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006bf63d9120006be63d9120006bd63d9120006bc63d91200073f53d91200073d53d9120007ba30d9120007b930d912026fbb20d912021fae20d912021fac20d912026fb820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d91200063f53d9120006be53d9120006bd53d91200063d53d9120006bc53d912021ebf72d912026ebe72d9120006bd72d912026ebc72d9120006bf52d912026ebe52d9120006bd52d912026ebc52d9120006bf32d912026ebe32d9120006bd32d912026ebc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006be31d9120006bd31d9120006bc31d912026ebf21d912026ebc21d912026ebf70d912021ebe70d9120006bd70d912021ebc70d9120006bf50d912021ebe50d9120006bd50d912021ebc50d9120006bf30d912021ebe30d9120006bd30d912021ebc30d912026ebf20d912021ebe20d912021ebc20d912021ebe10d912021ebc10d91200957e75991200057d75991200067f6599120
  | 13 => 0x932001cfc7159320004ff7558720014fe7558720004fd7558720014fc7558720004ff7458720044fc7458720004ff735872000cfe7358720004fd735872000cfc73587200067f53587200067d5358720024fc725872003ef77158720006f63158720006f5315872003ef7215872003ef42158720044ff76d072003cfe76d0720004fd76d0720296bf64d0720046bc64d072001cff769072003cfe7690720004fd7690720046be6490720006bd649072003dee7290720005ed7290720004ff7650720004fd765072003cfc76507200057f75507200b57c755072028ebf6450720046bc6450720005fb7050720025f8705072001cff761072003cfe7610720004fd76107200b57e75107200057d7510720046be6410720006bd641072003dee7210720005ed721072003def7648720006ef764872003eef6348720286ed63487202876f53487202876d534872003fe7714872003fe7614872001eee614872001eec614872003fe46148720287e63148720287e53148720025ee7048720025ec70487200b57e75d03200057d75d0320046be64d0320006bd64d032003dee72d0320005ed72d0320044ff7650320046be6450320006bd6450320005ef725032003dec7250320004ff7559220014fe7559220004fd7559220014fc7559220026bf7459220004ff735922000cfe7359220004fd735922000cfc73592200067f53592200067d5359220004ff715922001cfc7159220024fc7059220026be4059220026bc4059220046be64d0a20006bd64d0a20025fa70d0a20005f970d0a20044ff7650a200057f7550a200a57c7550a20046be6450a20006bd6450a20005fb7050a20025f87050a20004ff75586200067f75586200047f7558620014fe7558620004fd7558620014fc75586200067c75586200147c7558620004ff7458620006bf7458620004bf7458620044fc7458620006bc7458620044bc7458620004ff735862000cfe7358620004fd735862000cfc73586200067f53586200067d5358620026f77158620024fc7058620026fa3058620006f93058620026ef2058620026ed2058620026f61058620026f41058620044ff76d0620024fe76d0620004fd76d0620046be64d0620006bd64d062001cff7690620024fe7690620004fd76906201f6bf6490620046bc6490620004ff7650620004fd7650620024fc76506200057f75506200a57c7550620046be6450620006bd645062001cff7610620024fe7610620004fd76106200a57e75106200057d75106201e6bf6410620046bc6410620025fa7010620005f970106200a57e75886200057d7588620005be7488620005bd748862001ef66188620006f56188620025fa7088620005f9708862001cff764862001ef66148620006f5614862003fe42148620005fb7048620025f870486200957
  | 14 => 0x5f97008540004ff75588400067f75588400047f7558840014fe7558840004fd7558840014fc75588400067c75588400147c7558840046be5458840006bd5458840004ff735884000cfe7358840004fd735884000cfc73588400067f53588400067d5358840046bf4358840006bd4358840026ef7258840006ee5258840006ed5258840046ef4258840046bc4258840046ec4258840006ee3258840006ed3258840004ff715884001cfc7158840046bc4158840026bf4058840026bd4058840026fa3058840006f93058840026ee2058840026ec2058840045bd7690840266bd7690840004bd7690840265bf75908402c5bd7590840265bf73908402bdbd73908402b73f53908402b73d5390840045be7290840047ae7290840046bf6290840266bd62908401edbe719084021dbf709084021dbd709084021ebe6090840047ba609084021fba30908402b7b93090840004ff75584400067f75584400047f7558440014fe7558440004fd7558440014fc75584400067c75584400147c7558440046be5458440006bd5458440004ff735844000cfe7358440004fd735844000cfc73584400067f53584400067d5358440046bf4358440006bd4358440004ff725844003cfc7258440006be4258440046bc4258440026f77158440006f65158440006f55158440046f74158440046bc4158440046f44158440006f63158440006f53158440026bf4058440026bd4058440026fa3058440006f93058440026f61058440026f41058440045bd76904401eebd7690440004bd76904401edbf75904402adbd75904401edbf73904402a5bd739044029f3f539044029f3d5390440265be7290440006bd6290440045be7190440047b67190440046bf61904401eebd61904401f5bf70904401f5bd70904401f6be6090440047ba60904401f7ba309044029fb9309044003cff76c8440024fe76c8440004fd76c84400c57e75c84400057d75c8440045be74c8440005bd74c844003eee62c8440006ed62c844001cff7688440024fe7688440004fd76884400c57e75884400057d7588440045be7488440005bd748844001ef66188440006f56188440004ff7648440004fd7648440024fc7648440005bf7448440045bc744844003eee6248440006ed624844001ef66148440006f56148440005fb7048440025f8704844001cff7608440024fe7608440004fd76084401edbf7408440045bc7408440007e52108440004ff75593200067f75593200047f7559320014fe7559320004fd7559320014fc75593200067c75593200147c755932003ebf7459320006be5459320006bd5459320004ff735932000cfe7359320004fd735932000cfc73593200067f53593200067d5359320006bf4359320006bd4359320024fc725932003ebe425932003ebc4259320004ff715
  | 15 => 0xc75d8940004ff73d894000cfe73d8940004fd73d894000cfc73d89400067f53d89400067d53d894001cfe71d8940004fd71d894021ebf6498940006ef62989400057f75589400d57c75589400d57e75189400057d7518940216bf641894003eee6218940006ed6218940005be76d0940046be76d0940004be76d0940316bf65d0940316bd65d094030ebf63d094030ebd63d094030f3f53d094030f3d53d094003ebe62d094003ebc62d0940005bd71d0940236bc61d0940025be70d0940025bc70d0940046bf60d0940047bb60d0940024fe7690940305bd7490940006ef629094003eec6290940025fa7090940005f97090940024fc76509400057f75509400d57c7550940006ef625094003eec6250940005fb7050940025f87050940024bc76509400073f75509402ff3c75509402febf65509402febd65509402f6bf63509402f6bd63509402f73f53509402f73d5350940045bf7250940047af7250940007af625094003ebe625094003ebc6250940007ac6250940005bf715094022ebc6150940007bb7050940025be7050940025bc7050940007b87050940046bf6050940047bb6050940004ff75d8540014fe75d8540004fd75d8540014fc75d8540004ff73d854000cfe73d8540004fd73d854000cfc73d85400067f53d85400067d53d854003cfe72d8540004fd72d85401f6bf6498540006f761985400057f75585400d57c75585400d57e75185400057d75185401e6bf641854001ef66118540006f56118540005be76d0540046be76d0540004be76d05402eebf65d05402eebd65d05402e6bf63d05402e6bd63d05402e73f53d05402e73d53d0540005bd72d0540296bc62d054001ebe61d054001ebc61d0540025be70d0540025bc70d0540046bf60d0540047bb60d0540024fe76905402ddbd7490540006f7619054001ef46190540025fa7090540005f97090540024fc76505400057f75505400d57c7550540006f7615054001ef46150540005fb7050540025f87050540024bc76505400073f75505402d73c75505402d6bf65505402d6bd65505402cebf63505402cebd63505402cf3f53505402cf3d5350540005bf725054028ebc6250540045bf7150540047b77150540007b7615054001ebe615054001ebc6150540007b46150540007bb7050540025be7050540025bc7050540007b87050540046bf6050540047bb6050540004fe76c8540004fd76c854003cfc76c85400d57e75c85400057d75c8540045be74c8540005bd74c8540004fe7688540004fd768854001cfc76885400d57e75885400057d7588540045be7488540005bd7488540004ff7648540004fe7648540004fc7648540045be7448540005bd7448540004fe7608540004fd760854001cfc7608540045be7408540005bd7408540007e52108540025fa7008540
  | 16 => 0xa400067d6550a4018ede6350a40006dd6350a4003eee6250a40006ed6250a40005fb7050a40025f87050a40215bd7610a40046bd7610a40045bf7510a400473e7510a4035dbd7510a400473d7510a400053d7510a402173e6510a402173d6510a40045bf7310a40355bd7310a402179e6310a402179d6310a4034f3f5310a4034f3d5310a40047ae7210a40216bf6210a4026ebd6210a401fdbe7110a40045bf7010a40215bd7010a40047ba6010a40004ff7558640014fe7558640004fd7558640014fc7558640006be5458640006bd5458640004ff735864000cfe7358640004fd735864000cfc73586400067f53586400067d5358640006bf4358640006bd4358640004ff725864003cfc7258640006be4258640006bc4258640026f77158640024fc7058640026bf4058640026bd4058640026f61058640026f410586401667e65906400067d659064015ede6390640006dd639064001ef66190640006f56190640025fa7090640005f970906401fdbf7590640345bd75906401f73e65906401f73d65906401fdbf739064033dbd73906401f79e63906401f79d63906403373f53906403373d539064026dbe7290640006bd6290640045be71906401f6bf61906401f7b661906401febd61906401f7b561906401f7ba70906401f5bd70906401ffb97090640046be609064001cff76506400057f75506400e57c75506401567e65506400067d655064014ede6350640006dd635064001ef66150640006f56150640005fb7050640025f870506401e5bd7610640046bd7610640045bf75106400473e751064032dbd75106400473d75106400053d75106401e73e65106401e73d6510640045bf7310640325bd73106401e79e63106401e79d631064031f3f531064031f3d531064026dbe7210640006bd6210640047b671106401e6bf61106401febd6110640045bf70106401e5bd7010640047ba601064003cff76c8640024fe76c8640004fd76c86400e57e75c86400057d75c86401367e65c86400067d65c8640045be74c8640005bd74c864012ede63c8640006dd63c864003eee62c8640006ed62c864001cff7688640024fe7688640004fd76886400e57e75886400057d75886401267e65886400067d6588640045be7488640005bd748864011ede6388640006dd638864001ef66188640006f56188640004ff7648640004fd7648640024fc76486401167e65486400067d6548640005bf7448640045bc744864010ede6348640006dd634864003eee6248640006ed624864001ef66148640006f5614864001cff7608640024fe7608640004fd76086401067e65086400067d65086401fdbf7408640045bc74086400fede6308640006dd6308640007e52108640025fa7008640005f97008640004ff75d8940014fe75d8940004fd75d8940014f
  | 17 => 0x44fe7608740004fd76087401067e65087400067d6508740045be7408740005bd7408740007e521087400e67f74596403867e74596400067d74596403867c74596400067f73596400047f73596400067e73596400067d73596400047d73596400067c73596403867f43596400067e43596400067d43596403867c43596400067f72596400067e72596400067d72596400067c72596403867f42596403867c42596400067f32596400067e32596400067d32596400067c32596400067f71596400067e71596400067d71596400067c71596403867f41596403867c41596400067f31596400067e31596400067d31596400067c31596400267f70596400267e70596400267d70596400267c70596400267f40596400267e40596400267d40596400267c40596400267f30596400267e30596400267d30596400267c30596400267f20596400267e20596400267d20596400267c20596400267f10596400267e10596400267d10596400267c1059640006df7558e40006de7558e400065e7558e40006dd7558e400065d7558e40006dc7558e400dedf7458e400dede7458e40006dd7458e400dedc7458e40006df5458e4037ede5458e40006dd5458e4037edc5458e40006df7258e40006de7258e40006dd7258e40006dc7258e40006df5258e40006de5258e40006dd5258e40006dc5258e4037edf4258e4037edc4258e40006df7158e40006de7158e40006dd7158e40006dc7158e40006df5158e40006de5158e40006dd5158e40006dc5158e4037edf4158e4037edc4158e40026df7058e40026de7058e40026dd7058e40026dc7058e40026df5058e40026de5058e40026dd5058e40026dc5058e40026df4058e4037edb4058e40026de4058e40026dd4058e40026dc4058e40026d84058e40026df2058e40026de2058e40026dd2058e40026dc2058e40026df1058e40026de1058e40026dd1058e40026dc1058e40004ff7558a40014fe7558a40004fd7558a40014fc7558a40006be5458a40006bd5458a40004ff7358a4000cfe7358a40004fd7358a4000cfc7358a400067f5358a400067d5358a40006bf4358a40006bd4358a40026ef7258a40004ff7158a4001cfc7158a40024fc7058a40026bf4058a40026bd4058a40026ee2058a40026ec2058a401a67e6590a400067d6590a4019ede6390a40006dd6390a4003eee6290a40006ed6290a40025fa7090a40005f97090a4026dbf7590a40375bd7590a4021f3e6590a4021f3d6590a4026dbf7390a4036dbd7390a4021f9e6390a4021f9d6390a403673f5390a403673d5390a40045be7290a4021ebf6290a4021fae6290a4026ebd6290a4021fad6290a401fdbe7190a4021fba7090a4021dbd7090a4026fb97090a40046be6090a4003cff7650a400057f7550a400e57c7550a401967e655
  | 18 => 0x9305802103efb205802103ef8205802101efb105802101ef810580210467f74597400467e74597400467d74597400467c74597400067f73597400047f73597400067e73597400067d73597400047d73597400067c73597400467f43597400467e43597400467d43597400467c43597400067f72597400067e72597400067d72597400067c72597400467f42597400463f42597400467e42597400467d42597400467c42597400067f32597400067e32597400067d32597400067c32597400067f71597400067e71597400067d71597400067c71597400467f41597400463f41597400467e41597400467d41597400467c41597400067f31597400067e31597400067d31597400067c31597400f67f70597403ae7e70597400067d70597403ae7c70597400467f40597400467e40597403ae3e40597400467d40597400467c40597400463c40597400067f30597403ae7e30597400067d30597403ae7c30597403ae7e20597403ae7c20597403ae7e10597403ae7c1059740004ff7558b40014fe7558b40004fd7558b40014fc7558b40024fc7458b40004ff7358b4000cfe7358b40004fd7358b4000cfc7358b400067f5358b400067d5358b40046ef7258b40046ef4258b40046ec4258b40004ff7158b4001cfc7158b40006fa3058b40006f93058b40045bf7650b40006bf7650b400073f7550b403a73c7550b40046bf6550b400473e6550b403a6bd6550b400473d6550b400063d6550b40046bf6350b4039ebd6350b4039f3f5350b4039f3d5350b40047af7250b4003ebe6250b4003ebc6250b40005bf7150b4022ebe6150b40025be7050b40025bc7050b4039fba3050b4039fb93050b40004ff7558740014fe7558740004fd7558740014fc7558740024fc7458740004ff735874000cfe7358740004fd735874000cfc73587400067f53587400067d5358740004ff725874003cfc7258740046f77158740046f74158740046f44158740006fa3058740006f93058740045bf7650740006bf76507400073f75507403973c7550740046bf65507400473e6550740396bd65507400473d65507400063d6550740046bf635074038ebd635074038f3f535074038f3d5350740005bf725074028ebe6250740047b7715074001ebe615074001ebc6150740025be7050740025bc705074038fba305074038fb9305074003cff76c8740044fe76c8740004fd76c87400f57e75c87400057d75c87401367e65c87400067d65c8740045be74c8740005bd74c874001cff7688740044fe7688740004fd76887400f57e75887400057d75887401267e65887400067d6588740045be7488740005bd7488740004ff7648740004fd7648740044fc76487401167e65487400067d6548740045be7448740005bd7448740005fb7048740025f8704874001cff7608740
  | 19 => 0x9211157c7550921006bf6450921046bc645092103fac4250921005f7715092101df4715092103fe4215092103cfe76d052103cfc76d0521006bf64d0521046bc64d052103dee72d0521005ed72d052101fe421d0521044ff7650521004fd765052103cfc76505210057f75505211157c7550521006bf6450521046bc6450521005ef725052103dec725052101fb4415052101fe42150521004ff75d8121014fe75d8121004fd75d8121014fc75d8121044fe74d8121004fd74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d8121006fb60981210057f75581211157c7558121005bf7458121005bc7458121005df735812110ddc73581211157e75181210057d7518121005be7418121005bd741812110dde7318121005dd7318121026fa6018121006f96018121004ff75590210067f75590210047f7559021014fe7559021004fd7559021014fc75590210067c75590210147c755902101cff745902101ebf7459021006be5459021006bd5459021004ff735902100cfe7359021004fd735902100cfc73590210067f53590210067d5359021006bf4359021006bd435902103cfe725902103cfc725902103ebe425902103ebc425902101cfe715902101cfc715902101ebe415902101ebc4159021004ff7059021024fc705902101fe7764842101de77648421006e776484213cfe775484213bfe675484213cfe575484213bfe4754842101fe7654842101fe6654842101fe5654842101fe46548421007e77448421007e67448421007e57448421007e4744842101fe7644842101fe6644842101fe5644842101fe464484213bfe754484213bfe654484213bfe554484213bfe454484213c7e773484213b7e673484213c7e573484213b7e4734842101fe7634842101ee7634842101fe6634842101fe563484213b6e5634842101fe463484213b7e753484213b76753484213b7e653484213b7e553484213b76553484213b7e453484213b7e743484213b7e643484213b7e543484213b7e44348421007e77048421007e67048421007e57048421007e4704842101fe7604842101fe6604842101fe5604842101fe460484213bfe750484213bfe650484213bfe550484213bfe450484213b7e730484213b7e630484213b7e530484213b7e43048421004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff7458021006bf7458021004bf7458021044fc7458021006bc7458021044bc7458021004ff735802100cfe7358021004fd735802100cfc73580210067f53580210067d535802101eef215802101ef6215802101eed215802103ef52158021006e5215802101efb7058021006fa5058021006f95058021006fa3058021006f
  | 20 => 0x1cfc715922101ebe415922101ebc4159221004ff7059221024fc7059221006bf7559221006be7559221006bd7559221006bc7559221006bf7359221006be7359221006bd7359221006bc7359221006bf53592210063f5359221006be5359221006bd53592210063d5359221006bc5359221006bf725922128ebe7259221006bd725922128ebc7259221006bf525922128ebe5259221006bd525922128ebc5259221006bf325922128ebe3259221006bd325922128ebc325922101ebf715922101ebe715922101ebd715922101ebc715922101ebf515922101ebe515922101ebd515922101ebc515922101ebf315922101ebe315922101ebd315922101ebc315922101ebf215922101ebe215922101ebd215922101ebc2159221006bf7059221006be7059221006bd7059221006bc7059221006bf5059221006be5059221006bd5059221006bc5059221006bf3059221006be3059221006bd3059221006bc305922128ebf205922128ebc205922101ebf105922101ebe105922101ebd105922101ebc10592211b67e65d0a210067d65d0a21046be64d0a21006bd64d0a2101df671d0a21005f571d0a21044ff7650a210057f7550a211257c7550a211967e6550a210067d6550a21046be6450a21006bd6450a21005f77150a2101df47150a21004ff7558221014fe7558221004fd7558221014fc7558221004ff7458221044fc7458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d535822101cfc715822101eef215822101eed215822101efb7058221006fa3058221006f9305822101efb105822101ef81058221044fe76d9121004ff75d9121014fe75d9121004fd75d9121014fc75d9121004ff73d912100cfe73d9121004fd73d912100cfc73d91210067f53d91210067d53d9121024fe70d9121004fd70d9121006bf64991210057f75591211157c7559121005df735912110ddc7359121005fb7059121005f87059121004ff75591210067f75591210047f7559121014fe7559121004fd7559121014fc75591210067c75591210147c7559121006bf7459121006be5459121006bd5459121004ff7359121006df7359121004df735912100cfe7359121004fd735912100cfc7359121006dc735912100cdc73591210067f53591210067d5359121006bf4359121006bd4359121004ff7259121006ef725912128ebe425912128ebc4259121004ff7159121006f7715912122ebe415912122ebc4159121004ff7059121006fb7059121004fb7059121024fc7059121006f87059121024f87059121004fe76191211157e75191210057d7519121046be6419121006bd641912101cfe76d092101cfc76d0921006bf64d0921046bc64d092101df671d0921005f571d092103fe421d092101cfc76509210057f755
  | 21 => 0xc205932122ebf105932122ebc10593211767e65d07210067d65d0721046be64d0721006bd64d072103dee72d0721005ed72d0721044ff76507210057f75507211357c75507211567e65507210067d6550721046be6450721006bd6450721005ef725072103dec7250721004ff7558321014fe7558321004fd7558321014fc7558321004ff7458321044fc7458321004ff735832100cfe7358321004fd735832100cfc73583210067f53583210067d535832101cfc725832103ef6215832103ef5215832103efb7058321006fa3058321006f9305832103efb205832103ef820583210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210067e43596210067d43596210067c43596211267f72596213d67e72596210067d72596213d67c72596213d67e42596213d67c42596210067f32596213d67e32596210067d32596213d67c325962101e7f715962101e7e715962101e7d715962101e7c715962101e7f415962101e7e415962101e7d415962101e7c415962101e7f315962101e7e315962101e7d315962101e7c315962101e7f215962101e7e215962101e7d215962101e7c21596210067f70596210067e70596210067d70596210067c70596210067f30596210067e30596210067d30596210067c30596213d67f20596213d67c205962101e7f105962101e7e105962101e7d105962101e7c1059621046bf7599221046be7599221046bd7599221046bc7599221046bf7399221046be7399221046bd7399221046bc7399221006bf53992210063f5399221006be5399221006bd53992210063d5399221006bc5399221046bf7299221046be7299221046bd7299221046bc7299221006bf5299221296be5299221006bd5299221296bc5299221006bf3299221296be3299221006bd3299221296bc329922101ebf719922101ebe719922101ebd719922101ebc719922101ebf519922101ebe519922101ebd519922101ebc519922101ebf319922101ebe319922101ebd319922101ebc319922101ebf219922101ebe219922101ebd219922101ebc2199221046bf7099221046be7099221046bd7099221046bc7099221006bf5099221006be5099221006bd5099221006bc5099221006bf3099221006be3099221006bd3099221006bc3099221296bf2099221296bc209922101ebf109922101ebe109922101ebd109922101ebc1099221004ff7559221014fe7559221004fd7559221014fc755922101ebf7459221006bf5459221006be5459221006bd5459221006bc5459221004ff735922100cfe7359221004fd735922100cfc73592210067f53592210067d5359221006bf4359221006be4359221006bd4359221006bc4359221
  | 22 => 0x972103e7c32597211367f71597213de7e71597210067d71597213de7c71597213de7e41597213de7c41597210067f31597213de7e31597210067d31597213de7c315972103e7f215972103e7e215972103e7d215972103e7c21597210067f70597210067e70597210067d70597210067c70597210067f30597210067e30597210067d30597210067c305972103e7f205972103e7e205972103e7d205972103e7c20597213de7f10597213de7c1059721046bf7599321046be7599321046bd7599321046bc7599321046bf7399321046be7399321046bd7399321046bc7399321006bf53993210063f5399321006be5399321006bd53993210063d5399321006bc539932103ebf729932103ebe729932103ebd729932103ebc729932103ebf529932103ebe529932103ebd529932103ebc529932103ebf329932103ebe329932103ebd329932103ebc3299321046bf7199321046be7199321046bd7199321046bc7199321006bf5199321236be5199321006bd5199321236bc5199321006bf3199321236be3199321006bd3199321236bc319932103ebf219932103ebe219932103ebd219932103ebc2199321046bf7099321046be7099321046bd7099321046bc7099321006bf5099321006be5099321006bd5099321006bc5099321006bf3099321006be3099321006bd3099321006bc309932103ebf209932103ebe209932103ebd209932103ebc2099321236bf1099321236bc1099321004ff7559321014fe7559321004fd7559321014fc755932103ebf7459321006bf5459321006be5459321006bd5459321006bc5459321004ff735932100cfe7359321004fd735932100cfc73593210067f53593210067d5359321006bf4359321006be4359321006bd4359321006bc435932101cfc725932103ebe425932103ebc4259321004ff7059321024fc7059321006bf7559321006be7559321006bd7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006bf53593210063f5359321006be5359321006bd53593210063d5359321006bc535932103ebf725932103ebe725932103ebd725932103ebc725932103ebf525932103ebe525932103ebd525932103ebc525932103ebf325932103ebe325932103ebd325932103ebc3259321006bf715932122ebe7159321006bd715932122ebc7159321006bf515932122ebe5159321006bd515932122ebc5159321006bf315932122ebe3159321006bd315932122ebc315932103ebf215932103ebe215932103ebd215932103ebc2159321006bf7059321006be7059321006bd7059321006bc7059321006bf5059321006be5059321006bd5059321006bc5059321006bf3059321006be3059321006bd3059321006bc305932103ebf205932103ebe205932103ebd205932103eb
  | 23 => 0x4fd72d8141006fa30d8141006f930d81411557e75981410057d75981410067f65981410067c659814114dde7398141005dd7398141006fb60981410057f75581411557c75581410067f65581410067c65581410067f65181410067c65181411f6bf6418141026fa6018141006f960181410467f74594410467e74594410467d74594410467c74594410067f73594410047f73594410067e73594410067d73594410047d73594410067c73594410467f43594410467e43594410467d43594410467c43594410067f72594410067e72594410067d72594410067c72594410467f42594410463f42594410467e42594410467d42594410467c42594410067f32594410067e32594410067d32594410067c325944101e7f715944101e7e715944101e7d715944101e7c715944101e7f415944101e3f415944101e7e415944101e7d415944101e3d415944101e7c415944101e7f315944101e7e315944101e7d315944101e7c315944101e7f215944101e7e215944101e7d215944101e7c21594410067f70594410067e70594410067d70594410067c70594410467f40594410467e40594410467d40594410467c40594410463c40594410067f30594410067e30594410067d30594410067c305944101e7f105944101e7e105944101e7d105944101e7c1059441004ff7558841014fe7558841004fd7558841014fc7558841004ff735884100cfe7358841004fd735884100cfc73588410067f53588410067d535884101eef7258841046ef4258841046ec4258841006ee3258841006ed325884101eee215884101eec2158841004ff7058841024fc7058841045bf7650841006bf7650841004bf76508410073f75508413ef3c7550841046bf65508410473e65508413eebd65508410473d65508410063d6550841046bf63508413e6bd63508413e73f53508413e73d5350841045bf7250841047af725084103ebe625084103ebc625084122dbf715084122ebe6150841047b661508411e5bc7050841004ff7558041014fe7558041004fd7558041014fc7558041004ff735804100cfe7358041004fd735804100cfc73580410067f53580410067d5358041004ff725804103cfc7258041046bf4258041006bd425804101ebf415804101ebd415804101efb7058041046fb4058041046bc4058041046f84058041006fa3058041006f9305804101efb105804101ef810580410067f74597210067e74597210067d74597210067c74597210067f73597210047f73597210067e73597210067d73597210047d73597210067c73597210067f43597210067e43597210067d43597210067c435972103e7f725972103e7e725972103e7d725972103e7c725972103e7f425972103e7e425972103e7d425972103e7c425972103e7f325972103e7e325972103e7d325
  | 24 => 0xd63d95410067c63d95410073f43d95410073d43d954143f7741d95414373e41d95414373c41d954143f7441d95414367f74d954143e7e74d95411567d74d954143e7c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d954143e7f43d95410067e43d95410067d43d954143e7c43d95410067f72d95410067e72d95410067d72d95410067c72d954143e7f42d954143e7c42d95410067f32d95410067e32d95410067d32d95410067c32d954143e7f71d95414367e71d95411567d71d95414367c71d954143e7f41d95414367e41d95411567d41d95414367c41d95410067f31d95414367e31d95410067d31d95414367c31d95414367e21d95414367c21d95410067f70d95410067e70d95410067d70d95410067c70d954143e7f40d954143e7c40d95410067f30d95410067e30d95410067d30d95410067c30d95414367f10d95414367c10d95410067f65d89410067c65d8941004ff75d8941014fe75d8941004fd75d8941014fc75d8941006be54d8941006bd54d8941004ff73d894100cfe73d8941004fd73d894100cfc73d89410067f53d89410067d53d8941006bf43d8941006bd43d8941236be41d8941236bc41d8941024fe70d8941004fd70d89411557e75989410057d75989410067f65989410067c6598941006ef62989410057f75589411557c75589410067f65589410067c6558941005df735894114ddc7358941005fb7058941005f870589410067f65189410067c651894103eee6218941006ed621894101cfe76909410067f65909411a67c6590941006ef629094103eec629094101df67190941005f5719094101cbe769094128dbf759094142dbd75909410073f65909414273c659094128dbf739094141dbd73909414173f53909414173d5390941045be729094128ebf6290941007af629094128fac629094101dbe719094128fb6719094101db6719094128fb5719094101dbc7190941046bf6190941047b76190941005bd709094121ebc609094101cfc76509410057f75509411557c75509410067f65509411967c6550941006ef625094103eec6250941047ac4250941005f7715094101df47150941047b44150941005be7610941046be7610941004be7610941045bf75109410473e751094140dbd75109410473d75109410053d75109410073f65109414073c6510941045bf73109413fdbd73109413f73f53109413f73d531094128dbe7210941047ae721094128ebf621094101dbe711094101dbc7110941046bf6110941047b76110941005bd7010941216bc60109410067f65d81410067c65d8141004ff75d8141014fe75d8141004fd75d8141014fc75d8141004ff73d814100cfe73d8141004fd73d814100cfc73d81410067f53d81410067d53d814103cfe72d8141
  | 25 => 0x8042046bf415804203efb7058042046fb4058042046bc4058042046f84058042006fa3058042006f9305804203efb205804203ef82058042004ff7558b410067f7558b410047f7558b41014fe7558b41004fd7558b41014fc7558b410067c7558b410147c7558b4101cfc7458b4101cbc7458b41046be5458b41006bd5458b41004ff7358b4100cfe7358b41004fd7358b4100cfc7358b410067f5358b410067d5358b41046bf4358b41006bd4358b41046ef7258b41046ef4258b41046bc4258b41046ec4258b4122ebe4158b41046bc4158b41004ff7058b41024fc7058b41046bf4058b41045bd7690b41296bd7690b41295bf7590b41475bd7590b41295bf7390b4146dbd7390b414673f5390b414673d5390b41047ae7290b41046bf6290b41296bd6290b4101dbe7190b4101dbc7190b41005bd7090b4121ebe6090b41004ff7558341014fe7558341004fd7558341014fc755834101cfc7458341004ff735834100cfe7358341004fd735834100cfc73583410067f53583410067d5358341004ff725834103cfc7258341046fb7058341046fb4058341046f84058341004ff7558a41014fe7558a41004fd7558a41014fc7558a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a410067f5358a410067d5358a4101eef7258a41006ef5258a41006ec5258a41006ee3258a41006ed3258a4101cfc7158a4101eee2158a4101eec2158a41004ff7058a41024fc7058a41235bd76d0a41046bd76d0a41236bf65d0a4145ebd65d0a41236bf63d0a41456bd63d0a414573f53d0a414573d53d0a4103ebe62d0a4103ebc62d0a41045bf71d0a41235bd71d0a41047b661d0a411f5be70d0a4103eee6290a41006ed6290a4101df67190a41005f57190a4103cff7650a410057f7550a411657c7550a4103eee6250a41006ed6250a41005f77150a4101df47150a4103cbf7650a410073f7550a4144f3c7550a4122ebf6550a4144ebd6550a4122ebf6350a41446bd6350a414473f5350a414473d5350a41045bf7250a41047af7250a4103ebe6250a4122fae6250a4103eae6250a4122fad6250a4103ebc6250a4122dbf7150a41007b77150a4122fb47150a41046be6150a411f5bc7050a41004ff75582410067f75582410047f7558241014fe7558241004fd7558241014fc75582410067c75582410147c7558241004ff735824100cfe7358241004fd735824100cfc73582410067f53582410067d5358241004ff725824103cfc7258241006bf4258241006bd425824101cfc715824101ebf415824101ebd415824101efb7058241006fa3058241006f9305824101efb105824101ef810582411557e76d95411567e76d95410147e76d95414373f74d95411573c74d95410057f73d95410057d73d95410067f63d95410067e63d95410067
  | 26 => 0x4867c40d95420067f30d95420067e30d95420067d30d95420067c30d954247e7f20d954247e7c20d95420067f65d85420067c65d8542004ff75d8542014fe75d8542004fd75d8542014fc75d8542006be54d8542006bd54d8542004ff73d854200cfe73d8542004fd73d854200cfc73d85420067f53d85420067d53d8542006bf43d8542006bd43d8542296be42d8542296bc42d8542024fe70d8542004fd70d85421957e75985420057d75985420067f65985420067c6598542006f761985420057f75585421957c75585420067f65585420067c6558542005df735854218ddc7358542005fb7058542005f870585420067f65185420067c651854201ef66118542006f561185420067f65d81420067c65d8142004ff75d8142014fe75d8142004fd75d8142014fc75d8142004ff73d814200cfe73d8142004fd73d814200cfc73d81420067f53d81420067d53d814201cfe71d8142004fd71d8142006fa30d8142006f930d81421957e75981420057d75981420067f65981420067c659814218dde7398142005dd7398142006fb60981420057f75581421957c75581420067f65581420067c65581420067f65181420067c651814221ebf6418142026fa6018142006f960181420467f74594420467e74594420467d74594420467c74594420067f73594420047f73594420067e73594420067d73594420047d73594420067c73594420467f43594420467e43594420467d43594420467c435944203e7f725944203e7e725944203e7d725944203e7c725944203e7f425944203e3f425944203e7e425944203e7d425944203e3d425944203e7c425944203e7f325944203e7e325944203e7d325944203e7c32594420067f71594420067e71594420067d71594420067c71594420467f41594420463f41594420467e41594420467d41594420467c41594420067f31594420067e31594420067d31594420067c315944203e7f215944203e7e215944203e7d215944203e7c21594420067f70594420067e70594420067d70594420067c70594420467f40594420467e40594420467d40594420467c40594420463c40594420067f30594420067e30594420067d30594420067c305944203e7f205944203e7e205944203e7d205944203e7c2059442004ff7558442014fe7558442004fd7558442014fc7558442004ff735844200cfe7358442004fd735844200cfc73584420067f53584420067d535844203ef77158442046f74158442046f44158442006f63158442006f5315844203ef7215844203ef42158442004ff7058442024fc7058442004ff7558042014fe7558042004fd7558042014fc7558042004ff735804200cfe7358042004fd735804200cfc73580420067f53580420067d535804203ebf425804203ebd4258042004ff715804201cfc715
  | 27 => 0x14800000a0000000000046000003000c04a0000000048000005006000c0060000090008002005005000000a019002002403c00401d0000046000000004403200000a000403a000000800401a006006000802600000000000240000018008032002000000006002101b000c002004010009c002000044800400c0030028014004000004ff75587420067f75587420047f7558742014fe7558742004fd7558742014fc75587420067c75587420147c755874203cfc745874203cbc7458742046be5458742006bd5458742004ff735874200cfe7358742004fd735874200cfc73587420067f53587420067d5358742046bf4358742006bd435874228ebe4258742046bc4258742046f77158742046f74158742046bc4158742046f44158742004ff7058742024fc7058742046bf4058742004ff7558342014fe7558342004fd7558342014fc755834203cfc7458342004ff735834200cfe7358342004fd735834200cfc73583420067f53583420067d5358342004ff715834201cfc7158342046fb7058342046fb4058342046f84058342004ff7558642014fe7558642004fd7558642014fc7558642004ff735864200cfe7358642004fd735864200cfc73586420067f53586420067d535864203cfc725864203ef77158642006f75158642006f45158642006f63158642006f5315864203ef7215864203ef42158642004ff7058642024fc7058642004ff75582420067f75582420047f7558242014fe7558242004fd7558242014fc75582420067c75582420147c7558242004ff735824200cfe7358242004fd735824200cfc73582420067f53582420067d535824203cfc725824203ebf425824203ebd4258242004ff715824201cfc715824203efb7058242006fa3058242006f9305824203efb205824203ef820582421957e76d95421967e76d95420147e76d954247f3f74d95421973c74d95420057f73d95420057d73d95420067f63d95420067e63d95420067d63d95420067c63d95420073f43d95420073d43d95424876f42d954247f3e42d954247f3c42d95424876c42d954247e7f74d95424867e74d95421967d74d95424867c74d95420067f73d95420047f73d95420067e73d95420067d73d95420047d73d95420067c73d95424867f43d95420067e43d95420067d43d95424867c43d95424867f72d954247e7e72d95421967d72d954247e7c72d95424867f42d954247e7e42d95421967d42d954247e7c42d95420067f32d954247e7e32d95420067d32d954247e7c32d95420067f71d95420067e71d95420067d71d95420067c71d95424867f41d95424867c41d95420067f31d95420067e31d95420067d31d95420067c31d954247e7f21d954247e7c21d95420067f70d95420067e70d95420067d70d95420067c70d95424867f40d9542
  | 28 => 0xc00c000002807e01c011003400c0000070000000007003001400a0180010000004000003000000e00500100080ca000000003c0060700038010002004004800401e007001000000a0000008008012023000801401800402880180020000090094000008006801c00800e00200380140040000024000000000801400800100000000000060028000000003004001c0160000028018000000005001801403f0008000000004004801403c010000002c0340050008000004002003815806400e000800c01200a0008020008038000008401201f003001000000300a8008070003001000c00000400200f40a20020000008010007000000000e00a001000800a0230070000014000001000800600d00a00080100020008048004002002002c010000005801800e006003801001a007002800001800700000040020130090008002031000801805a0390080098002030004000403e002000809803e00101b801c012000000010c00004a0110030008010000012000a00a008000400000a0000000000000007800c00000400200100200020058074030000001000000400c00080c400200000900c000601600e002802400200a803c060001000800800200400d000800000300080bc00a001002801000a007003005c00800e000806001a0020088004000005000004800001900100a400001a007806800000200000100000110000088002004001000801201e0008184006003003000002e024002802400401d00000a400000100180300000010000000074000000000000200100180280dc003004000000200800300040000040008018058000001000c0640070000078034006009014000800000300080160030078008000000003001c03a00e000003400a0000008040000003001000001200a004800401805c00300080020080098000004014000000400200d000000c0140430008000006001009000400002b0000000012025001806800e0070000000088018006800800c0060020010006002000000000201000b80040020020000030000001005008c000002004801800000300000a800000002b802400200c0010024002000002000801a0000000000000001001000800001200200000020180050000002002002000803c001001000004e009030805801400c00580d80160100010004002000004802800200700100000020030038000002020009800400000800000000720020080080016002006001c006001000803807e0030010018002008003800800000f007001c036011001800000000100c801c002000000811400c00a00900000040170008000050000003001000c005005006402c0470068018000001000803c02c001008800401800201c80f800e00300500a400801d00000ec008041005800000000000200600180080008004038021
  | 29 => 0xc0018004010008000001800600900000100240000038008004004000002400200100e000000e0060068014006002005800c0060140030004008000001000000800500f801800000d00a80000120030028014062008009802800000b004802400400400c001000000c008800005200e0018014004008000800c00000000000140180020008018000001000800400600d000800c0400000000008020000000000407803200180040000220078000000000001800003e000001804c002000000807400200601580380080000208004000008002800400002a000002800000800a0044010002003802c05000100f8048000001004000802c00200b000800000400800080ca005001004401203d000000006402000100140180030058004000000002001400000000900d801c005002002c03e00e000002001a00400d0024008000001007000a00001680100060000100038026001000805c01c00000100000040060018020098001001800c02e0010050064000000002000c002006003801c00a00000300a000200d00100080020070000050022002008000400600600100100000050010034026002000801000000000400000260050090004020009007007c000000000006400000f001804400800701a00480080120018008000000005806c00200e0010004000007000800c008000001004c000018000000005e00e018000000a001009801406a00a000001001a00b006800800e001000000400800202c0010008001006800402000000400000000020040024002002000001c00c006000801c044002009000c04800600d001401801300e001000000e003801000a000002004c00600b004000c01a00d000808405a00300080680020200000020002007013001403e00101a002800e00800d000400000200d800c01600200100140000000000008002013000800001e009009001004a01a00200040080160040020038000001800003600f001808400e0030028048004006001000001c005001000c008003004003c0000040030024008001001001800c000000001c004007006800801c00300c007800200100b002c00000000180a4002000004000800e008000000004c000014801001e00600100080360510000024010001001006802e001000800000000001700380020000078020000001004814c018023000802400200000300140000070000004000001000000002a002000800400e0000068000026004000004001200000000480240000008028010001001828401a0020060004000008003001c00000700b0028000016000800001a000009001800000000c00100040140090000012001006800c050016000000000a004013008800a0010028020028000008802800200900000b000000e000009800c01b000801003600b001002c03400c00b000
  | 30 => 0x96d27c0d9400e068b0f08cc12d94b8d4a4517042a121b3db09f227a40423454eec26408e800000000c1cc350000060000059439c45b118651af07a803d0000eeb029c000000000010650bc16946f7419895d464c3f127040003f3c210330087a000032705980001a4502619c40003b6c9661b60000339c07f45bc4de1fe04f7000110519ac2bc198800021600000000b35446c6221a782ed2254dd82eac3cc0f186991fc07a51da0a660000368210c0000c0c0000f8800000010e10000eb50000f1b31d928937d063b1a9885720cc7c910911323d5856f05084d63848b2e13450480b6c99112908b40000dc742f8e0a3dac98f2d244c033bcbad000000033743862c3c9850b8cc6f266c0002bfd090025ce19462800014a4a1600008d132c4700039ca9900005ef12743ea17884ed0000270203c51d3bd000000011270104dc029247f4310c95a439858c39cc3fb3a60269105c4b52bec3562b98b240cac7a7192c7fc189511427580b02feca1723e401d21cc21e10a05721a74c9633389343d3c7bf01e42e2006d07906b477b43744124454da515e07452f7cbc30f5c1212b2d2653a6c860327cca9451c8ee0c78d2634b05e137b4259443400004e10b8000046a0c64dc616e0bc02fb03f74094ecd2c291bc1a1cbde193504441851e3309c38e18780002a1cb4e1a5860200000002658fa4176cdd33c1cc37158d21332e4b54009400000000001984f1e24b461147909ea0000734000105e0000000067c1570000f8f02d8000000041a3e30b2d00000003ce800000001740000af41d3c3e60ed80000000000209400000006463e2c00021c104e3f6114d140cb5c00000153edcc6a0318fe60000d6a00008bf00004e1471c00600900000560010008014006006004801800c00000480a0010001001801400000800200000020010108040024006000000003e0060010000004001000001801000000200000140010000008000001001002c00c000002801c018000006003401c0290008048002041003800c00400100a8008014016016802000200e007813400400b0340008026000000004000001900380b0052005000800000400000100000000010040000018001003000004201b00180340060000040000006012003001001201b007800002c00f0000030000002000800001e00a0008000004002000000402200a0028000016006000801801e00200100040000010010040000012000001001e025001802005c008000803c00000f000000c0080100000004006012004804c00a000002002c006008000003800601e0008000000019000004000e000004000803600400800140060050000014014008004006000e03a000000c00602900980100080100110004008001005801c000001001004000c00e000800c00a000005000801400600a000c00200
  | 31 => 0x40c0000171ca4f411432e4328d711034d7b2f8484f30a8bd408590d04208cc83bec2683800035163d2623ba0ca1383c1004048e5c0194c230bb06bf13609302db090334089b328fc4eb03a1028328d0eb06604700514af942a816d00646be36a8cb53ff521e1b0c02103dc533011cddc14305fc060478a42c084e33d02553288925263921640049fc4a1400f00003051dc426e19e820b0000dd614490ba00000000d851132c080ba388cc6800012750f540003cac7292c04c172f9c0000000c1f0254d1e2178d9d000122c115000041d0ff1250413e3e34929320cd0844dc7b91f680001a8c36e43801221ef806b1218d0643904a32ce107e1940c8e404071f000000044f5207207849604c408e000072f01d925503384202a8815d0b089dd2d0035817c8e3a3c901df06c831845404662ea0fa921747544010e9e2f64f08000000009fc0003ae43a31d68ecc0058915014515a000004a2fd8ca022e89282bdce0334d4a3239e0f1721180001fd872e00009d000005af000000018e81db021c5a34744c032c7c6e30160a4c393d0f039651ab247c3a4063923c1660e023144d2405587fa3194664007cdf23330ee144e8db403141a340006f00d309681408a9209d9200176000036b0824000000028d8bb0214834e2514588072839c3d60083054415c231525343d05d210c0d8314ec6b32c6cb8b0420d852b90000373d2021eaca1c0000dcc34c03132cc442f28a02384294a0a00009fb0c508f51800b52407883e20d0c5d00010fa1458ec846609d72d74342120113125f8000438cbdc2b9c00032c0a6839846433cc0d4503b000006402492610b192fe0d8229386123cd440126008d60d047c7298c24d0cf860624c402006a043a3fccfd3382c36c000110023f073f3df81c10be0fe540c435320d44b100009c505b0000358ceaa1cdc0001ba819735b400019e08d54020a674978ee00a40c2122691db0000000000000038c4c1b1f780000000d660000000120c6fa0000ee90f80d254494dde4854000483800000011451b949af276cfff14407d1396c4c3121d26831c896a25e8aa5439cc0e1b2478035745d10c44a9724e4e4e2014ada17ec0221810de439ec14012a0c81343918d2d6c83b2450b07051ce3e2a8494329acec50a7076d1668e253d981b42fd01842154cc449b818b33e85f90c2c7740ef06db1b492522e60a393afc50e00f80002dd8b3b01a8f7f20741e322b06c2034d28d3484cb629780c82dc8b870d807af3cb479a2b7445731c4fd9013c000000127606a893839442171d34874205c9fd41c83213fb122500012823198cc716b80000000d5a2660f771cb448e00183a523c4c7814f40002bb1129098cce33bc85ca1a68e1c4054b2f3898a651ce4c630a6cc0c1f6407716dc2dc411806e1aac656000096f1b180001b04d3a13fc
  | 32 => 0x88710000000200c000118885621d4f902e6826b1a810f21a88fb84090000290cd3f2dd49c61dfcafa2fe8f653f2055907a497444fcbd53398fc948a08530000dec402c00008cd1080c2815e254004800010d2081c0003af90980f2400010d0000000000049e10ea3d2470c0398000154444c27780180000000321cb0b3a245730b340003220de52accb5a36481cc429800000009b402b0ad3350026a15f80ad47890970658c8d00001fa18749ef02acfab30bc816000008c0e811a021042442a7486742508dd000123b03e11b3339520c398c67f0af400019f452700004bf17a0000059438c45444ce41a85682fdc6521ec102e23d90ed2578d9a0c90d843f00d9f13941fb0ce89591b406f63b6124d0218120084c0000000b6a000000000000001ddcc1345a049900007d230984811e5905916a8a3d18c52492b7cb513c18000000000023a8a34461447724fcd090000000136400000008402dcc2361cc05dc49610430d4103a04c856e1ac886e34b40e125b0e99227c4560000c84037ca6f096883027e4ea11b5caef18b8cf03f6c9d4151cb0e14ac1d1481800000002f6496c8c73f049701498912000000019a841e1145254210800048bca8849fc2340000f180ad8000008d1953858e6816192041138fad31b8b68014926a12991be229863245c81a7150820843a43d242104f13ed8a0529d8ede36790030b18c851e510d741307bc26d40292a3011b08980000000ba3477400009f101b36911d01c9908e0b1062a2e4c804278c00044984473260d5c1c3916a01e00001be10210464ee6124ca45405d1ea3530367000050f00004da0000f0108947e400011da000000000006840724ba2125471c175800028b878619943d300000000000000000000000000002a100000001166200082c2444c3c1ed4de30170b2c00000003bfc8c30fe0d4214a879b3eccd791a507e63a8cc7f1418aa94a48b4d10e4eef297d0d13980289104c7a84834f8e18200003474bfd0f209240000d8c0dc40002a592731328000430c0cf3fac000447c946015c5222a9c0c3000105c0e0041100000001ca0000335c6bc195000011fcc3815f4ccb3e511ba415cdbc0134f5f00008b126f000004e4b7f11201b02d8093a2bc4f990000ad63ce0e943d849b0326c45d25b87e515ec45a40dcac72ff86a90c686090cbcf590e6c9082ae0ece0f951f111700001380000036434613e4b5802a0dfe3018747467cd2f11848823eb03952294ac0000046f00010383c7ca6d351034447083773818dc33ff800000000b700000000dc0c5737ecc9a0424a7729c0171401ca73255924217fc37c41400003d1000012342ea000082607f800026fc4ae2a6005f1164f3341d50ec27883b2017905149e8e80296917e000090223386fb0000f4a42840002ef42091eb420c00004983e80000
  | 33 => 0x150c6fd0130a3a032c8900000000479ce323a900001cf4d6b38e072026ed24106489790388cab35b081a0000776233006f000119700011120998a7215b10cd2b6c00020c800043602a220dcbdd1fe40f2170466c436cb470000bca31e400000000000000798000000000000002d0d01f114094e470c38b46506a81ff425b0d7c2ae20d85be1598cf31d1914f00011e100000312f202c70ce03150cb475f0348f87306017b2c680621ce8000279924537a000018f0e011b742a3165c25c30f8cf93dc8024146c9821fc8c481d6cebd25c868904101520fbc04312c90a236fc1a202ed1390a307e80448aae229c17905600003f6923332a890436c8c6d0000000000000e19b8f7d2edc8e408a4d8f39c849035451a403b8dfa2190cb423b0c07099cc892ecc4d700009e02aad03626240a1241810a3c691d415185f71e4c69f1d44686113c82020543851084e2408c0af81cd80000ed05e33b1c94b1b7c0003d5044b0ed49fa114cf26146403900007170258b712de854532c827824292212d2c8872f88fe83754000341c4ba3e54aeb323c71300000002a780002929158000108d000054c00006cb124914e08ac1280ec4a512cfc0ef000036d1148000243c0001bb89ff00010de0a14478000074328ec69212e019903b4000040c0001b5000023711593be84ee160853000008980ba5111277101100011400f9cbd310d80000ef874400000003e4ca5237bcce9000009e3c3800000007d70000ab207f000000000002478e1b1b782bb0000669035400004a40002b5400038b06b415486ef473c7d636a4d57454c1ec0b64a3139f837e3a54ce229c4000000038436bd1d3000000000011dc30291730000f0f4214cbb2d110dc43144fb000000026e400044d03ed27b00000000a2a45e4000000000048444fc3d3083d3e7912010a51f417a428f047caa80530d0d2dac3cf0a05177232905845107f1188c96b2afce1424d800000004cd26b0e810000edf33a88cb10dcfed3c145321908cba1e64e1a00004c41414acc39045372d5400046e45e035f01a14508dc11c680000ca87580000a9a00002961cf017340fc6c700010bb000000009d4c6902201a5342c2f30d48000172041b000000000010950d2128103e8000389c7a90000a330f04223000104b1da42050000b4a253502315dcf5021fc84b3251155433924e174c000000059b1f9c1c3075887245ac00037a4b223aa000b0f0056d0c74d5f00005743e0819e2a9011c3b440002bb875d2cd90a70bd10c8241c1823a98ed346640a62764f02277ceea0e6926d1390000102c2864200191488c000230000000000000000b7709e45814824261329c8ae39b400016fc0000000792000082918ad26b000037629108b616d910100000b83efca470000c5607e07904974d7628340003ef0c4f49f4a4b24a
  | 34 => 0xfc73fd45ce4848000000102b00011ae255c7552c2094a0000000000051a3054117000126300010652c84000000039700ac3ad473097c261c9f80000f0a375cef008502d01c34f6f000000030e800000000001c880ea00000003bf400037dc00000000000000b0c06202570000000275461429182c03d9ceb83ec049147b453c457c47417c4b922b111a2119405b268049e0000b4c2b086850de0f731010fba173d07f00000000000b701190b9000280003ed000000008a4250827e23c845e000049c0000c1d12d00000000402036c36b3f081d734b800033f400000002560a105cd0000756366d03300005d72f38dd9000000007886a700000000000000385c00027d402c221818900000000000d5b00004bd02482a7383834b42206ac30d09c9116c9e737c47613a88cec00011df245ccca39b8d910000000000000048dc00040d01e7475c000378000045fc00024004e330b458d220417f49446e61ed089e32dcab0486518f09f4b393325078251c5232f2c8be10cc3930b850180000b503b70b3a0000bf309b460f131433d108c8442ded01c1920c1c1330dbe45c49553ef852017f8e3000b8cd100cc8e10c588aa3ee400014c4b00241522d3094e2a08e4f29000016447a43013fc11f542c40003acd0c13b282e71d051d834d8408000000012dc33c47bc9ca2c451d93e70c473370aac22f440c2720f69109cd8041f000000001340000d1a0000b2b00000000000b6424d4dd40aa000028749d30000000000000000011872c0c617000000026b48220a5417c17d400031490c90000000341021847c07e302f086c20340000000000311800031910320000b7e1890633145c5fd0e34cd04980e7f1f1449f19ccfa63315243226ca7a29b8c4b14d825400010fe3e8d08f1100cc635dce900acc88e268d272286844d1ca879d0b3c2213a18dea478048a474860a074c3642e0400021305950000000303502018d48c807b45703d6834028d51881de4a552ee101603fd06b2cf4e463264e752364a2148d84ec0e78c022e140000c30c6c0d7843f32411330000c670b60c122974ec00ae111728046054460e40231087d34e4e6a282cab90ad0000388009045f4d7e2cc83941c1044618d0ee319d80823824ed2197ce9301f4000022c0990e845c62ebc0001324d7822b4b2800008bb000051e10acc491424036028805d00000002e6c41511ac07b2e90dff3fc8b5e34047a14065227206001041c0000000106d04f40b23ec800045582b94190c7d3d4c00c0000d6e00000000cdc000000055600000001abc6bb000030e1750c7e3b0883c06006bd147c07319c8d0017e8690024d1b4485cab415e40000000eda224400011c800043ed1d51ba504725606b50c98b9f41089640d2841d00009ba24f0e4b000010e24dc3f345e8f9d00000000000f2309c800
  | 35 => 0x6300000001bcc81300002f200010090cd84323f7450d1348f8a204437a00011f73360e152c98cbc1b343e12618ef606f478c47ecd1b3c2c0ca2008be80becfe337acfe1450c3233cd918349a40343f8802f421823127091ce1cb0d494014e5e1e4448b1fa4d5e24406150000da63fd83eb0000000128118612eced71c6cb3c20e400000000da17e016a23a4df0126824e1b5411e19dc53f2958d2b4718f71000000023e80002b8c12f19440eb39604a5039055d38f44bc1510a8a3820c091c78ee229d0ac11b650922af88a0282509c2e2863e368c68039f4eb43b40e920c705394368ffa20bc86241ec0261cc8ec33c10fea028c30227dca4d2e800f0258c34f34480003c54e4942d4dfc30ace10233c29f367030f2b18f5208100003a8000017acc8b10b861306e8237045471d3ea10fd43e4d2700000002b40e553a38f700000000159486b0000a30142060d07d8d034154144203815304743f416008284964d8b3de4c6204904e91d488932bd4c5f0e489933df054f33ed1620000c973ca822048a91d63f7825f1f84000206c34d0210da201147640000ad9336d09a336812a16b10b22360d7430a064e00009993cf4d1608b4c191bfc0d1038d1231a0cf034a2c0000d98cf7000055b38e45df3f288880914000044d25a1d4d12f2424c2e0d6cd0c2890f3b3f54da72b146b017b83b933846a129f80000a90f10190447c00005b42b280e02d08000333c00000003bb2adccf600009a72c80701468528a28206e215242881c0c8e51900644441c52c0afcd0a384440a3d08e8433583f022e48ed274867c320058b0000584000000030b019d1688a0f0ab46603d1457f0d94f9a2c101251ee0dca3de8629248028d31ec00023406c03618ceb19bcf9f4704ced44388d72b50f920b0d0af3d548b80efd14b10f81da013839d236cb740e4100e3bd47ec15788ab04684ef35491bd1f50aaf180c39f24bc5c2167436a4a00db82850460250000002741ff448493e01c000000003332bc08f742cc2e046e062d26991cd0a1c45f00011fa267800031383394068292102402d43648012230f0011d4d3c26e061607bcee71aa905644d504132a086122cd1bf3784a931e0c9f41924c3b2f3cc3d08883fe417c14e2f6ca3c49b04b331300000c940003a2903d495c00015d42ca493ced91df40000abc000000000000000003218000240478700004fa000092301c4000488853835900540df513e02049f3131c46348d021525f45833a9c2ac3564b9900000004890091140088d00000dd359c469252406400003df1ae8000094c8d220a81b9213400015f000000002d2426428300c800020c4a00359461b38dcd4d47cc57137cc053327000005a0f3245308df2fc51f837350714258ba53ed41b7468d02227b80000000d682ad4e540b4c0000001264000096200
  | 36 => 0xd141a432982c541bc3e9202065d159cf813664da804cc1e605f49832eb0072089c50a01b4d1107f48e02258933252020f02a4ae800dc0610000000034012d125c0002fc80001c8c733000000000006ca00001700628d10044400000011b60000000000000030cc8cd035c7b21dccf190000de2000074e2a7c000000000032cd130000098a21ec0cd15e86f111b4c9e000092c10702d50000f133ef47ea3d382a10a60046299008a00005c33d900002b940001700a270ec0bd000012670f8c94f3f400552dbc84a0dd05694a10d8a0f1400018bc6d336387c147c8511167898d03a47c81968bc921dc27124389e10000b170bb886326501630e24a48103821d4920a6a0bbc185000000045f078903583af02cc000152c0000324c321450300212422e2b8849b48f4eb22d9d18e0000f7549ec000000000030e40270588000409c5621d700001870ca434611e80000f4605e8eee3254d693fe0211000014932bc0000aac000000098c000000008fc00034a509b0c410b7041c00000000000ca00003f5104d3b104441f54b2a100c000428c00000000000a00000054080c048cc9d0000000000000044a800008a909d21691ff0000e0d48687843cbd20b0f700aa37b88f82df50bf3c2518138f0f1d379cf4745ec6b80800db326a8be945282e602608ff03cc250116037f2d20228308056434a8a8935047fb2070f853a083b342d8f4147249e844701f0384cd22462508b46c0bae335016b254c3fd08045a10024eab364cafd0000dcb25a4ead227400020b40002c609670000712000000007741f142f43692de04f637690ff1e9928809000002a2c5a01e5cbc63f2d0ad1ab5152108806c23981be43000002cdc000169c4cb0ba00001790135162499210d465e32445bb201cd34428027400001ce3cf92051d7800035603d93db4b63000095c49012383f30a5031605d93f7d1692248e2944b813b3ff09e41f7cfef46003290e051c013d43aa274463d31d08e2226442d0068f912604f683a7067023f916d05dd07a018d24c2b4401e11cc79507cc8502e50f214a4091a3994d554318fa503311783cd07152e20ba14a38d3e0e64b230f446ae35283170cd47bb3b2479f2c9426008e80a002c44cf2ffd1b7081861a26845ad23ac95109cc15a120811028e0ecb00e85b346c90811ad886a1fb8000223c00000004d3334800000007311e0886507187073f445b500000000000e431e040003a3c00000009c43f142fd000000047f8659000000000007c319d40004464be613f4c0b1e7887c318009b26a000035847a009dc92200003ab1c90388195ccfc0b94000422482343dc299433c8452ac4e5d17740a43a0cf0c1f300fd164513848b823216703343d7112c2c505042084c5903084dd2844bba3da877804188a1071ce0c027c8da2efc25d191516510950
  | 37 => 0xac90d0d247235119231081bf0e3cd0513e01a900000001be4b41410000000003750000000119c00027ac82700009c700000000000000469813c3934382000099538d459206e0e9134dce1e099000014e81833580c3f1f2c00000004dc06805e73f1000035e86363e9d24b41a4a0e1528000269400039691094474c7a101c000000000000012740000e7631702a641748b049c400049f00003c8909300001f72250000154000000009a2463000000008b70001157000000039300002bf83a20a740002210000179491800010d51cf84fe00000003044c4a0000b953714c540c109880110000000126f47b8ef722a00003b188a21b9c70b0c485764a3d0a42a70f2819ed02a092c35528f87702f90c5b33644b021a110f0a944891c64fbb1a34b9100002d60e44e8835404ac344c54147780560d7459606540000000ab60000d4e1e3c0000000fee000019b2a184181250aad2a14f5b0000a4208708120000a8e00008c90b68a530000d9038ac10200008fb244c61f00011a90000d961cad09e2a445f4000000012a4000000063f000000000004d01bf000000000b40000471307912d2b80b292a546da0a506f511251a83f3862125ec4be3dd840038882583cdc9600c2115c1ee8ac311047aa01983ca3ae8927016804b13d0a411b3d2310000fb106d4c5a00003a6050c07519d07a40000b050124e873cc40003308e960cec88b3a3400008b00003184f84413c00049c02ce001c0002ea4ddb086ce0508ece2d13500942e0c5610a8070f07e43ac1c583c4381c13a2db8abb13a8d732ea860c02f8e5226dcdc920506970a4c63744ac23c33fd03e03d068839149520ee0e8b13c8ebb2498be046b03981284069430911e33c8fd60000cde1a54aaa0b5d1751fcce340d5c15448607c43c80d4f32e11b14a4cb623230c6b000064c02e42cb2fe495f24744b946a8d3d0ad42ff21f8b8e22704a7311410d3ac50ae1d2cdba24ac0000b7ca031bb40de02bd0f11b7000032f85f034506263b905e648e8bf5000100d16286fe2f3400000000004611190000042600006d1427d1cb3d7408514d110614b86e8035101d28108e30564bda181d0d33e84b9734cc9711f00b892a0c7eb202c6eb466c2d4432c66626691b500004161b851ad298462c28610c43b749be38a0f1c00007ff2e7417e37d818f00c03491640dc427b504a1c18bc11f40cbd21e44e82c74c551ac479c16a4d540000b1300000f900005b900000003e6011800000002f105f605540001c242fa00000c13f90dad199cbd10000eae29b00fb46ec0c0171047e0000dbd3248ca5311000000005cb0b4510c4674bcc1354ae138847f705807482ba82dd1df000040f00c700007ed21440000000efe0000c4d05d40000000d1f1398abd2a04b451740ddd0f74b6133e0c7c2c40acd30c02b118e0a2b0
  | 38 => 0x9190bc0e85422915e0000b9c12b52563fdcd53196026f2af0d7535bcea92170aa30528d23073c00031d422f0ee87fe21d81f5090cbb24a500000bdced40f5106c242cfcd110c2c8320878e3db83733d34a191c8498b2840db500001d926c838304fc24c21a43da10f453520e02a91b310f60f0ce66141c00303101140ac016136211f63d0cc290000be300001ae0294000452000000002de2ccc2b2080c00017cc014000076e0100d89000047d0f90f25000101439c0ef8000091b3e587ef06bc0500b24adc1dc88662bcc000000019a2e180002f08efc0988df500007b745511641838d0f1128b530000de60adc0003740f270000afc3f0c4451d28a79440c7251a705cc0d8cce42c548fd00000000000f3f02704f31eb846c2c9c7c62ff1226330c00024f4c1012200001e2ca691a3d26604b0a9b12bc000456c00000000000000df80504f1208083593d2000045b800048a450b47f4248000106003952612c780002c24ce04a0d0d40000b5f00010534828a570b901f2079020d26705993088332000024601f8e3f211c5480000d4748046101551039259459f47140002894655164ce4400001ac36e52870a691280f60001421c146265c0000a78c053b54c0400005bc0000f7429806283bb4bc725dc0284440ff92470aa017b00dc42aca4047f00001cd493b1c9c0004458518303c6a410e0630234c1271308c0112307b33588e9f24b828b2fc0c7305e053e28549fe45247882fac36217551962878000442c750101405914bc0000d5000025fcd202d5c9da000021906f11c41580a5408900003cb0cac15a8dfd0ea0e74019c4c13cf085907349a430507dc24c80002d3c6a5000038a00fca59000055f40a400036dc16e1ce08b247204060008297105000022bc000045906e34e0df91f6c9e548d4bd8351919a2308000395d05400000000000000403c620000060b064c83a00000000000d48399000005c8cfe31c000028dcad2286cd810000c16000000d00001b30000b8200005a433d469b267c8891fd4bb5000010b0d68a07107c0002d983f606350ee191c00000001c0440800000000000000000000000006ec51342e455a37440001a0425243f099d16140004a3000449400004488f0d17b4b590e9c9443940000314c54036ac0000ea50671154a80103c1c834c906231dc95b39f07590f5803c2cd0bee13c0acf09e814d000000010f000039591ec2fbd16c29f00002cc03cb464514123d014b0cb0b7c1db1160361c0172cf92860fb108c40d4bed0ff051c34703cd03f8dd220ac3962e3015b397c0001a6031b1f4d21c0000ecf01f08f000005550a081940b30f390000068000024f4428c503f80faf2e5855302002be0000f972e100002e7800000000000ae80000000e8c40ec5c92a507b10c7cfd745d8bd600010f337211243e88
  | 39 => 0x22d45ea47ac0000de40bd0fe800029f51f900000002db524427c4f783090ffb22a44c819e43872c488ef3c5123e3558c1a49280f51a2921007507144518e6f1d943f912105c521510df2120c3616f4fae2f48a5b00005b0000127728b01ee0ef4e470000d4b433076b000047a0000aa61a4d04900011632a3c000491800036c40002550eb009090911d247053bcc1a604c0f5e29611a5386121d05a42fe192816732fc8c607404683d8d0061c44cd516e852527601870748cdf3c5830d000000035c0e971c28ec140300000520000000064f3d8827b16ac23e21e04e22da51a72f14074297073b0dec0004008aba00207e000001372304760000063944100002e9c3f51e142f50000e670000c930000ce800000f1217d2084678b462b392032028f2e06d8a783e007ca33c43ae414882e0c8905a41dc62720650e5176825e420cb1c1f6017642b0ea548acbea35c90b40c18f7b20410e2248424107784c62ef0ad800a88de0bf0a6232b4ed63abca821bb03b70498ddf023d0132b20be516a0a020000e531c409b60001279092800008f43203708000000080909b000049f918b07d033f3af030922f012b35fc7184468d9838d87622bb4fd226ac3f2075400012ac976488086f39dcaf6288c0000f1c66d21b400504d80003ad80000dc80001adc1cb0000db0169800000000130710b8f14540003e20bb100007dd0a3865c3adce6c1bc8a1f44d8a8d1d3113b3c44a2f000000041f4ad7487c3ce29d4f573000d3b14b47b607ac78d3a7470810ec0002ee4000087c0003e18a901eb0fe9483ce6206c51e5416c5de322828a10a89c300010f5350cff410b09ce36b8fe728a4e3311b8a261df8f8308291821b1468c1d00e693654b5639289f639e8a131d8d16728b43d034a0ba6139c65348e420e1d5cfaa078407a43bc00012d844235f4a220be456b32b8000043cc083f705b2000036f000068e43580fc25cc00036d8eac1b10682196c54d2de46f400009bd00007e226b8d31220c1e000001ab1e8c6ce12a809a000000006700000000e42281888531787ce0848e6b10c49cf104008d0bacdbb000102d41d834702fcbb419a0d170cc025100448a31f08ade497c9a9057ce041de8fc60000000201810c48c84df36850a93e24e7919f852420fc0000d44c41071410549703ff0000000284874238ec0003334331000089707a01c22434bbe091c00011e400026c4557387c089148481f2eec000000094c45841e5216c1dc0000a7f0bc52140000c400aa83db3a6800038b876f36807cd000119c1ef4d193b9400030c49cd2730b0d22290f818600003be4f40392117409940ae23cc1011b58775180470200006b927003e825d466300011ca431c00036340d84575068365d07315707cf000090c00000003d444a2239cdce2ed8ae9479835c00483de
  | 40 => 0x3d80916387414f2c5876600007a208680b51d9d2300fb823512140002c1913c2e00bd705bc000000029115602c11b900000000961123d02c3e6c0002bc923f25e0000272c00011ec880334d00a00000000000000283052811d801c38bd02f136c6e01638587000000000000000000a2004b80f6076000006190e8153818c1da85013d2ccee29ecef100000001b20000000003b000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaba800c9640400157300192c80800317dd67558c104952ec3ceab182091e5a109d5630412bcb2213aac60800317e1d7558c104962fb82eab182092c5d705d56304125cb420baac608253964417558c1048d2f428eab182000a5e85dd163040014bb0bba2c608012b6a037458c1002d6cc06e8b182000a5e851d163040014bb0a3a2c60800387d525458c100052f42ee4b182000a5d85dc963041275af02b92c60800eb52057258c100052f428e4b182000a5d851c9630400153d08392c608002a76107258c1001d6b408e4b182005ad5811c963040095b500392c608016b66007258c100054f420a4b182000a9d841496304001c5ea92a4c40824a9b616539881000727a9ca73102000e4f8354e6204125c9e60a9cc40824b934c1539881048d37428a73102000a6e8590e62040014db0b21cc408012baa02439881000574c04873102000a6e8510e62040014db0a21cc40800e3d20573588100247743ea4b1020048ec87549620400155d08292c408002ab61052588100247743e64b102000a6e85cc962040014db0b992c4080123b21d325881001d7240a64b102000a6e850c962040014db0a192c408002aba10325881000556c2064b102003ae6810c962040095d500192c408002aba10755881000556c20eab102000a6f855d162040014d90aba2c408012ba201745881000537428e8b102000a6d851d16204001c5ea92a2c4080029ba16735881000536c2ce6b102000ae7815cd62040075c902b9ac4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac40800eb9a04735881000572c08e6b102004aea801cd62040015d30039ac40824799c43535881048f32886a6b102092a6d8594d6204001c9ea729ac40800393e0d535881049727982a6b102092e4d3054d6204125cce20a9ac40824b99441535881048d37428a6b102000a6e8590d62040014db0b21ac408012baa02435881000574c0486b102000a6e8510d62040014db0a21ac4080123be1d62d08100245fc3ac9210200287c85dd9420400917909bb284080123b20b76508100043fc2aeca10200287c855d942040091f100bb284080021f61b75508104861f326eaa102000c5e63dd5420411f8dcc5baa84080021fa1d65508100043e43acaa1020048bc87591420400187eeab2284080030f1d564508100062fbaac6a102000c5c7558d42040099b0e0b1a84080123b21d625081000637baac4a102000c6c755894204001972c9b8284080033658f705081000674b16e0a10200287e855d8420400917b08bb084080123b60976108100043fc32ea2102008c3e645d442040018bcc6ba8840801f1b98975108100043fc3aca210200087d87594420400187ceab2084080030f5d564108100062f3aac62102000c5d7558c42040018dceab1084080031b5d56210810
  | 1 => 0xaea32642880038d194648851020f3210eca90a203fea421d91214407bd484232242880f32e1c0644851001d7340ec490a2000cb864dc121440818e8edb2a42880fb2d1db64485101e65a3b0c890a2000e3465191214400f5cd0db12428800399d94624851000732328c490a2000ea7641892144001d48c83124288002f460c70485104bc3e432eba022008c3c645d740440830ff0fb2e80880021f61f65d01100061f3aec9a022000c3d75d9340440010ff0abb2808800a1f21576501101f45fc22eca02203fcb471d91404400f9c8c4b8e4088012b921921c811001e723b243902200087f855d920440050f90abb240880022fe1176481100445e422ec90220008df835d920440031b906bb2408825e1fa1b75481104b43f43eca902204187c87d95204407b17d0dba240880030fd9774481100061e32ee8902203f8be861d1204400187eca3a240880030f19474481102645f43ec8902203f8bc87d91204400187eebb2240880030f1d7644811026c5f438c890220088bc87191204400187eea32240880030f1d464481100247b436e290220049e48748520440095c90c90a408800f391d92148110025f0402429022000c3f749d165041250fb0f39aca0800317dce73594100062fc1ae6b28209187e871cd65040010fd0f21aca080021f61e43594100253d40486b282000a798090d65040010fd0e21aca080021f61c43594100051f420e4b282000a3d841c965040010fd0f992ca080021f61f32594100043f43864b28200087d870c9650400147d08192ca080028f610325941001d3b40864b282000a75810c965040094f500192ca080029e60032594104951ec2ca73202000e1f5394e6404001c3f06a9cc80824b87cc153990104970e982a73202091a3e8514e640401117d0e294c8080022f61c52990100051f42e653202000a3d85cca640401117d0e194c8080022f61c32990100051f428653202000a3d850ca640400756d02194c808002ad60432990100255d400653202000ab9800ca640400917d0faa2c8080030fdd754590100161f3aca8b2020048bc87551640400917d0f21ac8080028fa1643590100051ec2c86b202004aba8090d64040091790ea1ac8080028fa1443590100051ec2886b202000c3f759d5640400147d0b39ac8080028f61673590100255d404e6b202000ab9809cd640400147d0a39ac8080028f61473590104951ec2ca6b202000e1f5394d6404001c3f06a9ac80824b87cc153590104970e982a6b202091a3e8514d640400147f0ab92c8080028f21572590100255c402e4b202000a3e851c9640400147b0a392c8080022fa1c52590100045ec38a4b202000a3e85cc9640400147b0b992c8080022fa1c32590100045ec3864b202000a3e850c9640400147b0a192c80800eada0432590100055ac0864b202004
  | 2 => 0x574989100061e32ae93122000c3e75d92624400187aebb24c4880030f9d464989100061eba8c9312200287e86dd562440810f90dbaac4880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac4880030fd9774589100061e32ee8b122000c3f651d16244001878ca3a2c4880022fa1f64589100061fbaec8b122000c3c75d916244001938e7b22c4880022fa1c64589100061fba8c8b122000c3c751916244001938e6322c48800317d9773589100062e32ee6b122000c9f64dcd6244001938c9b9ac4880021f60f75589100045fc22eab1220088bc845d562440011bf06baac4880063720d75589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fc2ee6b122000c5c85dcd62440010ff0ab9ac48800a1f21573589100045fc22e6b1220088bc845cd62440011df04b9ac4880023de0573589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200287c87d4d624400187ee9a9ac4882730f1d353589100062fb9ea6b122001c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b12209bc3c7454d62440018bee6a9ac488007171cd53589100066639ee4b122000cd473dc56244001970e9b82c48826b2e1d2305891000e6c39c60b1220018f8874c162440df970e8982c488007361cd30589100072ca9a60b122098c757119462440011df0eb10c488002b320d62189100043fc2aeda12200287c855db424400f17908bb684880021fe1576909100143e42aed212203fcb671d9242440091e90cb8c84880031d19571909100143f42eeca12200087d85dd942440050fd0b3b284880021f61676509100043fc2aeca12200287c855d942440011bf06bb284880063720d76509100047dc02eca12200287c851d94244011179083b284880021fa1b75509104861e326eaa12200087e87d9542440010f90fb2a848801e2fa1f64509100061fbaec8a122000c3c75d9142440050f90b3b084880021fe1576109100143e42aec212200087c865d44244011878c8ba884880021fe1f65109100043ec3eca2122000c3e75d90424400187aebb2084880123d21971109100465a322e221220038f8865c042441310fd0dbaa828821f0f1937550510436b8086eaa0a209987e87d9541440810f90fb2a82880030fdd764505100061e3aec8a0a203ecb870d9141441310f90cbae42881021fe1f65c85100043ec3ecb90a203e8be869d3214400187ecb3a642880030f19674c85101e45e432e990a2000c3f655d32144001878caba642880fa2fe1f64c85100045ec3ec990a2000c3e75d93214400187aebb2642880222fe1c64c85100045ec38c990a2000c3e75193214400187
  | 3 => 0x5b2220008be8714b644400117b0e296c8880028fa1732d91100051ec2e65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b22203fab6810cb644400156b02196c8880faaea0032d91100055cc0065b222000a3e85cc7644400147b0b98ec8880028fe1570d91100051e42ae1b22203f8be87d43644400117b0fa86c8880fe2fa1f30d91100045ec3e61b222000a3e85cc3644400147b0b986c8880038754f30d91100070ea9a61b22203ee98304c36444011878c8bacc8880030f9d764991100061ebaec9322200087e87d9564440010fd0e32ac8880021f60f75591100045fc22eab222000c3f75dd16444001878ebba2c8880021fe1573591100143e42ae6b2220008bf845cd64440011df04b9ac88801e3b20973591100043f43ea6b22200287c87d4d64440010fd0ea9ac8880021f21d53591100045fc3ac83222000a3f8559064440014790ab20c8880030f9db65191100051ec1eca32220008bd87994644400117f0eb28c8880030f9d865191100051ec18ca32220008bd8798c644400147d0b318c8880028f61663191100045fc3ac63222000a3f8558c64440014790ab18c888002abe09631911000556412c63222000a3e8518c644400147b0a318c8880028fa1b53191100051e436a63222000c3e76d4c644400147d0ca98c8880028f21953191100061f3b2a63222000e3b658c06444001c70cb180c8880f6ae21930191100071db2a603222000e38654c06444001d36c6980c888003a618d30191100078ca9a60322209ba3d8594c6444001c3ea7298c8880f2aea0253191100055cc04a63222000e1f8354c644413947d0a298c8880f2aea0053191100055cc00a6322203dab681948644400156b03290c8880222fa1c52191100045ec38a43222000a3e85cc8644400147b0b990c8880f2aea0332191100055cc066432220088be870c8644400117b0e190c8880028fa1432191100051ec2864322203dab6810c8644400156b02190c8880f2aea0032191100055cc00643222000a3e85cc4644400147b0b988c8880f2aea0331191100055cc066232220088be87d40644400117b0fa80c8880222fa1f30191100045ec3e603222000a3e85cc0644400147b0b980c8880038754f301911037d5cc1c603222000e3b538c06444001c72a7180c8880038754d30191101e74c18260322203cabb834c06444079d3706980c8881bfa6dcd301911037f4c39a603222000e3b534c06444001d34a6980c8880038e54d30191100074ca9a603222000e19534c06444001d3664980c888003a64c930191100074d98a603222000e99314c0644400147f0a880c8880028f215101911000572c0865b122000ae9800cb62440039b0e6986c4880039654d30d89100076599261b122000c3f659d26244001878cb3a4c4880030fd9
  | 4 => 0x2c400f17b09bb285880021fe157650b100143e42aeca1620008df835d942c40031b906bb285880230f9917510b102345fc3ac82162000c3d7559042c401187cc8bae81880fa2fe1d64d03100061ebaac9a062003ce47158920c40093c90e90a418800a1fa1f7558a100043ec1eeab1420008bf845d5628401117908baac50813a1fa1c7558a100061fbaee8b142000c3c75dd1628400187eea3a2c5080030f1d47458a100043fc2ae6b14200287c855cd628400117f08b9ac5080222f2117358a100043f43ea6b14200287c87d4d628400187ee9a9ac5082730f1d35358a100043f43aa6b14200087c8754d628400187ee8a9ac50826f0f1d15358a1037e5c3a260b142001cd8734c16284001cb2a6982c50810a2fe1d64d0a100043fc2aed214200287c855da42840010ff0abb2850800a1f2157650a1021c5fc22eca1420048bc87591428401117908bb085080030fd917510a100461e322ea214203c8bf8759341840010fd0db9eca8800a1fe1f63d95100062eb9ec7b2a200087d8798f654400147d0931eca880028f61263d95100043fc3ac7b2a2000a3f8458f654400147908b1eca880029be0963d951000536412c7b2a200a87d8718f65440018bae631eca881069e21930d9510006adb9a61b2a2000e58634c3654400187ae83a6ca880021f61e73d95100062fc1ae7b2a200087e871cf65440018bae639eca881029ea0073d951020d3cc00e7b2a200087e8790f65440010fb0f21eca881029ea0243d95100053cc0487b2a200087e8710f65440010fb0e21eca880028fa1272d95100051ec24e5b2a2041a76811cb65440814eb02396ca880021fa1f32d95100043ec3e65b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2041a76810cb65440014eb02196ca881029ea0032d95100053cc0065b2a204087e87cc765440010fb0f98eca881061fa1f30d95100043ec3e61b2a2000a3e84cc3654400147b09986ca8800317dcf30d95100062fb9a61b2a2040e58304c3654400187aebaa6c88800b0f1d654d91100145fc3aa9b222000a3e8590f644400147b0b21ec8880062fe1d43d91100051f42887b222000a3d8510f644400147b07b2ec8880028f60c65d91100051f42cc7b222000a3d8598f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400147d0a31ec8880028f61463d91100051f436a7b222000a3c86d4f644400147d0ca9ec8880028f21953d91101fd5c43261b222000e98634c36444001e32a6986c8880030f5d475d91100051f42ce7b222000a3d859cf644400147d0a39ec8880028f61473d91101f55d400e7b22203fab9801cf6444001c3ea729ec88800387e0d53d91100051f42ee5b222000a3d85dcb644400147d0b396c8880028f61672d91101f55ac08e
  | 5 => 0x3eb66037458c200052f428e8b184000a5d851d16308001c3ea92a2c61000297a177158c200052ec2ee2b18409dacf825c5630800f59904b8ac61000297a147158c200052ec28e2b184000a9e841c5630800153b0838ac61001eb3a087158c2007d66c10e2b184004ada801c5630801f5b30038ac610002a7a105158c200054ec20a2b184000e375495261081254eb0b29cc21000395d4e53984200072bc1aa73084092e573054e6108125caa60a9cc2102469da1453984200053b42c873084000a758590e61080095e50121cc210002bc60243984200053b428873084000a758510e610800f1d904b9ac2100123da1f51584200247a43aa2b084000ab684145610800156b0828ac2100123da1f31584200053b42e62b084000a7585cc561080091e90e98ac21001eb920931584200053b42862b084000a75850c5610800156d0818ac210002ad610315842003d7341062b084004af2800c5610800156d083aac210002ad61075584200053bc2ae8b084000a74855d161080095e100ba2c2100029da1474584200053ac28e8b084000e375495161080014ed0b39ac2100029d616735842000573c12e6b084007ae4825cd61080014ed0a39ac2100029d61473584200055b420e6b084000ab5841cd610800f5cd0439ac210002b9608735842002579400e6b084000af1801cd6108123cce41a9ac2102479948353584204953ac2ca6b084000e575394d6108001caf06a9ac21024b95cc153584204972a982a6b084092e672054d6108125cca40a9ac2102469da1453584200053b42c86b084000a758590d61080095e50121ac210002bc60243584200053b42886b084000a758510d61080050f90bbb282100122f21376504200247a40eeca08400087f855d941080050f90abb282100021f61b755042043e1f326eaa084000c5e63dd5410810d8ecc3baa82100021fa1d65504200043e43acaa084000c3f755914108001878eab22821000317dd563504200062e3aac6a084004cd87058d41080018eeeab0a82100031d1d561504200065cb26e0a084000cd963dc141080019e2c3b82821000a1fa1576104200245ec22ec20840048f5815d841080010ff0cba882100230f99175104200062f31aea2084003c76615d441080010ff0eb2882100021f61d65104200061f3aac82084000c3d7559041080018bceab188210003175d563104200063b3aac22084000c757558441080050fd0fbaac9880021f60f75593104343f438eab262002c3c7595164c40071790eaa2c9880021fe1573593100143e42ae6b26200087e87d4d64c40050f90fa9ac9880021fa1d53593100043e43aa6b2620038bc8750d64c40018bee6a9ac588007171cd5358b1001c7643a64b16200087f855db42c40050f90abb6858801e2f21176d0b1001c5fc3ac92162003cb6715924
  | 6 => 0x43ec3eca20a4000c3e75d90414800187aebb2082900232b191721052000716328c990a40a087c865d621480010fb0fb2c429010e2fa1a74885200061fb2ce910a4000c3c659d221480851790cba442900030fd9574885200061e32ae910a40008bd87d92214800187cebb2442900030f5d764885200045ec38c910a4000c3e75192214800187aea324429013f99087654852026f5210ec890a404cea4211912148085970e032242900032e1937048520276363b6ca90a4043cac76d912148085958ec32242900038b194644852001d73436c290a4000e67651852148001cc8ca30a4290003a9d90614852000752320c290a4000bc9831c1214812d0f90cbae80900230f19175d012027c3fc3ecba02400087d87d97404800187cebb2680900030f5d764d01200043fc2aeca02400287c855d9404808717f08bb280901372b1cb64501200061fba4e8b28409287d879cd65080018bee739aca1000317e0d735942048c3f438e6b28400087e8790d65080010fb0f21aca100129ea0243594200053cc0486b28400087e8710d65080010fb0e21aca100028fa1071594200051ec20e2b28400087e87cc565080010fb0f98aca100021fa1c31594200043ec3862b284000a3e840c5650800147b0818aca1001e9ba08315942000536c1062b284004a7a800c565080014f30018aca1024a8f61653990200070fa9ca73204000e1f8354e6408125c3e60a9cc81024b874c1539902048d1f428a732040088be87146640800117b0e28cc8100028fa1731990200051ec2e6332040088be870c6640800117b0e18cc8100028fa1431990200051ec28633204007aae820c6640800155b0418cc810012aea0031990200055cc006332040048be87d51640800187eebaa2c81000b0f9d654590200245e43aa8b2040048be8790d640800147d0b21ac8100028f61643590200255d40486b2040048bc8750d640800147d0a21ac8100028f61443590200061fbaceab204000a3e859cd640800147b0b39ac810012aea0273590200055cc04e6b204000a3e851cd640800147b0a39ac81024a8f61653590200070fa9ca6b204000e1f8354d6408125c3e60a9ac81024b874c1535902048d1f428a6b204000a3f855c564080014790ab8ac810012ae20171590200051f428e2b204000a3d851c5640800117d0e28ac8100022f61c51590200051f42e62b204000a3d85cc5640800117d0e18ac8100022f61c31590200051f42862b204000a3d850c5640800f55d0418ac810002ab60831590200255d40062b204000ab9800c564080018beeb3aac61024a9761e7558c2048f2d104eab18409fe59209d563080018bf0ebaac61024b17dc17558c204962eb82eab184092e5a205d5630813dcb240baac61024697a147558c200052f42ee8b184000a5d85dd163080095b501ba2c61
  | 7 => 0x3c86d4c644800187ceda98c8900028fa1953191200051e432a63224000c3e7654c6448001c76cb180c8900038e19630191202655c432603224000e3b654c06448001c70ca980c890003a6d8d30191200074c31a603224000f19534c0644813747b0b298c89000387d4e53191202155d404a63224000ab98094c6448001c3f06a98c8902728fa1453191202155d400a63224000ab98014c644800147d0b990c8900028f61732191202155d406643224000ab980cc8644809955d05288c890002ab60a51191200445f438a232240008bd87144644800147d0b988c8900028f61731191202155d406623224000ab980cc4644801117d0e188c8900022f61c31191200051f428623224000a3d850c4644809955d04188c890002ab60831191202155d400623224000ab9800c4644801117d0fa80c8900022f61f50191200445f43e6032240008bd87cc0644800147d0b980c8900028f61730191200070ea9e60322406fab9838c06448001c76a7180c8900038e54e30191200070ea9a603224042e98304c0644808557706980c89010ba6e0d301912037f4db9a60322406fe98734c06448001c76a6980c890003a694d30191200071ca9a603224000e99534c06448001c32a6980c890003a6cc930191200074c992603224000e9b314c06448001d3262980c8900028fe1520191200051e42a4032240a087e86dd54248121878c9baa849023f5a083755092050c3f43ecaa12404e87c87d95424800187eebb2284900030f1d7645092021e5c386c8a124000ae5820c761480015e30018ec290007361cd30d85200072ca9a61b0a4000ed3314c3614800187ecb3a4c2900030f19674985200061fb2ae930a4000c3c655d2614800187cebb24c2900030f5d764985200061f3a8c930a4000c3d7519261480050fd0dbaac29013a1f21b75585200043f43ecab0a4000c5c73d9561480010fd0e32ac290003171cc65585200061fb2ee8b0a4000c3c65dd1614800187eca3a2c2900030f19474585200045f43ec8b0a4000c3f75d916148001878ebb22c290003271cf64585200045f438c8b0a4000c3f751916148001878ea322c290003271cc64585200062fb2ee6b0a4000c5c65dcd614800193ec9b9ac29000327193735852050636b90ca30a40008f78758461480015a906b08c2900021fe1576d05200143e42aeda0a40038bc845db41480010ff0abb4829000a1f215769052026e57396c920a4000c6c655ca41480050fd0bbb282900021f61776505200143f42ceca0a400087d859d941480050f90a3b282900222f21076505200043f436eaa0a4087c3c64dd541480010fd0fb2a82900021f21f65505200061fbaec8a0a4000c3c75d9141480050f90b3b082900021fe1576105200143e42aec20a400087c865d44148011878c8ba882900021fe1f65105200
  | 8 => 0xc6986ca900030f5d074d95200043ec3ce7b2a4000c5f835cf65480010fd0e39eca90003175cc73d95202753d400e7b2a404fa79801cf65480010fd0f21eca900021f61e43d95202753d40487b2a4000a798090f65480010fd0e21eca900021f61c43d95202743f43e65b2a400087d87ccb654800147d0938eca900028f61271d952027d37410e3b2a404ea6d821c765480010fd0f98eca900021f61f31d95200043f43863b2a400087d870c7654800147d0818eca900028f61031d952027d3741063b2a4000a6d820c7654809d4f50018eca900029e60031d952027c3f43e61b2a400087d87cc3654800147d09986ca900028f61330d95200062fb9e61b2a4000c5f734c3654809dcb060986ca900030f5d754d91200161e3aca9b2240028bf87553644800147d0b21ec8900028f61643d912000c5fc3a87b224000a3e8510f644800147b0a21ec8900028f60f65d91200051ec18cbb224000a3e8598f644800147b0b31ec8900028fe1563d91200051e42ac7b224000ab78158f644800156902b1ec8900028fa1463d91200051ec28c7b224000a3e86d4f64480014790da9ec8900028fa1953d91200051e432a7b22404dab8864c36448001d30c6986c890003c654d30d91200061eba8ebb224000a3e859cf644800147b0b39ec8900028fa1473d91200051ec28e7b224043aba801cf644809b5730039ec89000387d4e53d91200070fc1aa7b224000a3e85ccb644800147b0b996c8900028fa1771d91200051ec2ee3b224000a3e859c7644800147b0b38ec89010eab60871d91200045f438a3b2240008bd87147644800147d0b98ec8900028f61731d91200045f43863b2240008bd870c7644800147d0a18ec8900028f61431d912026d5741063b224000aad820c764480875750018ec890002ae60031d91200051fc2ae1b224000a3c855c3644809b17d0fa86c8900022f61f50d912026c5f43e61b2240008bd87cc3644800147d0b986c8900028f61730d91200070ea9e61b224000e1d534c36448087d3060986c8900230f19175991200061f3aec93224000c3d75d9264480010fd0fb2ac8900021fa1c65591200043ec1eeab2240008bf845d5644800187eebba2c8900030f1d774591200043fc2ae6b22400287c855cd644800117f08b9ac8900023de05735912001c7a40ae6b22400087e87d4d64480050f90fa9ac8900021fa1d53591200043e43aa6b2240008bf87590644800147f0ab20c8900028f21564191200061f3b6ca3224000a3d83d94644800117b0f328c8900022fe1d65191200061f3b0ca3224000a3d83194644800117b0f318c8900028fa1663191200051ec2cc632240008bf8758c644800147f0ab18c8900028f21563191200055bc0ac63224000ab48158c644800147d0a318c8900028f61463191200051f436a63224000a
  | 9 => 0x305884037f4da1a60b108000ec9324c1621000187f0abb484200030f21576908400061fa9aed2108000c3d535da421008797460bb484200032e4c176908400143f43eeab088087c3c74dd561100010fb07baac2200222f21175584404ce1e3a0eab08803d8bc8755161100010ff0ab9ac22000a1f21573584400445e422e6b08800087e87d4d61100050f90fa9ac2200021fa1d53584400043e43aa6b08803d8bc8750d611007b17d0f212c2200f6ada0642584400163a3aca2b088087e365494561100091e90ea8ac2200038d55151584400247a43a62b088001cd8734c16110001cb2a6982c2201bfa6d0d30584400076898a60b088000c3f855da41100018790abb482200030fd4d76904400061ea9aed208803ecba305da411000197260bb482201322fe1d629044026657392c520880078bd845db211000f8dcc4bae42200031b5d562c8440046573a2c590880038bd845da21100078ecc2bac42200031d5d561884400465b3a2c3108800087f855d921100050f90abb2422000237e0d764844000c6e41aec90880008bd86dd121100075c902b1242200133a1c1624844003d72412c29088004cf07058521100010ff0abb0422000a1f215760844001e73bb2421088000ce57648421100050fd0fbaac9900021f60f755932047c3f438eab264002c3c7595164c800f1790eaa2c9900021fe1573593200143e42ae6b26400087e87d4d64c80050f90fa9ac9900021fa1d53593200043e43aa6b2640078bc8750d64c80018bee6a9ac390007171cd535872003c7a43a62b0e400087f855db41c80050f90abb6839000e2f21176d072003e57392c920e40038bd84dd941c80010ff0abb2839000a1f21576507200046fc1aeca0e40018dc835d941c801187cc8ba8839014a2fe1d64107200061ebaac820e4008c3e645d740c808717f0eb2681900030f5d564d03202145fc3ac9a14400287e87dd561880010fb07baac3100022fe1175586200445e422eab0c4000c3f75dd16188001878ebba2c3100030fdd474586200061e3a8e8b0c400087f855cd61880050f90ab9ac3100022fe1173586200445e422e6b0c400087e87d4d61880050f90fa9ac3100030fdd353586204e61e3a6a6b0c400087e8754d61880010f90ea9ac3100030fdd153586204de1e3a2a6b0c406fcb8744c161880039b0e6982c3100039654d30586201e45fc3ac9a0c400087f855da41880050f90abb483100021fe1576506200143e42aeca0c4000c3f645d44188011878c8ba883100021fa1b73d95200143fc3ec7b2a4000c5d73d8f65480010fb0f31eca900028fa1263d95200051ec24c7b2a400087f8758f654800147f08b1eca900028f21163d95200053bc0ac7b2a4000a748158f65480250fb0e31eca90003175cc63d952027d3c43261b2a4000d5b734c36548001cb0
  | 10 => 0xa14806b93f865d4429000127b0cba885200024fe0d7510a400049ec1aea2148000d1e635d44290001a3ac6ba885201370fd897510a4026e1eb12ea2148008c3e605d44290011a74c0ba885200fe2fa1e54586400161e3aca8b0c803f8be87d0d61900050fd0bb92c3200021f61772586400045f43c84b0c803fab681909619007f17d0e212c3200028f61442586401fd5b40884b0c8004cda7058e419007dd3080b1c83200033658d70906400045fc3ac520c804dcae7258a41900010fb0dbaa83200031798f75506405143e43acaa0c8000c5f7558d41900018b8eab1a8320013361c163506400066cb1ee0a0c806593f865d4419000127b0cba883200024fe0d75106400049ec1aea20c8000d1e635d44190001a3ac6ba883200ff0fd8575106401fe1eb0aea20c8008c3e605d44190011a74c0ba883201362fe1d62106400061ebaac420c804dcae7258841900050fd0abb643200021fe1975c86400062f31aeb90c800087f8759721900010fb0eb2e43201c30f9d165c86400061f32ae990c8000c3d655d3219000193cc6ba64320003179d563c86400062ebaac790c806fc9e7458f219000193ae8b1e43200032b5d162c86400143f42aed10c800087f865d621900018bcc6bac43200021fe1d65886400043ec3acb10c8070c3e74596219000187ccaba443200030f59574886400064f31ae910c8000c5e7558e21900018baeab1c43201bf279d163886400064eba2c710c8000cb57458621900075c902b12432001eb920961486400263d382ca10c8004cda7058c21900079ceec9084320003395d921086403bf3332a4210c8000e656548421900edd8cc69084320003b158d21086400063cb2ae010c80089b8845c021900019b2c6b8043200037848570086400043fc2ae3b12800287c855c7625009b87ec8ba8c4a00023be1d62189400061f42ceda128000c3d859db425000187ea73b684a00030f54e76d09402345e432e3a12808fc3c76dd5425007917d0db8a84a00021fe1572d85400143e42ae5b0a803fc3f645d461500011ef0eb08c2a00030fa1676d05400061ec2ceda0a8000c3f539db415000187aa73b682a014a2f21972d05404361e3b6eaa0a80428be86dc9415000f179093b642a000e2f21276885400143f428ec90a800087d851d921500091790cba242a00126e20174485400043fc2aec10a800287c855d82150001bc242b8042a000a1fa1f75588404861e3a6eab10800087d83dd5621001117908baac4202870f1d075588402645e43aa8b10800087f855cd62100050f90ab9ac4200222f21173588400043f43ea6b10800287c87d4d62100010fd0ea9ac4200021f21d53588402645e43a86b108002c6c759496210121c5ca9292c4200123b21d525884000716aa2a4b1080048ec874c962100039b0e6982c4200039654d
  | 11 => 0xd0001878ebbb283a00030fddb75507400051f43acaa0e8072a3c8759541d000147f06b2a83a00028f60d65507400461fb8acaa0e8008e377159541d00eb87ce0b2a83a01d70f1c1655074028c5ec36e4a0e8000c3d65dc941d00050fd0abb643a00021fe1975c87400043fc3acb90e800087d8759721d001187ce8b2e43a00030f99574c87400061eb2ae990e800287e855da21d00010ff0cbac43a00021fe1d65887400043ec3acb10e8008c3e7459621d000187ccaba443a00030f59574887400245f426ec90e8008c3e7459521d000187acaba243a00126e20174487400461f3a2ca10e803d8bf865d021d000187acaba043a01df99995210874000732b2a4210e80a6a7b805d165901250fb0f39acb201c28fa1273596400051ec24e6b2c8000c5f739cd65900018bf06b9acb202461fa1c73596400043f43c86b2c800087d8790d65900094f50121acb200029e60243596400051fc22e4b2c8070a3c845c965900e147d08392cb200028f61072596400043f43e64b2c800087d87cc965900010fd0e192cb200021f61c32596403851f42064b2c8000a3d840c965900014ed02192cb200029d60432596400253d40064b2c8000a79800c9659000147f08b8acb201c28f21171596403851f420e2b2c8000a3d841c565900010fd0f98acb200021f61f31596400043f43862b2c800087d870c565900e147d0818acb200028f61031596400053741062b2c8000a6d820c565900094f50018acb200029e60031596400062fbaceab1c806fa9e849d5639000153b093aac72024a9761e7558e400070f424eab1c8000e1d849d56390001cb6813aac720247961027558e400062fc3aeab1c8092c5f705d563901258bae0baac72000396d017558e404972c202eab1c8091a5e851d5639014b5b700ba2c720293a61017458e4037f0f2a6a8b1c8004ada80d5163900015b301aa2c720002b6e015458e400256c402a8b1c8075e984055163900014bd0bb92c720002976177258e400054fc22e4b1c806fa9c845c963900014bd0a392c720002976147258e400dd4f420e4b1c8000a9d841c963900015ad02392c720002b56047258e400256d400e4b1c801bad9801c963900df53d08292c720002a76105258e400052f42ee2b1c8000a5d85dc5639000153f08b8ac7201bea72117158e400052f428e2b1c8000a5d851c5639003753d0838ac720002a76107158e4000567410e2b1c8000acd821c563900095b50038ac72006eb66007158e4037d4f420a2b1c8000a9d84145639009b17d0f2a2c52000b0f1d65458a4026c5f43e86b14800287e85dc562900010fb0bb8ac520013369c16390a4021f4c202c72148000cd9635c242900010fb0dbaa85200031798f7550a4051c3e43acaa148000c5f7558d42900018b8eab1a8520013361c16350a400066cb1ee0
  | 12 => 0x9daf120d70484213bdb3428e09084200b65851c1210840174d083824210802e961070484213b5e3418e09084200bc5831c121084050fd0fbaac0108021f60f75580210045fc22eab0042088bc845d560084014bb063aac0108030fdd774580210061e3aee8b004200c3f751d16008401878ea3a2c0108021fe1573580210143e42ae6b0042008bf845cd600841117908b9ac0108021fa1f53580210143e43ea6b004200c3f74d4d6008539878e9a9ac0108021fa1d53580210043e43aa6b004200c3f7454d6008537878e8a9ac010807179cd53580210062eb9aa6b004200ce78748560084019c90e90ac01080399dd52158021007323aa42b004200ea7744856008401d48e890ac01080339dcd215802100672b9a42b004200e67534856008401ccaa690ac010803b8e0121580210077040242b004203ee37048560084058f0eb282c010803b8486505802101c7c43aa0b004200ee1215416008535970e9182c010803b8486305802101c7c43a60b00426fcb8744c160084039b0e6982c0108039654d30580210077090a60b00429cc3f42dcd65d013987e83b9acba00030f90373597404e61e206e6b2e809b87d879cd65d00018bee739acba01d69ea0273597400053cc04e6b2e80aaa3f845cd65d001147908b9acba00030fe1173597404de1e422e6b2e8000c5f835cd65d013787e84b9acba026f0fd0573597400061f202e6b2e809bc3c405cd65d01390fd0e39acba00228fa12725974054d1ec24e4b2e8000a76819c965d00014eb03392cba00228fa1072597400f51ec20e4b2e800087e87cc965d00010fb0f992cba00228fa1232597400051ec2464b2e800087e870c965d00010fb0e192cba00228fa1032597400051ec2064b2e8000a76810c965d00014eb02192cba01d69ea0032597400053cc0064b2e8008a3e849c565d015147b0938acba00029ba0a715974000536c14e2b2e8008a3e841c565d003d47b0838acba00021fa1f31597400043ec3e62b2e8008a3e848c565d000147b0918acba00021fa1c31597400043ec3862b2e8008a3e840c565d000147b0818acba00029ba08315974000536c1062b2e8075a7a800c565d00014f30018acba029e8fe1170597400043f43e60b2e800087d87cc165d001147d09982cba00028f61330597400062eb9e60b2e8000a3f844c165d001147908982cba0003175cd30597403af1c20260b2e8075e58304c165d00050fd0bb8ac5a00021f6177158b4000e6d39a60b168000e59534c162d0001878ebbb285a00030fddb7550b400051f43acaa168074a3c8759542d000147f06b2a85a00028f60d6550b400461fb92caa168008e2f7259542d00eb87ce0b2a85a01d70f1c16550b4022c5ec36e2a168000c3d65dc542d00050fd0bb92c3a00021f617725874000e6d39a60b0e8000e59534c161
  | 13 => 0x54ec18a0b244203ab681141648840156b02282c9108022fa1f30592210045ec3e60b244200a3e85cc1648840147b0b982c9108038754f30592210070ea9a60b244200a3e850c1648840147b0a182c91080eada0430592210055ac0860b244200e99300c1648841196cc8b8e85108021f61b7550a214861f326eaa14429087e8759542885430f90eb2a85108030fdd56450a210061e3aac8a144200cb564dc542884050fd0bba2c1108021f617745822101c7c43a60b044201cd8734c16088401cb2a6982c11080e3b60b75d912103c7ac0eebb22420087f855c364484050f90ab86c8908021f60f75591210046fc1aeab2242018dc835d564484011f700baac8908123e20175591210161e3aca8b2242accb87095164484051790eaa2c8909d72e1c154591210062fbaee6b224200c5c75dcd64484018bf0bb9ac8908031721773591210043fc2ae6b22420287c855cd64484011f700b9ac8908123e20173591210062fba8e6b224200c5c751cd64484010fd0fa9ac89080a1f21f53591210062fb9ea6b224201c5c73d4d64485238f0e1a9ac8908021fa1d53591210043e43aa6b224200c5f7354d64484038b8e6a9ac890a4b1e1c1535912100e4e39e86b2242abcb870d0d64484031790ea1ac890807271cd43591215265c38286b224200c7b75dc164484018f0ebb82c89080336dcf70591210066c39ee0b224200c7b53dc164484018f2a7b82c8908031edd470591210063c3a8e0b224200cbb741c164484019b6e6382c890803361cc70591210461f322ea32242008bf87590644840187aeab20c890802ae201641912128c5ec3ec9a12428fd6421dd5424848b17b0fb2682908021fe1576505210143e42aeca0a42008df835d941484031b906bb28290a1b5908775505210043fc2ae9b02420287c855d360484011bf06ba6c0908063720d74d81210062fb9aa7b024201c5c7354f60484099b4c0b98c0908023ee1d60181210055c422c03024200cd97358060484050fd0fbaac8108021f60f75590214343f438eab204202c3c7595164084071790eaa2c8108021fe1573590210143e42ae6b20420087e87d4d64084050f90fa9ac8108021fa1d53590210043e43aa6b2042038bc8750d64084079cd0fbb2421080399a17764842100732c2eec9084200ce775dd921084019caebbb24210803a9a13764842100752c26ec9084200ae783dd921084015cb07bb2421080399d4f764842100732a9eec9084200ae580dd921084015cb0d3a24210802b9e197448421005b3c2ae89084277b64855d1210840178f06ba242109daf120d7448421005f1c02e89084200be0805d121084ef6cd0a3a24210802d9614744842100572c34e09084200ae7865c121084016cf0ab8242109ded92157048421005d3c22e09084200ba4845c1210840178f06b824210
  | 14 => 0xe85cc564c840147b0b98ac9908028fa1770593210051ec2ee0b264200a3e859c164c840147b0b382c990802a7a0e70593210054ec1ce0b264207aae829c164c840117d0fa82c9908022f61f50593210054f418a0b264200a9d8314164c840f55d04282c990802ab60850593210045f43e60b2642008bd87cc164c840147d0b982c9908028f61730593210070ea9e60b264200e1d534c164c840147d0a182c9908028f614305932103d5741060b264200aad820c164c8401d3260182c9908232b99172d07210043ec36eaa0e4287c3e64dd541c850f0fd0eb2a8390a661f21d65507210061fbaac8a0e4200c3c7559141c840195ac9b92839080a1fa1774583210043ec2ee8b0642078f8874c160c84039b0e6982c1908039654d30583210061fba4e8b2c42afa77815d165884074e902ba2cb10a521f61e73596210062fb9ce6b2c4203a76819cd658855d4eb0339acb1080317e0d73596214ac3f438e6b2c420087e8790d65884010fb0f21acb108029ea0243596210053cc0486b2c420087e8710d65884010fb0e21acb10ab69de0572596210043f43e64b2c420087d87cc9658840147d09b82cb108028f613705962101d3b40ce0b2c423ba75819c165884014bd06382cb108029760c70596210043f43e60b2c420087d87cc1658840147d09982cb108028f61330596210062eb9e60b2c4200c5d734c165884010fd0e182cb108021f61c30596210072c98060b2c4294a3d8594e6488401c3ea729cc91080387e0d53992214ad1f428a73244200a3e85cca648840147b0b994c9108222fa1f50992210045ec3ea13244200a9e83142648840153b06284c9108222fa1f30992210045ec3e613244200a3e85cc2648840147b0b984c9108038754f30992210070ea9a613244200a3e850c2648840147b0a184c910803a64c0309922101c7a40aeab2442038be87d51648840187eebaa2c91080b0f9d6545922101c5e43aa8b2442038be8790d648840147d0b21ac9108028f61643592210055d40486b244200ab98090d64884071790ea1ac9108028fa1443592210051ec2886b24420287e85dc164884010fb0bb82c9108030fdd675592210055bc0aeab244203ab4815d5648840147d0b39ac9108028f616735922101d5b40ce6b244200ab5819cd64884015750139ac910802ae60273592210051f428e6b244200a3d851cd648852947b0b29ac91080387d4e53592210070fc1aa6b244295a3e8514d648840147f0ab92c9108028f21572592210054fc1ae4b244200a9c835c9648840157700b92c910802ae20172592210051f42e64b244200a3d85cc9648840147d0bb82c9108028f61770592210051f42ce0b244200a3d859c1648840153d07382c910802a760e705922101d5b40ce0b2442008be87d41648840117b0fa82c910802a7a0c505922100
  | 15 => 0xf992ca208021f61f32594410451f42464b288200a3d848c965104010fd0e192ca208021f61c32594410451f42064b288200a3d840c965104074ed02192ca208029d60432594410053d40064b288200a79800c9651041147d09b82ca208a28f613705944159d1fc22e0b288208a3c845c165104014bd06382ca208029760c70594410043f43e60b28820087d87cc1651041147d09982ca208028f61330594410062eb9e60b28829ae38408c1651040147f08982ca208228f21130594410062eb9a60b28826fe38404c165104010fd0e182ca208021f61c30594410072c98060b2882038ec874c96210401878ebbb284208030fe1776508410061e42eeca108200c3f53dd9421040187aa7bb284208030fddb75508410051f43acaa10827da3c87595421040147f06b2a84208028f60d65508410461fb92caa108208e2f72595421048b87ee2b2a84209170f5c565508410061e382caa10823c8bc8750960104071f10e982c020807361cd30580410072ca9a60b008200c3f749d165c85654df04ba2cb9081e9b20974597214f43ec3ce6b2e4200c5f739cd65c840f4dd0539acb90ac69b60a73597210062fc1ae6b2e429f87e871cd65c84010fd0f21acb908021f61e43597210053d40486b2e4200a798090d65c84010fd0e21acb908021f61c435972158537c12e2b2e420087e87cc565c84010fb0f98acb908028fa1370597210051ec26e0b2e4207a6e829c165c84974db05382cb9080297a0c70597210052ec18e0b2e420087e87cc165c84010fb0f982cb908028fa1330597210051ec2660b2e4200c5d73cc165c84018bae6982cb908021fa1c30597210043ec3860b2e4200e59300c165c853d47b0b29cc99080387d4e53993210070fc1aa7326429fa3e8514e64c840147d0b98cc9908028f61731993210445f43ea132642008bd87d4264c840153d06284c990802a760c50993210445f43e6132642008bd87cc264c840147d0b984c9908028f61730993210070ea9e613264200e1d534c264c840147d0a184c9908028f61430993210074c9806132642038ec825d564c840f17d0faa2c9908030fdd754593210161f3aca8b2642078bc8755164c840f17d0f21ac9908028fa1643593210051ec2c86b264200aba8090d64c84015730121ac99081e2f21d43593210051f42886b264200a3d8510d64c84050fd0bb82c9908021f61770593210061fbaceab264200aaf825d564c840f55904baac9908028fa1673593210051ec2ce6b264207aae829cd64c840155b0539ac990802aea0273593210055cc04e6b264200a3e851cd64c840147b0a39ac990a7a8f61653593210070fa9ca6b264200e1f8354d64c853f47d0a29ac9908028fe1571593210051e42ae2b264200a9f835c564c840153906b8ac990802aee0171593210055c402e2b264200a3
  | 16 => 0x2582410061fbae84b04824c8bc87509609040187eeaa12c12080e3e21d305824100e6c39a60b048200e59534c160904010fd0db9ecaa080a1fe1f63d95410062eb9ec7b2a820087d8798f65504014f50131ecaa08029e60263d95410043fc3ac7b2a822a87d8718f65504018bae631ecaa0a1a8f21943d95410070e31a87b2a820087d879cf65504018bf06b9ecaa08021fa1c73d954143d1f420e7b2a8286a3d841cf65504018bae639ecaa0a1a1fa1e43d95410043ec3c87b2a8200a7a8090f65504014f30121ecaa0a1e8fa1372d95414351ec26e5b2a8287a3e849cb655040147b09396caa08021fa1f32d95410043ec3e65b2a820087e870cb65504010fb0e196caa0a1e8fa1032d95410051ec2065b2a8286a76810cb65504014eb02196caa08029ea0032d95410053cc0065b2a828787e87cc765504010fb0f98ecaa080297a0e70d95410052ec1ce1b2a8200a3f845c3655050f47908b86caa0a1e8fa1070d95414351ec20e1b2a820087e87cc365504010fb0f986caa0a1e8fa1330d95410051ec2661b2a8200c5f73cc365504018bee6986caa08021fa1c30d95410043ec3861b2a8200e59300c3655054587ae832ec4a09462f61e54d89410161f3aca9b1282518bd87d0f62504010fd0fb2ac4a0803171cf65589410043f438cab128200c5c7319562504018becbb9ac4a08031719773589410063db2ee0b128200c7865dc162504018f6ca382c4a08031e19470589411f65db20e0b1282008ef8758862504018e8cab8c84a081f3918971909414361f3b6cb2128286d3671d964250401c5ecbb1484a08f62f21970909410049fc2ae121282a287e86dd54250521a6883baa84a0a8e1fa1f655094143f16216caa128200c3c659d8425040187f0b3b084a08030f21676109410061fa9cec2128200c3d539d842505032790cba884a08024fe0d75109410049ec1aea2128251c3f625d442504a387ac4ba884a08230fd8575109410469bb0aea2128200c3c605d4425040127f0fb2884a08030f9db65109412145e432e021282018fb874c360504039b4e6986c0a08039654d30d81410062f39ecb3028200c5e7319660504018becab9cc0a08031719573981410266c302e73028200cd973d8260504050fd0dbaac0a0a1a1f21b75581410043f43ecab02820087e87195605054587ae8328c0a08023ee1d60181414e61fa16e6b288295c3f41dcd651052b87a83b9aca20a730f10373594414a43ec3ce6b288200c5f739cd651056d47f08b9aca208228f21173594410061fc22e6b28829bc3c845cd65104018bf06b9aca20a6f0fd0973594414a61fa0ae6b288294c3d415cd651053787880b9aca20a561fa1c73594410451f424e4b2882b5a3d849c965104074ed03392ca20ad29d60672594410451f420e4b288228a3d841c965104010fd0
  | 17 => 0x2a8400a5e839c365508014bb07386caa10028fe1170d95424851e422e1b2a8490a3e841c3655091f47b08386caa10021fa1f30d95420043ec3e61b2a8490a3e84cc3655080147b09986caa100317dcf30d95420062fb9a61b2a840087e870c365508010fb0e186caa1003964c030d954251e1eba0cbb0a84458bd87953615080587ceb2a6c2a11162f61f43d85420043f43ecab0a8400c5c73d9561508010fd0e32ac2a1003171cc65585420062fb2ee6b0a8400c5c65dcd61508018f6cbb82c2a10031e19770585420063db28e0b0a8400c78651c16150887976c8382c2a10023de1d611854200c7dc3a61b028401cda734c36050801cb2a6986c0a1003179cf65981420062f398cb3028400c5f655ce60508018b8cab9cc0a10133618173981420066cb9ec1302840287e86dd5605091f0f90dbaac0a10021fa1f65581420043f438cab0284a3c3d7419460508011f70eb00c0a127f0fd0b73594424fe1ea16e6b28849cc3f41dcd651093987881b9aca2127a1f61e73594420062fb9ce6b2884b9a3f845cd651081147908b9aca210030fe1173594424de1e422e6b288400c5f835cd651093d87e84b9aca2127b0f50973594424de1fa0ae6b28849bc3c405cd651093f0fd0e39aca210228fa1271594424051ec24e2b288407a6e829c565109714db0538aca210228fa1071594421851ec20e2b28840087e87cc565108010fb0f98aca210228fa1231594420051ec2462b28840087e870c565108010fb0e18aca210228fa1031594420051ec2062b288407a6e820c565108014db0418aca210029ea0031594420053cc0062b288408a3e84dc1651086147b09b82ca212de8fe1170594420451e422e0b288400a5e831c165108014bb06382ca210021fa1f30594420043ec3e60b288408a3e84cc1651080147b09982ca21003175cf30594424d71c20460b288400a3f844c1651081147908982ca21003175cd305944237f1c20260b28840087e870c165108010fb0e182ca21003964c0305944203c7a43a62b0884078f8874c160108039b0e6982c0210039654d30580420143f43eeab168290c3c74dd562d04010fb07baac5a080e2f2117558b4150e1e3a0eab1682528bc8755162d04010ff0ab9ac5a080a1f2157358b4101c5e422e6b16820087e87d4d62d04050f90fa9ac5a08021fa1d5358b410043e43aa6b1682528bc8750d62d048717f0cb8485a08024fe157090b4100556c20a4b1482038ec874c962904018d8eab12852080f391c56250a4147e1fbb6eaa14828fe2e62dd54290401a6eebb8a852080a1fa1f75582410043ec1eeab048241c3f41dd5609048387a83baac1208030f90375582410061e206eab04820087f855cd60904050f90ab9ac1208021fa1f53582410143e43ea6b04820087e8754d60904010f90ea9ac1208fa2fa1f4
  | 18 => 0x1401201800800800000000400000600200000000200400403e01801401a00200202601601a00000400000c01600a01000000000000000600003000200c00a00800201000400002a00a00200001a00400000601e00000200001600603e00e01000600000200602200800000000002602a00800000200a00001600800200201000000a00002600000200802000800000800006200002202600000e01000200a00800000001401a01800200c00401e00200400001600000e00200200200000600a00200001200a00200000600000a00c00a00202800804a01600400000402c00000e00600800000200000000400601401200801400000400a00400200e00800803000000000000a00400000200401400000c00000600001600a01200e01400203201200800600002000000200000000600a00000c02800e02400000000400000600000000000200600000204a00001600800200400000400801800200000000200000600402600200600a00000000400a00e00c00200600602600800201e02000202600000a00000801600200000001004000200800001000000a00201403c00400400c02a00004200e00400000400e01200e00c00a00c01a00c00000c00600000201400000001400600c00200200800800000201e01000200000e00000000400000a00200000400003e00400801401600c00000600200e00001200a0160060560240000020020060160060420000287e87dd561d090f878e9baac3a10021f60f755874203c5e422eab0e8499c3c741d561d088d1790eaa2c3a10021fe1573587420143e42ae6b0e84078bc845cd61d08010fd0fa9ac3a100a1f21f53587420043f43aa6b0e840087c8754d61d088d1790ea1ac3a1002ad610515864203c7a43a62b0c840287e87dd560908010fb07baac12113f0fd0b755824227e1ea16eab048400c3e40dd5609080187881baac1210021fe1573582420143e42ae6b04840087e87d4d60908050f90fa9ac1210021fa1d53582420043e43aa6b0484078f8874c160908039b0e6982c1210039654d30582420043f436e7b2a840287f87d8f65508018bae7b1ecaa10021f61e63d95420053d404c7b2a8400a798098f65508010ff0eb1ecaa10ca1f61c63d95420062eb98c7b2a848fa3c8650f6550801c38c6a1ecaa10021f61e73d95420062fc1ae7b2a840087e871cf655092147d0839ecaa123e8f61073d95420062eb98e7b2a848f87e8790f65508010fb0f21ecaa10029ea0243d95420053cc0487b2a849087e87ccb65508010fb0f996caa12428fa1371d954247d1ec26e3b2a8490a3e849c7655080147b0938ecaa10021fa1f31d95420043ec3e63b2a840087e870c765508010fb0e18ecaa12428fa1031d95420051ec2063b2a848fa6e820c765508014db0418ecaa10029ea0031d95420053cc0063b
  | 19 => 0x200020000000000000a405d03421e5108052cec208c000264906456a1f4071840621902315605b068a026a6e43b80002faa5187547760000e100003a94b1a0bc9800002ae84c062041a0011fa8b0600031ba1a0a3c26c280865060a9fc38b000088214f3b82078cc60f7129035cf822753399be8ef20004480000a2475f03b0b94eac30b3140c70e5286c126055823c61c4218cb826472317e98f12f47a91d399e0f0e0003311e693d223e4ae0e880000000c71930ea262b000174800091149180000000fb1e58f0cf5a0001470b482ae0003410800b1e00005384a40000510600001122000000000072c1272f39ae40c01190000a512ee88943b9e54cea31323b02249001a945604e001600000c00802600001a01400000401400800000802600e00000400000005a00800200800c00000001e01400200602200600200000000001000800401c00400000000000200200200a00000a00400000200400000601600600000002400400800000200202400c03601200400201800800000000002400000200602200400200003200800000a00008603400400a00400200200800200c00000001200000e00000200001001000600000800a00a00200002a00002600000000000005401800403e00400400401000c00002600600600c03e0040aa02400003000400000400000000a02200a01a01200c00400000400201800801600002c01000401c00000000e00403000200000e02600200c00000e00a00600201e00002200400400400000800000e00601000200e00200000003e00202c00001e00002401603200200c00000e00000200000400000203a00201200200600000200600400600000600200402600001801800e00000602400c00a00600000003e00400000000800000000000200400000401000400800600400200602600600600000000001200400000000000004400600000000000000000c00000000200e00c03e00000804a00200000c00600400000000000200200800800801600400600200c00600800002e00802800e00200a00600001000201200400203600400600000801000206800200600401200000800e01002801c01e01a00000200200e00203200600c01600800402000400a00401a00600000c00000600000203600e00a00600000400200800402400200800000600a00201400a00200001208400601c01400000600c00202801a00600e00004600a00001401000200401400000801800400000800800000200600000200601401600002600000c00600e00201600a00404a00800201801400800000c01a01e02201603c00000a01c00000400000400a02200000600a00400200200a00000a00200000800800c00000200000200600400001000000000402000a09e02202c04200000001c00c00001001201e01c0000020180160
  | 20 => 0xcd8000c2a6bf1f800012ae8b70000e4c0000000001604f487280002774d742ac00023bca8e7f510a101c1dc6901dd97ed0167f81ed185112e0ef1599c811d437a19089790a40003c923987f467023782d400009e08e182c9106fd2e6a1c11a000027b96709e60001461e34e726e537c17fc69800000000008c01e60b9a70c3449e5000272800000000023a01340000001ef800000026200013340002df976469a0002110828dd878f176a18c47869e000237c00034805e0000a9256200009b40002760001a300008cf00021f0000000000211c2983301f284b85ae85d0cfa72ce2200024b000041c8d21fd80000005050001350842000000000000010d000000020c00021380000007941271bd85c24aa0002448c48758000002c4520000001725096634059096cf5c26800027ec77200033f1b2490a3a31ec800116450b0b312ace8a9f72ab9e780006be15c04b4e4200047c0000ab80000000af914a3f84b6a2fc3ce377000103c0000002270000a505670001f8800000023c110c00000000009e4a787af00000000002c240d800120000000000011ac70c000032ca2c84f02e8000faa0f91210000000000064075461463a0fa89ac3560002da03f84c00000a116a908217a16e813904c0000000abc0000000000000c6679900027c41e495d1cf1d5c5140bf155a43c7cc08400020b80006ce0000b1d35c00009d14880008f113e00006689751650b905d49a12a18aa017237026c98a45be6bb00023652fa00004191244885fe4ad00003d80004510db4c248e000010a800000000012d53706a80360000a341b342ca4f832a000000000094c05f0ac000000078e2f89cd496e0222b00000d4447700008200003e12b2239c7500294f800000860001ef19c90e20003c8a644a4e2304b8a4740c800020e913527608001ca4892283013530c50ce24cb312a1400000003cd85bc0000b312e22a49c61333638954e4e7e82408000f42104000006c0008014a898b800062f2b495a09d20004d3a34400004b45381200f600010e9cb801c3e03500000c4676f28e800069e6193b596ecfe65be3f62188c1a55b0df99e40000000001c7120200000000001ea000247166917629a06f9efcebc896256000057e8f925f11f837428405b1d893a68dc00519b488a94c015a4c402a9581cfa8180a09db28c93581b246c03880c830c8b93590e3cf1429e2d398049080381dea768d828c605691a4548417412102c2a41d12b7244120685738c00013de92f4648be80000000c6082c0000002f31f3c00027e18b800081000029d201060e2f40002178f2071a20c88a03804381a90001044000451987894e0000000000dde89846398b09849aa2578370294854370016cd0295523913283842183251828cba1640040af10287f200010612cc734000000016825d00023294
  | 21 => 0x2503eb0f4c0008a608d06c870200000e91c133e0005020000b28458000053447400034a8bc81220003ef007000080820080007ba39722f0000bde5b10000f251429610228bbc75a0a400013a0ca23614ff8f3d0d257900007c492a24a4150a7021800041800009e00004940000e620002d000013bc842000000110e494000000002e04f000126043e03c477030800001a21e14d928a0bd1ba8000bb82e60001f0817c926206a5585045b82338a4c94a0dd1aa0ec8d9882142f8000a567f70138000f4017905080012e41da000000000039500008592880002101e703587120098b4d38e87b27e1a9c3c46672ba844c3005cf2709ce000031925008940007e60000ecd0fe0000a709c862457d0000920c8a2e732918406e200012c93200001ae0e296200000000eb17cd3086d3484997873672d236819c56c44f221026448a3152fe224cbfa271010084c54e88507121e5174063490868000000016a01d13d087849a8c090784a90d68d900004dc4900330b322062eb090d1284462ca90181f400000000000004f202b8614082773256909068e6f421b99992148463e917a485209411592ccbaa2eb0aa8a3c19e76e252105435e4e21600368e8067d461833909a316347800109013449b836000046300012709cc6e93dd021800005a2468ce02f01d23bf97e432c0004cd95c521a0000d196b40008b14df915402284a01a952c8b256100013b4df8000000108cabc22019900000001184938000a4c0001f389580000004cb000005e5100bf00000000002d580010a60000910edc0000f43ea0000000a051dd00000000004379dc840e21b000046c1ce5e000022040009d63a308e04e83df0000db80000000000ee121c00049a00000006aa0b0851c00047b2a8194c47a0001f1000000074d3b41b547aa1970e680dca845b709b95c0eca58b290a1688a636245a917026239431a80005a200046a00000000000000000b4a58a1418000ffe0001118c9867237626a8e6100420c44e03ac7fc2ae0c500003d60001c392f0e960004dda410cf698e00027e80000000000df0c727020000d5828200008a80007060000000c8c4f000009e951842a7fa1b58ad4df67df37120d11328172cd9b70f7a30c3b522d92a634b1428fc81045c44cf14501fa0002da800000017c32ca6dc03248b0000000c7a0003a980001e69744699e984420002f100000006741ad00003989bc494a53938c0004bc2268ba876900023303829ba3aa800098e7442660b6525c693084981d2807a837716a06bc40a3c280013c646b0001c1c9825c6000256442433632d9cd8dee00029d8f5c46661d38308d8fd27d0124a7d846a30040988dd0929703dd86943a054141fa4cca0662d1e5263518808f00010a000094348c011c0006c50000000a5e23218da0ed20c00014408a90980000
  | 22 => 0x4c5800000000000011301c85874fa9b5c4ce1ea2e11bb4f8a07d2960f111c46df0001f4c00033e00002380000004d780010c00002010cec000000363187c0006ae0001f808ac7c8174000039000022500000003e40891fd0c2c45a4b00de01cc0004db24ac1746d11b609685ec3d001ea0d8c849ab389a1c87188b33e60e988c47b30000000c3086500005b913a00033000010004d04d309b8b8a00048a8c9492690c078a0e0d7000017c9b740006f300011209a206d0f48000012000406a0d4dc600021991111aa000000216082635c49299f04c46444f11608dd41cb107a1f426a72529485d90208821298ed843843b0fc000000094d3d92158c3600000002ac4040002ed8ab476879f18d12e84582704858ded0fc8fa19502a052e6a900026b414c0000000f3895000000025880002691b3a4f0000000000000000049d00006f4000919000063c00051500000009420002d914603c63604049c547c65f817aa77cd5a000000093c00086a1c494093a441200007245aa0d12efa4c929658d174a3ac2e453540d20f91e66b40001a70dbc2a503b8000000000000000000030f00010d093257f42719340000e807e00008384e536426900005900001818a9e7da18f0000e948be1ee10980008671ac8000ec600009312c4e061204401fc00aa0ae34d80011fe5200000c9c0000003c49bc4a7200000026c000071e0000aec000344000000092448a0000fb83f600040799a8e321a73e880000003660c690c4fb6014049974491e6fe31306dd36274e4d4a71519c000298a280f0800029e8000c9e34000005a800032d39e9ddd1104914a5000098c0001e00000e826924fe81e8000151000000036c9d538096c00000002f708ecffa1bc000000111c11f3850ed4904000135036c000000000000000000000000000002a926d8000a2e0002d996480009cf000000000000000023d80008123a1800000000000013ec00015c48da070f1077b2cb800085a6b50ad14c8c2242b3b887f84fe6004201f600001630f408047d804a4f58b5800000012300000003ac2f298fccae0001a280000008283f5a62065e6d2076800000025f432000000057a16e00003b0000000220c6f278c26990b80001751d704ac0002574cc0dcc8e282c000000020a20900801fc0005a100000001d80004be00840000000000000a6896b0001184000380000133c00000035e1eb008007037f807c0989e034b2624ea43bf03491940000001958000f540000000778c6c00033780012908f00e700007de96c0000ac401e97e01f80011143c6446000000000040b0a600000003979ff912a22238b800096864318411cc5324573db21b939236f0000ac912428707c244c00060e384236103207812a163100a9072dea6cc87c4a34f70408ac600000005883de9e700000000001710000ad0
  | 23 => 0x7d685c24d054d13c386318856cf785a41a9959419a9c238fa5a12343181af9cec0008f730294e12a0296343142530239c00011406b600000027381d44254f6027c0ac00000008d0b2218939b94100000b7000137c0001441a099a43f437f000014d39a8cb2850d6043c8de000012400022f21d18251f841e03580000003353be13ace482911e091006940000120a4800000032300000005771068000000000000000058c1e446415e00000000b622b814a000000117c0005e300001a92100003ad8000000003000000000051b0f980011800004f993f8d480590439bc87b693f40e8e80f042b92180ae933a15f48e081454c0440b39af46746302929a74ae40281b282c403068038a159850057c29703192be1f61f88e483e800727b0fa800205807804a8ad69a221c8e84ca87ce3802640d088e919fa7d088e66e0b0192c3f8072191277120a96e460a6f839e34342a835133200000000000007c94a080300002391e9034ce1a1fd13195d00002401a8885c7f8586000000000000000000000000003cb02748f400023c80000000000000000000000360000066e5c30e99f2c60875a00027851ca2ff0ea17600009932de0328aac368000216d04a7ee35794a8cf406130781f80a487a06f0eac0000004309a845e277a4b39fc4d227302e39d5039450d3d39ac024a05e49813384ca5ca1849430b4450f454209ca9a1171c68ac059e18715500009de9b221e8c90b980e90682218bbc97b00021d132864700000000004f800004a000041f194a0e80b80003fda30822c4ea4a10bb024249f304028cf7054a0da1c8836a6db1d80000d9a4f14bf95cc5f00000bda57800000000000002a81e020d80009708230000000bba3c73208d3890e73c36c27901ac93d000090400096925b1db40000000858ff40000922db00008cc00001699acd560001c122f4a384743a380010221d70000000000000000149038e6030151a38e20000000000000000016f026000080c09d82bc7ac76c4551d9c43410f3e3a5bca906500dc8e94f681db34c0394cec37441ea6d40006c34c602c11f69951e88150b3a86d071a52501c1c4166a018eba9f20df0ffc6ba25100006780006e60d5100cd6c00014f94385e6640471a0e4f443cd000000000000030600c400000000000002780000001f28fde1f73fb069891271d37204903342263c024581aa5511819f34a0c43647689603e440e32e19203048b00028cc499a4ae4e2168cbd00b80dc227cad82fb4c1112c0008b42f913148227a52700000a461011d8957d34a1503a81a7c10256f2e800343e08ad0c090500006644e080004c853331123d40000004d60000caa4e700000000000002bb27201ec54e16280009600002fa00006e43064221d700f29d83ee9324b807b92a288c4efa3c83cea2bc00048c4628000d66000
  | 24 => 0x416588b80003d836505785f84354559cfc0001701a312789fa4b226c223c1445ba08400e800088d0160000b1ca022c4a4d92ca68d3f28d413a847d2d6026cdb26040001dd46225f01fc8674fb2000130a7e09ae4090001ab000012c2d30000bec3c21fb80008f800040c1f5c000000403a6706ae0003848000f5600006191b936824d1398e280000004810bf80004c34a3a02922e9a01aa9b588fe98337a92f40001451258ef897e40543b0e74ada4de466800000065831000013fc1a432d214477801e3ba1ec00001ee336018865870514080cc3869cc13d9b8471c43f00000011785444de800000013e3a480000004830000ca0d1673a0002374a8027709f83fc5b45c13951d0811427a3f182400003330001f0c00096436580012b630e2cf0384af600029801a094400000020cd3f25ea000000073400050197dcef04f516423d0e568e408a166000055300021ac0009a30ce00009fe6eb4e805acb724ec000031c00000000018ec7ec75925c9ff0a6e2c10000a6c0003f50000000b0869a31500008d03cc16184bd1080000001e8c2d21ff3bf0cf0db413601712186fc38500200002142c949203045407dc00023b011a57e4f500005444bb00020ac00009522925d89ba40434b800000070f0001d98d880004cb8000f026c20000c7cb9082935b8000308000000051800096a01b189c0005da0030000de072c12381cca0e00027224a874820450009bc4cc41027c99dd170096000000000000000000000000004c7973800000000007745c49d1217800092e000070000125868528420dc00000000003103b25ec00b1b502ee0004eb800130007522d822c0cc1881481fe40004fa0181e2c2463490c984393cc82026d1a1c59c74c11f98e08182ee0a000002226a54c31d210e600021601bc00000049d0fd0bf455a27705fc0248fd00004742d03f300000001761432691d3ca7c0aa22e81091ae89b0001c2d1161902969b3c11051333096012f29733d88574e1c68820b0e211e473e3e21658000000144a53cb0a4320690c343060000649ccc07c7b71458524936786000000000000000000005a000000021145428db10891450625ed23a91905e03990d4270050c2a305013d0f260340d8800071692d2ac8000a3e9541c88000f3009c38d86ec5c053f19ea548e4c00034c8da40000002d4924004c0230429a240007602f080000000000000bdcaaa91f32b000000059300000000002cc00000000000000000000316191000000020660209c8000c343af00009f4c2e7ed4f68660ec81590b68784a0059f0000fa4fc28150001ac4a220000b2800020e00033f9924b5c7b51ea153000022700004000003c51b5197c53a5d30628e4103e2e34c382a51b400001285f4bd60000cc8000f8c11000000006c631d1469f00dd00000560000c9c5cb22a000
  | 25 => 0x238514868314a8adc00007c319077c0dc55448f1a8c00055200007b4cd03421be8000d2866549c8890bc80000fc80000005d70001e5d05a621000262812e0000001cc91fc7e44c280000008663f38c803600000c91be50ea6e731f0af4f069d94d400007da6d016d80ec58861340191a845a0002d7a4e00ca70
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x105a0000002c00144e5058000000000000087c000056040000002830000000001244543c8c00848e1c2024000000860000000000004232227600781e007246260e005c52367e6488000018383a00000040006c7000003e00000080006e5e4a1a0000002a007a8a6068166a0000663400004c0c00482e007406620a820202001050004080021c08000002030c0008104000810051625d534c16090975c18405cd30594420051625d534c1609040103c9660d75109415d706101734c1651040103c9760d6550841006a2609300c164c8401a91814c030592210060e5d4805906448401898845cd60181210059164e85dd92108401a2685a13764842100691e0d53dd9210840141d931d774580210050764c751d1600840505c985cd53580210059164c754856008401c24751d1215802100439261734856008401c457354d2158021005986548048560084016a1942012158021005b064c8048560084014589754d30580215d7061d1534c160084012e09848530580210079054d214c1600840103e9890173597405d706101734c165d000103c9760d6550b400040f25d8359541d00eb8388059574487400040fe59835d4429000181f8698d7510a4037f06981635d4429000103f9660d751064000607e1a635d441900dfc1a6058d751064037e26211635c02190001c616548570086400073058d215c021900014589754d30588400253225d324c16210001c19534c176908400051625d534c161100094d0974c530584400070654d305da41100014589754d30586205d7061d1534c1618800145a96dcd30d952000586259534c3644800161993195301912000586654634c0644800161a9654d301912000586259534c064481776199594d301912000586657324c0644800161995cc530191200051625d534c16284175c187454d3058a1000516a5b734c365440016189654d30d91100058664c654c064440016199518d301911000586a59534c064440016189654d30191105dd86656534c0644400161995cc9301911000586657314c064440014589754d305891000e1621d534c16244175c187454d3058910
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80019000540b4742d09bb24210802c05a31d4744856008401422542e6a9a42b004200c90261534853058021
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4c
  | 6 => 0x4e
  | 7 => 0x3
  | 8 => 0x5
  | 9 => 0x94c
  | 10 => 0x94e
  | 11 => 0x124c
  | 12 => 0x124e
  | 13 => 0x138c
  | 14 => 0x138e
  | 15 => 0x8c
  | 16 => 0x8e
  | 17 => 0x98c
  | 18 => 0x98e
  | 19 => 0x128c
  | 20 => 0x128e
  | 21 => 0x150c
  | 22 => 0x150e
  | 23 => 0x10c
  | 24 => 0x10e
  | 25 => 0xa0c
  | 26 => 0xa0e
  | 27 => 0x130c
  | 28 => 0x130e
  | 29 => 0x180c
  | 30 => 0x180e
  | 31 => 0x20c
  | 32 => 0x20e
  | 33 => 0xb0c
  | 34 => 0xb0e
  | 35 => 0x140c
  | 36 => 0x140e
  | 37 => 0x154c
  | 38 => 0x154e
  | 39 => 0x28c
  | 40 => 0x28e
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x148c
  | 44 => 0x148e
  | 45 => 0x184c
  | 46 => 0x184e
  | 47 => 0x40c
  | 48 => 0x40e
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0x160c
  | 52 => 0x160e
  | 53 => 0x188c
  | 54 => 0x188e
  | 55 => 0xb0954
  | 56 => 0xb0956
  | 57 => 0x140954
  | 58 => 0x94b14
  | 59 => 0x140956
  | 60 => 0x289
  | 61 => 0x10a
  | 62 => 0x1489
  | 63 => 0x130a
  | 64 => 0x14c9
  | 65 => 0x134a
  | 66 => 0x409
  | 67 => 0x1609
  | 68 => 0xb1394
  | 69 => 0xd0a
  | 70 => 0x188a
  | 71 => 0xb0994
  | 72 => 0xb0996
  | 73 => 0x98b14
  | 74 => 0x154994
  | 75 => 0x154996
  | 76 => 0x10b
  | 77 => 0x130b
  | 78 => 0x1649
  | 79 => 0x134b
  | 80 => 0xb1514
  | 81 => 0xb8b
  | 82 => 0x184b
  | 83 => 0x148114
  | 84 => 0x11494
  | 85 => 0x11496
  | 86 => 0x160114
  | 87 => 0x11614
  | 88 => 0x11616
  | 89 => 0xb8a14
  | 90 => 0xb8a16
  | 91 => 0xa0b94
  | 92 => 0x184a14
  | 93 => 0x184a16
  | 94 => 0xd0a14
  | 95 => 0xd0a16
  | 96 => 0xa0d14
  | 97 => 0x188a14
  | 98 => 0x188a16
  | 99 => 0x29314
  | 100 => 0x130294
  | 101 => 0x130296
  | 102 => 0x149314
  | 103 => 0x131494
  | 104 => 0x131496
  | 105 => 0x41314
  | 106 => 0x130414
  | 107 => 0x130416
  | 108 => 0x161314
  | 109 => 0x131614
  | 110 => 0x131616
  | 111 => 0x9cd
  | 112 => 0xa4d
  | 113 => 0xb9814
  | 114 => 0xb9816
  | 115 => 0xd1814
  | 116 => 0xd1816
  | 117 => 0x1049
  | 118 => 0xb0214
  | 119 => 0xb0216
  | 120 => 0x20b14
  | 121 => 0x20b16
  | 122 => 0xbcb
  | 123 => 0xd4a
  | 124 => 0xd0294
  | 125 => 0xd0296
  | 126 => 0x40b94
  | 127 => 0xb8414
  | 128 => 0x40b96
  | 129 => 0xb8416
  | 130 => 0x160b94
  | 131 => 0xb9614
  | 132 => 0x160b96
  | 133 => 0xb9616
  | 134 => 0x194a
  | 135 => 0x14cd
  | 136 => 0xd1494
  | 137 => 0xd1496
  | 138 => 0x189494
  | 139 => 0x189496
  | 140 => 0x161854
  | 141 => 0x185614
  | 142 => 0x185616
  | 143 => 0x194b
  | 144 => 0x164d
  | 145 => 0x1a49
  | 146 => 0xec9
  | 147 => 0x5554
  | 148 => 0xeca
  | 149 => 0x1a4a
  | 150 => 0x14b
  | 151 => 0x14a
  | 152 => 0x2c9
  | 153 => 0x2cd
  | 154 => 0x12cd
  | 155 => 0xecd
  | 156 => 0x1a4d
  | 157 => 0x9414
  | 158 => 0xecb
  | 159 => 0x1a4b
  | 160 => 0x449
  | 161 => 0x44d
  | 162 => 0x74a
  | 163 => 0x74b
  | 164 => 0xe89
  | 165 => 0x131814
  | 166 => 0x131816
  | 167 => 0x181316
  | 168 => 0x180b96
  | 169 => 0x180d16
  | 170 => 0x181796
  | 171 => 0x18c9
  | 172 => 0x1949
  | 173 => 0x141556
  | 174 => 0x140b56
  | 175 => 0x141856
  | 176 => 0x155416
  | 177 => 0x154cd6
  | 178 => 0x155896
  | 179 => 0x29316
  | 180 => 0x28b16
  | 181 => 0x28d16
  | 182 => 0x29796
  | 183 => 0x41316
  | 184 => 0x40b16
  | 185 => 0x41796
  | 186 => 0xec9d5
  | 187 => 0x9ced5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2133
  | 6 => 4757
  | 5 => 2567
  | 4 => 72
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (87453+((h/711+packedAt gbK7 (78921+(h % 711)*12) 12) % 2560)*13) 13
  | 6 => packedAt gbK6 (248941+((h/1585+packedAt gbK6 (228336+(h % 1585)*13) 13) % 5709)*14) 14
  | 5 => packedAt gbK5 (161713+((h/855+packedAt gbK5 (151453+(h % 855)*12) 12) % 3389)*13) 13
  | 4 => packedAt gbK4 (5208+((h/24+packedAt gbK4 (5040+(h % 24)*7) 7) % 125)*8) 8
  | 3 => packedAt gbK3 (327+((h/1+packedAt gbK3 (324+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff0f0783fe0ffc780f01ffff0cfc83c38f49f
  | 1 => 0xc1ff007fc1ff0ff800fffc07f3340fccc738f3
  | 2 => 0xfe0fff8001fff0ffff001ff80c3871f307cf1c
  | 3 => 0xffffffe0000ffffffe0000fc07e03f80fe0
  | 4 => 0xfffffffffff00000000000fff8003fff000
  | 5 => 0xfff0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x129030181240118484908562c041c814185485
  | 1 => 0x4123002240a90a4802254815211402c8432832
  | 2 => 0xa40544800132a0512a00529024281161058918
  | 3 => 0x1088994cb40000a654ca80204ac06c02a806c0
  | 4 => 0x210eee7729dccc00180300c18fbe8003f6f000
  | 5 => 0x39c00c0630188804608c03060fff7fbc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37161
namespace PEqualNP.Outside.L_meta_37161
open PEqualNP.Outside.L_meta_37161.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 551 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 (concat bs3_4_224 bs3_4_256)))) (concat (concat (concat bs3_4_288 bs3_4_320) (concat bs3_4_352 bs3_4_384)) (concat (concat bs3_4_416 bs3_4_448) (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)))))
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
theorem bs3_5_640 : Interval s3Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 666 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 13 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 13 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 14 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 19 := block_range (n:=19) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 467 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 634 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 72 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_2560 : Interval gbAtlas 5 2560 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2567 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))))))
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
theorem bgb_6_4736 : Interval gbAtlas 6 4736 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4757 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))))) (concat (concat (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))))) (concat (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)))) (concat (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336))))))) (concat (concat (concat (concat (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464)) (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)))) (concat (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))))) (concat (concat (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)))) (concat (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)))))) (concat (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)))) (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128))))) (concat (concat (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 bgb_6_4256)) (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)))) (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))) (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2133 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568))))) (concat (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))) (concat (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 bgb_7_1952)) (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8feeafce8fee8fca8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813032 * 2 ^ 32 + 4276681896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37161.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[1,2]⟩,⟨.or,[3,5]⟩,⟨.or,[3,6]⟩,⟨.and,[8,9]⟩,⟨.and,[0,8]⟩,⟨.or,[6,11]⟩,⟨.and,[4,12]⟩,⟨.or,[0,10]⟩,⟨.and,[7,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276681896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276681896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37161

open PEqualNP.Outside.L_meta_37161 in
theorem PEqualNP.Outside.L_meta_37161 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276681896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276681896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
