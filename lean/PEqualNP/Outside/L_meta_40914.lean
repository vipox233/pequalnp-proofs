import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40914.Model
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


end PEqualNP.Outside.L_meta_40914.Model

namespace PEqualNP.Outside.L_meta_40914
open PEqualNP.Outside.L_meta_40914.Model
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

def SBf (j : Nat) : Nat := [8, 7, 7, 6, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_40914

namespace PEqualNP.Outside.L_meta_40914
open PEqualNP.Outside.L_meta_40914.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x4a402412000061c7c88100011030068023003040a167891c425c7804e154002a74226301c019004d01400012901a6cb0400808a21c6105481ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x281bd42502fea2a07dd4540bba8a817c51503e8a2a05d14540df20a81bc41503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4206f90840de210817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc2fca5985f54b30bf28e617d51cc37c83986f10730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461de328c3b865185f94630bea8c61be418c3788318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa9261ef524c2dea4985f14930f6292616c524c2fea2987dd4530bba8a617c514c3e8a2985d14530df20a61bc414c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830bea9061de320c3b864185f94430bea8861be410c3788218778c430ee188617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c82fca3905f54720df20e41bc41c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ef32883d865105f94620bea8c41be418837883107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a4174514837c82906f10520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4107bd0820f621041ef32083d864105f94420bea8841be410837882107b88420f6108417e50083de40107e88020f690041f920082fea9885f95310beaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c437c83886f10710fd98621f830c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21f7418437c83086f10610fa20c21b441843ee63087d0c610fb90c21f421842fca1087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53443bea68857d4d10bf29a217d53442f8a6887714d10ae29a217f52443dea4885bd4910bf292217d52442f8a4887b14910b629221be414437882887ec4110fb082217f54042fca8085f55010be2a0217f53042fca6085f54c10be298217f52042fca4085f54810be290217e51043ee82086f90410de20821f4410436882087dcc410fa18821f721043e842085f94010fd98021f830043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xf504caf8a0995fd5032bf2a0657d540caf8a8195f94c32ef21865dd430cafca4197b90832f6a1065df320cbdc6419774c832f699065cd320cafca2195f54432bf280657d500cafca7a0df54f41bf296837d52d06fca1a0df54341beaa4837e53906faa720efd0e41df21c83bd43907788720df94a41bea9483bf429077c8520ef50a41de214837e519077e8320fdd0641bf284837d509077ea720ef94e41dea9c83bc539077ea520ef94a41dea9483bc529077e6520ef8ca41de99483bc329067ca320efd4241df28483bd5090778a120dfd4d41be29a837f52506f8a4a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef90c41dea1883bc43106fca420df54841dfa1083be421077a8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020efd4c41df29883bd5310778a620efd4841df29083bd5210778a420efcc841df19083bd32107786420ef944419f28883b6511077ea020ef94041dea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598df54b31df20e63bc41cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c77c8318ef10631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa9263ef524c6dea498df14931f6292636c524c77c8298ef10531fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f78c831ee190637e510c77c8218ef10431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877c8390ef10721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e518877c8310ef10621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21df20a43bc41487ee4290fb88521bfa8243fb50486f6a090df14121fc282437850486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbcc821f6190437e510877c8210ef10421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740df20e81bc41d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40dfa1a81bd43502fea4a07bd4940b7a92817c52503d8a4a05b14940dfa1
  | 2 => 0x80002583184e382491208682a4604000002a0b6cf78003fe0000000054e05d0ca0d3321e80014900042c001b92643dcb8aa2410b50501680ea000000000008a4001870000010b94c000000000ef270874002311a0000ef19c000444001bf5025b9470000005913714400044855000514000002a50000004b8000e85d40000000000000000460024c1800000acc000000000000011416c220ada2f000000001a72366bc0002e00000000207550578c70260dc0014e8000003c4000001aa7cce62b645a0000006a584410000000005983e8001b68f8001d80002280004f0003804a8001ac00000000000188000004d26b89b2b15067f56d07620e0000000031693c0017a0000000023700000000000000af96f0320007a0128fb000000000000002315a2d725665471000000a680000007c00086851096001292b00009205109c1560000001c0f67ec309a2342034b080014c00000000000938a2acf10692c690495823cc2824044a87cbc18917c828968a80604d06b9f202c000519ce000000eb1370000000010812278100a0e00070090000000324078003018001c08468810218000218408e01210200e00e00400008410009e00608211018230000020600010000400041870000211220a00a78238008008090200208000018000408820008018021a10011628000820c18600808409a00059e10000600008400008018428828410810088008400002308268000808410000008200000208880001230a40058008260008200eb8238200268400c20011c00012200a41808430410218010418c0101821001802061062000004084017e52d0fdca5a1db94b43bea9687ed52d0edaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0bbca7a15794f42bea9e85dd53d0abaa7a16f90f42de21e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665ee42ccbda85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32ef21c65dd438cafca51977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265ef324cbbc64995fd4532be28a657
  | 3 => 0x1a81ea0000000018888c70abb4989f4639f02ee9f0851b13483e8a38732d8000f8800000a8d5607f0000001b0000004b0f48003887e5089be36c575139e23528000999e4943682180027a21ca78003ba1a5551ac0006e80000039400000000000000051f848600000000090a4400000000944fa80000000000000000104001653044991113f314a1026a5c16a97490a124e60000f11a3783b0f3a57132000538de000000001ec58800000000542000a08000000012a0e3276000260000000000023b0581e4002c9000000000ad000001390b3000001230b9000001048003860000028b10263c000003e8000b3a24218814000004708095fa440006b44f1280000004da1b3f86c8d500007e05400000000880971b353e001300001ca3fce38000000000016a000000cea644d63f49129b442000d1acc000000730004a0770ff0373c84a85916b00a000002ca19e0000016930c57c77000000000002d20003a4000000348ac000b7000224470b00009f8000000222e8e5a5500026000000000558cc028202000001251b8001672744e26110c0a100084ca429710c0006417c0000015c19003676524aa44069789f0005aa0000015451e000da9ab00034cdc00007a474de85f1040516c10532e97c002870000016c80056e3d90609d0001640025b2da7856b29534a0000011c0321f14f1620c84c0000000000013d80000000000172000000600002ae00163000000580671d10d68a02313c14a0000006d00000000000000b14000ed0006ecb7a150060cce415100e268ae1d00000011a8002327dc0006c55ca500008d51a43cad0000009d9460c53d60180900147242400000000a001480058e040000000000007212901000049800454328002750009a023a935a2999430001080000000047823cc69403842f00000013e5ec0025900044000071000518001db4b4000000000000006a2340000013d19a0001f9658a4000000250cb33677d0a00045c150738000b674d6e247000000cb00057808c1e26d000000978001d4000e785a0000001a80047400001000000000000000001740020400082c6081f4fe0000000006800022866000408f6acd0000e0560000000885f94d000001410003aa001162af49a19c5797900046000192524748001034eeb4caaa1e3a8000bb1b00c01c08b26300044c000000000000029c1f2000000bb0002140005e0000000000019a000e29313f447c000270002f4002ad0003a00000048a5380022640c0ec2b185000859530fc000000000550000000002000000075ac3556960000000000015d07800058d4c000152000001e3048374000001000000012720c7a8000c31849a8c99e60548f4b981d07437c689591689b0802a90000008f000000000002422e8000a12100004e81c800000000000000002e0459332fc000b82c
  | 4 => 0x9bc32ac000067ce490e4f2ac86600000000000000000988000004f03e0000044a6a14058003dc698c60002fe794000001281dc001394ac768002b50000000000046600000072000000c8a650000000000039a00016a8843436029add18c6211f842000248ac06f0a400144953572001380b101c000ca0ae3400bd4c94336800091a6700083c00000000000be8d90ae0002e0fe3ae8d8002bd0006000000026ab40780005201113080c22a3c800000000000a50001200851902b0621600000038c0014b2a00300000014b22e1000021c1e86dcfb
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4534831f5414d20c7150534823e64d45208f593514833754d4520cd153514835753d4520d514f514833664d4520cd59351483375414520cd15051483575314520d514c51483376414520cd190514823e65905208f196414831f5390520c714e41483375190520cd146414823e65105208f194414831f5310520c714c41483375110520cd144414837051c8120cb152204834c5388120d9146204823d65950208f986540832c62550208f185540823e64150208f993530823d64d4c208f990530823d6414c209d98453082756114c20cb55342082ce63d08209b59442082ae64cc820cb553320826d650c820cb550320834d530c8208fd91510823c645442097d8d510825c63544208fd96410823d65904208fd94410823d65104209bd9520082ac6448020b318d20082e461480209ed9520082f061480209798f54c425d63d53109b98b54c426d62d53108f99353c423d64d4f109b98b53c426d62d4f108f99253c423d6494f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b10cdd85548423e64d4e108f593538426e62d4e109b58b538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6414a108f59052843355410610ad59441843356510610ad99331842b664c86108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544427761551108f994544423e61151108f184544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534427b6054d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524427b60549109b994524432f5414910cb150524434f5314910d314c524423e6590510c7d4e414431c5390510cbd4a414432c52905108f994414431f5310510c714c414432f5210510cb148414435853c4110da14b10443345484110d514e104436452841109798c540425d63150109b988540426d62150108fd91530423c6454c109bd89530426c6254c108f990530423d6414c109b988530426d6214c108fd91520423c645481097d8d520425c63548108f990520423d64148109798c520425d6314810ad98641042756510410bc58041043366510410cd59441043b26010410ec58041042b664cc4109d59431042b664c84109d594210423e64940108f59250043344194010ec1073004279650c010ec10430043d0310c010ec10720042796508010ec10420043e021080109e59610043b041840109dd9510042b46444010b518d10042e462440109ed9510042d86344010ba18910043b24144010
  | 1 => 0x863e64948218f592520866d650c821d354c32086e5610c8219bd9521086cc6348421e910521086e860484219dd9521086f060484218fd91500863c645402197d8d500865c6354021ab58b43d029d63d0b40cd94441d033551107409bd89539026c6254e4097d8d529025c6354a40cd946419023e65d0d40c714f43502ad62d0d40c714d435034f53d4940d314f525034f5314940d314c525032f4314940cb50c525023e65d0940a758f425031c53d0940cb14b425031c5350940cb149425035753d4540d514f515036752d4540d914b51503575314540d514c51503675214540d914851503376414540cdd0c51503354314540cdd0851503354214540c7d4e415031c5390540cbd4a415032c5290540cd146415031f5310540c714c415032f5210540cb14841503375110540c714e405032c5290140cd146405023d6590c408f596421033651104408fd95401029c6350040ab18940102b461500409ed95401026e62d53309b58b54cc27661d53309d58754cc23e6494b308f59252cc23f64547308f19151cc3365110730cd54441cc26e62152309b588548c2ce62d0e308fd91528c23c6454a30a7992328c23f64546308f191518c23e61d51308f992544c26e62951309b58a544c27661951309d586544c25f63551309bd89544c26c62551309dd85544c27461551308f994544c23e6115130cbd53524c32c54d4930cbd50524c32c54149308f993514c23d64d4530cdd53514c33454d4530d9d4b514c36452d4530cd993514c33564d4530cdd50514c3345414530d9d48514c3645214530cdd90514c33464145308f996414c23c6590530cbd4a414c32c5290530cdd46414c33451905308f994414c23c6510530cbd48414c32c5210530cdd44414c3345110530dc147304c31c548c130d314a304c354518c1308f596540c23e6195030c718d540c23c61550308f990540c31d54d0c30b398b430c25d6510c30a7992320c31d548c830c7550320c34d520c8308fd91510c23c64544309bd89510c26c62544308fd96410c23d65904308fd94410c23d651043097d95300c29c644c030b3189300c2d4614c0309ed95300c2f0614c0309798f54c825d63d53209d98754c827561d53208f99353c823d64d4f209d98753c827561d4f208f99253c823d6494f208fd9151c823c6454720cd94441c833551107209798c548825d63152208fd91538823c6454e208f990538823d6414e20b398f42882ae64cca20d3d4c328823f64546208f191518823e61d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551208f994544823e6115120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8553482746154d209799
  | 2 => 0x654c8329bd95320cacf654c832d3d95320cacf644c832b3591320cacc614c832b3181320ca3f64544328f191510ca7b60544329e181510ca3f64540328f191500ca7761540329d185500ca6f6254e419b18953906ae62d0e41ab58b439071e5350e4197d8d529065c6354a41a798f429069d63d0a41cb94942906b661d4e41c7d4e53906af6254e41ab18953906ae6214e41ab58853906b66114e41ad987529072f5294a41a7d8d529069c6354a41a798c529069d6314a41ad984529063e65cca418f597329063e658ca418f596329078d320ca41a798f509069d63d4241ab98b50906ad62d4241ab98b43106ad62d0c41c754c431069e63d0841a758f421072d52108418fd954110677655044197d8d501065c63540419bd89501066c6254041ab98b53106ad62d4c41ad987531071d5314c41ad984531069e63d4841a758f52106b661d4841cb54852106b661148418f997321063d65cc8418f996321063d658c841add8532106b4614c841e34c832106b6610c841ad58432107366194441ad982511069f6354041a718d50106af6254041ab189501069e6314041a758c50106ae6214041ab588501066e62152319b588548c63f6454a318f191528c63e64942318f592508c63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c72f54d4931cb153524c72f5414931cb150524c63e6590531cbd4a414c72c52905318f994414c72f5210531cb148414c74c528c531ced53504c73854d4131dad4b504c76852d4131ce907504c73841d4131ced50504c7385414131dad48504c7685214131ce904504c7384114131dccc4504c75a31141319b98b540c66d62d50318f992530c63d6494c318f992520c63d6494831d3548320c6d5610c83197d95310c6cc624c431e5105310c6d8604c4319dd95310c6f0604c4318fd91500c63c64540319bd89500c66c62540318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798c548865d63152218fd91538863c6454e218f990538863d6414e21d3d4c328863e64942218f592508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219bd89534867b6054d219e181534865e6514d21c7d50534871c5414d218f996414871f5390521c714e414863e6510521c7d4c414871c5310521d314e214873b54d4121ce153504875b53d4121d614f504873a41d4121ce107504873b5414121ce150504875b5314121d614c504873a4114121ce10450487732114121da884504865e63d50219758f540863e64d4c218f593530863e6494c218f592530
  | 3 => 0x230000004bcaac2c8e42925d4ca2c626c850001fb3a0000219701965687d19a29c9ac3f0af3c8410bc2841cc0010e8a200012d4e9e630e45030a2717c0000012450c13c7f0004aa0000002947aa2d239472744b4002ae0843b43424f4166e4b924b50089887aa91548a53da68000b0d1825a366681211545025c4fd24810c3a8d780020c81d33ab35443580e8a614aae5628a1200234001f134e6c4001284141bcbd27c05495c450df102349261cd0002d92c18e3fc1ec068003c21b46a0003c4000c40492d45f8fe00046c9b4588762149443485a000584cf0974cc5a516137100304599d939806c00000270424001224e20000019d2f20015908e0004053c064000344780002e62ac001e501ca8400220000000002952aa0006a8003ce000491e04e6378001db0006540029137c7a8002b10ee19c648004781400015312c4d0001e3000a90208b03a2000000000000009d800000468ab1122fa46036000000000002794720f503000000860000a80003e48c9a4580000b39982bc00000000000001328000e6368001020383648ea88000545550003825ac0027d4e4290001d3018001179f32c0631472c10b60c017a212661281712c4a640c5dabd0c4000330000008ec0000000034c001742863fce01591b04c0f79c250a4310892011e598418c317e534afa3109821130276164240c6803000000d296833e96c610001126592a00036a000fa8db000768d60124ee6f51180041a0001e000011400030410031c501f20f0076c210014000624100008620304500008100400816f3040800810280b82000060001842e21030054411446403c02010111400074c03400ca2c6201001780010f0638b10e00014810000c1c319b00009531804000e1c51001660d2ac108005328700080408910220d0011401800010440010011050020040c004200099b4591c000108304c10518004014000004200a1dc54e2091400870050d00050820052024066c0101ab58b4390ece62d0e43b398b4350ead62d0c438fd954310e5f6550c439bd895010e6c62540439dd855010e746154043c754e43d0b1d5310f42ab58b4390a9d63d0a42b398f4290a3e6510d42b398f4250aad62d0c428fd954310a9d63d08428fd954210a6f655084297d8d5010a5c63540429dd855010a746154042cb58a54cca3e61953328f18554ccb2e5490b328fd9151cca3c6454732c758e548ca3e61952328f185548cb1e5490e32a7593328cb2d54cca328fd91518ca3c64546329758e544ca6d62951329dd85544ca7461551329ed81544ca7860551328f993514ca3d64d45328f990504ca3d64141329d987540ca7561d50328f992530ca3d6494c3297596430cacd6290c328f992520ca3d64948329b596420cacd6390832e350e420cb8e4350832a7593320caad648c832b358e320ca5f
  | 4 => 0x4584a9100509c09a8004a0a6d31a825263cd0807a39011d419254102e51d00022e0890a9830a40000018449aaf0000001400087b8000009585b8cf3260006397c0007ac100000007d80f8ce5303c9028364de454000002d81940004e0000013f9d70000011900035c000a400006288915011000000002a618a000001ed4c80001a80004a0e1450072647c8040e90000015a1f4000af80312a5740000c940000514ec0004927e1091853a82f49891b0e4000e900000021c5e0000009e87e1e90000015185e000000002c700a4fd061b43fe8ccdc12f3e0000000000802e8000e30d40040009f55a5fcd0923242a24701c338a508001801900ace78540e091488a6c43e35d0d1dc1ce4985613c32263cf405d402964429893bc2b9352521526882899b1f655cad8b8412134d695242ca34cc83444a988828e13386ec3a0260663f4d30e85883b07b04456e90d0caa006e7b80005c07e574b2058558a64a80cd2dc41c3f9ba3783754800057e000c322b13600000294000388000003023180b8c02ca000000000e2028021bf2560595b079400a7c650dc2820680002355e0f8bd92736e395271d51340793a89d41c5195a86052c1f41212932e8b47a90d076970c5963130000c51df23868d5d88846a1583e1fd2888e11f96d3200013f00b0005bd5809c43c6484f22823e1d4e3800000a5cd90000ae000d4800000a69539aa0000250e1d65844f4002132c400101a6108c4f90108b00000056800000000d5a87020000410000000000014f0000e8002170d604c000000000000006323c061230001e28d1528c446e084c121b00042ce514a3d805120a2439c0004a1b61de000a5a441260c9478000583303700014e9d0899a8480000bb0005700e40000016a00075a8c0aa5dce5a2e1f017c0a9c9298000519f704e03c000004be001078004ba000000000f00b4872a8000a49250000003414e1390a6000d80000000009729e1229a4000990003d0228003887e4ee80047c0005a1582b89b8000000903b9021c6210
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x61033600e2aa000b087800244b2e00000000b8011a000180894000726580c280200b4e803040004021a38ac828265235d3654c832988e2b2264194c870591320ca46ba0c099065611c5320c841960e0b086420cd070584320c7423108298863a4104604c4319c0e0b086410e84631052108750208c0908438314d62d0d40c1ac629684a052572d0c515028ab9e8428a818355262d0c3083eecaa4641860d5498f4208217bb2a999041341cd60104109c0e4b0082085907358041042d0392c0208212c5d8410c010962ec20840084b276905100434831c8288021a818a4144010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x800884815d3654c832884815d0604c832
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
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
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*2) 2
  | 6 => packedAt s0K6 (742+((h/14+packedAt s0K6 (672+(h % 14)*5) 5) % 55)*7) 7
  | 5 => packedAt s0K5 (21315+((h/245+packedAt s0K5 (19845+(h % 245)*6) 6) % 1195)*11) 11
  | 4 => packedAt s0K4 (28478+((h/237+packedAt s0K4 (27056+(h % 237)*6) 6) % 926)*11) 11
  | 3 => packedAt s0K3 (1510+((h/10+packedAt s0K3 (1470+(h % 10)*4) 4) % 49)*6) 6
  | 2 => packedAt s0K2 (121+((h/1+packedAt s0K2 (120+(h % 1)*1) 1) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3ffffffffffffffff03ffffffffffff0fffff
  | 2 => 0xfc07fffffff80ffffffc0ffffff80ffff1fe3f
  | 3 => 0xfff807f80ffff01ffffff03f01fff03ffe63c7
  | 4 => 0xfffff8000fffffe03fffffc001ffffc0ff83f8
  | 5 => 0xfffffffff00000003ffffffffe000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc0090908a28922448a00b2cb525b145106acdb
  | 2 => 0x74252514510e489152c0555a4a88aaa71562d
  | 3 => 0x4957446269a241d2275550263135a23cba6346
  | 4 => 0x926467458e448903b99a6980c1c6cf08dd83b0
  | 5 => 0xe38787860f870e1c3ee38e38f8070c30eff800
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000fcc0c0c0ccc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1e8071d140002b2a003804aa031600000000668a210a34000203000030a92230404f11002c413127cc800871112005d32c36a53801810c9000281900041042ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41f741fe41be41fd41fc41bc41f441b441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3800000000064000000030007631000001d1000000000000000000000000002705800001509800000000070001f800000000000020000044000027800f836000000080000000000000280000001c8007300000005e3d800a624001280000000007814000e8000000000d200000007a550000000000015c064900000000000000000000000ea0019800c600000000000000000000000000035000009a2e001b800500000000002f8001245000000000000a0000009160f20000000002c148000000330000000000000000000dc000000000000000000000021000c00000148ce001780000000007868001580076001c968003000000000000000000000000004c00000426b0000000002d8001618219a0380000038006f000000000000004e000d8682a00000c800000000000000004c9600389500a003a11000000000000000000000230000000000b834000020000e00016800ca00240000000000000000001a800460000000000800000002e000000012800000600000005904000005d0000000002b1f8000000000000000190000000000620f3f800ee7d0018400000000000000007c447800000d80436904000000000000000000003e23808005100000f400000000020024805000604404c000040000240005b94a43b6a9487765190eeaa321ddd4543ba28a875e5390abaa7215d94642baa8c85775150ae8a2a14f953329eaa6657651ccaeaa3994f952329eaa46576518caeaa319734c832bb28c833e519066ca320ed504419f28883b651106eca820ed95041dba1883b6431076a8620ed10c41dba1083b6421076a8420ed10841dba9883b6531076aa620ed14c41dba9083b6521076aa420ed14841db99083b6321076a6420ed0c841dba8083b6501076aa020ed140419f2a6633d54cc6dca598db54b31da20e63b4418c67ea898cf15131da20a63b4410c67ca990cf55321af29e435d53c87688390ed106219faa2433c54487688290ed10421da20e817651902eaa3206d10640afa9a815c53502dea4a05b14940bba8a8174515036882a06d10440da20e61b4418c27ea8984f15130b7a92616c524c2eea2985d14530da20a613e540c27aa8185b94830b6a906176510c2eaa2186d10430da20e41b4418827ea8904f15120afa9a415c53482eea2905d14520da20a413e540827aa8105794c20aea98417651082eaa2106d10420da20e213e548427aa9086d106109faa2213c54442bea6885714d10b7a92216c524436882886d10410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x130008898000199187080018001e178510128e218b8d801b00038b028a139216090d010099111a049d800f830000108c80150000170598819a80200f1f87869b800c0e9c800a940621001580001c0400149d20800216801e9f02b340024382601c08498c2761408d18554cca3464547328d185548ca346454632a998a43106a56290c41a598e42106956390841a998b53106a562d4c41a998a53106a56294c41c554c531069663d4841a558f52106966394841a558e521072552148418d997321063565cc8418d9963210635658c841e14c832106976354041a518d50106a76254041a918950106966314041a558c50106a66214041a958850107265210731c954841cc7165310721c554c41c87175310540c514c41503275210540c9148415023661d51308d993514c23665105308d194414c3275210530c9148414c23461550308d191510c23765104308d594410c3265210430c9548410c23661d51208d993514823665105208d19441483175310520c514c414823461550208d191510823765104208d59441083165310420c554c41082346115110c5d4c41443145310510c9d4841443245210510
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
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
  | 5 => packedAt s1K5 (810+((h/15+packedAt s1K5 (720+(h % 15)*6) 6) % 59)*7) 7
  | 4 => packedAt s1K4 (3612+((h/43+packedAt s1K4 (3483+(h % 43)*3) 3) % 410)*9) 9
  | 3 => packedAt s1K3 (2694+((h/22+packedAt s1K3 (2584+(h % 22)*5) 5) % 89)*8) 8
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 2 => 0x3f81ffe03f03f03ff0f83e0ff83e07c0f49ecc
  | 3 => 0x3ffe0fffc003ffffff003ff07fc007fff8e30f
  | 4 => 0xc0000ffffffc003fffffc0007ffff800ff03f0
  | 5 => 0xfffff0000000003fffffffff80000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x808400248800800002284a1088429052012c55
  | 2 => 0x952c66439255255cb05a168d3a3436867496cc
  | 3 => 0x2618aa89069a4d2d550425a45690472cb8c30a
  | 4 => 0x34514d1224d069b66996810867396208de03a0
  | 5 => 0x38618e1c38e38e3b8ee739ce04218430eff800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0aaaaaa00faaaaaa0aaaaaa00faaaaaa0aaaaaa00faaaaaa0aaaaaa00faaaaaa0aaaaaa00faaaaaa0aaaaaa00faaaaaa0aaaaaa00faaaaaa0aaaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4e70000108c00000a0b0000906ad5800003243c315126929d007c00014000000000000082c8af04315931c0550000011000ea40002e0001800010052064a1e368572600154a0020b622ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x300000000000000000000000000f64d3800000001300000000000000000000066000000000000000000000013c0000000bc00001f0000000000001a001a000000000000000000000007c000000000000147e000000000000000000003a000000000078000000000000000000000000000060000000aa00000001600001280000000000000000000000000000000000000000000000000000e03600000dc000000000602400000000000000e40000000001d2b000004800000000100000c80000000000000000000000000000000000000000000000000000002200000b00000000000007000007900000000036000000000000000000000004700124006800000ea000000038000b000780000000000000028000000000d200000000000000000000001140000000000000000010a8014800000000000004b270ac460000000000000000000000000000000000720000000000000000000000100000000000000000000006d0000000002d001045c001e8580000000001400000001100000000000000760013800fa00000000000000000000000001e0000000001f0000000000000000000000000000000000000000000000000000000000000002200000000000000353c21032002d80000000000000000000000002b80000000018c000000000620000000006b00000000006188000000000000000009060000068000016800e600000000000000000000000000000190d800130018400000000000000000082002f000000000000104140014010850010067aa5a1cf947439f286873d5490eeea2a1dd14543cfa9a873f5250f6ea2a1cf14543da28a87345150e78a0a1cf950439ea9e853e51d0a7ca1a14f55242bba8a85745150a7ea6a16bd4942dba8a853c5150b68a2a14d145429e282853e5410a7ca9994f55332bb28e657551cca7ca9194f55232bb28c6575518ca7ca8994f551329f2a0653d540cb9a64194f54e419ea94833e519067ca120cf54c419ea90833e511076ca220cf940419f2a6633d54cc6dca598db54b31da20e633f548c678a918cfd51319e2a2633e540c67aa818ed104319f2a6433d54c86bca790d754f21da20e433f5488678a910cfd51219e2a2433e540867aa810ed10421bb28c8175519027aa7204f54a409f28c81b6519026ca3206d546409f284813d531027aa4204f944409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f553209faa4413c548827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310da20e213e548427aa9084fd51109e2a2215f53442b8a6885bd4910b629221b4414427ea8084f15010
  | 1 => 0x5c0000329d8007e0300000000000000002f800000000000004c00000fe00001980000000000060000000051000000000000002400000004a711e810001000000000000000120003800a6000000000000000000000000000000419c0000000000000000000000000000043001504000000007400000000000000000000000000081140000000351b8000000000000000000de2e28000000000000ba000010800000a800000000000000000000b2210000000523b8a80000001180
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc0201202672433211668a02a7a0390500000b80000228000000b18886000000fe3430628d18552d0e3661943438d18553d0a3661943428d185544ca3860551328d185540cb2652107318b588548c6356510431a558c410c71653107218758c54886356510421a958841086346154c408d185521023461553308d987548c23461553208d98754883145310510c9148414423661d50108758c540422d6215010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s2K5 (816+((h/16+packedAt s2K5 (768+(h % 16)*3) 3) % 79)*7) 7
  | 4 => packedAt s2K4 (3706+((h/44+packedAt s2K4 (3618+(h % 44)*2) 2) % 665)*9) 9
  | 3 => packedAt s2K3 (1020+((h/8+packedAt s2K3 (988+(h % 8)*4) 4) % 43)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 1 => 0xe07fffc07e0fc1ff0f83e0fffe1e0781d27ecc
  | 3 => 0xff83ffff800ffffff003ff07ffe007ffe38f0f
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x21000889100200002284a108802290a404b055
  | 1 => 0x4b199187249492cb05a168d3b214350cd256cc
  | 3 => 0x862aa2120d29315550425a4555404659630b0a
  | 4 => 0x145344244981a5a69968108669996011b80da0
  | 5 => 0x1863873871ce39f8ee739ce071118461ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x20bf43bd43
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*2) 2
  | 4 => packedAt s3K4 (33+((h/1+packedAt s3K4 (32+(h % 1)*1) 1) % 3)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 1 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 2 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 4 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa6082046244842014a12c42946214a98186e15
  | 1 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 2 => 0x14316914483a6aaac109a6b12d3588528da370
  | 4 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000eaeae8e8eaea0000, s3N, s3R, (fun _ _ => 0), s3I⟩
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4bf43bd43
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
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*2) 2
  | 4 => packedAt s4K4 (33+((h/1+packedAt s4K4 (32+(h % 1)*1) 1) % 4)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 1 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 2 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 3 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa6082046244842014a12c42946214a98186e15
  | 1 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 2 => 0x14316914483a6aaac109a6b12d3588528da370
  | 3 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeae8eae8ea00ea00eae8eae8ea00ea00eae8eae8ea00ea00eae8eae8ea00ea00eae8eae8ea00ea00eae8eae8ea00ea00eae8eae8ea00ea00eae8eae8ea00ea00, s4N, s4R, (fun _ _ => 0), s4I⟩
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x289812002ee21ec21ef20ed20f710f510
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x12d2a010f848110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*2) 2
  | 4 => packedAt s5K4 (98+((h/2+packedAt s5K4 (96+(h % 2)*1) 1) % 8)*4) 4
  | 3 => packedAt s5K3 (55+((h/1+packedAt s5K3 (54+(h % 1)*1) 1) % 3)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81fffff81ffffc0ff0ff83ffffc1fffd18fe3f
  | 1 => 0xfe07e0ffe07e0ff0ff0ffc1e07fe0f02ef33cc
  | 2 => 0xfff800ffff800fff000fffe007fff0030fc3f0
  | 3 => 0xfffffffffffff0000007fffffff003ff
  | 4 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8c104408c1044401101190aa30c85518085615
  | 1 => 0x14b18511472854b07106948c534a46286b32cc
  | 2 => 0x2862d6a28a1d6d57088b5ac8a5ad64530dc370
  | 3 => 0x714518c414510a6aaaa04201063188e3b001aa
  | 4 => 0x4186108718618b8ccccc6311c0210083d6a800
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00eeeaea00, s5N, s5R, (fun _ _ => 0), s5I⟩
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1ba200b0baa2649980000002746b990000a0002707c0ad00c500b340020f3a0000d002403a1cbc3297664018106c534068489e389582672d42942031b2b00543800090b0000b34000082051541100206c82b007fd5001fe54007f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd4807fe52007f54807fc52007fd0807fe42007f50807fc42007fcc807fe32007f4c807fc32007fd4405fe51007f54405fc51007fd0405fe41007f50405fc41007fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc2100ffd4003fe5000ff54003fc5000ffd0003fe4000ff50003fc4000ffcc003fe3000ff4c003fc3000ffc8003fe2000ff48003fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x86620aff94331057faa19882bfc50cc415ffa06620aff90331057fa819882bfc40cc40bff9866205ff8c33102ffa6198817fc30cc415ff906620aff88331057fa419882bfc20cc405ff8866202ff84331017fa219880bfc10cc401ffb2a6200bfd9531007fcca9881efe654c401feb2a6200bf59531007f8ca9881efc654c401ffb226200bfd9131007fcc89881afe644c401feb226200bf59131007f8c89881afc644c401ffaa26200ff95131007faa898803fc544c4057fb1a6200ffd4d3102ffca698803fd534c40bfe29a6200ffd0d3102ffc8698803fd434c40bfe21a6200ffd8931005fec498827fe624c4077f3126200ff5893104ff8c49880efc624c401ffa926209ff94931007faa498827fc524c401ffa126209ff90931007fa8498827fc424c40bff9926209ff8c931007fa6498817fc324c4057fb0a6202ffd4531017fca29880bfd514c405fe28a6202ffd0531017fc829880bfd414c405fe20a6202ffcc53102fee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff90a6202ff88531017f84298823ff604c4117fb026208ff9813100dfcc098823fd604c4117eb026208ff1813100df8c098823ff504c411ff2826208ff54131047f8a098823ff404c411ff2026208ff50131047f88098817ff304c411ff1826208ff4c13102ff86098823ff204c411ff1026208ff48131047f8409880bff104c405fb8826202ff84131017fa2098823f5104c405fe0826200ffd9521005feca908037f65484013fb2a4200ff9952103dfcca90803fd65484017eb2a4200ff1952103df8ca908037c65484013e32a4200ffd9121005fec890803fe644840d7f3224200ff59121005fac890803fc644840d7e3224200ffd5121007fca890803fd5448401fe2a24200ffd8d21005fec690803fe634840b7f31a4200ff58d21005fac690803fc634840b7e31a4200ffd4d21007fca690803fd5348401fe29a4200ffd0d21007fc8690803fd4348401fe21a4202bfd892101ffea49080ffe5248407fea924203ff1492101ffe849080ffe4248407fea124203ff1092101ffe649080ffe3248407fe9924203ff0c921015fec29080bff5148405ff28a4202ff54521017f8a29080bff4148405ff20a4202ff50521017f8829080bff3148405ff18a4202ff4c521017f8629080bff2148407fb90a4202ff88521017dc429080bfc2148405f610a4202fd08521027fec090812ff6048409ff3024201bf98121027fac090812fd6048409fe3024201bf18121027fea090813fe5048409fea824204ff14121027fe8090813fe4048409fea024204ff10121027fe6090813fe3048409fe9824204ff0c12101ffe409080fef2048407ff1024203ff48121027da409080ffc2048405ff8824202fdc4121017fc209080bfd1048409fa8824202ff04121
  | 1 => 0x3ff52d041fff2968200ff54b4107ff8a5a081bff42d040dff2168206ff50b41037f885a0803ff32d041fff1968200ff4cb4107ff865a080afd61d0405ffa8e8202ff94741017faa3a080bfc51d0405ff20e8202ef90741017ec83a080bfc41d0405de20e8202ff8c741017f863a080bff21d0405ff10e8202ff08741037fec1a081aff60d040dff3068201bf98341037fac1a083afd60d040dfe3068201bf18341077fea1a083bfe50d041dfea86820eff14341037fe81a081bfe40d040dfea068206ff10341077fe61a083bfe30d041dfe986820eff0c341077fe41a083bfe20d041dfe906820eff08341017fe21a080bfe10d0405fe8868202ff04341007fecaa0802ff6550401ff32a8207bf99541007facaa0802fd6550401fe32a8207bf19541015fec8a0803ff545040dff2a28200ff55141037f8a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc635040b7e31a8200ffd4d41007fca6a0803fd5350401fe29a8206ffd0d41007fc86a0803fd435040dfe21a8200ffd8941005fec4a0837fe62504077f3128200ff5894106ff8c4a080efc6250401ffa92820dff94941007faa4a0837fc525040dffa12820dff90941007fa84a081bfc4250401ff992820dff8c941007fa64a0837fc32504057fb0a8202ffd4541017fca2a080bfd5150405fe28a8202ffd0541037ee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff18a8202ff0c541017fe42a080bfe2150405fe10a820cffd8141065fec0a0833fe60504037f302820cff58141065fac0a0833fc60504037e302820cffd4141067fca0a0833fd5050419fe2828206ffd0141067fc80a0833fd405040dfe202820cffcc141067fc60a0833fd3050419fe182820cffc8141067fc40a0833fd2050419fe1028202ffc4141017ee20a080bfe1050405fe882820cfd44141017f820a0817ff65cc40b7fb2e6205ff9973103dfccb98817fd65cc4017eb2e6205ff1973102df8cb98817ff64cc40b7fb266205ff99331035fcc998817fd64cc4017eb266205ff1933102df8c998803ff54cc401ff2a66200ff55331007f8a99880afe63cc40bffa9e6205ff94f3102ffaa798817fc53cc40bffa1e6205ff90f3102ffa8798817fc43cc40bffb166205ff98b3101dfcc598817fd62cc4017eb166205ff18b3101df8c598803ff52cc417ff2966200ff54b3105ff8a598803ff42cc417ff2166200ff50b3105ff88598817ff32cc40bff1966205ff4cb3102ff8659880afd61cc405ffa8e6202ff94731017faa39880bfc51cc405ffa0e6202ff90731017fa839880bfc41cc405ff18e6202f78c731017ec639880bfc31cc405ee18e6202ffc8731017fc439880bfc21cc40bffb066205bfd833102ffcc198806fe60cc40bfeb06620abf5833102ff8c198806fc60cc415ffa
  | 2 => 0x320a7f8209900afe65d440fffb26a207ff99351035fcc9a881ffd64d44017eb26a207ff1935103ffea9a881f7f54d440fff2a6a207ff55351006faa9a881ffc54d440fffb1ea207ff98f5102dfcc7a881ffd63d44017eb1ea207ff18f5103ffea7a881f7f53d440fff29ea207ff54f51006faa7a881ffc53d4401ffa1ea200ff90f51007fa87a8803fc43d440fffb16a207ff98b5101dfcc5a881ffd62d44017eb16a207ff18b5101df8c5a881fff52d440fff296a207ff54b5103ff8a5a8803ff42d4427ff216a200ff50b5109ff885a8803ff32d4427ff196a200ff4cb5109ff865a880afd61d4405ff28ea202df94751017eca3a880bfc51d4405be28ea202ff90751017f883a880bfe31d4405fe18ea202ffc8751017fc43a880bfc21d440fffb06a207bfd835103ffcc1a8806fe60d440ffeb06a212bf5835103ff8c1a8806fc60d440fffa86a207ff9435103ffaa1a881ffc50d4425ffa06a212ff90351097fa81a884bfc40d4425ff986a212ff8c351097fa61a884bfc30d4425ff906a212ff88351097fa41a884bfc20d4405ff886a202fdc4351017fc21a880bfd10d4425fa886a202ff04351015fecaa8803ff64544017fb22a200ff99151007fac8a8803fc645440d7e322a207ffd5151006fea8a8803fe5454401feaa2a200df5515103ff8a8a8803ff63544017fb1aa200ff98d51007fac6a8803fc635440b7e31aa207ffd4d51006fea6a8803fe5354401fea9aa200df54d5103ff8a6a8803ff4354401ff21aa200ff50d51007f886a8803ff62544017fb12a200fbd8951005dec4a8847fe62544077f312a200ff5895108ff8c4a880efc6254401f6312a203bb1895103ffea4a8847fe5254401fea92a207ff14951007fe84a8847fe4254401fea12a211ff10951007fe64a8847fe3254401fe992a211ff0c951015fec2a880bff515440ffba8aa202ff94551016fca2a880bfc5154405be28aa202fd14551017fc82a880bfc4154405ff18aa202ff0c551017fe42a880bfe2154405fe10aa210ffd8151085fec0a8843fe60544037f302a210ff58151085fac0a8843fc60544037e302a207ffd4151087fca0a8843fd505440ffe282a210ffd0151087fc80a8843fd4054421fe202a210ffcc151087fc60a8843fd3054421fe182a210ffc8151087fc40a8843fd2054421fe102a202ffc4151017fc20a880bfd1054405fe082a206ffd9741035fecba081bfe65d040f7f32e8206ff59741005facba081bfc65d040d7e32e8202bf99341037fea9a081bfe54d040dfeaa68206ff15341037fec7a081bfe63d040b7f31e8206ff58f41005fac7a081bfc63d0401ffa9e8200ff94f41007faa7a0803fc53d040dffa1e8206ff90f41037fa87a081bfc43d040dffb168206ff98b4101dfcc5a081bfd62d04017eb168206ff18b4101df8c5a080
  | 3 => 0xe30a8402bf185420cffca2a1067fc5150833ff20a8406ff105420cffc62a1067fc3150807ff90a8403ff8854201ff842a1063ff60508317fb028418ff9814200dfcc0a1063fd60508317eb028418ff1814200df8c0a1063ff5050831ff2828418ff541420c7f8a0a101bff4050831ff2028418ff50142037f880a1063ff3050831ff1828418ff4c1420c7f860a100fff2050807f79028403ff8814201ffa40a1063ed2050807fe1028418ffc41420c7fc20a1063fd1050831fe0828405ffd973202dfecb99017fe65cc80f7f32e6405df99732004fccb99017fd65cc8017eb2e6405df59732004facb99017fc65cc80b7e32e6405ffd933202dfec999017fe64cc80d7f3266405ff59332005fac999017fc64cc80b7e3266400ffd5332007fca999003fd54cc801fe2a66403bf98f3202ffea799017fe53cc80bfea9e6405ff14f3202ffe8799017fe43cc80bfea1e6405ff10f3201dfac59900fff52cc807ff2966403ff54b3201ff8a59900fff42cc807ff2166403ff50b3201ff8859900ffe32cc807ef1966403fb8cb3201ff8659900fdc32cc80bffb0e6405ff98732015fcc399017fd61cc8017eb0e6405ff18732015f8c39905ffe51cc82ffe28e6417ff907320bff88399017fe31cc80bfe18e6403ffc873201ffc439900ffc21cc80bffb066405bfd833202ffcc199006fe60cc80bfeb066416bf5833202ff8c199006fc60cc82dffa866416ff943320b7faa19905bfc50cc82dffa066416ff903320b7fa819905bfc40cc80bff9866405ff8c33202ffa6199017fc30cc807ff9066403ff8833201ffa419900ffc20cc82dff8866416ff843320b7fa219905bfc10cc801ffb2a6400bfd9532007fcca9901efe654c801feb2a6400bf59532007f8ca9901efc654c801ffb226400bfd9132007fcc89901afe644c801feb226400bf59132007f8c89901afc644c801ffaa26400ff95132007faa899003fc544c8077fb1a6400ffd4d3202ffca699003fd534c80bfe29a6400ffd0d3202ffc8699003fd434c80bfe21a6403bfd893201ffea49900ffe524c807fea926403ff1493201ffe849900ffe424c807fea126403ff1093201ffe6499017ef324c807ff1926403f78c93201ff8649900fdc324c807f61926400ffd8532005fec299057fe614c8057f30a6400ff585320aff8c29900afc614c82bff28a6415ff145320affc8299057fc414c82bff18a6405ff0c53201ffe429900ffe214c807fe10a6414ffd81320a5fec099053fe604c8037f3026414ff581320a5fac099053fc604c8037e3026414ffd41320a7fca099053fd504c829fe2826414ffd01320a7fc8099053fd404c829fe2026405ffcc1320a7fc6099053fd304c80bfe1826403ffc813201fde409900ffe204c807fe9026414fb4813201ff84099053ff104c829ff0826414ff441
  | 4 => 0xffd20d483df6906a403ff083520f7fe21a907bfe10d483dfe886a41eff0435201dfecaa9003ff64548017fb22a400ff99152007fac8a9003fc645480d7e322a407ffd5152007fca8a9003fd545480ffe2a2a400ffd8d52005fec6a9003fe6354801feb1aa400ff18d5202df8c6a901fff5354801ff29aa400ff54d5203ff8a6a9003ff4354801ff21aa400ff50d52007f886a900eff6254807ffa92a407fbd495201ffca4a900f7e5254807fe292a403df1495201fd8a4a900ffe4254807fe212a403ff8c95201ff864a9003ff61548017fb0aa41dff98552015fcc2a9003fd615483bfe30aa402bf185520effca2a901ffc515483bff20aa41dff105520effc62a9077fc3154807ff90aa403ff8855201ff842a9073ff60548397fb02a41cff9815200dfcc0a9073fd60548397eb02a41cff1815200df8c0a901fff5054839ff282a41cff5415203ff8a0a9073ff4054839ff202a41cff501520e7f880a9073ff3054839ff182a41cff4c1520e7f860a900fff2054807ff102a403ff4815201ff840a9073ff1054839ff082a41cff441520e7f820a901bff65d080d7fb2e8406ff9974203dfccba101b7e65d08013f32e8406ff59742005facba101b7d65d08013eb2e8406ff19742035f8cba100efe64d080dffaa68406ff95342037faa9a101bfc54d080dffb1e8406ff98f4202dfcc7a101bfd63d08017eb1e8406ff18f42007fea7a1003fe53d0801fea9e8400ff14f42037fe87a101bfe43d080dfea1e8406ff10f4201dfac5a100fff52d0807ff2968403ff54b4201ff8a5a100ffe42d0807df2168403fb90b4201ff885a100fbc42d0807ff1968403ff0cb42037fec3a101bfe61d08057f30e8406ff58742005fac3a101bfc61d08057e30e841bff947420dff8a3a101bfe41d080dfe20e841bff8c7420dff863a100fff21d0807ff10e8403ff08742037fec1a101aff60d080dff3068401bf98342037fac1a106afd60d080dfe3068401bf183420d7fea1a106bfe50d0835fea86841aff14342037fe81a101bfe40d080dfea068406ff103420d7fe61a106bfe30d0835fe986841aff0c34201ffe41a100ffe20d0807fe9068403ff083420d7fe21a106bfe10d0835fe886841aff04342007fecaa1002ff6550801ff32a8407bf99542007facaa1002fd6550801fe32a8407bf1954201dfec8a1003ff545080dff2a28400ff55142037f8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc635080b7e31a8400ffd4d42007fca6a1003fd5350801fe29a8406ffd0d42007fc86a1003fd435080dfe21a8403bfd894201ffea4a100ffe5250807fea928403ff1494201ffe84a101bef4250807ff2128403ef9094201ff884a100fbc4250807f62128403ff8c94201ff864a1003ff61508017fb0a8419ff98542015fcc2a1003fd6150833f
  | 5 => 0xd43007fec4a1802ff6250c4bff3128603bf98943007fac4a1897fc6250c077e3128625ff9494312ff8a4a1897fe4250c0dfe2128625ff8c94302ff864a1803ff6150c017fb0a8624ff98543015fcc2a1803fd6150c49fe30a8602bf18543127fca2a1893fc5150c49ff20a8606ff10543127fc62a1817fc3150c4bff90a8624ff88543127f842a188fff6050c477fb028623ff9814300dfcc0a188ffd6050c477eb028623ff1814300df8c0a188fff5050c47ff2828623ff5414311ff8a0a181bff4050c47dfa028623ff9014311ffa80a188fbd4050c0dfe2028605ffcc14311fbe60a188ffe3050c47fe9828623f74c14302ff860a188fff2050c47ff1028623ff4814311ff840a188fff1050c47ff0828623ff4414311ff820a1817ff6510c0b7fb288605ff9944303dfcca21817fd6510c017eb288605ff1944302df8ca2181afe6410c0dffaa08606ff95043037faa82181bfc5410c0b7f3188605ffd4c4302ffca621817fd5310c0bfe2988605ffd0c4302f7e8621817fe4310c0bef2188605ff50c4302f7a862181bdd4310c01cea188605ffd884302ffcc42180efe6210c0bfeb108600bf5884302ff8c42180efc6210c45ff2908622ff14843037fc842181bfc4210c0bff1908605ff0c84302ffec221817fe6110c057f3088605ff58443005fac221817fc6110c057e3088621ff9444310ff8a22181bfe4110c0dfe2088605ff8c44302ff8622188bff2110c43ff1088621ff0844302ffec021816ff6010c0bff3008601bf9804302ffac021882fd6010c0bfe3008601bf18043107fea021883fe5010c41fea808620ff14043037fe802181bfe4010c0dfea008606ff1004302ffe6021817fe3010c0bfe9808605ff0c043107fe4021883fe2010c41fe9008620ff08043107fe2021883fe1010c41fe8808620ff0404301dfccba901fff64d480fff326a406bf9935203ffac9a9002fd64d480ffe326a407ffd535203ffca9a901ffd54d480ffe2a6a407ffd8f5203ffcc7a9016fe63d480ffeb1ea400bf58f5203ff8c7a901fff53d480fff29ea407ff54f5203ff8a7a9003ff43d4801ff21ea400ff50f52007f887a900efd62d4807ff296a403df94b5201fdca5a900f6e52d4807fe296a403df14b5201ffc85a900ffc42d4807ff196a403ff0cb5203ffec3a901ffe61d48057f30ea407ff58752005fac3a901ffc61d48057e30ea407ff9475203ff8a3a907ffe41d483ffe20ea41fff8c7520fff863a900fff21d4807ff10ea41ffb8875201ff843a900fec21d480fffb06a407bfd835203ffcc1a9006fe60d480ffeb06a41ebf5835203ff8c1a9006fc60d480fffa86a407ff9435203ffaa1a901ffc50d483dffa06a41eff903520f7fa81a907bfc40d483dff986a41eff8c3520f7fa61a907bfc30d4807ff906a403fbc835201ffc41a9
  | 6 => 0xbfe308a602bf1845303ffca22981ffc5114c5bff208a62dff1045302ffc6229817fc3114c5dff908a62dff8845316ff84229817ff6014c0b7fb00a605ff9805300dfcc029817fd6014c597eb00a605ff1805300df8c02981fff5014c0fff280a607ff5405303ff8a0298b3ff4014c59ff200a62cff50053167f88029817ff3014c0bff180a605ff4c05302ff860298b3ff2014c59ff100a62cff48053167f840298b3ff1014c59ff080a62cff44053167f8202981bff65d0c0d7fb2e8606ff9974303dfccba181b7e65d0c013f32e8606ff59743005facba181b7d65d0c013eb2e8606ff19743035f8cba181bff54d0c0dff2a68606ff55343037f8a9a1803ff53d0c0bff29e8600ff54f4302ff8a7a181bff62d0c0dff3168603bf98b43037fac5a1802fd62d0c0dfe3168603bf18b4315ffca5a18affc52d0c0dff2168606ff10b4315ffc65a1817fc32d0c0dffb0e8606ff98743015fcc3a181bfd61d0c017eb0e8606ff18743015f8c3a18abfe51d0c55fe28e8606ff90743037f883a18abfe31d0c0bfe18e862bffc8743157fc43a18abfc21d0c0dffb068606bfd8343037fcc1a1806fe60d0c0dfeb068629bf58343037f8c1a1806fc60d0c53ffa868629ff9434314ffaa1a18a7fc50d0c0dffa068606efd0343037fc81a181bfd40d0c53dea068606ff1034302ffe61a18a7fe30d0c53fe9868605ff0c34314ffe41a18a7fe20d0c53fe9068629ff0834314ffe21a18a7fe10d0c53fe8868629ff0434302ffecb21816ff6590c0bff32c8607bf9964302efccb218027e6590c0bfeb2c8600bf5964302efacb218027d6590c0bfe32c8605bf1964311dfac921803ff5490c0dff2a48600ff55243037f8a921816fe6390c0bffa9c8605ff94e4302ffaa721817fc5390c0bffa1c8605efd0e43037be8721817ff6290c0bff3148603bf98a4302ffac521802fd6290c0bfe3148603bf18a43147fca5218a3fc5290c51ff2148606ff10a4302ffc6521817fc3290c0bffb0c8605ff98643015fcc321817fd6190c017eb0c8605ff18643015f8c32189ffe5190c4ffe28c8627ff90643037f88321817fe3190c0bfe18c8628ffc864313ffc432189ffc2190c0bffb048605bfd824302ffcc121806fe6090c0bfeb048626bf5824302ff8c121806fc6090c4dffa848626ff94243137faa12189bfc5090c0dffa048626ff90243137fa812181bfc4090c0bff9848605f7cc24302ffc6121817fd3090c4dee9848605ff0c243137fe412189bfe2090c4dfe9048626ff08243137fe212189bfe1090c4dfe8848626ff04243007fecaa1802ff6550c01ff32a8607bf99543007facaa1802fd6550c01fe32a8607bf19543007fea8a181bfe5450c01feaa28606ff15143007fea6a1817fe5350c01fea9a8605ff14d43037fe86a181bdf4350c0bff21a8605ef9
  | 7 => 0xa981fff60d4c0f7fb06a607ff9835300dfcc1a981ffd60d4c6b7eb06a607ff1835300df8c1a981fff50d4c0fbfa86a607ff9435303ffaa1a98d77d50d4c0ffe286a635ffd03531affc81a98d7fd40d4c6bfe206a605ffcc3531affc61a98d7fd30d4c0bfe186a635ffc83531affc41a98d7fd20d4c6bfe106a635ffc43531affc21a98d7fd10d4c6bfe086a62fbf5965302ffec929817fe6494c0d7f324a605ff59253005fac929817fc6494c0fffaa4a600dfd5253007fca929803fd5494c01beaa4a607ff1525302dfcc729817ff5394c0bbfa9ca607f7d4e53006bea729817ff6294c0bff314a603bf98a5302ffac529802fd6294c0bfe314a603bf18a531a7fca52981ffc5294c69ff214a634ff10a5302ffc6529817fc3294c0bffb0ca605ff98653015fcc329817fd6194c017eb0ca605ff18653015f8c3298cffe5194c0ffe28ca633ff9065319ff88329817fe3194c0bfe18ca634ffc865319ffc43298cffc2194c0bffb04a605bfd825302ffcc129806fe6094c0bfeb04a632bf5825302ff8c129806fc6094c0fffa84a632ff94253197faa12981ffc5094c65ffa04a632ff90253197fa81298cbfc4094c0bff984a605ff8c25302ffa6129817fc3094c65ff904a632ff88253197fa41298cbfc2094c65ff884a632ff84253197fa21298cbfc1094c01ffb22a600bfd9153007fcc8a9803fd6454c01fe322a606bf1915303ffea8a9803fe5454c01bf2a2a600ff5515303ff8a8a98037c5454c0fffa9aa607f7d4d5302ffca6a98177e5354c01ffb12a600bfd895318ffcc4a980efe6254c01feb12a631ff1895301df8c4a98c7fe5254c63bf292a607ff1495318ef8a4a98c7fe4254c63fe212a631ff8c95302ff864a9803ff6154c017fb0aa630ff98553015fcc2a9803fd6154c61fe30aa602bf18553187fca2a981ffc5154c61ff20aa630ff10553187fc62a9817fc3154c63ff90aa630ff88553187f842a98bfff6054c5f7fb02a62fff9815300dfcc0a98bffd6054c5f7eb02a62fff1815300df8c0a981fff5054c5fbfa82a62fff9415317ffaa0a98bf7d5054c0ffe282a62fffd015317ffc80a98bffd4054c5ffe202a605ffcc15317ffc60a98bffd3054c0bfe182a62fffc815317ffc40a98bffd2054c5ffe102a62fffc415317ffc20a98bffd1054c5ffe082a607bf9945302ffec829817fe6414c0d7f320a605ff59053005fac829817fc6414c0fffaa0a607dfd505303ffca82981ffd5414c01beaa0a607ff1505302dfcc629817ff5314c0bbfa98a605ff94c5302fbca629817fd5314c0bbea98a607f754c5302ffec429817fe6214c077f310a605ff58853005fac429817fc6214c077e310a607ff9485303ff8a4298bbfe4214c5dfe210a605ff8c85302ff86429817ff6114c0bff308a602bf9845302ffac229802fd6114c0
  | 8 => 0xf14654037fc832a01bfc419507fff18ca83fff0c654207fe432a0fffe219507ffe10ca806ffd8254035fec12a01bfe60950037f304a806ff582541f5fac12a01bfc60950037e304a807ffd42541f7fca12a0fbfd509500ffe284a806ffd0254037fc812a01bfd409500dfe204a83effcc2541f7fc612a0fbfd309507dfe184a83effc82541f7fc412a0fbfd209507dfe104a83effc42541f7fc212a0fbfd109507dfe084a807ffd515403f7ea8aa01bfe545500dbf2a2a800ffd8d54005fec6aa003fe6355001feb1aa800ff18d5402df8c6aa003ff62550017fb12a83dff9895401dfcc4aa003fd625507bfe312a803bf189541effca4aa0f77e525500ffe292a83ddf149541effc84aa01bfc425507bff192a83dff0c954007fec2aa002ff6155079ff30aa802bf98554007fac2aa0f3fc61550057e30aa83cff9455403ff8a2aa0f3fe415500dfe20aa83cff8c5541e7f862aa0f7ff2155079ff10aa83cff085541dffec0aa0eeff6055077ff302a801bf981541dffac0aa0eefd6055077fe302a801bf1815403ffea0aa0ef7f5055077ff282a83bff541541defaa0aa01ffc505500dffa02a83bff901541dffa80aa01bfc4055077ff982a83bff8c1541dffa60aa0effc3055077ff902a83bff881541dffa40aa0effc2055077ff882a83bff841541dffa20aa0effc105500f7f328a806bf99054037fea82a01b7f541500dff2a0a806ef95054037faa82a01b7d541500fdeaa0a806ffd8c54037fcc62a016fe631500dfeb18a800bf58c54037f8c62a01bff621500dff310a803bf98854037fac42a002fd621500dfe310a803bf1885403ffca42a01ffc521500dff210a806ff108541d7fc642a0ebfc321500dffb08a806ff98454015fcc22a01bfd61150017eb08a806ff18454015f8c22a01ffe511500ffe288a806ff90454037f8822a0e7fe3115073fe188a83affc84541cffc422a0e7fc211500dffb00a806bfd8054037fcc02a006fe601500dfeb00a838bf58054037f8c02a006fc601500fffa80a807ff9405403ffaa02a01ffc501500dffa00a806ff90054037fa802a01bfc4015071ff980a838ff8c0541c7fa602a0e3fc3015071ff900a838ff880541c7fa402a0e3fc2015071ff880a838ff840541c7fa202a0e3fc101500fffb26a607ff99353035fcc9a981ffd64d4c017eb26a607ff1935303ffea9a981ffe54d4c01bf2a6a607ff5535303ff8a9a981f7c54d4c0fffb16a607ff98b5301dfcc5a981ffd62d4c017eb16a607ff18b5301df8c5a981ffe52d4c6fbf296a607ff14b5303ef8a5a98dffe42d4c6ffe216a637ff8cb5302ff865a981fff61d4c0fff30ea602bf9875303ffac3a9802fd61d4c0ffe30ea602bf1875303ffca3a981ffc51d4c6dff20ea636ff107531b7fc63a9817fc31d4c6fff90ea636ff887531b7f843
  | 9 => 0xd92000000000000000039d1b20124000000000000042a41300000005af1c892b02b200028480d0f9600038b198c0000000001d4800000013a0f9cecc00000000006980000000a0800013f0001ce40000000000000c4800000000000000000001fc8d9e7e928709b0000000000000000000000000000a00c400002200401300e200403100011182200c00080004000900001000000806020421200403004000000000001040100405100020040d09802000621040528802000460040108060000801044000060000000000050000000000a002400000810100021100e808020010000040b000001100000c00000201840100802004011006000000000c20844210001100200100108400001011080109820008200800000401000c0084e0184030084000c011006000801180010140000001104000000008c8100c03000000844618c0101c25004400004000441000a00806400002000c208c0400400180011000101083080002080201040084833808200800280020002508020020201040000001004200000200001000000000000020008201100128401380210101400420004003840000420008000006008c000100000400100031040318020004000046100401204220000108003280090002100c02024c00082100080084600000100022004810000008422080a40080000401018200048000c41280010800209000004431000100482018000000008403080000044200401084230000300001180010802110000080802044400000004007ffd8f5403ffcc7aa016fe63d500ffeb1ea800bf58f5403ff8c7aa01fff62d500fff316a803bf98b5403ffac5aa002fd62d500ffe316a803bf18b5403ffca5aa10f7e52d500ffe296a807df14b5421ffc85aa01bfc42d5087ff196a843ff0cb5403ffec3aa01ffe61d50057f30ea807ff58754005fac3aa01ffc61d50057e30ea807ff9475403ff8a3aa10bfe41d500dfe20ea842ff8c754217f863aa10fff21d5085ff10ea842ff0875403ffec1aa01eff60d500fff306a801bf9835403ffac1aa106fd60d500ffe306a801bf1835403ffea1aa01f7f50d500fff286a807ff5435420efaa1aa01ffc50d500dffa06a841ff9035420ffa81aa01bfc40d5083ff986a841ff8c35420ffa61aa107fc30d5083ff906a841ff8835420ffa41aa107fc20d5083ff886a841ff8435420ffa21aa107fc10d50777eb2ca806bf99254037fea92a01b7f549500fdfaa4a800cfd5254037fec72a01bfe639500b7f31ca806ff58e54005fac72a01bfc639500dffb14a806ff98a5401dfcc52a01bfd62950017eb14a806ff18a5401df8c52a103fe529500ffe294a806ff90a54037f8852a103fe3295081fe194a806ffd8654037fcc32a00afe619500dfeb0ca800bf58654037f8c32a00afc619507fff28ca807f
  | 10 => 0x19e9f38efa81118a80006ce00000010bc000000000106905644f000000089000000000000000bb1b18001012000000000000000000000000000000000000000000000000000000000000000005540000000000000403000000000005f04b4720000000029c0125d931d8000000000000000011600000000000000000000378fb00000000000000000000000000000038a000000031c13700002c810e27890cc08658308f000000000012880000000000de000000000020397c0000000000000000000000000001660000001c48a043dd16c87c80000000000000b2664f199000000000030b8000f803a528500000000000000f0000000000005c8000000000000000000000011b8b4e000000000000000005200001181ad00007a865200000000000000000000000000311000155c00072d00000000006a60000e84414000000000000000000008d4000000239070c98c00000000000000000220000ba86820c28000a1a45e00000003c40000f209cc2260000d000006ae000000151cdee0000001a9400069b00000000000001b40000e3e0000eb80000005411ed8f98f6400005680006c800016f0000506000000000000000019601dc0002553e91d18000713061000086e0000000bf8000018000000000000000000000000000000000a6e000077858c4ee0002d580007d07aa00000000000003d600000000000000000d9c0000001c4426400037580000003eb262163800000009007f82ae0000000000000000000000000000000000004ae0002cd8578ee64a000000000000001f68fd40000000000000000000000000000000000000000000000001ffc986000000000000035e0001590000000000000000005d00000000000000000000376632000000104e00000000000000d500000000220003210000a580003cb87448827c633000006c26b33508534fb86f60be95a01f6036332082085c1d319d800048c00015202040000b10001558000007000000000030c005000000033000000000000001038020c7423d166002c1fa63c00000000000003a400000004fb000000045800000000000002ec41610840002b4000057c00000000000004b00000000b38b160000fd16e08a00000000000e1800021f182c0004e334b0000fa20001620000c3e0000000000fbe0000001a380000001d31c3c000000000179c000000000000000000000000000000002de0000000000000000000000018d08a49a26ea00012fcc140002d50000994000000000000000020b00accb0000000000016c36900000000007c20000000000000000093466a0000001018c4600000000000000000000000000000000000000000000000000001860000000000000000000000000000010a40000001f28000a0c00000009400000000000000000000000000000000000
  | 11 => 0xdb00000000001070000cee1000289b8cb105ea00000009847be0cb80000000000001e580000000000000cd21370001ec0000370202162800000000012c0f940000e5000000000016890ac0000000000b987e41be000050c0007d3000000000042d00000000000000000000bc644033887700000000000000000292125800000002c0b70f90000000000147800000000000000007d41f18000000000393800000026900000000000000000000000000371000000000028180000000000000000bfe00000000000000002ec00000002431bd800000024529200000000000000000826000000000000071900000000000002ed00000001c90000000000000302800034a00000000000004f809d000023400027d024000000000000009a405b2489a1801e64000003e8000000000000000000000001d0000000000000000036c0000becc1254604d8b28cca00000014807f0038165800000000034097dc2585a80511c5400000000000000000000000000000000193800000047000000004be12207a174400066601d0000a24239000000000000000000000000002bd000000043b00000000000000650eb000000034c800000000015e9460000000000000045c000000118c000000000000042638807900000007340000000c4229700000000000000001bd40000002d880000000002e6800000000000000009480002cd022800076b15e0000000000000045c0000000000000b181bd000099c43673800000003ce78d1758000c607f70c6000000021d00000000007262f30000b2a1db0518e54000000000206428e42519403a42aa4973b1948c0000003b2800000000000015e0000000000000099074d00000000004460001dd40000003f780000006010001fc4000000000096c0000002da800029c0000e7800076654000000000003f100000000007af08804e4a7a41f25b9ae0b2e00033b00000000002b58000a2800036a800000000034580004280002ae959876c3fb19c80000000000000b6c00000000018d0f405302b7085800000008083a8d641e322e00004a841e00000000000000001e0485800000000000000000000000bc200000000003266f400017ac000000169000000080d15c08840000000000000eb0000000012c0000000000e08d5600001f800070648c000000000009d0001b840000000cb000000000000000000007bc12b00000000001b10000b8200000016400000000001eac2140000001ad0000000000000000000000000000000d62dd0b0800000e07298fc00078c2548fdc00000002680000006dc000000012e58916a800000000000000007400001cb000062c81822f8a943b04d01a1017c0d24392ad06d00000000000000000000000000000000017900004444770001b800000000001c687ec095000000000000000000000
  | 12 => 0x36200000008483f800000015bc2f4000000196c0000310000000000000000000000000000000000000000000000d3a1891ac81f00000000c58000c6a00000000009808163618000606000000136c00051c2d0000000000002b019078a0000179968000000000000000000020c9f88cce00036d13a8000000000000000000000001b8ed25550001f5cf8821f3eb0bd47de6fc0001f740000000000000000000000000000000038c00000000000f480000007f525c107400078e2e297f400000000013b4ab06d2000000000000036a102c00000000000000000000001a410341a600000000000001dc80000000003c7848c5620000001efc5ca3d0000000000000000000006a80000000000000000000000000081b000031c9d0000000000025400000000004e400000000000007b100000000000000238dd4ce638b00016a4406000314800000000000000000000000000e7c00000000000000004880cc07c47820ce0fb1958c0e62c2350224de02480d79cec3363100bf82f02ca44d2d600f8cd400001391ac000000000000040200014d80000000000000000000000000000052200000000008f23f4000000000009300000009fc65f2c7888c95c0000001c1800069318a00005ba75000001ec00000000000000000000000000e100000000c080001a10000000000000000000000008f3e6800102838c00000000000000000fa400037e00007300000000209388df652a342903ceac0003ba00000000000000000000010320800000000000002b00000000001cd803600009598ac68675a1c0147c0000000000000000000000091000000026a0000000000000000000000004300000000000000000000000000000000000000000000000003761444000000000000045e4f913e0ffc0000000001880f3e000000000000000000012c400000000000000000000ea038892c0000000524000000000000000000000000000000002989f6c000000000000000000000012600001682991514dc80000000000bea0000001588946000000000000000000000000000003828000ed00000000000d400000a9034c00067e0000000b640000000000eb270718500001f000000000000000003fa000000000000001141fe35c352188877044a2b00000544000000066800027d19a000000000000000001540001be000000021a28e800000000034900000000001680000000352000000000035500000000000000000000a660001a9800000000003785e46ac000000049409e7551db966400000029e0bd8b6c6b6415000030200000007a000000000000000000000201c9000000000000000005f8000000000000000000000000000001a9c000764106000097c1cb00019c80000002270000000000000000000000000000008244ef3290fccfe00000
  | 13 => 0x13d18e400000040e03cc00000018c00000005b71250f68000000000000000041513b00000004610000000f7a1e600014bc00072800000009b8580000000000000002c08240006ca000041869400003614040004a1000000042000025e00000000000000bd02707951d700000000001f700000000002af1a00000000000000027a0000000000000000000000000011500000000001ba1dd1c2800000015985d40000000000e6c00013b3610990f5c3971838000ba400000000000000000000b0c00000000000005c00c10000000c185e40001b1452000000000000007d5000000000041b0001e4c00018e000000000008000000000002613bf800000000000000000006aa033000000000000000000000000000000000000000207d01647513f000077e15b24700000000000001de433c00006c0844a7e0001d50ac0af608d0000000e7a73f0000000106000000000000000000010880000000000000a6800000000000000000000a9c0da00000000000000001ef17a0000000000180c0006d727380a902610f0000000000000000156400000000007d0ed472e0000000000000000000001a63e00013a40007da1430000fec2ae00006285b4035221963400000000000000000001ad0cfc00001f00000f0cd000000000006fa000000000011c68400000000000000000000000000000071000037f1890000514000000000000049e00000000005793a4800000000000000001b600000000000000000000000000000414800012c2e22d28e047be47838494e000000000000000003d225a91580000001f81c5c5545ad10580000000002e19b4c45a732066800081200000015b000043200000000000000aa000000000000000007aa2e83a50000f3a000000000000000025d800020e0002c280000000000000a68000000000000000020400003845084ff31505a800000000000f48701c500000009440b838204a4000000000000000000031685143ba00019b80000000000640000000103000000000000000000000000002fd80000000001a40000404000000000000000000000000000000000000000000000000000000000014a449200000000000000002c8800000000000000000000003e4800000045d0001030000730000000000000000009ac0000002eb1d4ca006cb1ca15f01d07a50001b040000000000000c1e00003c800000000035100000003b1177118077c26d3dd8c00f905e23621494ab60003ab800023600015b8000eee3fe1e8800000000000003c00000003c900000000000cc953000075b00000000500b21a28368000526000136475233100000006e881e0000eac06e4e5000187444c2bb00000000005c20000e782800000000000bd200015480000000000000e1c32200000000002f02f038180000000000000c2000061a0000000
  | 14 => 0x2b536c9ea00003e000000000000003ce00000001823ca11f400004618d80000005812fd0f24000000000000000000000000000004510eb1a288a800000000000002880001148000000000000013e0003199154000000000189c0000000000c90000000000000000072a00007ec00000000000000000000000000fc21bf00019bc186000000000038c000000000000000000000000006e713800001d60000000000c8e44b00004480000151fc80009921ff0000000c0443d0e68000000373000000000000000000000001ed0000000000434000000000000000019887d434d3bc00000000000001b187f80003e18450e52000000105c00a638238800000000000000000003720000b0400076700012a000049a000045800000031300000000000000b7cd226bb0001270a5c00000000000005863e39fcc0000003c8800000000000000000000000000890f6a2e10721e2c2ba2752a980680000000e80000d2800040e8000000000000000000013c00000000000000001f90104573000000067800000000000000000000000000000000000000047c04c000000030d00000000000001bb95240000001351840a968280000000000000000000000000027900003b20000000000d7a0000000000cf2000057054000000000000000000002360e3c00032d013195400006b00000000000000438000e163af000000095e30e17980008da6c70ea8994e027cc0fa80000000002d3000000000022100000000000000db87a60cc11e0e18a7c02d32c80000005ef0000000b8e000259000000000028d91100283d43228eec00027935f80000002620a580000003d62b3967453211d00013cc094068000167c2e00000000000000000000063c000000000000000000000007840000000000000a3400000000000000000000000000000000000000071000006cc000000000000000000000000000000000000e2400000000000000000000000000000000000000000035b000000000000000000000001b500000000002850000000ac20000000000a2000000015c8000000000000104214118c80000002bf000000000071e0000000db07a90000000b760ec000000016e0002fb19440000000001fa06f0281000031466c00000000000007763361bf417200000000008c80000000000000000000186c0006461fe8ce000000000000000000002fc8000ac65360cf80000000000000000dfc00013889740005b30989a5cd06000000000000000034f000000078400019c000000000000008cc4da21000000000000d7000000012800000010205283af1718a2c00002d1ee800000007680000000001a59894c98000000000000000021200004007ea08f9e0cbb68151c680000000003c813580000002758000e4a2b9000000000000010c993800080f0000000000006
  | 15 => 0x80b60e4cfc600000014540006140000000ae82604119738d50770000000000055f00000000000650000000212000000093803a0000001ff0bb800000000000005ec00000000005ee000146400000000015d40000000000000000000000000000072c0001d84a0e4cc000000000000000000000000000508000000000000034800000000000008220000000000fda00039e000064c00021d01f874600004c8588b46351000000000030500000004fe00000000000002a1118000000000031b80000066f90001c8c00000000000000000003bd972097a00019580003fa00011980000007511bb1d0c0006081e4000093e01e000000000000022c19fc87e00004a00002e678a00005980005c900000007480df0d91c6c9e0000000000100a71d00000000000000000000000000000000000000000004d80000001e39e840000000000000000000000000000000010c00000000003bf000000000000005600007c50001f980000001bd00000000d90fc06b10140000be15f850e0000000000000000000000000052b097184c000000000000026018405a1e0800033a00000000000001540000000403199837000023224a1db89be7d90d50000000000000000101c0000000000e6e0000000000000486373114cff400000000000003ca00200000002ab00000000000000540908000000302000000000000000000006f800000000000000000000de600024480000000000000f880000000000000000000000000000000007e13dc3e66cd0001a54bba0000000000000000000053000000000000000004d300000006b0000000195cde43c301499f47b21eb0001d0859a6ff2a780007f4000000000000031d00000000000000000e1073800000013140000000000000c626bc4100000000000000000039050c0000000814000000000000000000000000e60300000894000000000000000014f0e0000000000017d1710ede00024501881ec1190128000e6633e035055800000016a1034fca7b30dc868c0000003fd926439c0001ee000000026335c80000000002be80000000000000ec088a00030012cc00000000000000000bf37299740000000000000b44000000000000000035f00009964fc029800000067a0000000a9400009087b800023b0000000000146000000068200000000000000001c280000000000000000000000000000000046837400000007620e1000000070207a80000006ee00016fcafe19034d018c3c0055356000052c0000000000000000123800000007a3f7000000000000000000002680000ba800010b180800000057000000000000003db02e84de6b507300001960000090000c862ed27e800000000000000000fa000000000000014416b143c000492000000060847a2cf136000029800007688b65270000e7414c000272000
  | 16 => 0x262c709f1940c880000000000000000378948400028b000000000000009300000000000001d802ec00036e80002b8000000000017a4dd000000000025e00b0a381ce648000000000025300015dcaca0000001fb0e7c74000000001c000000000000f000020e00000008031ae800000051700000000002ff15b00000000001e79de800032004e0000000000000000040c7871de0c88000000000000000048b000000094c80400000000000c6397800000000003800000000000390000baa0391c700000000000000bdc00022000000005f20001d4000000000026f000000000000000003bc00000000000320000fc97c4aa40000000000000000000000084e5b93c480cc3825cb00000000000001a20a345ce000000000000000000000000000002fe000045400036f000000029500000000000000000000000000000000000000000000000000000bd800000036029d00000001880000000000000000000000000004880000007a620c0000f8231e00000000004953f00c4c000482000000000000003380000004842328124e963cb3cd1380f3c74c02f0d40f0c00000000000005a400000000000000000000000000000067000000012600000000000001e000000002f682ace40000000000000000000012e400000000000009dc0002338c2c2c23cd40600000006d100000000000002820000d1e0850000000b5c09a2c118780000002b880c8000280000000000000018f88c40006af00000000000000000000000000115800000066d3178000000000000000000000011a04cca6a0000210000e6268934380000000000000084cd600000003f80040000000000c6c0000000000044000329822000000000000001ba000000000075a00000000005c830f00000000000001b690508b22cf00000000000003d1046049e00038e00000000001eb8000558000000000000000000000000005d300011f80000000001f9c00000000000000004ad2c3942000037100003c40b200040b800000000000002a400064b412890400035f000000099a00023f800031a00035180000000002ff00003600000000000000000000000025e000253800000064d1d1148894a14a27b00000001b74008000000000000000000000000000000000003b61e8c00000000000000000000ef80002d6550000000000043c0000000000000000015c0000003fc000000000000011d8000000000044400000000000009aa0000000a240000000000f600000002ef8148a165d736b19e0d5c4c700000000001a8000103800000032f00005b80003a708dc0000000001a6000005433d80002e200038000000000003cd8000f720003d3800089200026080004b84b600000000006ad000000000000000000000003790000000d6e55100017d00000000000b000004260000000d3e1b
  | 17 => 0x35d0000000000000000000011c00000001a04312f29ee00000000000000000000000000060c2ef12c89ec2c0398000052000000000000000006ef000000000017e000017047c4e614f043000000012d000000039a0000300000722000069c0004233e8153880a0002da000000000000000000000000000000b9e1d203f88549e82d715f000000068d28980000002280000d0042e0002bb00000000000000ec8000000000000000000000000005e20000000000d6078800000002d200000000000000000000000000000000000026a0000000000b28000000000000000000000006ca00000000000000003588f8400003b0000000000000000000000000026b80009d80000869928000017000000014a00038700000004903a080000000000c900000000002d080006540000001e6000000000000000002d800000008020000000000f320000001658f0a0000000000b94000000000000000000000009560001a795700ea6740000000c5020501719f016a1c714610d45f80c91da95b4c3825209211d0000000223800099c00024780000000000000a3c000000000059c0000000f2800000044c00011a40000000000000a7200036d8ac8000000231000000000026780004cc0003af91ec74e000239800000077c29d800000016d240000000054303080002e800000000000000003f58b200000000000001010000082865400000000007dc09067500000000000000000000c240000000000000000000000000062e0001eb400049321b19700000000000000d387cf000035c0e200000000000000000001414eb83bd0c380000002f80000000000000000013000029407c80000001801b30a9868e0000000d18000824057800000000000000000000000000000be40000a1000065c00006797783d80000688b24dbe00000000000000000000000000000246800053861511f800053e8000bb8f0800000000000000000001848abc53a2a0000013800000000007bc0000003ef0000000483000000000000030b1b4000056a27a9d5000000000012146de46f34601800002360001d3c78c0000000000a880000000000c1a00000000000007b4000000076800c31e80000007a400000000000000000ab40000b02b4800044e00000003b83440010718000d98000197883400000000000800003cc3db80000000003908000000000000126c000000000000081000016300000000000000ae80006fa00006a4b2448724e80000000003a20000850000000000000000000011680000001e706500005be00019b8000822000000000000000000000006490000000000400386966000074500010080000000001a2082024009a1bb47324aa00000001ee00000000000005c000000000005bd000000033a0000000000000000000198458a15a190800000058400000
  | 18 => 0x102415301180000000002a4000000075d000000000000000015080000241c51950000618093981800000000004080002e300000000000760001ba400000013c0d380000003548dac0002fd22b85440001084039dc800000000000000002d3000000013c0001e20000000000000000000000024080005d232311d000000000006a1ff80000000000000000000000000000000000000700000000501740c1c104000000000036a00000009c200025a0c94d8076d0000a8c000000107800000072b00016700005f3000000062e00000000005260000f800000000003fc800000018300000000001a4000000000077100012e80000000000000e8e0000001cd4000000000000069221c2a696c00005cc00000000000000000000ffa21e000000000000029685bc72400030888e00000842f000000001ab00000000008021f610c0c320
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc705912106eef2059121006ed20591210cef71059121006f51059121234fe76191210067f65191210067c6519121036be6419121006bd641912103cff76d5121004fe76d5121004fd76d512103cfc76d51210067f65d512103e7c65d5121034ff7695121004fe7695121004fd7695121034fc76951210067f659512103e7c65951210073f5495121004ff7655121004fe7655121004fd7655121004fc76551210067f655512103e7c6555121034ff7615121004fe7615121004fd7615121034fc76151210067f651512103e7c651512102cfe76d8d210067f65d8d210067c65d8d2103cfe75d8d21004fd75d8d21034fe74d8d21004fd74d8d21014ff72d8d2101cfe72d8d21014fd72d8d2101cfc72d8d2122edf32d8d2122edd32d8d2101cff71d8d21014fe71d8d2101cfd71d8d21014fc71d8d21226df31d8d21226dd31d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d2122eef20d8d21006ed20d8d21226f710d8d21006f510d8d210acfd7698d210057e7598d210057d7598d210067f6598d210067c6598d21005be7498d21005bd7498d21006df6398d210aded7298d2104df57198d2102cff7658d210057f7558d210057c7558d210067f6558d210067c6558d210bdef7258d2105df77158d21004ff7558d210067f7558d210047f7558d2103cfc7558d210067c7558d2103c7c7558d21004ff7458d21034fc7458d21006df7358d210bcff7258d21006ef7258d210acff7158d21006f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d2104eef2058d21006ed2058d210aef71058d21006f51058d21224fe7618d210067f6518d210067c6518d2102ede6318d21006dd6318d2103cff76d4d21004fe76d4d21004fd76d4d2103cfc76d4d210067f65d4d2103e7c65d4d2102cff7694d21004fe7694d21004fd7694d2102cfc7694d210067f6594d2103e7c6594d210075f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2103e7c6554d2102cff7614d21004fe7614d21004fd7614d2102cfc7614d210067f6514d2103e7c6514d21034ff76d0d21004fe76d0d21004fd76d0d21034fc76d0d210057e75d0d210057d75d0d210067f65d0d210067c65d0d21006bf64d0d21036bc64d0d2102cff7690d21004fe7690d21004fd7690d2102cfc7690d210057e7590d210057d7590d210067f6590d210067c6590d21006df6390d2102edc6390d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210067f6550d210067c6550d21006bf6450d21036bc6450d21006df6350d2102edc6350d2102cff7610d21004fe7610d21004fd7610d2102cfc7610d210067f6510d210067c6510d210079d4310d2101dee7210d21005ed7210d21
  | 1 => 0x952125e7c20d95212567f10d95212567e10d95212567d10d95212567c10d95210ecfd76995210067f65995210eded72995210feef629952108df5719952103cff76595210fdef725952109df771595210067f7559521004ff7459521034fc7459521004ff735952102cfc73595210fcff7259521006ef72595210fcef72595210ecff7159521006f77159521004ff705952100cfe7059521004fd705952100cfc7059521254fe761952103e7e65195210067d6519521246ef62195212557e76195210067e76195212547e761952124f7721195212476e21195212476c21195212477421195210067f60195210067e60195210067d60195210067c601952124f6f20195210076d201952124777101952100775101952103e7f741952103e7e741952103e7d741952103e7c741952103e7f731952103e7e731952103e7d731952103e7c731952103e7f721952103e7e721952103e7d721952103e7c721952124e7f421952124e7e421952124e7d421952124e7c421952124e7f321952124e7e321952124e7d321952124e7c321952103e7f711952103e7e711952103e7d711952103e7c71195212467f41195212467e41195212467d41195212467c41195212467f31195212467e31195212467d31195212467c31195212467f21195212467e21195212466e21195212467d21195212467c21195212466c211952103e7f701952103e7e701952103e7d701952103e7c70195210067f40195210067e40195210067d40195210067c40195210067f30195210067e30195210067d30195210067c301952124e7f201952124e6f201952124e7e201952124e7d20195210066d201952124e7c20195212467f10195212467710195212467e10195212467d10195210067510195212467c1019521034fe76d91210067f65d91210067c65d912103cfe75d9121004fd75d912102cfe73d9121004fd73d9121014ff72d912101cfe72d9121014fd72d912101cfc72d912123ebf42d912123ebd42d912101cff71d9121014fe71d912101cfd71d9121014fc71d9121236bf41d9121236bd41d9121004ff70d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d912123eef20d9121006ed20d9121236f710d9121006f510d91210ccfd76991210057e75991210057d75991210067f65991210067c6599121006bf6499121005de7399121005dd73991210cded729912106df57199121034ff76591210057f75591210057c75591210067f65591210067c65591210ddef725912107df77159121004ff75591210067f75591210047f755912103cfc75591210067c755912103c7c7559121006bf7459121004ff735912102cfc73591210dcff7259121006ef72591210ccff7159121006f77159121004ff705912100cfe7059121004fd705912100cf
  | 2 => 0x67f65d4d3103e7c65d4d3102f5e53d4d31015f671d4d31005f571d4d3103cff7654d31014fe7654d31184fd7654d31014fc7654d310067f6554d3103e7c6554d31005f77154d31015f47154d3102fd43154d31014fe76d0d31014fc76d0d310057e75d0d310057d75d0d31006bf64d0d31036bc64d0d31015f671d0d31005f571d0d31034ff7650d31014fe7650d31124fd7650d31014fc7650d31006bf6450d31036bc6450d3102f9c4350d31005f77150d31015f47150d3101cfe76d893104eee62d893103cfe75d8931004fd75d8931034fe74d8931004fd74d8931014fd73d893101cfc73d893104eec52d893104eee42d893104eee32d8931014fe71d893102cfd71d8931014fc71d89310beef21d8931004ff70d893100cfe70d8931004fd70d893100cfc70d8931006ee20d893104eec20d89310bef710d8931006f510d89310057f75589310057c755893104eec6258931004fe76d4931004fd76d493103cfc76d4931006ef62d493101eec62d493104f6e52d4931004ff7654931004fe7654931004fc7654931004fe76d0931004fd76d0931034fc76d09310057e75d09310057d75d0931004ff7650931004fe7650931004fc7650931006ef625093101eec6250931005f77150931015f47150931014fc764c931006ef624c93101eec624c931005f7714c931015f4714c93103cfe76d9521034fe74d9521004fd74d952102cfe73d9521004fd73d9521014ff72d952101cfe72d9521014fd72d952101cfc72d952125e7f52d952125e7d52d952101cff71d9521014fe71d952101cfd71d9521014fc71d95212567f51d95212567d51d9521004ff70d952100cfe70d9521004fd70d952100cfc70d95210067f50d95210067e50d95210067d50d95210067c50d952103c7e76d952125f7721d95212576e21d95212576c21d95212577421d95210067f60d95210067e60d95210067d60d95210067c60d952125f6f20d95210076d20d95212577710d95210077510d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95212567f72d952125e7e72d95212567d72d95212567c72d952125e7f42d952125e7e42d952125e7d42d952125e7c42d952125e7f32d952125e7e32d952125e7d32d952125e7c32d95212567f71d95212567e71d95212567d71d95212567c71d95212567f41d95212567e41d95212567d41d95212567c41d95212567f31d95212567e31d95212567d31d95212567c31d95212567f21d95212567e21d95212567c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95210067f30d95210067e30d95210067d30d95210067c30d952125e7f20d952125e7e20d952125e7d20d
  | 3 => 0xf655533103e7c6555331005f77155331015f47155331034ff761533102cfe7615331004fd761533102cfc761533103e7e65153310067d6515331036be6415331006bd6415331004ff7558b3103cfc7558b31004ff7458b31034fc7458b31014fe7358b3101cfd7358b31014fc7358b3102eef7258b3105eec5258b3105eec4258b3102eef3258b3102eec3258b310aeef2158b31004ff7058b3100cfe7058b31004fd7058b3100cfc7058b3105eef2058b31006ed2058b3103cff76d4b3102cfe76d4b31004fd76d4b3101eee62d4b31006ed62d4b3105f6e52d4b31004ff7654b31004fd7654b3102cfc7654b31005f77154b31015f47154b31034ff76d0b3102cfe76d0b31004fd76d0b310057e75d0b310057d75d0b3101eee62d0b31006ed62d0b31015f671d0b31005f571d0b31004ff7650b31004fd7650b3102cfc7650b3103cfe76d9531034fe74d9531004fd74d953102cfe73d953102cfc73d953101cfe72d9531004fd72d953101cfc72d95310067e52d95310067c52d953102cff71d953102cfd71d953119e7f51d953119e7d51d9531004ff70d953100cfe70d9531004fd70d953100cfc70d95310067e50d95310067c50d95310067f6599531185dd73995311b5df7359531005ef725953104dec72595310067f7559531004ff7459531034fc74595311b4ff7359531006df7359531004ff7259531006ef7259531004ef725953101cfe725953101cfc7259531006ec725953101cec7259531184ff7159531006f77159531004ff705953100cfe7059531004fd705953100cfc705953119cfe761953103e7e65195310067d6519531034fe76d913103cfe75d9131004fd75d913102cfe73d913102cfc73d913101cfe72d9131004fd72d913101cfc72d913102cff71d913102cfd71d913113ebf41d913113ebd41d9131004ff70d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d913113ef710d9131006f510d91310057e75991310057d7599131006bf6499131125dd739913104dee7299131005ed7299131155df7359131004ff755913103cfc7559131006bf7459131154ff7359131006df7359131004ff725913101cfe725913101cfc7259131124ff7159131006f77159131004ff705913100cfe7059131004fd705913100cfc7059131126f71059131006f5105913113cfe7619131036be6419131006bd641913103cff76d5131004fe76d5131004fd76d513103cfc76d51310067f65d513103e7c65d513102dde73d5131005dd73d5131034ff7695131004fe7695131004fd7695131034fc76951310073f5495131004ff7655131004fe7655131004fd7655131004fc76551310067f655513103e7c6555131034ff7615131004fe7615131004fd7615131034fc7615131014fe76d4d31014fc76d4d31
  | 4 => 0x514102cfe76d8d4103cfe75d8d41004fd75d8d4101cfe72d8d41004fd72d8d4101cfc72d8d41034fd71d8d41156df31d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d41156f710d8d41006f510d8d410057e7598d410057d7598d41006df6398d4106dee7298d41005ed7298d4102ede6318d41006dd6318d41004fe76d4d41004fd76d4d4103cfc76d4d410067f65d4d4103e7c65d4d41035be74d4d41005bd74d4d41004fe7694d41004fd7694d4102cfc7694d410075f5394d41004ff7654d41004fe7654d41004fc7654d410067f6554d4103e7c6554d41004fe7614d41004fd7614d4102cfc7614d41014fe7690d410057e7590d410057d7590d41006df6390d4102edc6390d41015f67190d41005f57190d41014fc7650d41006df6350d4102edc6350d410379c4350d41005f77150d41015f47150d4101cfe76d894106eee62d894103cfe75d8941004fd75d8941014fd74d894101cfc74d894102cfe73d8941004fd73d894106eec52d894106eee42d894106eee32d8941034fd71d89410deef21d8941004ff70d894100cfe70d8941004fd70d894100cfc70d8941006ee20d894106eec20d89410def710d8941006f510d89410057f75589410057c755894106eec6258941004fe76d4941004fd76d494103cfc76d4941006ef62d494101eec62d494106f6e52d4941004ff7654941004fe7654941004fc7654941014fc7650941006ef625094101eec6250941005f77150941015f47150941004fe76cc941004fd76cc94102cfc76cc9410057e75cc9410057d75cc941004ff764c941004fe764c941004fc764c941006ef624c94101eec624c941005f7714c941015f4714c94102e7f7559731004ff7459731034fc745973102cff7359731014fe735973102cfd7359731014fc735973102e7e535973102e7c5359731004ff725973101cfe725973101cfc72597310067e52597310067c52597311867f51597311867d5159731004ff705973100cfe7059731004fd705973100cfc70597310067f50597310067d5059731004ff755933103cfc755933102ebf745933102cff7359331014fe735933102cfd7359331014fc735933102ebe435933102ebc4359331004ff725933101cfe725933101cfc7259331006be4259331006bc4259331126bf4159331126bd4159331004ff705933100cfe7059331004fd705933100cfc7059331006bf4059331006bd405933103cff76d533102cfe76d5331004fd76d533102cfc76d533126e7f65d533103e7c65d5331036be64d5331006bd64d533102dde73d5331005dd73d5331034ff769533102cfe7695331004fd769533102cfc769533103e7e65953310067d65953310073f5495331004ff765533102cfe7655331004fd765533102cfc76553312667
  | 5 => 0x14fe7459741034fd7459741014fc74597410367e54597410367c5459741004ff735974102cfc7359741004ff725974101cfe725974101cfc72597410067e52597410067c52597411e67f51597411e67d5159741004ff705974100cfe7059741004fd705974100cfc70597410067f50597410067d5059741004ff7558f4103cfc7558f41014fc7458f41036df7358f41036df4358f41036dc4358f41004ff7258f4101cfe7258f4101cfc7258f41006de3258f41006dc3258f41126df3158f41004ff7058f4100cfe7058f41004fd7058f4100cfc7058f41006df3058f41006dd3058f4103cff76d4f41034fe76d4f41004fd76d4f4127e7f65d4f4103e7c65d4f41035be74d4f41005bd74d4f4102ede63d4f41006dd63d4f4102cff7694f41034fe7694f41004fd7694f4103e7e6594f410067d6594f410075f5394f41004ff7654f41004fd7654f41034fc7654f412767f6554f4103e7c6554f41005f77154f41015f47154f4102cff7614f41034fe7614f41004fd7614f4103e7e6514f410067d6514f4102ede6314f41006dd6314f41004ff7558b4103cfc7558b41014fe7458b4101cfd7458b41014fc7458b41004ff7358b4102cfc7358b41036ef7258b4107eec5258b41036ef4258b41036ec4258b4107eec3258b410ceef2158b41004ff7058b4100cfe7058b41004fd7058b4100cfc7058b4107eef2058b41006ed2058b4103cff76d4b41034fe76d4b41004fd76d4b4101eee62d4b41006ed62d4b4107f6e52d4b41004ff7654b41004fd7654b41034fc7654b41005f77154b41015f47154b4102cff76ccb41034fe76ccb41004fd76ccb410057e75ccb410057d75ccb4101eee62ccb41006ed62ccb41015f671ccb41005f571ccb41004ff764cb41004fd764cb41034fc764cb4103cfe76d9541034fe74d9541034fc74d954102cfe73d9541004fd73d954101cfe72d9541004fd72d954101cfc72d95410067e52d95410067c52d9541034ff71d9541034fd71d95411fe7f51d95411fe7d51d9541004ff70d954100cfe70d9541004fd70d954100cfc70d95410067e50d95410067c50d95410067f65995411e5bd7499541215bf7459541005ef725954106dec72595410067f7559541214ff7459541006bf7459541004ff735954102cfc7359541004ff7259541006ef7259541004ef725954101cfe725954101cfc7259541006ec725954101cec72595411e4ff7159541006f77159541004ff705954100cfe7059541004fd705954100cfc70595411fcfe761954103e7e65195410067d6519541014fe76d5141014fc76d51410067f65d514103e7c65d51410373e54d5141015f671d5141005f571d514103cff7655141014fe76551411e4fd7655141014fc76551410067f655514103e7c6555141005f77155141015f47155141037b4415
  | 6 => 0xf6350d5102edc6350d5112eec6250d51004fe7610d51004fd7610d5102cfc7610d5103d7e7510d510057d7510d510079d4310d51116ec6210d5101cfe76d895108eee62d8951014fd75d895101cfc75d8951034fe74d8951004fd74d895102cfe73d8951004fd73d895108eee52d895108eee42d895108eec42d895108eee32d895108eec32d895103cfd71d89510feef21d8951004ff70d895100cfe70d8951004fd70d895100cfc70d895108eef20d8951006ee20d8951006ed20d895108eec20d8951245ee76d895101cee76d8951006ef64d8951006ee64d8951006ed64d8951006ec64d89510076f54d89510076d54d8951006ef63d8951006ee63d8951006ed63d8951006ec63d89510076f53d89510076d53d895128fe751d89510ff6e51d89510ff6c51d89510ffe451d8951006ef60d8951006ee60d8951006ed60d8951006ec60d89510feef75d895108eee75d89510feed75d89510feec75d8951006ef74d8951006ee74d8951006ed74d8951006ec74d895128eef54d8951006ee54d8951006ed54d895128eec54d8951006ef73d8951006ee73d8951006ed73d8951006ec73d895128eef53d8951006ee53d8951006ed53d895128eec53d8951006ef43d8951006ee43d8951006ed43d8951006ec43d89510feef71d89510feee71d89510feed71d89510feec71d89510feef51d89510feee51d89510feec51d89510feef41d89510feee41d89510feed41d89510feec41d89510feef31d89510feee31d89510feed31d89510feec31d8951006ef70d8951006ee70d8951006ed70d8951006ec70d895128eef50d8951006ee50d8951006ed50d895128eec50d8951006ef40d8951006ee40d8951006ed40d8951006ec40d8951006ef30d8951006ee30d8951006ed30d8951006ec30d89510feef10d89510feee10d89510feed10d89510feec10d895108eec62589510fdee761895108eee7618951246ef65189512466f6518951006ef6418951006ee6418951006ed6418951006ec64189510076f54189510076d5418951006ef6318951006ee6318951006ed6318951006ec63189510076f53189510076d5318951246ef6118951287e751189512476e51189512476c5118951247e45118951006ef6018951006ee6018951006ed6018951006ec6018951014fc7654951006ef625495101eec6254951005f77154951015f47154951004fe76d0951004fd76d0951034fc76d095103d7e75d09510057d75d0951006ef62d095101eec62d0951004ff7650951004fe7650951004fc7650951006ef625095101eec6250951004fe76cc951004fd76cc95102cfc76cc95103d7e75cc9510057d75cc951006ef62cc95101eec62cc951004ff764c951004fe764c951004fc764c951006ef624c95101eec624c9510367f7559741034ff7459741
  | 7 => 0x915102cfe73d9151004fd73d915101cfe72d9151004fd72d915101cfc72d915103cfd71d9151216bf41d9151004ff70d915100cfe70d9151004fd70d915100cfc70d9151006be40d9151006bc40d9151006bf6499151005de7399151005dd739915108dee7299151005ed7299151005ef725915108dec7259151036be6419151006bd64191511cd7e76d515103e7e76d51510367e64d51510367c64d51510057d73d515126e7c63d515121e7e62d515121e7c62d515121e6c62d51510157e71d51510157c71d515103e7f61d515103f7761d51512ae7f60d51512ae7d60d5151014fe76951511e57d7595151006bf6495151036bc649515103f3f5495151206ec6295151015f67195151005f57195151014fc7655151006bf6455151036bc64551511eeec6255151005f77155151015f471551510157c76551510367c76551510147c765515103d7f745515103f3f74551510073f64551510367e64551510367c64551510073c64551510057f73551512667c63551511ee7e62551511ee7c62551511ee6c62551510077771551510157e71551510157c71551511e774715515103e7f615515103f7761551512a67f60551512a67d605515102cfe76d8d51034fe74d8d51004fd74d8d5101cfe72d8d51004fd72d8d5101cfc72d8d5103cfd71d8d511b6df31d8d51004ff70d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51006de30d8d51006dc30d8d51005be7498d51005bd7498d51006df6398d5108dee7298d51005ed7298d51005ef7258d5108dec7258d5102ede6318d51006dd6318d5116d7e76d4d5103e7e76d4d510057d74d4d5127e7c64d4d5102e7e63d4d5102e7c63d4d511be7e62d4d511be7c62d4d511be6c62d4d510157e71d4d510157c71d4d5103e7f61d4d5103f7761d4d5129e7f60d4d5129e7d60d4d51014fe7694d511857d7594d51006df6394d5102edc6394d5103f5f5394d511a6ec6294d51015f67194d51005f57194d51014fc7654d51006df6354d5102edc6354d5118eec6254d51005f77154d51015f47154d510157c7654d5102e7c7654d510147c7654d510057f7454d512767c6454d5103d7f7354d5103f5f7354d510075f6354d5102e7e6354d5102e7c6354d510075c6354d5118e7e6254d5118e7c6254d5118e6c6254d51007777154d510157e7154d510157c7154d51187747154d5103e7f6154d5103f776154d512967f6054d512967d6054d51004fe76d0d51004fd76d0d51034fc76d0d5103d7e75d0d510057d75d0d51006bf64d0d51036bc64d0d5115eec62d0d51004fe7690d51004fd7690d5102cfc7690d5103d7e7590d510057d7590d51006df6390d5102edc6390d51146ec6290d51004ff7650d51004fe7650d51004fc7650d5103d7e7550d510057d7550d51006bf6450d51036bc6450d51006d
  | 8 => 0x3e7c6554d3202f5c5354d32005ef7254d3201dec7254d3202fcc3254d3201cfe76d0d3201cfc76d0d320057e75d0d320057d75d0d32006bf64d0d32036bc64d0d3201dee72d0d32005ed72d0d32034ff7650d3201cfe7650d3212cfd7650d3201cfc7650d32006bf6450d32036bc6450d3202f9c4350d32005ef7250d3201dec7250d3202fcc3250d32014fe76d85320aef661d853203cfe75d8532004fd75d8532034fe74d8532004fd74d853201cfd73d8532014fc73d853202cfd72d8532014fc72d85320aef451d85320aef641d85320aef631d85320aef621d8532004ff70d853200cfe70d8532004fd70d853200cfc70d853205eef20d8532006ed20d8532006f610d85320aef410d85320057f75585320057c75585320aef46158532014fc755935103ebf745935103ebf545935103ebc5459351004ff735935102cfc7359351004ff725935101cfe725935101cfc72593511e6bf4159351004ff705935100cfe7059351004fd705935100cfc70593511e6f71059351006f5105935103d7f76553510067f765535103f3f74553510367e64553510367c64553510057f73553512667e63553511ee7e625535103e7c62553510157e71553510157c715535103e7f60553512ce7d60553511e77710553512c7751055351014fc7558f51004ff7458f51034fc7458f5103edf7358f5103edf5358f5103edc5358f51004ff7258f5101cfe7258f5101cfc7258f51186df3158f51004ff7058f5100cfe7058f51004fd7058f5100cfc7058f51186f71058f51006f51058f5103d7f7654f510067f7654f510057f7454f512767e6454f5103f5f7354f5102e7e6354f5102e7c6354f5118e7e6254f5103e7c6254f510157e7154f510157c7154f5103e7f6054f512be7d6054f51187771054f512b7751054f51034ff76d0f5103cfe76d0f51004fd76d0f5103d7e75d0f510057d75d0f5102cff7690f5103cfe7690f51004fd7690f5103d7e7590f510057d7590f51004ff7650f51004fd7650f5103cfc7650f5103d7e7550f510057d7550f51005f77150f51015f47150f5102cff7610f5103cfe7610f51004fd7610f5103d7e7510f510057d7510f510079d4310f51014fe7558b5101cfd7558b51014fc7558b51004ff7458b51034fc7458b51004ff7358b5102cfc7358b5103eef7258b5103eef5258b5103eec5258b510eeef2158b51004ff7058b5100cfe7058b51004fd7058b5100cfc7058b510eef71058b51006f51058b51034ff76d0b5103cfe76d0b51004fd76d0b5103d7e75d0b510057d75d0b51004ff7650b51004fd7650b5103cfc7650b51005f77150b51015f47150b5102cff76ccb5103cfe76ccb51004fd76ccb5103d7e75ccb510057d75ccb51004ff764cb51004fd764cb5103cfc764cb51005f7714cb51015f4714cb51034fe76d
  | 9 => 0xd73d5332034ff769533202cfe7695332004fd769533202cfc769533203e7e65953320067d65953320073f549533202dde7395332005dd7395332004ff765533202cfe7655332004fd765533202cfc765533203e7e65553320067d6555332005ef725533201dec7255332034ff761533202cfe7615332004fd761533202cfc761533203e7e65153320067d6515332004ff755873203cfc7558732004ff7458732034fc745873201cfe7358732014fd735873201cfc735873202ef771587320bef4415873202ef7315873202ef431587320bef62158732004ff705873200cfe7058732004fd705873200cfc70587320bef71058732006f5105873203cfe76d9532034fe74d9532004fd74d953202cff72d953202cfd72d95321a67f52d95321a67d52d9532014fe71d9532004fd71d9532014fc71d95320067e51d95320067c51d9532004ff70d953200cfe70d9532004fd70d953200cfc70d95320067e50d95320067c50d95320067f659953218ddd73995321bddf7359532005f771595320adf471595320067f7559532004ff7459532034fc74595321bcff7359532006df735953218cff7259532006ef725953218e7e525953218e7c5259532004ff7159532006f77159532004f77159532014fe7159532014fc7159532006f47159532014f47159532004ff705953200cfe7059532004fd705953200cfc70595321a4fe761953203e7e65195320067d6519532034fe76d913203cfe75d9132004fd75d913202cff72d913202cfd72d9132146bf42d9132146bd42d9132014fe71d9132004fd71d9132014fc71d9132004ff70d913200cfe70d9132004fd70d913200cfc70d9132006be40d9132006bc40d9132146ef20d9132006ed20d91320057e75991320057d7599132006bf649913212ddd73991320adf67199132005f5719913215ddf7359132004ff755913203cfc7559132006bf745913215cff7359132006df735913212cff7259132006ef7259132004ff7159132014fe7159132014fc7159132004ff705913200cfe7059132004fd705913200cfc705913212eef2059132006ed2059132144fe7619132036be6419132006bd641913203cff76d5132004fe76d5132004fd76d513203cfc76d51320067f65d513203e7c65d513202dde73d5132005dd73d5132034ff7695132004fe7695132004fd7695132034fc76951320073f549513202dde7395132005dd739513201dee7295132005ed7295132004ff7655132004fe7655132004fd7655132004fc76551320067f655513203e7c6555132034ff7615132004fe7615132004fd7615132034fc761513201cfe76d4d3201cfc76d4d320067f65d4d3203e7c65d4d3202f5e53d4d3201dee72d4d32005ed72d4d3203cff7654d3201cfe7654d3218cfd7654d3201cfc7654d320067f6554d32
  | 10 => 0x8542006f610d85420cef410d85420057f75585420057c75585420cef4615854203e7f749973203e7e749973203e7d749973203e7c749973202e7f739973202e7e739973202e7d739973202e7c739973202e7f439973202e7e439973202e7d439973202e7c439973203e7f729973203e7e729973203e7d729973203e7c72997321be7f42997321be7e42997321be7d42997321be7c429973202e7f329973202e7e329973202e7d329973202e7c329973203e7f719973203e7e719973203e7d719973203e7c71997320067e41997320067c419973202e7f319973202e7e319973202e7d319973202e7c31997321be7f21997321be7e21997321be7d21997321be7c219973203e7f709973203e7e709973203e7d709973203e7c70997320067f40997320067e40997320067d40997320067c409973202e7f309973202e7e309973202e7d309973202e7c30997321be7f20997321be7e20997321be7d20997321be7c20997320067f10997320067e10997320067d10997320067c109973202e7f7559732004ff7459732034fc745973201cfe735973201cfc735973202e7e535973202e7c535973218e7f525973218e7d5259732004ff7159732014fe7159732014fc71597320067e51597320067c5159732004ff705973200cfe7059732004fd705973200cfc70597320067f50597320067e50597320067d50597320067c50597320067f74597320067e74597320067d74597320067c745973202e7f735973202e7e735973202e7d735973202e7c735973202e7f435973202e7e435973202e7d435973202e7c435973218e7f725973218e7e725973218e7d725973218e7c725973218e7f425973218e7e425973218e7d425973218e7c425973202e7f325973202e7e325973202e7d325973202e7c32597320067f71597320067e71597320067d71597320067c71597320067e41597320067c415973202e7f315973202e7e315973202e7d315973202e7c315973218e7f215973218e7e215973218e7d215973218e7c21597320067f70597320067e70597320067d70597320067c70597320067f40597320067e40597320067d40597320067c405973202e7f305973202e7e305973202e7d305973202e7c305973218e7f205973218e7e205973218e7d205973218e7c20597320067f10597320067e10597320067d10597320067c1059732004ff755933203cfc755933202ebf745933201cfe735933201cfc735933202ebe435933202ebc435933212ebf425933212ebd4259332004ff7159332014fe7159332014fc7159332006be4159332006bc4159332004ff705933200cfe7059332004fd705933200cfc7059332006bf4059332006bd405933203cff76d533202cfe76d5332004fd76d533202cfc76d533203e7e65d53320067d65d533202dde73d5332005d
  | 11 => 0x4fd7654f42034fc7654f4203e7e6554f420067d6554f42005ef7254f4201dec7254f4202cff7614f42034fe7614f42004fd7614f4203e7e6514f420067d6514f42004ff755874203cfc755874201cfe7458742014fd745874201cfc7458742004ff735874202cfc7358742036f77158742036f74158742036f441587420def431587420def62158742004ff705874200cfe7058742004fd705874200cfc70587420def71058742006f5105874203cfe76d954202cfe73d9542004fd73d9542034ff72d9542034fd72d95422067f52d95422067d52d9542014fe71d9542004fd71d9542014fc71d95420067e51d95420067c51d9542004ff70d954200cfe70d9542004fd70d954200cfc70d95420067e50d95420067c50d95420067f65995421edbd749954221dbf7459542005f771595420cdf471595420067f755954221cff7459542006bf7459542004ff735954202cfc73595421ecff7259542006ef72595421ee7e52595421ee7c5259542004ff7159542006f77159542004f77159542014fe7159542014fc7159542006f47159542014f47159542004ff705954200cfe7059542004fd705954200cfc7059542204fe761954203e7e65195420067d651954201cfe76d514201cfc76d51420067f65d514203e7c65d51420373e54d514201dee72d5142005ed72d514203cff765514201cfe76551421ecfd765514201cfc76551420067f655514203e7c65551420373c5455142005ef725514201dec7255142037ac425514202cfe76d8d4203cfe75d8d42004fd75d8d42034fd72d8d4215edf32d8d42014fe71d8d42004fd71d8d42014fc71d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006de30d8d42006dc30d8d4215eef20d8d42006ed20d8d420057e7598d420057d7598d42006df6398d420cdf67198d42005f57198d4202ede6318d42006dd6318d42004fe76d4d42004fd76d4d4203cfc76d4d420067f65d4d4203e7c65d4d42035be74d4d42005bd74d4d42004fe7694d42004fd7694d4202cfc7694d42035be7494d42005bd7494d420075f5394d4201dee7294d42005ed7294d42004ff7654d42004fe7654d42004fc7654d420067f6554d4203e7c6554d42004fe7614d42004fd7614d4202cfc7614d4201cfe7690d420057e7590d420057d7590d42006df6390d4202edc6390d4201dee7290d42005ed7290d4201cfc7650d42006df6350d4202edc6350d420379c4350d42005ef7250d4201dec7250d42037ac4250d42014fe76d85420cef661d854203cfe75d8542004fd75d854201cfd74d8542014fc74d854202cfe73d8542004fd73d8542034fd72d85420cef451d85420cef641d85420cef631d85420cef621d8542004ff70d854200cfe70d8542004fd70d854200cfc70d854207eef20d8542006ed20d
  | 12 => 0xe74997420367d74997420367c749974203e7f739974203e7e739974203e7d739974203e7c73997420367f43997420367e43997420367d43997420367c439974203e7f729974203e7e729974203e7d729974203e7c72997420367f42997420367e42997420367d42997420367c429974221e7f329974221e7e329974221e7d329974221e7c329974203e7f719974203e7e719974203e7d719974203e7c71997420367f41997420367e41997420367d41997420367c41997420067e31997420067c319974221e7f219974221e7e219974221e7d219974221e7c219974203e7f709974203e7e709974203e7d709974203e7c70997420367f40997420367e40997420367d40997420367c40997420067f30997420067e30997420067d30997420067c309974221e7f209974221e7e209974221e7d209974221e7c20997420067f10997420067e10997420067d10997420067c10997420367f755974201cfe745974201cfc74597420367e54597420367c5459742004ff735974202cfc73597421ee7f52597421ee7d5259742004ff7159742014fe7159742014fc71597420067e51597420067c5159742004ff705974200cfe7059742004fd705974200cfc70597420067f50597420067e50597420067d50597420067c50597420367f74597420367e74597420367d74597420367c74597420067f73597420067e73597420067d73597420067c73597420367f43597420367e43597420367d43597420367c43597421ee7f72597421ee7e72597421ee7d72597421ee7c72597420367f42597420367e42597420367d42597420367c42597421ee7f32597421ee7e32597421ee7d32597421ee7c32597420067f71597420067e71597420067d71597420067c71597420367f41597420367e41597420367d41597420367c41597420067e31597420067c31597421ee7f21597421ee7e21597421ee7d21597421ee7c21597420067f70597420067e70597420067d70597420067c70597420367f40597420367e40597420367d40597420367c40597420067f30597420067e30597420067d30597420067c30597421ee7f20597421ee7e20597421ee7d20597421ee7c20597420067f10597420067e10597420067d10597420067c1059742004ff7558f4203cfc7558f4201cfc7458f42036df7358f42036df4358f42036dc4358f4212edf3258f42004ff7158f42014fe7158f42014fc7158f42006de3158f42006dc3158f42004ff7058f4200cfe7058f42004fd7058f4200cfc7058f42006df3058f42006dd3058f4203cff76d4f42034fe76d4f42004fd76d4f4203e7e65d4f420067d65d4f42035be74d4f42005bd74d4f4202cff7694f42034fe7694f42004fd7694f4203e7e6594f420067d6594f42035be7494f42005bd7494f420075f5394f42004ff7654f42
  | 13 => 0x935200cfe7059352004fd705935200cfc70593521eeef2059352006ed205935201cfc7558f52004ff7458f52034fc7458f5203edf7358f5203edf5358f5203edc5358f5218e7e5258f5203e7c5258f5218edf3258f52004ff7158f52014fe7158f52014fc7158f52004ff7058f5200cfe7058f52004fd7058f5200cfc7058f5218eef2058f52006ed2058f52034ff76d0f5203cfe76d0f52004fd76d0f5203d7e75d0f520057d75d0f5215f6e52d0f5202cff7690f5203cfe7690f52004fd7690f5203d7e7590f520057d7590f521476e5290f52004ff7650f52004fd7650f5203cfc7650f52005ef7250f5201dec7250f5212f6e5250f5202cff7610f5203cfe7610f52004fd7610f520079d4310f5201dee7210f52005ed7210f521176e5210f5201cfe7558752014fd755875201cfc7558752004ff7458752034fc7458752004ff735875202cfc735875203ef7715875203ef7515875203ef451587520feee21587520fef621587520fee621587520feec2158752004ff705875200cfe7058752004fd705875200cfc705875208eef2058752006ed2058752034fe76d915202cfe73d9152004fd73d915203cfd72d915221e7e52d915221e7c52d915221ebf42d9152014fe71d9152004fd71d9152014fc71d9152004ff70d915200cfe70d9152004fd70d915200cfc70d9152006bf6499152005f771591520edf47159152036be6419152006bd641915201cfe7695152006bf6495152036bc649515203f3f549515201dee7295152005ed729515201cfc76551521ee7f6555152006bf6455152036bc645515203f3c5455152005ef725515201dec725515202cfe76d8d52034fe74d8d52004fd74d8d5203cfd72d8d521be7e52d8d521be7c52d8d521bedf32d8d52014fe71d8d52004fd71d8d52014fc71d8d52004ff70d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52006df6398d52005f77158d520edf47158d5202ede6318d52006dd6318d5201cfe7694d52006df6394d5202edc6394d5203f5f5394d5201dee7294d52005ed7294d5201cfc7654d5218e7f6554d52006df6354d5202edc6354d5203f5c5354d52005ef7254d5201dec7254d52004fe76d0d52004fd76d0d52034fc76d0d5203d7e75d0d520057d75d0d52004fe7690d52004fd7690d5202cfc7690d5203d7e7590d520057d7590d52004ff7650d52004fe7650d52004fc7650d52004fe7610d52004fd7610d5202cfc7610d520079d4310d52014fe76d85520eef661d855201cfd75d8552014fc75d8552034fe74d8552004fd74d855202cfe73d8552004fd73d855203cfd72d85520eef651d85520eef441d85520eef431d85520eef621d8552004ff70d855200cfe70d8552004fd70d855200cfc70d85520eef710d8552006f510d85520eef461585520367f74997420367
  | 14 => 0x35bc7454d4302f9c4354d4301cfe76d89430057e75d89430057d75d894312eee62d894303cfe75d89430067e75d894303c7e75d8943004fd75d89430067d75d89430047d75d894302cfd74d8943034fd73d894312eec52d894312eee42d894312eee32d8943014fe71d8943004fd71d8943014fc71d8943004ff70d894300cfe70d8943004fd70d894300cfc70d894312eec6258943014fe76d8543126f661d854303cfe75d8543004fd75d854302cfd74d8543034fd73d854301cfe72d8543004fd72d854301cfc72d8543126f451d8543126f641d8543126f631d8543004ff70d854300cfe70d8543004fd70d854300cfc70d8543126f4615854302cff755944302e7f7559443034fe7459443034fc74594430367e54594430367c545944302cfe735944302cfc735944302e7e535944302e7c5359443004ff725944301cfe725944301cfc72594430067e52594430067c5259443004ff7159443014fe7159443014fc7159443004ff705944300cfe7059443004fd705944300cfc70594430067f50594430067d505944302f9f7650c4302d9f7650c430069f7650c430079f7550c430079e7550c430079d7550c430079c7550c4302f9f6550c4302f9e6550c4302f9d6550c4302f9c6550c430079f7250c432ef9e7250c430079d7250c432ef9c7250c4302f9f6250c4302f9e6250c4302f9d6250c4302f9c6250c432ef9e5250c432ef9c5250c430079f7150c432e79e7150c430079d7150c432e79c7150c4302f9f6150c4302f9e6150c4302f9d6150c4302f9c6150c432e79e5150c432e79c5150c432ef9f2150c432e79e2150c432e79c2150c432d79f7050c432d79e7050c432d79d7050c432d79c7050c4302f9f6050c4302e9f6050c4302f9e6050c4302f9d6050c432de9d6050c4302f9c6050c432d79f5050c432d79e5050c432d79d5050c432d79c5050c432d79f2050c432d79e2050c432d79d2050c432d79c2050c432d79f1050c432d79e1050c432d79d1050c432d79c1050c43004ff755884303cfc755884302cff725884302eef7258843116ec5258843036ef4258843036ec425884302eef325884302eec3258843004ff7158843014fe7158843014fc7158843116ef2158843004ff705884300cfe7058843004fd705884300cfc7058843116ef2058843006ed2058843004ff755844303cfc7558443004ff725844301cfe725844301cfc725844302cff715844302ef77158443036f74158443036f4415844302ef7315844302ef43158443004ff705844300cfe7058443004fd705844300cfc705844310ef71058443006f5105844301cfc755935203ebf745935203ebf545935203ebc5459352004ff735935202cfc73593521ee7e525935203e7c52593521eebf4259352004ff7159352014fe7159352014fc7159352004ff705
  | 15 => 0xe42596432767c425964302e7f325964302e7e325964302e7d325964302e7c32596430067f71596430067e71596430067d71596430067c71596432767f41596430067e41596432767c415964302e7f315964302e7e315964302e7d315964302e7c31596430067f21596430067e21596430067c21596430067f70596430067e70596430067d70596430067c70596432767f40596430067e40596430067d40596432767c405964302e7f305964302e7e305964302e7d305964302e7c30596430067f20596430067e20596430067d20596430067c20596430067f10596430067e10596430067d10596430067c105964303e7e65d52430067d65d52430373e54d524302dde73d5243005dd73d524303cff765524303e7e65552430067d6555243005df735524302ddc73552430379f4355243004ff7558a4303cfc7558a4302cfc7358a4302eef7258a43146ee4258a4302eef3258a4302eec3258a43004ff7158a43014fe7158a43014fc7158a43006ee2158a43146ec2158a43004ff7058a4300cfe7058a43004fd7058a4300cfc7058a43146ef2058a43006ed2058a43004ff755864303cfc755864302cfc7358643004ff725864301cfe725864301cfc725864302ef7715864313ef6415864302ef7315864302ef43158643006f7215864313ef42158643004ff705864300cfe7058643004fd705864300cfc705864313ef71058643006f5105864303cfe76d954301cfe72d9543004fd72d954301cfc72d9543014fe71d9543004fd71d9543014fc71d9543004ff70d954300cfe70d9543004fd70d954300cfc70d95430067f6599543005ef725954312dec7259543005f77159543125f47159543005fb705954311df870595430067f7559543004ff7459543006bf74595432767e54595432767c5459543004ff7359543006df73595432667e53595432667c5359543004ff7259543006ef7259543004ef725954301cfe725954301cfc7259543006ec725954301cec72595430067e52595430067c5259543004ff7159543006f77159543004f77159543014fe7159543014fc7159543006f47159543014f47159543004ff7059543006fb7059543004fb705954300cfe7059543004fd705954300cfc7059543006f8705954300cf870595430067f50595430067d5059543004fe761954303e7e65195430067d651954302cfe76d514302cfc76d51430067f65d514303e7c65d51430373e54d514302dde73d5143005dd73d51430379c43d514302cfc76551430067f655514303e7c6555143005df735514302ddc73551430379c4355143034fe76d4d43034fc76d4d430067f65d4d4303e7c65d4d43035be74d4d43005bd74d4d4302f5e53d4d4302f9c43d4d4303cff7654d43004fd7654d43034fc7654d430067f6554d4303e7c6554d43005bf7454d43
  | 16 => 0x97430367c41597432667f31597430067e31597432667c31597430067f21597430067e21597430067c21597430067f70597430067e70597430067d70597430067c70597430367f40597430367e40597430367d40597430367c40597432667f30597430067e30597430067d30597432667c30597430067f20597430067e20597430067d20597430067c20597430067f10597430067e10597430067d10597430067c105974303e7e65d4f430067d65d4f43035be74d4f43005bd74d4f4302f5e53d4f4303cff7654f4303e7e6554f430067d6554f43005bf7454f43035bc7454f4302f9e4354f43004ff7558b4303cfc7558b4302cfc7458b43036ef7258b43036ef4258b43036ec4258b4315eee3258b43004ff7158b43014fe7158b43014fc7158b43006ee2158b4315eec2158b43004ff7058b4300cfe7058b43004fd7058b4300cfc7058b4315eef2058b43006ed2058b43004ff755874303cfc755874302cfc7458743004ff725874301cfe725874301cfc7258743036f77158743036f74158743036f44158743156f63158743006f72158743156f42158743004ff705874300cfe7058743004fd705874300cfc7058743156f71058743006f5105874303e7f749964303e7e749964303e7d749964303e7c749964302e7f739964302e7e739964302e7d739964302e7c739964302e7f439964302e7e439964302e7d439964302e7c439964303e7f729964303e7e729964303e7d729964303e7c729964327e7f42996430067e429964327e7c429964302e7f329964302e7e329964302e7d329964302e7c329964303e7f719964303e7e719964303e7d719964303e7c719964327e7f41996430067e419964327e7c419964302e7f319964302e7e319964302e7d319964302e7c31996430067f21996430067e21996430067c219964303e7f709964303e7e709964303e7d709964303e7c709964327e7f40996430067e40996430067d409964327e7c409964302e7f309964302e7e309964302e7d309964302e7c30996430067f20996430067e20996430067d20996430067c20996430067f10996430067e10996430067d10996430067c109964302e7f755964302cfc735964302e7e535964302e7c5359643004ff725964301cfe725964301cfc72596430067e52596430067c5259643004ff7159643014fe7159643014fc71596430067e51596430067c5159643004ff705964300cfe7059643004fd705964300cfc70596430067f50596430067e50596430067d50596430067c50596430067f74596432767e74596430067d74596432767c745964302e7f735964302e7e735964302e7d735964302e7c735964302e7f435964302e7e435964302e7d435964302e7c43596430067f72596430067e72596430067d72596430067c72596432767f42596430067
  | 17 => 0x1cfc7259053004ff7159053014fe7159053014fc7159053004ff705905300cfe7059053004fd705905300cfc7059053006bf4059053006bd405905303d7f76550530067f76550530047f765505303d7f745505303f3f74550530367e64550530367c64550532657f73550532667e635505303f5e63550531ee7e625505303e7c625505303e7f60550532f67d6055053004ff7458853034fc745885302cff725885302eef725885303eef525885303eec525885302eef325885302eec3258853004ff7158853014fe7158853014fc7158853004ff705885300cfe7058853004fd705885300cfc7058853176ef2058853006ed2058853004ff7458453034fc745845303e7f54584530067d545845302e7f535845302e7d5358453004ff725845301cfe725845301cfc725845302cff715845302ef7715845303ef7515845303ef4515845302ef7315845302ef43158453004ff705845300cfe7058453004fd705845300cfc705845316ef71058453006f510584530367f74997430367e74997430367d74997430367c749974303e7f739974303e7e739974303e7d739974303e7c73997430367f43997430367e43997430367d43997430367c439974303e7f729974303e7e729974303e7d729974303e7c72997430367f42997430367e42997430367d42997430367c429974326e7f32997430067e329974326e7c329974303e7f719974303e7e719974303e7d719974303e7c71997430367f41997430367e41997430367d41997430367c419974326e7f31997430067e319974326e7c31997430067f21997430067e21997430067c219974303e7f709974303e7e709974303e7d709974303e7c70997430367f40997430367e40997430367d40997430367c409974326e7f30997430067e30997430067d309974326e7c30997430067f20997430067e20997430067d20997430067c20997430067f10997430067e10997430067d10997430067c10997430367f755974302cfc74597430367e54597430367c5459743004ff725974301cfe725974301cfc72597430067e52597430067c5259743004ff7159743014fe7159743014fc71597430067e51597430067c5159743004ff705974300cfe7059743004fd705974300cfc70597430067f50597430067e50597430067d50597430067c50597430367f74597430367e74597430367d74597430367c74597430067f73597432667e73597430067d73597432667c73597430367f43597430367e43597430367d43597430367c43597430067f72597430067e72597430067d72597430067c72597430367f42597430367e42597430367d42597430367c42597432667f32597430067e32597432667c32597430067f71597430067e71597430067d71597430067c71597430367f41597430367e41597430367d415
  | 18 => 0xc20d4e5330f5f10d4e5330f5e10d4e5330f5d10d4e5330f5c10d4e53004ff7458a53034fc7458a5302cfc7358a5302eef7258a531a6ee5258a531a6ee4258a5302eef3258a5302eec3258a53004ff7158a53014fe7158a53014fc7158a53006ee2158a531a6ec2158a53004ff7058a5300cfe7058a53004fd7058a5300cfc7058a531a6ef2058a53006ed2058a53004ff7458653034fc74586530067f54586530067d545865302cfc735865302e7f535865302e7d5358653004ff725865301cfe725865301cfc725865302ef7715865319ef6515865302ef7315865302ef43158653004ff705865300cfe7058653004fd705865300cfc705865319ef71058653006f5105865326e7e53d915326e7c53d915301cfe72d9153004fd72d915301cfc72d91530067e52d91530067c52d9153014fe71d9153004fd71d9153014fc71d9153004ff70d915300cfe70d9153004fd70d915300cfc70d91530067f50d91530067d50d9153006bf6499153005ef725915318dec7259153005f77159153185f47159153005fb705915317df87059153036be6419153006bd641915302cfe7695153006bf6495153036bc649515303f3f549515302dde7395153005dd739515302c7e769515303d7e74951532767f64951530073f64951530063f64951532773c649515302d7e73951532775e73951532775d739515302d7c739515303e7f639515303f5f639515318d7e729515318d7c72951530057d71951532757f70951533057d709515302cfc7655153006bf6455153036bc6455153005df735515302ddc73551530057e761515303e7e76151530047e76151532757e741515303f3e74151532767f641515302d7e731515302d7c731515303e7f631515303f5f631515318d7e721515303d7c72151530057d711515303d7f70151532fd7d701515301cfe76d895303d7e75d895318eee62d895318f6e52d895302cfd75d895302c7d75d8953034fe74d8953004fd74d895303cfd73d895318e7e52d895318eee52d895318e6e52d895318e7c52d895318eec42d895318eee32d8953014fe71d8953004fd71d8953014fc71d8953006ee21d895318eec21d8953004ff70d895300cfe70d8953004fd70d895300cfc70d895318eef20d8953006ed20d895318eec6258953005f77158953185f47158953014fe76d8553186f661d855302cfd75d8553034fe74d8553004fd74d855303cfd73d855301cfe72d8553004fd72d855301cfc72d8553186f651d8553186f441d8553186f631d8553006f721d8553186f421d8553004ff70d855300cfe70d8553004fd70d855300cfc70d8553186f710d8553006f510d8553005ef725855318dec7258553186f4615855302ebf745905303ebf545905303ebc545905302ebe435905302ebc4359053004ff725905301cfe7259053
  | 19 => 0x935303e7c545935303ebc54593532667e535935303e7c5359353004ff725935301cfe725935301cfc72593530067e525935303e7c5259353004ff7159353014fe7159353014fc715935303e7f5159353004ff705935300cfe7059353004fd705935300cfc705935303e7f50593530067d5059353006be4059353006bc405935303d7d769535327e7d769535303f3e749535303e7f649535327e7d649535302d7e739535302d7c73953531bd7e72953531bd7c72953530057d719535327d7f70953533357d709535302cfc7558b5302c7c7558b53004ff7458b53034fc7458b5303eef7258b5303eef5258b531be7e5258b5303e7c5258b5303eec5258b531beee3258b53004ff7158b53014fe7158b53014fc7158b53004ff7058b5300cfe7058b53004fd7058b5300cfc7058b5302cfc7558753004ff7458753034fc7458753004ff725875301cfe725875301cfc725875303ef7715875303ef7515875303ef451587531b6f63158753004ff705875300cfe7058753004fd705875300cfc705875302ebf745925302cfc735925302ebe435925302ebc4359253004ff725925301cfe725925301cfc7259253004ff7159253014fe7159253014fc7159253006be4159253006bc4159253004ff705925300cfe7059253004fd705925300cfc7059253006bf4059253006bd405925326d7d76d525303e7d76d52530367e64d52530367c64d525303d7f73d525326d7d73d525303f5e63d525321e7e62d525321e7c62d525326e7f60d525332e7d60d5253036be6495253006bd649525303f3f549525302dde7395253005dd739525303f5f5395253034ff7655253036be6455253006bd6455253005df735525302ddc735525303f5f53552530347f765525303d7f745525303f3f74552530367e64552532673e64552532673d64552530367c64552532657f73552530075f73552530055f73552532675c735525303e7e63552531ee7e62552531ee7c62552532667f60552533267d605525302f5d76d4e5302d5d76d4e5303e5d76d4e5303f5f74d4e5303f5e74d4e5303f5d74d4e5303f5c74d4e5302f5f64d4e5302f5e64d4e5302f5d64d4e5302f5c64d4e5303f5f72d4e5303f5e72d4e5303f5d72d4e5303f5c72d4e5302f5f62d4e5302f5e62d4e5302f5d62d4e5302f5c62d4e5331f5e42d4e5331f5c42d4e5303f5f71d4e5303f5e71d4e5303f5d71d4e5303f5c71d4e5302f5f61d4e5302f5e61d4e5302f5d61d4e5302f5c61d4e533175e41d4e533175c41d4e5331f5f21d4e533175e21d4e533175c21d4e5303f5f70d4e5303f5e70d4e5303f5d70d4e5303f5c70d4e5302f5f60d4e5302f5e60d4e5302f5d60d4e5302f5c60d4e5330f5f40d4e5330f5e40d4e5330f5d40d4e5330f5c40d4e5330f5f20d4e5330f5e20d4e5330f5d20d4e5330f5
  | 20 => 0x4ff7358a5402cfc7358a54036ef7258a54206ee5258a54036ef4258a54036ec4258a54206ee3258a54004ff7158a54014fe7158a54014fc7158a54006ee2158a54206ec2158a54004ff7058a5400cfe7058a54004fd7058a5400cfc7058a54206ef2058a54006ed2058a54034fc74586540367f54586540367d5458654004ff735865402cfc7358654004ff725865401cfe725865401cfc7258654036f771586541fef65158654036f74158654036f44158654004ff705865400cfe7058654004fd705865400cfc70586541fef71058654006f5105865427e7e54d8d5427e7c54d8d5401cfe72d8d54004fd72d8d5401cfc72d8d540067e52d8d540067c52d8d54014fe71d8d54004fd71d8d54014fc71d8d54004ff70d8d5400cfe70d8d54004fd70d8d5400cfc70d8d540067f50d8d540067d50d8d54006df6398d54005ef7258d541edec7258d54005f77158d541e5f47158d54005fb7058d541ddf87058d5402ede6318d54006dd6318d5401cfe76d895403d7e75d89541eeee62d89541ef6e52d8954034fd75d89540347d75d895403cfd74d895402cfe73d8954004fd73d89541ee7e52d89541eeee52d89541ee6e52d89541ee7c52d89541eeee42d89541eeec32d8954014fe71d8954004fd71d8954014fc71d8954006ee21d89541eeec21d8954004ff70d895400cfe70d8954004fd70d895400cfc70d89541eeef20d8954006ed20d89541eeec6258954005f771589541e5f47158954014fe76d85541e6f661d8554034fd75d855403cfd74d855402cfe73d8554004fd73d855401cfe72d8554004fd72d855401cfc72d85541e6f651d85541e6f641d85541e6f431d8554006f721d85541e6f421d8554004ff70d855400cfe70d8554004fd70d855400cfc70d85541e6f710d8554006f510d8554005ef72585541edec72585541e6f46158554036df7358c5403edf5358c5403edc5358c54036df4358c54036dc4358c54004ff7258c5401cfe7258c5401cfc7258c54004ff7158c54014fe7158c54014fc7158c54004ff7058c5400cfe7058c54004fd7058c5400cfc7058c54006df3058c54006dd3058c54004ff735885402cfc7358854034ff7258854036ef725885403eef525885403eec5258854036ef4258854036ec4258854004ff7158854014fe7158854014fc7158854004ff705885400cfe7058854004fd705885400cfc70588541d6ef2058854006ed20588540367f54584540367d5458454004ff735845402cfc735845403e7f5358454004ff725845401cfe725845401cfc7258454034ff7158454036f7715845403ef7515845403ef45158454036f74158454036f44158454004ff705845400cfe7058454004fd705845400cfc70584541cef71058454006f5105845402cfc755935302c7c755935303ebf745935303ebf545
  | 21 => 0x208011907020103010f05070207001003000012090504020002060226000416011208010505000a0f00020301032707170200010106000e0321000c00090000000207041306040000010001000106070002010a010800000300030500000001000500020a04060234010301050320450304060000040204070307012a081404050e000001090d090528000002080c07002a170f0203021002021b1308051803060503000002000b0007030403000100000003000800a503000a060a05010000070302090109000800000f090c140415100b1501000109140004020802590209000001070003040e1e00030003030c03150900060d0b0f0f0200034fc7558f540347c7558f542767e5458f5403e7c5458f5403edf7358f5403edf5358f5403e7c5358f5403edc5358f54004ff7258f5401cfe7258f5401cfc7258f540067e5258f5403e7c5258f54004ff7158f54014fe7158f54014fc7158f5403e7f5158f54004ff7058f5400cfe7058f54004fd7058f5400cfc7058f5403e7f5058f540067d5058f54006de3058f54006dc3058f54034fc7558b540347c7558b54004ff7358b5402cfc7358b5403eef7258b5403eef5258b5421e7e5258b5403e7c5258b5403eec5258b5421eee4258b54004ff7158b54014fe7158b54014fc7158b54004ff7058b5400cfe7058b54004fd7058b5400cfc7058b54034fc7558754004ff735875402cfc7358754004ff725875401cfe725875401cfc725875403ef7715875403ef7515875403ef45158754216f64158754004ff705875400cfe7058754004fd705875400cfc70587540373d76d52540353d76d525403e3d76d525403f3f73d525403f3e73d525403f3d73d525403f3c73d52540373f63d52540373e63d52540373d63d52540373c63d525403f3f72d525403f3e72d525403f3d72d525403f3c72d52540373f62d52540373e62d52540373d62d52540373c62d525434f3e32d525434f3c32d525403f3f71d525403f3e71d525403f3d71d525403f3c71d52540373f61d52540373e61d52540373d61d52540373c61d52543473e31d52543473c31d525434f3f21d52543473e21d52543473c21d525403f3f70d525403f3e70d525403f3d70d525403f3c70d52540373f60d52540373e60d52540373d60d52540373c60d525433f3f30d525433f3e30d525433f3d30d525433f3c30d525433f3f20d525433f3e20d525433f3d20d525433f3c20d525433f3f10d525433f3e10d525433f3d10d525433f3c10d5254034fc7458e54036df7358e54036df4358e54036dc4358e54004ff7258e5401cfe7258e5401cfc7258e54004ff7158e54014fe7158e54014fc7158e54006de3158e54006dc3158e54004ff7058e5400cfe7058e54004fd7058e5400cfc7058e54006df3058e54006dd3058e54034fc7458a54
  | 22 => 0x78a5fcdf25970000001ca00006f3000025843337b8001126d14457ac51372d2700011f544c00010302050000051102010b02041501000d01080500030600031e03160105150404000b070100070b090001050613b1000f0200031b02030401020900051800000308141800140200010007200517002100030f0200050501010100000f00021100092e02001c060300040012100004020518010203190203010501060300000100030a070001040003050f01050002041c00020703001100000300010211000100010204000207000102011a00030000000a0100000000030304252b041c010300000101030a021c030e000002130b03000c02001001070b080504020905080501010e080001080b0003082102000c01130106000202001702000012010008000a00090101010000000303020903060305050303030000080507071200040205090c040002000e03000b040c01010003060800030903010001420900040100010004030208050804080000002a030200043802220c010000000101200a03100204000b00010400070e0c0d050000010520070532010d0407010301010104000106070a031f011203100407010b01080101000003100616000f020001130000010001090000010017040002040000010400060103001e140303110505010000000901040007060303060f080003090c080b040401000204060e0001000201090e00001a1104041708070200000600090205010e051500110500060201000106010b0415050d120e0c02160a05060808000501111518040300040a020800060c0b000d0a0100041a031c1a02040028160403000405020c000111001503100000000003010205020c17040a0c010101270001010c030903120e0a040000020200010005010f04000e1010000d1300040202001e0a0100001a0004090403010d05020b01010001010018050100020000000100260307021405080304000000000409080b06040004020009020601002a0b2e0c040704050d10060523030600071400100a04090e0000040403032005020905090509020000080f0003090318001426080902031904000105030b0500000004040103000000000100000206090a0302000900020506150006000002000104000117080401000a030011171300200d020522020c030200000000072b02000001010c0c070315360400060a000001000706052600080110150708061700000105010e0002020001150e000012030200190803140110010100000102000004000b002f02000d0608090200010b0e0304000e0110160500070002000c010012010002060801000200010703020300020003020100000c0500000700040301040107070003020202000601100c010500050004000005001501000e0002030a00020016002000013810060200
  | 23 => 0x53a4262d200019c06535248001a7215f08b1188bde0bb0001871bc22090001f609aed5373280008a4c1b3db0000214ada1759a481ac8623fda1e800000000010251f45f30001450c661b22e4266db222bd47e9e882963ac0cd9c847ca2ce71826d8000dec2e5af5000000000000000004ad71a387039e6f0000000000000000025d91b0d690001579340000000014560aa300002240e064414de399ce5c3251ae2ea411c0d0510354133a1375e22374f8e93d0002cf8000b6829e80000000000000555cda0005679fa4064bef3e3129800064e1530270e7ea611e60ca0ccc84228708e1670d886ac0c45348e700f200004929f9310b778000000000071c9b246e528327908ed4f57f15e4094322339909d7589a51b1b5d0ff232305e800055679752d389d97800069e1eac0000000001cbdce64980d081fd830000000000000000000009f1738e016caa68d51e45333b09b8000377000000158e7f403c00005ce00028c80000000000000ed80bea0b53d000000000000038ec5ca43900032c40004e2140060dcae00000000000000001058f7dae476668b843dc1a99a0002f94e20d1a035b32451c8596f411fd93254531a2fd45e6778484a8e87d05041ef39dcf7e6841a8045c456da64dd0754b8aa7748125b020200013ba9d937a1bd54f8a8410c4736b3b2d0f1e294025a7bd59407213fa2b8a1e3f507508b885ab940233774f120005052f7c13cbc3317acac55a5f7127a989b8e0000f300000000003ada964000d202239b497c000030eb5cd95600000039bd21a47a4a73351506dc24c50f3974097e6b502746eade5695a6ddb1e88700024652be2a36bb281839c01a5f200619bc0f23482a88ca22d345c94ac8be46157e05d44e6bb1000255403c0001051ff88928e36c58000000b0755db274d6686400034e0d2cc29393062d2f6d7b0e801810cc35b5a9207401273203e25c98de0761cfb744de41ea12a2ddc8987a864829a999c5e651b2bc088639b518a728e2e5fe0451b8c1a263955f0001090d0c00033185601e92ea86dc0005220f78984eb0497000080c0005011f7056c0006a60000ef0f54e710001e340002ac43e000053e6c605530dd0f2da23a200009ea73d56e338d49092355a80002ce6bc4318df0c12d262aa0bd875a3b755985fc130ad93228dd8fcc1a66fc0000eca00001eb09891e0006272d1d8dca3c6820948c868c66cca76c0003954140cf520202759eb8d8b383411e3000047a00048282c42f4000000037c0000006bc97b1bdccca1c32a456125096032a50a902536c72fd80244a0381000158c2955040000574aaa644b3d5a1631300000006c000026b03b0f82a1d0000c90000746000000032a69102b800000000000008d00001ca000136d03eb78000183849c1880b400000001c8196a91c3e20003cd369519c76d2
  | 24 => 0x293b9640000000a6a5ac688e2100000000000000001db935ca1e2b000018182966629b24e167700cfa37946e7be3c2216963c7f31c78000de6cc00bb9688000000000000176a02964516d4846063393b248392c1264402e043ebdb2922b7506657663a92e4aba87d369a104cc6e2c472a5948702d0344a010c4a6a8668242d2743a6676004ca6283d188260400011d20eb125a2c3c328f0b583ea88a0690f4d774000012aba57e210d5158d249e0e38673a94cf6e7b3000001922e2e82fd8040d44c7d0580860000b6f44d88a0000000000097c0000e924a0b89afc49f21f181400034247b9e183da156271b3e125c0c34172be80003fd62e0070a6e81007eb23c0000642d91cb5aa80210003418000706000000181655c000301c000c4d62c0000000b370000ffcc340005c580000000006960fac00000011b23d0994b85000000000065b0000fdc382c7419b0f70000d905b98001160c0443886e9a208c72f52c9000018400035b15d472523a80000002000001ab9cc400000030840009c30002a9480ca2722d1f2577cde40d1a2d80000000000e9c69ea8c42733680000003cd800097e83e0002cb516600000000000000006638000ad8e4500000b473ce2b1b49c297fa92b1d59f0000000006a2d10aee0833ab8000000cea32a9dc989ea6900f8a640504741e1002d04405c30c0e096822a95663108b7000052c1a380000000001c6da76cb7000000081a13a3cb18f8cc400068780009883487129704e1ae796be1ab45f4cac07d800000030c48f8b102a47942a386b541e000038a78952e4850000c38000b8637437c42322a870b073000013400015d1b8a3f167786a18825b40801900d9ed47000024810e5c952a800140a85e0000630bc69570d28c29c8464a5891f44b7a077439a2f4d3e2577042430b3c000000000973e50a6dd8d84ef6aa34a520657f255519a33dd01a0003a0ab34e1849b0000c087c80002c72474184e2f6e480000008922ac95fd4584370002b4cff85dc446001d7e83a41aca14cb22b985b8abb55f688f24811c9aca0002250cac8ee0004c72bbdcba00073d2df0eea0004748719cecd5a3ce999089065236d336da50da94502d3c5aa0000003539bf492506508a9132000262b888f3200051724ec00000041831a8000aff6161dd00004362a80bf0d6e4dc18b80014cc364000000143400000029b800084a000137c0000001030000d7400062aa6359984a70980000000ceb6968b1c00000064d800096a7910000000710ca82a3188d2b0e7801e1734c6c3f20000000ef82c36ffab2424e5f26e6033182018d58e066137c1b01fa2e3947666f499059957e0001f68b340008a20ce9d681048e85e09ce80009b142aa060b607c80000000000b0128f8000298c3c3bc8f847b400002c80002400e7643800018e8ba2522a84
  | 25 => 0xd042c952061da18e280339887b85fea794f839d41880945f69b719e85d9456b788d880f6022b7708ba834316120c226bc226a94ec0180001d0378c0002310170000a4637a1e93489b025ff00018ad6c6d8d31a9344040a0d2319f3447c69c02e8154e22c35642a2b017438513c9d8445825133284c40000000001d0c0000007318000242c6365f0e25828ae316e800142600000000000000000000000000000123000000056e40405780000006532524000e5e00000013420000bc94b467800036b932043284f0000000000b871c9adb12a842b29e2ff950e4f9616b5c06b0ab13f50409c3a000120b86844e1e23942cbcb6cbbb10821acd3478c1d12bc94e48ff2d188c0000869000000072200055ba400fdc0000000000acc00000022240001fc000000000001b00021355d00002c4a11007205a2b480000008f600006ed056c081b980000007bd000230c0000002128db5482e33479b6dc0006e659d80007aa0e413400000dc5855d680004440000930001102d89430243800060f39b0e655c298f2548000000e06201800192835726d00000000d95aa0000d2e63d0001cf0974ba2000078c5b6e4f5ab9bd4000b3536537f5b360f30000da800006612b3384fc09cc0918000000dfc51c25a17dc00000026d4a840000c838f8d7254341b000089e0c037db7618041324f1aea16cea1c1078c50480d7a03f2d812ee2a22dfa7385262331608240d185562f8aefc30e96056bb2c03bc35d3210e41c908845531ed4b269a64f021dd504c3871433207084d86461b60d848ab46591b4388817000237d35a11b1a0272d6b200055712118740c800034082c2ac24a22cc400071c4dc3951a1478234cb5bcc160e14d59aa99a49d54be88502ecc612b99ad98fe5ad5ad8000476c8e000112c00080900029316d265019d800000028a0001f4ca70a9c1c0b7ad806bd327795a17b058002d85a9080c1732fb524000c9a0000ce163e00018e8ea020819e21e35e05842b80001dfc714dad66a9108fdee044a3a47864e3bb3ea0ad80005ee0e99b913ae00011aad0849aaaf1fd23b8cb000015a27fdb2e8140a38ac4000000355ac38b342b74c39ba4d8280604786cc90c39418682d80028ca18e0dec3ee429729a9f4b3241530814c16c84ac4f20000fd65db5d730752da0a61a3a130a0a6543be9f8c4c0e4641ab7c010222d1391fb000025d20815d4000c591e8995903cb0f01a2cb800000030500010bea4b3fd38280007180860000780d050001dac0009e638280015200000002a18c4ecf114b953017c4050a415f0b2a60100000000006e027d16e929842163400000000006aeb9312b800050b8001c2e2651c00000cc2a786e599a0134000000101c63c0000001b9c48e9530a331b01f21dc5e3a7b8802896692335d2d4e3a4a1a58865eaf64f5ae3c42c171
  | 26 => 0x4274303dac82866818c19ba40004f909f45169f100032fd872050000071578a78b576130ca9ccff0000001b56b495c119300ce3ba0e8a661ca292a00006b80009b32e01d597ee1d613da29cd604dd2d4a655a2ad931368000000742000064994a3e646a244884034e6af079c9ecb20399838c9962983aca2a4000c363f80524000ce949494f94f882642886f10169c265d0998334000000397c3385c456423f8e2ce1400037414ea46852a281061217d2728000bc8c7e018b7cc40e7a05d20df5778ce22058ea800000000012941660910cb9608a2cc3d594249088ac334ab256c2280000002cfc000000484383921eb7200029100000006cb000083e4aa5f50394f607835f831480004e9532b01402e43f000370000000000000000000004418000af62bf0002e6841a86c63d3460dcaa23560357d1ced590000000b7c769448995d2442215f33580642275333a3e18683073aa1bf1b40e2455c142d72a0da24690c408450c0292678ec43fb4f60ba82122326dc147187e0000002e2116e02c50c80008d4d190000001b9077e4978000000c1e55e00000004f73a494940006f854003a0000e0b57c0001130da448d1d1d1a00000c09abc698000050090ca74946000000077261270789912cc00063c9e21ce849e3c8270462a60c2c831cc06a00059500007bac2445a1225c9ccd9422b9ac2d8301345b514e48a8d5e400000004e150c027c50a6db197241c934ba52113685c367b26f6aa280004c00000000e7c0006988000000290005000000069300003b9be8000527aff0000878164000000000000003e8ebeafd51eae24e00000000370d6fe00000018fd3068d61ce0908cd236f0ae25208b0cb322b2ae8000000000262c000ad850a23f00000001660ff024400000420ec00086f47126c16ba5100002a54288c7b0000e5c404000537b7d89d60004f289140002e30002e6c0000006dd000000000009200000000000000000b085ab034800000000036814b80003c93eb30692a4b5a0001d4837cc3b06485000000002b09b342f6dc12a08000000c3e0003660a1a9340970d440009e109b2d359fa51546795340000000001ad5238000042396c2da00009e919d9b8ab614f2d14b404e05629888356e230002710512b586da92bd494b3353587ad77282554c2314d4882f3fb347c00014a09529cd34e1500000ea400000000028f866650206789a800000000000015c4b510ea325955a0004070000766000045a71535ebda00000000709361b600000f623f5cbb8fd0e800061786d4fb6d6b56a13d18bec8b5b100003b400000008154be00000001942fc02400000000005530002ec042ad4235880016060003a688958a2bd11a3367d95c0493848b8000023a39d8de400000000025b87162816103751aaa196327813035e8b55ba1d409149c06ff1c4
  | 27 => 0x2056471f00a0c140000006138e39cf874833a104991a1450be1b44cdaabd54d8f3d44276c000000145e0000002dec7d87ed0ee8bb00000000001ea45403b251900459860000002844dfc3c72c9279d6cc00016780006a472a6dc81b4c3c89e5f39190fc4d8704cad7d1d86de4d40b28ad68725f9928c0de2786498bc911c51816c0bbccc0856720b1dd4c80ac57716951aedcd07baae4c786ef4e3b7541e896420109b0d687ca2b918ec1e002b0a99f1181a20e50709602baad262826fd39e8d5294981c576e61717176173240020215484b42f72f820dd9dc34363499200b006804019048fc8f22589445548a704b0b9341567015881b7d326a1f538a1508749de279b3ec8a27c5266b6d012a3542c621b53ba16045400013584542f38eb9680d852e1158d88e0d712da5a47c4df219fb4946b4d6e5ff9d28f2481558bb4e90b8000659000179ec5b3eba3b5c229d36c51ee99b045c4ed2334b8e40f52125348e243004ba0712de0dc00010d03e403e0c70000ce466e1d2a0c96041d26950001a3a000308aa4d2703195d58001724daf30c87e92602620f424e5058a460fa2c10ffabd74cb1aed856bc01edaa8139a8a30c5267c0c4a9e326858dc6a466414aa10222e4a4fea2c59c84c972ab09420ad5118d00003b62da3cf8d95938a6c20d00000001f6000268808833a1b92b81a7eb110df902913e76749f80006d67e74efa7248bc5444402dad2804cc60a9dcccf274033e236d5604ff654a1b80000004f4a26800000065780000007ce000000000061657c8001c3c000680064c608dc4000000086400017827614ae0007000be173ab3c00023c40007da00000003fc68200000000005a121e9468344da826117a4904e2a03ea9712f823733aaf75b94bcb000079544a0000001ca57f06786ca1b8800028d0001b1c2e4d9e1178bc42e66291cd174015cb7e31300002b29d21120b2400098c00000015640005e731ac000a091418000fba00000007c00000000a18de000086500000013904bb5bd15c000045b5a600010702e16eb1bd03229744750000dda00045f99700000a92400000000e0200031d800000060f9aa52b40001488cd58cccf917a140d6fa2d13dd97d4000a8b34a946d63a20c2d88cc182675e58b24a189603f01b047d814af303c9a0dc96cc127601c1a0ee071e2b6f400098528e80000000000b233f00000003a600008f20000001ef0000000000135096600018c246c1de0004bd1ac8000e0900694d4000b27000308c7e03cd2d392f8dec5966a431e000000051480000003f609280000000000000000000af100030c00740fe2608000760c702a51c88adec6520e00000000000001b1512eb5069a1f65b4668d410358c0009426d70ab91b4a036e326216320006e99634000000531800000067157b80000006ce4fa99ec0004e
  | 28 => 0x664af1e1c0005ca31717f4ac4b8443d9620c70e586c101847e6adb000265c0009dc27e80005fc00070c8f605d20ad0000235b9e0c50b782d41c0000361800000000000009e80000002ef000185c0005490780cfc48b44105949020eb08584384bc97559900009a046b00000000000005b508800000006740d54f5e3c400034b800000065a80000320b91de95f41460003352feda3c1ec208b2b400000000026006ce00073f23080005cf39ca7e00a89aa099800c00000044300019cc0000002460230bd038200015ccb480001fa164a0af2950000000bdc000156cdba00000000019fc0000002e356c2bb7050960d9e406c702a4b530c000544000140400069480000003370001bc4926a2a0fca2755a241e00000005f2a810000001672000000000000079c19f1b544e88574c200000f45aa0001f4877000000022ec0000000131ddc1dae6c1d180011c2730500a45802a6fa66e8b79a601aa14120f05b87f85e4b8540005d60000001a8000f411a7a93e81b61a99c1c00083f24eafb005e77a6089e7825ee6e63210d40ea0006a200019a21704c80001b0625047c8b5cc068fb000369d6587e500027f909290600034d80009315e93880fa000065c326000051242832ec0000f50001cd5944ba700024f000013e00000004e20003919b2c0000000001ab02841543e61974000614000122001c0000000000000d7d20b0d1400067d03a0000e32def0002b0c96cdb600000005a807324a9891138cc44758f8cd0e00000000ecd0a5b90002718000a156d604e0f4ecd6133a1a0252c1630417e0ebaccd6200a20a6800033faf8caf0000067314c4d6a24672a44c35885246e39ecce0d9d2831f0d78c0005e6285862cbe91da81006fe5d43a994bc90e000000000043c60029f80007300006eca1600004405eab5fc9327760000001862b226d880005c8b5e0000cb12a20000e6aca4bd60000002044000b1329ca504000000718af2949a507553b3d91929fb000000177ab5300017e496882a5bc8000000c84226970c4aaba16240001c5294b5d9296c0000000ef8000000000000000102c0001b70af0f7200000000000008d20000a10828921193072c000000185b33c1ba3006870000c6034d00000000006496d92d956e06376fa8d2c3860372e8a0158a80002542a38c5400000293f800042f69f0df911a174503800195499900000000003292231cdc380bb359b36f843a0000000000000b0c0000000000276227187ca9ed622698fa5cc00ff000000153430323e239972c2a5604a6085965202cfb3c1178b8c3752429ae25d7509161cbbec672d320698dac452a889bcaf4d4149395606bc8e016fb2190fcaab70f81203001860da2b780864fb310040d26ad9c06a80000007122f40294c042c64bc0001c300000b48000aaea0039c000000000058d82
  | 29 => 0x14e80004188000a6400010090a800054b51f80000008c00000fe183233200000c0000ca7237a00899e00000025c597ad6d34d8b99c78c603e11d8091c158248ad294fee101690c3d568ac45930f2db340b732c931c70e06a09fa9145f67f700016dc0002446501c8027855a4f998c9cd06a03d692ac5245002508bf4e9c4e63b19c7481c4f20002aa4d02ac10000615b087b43ca81349187800699a288b2d755fd353029cd1c4dd8e583124b01da162904e5ed08e383000089506f000097a0003e78868272af56a1add800085b12581593640000002e00bf4677352844010a67a49f2db80000001ba25e4000a103400000000a1b00000000006fd28b800133800020c88e4dfe0000000000000c286df800000000029991c000000025900000005210000000ace70800029a06cc000529390cffe0000001818636aeb00000890260000001731768c4400000015128c162d0f81116000585000000000034784554180003763209696460000363000012b000000077c0000000001c8800062610b8790a22011800000028c000380cabe00067d00007de6b8000000146a5860000075b540003c9a0280009f65199cb09bcd4a0001498d465bc000299c00058b21d800122a0006a900000000bf10430052ced0d499b179bc07b1269196855ebeb1b883e14bac4a4b9a9807060000001afc1b6b3435e8000dac0a84ae9e29a647715b6b2040004e75c980000006cc56fa1d4858d095aab4bcc9687f23d983409ead564f984d7200416ada41020e66b56711958f89a94688efd98421b15231c8944d1343381789da78109aa31033236808d2b958645ce2c7830400029a5908a9c51ec5d2d9a2f84522be5a3332d3681d9688aa581128466c90f5dc24615542875cd42424000185c00000000026440000005140ca8d804ea3871d91b00000000000000019436c97840000000000000580000000088c000000565b7a94dad68623352c000000134b6c000000000004a1bce0000000f416301080000001a6e4c660e27e98aee49641b5dc3f60cd0f98001a9a000000203c00000065b20e905a31f5ec9c3c82e2aa0002e0c7fcc971a50568d0c5e000015b4c08000000053da24a395c080003c20002ed25140009e838a855c7d4e4045300016ac7551d082c981c5a87348000000b9e12caf5800071a66f9d1492459b3640000000000000115c6248b20000a6c000b1a6c300017c299400002590960bc11e0bd56740002a0000122274b00000000000000000000000a4e73f8000196c565e6b9f4bca27e3c70001b9cd46190111095c0002d7a2e1cb8cd315a8e741183d4000275806600000027b526e00005121742247d5316986dac200034f0f28000b753231e14e288c819c98a1bee8a42899cd00007a35ef2048000ad00dcaa64362894000000100e4f857a0000340d
  | 30 => 0x43523900003313d08844e3cd3d6ebac5400021c4380001ce4b0b5f125405b20001ab1e98b301a94441dbd61a00037717180000006400001746ae736a2185646e3765c906174c0005f4014d7148f000035704242701d79a60feacf32840000000d084819fc5a6600000000003703d90270001ccc00000000008ec9d90b1391c6c437071c88107ac52c0000000be8000063000081000000003880000004122ebd76ca566ab933903618220980000008006002c200002ed00000000009f700039908a09d0000000096e801000297929e287528b9a80000934c4a10c00025c00037680007a400000000000003a7b77d8543924ac8accd101d8109b84dcb40473b51f90fe47b823c3958c8e8cc3ef3244ad446c0539eb020cbaa65204b566088549034d43fad011d891a4fbebb865097d82a2d1b52190a0282751690a498c7411e5ae1271bf22c5554092849838c5a180002d600071922a8b5c2261e096b0b3a0e632205b92e00fc184000000000045292f1aac0000d20000000a9d0000f9c00000000000004c60a42c0a8b4eb8aac00003600007a50000fe4000e5200000000000000001eb92c60000020000bc4de957223bc2f00b45f92e440006a709d9f85b7852849621d8a925fc34ea3d483624845098c56009fc27e00a8f30a7b000234cbbaad651a14d93a20006ed80018c400000026480000000fc2d39018ced25c00000000000000000384db332f0000b2800035f2c18000455691974dc5a2172b29bace567dc14e1590b761a7078a90000038d00020e400000046cb7ec0000002bf0000136e3d2e90bb9d001ff3e58058dc291034a0000cd800024b00018865710000001946c22000000000000000013b831e00053f0d7c572e2600000000009144ea0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa76810c065484014eb02180ca909d71be1d20195213a63643a4032a4248a6e8148065484914d902900ca909269be01201952124f35c024032a4273e671048065484e7cd420900ca909cf9a441201952100733c122032a4272e648244065484914ef00880ca909239ce011019521397339022032a4272e72204406548401cca40880ca909cb9c4811019521007309022032a420087f855cf644840f0f90ab9ec890802a760c40d912100556c1081b224200ab5811036448401dc240886c8909c71b5c865991210062fb2ce73224200c5c659ce64484018becab9cc8908031719573991210064fb22e73224206c9c645ce64484010fd0fb2ac8908021fa1c655912138637b90cab22426fc777119564484018d8ebb92c8908031d1d771591210043fc2ae0b22420787c855c1644840117f08b82c89080237e0d705912102c6e41ae0b2242008ef825c164484011ef02b82c8908063b21d205912135e363aa40b2242018f48744164484d58e8ea882c890803b848110591210045fc3ac8322420687c855db544840147b09b2ca8908021fe15765512100477c12ecaa242008f7815d9544840d0fd0fb2aa89081e1f21576151210043fc2ae9b1a420787c855d3634840153b08186c690802b360830d8d210056ac0861b1a4200ee12044363484dd8dae432cc6908030fd967498d210061e32ce931a4200c3f655d26348401878caba4c6908172718d7498d210064eba6c731a420087e87d9563484010fd0e32ac6909b71bdc86558d213663bb88cab1a4200c6c75dc963484031ed0fb8ac6908031d1d77158d210043fc2ae0b1a420787c855c1634840117f08b82c69081a2f2117058d210046fc1ae0b1a42008ef825c163484011ef02b82c6908063b21d2058d2135e363aa40b1a42018f48744163484d58e8ea882c690803b84811058d210046fc3ac631a420587c855db53484014bb07b2ca6908021fe157654d2100477c12eca9a42008f7815d9534840f0f90a3b2a6908161fa1f6554d212543fc2aec29a420787c855d853484010ff0abb6869081e1f21576d0d2102c5e422eda1a420087e869d743484010f90cbae86908021fe1f65d0d210043ec3ecba1a420787f8719743484010fb0e32e86908021fe157690d2103c3e42aed21a42058dc835da43484010fd0d3ac86908021f2197590d210043fc3ecb21a420087d87d96434840f0ff0e32c86908021f61c6590d2103c3f42eeca1a420087d85dd943484010ff0abb2869081e1f2157650d210047dc02eca1a42018f8805d9434840b17d0fb228690816a7a0f6450d210346f43ec6a1a4206a9e84d8d43484010ff0abb0869081e1f2157610d2124e37390ca21a4200c9e7650c434840b938eca18869080387d954310d210070e32a8621a42028ec865c843484018d8cab90869080a792057210d21
  | 1 => 0xf0ab82c59881e1f2157058b3100c7643a40b166200a6c8548162cc40b1df0eb16a5988029be1562d4b3121e37314eba1662058ef8758b42cc4018dceab16859881a3de1971d0b3100636b94a5b2a6200a6e82943654c4f18beebb9aca9880e3ba1f725953100637ba8e4b2a6200ce472dc5654c4010ff0ab82ca988022fe1170595310345e422e0b2a62008df835c1654c4011df04b82ca9880e3b20970595310043fc3aca32a6200a6c82594654c4010ff0ab96c89881e1f21572d91310054ec1881b226200ab581103644c4010ff0ab82c89881e1f21570591310045fc22e0b2262008df835c1644c4011df04b82c89880e3b209705913100c7a43a20b226201cf070441644c40117f0eb20c89881a1f21576d513100477c12edaa262038ec825db544c4051b90cb9ea8988023be09765513101c76412ecaa262008f7815d9544c4011f700bb2a8988063e20176551310343f43ecaaa26205a5c83d97534c40b53d07b22869881e1fa1770d89310043ec2ee1b126200ae581883624c401dc440886c4988031b188755893100536c2ec5a9262068ee87d89424c40b1ed0db8a849880339d8b715093100536c14a1b2a420187f87543654840147f08b06ca908028f21160d95210052fc1ac1b2a4200a5c8358365484954d90c906ca909271b9d920d95210073430241b2a424ba748644365484918ecec886ca908039c18110d9521007b090221b2a4200c3d741d365484018bae639eca9092e9ba0870d952125536c10e1b2a424aa76811c365484974eb02386ca908021fa1c40d95210043ec3881b2a4200a5e8310365484014bb06206ca9092e9ba0840d952100536c1081b2a424aa768110365484014eb02206ca908021fa1c30d95210043ec3861b2a4200a3e840c3654840147b08186ca9092e9ba0830d952100536c1061b2a424aa76810c365484014eb02186ca909df1bdd772595210043fc2ae0b2a42008bf845c1654840d17908b82ca9080237e0d705952102c6e41ae0b2a42008ef825c165484010ff0eb28ca909469be0965195210043ec3cc032a4273a6d8298065484e54eb03300ca908021fe1d60195210051fc22c032a4200a3c8458065484014bf06b00ca908029720d60195213b537c12c032a4248a6c864806548401cd6c0900ca909269d219101952124733b122032a4200e73604406548401ec240880ca909269ba0a401952100536c148032a4248a768190065484014eb03200ca9081e1fa1c40195210043ec388032a4200a5e8310065484014bb06200ca909269ba08401952100536c108032a4248a768110065484014eb02200ca909269ba0a301952100536c146032a4248a76818c065484014eb03180ca9081e1fa1c30195210043ec386032a4200a3e840c0654840147b08180ca909269ba08301952100536c106032a4248
  | 2 => 0x743d895100536c2e87b12a251a6e8590f62544014db0b21ec4a8803a350c43d895128d3742ee1b12a21fa6d85dc3625443f5cd03386c4a8802b960670d895100675b84e1b12a21f8ee8794362544011db0f286c4a887eb9a0650d895100572c0ca1b12a2008ee8710362544011db0e206c4a89469ba1440d895100536c2881b12a200ace83103625440159b06206c4a887eb9a0440d895100572c0881b12a2008ee870c362544011db0e186c4a89469ba1430d895100536c2861b12a200aae840c3625440155b08186c4a887eb9a0430d895100572c0861b12a2008ed8799062545034db0b320c4a8802b3a0e641895100566c1cc8312a2008ef8759062545014df0ab20c4a8802b9e05641895121d37428c8312a27fa6e86d5062544914dd0caa0c4a89229b219541895100717b22a8312a2008ed8798c62544fd4db0b318c4a8802aba12631895100556c24c6312a2008ef8758c62544fb4df0ab18c4a8802b9e0563189511bd37428c6312a27ca6e86d4c62544914dd0ca98c4a89229b219531895100727b1aa6312a2008ed8798062544f74db0b300c4a8802b9606601895100477c3ac0312a27aa6f85580625440155f08b00c4a8802ab211601895100567c1ac0312a200acc83580625443f9c8e3b12a4a881a1f21676d09510143e432eba12a23dc6c625d742544a38dcebb1684a88031b5d762d095102c3e42ced992a20287c865d732544638d8c4bae64a89471b9d762cc95100636baec5992a2038ec821d932544018dee5292cba08061f21d505974103c3f42ee4b1e820087d85dc963d04031b90e982c7a08161f21576d4f410346fc3ac7a9e8200a5f8558f53d040d93ce8b1ea7a080297e0d6594f4102c3ec2eeca9e824f87f8759453d04010ff0ab82c5a081e1f2157058b4100c7643a40b168200a6c8548162d040d1df0eb16a5a08029be1562d4b411be37314eb9968200c6e7558b32d04018dae5296caa08029ba0a50d95413ce1fbaee8b2a82038ee87dc965504018deea392caa0803391cb71595410043fc2ae0b2a82008bf845c165504011bf06b82caa08163720d705954100477c12e0b2a82038ec825c165504010ff0eb28caa08029b20965195410351e426cbaa2820087f855cb635040f0f90ab96c6a0802a761030d8d410056ac0861b1a82008df8758c635040b0f90abb6a6a08023be0976d4d4101c76412eda9a82028bc865d3535040f0fd0bb86c4a08021f61770d894100572c0c41b128200ee22044362504018d8c43aac4a08029b61762d494100673b16e29928200c6f7294965cc4030f90ea82cb9881e1fa1772593310043ec2ee4b2662018bc8750164cc40d0f90abb6a9988162fe1d64d53310051fc2ac9aa66205c9e7359354cc40b0ff0eb2ca9988028fe1165953310343ec2eecaa6624d87f8759454cc4010f
  | 3 => 0xaaa66400c6d65dc954cc8031e90e882c3990031d5c651d953200536c14a1b2a6400a7681943654c8018f2e1286ca9920b17dd773595320147b43ee2b2a6400c77751c5654c8019cee438aca990021fe1570595320045fc22e0b2a64068bc845c1654c8011ef02b82ca9900a3d20570595320043fc3aca32a6400a7481594654c80153b06206c899002ab60840d91320043fc2ae0b22640787c855c1644c80117f08b82c89900237e0d70591320047bc0ae0b2264028f4815c1644c8031d90e902c8990073a1c120591320045fc3ac8322640687c855db544c8011ef02bb6a89900a3d20576d513201c6e432e7aa264038dc865ce544c80b1d90cb94a8990023be0976551320047bc0aecaa264028f4815d9544c8011f700bb2a8990063e20176551320343f43ecaaa26400c6f65dc9534c8015cb05086c299003b848210d85320063a308eab0a640787e85dc964d440f87ee9bb2a9a89321f61b73553512662f31ee6aa6a20787e85dc963d440f8bee7bb2a7a893a1f61b7454f512761f326e8a9ea20687d855db43d440b0fb0abb487a880a1fa177650f51014ba40aeaa1ea20097585dc543d44eb0ff0ab82c5a880a1f2157058b5100e7938220b16a20687d855db42d44012eb0bb8a85a88161f61576ccb51004bac2ee2996a24a87f855cb645440147b0a206c8a8802a760c40d91510055ac0881b22a200c9f645ce645440d938c8b9cc8a88022fe1d641915126c3e432e7aa2a200c6c625cf54544018d8c5b9aa8a88039918b71551512543fc2ae5b1aa200a5d850c3635440153b08186c6a8802b560430d8d5102e4e31ae931aa200c9d74d8e635443f1d90db92c6a880237e1d6318d5127c3e432e9a9aa200c6c625d353544018d8c5ba2a6a88039918b7154d510343e42ceda1aa2058bc845db43544011df04bb686a880e3b20976d0d510143e432eba1aa200c6c625d7435440187aebb2686a88161f2167690d5102c6e41aed21aa2008ef825da43544071d904bb486a880a1f2197590d5100636312eb21aa200c5d75d8e43544071dd05bb286a88023b60b7650d510143e432eaa1aa200c6c625d543544052e902baa86a8816a7a0f6450d510354f426c6a1aa2008ef825d843544071d904bb086a880a1f2197510d5100636312ea21aa200c9e7650c435440b938eca1886a8977a31894310d5103c3f42ee1b12a20287d85dc362544031df0e906c4a88029be1520d895100e7538241b12a200ace83993625440159b07326c4a887e9b21954d89511ee373b2a9b12a200e2c64553625440155d0931ec4a8802ab61263d89510fd36432a7b12a231c6e7654f6254401c98c6a9ec4a8802abe1160d895100556422c1b12a200acf83583625440159906b06c4a887e9b61474d895128f17aa4a9b12a21fa6d851cf62544a3c9ea729ec4a89469ba1
  | 4 => 0x110c011df04b82c22180e3b209705844300c7a43a20b08860096d85dc943d48bbe1ca4a1887a90025be157210f5200e7538240b0ea485c3d75d92645480117f0eb20c8a90f71bd9772551524262ebaec731aa4008df8758c63548638decbb92a6a900e1f21975d0d5201c3e432eb21aa40087d85dd943548011ef02bb086a900a3d2057610d5200c7bc3a21b0aa401cf270443615480f0fd0e18ccba10021f61c319974203c3f4386132e840087d870c265d080d47d08184cba10028f610309974221d374106132e8400a6d820c265d08014ed02184cba10029d604309974200537c122132e8443a6c8244265d08874dd04084cba10029b60810997420343f43ca0b2e8400a6d8294165d08014ed03282cba10029d606505974200c3e43aa0b2e8406a3e849cd65d08018bee739acba10029be09735974200537c12e2b2e840087e870c565d08010fb0e18acba10f69ba0a705974200536c14e0b2e8400a76819c165d08014eb03382cba10021fa1c30597420043ec3860b2e8406a3e840c165d080147b08182cba10f69ba08305974200536c1060b2e8400a76810c165d08014eb02182cba10f69ba08105974200536c1020b2e84018dc874c163d080f87ccaba6a7a100297e0d6594f420061eb2ae929e843dc6c7259553d08018dacbb92a7a10063d21d10587420063ab8ca3b2a8400a6d8294365508014ed03286caa10031e5c250d954241e1fbaee8b2a84028f687dc565508018eeea38acaa100339dc871595420043fc2ae0b2a84008df835c1655080b1b906b82caa10023de0570595420147a40ae0b2a840087f8759465508014e902b28caa10031bd9772551420054ec2061b1a8400acd820c363508011bf0eb18c6a10161f21576d4d420047bc0aeda9a84028f4815db53508071790cba6a6a100e2f2197494d4200572c1421b0a8400ee12084361508018e8c23aac2a101e1fa1c41997320043ec388332e640787e8710265cc8010fb0e204cb9901697a0c40997320052ec188132e6437a6e8210265cc8014db04204cb990029da0440997320053ac088132e6400a6f8244265cc86f4d904884cb990de9ba08109973200536c102132e640587e8794165cc8014db05282cb990029da0650597320053ac0ca0b2e640187c8754165cc80187ee93a2cb9901697a0e745973200537c12e8b2e6400a6f825c565cc8010fd0e20acb990021f61c415973218d37414e0b2e6400a6d829c165cc8014ed03382cb990029d60670597320043f43880b2e640087d8710165cc80b4bd06202cb990029760c405973218d3741080b2e6400a6d8210165cc8014ed02202cb990029d604405973218d3741020b2e6400a6d8204165cc8031790ea02c99901f1799573d533202c3fc3acb2a66400a3f8459654cc8018bacab9ca9990161f21d655533218e36392c
  | 5 => 0x181e1f21d20996430053b4084132c8600a75810826590c0147f08884cb2193e8f2111099643005374102132c8600a6d820426590c0b4bd07292cb218031bdca525964302c3f43ca0b2c8600a6e829416590c014db05282cb218029da0650596430053ac0ca0b2c860187c875416590c014df04ba2cb218029b20974596430053bc0ae8b2c8600a74815d16590c014f700ba2cb218029e201745964302d2f41ce4b2c8600a5d839c96590c018dee5392cb2181697a0e42596430052ec1c84b2c8605a5c835c56590c014df04b8acb218029b209715964302d2f41c82b2c8600a5d839056590c0b4bd0610acb218029760c21596430053d40042b2c8600a79800856590c0b4bd07382cb218029760e705964300537414e0b2c8600a6d829c16590c014ed03382cb218029d60670596430052fc1a80b2c8605a5c835016590c010ff0e902cb218021f21d205964302d2f41840b2c8600a5d830816590c014ed02102cb218029d604205964302d2f41820b2c8600a5d830416590c014dd04082cb218029b608105964303e2f32ae7aa4864ed1e545cf5490c018bacbb9aa9218021fe157058a4303c3e42ae0b1486018ec874816290c031e90e882c32193b0f95374595432662f29ee6b2a864ea3e849496550c994bd07292caa18031bdca52595432563a38ca4b2a8675c78709496550c018dee4292caa19231d1c452595433a63c380a4b2a8600ce772dc56550c019c8e5b8acaa180339dc8715954300672390e2b2a8600ceb72dc16550c019d0e5b82caa18033cdc770595430067838ee0b2a86008ef825c16550c071d904b82caa18023de0570595430147a40ae0b2a8600ceb721c16550c019d0e4382caa18033cdc4705954300678388e0b2a8601c7870d416550c030f90ea82caa18071e1c150595430043fc3aca32a864e87d87d975450c018becbb9aa8a19321f61f65d4d4301c76412eca9a86028f4815d95350c011f700bb2a6a18063e2017654d430061fb2ee8a9a860787f875d76250c018df04baec4a18031b20975d894303c3f42ee1b12860087d85dc36250c018dee5292ca218061f21d505944302e4f43eeca188600e1e85dd94310c01c3b0bbb28621802a7e037650c430054ec06eca188600c9f76dd54310c0153b0d3aa862180347dd67550c430054fc32eaa188600c9f765d54310c0171f04baa8621976e32097550c43005cbc0aeaa18865cb94815d54310c0173700baa862196ae62017550c430058f42ee4a188600b1d85dc94310c0153f0cb928621802a7e197150c430043fc2ae0b10860787c855c16210c0d17908b82c4218163720d70588430047bc0ae0b1086028f4815c16210c031d90e902c4218029b21520588430355642240b108605acc834816210c010ff0ab82c22181e1f21570584430345e422e0b0886058dc835c16
  | 6 => 0xc7a43a20b0ca800a7785441619509f47d09296c6aa1321f61c52d8d542652f418a5b1aa84c87d87d4363550994bd07a86c6aa00237e1d6318d5400536c2c43b12a8018ef8748362550014df0a906c4aa0063de1d10d855400c6e43a60b18a80787c855c162150031d90e902c42a01e1f21570584540345e422e0b08a8008df835c1611500b1b906b82c22a0023be09705845401c76412e0b08a8018f487441611500d56908882c22a13e1fa1e525935327d1f424a4b26a60587c855c164d4c9f0f90ea82c9a993e8f211505935303c5f43c80b26a607a3e8510164d4c0153b06202c9a9802ab60840593530055ac0880b26a60587c855c162d4c0b53d0720ac9298028f614415925302c6e41ae0b24a6018bc875016494c0b53906a02c929817271cd6455253264aec36e6aa4a600c5d86dcd5494c031d90e902c5298029be152058a5300c7a43a20b0ca600a77854416194c9b4bd07296c8a993a1f61c52d91532751f420a5b22a6078dd83dc36454c9d0fb0fa86c8a993a8fa1350d91530045fc3ac8322a606c9c645ce5454c9d47b0fb24a8a98030f61f649515303e2fb1cec2a2a600a6d858876254c031df0e906c4a98029be1520d895300c7bc3a21b0aa6018bc875016414c0f87ee9bb2a82981e1f215705885300c7643a40b10a60787c855c16114c0117f08b82c22981a2f211705845302c6e41ae0b08a6008ef825c16114c071d904b82c2298063d21d105845302d6a41a20b08a600a7a8008665d0c014f30010ccba18021fe1d209974303c3e43a4132e8600a768108265d0c014eb02104cba180297e0d109974326d2e41a2132e8600a6e8204265d0c014db04084cba181a8fa12525974300637b94a4b2e860687e8794165d0c014dd05282cba18029b60a50597430053b40ca0b2e8600a758194165d0c030f90ea82cba18029be09735974300536412e6b2e8600a77815cd65d0c014e902b9acba18029ee0173597430053c402e6b2e8606a3e849c965d0c0147b09392cba18031bdca72597430351f42464b2e8600a3d848c965d0c0d47908b8acba18029be09715974300536412e2b2e8606a3e848c565d0c0147b0918acba181a8fa1021597430051ec2042b2e8600a7a8008565d0c014f30010acba181a8fa1270597430051ec24e0b2e8600a6e829c165d0c014db05382cba18029da0670597430053ac0ce0b2e8600a3f844c165d0c0d47908982cba18021fe1d20597430043e43a40b2e8606a3e8408165d0c0147b08102cba18029da0420597430053ac0840b2e8606a3e8404165d0c0147b08082cba18029ba08105974300536c1020b2e8607c3e655d353d0c99a3ca6ba6a7a18030f5977454f430043fc2ae0b16860787c855c162d0c031d90e902c5a18063d21d10587430053d4004332c8600a79800866590c010ff0e904cb2
  | 7 => 0x1b02380001a1c1548e65b44cc000001c00005fa546bae091f0394b2c7d319f3024204f600000046c7688c15aa997780e456f70a490c40e0006219d340000dd1800f4d70bc8055204b9081ce5989d9d6ac62d0258f428e44209986379548a2d9e3052e4d9c002ee484e6d629f0000139a180077e93c1e000558b003a24865674414361088104ef0000001a80019e0ba72d3f8003ecc955b0000003d9da1fd53e3a0bf2b71d89040002e44c0019d27042c76c0000001214c0009f710000003182ca29dc9a8765e3f85b9e500041c0001300000000000000e3d12800000000000005c400000078452c0c00202226699c00ab6e6434f53ce000028628f53f22ec0018c0005080024c10023c8d11f3686b53700025a878c7ad1274000fe100594534000005d8f09a7a2a690181708df25666c0016c000000eb2c90004d9490003149b55e08e55c00194ad77a4de9cc1c55d40811880020833c000f108613db1b0d2c48d8de39600000146000000b500033200000111240000c64000b200e1bc002fc000825c31c0534cd8850db2b40a400062294288668007788340d0840bc00077000280940002660000fca63c71b82d59db512f000d0426f70e798443da320e740000026a001aa00077a9d1390004d6cf4003b60ce0000029e78a65406000658acc8f05913c57166b39242000002e81c62a1e416a30ca35328ce1540000027b7560014080070a001a480014a290f39d9764d043315f2ecd4d7f8b84fc9b08327d5a45cd1b8000000000017f436a18391b9000128348c05069605e8001ae3543ca4e000b117e8320007218b3403b00dd268302964f40000018c671a50190004dc5c8004585bc2da280001303ea6701e000000ba0007e96b14f10edbd2380027e85c8e0002ea0000031300000070200611478005884018008038830a00060c4040a000808e638080102d1051c41610c2000981801ac5a808ed0830228a20808a20cc8460020c19441a18a09200420043608001a0800b201ef0000208440600004838a0080ec00220400818400002039800c1001a4c1a4000840100001000002803e803400610000208e0000960103c000210200020a01c08009c50a00a00e10038080210288008a18400800201c1035b2414080000180182000e8c40608010650228a10a78e10608207421a08400201338e38a60011000e0a00da410f1210c60009c53c58079231e00600419020c61240420b1000f040a3090800861ae10810200400209361fa1e5258f5426d2f41ca4b1ea80687c855c163d509b0f90ea82c7aa1369720d5058f5403d2f42860b1ea800a9d840c163d500159b04182c7aa002b56043058f540343e42ae0b16a806a9e848c563950014bb0a18ac72a01a2f2117058e5400c6e43a60b1ca806a9c844c163950031d90e902c52a0029be152058a540
  | 8 => 0xd0005a565800470a601d80061c001a10906e4959919105324f0000000000017337f6d49f035a4522ebd4003be00098400000000abc000c83a6785500006a0000001510003fd84ac30007d4001165260f8000005100000039f258669d3321000d98f4b6d240114000000004ecee800000de0001dc73427400000228001b60421f6e7804334074045349da2c27514000012261d900cc0eef54e6249728b78368af03ebc8242a154a9a04c0552c609560a431bc69cff8231d6b74e080b3665f11384d254b1ce78766205d00031428a2f1542d96fa0bdaf800000d610080056a40800049000df00038e0963094a91937687018ba845abcd70200430eb982257418e3474abf3da001699a1000dd1caba3562aac518ac346001641f106877c001d24a2a3d9f1276d2051923ba414dc00315762e424002244b6498081c621ce48db9706443e0d502c6708c84a0002cc000da8830004a4f2308000a6d2f2853304c40013e4b4000002394d4ac84c833488b9445bb7000af8112d51f2ecdab89b794ea97daf82a8540202f0554001a28d96bc70d9ba7343e6098abc3422d48af11533e6c92328200064c2fab8000001671ee0c21f93d05a0fef3d1e2a7000e40a0af65f2000778004680000020b696000000001420001c00000000087999248000000007ac5593c8007b62f83e0000006f800000000ee0000275ce1b8002526347c8000b11f854c980006388cd980007a8000003973246a00001e60eb7c493d75fcdd8dc18d2724bd4b3c168e061098000a29e117b6e1a20007d16b52e4c87bb91000170fa00006c1ed930001ce0f400128000000002ad008a45019bd1ba0000b850000e9000111460ddc928e50008648c05214ca747eaa35148f4799ab3ee489830f00ae3286b0b0388f444e23f1b0f65ac8c945c009bda154ea688a3b44614b096e0f40541940ab33758e0d5e967002351a612311a5805482b1a483980a535e8474bd94e34a65d76a12000e9c4d01d4e2c4439b7e000e8400134000788f00890008680038965c001ab06437e0012f88a0006451a8004280000000005a00000086718341ba8003a09898580068c000003d3000a100000074a42c000241401c55809567e691788217806c00e1814760000025d65a24c00016196724000002a4000003b100000080b6b36c7e031afa0361a059adb574b40bbbcd06a000002066ca001ce000000000c2bcc000000b20005d230dda9ef1e4bade49831a6929321124c0da0c73c63ae209c23af362d6daa9ac4aa000001440b07edcca05310611879960a850c00335000001a7000000c74000000004e13bbbb384001dc80000088c003a2662001720004086a5b10001c4ae4e6bd0000560acb1b3d6f60003a9316aec70800000f2dad327000a8863800000119258005c639081b283fcec1a6885290000d78ae0
  | 9 => 0x5b800105394001b8800328001c0b8b000001d01466247557bb1e2ba25d6c07535c000608000ac6255a0006c078d0ea3a0002d10797a6045b5678ea714a700029400056d951716c8420e38b6000001800004b8a246d1557888800017
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2414000000900c20011603814c308900181d86dd67550c4324619204625d543544018e181dc270d895125598259204436548497a608648110d952143f189d9204436548491662984811019521245982612044065484ebc639748110195213a71825d20440654850dc60754811059121437181d5204416348491864811957210d21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0xb09
  | 5 => 0x4
  | 6 => 0x5
  | 7 => 0x6
  | 8 => 0xb49
  | 9 => 0xb4b
  | 10 => 0x1d49
  | 11 => 0x1d4b
  | 12 => 0xb89
  | 13 => 0xb8b
  | 14 => 0x1d89
  | 15 => 0x1d8b
  | 16 => 0xbc9
  | 17 => 0xbcb
  | 18 => 0x1dc9
  | 19 => 0x1dcb
  | 20 => 0xcc9
  | 21 => 0xcca
  | 22 => 0x1ec9
  | 23 => 0x1eca
  | 24 => 0xd09
  | 25 => 0xd0a
  | 26 => 0x1f09
  | 27 => 0x1f0a
  | 28 => 0xd49
  | 29 => 0xd4a
  | 30 => 0x1f49
  | 31 => 0x1f4a
  | 32 => 0x589
  | 33 => 0x58a
  | 34 => 0x58b
  | 35 => 0xe89
  | 36 => 0xe8a
  | 37 => 0xe8b
  | 38 => 0x1789
  | 39 => 0x178a
  | 40 => 0x178b
  | 41 => 0x2089
  | 42 => 0x208a
  | 43 => 0x208b
  | 44 => 0x5c9
  | 45 => 0x5ca
  | 46 => 0x5cb
  | 47 => 0xec9
  | 48 => 0xeca
  | 49 => 0xecb
  | 50 => 0x17c9
  | 51 => 0x17ca
  | 52 => 0x17cb
  | 53 => 0x20c9
  | 54 => 0x20ca
  | 55 => 0x20cb
  | 56 => 0x749
  | 57 => 0x74a
  | 58 => 0x74b
  | 59 => 0x1049
  | 60 => 0x104a
  | 61 => 0x104b
  | 62 => 0x1949
  | 63 => 0x194a
  | 64 => 0x194b
  | 65 => 0x2249
  | 66 => 0x224a
  | 67 => 0x224b
  | 68 => 0x15ca
  | 69 => 0x144b
  | 70 => 0x160a
  | 71 => 0x148b
  | 72 => 0x44a
  | 73 => 0x2cb
  | 74 => 0x164a
  | 75 => 0x14cb
  | 76 => 0x104c
  | 77 => 0x224c
  | 78 => 0xecd
  | 79 => 0x20cd
  | 80 => 0x20e
  | 81 => 0x140e
  | 82 => 0xbced1
  | 83 => 0xbe0d1
  | 84 => 0xbd051
  | 85 => 0xbe251
  | 86 => 0xeddd1
  | 87 => 0x1dced1
  | 88 => 0x105dd1
  | 89 => 0x1dd051
  | 90 => 0xe8591
  | 91 => 0x58e91
  | 92 => 0xe8592
  | 93 => 0xe8593
  | 94 => 0x5d051
  | 95 => 0x74ed1
  | 96 => 0x194ed1
  | 97 => 0x20d7d1
  | 98 => 0x20d7d2
  | 99 => 0x20d7d3
  | 100 => 0x17d051
  | 101 => 0x17e251
  | 102 => 0x1960d1
  | 103 => 0x225951
  | 104 => 0x225952
  | 105 => 0x225953
  | 106 => 0x94e
  | 107 => 0x98e
  | 108 => 0x1d42d3
  | 109 => 0x1ec452
  | 110 => 0xcc452
  | 111 => 0x1d82d3
  | 112 => 0x1f0452
  | 113 => 0xd0452
  | 114 => 0x942d3
  | 115 => 0x98452
  | 116 => 0x449
  | 117 => 0x1649
  | 118 => 0x128452
  | 119 => 0x165f52
  | 120 => 0x17e0d2
  | 121 => 0x196252
  | 122 => 0x134452
  | 123 => 0xa4452
  | 124 => 0x5c452
  | 125 => 0x17c452
  | 126 => 0xec452
  | 127 => 0x74452
  | 128 => 0x194452
  | 129 => 0x104452
  | 130 => 0x17e0d3
  | 131 => 0x196253
  | 132 => 0xee0d3
  | 133 => 0x106253
  | 134 => 0x98956
  | 135 => 0x44992
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2093
  | 6 => 3713
  | 5 => 989
  | 4 => 13
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
  | 7 => packedAt gbK7 (80926+((h/697+packedAt gbK7 (77441+(h % 697)*5) 5) % 5315)*13) 13
  | 6 => packedAt gbK6 (188120+((h/1237+packedAt gbK6 (178224+(h % 1237)*8) 8) % 4827)*13) 13
  | 5 => packedAt gbK5 (60325+((h/329+packedAt gbK5 (58351+(h % 329)*6) 6) % 1286)*11) 11
  | 4 => packedAt gbK4 (922+((h/4+packedAt gbK4 (910+(h % 4)*3) 3) % 22)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff03fc07fe03fffffc07ffff013cf8fd18fe3f
  | 1 => 0xfffc3ff83ffc0f807ff81f000ed34f1eef33cc
  | 2 => 0x3ffc0003ffff0007fffe000f0e38fe30fc3f0
  | 3 => 0x3ffffffc00000007fffffffff03f003f003ff
  | 4 => 0x3ffffffffffffff80000000fffc0003fffc00
  | 5 => 0xfc0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x15004400461052a30c20a5460004186c085615
  | 1 => 0xd92c1d881a944b053528960a06514b146b32cc
  | 2 => 0x1355c0422d5b620a5ab6c41470a28da30dc370
  | 3 => 0x429aaad68041001063c718b8bb03e003b001aa
  | 4 => 0x82e3336731e38c5c00820020ddf80003d6a800
  | 5 => 0xe000038401820860030410c0effff6d8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40914
namespace PEqualNP.Outside.L_meta_40914
open PEqualNP.Outside.L_meta_40914.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 2 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 30 := bs0_3_0
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
theorem bs0_4_704 : Interval s0Atlas 4 704 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 712 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bs0_4_0 bs0_4_32) bs0_4_64) bs0_4_96) bs0_4_128) bs0_4_160) bs0_4_192) bs0_4_224) bs0_4_256) bs0_4_288) bs0_4_320) bs0_4_352) bs0_4_384) bs0_4_416) bs0_4_448) bs0_4_480) bs0_4_512) bs0_4_544) bs0_4_576) bs0_4_608) bs0_4_640) bs0_4_672) bs0_4_704)
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
theorem bs0_5_704 : Interval s0Atlas 5 704 31 := block_range (n:=31) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 735 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bs0_5_0 bs0_5_32) bs0_5_64) bs0_5_96) bs0_5_128) bs0_5_160) bs0_5_192) bs0_5_224) bs0_5_256) bs0_5_288) bs0_5_320) bs0_5_352) bs0_5_384) bs0_5_416) bs0_5_448) bs0_5_480) bs0_5_512) bs0_5_544) bs0_5_576) bs0_5_608) bs0_5_640) bs0_5_672) bs0_5_704)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 42 := (concat bs0_6_0 bs0_6_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 68 := (concat (concat bs1_3_0 bs1_3_32) bs1_3_64)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 129 := (concat (concat (concat (concat bs1_4_0 bs1_4_32) bs1_4_64) bs1_4_96) bs1_4_128)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 45 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
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
theorem bs2_4_128 : Interval s2Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) bs2_4_64) bs2_4_96) bs2_4_128)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_4_0 : Interval s3Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 2 := bs3_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 2 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 13 := bgb_4_0
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
theorem bgb_5_960 : Interval gbAtlas 5 960 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 989 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) bgb_5_64) bgb_5_96) bgb_5_128) bgb_5_160) bgb_5_192) bgb_5_224) bgb_5_256) bgb_5_288) bgb_5_320) bgb_5_352) bgb_5_384) bgb_5_416) bgb_5_448) bgb_5_480) bgb_5_512) bgb_5_544) bgb_5_576) bgb_5_608) bgb_5_640) bgb_5_672) bgb_5_704) bgb_5_736) bgb_5_768) bgb_5_800) bgb_5_832) bgb_5_864) bgb_5_896) bgb_5_928) bgb_5_960)
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
theorem bgb_6_3712 : Interval gbAtlas 6 3712 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3713 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) bgb_6_64) bgb_6_96) bgb_6_128) bgb_6_160) bgb_6_192) bgb_6_224) bgb_6_256) bgb_6_288) bgb_6_320) bgb_6_352) bgb_6_384) bgb_6_416) bgb_6_448) bgb_6_480) bgb_6_512) bgb_6_544) bgb_6_576) bgb_6_608) bgb_6_640) bgb_6_672) bgb_6_704) bgb_6_736) bgb_6_768) bgb_6_800) bgb_6_832) bgb_6_864) bgb_6_896) bgb_6_928) bgb_6_960) bgb_6_992) bgb_6_1024) bgb_6_1056) bgb_6_1088) bgb_6_1120) bgb_6_1152) bgb_6_1184) bgb_6_1216) bgb_6_1248) bgb_6_1280) bgb_6_1312) bgb_6_1344) bgb_6_1376) bgb_6_1408) bgb_6_1440) bgb_6_1472) bgb_6_1504) bgb_6_1536) bgb_6_1568) bgb_6_1600) bgb_6_1632) bgb_6_1664) bgb_6_1696) bgb_6_1728) bgb_6_1760) bgb_6_1792) bgb_6_1824) bgb_6_1856) bgb_6_1888) bgb_6_1920) bgb_6_1952) bgb_6_1984) bgb_6_2016) bgb_6_2048) bgb_6_2080) bgb_6_2112) bgb_6_2144) bgb_6_2176) bgb_6_2208) bgb_6_2240) bgb_6_2272) bgb_6_2304) bgb_6_2336) bgb_6_2368) bgb_6_2400) bgb_6_2432) bgb_6_2464) bgb_6_2496) bgb_6_2528) bgb_6_2560) bgb_6_2592) bgb_6_2624) bgb_6_2656) bgb_6_2688) bgb_6_2720) bgb_6_2752) bgb_6_2784) bgb_6_2816) bgb_6_2848) bgb_6_2880) bgb_6_2912) bgb_6_2944) bgb_6_2976) bgb_6_3008) bgb_6_3040) bgb_6_3072) bgb_6_3104) bgb_6_3136) bgb_6_3168) bgb_6_3200) bgb_6_3232) bgb_6_3264) bgb_6_3296) bgb_6_3328) bgb_6_3360) bgb_6_3392) bgb_6_3424) bgb_6_3456) bgb_6_3488) bgb_6_3520) bgb_6_3552) bgb_6_3584) bgb_6_3616) bgb_6_3648) bgb_6_3680) bgb_6_3712)
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
theorem allgb_7 : Interval gbAtlas 7 0 2093 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) bgb_7_64) bgb_7_96) bgb_7_128) bgb_7_160) bgb_7_192) bgb_7_224) bgb_7_256) bgb_7_288) bgb_7_320) bgb_7_352) bgb_7_384) bgb_7_416) bgb_7_448) bgb_7_480) bgb_7_512) bgb_7_544) bgb_7_576) bgb_7_608) bgb_7_640) bgb_7_672) bgb_7_704) bgb_7_736) bgb_7_768) bgb_7_800) bgb_7_832) bgb_7_864) bgb_7_896) bgb_7_928) bgb_7_960) bgb_7_992) bgb_7_1024) bgb_7_1056) bgb_7_1088) bgb_7_1120) bgb_7_1152) bgb_7_1184) bgb_7_1216) bgb_7_1248) bgb_7_1280) bgb_7_1312) bgb_7_1344) bgb_7_1376) bgb_7_1408) bgb_7_1440) bgb_7_1472) bgb_7_1504) bgb_7_1536) bgb_7_1568) bgb_7_1600) bgb_7_1632) bgb_7_1664) bgb_7_1696) bgb_7_1728) bgb_7_1760) bgb_7_1792) bgb_7_1824) bgb_7_1856) bgb_7_1888) bgb_7_1920) bgb_7_1952) bgb_7_1984) bgb_7_2016) bgb_7_2048) bgb_7_2080)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00feeaeae8eeeaea00
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808424 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40914.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.or,[1,2]⟩,⟨.and,[6,7]⟩,⟨.and,[8,5]⟩,⟨.and,[3,4]⟩,⟨.or,[9,11]⟩,⟨.or,[3,4]⟩,⟨.and,[6,13]⟩,⟨.or,[14,10]⟩,⟨.and,[15,12]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40914

open PEqualNP.Outside.L_meta_40914 in
theorem PEqualNP.Outside.L_meta_40914 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)