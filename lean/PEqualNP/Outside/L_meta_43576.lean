import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_43576.Model
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


end PEqualNP.Outside.L_meta_43576.Model

namespace PEqualNP.Outside.L_meta_43576
open PEqualNP.Outside.L_meta_43576.Model
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

def SBf (j : Nat) : Nat := [6, 8, 6, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_43576

namespace PEqualNP.Outside.L_meta_43576
open PEqualNP.Outside.L_meta_43576.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x2000000000210b20020230df30be42de32be40dc32dd30bc42bd41de31dc31bc40bf41
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa00006000040000138505071884194b14941a6292614e528c6a8a2984b94a40
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
  | 3 => 2*((h/23+packedAt s0K3 (189+(h % 23)*3) 3) % 7)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 2 => 0xffc0fffffffffffff81ff80fffffffffe38fff
  | 3 => 0x3fff01fff80fe03fffe0fff03ffc0f80fcf3cc
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4a4414423122490a01652a544a2194aa0d3615
  | 2 => 0x909228a442449414580a510a94c629546288ea
  | 3 => 0x230a4d2890e90566aaa09d6227688e06b4d34c
  | 4 => 0x3a2cb1d12481d9bb34d3064c39b3c418df03b0
  | 5 => 0x3c30c1e1c70e1e3dc71ce78f01c30860fbec00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_43576
namespace PEqualNP.Outside.L_meta_43576
open PEqualNP.Outside.L_meta_43576.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x11810814401c014200520000004028409140b000fd43fe10ff41fd42fe31fc20fe43fc31ff43ff42ff31fd20fc21fe42be40fe20fd21ff40bd42fc42bf42bc40fe41fe21ff32ff20fd31fe40fc32fd40ff10fc43ff30fd10fc40fd41fc41fe30fd30ff21fc10fd32fc30fe32
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x6437c540c6fea8995f14d10bf284417e5104378a8985fd4e10dfa12637e510c6fca8995fd5131dfa1665ef20082faa018df947209eaa065be54c877ca7205f94841bf2a243bd420c2fca0185fd41439f2a063df310c6faa8985f14943de90c81bd42482f8a790efd0e43b6292637e518caf8a4a0df54742df194817e5190f7880085fd4532f7a9261bc31103f621087dcc631dea0081bf529037e8220df94740bfa9e217d52cc6f8a918ef95232df18c81bf41102fca3205f94631df908816d52d067ca0207b50a21bf28421f731043ea20085fd4810dea1661be21902fca3186fd4d42b7a9263be40882faa8186f10440fb082217e544c3f420085f54a10bf28881be519037e8520efd4440deaa0657e5010b7a65205f94432bea80657f524c2fca320df54f42f6a1065bc40842dca5a0df95041de28c81de324caf8a9086f94440be29c41bc544427ea8885f95010dfa9285bd42442fea9885f94010bf286837c50486b8a6886fd0a42bf28481bd540c6fca9106fd0842bea9083bd419037865206f50b31f799465bc43907ee63086fd0640ee990657d54442fca410fb90832df20041be40c42fea2a1778ca30be29a437f5250efaa3186f90230de29a857d50d0b7a8490fd8c431deaa643be540c6f8a8995f94043df28e85dc328c2faa818df55321beaa065be4350ed8a4987ed4131bf28c417f52c42fca4184fd5120de28a857d50d0f7c80085f94621bfa9e41bc21102fea9986f55330bf29c877e5108378a8905f94241bf29c21fb20882f8a9885f94021ef18c617e53106f8a6a0ef0c640f7102417d54843ba60186f94840bea9e437d51cc27ea8987d48421bf29e85bf43d0b78a4207790c43bf29e813e54cc2f8a4886f15131f7210437d5110efca4206fd0830bfa92837d5310afaa9205f95031be29841ef320867ca9906fd0c43dea9881bf424837e80205f15020fca0081bc41902fca5a1df54232df21e85be50102faa4185fd5031bea9c85ed52d06faa7885fd5210de21e857e52d02f8a098ef90210dea82857f53c8778a0a15f95040be290213d54082fca898ef50a20f729683ed20082fea5085f94231df90c81fb40503b863186f55232df28285ad52102fca0204f15110dfa1661bd4350afca5185f14f10dea1443ad42c83ee4290db54840be2a661fa401037886a14f55242bf294657c54cc6e8a2985f54910bea9881ed42ccafea690df94843bf2a6637e53887ea8220df15232bf28663bd428cb7e8598fdd0541bf29c83bf544c75a85995f54420bf29c853d548caf8a5087dc8621de10c817e548437a84995f54b40fb88021bf321037e84885fd4e20bf2a465bc404c27aa5204f55320df202817f5444378a7a17bd4910bfa9c43ed420877ea0a16fd4640deaa041bc40c837a84a0df55132de298817f54886faa110cf95020
  | 1 => 0xf42c437a84a05f55320be28a65bd519037aa3a16f50d41bfaa463bf428c7be64197b14931f619041bc429037880905fd5030f629261ef524c7788620fb48421beaa6617e520c6faa9885f94230b7a9261bd3190278a898df94c30bf29a433c5050b7ca1a16f50c40dea1481ad42887f660085f54a20dfa1643bc40cc37aa42077d4d20dfa1063be41903f0a098df54640bea98437d510c2fca5887ec4110f6a1085bf544c2faa9186fd0841be2a665ee4210ab8a6905f54332df2a6217e5090fde4310df546429faa4417e530837c87205f15120bfa9a857d540437ca9905fd4d20dfaa441bd53d0b7e85a0df14d40beaa6657d508c6fca6885f55331df28a85be400c2fca8885f94c40bea9483bd52902fea8106fd0840fc880217d5408678a9105d14520dfa14217e530c77ca62057d4d10bea8c217f548cb7aa1a16f10110df98881bd43d06fca020ef15220bf2a085de314c6fea6085f54042de21881f7514835ca4205f950219f2a065bd5350bba8621f78c830be2a2616c524427ca990df14542bf28643bf43903e8a2986f50930beaa487ee424837a85905f94a40bea9c81bc53903d84310774c4319faa2637d53882dca4205f14f20b6a96877d52102faa910dfd5331deaa0437d51c82fca9185f54740bea9c43bd42ccbda84905fd4131df202417d5010efca4085fd4c21bf286877e540c2faa518ef95021df29e857d54486faa7a0df95310bea9e817e53c437e8410df54b10df206617d53c82fea2905f54041fd100417c540cafca3995f54e329f2a465f5310c6faa9215b94b43df2a0657e51d0efca910cf94342be2a641bf42502fea2985e14131f610841ec32086fca518df54c10f721443bd439037aa990770c830bf288437d528c2faa1216f50931bf28685f9300c2f8a0a15fd4c20bf28065bf52102f8a610efd0b40dea88817d5008778a5207bcc932bf2a2417f53502f8a898df94e40de204617d53487de85215fd4540ef18861ef4250b7a42206fd0a40bf288617e5090b7aa7207dd0641bea84837d53442faa2206fcc640df202217d518835a84195f14b10df294817d544837887205f149409f28481bd5150b7c42206f50a41bea9443dc310c37c84a15fd5220dfaa2417c540877a84216f8c840de20441bf42c83be61185f14543dfa1a857f540867aa990df54c20bf290652d52102eea2985f14141de99081be43907de65106f94d42bea9a41fb20482fea890fbc8220bea8c655f53482fca0105f94442be2a441dc53442f8a7086f10020bf284657e528437a82206f50441dfaa221d5310c6f8a910ee94040beaa483ee521035a8410fecc130f7994437d51d0efca8197bc8421be28265be31102fea8085f94c10df2a661ef320837e84985fd4142de190817f52442f8a2986f103109eaa063df318c6eea2905f55220bf2a
  | 2 => 0x4030bc04038100501c009270745f0a051000010c88000801000ae038060141905c0008c00000630080d0082201403030140d80000c24018002800907481030060200002c0510402004510e4090000600c0f00c01030030c000001800d82a01c000083e0745e0029fb480400c0b00014000c00840102401000030743232805038007881a000fe0091329433018110046900000000010000000000000040280211003010001088e004010601a038010140301c1700c0e0240d0180604c000300101400010080203d1dc048d81600c43002cf02c9208019000070140001c00000ef024001ac540500806807088360382300c001642b07400008200280a30c68000710000007801000000287a11acb0000406c08390772280502400008010041aaa8030000000009044020cc0731057024020b400000031440e000130f40602c130000003c3401808111d614815024010680103c1603c290001d0308600000018570006200c29014001342400eb405b7a87a16f90541efa1c87f621086fea0a0ef50820bf294837d5190efaa190fd0c410fb88421bd420cafaa71877cca32bf290417d50cc6faa720ef50a30bea9c637e534837e81206f50b10bea90637d5090efaa5a1df54a43dea1887bd428c6f8a8186f14440bf296617f544827aa9885f14e21be29a853d54cc278a8985fd4121bf298657c540437c82205f54432bf29e437d5110bf681205f94332bf284437e51cc2fea9905fd5130bea9661ee214867ca810f714d20be2a643be54082fca9987dd4530dea1021f4318437a8418ef90320beaa041bf424cafea0997d14520be2a461bf435077ea6206f90d42bfaa0657e5110fee42085fd49319e2a241bd31102faa7085f54843bea98837f548c2fea4a05f95320bf29221bf41907da85906fd0a20bf29e836f524437a8420dfd4d41df21081bd42d06faa1a0efd0a32f721641be404c3dc43105f94441f7296873d54087ee6298efd0921dfa8685bf431037a84207b90b32bf28063df534437a85086f14742be292637d52d06fca5a0ef10840deaa621bf5150afca3216f90c41bf29e417e54ccaf8a8884f95042dea1643bf42887ee43086bd4942ef98061f830c42fca4217d08410df21881ed52102faa4085f94a42de286857d529037e65205f14520d6a1241ee21083f661887b0ca21bf294877c5050efca3a15f14c10bfaa6437f54ccbf460187b8c832bf29c417e5310ff240105fd4543de20061ec328837c85205f14d20beaa465bf539027aa4206fd0a30fa10c217e52cc7f060087b4c832dfa9e857e548c77e87a0fb54b43dea1043bf42083d8a4885fd4d10beaa263bf425067ca9886fd0810bf2a0417d548c6f8a2a06f50b40dfa1065bf51d0af8a4985f95043bf29843de304c3be86a1fd90441bea8e657c54486f6a098fecc230bf29885b
  | 3 => 0xb03006040a4014640c00b00
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x8404c23c6454c108fd9531103733114131cd5445150b2e4354840ab58b419023d6414a108f596421038f424c832d3d4c524423d64149108f590524c63d64d4f20ab58b4390f2f54d49309b18953906e860509209b594320823d65950208f597420866d62950318f593504c63e65d0930cb50d521032f6154840cb508514831f5350910cbd4b424c6b8604c640cb98a540c65e63152219d584540c354518c130ad584531023e6414e219d986544827860551219b588540c2ad6214c40cb553320823c6454021ad984531023f6454331cb54942cc63e650ca40cb549428429d6314742cb54b321025f63551108f99052c423c65509308f195424832e62953109b98a544423f62550208f997425036452841109758f52c4397424c431ab588400832e5250b418f58b544c23e6494b309d984540c26d6294d108f992544c6cd63908329b189544c2d9600c830e5191310c72d4354b418f992518c32e6295320cbd53208832c5350b209b58a54c42bb60484408f992524432c63548408f994544833542d4530ab588400c355530c410ae98351102e462440109bd954210a786055132cbd0d52d063c60550218f592530c26c6255110cbd50524c72c54149108f180544423e65101109e98353c865f6354021cb54b211032f6550b328f59542c423d650c440abd92204832d524c440cb54842103645214530ae98051102ad64909208f99640442f0614c0308f59053c876452d45308f99053042ba60d4a40cb949420823e6494e109758e524426f6254e408f195424423d6494b31b558e310c72e6054840ab592320ca7965840108f992544823d650ca40cb54b421072e6414910e54c4311023c64546208f19150c87374214530cd14640482746155132cb550210829c6354542ea54a501031d5314d428fd91500ca7b654c030ab9875250a5d6315221cb150524c23e65d0931b6181310c72d540c8209d185500cb2c6550920cb9514210ab76154142e918542886ad6295031cb98a540ca5d6315010c714e404832f5250910a758c51102786055131ae18132102ae6214c40cbd95424832f52901309b98854842ae62d44409dd85544c25f63549109bd89544c65c63551108f990534863e65c84409b988540c23d64148108f592510432d5214840e9508218426c6254640ab593210863e6494c30abd8951903ab42480208f99352c423d62151109798f52c432d5250a31cb54821103685214131d314c524431c5350910da14b504c66c6254643b5185300c32c54d4931ab58b4310f2d520c840cd54451d0a3f65100208f994211032c4354840ae181420423e65101208f195424c62d62953309b98a544c63d6590020a758f50d0b2c61548408f992518825f654c030cb54b311023d65d08208f59721903a542084109b58853043345110130ab18931903394214131
  | 1 => 0x42776550441ab181424825c63549108f597420c65d6314810ab189539032d52d44408f997219023c6454430e5551310c63e6494821ae1815350b2d52944408f994219031f54d4d108f997424432d52144409b189500c7654214520e3508328c354538411097d954310e6f62546408f18154c87c4624c4318fd91510c26d650c8219d185544832d42947209dd9521087b04044010cb153524423e65d0d418f197424c25e6395120ad58453d0a3d6494d20e318d42cca3e6494b10cb548411034c528c130b518d100426d62951108f596329032f54086209b98a524423f6590020c7d4e404423e64944109ed81534871c5414d10d314d424823d64d4f10cdd0b514832e5350832cb14840443386414131e5509310c63d62550208f596540872d62953308f58b544c66f6548020d9d48514c2ae62d0c409718d54482b46154d429718d50086ae6214840cbd53328823d6494b108f191534863f654c640e950a210866e62150208fd8954cc32e6454b419b58854cc63e6494a30cdd5351482ba6014640ab98b419032c5354840ce982501026e6294d10cb553320863d64d4f21e6101300c23e6494830ced90504c6746155130cb549321023f6454031aed81319032e5250830cbd93524c63d64d4e10cb949428c26c62551318f59742c432d528c840cb549511025e6514d20cdd46404c23f65d0b308f197424c62c65509209d586534827561153329ed95100423f6454d10cb153524c31f53d09208f993504cb3a64d41318f99253882af6254d42e950b514834c53d4910ced50504c7d0310c0108f982540871c54d4d20cb54a421023f64547328f59053c838d42cc832cd153514831f54d4d209d586544c2766114c208f990524c72f5250931cdd44404823d64948209dd85524423d65d0b30cbd4d521023e64948328fd91508cab461509419d58753c82ad6210230cb549428c2ad6210210cb193524423e6414f10ab58b411063c6454032cd508514c27b60551218f594321032d5294040ab58b439023f6454d20ab58a5350a3e6494b31ab58b51102ad62953109d185534832c52d09308fd97420c6b86050a20ab181428866d62152108fd9742c423d65950319798e544423e6550910e3d4d424838d420c8308f593530872e6454b43cb193524c72f54d4910ae980531023e6414c209b189510c23e64d4c21ab98b531023e650c840a798c51d0b1f53101208fd95411066e6215230cb152424823d64948329dd85500cb2d540c821cbd4a40442ad6490821cb148404c2756114c208f983544c72f540ca20cb509500cb2f5250941cb553328cb1f5414d10ab592420cacc624c0308f590530863d64948218fd91508c6ad6210010cb54a311023d65508318fd91534863d650c640ce150504c76752d4530cbd0d521031c5390110cb14942c423d6215130ab58
  | 2 => 0x5488420d5d4c514823e6414f20cdd50514c23c6454e21cb949421023d6550b308f980544c63d6414c20cb54a411029c63541428f996404c26d6295130ae181211023c6454910c714c404425d63951108f59251882af6550b20d9908514832f63548409d98454cca5e6394d10ab593218866d62d4e108f59252442b86050b30cb949420423d65084408b58a54c423e60950318f588544c72e5450832ead81424832d6354840cd153514c3aa5294040cb58854882b8604c4409718d544866c6254c108f59253842b86050b109ed81544c6ad62d0440aed81311034d530c8218f99353c872c5350a21ab98f5250b4c5390920bc181310c63c64543329b58a5448679650c010f4181310c65f63551219b189534423d6494b30ce98054882766194d20cb990524c72e6295021cb54a211026d6295131cb990524c23f64543219ed81534423f6550821cbd95420cb3542d45208f99454442b860509208f98054442ac6250d42ab58a54cc23e64d4e108f58a540c6ac6050821aed815150aad62d0641dad48504c7374214520b9586420872e5350821ab58840442ba6014e409e582544c795310c640cb549401023c6454031cbd53524c6ad640c821ab181420cabb604c840ab58853d0a3e650c6408f592520c63c65d0910cb54b40102776154d208fd954210b2d52d0440cbd4b424c23f6454c108f982548ca3e65d09208f181540c71c54d4d108f993530827b60551329758e544823e6494d108f59053c42b66114f42cdd5051482ad62900208fd91524423f65508208f99053c871f535092097d95320cb1c53d092097d8d544831f5414d209b98b53842af6254e40ab1895190357530c610d614f10442d4604c4318fd9542c423c6454d108f996329026f62551308f590514ca3d62953109dd85544cb5753d45209b98a540c66d6215231cb549429023e6414930e9508514826d62953308f995424c32c52d0931ae98351903345110120cb98d521027565084108f992528c757654c4318fd9150887345414520cb590524c72d6414910cbd48404c23e65509319bd95320cb55510c4308f590534872f6550821cb509508863f6454021ea181424832c5250930ae1815150ae461480209bd95210872f5250b10b9584320872e61548409ed95401033451901308f594219029e63d4342ab588408838c5350920cdd53514c32c5414931d3d4f524423d6494d108f597420cb2d6154840c714c404827a6095131cb58b548826f6254d20c7150534832d520c4408f990514cb2e5250a319b98a544c2ba60d0a20cb19542ccb2c52d09109798e534836b52d41318f99052042ac624c440bc58021042af624c6408f596540caaf6550821b318d200832c6054840ced53504c63e64948319dd95310c7a74248421cbd49425032d5354840ab18142c832f6554840cb58a54c
  | 3 => 0x131ab59032887a942c8120add855350b2d42944328fd9150ccaaf624c4409bd89530423c60552329e980530872c5350821ab98b41102ad6290220f1d89310c63d64d4b108f992528432c52901109b18953902b561d08419bd89534866d6215230ab58b53102766195130ea101200830c5350920ae98052902ad62103308f99353c42ae62d0e408f992544c32e52940409e58353c86d86344010d9146204823e6415021cb551200832f5414930cb94d42c826f62546438f98254c863d6295330cb509500863e65151308f191508cb2d6295031cbd93524423f6454e21ab58840c42b86050830cdd0b514c29e63144408fd89540c6bb6054d42cb553200825e6315010dc147304c23d64d41328f990540cb1f53101108f994311033a60d5220ad58750d0b2f5294a408f592528432e5250a409b98b53c432f548862097d95310c66f6255110cbd9542c832d4294421b5d95310c66e6295330a7d8d5050aad62144408f982540caad62d4f42cb549211025e6514d108f59353082ad62101209b588540432e5350a21cb50950cca3e658c840cb949428423d6590c41ab58840c833542145209dd95100432c64d49308f19531102ba6014840ce593504c6796014c21cdd4640482ba60d4e40cb54b42d02d0604c4318f58b544434c53881208f994404c23d6494e20ae983424832c52509419d98753c823e64948108f191508c72e5450821cdd44404c32d64149309b98a54c423f6550831cb94d521023d6494a309b98854042ae6214440cb54942043345414530cbd49424c3d3604c431cb54b421032e62953308f596321023e64d4f209b596420863e6494d209dd85534431c5350920cb549420c35a31141318f590524c26f6254e41cb991521032d5250440cbd4b42442ad60d49429b98853042ad62d0c409d586544831f5390120ab58b435063e6414a108f992544432c52901309bd89534423e64948209ed95200823d64946308f590530423f6550c438f592528c72d52d0b418f594400823d6414e218fd8954c423f65500409798e524423e64d41318f996404826f62544308fd91538832c5250931c714f424423f6550b30ab18142cca3c654c6408f990540c63f64546209798c520432c5350920e9d854288797644c431e5951310c63e65151318f592520c2b461541429b58a544ca6d62d4f109e181534862d62950318f990524431c5350d42aa18142482ad65948408f181540cb2d42947329b596420cb2d62151208f191534823c6454e208f593504866e6215231cb549429073b42141319b98854cc66c65509209dd85544823f6550832d514f51482ba60d4c40ce153504c71d5310f42cb95142c833b42d4131cbd4840442ba60d48408f592520432c5250910abd95420caad62d0f418f191508872c6550a218f993504866e6514910ab98b4350b2d
  | 4 => 0x57030190100806c2a04c0e02c030040800005004a80182200000000090c068010000001700086000510080800c51004000002f00001064170000103c010281100013000070cc000800109c0f3981002c560003a0080a028270000000c00050000b000000220301f07800034000100f0b41e020000140716c0f0483a0c0020040d06c011302a000070640049c0003c0001c25124070043d360060180407c230f401144100300b0140020c390000300000004261f00000000008060340f0402405487074020142c00d3a00002018010700000c060502e08814004060040103c0602c00008120780003053000010942b0001a00417004100d80004425029c11dc291d41202c060001f02005008101680100c0006800000030000d0200b05404080040388e07c0013c0c0005cdb401000ff01800000040c00d0280200805080a000c1401417000020043b14c00000000308a0045100c02018010200502403018020180c0000f0540f0140d004010881e22001018040181200027024000001115802018800100303400008040080500805000314fc0400000da0023bc560180c008a50008900800028009e40d000170000d01c14040000926f62540318f990540829f63545429d594310423e6414c21c9508514832f6550a21ad98750d0b2e53509208f19150cc63d65c8440c7d4f424432f64d4930d514c514832e5250b31cbd50524438f6350b328f19151ccb1d5314f428f59052c433942d4
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x305000000001c000b1f00000300080e100c0003010001036f00040300050305000601691c150007030e000a0019060304000002000700040e54032912280000040d0000000000010e08000305005826170618c2ac6a88a3a142f76d48404c294382c2a90818a54b604c840c52a430262205257199152d0f44a12c019061c1549310c440a48e0a10a2904d071580320c34830880980614a1c14214520d20c620220087075350851483503088090041a4950604c431b40e0a10a29052972993504c68739ecaa12410b5d4624c440c1ec829c40905267194d4248307a9ac420241c214f605092085ae4302a818e2952d812110293b8ac6a90810b5d662d0c40a1ce7a92858842d7219150cc616b94c928821b0d88604c431c2aa6b08a7a162562d44404c28639ac2a9081895086154032c4ec828c409042d72191508c742320c4988630b5ca64d4131a28e6a88a2a152972190504c686b9cc8a9081c8dc14214520a52ea202401060c635095008784298c0a12410b5ca6494630c56a430285885147154c5350a4a3b284988630b1d9524c44085aec2908088528705095008714a96c0988810bddb5210110c1ea6b108088590704c4319038229a8428a4189584615484085ae532862205247158d5210216b94c829a430b5d662d0440c1cc6a90a22060c535884048298382a228a85495c45354840c30a6302849062952181420c294382c6a90814a5d7424802085ced29a849042d7299053c42d038285a8a41c81c14214520a2aeba126218d8972101300c28739ca6a12418a58a60d5220c4ac428880905187054c5350b48a10c098863a4d90604c431d80c43026218e8b5318142482c83826218881499c46550b32a60e0a10a29042d72983544c6d038284108219214c6050920d4284b0042084d07358021042c2b94a898863499c66454840a50e0a12a01962562144404c348320c098863a4dd0604c431e08a6a16a2905a17210110043153a8c0a1241a41d0604c431c54a6302849050f735855210349a10c0988634a5c05350821c18a6b1080885267114d5210306aa0c6900410b9d9524c440c4acaa10420869154181310c6b03828428a4194594310c01085aec2908098608531814248287398caa1443499c7655092085ae432a622043870595420c616b90c02a221621c1420c83085ee4b286320629521814204312aa0c290041a214c6050920c18a6302849042f7558a4008292b8cc8a9081481c14214520c4ac5a88809060d63548511030ab2a6218881a2188404c030c50a6302849042d7299253842553a8c0a1241a218c4048020c1ac631aa42050e739915210286b9cc8a9683a81884044010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x1c0408010a003a8082008003b4e0a8182950604c431a048158c6354840a088058c635484090487549310c440d00531c142d4520a0a83d486050b10c097518c4048020a20805086154032884865ca544c431a81821d0604c431c80635c84044010c11651c1310c440c21651c1420841088987188404c030c8172184404c030c81421c5600c830d03531c14214520a04835846154840c80735096008410a1185d08604c4318a1871884044010a20805846154840c08631c14254021a11851d0604c431d00531c14214520a228194c6050920d01521c1310c440
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 27
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s1K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/302+packedAt s1K5 (21654+(h % 302)*10) 10) % 802)
  | 4 => 2*((h/350+packedAt s1K4 (33554+(h % 350)*10) 10) % 883)
  | 3 => 2*((h/83+packedAt s1K3 (7056+(h % 83)*8) 8) % 144)
  | 2 => 2*((h/23+packedAt s1K2 (1620+(h % 23)*5) 5) % 27)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffff01ffffff03ffffffffc0fffc7ff1ff
  | 2 => 0xf01ffffffe03fffffc0fc0ffffff07ff91fe3f
  | 3 => 0x1f80fffffc07fffff000fc0ffff87fe18fc7
  | 4 => 0xffe000fffffff80fffffff000fffff83fe0ff8
  | 5 => 0xffffff000000000ffffffffff0000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10c08a111c48912100b2c92c92c048a426b0db
  | 2 => 0x25491462243922462c0550572559054991562d
  | 3 => 0xa9226b44890748b5550289989aad072e18b46
  | 4 => 0x431858c8912240ec9a69b2020e34a6035a0db0
  | 5 => 0x8c1c60f0e1c3870fe38e3ce3c038c463fde000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfaaaa0a0faa0a000faaaa0a0faa0a000faaaa0a0faa0a000faaaa0a0faa0a000faaaa0a0faa0a000faaaa0a0faa0a000faaaa0a0faa0a000faaaa0a0faa0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_43576
namespace PEqualNP.Outside.L_meta_43576
open PEqualNP.Outside.L_meta_43576.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xdc30de30f441f741
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/15+packedAt s2K4 (64+(h % 15)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffffc07ffffff03fffffe01fffff1ff1ff
  | 1 => 0xe01fe03ffffffe03ffc0fc07ffffff00e63ff8
  | 3 => 0xffe0003fff80ffffffff0007ffe03ffff83e3f
  | 4 => 0xffffffc00000fffffffffff800003fffffc03f
  | 5 => 0xffffffffffff0003ffffffffffffc000ffffc0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x82a8a182530a2248b00b2ca9648b4b550af0db
  | 1 => 0xb682ca968514443972c05522a9b39534661778
  | 3 => 0xc4da95250a26a892d5550284d5c926e6b83a2d
  | 4 => 0x171306362c58d12369a69b30191238b8f74036
  | 5 => 0x181c18383060e1c38e38e3c71e1c00c0ddad80
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaacc88aa000000eeaacc88aa000000eeaacc88aa000000eeaacc88aa000000eeaacc88aa000000eeaacc88aa000000eeaacc88aa000000eeaacc88aa000000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_43576
namespace PEqualNP.Outside.L_meta_43576
open PEqualNP.Outside.L_meta_43576.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1a0000002020026020ac000016141049044006041001fd10fc40fc41fe30bc40de30fd43ff42ff43fd42ff32fe41ff40fd32fe31fc32fc30fe20dc30fe42fd41fd20fc10ff41dd31ff20fe21fc31fe40fd21be40ff21ff30fc42fe10ff10fe32fc21fc20fd30fe43fd31ff31df31fd40fc43
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2003810a0104180000208000020009208002005e00300000818100000030020f0346242802e001810000300001c58500f88810201300042401f0000100015f5350b70801075944309e2a2215e500c3aa6210de54021cf98c813d54cc27aa819674c440aaa88619e400c2f0a0a15754c10bc282873d540867ea8984f94040ea98e215e53086eca2185754e31bb28e655d53906bca7905754f10ba28a417551ccab8a6a06790230b7a92213f54483aea298d754c41bca84835d53086f4a120f6d0030bd280435d518c2bea70857d4d109f2a6416c52443aa6288674c640aea9c43b840c82b8a7086e10030ae29a85745150a7ca9986710230af298835c504c6baa7905794c429e2a261b840442bca7a06710030bda82875d510c27aa99075544309faa2213d54c43aa6390d794c10af29e213e54c433e62205dd45209e2a2413e54086eaa2185ed4142afa9a813e540cbb4a0185714d20ec200615f5348370819857943319f28481775150ab8a6885794e21aea98855e508c2bca618ee10210aea9e8198400c2bca720ee94040
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x54020400103515110030d114931443915110030ca14840443185310210c694c40c83925110030e44c440443115110030cc544400c29a60900309558653c83185310110a6181311035151d0030d44c5500871551100308e181540ca54654c510c6544400c3155190030
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x510754c44044288b8ca620641c01493110110
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/29+packedAt s3K5 (736+(h % 29)*6) 6) % 46)
  | 4 => 2*((h/75+packedAt s3K4 (2673+(h % 75)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s3K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/1+packedAt s3K2 (147+(h % 1)*2) 2) % 3)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe03ffff01fff0383fffff83fff03fe00fcfe7c
  | 1 => 0xffc0ffffe07ffffc0fc0ffc3fffc1fff631f8f
  | 2 => 0xffff03fffffffffff000fffc1fffffff83e3ff
  | 4 => 0x3ffff8003ffffff00001fffe003fc03f0
  | 5 => 0xfffffc00000003ffffffffffe0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x29861811c5121480b2c53804a72132182c6e3c
  | 1 => 0x429221224324519405544a42c96514a9611685
  | 2 => 0x85084a4488488229502094a8128a495282a15a
  | 4 => 0x162cb389120edbce69b606229cf39063f403e0
  | 5 => 0x1830c30e1c70e3738e38e73300c20183dbd800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e0e0c0c0eaeae8e8e0e0c0c0eaeae8e8e0e0c0c0eaeae8e8e0e0c0c0eaeae8e8e0e0c0c0eaeae8e8e0e0c0c0eaeae8e8e0e0c0c0eaeae8e8e0e0c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_43576
namespace PEqualNP.Outside.L_meta_43576
open PEqualNP.Outside.L_meta_43576.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x217e51882fca110df54743be2a4417c54cc3baa610dfd5020bf2a0877c54ccaf8a9885f95331bf280657e54443bc87995f94630bea98417c53042fca1086fd0d42bea88657e50cc7b864985f94e20be28a417f51483be8798fbcc932fda8285fa20842fca0216fd0f42bfaa0617e50d0ebea6a177cc931ef99465de32cc3f44010774c730fd284835f53443bca720dfd4530bea9e837d53483ba64195f55032bf2a0417d544c2f2a120f750f32fc20221de318c2f8a6a05f94420bf298217d54482f8a8105fd5131dea1081bd540cafca4205714d42bfa82837c53882fca1a17ed4143bf29c437e53106fca7205f54643deaa663bf41106faa190d794f41bea9e817c525077aa810fe4c030dfa10817d52cc3be87197bc8621fd98261de538827ea8986f95021be29421f7314c6f8a0a0dfd4132ee98061fa30442fca1217790c43be29621df53442faa790fb48020bfaa663785050afca1205b14910be28a85dc318c2fea9085fd50219e2a2617f53482bca610f794f20eea1e617d52902fca01877cc631be2a021dc53502f8a4a1df14940fb90a437f5350bf0a0a1df54720fa988637d50906fca4217ed0240bfa9a217e51102fca7a0fdc4210df21285ef20082f8a6a17e4c320bfaa465dd4310ff261085f95232ee21a637d53903de84a15fd4f21bf29463dc438cbb8659877cc832be298433e540cbe88210fe4c020fda00617e53d0afea498de14121be29a417d5210ef8a818774c830df20281ec52442fca3a15fd4941df21a877e50906baa7105f94341beaa0617d5090bf681985f94a10ee194637e508cbf280205f14d21bea9c85bc43103f681905f55232dfa0c837e51887f6a090dfd4f10bea80837e540867aa9906fd0842fa28a85df53487be8698f7cc030bea8c217e530c6fea610d794c40beaa0437e53087ee8210df15331be282853e54cc6fca521d794e41fda00417f538837883207ed0210bf294857f52502f8a8995f54342dea10857f5150bbaa7a0fdc4010bf2a083dd53042faa1a0df54d10fd902416f52443be6218f710c32bea8c617c50486fea990df94641be29a837d52102f8a810f794c40ef990617d54882f8a7885f14930dea1c837c524c6f8a898de54332bf28083ef4290abaa6215f55221bf29a41f920083f241087d88421bf298857e540c2fea818ef90e40ef21c63f6411077882205f54e41bf2a263f75150afaa32177d0d43beaa2217e53486f8a4085f54910bfa9c437d53c42fea918ef95331bea9421de314c6fca9995f15320ef29843de304c3b886185f54221ba28a857f52c42faa9205f54e20eea1863ec21882faa4085fd5110be2a243de328c6fca9087e94332bfaa6617d528c6fca418df54420bf29841df5350afca3a077d0c32bf2a0217e5110efca3906f15121bea98837f52042fca721de94031
  | 1 => 0xe53443bc8618df55020dea0883dd438c6faa690dfd4f20df2a6417d548c3f041885f94f40fd900217d54c877e85215f54e10de2a261fa40102fca8986fd0e41dea1683de320c6bca6215f15230ee190637c548cbba65185fd5320eea9e41df430c3ba6218df55310bfa8a813d540cbf040085e94021bf280637e51d0efaa198f7cca30dfa0481fa10042fca9907b88620bf28883bf544c2faa0195f94f21bea90837d53042fca7085f14530dea1e85df314c3788520df54640bf28c817d5090efaa598fd44010bf2a4617e54c877e8620df94b10bea9683f930442faa6205f54732bf288437b5050efca9885f55243bea8e817b5050afaa010dfd5230bd284837c514cbbc86996f50d42ef984617d538c2bea690ef90541fc20061fa500c6fca7905f55121bf29061ed4210af8a2a06f50040dfa1c87f840cc2faa0217e10320bfa82637f54887f460185f14f21bf29481dd32cc6f2a018dfd4532bfa9c21fb40442fca5197b8c832bea96817d520c6fea4884f15121df210837e54887f661187e8c320df2a0657e541027ea890df14e21fc200417e5010f7e85205754c21fd184217b50486bea6a05fd4143bfa9841de310c3f081085f95231bf2a661785050fb8a690fe54031bf28863be431027aa810fb48421f710241fa30082faa118dfd4930dea1887dc5350afaa521df14f20bf28c877f5050afca8907e48110bba8a853c54442faa221ef50a40bfa8a87de53042fca0205f94c43faa08837c504cafaa920df54a20bf28643df31cc3f2a010df94a41bfa9a437e52042faa520df54031de2a2213f54442faa818f7ccb31bd286657e521077887207dcc631be29c21f441c86fea8197b08420f7904417c5150efaa510df15231bf298617c5050fbc8698778c930beaa463dd314c2faa1a1fed0140bf284617c504c6fca8195f94b31f7994657e530cbf0a090d714d10fc28285bc42106fea090dfd4d40bea8c657e52083b887185f15130aea9e417f544c37c82207710f31af29c417e5090efaa610df94231bea9c437e5410a7ca810df95031bfaa441dc310c3f4a010df14c20bf290877e508837ea8885f94b40bf29c85f741506faa5186f90a41bea96217e50042fca7885fd4943f6990657f52842fca1994f95320fba0e437c540c6baa7a0dfd4d41beaa4857e510c3baa720f7d0e30efa1c877f544837aa9905f54f20f710a437e544cbec6218efd5121ee29a217e52086fca5985f94632ae29a81df53503bc64995f94442ee992637f54042fca5a0fb90842be2a6435e53042fea9885fd4c10fd88221bf42506f8a8195f54b43fca8665bd42507bc87985f94410ef29885ef21086faa1195714d21eea1a65bd43106faa9906fd0040eea1a617d520c3dc42105f94631fb90c437d5010e7aa998fec8220be29a217e5190afea890df54620fc88
  | 2 => 0x8c000903502c02128000607e0540106c000082c011df0000602814038260e043008240b40c048000500601c021411a16c150049601019000140000a20803028027681f00401080c40c8001144501c005d40000cd30f9a100019014010c80711c10078a3000080181f0040b06c0009c0001001028070400501c1802003000041480200000008072a8520d8060000701402004000403700000000410d8070040100423000930000b62c2a514140015a234000dc0202401088163140138c010002c0103b03c9800400000000100200c23098190100213000368000001b019060600a0c401000151b8000240a020010006f174932c4010b00000c020000b094060203401c18048090200606c24028b50382c27c00004040040005c1408407bf29687fa20443dea4885f54442be2a221f741907bca7a0df54440be2a443f950907baa6215f54332fa908437e54882faa3985f54430bea9e85bf4310f7c83205f14910eea98817d544c6faa3a15f94910aea9821f610442faa6215f94020bf28e65dd53882fca720df95121fd884217950086faa9985fd5132beaa265fb20c42faa9085754e41dfa16837d538caf8a9085f15120bf290657e51cc2fca6205f55332beaa6637e50086fca5185754c40beaa0217e510cabca7905f54e31bfaa6657
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd500c6d963101109ed81521063f6550c43ced5040442b46150840a7593318c67761551219e597200435b31540318f992528c29e63906409b58854cc2d86050c319758c52506786055121a7593310c65d6394742ced9150cca3d6595032d654e50906d960cca32d614f504873860553319758e544426e6295110c754e411031e5454f208f992544425f6550c318f992530c63f6454332cbd5052442d86050e319e18152d0f586054c4097d8d52c427b6055331cbd53524435a53d0320da14a304425d63153208f19150ccb1c5490d30ae1814350ad963103209718d508863e6494820b658c408431d54ccb31c754c41102d86050f329ed81544c65f654c0308f191510826f65480208f990540cb1c5414d10ced50504867b6055132ced81540ca7960951219718d521075b53d41429e195304429d631084197597430ca3e6414810c7d53534425c635512197594430cb1d53d0840c754f4210b596014d1097997314c23f64546309dd85544ca7a60d5010dc1475050a5d63952218f993530865d6315120d64c5500c6746154d209d987548829d640c930a758c42906b46150a408f99742506776544010ced8154cc65e6514d21b6583320c31d54d0c329718d50d0a5d63d4a108f990538431c548c130b6583320ca5e6394742cdd0c5150a6f6550842c758c544c3386055032d5d4f5150a7461551209798c52c423e6494e219e98253c865e63d5310c7550430ca6d62150108f992544867a6014e218fd91534863e6494a10ce153304c25f6354b40da148404423c64540319758e54c425f6354342d694e509077351141429798e524431d544cb318f191524427a60d52318fd91534823d6595021a7590328c66f62551109798c52042d86050f3097596320c65f6355321a759331cc25d63951219e580530863f655044197d8d510823c6454d219e583548863f64549109718d519025e63d5021da14b104423f6454d109718d544823e6494910a718d401033b64540319718d54c865e65d0d319d984540825d6394321c794f439063e64d4a10c7d50534874f53149108fd915108279658c0209798f520431e5494f20c754d421023f6454632aed81421034f53d4910d694d500863d64148109798e5090a5e63d5221da14b404425f63546429718d52d025d6394820ced53504867860551319e980514ca5d63145209ed81540cad96310330b658332cc6b461508429798c54c827a6014c10d614c5050a5c6354b109e596100423d65908419e582534825e63153219758e52442d960cc931b6181434ca7960d52329798c530869d63d04418f590530831d5494c21d6d4c504866d6215031da14a204425e65cc93197596530431d5350842d514c5150b1d5454f20b618d40102b8644c03097d95320ca786054a319798e548865e6394d1097d8d548425f6355130
  | 1 => 0xc6796015031ba189100436852481108f994544425c63540419bd89534425e650c930ad18542d075953540219d58454082d86050c438f59053c867960d5021d654f200431c5450d309e59440083395410320c7d50534427565104219e181544cb5953840109798c540427a6015332c7153314c25e6395310c755043cc677654c4319758c548425d63d52218f59053c8368524c110c79525308758538c110d694e500871d54cc8329e18154c865e6590d30c755253c825c63544209e980520427960d50319b98a534423e6494d108f990540865c6550d32ae1814310e6d6295110d614f5050a3e6494d219dd95411065e6394a409e983540c65f6550c43ce951500863d6494a108f99053c86796014532d654f208825e6394d21c718d540cad960cca309758c540863c64546329798c530433a4314143c718d54cc65d63153219798f528425f654c830ce552500865d63d5220ae181439075a53542419ed81524425d631522097d8d508865e631512097d8d501063e64951309b189544425f63550209bd95320ca5e63141419e580538865d63947409e982544871f54d4d219758f520435453d45429e58054cca5d63d50108f59052c423c6454221d614c40443575314542c7951530871c544c5309758c54082d963881109ed95100425f63551219e58054086b8644c0208fd91500c75a32540318fd95401033554d0421ae181431067a60947439798e54486776154d20ad185425071d53d0b419e980540c69d640cb30d6d4c5050a9d63d06418f59253886d963882109e58251d0a3e64d4f109718d540826e62150109798e528426e6294910d314f524427960d53329ed95401025d6314b109b99452443696014910d314c524427a65881109758c54042776548421ce583544423e6414c20d694e30c825c6550d308fd954210a7a60947429758e529033b6055320ae18143d0a5d6590c319e583530869e63904408f59353c43595394021b6580310c35853d0110dc1445050a5c63551109b988540c63c64546308f592528c25e6514d109798c525065e6315032b658c400827860553318f593528427860548418f592534863d64d4f208f191534427960947439ed8153486776155120d614c504871c54d4d219758e5090b1d544c8329798f548827b654c0308f99454486b8644c110ce19150cca3d64949109ed81544825d63d5021ba18121086756114c209798e51d03583254031cd54441102b8644c210c754d42d071c53d0d429798f54c827a60d53329798c54082b8644c3209e983548ca786054d21ce191500c67561d50309e983540867b6054a31ba588400825c63552109798e500825d6510c30d694c40c823d6414e10ae582411033a54940219e980530865e63943219798c514823c6454d2097597430c25e6315030c754e431026f6548421d650
  | 2 => 0x2018154540700800004050042905000000000e8130140000c050a8090102f03c0401013120030341b00c030186d05800008220c03d034006600100c700000402006010020040002004004710140a000010108e01c021840300801028030881112041050000bc9a0040018800064000384201400064203400d000150ec010c81f01043000000b017000001740201c061c00002c000480304c000004901000380000080000802054150d02000032064060200000415150080080000c030440a0180001400004001400b0000d00c000180202c00144050846806c000b40a07c0b00400130930002a0082d004040000b06c1804c02008010047f0000002000000071081a01408000000380d00402014031001400000120040601b010014a73854141219e195204427860550328f59252082b464484219718d5190a5d63d532097d8d544427661d503097d8d524427b6055321c7152324c2796094d219798c540865c63549108f590524c66e6215330da884504863d64d4c219798c548823e65151309798e544425d658c430c7150534867a60150219e58253c873854d4121e610c400c35a43540319d185544ca766114c209e98353087395454021d654c200427b605512197d8d544825e63948209798f540c63d6494d109758e528425e63152109758e500835853d01409bd89544c7595354241ba580218829c6350a409758f54c433454c85219b58a534432c54149108f99053c829c6350840c7551530869d64cc530cd9085150a9c644c030d690d50cca3e6414b10c714e40503596094f2097996434ca7b6054b439d58754ccb5943543329b18953442d96388020cd185540866c625513197d95310c69d640c831e690c40cc25d6395131c755343cc72c54d4910c7153534425f6354640d6d4f504867a6094d219758c520425d631414197d8d52106d9600c6309e983548867960d52319798f540427b6548020dcd475050a5f6355132d6d0c5050e3e64d4f20c7150324c27a65d01109ed81544c27965080109e594400c25e6510d318f590530863e6414c219d587548823f64542218f990524c75953440109d98754cca5d6594c21cd50c5150ad86050d308f592530
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2530ea008403024001880000018655160ccb31c92a6312200841d76153314c28c3a2c029a218655160cc832c2aa630a8421519740c9500c70c2a0c0a1a618554c6150840c92c629440884597614c404428c3a2c129e414c1c14314542c30c6302a8196186318154cc68c382a821865461c15410f3183aec2a064984597694c40c8324b18a4202218a190524c110930e8b00621849874583320c28cba662a80638554c6150b41
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc18188755160cc832818865d331540318188755160ccb31818865d03254031
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | 2 => packedAt s4K2 (i*60) 60
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s4K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/228+packedAt s4K5 (17928+(h % 228)*10) 10) % 664)
  | 4 => 2*((h/228+packedAt s4K4 (20482+(h % 228)*10) 10) % 539)
  | 3 => 2*((h/22+packedAt s4K3 (1225+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s4K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf01ffff80fff8383ffc0f87fff07fe01e0fe7c
  | 1 => 0xffe07ffff03ffffc0fffff83fff81ffe7f1f8f
  | 2 => 0xffff81fffffffffff000fffc1fffffff83e3ff
  | 3 => 0x1ffffc003ffffff00001fffe003fc03f0
  | 5 => 0xfffffe00000003ffffffffffe0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x94c30c88e2891580b2d43826a7433218e06e3c
  | 1 => 0xa14910112192109405454880c94914a82d1685
  | 2 => 0x4284252244244229502095481294495302a15a
  | 3 => 0x8b1659c489075bce69b604629ce79063f403e0
  | 5 => 0xc1861870e3863738e38e67300860183dbd800
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xece8ece8e0c0e0c0ece8ece8e0c0e0c0ece8ece8e0c0e0c0ece8ece8e0c0e0c0ece8ece8e0c0e0c0ece8ece8e0c0e0c0ece8ece8e0c0e0c0ece8ece8e0c0e0c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_43576
namespace PEqualNP.Outside.L_meta_43576
open PEqualNP.Outside.L_meta_43576.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x430000020000021810c00001040940440570c2fd31ff31fd10fd32fc31fe30fd30fd41ff40fc40ff42fc32ff32fc21ff30fd20fc20fe21f721ff20fc43fe32fe42fe40fd21fc10ff43fd42fe10ff10fe43fc30fd43ff21fc41fe41ff41fe31fc42fd40fe20f421
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc817c5150fbe64195f54e42bf29e21f721082faa8887d08720bfa90217d53102faa810fd14c21fb90c817d520c6fca190fed0330de2a2657e5290afea818fd54443be282657d51d02faa8085f15032bfa9a83f431c86fea790df15132be29e41dd320caeca2185f94331fc20641f641086fca2185f14532bf284637f53086fea7887d95021ba28a657c540c77c87215f14a10bf290657c54c42faa7a0df55331be28287f721c43eca2205f54b31ef98061f840082faa7887bcc932fba0a83f641107bea6a15754e41ee98c617f5050efaa8187d50b21bf294217d544c77ca9885f94342fda06417e54443f2a010df95321efa1c61be4310afca0205f15230fb08221f441086fca820de54241df21e835e539077884207d94430dfa18877d53902faa5885fd4532f6990657d510cbe843207dd4021fb19643fb10842eea2997d94620bfaa2637551102fca690fed4142bf28043dc434c6f8a498fbc8220bea8665f7314c7f480205f54231bea8881fb10442fca7a15fd5321bda8265f443c87be63186fd0941ec98061f742c86faa720df94c30fb20e217d51d0fee43104fd5132bf29683f541c86fca618df94332bfaa4433d548c7f680105f94030be29e21f431087e843885f15210bfa9a21bc54482eea2907e88210eea98437f54042fea2905714d40fa218437c538427ca9887554c21bf288417e52087f440885f54b43daaa0437652087f681205f14520fb19043f732c87ea8410fe4c030bea9e817e52083eaa3995f94620be298435f5350afaa9185d94620bf290879d4310fb887195e94021be292877d52102e8a2907dc8540bf290617e51d0efaa690dfd4e20bca80437e5090be8a010fd08620be292217e54083ea8210df15121bf28c85f7210c3ee8790ef90e40bea9e857f52842fca810fecc320ee29a81f642c87eaa610df15231bf2a4417d54483f661187b48421faa8643f721486fea998efd0e43be2a661f541107b8a6a15f94621bf28441f531c86eca310df94e20bf29661f830842fea9995fd4142bfa8a85dc430c3f280205f94e41fb98e433f544c2eca221df94641bf28c817e518cbee42085dd4542bea94837d5010ff060885f55020fa10a81df438caf8a2a05f55321be2a241de304c27ea8905f94042be296217c53502fca7a0fe44010ef98863bd548c7f420087d08430fba1843de320c2fea690fd90531ee988637e53c82fea6a15f95330aea98437d518cbb865187d48421dfa0481f541c42faa8197e94021be2a043f250086b8a6a17794c21fba1043f631c86fca321fe10030fa988437c53882f8a8085f95131bfaa061be42903f660106f55021bf296637e51042fca6085fd4943deaa6217e518c6f0a0997d08410bfaa065f653c87ee6210efd0641bf29021fb40502f0a0a1df94a30fa28a65f432086fea9185fd5121
  | 1 => 0x4214c2f8a898df95130fb21e437f514c2fea2a06f90942bf288637f54442fca1086fd5130beaa2617c54887e842205f54a10fc20221f840843f6411077cc631bea8643de314c678a8997d14f21fda0421f532087b886196f10e429f2a4637e5110bec8610f7cca32be2a4657d5090fea8318df54830bfa9261f650c86fca2207dc8740fb10843bd42d07ea8610dfd5020be2a641ee4210af8a090fdd5021f799465ee20483bc64996f15130bf29c217e540c2fea7086f95021fd284637e5310b7a84215f54241afa9a81bc43d07f460185f15332eea18877e53c87f4a120f7d4d40faaa043d653087ee21085f54221fc18641ee320cbf680886f10c42fa2a6437f544c3e88390f790c43bea8e41fa20083eaa010df94630bfa82657f524c6fea8907d50510bea90877f54c83e88410fe0c020bfaa6217d53482faa1a1df54a31bf29483dd300c2eca3a177d0c32fd902417f52c42b8a6905f54910fca84637d518c3ee6318f70c830bfa9a417d53842fca3a15f54a20bea8e61be41506faa2215f94341fba0e43df4350efca4206fd0a42bf298877d5110efaa3a15f94c41bf29e81f753c86faa8997d14321bfa8a877d53042faa018df54f20bea86837c52507bca7887dd4542bea8c857e52902faa990774cb31be29281df324c6fca021ded4142ba28a857c504c6f8a0a0ef50941bfa98417e50042fca6196fd0b41be2a2617f53502faa7197d94742fb2a6437e53886faa7185f94a32efa1c877f54cc2fca2196f95231ee99263f653087be6598df54d10bea8c21bf4210afaa5185f94910fb28e657d53882faa1215f54b40bf294877d50d0afca8205fd5210be298217f54087e88590fdd4c21be2a663f642086fca5a05f94c20bfaa465dd53c43f0a0a1fd94443bea9883f721cc3bea6905d54430beaa487f950906f8a6906f90d43fba08437c53443e843985fd41219f2a0437e51086bca7885f95320fda82877d540c6faa9885f55221fd982617d508cafca221fdd0641fb90c617e509037c86205f15220beaa421bc43903e8a2a17b88521dea0883fb30843f0a0a15794c21df20281f531442fca5a1d754f10bea80437c514c3eaa790df14930f8a8043de53906faa5a0ef50640f6a1085fb30443eaa2186fd0040bf29a417d51ccaf4a120df15110bf28883f721c82f4a118fd94021fa880217c5150bde4210dd54732fb20e437d52cc3eaa990cf15120bea80837e5390b7e82205f14f21bea80857d53082faa420df95210beaa6657d51083bc65185f94232f329043ef4290b7886a0df94d10faa8c417551883de40105f55232fa10c617e53102f0a0a16e50040fa108417e548c7b8a6905f94343df210817e5210bec62887e48020bfa9e41f840cc2eaa221fd94821beaa2437f52442faa3105f94c21be2a643dc438c2fea710df95121bf29
  | 2 => 0xa0220209c0104a0002005004000081d8d20000400aea008460082e0b8040000e1a010130082e800000328680a340060184a0280001800060000201001050000083d8120000003832d901601008038002683c18806008ca0b0080eb349c8320007800880008080687e0000e00866068020000000004088180000a7e8000013717004018420004a000f61a044660600328822800021d8000b60017c140380602e0400e188107b00000042042b001016050020480404802010420115a0400c090000002a3683003862020000889a1780e0001c008041801edd852020060900a070360c8160004401000001e81a0080708200000309180385401004209e02d0000708408028808b00e9e4270860084a0b89c020484287e0080a000980000000800060324401a050000100608000020060007c0080011812048041f0780118a0a83e011440005a27df54640dea18873c544c3de84a15f55220bf2a6637d54cc3f680185f54032bf2a2657e51cc3eea2995f55242bfaa441dc43cc6faa2185fd4940fa98e217e51ccbee42905f14d21bea86637d52043ec8318df54c42bf28065f754c86fca721ef10c409eaa6217f505077e83207dd4520bb28881f631086fca120f7d0d31bf28041bd41103ea6218fdd4321beaa4837c538877c86a0dfd4131bf2a085f432c86fca121fd14520fb90a61df430c2eaa3a17d15021bb28e65f9208437e8220df94221bfaa4637c54083ee42207d50f21be29a85ed20083ee43085f95120fb880217e540c6faa321fed4132ef98861f721443e842887e48110ee988617e54042faa521df94841dea0081dd53906f6a0a1fd08740bf2a443bf544cafaa610df94831bf29621df43cc6f8a0a15f55240bf28063ef21887e842905f15030bf2a665f8504cafca3905f54f21db2a0437c52043be61186fd5120bfa98217e5410f7885207d8c710faa0a637f544cafca1187d54440beaa4637e548c2fca518df94041fb20a217e540cbec6218df95232fa996437d538c6faa510df54e21bf28e817e54c43ee4310df14c20afa9a417c53506fea4a0cf55021bca8463f732086faa5207d08610faa8e85f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x52042766294443cd55131086d56314021f4545300c2756115020ce153504cad86350040d554d50086746114910a718d40102d763508219dd9542086756194f20bc18143c865d6315310dc949500867661150209798e518829c6350842c7953318c67b6055121aed85401025e6315020ad984435073754c85309e181540cb385414132d554f31086d66315021cd951410873a5454231bc18142086d6639053197d8d54486d76355321dc505508c67b6055032ec55150087955454c21d514c21502d663d5021b518532cc6776154a43c755043cc6f36050f219798f54c427b6055120d6d4f5050a5e63150219b189544425d63946209718d54442766194e429d59631086f2608c5108f590530873564946209ed9510042766115230c7d50438c27a60150219dd8553482b76454321cd18554087e021480209d58654486b86350040a798e41506b86250040b658c400c2b56408510e6191300c27661942329718d540836452085409d195414c7713154021ad99050087b15150040e6d814310ee662d5021da14920443724154231a7191320cab5648c5109d984540c67765484218f59052c425d63d5320d510d510c27561d493097594430cbd1310c110d614f204823f6454d21dc982510c2f26110110ced5040c82f26090510cdd5321483566194f109dd94211025c63553219d5865090b1e5454c219d584540cb5753c85209e983540c67a6094732ad584431035553504219758c540825f654c8329ed81534827b6054f21ae982415073554d4c21dc54d50086f2610c1109bd95320ca7565c8430cd90d511023d6414c20ced5040cc29863500409dd95411077141540219e583538875553c8710cd98654086d56110c309758f548865e63944109e983530427b654c0309bd89534433664946209798e544825d63d50218f99353c423f6550040c7152324cb356494732ad590530867761548309d98454cc2776154b40b518d50c86b96010c408f596540867a6094742dc982511039b644c0309d594210c2f260150219d9845050e5f63551309d18552d0ee662d4f219e98354cca3d6414f10cd55231c425c63551219d586508ca7561153309798c54c42d66314c219798c5204335544c710bcd8142086f161103308f592510c6756194d21b998854c865d63d4b10c715353483555390421dc144504cb5153540219798f540c67a60d50109dd8552042756115030d994821c43a65494821b5d8d42c873a5454021f494e500863d6494d20ce55250087595354241bc982310867561953209dd8552cc23d64d4c10cd150514827a60d4c218f19153083735114132b6d95300c2da63c4210cdd50514cb566194c21b518d420865e6314b10d99482104277654c821ad596540863e6494410dc9825110e746154a43ad19150c875853d01408fd9152443575308540
  | 1 => 0x86b7644c821bc18132086d86348110ec95250086b960d0440bc18143086f06054f21dc547400c3e252940218fd954310e766114e209e983538865e6514d209e582544ca776155132b558e41c86f06055321d598e51883b32150040cd95321c43375414520c7952530863e65151208fd91534833554c8710b5984434c7365150440ae58042103155454c21d5d4c5150a3c6454d10a6191300c3595394241cc55150086d661cc931b618d20082f16090721d5d4c514827a6094443bc580530863d64d4c219dd9721103716094443f454e500873454c8530bcd8143086d56594c219d5845050e5c63543219bd954210a3e6414c21bc59650086f160d50219758e510423e64d4e219d98754ccb724154021b6991300c25e63d5021cdd50214c35453c85209718d52102796094742d558e51882766115032dc1445050b5a53540219718d50d077351d41429dd94210c37260947429dd97210c2b86050941d554f50086f260085108f99253482776154b438f99353086f160904219798f548869c63509419798c530866c62551319d98454042b664d40219d587548827960d5332c714e4250a9c6350b4197d8d52103395410020bc584400c2766114c10d5945310c2b5648c421d694e500871c5414d209dd855210f965494c219bd95200831d5310c429e596100425f6355132e610c400c2d563087109d584535035453d4542b998b54c867561d53329d98654c82756508410d6cc6508c65d63148109d185528c27960d5232cdd53514836752085409d189510c23c6454910bcd8132c867661d49439e980548c6746154d20ced954010356534c4219798f548826f6255110a719132cc6f26014021f194e52086b860508428f99352c427661d4e20cd95141c433b54d4132cdd5021483d3214c0308f19150c875753d45209dd8552102f0604cb21cd952520873954542318f99251ccb3454d45329dd85528c3366494732d694d509071d5454c21d5d4c21482746154a409b988540c25f63540429e98052042f261881108f191520c2b564d4c21bc58231c867b6055131dc1475050ab66414c219e583540c63c6454f219d584548831d5410c32d554c21c427965100209d185544cb1c548c1309b588540c3d253540219d18554482da608c5319ed81534867665c85208fd954210af06148210d614c5050a5f6354321ce153304c31e53d0641d5584535027561d4943d554e520873b41942419ed81544ca756115130d6d0c5050e7b6054f41ce551500867b654802097d95300c25d63d5310d514c5150a766115130cd150514ca3c6454032dc9845050eb76454f218f59251ccb59530c210d594d31c425d63d52209d9845350335548c4219d18552d025d6510c308fd91534423d64d4f10e9552520873854c81209e58353086776154910add9132c867661942428f99
  | 2 => 0x61548309d1855210e756590421f4945300c3b25454021a7d954310fe2525402197d8d544827b60548438f19153486f26014c2197d8d54083986350040a7992314c7b02150040b518d42c86766115030b558e41087954310c21b698f104427a6014c21b518d54c86776154d2197d8d544425e63d4b10d9148214c3356494430ae1814310f395494231ad18542d06f160906319d59431086756194e42bcd8153c86d763543219d587540c25d63d50109e997304427a60d50219d99443c863e6494620ad191320873554540218f99054086b6648c421bc582414c6d86348210d694e509063f6454e10d5551530867b6054c42d994b21842986050c439d994430873654087109d986548cad563085109d586544cb1c5390140b998b53086786055331ce55040842796094443d594f21c42f2608c721cd584544c3575454c21b658e300c371611414397d8d524423e6414f109e181544c7566394440cd55021c423c6454e10a7191300c3715454021d514c214835b530c3208f592510c3355494821b6191300c35453d45209d98a510c27661d50308fd9541107d15354021d5d4f215027561153328fd9150cc71f6550c43e61814310e7960d5221e550d5110e5e63947429d19541443345408530dc58251ccab5648c721cd986548c7366115130ce95250087954394443d5d95530865c6354042d6d95300c2d8624c0309798e51102e76250c21d6d4c5050ad66390721b5584438c2f260907219e594300837260947328fd91500ca7661d52208fd91530823e64d4f20ad5844390359530c0209d987524c2756194d209dd8554486786055132b558e41c427661d4810d598453502756114e208f994544ca746154b30d5d4f5150ad9600c830d598e51d0a9f6150c43dcd4d500867561d4940dc580514827960d5021ce55040442b864481108f994544c25f654c431ce550400c3726094620ce952508c65d6594c219d586548ca756114c209798f54042f160d4c218fd9153c876452c85109e195204427965100309d185521025e63d53209758e51d0b7354540218f99353042b86050b418f59353886796014c219d994214831f54d4d209dd9510043d0214c030ce9085050ab86448020b9189430875953940219e99740443355454c21ae99310442756510f2197d8d54c876662948219d98653c831e5494f10ad990540867b6055130bc983540871d5410d319d584548c2b8644c0309d58654482d563150219d1895110f735114142d9d48214c3a54210821cd153214823e6414b10cdd53514caf360553219dd8552903954310f21bc582310867565c84409e983548871d5494f10e6d8d40103b14110110dc147504cb1d5310c40d5d0d510c37351d4132cd951418c63e6414c20ad99231c866f62551319758e544823f64543219d98454882756510421ad19132c
  | 3 => 0x881c000110080102001020640782c09d3018c002f824004110219b0840106026240000081403009030000080000c00010000c8000340b928090793200c000c03b0000c07857000220000a0003c0a0045541600000014700302f00000010000043d008040b4000081b32c150040607c170002b0005605c04598000002a0b8060109201c3300000028030185d0680508c8a0c804030111683b0093c00c00004440a8063dc00000120100003c3304c0003809158040000603c070000c004020040101c0301c06001b202800000100c9e10011900c640b8002300b0000019002000021dd9501c020dc100082b1640e0f81703800080240680101c0c008002b40001ce59c47d2800400803008ad0401a050074f8400380c000143a4031a4070440a1000b00c910080000c000003f060000040600c000041f0000100801020000ac36058000140ad5185530872c52509419e580540ca5f63552109e580548c67665c85109dd8554482b564d40219e58054087736554021c7d5053482f3604c821c7d50438ca7a60951329d597320877252940219e18154486766294440a71814310e7661951208f59352c42d96010c30e510d414c6d8604cb31c795153c435553507108f19150cc67b60553318f19153483556394742b558e41442f06050b218f590520423e64d4e20b998853087565308710ad19153c875853d4142b6181320cad663d40219d594211029d6490c43ce90c5050e3d64946208f992544827561d4e20bc58021842766194d20c755153c42f260904219758c52c431d5410c309e983548ca3e6494430a71894310e3f64548309d984530833664944309ed8154c86796094732d514f215033661953109e983548c6b664d4c219d98454cca5c63551209dd95310c73b54141328f992544cbb25150040b6d85300c25e6394d20cd15021482786054c429e583548c6786054f219d18951102d66390421b61814310f3554d40219e1815210e3d64944108f992544c2b96490040b9988540865c6355210b6583310c3b15494021b598c500867565d08218f992510c7c5320c8219e18154c865f6354341d554e41c425f6550c439d19531442b864482109ed95401033554d04219e18153d063d64d4f20b6181324c6b56408710a7191324c71d5494c21e555253086b661d0941ad59050086bb655004097997434c6d563d50219b18953442f260d4c21b998853c87595354021dc544400c25c6354910bc580540866f6548421d68c8504ca756510c219e980540cb7160947429758c540871d5310f419e18153486f36050b21f154e52087556394440ad59231c43344354440d514c514827661d4940cdd9554087566194e419758e511034c524c9319d986544cb565394821dc8c550086ba64c4210cd15351482d563d40218f59353883965454c21d654c3044274
  | 4 => 0x126000620481b0640200800020000a00a0180100dfb004001d8080453c00c1909c3d0cc06000080016a23c020d06c11c16004040bc0201800004020080603c34000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2c0040a063000a001812200c2108080002c843808c4849822500015e08120001c1812c20051870550434c6a8ba84298061a45c4644c030a30e8a9860885907050e5110e1abb0a810a61345c4644c030a30e0a988621518735504008324290c0992634c5d42150040c50c829240885187454c3008314290c0a12838559153d4021d24e231a80205907050c4308749388c898061a49c46050c43a30e6aa08108495711814310e58b88c6a00814c5d35354021d22e23028621d847250c430864c39ac021081431c95410d31a2aeb2a2a610d317595150086a4392a618221681c14210821c18c629284a0e156458e51882a8b9ea8a80439458d6094742b22e221880186486314920442a8baca6a8043a4192514c030c2acaa188610e155458c21c428cba88620061611d1320c821a34e9a9861906906308540103892a2a6a8043701c1320c821aa2e1aa2a610ea06208540103483264298061a418f2150040d80c410a601871043544400c28c382a621e83155d85308540aa2e720aa010e9064085300c388aa2a6a8043a81902148020930e8b0064187115454e500868d386a821c651c5d46050c21930e8b0662185187055043cc718aa2c1a9843a418e5150040d2086b088018584735084208748b88c6a0081641c14354443a62e918aa010d907050c43c864c39ac1a0881469cf5410320934e93226018690635454010318aa2c118843c45525354021d80c610a40106155458f5008718b22c128e65a4191514c030ca2a6b048210d1870550430cb0cb288620061461cd5410110c18c82926498e156454c21c428c3a2a6184214a1c95410110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x33400004002a11859c4644c0308918718c215004089187192514c030c1175190214c030a11859c46050c43911851c14310c21c11651c14310c218918718e5150040c117518c215004089187190214c030891861c14394443a11859c46350040
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 6 => 2*((h/28+packedAt s5K6 (672+(h % 28)*6) 6) % 42)
  | 5 => 2*((h/261+packedAt s5K5 (20007+(h % 261)*10) 10) % 741)
  | 4 => 2*((h/313+packedAt s5K4 (30172+(h % 313)*10) 10) % 794)
  | 3 => 2*((h/44+packedAt s5K3 (4459+(h % 44)*7) 7) % 91)
  | 2 => 2*((h/11+packedAt s5K2 (720+(h % 11)*4) 4) % 12)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffe03ffc07ffc0e0fc3fffe0ff83fe003f9e7c
  | 1 => 0x7ffc0fff81fffff003f03ff0ffc3ffe38e38f
  | 2 => 0x7ffffffffffffffffc003ffffffffffc0ffff
  | 3 => 0xf80000ffffe000fffffffc000fffc003ff03f0
  | 4 => 0xffffff00000000fffffffffff0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x31298644714495602c0b54e893a272181b8e3c
  | 1 => 0x554292c890c934e50215d13984e634aa38a285
  | 2 => 0xa08508112212000a5440024229088950c0555a
  | 3 => 0xc5162ca24483a6b39aa698100e7310636d03e0
  | 4 => 0x61830c3871c38dce338e39cc0402183b6f800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0fae0e0c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_43576
namespace PEqualNP.Outside.L_meta_43576
open PEqualNP.Outside.L_meta_43576.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904001ffd5003fd31027f14009fe5200ff04003fd2100ff88403ff21007f4c009ff53007fc8007fc4001ff90803fe41007f8c807fc42027f94005fe5300ff08405fe43027f54809fc5200ff10403fd51007f08003ff41017f14c01fe2001ff90005fc3000ffcc403ff5101ff50803fd41017fcc805fc4300ff44009fd5000ffc4007fc5400ff84003fe5100ff8c407fd4001ffd0c01fd20027fd4803fc51027fd4007fd4301ffd0007fd5401ffd0803fc3101ff95005fc32007f4c805ff30027f54c01fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x84003bf19130067f8c690047fe548800d7e3264006bfd963202ff8209002ffd614803bffb0a6402bfd8130017fe629900bfc534c80bfea844022bf5963203ff8a21007bfd424c83fffa82641fff14132035f8cb9005fff414c00bff32c6003bf99230037fc851903ffe218802fffb0a6005ff8812010dfac91908bfc508c811ff2984006ff0863202ffac91004ffe51c8041ff8846402ff8c63202ffe811800bfc318c83bee98a6405ff0c12002ff82190016fc658c033ffa826005ff0423001dfcc99007bff404c80dbf32e4006ff8c93205ffe829002ffd214800bff9044002fecc130107fca31904bfd528800dff304641aff1463000dfcc21001bff608c80bfe1864005ff84220017fca71801bfd21c800bff3244004bf9963009ffe839005eff614c00bfeb0c4000ff9813202ffc8110083fd418c805ffa9a6401bf98520075faca90047ff428802ffe20a6001bf18632037f86519063fe544c03dfea02640bbf58a2002ffac810017fd108800df61946400afd912002ff8ca10017fe650801ffea8c4019f754d300c7fec89801bfc424c823fe2a44000ff4c1200c5fec89803ffe41880237eb244005ff04020037fea51901afe628c00dfe9964002ffd0e32037f64110002fd628c00bff1004000ff4c3200effc429903ff9108800bfd0844002ff8ca3002ffc209800efe6408033fea926019ff541300c7fe849801bff214c80dfe9084006ff5872002ff8601001afe6208017fe98a4006ff196320bff8c29800afe634801f7eb0c4001bf1853001dfcc910017fe3088043fe204640bffc41200bffa2098017fd628c005ff98c6016bf597200d7fe4318067ff654c00fffa08401dff1053202ffac91803ffc518800bfd1004006ff0852002df8c21007ffd524c827fe98e401bff90a30017de651902ffc314802fff10a601aff4863005ffc6290063fc544c00d7fb246405ff90130024f8ca9807bfe544c80bfe1846005f7cc2300bffc8298036fd6448035ffa0c6013ffc43200fffcca99003fd32480097f32a6002ffcc9300cffcca9801bfc21c800dfe3046405ff4c02002ffca098016fe6088005ff21c6413ff0c72009ffc6390077fd104c80dfe2926418ff9913010ffea919043fe538800dff2946400bfd8d200fffaa09902ffe514800dfeb1e4006ff997200bffe209806ffd548c001ffb126006ff909200bffac29800bfd438c805ff18a600bff505200c5fac898083fd108c80ffe988401dff8413202dfec698017f8308c02ffe90a6005ff192300effe8299017fe304c00dffb1e4005ff14130025fcca9901efd610803dffa126406ff90b200f7f8a89901bff61c801bde3224005ffc40200effc8299077fd514c80dee1926413ff5072002ffec81001bfc210800fff2884006ff908200bff8a29807bfe404c80d7e31e4007ff0c420
  | 1 => 0x7fe514c805ef29a601dff50532047f88610017fc404c00dff212640affd4c2002ffe811000bfd434c005ff21a6000efd912002fda4010037fe544800b7fb184000dfd95300e5facb180027f654c0013eb2e4006ff9932002ff8c710033fe634800def9946405fbc8020107f8a31901bfc52480077f3226002ffd0d30025fccb19003ff6348017fe20a4006ffd9320037f8841004afd658800dff90c4005ff98e200cffca498063ff544c033ffa92601effd91320affca990017fd6388021ff994401cff54a3009ffaa39003fff318803f7fb2a6402ff0c93005dfec290017ff500800bffb146002ff54d32035fcc51901bff2048027fe20e4019ff14930017f88718043fc538800bff0824002ffd4e300f5fac899037ff424800bffb2c4002ff94e3208ffaa910017ff308c031de3226006ff88720017de649906ffc428c00bff9004002bf98e2002ffa8010012fc654c00bff080400ebfd95200b7faa190067fc654c03dfe202640dff5912005ffa2090017fe40480075e3226005ff1962005ffaa29002ffe21480037f30e401fff19532037fe8590017fe10c8023fea144017ffc853002ffaa010056fd64c8005fd984600bff9052002ffea118017dc304c013ff2a04005ff48020015fcc790017fc658c00dfea964006bfd972005ff42090012fe65c8027fe8864006ff1482003ff88210002fd63880077e3224005ff9412005ff2209007fff654c80bff2064002ff50d3202ffaa11807fff524c80b7fb24600dffd912000df8c29901bfc324c831feaa26005bfd9620037f8c91902afd6508041fe0846405ff9902007ffea310002ff604c80dff30c6405fb8812003ffc8210016ff650800b7fb084005ff943200dffca91806fff428c00dff1084005ffd8e20037fc6510006fc6148001fe3126018ff10930097fea71001bff4208035fe20c6018ff5093002ffc609006ffc548c017fe28a4005ff184200eff8c29901bf9200800dfea904000efd9130037fa431900bd8304c00bfe8804010ff10e2002df8c610073fc528c00dfeb046407ff5442002ffe6110016fc6588013fe2a04005ff9002010ffaa91900bff324c80dffa146405ff8c3200d7faa31807bfd644c80dfe214400cff94d2002fde4110017ff50880015fb226005ff842300f7fea899017fe500800dfe31e4013ff147200bffea29807bfd544c805ffa1a641affd4630025f8ca90003fd634800dffb0c6405bfd8e20017f8869906bfe418c029ff29e4005ff442300c7fe809806bfe218c0057fb126402ff8c93002ffca11001aff634c8077f3246402ffd4d30017f8869801aff64c800bff204601dffd453202df8c099012fe6548031fea026019bfd9530017fe609900bff314c0017eb1e4005ff50220017fa631900bff304c00dfe2944005ff8c02007ff88310063fc644c00bfeb
  | 2 => 0x20037fe6590017fc500802bffaa64006f78c932037f88519017ff658c00bfe30c4005ff9863002ff8c318017fc304c01dffb2a4006ffd4b2000dfcc319017fd630800dfe1964005ff5863009dfac390006fc61c800dff31e4006ff99232037fecb90006fe614c0017eb1a4005ff10020017faa718017fc628c01ffe98c4021ffd0232037fca41001bff658c83dff322640dff9912002dfec31001aff618c81bfe3224017ff9853002ff8a11800bf8304c00dffa904006ffc8520067fe6490077fd614c81fff18c4008ff90c2002ffec610027ff4308005fe21c6402ffd4e3202ffe211001bfc218800dff30e4006ff59632017fe631901bfd42c8005ff984640fff0c62002df8c310016fc648c00d7e3126005ff502300eff8209900afd638c00bfe2046006ffc872006ffaa890087fd408c813fea184006ff0c820037f8c390003fd328802dffa864006ff5923202ffacb1803ffe518802ffe10a6010ff90e20037f8a590047fd4388017fe30a4002ff4c530017f8629800bfc304c805ff21c601fbf59532067f8a69006fff548c045ffa84641cff94a300effa429900bdf314c82bfeaa64001bf98620107fe8319012fe658800dff9084006bfd8720017fa8718053ff30c801dfea92400fff50620017faa719073ff528c00b7fb204002ff0ca30007fac09900efe644801bfea124005bf1902009ffc839001bfe4288005fe9926009ff5502001df8c89901bfe3248005fe29a6007ffcc4200bffaa29801bfc424800dfeb2e4006ffcc82002ff88110017fc640802bfe2a64012ff54e20037f8c31906efd648c00b7f3046405ffd8420017fe651802fff514800bfeb284021ff9523202ffeca1000afd638c80bff3246006ff94a2002dfec91000bfc308c80dfe326400dffd0120017faa698083fc418c82fff28a6020bf5863202ff8a11003bfe654801dfea824006ff54a32037f8a51901aff63c8005fe98a641fff595320bffa829804fff51c801dffa9a4018ff9093002df8c31808bfd508c80b7fb2c6006ff50820037fc659005efd614c019fe21a4015ffd032005ffe6290047ff4388011fe298400cffcc12002ffcc310083fe108c8057f3184014ff10f20037f64090006fe618c03d7fb226421ff90232037fec919017ff648c01dfeb2a400eff1952005ffcc29000bec324c80dfe10a6402ff8c53202ffe601007bfc644c80bfe318401dffc4132017f8629905bff53c800b7fb0c6003af19120097fea510083fd518c80dff1904021ff1523208ffea91001bfe218c801fe302640dff15120035f8cb19017fe610801dffa824000ffd8132107fc831901fff51080017eb184002ff90d32025f8ca99017ff400800b7e31c4006ff0ca2002ffacb10057fd40c800dff2926405f78c13006ffa809001bfc65c8037fea146022ff94232017f8a71807
  | 3 => 0x17488ec0180009194082763093c00070018b43104e00004eb0c60882a018069f020e201000004018e6001592b83e080062f42206000048006522040476028001f814060002e00007812028860e0040d000000340602a0880ce602c1482c3800800800002380b808010020080a6c01223020748f711004010006cc9c01000228020b00e081060202a408083e0028e00a018014c8260000e00818a910a12808a387c79800070140000c001200081e9931001808008000e85c0000c000160101a000001c8022f8e4020340d000000060180c6e03a0081a6a0026d84c6d8243985a050001226a0129c0801a4b00020000000040006e01806020820b806e892033802008021a81a1c8500007e0fb94030002681201d5000002009da3201c08866028020180a0000007804000620d9300b0062a8040002e000080000c0a8180c85e0a06e000000300e9987a0280a0000c0101a0b81403032010021f0000581ffe31080017fb126014ff14f20017fa6318017fe508c00dfe216400dbfd9120077faa690076ff614c805ff29a6000ff58930037fe4319017fc504803fff2826406ff4c82002ff8211001bff328c805ff18c6005ffc423002ffec318017fc404801bfea1a4005ff0413002ffccb10077fe614c815fea984006ff99632037fac990063fd644c01bffaa24005ff0c22009ffe6390033fe4348035fe10c6005ff143200b7faa790037ff434800bfe2064009ffd5020017f86318017fc648801ffe90c4005ff98a3003ffa821001bfe52c8033be32a6020ffd463200dfcc29906afd618c0057e31a4005ff4c22002ffec91000bfd328c01fffa0c4006ff5863202ffcc610067fd654c0337eb2a601dbf5853205ffec290026fd640802bffa1e4006ff9492002df8ca10012fe65080177eb0a401dff14532017fe871801b7d65c801dffa924005bf982300d7fca31800efe644c80bffb0c4002ff14e32037f8649006bfd418c029ff21e4002ff94d32024fccb90057fd43c800d7e3246406ff50a32007fcc498002fd608c80b7f3004005bf192
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf40d953002cfd72d8d2002edf7358c20004ff7558a30006bd61d9130036f8205823201cfe7458e2002cfc7058c2000cfe71d813212e7e4059720004fd74d8d201567f31d953001cfe745823202cfc70d89300367c42597201567e31d953014e7c40d953013ebe32d9130034fe72d8d20004fd7158d200067d10d9530036de3258f20006ed6218930006bd21d9130126bf21d9120004ff7158c20014fe76d8d20004ff7558e200367f205972013ebc32d9130066dc53d8d20004ff74d8d20006bd65d9120126bf70d912002cfc764ca20006be51d9120006fb50d8132004ff7158e201567d70d95300063c65d913002cfe70d893011ebc10d9120036dc3258f20006bc7458d20145be76d9130024fe75d89300067f655893001cfe7458d20006bc61d912013fb830d91300067d72d9530066ed3258a30006bd72d91301567c73d953014e7e70d9530024fc75d813206ebd20d912002cfc70d8d2014e7c30d95300fd7c7558132016de634c32000cfc71d8132006bc6458d2002cfd7058c2000cfc71d89300067c65d8930004ff75582320067e71d9530016dc634c920004ff7458232006bf7458d20004fd7558a300067d61d9530006be71d9120066fa3058232006ef7258d20024fc75582320067f42d953001cfe7458a30136bc20d9130136be30d91300067f61d953013ebd30d9130005f77158132006dd634c320024fe7558d20004fd7458f200067f4159720136be20d91300067c7359720006f850d81320367d4259720006bf30d912002cfe7058c200067c42d953006ebe76d91200067e72d95300067d7059720006bc52d9130136be70d91300367f21597200057f754c32014f5e30d9530127bb20d912000cfc7158c20016de634ca2002eee2058a30066ee3258a3002eec2058a30004ff74d89300247e76d953012e7c1059720004fd755823200cfc7158d20065f970989300067c61d95301575830d95300057f7558d200047f7558d20035ec724c3200067d74d953001cfc74d89300367d20597201577b30d953014e7c10d9530006be65d9130004fd7558c20006bc65d9120066df30d8d200067d4059720006bf72d913001cfc74d813213ebe31d9130136be50d91300067e74d95300067d71597200067f41d95300067e4159720006bc71d9120004ff71d89300367c725972002df8704c920006bd51d912013ebf31d91300067f21d95301567e73d9530006bd10d91300367e21597200a6df3158f2014e7c70d9530006be61d9130004fd7558f200067d4159720005bd74989300067f305972000cfc71582320067c72d9530014ff764ca20006bc51d912013ebd53d91301567f43d9530006bc64d8d20064fd764c12014f5f73d9530006bf75d9130005ef724c320006bc645893002cfe70d8d20006be52d9130005f771589300067e7359720
  | 1 => 0x95300757c7558d2013ebf70d913011ebe50d912001cfc7458a3002ede3058c20024fe75d8d20006bc64d8930004ff7158f20006bf64989301567d32d95300067c6558930004fd745823202cfc7258f200f6bc644c9200367c205972012e7e305972011ebe70d912001cfe74d81320367e205972011ebc50d912011ebc30d9120006bc75d91200247c7558d20006bd51d9130006f47158d200067d654c320024fc7558c2002fd8304c120006bc51d9130006be31d91200067d21d95300367e4259720006be75d9120024fc75d8d20087d830d89301567f32d9530005bf7458132006bf52d9130006bf75d912000cfe715823202edc3058e2013f9830d91301567e32d953006ebd72d9120004ff75d8132086de5358e200067c4159720004ff7458f2002cfc7058e2012e7c405972013ebd73d913002df8704ca20004fd7458e20006bd31d9120006be53d9120004fd7158c20006bf6458d2000cfe7158d20006de31d8d20086ed32d893000cfc7158a300067e7159720004f77158d20004ff7458e20046df3158c20005f77158d200067f4059720034fc7258232005fb704c920127b820d9120066de63d8d20006bd71d91200067f31597201567d43d9530006dd5358e20024fc7558e2014e7e20d9530004fd75d8d201567c32d953000cfc7158e20006bf50d91300067e64d95300c6be76d913014e7c20d9530006be72d91300b57c754c320006bd61d9120024fc75d8930006df7358d20006be63d91200c5be74989300067d1059720006be61d9120024fe75d81321577830d95300067c7159720006f960181321567f70d95300067c21d9530006bd53d912001cfe7458c2006ebd70d9120034fd73d813201cfe74d8d20024fe7558a300a7d830989300067d73597200067f7558d2002cfc764c920086ee32d893002edc3058c20006dd3158c20024fe7558e2000cfe7158c20004fd7458c2013ebd32d9130034fd7258c20006be73d912012e7c7059720126be72d912000cfe71d89300073f65d91301567d30d95300067d315972011ebc70d9120136be10d913013ebc31d913012e7c3059720006bd75d91200073c64d95300c6bc644c120004fd7558d20006be65d9120126bf20d91200067c7459720006df4358e201567d31d9530006bf51d9130006bc73d9120136bf73d9130006dd5358c2014e7f73d9530006bf65d913005df47158d2000cfe7158f200067c41d95300067c6598930006ec21d8930006bf64d8d20004fd74d8132006bd50d913013ebf53d913013ebf32d9130034fc764c320004ff7158d20006bd52d9130004fd71d8132034ff7258c200a6dc4358f200367f4259720006bc61d91300757c754c120006bd71d9130007b910d912001cfc7458f20034fc72d8d2000cf47158d2014e7e40d9530006bc53d91200067c65189300067
  | 2 => 0x57d75989301567f30d9530136bc70d913013fbb30d9130006bc71d9130086dc4358e200067d64d95300067f65189300367f3259720006bf644c920004fd7458a300067c7558d20006bc75d9130006bf64d8930004fd74d8930006ef62989300c5bc7458930004fd7158e20005ef724c120006bf21d9130126be32d9120006bd50d9120047d8301893001cfc7458e200067f1059720006bf51d91200067f6598930006bf71d9130004fd7158f200367d7259720006bf52d912000cfc7158f20066dc31d8d20006bf61d9120006bd73d9120006df4358f20004fd7158a30036fb2058232067d83058930086df3258e201567c31d9530004fd75d8132004fd7558e2013ebc53d9130006df634c920004ff7558c20004fd7158232126be52d91200067f435972011ebf72d9120006bf32d91200057f75581320067c31597200067e42d9530004ff75d8d20006bc63d9120004ff71d8d20014ff764c32013ebe73d913006dbc744c1200067f7159720006bf53d9120006bc72d9130006fb7058d200067f65d8930006f77158d2000cfc71d8d20006bc641893012e7e10597200367d325972002fd8304c320004ff75d8930006bd65d91300367f7259720006bd21d912002cfd7058a300067c4359720004ff71582320367e3259720066df32d8d20006bf31d9120126bc32d912001cbe76d9130006df53d8d2013f9e53d913000cfe71d8d20006bf644c120004fd7458d201379c30d913015d7e76d953002cfc7058a30007ba10d9120136bc10d913001cfc7458d20006bf73d912013ebd70d9130006bd52d9120126bc21d9120006fa10582320a4ff7058d20006be75d91300073c65d9130036de3258c200067c64d953002ede3058e20005bf744c120034fc7258c200067c74d9530034fc764c12000cfe7158a30006bc65d9130005bf7458930024fe7558f200067e745972002efa6018132004ff7458a30004fd75d893011ebc20d912002cff7058c20024fc7558f200067f10d953011ebe30d9120006dd4358c20036df7358f20006bd10d9120004ff7558d2011ebe20d91200cd7e75989300079d53d9130024fe75582320367d21597200067d41d95300067d43597200a6df3058f20036dc3258c20126bc72d91200067f64d9530006bf641893013ebf30d9130006be21d9130126bc52d912012e7e705972001cfc7458c2002edf7358e200367c32597200067d7459720004ff7558f200067f7459720004ff7458d201567c43d95300057f75589300067c71d953001cfe74d8930046de5358c20006ee21d893014e7e30d95300367e7259720034fe7258c200067e3159720006bc649893013ebc73d9130006df634c1200067f735972001cfc74582320ce7e654c320004fd71d89300367c21597200f5bc745813201cfe7458f20084ff7258d2014e7e10d
  | 3 => 0xa0100000000c09008000cc2c098090d0680141001c24009550240b008ba0280704400014ff07000000040000601c49014000080702c0a01c0009c03070033984a08c8a0040d0000d0a402444000340f00012060260182d1e400050031700005008125bf15c04020020481000001020000001a0241300c02038041a0ba000403648000d120f19b0000213c0500009000d904c030200103806000000100000c270080004c2f0c01106432000010f80b010061841e00000000010282102802200080083e01800040020d802068467d50b0240001c000ec03008ea0000f00402174260b8030c8015783605c36004af0800207c6d369e2000000601d04c18000020040107089000630a40003800008000f06e0000a70c000a888024fc7558a300067f71d9530024fc7558d20006be71d913001cfc74d8d201567e43d953013ebe53d91300cd7c755893001cbe76d9120006f91058232004fd71d8d20004ff7458c20136bc50d9130006be21d9120016dc634c12013ebd31d9130006bf64589300057f754c120014ff764c120136bc30d9130036fb7058232006bf10d9120006dd3158f200edf471581320a5fb70589300067d42d9530046de4358c20004ff71d81320067d71d9530006bf50d912006dbc7458d2011fac20d91201575c73d9530006fb60981321567d73d95300adbc744c32002eef7258a300067f74d9530004ff7158a300067e43597200a6fa30d813214f5c30d953001cbc7458d20006bf61d9130035ec724c1200b67f705972002cfd73d893006dbe76d912000cfe7158e2011ebe10d9120006bf65d9120006bd75d91300067f72d953002cff7358c20005fb704ca201379e30d91300063c64d9530006be51d9130006bf71d91200ce7e76d95300bdf471589300067d40d953011fae20d91200067e61d9530066dc6358d20004bf7458d20024fe7558c20064ff7358d2002cff7058a30006bc21d9130034fd70d8d20006bf10d9130004ff74d8132036ee62189300067e21d95300063f65d9130005bf7458d20005bf744c320006bc31d91200067e41d9530006dd634ca20
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xdd030dc5624c001c3b0632ec8980c7960c065989301345e436e8b126032e1e83197644c00156902a96c8900028fa1271d95300051fc2ac3b226000cb764dc5634800187eebb22c69000e2fa1f7458d2014c3e436eab126000ae980087624c0018bee739acb900063e21d10582320061e3a0cab126000d9830dd1624c00153d0638ec8900028f610715972000c6e43a62b1e40248bc87d91304800147f0a886c8900028fa1261d95300051fc2ac3b22400087f855c5634804f53d07b96c898002a720d61d912013c5f43e21b2260038be86dd1624c0090f90ab8ac5180cbc60c065d91300065a388c8b1a4027ab980dcb644c0018e8ea38ac690002b9205621893017d37c12e0b2e4000c3c75d91634800b9b0e0b1a651009ae620153d91300045ec3c63b224000d5830dd5624c00147b0a10ec8980c71edc065589301355d400e3b226025a78805cd65c80031ed03baec49800e2fa1b7458d200047b438e2b1a40008f7815d1634800153b0638ec8900b61f21d10597200065bba0e2b1a4000a7581dcb654c0014ef02b82cb900022fe1d61d91200043fc2ae3b1a4000a3f84587654c00117d0fb22c6900030f597744c3200243f43eeab1a4027a9e83087644c0019aee638ac690002ade0552d91300063bba8e2b1a40068de87d0d63c80010ff0ab8ac1190022fa1c7458d2019e1f3b0cbb226000c3c7459530c800147b0b396c8980031d19771589301445f43ec89824000a3e85087644c06b47d0b32ec8980021fa1c65589300051f42cc3b2260018f4815d563480010fd0e3aac6900023be1d62189301c78c180c9b2a6000a75819d165c800717908b8ac6900022fa1c21d91300053b40ee5b2a600487e85dc563c80010fd0e216ca980028f61021d95300054ec18ebb224000a9d83087644c0014f30010eca980028fa1310d95301743e43a21b2a6036f1830d97644c0051f301ba6c498092ea20910d912014d3d40043b2a6000c3c655d2624c0014df04b0eca980030fdd7645893002c6f43e86b1c400087d8710b654c00187eea322c4980030f9d065989301371d286a1b2260008be8719163480018b8ebb1a60900c3960c065189300045ec3cc3b226000cb464dc5624c0014ed0339acb900d28fa1865d913000477c12e2b1a40008bd87087644c04d5750010ec8980030f19774589300045ec38a3b226000a3f845c165c8001c3ea729ec8900121f2157458d2002c6e43aa6b18400087e87087654c0010fb0dbaa61900121fa1b75589300045ec3e21b226000a3e841c565c800117b0f32ec898002ad20565d91200052ec1843b2a6023e9830d9130480010ff0eb26ca980028fa1310597200053dc02e6b2e4000c3d751d76448001ab060bacc4980023ee017558d200063bb2ee2b1260008f7815d563480014790a886c8900030f1d36558930
  | 1 => 0x902a96c8980021fe157458d200065a38ec8b1a4025a78805d165c8001878c9baa60900021fe157158a300061f3a6cb3126000ab980087644c00196ec9b8ac49800e2f2117558c2001c5e422eab1a4000a3e85cc764480018baeba9ec690002a720d65d91200243e42ae2b1a4000c3d741d3654c0495730038ec89008e2f21b7458d200051ec2cc3b226000a9f83597644800153d063aec8900163e2017558c200051fc2a21b226000a76811d3654c00187ecbba2c4980022f61e61d91200065a326e2b1a4023aba801c764480014790ab0ec8900030f1d47458d200061e3a8c8b1260018f687dc5634804d57501b96c8980029d205705972000536412c3b2a6000c3e75192624c0014eb0339acb900029da0674597200043fc3ac3b2a602d87f87443654c00147b0b98ec8900163721d4358c2002c77436e49824000a3e848c565c8007938e8a1ac6100029d60474d95300065bba6e2b1a4000c3f751d1634804bcb060b2a61900030f1d46458d200063a3aee2b1a4000c3e75d92624c00117d0fb22c4980028f21170597200043ec3843b2a60008df835d5634804d53b063aec8980028f61310597201354ec1ee5b2260008bd8714764480010fb0f30eca980030f1d7644c1200043ec2ee3b026400a3d849c7654c00b1f100ba2c5180022fe117558c200063bbaee2b1a4000c3f75191634800156f02a96c8900030f1d77458d201645f436e89824000cb471d91624c00155f04b0ec8980022fe117158d200045f438a3b226027a9e831d7644c04917d0f886c890002b660c50d81320062e3aee6b1a4000c7471195624c00117d0e28ec8900023d60775d89300070ea1886b2e4027a9e831c7644c0014b906b82cb900022fa1c64589300043ec2ee2b1e4000c3f75dd1634804d53b0638ec8980028fa1021d95300052fc1ae0b2e4000c75711c565c804d5390ca9ec89800327dce73d912015c3e43aca9864000a3d848c565c800b5b100a9ac610002a7e0d61d912002c6e43a62b18400087d87cc565c800155904b0ec8980028f61261d95300243f42ee3b02640487c855c5608c8011f70eb00c0990063d2057558a300043ec3cc9b2a602e87f8744165c800117f0eb2ec8980028f21161d953013d5cc00e3b2260008bd87997644800193886ba2c7900028f61310d95300065a388c8b1260008f7815d5628c00187aea3aec8980aa97a0c21d95300061ebaec931260018f4815d1634800159b0610ec4980030f997744c320006cc182e93126000c7471d95624c0014790a886c8980022fe1d65d91200051e42ac3b226000c3f75d91304800117f0eb0ec898002ade0565d91201255c43221b2240008df835c5634800187ee93a2cb900030f5d464989300051f42ce5b22600087e87d95624c001968e838ac6900121f21571d8d201543f43aca9864000
  | 2 => 0x429d04c003500000300002c040000bb01a00040300c07030001a510b1b42822050000a3b400543c3d258048400048380200000013000020242447019100e1501994000f00010242a7a85830000c0b09e0504054000d0003c1a01018000414430bc54000380806190c0cc06020000404010f0986e68048147c040300c1e455104c30280d8102802000d002000680c6f87cedb2ec89801a3b2097158c2002c6e43aa6b1c4000cb474dc5634800b5b501b1a60900030f1d764589300063c3aee0b1a4000ce7721c5634800117b0f886c8900029e21560181320045f43c63b22400087e87cc565c8001938e8b1a61900022fe117558d200061fb2ae93126000a7b805d165c800156
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1c18309d06598930
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x3
  | 7 => 0x8a
  | 8 => 0x8c
  | 9 => 0x8d
  | 10 => 0x8e
  | 11 => 0x98a
  | 12 => 0x98c
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x128a
  | 16 => 0x128c
  | 17 => 0x128d
  | 18 => 0x128e
  | 19 => 0x150a
  | 20 => 0x150c
  | 21 => 0x150d
  | 22 => 0x150e
  | 23 => 0x9ca
  | 24 => 0x9cd
  | 25 => 0x9ce
  | 26 => 0x12ca
  | 27 => 0x12cd
  | 28 => 0x12ce
  | 29 => 0xcca
  | 30 => 0xccd
  | 31 => 0xcce
  | 32 => 0x15ca
  | 33 => 0x15cd
  | 34 => 0x15ce
  | 35 => 0x1609
  | 36 => 0x130b
  | 37 => 0xd49
  | 38 => 0x1789
  | 39 => 0x130c
  | 40 => 0x10c
  | 41 => 0x17c9
  | 42 => 0x134c
  | 43 => 0x14c
  | 44 => 0x10b
  | 45 => 0x14a
  | 46 => 0x134a
  | 47 => 0x151296
  | 48 => 0x14094
  | 49 => 0x15514
  | 50 => 0x15314
  | 51 => 0x14114
  | 52 => 0x131354
  | 53 => 0x130154
  | 54 => 0x135314
  | 55 => 0x134114
  | 56 => 0x11354
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 751
  | 6 => 593
  | 5 => 294
  | 4 => 1
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
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/278+packedAt gbK7 (27787+(h % 278)*10) 10) % 751)
  | 6 => 2*((h/225+packedAt gbK6 (28464+(h % 225)*10) 10) % 593)
  | 5 => 2*((h/126+packedAt gbK5 (17346+(h % 126)*9) 9) % 294)
  | 4 => 2*((h/1+packedAt gbK4 (70+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffc1f80ffffe03ff03ff8000cfde0fc3f9e7c
  | 1 => 0xfffe000fc03ffc1ffc0fffc73627f1e38e38f
  | 2 => 0xf01fffff0003ffffffffffff838383e3c0ffff
  | 3 => 0x1ffffffffc0001ffff0003fc03fc03ff03f0
  | 4 => 0x1ffffffffffffe00000003fffc0003fffc00
  | 5 => 0xffe000000000000000000003fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x95ac05802d54e2127219c818042ce06c1b8e3c
  | 1 => 0x9dca00854d12e509648d2a831602d1638a285
  | 2 => 0x20014ab1000250a528a22551828302a0c0555a
  | 3 => 0x8496735a9b980401cf3c4062dc03f4036d03e0
  | 4 => 0x91b9c6ce2e39f38040081837bf40003b6f800
  | 5 => 0xce0000700300182008300603efdbdbd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_43576
namespace PEqualNP.Outside.L_meta_43576
open PEqualNP.Outside.L_meta_43576.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 27 := block_range (n:=27) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 27 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_96 : Interval s1Atlas 3 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 144 := (concat bs1_3_0 bs1_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_576 : Interval s1Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_672 : Interval s1Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_768 : Interval s1Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_864 : Interval s1Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 883 := (concat (concat (concat bs1_4_0 bs1_4_96) (concat bs1_4_192 (concat bs1_4_288 bs1_4_384))) (concat (concat bs1_4_480 bs1_4_576) (concat bs1_4_672 (concat bs1_4_768 bs1_4_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_672 : Interval s1Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_768 : Interval s1Atlas 5 768 34 := block_range (n:=34) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 802 := (concat (concat (concat bs1_5_0 bs1_5_96) (concat bs1_5_192 bs1_5_288)) (concat (concat bs1_5_384 bs1_5_480) (concat bs1_5_576 (concat bs1_5_672 bs1_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 44 := bs1_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 4 := bs2_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 99 := (concat bs3_4_0 bs3_4_96)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat bs4_4_0 (concat bs4_4_96 bs4_4_192)) (concat bs4_4_288 (concat bs4_4_384 bs4_4_480)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat (concat bs4_5_288 bs4_5_384) (concat bs4_5_480 bs4_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := bs4_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 12 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 91 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 794 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 69 := block_range (n:=69) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 741 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 bs5_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1 := bgb_4_0
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
theorem bgb_5_288 : Interval gbAtlas 5 288 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 294 := (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288))
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
theorem bgb_6_576 : Interval gbAtlas 6 576 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 593 := (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576)))
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
theorem bgb_7_672 : Interval gbAtlas 7 672 79 := block_range (n:=79) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 751 := (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 bgb_7_672)))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 1 zero, 33, 35),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0feeaece8fae0e0c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4209041600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_43576.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.and,[0,6]⟩,⟨.or,[2,7]⟩,⟨.and,[4,8]⟩,⟨.and,[1,5]⟩,⟨.or,[9,10]⟩,⟨.or,[1,7]⟩,⟨.or,[0,3]⟩,⟨.and,[2,12]⟩,⟨.and,[11,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209041600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209041600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_43576

open PEqualNP.Outside.L_meta_43576 in
theorem PEqualNP.Outside.L_meta_43576 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209041600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209041600) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
