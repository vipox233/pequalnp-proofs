import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40527.Model
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


end PEqualNP.Outside.L_meta_40527.Model

namespace PEqualNP.Outside.L_meta_40527
open PEqualNP.Outside.L_meta_40527.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 7, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40527

namespace PEqualNP.Outside.L_meta_40527
open PEqualNP.Outside.L_meta_40527.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x10cc0010c000104a0c97810c50800011800c8fc41fd40fe43fc31fd10fd32fc32fe32fd42fc10fe42fe10fd21fd41fc21ff42bc40bd43fe30fe40ff31fc30fc42fe20fe41ff10fd20ff43fe21ff32fe31be40ff20fd31bf43ff21ff40fc43ff30fd30fc20fd43ff41fc40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1003800716300081200d002000180005c1912428a85000850000000044000000000400444d50c80200089004c000020020e013d53102bea6884f553329f2a0615e53d067ea890dd946329eaa0637b504877080186750c31da28a873e50d0eb8a6906750e31cf29881e521086bea6904fd5130af2988178504867aa9986e14143ba28a413d54c827ca818cfd51109e2a2211d531027aa8185b54a31b7a92613f54482dca518cf550329f2a6413f548c27ca9995b94810ba28a876c52442bca7a14f55243bc2828775518cb5ea4a1db54810b6292613c54482baa7a14f95330cea1a619d438ca7aa998edd45439e2a24377514833ea6a1dd94420afa9a437551082eea2a1eb14943ba28a615d53d0678a9185bd4943bda82879d43cc376a0a1e754c409f2a0873e54cc6b8a690e750c32aea98813d539027ca0205714d109f28481ba501027ca9884f141439f2a0653d54c437081985dd4530b7a9221385050e78a8985b14943
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa15880014430100032f2b5214143a6181430c6986050c32a6181438ca986050e31c3189531021c6550d30c550c514c2996310330cc1445050f0f6254c40b818121087146154c40ccd445050f0d4314930c91485150f0d4394a31c550e518cb176154c40ca1485050e1d63953108758e54c83186054c40a618143cc2396510030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x400005811886154c40a10e0a1ca518d107050e518cb04310c0a9881841846054c40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => 2*((h/28+packedAt s0K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s0K4 (2457+(h % 58)*7) 7) % 91)
  | 3 => 2*((h/15+packedAt s0K3 (950+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s0K2 (245+(h % 8)*3) 3) % 5)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffc07ffff03fffffffff01ffe3ffe3f
  | 2 => 0x3fff01fffff80ffffc0fff01ffffe07fcf1fc7
  | 3 => 0xc07ffe03fffff01ffff03ffe03ffff81f3e3f8
  | 4 => 0xff800003ffffffffffffc00003fffffffc03ff
  | 5 => 0xfffffffc0000001ffffffffffc000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x429114288471224500b2cb4a94b08aaa156e1b
  | 2 => 0x13224c514890e48b2c0555295956a24ccb16c5
  | 3 => 0xb244289a512241d3555026ac526ad30963a368
  | 4 => 0x2470b163a244891c9a6980c1838d1c71bc01b6
  | 5 => 0x3878c183c3870e1ee38e38f1e00e1861fed800
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40527
namespace PEqualNP.Outside.L_meta_40527
open PEqualNP.Outside.L_meta_40527.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x206a0010141021434c094200108175dfd30fe41fe20fe42fd42fc30fd41fe43ec32ff31fe21fd43fc43fc41ff41ff40fd21bc40ff43fc40f431fd32fe32fd10fc21fc20fd31ff30fc42fd20fc32ff32fc10fe10ff21fd40fc31f731fe31be40ff42ff20fe40ef32fe30ff10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x80000200000000018e0220010006c100700000030a418106040813a30003002018100000680025200da2408301603001e049801a001840000380aa04b8072209d754c40f3996636d528c79a86195754f42aea9e8377514827ea8904f95031bb2884176518c2bca7a0f30c8309f28081b731903a86418f90cb31b729687c4320c6bea690cf15130d7290815f534436862204f55031cf29881d4318c2daa5a1dd54630baa8881e7320c7ac6418dd94440ba28a653d540cab8a6885b54a30f2908433d54cc2daa5a0db14943ae29a437551d0f6863205b54840d7990819d53103986418ed544409e2a2217451483986518db94a31dc206616c524c6eca618ddd45309faa261e4320c678a8906b0c8409faa221cc328c2d8a4985d145309f2a62177514cb5ca8195b14910af298813d54c82bca7a17594c31b729021af329036ca2206d55031eb21863d4310c2dea4985714d209eaa6215f53482eaa3197550c31dc20061ad52102eca318dd14543dd28081785050eeca3a1eb0ca40baa88417551d0a7ca1205b94840b6a9021b731102dca5185bd49109f2a6616e52d06dea4a1ddd45439f2a0657b5050f6ca818dd94742b7294656f524c6eca3195b94c32d6aa065ce530cb9c86194f95320
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x5000000000098a005001500200000ee10c831103903110030c554d5110346520c6309518d510824c6354810e1950320c6c46150c32e1590320c78832100308b59432102c86050c32d10ca518c2d06050c31c354d521030d540c831b198a320c6c46250c31a5590320c635650c440e1550320c784320c640b118d2108786640c831
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xa0aea190622050575990320c702b286418881215da540c831
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s1K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/74+packedAt s1K4 (3159+(h % 74)*7) 7) % 117)
  | 3 => 2*((h/29+packedAt s1K3 (912+(h % 29)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s1K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 2 => 0x3f01fc07ffe07fff83e0f81f80fff83fd333c7
  | 3 => 0x3ffe0007ffff81fffc00ffe000ffffc1e3c3f8
  | 4 => 0xc0000007ffffffffffff000000fffffffc03ff
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8114282011c104200c6118a28e2c214a05561b
  | 2 => 0x924c51ab224728e581a86a9b1255a92cd332c5
  | 3 => 0x24289ab5448a1d6ab410b6ca249ab58963c368
  | 4 => 0x30b16346891451935ada041048e34631bc01b6
  | 5 => 0x38c183870e1861dc631cc71c70038421faa800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa00000faaaaaaafaa00000faaaaaaafaa00000faaaaaaafaa00000faaaaaaafaa00000faaaaaaafaa00000faaaaaaafaa00000faaaaaaafaa00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40527
namespace PEqualNP.Outside.L_meta_40527
open PEqualNP.Outside.L_meta_40527.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1062460c000004108b200007001041003006240183fe42fe20fe41dd43ff40fc31ff43fc42fd21fe21de43ff21fc10ff20ff32fc43fd10fc41ff41fe10ff30ff31fd41fc21fd31fe30fd40fd42fd32fc30fe32fd43fe40fc32fc20ff10fe43ff42de32fc40fe31dc32fd20fd30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xc0c0810034000060169b00340004c28780001800b0004012061c003181408486243ae06040370a0008d4e681045e00c971802bea8195b948109eaa065cf5250f3aa8195755243a6292876d5210398a4a1d755232b7a92635c5250e78a8905794f42afa9a215c53486eca3a14f95031af298877551d0abea6a15754c41ae29a855e520cabea690d794c41cea1a859d43d0b9ca4197310832cea1e836d52d06dca4205754c10bb288813d54cc2e8a29073d0832b729461cc32886eea2904f55010af29e833d54886baa6215714d20af298813e54cc2daa4084f95221af298853e54042baa8194f15110cea1c815d53886eaa2204755032e6196415e53882baa7a167d5143af298215f53482dea4a1e750c40cea1a835d53882baa7a0d754c40b7296835f548cad8a498d754f40af29e813f544439864905714d10b6292879e540cabca710d794a329f2a0656f524427ea8904f55031b6a94615e5290f986410db14910
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x80023800c08001081c100c041828c6250f41c3189540ca1d6494e20c3553420cb0d43548409318953d03154354742c550d511028d640c920a3189431030c540c920a318943d0a4d651083293189531068d640ca21c3950328861d6595032a31894390344321452087590534870d4354b41b1987420ca8d640cb20a3189435068d640c821
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x400000800206bb0a819241411c9435444081aed2a06510d047250d51d0a82ba06428a418155261d0832
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
  | 4 => 2*((h/58+packedAt s2K4 (2430+(h % 58)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s2K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/30+packedAt s2K2 (294+(h % 30)*3) 3) % 6)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe07f07ff83fffffc1e0ff8781ff87fff4e4e3f
  | 3 => 0xff8007fffc0fc3ffe00fff801fff87038f8fcc
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x420a00230020800062110088c50089281090d5
  | 1 => 0x89144a441945212c0c8648510a4852d146462a
  | 3 => 0x4526948928ea0655a10b95025395041a8b8b4c
  | 4 => 0x9658e7125283ab9ad7a0c4449ce66063f00db0
  | 5 => 0x1860c61c630c33e319cce66700c44083ed6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888eeaaeeaaee888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40527
namespace PEqualNP.Outside.L_meta_40527
open PEqualNP.Outside.L_meta_40527.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x50c50000c20062010c0508099018085ff31fd41ff40fe32fe21ff41dd43fc20fd32fe40fd42fe30ff42fc42de43fe31fc10fd10de32ff30fc21fe43ff43fc40fd31ff21fe10ff32fd21dc32fd20fe42fc31ff20fe41fc32fc41fd40fd43fc30fc43ff10fe20fd30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x6800010202061451022041002434501260010124387801000e00080acc28a302940402eca3a173d4943aea98815d5388798a4a1d794c41af298215e5290ebaa7a14fd5120af298876c5250eeca2204fd5110af29e816e52042baa71057d4d20e6192413e540cabca7a15755243b6a94611d540cadea4885714d20af294656f5250e7ca910e750e40e619043cc328867ca8084f55330cea1a855d53d067ca818d754c41aeaa4653e54cc2bca41957d4d10e7290655c5350aeaa2206750d41ba28a413d540cadca5184f15110b7296836d52d079884195794f41cea1e836f524c6b8a690d714d10cea1e853d540c678a8905314943aea98215e531033aa81973d0832ae292875d540cb3ea8a1d7d5232b7290815d5310adaa4085754f40af298855f534879865905dd4520afaa0656c524c67aa910d794e20af29c433d54042d8a4885d54742cf2a0659d43102daa42057d4d42
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20ec05040000002038220000103315435444087590534868c6250c409318953d024d6510832c350d52d064c6254c41a3590328868c6250d41c350d52102c661d0832a3189439030e540ca21c3150324828d640c821a359032c83443214520c3189540ca8c6250f41c550d51d0a1d6595032a3590324821d6494e20a318943d0b0d54d0832
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x4408206bb4a819443411c94354742a08e4a1aa22040d761503248282ba06428a418155261d0832
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => 2*((h/21+packedAt s3K5 (704+(h % 21)*6) 6) % 44)
  | 4 => 2*((h/44+packedAt s3K4 (2430+(h % 44)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s3K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s3K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe07f07ff83fffffc1e0ff8781ff87fff4e4e3f
  | 2 => 0xff8007fffc0fc3ffe00fff801fff87038f8fcc
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x420a00230020800062110088c50089281090d5
  | 1 => 0x89144a441945212c0c8648510a4852d146462a
  | 2 => 0x4526948928ea0655a10b95025395041a8b8b4c
  | 4 => 0x9658e7125283ab9ad7a0c4449ce66063f00db0
  | 5 => 0x1860c61c630c33e319cce66700c44083ed6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888eaeaeaeae8e88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40527
namespace PEqualNP.Outside.L_meta_40527
open PEqualNP.Outside.L_meta_40527.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc2418000001a00000708c0000000df43cd32ee21df30dc43dd32dc31ef20dd30ee32ec21ef42ed20ec42df32ed32de31
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x8008000000600015354831a7a82654d538ca9aa5985354d20a6a98434c514ca9aa62153d4e21a62a2654e544ca9aa7905354843
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x91986544ca0e64d4e218319153482446154d20
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
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
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/26+packedAt s4K4 (272+(h % 26)*5) 5) % 17)
  | 3 => 2*((h/25+packedAt s4K3 (351+(h % 25)*4) 4) % 13)
  | 2 => 2*((h/8+packedAt s4K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffc1ffffffffffc0ff83fe0ffffffffe631fff
  | 1 => 0x1ffe07f07fffffff07fc1ff0703fffff9ce4ff
  | 2 => 0x1ffff8007c0fc1fff8001fff803e0f81e0f8cc
  | 3 => 0xe00000007ff001ffffffe000003ff001ff00f0
  | 5 => 0xffffffff800001ffffffffffffc00001ffff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x424420a4042088401880a202918a9494210955
  | 1 => 0x848891408945108b03140c50221529688c64aa
  | 2 => 0x5714526d50ea1bd56852976b04a78e0de0b8cc
  | 3 => 0x9639658e62839de6b5dac14a0939cc31f700f0
  | 5 => 0x18218608430c2138c663198c4e0000415ad600
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeea88888888eeeaeeea88888888eeeaeeea88888888eeeaeeea88888888eeeaeeea88888888eeeaeeea88888888eeeaeeea88888888eeeaeeea88888888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40527
namespace PEqualNP.Outside.L_meta_40527
open PEqualNP.Outside.L_meta_40527.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0xc11cf1400002c00001024c0100181042002019002fc21fc42fc30fc41fd30fd40fc32fe42ff10ec42fd32dc43fe30fd42ff21fe31ef42fc10fd31fd41fe32ff30fd10ff31ff41fe10ff43fe21fc31fe41df43fd20ff40ff32fd21ff20ff42fe40fc43fe20fd43fc40fe43fc20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x685f441043b8a421fbd0a41bea94437c54c43dc6590df14d21beaa265ec420cb7c87215f54841beaa0436f5250efca1997bd0820bfa9e437e50106faa8987754843eea9843ed32c86f8a5885f54d21bfa8a81ef424c2bea6a0fb10910bfaa0637e50103f0a0a0df94443be29a81df43c86faa5a07ed0140fd882217f54086faa2214fd5132b7290637c54483daa2215fd4d21bea8e417e54cc3e883085f54831bf29483bf41d03b886995b14940beaa483dd32cc77c86215f94642bf294817d51902fca5195fd4b10bea80637f53c83dea4a07b4cb20bea9c417d520c3be8718df94b10beaa021f910043d884907710f31dfa1c87ec42107bca1a1dfd4d20f7a16437d548c7ec6218fe90040f6a9063f7410437886217d90441bea8c215e5410ef8a2987710e31f6a1085df43507be87905f54d20ee21e857e54083ee6298fbd0a31aea9821de53043d88498db14943fda82835e53902fca0185f54430be29a83fb20882faa8905f94632efa18437c54443daa6215f94e20f6a9e85dd53906fca6905f55320bf29687bd4310f7a8220df946409f2a0217d53c82fca8905f95132ef98a61f721487be8710fbd0821bea94417e51086faa021f78c932bfa9c436e520c3be87217714043f719641dc438cbee83085f54f41be2a461df43d03be87207bd0921f7904417e51d03be64197b14742bfaa663ec42d07d885997bd4042efa1a877e5290fbc8621fb10b30efa8e877d54486fea2997710e41ee218417e52106faa6215f94641bf28c877c54cc35886215fd4c20ef29c837e530c3dc87a17d48421ee21a61cc4310bd88418fb50f42be29a41de53902fea890f7cc230f6992435f5350afca120f7d4d40f6210616d52902fea9905f54221efa1a43ed52906faa9185f14520ef28087ef4290afea2a17b14943bfaa4215e5390b5ca8215f95221bf29a217c53887be86195f15220be2a641ed51d0ab8a6a15f54810bea8e617d5090af8a918df54c21ee21e437c544cafea4885f54732bf28e87ed320cbdc6490efd0040bfaa643ef200837a84215fd4132fb88021dd31cc2fca318df14f20dfa08837d518cafaa2207bd0a40beaa443ef4310bbe6498f7d0d10bea8c877f50486fca2205fd4d41bea92217e53d0be2200877ccb30bea9421dd310c6fca8985fd4930bf28461ec52506f8a7886f90140be28283bd54043bea6a0df54e42be28287df438c2fca820fb54810be292636d5290fde4210df95043ef98c63df43483bea5a1fb14f42af29c877d5190bee21085f94a42aea9c83de5390bde43905f94242bfaa241cf43d0bda64905f55030beaa041bc4390af8a2a1dfd4f10bf2a0437f524c6fca9995b94a43ee28e87dd4310efca5087bd0910bf29c216d52907b8a6a07710f20fa28a81dd5390afca4085f54b31efa1a857c53087dc64197dd0641
  | 1 => 0xe5410efca9085f54420bea9c65ec429079887a17754043dfa0a817e5390fb886a17b14c42efa1e857e54c87dca4185f14941bea8687dc52d0ef8a9197ec8120bf2a061dc434c6bca610df94c31f7a14437d54883de87a15f14a10de2a265dc43506f8a790fbd4742be282437f54883b887985fd5032bf28487ec428cafaa88877d4343bfaa4637d51883d8a2215f55131bea8083ee51d0afea6085f94020f6292816e5410bdc86216f90541bf288835d53082faa0195f95042bea86637f52043be6218fb10820beaa665df43042f8a990df54f40f7294817e52102f8a8195f95310ef29843dd32cc2e8a2a05f54e30efa8087ec424c3be87087754c10efa1e217d51d0bea8220df94f21ee21861df32cc6f8a8185f15131bfaa6617e520c3de4310d714d40f6a86857d53902fca4195f55331bf280437e54882faa990f7cc730ee21e65de304c37ea8996f95010bf28685dc430c6f0a0a0df14142efa1a813d54042daa4085fd5230bf28861ef42042daa418dfd4143bf28441dc4390afaa31877d0c40dfa1085ec42c87de85887710e21dfa18877d5090f7a80205f54b41f7a1281bf40903baa5a1dfd5332bfaa0617e53907dea4a0df94c32bf29661dc43d07da42905f54021bea8e877c54087d8a0217d4c431bf28087dd314c2faa5185f94b41eea86877d53107b886215f55031fb98c637e518c3daa0215ed4141f621463df438cbde85085fd5232f729885ef42102f8a2a17b10b20ee28887ef420cbbca821df94910ee29a83df43cc7be65195f54321efa1a657e50d06dca5215f94c10fba0a837e52086fca2105f15020bf2a463ef420c7d88410efd0641f6214437c504cafea70877d4443bea94817c53842fca6105fd4c21bf29843ef42d03b886a05b94810be2a261f751502faa7a15714d41bf2a0637d5290edea4a05f54042bba8a817e500c7de84997754743bfa9a817e51882fca218f7cc930bf29881ec428c2fca62177d0e20f7a14657c524c2f8a9995f95032bea96617d52907ba64987b10f42bf284637d54c42faa9087d44010ef29087de314c6faa118df54e10bea86656c52507de8598e310c42bf29887ed4310bd885a07bd0b20f7a88857e50d0efea098f710e20df212853c544cbba60185f54e31fd98461ee4210afca0196f50740bf28e857f54082fca4105f54341bea8887ef42883b886085f54432efa1841ec42506fca3987e88020bfa8a617d53082fea0a15f14c20ee21e217f525033887215f94621fb082217d53c86fca518df94331aea9c85ec42902fca99077d0e41f621243fa300c39e86215f94842beaa4877f53442faa9215f14810be282637f53882fca8205f15221bf28465df434c2fca998f710c40aea9843fb40043b887085fd4520e6990657f52507dc4290fb54830fda06217e544c6faa518df94321f728
  | 2 => 0x76020141980002800000621983400014000000101e020340092a001fa0b0b400002180080000000030090000082c000020f00c008580489a9087a0686804812000700e9400684a09810130161b80810011078e6388201e01200800029ce8b80000002020ce1400b3329e048000395e13816018001324202338001ae00000720060b0000c0180200c00000100fe018020303c0400c1002801a6600102003762301c0494e08c420101a0a804ec01a078000080003026018105400a0384c05006000440180e000001081868ae0470ca0f8e05580201878520180017a0085800c62498100c00600000080020300000b9601800030780031000800010221206000012050000000036802080285f04802800071d80e00420033568041d81e000aa068020086807006001460600205000318000001c0c0080087a06a0af300016814c30dd3ec30e68b80200202000098000115c010020b00001b00031c404004140900b8090a82c000717f544cafaa6205f94e40ee28687de52d0ef8a818dfd5130bea9821ec42c437e85217bd0a30ee21843ef42483be8698df14e20bf29c437e54486faa1195f14910f621021df300c2fea0a0f7d0c41f710241ef53d0bde84a0df94a30ef298417d540cbdca2217b94a43f7a8685dc43d03de84a17bd4c42f6214217e54443dca520fe48020bea90817c54cc6fca9185f94843bf29e216e52907dca418dfd5010bf28421df5210fdca4086710c42bfaa263df430c2fca8087bcc932f719241ed52903de8498d754e40ee218657d50d0afaa710df15121f7a10837c53443d88420774c832efa1e61ec425037a82a05f94e42ee21a436f52507b887205f94c41ef28e877e5110bbe87997b10932ef288875e53906fca2085b94a40fb90c43f940103da401077d0c31be298217f54886f8a6a17ed0240eea98417d53442faa3a05f54b10ee21a217f5350afea4a1dfd5110beaa465ef42cc3d8a1a15f94010bf29a437d54cc2fca9195f14540bea90877e510cafca110dfd5310bf296817e51c83be87a0fb94042bf29e81f840042fea5085f94240fd08021df5350bde85995f55240bf29e415e53043da4210fecc130d721885dc5350afca3997b10c42efa1885ed21c83f621085f54b43fc206217e52cc77c86a1fbcca32f729e85ec42cc6daa4185f15010be28a655e53083de84185f94831bea9c837c52503de42907d88421eea88877e53d07be8721f710e30eea9c817c54843ba6498fb54a43bea8483ef42d06fca0217b10a20afa9a81dc43483dca8215f54f10bfa8a87ef5250ff260185f14943ee218839
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5534825d6394342d354e529066c6255110d354c420826d62d5330d310d520c65e6314c219ed81534872c6255010d314c525025e6394b408f590530425e63d5321cb950420cb8c4310a10d310e52902d8604c530bc586100423d65950109bd97420425f6355121d9d48515034d5394a4097d8d544c65d63d51209ed95200831e54d0e30d914851502e66114042a798e4310ad96014443e310c421035b50943438fd91534425e6494c209ed81544866d62d5210b398c5110a5e63d48109b58a50d0e5d6314a10d5d0c515026e64948319798e50d074f43948309798c540426e65d09219b594420c31e54d0c1097d94430827661150309798c504874d5310a409bd95200834c4354a409b594420c63d64d4810ab58a4310ae96010820d310e529066d6594810d354b300c2e561108219718d54c874d524c431c7953438cb4d53d0a42cb950420826d62d52319bd954310b2e5410b2197596530866e6214810cb95342882776544010e310c42ccb4c43948318fd95401026d6510821ce181540434f4394a43c7150434832e5410a32cb953420431c5410d21b5987434c67561d5330dad4b505078c4310931f454d100425d63d501097d95320ca5e6510d41d6d4c505071d5454c109798c540872f6255010d314d32c826c62553319b98a53d071f5410d21b59845010e5f6510c21dc147405034e5394a4197597430438c4310b209758c514832e54d0a2197997434c31c54d0d30cb15042442d56114843e310e5110bd04344010c7550430426e62d5310c755043cca9c6350842ab19132486ac644c920b358e4210a5d6594c20e310c420871c54d0d319b195324834d53c80209798c520426c62550319b98a50d0f6442d4540d354d520438d6110c429718d54c426d62d5110d95445110a6c6255231d354c420874c4354a41d310d520432d5410a31d354e520427960d532197d954310f2e5410810da148505078e5310c42d310e520425e65d0d40b398e50d0a3c64549109bd97420c78c4310940a7191320ca5f63550109dd95210874e54d0c42e310d5110a5e6394740ab5964310b5b43d4141d55445110e7661150209718d548823d64d4e21d314c525066e62d51109e181544874c524c9309b189544c28e6390c4297994435031f6395010d310c525066e651094197d95310c78c4310820d394d529074d5310a419b58b54c425d6510c20b398e51d0b1e5410c32d3d0e529026f6255031c7552530423e6414c10c755043886cd6314442cbd50424426e64948109b988538438c4310b31bc580410426c64548309bd89544423f6454d20d9d4651d0a5e65d0d329b588504c76b42d4141f494d100432c54109319dd95310c63e6415010ecd07400432c541093097d8d540826d62d5031e310e5010b8c4390842e31944310a9e6295043cb950420863d64d4c10
  | 1 => 0xc3695014042ab98e4310b8d4310c4297992530426e6214f108f191534427960150219bd89540423e65151329b5964310a3d64d4e20d314c425025e63d5210b55845010f1d6510e429e181544c7d343440109d584540838f644c8329b59442082da60d0d30cb95152042796014f218f993538865d63d53219718c544c38c4310a40dad4250d0b8c4310b40d3d0e520c7545314540d514f51502e66114c429b997424ca7461551309798c524434e5310810e310c428c25e63d5310cb952520438e6210c42b6580430c34f53d494097594430ca6e62d5330d394f420874f43149419b5885344359501404397d94430432c54d09218fd95411067461551209798c540834f53149409bd89544825d631412197594430438c4310b41cb15042ccb4d3254032cb153424826d65d0831c755343042ac644cb219798f540c6b860507409ed95100426e62d523197594430866e6214530e3d844310a6f65d0830d3d0d529065c6355210b398a51d0e5d6394b40b39885110e9d6510e42c7950430c26d62d5010b358a50d0f2e64950429bd89548c27a60150328f19153486ac644c8328fd91534875b53d4141d614c505065d6510c309758f54887584314141b35885110e9c644c930b358e50d0b8d5310c42f8d0910042e86048520d354c5310b2d54d0810d3d0d520434f53d09419e980540c66f6548421d394f4290a7561d53209b191520427661150329798e52d065d63149109798f54482ce63d0932b398e4210b4f43948109798c530432d62d5132e39504310acd6310832e39944310b8e6010c42d354d210874e5354a40c718d54042e56114042e310c424ca6e65d0941d310f52502f264440109bd89548425e6510d42d394c420872e5410b20b358a4310ecd6314042bc18141106766114f20d3d4e53d0b1c54d0d329b195324863f65508429bd94420c66e6215010cb5964310a5e63d5032d354d529066d65108329758e50d078c4310930d310c525034d53d0821e310c428ca796015031e310c5010b4f5310941b95845310a6d6215010cb550420438f6510c42f8109100427a60d5321d314d32c876852d4141e310c428c74f53d494197d8d524426d6294f409b988530426e62d5021d354f429034f43d4941e310c421074f43548309b58a50d06ce62943439dd95411066e65d0920a719132cc73461550109798f540426c62553109bd89544c65c63552219758f544426e62d53319bd89534438c6110c4297594430c71e5410c3197d8d544823e64d4c10c795043cca3c6454d20b69805210e6c64548319b99442502da60144439758e52d072f5410930e310f5010ad66114843d354b310c66e6214c21d354f42082e661d09219758f544874c53d4940d314d324878c43108319758c540825d65d0c21a7191324c74f43149439b588514c33554d04109d18
  | 2 => 0x53d0940d394c429034f53d09429798e51d0a6e62d523097d9743087b15444010c7950438874f654c8329bd89540825e63145209b189548431c639501097d97430436442145409e580540ca5f63552209b992520c23f6454910bc185401025c6355021d3951320ca6c6254d10ba9805110a6d6214f10cb153424cb8e6410f42d6d0c505078c435404297d8d548865e65d0d319718d540425d6315010e310c429066d62d4c109bd8954cc3e152440109b98b540831f5410d10c7d8c544ca776155120979974350b8e6410c42cb55152042cd62947439b189544c74f5310940b398b434ca6e62947409b58b54cc65e63d50209798f544438c43108309719153082cf6350842f8949100434d5354a40cb552520426e62d4c10b65805210f4f5314941e31804310b4d53c8421d394c420834c53d0941b39885010e5d63d48109758f548434f5294b439d98754cc25d6394740dad08505072d5410a32c754c4390a5f63551329798c52c431c548c9329b58a51d025f6355320d354f420434f4354a43d5d4c515031e5494c109ed95401034f43d49409bd89544cb2c54109329dd85534827761551109798f540c35753d4540d39504310a756510410e310f5110b4f4314940d3d0e529067a60150219758f54082cd638c832d35485210e5d6314b10ba5805110b4f4354a40d614f505072e5410a319b988534426d6215030c7150434cb8e6310c42cb550428c35843d414197d8d54c878d6010c42d314f4250a5f6355130e310c420431e5410f31ba98342482786054d219d584540c26d65108109bd89548c65f6355310e310d4210a3e64d48109b189540425d63947429798f544865e65d0d41d314c425063e64d4e20a719132cc26e65d0940c7550438834c544c8329b98b540c34c524c931cb153324ca5d63d53209718d544874d5310810ab98c4310b4e53d0a41cbd50424ca7965840109bd94420426f65108309758f548831f6355010ce553400438d6210c42b3991320caf064440109d58453c834d5348020d510f515038c43109219b58a53d078c4310910cd147415038c644c832c79925410f8c4310920b398e4310a3e64951329b189540c2ac644cb20d314f425027561150329b58b548c37341141419d98754c832e54d0b329e98354cc74c534c9209e98053c865c6454c109718d524426d62d5131dcd95100434f4354831b318d4210b6752d4540b3d894310f8d6510c42b398c5010b5443145409798f54c827b60551319b98b548425c635512097596530434e53d0810cbd8a540425f654c030b3588430ca6f654c8329e594400425e63d50219b98b54042cc644c83297191530874e5310a419bd8954c43b254440109b588540c66e62943418fd954310e5c63551109dd85544c2f365440109b597420c25d63d5021c7150438cacd6214043c795043c
  | 3 => 0xb00d100143b00803000051340b0981d0000103c0013c01020813500006c020700300408008350180005807a00cf801560f8050b248000030248000000078350bc0009c08048000400000854028010480203c8b0280001806038060b417030000000c0a800015f3008040001201403028ca0bc5900015024320189b034010081101441000160048d02d038cc1d000140240600c1100060014088340d0185f01426054011f04e07a4c004f20500011008021261e41b3cc440701c1040892807000b656806018020000d0000003c0000000004020007402c065b84c018d063800000300b40000001012104fe2b6e41202800025ef120060140000008022490107702c1401407000000140002c00000050182005c000082a00c0000002044060847d01801000d1044110f46a6fa21000000092e11412014000e40c81400000270158c010000002b050c10180200c04000280180d004bd004c8000020000235c000051e048d900c050002a05dc3470069b98b540c66e6214c20e310c42506ce6410c42e310c42c865f6355110a3191320ca6f6255121d310d520c26f6255130d5145314c38e6110c429758c520434f43d49439ed95300c25c6355320e310c420cb8c4310a209b988540c6ac6250c43cb18a540425d65d0c20d34c9510cb645148520d394d52042cf654c83297992530872e43149439b58b540c32f5410931d5d0f515025e6314c20b31894310f8c43144429b98b540cb4e5394810da108505066c62553309798f548878c4310b109b58a51d0ed56110c31d914b515025e6314a10ba5805310a3d6414810e39534310b6842d41419758f54c425d63150219b58b544c34d524c030ba9805310b6742145409b188544823e641481097d8d548434e53d0a409bd8954cc66f6550842c758f544cb2e5410a309b98a53d036b52141419bd89540c25f6355030c714e4250b4e5394a409b98b544c36742d45409b98a51d0ef1611001097d97430838f6010c429798e50d0b1c5410d109b98b544c71e5454c10d5d4651d0e6e6215030d354f429071f5410d329718d540831c43948429b588530438c4310a21d314f525071f5410d2097d8d540878c4310b30c7950438834e53d08209798f548834c4394830c7953438c74c43d4941c7950430427b6055110b358e51d0a6c62552309b597420426d6214e109e58354cc6ae6395042cbd88544ca6e6214131b398a4310f4f
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x401413c2820028101020101c000ca3518000002200018124c003334c41d41431d15310820ca2a2b00a221e0c64951320ca87ba88621021071d16314910e22a8a9a2008586711804310a87396a821a2183190544c832a92e02a2641960c6410d520c330b0aa028085439cf5410910a1eea21884105457114d32c82c4b80ca21885619c46510c42c18c829a659050c744c9510caa4b80a699643c110c42d4540c92a6b00841060c6410d520c7483208688021a110d6114042a18e4aa08608645635445110aa2b8886a90638315263d0932c8aa4b08a421e49525805210e863a264a8065a81904244010e42a8a92200848e74991320ca86390a821a41a110e6114042ac2ea2122008649625405010f42b08c221885c110c4214540a8ae22a2641950c7355042042163a2c429a2183190534cb21a1eea2188410e0c6414d3248707ba8c8990659258d5014042a1aea2188408708435405010b44b00c021885629c06510c42aa2ea21a200878043109100434421ac028885c210c42d4141a18e8a988410e0c6318a5404307b2886210218315262d0d32b12e03088621645625445110ea4b8086a90619254d6014c42c8aa6b08a6216455358442086c5380c2218858318c6255010c1eca322641960c64149324c306b288621021c210c4214141a18e8a988408585711804310b4421cc028885945855014043c18c82926498e61515805110b07b288621063831904354810b0ae2328862160c6414d324838221aa22888583d944310830
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x300000010030000020056010c04645c44354831c08645c04354830c08645c0544c832e00435855014042a088454d6010820d017510c4244010b018510c4244010c81715806010c42a048454d6110821e00435456014442c04645c4544c832c08645c0534cb21c81615c06110c42c04645c4534cb20
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
  | 2 => 14
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
  | 6 => 2*((h/28+packedAt s5K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/287+packedAt s5K5 (21033+(h % 287)*10) 10) % 779)
  | 4 => 2*((h/293+packedAt s5K4 (28652+(h % 293)*10) 10) % 754)
  | 3 => 2*((h/35+packedAt s5K3 (4165+(h % 35)*7) 7) % 85)
  | 2 => 2*((h/25+packedAt s5K2 (840+(h % 25)*4) 4) % 14)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ff81fffffffff81f83e1ff0fffffffa071fff
  | 1 => 0x81ffe07ffffffffe003fe1ff0ffffffc38e3ff
  | 2 => 0x1ffff80f01fc1ffffc001fff1f07c07c0fccc
  | 3 => 0xfe000000ffe001fffffffe0001ff8007ff00f0
  | 4 => 0xffffffff000001fffffffffffe000007ffff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x44a420a12448880590a0a505254a552030d55
  | 1 => 0x28908914248911160214a0a504a94aa41862aa
  | 2 => 0x54e1452641d21baaab408936613c7036c0b4cc
  | 3 => 0x18c5965889039dcd33a6cc0441ce60c76d00f0
  | 4 => 0x610618600e1c2071c43911c888000301b6db00
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888fee88888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40527
namespace PEqualNP.Outside.L_meta_40527
open PEqualNP.Outside.L_meta_40527.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904002ffd5001fd3100ff14007fe5200ff04001fd21017f88407ff21007f4c00bff5301ffc8003fc4001ff90805fe4101ff8c807fc4200ff94009fe53017f08409fe4302ff54807fc52017f1040bfd5100ff08001ff41027f14c03fe2000ff90003fc30027fcc40bff51007f50801fd41027fcc809fc43007f4400bfd50017fc400bfc5400ff84005fe51017f8c401fd40007fd0c01fd2002ffd4805fc5102ffd4001fd43007fd000bfd54007fd0805fc3102ff95007fc32007f4c809ff3002ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xa4204ef10f43177fca3a107bfe6050405ff8824200ffd8542007fec6a0027fc61d0801feb1a8220ffcc141017fe82a0802ff6150007fe2924209ff9514101dfcc4a080fff5250807ff10a4035ff04343015fec290807fe40500013eb2e8034ff9954304ff887a080bff31d04017fb0a4002ff1053110ffaa4a08cffe5250c017fb226000bfd9131137fca099013fe324c401fea126200ff50d2012ffaa1a080bfc104c4017fb0a640cff99520005fac89900aff634c421ff10a8009ff90b41007fec098813f7314c407f79068403ff10920005fac890803ed2148033ff29a4202ff9052104ffcc7a0006fe60d041dff2926000ffd0d10187dea5a1003fd4350007de2168409bf1974212dfacba080eec62504097f31a8405bf9954001ffe40a10c3ff50d0835ff32a422aff1854200ffe408800efc624c4017eb168604ffcc532127fe61a0827fc4250051fea82640cff5512004ffcc7a0857fe52d0005ff18e821eff0c14104ffecba1013fc434c803ffa024004ff14d43005dec4a0807fd3048015fe28a4009ff90f42077f8a498043fc515003bfeb2a6232ff08543005fec690813ff304c8077fb128402ff4c51009ffaa8a0027ff54d0c05f610a4209bf99131027fc65a1826fc6444067fe2928602ff841311affc21a1832fd6548061ffa9e8430ff5474200ffa809800eff624c803ffa028004ff54d4301fbc64990cbfe4150c65ff8828602bf9934110dfacaa0806ff634c0017eb226009bfd97400f7f8a0a086bfc544843bffaa2622cffd4142017fe209888bfe20d041bfe10a6001ffc4130027fca699002fd6348043fea828209ff197410aff8a5a008ffe32d0445ff2868209ff9074301fd8849000ffc3248405ff90a8203bf189400a7f843a000bff21d0409fea9a6009ff95142017f862908a2fd654c83ffe3128203ff90932027fc6299027be54d0405ff98a8209ff9534201ffc409906ffe604c401ffb226404bf18d21005fec098802ff605082ffea9e8001ffc434006ffc8298027ff42d0455ff28a8409ff9074002df8caa1807ff2050013fe21a8203ffc853204ff8a9a000bfe5144009ff29a6009ff9834100ffea08800afe61480057e30e8000ffd8d4201dfac5a1003ff644401bfe30a6009ff59741027fca6a188bfc50d0405fa10a4200ff59132007fec299007ff204806fff2968637ff14b4300ff481a008bfc20d0407de2128403bfd8d3204ffe86a004ffd515001ffe32a6000ff4c520027f862a1803ff43480017fb02642bff90d42005fac888027fd62d004dfe2826408ff90d100e7fca498813dc31d0c05fea8a2006ffd491004ff8c7a1073fe624c433fe29a4202ffd451004ff8a8a1827fe60d0c31fe2024201ef10140007fec4a0813fe304c859fea8a8409ffd8f4104ffcc3a1803ff6048465fe30a862cffd4542
  | 1 => 0x7be54d0013ffb2e8215ffc8740027fe63a1807fe504c051ff32a6400ef1913204efacba004fff6550055fe18a84059f19510197fcc2a1813fe434c8017fb224002ffcc5311c7faa1a1806fc6050833fe31a4210ff90540027fc6298013df324c4017eb0e8004ff10f431affca1a1807fe304c029ff18e8021ffd414101ffea4990cffe6250c13ff2168628ffd4532007fac0988b3fe6550803fe286801dff54131177f8a3a1027ff42d0013fea1e8403ff8c92105ffca690007fc504c0097e31e8009ff95341027fe61a1813ff3250c0fff3122008ff14d1001dfec8a100ffc4250843ff32a8204ff8c14309dfacaa0013bc4350c03ff1868003ff10b4201ffa8490803fe6444001feb028601ff10110027b886990affc5350805fe90a2012ff94d40027fe6098816fe65d0405fea8a8209ff10543005fec4a1887ff5350419fe2a24009ff1014206ff88298027fe65d0809ff9926009ff10740017fca2a0813df314c835ffaa24235ff8834304ffaa9a1027ff65d0015fe18a4003ff0c920017fc2090803fd644c063fe0828616ffccb40007fe8498027fc5450001feb12602cffd954200ffc8088013df304c849ff9968204bf98d10015fec298802fd62d0403fe1068005bf1954001fee4290887ff5250413fe3068634ff1954304ff8c7a08dfff21d0c23fe192800bff18d20107f8c6a0827ff60d0843deaa28220ff90d410e7fc84988a7fe4050805ffa8a8204ff0c132015fac3a0812fe6348437ff1026202ff8c53101df8c4a0807fc104c0357eb2a422cff5514204ffa85a0027fb4050001dea0e8003ff48520017fc428802ffc5348005ff90a6210ff0c54001ffc42a1003fd32d0451ff2a26401ff04340015fcc3a1097fd52d0435ffb2a4202bf9854200dfcc099027ff61d0c13fe30e8030ffd474204ffac5a0803ff644c001fea1a2004ffd4d32005fac688027ff63d08017fb12821bff94131025fcc9a18d7fc50d0c1feea9a6000ffd8d2012ffea7a0803ff644c40ffe2122000ff50d42007fac09080ffb2048007ff292420cff1952000dfec098013fe3250c13feb168601bf18343005fec2980d3ff5450c03fe202401aff54d2118ffc20a186ffc504c40dfe32a2003ffd4b4204ffccba0803ff424c407f71924212ff14d40025fcc7a0827df4350c0dfeaa2201cff1893100dfec490007fc4050001fe90a8006ff5951000ffe8088013fe30d0c09ff1926011ff9894000ffa608800bfc51440057f30a8604ffccb4300ffc209800fec4250809ef29a6001ff9012004ffe87a108bfc30d0401ff3226200ff509301aff841a18abfc515081fffaa26009ff1074304ffec5a0812fc6350001fe9928209bf1974104df8cba009bfe604c801bfb2a2009ffd53400affc65a0007fe10d0009ff9926204ff8c1310dff84098802ff644c805fe1
  | 2 => 0x40005fec6a100fee3248013ff20e8400fbd09200f7fc80a080ffe5250803f61024000af19132007fa86a0803fd6244009ffa9a6021ff1954101ffa849000bfe2150409ee29e8606ff99510007fa65a0027fc40d0c037f3028619ffcc12104ffcc5a1807fd4044009ff18e8600ff5854004ff8c7a0026fe6448007ff1924000ff50940027f860a1807fc304c003ff0824002bfd85410bdfacba0007de304c00dffb2a2007ff1491009ffea8a0013df324c0097fb228600ffd894317ffca7a1003fd6250c03fea868000bfd814305ffcc690047fe32500137e322622bff18d42027fe62a1813df30d0c13feb1e8003ff8812100ffc20a0013df304c4017fb0a8602ff0851004ffacba1077fe544c4017fb128038ff54b43007fcc899027fc4250455ff8828401fd0411001fd8a5a100bfc5150403fe1868003ff0854201ff8a4a1002ff6444007fe1928403ff0cb42007fec68801bfd53440137e3224009ff5974304ff8a9a100fec424c803ff8822031ff9414301df8c5a08d3fd5050c59fea9a8421ff5514111ffe41a0827ff43d0405ff90a421dff19531027f886a1816fe6550401fea0a6009ff18b4304ffca9a18abfe415086def18e8604ffcc143017fc828800afe614c0097e31a821fffc814100ffc41a0013fd324c4037f3028403ff94920097fcc6a0003fd644c4037e3068209bfd9741007fac0a10d2ff6550c01feb224203ffc8132007fac29000bff414c405ff18a4204ff8c543027f88698003dc6350403fea826005bf995320effaa498803ff614c009ffa1a6404ffd4f43027fe6298012fc63d0401feb0a6016ffcc7400c7f8a090813df32d0c23ff2928001ff94340007fac299027fe40d0809ffa9a6207ff1891004ff887a000ffd524c8017eb1e8031ff08143005fac89880efc62d0003fea024009ff90f4101dfcc5a0007ff30d00137fb2e8403ff08121017f88290807f61044011ff29a2033ff9094300ffe6098027bf41d0013ff2168025ffd4b411c5facba18affe5350813fe32e800cffd9520027f861a1807ff1050013fe2a2842fff14f4201ff84290003fd6448001ffb1a4218ff8c12100dfcc09089ffe514c805ef18a6209ff1034212f7aa9a08a3fd514c813ff31e8403ff14920037f8a8880cfff2150c07ff9924203ffd0921017fea3a0826fe6448405ff28e8201ff0813012ffea1a08167e65d000b7e32a6204ff10d31067faa690047fc5250021fe10a8007ff0c91000df8c0a1807ff1048007ff10e8404bf18f4200dfcc0a0827ff4350405fea8e8201fe1014004ff8c5a080bfd414c409fe1826228ffd413218ff8a0a180fee5248041ff31a8203fbc813209ffaa6a003bfe424c001feb128004ef90f43177dc43a100afc614801dff90a6009ff18341057fc829000bfc1048403ff1026002ff0c510015f8c2a002
  | 3 => 0xfb124234ffd4143197fca2a183fff524c069fea8a8603ff0c932127f8a7a080bfe4150403df2068000ffd0910027f86299006fc6048401feb126208ffcc91000ffc608800fff4250815fe20a4001ff0811004dfecba189ffe614c8057e30a8603bf9934201ffc84900a7fe3050801ffb0a8003bf9894000ffea1a000ffc20508017eb1e8400bfd912101ffc65a1073ff204c403ff1024004ff90d4304ffea9a1016fe65d0051ffb2a642dff84342017f88288007ff504c069ffa8a8604bf58f4309ff8caa0037fe514c001ffb0a4003ef9094208ffe42a002bfe3148023ff2128009ff90f4004ff882a1013ff434c403fe0822009ffd83431bffe41a1807fe504801bff30a6003ef90b4202dfcca90016fc654401fffa8a6002bf187420bffea5a00a3fc654c853fe0828403ff549210077e82a004fbe5450013ffb068205bf995310dff8c0988b3fc6550831fe1824200ffd8142017fe8290827fc40d0403ff2828001ff14120087fc62a0027fd60d081ffea8a6017ff5474004ff8a8a085fbd54d0003fc1826001bfd814000ffc60a005fff51d0003ee1826004ff14d3201ffa649089ffc614c84dff2026409ff18b4000ff84090013dc4350c05fd8822006bf5951000ff8a0a007ffc32504597fb2a8401ff08140004feca88003fd63500037e3026200ff99121137f8809906bff5348401feb222000bfd85421c7bea7a180efc6250c07f61926400f7d0d3204ffc81a080ffe52d0813f7a128404b718d41005fec6a0013be4350c05ff10e8202ff0c541067faca90003fd4244007ff9924003fbc8520017ec83a080fff424800fff1922009bf1913001ffc64a1027fe62d0003ff1824001fb88120007fac690026fc644840dffaa2202cffd51420177c83a0867fe6348403ff0822009ffd094004ffca8a18a7fe1050807ff9068402bf98540097fe64a00c7fc6050c09ef98a6034ff549431c7fea3a1867fc434842fffa9e801aff541211c7fea1a184ffe6550005fea8a6204f710d30015f8c2a1003dd324c413feb0e8401ff041200effea098813fd434c807fe10e8403bf1893001ffc4299027fc42d0413ff3068404fecc130027fa6498016fe654c0077f3126002ff94531107f8a6a0827fc41500097fb1a8600ff1913108ff8c4a0003bd4150013bf32e8038ff5474304ffca9a0006ff6048009ff21e8609ff10141017fa8290807fc10500097f31a8204ff90d3107ffca8980c3fd53d0871ffa96861aff5952104ffaa9a08bbff10d0805fe28e8200ff58543007fe8298027fd41d0031ff2824200ff19132057fcc290003ed324840b7e32a4209bf991301a5facaa1833ff5448011fe31a2009ffd074000ffa408803ffd524c03bffa926202ffcc521007fec488002fd634844ffe28a6409ff5874003ffca488027fc60d0805df20a8217ff54b
  | 4 => 0xcbfc5150c13ffa0a8002bf187430f7f8c0a082bfc614801f7eb2a6005bf19530017fa82880a7fc3050863ff1028605bf9952101ffc85a1013de43d0c017eb16800cff95120037eaa288003ff434843bff32a6209ff9974304ffccba000afc614c05dff18e8404ff50d3000f7881a0027fc41d0813ff2a28009ff50f40027fe86a1803fd4250413feb06820eff1093001ffe4090827fc42d00517fb2a6400ffd912001ffaa490007ff404c007ff1068403f70c93201ffca49907ffe3250405ff0828201ff5411001ffe43a1053fc51d0005ff98a2000ffd814107ffaa89800ffd3248055ff30a842dff94342007fec6a0887ff6550419ffa9a4010ff18540007fac68804ffd5250013feaa68008ff10d10005fac3a1007ff3044027ffa9a8001fe0411006ff8a29800bfd3148401feb1a4200ff4c94004ff886a100bfe41d044bfea9e8202ff0874113ffc82990cffc6250c47fe2968209bf1913201df8c488026fe644c835fe32a4202ef1074101ff88499027fe40d0c4dfe3026409ffd0d4216ff8a1a106ffe404c463ff3028609ffd8f40015fcc29904ffd6550057ff9828409ff197420fffca4a080ffe4250835ff2a24202ffc4341017fca290813fd534c80b7e32a8204bf18d2004ffac7a102fff3148007fe10a6403fbc81210edfeca98807ff204c0017fb126200f74c93001fd843a1007fc3048007fe2926403bf9891001fdc85a1002ff604846dff10e8600ff5052001ffe65a1027fc65d0c13feaa68600bfd8d41127fca7a089fff104c8617eb2e8421ff54d4119ffe40a181ffe424401f7fb2a6000ffd854300ff860a0016fc654c8037f3268000fb4c920067daa49000fcc324c807ff1028402ff885310d7fea09080ffc20d0805fe28a6209ffd974300ffaa0a000bfe3144003ff1022001fe08120027fa869880afc614c805ff90a2003ffc85420cffc8690816fe6550869feb2a8601ff941100e7f88498826fe6444001efb1a820eff98930005fec690003fd4150003fea824018ff98121015fcc3a00b7fc10d080b7e32a4012ffcc540027fe869808ffc32d0405fea8a4201ffc8340017fea29082ffc4348003fe2822000bfd893001ffea490803fc6444053ff2828400ff58d421b7f8a3a180bf44150413fe21a801dff551310177882a0827ff43d0055ff18a8400ff19130027fa629800bfc2150413fe2a68200ff9913001ffe64a100efc62d0c03ff9824036ff94743025fcc7a1003fd6150805fe18e821fff14941147faa899083fe535041dfe3126029ff14142017e86298803fd31d0013feb2e8004ff90d30007fec0a18bbfc31d0807fe296842bff98d42017fe20a0853fe51d0069ffa928601ffcc140097f8c6a003ffe654c003ff1028002ffd453102dfccba100fff2148013ffb168003ff9092100dfec8a00a3fc544c8057
  | 5 => 0x10000280e8260020f4040200480000080d0020bc030520100000502a00a000c381700609c0b00000c0000c81505c0040881400a0140180501e008150080140000007100c0040183c174000000000040500100501e2905281500414436035017fc62a0876fd654c409fe18a6004ff0c943017b86298873fc524c425ff21a801eff941410b7fca7a007ffe4250405fe20e8222ff8c34100dfec288003fd3150009fe18e860fff59530007fac4a0803fe6448001fe3224003ffcc9321b7f843a180ffd52d08597eb2a840fff1513004fee82a087ffe625043dff1028200afd9132087fcc2a0027ff42504037e3028200bfd81411b7fe21a180efe6250c07ffa126400bf58f4110f7ca8a0813fd53d0c05fe10a6200bf5834201ff84099007be405000b7e32a8413ffd4540027f8649800fef214c805fe0868220ffcc9410c7fc8090857fc32d0015ff28a4027ff10532017fc4290803fd604c813ff30e8014ff0c74010dfecaa0863fc6048403fe2068000fb18941027faa698807fe40d0003ffa824004bf98d4001ffaa4a1087fd6550413feb0e8605bf9954316ff861a1027fe61d0801ffb02641eff0814104ff8c3a186aff6548413ffb0e8010ff9454005ffc869009bfc104c805ff0868200fbd894101ffc649901bff5344003ffa828003ffd4920067fea290003fd4348401ffb224202ff9053107ffeca9800efe624c405fe20a820cff5452018ffc80a1827fc4050c59feb2a8404bf18d1004ffa87a0827ff61d08037f3026200bfd8910037fca88800ffc4248435feaa24200bf58910017fe828804fff52500037e3068400ff48530025fcc6900a3fd654c80b7f32a2016ff14f40005fac1a0813fc534c0057f30e8606df19510027fca7a1803ff6250027deaa28009ff50b4100dfac1a0002df635045fff98e8406ff54910007fa43a0012fe63d0043ffaa2821eff8c14114ff8c0a1027ff54d0401f7a126402ff14521035feca88003fd3244009f79926404ff94d31167fea6a1007fc404c0037f3068602ff0c5311a7fecaa1816fe65d0c57ff98a8409ff1534304df8cba18c3fd50d0801ffb126004ff14f43065feca900cbfe2150c07fea126404ff14d31137fc2099027ff62d0c13feb1e8228ffd513201fdc65a1027fc43d08097e31a8404ff0cb43017f820a0806fc604c83bfe2a26200bfd8d1004ff885a180bee21484017eb224000bf58343027fea6a1803bf644c809fe1926201bfd8110007fe829004eff6550003ff202602fffcc34201dfcc5a08b7fe30d0813fe2128600f7d0d30017eca288077ff654c41bff10a6029ff9814201dfcc5a1803fc6448469feaa28601bf983420dff88098827fe62d0401ffb126201ff0c110005fac3a1803dd314c001feb02822cff541420a7fc43a000aff6450447ff2968209ff58343047fcc688
  | 6 => 0x401581c088038040360b40007081d00100405c010124c24a807828000000088101120102080107600c0200713e0ec660370002146480403a5580c0040a2000188080000600004908e004000050080000c0000040b4000030f22702605e044058048000700002c01e00010c0307b006094268060040240600f59c05c038000740000c8100060000592000e324c88000000c4118070020d80107a00c0182c164000084420270001040107e000140040000000d4020010703040480203a0a41e80007c0800e01000400400057004004f48040000081500500002c0580305c0001f80001201c168160022941780025e11c030480640200a0af05a168038020061cc408050020500280e004514190130ae02809815006054040080047a80081d07c169578110040d4000770f22600086110e13c0303201603c2e12e00a0442300800202c0301e0c8000070360000e00280e026000050010140680100216a16c1e80e0043e81c0020060601385400219c0d80700603c0300d0002ec0804e0802900080e08e011c080302e0480580b0240000002f02a0001c8050200d00003900c01c098030020040002b00404c000aa00c00c0402d0001240303906c12c0000e0540000780312c06c0b0dd01200c0391b03c0282d805012008000170040780100200000000008004030020230000001781307c024048000a0128a70
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc744c920357ac41189410e6ee52d8931006ee60d8941296bd42d912002cfe75d8d401c6dc65d0d32004fc7650910006dc7359121305bd75d0540026df62d0d3202cfc75d8d2104e3f4159740006df6518d4137f9c4118d41004ff7650d20006bc71d913208eec52d89403c7cc32d913204edc4358f41004ff7158343004fd75d8d41256de644c93104ebc7319132006cf6318941004fd75d894300dda70d0d30015f47150d41006dc72d8d411b5df7359131007ae54189411e6ef21d8910027db60d0d300067c7159740006ef52d894002cfe755912104ebd7119132006ef624c940006dd70d8d41004ff75d85303c69d73d9132077cc624c930014fc7458b4104edf7358f4227eec42d81320057d7599110004fd755912000cfd73d91300079e5418d4121f7410d951021f7471d951003eec32d89101b6de51d8d4115ddc7358542005df7358540026dc634cb4104ebd7519132024ee76d0932016ee6148520006f751d854000cfc70d8941006bf10191323bebe301913201edc764c93100dec70d0920004fd76d0910024fd72d91320067c2159740256dc644c9303c7ae72d9132006df53d8d4020ebf40d9110006f771589102a5df754c53026eef20d8930006f551d853201cfc72d8d10004ff765093106ef46158530004ff764c520006df6350d410fdec725814104ef7715874201eec624cb40006df735913100dbc7050540006ef7258d10006ec70d894101eef63d093200cfd72d8520014fc7458341006df72d8d4100cfe70d8d413cebd43d913202cfc75d8542004ff7158342006bf65d9132004fd7558d21056f621d85200067d654cb4002cfc75d813106df471589300cede53d8d2104e7e4059740006bc75d9132006be43d9121006be51d9132256df64d0d3200cfe70d9110007cf434c921004fd74d81312cedc43d8930006bd641912000cfc70d8d4132e7e705974000cfc705913104efb4058342006ef651894119dec725854332e7f3059740006bc10d9132347cc32d8532006ee50d8941006bf6458532004ff725913104cff76d0d21016d4614c530096de43d8d40076ec6258930005bf744c941006ef50d8941005df7358141006bc7458d1032e7e105974001cfe7458742014fe71d91303cebf53d9132176ef51d894100cbc765054001fe7614c92104cfc7458d2104cfe74d89101b6df10d8d41137d8704c93013ef651d8532006ee20d89410057f755853004eef7258b4039eec40d894102cfc75d913003eec625891036df77158931014fc71d8940006be61d91320067f7559110014fe76d853001cfe76d8931004ff7559130004ff75d9121004fc764c94101cfc7650d42076ee32d8930016be61d0540007cd324c520004fe764c94002c7c7558d20004fd76d0530004fd74d8d20014fd73d91311b6dc41d8d4106ef421d8530
  | 1 => 0x8d10004fe7650d20006ef624c941006df624c530006bf7458910005ed71d0932235ee744c92000cfc70d8520014fe76d8540195dd7399131006dc70d8d41006ef52d89413e6df43d8143006de50d8d413c4fe761913200dbc70d0540024fc73d8940006be43d912001cfd73d913202cfe75d9131006be41d91201b6df51d8d41176ee61d0932006ee40d89411beec42d8d42004fd755913104cfe74d8d10014ff73d9131026dc6350d42004ff75d8d1001eec62d093101def734c920006df50d8d41006de70d8d410e6ec20d893101cfe72d9131004ff7558d10005ef72581313c6bd72d913202c7c7558d10006bf7458d10357ae411894100dee76d0920006bd5458740176ee10d89410e6ee62d8931006df43d8132004fc7650d21004ff7558743004fd72d9110004fd72d8d413aedc40d8d4104ebe641913104cfd70d8540004fe764c52001cfe7259110006ec53d8941026ec634c921004ff764853002cfe755913204dbc744cb41006bc40d9132004fd75d8d2114ef86058142006ef30d89410079c73505400059c744c930004fd73d8142014fc7158f423bebf5319132014fe71d894002cfe7558d1000cfc70d89312267e31d95100067d7359740006ef631894104ebe73191321b6dc10d8d4137f9e4118d410079f64d0d32006df6350d40006de32d8d1000cfc70d8542025de734853004ebf7119132096dc6358d403b6bf2119132024fe73d854002cfe75d81313cebd31d9132005f77158d2002cfc7558b41024fc74583433c6be20d913204cfd72d814204cfd73d814304dbc744c940005bc7458131004ef725913114efa60d8142006df63d0d21024fc73d8540006bc42d9130004ff75d9130206df31d8d1029ddf75d0d30334ff7258d21004ff75591323cebd30d9132006be50d9132105dc73589410e7cc624c931004ff7259130024fe7458343046dc32d8d10006bc43d912004cff76d0d1000cfd71d891001cfc72d853000cfc73d8131006bc41d9120024fe73d9121024fd72d813200cfe7458f400067f65d0910137cd304c920006bf51d913201cfc7258f40004fe764c5400defa10d813104eef4258b4104cff7659130006df7358910004ff7059121005df735053004cfc76d0d1004ebe7119132014fc71d814204f3e6550740006ec65d8941106de7618d4104cfe74d81211afda70d0d3000cff71d9110004ff7158b40256ee644c920014fc7650941024fd72d853215edf3058b43004fd7558f41004ff7158d20005bc7458532004fe764c9101d6ef20d891002cfc75d91320063d65507403afd741d8d4100ddc764c93001ede624c93102cfe75d9132014ff70d8910006be54d9120004fc7650931014fe71d8d4004dbc744c94132e7f70597403b6bd20191320067f325974001cfe725874308eec21d8940335ef7258d21005a
  | 2 => 0x5bf7458d2001edc764c930006f77159110006be10d9132156ef2158b4108eec425912018ef8605814301cfc72d85433bfaf3219132014fc71d8132025df714c5302267f21d9510005df735812102cfe7558f42004fd76d0d10006bc64d85323cebc53d913202c7c7559110006be42d9130024fe73d8910004fd70d89410067c32d95100feec52d8941006be54d913119eef2058f42005ef704c92104ebf6550740006ed70d8941346ef20d85321cdf7715891035cfe7619121006bd65d9132006ec60d8941176ec2158742006f610d8532007e7714c9213c6bd73d91320067e32d9510025dc7350930007bb70505402267f31d9510006ee53d89411b6dd51d8d41004fd73d912101fae74d0920006bd511913231dbf7550740006be51191320073d751913213df4715813220ebd40d9110235ec744852000cfe76d8141106df30d8d41007af744c921004fd73d8941004fd74d8d10014fd70d8d10004fd75d8520006bf6519132256ee644c921005bc7458d2000dea70d09201d6ed20d8910006ed73d8941004ff75d8543006be54d8141006ee75d8941004ff764c9403bebd311913200cec7648520004fd71d8143005fb7050d403cead72d91320067d72d95100defa60d8131006de60d8d41016de614c530006be43d9110014fe71d8d20014fe7458b41006bc10191320f4fd769911029dde744c93001cfc73d8930274ff7358d20006ef6258141216bf41d9110004ff764cb41005ef72585301667c6550910004ff755874024ef521d8520006be611913204edc4358f42137cf304c920196f4615854304ef7715874004cfc76d0530005dd73d912000df8705054028ebd40d9120006ee21d894001cfc725913027fcc32d8132014fd72d8d213cebf30d9132004fd75d8142196f661d854327dfb7058d2005dde73d9120006ef6348520016f461505402267c31d9510006ed32d8121006ef32d8941004fd70d8d4201eec62509400067c74d9510216bd41d9110014fe71d891004ebf731913204cff7659110006ef725911004cfe74d8131006bc40d9121176ee71d894101cfe76d8910016ec7648520004fc7650530005bc745852001cfd71d9121025dc73d09300067c7558d2002cfc75591312267e71d9510006bd54d8540136fa30d8132296ec42d912001cfc7258743016be6150740004fd75d8532006ed50d894104e7c425974001cfe7258d10006dc735911018efa30d8143024fc73d8910005bc745853001cfd70d91200067e2159740024ff7658d10006bc43d91100067c65d8910014fd73d8131006be75d91321addf7359130007ad54d894126def7258d2001def7148520007ac725054008df97099120026dc63d0d1001cff73d913200cfc70d9110257cd72d0d3200cff73d913004ebe641912101cfc7258343006dd75d8d410357c755
  | 3 => 0xc6350941004ff75d8532004fc7648540005dd70d0d32004fd70d9131006be40d9121006dd32d85300067c6558d1001cfd74d85423cebe53d913200cff71d8910004fd72d9130004fc764c520006df635814102cfc755913200cfd73d853016efa2058342014fd73d89310067c72d9510006ef62d0931106df32d8d412e6dc43d91302e6bf43d913002cfe75d8910024fe76d8d4021e7f71d9510086f661d854004eef4258b40004ed72d9130024fe7359120176ec71d8941006fb705912002cfe7558b41006bf5119132014fc7158b40006ec7259110154ff7159121005bf745853001eec625094104ebc751913204cfe74d89300c6f86058121006ed52d893102cfc755834201cfe72d9120004fd71d9132005bf7458121024fd70d8930006dd50d8d4100cff71d8d10006df52d8d41176ee61d0920014ff70d91100057f7558d2029edd64d0d30006ee63d8941006de31d8d201aedf30d8d40006f7715912129f9c64d0d30007cf624c9310657c75585200067d654874000cfd74d8540176ee2158742006be5019132024fd70d8530006dc52d8d410c4fd72d8910004fd76d0520004fd71d894329ddc744c530005f77158930006bc65d91320057f7559110014fe7158b403c5be7619132004fd73d812102cfc75d8540004fd7558f40006df7358d20016dc764c530006ec7258d103be9f30191323c6bc21d91320067f65d89101edf77158d10004ff75d81423b7cc3219132006df634c941007d7614c5302eebf6550540004fe7650530386bf41d9131024ff71d913121e7c30d951001cee72d9130004ff7258f4004e7d74597400079d54d8d41005df7358910014fc71d8910006de40d8d413bebd3019132006bf7459130006bd50d9132024fe76d8d100def8605813102cfe75d8943006df7358d10006bf70d9132004fd75d9121004ff7648740004fd76d0d20106dc53d8d41004fd74d891021f7610d95101b6de10d8d41134ff7058d200047f7559110004fd71d8930004ff75d9110004ff75d813102cfe7559131006bd54d913021e7f20d951017eee76d0932004df7358910026dc63d0d213c6bc52d91320067f72d95101b6df74d8d41004ff7058d213c6bf52d9132004ff7358b40004fd70d912108eee62d894000cfc70d894300cfc7650d40257cf43d09320e6ef2058d2102cfc75d8d2004cfc7458d10014fc7159120007cf634c92018cff705913004cfc764cb40014fe7158343005bf745813102cfc7558d213c6bf73d9132004ff7158f400feee74d8941006dd72d8d413b7ac72191320357c7559110024ff70d9130005dd71d0d3002cfe755911002cfe7558343006be40d9132024fc735912004e7e42597400067f715974004cfd70d894002cfe755874021e7f40d951000cfc7458b40046dc43d8d10004ff764c910014fc7158b43
  | 4 => 0x89410067e43d951000dec7048520007ac744c921024fc7358b41004fd75d89100067f7359740006ed54d8941004ff764c740006dc6218d4104cff7659120014fe71d913204efb705834101cfd73d8132005df714c930116fa10583412f5bf75505402267f41d95101bfcf21d0d32245fb7058520397e7411894108dec7250540004fe7650931006dd6518d41004ff7358910096df32d8d401457e7519132004ff755912137edf6418d410e5ec725813104cff76d09100067f6558d10356ef6118941006ed32d8520004ff7458d1001cfd71d8121006bd71d913204e3d751913200cfe7058d21027cf724c931356ef6418941004ff72583432267d41d951038ebd43d913104ef7715874328cfe761912021e7d20d9510237e970d092001cfd74d8d422b6df32d853004ef84058342026df614c931014dc764c9310067c7359740024fe76d8d2104cbc7458d21014fe71d813202cfc75d8931006bf745913102cfc75d81410feee42d894100cfe7458740007eb7048520206dd31d8d100cede63d8d21004ff7558d2132e7c20597403aedc42d8d41016ec614852004eec4258b43004df73591211a67c6550d10355ee76d8941096dc53d8d403bebf301913208eee42d894001cff70d91200067c43d9510106de53d8d41004ff75d8d4002cfc75d812133cff7358d2102cfc75d8532014fc71d8143004ff75d91313c6ae72d913201cfc7458f4216cff7259120357e44118941005ed73d09203c6be21d913237edf6118d4101fcf734c92101dec72505200067e715974037dde76d8d4104ef8405834102cfc75d814332e7c705974000cfe70d893117def72591322267c41d9510156f661d854221e7e30d951005edc31d8d2013fcf314c92137fd44118d4105ddc7350520005bc7458d2101cfe745834219eee62d89432c5fb7058930005ef714c920006bf64d813204cfe76d9132025ce73d09320feec6258941004ff75d913221e7f10d95103c6be72d91320b5fb7059130014fe7158f42156f641d8542006df634c9401bcff735913213ef621d853200cfe76d813104cff76d0d20005df735912104cfc76d0d2002cfc7558b40005bf74589100067f655091019eec52d894300ddc764c53005ddc7358520007af64d092000dec764c920025de74d0d3032e7d1059740027d7714c53001ede624c93003eee62d8910096df325834302cfc75d8142024fd74d814313fd4714c9310067c65d8d10006ef52d8943106df3058743026de634c52000cfc7458740014fc71d8930136fa20d8132006dc6358941004ff764854004cfc76d052001cfe7258f412febf65d0540024fe73d8121006dc60d8d41386bd41d9131005f77150941006ed651894104e7f435974001cfe72d913000cff72d9120176ef62991211b6dc21d8d41004bf7458910004fd75d894015ed
  | 5 => 0xcfcc434c921025ec73d09323c79c32d913204cfc76d0d21024fc73d89410657c7558d20004fd72d853007d7e7599130004ff715913004cfe76d913000cfc7058b430f5f57199110006ef42d8132004fc7650d20006bc40d91310067e7259740007cf63189412c6df31d8132265ed75d09200c4ff70589100e6ee32d8931004fd764c740004fd70d8d2102cfe75d814202cfc7558f42006bc651913239eef43d8941004ff75587423c79e32d9132016bc765054019eec6250d41024fe73d8141174ff725912104ef44158742024fe73d91100057f7558930015de714c9313b6bf32191323cf9f31d9132006ef63d0920014fe76d8520004fd71d8d4204edc4358f400067d7159740014fe7158d2002cfe75d8d20026dc6350d4100dbc765054004cfc7458d20024fc74d8d40004fd74d853204cfd71d89413c78c32d9132006ec50d8941006bc60d9132006ee65d8941005fb70505400067f65d8d1000cfe70d8941006ec73d8941006bc70d913201feb604c92000cff72d8d2019eec4259132006de31d8d42014fc71d913002cfc75d8543024fe735911033edf31d8d213b6bc211913223ded7548520004ef7259110005ef7259110024fc73d81413b6bd3219132176ed71d8941336ef21d8931174ef7259121076ec4258d20027cf724c93001cfc7458342075ec725853014cfd7699120004ff725911004cfe76d91100e7cc424c931004ff75d89433b6bc5219132006ee70d8941045dc7359110186ec65d093225def754c92000cfe705913220cfe7619110006ee21d8943256dc644c931005bc7458930004ff75d8d420067c73d9510004ff7358b41006dc65d8d412a5dd754c530106df3258743004fd7559132005ed7348520096de63d8d403b6bf521913202cfe75d8941006bf75d91321b6dc61d0d3204cfc745891001cfc72d9131024fc73587403c6bf32d9132004fd76d0d211f6dd30d8d1001dec72d0d20026ee634c92104f3d6550740024dc7359110005dd7348530004fc76485300feee52d8941095dc73505401fdfb7058d1002cfe75d911000cfe705912101cec7259131024fc73d912016fea70d0920006be101913204cfe74d8d20006be761913218cfd7699130025ee73d093221e7d40d9510024fc7358b400057f7558520004fd71d8d4001cfc72d9120004ff705874201cfd70d8520007db704c53003fcc324c9103bebc5319132006ef7259120175ef725912102cfe75d812100cfc70d9132057e4614852002cfc7558740026cc634c920014fe7458f4101cfc72d814300cfe76d81321bfcf20d0d3215ded7299132005bf7458930024fc7358342006bd651913200cfe70d9132006df73591322267e41d951001eec62d091001cfe72d81433a7d74118d4101cfe725834102cfe7558d2002cfe7558f40006df7359110006cc631
  | 6 => 0x77158d2104ebf60505400067e3159740004ff7258341256ec644c9213b6be2119132006de75d8d41004ff705913102cfc75d8941024fe73d8142006f731d8520286ef21d8d20006dd32d8131006bd545911019ddd7399132004fd75d8d20005bf7458931014fe76d8532005bc74581320feee62d8941006cf63d8941026ec764c921024fc7359110005bf744c910014fe71d8930006de52d8d4101ecc624c930025de74d0d32004fd73d85203deef42d8d42004ff755834301eef604c92021e7d30d9510007af72507401f6df30d8d102dedd73d9130026ec634c92019eee42d894303dec725911000cdc764c93001cfc725911002cfc755874302cfc7559120006bc50d91320c6fa20d8121024fe73d89413c4be7619132004fe7648530006dd634c91002cfe755891002cfc7558f41076ec21d8930056f431d852004e7f4259740014fe71d912001cec7259110006bc64d81320cedf3058d2101edc624c9300067e62d9510004fd75d8530006be65d9132004ff7059132256dd64d0d3204ef74158742015ec714c9210067d7259740006ed52d8941075ec7250530006dd53d8d21007cf434c92021e7e20d9510004fd76d0930006dd54d8d41004ff75d8d4104efb405834304ebe641911001cfe72d853001cfe72d8543006dd63d0d2031dbd755074004ebc72191320e6ec6258931025dc7350530004fd72d8143006ec631894101cfe7259130004ff764c540014fd74d81410f6f86058141006ee73d89412ceed32d8930006de20d8d41024fc7458743027d7614c93118efa40d8143007cc63d8941384fe7619131004ff7058743006bf6499110005ef7258d4104fbb60505403c6bd21d9132006be70d913218efa60d814321e7c71d951006ef631d853036edf30d853201dec72d0520004fc764c54004cff7659121016bc615074001eef614c92100cfe70d891015edc31d8d42006bf7458d2102cfe7558b403bebe5319132004ff73591213cedc43d913202cfc75d9120115f77159110006be60d913202cfe75d8143077cc424c930256ec644c92017fce73d093201cff71d8d213eedf43d894321e7c10d9510006bd54d9132176ef71d8941024fd71d89310f4ff7059110176ed10d8941004fd7558740004fd73d814119eec21d8943014f47158d20004ff7558b4100cfe7059131006bd5019132004fd7558910014fe71583420cedc30d8d2104ebe641913000cfc70d9131004fe76d0930006de42d8d412267d31d9510004ff7458d200067f6550d100feec20d894114eef2058b40004fe76d093102cfc75d91210057f7558d1002cfe75d8532016dc614c530006ef62d8141006bd5458341007af64d09320047f7558d10106dc6358d41004ff7650d2101cfc72591312bddf754c930005f7715813204cff7659131006ed6318941006be71d9132
  | 7 => 0x91103b79c3219132006dc6518d410aeec42d8142004ff7058b4100dde70d0d303bf9f3119132005df724c530014fd70d9110004fd75d8d4218ddd73991303c6be52d9132046dc6358d10005ef7259131004ff7559120006f721d853002cfc75d8d403b79e3219132006ee601894101cfc7458742006bd51d9132006fb50d8141006bd70d9132006bf50d913225ded754c92002cfe75d8931004fd71d8132006bf649913202cfe75d89403c6bd52d913219fcc3259132004fd76d0931006ef72591312febd65d054002cfe75d8d2100cfc7058d21006de6018d412c6dc43d8132014fc7158f40006df63d814104cfc76d093019cff7259132006ee21d8930014fe7159132006bc42d9110006ed634852002cfe75d8d413c7af20d91320067c3159740024fe735834200cfc705913204fb771507403bebd5319132004fe76d0d212eebd6550540176ec61d092002cfe75d912103eee3258910006dc20d8d4100cfe70d8d213bebf3119132006be40d9131006bf50191323b6be20191321c6de65d0d322579c64d0d3213fcd314c921006ef32d89100cedc43d8d21006bd641912104cfc764c740005dd71d0d32004fd7558342256ef64d09321b6dd21d8d41006bc601913227eef21d81321467c654c91000cfe70d8532004fd70d853204ebe75191323cf9e73d91321b6df6399131046de63d8d100b6dc43d814302cfc7558343004ff7558d2001ddc72d0d3234eef20d8d2102cfc7558910006df73591300ee7e654c7403c6bc20d9132004ff735874002cfc75591300067c6599110004ff76509101b6df71d8d4100cfc70d8d2102cfe75d912014ded729912015ede63d8d421b6dd10d8d41006ef65d89413c7af21d913200dde76d0d302aedf32d8131004ff765093019edf3258f42004ff75d8d2117fcf31d093213ef410d85323c7ac32d913201fcf63d0932236ef64d0920004fd75d9131006bc64585320067f72597401b6f6315874321e7c40d951021e7c70d9510004fd75d8131005bf745813201eec624c94001cfc72d8141004fd764cb4102cfe7558341024fd74d854305ede63d8d20026df604c530106de63d8d41014fc71d9120176ed74d8941014fd74d8941004ff764c941004ff75d8141004ff75d893102cfc75d8d41046df3258d10106de43d8d41004fd73d89401b6dd74d8d411b6dc74d8d41004fd7558d10006bd6419110006df63d89411b6de41d8d41077cc3258132006de65d8d410057d75991201b6de21d8d411b4df735913102cfe75d853004ebf60d0540086f46158540004fc764c91002cfc75d8943006ec75d8941006bd54d912104ebf7019132004fd7559121006bf74591103cebf43d9132004fd73d854204fbb60d054001fae74d0932004fd73d911001cfc72d8131006de30d8d2104ebf751913201cff71d9121345f
  | 8 => 0x6df65d8d41006dd73d91200067f215974001cfe76d8943006be651913204efb705834200cfc705912104cbe76d9132007af7250540014fe7158b4333edd31d8d2101feb6048520006bd54d91201bfcc329913204cfe74d893121e7e10d95103b6bd2119132004fd70d89430067f6599110004ff75d8121007d7714c931006bc42d9131006bd641913102cfc75d89401b6de61d0d30177ae41d8941004ff715912004edf7358f41006df75d8d410067e7359740014fe76d854300ddc70d0d30004fd75d8143006df43d893000cfd74d8d40085f97099110014fe7159120007ad541894132e7f2059740004fe76d05303b6be521913201eec624c941004fd75d812100dec76485200cddc735912104e7f4059740006be601913204edf4358f41014fe71d8943006dc50d8d41176ec74d8941004fe7650d2132e7c3059740004fd755834128eed72d91200f6fa60d814104cfd70d8d40014fc71d8d10004fd75d89410067f73d95102f5bd7550540026dc634c94102cfc75d8d42004fd7558f42004ff7458d21004fe7650d1029fd970d0d30004ff7158f42004fd72d81310079d5418d41006f47158d20014fc71d8d20004ff75d9120004ff75d854000cfe7458b40006ed75d8941004fd72d8141026ee634c92000cfe7058f4208eee32d8940025df724c931004fd74d8d2139eec54d8941006ef725891000cfd72d8d2006fd4614c530004fc7650d101ccff7158910024fe73d8940006ef63d8941005ef7258d10006bf6499120004fd755874202cfc7558742004ff7358742007e76148520006de62d8d4104ebd72191322bddd754c93000df8705094001cfe72d8d1000cfc76505401cef710d8520356ef6219121004ff7258d1002cfe7558d2101cfc74d89400079f7350740004ff7558f4200cfe7058f4101cfe72d8141024fe73587420067c3259740007cd3248530027db604c5300073e7519132004ef7258d1021e7f30d9510004fd7558b40005df7359110006df7358d21006bf6499121006be54d854000cfc70587420067f31597402debf40d9130006bf71d913204ebe5458740186ee65d0932236ed64d092008eee3258342014fc7158342006ef7258d21177ac41d8941006ec651894101cfe72583430067e325974019cfd7699132026ec764c92000cfe70d894304cfd72d8d42006dd52d8d4107d7c755893001ecc624c931024fe7358740024fc7358742004df73591100ed7e7519131006df6350d4202cfe75d854213ef46158532005bc7458d10004fd71d8142006bc61d913203eec42d8910005ef7258543257ac64d09323b78c321913206ef661d8530004ff7558342006bc745891004ebe7219132134fd73d8d203cebd53d913204cbc7458d10007ae54d89410067c7558d100057f755813201edc624c931004fd72d85400067c655
  | 9 => 0xd73d912001fe77148520004fd72d8543096dc4359130024fe73d852000dde704c5303b7af201913204eef4258b43024fe76d8d4239eef40d89411acff735913004cff765913201eef604852004eec4258b4104e7c435974001cfe72d8d201b79c41d8d4104cfe76d9120005bc74581213bfaf721913200cfd72d912000cfe70d8543014fc73d853001cfc72d8d20176ef21d894102cfc75d8d10004ff735911002cfc7558d2032e7f1059740005bf7458d10006dc735891004cfe74d85323aedf42d8d4101cfc72d91300057f7558540086f451d85401c6dc65d0d30006ef6250940004fe7650520095f970991300cfcf304c9210feec32d89410079f744c930006bc54d9132004ff75d894100cfd74d894013ef631d85323cebe31d9132024fe735834101eee624c910004f77158d20176ef31d89413b7af211913232e7e30597403b79c7319132024fe7458b4300dee70d0920136fa60d8132006bc41d913001cff70d8d2000dee7048520004bf7458d103b6bc20191320feee32d8941156f621d8542007b7615054004cfe74d8520006f77158d10014fe745834100cfc7458f400079e54d8d4121e7f70d951004e7f745974004edf7358f40257cd73d0932176ec61d09320f6fa40d8141006be54d913004fb7715054018edf3058f40004fd75d91300067f655911002cfe7558b4302cfe75d854304dbf715054000cfe70d8542024fe74587430067c755891009d7c75585403c6bf42d913204e7d42597400f6fa10d8141004ff76505300adfb70591203c6bc72d9132237ac64d0920006bf745912002cfc75d8520024fd71d9131005df73585200057f755814101def734c921014fe71d8d10006ec6018941006bf645813223def7548520376df30d8931006ec625814100cfe70587430ed7c755813101dee74d0920026dc6350d401aefa305834302cfe7558742006ee20d89311eef710d853016eef20d89400f5bd71d05401b4ff7359131024fe73d8542006de73d91202267c21d9510006dc6018d4100cfe76d8142006be42d9110005df704c9310067c62d9510196f631d8543005ef7348520014fe71d8d42005bc744c9100057d75991301c6de65d0d300067e73d9510025df724c930024ff7658d21007af744c920006bf7459132004ff7359120004fd765091002cfe7558743024fc73d8121014fc71d8d42176ee31d89411ecff7158d10006dc63581410067f654c9100c6fa10d8121176ec51d8941024dc7359121004ff764cb4032e7d705974010d7c7558141276dd30d8d200afcc324cb400079f744c9310067c6558910004fd7650d21004fd72d8d40004ff7558910186ee65d0920006bc501913217fcc43d093202cfc7558b43004fe764854001eee624853015ede43d8d420067e63d95100279e74d0d3021e7e40d9510014fc7158343
  | 10 => 0x8d41004bf7458d203b79f7319132004ff7058f4101cfd70d8d2001cfe72d8131024fc73591213c6bc32d91322b6f531d853002cfe75d8d10006ef62509410ffcc324c94100ddc704c930004fd71d9130006de31d8d403cebf31d9132006ee72d9130026de634c9100067c65d9110246ee32d812100ddc704c530007cf424c931005df7350930006df70d8d4116def725912004cfe76d912102cfc75d913104e7c415974029ddc744c93015edc6358d42026dc634cb40005fb7050940024fc73d91100079f64d0d3005edf3158d20316bd6550740256ed64d093205fcf314c920004ff75d8132006ed53d8941026de63d0d203cebc31d913204ef4415874308eec6258940005df73589410feee3258742006fb705891004e7e415974000cfd73d89300657e759912001cfc7258f41004ff7558f400defa30d813104e7e4359740006ed63d0920006bd54d913104e7f41597400057d75191311d4ff72589102267e21d9510366bf42d9121004ff7058b43004ff735834204cfe76d913104ebc7119132006be41d9130004fd75d813202cfe755913001dde76d0d320067d74d951004edf4358f42024ff72d9132006df53d8d420067f655891001cfd71d8d2104ef7415874304e7d405974000cfe76d8143024fc73d8542024fd70d9130014fd74d8d41024fe76d8d20014fd72d812104cbc7458d20014ec764c9210079f73505402debd40d913000cfc74d8141006df7359121006bd54d814100cfc70587433b7ac3219132004fd71d894001cfe7258f40006bc51d9132006be42d91311b79e41d8d4114cff70591200feef20d894100cfe70d8d10004fd74d8530015f4715094100dbe7050740004fd7559130004ff75d8d200067c63d9510004fe76d052002cfe75d89303b6bd52191321467e654cb40014fe7159130024de73d9120006fb7059130004fe7650930276df30d8d2002cfc75d813200df87050d4000cfc72d8121004fd75d8542005bc745891004cbc7458910004fd7650d1004ef84058343235ec744c920006ee631894104cfc76d0931004ff7558f4100cfc7058f4204ebe7019132004ff75d8910004fc7650930014fe76d85423aedc54d8d410067c42d951000cfd71d8d10004fe76d0d201e6ed21d8910014ff70d8d10006bc611913201cfc72d9110004ff7258f41006bd6419130156f46158542005bf745852032e7d205974007d7c7558530004ff75d8143014fc715913204e7d41597400067f74d9510026df604c93004cfd71d8d41256de644c93000cee76d09201b6dc71d8d4119eec6258943004fd74d812126cff7258d2000cdc764c53004cfd73d854301cfc72587403c6dd73d9132005df7358542024fe7358b41014fc72d8520006fb705911001cfc72d8d4102cfe7558f410cedc6358d210067f32d9510006ef75d8941004d
  | 11 => 0x4fe76d0910155ed72991212e6bd43d9130006f77158d203bebe311913200cfe70d9131014ff72d9121114ff715911002cfc75d8530006ed65d8941005ef7250520006ee43d8941095dc735854032e7c105974004ef441587400dcfd73d8d10024fd74d89431b6de61d0d32106dc30d8d4103dec7258d1004cfc7648740024fe73d912000dbe70d0540105f5719913104eef7258b4302cfc7558d1019eee32d894302c7c755891004cfc764cb4100cec764c920014fd745874004dbf75d054002cfe75d9130015dc764c93100cfe70d8d4200dde704c9300357c7558910004fd75d9110005ed71d092034edd32d8d21004fd75d91200067e42d9510176ef41d894138ebf43d9131005ef7258141006df20d8d41176ef10d89411b6dd71d8d41004ff75d8542004fd73d9120004fd75d893104dbf7650740177e441d8941176f621587421b6de31587431b6df21d8d4129edf64d0d3004cfd71d8141176ef74d8941175ee7618941075ee72d91300047f7558d200cddc73581210c7e87048520006bc7458d210e7cc325853202cfe75d8540024fe73d9130154fd7699121004ff7558341006bf649913100cfc71d8121006bd6419132014fc71d8943004ff7158b432277b10d9510014fe71d91103cebc30d91320f6f7105874011df771591210067d654c740024fd71d813101cfd7458b4004e7d43597403aedf40d8d413c79d73d91320057d751912105fcc634c920024fc735834101cfe725913139eec43d8941014fc71d8d40105dc7358141006ee30d8941004fd7648740006ef725912104ebd7319132007ac744c9200fdec7258d4101cfc7258d10106dc32d8d4100cfc70d8d100d57e7519121014fe71d8143004ff75d85203c6bf20d9132007cf634c92101cfc725834101cec7258d10004fd75d8543007cf424c930027cf62d0d3214efa20d814204efb70583433c6bf72d913222d7e76d9510056f46158520004ff73583410079c744c931006ef72591320dfd8704c530006df63d0d10005bf745853200dee704c92013fe4714c9211b6df31d8d41006ed72d913001eec624cb41006fb7058d10027db604c93008fcc324c9400d57c75581210279e74d0d321c67c65d0d1001cfe72d91101beee3258b431b6dc51d8d4100dec704c92002c7e76d951004cfe74d8d213cf9f30d913211fcc324cb4101fcf734c920005bf744cb4005edc6358d2039eee54d89412d5dd75d0d30006ec30d8941286dd32d8d203ceed72d9132004ff7650d10014fe71d81423c6be32d91323c6bf21d9132006ef54d8941004fd70d8931004fd7559110007cc6318941004fd7558343004fd75d89300067f755891001cfe76d894002cfe75583420c6fa60d8121014fe7158f40025ee76d0932004fd7650d20176ec31d8941015ec764c9210067c65191101b6de71d
  | 12 => 0xc41d89410057f7558121014fd70d891004eef7258b4101eef60d0920016e4614852000cfc7058b41004fd74d852004ebf7219132004ff7558b43055f47158d2002cfe75d8132006bc7458d20006df54d8d41016bc6150540024fc73d81421bfce72d0d3200dbc70507400e5ec725913102cfc7559110015dc714c931006bf54d9132004fd75d913215edc53d8d42096dc31d8d400067e72d951029dde744c53002cfc75d8930006dc63d814117fcf30d09320e6ec42d893104eec4258b403ce9e73d913221e7d10d9510006dc75d8d41004fe764c941007eb704c9201f4ff7358d1004e7c4059740006de30d8d4101cfe72d8d41024fc73d912101cfe72d8d40015ee714c921006ec7259131006fb7058d2024eee32d8520006bc41d91320067f65d0d1001cfe7458f423bebc311913217edc43d89430067f6519110196f641d8543006ef73d89413cebe73d9132196df3158f41086f641d8540004fd75d8d401b6dc61d0d30004fd70d854321e7e70d951030dbe76d054021e7d70d951004ebe76d0540006bc51191320e7cf204c9311b6dc3158743004ff75d894032e7e205974001feb60d0920004fd75d8d10004fd7558d20006be54d9132025dc73d053002cfe75d8d42004fd71d91200067e74d9510004fc764c94000dbe70505403cebe30d9132004fd7558b41004ff75d893034edf32d8d2115edc43591320079c744c93005fcc434c92019eef20d8943006df6350941024fc73d852005edc4358d20006bf10d9132006de32d8d41076ef2158d200357e759911002cfc7559121006ee6518941235ee744852001cfe76d8941004fd70d9132014fc7458f4116eee76d0920176ee41d894104cfd72d85420067f65d911015edf30d8d4201cee76d8941006ef7258d20005f77150d41005ef725054013fcf214c93100cfe70d91210057d7519132006dd53d8d4113cff7158d2101dee724c520006de6518d412267d21d951032e7d30597400067f7558d10006bc645813200cfe7058b41026dc634c940004ff7650520024de76d8d41006f76150540005bc74589310feee7618941004ff725874300cfd7458341006cc63d8941024ff7658d20006ef53d8941004fe765091037edf6319131056f661d852002cfc75d911001cfe76d8930296bf42d9120006dc63d89410dcff7058d10024dc735891004cfd73d8943024fe7358910024fc7458b4304ebe5458341014fc71d911021f7771d9510116f710d85403c6bd42d91321bfcc42d0d3204ef7415874004e3e75191323cfad72d913239fe741d8941014fc74d8540006ef70d8941024fc73d913002cfe75d8141005ef7258540286df32d8d20005ed72d913001cfd74d814201eee62d093001cfe72d8540004ff7159132004ff7258740014fc7158d20194ff7159131004ff7558b40045dc7358910
  | 13 => 0x8742004fd75d814100cfc70d8532137cf204c93001cfc72d8540006bf64d853201cde76d0d3213ef661d853235ebf41d912101dec7250d203cfaf32d9132014fc71d9132125f7715913128ebf40d9120024fe7359121376ed32d89311bede76d0d32235ef75d0920005dd72d0d303bebc30191323b6bf20191320067d73d9510006dc62d8d41004fd74d8930004fd71d8d20024fe76d8d410067c755911002cfe75d8520286ec42d8d20026df60d0d30006dd65d8d41005ef7250530004ff7058f42006df53d8d4100cfc70d854301cfe725874035ebd41d912104edf4358f4002cfc7558f4002cfe7559120076ee62d89300fdf571991213b6bc32191323bf9f3019132004fd7558b43006de72d8d41026cc634c92100cfc70d8910006f77159131176ed31d8941024fe7358b40006ec63d8941137e8704c920007ac7250740004fe76d0d10087b4615054004ebd7019132005df73505401bedf32d8d42014fc715913001cfc72d8d400d67e6548740014fd72d912102cfc75d891004ebe641912001dee74d0932006de6218d41004fd73d8910006bc43d912102cfc75583410079c7350740004fd74d8132136f86058132005bf744cb41005ed70d093200cfe7058b433b6af2019132006bf74591213aede54d8d4104cfc76d0910006f77158d21006be54591102cedf31d89303c6ec42d9132194fd769913100cfc70d91210057f755813101dec7250d4221e7c20d95101457c755813200cfc70d8d420feef205874201cfd73d8532006bf649913000cfc7058f41004fd755874304cfe74d81320067c72597402dcfe76191301ddfb705891004dbc744cb40004bf7458d21024fc7358910024fd7458f40005bf7458d213d6ef42d8142004fd72d8d1001cff765891000cde76d0d30004fd764c910006be54d91210a5fb70591100057f7558910176ed51d894100cfe70d85201b6df41d8d4121f7810d9510006be41d9132005bf744c940004fd75d8540004fc7650520004ff7458910006bf7458d20006ef62d09101aede76d0d30004fd70d8d413c6bc73d9132005ef7250d421b7d441d8d412adfb70585300047f755891004ebe6419132005df73505201b5de7618d41007db704c930176ee51d8941014fc7650d41004ff75591100f6f850d814108dec725854004cfe74d8530004ff7559131106de74d8d411bddf7359132326bf7650740176ec10d894104e7e7459740007cf63d89410cfcc634c921004fd73d85403b6be321913201dde72d0d32006bd75d9132004fd74d8931014ff72d8d2104efb4058341004fd70d854213cfd73d8d21007cf624c930186ec65d09200f7b8705054001dce72d0d3200cfe76d812100cfc7650940006ed43d8941006df635894104e7c7459740016bc61d0540006ec62d8141006ed63d8941077cf214c930176e
  | 14 => 0x100000e0af03a00704a13e0a500000500a0080270070080040200020924f300165701029001f00700000001400a03c00009600000100f00004200232c01c0000b000c03200102c04c01300006700d00405204d01d20000200300003102f00c00400300600100905f0a601d26400900702500505210c0030360070000b800700007f09500400303503602001600b00a00101c00d00c00700100000900b03e02001501b0a40140f90320030c60b80482704f400904b0330000a300301a00200003700000d00903300400301600500300101101a04d00409e01a0210044e500100022400100416c00006c0160070000780170146c400e02a0c500000701201906f0000150000474a000401300600d00c03800100b03900000400419f07300581001804401801802900000000005100633802e0ce07a00000002f00200e01900200007f00059103c0120011c902b04900103600527908d1ec00003a00f00c02100d13a0130010eb01e03200711d00000001a05e00000301100900000f3a802600c00506000000100304a00500717900403400600302303100a01100b0000193d900300700000000401e19c3ca02e00c05300100802409800202f05b00d00500d02207b44c13e00600a04b0010000810010381684d800600412809e02900602b10e02f08d00b18300109205700120d00f02500406c06201900503400500003100200000800101900502d00000f0011f300200b00112501800003002d00704500601701d00000401200400000101100000b00100000400000200300000c0090ca0000301010035c100202b04e00406403700002551400300000300000700803a0000000030000010cd00100300005e1460000060010560440000000000020005b903a01d52200200e04501500000005d00001f00100808100000c00200100001701400600008c00e0070590c20040d800f0010020360a801a00a00100800a0020030100a800201907200c05a22200805808e03402400a01200b01f00000000200008700203300305600800554153300600900102e0130bd00000400303305f00100300200b05300600b00a02100700f00100500200001600169a00000900201100400c03003002b00801703f00000202a01200600000211703e01b00500200401a00000000000300618b00b00000005000000001911e00200c00506200601a01606b13201300300000700000109000700700907200200200000600000f00101401600000f06800c00000800e00300601c0b600000b00407102603704f03f007013011032366bd42d912104ebc70191323c6bd20d9132016be6150540005ef7250d2021e7d71d95100067f7558d2014efa40d814200cfd71d91100367e76d95101867c65d0910004fd764cb40004fd72d9131006dd634c520006ed624c91000cfe705
  | 15 => 0x22a02400701e00e01500003d00f3a700218500100b00101f01703a00200203501800707c00e06803301b06508600000800302301302b0830010a100402401620601800300200d00100100200700d0ac27000809100c05701801c0000000670000160040030001044eb01401100100011b0160050060050020560076bf0030680190025ab00a00000000300000100000000500004200002700102d04d00000a0510550020500070640220040000000010690220012a700000002401500e01200300641202400200000600700000203b0330020c100400665600100a00203401a00e00014e00e00303500b05600d74c00602405b00903200101800800005a01400000000002105500d0380080f403201c0400010760000126ce03200000201b00507d00205f0430000d70b60081ca05200c00100001600200028d00000306d00e0000000000000de00600600000302e04a06e03400200b007001
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6e821cf65440011bb0f328c6a08023b61c50d8941007472a6c63128297caf72191614c80153906b20c8908031bdd7625814139d57426a7b128200a5d839c565d00f355b04386c8991fb2b9c954d913004d1f424e2b2e80038ec825d3604c41317d0e288c8990161f21576d0d1000556c1021b226477a9e83840644c80739d04b8e869922b8e14154d814117556c26e7b128200a9e8390b644405d1d90db92c0a080297a0c72d951001c77414eca0a6079a9e831d7644c8014dd05ba6ca880023be0975591300052f418c5b2a2000ad880597635040187eebba2c488002ada0450d91320055b40cca3226400aad82140644c8018b8e632ac8881e72718f744c94100657ba6e4b1a207ecac7255164440f117f08bb265a0013331cd32d85200061f3b4ea32264048dc835d3604840187ecbba2c488002b3a0c50d89410256741ec4992820587c855c3644c4018baea3aec6a08028fa1661d91324df46190ca3226400a3d848c565d00055a902b1a62900023be1d651894102c3f42eeca1220048ec87589324400159d05386c6a08021fe1570d9121006663b26498a40008ed82dd764440018deea312c0a08023ba1c50d894101c76412eab22620087f855d942440018beea39ac888003630c874581324e557c12ca3226478c9e76d93434c801878ca3a26488002b360a6018d410246e418eca0a6000a9c83590644400759d0db1264980030f1d764581320051ec2883b2260008ef825d932440f353d06286c8990262fa1f7458d1000726192ca99680018ec825d360484018baeba9ec6a08030fdd77458d203cd56c16e1b226400c9c74dcd634400199ee7b92c8880bb2b1db72505400054e41aa9b224000a6e8290f654400159906b2ec4a080333dcc725911045f47208c63128200a3c855c3644c80b0f90ab86c8908030f597744cb403ad4f420a1b1a8200c6c721956344001938e839ac488002b360a6518d410046fc1aeab22642eae681143625040117b093b2648801237a1f735911001c6ec1eec9968003ace86d89324c4091bd07baec8980270f1d1654cb400061fbaee8b1a2000a9d84d4f63500f3938e73b0c8991df2b1d8744c92000656310e8b122077a9e83944644c80147b0a21ec8900da37e0d74d813100c5f436e899280058df8754f63504f195cedb2684990123b60b764cb4101c6e43ac69922000ab984d43605040147b0818acba001237a1f735912140d4f420ca31a82008ef825d5644c40147d0b308c8990daa761075d8d4101c76410eca0a40098be87140644c90bb1e403a264980baab61075d89413fe4f39aa9b224000da471dd1324850bd1864322c0990031719773591101b54e432a9b1a82008be87d91614c8ed35d0fba264901ab2b1d8725054000657ba0e4b1a20038ee82dd7644c401878ea322c0991daa760e7619132
  | 1 => 0xf06b28c8990021fa1c6558d100247743ec49928000e2f6555062504014db0538acba00023be0974d8d103bd4f41820322642ece471d8942504091b906baac890802b3a0e60d89410054ec20a1b1a8200ccc62dcd6250401b1a603a2649000eb3209634c9100062eb98e7b2a2000a9d83840644c80147908b9eca880029b60a735974002c3f43eeab1a4000d8c321d1614c80117f08baac69001237a0f75d91101853642ac7a124000a9d83040644c8091bd07baec890803335cd72d91300043fc2aeca1a20368dc87553635050f93eec39a83a0003335ca73d912029e8f428e89926000c5c73195624400317908bb265a00063ba1b72505200046f43ec6b128200a5d83dd3654401317908baac4880030f1d47458d200061ebaea9b226404ccc76d0d324850393ce72a6c8900262fa1f7458d2000536c10e7b2a2000a9d83944644c80959d07b1264a00022fa1c645813200556c26a5b128200a9d84d4f63504010ff0ab86c899002b3e0d54d8941006e2196e2b026400e2d651c941d000159f04aa6c6a0802b3a0a60d8d410065bb26e2b0264008de8718d605050d95eec39283a0002b320954d8d4102c77c3aa5b1282008ef825d94344001878ca3a2c488002b3a0a6518d4102c5fc3aa9b226000ace83980625040b0f90ab86c899267a30c861191320054ec26a7b1a8400aad82143644c8091bd07baec8900022fe11764c91049c77c3aa9b128200c3d741d36544095a38e6ba8c8990023de05755911017477c12e9b024200aac82590644c401b30e1ba264981bf271d8735054004e1fb8acaa0e8075e1e54d536350401998c7b92c0a0803331cc725911000666390c6b028200c5c75dcd624400159d0da1a64901d7271d3634c9410246f41ceda0a4000c7475dc56444001878ebba2c6881e72b1db744c9203c6c7396c9a1a6400ce472dc5634406d5a902b1e86900161f2157650d200043ec3885b2a2000a5e8390b6544135d1865308c8990038d55351d854039d57c12c83224200acc8259463504031f100baac6908028f61442d913129e8ec28e89926000aae82903644c40147f08b96ca880daa761070d8d410056641aca3128275a9f83590644c4011bf06baac890003630cb74581320063bbaee2b1a400587e85dd943440011bf06ba6c0908023be09755913200656b9085b2260008bd87043644c8f153b07b86c89901237a1f735891000636baea5b128200a6e829cd65d000159f04b2ec6a08023761e42d8d4104c5f424ec9922000c6c65dc96344001968c9b8ac0990161fa1f7558d100055b40ccbb2264008ef825d9434845d55b08386c4a08262fa1f74589100051ec2883b224000ccc73dc964440018b8ebb1ac0a09e32b18b744c9400064e3a6e6b1a4200c3c651d16344001878cbba26488003275cc43d91203c656394ec3226400
  | 2 => 0xf62581410063c3aee0b2220008bd87144644c8018decbb92c688003b14cb21d85303c54ec1eebb226400d8c32dd1614c8c747b0938acba00023de05764c91000575c02cbb1282008ed8790f62504014db05ba6ca880022fe1d64191103ad4f420ebb1a82018dd839db414c0014dd0418acba000e3ba1f725911001d67416c69928200c5c73d956444001968e9b8ac69000ab920563485200043ec2eeca1a2000a5d8318b6544001998ec9924298002ab61352d89430052ec1ce4b2e8000ccc425cf644800159b05206c6a085e8f61372597400066a39ee2b1220008ef825d5644800156b0332ec899002b3a1b424c93000657416e8b1a4003ace82d8d32500051db05baec890802b6e016518d4117477c12e9b1a42008ed829db414c00193886ba6c49822727dd0635814100477c12eca1220028be86dd1325041317908bb264881e3639cf64d09322554e422c69922077d9b601d1324c00117b0e280c89900333d0973d91200052f41842b2e8000ccc329d932504031dd0db92869024b27dd063589410062e3aee6b222000c3f651d13244001878cbba2c6880030f1d77458d2000556c20a1b128200a9d83d53644c90195ce52a6c8980023b61e631894100c76c16ebb224000ace8390362504011bd0e106c6a08023760e7650d200043ec3887b2a20008ef8758f424800117b0e080c899002b3a0850d8d4100477c12eab2220008bf845d94348001c3ecaaa0c6a09dea7a0e501913204c5f438203226400e4f5394f6250541d1864b20c8991e2aba0875d91320064fba0e6b222000ccc435cb644c0eb53d09a96c6a08023b60b75d91303c54ec18e3b226400c9c74dcd62440051e902baac6900063b60a76d0d200054e41aa9b2242008be87147644c81317908baac690802ad606651913200636396cab1a2000cb471191604c8015d700b28c4a08161fa1b75589103bccf43ee89926000c3c75dd1624411195ee8312c0a08023b60b75d91314ff46194ec3226400c77751c5634800117f08bb2868800327a0f7458d2004e1e322eb3226009a3e84dc965d000187ccbba265a00036a1d3704c9200246fc3ae7b224000a3d8408565d00019aee638ac6900038b59772507403cd4f418e1b2264018ec865cd214811b59d0c318c4a080f331c932d813140656394a8b222000ccf73dc9644840193ee839ac8908021fa1c75591100055ac26a3b0a8090cce76d8c62504018becbb9ac8880063760e76d09300045fc3ac83224000a3d8510f644840156b02286c89900a3760f75d913100666b92e7b224000a3e85107644c81347d0810acba000317dd4635814100666b9ce5b2260368df835d3624c495a58e4ba8c8991daaba0a501913201c76412eab1a2000a6e829c565d0001c3aca39a83a00063ea1f7058910006c6398e4a0e8000c3e765d4644c93b53
  | 3 => 0x3128279a9e831c7644c80159f06b28c4a09e7a318f744c9210051e422e5b2a2077aad829d8644c8011df04baac68800237a1c50d8d4100574402ca3128200c6f751c9634406d53b09b96c6a0803330c8764c9410045ec38a1b226400acc8259763504010ff0ab86c898802ab60b54d913200746aa0c63128200c9c631d163440010ff0abb264880023761e40d8d4100556c102032264038ec825d5644c0051e902baac89000237e0d75591100062e32ee6b1220008df835d943484efd18c63a26490803171cf65589103be563b0e899242008dd839d9414800159b07386c4a08030fd94745891001c76412e9b1a2000a6d8218f654412355b09328c4a09e72718f744c94001c76412e9b1a4004acc8358932440d55590caa0c4a08022fa1c10d91320065bba6e2b1a4000a3f855c3644c80147b0b308c899002a760c10d913200556c26a7b128209a3e841c565d000155b09a96c4a00063e20175591310062e3a8c6b0282038ee829db414c00159b05386c6a080317dd7635814100637baee4b222000f0c325d4644c8018deea392c8881dfa318c744c9200064fba0e6b122000c6c75d8960504ed95ec03a2649012aab211624c9103ce563b6e89924279aad82dc7644c8091b906baac4880021fa1f6558d100061fb28e8b1a2078c9c76dd1324c4011bf06baac4880063720d74d81310062fba8e6b122078aae821c7644c8f353d06086c8990032d1c764581320056ac08a1b1a82008bf87590644c0011ef02baac89000ab9a1b61485200056741481b1a8200c5f739cd65d00019cee438ac69026327dcc6458532234d6422e690a4009c3c645d664480071bb07bb265a0802b360e60d89410045f43ec8b026496e8c32193604c80155904b20c8880dab5a0450d8d410062ebaea7b1a8400c3f751d1624401317d0fba2c690803330c8764c9100062e3a8e6b2220038de87d8d32500010fd0fb2ac8880022fa1c50d91320063a3aee2b1a4000c9d83dd163480010fd0e32ac8880022fe1d64191210045ec38a3b22646fa9c8655063504e755d08386c4a08da3721b7358141006363a8c4b028200c6c7219564440014bd07392cba00161f215764c9100046fc1aec9922000c6c65dc9644400195b05ba2c6900170f9d554587400043f438cab1220008ee870c3625052b1bf0eaa6c6a09e6ab60b75d913200657ba0e4b226200acd8298363504f355b043aec899003930cb654c9100147a40aeca1a400087e8710b654406d938edb9a82a00030fd97744c91017556432a9b1282008ed8790362504cb4f100b8acba000e3be1d72d913000c6e432e690a60008dd83dd764484ed938ec3a26498802b360a65d8d4100667b9ee4b226278a9d83dc7644c80b1bf0ea9ec6908162fe1d54d912000536c1487b2a209ee8c32994644c85d1d90eaa6c4a08023ba1
  | 4 => 0x44400117f08baac4880028fa1410d91321c52e42ac7a1a4000ccf729cb635040159d05300c6a0802b320d54d89413cd4f41eebb2264008ed829d9414c00199ee6392c8988270f19175191320246e41aeab222003ccc76d09324c40147b0b30ec89923eb3a0e631894100556412a9b226000caf741c964440011df0eb18c4a0802b360e65d89410054ec18a03226400ccc73d89605040196ee838ac69000637a1b73509300070eb2ee6a0e80048de839d941480014bb0610acba00161f21576d09100bd1ec26e6b2e80008ed870c3625045d5c902b1e8490002b3a0e65d89413cd56c10e3b2264058ef8754b624c401958e8392c68820f1ddc4655911000536c1062b2e8000c3f751d1634400147f08b9eca88003661d3704c9303c54ec18e1b226400c3f65dd163440091b906baac89000237e0d74d8910007472a0c7b128246d2d851d1324800187aea3aec89900237a1c635894101c6e41ae9b126000c6f75dc963440031bd0db9a8298003331cc62581410061e32ee8b12200587e85dd932440f155d05baec8990022fe1d65191320043fc2aeda122000a5d831cb65440014bd07ba6ca881dba3188744c9303b746310e89926200a9d84d4b635040159b07328c4a0802ba20165d89410147b43ee2b1a4076aae82944644c80155b05280c8991db6ad80744c9200052ec1c85b2a207ecae7655362504071dd05baec8880028f61410191320051f428203226402ad686d85314c00159d07328c4a08023761c50d8d4100567c12ca31a8200c3f75d91604c8870f90dbaac488003175d753d8d400046fc1aeab226000d4c32dd5604c8eb53d08386c6a080333dcc62581413fe4f3b2a9b1a82008fb805d56448509b1e603a264900021fa1c43d95100047dc02eab1a4205c3c75951644400199ee7b12c0a080e37a1f634c9413b557410203226409a3e840c565d000117b0f328c8990162f21d545911002c5fc3aa9b226217a3d841c565d0001e18653a8c8990021fa1c755891004d1f426e6b2e80008bf845d5634840159d0da1264988031d1d47158d200043fc2aeda1a20008bf845d943484011bf06baac8908162fe1d54d91210046fc3aca31a8209a3e8488565d00031bb07baec898212ab60a60191320046ec3841b1a820587c855d943440091b906ba6c488003a355063d8941006563a6e4b1a4200d9471dd1324c40b87ceaaa6c0a08030fdd464581323cf4631ee89924000c9c631d163484ff938e6aa2c8881ceaba1050d894102c5fc3aa9b226494a9d8499463504015b100b28c6a0803331cb635814100667b1ee4b028200ccf73dc9644c8011bd0fb1ac0a09cf8b95354d894100477438c4b028200cb4741c5634800199ee739ec4a08022fe1176509100147a40aeab226000ace8299763504011f700baac888002b360850d8d4100566c1cc
  | 5 => 0x8002a760e501913202c3f43eeab1220098bc841d93250001998c7b92c6a0a16a760e60191324163db80cab2220038ec825d5644400155d0521ec88823aabe1163189410043f438eab1a40008ef825d5644846d9a8e3b1a86a08022fa1c64585320043f43ecab122000c3d75d9264480051b90eb1a629000317d97735891002476c16ec9968000c5f75dcd64440011db0f328c4a08028fa1671d913204d1f42462b2e8000c6c751c964440015cb02286c4a08032b10974d8d2000667b98e4b1a2000c6c75dc96444001b18e639282a00030f1d47458d1004c5e422eab1a2080aae8419462504071dd0fb92c68800e3ba0b75d91203c64e3b6e899260008fb805d5644c4ef53d06280c899002ada0450191320045fc22eab2264098bc845d56348103938e72a2c8880161f215765091002c7bc3aa3b0a640087d85dd932440031f100baac8908030fdd47458d2001c76412eca1a2078a9d831d7644c80199e86b96c89800317dd77358910006363aee4b1a2000c6d75d4b6250c0147b0910acba00023760f75d9120007472a0c63128200a9d83143644c8a733908b9a42980023be0974d81313c557410a1b226400a3d85043644c80153d07206c8908031d5c47159740024e741ae3a126400adb805976350401b50e1ba26490002ab60a51191320046fc1aeab226200ccc73dc9624400959d0db1a64908028f61442d91300064fba6e6b122004ace86d8d32480011bf06bb28688003a355363189410051ec2883b226400a6e8218f654400159f06b2ec4a0803530c9751913200566c1c81b1282008bf87590644c80117f08baac68800297a0e715974000656310e8b126273aae841d762504051d90eb1a4290013331cd32d81210246e41aeca122000acd83143625040147b0b38ec899003171d47358910024e741ae1a126400c6c72d9564440031db053b682900031bd977259110006563a6e4b122000c6d751d7625048da5d0a3a2649022fa310463189410043fc2aeca1a4076aae82840644c8f1958c5ba264a0802ad60450191320145e422ec9968200ace86d0d3248401998653b264881e3a318b744c9310056741ce1b1282008f7815d5634800155b05080c8990023760e76d05200061e3a8e8b12208ccce7618c625040187aebb24c8981e2aba0810d91320043ec2eeca122073cac74d8932504ed938ec3a26498003331cf72591210047bc0aeab2260048ed82dd7644c8f155d04386c89900e3760f75d913201e6639265b0a60039ce825c3434c8011bb07baec88800e3ba1f7259131006563a6e4b1a2000aac82553644c4071dd05baec8980023de057650d200053dc02e2b2e8076aae82140644c8011bf06bb284880031b1d47258d103be4fb00e89926078e8c62dd1324c0091dd0fb1264a08022fe1d64191310076299663b0a400587e87dd56
  | 6 => 0x82916802800508380000000000538280001027000b395005034008560181a0f0260b000008502a01a1e01601000130400000204002108081180e0014c0500c9082ea200f718000001403008258980300a038140100609186000b40083e1484c02036000042f854120000481424848008064b8000000070814150ea6e8001c0500b00a000157200e028240089e000000381c01072b80b45381e008260011a26038048860107202000068000003a1c8260d012088c8000000001200d3a0008a0605c77010000300d806070281a80006078020062b084110060288e6d8060d010030082f850010000002e0080a0010a07810028001b0020006c0c0000180a0686c278023e000170ce06042074680482e010140080e00094088c400002020480e8080186c110002c81e0000e0103c000702200c1909e7503c380100506604002000005c8000280c0000c0500a0107c168080f016000500601a0c8020900c470000300c5e804040340086e0a0001303a94000110004800009e377159541d00010fd0e3aac68
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x400b0015400010070400531644321d9325040160e960c975191320052364c621d16244001c0d651cc7250740006830ca85984644c89550c970c97519132006a10ca81994644c801c0c321d4645813200513a58325d4644c801c84321c4645813200523648631d1634400103d98194744c91000433660321d9324400160e960ca7519132
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x6
  | 6 => 0x94e
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x5
  | 10 => 0x98a
  | 11 => 0x98c
  | 12 => 0x98e
  | 13 => 0x9ca
  | 14 => 0x9cb
  | 15 => 0x9ce
  | 16 => 0xa0a
  | 17 => 0xa0b
  | 18 => 0xa0c
  | 19 => 0xa0e
  | 20 => 0x180a
  | 21 => 0x180b
  | 22 => 0x180c
  | 23 => 0x180e
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0e
  | 27 => 0xb49
  | 28 => 0xb4b
  | 29 => 0xb4e
  | 30 => 0xb89
  | 31 => 0xb8b
  | 32 => 0xb8c
  | 33 => 0xb8e
  | 34 => 0x1849
  | 35 => 0x184b
  | 36 => 0x184c
  | 37 => 0x184e
  | 38 => 0xcc9
  | 39 => 0xcca
  | 40 => 0xcce
  | 41 => 0xd09
  | 42 => 0xd0a
  | 43 => 0xd0c
  | 44 => 0xd0e
  | 45 => 0x1889
  | 46 => 0x188a
  | 47 => 0x188c
  | 48 => 0x188e
  | 49 => 0xe89
  | 50 => 0xe8a
  | 51 => 0xe8b
  | 52 => 0xe8e
  | 53 => 0x18c9
  | 54 => 0x18ca
  | 55 => 0x18cb
  | 56 => 0x18ce
  | 57 => 0x1549
  | 58 => 0x1409
  | 59 => 0x150a
  | 60 => 0x128a
  | 61 => 0x16c9
  | 62 => 0x1449
  | 63 => 0x168a
  | 64 => 0x12ca
  | 65 => 0x1489
  | 66 => 0x130a
  | 67 => 0x14c9
  | 68 => 0x134a
  | 69 => 0x2c9
  | 70 => 0x98d
  | 71 => 0x98b16
  | 72 => 0x138b
  | 73 => 0x124b
  | 74 => 0xccd
  | 75 => 0x98cd6
  | 76 => 0x99896
  | 77 => 0x1709
  | 78 => 0x15c9
  | 79 => 0x168b
  | 80 => 0x12cb
  | 81 => 0x1609
  | 82 => 0x130b
  | 83 => 0x9cd
  | 84 => 0x9cb56
  | 85 => 0x138c
  | 86 => 0x124c
  | 87 => 0x9ccd6
  | 88 => 0x150c
  | 89 => 0x128c
  | 90 => 0x9d8d6
  | 91 => 0x1789
  | 92 => 0x130c
  | 93 => 0xb8a16
  | 94 => 0xa0b96
  | 95 => 0x184a16
  | 96 => 0xa1856
  | 97 => 0x289
  | 98 => 0xb9816
  | 99 => 0x180b96
  | 100 => 0x10a
  | 101 => 0x1049
  | 102 => 0x170a
  | 103 => 0x15ca
  | 104 => 0x16cb
  | 105 => 0x144b
  | 106 => 0x40a
  | 107 => 0x160a
  | 108 => 0x148b
  | 109 => 0x154c
  | 110 => 0x140c
  | 111 => 0x58a
  | 112 => 0x178a
  | 113 => 0x148c
  | 114 => 0x20d
  | 115 => 0x140d
  | 116 => 0x24d
  | 117 => 0x144d
  | 118 => 0x58b
  | 119 => 0x40c
  | 120 => 0x178b
  | 121 => 0x160c
  | 122 => 0x150d
  | 123 => 0x15cd
  | 124 => 0x168d
  | 125 => 0x170d
  | 126 => 0x104b
  | 127 => 0x104c
  | 128 => 0x194b
  | 129 => 0x194c
  | 130 => 0x15812
  | 131 => 0x2d851
  | 132 => 0x40994
  | 133 => 0x589d3
  | 134 => 0x40112
  | 135 => 0x58112
  | 136 => 0x41312
  | 137 => 0x59312
  | 138 => 0x104b91
  | 139 => 0x58412
  | 140 => 0x59892
  | 141 => 0x418d2
  | 142 => 0x41792
  | 143 => 0x40592
  | 144 => 0x18d892
  | 145 => 0x41052
  | 146 => 0x59612
  | 147 => 0x40e
  | 148 => 0x59052
  | 149 => 0x58e
  | 150 => 0x59693
  | 151 => 0x41414
  | 152 => 0x59453
  | 153 => 0x24593
  | 154 => 0x144593
  | 155 => 0x5c593
  | 156 => 0x41a14
  | 157 => 0x59a53
  | 158 => 0x1a4593
  | 159 => 0x178593
  | 160 => 0xe8593
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1308
  | 6 => 2405
  | 5 => 835
  | 4 => 14
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
  | 7 => 2*((h/436+packedAt gbK7 (48396+(h % 436)*11) 11) % 1308)
  | 6 => 2*((h/850+packedAt gbK6 (115440+(h % 850)*12) 12) % 2405)
  | 5 => 2*((h/299+packedAt gbK5 (49265+(h % 299)*10) 10) % 835)
  | 4 => 2*((h/18+packedAt gbK4 (980+(h % 18)*4) 4) % 14)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff81f807c0ffc0ffffffff04f318fa071fff
  | 1 => 0x1e01fe0007ff07ff07ffffff1b4ce72438e3ff
  | 2 => 0xe001fffff80007fff87c1f00e38f07c7c0fccc
  | 3 => 0x1fffffffff800007fe000fc0ff807ff00f0
  | 4 => 0x1ffffffffffffff800000fff00007ffff00
  | 5 => 0xfffe00000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa21c8058214029402895292a0011084a030d55
  | 1 => 0x1421160042950295052a52d4094463241862aa
  | 2 => 0xc045aaab680424e6b04f1c06628f05c6c0b4cc
  | 3 => 0x8089cd3574e6b00420739818b40fb8076d00f0
  | 4 => 0x111071c68738c738c6000060dff00001b6db00
  | 5 => 0x19e000070030803084000080ffead6b0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40527
namespace PEqualNP.Outside.L_meta_40527
open PEqualNP.Outside.L_meta_40527.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := bs0_5_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 24 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 117 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := bs1_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 13 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 17 := bs4_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 14 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 85 := block_range (n:=85) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 85 := bs5_3_0
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
theorem bs5_4_672 : Interval s5Atlas 4 672 82 := block_range (n:=82) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 754 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 bs5_4_672)))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 779 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 14 := bgb_4_0
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
theorem bgb_5_768 : Interval gbAtlas 5 768 67 := block_range (n:=67) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 835 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 (concat bgb_5_672 bgb_5_768))))
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
theorem bgb_6_2400 : Interval gbAtlas 6 2400 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2405 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440)) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728))) (concat (concat bgb_6_1824 (concat bgb_6_1920 bgb_6_2016)) (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 bgb_6_2400)))))
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
theorem bgb_7_1248 : Interval gbAtlas 7 1248 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1308 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)) (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 bgb_7_1248))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 34, 38),(inputs.getD 3 zero, 34, 42),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888feeaeeeafee88888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40527.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[1,5]⟩,⟨.or,[4,7]⟩,⟨.or,[1,5]⟩,⟨.or,[2,3]⟩,⟨.and,[8,10]⟩,⟨.and,[2,3]⟩,⟨.or,[6,12]⟩,⟨.and,[0,9]⟩,⟨.or,[11,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40527

open PEqualNP.Outside.L_meta_40527 in
theorem PEqualNP.Outside.L_meta_40527 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276652168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
