import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36703.Model
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

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
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
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


end PEqualNP.Outside.L_meta_36703.Model

namespace PEqualNP.Outside.L_meta_36703
open PEqualNP.Outside.L_meta_36703.Model
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

def SBf (j : Nat) : Nat := [7, 3, 7, 7, 7, 7].getD j 0

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

def checkRow (g : Atlas) (k i : Nat) : Bool :=
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

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_36703

namespace PEqualNP.Outside.L_meta_36703
open PEqualNP.Outside.L_meta_36703.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x90a0099c247439e2a0109f56116204a4412d4ca4a171c040165e8d38b14b83001ea0d804400c00480002a106480c0600d0d000e48002ee00000030e800080ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20ee20fd20fc20ec20ff10fe10f610fd10fc10f410
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xf05d36184ee3f228b40012478d4f200448002a5b46074040924a3400001206490750a0ac00130e0a41c6336968002a2707c003e0293c006f139883633101cc3c533815d0476161d1144400088004d12a10bc552a19cf8003ea38141700000d4811183c304703820b00b2e0bcd2861e9e800510320c22000010c4c7106801004c3d964646e42900787221128fe0c018680034258006e0417004cc4100220ca87000d800000000000001c918c81000148628b0b1a0ac21359405060180e0767e2f800740c0701000007010004030501031e060005110a00113201030100310e000600042b0c0c0002070b020204000700040203b7296876d52d0edca521db54a43cea18875e53d0abaa7a15794e42aea9c85ad4210a7ca9994f553329f2a4653d548cb9a641957d4d41ae29a836f52506d8a4a0ded4141bc282835e53106baa620db94841b6a90833f544c678a898dbd4931b6292637b504c6f0a098cf950319eaa0636e520c6daa418cfd51219e2a2435f53486b8a690ded4121bc282433e540867aa810d794c21aea98435e53d02baa7a05b94b40b6a96817651d02eaa3a04f94240afa9a815c53502dea4a05b14940bba8a8174515027ca0206e940409f2a6613d54cc2dca5985b54b30bb28e617551cc2bca1186790230ce204613f544c278a8985bd4930b62926177514c2e8a2985794030ed280619e400c33880184f953209eaa6415e53c82baa7905d94720baa8e416e508835c81106b10220e718441cc308827ea8904f15120afa9a415c53482eea2905d14520b728041ea500835c80106b10020e718041cc300827ca9884f55310af29e215d53c42dca5885b54b10dc20621d830c43d041885d94210db20421b440843ac6108750c210f310421e4208427ea8884f15110afa9a215c53442dea4885b14910dc20021d830043d040085d94010f928021f3400436c80086d10010f820021b040043e66008758c010ea18021f030043a060087cc8010f310021e420043e040087808010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x72480218041638c01401e10a600222692000407c388400c020b498f40042e262d0010ac98240042b264cc010b898b30042d2608c010e41023004392400c010e410030042b264c8010b498f20042e26088010e810220043c03088010e890020043a04008010f08c020043c03008010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 144
  | 3 => 19
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (4272+((h/48+packedAt s0K4 (3888+(h % 48)*8) 8) % 173)*9) 9
  | 3 => packedAt s0K3 (752+((h/6+packedAt s0K3 (722+(h % 6)*5) 5) % 23)*6) 6
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffc07fffffffffffffe03ffffffffff87fff
  | 3 => 0x1fffff803fe01ff00fffffc07f01fc07ff98c7
  | 4 => 0xe0ffffffc0001ffff00fffff8001fff80fe0f8
  | 5 => 0xffffffffffe000000ffffffffe00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8412c092492145112122a2c58b522d4a93ab5b
  | 2 => 0x825742492528a2a4a45502ad5a556952855ad
  | 3 => 0xb04995762394d348ec89f560663198c7cd98c6
  | 4 => 0x1d8e26473b1b1c8c88ee79b340c1e3e18ee0f0
  | 5 => 0xdef038783c1c1f0f0f0f9e3c78f903060f7e00
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36703
namespace PEqualNP.Outside.L_meta_36703
open PEqualNP.Outside.L_meta_36703.Model
def s1K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (5+((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffd5f1c71f878f1e93
  | 3 => 0x66fe07e3f80fe31c
  | 4 => 0x78fff803fff003e0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff8010000008810025
  | 2 => 0x2a2caab1c52a5a92
  | 3 => 0x1945b496d44ccb18
  | 4 => 0x78926db666893c0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 29 s1Pos s1Neg, 0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36703
namespace PEqualNP.Outside.L_meta_36703
open PEqualNP.Outside.L_meta_36703.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x700b432a0890ca756856224c0cf8000740101814d145c000174a5878d50014a002009022a6098b2278400462579b1438e0000c0000008010100044220d147ff43fe43be43fd43fc43bc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xd01237398014a0001a34d6001399418954c1e000071e939041a09aa454010f2b0009b002a8ae91028710819250000000002b8000000000009653800809c2c968e4005c1c1126c41a8000603e85950501c02800753b0ac2aab36801721d31a50c8183791d686a0b82000a10000000000da6892b11e2640029279a45a862f2b4c2041f881487a3f8c11c92211c4a2434e9a0b080512c11e1f458984245599f0466e0827828850721d6e125a8d8004c4b954e8482b044889f4814cba771d894f6001d29800322692c1e5f000d4f2b2290888281518b0000200228002f058c40c002a1891093000cccc8c140e4b667000900000231f85cb6001707c0d5781c080850044890040000285404000404003c000c040c1c241c2800000c0471002400344c087c00040c0020100800104c1828040000004808500c040c0c4adca521db54a43bb28c87755190e7ca721cf94a43d7294872e5290f5aa521cf94643db28c87365190f6aa321cf542439f298879e5310e7ca421cf944439ea80875e5390abaa7215d94642baa8c853e5390b3ca7214794e42cea9c853e5290a7ca3216d946429b28c85b55190a7aa1214f94c429f29085ae5210a7ca2214f540429f2a6653d54ccb3887995d94732baa8e653e548ca7aa9196b10a32bb28c6575518ca7ea8994f15132ce21a65ac424ca7ea8194f15032e6990655e53906baa720db94a41b6a94833e539073ca720c794e41cea9c833e529075ca520cb94a41d6a94833e519067aa120cf94c419f290833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918db94a31b6a9463b4418c67ea898cf15131ce21a63b4414c67ea818cf15031ea988633e54c867aa990d794f21aea9e43ac42c867ca910cf55221af29c435d53887688310cfd51219e2a243ac42487688290cfd50219e2a043e5210867ca7a04f94b409f28e813d54902bea6a05714d40b7a92816c52502eea2a05d14540cfa9a813c5350338a6a04714d40d7a92813c5250358a4a04b14940dba8a813c5150368a2a04d14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2616f524c2d8a4985dd4530ba28a613e540c27aa8186710c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f55220d6214413f5448278a89057d4d20ae29a417751482e8a2904f950209eaa0415e53082baa6106b10820bb2884175510827ea9884f153109f2a4213d548436883084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1400000070000000787668729a108c9c242c908274008e7c64000000005806a6284a5c98000048540000005a1808a20000663a0c001600002a00005e000000880e0052426c22380000006e0046843000920000a012560432869e26946a00360a002ea4007e000000004400024c8a000000008000003e1e50967a4e0000600020340000623c000000000000001c40001a000000010802060105000100020800080200000206020000000b0003000205c994a5190f255294643c99495190e8d6294c43a55865310e3661948438b98a5110e2c62540438d1855010f165394642c554e5190b1653546428d9865310a8d6394842a95865210a1e63944428718d5010a346154042c510d51ccb2442546328d987544ca1e63d50328b98b540ca3661d5032c3151320cb0e5394a41c354e529070e5354a418b98a531061e6394841a558e51106a562944418718d501062c6254041c310d52cc72552106318b98b544c61e63d50318b98b540c63661d5031c5151310c70d5310b21c554c418861e63d51218798f540862e62d50218d987540872454484218b98a53d02366194f408798e52d02366194b408798e51d022e6294740c314f525030f5314940c314c525031453d4540c914b51503175314540c514c51503275214540c9148515022e62d53308d98754cc22c62552308d185548c21d6510c30c310d520c31443544308798f54c823661d53208718d548823461552208b594420830d5310820c9109510821e63d53108b98b54c421c63552108b18954842356510410c554c41043255210410
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 186
  | 3 => 84
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (864+((h/16+packedAt s2K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s2K4 (5518+((h/62+packedAt s2K4 (5022+(h % 62)*8) 8) % 224)*9) 9
  | 3 => packedAt s2K3 (3416+((h/28+packedAt s2K3 (3192+(h % 28)*8) 8) % 147)*8) 8
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffffffffffe07ffffffffffffff87ffff
  | 1 => 0xfc1ffe07e07e07fff8783c1fe0f83e0ffa4e93
  | 3 => 0xffe0fff8007ff81fff803fe0ff003ff07c731c
  | 4 => 0xffffff80001fffffc000ffffc0007f83e0
  | 5 => 0xffff00000000001fffffffff000000007ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40002410010000001104821010a0284009425
  | 1 => 0xa94664324aa4ae8e582a151a68d0b42b3a4a92
  | 3 => 0x30caa890d349a2b6aa842748ba4139615c6318
  | 4 => 0xa294d1249a0d34db34ce8210dce590426f03c0
  | 5 => 0xc318e1c71c71c71dc7773b9c1086218c77fc00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88eeaaaa88aaaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36703
namespace PEqualNP.Outside.L_meta_36703
open PEqualNP.Outside.L_meta_36703.Model
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
end PEqualNP.Outside.L_meta_36703
namespace PEqualNP.Outside.L_meta_36703
open PEqualNP.Outside.L_meta_36703.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2c067922632a46152e8c02800240001a187af400000002b400036615824451516344471d009d090142d2880e7c21c260092e0a0001030883689407449c0105ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4c26800380000174881b1c000f05735000008336000b43537138c4000000046580000000003e09c026500060fc001804c00002a09800000000092001b0000000001ac1800000e8763424128000000000006d3a18000221593ce000000f408000005c2c4b1b8b872520000000084083800850f0000076000500000000001400000000010000f8ce0022868002c0018c00822b1e40000001e8000000000fe28001400000388000000001a4544200000000000000ea40191ec781523874d01114880820d059540a3f169bcb65328a003e84001cc866639000420212000001212990bc000000000003b80000000380000002f800b803179f462460000000000798432092c8006606000100000400400140000040400001c442c00100014042c000404100c340404040054000c0808040818040004027ca5a1cf947439ea86873d5490f3ea6a1cf149439e28a873f5050e7ca821cf54e429f294853e5190a7aa1215794c42aea98859e5310a7aa6216754c428ea98853e5210b5ca4214f944429ea80853e54cca7aa9996750f32bb28e657551cca7ea9194f152329faa2653c544cb3a86994f950329eaa0653d539067ca520cf946419ea84835e53106baa620e794c419ea98839d531063aa620cf948419f28883b6511067aa020cf953319eaa6639d43cc6dca598db54b319faa4633c548c67ea898cf15131cea1a633e540c67aa818cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cfd51219e2a2433f5408678a810f948421af29e815d53d033ca7a04f54f40cea9e811d53d027ca5a04f947409eaa4813f5350278a4a04f14540dda82813e541027ca9984f553309f2a4613d548c33a87184f951309eaa2613e540c27aa8186750c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f552209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x30080194010008800018c80000b00680a0001e00e9a200a48ca96b800240047000040010130008758e5190a1f6354242c550d51cca3661d523287195434ca8c6250d328758e529061f6354241c350d52cc62e62d523187195434c6946150d318758c544861d63150218e580540861d63149408758c515021d63951308b189544c2346155130c350d520c31543544308758c54c821d63952208758c54c421d6395210
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (864+((h/16+packedAt s4K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s4K4 (3970+((h/44+packedAt s4K4 (3618+(h % 44)*8) 8) % 234)*9) 9
  | 3 => packedAt s4K3 (1036+((h/8+packedAt s4K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 1 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 2 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 3 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x800010208010000044120088008a0a10085025
  | 1 => 0x2519221924a430960a854853485090aca32692
  | 2 => 0x432a44486949032aa109950595012585458b18
  | 3 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36703
namespace PEqualNP.Outside.L_meta_36703
open PEqualNP.Outside.L_meta_36703.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1810c80008d59e2ca07004c0908000011002420000009100a16a8e033625487225cf93305469034147810c94a27007560f2123cd1022002d508c242ff43bf43fe43de43fd43bd43dd439d43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc008101b49a001a9680a0700150900000104f80a3980076752983492000e99822770d84c4c470d12cf03601000027d1a1c8d4001e09464390017832180000070652b0dc5e0f31984f245358b4000309000aa0027000424c001d0e0003f1d87e001499c00000480000001100000000012800001885cd00b290cc3e000005808001400000620007000151f16454571580000503d110fe000016000420017c4e1017038181440170e23d36100603a32118486e0f1ec864f288b0d25b031bcba2305078380000002800485810200000080838782000580828604130d001080010200160580838281000f03814f55243aeaa4871d5490f3ea6a1e7d5143cfa92879e5250f3aa4a1e714943cfa8a879e5150f3aa2a1e714543cfa82879e5050f3aa0a1e7141439f2a0875e5310f3a8621d794f42aea9e859d43d0aeca3a15d54742cea1c859d4350abca6215754c42cea18853e54cca7aa9996750f32bb28e657551ccb3a87196750d329f2a0653d540cb3a86195794f41aea9e839d43d06dca5a0db54b41cea1c839d43506bca620d754c41cea18833e54cc67aa998e750f31b7296636d52cc73a8718e750d319f2a0633d540c73a8618cf953219eaa6435e53c86baa790e750f219f2a4433d54886bca710d754e21cea1c439d434873a8610f948421af29e815d53d033a87a06750e40cea1a815e53102baa6206750c40b7290816d52102eca2205d544409f2a6613d54cc33a87986750e30cea1a613e540c27aa8186750c30b7290616d520c2eca2185d54430cea1e419d438827ea8904f15120afa9a415c534833a86905dd4520ba28a413e540827aa8105794c20aea98419d43082eca2105d54420cea1e219d438427ea8884f15110afa9a215c534433a86885bd4910b6292213e540427aa8085794c10aea98219d43042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x138000208b000d80000408000000031400000000000002a18c8480000998001300000e801f8d18861a9285950196999017000000001d001780210000160b80000000009f1c02071e068a159e850a80001480000000038c00200007801b80001b0e09121c8000088000001a0f91811d8000110010990f0200080000010100020a0018506202800438104a59875250e9561d4943a59865250e956194943c35485250e8e62d4543a358b5150e8e6294543a358a5150f155114543a3d895050e8c6254143a5d855050e946154143a39885050e8d6214143a59845050e956114143c550e51d0b154354742c550e51ccb154354732c350e52d070d4354b41c350e52cc70d4354b318758e54c861d6494f2187d9543c861d6550f218758e548861d6494e2187d95438861d6550e21e150d210870d4394840c350d52103154394440c550d511021d6355030c350e520c30d4354830c550e510c31543544308758c544821d6414d2087995434821c6550d20c550f514831543145208758e540821d6494c2087d95430821d6550c20c550e510831543544208758c544421d6414d1087995434421c6550d10c350f524430d43149108758e540421d6494c1087d95430421d6550c10c350e520430d4354810
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
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
  | 5 => packedAt s5K5 (810+((h/15+packedAt s5K5 (720+(h % 15)*6) 6) % 55)*7) 7
  | 4 => packedAt s5K4 (3827+((h/43+packedAt s5K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s5K3 (2738+((h/22+packedAt s5K3 (2584+(h % 22)*7) 7) % 118)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x87ffffc3fffffff03fff07fff07fffff38f1ff
  | 1 => 0xf83e0ffc1f07c3ffc707f8787f87870fd74e93
  | 2 => 0xffc00fffe007fc3ff807ff807ff807f0e78f1c
  | 3 => 0xffffff8003ffff800007ffff800f80fe0
  | 4 => 0xfffff0000000003fffffffff80000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x80000040000000000008008800088100001025
  | 1 => 0x128c9488ca4a8612c34348513485122e534692
  | 2 => 0x219529114695206558859502595024e2a58b18
  | 3 => 0x7529ce2294c1aab9add0c4446e667044f80dc0
  | 4 => 0x46318c3b18e6333e36e6e6670c444088fee000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8eaeaeaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36703
namespace PEqualNP.Outside.L_meta_36703
open PEqualNP.Outside.L_meta_36703.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1200155c00d118049b46011d8a4000000a18c941e8ad1e410010c5b4162a945ecc817555c050116ae82609898e87100423802c8074f8054980294e5b7004a00000562ce0000001910058100020004020022cd800000007000c10a240009ff5301ff94c01fd5301ff14c07fe43007f50c07fc43027fd4805fe52007f54805fc5201ffcc805fe32007f4c805fc32027fd4401fe51005f94401fd51027f144017c5101ffcc401fe31007f4c407fc31017fc8401fe21007f48405fc21027fd40017f5000ff94001fd50005f54003fc5001ffcc003fe30007f4c003fc30017fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x924002ff8c920017dc649000bfd3248001f69924002ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148019ffa8a4000ff94520006fca290003fd5148019fe28a4000df1452005ffe6290003fe3148001fe98a400bff0c520017fe429000bef2148005ff10a4002ff48520007da429000bfc21480037fb024001ffd412000efea090007fe5048003fea824001df5412000ff8a090007ff3048003ff1824001ff4c12000ff86090007ff2048005fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffc2090007fc1048001ffb2e2000bfd9710006fecb880027f65c4015ff32e2004bf99710007facb88002fd65c4015fe32e2004bf19710006f8cb880127c65c4001ffb1e2000bfd8f1004ffcc78800efe63c4001feb1e2000bf58f1004ff8c78800efc63c4015ffa9e2009ff94f10007faa788027fc53c4013ff21e2000ff50f1004ff88788003ff62c40017fb162008ff98b10015fcc588003fd62c40017eb162008ff18b10015f8c58802bff52c4011ff2962000ff54b10047f8a588027ff32c4011ff1962000ff4cb10047f86588006fe61c4015ffa8e2000ff94710006fca388003fd51c4015fe28e2000df1471004ffe6388003fe31c4001fb18e2000ff4c710007ea6388027fc31c4011ff90e2000ff88710007ec4388003fd21c4001fa90e2008ff0871000dfac188007ff50c4003bfa862001ff9431000ffaa1880077d50c4003fe2862001ffcc31000ffc6188007fd30c4003fe1862001ffc831000ffc4188007fd20c4003fe1062001ff8431000fec2188007fa10c4003fe0862001fd04310007feca88002ff6544001bfb2a20009fd951003ffcca88012fe6544001feb2a2000bf5951003ff8ca88012fc6544001be32a20049f19510007fec688002ff6344001efb1a2000b7d8d10037fcc68800efe6344001feb1a2000bf58d10037f8c68800efc6344001ee31a2003b718d1003ffea68801bfe5344001fea9a2006ff14d10037fc8688003fd434400dfe21a2000ffd8910005fec488003ef624400177b122005ff98910015fcc488003fd62440017eb122005ff18910015f8c488003ec6244005763122007ffd491002ffca488003fd524400bfe2922006ffcc91002ffc6488003fd324400bfe1922001bfd851003ffea288003fe5144001bf28a2000ff5451003ff8a2880037c514400dff98a2000ff8c510007ec6288003fd3144001fa98a2006ff0c51002ffe4288003fe2144001fb10a2000ff48510007ea4288017fc21440037fb022001ffd411000efea088007fe5044003fea822001df5411000ff8a088007ff3044003ff1822001ff4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff1044001fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd6254023fe312a002bf18950027fea4a80137f5254009ff292a011df94950027faa4a80037d5254009fe292a004df14950097fe64a8047fe3254001fe992a011ff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8002fc6154009ffa8aa004dfd4550027fca2a80037e5154009fea8aa000df54550027f8a2a80137c5154025ff98aa000ff8c550007fa62a804bfc3154023ff90aa000ff88550007fa42a8047fc21540037fb02a001ffd4150027f6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ff982a001ff8c15000ff860a8007ff2054003ff102a001ff0815000ffc20a8007fc1054001bfb1aa012df98d50006fac6a804b7c6354025bf21aa000df50d50096f886a80037f6254023bf312a000df5895008ef8c4a804b7f3254023bf192a000df4c95008ef864a80037f6154001bf30aa000df58550006f8c2a80027c6154025bf98aa000df8c550006fa62a804b7c3154023bf90aa000df88550006fa42a80477c2154003bfb02a0019fd8150026f6c0a80077f3054003bf182a001df0c15000efe40a80077e2054003be102a001df8415000ef820a8003ff654c0017fb2a600fff99530025fcca98003fd654c0017eb2a600fff19530025f8ca98003ff644c0017fb22600eff99130085fcc898003fd644c0017eb22600eff19130085f8c89803fff544c01dff2a26000ff55130077f8a898006ff634c007ffa9a6003ff94d3001ffaa69800ffc534c007ffa1a6003ff90d3001fbc869800ffd434c001eea1a6003ff10d30007fec498002ff624c01bff3126002bf98930007fac498037fc624c0057e312600fffd493006ffca498003fd524c01bfe292600effd093006ffc8498003fd424c01bfe2126003ffcc93001fbe649800ffe324c007fe9926000f74c93001ff86498003ff614c0017fb0a6000ff98530007fac298003fc614c0017e30a600fffd4530007fca2980037e514c001fea8a600fff14530006f8a29803bff414c001ff20a6000ff50530077f8829800fff314c007ef98a6003ff8c53001ffa6298003dd314c007fe18a600dffc8530007fc4298003fd214c01bfe10a6001bfd813000ffea0980077f504c003ff2826001ff5413000efaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826003fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007ff204c003ff1026001ff0813000ffc2098007fc104c001ffb2a4000bfd9520067fcca90012fe6548001feb2a4000bf59520067f8ca90012fc6548001ffb1a4000bfd8d2005ffcc69000efe6348001feb1a4000bf58d2005ff8c69000efc6348019ffa9a400bff94d20007faa69002ffc5348017ff21a4000ff50d2005ff88690006ff6248005ffa924002ff94920017faa49000bfc5248005ff9
  | 2 => 0x310dff8c098806fc604c43dffa82621bff941310dff8a098877ff404c437ff202621bff1013101ffe609880fdf304c407ff1826203ff0c1310e7fe409886ffe204c437fe102621bff841310dff82098803ff65884017fb2c421aff99621025fccb10803fd65884017eb2c421aff19621025f8cb10803ff63884017fb1c4219ff98e2101dfcc710803fd63884017eb1c4219ff18e2101df8c71086bff5388433ff29c4200ff54e210cff8a710867fe4388401fea1c4219ff10e21015fac51080bff5288405ff2944202ff54a21017f8a51080bff3288405ff1944202fb8ca21017fa6510803ed3288405fe1944202bf986210d7fea310803fe5188401bf28c4200ff546210d7f8a3108037c5188433ff98c4200ff8c621007fa6310867fc3188405ff90c4202fbc8621017ee431080bfc2188405fa10c4200ffd82210c7fcc110806fe6088401feb044200bf582210c7f8c110806fc6088435ffa844218ff942210c7f8a110867ff3088431ff1844218ff0c221017fe411080bfe2088431f71044202ff08221017d84110863fe1088431fe0844200ffd9521005feca908037f65484013fb2a4217ff99521025fcca90803fd65484017eb2a4217ff19521025f8ca908037c65484093e32a4200ffd8d21005fec69085bfe63484077f31a4200ff58d21005fac69085bfc63484077e31a4217ffd4d210b7fca690803fd534842dfe29a4216ff90d21007fa869085bfc43484057fb124202ffd4921017fca49080bfd5248405fe2924202ffcc921017fc649080bfd3248405fe1924202bfd85210bffea290803fe5148401bf28a4200ff545210bff8a2908037c514842dff98a4200ff8c521007fa629085bfc3148405ff90a4202fdc8521017fc4290803ee2148405fe10a4202fb08521017e8429080be42148401ffb024200bfd81210affcc090806fe6048401feb024215ff1812100df8c09085fff504842bff2824215ff141210b7fe6090857fe304842bfe1824202ffc8121017de409080bfe2048405fe1024215ff841210aff820908137f63d4009bf31ea004df58f50026f8c7a80537e43d4001bea1ea014df10f50026fec5a80137e62d4009beb16a004df18b500a6fe65a804f7e32d4001be996a013df0cb50026fec3a80137e61d40013f30ea004df58750026f8c3a80537f31d4001bf18ea000df4c7500a6f863a804f7f21d4001bf10ea000df4875009ef843a80067d60d4003bf986a001df8c35000ef861a80077f20d4003bf106a001df0835000efc21a80077c10d40037fb2aa000ffd8d50005fec6a804bfe63540077f31aa000ff58d50097f8c6a800efc6354009ffa9aa004dfd4d50027fca6a804b7e5354009fea9aa000df54d50027f8a6a80137c5354025ff21aa000ff50d50097f886a8003ff62540017fb12a011ff98950015fcc4a800
  | 3 => 0xfb02a226ff9815100dfcc0a8803fd605444dfe302a201bf18151027fea0a88137f5054409ff282a204ff14151147fe60a889bfe305444dfe182a227ffc8151137fc40a889bfc205444dff082a226ff04151026fec6288137e6314409beb18a204df18c5112efc86288037d431444bbe218a204dfd8851026fcc4288137d6214409be310a225dfcc851126fc64288037d3214449be190a204df98451004fcc22881376611444bbf988a225df0c451126fe42288937c2114409bfb00a204df98051026fac0288027d6014409be300a225dfcc05111efc602888f7c3014449bf900a223df8805111ef8402888f7e1014447be080a200ffd9631005fecb1888bfe658c4097f32c6200ff59631005facb1888bfc658c4097e32c6200ffd9231005fec918887fe648c4217f3246200ff59231005fac918887fc648c4217e3246222ffd523110ffca918803fd548c443fe2a46203bf58e3101ffea71880ffe538c407fea9c6203ff14e3101ffe871880ffe438c407ef21c6203ff50e31007ba871880ffc438c401ffb146220ff98a31015fcc518803fd628c4017eb146220ff18a31015f8c51888bff528c441ff2946200ff54a31107f8a518887ff428c441ff2146200ff50a31107f8851880fff328c407ef9946203ff8ca3101ffa6518803dd328c407fe1946203bf98631117fea318803fe518c401bf28c6200ff54631117f8a3188037c518c443ffa0c6200ff9063110ff8831880fff318c407ef98c6203fdcc63101ff8631880ff4318c441ff90c6220ff08631007fec11887ffe608c4037f3046200ff58231005fac11887ffc608c4037e3046222ffd42310fffca11887ffc508c443ffa04621fff902310fff8811880fff308c407ff184621ff78c23101ff8611880fdc308c441ff904621fff882310fff8411887ffe108c43ffe0846200ffd9531005feca988037f654c4013fb2a621eff99531025fcca98803fd654c4017eb2a621eff19531025f8ca988037c654c4093e32a6200ffd9131005fec898877fe644c4217f3226200ff59131005fac898877fc644c4217e322621effd51310effca898803fd544c43bfe2a26203bfd8d3101ffea69880ffe534c407fea9a6203ff14d3101ffe869880ffe434c407fea1a6203ff10d31007fec498802ff624c439ff3126202bf98931007fac498873fc624c4057e312621effd49310e7fca498803fd524c439fe292621dffd09310e7fc8498803fd424c439fe2126203ffcc93101ffc649880ffd324c407fe1926203bfd85310f7fea298803fe514c401bf28a6200ff545310f7f8a2988037c514c43bffa0a6200ff90531007fa8298877fc414c407ff98a6203fdcc53101ffc6298803de314c407fe18a6203f70c53101fe86298873ff214c439fe10a6200ffd8131005fec09886ffe604c4037f3026200ff581
  | 4 => 0x3fd644c8017eb22642dff19132085f8c8990bbff544c85bff2a26400ff5513216ff8a89900aff634c807ffa9a6403ff94d3201fbca69900ffd534c801eea9a6403ff14d3201ffe869900ffe434c807ef21a6403ff50d32007ba869900ffc434c8057fb126402ffd4932017fca49900bfd524c805fe2926402ffd0932017fc849900bfd424c805fe2126402ffcc93201fde649900bfe324c805ef1926402ff0c932017b8649900bec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf18532177fea2990bbfc514c85bffa0a642dff1053201ffe629900ffc314c807ee18a6402ffc8532017f8429900bec214c801ffb026400bfd8132167fcc099006fe604c801feb02642cff1813200df8c0990bbff504c859ff282642cff1413216ffe80990b3fe404c859fe2026403ffcc13201fbe609900ffe304c807fe1826402ffc8132017de409900bfe204c805fe102642cff84132167f82099012fd6594401ffb1ca22bff98e5101dfcc728803fd63944017eb1ca22bff18e5101df8c728813ff5394409bfa9ca204ff94e5115efca728813fd5394401bea9ca204ff14e51026f8a7288affe4394401fea1ca22bff10e51007fec5288abfe62944057f314a200ff58a51005fac5288abfc62944057e314a204ffd4a51026fea528813fe5294455bf294a204ff54a51006faa528813fc5294409be294a22bffcca51157fc6528803fd3294455fe194a204bf98651027fea3288137f5194409fba8ca204ff14651027e8a3288afff3194457fe18ca22affc8651157f84328803ff6094453ff304a201bf98251007fac128802fd6094453fe304a201bf18251027fea1288137f5094409ff284a229df94251027f8a1288137c5094457ff984a229ff8c25114ff861288abff2094453ff104a229ff0825114ffc21288a7fc1094401bfb1ca22bdf98e51006fac7288af7c6394457bf21ca200df50e5115ef887288037f6294455bf314a200df58a51156f8c5288af7f3294455bf194a200df4ca51156f865288127e6194457bf98ca22bdf0c651156fe43288ab7c2194401bfb04a229df98251006fac1288027d6094453be304a22bdfcc25114efc61288a77c3094455bf904a229df8825114ef841288a77e1094453be084a204bfd9551007fec6a8802ff6354451ff31aa203bf98d51007fac6a88a3fc63544077e31aa204ffd4d51027fca6a8813fd5354409fe29aa228ff90d51007fa86a88a3fc4354401ffb12a200bfd895113ffcc4a880afe6254401feb12a227ff18951015f8c4a8813ff5254409ff292a204ff54951027f8a4a88a3ff325444fff192a200ff4c95113ff864a8812ff6154409ffa8aa204fdd4551027fca2a88037e5154409fe28aa204df14551027e8a2a88a3ff3154451fe18aa227ffc855113ff842a8803ff60544017
  | 5 => 0x9553007fec8a9802ff6454c6dff322a610bf99153007fac8a98dbfc6454c217e322a604ffd5153027fca8a98db7e5454c09feaa2a604ff15153026f8a8a980eff6354c07ffa9aa604f7d4d5301ffca6a980f7e5354c07fe29aa603df14d5301fb8a6a980fff4354c07ff21aa603ff10d53007fec4a9802ff6254c6bff312a602bf98953007fac4a98d7fc6254c057e312a604ffd4953026fea4a9813fe5254c09fe292a636ffd09531affc84a98d7fc4254c07ff992a603f7cc95301ffc64a980ffc3254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa600bf18553027fea2a9813fc5154c09be28aa636ffd05531b7f882a980fff3154c07fe18aa635ffc85531aff842a9803ff6054c017fb02a634ff9815300dfcc0a9803fd6054c69fe302a601bf18153027fea0a98137f5054c09ff282a604ff141531b7fe80a98d3fe4054c69fe202a603ffcc15301ffc60a980ffc3054c6bff902a634ff881531a7f840a98d3fe1054c69fe082a600ffd9543005fecaa18cffe6550c097f32a8600ff59543005facaa18cffc6550c097e32a8603bfd8d4301ffea6a18cfdf5350c07ff29a8603ff54d4301ff8a6a180fdc5350c07ff21a8603ef90d4301ff886a180fdc4350c07ce21a8600ffd8943005fec4a18cbfe6250c057f3128600ff58943197f8c4a180afc6250c67ffa928632ff94943197f8a4a180fff3250c07ef9928603ff8c94301ff864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a8633ffd454319ff8a2a180fff3150c07fe18a8603f70c543197fe42a18cbfc2150c01ffb028600bfd814318ffcc0a1806fe6050c01feb028631ff1814300df8c0a18cfff5050c63ff2828631ff1414301ffe60a180fdf3050c07ff1828603ff0c143197fe40a18c7fe2050c63fe1028631ff8414318ff820a180aff6554801ffb1aa400bfd8d52187fcc6a900efe6354801feb1aa430ff18d5201df8c6a9013ff5354809bfa9aa404ff94d52027faa6a90037d5354809fe29aa430ff90d52007fa86a90c3fc43548057fb12a402ffd4952027dea4a900bfe5254805bf292a402ff14952016f8a4a900bec5254805ff992a402ff8c952017f864a9003ff61548017fb0aa400ff98552007fac2a9003fc61548017e30aa404ffd4552027f8a2a90137c5154861ff98aa430ff0c552017fe42a900bfc2154801ffb02a400bfd815217ffcc0a9006fe6054801feb02a42fff1815200df8c0a9013ff5054809bfa82a404ff94152027f8a0a90c3ff305485fff182a42fff0c152017fe40a900bfe2054805fe102a42fff8415217ff820a9003ff654c8017fb2a6400dfd9532004feca990bbfe654c8097f32a6400ff59532005faca990bbfc654c8097e32a6400df19532024f8ca99003ff644c8017fb22642dff99132085fcc899
  | 6 => 0x101da00119480503017c8a600000125647413400127717119000089c0000001900007f4ab60006b20000000007783960005be1180000000bc000000eda000b04786124ff0e10e7eeb400000009cbd47fd1b9028d8e6c006d0a8c5c268924698724fd08e4082ee136106d4784c0aa20010b00004e81f90c8f502e000018ca60814128b805ea000320c58911014000fe47acc6c5d400042071d2e06fd341108e6e908ecc254e70aecabc68c7622ed3247411d82fd4480007e07f8c300000b12ac150214f669ea00032d16ed3c278e0f3acd6035c164a78ca40213111ec7105dc7e4036c1b000076938aa09345a03a2c351a2cf4b90f180008240012cc004028000000e805002000000008120000a0018000120000e0020000200181100a0c8000010180200080d0140000e0000000200000301a0040a80a0020180000000006c0d00200a0000000201c010018060020040080e0000000e8010180140002c00e0180980500c09400836000000010950380100083b000010040010100001680600a00c07800002034198000060000380200800002007050150010020480b8060010120180d01200001c0500000611003802004014050040100000480000602c00029030074008000080080a0030020200000100e008000040260000280001000c000000000040280103a0040481302602c010260040180d0020080100000200a00810004000004008530180101800002800c1880c0300c0010170260140200a0060440200208c0000280001000c00003030054018050080300602f0000080080000605c0480e034000018050040040001503a00800801002054040000000000180100208401806006000110050000040000000c0200900d02a0040000803000810005000064050040000640000f0260200180400600c010000120000380200401c0780400c020040000060040180000005c0000705e0080000700205802818008000010020060140280000001000009008024000030020040102d00a00c0b8010000240d80003e03400008010008090070040000000200000c0880101802c0d805002004018000140000400700203c0b0030040000100103c0340a01102402c038010380080000200203012802022000008010000040002b0340340381e01e00c0200e00c000030000060600300000200c020040180040200000c034090000020900000500200c0683f0140180580003e04003000000000058000060000400300200c00000030060068020060140281d00c0080000000c074000000220100100500600c000000020000081002e0940000004a0080180a02e000000000160000080a00006c0380a00e02c0100000005c07800016000030050080081d001030000090030000280101a00001400002000014058030000200400101201c0d80103803bfd
  | 7 => 0xe93293bd218a4c4348ca00052c000000404b547c4000b6d2f4f0291d2d419e78000065c508e5a5649a0000e540010492100000012412a0000e1616875c014000d902180c0000000088dea079188a94d44368b3c84a000000048000e6c1028284149440000001893c52200009800f84871cd3567f12d802d178e7a7653dc000e62918fa80000000000000001de0000000012700f00000540000012680013a48c4362fb4c24aa8f7cccc038954122aeab764ed008f607e89a480c40cb153f89c8860ee8af08c12169f6c2a72ab34b5cd180d93d54b4ce0000a503dd2040007606946d4238a303f0291314d78ea28d487cfc914d4bc3d83a40003ed2a482c11534e66400003524c28c7500005c059d2900000009dc6728a0638578e44f9120cf4c59a9aca3c74c5f4d2096f4883a060ed8d4c013601cbc4000000f228e0e243400003c434c38c43c00129c000a00e649aa0100000000000008b8884ed14951554742a860c6bcbf800000063200000140873d42ce802813f13843c0348d1cc44a6c44501084e140a3400099a4642f40000dc0501fd0eaedc8be3ace04000000cfd1fcde00000008829d02cc8c6f44d09294a24d0cc234a007d31c994c004f4178322000c3d3425e029936d28504ca2076c3a80004185321a800114529a2d81e8000000000058ecf24248128036d4a945000000075e001266a800001a20000008a8158ff501213d2d0a54458e187da73e874ffc3052c0000000000daa60a99ed3002e3d501916c7985dec4c6a8000e7c5043392a8cd000008c400dc4000fec0000000000013cc2d03d11e000012a0004d80000000005c800000078a001068000940558d391ac8bc3949ca72087b1b4000caceec000370728a74000000388dd0a6400000122c000000fcc748000000f042105311e4e732c80004cc0b8a403e8d1a4f9252ec2bec718c28ca84793fc5fd439128c88518689362aac0864087347aa6148e80af1c92930068a2538b4400096800000044cd013e08dc0012dc378106f260001dc54c93d33b15092d0d4294cba326008774000dd800000020e00037610095caa4ef8e951b0670001246e9112041c8b52e5124ae89752311e810e6f084873264d1a00689fca38b386369d6b8844843aa1c5bac0c265424e3058cb0902c84123c8007b53a8df945c39d3803667713682b0616730ba515905c033331298d043602847d10f8adcf88d5e6085d82609f22ad1a8000854fbc060148d86d46200b208ae24d34d352000000ef4fb8000001302978b7927d46cb405f096c9b80000000000012daed4c211d4e3c680000930f8611e000ba0c389ce6b4dae588d4941124a112ff81acefe9c514890c890920d684dc47f35e29c36a472af51a4a592d2450544d2d090f945e455d37400072e000c4060485849c84cc9849027a9287d450a6
  | 8 => 0x7c000000010907000132c580b98000be8d34d82e1239e6409de6a030c86cad537cff2d56554efa668372b840980f4844f688521a0b6026a2b823c14432e9a8b2cbd03980000e12ff3642080005a4000ea800143400117c31543046c3a63bee52b3a926e34d1494ceb8a054986743bcb2871f480000b740450390203f83ba19c77ef1c79d35d1f473a00c7d2894be07fae9a000880c0543c0002e3016000758ab90243b8072d50fb0b10d74bf0e7533c5a8c1c15cf9c310f34a71354184fe2000dc9254fd48d20282743c6de4484180001078001064bbc7550840005923c2f254a43f4db0e000000007b867948c4b0db94186dc9bc66c00064905925e12e9f51410a000070e3184fca88000cec000c7c090d428ba1b84b80005107008ed370e5e62cde8000c8c000a9932141402411b28c0000012c442e0000007c85507a8ba81e4b00000e40a2d2d6000000fe71321c12006c8634e84c6000107ced647022c7d66e40acec6272f200fc9ed1650984d4fdc8f4e28e6a38032b1ab160f10df0a28b7c948cb9468a68afc1310446f8d10ff6344984db4e4cab031c5e68d0712f0d26a196708c74c544d057c782870e56b950052781205c6630000ca0c1400048a1f4e08d802a0da4900a0cd7c0000b52887aecc0bb0a180010fc5b007a970d5cc84620b18864acd07451d344000722fc4b48000f3c00061c0b27feb4cdac99837492a0013e53002490e87cf0020000004e40000013b04773b800103c4ad2092742e6b8c2200012b8000b64f5c14cd6200101c5acda885126d0f5458ae465026e1051847a0240160e78116d711313e85491bc004a9cf4949d30b0dcaaac81180560dc00a40012e80008ce25f11109400021730d20e000b0c174ae04c8f1e00135a064d98258b160001ef00c00099cf70d8b3580006591747a61d0cf0d94001138000000000dcd21cfa4f780000000000000005060012588b6000266000879440b24ebc4cb3f467cefc0aa51462e0009fad8419a2353381c805c494f40c273b4001490dbcc64d5500f250c78ac46d011d3510ac7ca56d398288fa1238c2c6907909e09960fe0000012fc0005b4000ee40010a48d8bf48c8af80c4dd4a5c810000c112b400050c5c2ed80004a49d80000004552480013a0ddc000fea12c8cd378ad9102000000d5a6ccf08428eacf8e000438e9e87677c33d264000ffb39cf6a0010cc9d4fe0e2cd88da62c02308fd1685e8154d7e7162771e2c490ec468070d4d38c0309885349c119cdf42f14700003ae70cf008b06ba03ccdc618b1c328596bc00000ccea404d44478800067653d2b109c8682ea22448ea146ec00134607e3648acc8ed6d080768000000660204e383aa1d408538810a898b30c527ed1c4726000001404000000000000e20566d402a44e09141ea8c319845c43213aa8496a47d0d
  | 9 => 0xada81cb500010e4ed2498000e60c923fc000000358e688310b92249e81bc21c00062857066a9eeac00012ec3e4000dfcb680013060013c80002b41e2ad0e5d0e0808411260742e48000c509590612bd4207d80e4f14384a4421a5e311cd1e3246acef73083e03304a8000000000c9d3340002f828273692239b1180000000008347f6ec8eb12963910c0e671f93492346e80002dc97cbd8cb124e684000f8c0c8fd8cfe0005cc7946066252127451e617072c25c9a200100a20c2c400118cec0000de6f284880000002e8f6ccc400027ec7000095124454085c0000013d80001cc70525a5d00000ec6b8000000000da00010fe7389b00000000003509e2bc84410d8f98ce44dad64c954285b842cbfc4611d0094aba7b0000fee000ec4f586e063c2129a6f920000d42e40000007840d08384246f41c49d26becf940d10c6c43b6905484cd4000fc026c2c866e888d9c7661109771049cc04126331852871a03a0805685c4e76cbcc0800087e2bca090b42560009da00147c0000004bc7dc13efac3b46a5460e50000132fe8e143b2f30ab48aaef0820f06270fdef852720a00000000000008188560005750c43014006132f08a444e3b00004b4dec000e990889f94acd293ec00016c0003cd13c714bcc83c2d4c68a8c6546d90501d8c185bc1988b2308f8a7a4e1c1a4644cb46b070a9e6591228ea0c90a49454d24d221b4fff26e27c600ab2be47ccbac44acc80000a908c00129eb709e51343c8961394e1b1f0262b58bdc1e60191dc0004c544d3c0a7c1ecbb8000c620005986b62defda12600078d3912f89f0990ce912ce9c7a20003348f01380000013d04f0524000d58e8ce585ec7bd15c000a900000005f930436ef5521459400105407534a69c0a6286a109b4e0cf2c98c48cf810f0ac8f6425a707034cd8e88521114000f75100bb43542281f01e11c14b00004a09654651a60001b05010bc37c8f904010cb9d4b897258541c00000125c24488c250000f38000000194000430
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7658c51000774658c510005f7748c510005f5748c510007b7648c510007b4648c5100ddf5738c5100ffd7638c51001ef6638c51001ef4638c510037d4638c51001ed4638c510037d6438c510007d5438c510005f5728c510007e7628c510007e4628c510037d7328c510007d5328c51000df6708c51000df4708c5100fef7608c5100ff77508c5100ff75508c5100ffd6308c5100ffd4308c51001cff764c51000cfe764c5100dcfd764c51000cfc764c5100057f754c51003d7c754c5100067f654c5100f67c654c510006bf644c5100eebc644c510006df634c51001edc634c510006ef624c5100e6ec624c51000776514c51000774514c510037d4314c510005fb704c51000df8704c51000df4764c51001ef4764c51000cf4764c51000777754c51000774754c51000777654c51000774654c510005f7744c510005f5744c510007b7644c510007b4644c5100fdf7734c510007d7734c510007d7634c51001ef6634c51001ef4634c510037d4634c510005f7724c510007e7624c510007e4624c510007f3704c51000df6704c51000df4704c5100dff0704c5100def7604c5100df77504c5100df75504c5100dfd7304c5100dfd5304c5101c4fe76885100067f65885100d67c6588510006df63885100cedc63885100c6ef6288510016ec62885100077651885100077451885101c5f676885101bef67688510007776588510007746588510005f77388510005f57388510007d76388510007d463885100adf572885100c7e76288510016f66288510016f4628851002fe46288510016e4628851002fe63288510007e5328851000df6708851000df470885100c6f760885100c77750885100c77550885100c7e620885100c7e42088510014ff764851000cfe76485100acfd764851000cfc76485100057f754851003d7c75485100067f65485100be7c6548510006df63485100b6dc6348510006ef6248510016ec624851000776514851000774514851002fe42148510005fb704851000df8704851000df47648510016f4764851000cf47648510007777548510007747548510007776548510007746548510005f77348510005f57348510007d76348510007d463485100c5f77248510007e77248510007e76248510016f66248510016f4624851002fe46248510016e46248510007f3704851000df6704851000df470485100aff070485100aef760485100af7750485100af7550485100afe720485100afe5204851000dfa76c411000efa76c411000cfa76c41100077b75c41100077875c41100077b65c41100077865c4110007db63c4110007d863c4110007eb62c4110007e862c411000dfa71c411000ff271c411000efb61c411000ff361c41100077a51c41100077851c4110007f231c4110007f131c4110007f221c4110007f121c4110
  | 1 => 0x8910035dc7358910006df6358910006dc635891002eec62589101ddf77158910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7358910006df7358910004df735891001cfe735891001cfc7358910006dc735891001cdc73589100c4ff7258910006ef72589101dcff7158910006f771589100acff7058910006fb70589100ae7f50589100ae7d50589100c5ee761891002eee76189100c4ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189101c7e571189101c6ef61189101c6ef60189101c76f50189101c76d50189101c7e610189101c7e410189101c7e81018910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100267c6554910006df6354910186dc6354910006ef6254910016ec6254910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c91003d7c754c9100067f654c9101767c654c910006bf644c91016ebc644c910006df634c91001edc634c910006ef624c910016ec624c91011cfe769451014e7f65945100267e65945100067d65945100267c6594510006df639451015edc6394510006ef6294510156ec629451014ff0109451011d7e76945100067e769451011c7e76945100067f63945100075f63945100065f639451015e7e63945100067d639451015e7c63945100075c639451015e5c63945100067f62945100076f62945100066f62945101567e62945100067d62945101567c62945100076c62945101566c629451011d7e719451014e7f619451014d7f709451014d7d709451014e7f609451014f76109451014f74109451014f78109451014f701094510024ff765451000cfe7654510134fd765451000cfc76545100067f65545100267c6554510006df6354510146dc6354510006ef625451013eec6254510005fb705451000df87054510137f0105451014d7e761451003e7e761451014c7e76145100067f63145100075f63145100065f631451012e7e63145100067d631451012e7c63145100075c631451012e5c63145100067f62145100076f62145100066f62145101267e62145100067d62145101267c62145100076c62145101266c621451014d7e711451003f76711451011e7f611451011d7f701451011d7d701451011e7f601451011f76101451011f74101451011f7810145101d4fe768c5100067f658c5101167c658c510006bf648c51010ebc648c5100fedf638c51001edc638c510006ef628c510106ec628c51000776518c51000774518c5101d5f6768c5101cef6768c5100077
  | 2 => 0x247c7558d10004ff7458d10006bf7458d10004bf7458d10084fe7458d10084fc7458d10006bc7458d10084bc7458d100fcff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d101e4ff7158d10006f77158d100dcff7058d10006fb7058d100de7f5058d100de7d5058d100fdde7618d10036de7618d100fcde7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d101d7d57118d101d6df6118d101d6df6018d101d75f5018d101d75d5018d101d7d61018d101d7d41018d101d7d81018d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100267c6554d10006bf6454d101b6bc6454d10006df6354d1001edc6354d101aeec6254d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1019e7c6550d10006df6350d1001edc6350d100379c4350d10196ec6250d10014fe76d89100067f65d89100067c65d8910006df63d8910006dc63d891002eee62d8910024fe75d8910004fd75d8910024fc75d891001cfe73d8910004fd73d891001cfc73d8910006ef52d891002eee52d891002eec52d8910006ef32d891002eee32d891002eec32d8910014fe71d891000cfd71d8910014fc71d891002eef21d89100c4ff70d891000cfe70d89100c4fd70d891000cfc70d89100c67f50d89100c67d50d89100c6ef20d89100c6ed20d89101c5ee76d8910014ee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100c7e771d89100c76f50d89100c76d50d89100c7e610d89100c7e410d89100c7e810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d89100c6ef71d891002eee71d89100c6ed71d8910006ef51d8910006ec51d8910006ef31d8910006ec31d89100c6ef70d89100c6ee70d89100c6ed70d89100c6ec70d89100c6ef50d89100c66f50d89100c6ee50d89100c6ed50d89100c66d50d89100c6ec50d89100c6ef30d89100c6ee30d89100c6ed30d89100c6ec30d89100c6ef10d89100c6ee10d89100c6ec10d89100057f755891003d7c75589100067f65589100067c6558910005df735
  | 3 => 0xd20d951014e7c20d951014e7f10d951014e7e10d951014e7c10d951003e7c6559510005df7359510035dc7359510005ef725951002dec72595101f5f7715951014cff75595100067f7559510004ff7359510006df7359510004df735951001cfe735951001cfc7359510006dc735951001cdc7359510004ff7259510006ef7259510004ef7259510014fe7259510014fc7259510006ec7259510014ec72595101f4ff7159510006f7715951003e7c5159510134ff7059510006fb70595101367f50595101367d505951014d7e761951003e7e761951014c7e76195100067e63195100067c63195100067e62195100067c621951011e7f611951011e7f601951011f76101951011f74101951011f78101951001cfe76d8d100067f65d8d100067c65d8d10036de63d8d10024fe75d8d10004fd75d8d10024fc75d8d10084fe74d8d10004fd74d8d10084fc74d8d10006df53d8d10036de53d8d10036dc53d8d10006df43d8d10036de43d8d10036dc43d8d10014fe72d8d10004fd72d8d10014fc72d8d10036df32d8d10006de32d8d10036dc32d8d1001cfe71d8d1000cfd71d8d1001cfc71d8d10036df31d8d100fcff70d8d1000cfe70d8d100fcfd70d8d1000cfc70d8d100fe7f50d8d100fe7d50d8d100fedf30d8d100fedd30d8d101d5de76d8d1001cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dc64d8d10006de62d8d10006dc62d8d100ffd771d8d100ff5f50d8d100ff5d50d8d100ffd610d8d100ffd410d8d100ffd810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d100fedf71d8d10036de71d8d100fedd71d8d10006df51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d100fedf70d8d100fede70d8d100fedd70d8d100fedc70d8d100fedf50d8d100fe5f50d8d100fede50d8d100fedd50d8d100fe5d50d8d100fedc50d8d100fedf40d8d100fede40d8d100fedd40d8d100fedc40d8d100fedf20d8d100fede20d8d100fedd20d8d100fedc20d8d100fedf10d8d100fede10d8d100fedc10d8d100057f7558d1003d7c7558d100067f6558d100067c6558d10005bf7458d101edbc7458d10006bf6458d10036dc6358d10005ef7258d1002dec7258d101e5f77158d10004ff7558d100067f7558d100047f7558d10024fe7558d10024fc7558d100067c7558d10
  | 4 => 0xc710005f5728c71004fd7328c710007d5328c71000df6708c7100fff2708c710007f1708c71000df4708c7100ff77508c7100ff75508c7100ffd6308c7100ffd4308c7101e4ff764c7100057f754c7100557c754c7100067f654c7100f67c654c710006df634c71001edc634c71000776514c71000774514c71004fd4314c7101e5f7764c710206f7764c71000777754c71000774754c71000777654c71000774654c710005f7744c710005f5744c710007d7734c710007d7634c71001ef6634c71001ef4634c71004fd4634c710005f7724c71000df6704c71000df4704c7100df77504c7100df75504c7100dfd7304c7100dfd5304c71000cff7688710014fe768871000cfd76887100067f65887100d67c6588710016ee6288710006ed628871000776518871000774518871000dfa7088710005f9708871000df57688710016f5768871000cf57688710007776588710007746588710005f77388710005f57388710016f66288710047e66288710007e56288710016f46288710047e63288710007e5328871000df670887100c7f27088710007f1708871000df470887100c77750887100c77550887100c7e620887100c7e420887101dcff76487100057f75487100557c75487100067f65487100be7c6548710006ef6248710016ec6248710007765148710007745148710047e421487101ddf776487101fef77648710007777548710007747548710007776548710007746548710005f77348710005f57348710007e77248710007e76248710016f66248710016f46248710047e46248710016e4624871000df6704871000df470487100af7750487100af7550487100afe720487100afe52048710024fe76d951003e7e65d951001cfe73d9510004fd73d951001cfc73d951003e7f53d95100067e53d951003e7c53d9510014fe72d9510004fd72d9510014fc72d951003e7f52d95100067e52d951003e7c52d9510024fe71d951000cfd71d9510024fc71d951003e7f51d951014cff70d951000cfe70d951014cfd70d951000cfc70d951014e7f50d951014e7d50d951011d7e76d95100247e76d95100067e63d95100067c63d95100067e62d95100067c62d951014f7610d951014f7410d951014f7810d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067c32d951014e7f71d951003e7e71d95100247e71d951014e7d71d95100247c71d95100067f31d95100067c31d95100067f21d95100067c21d951014e7f70d951014c7f70d951014e7e70d951014e7d70d951014c7d70d951014e7c70d951014e7f30d951014e7e30d951014e7d30d951014e7c30d951014e7f20d951014e7e20d951014e7
  | 5 => 0x4ff7458f10084fe7458f10084fc7458f10006df7358f10004ff7258f10014fe7258f10014fc7258f1001cff7158f1001cfd7158f1000cfc7158f1004edc3158f100de7f5058f100de7d5058f100dedf3058f100dedd3058f10004ff7654f10004fe7654f10004fd7654f10004fc7654f100067f6554f100267c6554f10004ff7650f10004fe7650f10004fd7650f10004fc7650f100067f6550f1019e7c6550f10006df6350f1001edc6350f1004f9c4350f100067f65d8b100067c65d8b10046ee62d8b101c5f671d8b10024fe75d8b10004fd75d8b10024fc75d8b1001cfe73d8b10004fd73d8b1001cfc73d8b100acfd72d8b10046ee32d8b101c4fe71d8b10006f671d8b10046ef21d8b10006f970d8b100c67f50d8b100c67d50d8b100c6ee20d8b100c6ec20d8b10014ff7658b100057f7558b100557c7558b100067f6558b100067c6558b10046ec6258b10004ff7558b100067f7558b100047f7558b10024fe7558b10024fc7558b100067c7558b100247c7558b10004ff7358b1001cfe7358b1001cfc7358b10006ef7258b10014ff7158b10014fd7158b1000cfc7158b10046ec2158b100ae7f5058b100ae7d5058b100aeef2058b100aeed2058b10004ff7654b10004fe7654b10004fd7654b10004fc7654b100067f6554b100267c6554b10004ff764cb10004fe764cb10004fd764cb10004fc764cb100057f754cb100557c754cb100067f654cb101767c654cb10006df634cb1001edc634cb10006ef624cb10016ec624cb1000cff7694710024fe769471000cfd76947100267e65947100067d659471000dfa7094710005f9709471014e7f76947100267e76947100267d769471014e7c76947100067f639471015e7e63947100067d639471015e7c63947100067f62947101567e62947100067d62947101567c629471014e7e619471014f7a709471014d7d709471000779709471000579709471014f76109471014f7a109471014f7410947101f4ff76547100067f65547100267c65547100267f761471014d7e76147100567e761471011e7d76147100267c76147100247c76147100067f631471012e7e63147100067d631471012e7c63147100067f62147101267e62147100067d62147101267c621471005776711471011e7e611471011d7f701471011f7a701471011d7d701471005779701471000579701471011f76101471011f7a101471011f74101471000cff768c71001cfe768c71000cfd768c7100067f658c7101167c658c71001ede638c710006dd638c71000776518c71000774518c71000dfa708c710005f9708c71000df5768c71001ef5768c71000cf5768c71000777658c71000774658c710005f7748c710005f5748c71001ef6638c71004fd6638c710007d5638c71001ef4638c71004fd6438c710007d5438
  | 6 => 0xe201452011f6c201452011f782014520004fe768c520004fd768c520004fc768c520006df638c52001edc638c520015ee728c520005ed728c520007cd328c520004ff764c520004fe764c520004fc764c5200057f754c5200657c754c520015ee724c52000dec76485200aeec764852000cec76485200076f75485200076c7548520005ef7348520005ed7348520015ef7148520017e77148520007e76148520006ec6148520007e46148520006e461485200076e51485200076c5148520007eb704852000dee704852000dec70485200afe87048520016ef6048520017eb60485200af6f50485200af6d50485200567e65d971011df671d9710134fd75d971001cfe73d9710004fd73d971001cfc73d97100567f53d97100067e53d97100567c53d9710014fe72d9710004fd72d9710014fc72d97100567f52d97100067e52d97100567c52d971011cfe71d9710006f671d97100567f51d9710006f970d971014e7f50d971014e7e50d971014e7d50d971014e7c50d97100067e63d97100067c63d97100067e62d97100067c62d971011d7e71d97100077671d971011d7671d97100077970d971014f7610d971014f7a10d971014f7410d97100067f73d97100067e73d97100067d73d97100067c73d97100067e43d97100067c43d97100067f72d97100067e72d97100067d72d97100067c72d97100067f32d97100067e32d97100067c32d97100067e71d971011c7e71d97100067671d97100067f31d97100067c31d97100067f21d97100067c21d971014e7d70d97100067970d971014e7f30d971014e7e30d971014e7d30d971014e7c30d971014e7f20d971014e7e20d971014e7d20d971014e7c20d971014e7e10d971014e7c10d9710024ff76597100567c65597100067f7559710004ff735971001cfe735971001cfc7359710004ff7259710014fe7259710014fc7259710024ff7159710024fd715971000cfc71597100567c51597101367f50597101367d50597100567e76197100067e63197100067c63197100067e62197100067c621971014d7e711971005776711971014d76711971011e7e611971005779701971011f76101971011f7a101971011f7410197100067f65d8f100067c65d8f1004ede63d8f101d5f671d8f10024fe75d8f10004fd75d8f10024fc75d8f10084fe74d8f10004fd74d8f10084fc74d8f100dcfd73d8f1004ede43d8f10014fe72d8f10004fd72d8f10014fc72d8f1004edf32d8f101d4fe71d8f10006f671d8f1004edf31d8f10006f970d8f100fe7f50d8f100fe7d50d8f100fede30d8f100fedc30d8f1001cff7658f100057f7558f100557c7558f100067f6558f100067c6558f1004edc6358f10004ff7558f100067f7558f100047f7558f10024fe7558f10024fc7558f100067c7558f100247c7558f10
  | 7 => 0x8d20004fc7158d20006f47158d20004f47158d20164ff7058d20006fb7058d201667f5058d201667d5058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200267e6554d200067d6554d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2001ede6350d20006dd6350d2005f9c4350d20015ee7250d2000dec764c92001eec764c92000cec764c9200076f754c9200076c754c920005ef744c920005ed744c920015ef734c920017cf734c920007cf634c92001eee634c92001eec634c92005fcc634c92005fce534c920007cd534c92005fce434c920007cd434c920005ef714c92005fcc314c920007eb704c92000dee704c92000dec704c920167e8704c920016ef604c920017eb604c9201676f504c9201676d504c920167cf304c920167cd304c9200657e75d85200057d75d8520024fe75d85200067e75d85200247e75d8520004fd75d85200067d75d85200047d75d8520024fc75d852001cfe73d8520004fd73d852001cfc73d852000cfd72d8520006f751d8520006f451d8520006f731d8520006f431d85201bef621d85201bef521d8520014fd70d85201de7f50d85201de7d50d85201def710d8520006f7619852002df970985200057f75585200657c7558520005df735852005ddc7358520045fb7058520006f56118520024fe7518520004fd7518520024fc751852001cfe7318520004fd731852001cfc731852000cfd72185201c6ed72185201feee3218520006ed3218520006f75118520006f45118520006f73118520006f431185201feef21185201fef621185201fef5211852000cfe7018520014fd701852000cfc70185201c67f50185201c67d50185201c6ee20185201c6ec20185201c6f51018520004fe7694520004fd7694520004fc76945200067f65945200267e65945200067d65945200267c6594520015ee7294520005ed72945200067f76945200067e76945200067d76945200067c76945200067f639452015e7e63945200067d639452015e7c63945201576e72945200076d729452014e7f62945201576e32945200076d329452011d7e71945200067f61945200067c61945201576f219452014d7d709452014e7f60945201577b209452014f6e209452014f6c209452014f782094520004ff7654520004fe7654520004fc76545200267f76145200667e76145200667d76145200267c76145200067f631452012e7e63145200067d631452012e7c63145201276e72145200676d721452011e7f62145201276e32145200076d321452014d7e71145200677671145200067f61145200077761145200067761145200067c61145200077461145200067461145201276f211452011d7f701452011f7a701452011d7d701452006779701452000579701452011e7f60145201277b201452011f6
  | 8 => 0x12f7b301453011f5e301453011f5c301453011f783014530004fe7690530004fd7690530004fc7690530006bf6490530086bc649053001dde7390530005dd73905300079d4390530004ff7650530004fe7650530004fc76505300057f755053007d7c755053001dde735053000ddc764c5300dedc764c53000cdc764c5300075f754c5300075c754c530005df744c530005dd744c530005df724c53001ddf714c53001fd7714c530007d7614c530006dc614c530007d4614c5300075e514c5300075c514c530007db704c53000dde704c53000ddc704c5300dfd8704c53001edf604c53001fdb604c5300df5f504c5300df5d504c530004fe7688530004fd7688530004fc768853001dde7388530005dd7388530006ef6288530016ec6288530007cd3288530004ff7648530004fe7648530004fc76485300057f754853007d7c754853001dde7348530005dd734853006fe42148530024fe76d95200667e65d952017cfd75d952001cfe73d9520004fd73d952001cfc73d95200067e53d95200667c53d952000cff72d9520014fe72d952000cfd72d9520014fc72d95202467f52d95202467d52d9520004fe71d9520004fd71d95200667c51d9520014ff70d9520014fd70d952023e7f50d952023e7d50d9520024ff76595200667c6559520005df735952005ddc7359520235ef7259520005f77159520005f4715952009dfb705952023cff75595200067f7559520004ff7359520006df7359520004df735952001cfe735952001cfc7359520006dc735952001cdc73595200667f5359520234ff7259520006ef725952008e7e525952008e7c5259520004ff7159520006f77159520004f77159520004fc7159520006f47159520004f471595200667c515952017cff7059520006fb705952017e7f505952017e7d505952001cfe76d8d2005ede63d8d20024fe75d8d20004fd75d8d20024fc75d8d20084fe74d8d20004fd74d8d20084fc74d8d20164fd73d8d20006df53d8d2005edc53d8d20006df43d8d2005edc43d8d2000cff72d8d20014fe72d8d2000cfd72d8d20014fc72d8d2022edf32d8d2022edd32d8d20004fe71d8d20004fd71d8d2005edc31d8d20014ff70d8d20014fd70d8d202167f50d8d202167d50d8d20216df30d8d20216dd30d8d2001cff7658d200057f7558d200657c7558d20005bf7458d20225bc7458d2005edc6358d2020def7258d20005f77158d20005f47158d2021dfb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20024fc7558d200067c7558d200247c7558d20004ff7458d20006bf7458d20004bf7458d20084fe7458d20084fc7458d20006bc7458d20084bc7458d20214ff7358d20006df7358d2005ede4358d2020cff7258d20006ef7258d20004ff7158d20006f77158d20004f7715
  | 9 => 0xc6258930005f77158930005f4715893025dfb7058930004ff7654930004fe7654930004fc76549300267e65549300067d6554930004ff7650930004fe7650930004fc76509300057f755093007d7c7550930086be645093001dde73509300079d435093000ddc764c930016dc764c93000cdc764c9300075f754c9300075c754c930006df654c930006dd654c930005df744c930005dd744c930006df644c930006dd644c93001ddf724c93001fcf724c930007cf624c930016de624c930016dc624c93006fcc624c930005df714c93006fcc214c930007db704c93000dde704c93000ddc704c930167d8704c93001edf604c93001fdb604c9301675f504c9301675d504c930167cf204c93007d7e75d85300057d75d8530024fe75d85300067e75d85300247e75d8530004fd75d85300067d75d85300047d75d8530024fc75d8530084fe74d8530004fd74d8530084fc74d853000cfd73d8530014fe72d8530004fd72d8530014fc72d85301cef631d85301cef531d8530006f721d8530006f421d853001cfd70d85301e67f50d85301e67d50d85301e6f710d8530006f76198530035f970985300057f755853007d7c7558530005bf7458530075bc7458530005ef725853006dec725853004dfb7058530006f56118530024fe7518530004fd7518530024fc7518530084fe7418530004fd7418530084fc741853000cfd73185301d6dd7318530206de4318530006dd4318530014fe7218530004fd7218530014fc7218530206df3218530006dd3218530206df3118530206f63118530206f53118530006f72118530006f4211853001cfd70185301d67f50185301d67d50185301d6de30185301d6dc30185301d6f51018530004fe7694530004fd7694530004fc76945300067f65945300267e65945300067d65945300267c659453001dde7394530005dd73945300067f76945300067e76945300067d76945300067c76945300067f64945302567e64945300067d64945302567c649453015f5e73945300075d739453014e7f639453015f5e43945300075d43945300067f62945301567e62945301567c629453015f5f32945300075d329453011d7e71945300067f61945300067c619453015f5f319453014d7d709453014e7f609453015f7b309453014f5e309453014f5c309453014f783094530004ff7654530004fe7654530004fc76545300267f761453007e7e761453007e7d76145300267c76145300067f641453024e7e64145300067d641453024e7c641453012f5e731453007f5d731453011e7f631453012f5e43145300075d43145300067f62145301267e62145301267c621453012f5f32145300075d321453014d7e711453007f7671145300067f61145300067c611453012f5f311453011d7f701453011d7d701453011e7f6014530
  | 10 => 0x855000d7e704855000d7c70485500ae7f60485500bf7b60485500af6f2048550024fe76d953007e7e65d95301a4fd75d9530084fe74d9530004fd74d9530084fc74d953007e7f54d953000cff73d953001cfe73d953000cfd73d953001cfc73d95302ae7f53d95302ae7d53d9530014fe72d9530004fd72d9530014fc72d95300067e52d953007e7c52d95302aedf32d9530004fe71d9530004fd71d953007e7c51d953001cff70d953001cfd70d95302a67f50d95302a67d50d9530024ff765953007e7c655953029ddf73595300a5fb70595302a4ff75595300067f7559530004ff7459530084fe7459530084fc74595300067e545953007e7c545953029cff7359530006df73595300967e53595300967c5359530004ff7259530014fe7259530014fc725953007e7f5259530096df3259530004ff7159530004fc715953007e7c51595301a4ff7059530006fb70595301a67f50595301a67d5059530084fe76d913007d7e75d91300057d75d9130076be64d9130024fe75d91300067e75d91300247e75d9130004fd75d91300067d75d91300047d75d9130024fc75d913018cfd74d9130076be54d913000cff73d913001cfe73d913000cfd73d913001cfc73d9130296bf43d9130296bd43d9130014fe72d9130004fd72d9130014fc72d9130006be42d9130076bc42d9130296df32d9130004fe71d9130004fd71d9130076bc41d913001cfd70d913028e7f50d913028e7d50d913028ebf40d9130084ff7659130076bc645913027ddf7359130285fb7059130004ff7559130024fe7559130024fc755913027cff7359130006df7359130004ff7259130014fe7259130014fc7259130276df3259130004ff7159130004fc715913018cff7059130006fb705913018e7f505913018e7d5059130004ff7655130004fe7655130004fd7655130004fc76551300067f65551300267c6555130006bf6455130086bc645513000ddc7650d30086dc7650d3000cdc7650d3019ede6550d3019edc6550d3001ddf7450d3001f9f7450d300079f6450d30086de6450d30086dc6450d300779c6450d300869c6450d3026f9f5450d300779c5450d30005df7250d300779f4250d30005df7150d300779c4150d30007db7050d3000dde7050d3000ddc7050d3018fd87050d3001edf6050d3001fdb6050d3018f5f5050d3018f5d5050d3018f9f4050d3018f9d4050d30014fe76d893006eee62d8930024fe75d8930004fd75d8930024fc75d8930084fe74d8930004fd74d8930084fc74d893000cfd73d8930014fc73d8930266de43d8930006dd43d893006eee32d8930266ed32d8930004fe71d8930004fd71d893006eec21d893001cfd70d893020e7f50d893020e7d50d893020eef20d89300057f755893007d7c7558930005bf7458930075bc745893006ee
  | 11 => 0x57b705855003f7b60585501f57e76185500957e73185500057d73185500957c73185500067f63185500067e63185500067d63185500067c631855008d7e72185500057d721855008d7c72185500067f62185500067e62185500067d62185500067c62185500067f61185500077661185500067d61185500077561185500077721185500077421185500257f701855000d7e70185500257d701855000d7c701855011e7f60185502bf7b601855011f77101855011f7510185500067f73185500067e73185500067d73185500067c73185500067e43185500067d43185500067c43185500067f72185500067e72185500067d72185500067c72185500067f32185500067e32185500067d32185500067c32185500067f31185500067c31185500067f21185500067721185500067c211855000674211855011e7f701855011e7d70185500247d701855011e7f301855011e7e301855011e7d301855011e7c301855011e7f201855011e7e201855011e7d201855011e7c201855011e7e101855011e7d101855011e75101855011e7c10185500057f768c5500057e768c5500057d768c5500057c768c5500057f748c5502b57e748c5500057d748c5502b57c748c5500dd7d738c5500075f638c5500975c638c5500975e438c5500075d438c55008d7e728c5500057d728c55008d7c728c5500975f328c5500075d328c5501d57e718c5500067c618c5500975f318c55009777318c55009774318c55000d7e708c5500fd7d708c55000d7c708c5500fe7f608c5501177b608c5500ff5e308c5500ff5c308c5500057f764c5500067f764c5500047f764c5500057e764c5500057d764c5500057c764c5500067c764c5500047c764c5500057f744c5502b57e744c5500057d744c5502b57c744c5500fd7f734c5500057f724c55008d7e724c55008d7c724c5501e57f714c5500067c614c55009777314c5500075e314c5500975c314c55009774314c5500dd7f704c55000d7e704c55000d7c704c5500de7f604c5500f77b604c5500df5f304c5500057f76885500057e76885500057d76885500057c76885500057f73885500957e73885500057d73885500957c73885500ad7d72885500076f628855008f6c628855008f6e32885500076d32885501c57e71885500067c618855008f6f218855008f77218855008f74218855000d7e70885500c57d708855000d7c70885500c67f60885500d77b60885500c76e20885500c76c20885500057f76485500067f76485500047f76485500057e76485500057d76485500057c76485500067c76485500047c76485500057f73485500957e73485500057d73485500957c73485500c57f72485501dd7f71485500067c614855008f7721485500076e214855008f6c214855008f74214855008f6421485500ad7f704
  | 12 => 0xc6458d5029d7f7358d500075f6358d500967e6358d500967c6358d500975c6358d500965c6358d500057f7258d5008d7e7258d5008d7c7258d500975f3258d500057f7158d500057c7158d501a57f7058d500077b7058d500057b7058d5007f7b6058d500057f7650d500057e7650d500057d7650d500057c7650d5027d7f7350d500075f6350d500975c6350d500973e4350d500975c4350d500971c4350d500057f7250d5008d7e7250d5008d7c7250d500975f3250d500057f7150d500057c7150d500975c3150d5018d7f7050d5000d7e7050d5000d7c7050d5018e7f6050d5019f7b6050d5018f5f3050d502d57e76d89500957e73d89500057d73d89500957c73d89500067f63d89500067d63d895008e7e62d895008f6e62d895008e7c62d89500057e71d89500057d71d895008f6c21d89500257f70d895000d7e70d89500257d70d895000d7c70d89502367f60d89502cf7b60d89502376f20d89502376d20d895023d7f76589500057f73589500075f73589500055f73589500957e73589500957c73589500075c73589500955c73589500067f63589500067d63589502357f72589500076f625895008e7e625895008e7c625895008f6c62589500057f71589500077771589500057771589500057c715895000774715895000574715895017d7f70589500077b70589500057b70589500677b60589500057f764c9500067f764c9500047f764c9500057e764c9500057d764c9500057c764c9500067c764c9500047c764c9500057f744c9502b57e744c9500057d744c9502b57c744c9502157f734c9500975e634c9500075d634c9500975e434c9500075d434c95020d7f724c9500976f324c95008f5e324c95008f5c324c95008f6c324c9500057f714c9500057c714c9500975c314c95008f6c214c9501657f704c95000d7e704c95000d7c704c9501667f604c9501777b604c9501675f304c9501676f204c9500957e73d85500057d73d85500957c73d855008d7e72d85500057d72d855008d7c72d85500077721d85500077421d85500257f70d85500257d70d85501f67f60d85502c77b60d85501f77710d85501f77510d85500957e73985500057d73985500957c73985500067f63985500067e63985500067d63985500067c639855008d7e72985500057d729855008d7c72985500067f62985500067e62985500067d62985500067c629855011d7e71985500067f619855000777619855014d7d70985500077970985500057970985500577b60985500057f73585500075f73585500055f73585500957e73585500957c73585500075c73585500955c73585500057f72585500076f72585500056f725855008d7e725855008d7c72585500076c725855008d6c72585500077761585500067e61585501357f70585500077b7058550
  | 13 => 0xc9500057f754c9500257e754c9500057d754c9500257c754c95001ede634c9500975e534c9500075d534c95000cfd75d85501f67d75d855001cfe73d8550004fd73d855001cfc73d8550014fe72d8550004fd72d8550014fc72d85502c6f651d85502c6f551d85502c67c51d8550006f721d8550006f421d8550024fd70d85501f6f710d8550006f7619855003df97098550005df7358550095dc7358550005ef725855008dec7258550055fb7058550006f5611855011e7f751855000cfd751855011e7d751855001cfe7318550004fd731855001cfc73185502be7f53185500067e53185500067d53185502be7c5318550014fe7218550004fd7218550014fc72185502be7f52185500067e52185500067d52185502be7c52185502be7f51185502bef651185502bef5511855011e7c5118550006f72118550006f42118550024fd701855011e7e501855011e7c501855011ef5101855000d7e769455014e7e769455000c7e76945500957e73945500057d73945500957c73945500067f639455015e7e639455015e7c639455008d7e72945500057d729455008d7c72945500067f62945501567e62945501567c62945500257e71945500277671945500067f61945500077761945500067c619455000774619455000674619455000d7e709455014f7a709455000779709455000d7c70945500267f60945500277b609455000d7c76545501367c765455000c7c76545500057f73545500957e73545500957c73545500057f725455008d7e725455008d7c72545500257f71545500277771545500077761545500067c61545500077461545500077b705455000d7e705455000d7c70545501377870545500267f60545500277b6054550004fe768c550004fd768c550004fc768c5500057f758c5500257e758c5500057d758c5500257c758c550006df638c55001edc638c550004ff764c550004fe764c550004fc764c5500057f754c5500257e754c5500057d754c5500257c754c550004fe7688550004fd7688550004fc76885500057f75885500257e75885500057d75885500257c7588550006ef6288550016ec6288550004ff7648550004fe7648550004fc76485500057f75485500257e75485500057d75485500257c754855008fe421485502e57e76d8d502b57e74d8d500057d74d8d502b57c74d8d500067e64d8d500067c64d8d500967e63d8d500975e63d8d500965e63d8d500967c63d8d500975e43d8d5008d7e72d8d500057d72d8d5008d7c72d8d500075e32d8d500975c32d8d500057e71d8d500057d71d8d500975c31d8d500257f70d8d5000d7e70d8d500257d70d8d5000d7c70d8d5029e7f60d8d502df7b60d8d5029f5f30d8d5029f5d30d8d502a57f7658d500057f7458d502b57e7458d502b57c7458d500067e6458d500067
  | 14 => 0x257e76887500d57d76887500257c76887500057f73887500a57e73887500057d73887500a57c738875009f6e62887500d76d628875009f6e32887500076d32887501c57e71887500067e618875009f6f218875009f77218875009f74218875000d7e70887500c57d708875000d7c70887500c76e20887500c76c20887500bd7f76487500067f76487500047f76487500257e76487500bd7d76487500257c76487500be7c76487500247c76487500057f73487500a57e73487500057d73487500a57c73487501dd7f71487500067e614875009f7721487500076e214875009f6c214875009f74214875009f6421487500ad7f704875000d7e704875000d7c70487500af6f204875001cfe76d8d500257e75d8d5000d7d75d8d50096de63d8d500975e53d8d5000cfd75d8d5029e7d75d8d5000c7d75d8d5001cfc75d8d50084fe74d8d50004fd74d8d50084fc74d8d500067e54d8d502de7c54d8d500967e53d8d50096de53d8d500965e53d8d502dedd53d8d500967c53d8d50096de43d8d50014fe72d8d50004fd72d8d50014fc72d8d502de7f52d8d50006de32d8d50096dc32d8d50004fe71d8d50004fd71d8d502de7c51d8d50096dc31d8d50024fd70d8d5029edf30d8d50096dc6358d502f5fb7058d5000d7c7654d5001e7c7654d5000c7c7654d500057f7454d502b57e7454d502b57c7454d501b67e6454d501b67c6454d500257f7354d500275f7354d500075f6354d5001e7e6354d5001e7c6354d500975c6354d5001e5c6354d500057f7254d5008d7e7254d5008d7c7254d500975f3254d500057f7154d500057c7154d500077b7054d5000d7e7054d5000d7c7054d501a7787054d500267f6054d500277b6054d50004ff7650d50004fe7650d50004fc7650d500057f7550d500257e7550d500057d7550d500257c7550d50006df6350d5001edc6350d5019f5f5350d500975c5350d500979c4350d50014fe76d89500257e75d895000d7d75d895008eee62d895008f6e52d895000cfd75d89502367d75d895000c7d75d8950014fc75d895001cfe73d8950004fd73d895001cfc73d89502ce7f53d89500067d53d895008e7e52d895008eee52d89502ceed52d895008e7c52d8950004fe71d8950004fd71d89502ce7c51d895008eec21d8950024fd70d8950236ef20d8950005df7358950095dc735895008eec6258950005f77158950005f471589502edfb705895000d7c76549500167c765495000c7c76549500057f73549500957e73549500957c73549500067f63549500257f72549500276f72549500076f62549500167e62549500167c625495008f6c62549500057f71549500057c71549500077b705495000d7e705495000d7c705495017f7870549500267f60549500277b6054950004ff764c950004fe764c950004fc764
  | 15 => 0xe60885210c6ec608852100cfe76d81210067f65d81210067c65d8121047e421d81210aefa60d81210067f75d8121024fe75d8121004fd75d8121024fc75d81210067c75d812101cfe73d8121004fd73d812101cfc73d812100cfc72d8121014fd71d81210067e51d81210067c51d81210aefa20d81210aefa10d81210057f75581210bd7c75581210067f65581210067c6558121005df73581210b5dc735812102fe421581210aef8605812119d7f7650f500257e7650f5019d7d7650f500257c7650f5027d7f7350f5019f5f6350f500a75c6350f500a73e4350f500a75c4350f500a71c4350f500057f7250f5009d7e7250f5009d7c7250f500a75f3250f500057f7150f500057c7150f500a75c3150f5018d7f7050f5000d7e7050f5000d7c7050f5018e7d6050f5018f5f3050f501757f764cb500067f764cb500047f764cb500257e764cb501757d764cb500257c764cb501767c764cb500247c764cb500057f744cb502fd7e744cb500057d744cb502fd7c744cb502157f734cb500a75e634cb501775d634cb500a75e434cb500075d434cb5020d7f724cb500a76f324cb5009f5e324cb5009f5c324cb5009f6c324cb500057f714cb500057c714cb500a75c314cb5009f6c214cb501657f704cb5000d7e704cb5000d7c704cb501667d604cb501675f304cb501676f204cb500067f73987500067e73987500067d73987500067c73987500067e43987500067d43987500067c43987500067f72987500067e72987500067d72987500067c72987500067f32987500067e32987500067d32987500067c32987500267e71987500267671987500067f31987500067c31987500067f21987500067c219875014e7f709875014e7d709875014e7f309875014e7e309875014e7d309875014e7c309875014e7f209875014e7e209875014e7d209875014e7c209875014e7e109875014e7d109875014e75109875014e7c10987501157f768c7500257e768c7501157d768c7500257c768c7500057f748c7502fd7e748c7500057d748c7502fd7c748c7500a75e638c7501175d638c7500a75e438c7500075d438c75009d7e728c7500057d728c75009d7c728c7500a75f328c7500075d328c7501d57e718c7500067e618c7500a75f318c7500a777318c7500a774318c75000d7e708c7500fd7d708c75000d7c708c7500ff5e308c7500ff5c308c7500f57f764c7500067f764c7500047f764c7500257e764c7500f57d764c7500257c764c7500f67c764c7500247c764c7500057f744c7502fd7e744c7500057d744c7502fd7c744c7500057f724c75009d7e724c75009d7c724c7501e57f714c7500067e614c7500a777314c7500075e314c7500a75c314c7500a774314c7500dd7f704c75000d7e704c75000d7c704c7500df5f304c7500d57f7688750
  | 16 => 0x95211557e76195210be7e76195211547e76195210067e63195210067c63195211267f62195211267f61195211277721195211276c21195211277421195211276421195210057d70195210067e60195210067c60195211276f201952101cfe76d8d210067f65d8d210067c65d8d210b6de63d8d21107e421d8d21024fe75d8d21004fd75d8d21024fc75d8d21084fe74d8d21004fd74d8d21084fc74d8d210b6de43d8d21104ff72d8d21104fd72d8d21106df32d8d21106dd32d8d21014fd71d8d210b6df31d8d21106ec21d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d210b6dc30d8d21106ef20d8d210057f7558d210bd7c7558d210067f6558d210067c6558d210b6dc6358d2130df77158d210e7e42158d21004ff7558d210067f7558d210047f7558d21024fe7558d21024fc7558d210067c7558d210247c7558d21004ff7458d21084fe7458d21084fc7458d21104ff7358d21006df7358d210e4ff7258d21006ef7258d2130cff7158d21006f77158d210b6dc3158d210e6ec2158d21004ff7058d2100cfe7058d2100cfc7058d210b6df3058d210e6ef2058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210267c6554d211afe42154d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210067f6550d2119e7c6550d21006df6350d2101edc6350d210b79c4350d21197e42150d21124fe76945211567f65945210267e65945210067d65945210267c6594521157e421945211257e76945210067e76945211247e76945210067f639452115e7e63945210067d639452115e7c63945211567f62945211257e71945211567f61945211577721945211576c21945211577421945211576421945210057d709452114e7e609452114e7c60945211576f2094521024ff7654521014fe765452113cfd7654521014fc76545210067f65545210267c6554521005ef7254521015ec725452113fe421545211557e76145210be7e76145211547e76145210067f631452112e7e63145210067d631452112e7c63145211267f62145211557e71145210bf7671145211267f61145211277721145211276c21145211277421145211276421145210057d701452111e7e601452111e7c60145211276f2014521304fe768c5210067f658c5211167c658c52101ede638c521006dd638c521107e4218c52101cff764c521014fe764c5210e4fd764c521014fc764c5210057f754c5210bd7c754c5210067f654c5210f67c654c521006df634c52101edc634c521005ef724c521015ec724c5210e7e4214c5210076f65885210076c6588521006ef6388521006ed6388521015ee7188521017e67188521015e67188521016ef6188521017e761885210076e51885210076c5188521005ed70885210c6e
  | 17 => 0xcfcf304ca21014ff7694621024fe7694621014fd76946210267e65946210067d6594621015ee7294621005ed72946211567f76946210267e76946210267d76946211567c76946210067f639462115e7e63946210067d639462115e7c63946211576e72946210076d72946211576e32946210076d32946211567e61946211576f21946211577721946211577421946210057d709462114e7e609462114e7c60946213276e20946211576c2094621314ff76546210267f76146210d67e76146211267d76146210267c76146210067f631462112e7e63146210067d631462112e7c63146211276e72146210d76d72146211276e32146210076d32146210d77671146211267e61146211276f21146211277721146211277421146210057d701462111e7e601462111e7c601462131f6e20146211276c2014621014ff768c62101cfe768c621014fd768c62101ede638c621006dd638c621015ee728c621005ed728c621007cd328c62130cff764c6210057f754c6210d57c754c621015ee724c6210c6fa60d822100cff7658221015ec72582210c6f860582210c7ea2058221004ff7558221024fe7558221024fc7558221004ff735822101cfe735822101cfc735822102eee3258221006ed3258221014fc71582210067e51582210067c515822102eef21582210c6ee20582210c6fa20582210c6ec20582210c6f81058221024fe76d95210be7e65d9521157e421d952101cfe73d9521004fd73d952101cfc73d95210be7f53d95210067e53d95210be7c53d9521154ff72d9521154fd72d95211567f52d95211567d52d9521014fd71d95210be7f51d952100cfe70d9521004fd70d952100cfc70d95210be7f50d95210067e50d95210be7c50d95211257e76d95210247e76d95210067e63d95210067c63d95211577721d95211576c21d95211577421d95211576421d95210057d70d95210067e60d95210067c60d95211576f20d95210067f73d95210067e73d95210067d73d95210067c73d95210067e43d95210067c43d95211567f72d95211567e72d95211567d72d95211567c72d95211567f32d95211567e32d95211567d32d95211567c32d95211567f71d95210be7e71d95211567d71d95210067f31d95210067c31d95211567f21d95211567e21d95211567c21d95210067f70d95210067e70d95210067d70d95210047d70d95210067c70d95210067f30d95210067e30d95210067c30d95211567f20d95211567e20d95211567d20d95211567c20d95210067e10d95210067c10d95210be7c6559521315f7715952113fe42159521154ff75595210067f7559521004ff735952101cfe735952101cfc735952113cff7259521006ef7259521314ff7159521006f771595210be7c5159521004ff705952100cfe705952100cfc70595210be7f505
  | 18 => 0xc73505310075f658c5310075c658c531006df648c531006dd648c531006df628c53101dde718c53101fd6718c53101edf618c53101fd7618c5310075e518c5310075c518c531005dd708c5310fede608c5310fedc608c53100cfe76d81310067f65d81310067c65d81310defa60d81310067f75d8131024fe75d8131004fd75d8131024fc75d81310067c75d8131084fe74d8131004fd74d8131084fc74d813100cfc73d8131014fe72d8131004fd72d8131014fc72d813101cfd71d81310067e51d81310067c51d81310defa30d81310defa10d81310057f75581310f57c75581310067f65581310067c6558131005bf74581310edbc7458131005ef72581310e5ec72581310def860581310d67e65d96210cdde73d9621005dd73d9621125f671d962113cfd75d962101cfe73d9621006de73d962101cde73d9621004fd73d9621006dd73d9621004dd73d962101cfc73d96210d67f53d9621006ed72d96211567e52d96211567c52d9621124fe71d9621006f671d962100cfe70d9621004fd70d962100cfc70d96210d67f50d9621024ff76596210d67c65596210067f7559621004ff735962101cfe735962101cfc73596210067e53596210d67c535962113e7f525962113e7d5259621014fc71596210d67c5159621004ff705962100cfe705962100cfc70596210d67f50596210d57e75d8e210057d75d8e2132dbe74d8e21005bd74d8e210cede63d8e21305f671d8e21024fe75d8e210067e75d8e210247e75d8e21004fd75d8e210067d75d8e210047d75d8e21024fc75d8e21084fe74d8e21006be74d8e21084be74d8e21004fd74d8e21006bd74d8e21004bd74d8e21084fc74d8e210e4fd73d8e210cede43d8e21006ed72d8e21304fe71d8e21006f671d8e2100cfe70d8e21004fd70d8e2100cfc70d8e2101cff7658e210cedc6358e21004ff7558e21024fe7558e21024fc7558e21004ff7458e21084fe7458e21084fc7458e21006df7358e21006df5358e210cedc5358e21006df4358e210cedc4358e210e6df3258e210e6dd3258e21014fc7158e210cedc3158e21004ff7058e2100cfe7058e2100cfc7058e210cedf3058e21004ff7654e21004fe7654e21004fd7654e21004fc7654e210067f6554e210267c6554e21004ff7650e21004fe7650e21004fd7650e21004fc7650e21006df6350e2101edc6350e210cf9c4350e21015ee7250e210cdef764ca2101eef764ca2101cef764ca210076f754ca210076c754ca21005ef744ca21005ed744ca21015ef734ca21017cf734ca2101eee634ca210cfce634ca21007cd634ca2101eec634ca210cfce534ca21007cd534ca210cfce434ca21007cd434ca21005ef714ca21007e7714ca21007e4714ca21016ee614ca21017e6614ca210cfcc314ca210c5ee704ca210c5ec704ca21
  | 19 => 0x9131374ff73d9131374fd73d9131376bf43d9131376bd43d9131014fe72d9131004fd72d9131014fc72d91310eebf42d913101cfd71d91310eebf41d9131376dc31d913100cfe70d9131004fd70d913100cfc70d9131006be40d91310eebc40d9131376df30d91310057f75591310f57c75591310067f65591310067c65591310eebc645913136df77159131004ff75591310067f75591310047f7559131024fe7559131024fc75591310067c75591310247c755913133cff7359131006df7359131004ff7259131014fe7259131014fc725913136cff7159131006f7715913133edc3159131004ff705913100cfe705913100cfc705913133edf3059131004ff7655131004fe7655131004fd7655131004fc76551310067f65551310267c6555131014fe76d89310067f65d89310067c65d89310e6ee62d8931024fe75d8931004fd75d8931024fc75d8931084fe74d8931004fd74d8931084fc74d89310e6ee42d89310e6ee32d89310ceed32d893101cfd71d89310cedc31d89310e6ef21d893100cfe70d8931004fd70d893100cfc70d89310cedf30d8931006ee20d89310e6ec20d89310057f75589310f57c75589310067f65589310067c65589310e6ec6258931365f77158931004ff7654931004fe7654931004fc76549310067f65549310267c6554931005df735493101ddc7354931005f77154931005f47154931004ff7650931004fe7650931004fc76509310057f75509310f57c75509310067f655093135e7c6550931006bf6450931086bc6450931005df735093101ddc7350931006ef6250931016ec6250931005f77150931005f4715093112cfe769453115e7f65945310267e65945310067d65945310267c65945310f777519453115fd4319453112d7e76945310067e769453112c7e76945310067f64945312567e64945310067d64945312567c649453115e7f63945310067f62945311567e62945311567c629453112d7e719453115e7f619453115f77319453115f5c319453115f74319453115f5431945310057d709453114e7e609453114e7c609453115f5f3094531024ff765453101cfe7654531144fd765453101cfc76545310067f65545310267c6554531005df735453101ddc7354531147d4315453115d7e76145310f67e761453115c7e76145310067f641453124e7e64145310067d641453124e7c641453112e7f63145310067f62145311267e62145311267c621453115d7e71145310f776711453112e7f611453112f77311453112f5c311453112f7431145313577721145313577421145310057d701453111e7e601453111e7c601453112f5f301453134cfe76905310067f65905313467c6590531086be649053101cfe765053133cfd765053101cfc76505310067f65505313367c6550531005df735053101dd
  | 20 => 0x12f77311463112f74311463138f77211463138f7421146310057d701463111e7e601463111e7c60146313875e301463112f5c3014631084fe769063101cfd769063101dde7390631005dd73906310079d43906310fefa60d823100cff765823101ddc73582310fef860582310ffda3058231004ff7558231024fe7558231024fc7558231004ff7458231084fe7458231084fc7458231036de4358231006dd4358231004ff7258231014fe7258231014fc7258231036df3258231006dd325823101cfc71582310067e51582310067c5158231036df31582310fede30582310fefa30582310fedc30582310fef81058231024fe76d95310f67e65d9531084fe74d9531004fd74d9531084fc74d95310f67f54d95310067e54d95310f67c54d953115cff73d953115cfd73d953115e7f53d953115e7d53d9531014fe72d9531004fd72d9531014fc72d95310f67f52d95310067e52d95310f67c52d953101cfd71d95310f67f51d953100cfe70d9531004fd70d953100cfc70d95310f67f50d95310067e50d95310f67c50d953112d7e76d95310247e76d95310067e64d95310067c64d95310067e62d95310067c62d953115f7731d953115f5c31d953115f7431d95310057d70d95310067e60d95310067c60d953115f5f30d95310067f74d95310067e74d95310067d74d95310067c74d953115e7f73d953115e7e73d953115e7d73d953115e7c73d953115e7f43d953115e7e43d953115e7d43d953115e7c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067c42d953115e7f32d953115e7e32d953115e7d32d953115e7c32d953115e7f71d95310f67e71d953115e7d71d95310067f41d95310067c41d953115e7f31d953115e7e31d953115e7c31d95310067f21d95310067c21d95310067f70d95310067e70d95310067d70d95310047d70d95310067c70d95310067f40d95310067e40d95310067c40d953115e7f30d953115e7e30d953115e7d30d953115e7c30d95310067f20d95310067e20d95310067c20d95310067e10d95310067c10d95310f67c655953137df7715953115cff75595310067f7559531004ff7459531084fe7459531084fc7459531144ff7359531006df7359531004ff7259531014fe7259531014fc725953137cff7159531006f771595310f67c5159531004ff705953100cfe705953100cfc70595310f67f505953115d7e76195310f67e761953115c7e76195310067e64195310067c641953112e7f63195310067e62195310067c621953112e7f611953112f77311953112f5c311953112f7431195310057d70195310067e60195310067c601953112f5f3019531084fe76d91310067f65d91310067c65d91310eebe64d9131024fe75d9131004fd75d9131024fc75d
  | 21 => 0xd4359231004ff7259231014fe7259231014fc7259231006be425923110ebc425923133edf325923101cfc715923110ebc4159231004ff705923100cfe705923100cfc705923110ebf4059231004ff7655231004fe7655231004fd7655231004fc76552310267e65552310067d6555231086be6455231006bd645523110ddf7650e31086df7650e31084df7650e3119ede6550e3119edc6550e3101ddf7450e3101f9f7450e31086de6450e3110f9e6450e310869e6450e310079d6450e31086dc6450e313a79f5450e3110f9c5450e31005df7250e3110f9f4250e31005df7150e31007d77150e31007d47150e3101ede6150e3101fd66150e3110f9c4150e310fdde7050e310fddc7050e3110f9f4050e311157e75d8a310057d75d8a3110dbe74d8a31005bd74d8a31106ee62d8a3139df671d8a31014ff7658a31106ec6258a31004ff7558a31024fe7558a31024fc7558a31004ff7458a31084fe7458a31084fc7458a310b6de4358a31006dd4358a31106ee3258a310b6ed3258a3101cfc7158a31106ec2158a31004ff7058a3100cfe7058a3100cfc7058a31106ef2058a31004ff7654a31004fd7654a31004fc7654a310067f6554a310267c6554a31005f77154a31005f47154a31004ff7650a31004fd7650a31004fc7650a310057f7550a311157c7550a31086bc6450a3101dde7350a310079d4350a31005f77150a31005f47150a31105df764ca31016df764ca31014df764ca310075f754ca310075c754ca31006df654ca31006dd654ca31005df744ca31005dd744ca31006df644ca31006dd644ca3101ddf724ca3101fcf724ca31016de624ca31107ce624ca31007cd624ca31016dc624ca31005df714ca31007d7714ca31007d4714ca3101ede614ca3101fd6614ca31107cc214ca310fdde704ca310fddc704ca31107cf204ca3101cff7694631024fe769463101cfd76946310267e65946310067d659463101dde7394631005dd739463111777519463115fd7319463115e7f76946310267e76946310267d769463115e7c76946310067f64946312567e64946310067d64946312567c649463115f5e73946310075d739463115f5e43946310075d43946311567e62946310067d62946311567c629463115f5f32946310075d329463115e7e619463115f5f319463115f77319463115f57319463115f7431946310057d709463114e7e609463114e7c60946313975e309463115f5c309463137cff7654631147d731546310267f76146311167e761463112e7d76146310267c76146310067f641463124e7e64146310067d641463124e7c641463112f5e73146311175d731463112f5e43146310075d43146311267e62146310067d62146311267c621463112f5f32146310075d321463111776711463112e7e611463112f5f3114631
  | 22 => 0xc5112d7f7350c5119f5f6350c5112f5c6350c5112f3e4350c5112f5c4350c5112f1c4350c510057f7250c511257e7250c511257c7250c5112f5f3250c510057f7150c510057c7150c5119f766150c5112f5c3150c510057f7050c5111d7e7050c5111d7c7050c5112f5f3050c511757f764c8510067f764c8510047f764c8510257e764c8511757d764c8510257c764c8511767c764c8510247c764c8510057f744c85124d7e744c8510057d744c85124d7c744c8511257f734c85112f5e634c8511775d634c85112f5e434c8510075d434c8511257f724c85112f6f324c8511275e324c8511275c324c8511276c324c8510057f714c8510057c714c85117776614c85112f5c314c8511276c214c8510057f704c85111d7e704c85111d7c704c85112f5f304c8511276f204c85115e7e739845115e7d739845115e7e439845115e7d439845115e7c43984511567e72984511567d72984511567f32984511567e32984511567d32984511567c32984510267e719845102676719845114e7e709845114e7d709845114e7c309845114e7c20984510067f73580510067e73580510067d73580510067c73580510067e43580510067d43580510067c43580510067f72580510067e72580510067d72580510067c72580510067f32580510067e32580510067d32580510067c32580510067e71580510067f31580510067c31580510067f21580510067c21580510267f70580510267b705805111e7f305805111e7e305805111e7c305805111e7f205805111e7e205805111e7a205805111e7c205805111e7e105805111e7c105805111e7810580511167e65d963112df671d9631144fd75d9631084fe74d9631004fd74d9631084fc74d96310067e54d96311167c54d9631006dd73d963115e7e53d963115e7c53d9631014fe72d9631004fd72d9631014fc72d96311167f52d963115edf32d963112cfe71d9631006f671d963100cfe70d9631004fd70d963100cfc70d96311167f50d9631024ff76596311167c65596310067f7559631004ff7459631084fe7459631084fc74596311167f54596311467f53596311467d5359631004ff7259631014fe7259631014fc72596310067e52596311167c5259631146df325963101cfc71596311167c5159631004ff705963100cfe705963100cfc70596311167f505963110ebe64d923134df671d9231024fe75d9231004fd75d9231024fc75d9231014fe72d9231004fd72d9231014fc72d9231376df32d923134cfe71d9231006f671d923100cfe70d9231004fd70d923100cfc70d9231084ff76592310057f75592311157c755923110ebc6459231004ff75592310067f75592310047f7559231024fe7559231024fc75592310067c75592310247c7559231006bf745923110ebe545923133ebf435923133eb
  | 23 => 0x14d7e704ca5114d7c704ca5115f5f304ca511576f204ca5115d7e73d82510057d73d825115d7c73d82510067f63d82510067e63d82510067d63d82510067c63d82511557e72d82510057d72d82511557c72d82510067f62d82510067e62d82510067d62d82510067c62d82510077671d82510577661d825114e7e60d825114f7a60d825114e7c60d82510057f735825115d7e735825115d7c73582510067f63582510067e63582510067d63582510067c63582510057f72582511557e72582511557c72582510067f62582510067e62582510067d62582510067c62582510257c715825103e7e615825103f7661582510077b605825114e7e605825114e7c605825114f78605825114f7810582510067f73582510067e73582510067d73582510067c73582510067e43582510067d43582510067c43582510067f72582510067e72582510067d72582510067c72582510067f32582510067e32582510067d32582510067c325825103e7e71582510247c71582510067f31582510067c31582510067f21582510067c215825114e7f305825114e7e305825114e7c305825114e7f205825114e7e205825114e7c205825114e7e105825114e7c105825114e78105825101cfe76d8d51146de63d8d51084fe74d8d51004fd74d8d51084fc74d8d51146de53d8d51116dd53d8d51146de43d8d51014fe72d8d51004fd72d8d51014fc72d8d51146df32d8d51024fd71d8d511167c51d8d51146df31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d511167f50d8d51006de30d8d51146dc30d8d51146dc6358d513b5f77158d51004ff7650d51004fe7650d51004fc7650d51006df6350d5101edc6350d511479c4350d51014fe76d895113eee62d895101cfe73d8951004fd73d895101cfc73d895113eee52d89510d6ed52d895113eee32d8951024fd71d89510d67c51d895113eef21d895100cfe70d8951004fd70d895100cfc70d89510d67f50d8951006ee20d895113eec20d895113eec62589513adf77158951004ff764c951004fe764c951004fc764c9510057f754c9510257c754c951006df634c95101edc634c951006ef624c951016ec624c9510067f639455115e7e639455115e7c63945510067f62945511567e62945511567c62945510257e71945510277671945510267f61945510277761945510057d709455114e7e609455114e7c609455100cfe76d8151136fa60d81510067f75d815100cfc75d815100c7c75d815101cfe73d8151004fd73d815101cfc73d8151014fe72d8151004fd72d8151014fc72d8151024fd71d81510067e51d81510567c51d81511367f50d8151136fa50d8151136fa10d8151005df7358151145dc7358151005ef725815113dec7258151136f8605815119d7f7650c510257e7650c5119d7d7650c510257c765
  | 24 => 0x77154a51007747154a510267e6154a51027766154a510057f7054a5114d7e7054a5114d7c7054a51004ff764ca51004fd764ca51004fc764ca510057f754ca510257e754ca510057d754ca510257c754ca5101edc634ca5115f5e534ca510075d534ca5114efa60d825100cff76582510257c755825114ef8605825114f7a50582510067d7558251004ff735825101cfe735825101cfc735825103e7f53582510067e53582510067d535825103e7c5358251004ff7258251014fe7258251014fc725825103e7f52582510067e52582510067d525825103e7c5258251024fc715825103e7f515825114e7f505825114e7e505825114efa505825114e7c505825114ef810582512557e74d8e510057d74d8e512557c74d8e510067e64d8e510067c64d8e5115e7e63d8e5115f5e63d8e5115e5e63d8e5115e7c63d8e511557e72d8e510057d72d8e511557c72d8e5115f5f32d8e510057e71d8e510077671d8e510057671d8e511177661d8e5114d7e70d8e510057d70d8e5114d7c70d8e510057f7458e512557e7458e512557c7458e510067e6458e510067c6458e510075f6358e5115e7e6358e5115e7c6358e5115f5c6358e5115e5c6358e5115f5e4358e510057f7258e511557e7258e511557c7258e510075e3258e5115f5c3258e510257c7158e510f67e6158e510f7766158e5115f5c3158e510057f7058e5114d7e7058e5114d7c7058e5115f5f3058e510057f7650e510057e7650e510057d7650e510057c7650e5115f5e6350e510075d6350e5115f3e4350e5115f5c4350e5115f1c4350e510057f7250e511557e7250e511557c7250e5115f5f3250e510057f7150e510057c7150e5112e7e6150e5115f5c3150e510057f7050e5114d7e7050e5114d7c7050e5115f5f3050e5115d7e73d8a510075e73d8a5115d5e73d8a510057d73d8a510075d73d8a510055d73d8a5115d7c73d8a510067f63d8a510067d63d8a511567e62d8a511576e62d8a511567c62d8a510057e71d8a510077671d8a510057671d8a510d77661d8a5114d7e70d8a510057d70d8a5114d7c70d8a510057f7358a5115d7e7358a5115d7c7358a510067f6358a510067d6358a510076f6258a511567e6258a511567c6258a511576c6258a510257c7158a510be7e6158a510bf766158a511576c2158a510057f7058a5114d7e7058a5114d7c7058a511576f2058a510057f764ca510067f764ca510047f764ca510057e764ca510057d764ca510057c764ca510067c764ca510047c764ca510057f744ca512557e744ca510057d744ca512557c744ca510075f634ca5115f5c634ca5115f5e434ca510075d434ca5115f6f324ca511575e324ca511575c324ca511576c324ca510057f714ca510057c714ca511267e614ca5115f5c314ca511576c214ca510057f704ca51
  | 25 => 0x8532006f410d85321757e75985320057d75985320067f65985320067c659853216dbe7498532005bd7498532006f761985320057f75585321757c75585320067f65585320067c65585320067f65185320067c6518532006f561185320067f7518532024fe7518532004fd7518532024fc75185320067c7518532084fe7418532004fd7418532084fc7418532014fd731853239ede4318532006dd431853201cfd721853239ef53118532306f5211853200cfe7018532004fd701853200cfc7018532006f61018532006f4101853200cfe76d81320067f65d81320067c65d8132166fa60d81320067f75d8132024fe75d8132004fd75d8132024fc75d81320067c75d8132084fe74d8132004fd74d8132084fc74d8132014fd73d813225ede43d8132006dd43d813201cfd72d8132004fe71d8132004fd71d8132166fa30d8132166fa20d81320057f75581321757c75581320067f65581320067c6558132005bf745813216dbc7458132005f77158132005f47158132166f8605813215ede63d8e513c5f671d8e5101cff7658e510257c7558e5115edc6358e5115f5e5358e51004ff7458e51084fe7458e51084fc7458e510067e5458e510f67c5458e5115e7e5358e5115ede5358e5115e5e5358e510f6dd5358e5115e7c5358e5115ede4358e51004ff7258e51014fe7258e51014fc7258e510f67f5258e51006de3258e5115edc3258e51024fc7158e5115edc3158e51004ff7058e5100cfe7058e5100cfc7058e510f67f5058e5115edf3058e5115d7f7654e5101e7f7654e5101c7f7654e510057f7454e512557e7454e512557c7454e511b67e6454e511b67c6454e510257f7354e510275f7354e5101e7e6354e5115f5e6354e5101e5e6354e510075d6354e5101e7c6354e510057f7254e511557e7254e511557c7254e5115f5f3254e510057f7154e51007777154e51007747154e510267e6154e51027766154e510057f7054e5114d7e7054e5114d7c7054e51004ff7650e51004fd7650e51004fc7650e510057f7550e510257e7550e510057d7550e510257c7550e5101ede6350e51006dd6350e5119f5f5350e5115f5c5350e5115f9c4350e5115dde73d8a51005dd73d8a51156ee62d8a513bdf671d8a51014ff7658a510257c7558a51156ec6258a511576e5258a51004ff7358a5101cfe7358a5101cfc7358a510be7f5358a510067d5358a511567e5258a51156ee5258a510beed5258a511567c5258a51024fc7158a51156ec2158a51004ff7058a5100cfe7058a5100cfc7058a510be7f5058a51156ef2058a511557f7654a510167f7654a510147f7654a510057f7354a5115d7e7354a5115d7c7354a510067d6354a510257f7254a510276f7254a510167e6254a511576e6254a510076d6254a510167c6254a510057f7154a510077
  | 26 => 0x40e7f63195324175e431953240e7f62195324176f321953240f5e321953240f5c321953240f6c32195320057e71195324175c311953240f6c21195320057d70195320067e60195320067c60195324175f301953240f6f2019532084fe76d91320067f65d91320067c65d913216ebe64d9132024fe75d9132004fd75d9132024fc75d9132194fd74d9132014ff73d9132014fd73d9132406bf43d9132406bd43d913201cfd72d91323febf42d9132004fe71d9132004fd71d913216ebf41d9132406dc31d91323feec21d913200cfe70d9132004fd70d913200cfc70d9132006be40d913216ebc40d9132406df30d91323feef20d9132084ff76591320057f75591321757c75591320067f65591320067c655913216ebc64591323eddf73591323f5ef7259132004ff75591320067f75591320047f7559132024fe7559132024fc75591320067c75591320247c75591323ecff7359132006df7359132194ff7259132006ef7259132004ff7159132004fc71591323e6dc3159132196ec2159132004ff705913200cfe705913200cfc70591323e6df3059132196ef2059132004ff7655132004fe7655132004fd7655132004fc76551320067f65551320267c655513201dde73551323df5e5355132015dc7654d32026dc7654d32014dc7654d3201ddf7554d3201f5f7554d320075f6554d32026de6554d32026dc6554d321775c6554d32005df7454d323d75e5454d321775c5454d32007cf7254d32015de7254d32015dc7254d321afcc7254d3201edf6254d3201fcf6254d321af5f5254d321af5d5254d32005dc7154d321775c5154d321afcc2154d32005df7054d321775f5054d321afcf2054d32015dc7650d32086dc7650d32014dc7650d32005df7550d32005dd7550d320075f6550d3219ede6550d3219edc6550d320075c6550d3219e5c6550d3201ddf7450d3201f9f7450d320079f6450d32086de6450d32086dc6450d3216f9c6450d320869c6450d323cf9f5450d3216f9c5450d32007cf7250d32015de7250d32015dc7250d32197cc7250d32015cc7250d3201edf6250d3201fcf6250d321979f4250d321979d4250d32005dc7150d3216f9c4150d32197cc2150d32005df7050d3216f9f4050d32197cf2050d321757e75d85320057d75d85320067f65d85320067c65d853216dbe74d8532005bd74d8532024fe75d85320067e75d85320247e75d8532004fd75d85320067d75d85320047d75d8532024fc75d8532084fe74d8532006be74d8532084be74d8532004fd74d8532006bd74d8532004bd74d8532084fc74d8532014fd73d853230edd73d853201cfd72d8532366ed72d8532366f631d8532366dc31d853230ef621d853230eec21d853200cfe70d8532004fd70d853200cfc70d8532366df30d853230eef20d8532006f610d
  | 27 => 0xf7518552014fd751855201cfe7318552004fd731855201cfc73185523be7f53185520067d5318552024fd72185521267e52185521267c52185523bef551185521267c5118552126f5211855200cfe7018552004fd701855200cfc70185523be7f5018552006f61018552006f4101855200cfe76d815217efa60d815209e7f75d8152014fd75d815201cfe73d8152004fd73d815201cfc73d81522ee7f53d81520067d53d8152024fd72d815209e7e52d815209e7c52d8152004fe71d8152004fd71d81522ee7c51d815217e7f50d815217efa50d815217efa20d8152005df7358152185dc7358152005f77158152005f4715815217ef86058152024fe76d95321767e65d95321acfd75d9532084fe74d9532004fd74d9532084fc74d95321767f54d95320067e54d95321767c54d9532014ff73d9532014fd73d95324367f53d95324367d53d953201cff72d953201cfd72d953241e7f52d953241e7d52d9532004fe71d9532004fd71d95321767f51d95321767c51d953200cfe70d9532004fd70d953200cfc70d95321767f50d95320067e50d95321767c50d953240d7e76d95320247e76d95320067e64d95320067c64d953241f5f73d953241f5c73d95324375e43d95324376f32d953241f5e32d953241f5c32d953241f6c32d95320057e71d95324375c31d953241f6c21d95320057d70d95320067e60d95320067c60d95324375f30d953241f6f20d95320067f74d95320067e74d95320067d74d95320067c74d953241e7f73d95324367e73d953241e7d73d953241e7c73d95324367f43d95324367e43d95324367d43d95324367c43d953241e7f72d953241e7e72d953241e7d72d953241e7c72d953241e7f42d953241e7e42d953241e7d42d953241e7c42d953241e7f32d953241e7e32d953241e7c32d95320067f71d95320067e71d95320047e71d95320067d71d95320067c71d95320067f41d95320067c41d95324367f31d95324367e31d95324367d31d95324367c31d953241e7f21d953241e7e21d953241e7d21d953241e7c21d95320067f70d95320067e70d95320067d70d95320047d70d95320067c70d95320067f40d95320067e40d95320067c40d95324367f30d95324367e30d95324367d30d95324367c30d953241e7f20d953241e7e20d953241e7d20d953241e7c20d95320067e10d95320067c10d9532024ff76595321767c6559532425df735953242def725953241cff75595320067f7559532004ff7459532084fe7459532084fc7459532424ff7359532006df73595321acff7259532006ef7259532004ff7159532004fc71595321767c5159532004ff705953200cfe705953200cfc70595321767f505953241d7e76195321767e761953241c7e76195320067e64195320067c64195324175e731953240f5d7319532
  | 28 => 0x9543006df735954319edf53595433de7e53595433de7c53595433dedc5359543004ff7259543014fe7259543014fc725954319e7f52595433dedf3259543004ff7159543004fc715954319e7c5159543004ff705954300cfe705954300cfc705954319e7f5059543014fe76d89433f79c43d8943196ee62d8943024fe75d8943004fd75d8943024fc75d8943084fd73d8943196ee32d8943004fe71d8943004fd71d89433f6dc31d894300cfe70d8943004fd70d894300cfc70d89433f6df30d89430057f755894319d7c75589433e79c4358943196ec625894319d7e75d85430057d75d854336f9c43d8543195ee72d8543005ed72d8543024fe75d85430067e75d85430247e75d8543004fd75d85430067d75d85430047d75d8543024fc75d8543084fd73d854344edd73d8543014fe72d8543006ee72d8543014ee72d8543004fd72d8543006ed72d8543004ed72d8543014fc72d854336ef631d854336edc31d854300cfe70d8543004fd70d854300cfc70d854336edf30d85433779c4398543006f761985430057f755854319d7c755854333f9c435854334f9c4318543006f56118543024fe7518543004fd7518543024fc7518543084fd7318543014fe7218543004fd7218543014fc721854334edf321854334ef5311854300cfe7018543004fd701854300cfc701854300cfe76d81432879c43d814318efa60d8143024fe75d8143004fd75d8143024fc75d8143084fd73d8143014fe72d8143004fd72d8143014fc72d8143286df32d8143004fe71d8143004fd71d814318efa30d81432779c435814318ef8605814301cfe76d8d52186de63d8d52014fd75d8d52084fe74d8d52004fd74d8d52084fc74d8d52186de53d8d52446dd53d8d52186de43d8d52024fd72d8d52426df32d8d52004fe71d8d52004fd71d8d524467c51d8d52186df31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d524467f50d8d52006de30d8d52186dc30d8d52186dc6358d5243def7258d520157c7654d5201e7c7654d520147c7654d520057f7454d521b67e6454d521b67c6454d520257f7354d520275f7354d520075f6354d5201e7e6354d5201e7c6354d521875c6354d520076f7254d520157e7254d520157c7254d521af6c7254d520267f6254d520276f6254d521af5f3254d520057c7154d520057f7054d52004ff7650d52004fe7650d52004fc7650d520257e7550d520057d7550d52006df6350d5201edc6350d5219f5f5350d521879c4350d52014fd75d85523167d75d855201cfe73d8552004fd73d855201cfc73d8552024fd72d85523aef651d85523ae7c51d8552316f621d855200cfe70d8552004fd70d855200cfc70d85523ae7f50d8552006f610d8552006f410d8552185de7398552005dd7398552006f76198552006f561185521267
  | 29 => 0x1100281b4042006000801000c001004803c0080010000000010000000000000400200c0000000003002000000000400980400000030008000000000003000000c000000801401a00000080740000290020004008009003800002600a0018010056000000000000000200080c00240040050014000000084fe76d91530257e75d915301d7d75d91531b6be64d91531b73e54d915301cfd75d915347e7d75d915301c7d75d91531b67e54d91531b6be54d91531b63e54d91531b67c54d9153024fd73d9153476df53d915347e7e53d915347e7c53d915347edc53d915347ebf43d9153014fe72d9153004fd72d9153014fc72d91534767f52d915347edf32d9153004fe71d9153004fd71d91534767c51d915300cfe70d9153004fd70d915300cfc70d91534767f50d91531b6bc64591531b73c545915346ddf7359153014fe76d89531aeee62d895301cfd75d8953084fe74d8953004fd74d8953084fc74d8953024fd73d89531aeee52d89531aeee32d8953004fe71d8953004fd71d895343e7c51d895300cfe70d8953004fd70d895300cfc70d895343e7f50d89531aeec625895301cfd75d855337e7d75d8553084fe74d8553004fd74d8553084fc74d8553024fd73d8553014fe72d8553004fd72d8553014fc72d85533b6f651d85533b67c51d855337ef631d855300cfe70d8553004fd70d855300cfc70d85533b67f50d8553006f76198553006f5611855312e7f751855301cfd7518553084fe7418553004fd7418553084fc74185530067e54185533c67c5418553024fd731855312e7e531855312e7c5318553014fe7218553004fd7218553014fc72185533c67f521855312edf32185533c6f5511855312e7c511855312ef5311855300cfe7018553004fd701855300cfc70185533c67f501855300cfe76d81531a6fa60d81530a67f75d815301cfd75d8153084fe74d8153004fd74d8153084fc74d81530067e54d81532f67c54d8153024fd73d81530a67e53d81530a67c53d8153014fe72d8153004fd72d8153014fc72d81532f67f52d81530a6df32d8153004fe71d8153004fd71d81532f67c51d81531a67f50d81531a6fa50d81531a6fa30d81531a6f86058153024fe76d954319e7e65d954301dde73d9543085dd73d954319f5f53d95434579c43d95433dcfd75d9543084ff73d9543084fd73d9543466dd73d9543084dd73d95434567f53d954319edf53d954319e5f53d95434567d53d9543456dc53d9543014fe72d9543004fd72d9543014fc72d95430067e52d954319e7c52d9543456df32d9543004fe71d9543004fd71d954319e7c51d954300cfe70d9543004fd70d954300cfc70d954319e7f50d9543024ff765954319e7c655954345ddf73595433df5c53595433df9c4359543454ff75595430067f75595433dcff735
  | 30 => 0x1a80340000010028020004000001800c01404b000000800004500f000000200b002000803c002004803c01200800d00880000090030088002006001000000c000001000008e0020028038026007000000800600500080000020050000020000000001000c002002006800400a005001803c01002101c8000000000002800c01600400180440060000088010038003017004c0060030058004034016000801001603b003000c028003000800800e010008003000200004a000000a02900a800003e00b000000004800401d800000001a004000000e000000011401002600c000400200c0008008012003000000400000300f001c004002004000000a010003000807e0010038004024002000800000c007002005800e0020028008004001001006001000100100000560020038000074004004801c000000003800400204801c800801a0050000044004004005800c01600a000000401600100d001801000200100000540270008010006000000002000200d0018014006011006807c034015000800000600000080000000010150004028002000001800a00200080000040010000024010008000803000400000400140020110000000000000001007800a00e0000000026004003005800e02b000007400a002005001001a0060260004004004013808800a0120028004000005003000800a008002800000001500380080040010000000004008000000400a00200e8000000016000007400400400480c800600200980000be00000c0000004017009800000600700b801000201500780d001000001580200020060000038000003000807400a015009000000a001002801807c026003800c000007010007001e00b0040058004017000803001003500800040040040000008006001000004c000000000800c00c010000000c002005004000800c0010010000006000010801400800d009800c0140080018038010005007000c00001d002000401c00000f8000016003000000c00a003000002c01a00001c800c0000000008000040002000006000600100700180000010000008000000001000401c00000180280160040010228000006002801c00001d0090000000019005002c006000000000000a008003000403a00b003803400e003000000000c0130100014000003000002c002013000800801c012004001800000f0048000000003011811c00000e0030078010001000802000201a000002c0060000020018000000000000400002b00500080020170120078000002002800c00203200a000000a00100a00100000000008050012017005800800800e00e0004004000003001401e0070018000008000001003800c00c0110018000004000001003202a00080000000100040010000009005003800004e000000803a000003002000c0030008008
  | 31 => 0x80020020050010012010002800800000100b001c000005010004c00400400000140000030010008054001000800000a00600000e00080020000008000001000007c00a0020010064004020007012c00200d001800400001400000100000190008014022001002001003200f005800c00400100600000060000018028004001007006c00400104d8014002007003000000a000000000400802300000140500060020014002013001800000000000400240520300050014030001000800000c0060020108010003000000400000c003000400801600180040000140020020008000000003003e0270038018002005007802001201e000800401c0050000024036000001003000400300c00b0000011004000000000a0030010054000019003004400000d0028002003002005007e001001802400001000380340000020070008000002000000c01e0000010004014002028800001000d017000805c006002000804e01100c800000e000002001400e000005000401e001002802c002000000026c00e026009001800c002003802c02e015000002c00000100e0008002000000001c00a000004002801a056005800400a001001000000401502100c003e000004000800c0010000020000004002803000000400500080440020050048002000006800000e0020050038000004000803c00401f00400280500010060000010006000000800e03d0068030006013001000401000e00180d000a00000080000000000040040004005001001c00002d004800000200a007000c01200c0000010000003028801c00a003001801400000c002800800800100100680a404c0000044000002003002800803600f8014002001004000001600200480640120070010000004008006000c05e01900600100180050020000002002000800400200001a8020004069001000802201200000140060020008000004024001000c008001002809c010008000001005000100a00480060010088010000007000002c002028000800000e02b00000a001801a0040088000002002808800000100e800002e000000801000000000b005400c0310008090010002000000c06a001000001001802200180440680070038068020005004004c00400000d8000000000000000000200800200000020000040000016003000002800000200380000000090010000040003000002800200c00080480000030000054000001000011c002005018003c03c0020040008008004000800000401a01000c00300000128004002072000003400601e002800801e05600100080080000018010002006000000002a00000100540000060038010000000002003c0d0009009000c02000b00c0000002000001800400403b011805c01c003001004c002002005001c00800100000080000170000000010002
  | 32 => 0x7000802000400c005000400000500d8078000000000000800a00e000802402a015005801000000400100240000000038004000005000802402800200080bc008005008807800000201e8010012005001800401000d001800801800200880000000000048078004001001001800201a00580100d2000001002000c009004806800a00200a000402c0a400180ac00c0290008000006007001800800c00000f800c0000000000008006008004802800601a01180a0070003000001800c00600180040000000118000004003000000400401b0020034004003002800001400000080700040130058054042004002800000200c000002c002000005000400203c001001000a00c00380040140020338004006014021802400600201f800801200300b802000e002000801c00600b0018000012004007801c01200300e003c01600100b007c0100130018008084007003000004a015002000802800100100000040000000004002000001002c00200003880080000090000018098029004000800c00a00100d800200504680680100020010050004029015005800000300680300020020000030034003008804c032000004000405400301c80d0002001002800001001700900480040030008004052003002001400609300700480020470038014012002004001800a00b001000c006002000003c008000002802c000000001000001a0060028008010002000006000200500980100000000020008006005008800002000000000000100010008014002002000000003c014001800400e005004002406c0010028018032002003000000400b003000000004a001000006c00d003000003403f000005801800400000100080010058000004003002000000400b000000001801e0000038028004000000c0180000038024014004001808c02200500000040020010008010008004000800400a000000000000000a004805c0180240000000004000002800001a00300c0000008009002800804a00000100000000010040078016000001003800000b000003c0400260008010002009000000c01400300b80580ae000011000000e000002003000c003002802c02600000280040ae0190050034056000000800800a047018803400c00f007000400000c00000a0054000006004400c02000c800c04a016002005800e0000000014004000000001400c00000000000060000000030006000000000005e002000801c008004000000400002e0058060030000039801c000004003000803c02700a000004600902b8024064021001001c0060000000000032002002000400a01e000803c002003000001400000b00d800401a00a001000000e0000098010014000001000c00a0020030000000007002002000000b000800000000e00400040000050048030064004005806
  | 33 => 0xd3e23a0e3b34c4c7244f287b11cd0be118a45c080e0e72466017604226a517b00001d949ac2c2893708640000000e6429641c0000000000000000000f4600010933c1200000000000e580003670ff71ddaba791fa99a0fb13b44c6c9890ea288443e0494294470043687b031f828317ea9493d30000379c8243d8000834ac0000000a16397452803a89ca4cbc0002bf80002cad03900000003d080003b1400034f8834a046c813f0512c1e98eca26c82549cd4e0317d8155a0b46db0000d222f281e6000036200000002a98fa34f980000000dbe3fb403a4c18e880000000076e4803788ec100000001e24b2c0aba9312cbc000000080e147915000000000000000000072d26b441309480004620eee4328fd0b8980000a705dd01a00000000000000000031810f200008c20000282352c65a000037d80005ac34b4b1f00000000000b3b000000021e40000e2c0000fe20000000000000000021a6ef9bcdd0dd432c81b1d2c00000000004f811673894ff905766c81d302900000fd3419cb230000b6c8a1818802702c50cc0bec86900002e212bb00000001f560000000000386c00032501e39594000278a0000000a9e9e1c447ba16cb11f10b1100000d00000752000000005a80003c460004dbc9c6000108e42587e2151c0000000fe43c448913334c653f16cda0334175bc6000000000004aa4ab402e0ba2800000000003db00702760000f3a0f847c7bf4000000007c5000054300010f328cc67f000079b1eb8109000000000000000000c2811eaa20000133a00000000000000000031d00000002800a2b00008a5000138810f00003da85701919243000000024b4dda3fdb0b9000086b80006c792e4d962980dc3029cab22594a0846e08e50000c6b0000133014e0000a9232c19208da0000754415c0004f480004c70e5b4580e7d144897c403488202d0b7202b67513980616036412ece84cd71368d9000009d324cc36599e012f3a24f35022c4393d4a52429893cc3ca8b6a258487044652c1c91434c412cfe38220cb626dcf68bdfc40d295c50697dc7f535d93b506232a73804d6e378066c34ec16d1c223e51f707b62de85df3dd0e3909e4e8788e8139091077e8cb8627388c460261cfbba5e4e6a2a2237cb096d02009e7bca2c438229f0fd19ebc42f115cf4d2ee531601088de3ab8c6119b4043279005c15d84cd0a6403c2a044791974536066c0cf880cc804ebc8471f8093a1ae4e2f2b0cee2059c3b20de1156289123c42c447f039c17a82f0a5484c8ab01f42e3705e2ae50d6027b2ba07db3190ae231c090d4c988f44cac031318b1294236ef72d1c1b82e92a97111476b2dd820700881be4e5c0ad1ce4cf64f0c02c0d946f7829a00c01e000c00a003000003c0000080000018002000000800800000e001005c0ec004000804400002
  | 34 => 0xf1bf8d9f3a527b4392cab604a019f3a2a548b1b00cb84f08281abd22c1a5529733f107439e8000000000031dc000089021a3d5203b199c0000000d1116b4da2000000000000001d3c174c9bcc00214ab60ba60e3c1ba066b258cf714d30833c44027ab8969f80000b858b652e1483105119048f93e20ae30eb82700000000000037b1bca8fd35082c2bc36f514c5ab869f545e128b5043406c25891722ac0000000000002b0000478185c0003e280002fc4c71c8e0ff80ba8e791eb41b007f000023e000017a85c801e8ae700002cb009d25d081109100002ad30544cb42d4a803028b4e33f83662f9ce3e1b082afa20c9302a34ce2004d03a112015e0000bbc0000000172c41f2a4480f0000f8d02e8906417c0004b900003d1f20000000003a7400005f2f0e92693811894cc00e28ebe1804ca23e8472c3604c9226442e63de0ddb0a952c22fb8f2424f44c631302fbb96a0000930b4d00000004f6c75f18c918a0e1c019187c42485a000009b8000000000024ba00010545ef254456741a4000000000000003c40000000000014615d065e3d847b713902281b2cfdc154015a14620f7cd42d0701f06bd34b85a700000003038af62920e2206e800010be4ea20327f22788001121cf7745a40c906606ae0040a1b4784ccc288a8d435902472d980003aac0000000000000013f000042104a20818000c7cccd60004418441224703e00007d2c5680003f3b3323bcc2d2aa020000d0a8ad00000000d200fb097d2d600000000000000435c95f0b20ebb000000003b888602440000000246007cf108000000000000000000000000d6300000000000000000000000005104bac00019580003c78e340b2aaf23f9a00048ccb333e4c9d43afb0350ae600009c45198000d4a06f0bb6427400038ad2b020846f327003bf3f94b5000000000000a7731b4000353930c4e3d39d1e7ca1148c86e62de0ad9a6051f300bcbc0224e6224790409263c9f7055111b04953760e80a472d040f831a016c1098da439705532bbc8bd2121098329b0371e2000021b6f0132a00ec00013a00000a222e4aa8e4dd0e938b3d04bba08e5600000004a780002a271fd46a800037c083000004500000074960128a28240b542ac8331a9903f227c44b000035200000004c5d00c00000004c6e7f8a44e0000b9cbc813060002e648c837fc0001c54ec900000003924d863b16f0824ed12524d8c201564604340710f04d80890278418221506b000035033e460dbcac0000af400039181a32a72cbd0b6800049413538000fb6000114d0000b224aa00003a12ca5000079e1d209c40326b052a18370168c00045287ed078c00046d510a3ea80004bd72101c791d6027400031d8b7db858000355117f127a2922c191243228078a860f2d491c251898920529f66a10122000135600046a
  | 35 => 0x20dfc3f482bf1ab0186161534328e117c9d9905230b436e489c76e2edd0b631e0edf08bc716148c54f25d1038bdb521814d11e3128400d0001259000088036dc0000000ed600000002998cb94330d690b4932200006973428000268876346ea0000000000094c2232e4033f368c79d22880000f8c0a5ca8d2ef05942810b391bc071e96002647284c147d2245a68f2744be833f20004768e6b261886121f707b000000015d448923046cf4668000259000000008b04ad020b2614a40ccdc9004e6454a0000eda0000000149400033fc0000000000127850000000002a100000b02c5f1d5488a441c88b20b11f00330147b90d3952be0b094db0287126c00f27871eb30888202a547623df6ba6c594c69472035dc6e44df39fc94c4d8cbe543a0a0980000000000eba37d4fc195dc38e000029307705bf13fca552cfd2c09d1634b4f653cb3ad0bad27f07ac0bed37812881f749a0d1d465119c49611230776ff539001fe1e545aebef926d31ec1992e7506c24cb2e318843f20240931b4ae972053400940912854b748e616451c78000e30b4cd01e2da467413540a021544c4383065123108722e391e51164ba94c813c63d770b0111006d2f145cf0000b9312bc00000001084d00fec0120000117c00000005051b441aba7e60002c4d0542a6464300013a700008fb23585412874000124e2893d2c2ef2df4104333c816000082f2a7000003e600022a0295375cfa22838822155cc5e00012773eb128717549293395355bc1035d4f201f600003a80000d1f1c6400023a70451fbc87125d486a2aa833a047465915cc84248a48d335f828e06f40000ce44dd38851614dc400024707764ac80000000bc14318c3017d40001ca8d0641100d825feea91258a0c0ed0c910001267000135aca74d3e8000ae11f607e8326c1c132584e53220a19223cb623240dd1447809d92b1306c31aa06450000014a8e354d9c2db40d626634c048a2b6507309d086a97d038611a4000247cc85209481800003af37e07fb39f0bfa1b54f7a16026723e6020e2f18297bf880004890aa317340003f6068f8000d7200001034dbe000372930f0f5d33f0000653249c5971a18c97248400031ca05b378c00017e05d21758b750148f4baf4041b074513c164cd6a390832815545312c600000001015006c53c40211e8129868a40492c50a9000000004d001c80003b8449f1ec2bec0001060009a56a4c926522a3000002951454304ab395452e707a8000076925a3068df6a90097116805c02b2913b0e682063b500a4182d01613612cc0cd91ec1940d5c3bad0490000fc54a440000000db2082014001cd192269ce0a4a1077c3fe8a930000231364800007642172f80ce2c652b81000096939680000000753144a376332104d00000001e490f118c4000000014c24208238000fe
  | 36 => 0xf58001070292a0000baad51170ea1f385436b00002a20000dab00000001a3000000010a80000000000000023e800023a40000000a12000015f00001b988d0d742db47bc00001c60e0481d00006d78000a92000080a2f34873281464e0cea04d41366bf43ec1072ed50d2cab844940e63c047ecefa2b5e8ba000057135680002b24a4f305000006b90502cc93cbc0eacedbf5d1270d10bd20a80c7d0efa8f723646d33a0ac354e2d1a700000000000017471003700002bc4e2847f80000003b9c96a17064c10000f8516646820e348db0000000186087c000115e1f68ab548950aa3c153a41d70745014511a0ff80000000f1738e85060130da73c94b7e48550cd33c0fcf035c2e21ff404930e8ab318e0bd313581a62a141b339a0d0910f4a031d692b5087828c0000a568000feb3654b2e434020218680c01f9cbf5197cbbf4afef79313424126372a7cbe0ff23698b1e4e7094249e011846f425919d8a3d83ceb6f135cad326ad35c195c00000004dc800000011552da48487f687580003cc47770318000000031205bc8c3289c9671a000002045185000057e016800005848fcb70800040d80004bb53941b1403400000004df01df30f510101f4ee9467517c3dd8b961d04fbc015439f3a2800024e42d6152e83d000000000005ca0c6c075179c00045c46fb471858916748f12bb82983d3c1b511b04c818e4a90a7586a2a021375393528624e0f1640843c32b6255d046800036a463f3e0c000000133317e41011a1c0001090ecf16f034d2ce888383a090a05440002e230ce4c5504e0000cc939a51d7052045a000034021701fd318cb164ca50d38000c6249b0658032c0004f940001004f0900009fcabb43bb000000023860001e5032f483845ea8b859c42cd2f880000003def34e0000bed00000b900de9171c9c04417408be37ac9761d782690e40a280128ece00001429560388044038c188600000004300c7cfd637b418c34e10b232c00004008000000000018f2b018dee83c23d921f1e5c61d0414b0106700004cb400033080003e9c50780000004a4cd8d0048414130ecc516bee4bc38cbdac356fc62564c4013a08e33ba0fea0010cc0b72c27226bc4fe80000000b952f017c400037740000000a3710f800021783e9050c542b4d02c2000127a000121c000121a3d4d03ea7b10e2395b1cfbc0616ca782bdd2de337732f0e523abc6a6a16892828ec2d5180d2300a67371b390ead4789080452419417ce04627c4af14f54d323d0497e914313830d03d2079c1701dc4f214dda0002afc857077eb74071538500005f0c5b92614d3d30ba4043b607302364c101c58000efe1a86245000124f4498403468d1571cbca361134e671bac2e80c450010000b50c616a5b01a50c200a53de3dcc9582e3c42227c892629108cb4abcac622d45de25
  | 37 => 0xcb111524783a24daa70703f4c3f0304c768000d5d0000c440000a539bd4e62ce1c7c818f82c33f7400028984ed3aa0d430a8c000026f22213b863c0000cdf00001804e883eec0291741e84eb6132400000000000000000426c63a4434db9095c6ec14dc2d0462e0003c4000029e008e47380000000f580e54db63df8e991074ac406b52bb80007840fc03c70c0478b2c54e9f3218ed100000003824000000000000001d9c36521b1c053440cc400005ad3d023ea9960126cdd0000ab74c643ff208c9e043f0f020000b77472caf1935af3d416823513d48bc465cbfe405018d913d1f62460b4b28f853f15686b215581a6a3fce084e34eac1a691cf3c012fe2dfac6a000124c28bd05b01e45e900000001026000474c744000116a2f5b13f29a47f014681c9800000018dadfe3c16b4c0d510158920455bc38501174c12c23a84d20001256422ca8796e854234a902ac23e53e00003ca026c34937d91b44ead22a179894b0000777cc7d1b1497d2b13e80a85c51090732ed36da2600004ec0000000065c00011802c50f9f0430845cdb87ec4e4cca008cc06c248c5d901ac0000bcca7a461c0000000dd90000000224a6ea3e3ca35321000016880001b8c3e8000000014b0000464c000187885217b4f223de711433fe77d2d8110346f287d00000414b4800030d8b262570f572c3280b076048818d84cc3b188bf3040000235502300001343c666ba800086e000000029d8d4d05a51113d4e2320d6cd102da000041745b24aeaf9b13e45441e45027836b36b8c6e0002588cb72a6c7cb270c5b91300a1a48d04433bd4364afb72f948dc79a0b846c63519081218ca040bac1b91980b4a1ea6ebf0d1cf500f3d02e2548b1b073d2df1008a2c3d747de157d1d049807473a98b611da8000402a0ab22e425fad442613f011784edc00047713e11b603d006b71b31820000083ce064132d551bf044c099c0003d9817f2fc9180a854fc6b45405d9b48a4647e05b03eb4000000000000001ce396e2e03840de629ccf7d2fd800012a90a514ec878000015c301922b0beac63916030d0c3931d18b4917b22c00031088760c2890e2c3120813380003d20e0d0000f13921909205130f62e84f9a226cacc15e8427139c6f20e0cce120503722632a8a0f4d0b2ca04de50da12962ee1093925482b28a8cd112c8da03ab6153b07018baea93300f88ae018b13e4231c3643610d8328d0e070d1422e34da493062b34d0bfd09e0b000f32aa527449000000000eec29508ddaf8c7a93956e312ead08a00011cd39b05023d582fd4b888ab3f9ee623c860000e4c341166cbdd9b9470a01ce6340000d891bea0004d2897d016078d3ec023800000002430faf465800028a467a0000fb8000089e000005700007fc899a9ba000043b8000b4f03201d30000000000032413989
  | 38 => 0x316507d429875d3ea4b1d21ac100a28c73e41c85aa431eb5401a83a30000000000061ca2800003784c78800052607c4c779a0c00025744a800000003e309d70bf8578008d33c057a51780d8bdb0a4462801f8acb090c29ba4c248c32d12732b6c1cd2bfcb44972f31a4b9433d34aa2dd0be88b815ec3923e0e448c4c829e1c14cc41f3c71d3978b0742300620f080b4b589365289413a36f08d742dc3dd4864aaf0a2c9113fde8df29fd3519d086620dbc3082b34bb69806605337908f3910b5a014a8eb28407c01fb84a53758ee34cd8c540c58aae1620ced34148809ef800c13ead00184c5fe2f9842d29f81eb487875907803acad485ce1a204253e3904016866bb1ae8ec71648af00258000000127d259a2cc4a40d51800000021b213700013603a047830000000000101c0000e0500000000000895033a6704d6600031ee000000018782da00000007c880007c91df32062a940000000c58447c0003a4c0001fde2b520ca76428e8f6e4f44124260628a22529cb393084f4d88e8c3c2819000000003d0cc24b0087171c248d23c820df42e13b91e8c7ce17d6341afec8e8184117d32b60ed4da53bd17eccef4a3ef1c02c878d9a780c507bc8e704af34827d499029913b620fc0fc2a76e54203a915cce53274f3d2f62929216152ce61319227c0d28ad735d48560ee8f812ab4086399922839145681a447f300000003354c032a7c6331a1487f0fe51000000cf10f5010d04aaa831364867224c26b38389553e413860d8515500001458000000000138400011958000000367459f39c454612d130144d8fe4843c9252ba4e6e1c8c7fe23b876f033cd0d2eb8bf19994622a7a400042f499f0000d171f9024e00009200f2c0b6000000048bc0c31b9e58280010852258d133d4284b0000e2d00000003438ff037343f14b24cf421192174f50356386032035dd0c5306ee6d356c08a00000db00012b60bb43d99f94f440000209098057d0b109a84014860445800cbb5c00038d90d628a68e448e499927a083a30ac2b2000113d092c6072ebc0002ce4c9c00012d40000e910000fb13b0039780000001a400004f8c9f3153246bb3cb07500007364060b87acb52b98d3c81080005e5000050a095a26d2b0818e2de43d827e8000046c000108071b0f8f0c4b2244f8170c05e2114d264b807e3275478f0e920003290bb1253493bb7dc58f271c7a2403d0294394ba3800018b1a883f30d544160fb8000049886880004bb85de0000cccbb7800000000000000604000264c000000060a13ac31480007852c800003ffc66800002d1001c24a36785a621fb1861b7c0004928b1c0e3c47bc3b878e3e250a31d7a6e9391cb37475abef4fa123b4d2417999a8813475400011f6dba000000005593d30b1d2cb08fd3bc402c00000011f701c437d2c9094f4
  | 39 => 0x39710a800000006a8204001e4ba85602ec904f27792a4806139124b91d200b8bd130a53dc28fd33cba4056132681a797082b0a18811c303d3eb3fa019a35304122c68f7ab4a123d41fcb6b175635f0fad2fb4b04f068d4cb5f96a03adbfead8c088480445085663be02c91ffc000022a456b198d794a985bd084052711187750000b443ff0ea44d049344d407d38574d18057e142000047d2db63c118f4b6c20a8d362f3834308ac000000000003dc0002fcafdb252ee8f270417bbf963210a76b58111cefa8c7894100b40322e88ef916e04498e78bf0277000045b000035bd3bf05d400027d80001d5c00000000003ad4d5900000000000d8f0e9102247f829a029907e4eb91f43a006000720f6900003cc0000000371c58d4998a4b1608c08c6dcfca430c23c4bb00000000b8a000047a25b096f4c8f2ff000126333760d24dc81ab01d00004590d7d297c2d7000000000004bb0000c6080002dc2d4d19025e0a98145c75825ad2833bc13560c5000000005a3a32800000000000000beb16d082900000003b08b830000000034ce0400004c3430112d3d2539e0c2cb0b1ff0d2f1fc4dc64e587380342050162c78029e31ea06260000f7d0fd06c91534e9800025a2ff1023c0002a46fd405d0f4a164012e283cf90943ccae3938b85331d191178c92dabac9df4a7059525a7253045c7c5847c3e004acfc7a4585c946650f93c3431c0c606c1120430005aebb5bee845c4f08b0329783ea3208173087ce1122a8e8e48040002dde1134e950168000db50b788e132300003b2c1842ce0f0734f0000080481f097137f4068c1e3668f00b170e94314446a2bb044fcc293ac26cc3e63c30fbcbeece7b242cddf20993dd40b4355851af0f20340001d580004ae458a0000000233817d0a351d838e0e511696000117e0003cbc760136b08d2608183244d0a74c94f34000025521ed3d848d809a80fc100000071400548af26287120000f4000002b10000c5a02b09c542d231a47d4a5a3c64250102897309092aa27c06ad42d6f8705dcbd60bc8251315c5a0aecefd12e8d22d0ac0db33b5514f02540000000e301248f5f0000859397a73213dc92c0e00b5726d12c62ba84ae1b50fd29e64ebc354e47b3df0ff432a8a46819498313f0f4e4c5066604b611785051c301ae0f00f682ec120c3ef90f6d732488fde10a0e762becb653f20f6c1b30187011c69326c402412e81129a5049146c8ffb17d2c731f7ef5b3284b5c45380bd290c9ed14b4050a6a8af31cfca4e38b861206b05e23a880003d9000009ee0003f3827733f502510d405606ca90907c8eaa4e7ccd437210661578eb2095009a29c89144eec8dd25103091dc10c81a701581efcc1ccd987f449c8cf334e40000001354c654fc096ac0004f10abe27948873822e2700008659f0cc553f34
  | 40 => 0x91dd1e60a0739530304ee093f193cc9331d426408601299ea103c32cc0389275390429106425691044cec1820fdc0b32c2a579482487e052800033da1ee054063b255a1d421040000f582f000006cfbfccf1400002e414032412fe097a000000016183ec82a6637351106f18653b1196c0872be894aa660a451c3c37110f200000007f994f49fe4db20002df21a5958cb5d15b0239443881c3f2cfc741844bc21b41b711aaa4b94e52aeb9e0d6500000000000454802c3153c0e5c629082ad84881912bf4d613b600e92ecc77918807dc8b32bcb130b3c514349f6c68525e0000ae403940cac9952a6c4c46f8000115c12f452b3954011445c1e43d653c914c06c900000001000a6796dc000192c0000001347000000004853ba3f98b9514848b42d0ea55b878e770a6ca86b3c8252b64cd1e0418602000000000cd0070000c07240d27c03daec8010064a27ec0000b9b0900c11373265c52f0000423a300d1621940f5c3432d3000113919f4e4a926409712c0adf2b48ac11c30d6b487433829347c64246efc3e0014507cc6d182a495e1370b0816cd382459928028347d60bd5135134c61c250cd562204cea3ae022a13809053a58d3a29d445d80840eb0b8cad102f923a1188889254a077049c6c74a647180000c83307c8c61b8800022509eb1e94298c5d53242c3712201aa1d038c908ec81cc72000011107a0a394c603dc43ad10b2e501b610a40001014e1c14c8000000084908583ed0f441dcbe54ea502a10f0000062e17f06fd0000c98208a36d33acbd72d6c3774c38da51cb8c120c3c0000000a413fa41bf4c092ca00000001ac109c00007bd38a04bf0000fc48000f290ea800022740000098f958af800000003220000cf5000000045b402008ec000000000005ecb64000018a40c4c0930040003b74000000000010209cf451800021a40004c342270a8525c458cd0c0aac4fa2680d00b0f051d213028812387f739952e94b34f43a66cc08427a7b84474cc64b788063c552c7079251503586a719f839900d478210b01489fac6e70848def37a49bd15bc8a1263a2508c400000a0040f38641ec41080002aed2b33b4c9500000c31169e0001520ad63a18f1a4164fee0f181f01b0c000000002a09a800040d036a251c00018ac00025282e8c5607213fe2000308c000209600019c400000000004ef92bc086ceaabca07d128c483215c800000000003d702b827244f44a4a0000a16ce741a88b748512a5000000000008354bf5223028840c232421d065d28d302c6d645cc8fb849e03d14bf0974bdc258329d12f40ed02f3e7535b455077d8ca4f3c1b342a70000904437c06f4a2d01023892e6083677b38b07462f240000222f5e1a8d0de31d00004a30a9010c84721fe85bb0000fd52dfe5044ce0bd913843fc414d0e622b013000011c2
  | 41 => 0xa305c363370106d0448dc41b749db4bcc9b53ae52ad3acc13b1f34e8b26010c94ca13d64c1f0ba0d7a8d10f5b3613a5d1680cac4e93880681097400045651ff14703bd3c740000e7520f1198fa832f90860000f8b07844bcc0f49dd1fea76c000136821342ae1fee9bc3b78ab144ac74908440004fa8315ab5aa3e80011d9000114816bca0134221af00002d8481072540ac33c4ca89ce0c5c00042ce1aa13c4114323c0392a812f10e5a70e2138b9f25ec5492a246c024f2f93c03817146b127f1cccf9912d50ea27eab8c00000004574000343d0be30b80003b7000000012030000000433d25b177006711d8b352940d4743e936ea02413d3f108dc03808544f0081928709a104a8fc21314fb32a90c9f0cc89ae233c0002c34a9e2a3ce3b1ee6c2c34c50e13410ea705100002984a1321dcc181f303ce0a992ce0d788031de00f94b607f61f7d2e80b505fd4e6800009e07e12d0ca6a25c6000000000000003e71cf1300470400022a4d58013855c03d81deb9200003af52a1038878612a4cb0a85c263058c33b4a13011179e9570c3137585e8dd311825bfb6fd1f12d589664d1800030c86541ea85c41a341163940ecc3d8c00012c531a9f985eb0000d87000046d24f89ee2e78946450c99e439ceef06ea5c500006ee01849193b0cee42f5e5cc12cce9a456c80ba62d2a20ec000008dc35733b07c213ec85b14203b72d18a6d0000c79334c0931ca47ea00000002cab2c043d020c10180de4af888e02ba3a73cca00003e27044d4cb0f4288e0b2160afc0728a5c4decf5187872d9466d1a80ae899d40a07f84c200b124c86630cd101703fcb401f4c5a4375484329a0bdc4d145c7387d37020ecdc124542f814a520d498806316b8984021508949b92c8494887f975cbde07e0cd6183873719dc5f240a20e10fd44ab37510d1142c31941dc42e18343a144141c34d2d1e59c70dbb299c5b64700c250e5735d13883850432cc3282cdad47148cd1b903983da0b0e0fd095b457d07a357cd530d648153c6a15512dcbdf08b047e0993279439071a3808f82069c54c2c0032621d40ca23cc3911692b02219b1ef076ccbf482c54d1bba14b4730bcc11cd03793fee4a19ed0d40fecc333d94b7f4b4486f4588d99185400011583c82828ee50de83c51458ba441200ae4691339bc190711bdd0094cf43a6333832700000000000b9a277e09f45e856b301427a3278daf40007d70000ccb0000e59493935a05e0323043a1c73e185e022680823a701d5421c7132cf02852078d2537c400044e8d8b0000c4115a477400004f78000b7342b457c13bd2ac2e4e2c9c2eccfb000000009f400011f000035b400000000003b64000000000005db28e00003ad000052e359d321310c0003c491094844000270934bb46451407d41891c400000000e572aa123136b
  | 42 => 0x6a18d0000e1f8b7ca14144441e30e524d04e11212004f1f4744a4c8000000173b2cf3724cd814e032d4a8021528f0115005006e000082e42a41e541313ad30dd05511dd20a000000db420bfc3a6c8c5276456e3264c71409a9923ed09fd0fbc00035c00000f0231a80000000000820aa74b518000a3d1a7ced247f1290bd1419d26e4a3fcb0c00044c02962b54bcf0390000119410a00000000181042800118f0000000272e00004f935f148800000011c68d38028bfee7c71d0c1acc6040030654c7a31f0000000004f4adcffd0000b0400008519ad81ff3e5c9da11000000000025c62400000002aa000080c22906de00000002eb0c4f00080000000ce8353c00003f80000ef114b308a0003d8800000004f6000000046305ee150eeea3660000000000037150bf4dca00046940da031010e32ac000418d2494c7936b4081172000028f00004f20000fcc1e6e76183c8da11908000000000043600003f3f1a9246277a328d14c435527b00000001b100001790aac020af6745e600027fc000476c00048d4000023040e0000000000138349200000000b214bc8d8200001e5c1604fbb0446e027411ae32d4185419446b2b787d41460000148029d0e70a533b406143d50c8d0ca805d1be2df40000000323eba51e9c64532ae4be1bd09e62f6e5620a12f5a374862f0a7ce3f27606a40370fa40ea41a929167b24c2c6470ba46492e00a521b1a5d118d483e431678c278411e0a508402c940004480c9526304a3247400036444753030c9d4264df9170a20a0bd903338483f7c92cc48108c43b254c2cbc9508384e011c70000af4bcb0f9a800000006ec6c9a036ba63c8aad447e86aa054cec4181e00004a51340234d3716605d41898caf0000d8006a000034d6d602e08000000005f0000d9743b437eca2055b19d5184000009800009be467800038748ae04800001cac000373830546c00000000b4500009a30000000136e00011d0000121000000008ed000027f13b057f22201ed36292fa31140003dac26f2ec045d18b200022344de07d0f3f1890373301104ecc1cc73a4481fa4d54cdc25cb00410dc83735781590dd48740aec43f29ec00a34be4fe161cf381db50dc0efe15720c41a54742c261930b7c4b400f2bb34ef61eacc21078928584c40d5129709f3d48d6c0f7817908f800033c70d22cf43daca600003c0c0000000000000000032b44543c9859a34f50060000f3327bd0af1da0bd8077400000000000778a8816583ac000027301ec96780007dd00000000000000000000017c0d1a0b22337096c73a00000000000a71000098800011be3cc871f01de0004220daa1f47137350433e40c88ec144c2f40000eb040daaa2411d04143d522e19a4cc12a6800040980003075334081417c1a48bb41d9c0000a8e8072b7469eac480000df084
  | 43 => 0xb54c4092fb90503b97e929b41e0fc900010e043fc3fa1e6ac133eb828439861924d640001ee91af2ae11474990aa1154812300000001c08a870338bdc80011a62f1c5139500ea314387b518c106808708022f6827e20d026c0f544982699082454400010d0cd94322f9e32c80000000a4990e80000c080f522300002cf933e3ef400047e4fe2a3c8de836e126b34b13df340d12e4bf30a2ac0200000002c10000000000113e4724dec21a098d0000000105d05600003fd00002251f823844a3c07f00a00000000eb713ccbe24a4ebf70000000000000e00000000000000000000038b6d71484d39802480b0800102c00012bf072cbd410c4efd00007f94a68ac8a3f89bb102249733e0935444c6d036500000ad09b000005074cc53a80146dfb800000045ac0001bc40004d080004bb83699f4045e1900c5339c01c4123c1b3b8a43c91d0066e0ba600000011521d851020000000393c0003f807ca0462453000001632aa0000000b48131c51b2dc47d480008b600010462878a7d2b3ca6b3e667a024f0e75099400000000003598000249099500012c43bc80004cf600000006bc22323ab0c940001a46000000000000000000000c2f129d2950ef8c871604d3f00005e8092400036f46d7417807600006b10000ca92749182434c0000000fb225590942b146ef2b40a3037b8229306506230ecaf431393cd346c000000000000000004f048d81b68cb81a6a7500a5cb8b26fc0b016f85b52ff4f1bcd4aac848086a90958000133d37d385c000398ca6e04066640000000140d095089864d3730e9546fc5a933e879c37ec7960210abd12350c42c644c08da47c118ba2ee35141c919548cc1144df38d1840b4e8c4103a4859e0986fab3174c561acc25a14643b1072b2f53c4cba70000066118c1d72f0cb34225600000005db3a3527e3129046c7b8e7e2ef4fc3217c240225c0001b64d12000020d3e45092bd9ee1a9bce2bab8511124ea418c831c1a022ec00017cd2f432b20002b3800000002b71ad514100007b90000c7f3cecb29b42c4851d1e9b829607304da8e1300946ce1350b7b376053518a89fb959097714ccfe70c4cd1c2b9917929e404500000003b8070b3e9477f08803742b60cca0000fb516c40002ae400041e400027e40003fa31830000c75b11c8920000b5f02fcd883e501b12be46ff051c66f10ccb9b0000490119d0031c211e643b00000000ce60000bf44c481fb0cee940000107c4e380000000889b48d2264dde82705c8d7831d32203f7c1d22ca82fc000f2422e11289436cc5b4dc2c3e209a0f4a7d10d480006610c1847000009c82ed2f2002848360f6485d1bc135839ccf0b0000000000045b00000001704dd01824689000000024ce407122d221386878107e43794f68154812cb89cbf13090d9cf751d282f90e507203a
  | 44 => 0xbdcbe4211016216944641be41a2350046140f244a9a60e831c34b862fa42b919f1282224000000012ab33dc85342f082180000e61b713b345c094e01c0fb9021205cb79103d8ad8ea12af6d7a2d7a14380010b426a4f94b97c2c18000000306d19f23bcb2922072b823d4257c7780bb0850b8702bccb897fc87a23c00dd0d1ad7c1da53ce44a0f69aca06443ff89b61cf4bea30a8d014f9c760cb540831010ea02cc030721452ba4d50c67433f2bd41b8e001c19090befcfe1136c722334003e3cb8bba33a47c6b09cc5002a80cdae48ba000000000c0cf1b22cc6be4d911d4054b1ed2ad295418441661818a940000d50349c75b39bcff628086ab00000004ec8980cc44b9801e035105b80ccb548df483bc8502e70d7b00004c20fd8a23000000049c00002e345a6bedc360030886404b25091be8c5211bd04a491137a26705da42684a00dfce9e4f1c05312b4471138c73b2f08b422340f7201510ef1b8469d4ea93e900004b837a83b84db4f84000138c2bcef6f1eccb1711482a9229877bb6d0fbdae96949a638a563dc0e8547290f71fa46f64e6c98fce48149183d3521e4c21330908fc0d682752cd81b402006791e900302a0836c45f809400008b20464dcf0000545000070329944a4491897f2974335000035c0accb700000adc03d029a9df800000011f2428061b4de40002d7911c01913891760a57bb6c0060934000000000000000000000cd8c1703b91c44c494a7c91b038c69b2048a8b2ea092a1e402ca00681139b28f5549540000000000243c20a968468b1e28000000020000000003f680004aa2d294d92ee60e5214f2fc2b272b00f0fa79c4b60aa101d3d1d1e04420f9c45bd0ae13dadb1000019e4688b10431cf18ab6923e04b4c4b49441643f8c902137600037e925736a0c0d0408b6e14e88a72650b9700152dc49d886c3dec56d3cd8c460580ce30b4eaf747a508300000003e98bf937783e4a0931ad088817e2734d494a972db0000000421058e11b84f02f10b5531bc002983097049d4bf33bec9ea3960c619128f923fd718e36b020eb770a4c409cd683ac41932a9c430960d1180a726230000d85035051f1550b89355c00000000003380d202aac000404d26a3a1c41c000000004d4f3925f8000470600000007311a6537e3cf83a5063a5842694000336c0002bd4e0f000018f19cd12a1d34000070891a3d720000000c6e00000004b5c389349000000001e900004fd000014e34d4df346d8db01068000000000028853230df93031a802af394c5a28000866000118d2d2400009a10e9226400046e800040640000000a63000000000000000001357206800000000fa39d02f1244132e3fe66ed45ec39b190297db0e0d482eeca7424523f837c8ef11ad00001adc7dea3a30a142b07ddb5fd13348fd0fe2d8cf2332383
  | 45 => 0x2cd40e02e7bcc02d31ae0f27134475fa92535e2b1cca6054858c29c00002f540000000eed38a92a42ffc00038cc684042c0810685291a6907720000e5f80013d7238047ca8c801d1f6448230583422fceabc16509e31064b913bfc000125280f90e0638b890000056d18b104496838f4aba1dcc44e0344a6c46ed1a01d38059201468e2d9d26908b49cc1b3692f4cd517608f489c1108a960000ef434503e403c40b70f35292479ccee10d849c2000dfd44308171a5800008c000000011df00000aa893c0d9b63842b20e53510978cac0b1850c2cc40000000000000102a407c0004ab67261538cba2514f96132929445dc2eb8582efb9eecd9b40a6fd9028ce842dbabbe11a096d334896e0f63076219ea6f0658af2b484b5924ad2710
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5e7618c5144001c3ec8318a28800387190631451012537436c428a2099c6e76d885144001c9ec7b10a2880039318f62145104ce3738ec428a2000e6671d8851441318dee1b10a2882631b5c362145100043fc3ac428a2000a5f83588514404b4b906b10a28825e9de05621451031d37430c428a2096c6e761885144001c9ec6310a2880039318c62145104af33b08c428a202be5463946314404bca8c628c62881c799188518c5100072a31ecb18a2000e54631963144001d28c7b246288003a518c648c5100056a4328718a2000ec463d8a31441299ccec314628800399194628c51000752320c518a2000ec46318a31440015a90c994628808e1fa1b754c5100061e326ea98a202bc5c63dd531440018d8c5baa62880961fa1f654c51014c3e43eca98a2000e5431d95314400187eebb2262880030f1d7644c5100062fbaec698a2000c5c75d8d314403f9b0e1b1a62880031bdd7624c510006363aec498a2029c74769453144057ca8c728a62880a75c1c2514c51011e3a3b0a298a206ae646214531440578e8edbaa62880035c1c3754c51012e3a3b0ea98a2029c7476d953144001ca8c7b2a628808f1d1d8654c51000c7a432e898a2093cb476d913144125968ec3226288003a518c644c51001e6a3b6e698a201fdd070dcd314403f9a8edb1a6288063391db624c5101c6723b0c498a2000e64651893144001d48c83126288003b118c624c51015732314a310a2091c76761462144049cc8c428c42880039918b658851048e3b3b0cb10a2000e646219621440011ed0db9c42880026d613738851000762316c710a2090cd67618e2144001d88c431c4288002b9219328851011c3f436ea90a2000c5c63dd521440558d8c5baa42880921fa1f654851014c3e43eca90a2000e6421d9521440018beebb1a4288003171d763485100076210ec690a2000c6f75d8921440018d8ebb12428800ab9a0762485100c674386c490a2029c74769452144055cc8c528a42880a75c1c2514851011e3a3b0a290a2024e646214521440031f50db8242880ab1d1db754851015732316ea90a2000d7070dd521440498e8ec3aa428809399188754851014e3a3b6ca90a2000e6462d9521440478e8ec32a428800399188654851000c7a432e690a201fcd476d8d2144001d88c5b1a42880eb351d8634851000762310c690a2037ae686dc921440059c8edb924288063781c3724851001573436c490a2018ce476d8921440474f50dbae20880a71e9db75c411011db940eeb8822029d7271dd710440534f50c3ae20880131e9d875c411014db9408eb8822029c7a76d9710440098f4ec32e208807f369db63c411001e6d3b0c78822018cea76d8b10440059d4ec316208808e9ea1a51c41100263d3b4a38822029d727194710440534f50c28e20880131e9d851c4110
  | 1 => 0x8e7b8ac4881931b9db651891052f32b8eca3122096a6f80d94624412d4db01b28c4880023b61e65189104ad3742cca3122000ace83994624400159b07328c4880023be1d651891000567c1aca3122000acc8359462441495cf02b28c48825a9ba18651891031e373b0ca3122091e6571194624412b4df00328c4882569b600651891048f33080ca3122091e6410194624414799cedb18c48800393d9763189100072632ec63122000e8f64d8c6244145d8ae3b18c48828b93d43631891051726a86c631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c624412959d07318c4880023be1d631891000537c2ac63122000a6c8558c624400155f08b18c488002ab211631891050d73c0ac631220a0ace8618c624413f99cec318c48800393d94631891000726328c63122000e8f6418c6244001d18c8318c488243b1604631891048762b88c63122090e4f5018c6244121c9aa0318c488243b1840631891048762080c631220038de83dd952440011bb07bb2a4880021fe1576549100046fc1aeca9220038dc835d952440011df04bb2a4880023de0576549100143f43ecaa9220048ee87d8952440090fd0bbb264880021f617764c9100845f426ec99220008bd84dd932440090fd0b3b264880021f616764c9100043fc2aec992200487c855d9324400117f08bb264880422f211764c9100046fc1aec99220008ef825d932440011ef02bb264880121f214764c9100043f436ea9922000c3c64dd5324410d8b8c7baa648820f1b18b754c910004bb40eea992200087e87d9532440010f90fb2a64880030fdd7644c9100061e3aec899220028de87d8d32440018beebb1a6488003171d7634c91001c7743ec49922000c6f75d8932440018d8ebb1264880061fe1d65945100052fc1acb28a202ba5c8359651440014df04b2ca2880aa9b20965945100253a40ced28a209ee70109da51440574bd0db1ca28826f179db63945100070fb26c728a209cf5010d8e51441398bee1b1ca288273175c363945100043fc3ac728a2000a3f8458e514409547908b1ca2880029be09639451015536412c728a209dc5e7618e5144001c3ec831ca2880038719063945104d7a8080c728a202aa6e86d8a51441318dcedb14a28800393d8f62945100072631ec528a2099f6010d8a51441338dee1b14a2882671b5c362945100043fc3ac528a2000a5f8358a51440574b906b14a2882571b9d8629451000727b18c528a2000e4c6318a514412dec020314a2880a71e1c3655451012d2f436c628a209cc5e76d8c5144001c3ec9b18a288273179c763145100072b38ec628a209bc5f70d8c51441378bae1b18a2880021fe1d63145100051fc22c628a2049a3c8458c51440014df04b18a2880929b20963145103852f430c628a209a
  | 2 => 0x6518d104ed2ec00ca31a20abc9e76d906344001c3ecbb20c688003871976418d105574ab8ec831a20aae1f50d906344155c3aa1b20c6880023761e6418d100052f42cc831a2000a5d85990634415353d09320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc82590634415193cec320c68800387d946418d100070e328c831a20a7e9571190634414fc3ea0320c68829f875406418d100052f42cc431a2000a5d85988634400153d09310c688002a76126218d100845f426eca9a20008bd84dd953440051dd05bb2a6880023b60b7654d100043fc2aeca9a20008bf845d9534402117908bb2a68800237e0d7654d1000477c12eca9a20028ec825d953440070fd0fb2aa68801237a1f6354d100243f42eeca1a200087d85dd943440051dd05bb286880023b60b7650d100064e21ceca1a200087f855d943440090f90abb2868800237e0d7650d1000477c12eca1a20028ec825d94344001938863b286880038710f6550d100846f43ec6a1a2010a9e84d8d434400159d0732ec488002b360e65d891000567c1acbb122000acc835976244001c9ecbb1ec4880039319763d891000747b26c7b1220a3e4f50d8f6244147c9aa1b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec48827fb160463d89104ff27a80c7b12209fe4d5018f624400159d073aec488002b360e75d89100053742ee7b122000a6d85dcf62440014dd0b39ec4880029b61673d891000557424e7b122000aad849cf62440015cd0239ec488062b960473d891000557424a7b122000aad8494f6244001c9ea729ec4880029ba1643d891000536c2c87b122000e8d4310f62440311dd0f98ec4880023b61f31d89100053742e63b122000a6d85cc7624400155d0998ec488002ab61331d891000636316eab12200087e87d9562440018b8e7b2ac4880021fa1c65589100062e398cab122097c777119562440018becbb9ac48800317197735891000666316e6b1220008de87d8d62440018beebb1ac488003171d763589100064fba6c6b122000c9c74d8d62440011bd0e31ac48800317dd463589100062e3a8c6b122000c9f7418d6244001938e831ac48829b35dc463589100243f43eeab12200087f80dd562440010fb01baac48800e37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac48800317d4373589100062ea86e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c6f75dc962440018d8ebb92c48800333dcf72589100066639ee4b122000c7475dc562440019a
  | 3 => 0x4b2a2000ce472dc5654400147d09318ca880028f612631951000537414c632a2000a6d8298c65440014bd07310ca880029760e62195100045fc22ebb1a20108bc845d763440010ff0aba6c6880121f21574d8d100062ebaea7b1a2000a5e85d0f63440014bb0ba1ec688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec68800387d9764d8d100070e32ec9b1a20abe1f50d936344157c3aa1b26c68800297a1664d8d100052ec2cc9b1a2000ace82993634400159b05326c68800297a1662d8d100052ec2cc5b1a2000a9e8498b634400153b09316c688002a7e1175d8d100054e422ebb1a2000c5d751d7634400193ee93a6c68800297e1574d8d100052e42ae9b1a2000a5e851d363440014bb0a3a6c688002b5a0474d8d100fd6ac08e9b1a20008de8795363440011bb0f2a6c68800387d5254d8d100052f42ee5b1a2000a5d85dcb63440014bd0b396c6880029761672d8d100054f424e5b1a2000a9d849cb63440015ad02396c68807eb560472d8d100046f438a5b1a20008dd8714b634400153d08296c688002a761052d8d100046f43885b1a20008dd8710b63440014bd0a216c6880029761442d8d100fc6f43e83b1a20008dd87d0763440014bd0ba0ec6880029761741d8d100056741683b1a2000acd82d07634403f1bd0f90ec6880023761f21d8d100052f42e43b1a2000a5d85c87634400153d0990ec688002a761321d8d100062e31eeab1a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac6880030fd977458d100061e32ee8b1a2000c9c63dd1634400187eebb22c6880030f1d76458d1000656396c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d100066631ee4b1a200487e87dd563440010ff01baac6880021f6037558d100845f43ee8b1a2000c3f75dd16344001878ebba2c6880030fd437458d100061ea86e8b1a2000c3f751d16344001878ea3a2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac68800a3ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f50dc963440018daa1b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d1000672396e2b1a2072c5e76d94634415bcaae3b28c68826a97e036518d104d52ec06ca31a20008dd87994634413b4bd0b328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d104d52f430ca31a2070c5e761946344159caae2328c68827697e0
  | 4 => 0x2c40090f90abb265880121f214764cb100043f436ea996200097681dd532c40010fd0fb2a65880021f21f654cb100146f43ec699620038ee87d8932c40534e902b2ca3881da1fe1d639471014c3e43ac728e207587f8758a51c40530f90eb14a3880a71ee19709471014e3c432e128e2029d73815c251c4053ae102b84a3880a71e985709471014eb930ae128e200187e87d9551c40010ff0eb18a3880121f21d631471048d3b40ec428e200087f8758851c40090f90eb10a3880131ee1970147100263c432e028e2000c7b625c051c40018f2c4b80a38808f5ce05701471011eb840ae028e2023c7a615c051c4047ae4c2b80a3880a71d5da518c71015f2b31ca318e2023c757614631c40538eaedb2c63880039598f658c710005b8c06cb18e2023c757619631c40016e30032c63880063d61b748c7100056bc326518e200087e87d9531c4001ca863b2a638800637a1f634c71015f2a31ca298e200097687d9531c4001ca8c7b2a6388002dc603654c710004bb438ca98e2000b718019531c40033ad0fb1a6388002f4603634c71014e3abb4a310e2023c757614621c40538eaedb2c4388002dc603658871011e3abb0cb10e2000b718019621c40031eb0db9c43880026d61373887100043f43eca90e2000e6421d9521c40031dd0fb1243880feb9a07624871015732314a290e2097c777614521c4049cc8c428a43880ab9918b75487105763bbb0ea90e2024e64621d521c40012ed0fb2a43880039918b6548710005b8c06ca90e20009768719521c412f8eeec32a4388003991886548710005b8c00ca90e20008f7865cd21c40033cd0fb12438800ab9a1b6248710005f0c06c490e2000a3e8494f654400147b0929eca88003175ce53d95100053ac0ca7b2a2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a2000a5e8398b65440014bb07316ca880028fa1073d95100051ec20e7b2a2000c5d731cf65440014ed0239eca880a69d60473d95100043f43c87b2a200087d8790f65440014bd07396ca880029760e72d95100053b408e5b2a2029a75811cb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb65440530fd0f98eca880021f61f31d95100051f42663b2a2000a3d84cc765440014dd0598eca880029b60b31d951014c3f43e43b2a200087d87c8765440014bd0790eca880029760f21d95100062e32ee6b2a2000c6c65dc965440071bd0fb9aca8800317dd773595100064fba6e6b2a2000c5c51dcd65440018bea1b9aca880031754373595100062fba8e6b2a2000c9f741cd6544001938e839aca8800a3ba1f725951000637baee4b2a2000ccf73dc96544001998e7b92ca880031b147725951000637a86e4b2a2000c6d50dc965440018deea392ca8800333dcc725951000666398e
  | 5 => 0x35ae097014520006b4412e028a4023c7b625c05148047ad6c4b80a2900035a8c97014520006b4992e028a4000d73615c051480018f0c2b80a2900035c18570145200063830ae028a4000d6b215c051480090fd0b3b462900021f616768c52000c76432e518a40029cf874ca31480075990c99462900121fa16764c5200043ec2cec98a4000c6c76dd52148001ad0e1baa42900031b1d8754852000c76432e690a40088ee8718521480115cd0e30a429000339a1c614852000733ba8c290a4000e647518521480055cb0030a42902c799d40614852058f32a80c290a402496e8794521480538d8ed28a4290003991865148520154b7438a290a4023c6c761452148001cc8c228a4290002da60051485200051f424a7b2e2000a3d8494f65c40018bae729ecb880029da0653d97100053ac0ca7b2e2000a768194b65c400147d0931ecb880028f61263d971000537414c7b2e2000a6d8298f65c40014bd07316cb880029760e62d97105863b38cc5b2e2095c767118b65c4001ae4e2b86cb880029da0773d97100053cc06e7b2e2000c5f739cf65c400147d0839ecb880028f61073d97100062eb98e7b2e2000a76811cf65c40014f30039ecb880021fa1e43d97100043ec3c87b2e2000a5e83dcb65c40014bb07b96cb880029da0772d97100053cc06e5b2e2000a5e839cb65c40014bb07396cb880029da0472d97100053cc00e5b2e200087e870cb65c40010fb0e196cb880028fa1032d97100051ec2065b2e2023c75879c765c40018ece538ecb880031d1ca71d97104f63ab84e3b2e200087d87cc765c400147d0998ecb880028f61331d97100053741663b2e2000a6d82cc765c40010fb0f90ecb8800297a0f21d97100052ec1e43b2e20b0c7671c8765c412b8ece210ecb880a69ea0021d97100053cc0043b2e2000c7a715c365c4001ce4e2b86cb880028fa1263197100051ec24c632e2000a6e8298c65c40014db05318cb8800297a0e62197100052ec1cc432e200087f855d363c40090f90aba6c78808e5da077558f100043f43ecab1e200087e8719563c40090fd0fbaac78808e1fa077558f100043fc2aeca9e200387e87d9553c40074bd07b2aa7880121fa177650f100043ec2eeca1e20028ee82dd943c40011db05bb287880021fe157650f100243e42aeca1e2000e1c43d9543c40211bd0fb1a8788042a7a136350f1048e3b388cbb16202397681dd562c40010fd0fb2ac5880021fa1c6558b100243f43eeab16202387e81dd562c415f5cd03b92c58800e37a0e7654b100046ec1ceca9620008f6819d952c40010ff0abb2a58800a1fa1f6554b100243f42eec996200087d85dd932c402117d09bb265880022f613764cb100243f42cec996200087d859d932c402117d093b265880022f612764cb100047b40cec996200087f855d93
  | 6 => 0x62ebaea7b1a4000a5e85d0f63480010ff0ab8ec6900121f21571d8d200045fc22e3b1a40108bc845c763480051d904b8ec6900033518c7158d200243f43eeab1a400087e81dd563480010ff01baac6900021f6037558d200845f43ee8b1a4000c3f75dd16348001878ebba2c6900030fd437458d200061ea86e8b1a4000c3f751d16348001878ea3a2c690003171d77358d200064e3a6e6b1a400487e85dc563480010fb0bb8ac6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031da177158d200063ac2ee2b1a4000c7750dc563480018eaa1b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000c77851c563480018e90a38ac6900033590c7158d200063ba80e2b1a4000c75501c563480010ff0abb2a6900022fe117654d200845e422eca9a40008df835d953480011ef02bb2a6900023d2057654d2001c3e43acaa9a4036a3c8459553480074b906b2aa6900029d2056554d200064e21ceca1a400087f855d943480090f90abb2869000237e0d7650d200047bc0aeca1a40008f4815d943480090fd0a3b286900021f6147650d200064e218eca1a40108dc8758d43480674b90ab1a8690042a72116350d200056a40ac6a1a4086c6c76dd53248001ad0e1baa649020b1b1d8754c92000c76432e89924000acc8650d32480711dd0db8a64900026b613714c9200243fc3aebb0a4000c77815d761480270ff00baec2900461f60175d85200063aba8a3b0a4000a7685cc7614800156d0998ec2900023de1d61185200053a42ac230a4000ad48358461481675cf04b08c2900021fe1573185200243e42ae630a4000ae7814c861480015cb04288c290002bc60051185200053b42e6230a4000ab684cc461480015cb05988c290002b96083118520007629906230a4000a5f8359651480574b906b2ca2900029de05659452000c76432e528a402ba5e83dda51480014bb07bb4a2900029da0776945200063b38ced28a4000a76811da51480010ff0eb1ca2900021f21d63945200051fc22c728a404aa3c8458e51480014ef02b1ca2900029d205639452014d36432e528a400096f874ca51480534d90c994a2900021f61676545200043fc3ac628a400487c8758c514800147f08b18a2901268f21163145200053bc0ac628a4000a748158c51480012df0e990a29008e9b21932145200053ac3ec228a4000c7587d8451481618eee1b08a2902c31d5c361145200053bc38c228a4000a75871845148165ccd04308a29025799608611452059733390c228a4000e65721845148165ccc64308a290003994c861145204af39380c228a4095c75701845148001ce2e0308a2902579988061145204af32100c228a4004c7b865c051480098f10cb80a29
  | 7 => 0xec825c7644c0090fd0bb8ac8980021f61771591300043ec2cecaa260008ef825d9544c0051d904bb2a8980023de0576551300047a40aecaa2601087e87d95544c00917d0fb22a898042a7a1b6450d3026d8f42ec8a1a603a8de86dc5434c00139b05b8a8698043271d143d89300043fc2ae3b12600487c855c7624c00117f08b8ec4980422f21171d89300146e41ae3b126000ce4621c5624c0050f90eb2aa4980121fa1676509300043ec2ceca126000c9c7650d424c09ba38eaa1a849820f171db754c93040e2e3b0ea99260028dc87595324c0031b90cba2649800297617644c9300146e43ac89926002acc82591324c0751bd0db8a649800267613714c9300243fc3aebb0a601487f805d7614c0250fb00baec2980023de1d61185305a56bc1ac230a6000ae482584614c021938e8a18c2980021fe1572185300243e42ae430a6000ad7814c8614c0015ab07908c298003395c82118530007629904230a60008bf845da514c02117908bb4a2980422fa1076945300045ec20ed28a6012c5e73596514c0031b90cb9ca29800317d9573945300062f39eed28a6000a7681dda514c00147f08bb4a29812a8f21176945302551f420ed28a6000a3d841da514c0014ed023b4a2980021fa1f64945300043ec3ec928a6029a5c865ce514c0018b8ecb9ca2980a69721943945302570e3228728a600095f874ca514c0534b90c994a2980021f61676545300243f43ec828a600087d87d90514c0014ef02b20a2980029d205641453011d2e4328628a6049e1c6450c514c0012bf0e990a29808e9721932145300043fc2aed20a600487c855da414c0090fd0a3b482980021f614769053000c6e432e720a600399f8750e414c0215390ca1c8298003279d943905300243f42ceca0a600087d859d9414c0018b8edbaa6298003171d8754c53000c6e432e898a60098de87185314c04b2bd0f28a62980a7171da514c5300072a30ca298a602b95e87145314c0478b8ec28a62980121fa1676885300043ec2ced10a60018dc865ce214c00739f0e994429800ab321932885300243f42cec90a600087d859d9214c0019c8433b2429800339084764853000c6e432e690a6000a3e8494f65480018bae729eca900029b60a53d95200063a328e2b2a40038de87dcd654800193ee9b9aca900031714773595200062fa86e6b2a4000c5d50dcd65480018beea39aca9000327dd073595200064e3a0e6b2a4000cd773dc565480019a8e7b8aca900031da1771595200063ba86e2b2a4000c7550dc565480018eeea38aca9000335dcc71595200066a398e2b2a4000ce7721c565480018ef0a38aca900031dd4c71595200063b290e2b2a4000c74521c565480018eea038aca900031d54071595200045fc22ebb1a40108bc845d763480010ff0aba6c6900121f21574d8d200
  | 8 => 0x9b98c2a80028f61373185500053b40ee630aa000a3e849cc615400147b09398c2a800317dce73185500062eb98e630aa000a76811cc61540010fd0f218c2a80021f61e43185500053bc0a8630aa000a748150c6154001c3a86218c2a80029da0772185500052f418e430aa000a5d831c861540014ed02390c2a815e9e60072185500053b40e6430aa000a7581cc861540010ff0e990c2a80021f21d32185500053bc0a6430aa000a74814c861540010fd0e190c2a80021f61c32185500051f4206430aa000a3d840c8615400147d09988c2a80028f6133118550005374166230aa000a6d82cc461540014bd07908c2a80029760f21185500053ac3e4230aa000c7587c846154001cad07908c2a80039560f21185504bd3bc064230aa097a7580c846154161cce41908c2a82c399483211855011d3d4004230aa000a798008461540014eb0e108c2a800399a082118550007333904230aa000e65720846154001ccc64108c2a8003994c821185504af394004230aa091a75800846154001ce300108c2a82579988021185504af321004230aa000c5c63dda31540012f301bb462a80024fe11768c5502b49e422ed18aa00097b805da31540ad27d083b462a80024f610768c5500043fc32e918aa00087c865d231540018baedb1c62a815a57e1d438c5502b68f3a28718aa01195f874ca31540014b90c99462a80025e603764c5500063cc06ec98aa00087e869d9315400127f08bb262a815a4f211764c550004b7c12ec98aa01196c825d931540012f700bb262a8003170c4764c5500243fc00ec98aa00487d801d931540018be603b262a8003174c0764c5500063b880ec98aa000c75101d931540010ff0cba262a80021f219744c5500062e3b46298aa01295e83dda21540012bb07bb442a80025e6037688550004bdc02ed10aa00087e86dce21540010fb0db9c42a815a4fa1373885500049ec26e710aa01296f874ca21540014d90c99442a80025e60376485500073210eec90aa000c7980dd921540010fd0d3b242a8003590867648550004afc1aec90aa01295c835d921540012f700bb242a800359084764855000732108ec90aa000c77211d921540018d8423b242a80031d084764855000632108ec90aa00487f801d921540090fb003b242a80031bc80764855000636900ec90aa000c77101d921540018ea203b242a80021fe1973485500043e432e690aa000e642118521540032dd0f10a42a80031b1da214855008db340c4290aa000a5d8394b654c00187ee92a2ca9804a97a0e54595305ae2fbaee6b2a60038dc835d7644c0090ff0ebaec89800317e0d75d91300062e41aebb226000c5f325d7644c0010f902baec8980521fe0175d91300943ec02ebb22600087f855c7644c0090f90ab8ec89800e3720d71d913000477c12e3b2260028
  | 9 => 0x7150d5008c3ec3ec7b12a012c5e73d8f62540010ff0eb1ec4a804b171cd63d895000cbd404e3b12a007979809c762540012bf06b8ec4a804a5720d71d8950094af43ee6b12a000d1f74dcd6254001ab6c1b9ac4a800317dd873589500068fba0e6b12a000d1c741cd62540010fd0fb1ac4a80030f1d363589500962e39ec6b12a01187c8758d6254001878e8b1ac4a804b171cd6358950006abb9ee2b12a000d5473dc562540018eb0db8ac4a80035cd837158950006abb98e2b12a000d54731c562540018ef0c38ac4a80031dd8c71589500063ab18e2b12a000d67621c562540018ecc438ac4a80031d1887158950006b2310e2b12a000d73601c56254001ab6e7b82c4a8003561cf7058950006b9b8ee0b12a000d7071dc16254001ad6c5b82c4a82db5a18b7058950004bcc06ec992a00087e81dd932540018f301bb264a80021fa1a764c9500049fc22ec992a05693c845d932540012ef02bb264a80025d205764c950004bdc02ec992a000c5e831d932540018bb063b264a80031790c764c9500062f190ec992a000c5c321d932540010fd023b264a8003170c4764c95000636108ec992a00487f801d932540090fb003b264a800317cc0764c9500062e980ec992a000c6f201d932540018da403b264a80021fe19744c9500043e432e8992a01195c8758d32540018b8ecb1a64a8002d6e01634c95008cae43a86992a000c5c7650d32540ada38e8a1a64a8046d3209434c9500043f436e2992a00087d86dc532540ad27d09b8a64a80024f613714c950005b8c0043b0aa012c5c73d8e615400147d0931cc2a80028f61263985500062eb9cc730aa000a758198e61540258bce6b1cc2a800297e0d62985500052e41ac530aa000a778158a61540014bd06314c2a80029760c6298550006b9b0ae130aa01295e87dcd6154001a3ee9b9ac2a800356d8373585500068fba0e6b0aa000d1c741cd61540232dd0fb92c2a800353dcf7258550006a639ee4b0aa000d6b60dc96154001a9ee6392c2a8003531cc7258550006b2396c2b0aa000c5f7398561540018b8e730ac2a80031bdca615855000636394c2b0aa000d5b73dc16154001ab0e7b82c2a80035adcb7058550006b4396e0b0aa00197886dc16154001ae6c3b82c2a804a1f61f63185500962f39ec630aa000a3e8498c615400147b09318c2a8003175cc631855008c3ec3ec430aa000a7581d8861540014bf06b10c2a80029720d62185500053bc0ac430aa000a5e8318861540014bb06310c2a8002dc60261185500043fc3ac230aa000a5f8358461540014b906b08c2a80029be09611855000536412c230aa00097787584615413d4ef0cb08c2a8002d92096118550005b9c02c230aa000a7586c846154001acae4108c2a800399d882118550007323104230aa000b7180084615400147d
  | 10 => 0x98ea000c7710dd931d40018ea21bb263a80021fe19744c7500243e432e898ea07687e8798531d4001ca86330a63a800317dda314c7500243f436e710ea00087d86dce21d40bf27d09b9c43a80024f61373887500a4b7c3a6510ea000a6f864ca21d4001cc843bb243a80121f20776487500063610eec90ea000c6f20dd921d40018da41bb243a80031dc4376487500063a886ec90ea00087f865cd21d40090f90cb9a43a81d61fa1e61487500073210cc290ea00196e8788521d40018deed10a43a804ed9a06214875001c3e42ae9b1aa00087d8795363540254bd072a6c6a80029761632d8d5001c3e42ae3b1aa0008bf845c7635402117908b8ec6a80023be0971d8d5001476412e3b1aa08fc5c63dd153540074bd0db1aa6a808e1fa1b7154d5012e2e318e2a9aa00187e86dd543540ad2bb07baa86a80061f2197550d503de2e31aeaa1aa0108de87d8d43540018beebb1a86a8042a7a136350d505c70e2a6c6a1aa08287f8754f62540078b8e6a9ec4a800a1f21571d89500046fc1ae3b12a0038dc835c762540019c8c438ac4a82061fa1f63549500962e39ec6a92a02387e86dc552540090f90a3b264a80031794c764c95000c3f436ea992a00187c865d532540092b90ea9a64a8003171d9534c9500047bc3ac230aa09ea778558461540015c904b08c2a80031714d73185500051f424a630aa000a3d8494c61540470f90ea98c2a808e1f21d52185500053bc0aa430aa000a748154861540014eb0b908c2a8003395c8211855015e2f31ae728aa012c5c73d8e515400f0fb0fb0ca2a815e9da1b61945500063b390c328aa000c7472186515413dce4e030ca2a80039c18570945500543f438c2a8aa0008bf845da315402117908bb462a80422fa10768c5500045ec20ed18aa00187e86dd631540578b8c7bac62a80061f219758c5500062ebaec718aa00487c851d931540030fd0dbaa62a80061f219754c55000c3f436eb10aa01295e83dd621540012bb07bac42a80061f21975885500067210cec90aa00487c851d921540019c8423b242a80061fa1b754855000c3e432ea90aa012a5e8399363540250fb0e326c6a80030f5d064d8d500952f418c9b1aa000a5d868cb635400127f08b8ec6a815a4f21171d8d50004b7c12e3b1aa01196c825c763540018b8c7ba2c6a80030fdd26458d500952f41cc8b1aa00087e8719163540254bd0db1ac6a804b17ddb6358d500062e318e2b1aa0b7e5863dc16354001ab6c7b82c6a82df5618f7058d505bead996e0b1aa00097980dd943540018b8c6bb286a80025be097650d5008cb6412eca1aa000977815d943540012e902bb286a80025ee017650d502b4af43ec6a1aa000c5f76d8d43540ad63d09b1a86a8003871936350d500043f436e2a1aa00087d86dc543540232dd05b8a86a80025b60b
  | 11 => 0x4840147d09318ca908028f612631952100536c14c632a426aa758198c6548401ac842b80ca90af79908660195210052f418c032a4200a5d831806548565cc842300ca908031e5c0601952138f32108cbb1a420087f855d363484090f90aba6c690803590877558d210043f43ecab1a420087e8719563484d5cc84232ac6908121fa1f7558d210043ec06eab1a420087f855d953484070fd0fb2aa69080e97a0f6554d210243f42eeca1a420087d85dd943484011db05bb286908021fe157650d210243e42aeca1a42008fb805d943484031f100bb286908038710f6550d210846f43ec6a1a4210a9e84d8d43484050ff0eb2ca290af39908676945210043fc3ac728a422987c865c25148401ac842b84a2908a71e181709452115636396caa8a42bbe6421d8c51484010ff0eb18a290aeb99085631452111c3e432e028a4200d64215c051484478f0c0b80a29080a37e1d638c5211243f436ea98a4200d6421dd5314844b0fd0fb2a62908aa1f21f654c521156b338ecb10a4224d667119621484071df0eb1c42908929ba1a5188521156b338ca310a422aa6e861462148449acce228c429080a3b21970885210c674302e110a4200a7980dd760484014f3003aec0908021fe1573d81210243e42ae7b02420087e8794760484014f30128ec0908021fa1c51d81210053cc00a3b02422a87c86dd56048401ac843baac0908021fa1f65581210062e39ecab02420087e8719560484018b8e632ac090ae71ddc465581210062fb2ee6b024200c5c65dcd6048401b8843b9ac0908121fa1b7150f500043ec36e2a1ea01396e82dc543d40012db05b8a87a80021fa07764cb500062e18eec996a000c6c21dd932d40018be61bb265a8003174c3764cb5000637906ec996a000c6d20dd932d40010ff0cba265a80121f219744cb5009cae43a86996a033c5c7650d32d40bfa38e8a1a65a804ed3209434cb500243f436e2996a00087d86dc532d40bf27d09b8a65a80024f613714cb503c53b40ee730ea000c5f739ce61d400147d0839cc3a80028f61073987500062eb98e730ea022a76811ce61d40010fd0f21cc3a80021f61e43987500070ea188730ea000a5e83dca61d40014bb07b94c3a81de9da0772987500052f41ce530ea000a5d839ca61d40354ed02394c3a80021fe1d32987500043e43a6530ea000a77814ca61d40014e902994c3a80021fa1c32987500043ec386530ea000a3e840ca61d400147b08194c3a807a1f61f31987500051f4266330ea000a3d84cc661d40014dd0598cc3a80029b60b31987500bc3ec3e4330ea000a5e83c8661d40014bb0790cc3a80021fe19748c7500243e432e918ea05f95f8750e31d40bfa3ce8a1c63a804e57e1d328c7500052fc326518ea000e573198631d40018b863bb263a800317cc3764c7500062e986ec
  | 12 => 0x8029e60375d81310053cc00ebb02620087f855d3604c4090f90aba6c0988021fe1572d81310243e42ae5b02620087e87947604c4014f30128ec0988021fa1c51d81310053cc00a3b02622b87c86dd5604c4010fd0fb2ac0988030f1d3655813100636396cab02620087e87195604c401878e832ac0988031b1c865581310061fb2ee8b026200c3c65dd1604c4018decbb92c0988031b19772581310064f3a4e7b2c42038df875cf658840193ce8b9ecb10803275d173d96210062f28ae7b2c4200c5c515cf65884018bea0b9ecb10803355ce71d962160672b94e3b2c4200a5e83dd5658840147d0929acb1080317dce535962100536c14a6b2c420487f875d763884010ff00baec7108030f9d674d8e210061ebace9b1c42108bf875d3638840187ceaba6c7108030f5d574d8e210065aba4e3b1c42bfce5729c7638842117d09baac7108022f6137558e210243f42ee8b1c420087d85dd163884014bd0bb9ac710802a7a137358e215f56b40ee6b1c4200c5f75d4d63884014bd0ba1ac7108021f6167654e210845f424eca9c42008bd849d953884011bb073b2a71080e1fa1f6554e211b51f426caa9c4203a5e83d9553884090fd0bbb287108021f6177650e210064e21eeca1c420487e859d943884010fb0b3b287108023760e7650e210064e21aeca1c42108de87d8d43884674bd0bb1a8710842a7a136350e2143637bb6ea9944282c6f761d5328840159f0ca1a65108723b61b714ca21004d6c26e2994422aa748159651884010fd0fb1ca3108121f61f63946212551f426c728c4200a3d84d8e51884012df0e994a3108ae9be1932946210243f43ec628c420087d87d8c518849347d09b18a3108028f6136314621004b7c3a6428c4225a6f864c851884478f0c0b80a31098f5a8817014621014e7c3a6518c4203acf864ca318840178f0299463108121fa1773582210043ec2ee6b044200a3e8494f654840147b0929eca90803175ce53d95210051f424c7b2a4200a3d8498f6548401ac842b86ca9085e1f61c60d95210052f418c1b2a4200a5d8318365484018f2e0306ca9080317dce73d95210051f420e7b2a4200a3d841cf65484018bae639eca908021fa1e43d95210043ec3c87b2a422a87e87cc765484010fb0f98eca908028fa1331d95210051ec2663b2a422aa6e82cc765484014db0598eca9080297a0c70d95210052ec18e1b2a422aa6e821c365484014db04386ca908029da0470d95211553ac08e1b2a420087e878c365484010fb0f186ca908021fa1c30d95210043ec3861b2a4200a3e840c3654840147b08186ca908aa9ba0830d952100536c1061b2a4200a76810c365484014eb02186ca908aa1fa1e10d95210043ec3c21b2a420087e87043654842f0fb0e086ca9080297a0c10d95210052ec1821b2a422aa6e8204365
  | 13 => 0x61eba4a9b2a6200a5d83953654c4014bb07286ca988029ba0a64d953100536c14c9b2a6200a3e8498b654c40147b09316ca9887a1f61c60d95310051f420c1b2a6200a3d84183654c4014dd04306ca988029b60860d95310063cb80c1b2a6200c3f749d3654c40187ae83a6ca988ae97a0c74d95310052ec18e9b2a6200a3e84dcb654c40147b09b96ca988029760f72d953115d3ac0ee5b2a6200a3e849cb654c40147b09396ca988ae97a0e72d95310052ec1ce5b2a620087e8710b654c4010fb0e216ca988ae97a0c42d95310052ec1885b2a622b87e87d07654c4010fb0fa0eca988ae97a0f41d95310052ec1e83b2a6200a6e82d07654c4014db05a0eca988ae1fa1f21d95310043ec3e43b2a6200a3e84c87654c40147b0990eca988ae97a0f21d95310052ec1e43b2a6200a3e841c3654c40147b08386ca988ae97a0c70d95310052ec18e1b2a6200a6e821c3654c4014db04386ca988029da0470d953115d3ac08e1b2a620087e87903654c4010fb0f206ca988021fa1c40d95310043ec3881b2a622ba5e83103654c4014bb06206ca988029ba0840d953100536c1081b2a6200a7681103654c4014eb02206ca988021fa1e20d95310043ec3c41b2a620087e87083654c4010fb0e106ca988028fa1020d95310051ec2041b2a622ba5e83083654c4014bb06106ca988029da0420d95310053ac0841b2a622b87e87843654c4010fb0f086ca988021fa1c10d95310f43ec3821b2a6200a3e84043654c40147b08086ca988ae97a0c10d95310053741021b2a6200a6d82043654c4014bb07320ca988029ba0a641953100536c14c832a6200a3e84988654c40147b09310ca988029760e62195310051f420c032a6200a3d84180654c4014dd04300ca988029b60860195310063cb80c032a620087e87d95644c4010fd0e32ac8988121fa1f75591310043ec06eab22620087f855d9544c4210fd0fb2aa8988428fa1365551310043f43ecab12620087e87195624c42117d093b2a4988022f61276549310143f43ecaa92622bc5c73d95524c4018becbb9aa49880e3da1b71549310063bb28e2a92620487e85dd9424c4010fb0bbb284988023760f76509310243f42ceca12620087d859d9424c4090f90a3b284988021fa1b75509310043f43ecaa12620087c87d95424c40517d0fb2284988423ba1f625093101c7b436e2a12620387f87596514c583ca8633b4a2988021fe1d649453114c3e432e128a6200d54315c2514c4538f0c0b84a2988af171cf65545310062fb2ee6a8a620087f87590514c44b4eb03b10a29888e1f219701453111e3c302e028a624987e87d95414c4570f90fb2a82988af95d87658c5310846fc3ac918a6225a5e86946314c457aace328c62988af95d86518c53115d2f430a318a62038dc865c2314c43f9b0c0b846298
  | 14 => 0xc855cb60544014f30128ec0a88025da077250c51004bac0ee4a18a22496e82dc543144012db05b8a8628803170c7764c8510063610eec990a20087d80dd932144018be61bb264288031bc83764c8510043fc32e8990a20487c865d132144492b90ea1a64288cf171d9434c85124e8e3a286990a224b4c8250d321449327d09b8a64288024f613714c8510051f424e6b00a200a3d849cd60144018bee739ac02883e9e60273580512f53dc02e6b00a200c5d731cd60144014ed0239ac02888e9d60473580510043f43c86b00a20087d8790d6014401c3a8621ac02888e9ea0043580510053cc0086b00a20ca79809c960144014bf06b92c0288029720d72580510053a40ae4b00a25da7b805c960144014bd06392c0288029760c72580510053b408e4b00a223a75811c960144014ed03992c0288029d607325805111d3d40464b00a200a79808c960144010ff0e992c0288021f21d32580510043f43864b00a20087d870c9601440147d08192c0288028f610325805111d3d40064b00a200a79800c9601440f4f30138ac028b139c042715805111c3f43e62b00a20087d87cc5601440147d0998ac0288028f61331580510053741662b00a200a6d82cc560144474f50198ac0288029e603315805111c3f43e42b00a20087d87c8560144014bd0790ac0288029760f215805111d3d40642b00a200a7980c856014561ce02190ac02888e9ea0021580510053cc0042b00a295e6a20085601452bce02010ac0288030f5d254d963115d2f41ca9b2c6200a5d83949658c4090fd0fbaac91880317a0f75592310062ec1eeab246200c5f32dd5648c44b0fd03baac9188021f603755923161d5b40ee8b2462028ee829d9548c4011db053b2a9188021fe1576552310843e43acaaa462048bc87591548c42153f0cb2287189d2c72156450e3133c6ec36e2a1c62009cd82dc5438c42193ce8a1ac51880a1fa1f6554a3101c7ac30e2a946200c77651c5528c4010ff0abb285188121f2157650a310064fbb286a146274d1c7550d428c4073ad07b8a851880e3d6187150a31006caa18e2a146283c5f76dd5328c5038beec3aa651880a37a1f654ca310146f43ec89946202ace82d91328c4014bf0ab22651885a3761b714ca31004cec26e29946200d5775dc5328c4574e902b2ca3188031759573946316143fc3ac928c622b87c87592518c4578beecb9ca31892a97e1943946312570f3228728c6200b578150e518c4012bf0e994a3188aa97e193294631005abc0a6528c620087f87590518c4090f90eb20a31892697e19431463124f0f3228628c6225a7481588518c577cc842b10a31880257e1d32146311252fc326428c6271f44214c8518c42153f0ca1c831880f275d94390631005cbc0a8720c6210c9e7450d608c4090fd0bb92c1188021f617725823100
  | 15 => 0x8b1a8728803879916350e51154b7416e2a1ca20096d82dc543944018bced39ec528803479d273d8a5115cafc3ae7b14a200d1e745cf6294401a3ae8b9ec5288035598573d8a511543ec3ec7b14a200c3e74d8f62944578bce7b1ec5288021fe1d63d8a510061f3a2c7b14a22bc5e7358f6294401aace738ec528803555ce71d8a510063ab1ce3b14a2bcd66629c762944010fd0fb1ac5288af179cf6358a511543e43ac6b14a22bc5c7358d62944016cd03b12c52880317a0f764ca510062ec1eec994a200c5e43dd932944018bc65bb26528803170cb764ca510062e18eec994a200c6c21dd932944010fb01bb2652880317cc3764ca5100637906ec994a24a93e849d9329440127b093b265288025da06764ca51004bb408ec994a20087e871d932944018ed023b265288021f600764ca510043fc32e8994a20087c865d132944552bd0fb1a652880317ddb634ca51005ab40ec6994a22a95c8750d32944018beeca1a652892b471d1434ca51155a641286994a24a93e84dc5329440127b09b8a65288a61f61f63d825115e2f39ec7b04a22bc5c7358f609440147d0831ec1288028f61063d82510062eb98c7b04a22987d87d8b60944014bd07b16c1288029760f62d82510052f41cc5b04a200a5d8398b60944534f500316c1288a61fa1e63582510062fb9cc6b04a229a7a8098d60944530f90eb1ac1288af171cd63582510051f420c6b04a200a3d8418d60944014ed0231ac12880297a0f62582510052ec1ec4b04a22987e8798960944014bd07312c1288029760e625825114d3d404c4b04a22987c8758960944014ed02312c12880317dce73582510053cc04e6b04a200a3f845cd609440147908b9ac1288029ee0173582510051f420e6b04a200a3d841cd60944018bae639ac1288029da04735825114d3ac08e6b04a20087e8790d60944010fb0f21ac1288038750c43582510052f41ce4b04a200a5d839c960944014f301392c1288029ee0172582510053b408e4b04a229a75811c960944010ff0e992c1288021f21d32582510043f43864b04a20087d870c9609440147d08192c1288028f610325825114d3d40064b04a200a79800c960944530fd0f98ac1288021f61f31582510051f42662b04a200a3d84cc560944014dd0598ac1288029b60b315825114d3d40662b04a200a7980cc560944530fd0f90ac1288021f61f21582510052f41e42b04a200a5d83c8560944534f50190ac1288029e60321582510052ec2c61b1aa20087d85dd943544051dd05bb286a88023b60b7650d510846f43ec6a1aa210a9e84d8d43544010fb0bbb264a88422fa13764c9510045ec26ec992a286c5c63dd532545078d8c5baa64a880a37a1f634c9510062fbaec6992a2038ee87d8932544090f90cb84a2a88a71e181709455100c3e42ae7b02a20187
  | 16 => 0x550d3240e2e3b0caa1a6400e1c64195434c903a98e432a8699042a7a1b6450d320070e32ec8a1a64029ce87dc9434c8053990438a869900a7320b7050d321743ec3ecbb0a6400c3e74d97614c8014ed03b2ec2990030f9d065d85320053b408cbb0a6400c3f655d3614c801878caba6c299003175ce75d853200636b94ebb0a640487f875d7614c8018bae6baec2990031b5c975d85320043fc02ebb0a6400c3e759d3614c80187aeb3a6c299003275ce74d853200656b94e9b0a64108bf875d3614c80187ceaba6c2990030f5d574d85320064eb9ae9b0a6400cad725d3614c80193862ba6c2990032b08574d85320064f982e9b0a6400caf205d3614c80156b08086c299002b560c10d853200572c1021b0a6400c3e74d96614c80187ce832cc29931f175cc65985320061fb2ae930a6400c3c655d2614c80196ae9b0cc2990021fa1f65585320043f438cab0a64008f787584614c8014ed03ba8c2990029da0475185320043fc2ae830a640487c855d0614c821938e8a18c2990021fe1570185320243e42ae030a64008bf845c0614c82117908b80c299002ad61010185320056ac182030a6400ae582040614c8014f301baec0990029e60075d81320043fc2ae9b02640487c855d3604c821938e8a1ec0990121fa1671d81320043ec2ce3b0264108be849c7604c80117b0938ec09900637a0e71d813200c77414e3b02640087f855c7604c8090f90ab8ec09920e1f21b75581320043f43ecab026400c3c74d95604c8010fd0e32ac0990030f1d065581326362fb98cab026400c3f65dd1604c801878cbba2c0990031dd9771581320063a32ee2b026400c77651c5604c8018e8ca38ac0990021fa1e5458e5115d2f41ca8b1ca200a5d858c9639451f8bcc7ba2a72880e97e196354e510f43ec36e2a9ca27897687dc553944298bcc7b82a72892a5760f7550e51004bac0eeaa1ca27bc5e635d543944211b90eb1a872880317dd56350e510854e422c6a1ca2c5e1c5458d43945050f90ea9ac52880f179cd5358a5140c3e43ac6a94a22bc5c7358d529442f0fb0db8aa5289de5da1f7154a510062f29eec994a20495c8754d32944018beeca9a652880297e0d75582510052e41aeab04a200a6f825d560944014d904baac1288031714f73582510051f424a6b04a200a3d8494d60944014eb0329ac1288031798d74d8e510061eba0c9b1ca22ba5e83193639444b8bcc738ec728b079598e71d8e5160eab31ce3b1ca2c1d57329c763944018bcc6b86c7288ae1fa1e6458e510061fba4c8b1ca22ba5e8399163944010fd0e322c7288ae97a0c6458e5115e2fbb6c6b1ca200b5681d8d63944014bd0d192c7288031798e7650e51154b7414eca1ca20096d829d943944012ed033b287288025da047650e51254ae43ac6a1ca200c5c7658d43944956390
  | 17 => 0xa8600c6e759cb6150c018daeb396c2a1803335ce72d854301477c3ae5b0a8600c6e755cb6150c018daeab96c2a1803335cd72d85430066618ae5b0a8600ccf305cb6150c01a3887baac2a18023de1d611854361f4a21ac230a860087f855c86150c090f90ab90c2a18021fe1572d81430243e42ae5b02860087f855c76050c090f90ab8ec0a1b2e1fe1574d8d520052ec2c61b1aa4ca87e86dd153548011ed03bb286a90023d6077650d520143e432eaa1aa4108de87d8d435482153d09b1a86a90029d61410d85520056ac1821b0aa400ae58204361548019aae7b0cc2a90023de1d61185525e53bc2ac230aa48387f855cc61548490f90ea98c2a900237e0d701855201c6e41ae030aa400a758584061548015ab06080c2a9002b9608101855241c3fc2ae7b02a41387c8754f60548030fd0b38ec0a900e37a0e71d81520046ec1ce3b02a40187c855c7605480187ae92a6ca990029760e54d95320052ec1ca1b2a6400a7681993654c8014eb03326ca990035908671d95321743ec38c1b2a6400a3e84183654c80147b08306ca990029da0460d95320053ac08c1b2a6400c7970183654c80187ee93a6ca990030f5d074d95324352f418e9b2a6483a5d831d3654c80147d09b8eca990028f61371d953241d2ec1ee3b2a6486a6d82dc7654c8018ee4338eca990031d08671d95320043ec04e3b2a640087e87d07654c8010fb0fa0eca9921a97a0f41d95320052ec1e83b2a6483a6e82d07654c8014db05a0eca990021f20570d95320051f420e1b2a6400a3d841c3654c90d4bd06386ca9920e9760c70d953241d37410e1b2a6486a6d821c3654c8014ed02386ca990029d60470d95320043f43c81b2a640087d87903654c8010fd0e206ca990021f61c40d95324352f41881b2a6400a5d83103654c9074dd04206ca990029b60840d95320053b40881b2a6400a7581103654c8010fd0f086ca990021f61e10d95320043f43821b2a640087d87043654c80147d08086ca990028f61010d95324352f41821b2a6400a5d83043654c9074dd04086ca990029b60810d953264e2fbaee6b2a64c8a5d83990654c8014ed03320ca990029d60664195320051f420c032a6400a3d84180654c8014ed02300ca990029d60460195320063cb80c032a6482c5c73197644c8010ff0ab8ec8990121f21571d91320067210ae3b22640087e87d95644c8010fd0e32ac8990121fa1f75591320043f40eeab22640087d80dd5644c8090fd0bb8ac8990021f61771591320043fc2aecaa26400c5e531d9544c8210fd0fb2aa8990428fa13655513241e2e3b6caa9a640395d85dd1534c8f5a3ca9ba2a6990cf171977550d3201ccec26eaa1a6479d1f54dd5434c8051b90cbaa869900a732097550d324152f436caa1a6483c5c76d95434c801c38c9b2a869920f531cb6
  | 18 => 0x900380e00000180000180080000700101700701080800500100000200281380280000280200080600500580081d80e00400000e80000100100480600000100000080180180000300380080000180180280181b00000880280200280900000000100680000100400100780080900a00000100200080880000001000000080000000100500400000280000300000000280000000382100680800200500300100080180800300a00300000580280080480880100080000100001101780900000001d00600080380180080000000100000101d80000700880500000182a00580900280b00000000300000680000600000480100080300300180200380100d00200200100180400900000a00480000c00101500100280280380f80280280001d80000100b80101f82800300e00000280700480000000580000500280f80100680080380600800000400000100580180300000800180280e80100300000100002980100300000600300180600180080a00180400100081700280000001580580000000000000180000101580080000600300680000001400580380000180500000800080000301780802280c00401402800080400180000880000a80481800480000100780000980380000480100000480001000000200200280480080280200200000002680400180681780000b80900800100180280b00080500201f80080500080901301b00000200700280180280300a00000500200080000200300000080080200680080400100100000380200380000080580180180000001700400b80180300180280280080000181600900701080000080400600000780100180000480500000100000500480080700101400080080e00001180080180380000480b80000780180180480380280000300280101701980400700081c00000200200100080d80180080100000000c80980280780080580900000880000080102980000e80780a80080000080100000000100100080300000380280000001280200100080f80800180100080700000780001380b00000000000080c80300280080080200000200080080000800580000000380380680000080100900080500200800280100180780080280200580100000580300b00380380080100100100100100000380000101880000080000200080280300400580500301081a0030008008000038020020031d14671d89530047bc3ac230aa6c1a77855846154c01878a8ba0c2a989697a0e54185534343fc2ae430aa600c3c545d36054c294bd072a6c0a9a1a1fe1572d81530052ec1ca5b2a8600c6d7294b6550d998beebb9acaa18021fe1571d89430243e42ae3b128600cd4315c76250c01a3887baac4a18034710d75d8543006c621ae5b0a8600c5d739d76150c090ff0ebaec2a1803175cd75d85430043fc02ebb
  | 19 => 0x3400000000011c8f1800013d00d07fa3b8227000090e8e63ca80011985c98e4a014d0634138ea5d800076a0f0932d2dc2409050e441d986f8af852c5ba6961a224fca3c77a0470d94a0469b16e11209d61da044c0cccf519c80610446225aa4df044d0848b819f80003263100d70e5c00061847896609029523cfa16c89612cc4516c4aad6100000b490640002a94fe40001f40000860d071463208f650ee2ee3a98c90e9a0672bf9ba521c93632d99ac25563a3060bfc0484204600d24d6e3641680470ed85d80d5a28839449b203861c9ee3e71650f3cf8599236b86bd1c0601bbd998e74603695225e04281f51a5119013533917a978cf4224a4030c0d1390fa01693c02dc1680a7991510036647d20a901425c0aca5f106a09834887f03f29102cd8a549282112f80ae53589470c121c30284533648d143d81569ed2550d6c0a01a3916849a9c628b84f4de13d01ebcf772522ac23800000007fc3c1000067a0002bd931cd2a8a04d08000bc85be2dd85a28be25e2cb60068385f800002c45c221a2d20000f660003a526f064c0001cd849c0ba55f89a4a640002a941882cc6d89c23af05c421c0d401d81fa1380000f49ab84fa1cc48b0000000875000000000084f800000084a5974db8da086f2aa32b98246784cc1f05bad1b42c22ca01c425407500080500181c80880100580000300000800780000000a00181481780000080300180480000100280180180100000080900000000300080600a00180600480200080000000000100400400100901a00000082080300100000000080180800780680100000180000580980380080000200000080200500380080a80000000580000200000b00300080582180180780000580080200080000080001e00080100100400100180200180b80b80280180000080481180280181500380d00000000000180000600080100000700080500800300780880080300000780080a80000000000600380200080000080000181080300000000100100000100000100100180200c00180080280180000580000280100100000d01b80500000f01680180100800580080300c80080480a00780500b00000200001080000000900500280d00200080000200100080880880001b00600080000500780001080081c80581d81281500700281280280000200b80000101400000c81b80000d80080c80380080580280880000080300000000180d80b80000a00000a80380780f00000c80000000000480780900000000283300200d01680000001580880a00000100080300b00b80081500280580900180000000380101a80080900000a00a80601400080380180000180300680a80781300100100700000800000000e00200400900000300d80b80080280580300000402100d80080000500b8028028010068010138020
  | 20 => 0xa242491148c491433b8a1420887c1361bb457892c41b66800000003f9800109048327c0dc516837639a19f801c3482288c946d575a3149b503c88b008ae36ca2649f47c85282c43a82e5d524492586304238c0e393515d8fecd963363c4a3e049e68b4a309405fc1a61b752485892d32d988086de8811f19f590c171442c8480e826ad1ab24c0e861f837100005228e900019080004462361f300006f1323a0880000c549a01369e400048e0d4014e6be27a64ec6045583f0c24935c72a1e90228f567b814303e0e002ae0e99f9c39c00013d80000004354221e76eae5200a1242884e91541d2160f9208c3cba0593810000ec8000fc2166b440eb10aa6cc8ca14568bc2714324994aac82446aa3780d0150bb791f439a4f918e1438f8d7d42e9971ce9211b3588a486b880c37d19e4aa062f0c9059928274234e2554f9e47a4bf8118f2033b25ec0000ac2be23a9aaca5638043c806c9d2000392860caa46c20f915b02450a23964000c6c1b300005fcb1a61544e8bd939e086086878008800000025080448ed0001a1400000000008b40009b148c00000003ca25f062400000025e8dfc32e4d280009d90e25290000f18cea198a64162800000012983c028656607e896659b0eaac140000009b348992263ca50d00004c0f2800015392980000001ee85309701fa091dc113aa9851f49ea497e8aa0089e7538a00011a89584ba99e2251cdc000000086d5f80006d10ec01f600071706d9a6400000006f0f5c2220e18621c7d116137cb69a9041e66f15e94f4f264a0311218c2a23344dd583900e66932504a42d66380e38b605620b84461c3c7880003f72098c929374afa6e40d94f58e8265133f36980000000003571418920b7e37d09898de4100c93998e3cfea54408015b411a1d14a280f00d753a10210b83c40001706712ef20001d288d00000003ff000047291202f892c9384d34611cd85871cf23e20dea9c0ae1885eb13000003afa69501a0fb000000058c0000cf843096c83d2c70ce800000000016984327542faa0dc00003100010c8242046bef91b4c7e5f64998e742e17ec4c209e06347c3332845ee2616bc548ae92e28ab1f4154217c38683a233252c2c50b79fc914a045c7607bcf969584138ad466426645b83580000000a68000c723c5a814ed10b809b2371c983e000000001b081e5ed00019cc0000004df93f41000000000ca4c2583035415e80009773ee0000de899a2f3a58503e2890350d50c1470930b0a4105e3d62c994bc0df5370770b64c86000000252105080900000002a03ed0714000e3404b39100011e60000630d0c0009ca00021500003c92de8bc50821fe000034121a0004e5800099200000016c00000000000d3ccdc00026c8000000000386000059e96927d0a00c0655900010252cc02b00017387d600017580
  | 21 => 0xbb2a5478a23400010f079200c843c0006f2043978809230d02e035d2ba14917c8b000003670498bbca3615e1e380005925c312300002ee4c00000d8c8923421b824c923c05407a95f13104611f78d263302ec0fb8da44a43e011d80b81d000048d99d0c805fe1101254bac30f3619528a0d00042e95504d61c800012380008ba47392820000001ca5fc434b4bb37399901de45c46f9df000000000000003227c800000005a2751000256cfa400019f0000fb430c3b00460b5822583e0b0ce9c8bd2d798c8000136000123c87400000000009840001938000e468f545f03f003e7ac8c285ec6802000001a18c685d02dc04a05308d349199b087837a84414b438699f0001d7431660626e2468d094d739c80007f0000000138c66084e86380012de7d10001fec79600045c80000000000000000ed6532093049400027921580009be4b900008cc34e0001aa8cc400000000016f139858b1f50f86dd03881440cac1b200047e000132a00028323247e625a00005a8ae43461591efc1a65cf2b088b8dfe4f40000cf20000000001d58f320000000000ade5272cf067400008480013fd33202a3c1a7480000000000ac038807d000000131c10a09b842a4c4000205169c2af7f725580000006a78000000b341f14620b044aa11d80000010be2703c3907513419921308622aa53526f014c13216796fd43caba007b450d7cf3623a00002e447e03802681e84be7e0c4321f91465ff1640000e3882311222380000410d80000d447781db1c2800067a01f2240bba698c4406a8ae6000256000041676329a24b460a00000000002cb0dd054a1c8b0437801ca42c00000000022249798a82590db6bb470b43596b49de75b2198330d9428a334188c6d64af3dc90689e244131e894444c986429047a96213f0c55f5cf622fa4229bb049c72808b9b3cdbc6f70ac1e94dac48b0c6d82d05a573bfc20b84de00a36f90647903b500f1c3446c7680d6866c780052211943f1240b604b9ec86c42e810a97106427f0278c7981427aa2621ffc3422050a900002ce7e431dd9480006b940e11a44122a619b80009220a4aed8f50d64560362d8f066a52834a224cb945471859004df290716d184cb466cd0f70efcc9e2750001b18d4e6c426d9a007346a000022100000004ddcd340003720811518000000000271a42494e3ec2658ff20000d4124c2391c244195e65023d13a297001c63f0051800c7b65774309010b952ce07117a10c4000014800000007b49f041c00039002d0ce0c5470733114170004b300018d4e70000000060432300016f99c8a20000231941446d7862f003b491559040b83205c08afc84000004a0004e7079c0261540001f54000431292a6f20006980000000c2200020a1a1c0020000000000be43fa05ba1a11b30003490300f7c67618e93b0e7c2
  | 22 => 0x508b2f00008241d63ef0668c5081e4571bd87b06901ef15f41580f941f0d84098548abb12740422cd478199cd1a63307f1a7c9440004361380d3c1e82841bf405821f00009840000c3091a2980c87af03c95acf8e33bc7584582ea0ff3b72278ba46d205e14b8d18987271033929e3f631b833523a1b84e39e802760002200a70fca42d29822f12d49d323f00000004363829d106f40654689a5e6e6808000018c0006f54d3a08e406000437a06071c00007b8574b6801535e97840005ba371a128b9b7840fe856806a000000000100481942b1cc86140002cc80000000510000d30b0e9b84889cd40000620001b6c000000000000008475c2d591d88a085a01f88ae00022b0ba07740004f280024e455600039024052b41530001c480002ea1ae97780008ca0cece4885803a25a01c2a8466612385e40004ca3b900000007480001b6400027246e40012a63f209f18562660000001400f8a9a080008188100bd175c63c23a90f000269e34032c120139800086e800000037c0003b81bb832086d14fa17800004a1dc9c40eca0001be152cf765fa492800000000025d1a680b2000000000118e0002069750e2249e184800104080b2f8a194e8e29323ba62c5f89404200000c3e7db026505c81c2b44d80000b351b614d24302ec18005695260003c12dc8f0c15360727411a8f558c51729e2c2f05cc4ec0000c4a0002411e04c020d5472808113b11e2c90a5cbe88344950b984880700df817854a62638702048884aa25811eabe65160e59ede31a01a3d408889009241f095785ee7664d10c00ab80eb83c5ed8b1810600023c800043f000196805044d46417046f25fb2062338bd8871c29899c1680e9442a038b089a6095839d182250a441950bfa70809ad1c45ae43808498ec21786938c1cbc42c09515419110768b138b05b51c82d42b513f0a4637538c96d425a25195b1d9c6509c31c326349f62133654000e9e1f34c10a2c63e2ed1ee214469c49a0398402fba86644a8000c566bc00024c4e98131bfe58103640002cac00044e4660000abc0009a306f62d432c84b43e98b47be56317a1880ea441514d8000000486030a5e400000000008700007730002264dde8251999934063000395a6ac000000114800000053f09903b038a12c00017dc23264c0a7146013d572ce426a0b645242ec9d003c63743cb21812423fc2a1a7248e67a2000019874c56500012b92f6521419a270de010b0890000cf836d0728d48e026ba4b600000006b034218c50e04792239c907761a900000d92b216303b09a0b1209ba1a1a9a000457370000000000000014451ba09438d800083012f80000010f428e0429df40001bd1f325f52d616408a934e6fc1600e301f8abe13413f8f9000000000017a49ca97a43d931423439921f215c91249704d00213063a01c60
  | 23 => 0x1ab000054d0001f34f5a5d7842dbd68d66af2421ef00005c20b2400059687441600006057061319b94f6e4c1cc804b8f1c3892110000db489b0bf26aaa661eb13b85a725e3d505f9304fc40e13960ee82ac54035fa2d8eee00888a23191b800026193a8d6a58805a830520684d1c39b74df69680270210bd614729b19c00a071e0ab80bca1484e01300240384052b384e80ae00047a206c37646f4970afcf5c00022e9a04e7e00000000009202310a213ba72c938003800002e762335200c51f8e224608c653a84f0489ec0000237a541f3e3d459c2568d6ca316e62059bf095286e4832660eec4a10b60c491d43cd3e995200009a9000000087238420d9426e9600041fa3fc000000000265e0002f22b2402c00032323dd00c46e53804187500007d91fa0fc47425074158b9cbaa0002db80011730004d78dec7640f630e1acc0009513411a5c71d014000109106c00047083c40b000000b1ff40000454099e9908682fa8924ac00c3ec0000000cfe72118981202200002d70000e520001425df885400000000000002de3da0208d4c8d8b4793d864043727716887523a23109c546540e6232a630d7062427092910985192a7985c31c6001d391fc3b85784da1a84f000004af1aa51ee75818b0ddcc6d22c947a4012e67a34ea1cc4cb299305d0ef04e80ba9840c510c383c00008a8eaa54c20012601bf00047a5d905fb8d8284970a0009d707a0000fd01d54008000ad243d2cfa0a51f636022120109fc8980000000000000338a3f447a0003da8360d983ff3fd105831f0003b68a1c0000000fd92c73957692fc83280608f62a280092c661d4ba82ad0fe15b0ef8bfb020821245083456e2430e08b58db826d4b0236a91a6303551a950c73c20be908479c8bb224dbe08a420700000013a05fec931c0c5b677131709cd0015e518a9b146b430190e91eccc09193cd1f2820a3988659ce920a3b010d96d914254114a140cd3a98f49d083045899880026911fc4060e002c0a3a9a5b0d935000000000022bc77a139a3c0da80000003a8156c4c89973f19cc094e319000248103a000000000060e9b20b9219c30c7bd08181dc71a9b62c1a5d000015c0000e90b4a4b72b805cceb200016217b800087346c9b409b400024280c80da60d000003c1c80004dd96048ce0002010d223a49672ab94f00005962a9a2346a24a30001e7000006b000107c0000004ae273eee82b30001ad00009ad06f84e0000458126000075e4d0117800044958544b8488ad05a83d206911dc5df4a59f4028a9cd0578e4ca342fb0dc800120891f00026443fe5910ef0eb455a4d54e6c276fd68383138fdd2944282d0a7449ac1843fecec425e25814f22bb1a822800006dd35408f17c13b658e8a70eb80000000d22768000c966fe3368001122456000000073894d44dc00072a
  | 24 => 0x245c696653456a51092c8bf4778cbc2ca26a1712530cb019e16aa2d2a628e830a14880e40dc03cdf1826a7a732b0000fec0ff93e1344a198d604599ef0a032e0d1197d2a03ab2a9c420c27557b16145102227e18090a40001612ce83a89c860f1f11cb40f00e046b963c06e66108f876d2ac8cb1118e611970004091724000221000000113e0eb3cf0b8ca9f00038124a021d00001e9b4cfda9ba0000e0cf105018000154a4c151a8a5a4c36a118a8089b8f304b09e980001b40000000d640008cd2d4956903453942300000000004b2165538063e0520d7804600049e000099a000000185ae5c6890bd0000adc09e1780db80007c43b0a5f84b5785120d7a80004c091940000005dc037000110e00041c94b048a99d22d890414c5752f780001203de8809430d9028c0000f309a43d88349954ca01411210eb80000cf3e08e780001ba1518000e7661e1410e2800004f1c09bcc3182e4423800077c23c80000000000000001f00ac46eebfa14f924e000002800119e53b000034459831190087d80007a48f6811cd9c6d844a1dfc7043f54c500003105e63f51b5434f9bd0000c38000000000050000000400000000004100b8000112c000000229099c158c561554c0568e31ccff8cf69620001918540000217a30cae2000302a2cc9e699da8223488874b522780000002173e1018098c00022a0000000000119159600060209c9938d800002e8a4f4000000130013a1500001e2800016400027380005e69d605dc1fcf2239f013a1a800000000e8f9412c0000001714630579000000000023c2ba00009b019520f00008861bc4a49ba80006481d9806000028d92c885b0c87ba4b2994511e65d3e709502780004910c6c0000404cd9aec3148154a183c80004cf0002710f777e90da08c0a2a902182145e4702fd11f02a80009090001294cfa06f2181a8c7545c823a0cb4cc6000370a604b876c118b889441c7e00d2800131209d000028e71643b372027c0009c122a800082600000026d501e61a000096c2900894ce1c9c9327ef0000a0a338746079884000005b17493d52e42b80000000c3200000022092e05c636384900240bb28e172cbae00028597f0ac86120d1947c8980002e686b09ba65c4680edc3628a690f1164cf02840b4a2c8f1e3530219cf08c00a51468d60f1a2571f70f52e7a00018300412ae8761ca09a454231e1911544b405803f312f02f80000000000eea000285c00070a0c2000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x120c002a000a4a00889226217038003a7a009e008668421a9c94906a0050bc748c403b8e587d982800662000711b6c467e105ab08018b24e52be0000722e06224800acae04625e30826008449a1e9600818a320064ba021c846536aab65ca82414162c6e1f56a400007fa200007c00762d004c00b8780e0000a0a654343cb7b43e0c0014010403230f1a1501070118192a071200000000071000010405311a00020018010040fe61741d3654c80141d9494f764ca5100417a5e868c9639440184e8298e7650e5100417a607658d439440141d94a0f764ca510041766243dd9329440105d980cb764ca510050765032dd9329440184c82dd9434ca5100417e61731cd609440105f985cc73580510068650d8010d601440105e97e15644ca3100651087874c8518c40103f985d074d95310042766043dd9438840148d9210f7650e2100417e61731cf654840156190085701952100691085831806548401c60215c060195214ae19218215c051484015619008570145214af18180215c0514840105f985cc739875000515a5c3198531d400141d9494c764c95000538640211d9215400105f9761a32d8d5000613208635d94354001854632057650d500041766376d8d435400145593188715895000507652831d9325400105d9890c764c95000417660321d9325400141d940c8764c950006132087650d3254001645931882118550006585c9800846154001a6062600211855000417e61731cc615400126692e05431855000685a1283c84615400164593a08211855000698a0980084615400105f985db638c5500059864021dd9215400156190086764855000558640211d921540016619008476485500051a640211d9215400147190084764855000718a40211d9215400146590084764855000718640211d9215400146190084764855000519245201d9215400146492c40764855000519249101d92154001c6120440764855000619a0476885215400105c97617644c93000417a60765ce514c0014e19008476485300051564c521c565480014959418c7158d2000427660431d9434800148d9210c7650d2000519e5d321845148001c62725c06114520007185c970184514800154993209701452011d58644825c0514812bc636218570145204af18648615c05148001c6382185701452000718208615c05148001c62321857014520007184c8615c0514812346a96c8570145200055264f215c05148001c6061c85701452059619a1c6194521480478687660051485200069818580145214800105f985cc73d971048d1ca47625c051c40014569718f654c71000619a1c21d9521c40018668718b65487100059864062d9521c412f87376600654871000525a44431d9434400186462a07754c910
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x14005b94d20cc2800089306058c01520d0042c18c032a4200a186a0215c060195214ae0c10cc8042b80a290802a41a3189800846154001520d1d04c004230aa000a18682811da214855048c8c352410c2b80a290002c41a3208615c05148001a20c98c390ae028a4000c18a1d9018b6548710
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x6
  | 5 => 0x94b
  | 6 => 0x94c
  | 7 => 0x94e
  | 8 => 0x138b
  | 9 => 0x138c
  | 10 => 0x138e
  | 11 => 0x98c
  | 12 => 0x98e
  | 13 => 0x9cb
  | 14 => 0x9cd
  | 15 => 0x9ce
  | 16 => 0x5
  | 17 => 0xa4b
  | 18 => 0xa4c
  | 19 => 0x198b
  | 20 => 0x198c
  | 21 => 0xb09
  | 22 => 0xb0c
  | 23 => 0xb0e
  | 24 => 0x1409
  | 25 => 0x140c
  | 26 => 0x140e
  | 27 => 0xb49
  | 28 => 0xb4b
  | 29 => 0xb4d
  | 30 => 0xb4e
  | 31 => 0x1449
  | 32 => 0x144b
  | 33 => 0x144d
  | 34 => 0x144e
  | 35 => 0x2c9
  | 36 => 0x2cb
  | 37 => 0x2cc
  | 38 => 0xbc9
  | 39 => 0xbcb
  | 40 => 0xbcc
  | 41 => 0x14c9
  | 42 => 0x14cb
  | 43 => 0x14cc
  | 44 => 0xcc9
  | 45 => 0xccd
  | 46 => 0xcce
  | 47 => 0xd49
  | 48 => 0xd4c
  | 49 => 0xe89
  | 50 => 0xe8b
  | 51 => 0xe8e
  | 52 => 0xec9
  | 53 => 0xecb
  | 54 => 0xecd
  | 55 => 0x124b
  | 56 => 0x209
  | 57 => 0x124c
  | 58 => 0x249
  | 59 => 0x1549
  | 60 => 0x16c9
  | 61 => 0x94d
  | 62 => 0x19c9
  | 63 => 0x4b
  | 64 => 0x4c
  | 65 => 0x1709
  | 66 => 0x15c9
  | 67 => 0x168b
  | 68 => 0x98d
  | 69 => 0x12cb
  | 70 => 0x1a09
  | 71 => 0x1649
  | 72 => 0x134b
  | 73 => 0x2cd
  | 74 => 0x14cd
  | 75 => 0x150c
  | 76 => 0x128c
  | 77 => 0xe89d6
  | 78 => 0xa0c
  | 79 => 0x18c9
  | 80 => 0x180c
  | 81 => 0x1789
  | 82 => 0x130c
  | 83 => 0x1a49
  | 84 => 0x17c9
  | 85 => 0x134c
  | 86 => 0xa4d
  | 87 => 0x4e
  | 88 => 0x124e
  | 89 => 0x128e
  | 90 => 0x449
  | 91 => 0x12ce
  | 92 => 0x5c9
  | 93 => 0x150e
  | 94 => 0x168e
  | 95 => 0x198d
  | 96 => 0x24b
  | 97 => 0x16cb
  | 98 => 0x19cb
  | 99 => 0x2d411
  | 100 => 0x14d411
  | 101 => 0x140d
  | 102 => 0xb8e
  | 103 => 0xb8c
  | 104 => 0x148e
  | 105 => 0x28c
  | 106 => 0x2cb53
  | 107 => 0xd0e
  | 108 => 0x154c
  | 109 => 0x184c
  | 110 => 0x148c
  | 111 => 0x19cc
  | 112 => 0x2d451
  | 113 => 0x2d453
  | 114 => 0x14d451
  | 115 => 0x20c
  | 116 => 0xe9456
  | 117 => 0x154e
  | 118 => 0x16ce
  | 119 => 0x20e
  | 120 => 0x24e
  | 121 => 0xe8cd6
  | 122 => 0xeccd5
  | 123 => 0x104c
  | 124 => 0xd0c
  | 125 => 0x18cb
  | 126 => 0x188c
  | 127 => 0x178b
  | 128 => 0x160c
  | 129 => 0x5cb
  | 130 => 0x44c
  | 131 => 0x17cb
  | 132 => 0x1a4b
  | 133 => 0x1a0c
  | 134 => 0x164c
  | 135 => 0x170e
  | 136 => 0x15ce
  | 137 => 0x16cd
  | 138 => 0x194c
  | 139 => 0x1a4d
  | 140 => 0x17cd
  | 141 => 0x18ce
  | 142 => 0x178e
  | 143 => 0x1a8c
  | 144 => 0x24211
  | 145 => 0x2c211
  | 146 => 0x289
  | 147 => 0x1489
  | 148 => 0x20251
  | 149 => 0x202d1
  | 150 => 0x214d1
  | 151 => 0x2d551
  | 152 => 0x1402d1
  | 153 => 0x1414d1
  | 154 => 0x254d1
  | 155 => 0x1442d1
  | 156 => 0x1454d1
  | 157 => 0x242d1
  | 158 => 0x2d4d1
  | 159 => 0x25411
  | 160 => 0x21451
  | 161 => 0x216d1
  | 162 => 0x144211
  | 163 => 0x145411
  | 164 => 0x219d1
  | 165 => 0x14c211
  | 166 => 0x25551
  | 167 => 0x28251
  | 168 => 0x29451
  | 169 => 0x24291
  | 170 => 0x148251
  | 171 => 0x149451
  | 172 => 0x2c251
  | 173 => 0x14c251
  | 174 => 0x2c053
  | 175 => 0xb0211
  | 176 => 0x1542d1
  | 177 => 0x20b11
  | 178 => 0x42d3
  | 179 => 0x21411
  | 180 => 0x25451
  | 181 => 0x1a57d1
  | 182 => 0x198a53
  | 183 => 0x198a54
  | 184 => 0x12ce96
  | 185 => 0x2d253
  | 186 => 0xb42d3
  | 187 => 0x1442d3
  | 188 => 0x2d4d3
  | 189 => 0x1242d3
  | 190 => 0xb4253
  | 191 => 0x20b14
  | 192 => 0x20b16
  | 193 => 0x2d4d4
  | 194 => 0x184e
  | 195 => 0xb8294
  | 196 => 0x14c2d1
  | 197 => 0xb4e96
  | 198 => 0x5d2d3
  | 199 => 0x5cb53
  | 200 => 0x5ce93
  | 201 => 0x1a57d3
  | 202 => 0x74b
  | 203 => 0x194b
  | 204 => 0x1a57d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1329
  | 6 => 5100
  | 5 => 2521
  | 4 => 96
  | 3 => 10
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
  | 8 => packedAt gbK8 (1369+((h/21+packedAt gbK8 (1222+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (55333+((h/560+packedAt gbK7 (49173+(h % 560)*11) 11) % 2019)*12) 12
  | 6 => packedAt gbK6 (270657+((h/1989+packedAt gbK6 (244800+(h % 1989)*13) 13) % 7162)*14) 14
  | 5 => packedAt gbK5 (159959+((h/935+packedAt gbK5 (148739+(h % 935)*12) 12) % 3367)*13) 13
  | 4 => packedAt gbK4 (7000+((h/35+packedAt gbK4 (6720+(h % 35)*8) 8) % 129)*8) 8
  | 3 => packedAt gbK3 (830+((h/4+packedAt gbK3 (810+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1ffe03fffc07ffff01fffffffd09e78f38f1ff
  | 1 => 0xe0fffc381ff83e07fe0f81c0fef69a73d74e93
  | 2 => 0xff07ffc01fffc007fff001ff03071c7ce78f1c
  | 3 => 0x7ffffe0000007fffffe0003f81f80f80fe0
  | 4 => 0x7fffffffffff80000000003ffe000fff000
  | 5 => 0xfff80000000000000000000003ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1080000200042800010a05040002085001025
  | 1 => 0x20d22c190d483413520d0482b8728a32534692
  | 2 => 0x5a0556c216968025a5a0092e0b051458a58b18
  | 3 => 0x8479b6f40c21046f9ce5c0413b81f00f80dc0
  | 4 => 0x1087e3b79be739703084100823dfc000fee000
  | 5 => 0x9ce1020403042180c1086030c3efffef000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36703
namespace PEqualNP.Outside.L_meta_36703
open PEqualNP.Outside.L_meta_36703.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 19 := block_range (n:=19) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 19 := bs0_3_0
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
theorem bs0_4_128 : Interval s0Atlas 4 128 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 144 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 20 := block_range (n:=20) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 84 := (concat bs2_3_0 (concat bs2_3_32 bs2_3_64))
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
theorem bs2_4_160 : Interval s2Atlas 4 160 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 186 := (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat bs2_4_96 (concat bs2_4_128 bs2_4_160)))
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
theorem bs4_3_0 : Interval s4Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 26 := bs4_3_0
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
theorem bs4_4_128 : Interval s4Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 134 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 68 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_128 : Interval s5Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 129 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 45 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 10 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 96 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_2496 : Interval gbAtlas 5 2496 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2521 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)))) (concat (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)))))) (concat (concat (concat (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376))) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 (concat bgb_5_1504 bgb_5_1536)))) (concat (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856))))) (concat (concat (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016))) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176)))) (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336))) (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)))))))
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
theorem bgb_6_5088 : Interval gbAtlas 6 5088 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5100 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)))))) (concat (concat (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528))))))) (concat (concat (concat (concat (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)))) (concat (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168))))) (concat (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)))) (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)))))) (concat (concat (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968))) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)))) (concat (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288))) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448))))) (concat (concat (concat (concat bgb_6_4480 bgb_6_4512) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608))) (concat (concat bgb_6_4640 bgb_6_4672) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)))) (concat (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))) (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))))))))
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
theorem bgb_7_1312 : Interval gbAtlas 7 1312 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1329 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)))) (concat (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120))) (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 47 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 26, 58)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8eeeaeae8eaeaeaa8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36703.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[3,4]⟩,⟨.or,[5,7]⟩,⟨.and,[3,6]⟩,⟨.or,[2,9]⟩,⟨.or,[7,10]⟩,⟨.and,[1,8]⟩,⟨.or,[1,11]⟩,⟨.and,[10,12]⟩,⟨.or,[0,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36703

open PEqualNP.Outside.L_meta_36703 in
theorem PEqualNP.Outside.L_meta_36703 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3941264040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
