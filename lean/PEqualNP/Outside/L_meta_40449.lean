import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40449.Model
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


end PEqualNP.Outside.L_meta_40449.Model

namespace PEqualNP.Outside.L_meta_40449
open PEqualNP.Outside.L_meta_40449.Model
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

def SBf (j : Nat) : Nat := [7, 8, 8, 6, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_40449

namespace PEqualNP.Outside.L_meta_40449
open PEqualNP.Outside.L_meta_40449.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x14f8060020004400000800900c2200300009380000001fe10ff42fd41fd40fd30fe42ff32bf41fe20dc32bc40fe32ff41fe40de32fc40fe41fe31fc41fe21ff20fe30fd42fc32be40bc42fc21ff30fc42fd43fd31fd20fd10bf43ff31fc10fd21fc43ff43bd41fd32fc20fc30bd43ff10fe43ff21be42fc31ff40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1030000000300000200002d0501848d00000000000181808181028000830300080000060080000200010003808000079d8a800080010100028000808f858100ba008001020517838081030000030015840084821b001d980000071cb00080014f94840ae29a855c534827aa2216750c319faa2413e540cb3a87195b94a319e2a2413c544427aa918db14943b7290213d5390abea6884fd5020aea98813e509027aa898e7550329e2a6435e538827ca1a0cf953319eaa4433e548833884194f14941bba8a413e544c67aa998cf552439e2a4216c524c27ea990cfd51219e2a4653f548427aa8185b149109eaa6659f5350e7ca1a1cf141439ea9e83cc32486e8a290678ca40ce190813f5150e7ea6a0cf940429f2a063cc32c8678a4a1e750d309e2a2653f548c278a8985754f42af29e839f430ca7ca5204f95010cea1865cf420cb6ea2a0cf55310e6190419e53102bca419678cb419f296833e54c827aa6215714d109f2808178504867aa810dbd49309e282835e53d0b3c64a0d714d21d621065cc328831884194754f419e2a0413d5490774a0204f5532096292873e54cca78a890d754c10cea98813e548c67aa3204fd51309ea88815f534867ca820ddd45309faa2213d5190a7ca5a1e7d5232aea9c419e428cb3865204f950219f2a6613d531023aa6205794e21d621665ac5250e7aa818ded4121afa9a419e53d067ca910e7908329f284853d51d0f3a8798670cb41af29465af5250edaa518d7d4d42cea1c639c428ca7ca4214f54e40b6a90213c548c27aa9105bd4943aea9c433f544ca7ca821dd145309faa4659c3250738a9194f55032af298813d540433ca8194f95310e6210653d54cc39ca419678c8409f2a0615e53042dea4885754f41cea9e839f438cb5ca4214f94a42
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40a005410000000440020800c010102108408800000e04010016400301200201d011c318953d068c6250d30a3189438c68e6010832c3150320820c6254c40a398b548ca1d6395310c3d8c5250f0c520c941c550c514c30f6254f4187189531030d4394a318758e5090a1d650c8408b189531021f6354642a5584548cb0e520ca40c3189531028d61108328758e540868e6290832a3988548cb0f53149438e181544c62d6510832a3d94420cb4832141218b18953d070c540c9218758c540824c6254f41c3950328828c6254f418758c54c861d63141418b189544c70c540cb21a3189430c61f658c8408758e54c823561152328318953d070f6254c4093189531028c6250f30a3594420ca2e62d523087195434c21d6315210a3189531021f658cb418759432d063561150208758e544c70d43149308718953d061f6354640
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x814400228338ec629287215c7651083281aec2a064105047250c514c282b88a819041031c96314141818e4b18a90840c7258e54c4206392c72a043039cb6354640
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => 2*((h/30+packedAt s0K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/97+packedAt s0K4 (4455+(h % 97)*8) 8) % 165)
  | 3 => 2*((h/48+packedAt s0K3 (2280+(h % 48)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s0K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf03ffffe07ffffffe07fe07fffc1ffffce3e3f
  | 3 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1105108c412248100594a8a25012915414d0d5
  | 2 => 0x248a29103244942960294454a6412aa8ca262a
  | 3 => 0x42934a2490e904caaa8275113aa40c0d634b4c
  | 4 => 0xb2c74492481d974d34c1861cd39c031bc0db0
  | 5 => 0x8c307871c70e1e7f1c739e780e3188c1ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40449
namespace PEqualNP.Outside.L_meta_40449
open PEqualNP.Outside.L_meta_40449.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x153010414401c01c60000c90000402c508f10e000fd43fe10ff41fd42fe31be40fe43fc31fc21ff31ff42fd20bc40fe42bf41fe20fd21ff40fe41fc42ff43ff32bd41fe21fd31ff20ff30fe40fd40fc20fc32fe30fc43fd10fc40ff10fc41fd41fd30ff21fc10fd32fc30fe32
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x887f7318437ca6a0ef95221dfa0c81bd41cc3baa6085f54830bfa8a817e52d03de4310df15231bf28021fb40902fea0995f54a30df2a043bf4390f7aa9887bc8220dfa0c63bc52d06fca821efd0710deaa463be54c83be6318df54a43ef19061bf40902faa9995fd4c20bf290657d51ccbde85215f54841de2a421ec524c2f8a890ef944409e2a2617e518877a82205fd4941ee194617e5190f7e87a0df94a42f710a43dd53887b8a6906fd0621ee190617e52cc67ca0206fcc640be29843de314c6faa0195f54730deaa6617e548c2faa1196f50842bf29e217d51d0f7881906f90a40ef18c616d528c77ea9085f95330ee192637e54482fca0215f95132df202817d53842f8a6906f54f41df20c815f5350b7c81185f94c42ef192657c54cc2faa010dfd5230bf296617d5190bbca6085f54b43dea82837e540cafca1107dd0641be28a857e548cb7e8220df14132bfaa463bc43102fea990fdcc410fb082217e52042faa790dfd4f10bf2a243be435077ca8196fd0a40de29a837c544c6faa7214f95231f629221bd54c83de84a17e48020ef994657e50842f8a6a15714d10dfa0e61bf43d0afca410db94a31be2a0213c54443ee6318fd50441dea9683df31cc3e863086fd0440bea8e85be52506fca720df543419eaa043be4310afca2214f95320dfa0e637e528cafca120dfd5232dfa82837e50886f8a790dfd4910bf280817e50107f220086f10230bfaa4417d54c87ec6218ef94c40dea0e817e508c6fca620f78c430df208817d52887daa40877cc230ba28a61bf519037a63205f94620be2a643bd43902fca218cfd5132deaa0217e51042faa720efcc440efa1a87ef200837a85205f14f10df20061f9401027ca12077d4d42deaa443dd320cafea6084f94341efa1c877c514c27aa9905f54f40fd100417e50d0e7ca818ef50040dea1e85be54042f8a4a1f74c730de18c81bf4210378a7a0df94e43df20241bd41c837a62205f15232df20221ef21c82f8a8987b90842de298817e51087de85995f95231fd882217f52042fca7107ecc230dfa1a85bf41c837c84205f54840bea9a43df320cb7aa4a0dfd5331f7994657e50d0afaa7a0cf54440beaa043be404c2bca710df14d40bf286637e510caf8a098cf55032bfa9a81bc43507da43906dd4541bf29e43f431042fea8085f95320ef980617c544437c81107d14530bf28c83be43902fca8215fd4f20fd080217f50486fca5205f55121bfa9a857f52502faa5a0df54242fb20883f5100437a642057d4d10bf28e81bc311037aa3204f55241dfa88817e530c2faa7105b14943dfa8a83bc404437a65207d08610de90c817c52042f8a690df94630bfaa0617e509037e42206f15130bfa9e43bd540c67ca9885f54430df286836e52042fca9996f8ca40fb90c217f544cb7c82a0ef10120
  | 1 => 0xe5290f7e8298fbd4930dea0a217c51502fea8905fd52219f2a0657c50506fea2907e90040af29821bf43902fca6207b10b32bf28643be52d077a8621df55031fd904413e54086fca6106f14341dea16837e54082f8a8905f95040f690a41be548c6fca8984f15120bf29687be21902faa9207bcc820bf28841f710043ee4290ef10020be292217e534437e8218df55131dfa0a41be54cc3dea4885f94441afa9a417e53d077ea89077cc431df108817c52506eea2986f50f41df280817c535077e82186fd4f41f629287bd41882faa710ef100109e2a4217f540c77e82886f14640bf280437f538867ea8985f94843dfaa221bf414c3be62985f15132bf28e857f53486faa198ef14440bf290856d52043da64197710e32f619441bc41902fca618fb08420dfa9a83bc32102faa4884f55010bfa8a61bd41842f8a0a1ef90f41bf28e417e500caf8a2996fcc941fba8a417d52842f8a7107e8c030bea98213f54843de6590dfd5320bf28e617d500c6fea7085bd4943df21285bc42506fea4a1f78cb31be29263bd21102f8a8186f8c440de99683bf418837881885f95220ef182617e500c2faa3186fd0610ee988637e54086faa9196f50421df21c85bc4310bd884196fd5130bfaa0657e534837c64a0fbd4943dfa8683bf32d07de6490cf54640f719065bf43102fea9995f94c21bea8483bd53103dc43105f94732df21a87bd540cafaa118ef151209f2a021dd314c2fca6087b48421ae29a41bf52507ee6298db14930dea08417e53c82fea0a1dd14520df294817e53902faa321df94b41bf290817e51903b862185fd5130dea94813d54886faa9215fd5131ee21865bd41106faa8995f55230bea8487bd52102f8a9085f55020bea9463bc42d06fca990efd0421bf292217e518c6f8a8105f14520bfa8263ee520437c65a0ef14a40bfa9c417d52882fea5885f55010be2a441bc41103d864105fd4542dea9c81bc544cafaa921df55120bfaa4217d51843bca710ef50410beaa4217e528c7ba60185f94243bf28461bc40cc37a8390df94043bea8c656c524427aa918df54e30bf28063be54c42faa520df95131bea8e81bd4350afaa2215f94430be29841be40c837864a0df55231efa9a417e5310ef8a5086fd0420ef194617e5090bd86590f78c931fba8a61bf43506f8a810ef50640dea0a437d544c2f8a090df54c21f710841bd418c6b8a6a15fd5310de21c817f53482faa1995f94831dea0e21dc32cc6faa3205f94020bf2a021bd511037ea5a0df14e21dfa0081be53902faa7197e4c030bea8085bf41042fca5087d4c431bf29a437f528437e8390df94a41bea9841ec32486fca6196f543419f2a6617d50c86f8a4a06fd0842bf2a221dc5350afea6a0fd14520dfa0a437e53d02f8a9185fd4930de196837d5110f7a8310df55221dfa1
  | 2 => 0x2000088b804812009fa00006168540009a06012030040102804800000600180c130000c834088040080801006128621c80208812000000000a048026880400008450508f00e0180e0005062004368004484c0e836000040001400800010401e8060d80203024058020085e89864040044c0020085a0205a00048598000c00c018f0088220d00000036a90001534e0300a05000c8834e48020206201802308670b84800058ea8300001e028028b9321007401826008001b80000802008000110e008100303a11832090140180200020030ae0c8041e00a1085e3a004450040080823aae128301981c0f00000994098220301622066004520023c040200291c17020000000c06a450000480089000018141e8160000a008100300c060140000a2e0100b18e020120904a0181a0701407026378127e18e01000258001180c03096130020181c00834000060100e2efb88120fd88421bc43d077e43206f14141bf284657d5310afca818efcca40dea10817d544437885205f14543bea9681bc54443be87195fd5121bf28c85be408437aa6a0df54843be2a663dc534427aa9985f54d20be282856f524c2faa2196f94840fd982613e54887b863186f50540be29a217d53c8378a4206f50c40bea98817c540c6faa5885f94830dfa90817d511037ca818df55032df21881bc21902faa110df15310bea8e417c548867aa9886f10030bea90637f50506faa9907dd0541de992837d5010efaa5205f54041dfa9c81bc404c2faa7886f50731bfa82856f524437c84a0efd0740df20041cd320cabaa710efd0540de21c85bd418c2faa4087b50842deaa043bf531037e84a0df15320bfa8a877d538c7ba8621df14f209f2a0833f54482fca2205fd5020bea9c81f4210437a8298cfd5110dfa14857f53086f8a6085f55220bf2a6217e5390afca7a16f94640de29c817e521077ca7a0df94e10f7a1065bf41907da40106f90010de20441bf544ca78a0a0fd484219eaa063f710843be86195f95331fda02817e52082baa6085f94632dfa1683ef21086fea810df94b10f7992657e538877c85a0dfd4931beaa661bf529037e64206f90330beaa483ef32882fca1995f95221efa9a21bd414c2fea6885f54d10fb90c437c54ccb7a8218df94341bf2a0617e51d0ff640905f54420de204217e528c2f8a4987b08620df20621bd42506faa7a15f54342de19481bf418c2fca221fb94a31df28283be319037842206f14941bea86877d540c3de42905f95210be29c217f54cc374a0207790c43dea0a413c544cb7a82185f55331f6a94637c540caeea2905f54b31beaa6217f544437884205fd4532fb10843f7210437c64205f54c41dea1a837d52cc2faa3105f14b10bf2a0837
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa544c2d463440108f59053c872e5454a319758f520423c6454a108f992544827561150309798c5404335514c4408f597410c63f6510010a7d8d525067761540328f994544825e6394d10b3189300c29f6354840cbd4a529023e65901208f59541c832e5250631ad58440842ba6014c40c718d540ca3e6510130cdd45414826e62947308fd95321025f654c0309718d528433764d4520c7552530423f6454d209798e544823e6515132abd8953507545314520d3149314c23e64d4e21aed81311038e544c8329758e524431d5310f418f59741c823d650c4408f59353c423e6414f20ab18943d0a3f64540218f197414c3356414530c714e404826e6214c1097d8d528423e64d4f10cd546211025d639442197d8d524433751d0530c794f41042756115232ae18131102b561100108f997414423d6414e219b994524429d6314b419798f52c429c63548408f59352c432d5210840cb54842d067661d4f20cdd45415026d62d4f108f195329023e6494e20d314d214829f6350b419e59610042ac6250c40d514e104425d6315010d394f218867b65440109e181544863f61550329758f548878c644c8328fd91500c63d64944308f592518ca5f654c8329b98b53c423c6454910ab58853d063d64946209b588540436451c8520c7952538872f52101309dd85534826d62150308f98254886ad628c640cd54741d02ae628c6409b189531038f43d08329ed95401023d61d51329d98454cca796014c21cb548521032f5414910ab58b53903a541484218f58454482cc6250c43c7552538872e5250410d5d4f51482ba60d0610a7d8d505072c52505308f590534863f655084297d8d544ca3d6414532cb548400425e63d52218f593538865d6395110b5986324c66f6255132cb14b414423f6454321b398a318c23e6415032cd193514823e64d4132ad586408425f6354840cbd53524c23e65d0d428f996311033a6094040c7d4d414438d320c9419bd95210863d658c640d3d95320ca3e6494720c7153534826d6295110c714d41442ce644c8328f593504caaf6254c408f59251c827561951208f592534431d5350621a798c51903345110120ab189505065c63551209d185544c31c53d0520c7952530423c64548308f592510ca6c6254f41a718d52d063e6494d208f594211026f6548020ab98853d078d320cb41ae18141c823e6494420cb54b418c71e5350e40ad58752d067b6054d218fd9541106766195120ab58b50d06b56190010c7d4c40482ba6014640c7553430ca3f6454a10a718d505063c60552318f592528c23e6414931cdd47414832e52d06318f99541483b040440108f99421102cf614c8328fd8554c8334541452097d95310c74d530cb21ad984521038d544c832cb14a404c32e52900109798e544423d6590c429758f548831f5414d10
  | 1 => 0x27a6014c218f590514c23e6015132a718d425063d64d4121ae181535071c5350d41b318d4210b4d520cb319b98a524423f64543329bd89544c71f5390120ae983529025e63d48108f596400431d5314d41cb55152042ae62d4e40ab98b50d06b56194941ad584531023e6588440b9987324863f6454e109bd954210a3e6494430cd54541902ac6250f418f19150cc69f6354b41cdd5351482776154910ae980511023f64542219dd95411063e6495110cd94541082776544010c714e4250aba60d4c40cb54b410429e63148408fd9153083366414530abd89505065e6394d208f992510cb1d53900108f990530423d61d51208f59252082b66114c40d9d4b514c26c6254d108f593530863f6454f21aed81211032e5210010cb148404c23e6414c21cd146404c26f6254031cd545211025f6354021cd5875484395414c431cdd46404832e5250a40cdd45414c26d6588420c7d4c404423f6550c438f5925384335518c440e34c8321023f65504218f59251ccb6452841108f19153486b86050610cb189540cb4e53548108f99352c426f6254e10c754c431025f6355121c794d410423d6494421d5185530429e63144408fd9532d073451d05208f992518cb2f5414930a7d8d42507645148520c714c404433451d0530b398e218832e4314943ad987325066c6254e10cd590514826d62d5230ecd0510042ba601484097d8d544423c64543218fd91508ca3c6454b318f99432d069e63d4a40cd150514c2ba60d0510cb14a404423e650c941d314b314c23d6414c20add8553506e462440109798c54886bb6054d419718d52d063e64d4e209798c520423c65505108f59353c831c5350520d5146304c23e6494620c7551530425e63d50109b594320831f53d0520d394b318c65e6315321abd89431023e64d48109bd89544c34f43149438f996319031e5454e218f982540c63e6494e10ad58452d06b86050430b318d20082ce628c531cdd93514c29d63884409b98b548c71d53d0410ab191320cb3551504309bd89534429d6314440ab988519023d64947309b988540c26c6255110c7551538872c52505109b58a534434c53d49108f993504c66e6214810cd547411026f6254f418f195414823f654c9418f596540c6ad6214c408f59741cc23e650c640a7d8d429031e5390010c795153042766194d20ab588511033751901309d984540c25c63548408f996404426f654c8328f982548c72d52506318f181540c63c60550219d18553482b561cc941a718d42d072e5454810ab189531027561153328f992510863c6454d209ed95200826d62d4c10c7d4e53902ce628c430d9146204832f5210110cb952528c63d65d04108f180544423c654c8409b98b530423e650c4408f990530826e65c8520d3d4f524425e6514d10b358e320cacf654c8329b98
  | 2 => 0x54d4530ab18943506ac6254d41c714f414423f65507308fd91520c23e60151108f992518c32f5250530abd89439034e53948109d984540836452d4530cdd44404c23e65d05209b98b548c25e6514d20c754c531025d6594c108f992544c2ba6014a408f191500875453d45208fd9150cc6ba60d4440d5145314c31e5310010a3191320caba6014e409d586534826e6215010ce983548423e6414f108f197414823e6414b10b3191320ca75650c4108f195414c23d64d4c109d586544c23d6414f208f58654c82bb6054941a7d8d421031e53506219dd85544c32f52901308f996219026c6255130a798f50d063f6454231cb552528c63d650c6408f59432d06b561148408f992528425d63150208f586540cb1d53d0621ce980548429e63886408f992510423d65950108f590530433754d45308f596540cab86050510cb549410425d6510c328f983544ca766195130b9185200823c6454d108fd9541c823e6414f218f994321035553cc4108f992528c32d54d08329e181544c63e65101109d984548ca3e64150318f590530874c53c85208f191500c63d6414520cd193514c23d6550730cd990514832f54d4910c714f4350a3e65151108f996404c26e6215231cb148404423f65d07208fd91534876552c84108f19153c869e63884408f590524c63f6155010cb54852d07675214530cbd4b41442756114c20abd8943d074f53149108f592528425d658c430d314c524431c5310120cb95252043646154810c7150534423e6095021ae98351902776548421cd945410c2b5618c941a758f50d063e650ca40cd14541482ae628c440a718d525078f644c8329b98a534426e6215331cb153324ca3d65950218f592534826f6255110b5185300c31c54d4d108f592510c63e64947329b98b540429c6350842cb54a400423d658c4408f590520425c6354910cb548525067561d4f20ab189439023d61953308f19153083375110120d354c320823e6494820c7150534823d61d51309798c530423f61553308f592538826d62947309dd8553442ac6250c438f597410863e65101208f99252442ad628c440b3181320ca5d6315321c7d4d414825d63148108f191538432c54d49309b58a544c23d64944209798c540825e63947209d984530834f530ca208f993530867561150208f99052042786054d218f99251cc34d53548108f982540ca5e63d5220c754d410431d5314f418fd91534429c6350a409b58854cc67b6055131ab18953d063f65504318fd9152cc7345150530b398e21487345190120cb153524423e65d0540ab988531023f65d0730cd153514823f64549109b98b530863e65151309758e51c82ad62146408f59052c423c6454032d5d4c514826d62d5231c7d50534838c4310832cbd4b414c2b56194d418f990540423d64d4e208fd95401
  | 3 => 0x501004364010c40615c00000194f8780601100c0c0080508452020000080000003000030004502c3a02c28008000f4041040004c02018310e804008000983e0580000c000580b09c1b00001024060003400402018b33b9441756c044040002400c8e024040742f01817000130003001c120bc1212000008557b89b62a32175d300410008080080c004d2000110044f08c050047b00531008000600a0003a37c032dc135dc04219c15084212034038e106007000150583201c0b0080000000534010cc0100000024094f4054340208c000c81741804004452880c004090087a0002827804018190001f128017a82c0141e01c010400d120001189509c000041001014001e003c0000004934dc00400008386980004c00000303b44609c022a8d40440029418208021989701c0207c0e0097134c172780a00c0d001960b8000001d0440065403030030002336c0100001024036f40001b4d520c8308f990514823e6494431ad58753d06b761549418f181548869d63148408f191508c6b86050730c7d4e40442b6618c9419b588548c63d6588440ae181525066f6254d208fd96400423d6414f108f19532d066c6255131ab1894350b8d320ca40d354e520425e6394421cd144404c31d53100109b588530423d6494910d9148514c23d61550109b596520425d63152219d185500caaf6250d41b3588430ca5c6355110c714e404433561152108f992544ca3e6494d10cb14942506ae6214440cd951411063d65904409b594420cb2f52505108f594329025e65cc5309ed81544872c5414930ae181410825f6354b41a718d421023d64d48109dd95310c75451cc530cdd50514829c644c8328f99353c834c53881209b997324863d6508640c794f418874c528c130c7d4f414423e6494c30a798c52d06cd6310832cb15052442b56114f41abd8953d066f6254c409758f52c423c6454232d354c324872d54948109718d500863d6494410c714d4350a3d64d41318f99054086ba60d4e4097d8d544829d63d4a408f584544ca7461551208fd91500ca5f6550c439ed95300c32e52d0410a758e21903375414530a758c519031f54d4d208f594325067761551208f59621902b860484409b58b540432c52d05309b98a544423e6508640c7d53534425e63949108f993504867565084108f181540ca3e6414d218f995414c23d64946309b189500c63f654ca408f592530c32d5454a319758f540425d63951208f99353042ba60d48408f997414c23c6454221d314f4250a3d65100109718d544863e6414530b398e210831c548c932cbd4a404423e6414e218f195325063f65504108f594321023d61151308f19150ccb3551504208f990514cb34
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x21011c52001a4244148200914440403200007091ce93226419625625463110312a92c220021431cd5214941a18e6a9085a0e0c6394942902863aa6419683431c95314c40c62a2302821848c76951320ca8639aa4296838358d5214b41a18e4a98a6a0e15635462110312a92c229081431d1520c830c62a2302821060d654c832d0687baa6419481235c4644c832a18e4a9887a0e0c5318943506863aa6419283431d1530cb21c1ac6a90a42050c754c8321021ab88ca9908183595320c840d40c4202200850c7254c43102873a6a6194418394c6250e40a18e6a90842050c7454832cc68739ea529481239c0644c832a30e0a98a6a0e28521814144306318c4aa065231d9544c832a18e8a986490e90631011004287396a729c814a1c15214941a90e0a986490e0d535885310306318a4a1283431d1530c820c62c3306a90843870594325070c298c0a0a218554d6110010c1aa6b10a7a0d0c73548521030aa9ac229881431c95314f41
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x20080080c87595320cb4180c87595320c840a04835496114840905811d5320c840a048254d6114c40885811da544c832
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 5 => 2*((h/267+packedAt s1K5 (21627+(h % 267)*10) 10) % 801)
  | 4 => 2*((h/274+packedAt s1K4 (29678+(h % 274)*10) 10) % 781)
  | 3 => 2*((h/25+packedAt s1K3 (2744+(h % 25)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s1K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff81ffffffe07ffffffff81ffffc7ff1ff
  | 2 => 0xf81ffffe07ffffff81f07c1fffe1ffffa23e3f
  | 3 => 0xffe03ffff80fe0fffe007fe0fffe1e03c3cfcc
  | 4 => 0x3ffffff000ffffff8000ffffe003fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x882808c4122400016509421280222a80cd0d5
  | 2 => 0x924519103244986580a4291a53215551a2262a
  | 3 => 0x2149aa2490e909aaaa084f489d54181ac34b4c
  | 4 => 0x859634492481d2d34d3d0210e6998063740db0
  | 5 => 0xc6183871c70e1cfc71ce739c07111183fbb000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faa0a0a0faaaaaa0faa0a0a0faaaaaa0faa0a0a0faaaaaa0faa0a0a0faaaaaa0faa0a0a0faaaaaa0faa0a0a0faaaaaa0faa0a0a0faaaaaa0faa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40449
namespace PEqualNP.Outside.L_meta_40449
open PEqualNP.Outside.L_meta_40449.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x210604000900024710004124300400240008d001fe30fd21fe43ff10fc30fe40fc31fd41fc40fc32fd43fc41ff41fe21fc43fe32ff32fd32fe20fd20fc42fd40ff42fd30fc20fc21ff30ff31fd31fd10ff40fe31fc10ff43fe41fe42ff20ff21fe10fd42
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xe43f5510c3da84215f94c41beaa4857e528cafaa710fb88620ef988637c548c2fea6085f14e21bea8e817c54886f8a8885f14d40bf298417e53906fca618df94a43f629287df308c37ca8195fd4d41ee29a417c53842faa7a05f55320be29263df4390fbca710df54b40beaa0437c5150afea8985f15130ef98c63f840843bea6905f14e20fb28841ef4290beea2a1df95010fca80437e54086fea9997790e30efa1a877e53d02fea990de542419e2a221dc32cc7f6a0a17bd4910fba8a857e51d0efaa990df14f10bf2a0617f53c86fca8987790c43be282837c540c6fca6197790f32aea98837c53486fea4985f54a21beaa0637e520c6fca110df94440dfa1e85be54cc2fca210df54041bea8881f920842fca2185f15330bea96836f52442faa7885d94640baa8e657d54c437c80a05f94e42bf294217d538c2fca421df94410be2a0217e54cc2eaa3207ed0210bea86657d50cc6fea098efd0a42bea9e83bd4310f7e8220f794c41bb28841de324c6faa7195f55121f690843f741907eaa2105f55110fba0a833e54cc3d8a4885f54f42bf294617e5010af8a2985f94c40ae29a417d52442fca4196f50040bf28687ef21886fca8885f54a30fd10421ed320cafca0195f54c41afa9a41f741442faa118fdc4010bf28865bd54cc2fca7207750c30bea8c617d51c82f8a9886f50f42be2a06175510c2fea810774c832dfa1c817f544cafea9087d4c510bf296817e52d0efaa4185f54243bea8e877f52443baa710df55330bf28087ec42ccaf8a0995e94021bf29c876c5250efaa5885dd4543fb082217e5190afea2905f15232bea8687dc318c2fca420df95230fc980613d54cc2fca1215f94331bea9c21de32cc77e86205f54730fb18a21ee320cafaa221df54a31bea9a217c54c82f8a0a1df94030b6292217c52c437c85205f14c20bc282857c5350af8a6905f55240bf28c877551082eca3995fd4941bea8c857f54883bc63187bc8020bfa9a417e51c83eca2185f14943be28243df5350bde41107714d42bf298857e5210afca7886f90840ef21861bf4350b7a87205fd5331dea1085fa50086fea4085f94342bea8c877d508cbb8651877cc030eea98837d510cb7ea8905f54a41be292217e5110afaa2215f95221ef990657e548cafca119778c9329eaa0657d500cbea8220df54c21fba0863ee4210be8a2a1df95321fba0e43f741086fea890fd4c721beaa665f441443b886195f54e20bf2a0857d544cabaa6216fd0e43beaa4417f514c2fca998ef50c40fd882217d52cc2faa5087d4c421fb208837e54c43dc4290fe8c030bea9c817e54487f660985f54321bf29a437e50843ea6218f7cca32bfa8a85bf40902fca5887d08610be28263f741cc7f280205f95043bfaa2417e52082fca9995f54f20bf2a641f721843da40107790d31
  | 1 => 0xd548c6faa6205fd4d21ef182617e53043eea2906fd0842df20881be4350efea7085f54f219faa241ef420cafca121f7d0c32be2a265dc53442faa3a15f94341bf294837c54843ee6298df94040df20a837d54cc6f8a2905f95131bf29e417f52842faa5a1f70c430bea9081fb40502eca2185f14d41ef194617e508c2fea5885f54021beaa4657d51ccafaa921df15220bf2a041dc438cbf66118778c430bfa9e417f54886fea0a15fd4143efa9a217d53483de64995f55032bf280637d544c6fca1205f95210fb98c637e50906fca1997d10421fa20e437f53502faa1a15714d10be2a2417c52503de65197d54732bf28c41dc320c3e88218df14c10ba28a877c544c6fea710fec4210bfa8243be4250a78a8905f94740bea94415c5350afaa920fdd0710be28a817f544c7ec4210df94020bfaa4637e54102fca6905f54e42de21481f840c82fca1107750f31af298857f50507ea4210ef10840fa98e217e52102bca710fd14542bf29861f721486fca9105f94443bfa8265f710842faa89857d4d10bf28c817e53086fca6887dc8621fa20e637751482faa120fed0320fd90241785050efaa3085f54640bf29221fa40103f220085f94441f6108417e5310fdea4a1df15231fb18e217d548c2fca21077d0e32fda8287de5310bba6218fb08620bea9487f8400c2faa910df54d21fb28c81dd53d02faa3195f15121fda04817c52042fca5a0df55120fda00617c54086f8a6885f14f20bf29c437d50886faa6105f14c21fa880217c52506fea810df14a10fd90441de53d02fea8195fd4540bf290617f53082faa8185f94f41bea86837d510c2faa8105f94a40ef21e635f5350bba60186fd5110bf29c21dd4310efca8997750d32ef190617c54ccabca7a05fd4d10bf280837c540cbf080887d94732bf29e857f53882fea4a06f50d42fa28a417c5150f7a8220df94632bea8085bf41906faa5205f54043bea90837e51d0bde85995f94810bfa8a657e52cc6fca3985794c41bfaa0617e518c2f8a2995fd4543fa20e215d53887f080105f94a42bf28e657e540cbf240106f10640f7908437f540c6fca8905f95041bea88417e50c87f4a120ddd4542faa8c817d500c6fca010cf95032fc206617d538c6fca5985f54810beaa0217c54c86baa7a07750f32bf28c437d52cc6fea8085fd5230bfa9e217c54cc6fca410df94631fc90221fb40083ea43885fd4d42bf29463de314c6fca818fed0110f62106579500877882205f94010fd08021f621c42fea9905ed4143eea1c61fb40cc2fca320dd14520bea98217f524c7bc86995f54e41deaa0657c54082fea8885f94431beaa4217c5050af4a120fd08410bda8285dc324c6faa421dfd4943fd100417e508c7ee42087e54241de2a2217d520c67ea8885bd4943bf2a463fa20442faa1217b88420bf29
  | 2 => 0x83b020035276fc00000090042107400004200305a0000300c0008c190a84e0040c0e0000000004c664b4010000101c010701401d59038010140000c0100000008350047200cd80000100c0000c03020010002e0000a0000d000000005d0ac1500c02004240001f02005000032240308800000010180022416014260200000000008003a80b02034000160000379409048130081101556004030001701407040f50d0520340a0001a03001024035081a060052c43d000030240000010024150280602136010010a01d05c540587e098010e22500c01000f0008030a80302815008501a0030040a6804001c000501300001024162286000c030005b03000000050e80000c340180900c000015200400198120080300c030006105800050010741f00000000011e0020740500c02048120e825008270540006c0501400704190240d0081c000000000602001004030001a07c040380400c09008040300600400070480001801000f7a12857c53c87ec6210fe14143f710241bf40102fca7107d48510ba28a857f54cc2fea9885f14930bea8c417f548cbec6390fd8c431bea9885dd5310bba8698ef90640fb10a21bc54483f0a0a16fd0c43bfa98437
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xb548c31c63550329e997404425d6590c309e583548c6756114132b9588410865d631532197996434ca756194d219e18154c872c54d4910d314f4250b734154241b5587328ca3d64d4b10d3d4c5244364528851097d8d521027b6054d21d5d4c514836452d45439d587548ca6f6255110da14a204437351d41438f191534867761553309d58754cca6e62150109e181534863f6454d219758f520423f6454231da14b5050e5d63153209798c54c833561d51108fd91524427965840109798c54c423e64d4b109d587540825f6550c43d514f5148277654c431d550d510c364528c510d558453442b860508429d984530433761550329b189534427a6014c21b9189100427661141329e583548866d6294d109d185528c31c53d0d429d597210431f54d4d10a7590320c3545310510c7d50534834c53d49109d195214427661943429d18553482756115020c7d50534436960149109bd89544ca7661d5020dc1475050e7661d5332ce181540cb5863542419e98354ccad563104218fd954210a766114c208f992538825c6354910d614c404436561149109ed952008275611533297594430cb3b54101109d18554cc34f53d4910cd153514826f6254d109718d544425c635424197d8d5090a796015021f8086208435853141429758f548829d6310640d914a104437151d0240d9149314435853d0110c7150534426e62150309758c54c42e9600862097195434c6ac6250e409ed81544835553c8621dc54740082cc6250c439b594420ca746155320d590d510c2d563107219d987548cab864481109dd95210867a60d52329dd85544c78f43d08329ed81540ca3f6454d10dcd445050acc63508429d98654482ac6250f428f992524427960d5021ced91500865d63d5221b518543cc65e6394910b91852008274615513297d8d528432d54d0832d91485150e766114810b318943cc67661d50309d587540c37051141429d984540c3704154021d514c514831c54d4d109ed81544c7994310030d914b41442756194f20d9d4b5150e6e62949109dd85524429d64cc030dc580514829d6310a409d58650d0e5e6395120bc185208426e6294d109798c540c73454145208f99053c427761551309758e544425c6354a109d587548c27561943429d594410c65d63151218fd91534823e65151208f191508c65d63d4b109b58b5304275658c4218f590530866c6255131c754f4210a5e6394642b958a310867565104219d185540ca3d6494e20d58c9510c33960d51109d584538827661d5010b558e21442776154b438fd9541107735114143aed8143102f160904419e58354ccaf161900409bd89544c27761551219b98b530426d62153319b98b548c71c54d4d209ed95100426d6215010dad485050e5c635424297d95300c2776550441d6d8153d025e6315010
  | 1 => 0xcb5753145429e58251d0a5d63150109798c54c8677615512097d8d544cb6852141439798e510874c6254c429e983540423c6454232d550d51cca746154b43d354832cc63c64549109798f54882cc6250c3097994534837051d41429798e534425c6355121b558c414423f6550c439758e54882766115020b658f400c25e6395220dcd475050a5c63548408f590530823e64951109b189544c27561150309d587530827a60d502197d95320ca3d6414f219d185544823d659503297d95310c7543254430cdd5351482d563107109758c54886cd6310b329b588540c23c6454d20dc1445050ecc6250e30dc88550086f160084108fd91508cb1d544c8329758e544c25d65d0c32ced8154cc27a60d52219ed81544865e63d4b10b3189434cb586354021d514f41442796510030dc8c5500869d640cb319ed8154cc66f654c832d6d4c5050a766194d2097d8d544425e6315021ae582411027761553209758e548427b60551329d987548c2796014c2197d8d500863e6494d20b3189434c63e6494c3097195434ca3d6494d109758e544826f62551319b189544425e63152219e98052043715110020d6d8d509069d63d024097d8d5448755518c430b5185438c26f65508429d98650d0e3f65500408f592530c3645210510c7150534827a60d4c21cd185540cad56388421c7553320ca786548110ae1912084279651002097994534438d43d0b32b558c41cc67665d05109d987530835b53d41429d18552102766115332c7151434c73b6055032cdd5051482f160086109e983548c65e6315121d590d51cca776154a30cb150524427661d52209e983540c676658851097d8d544832f5414910b5185430c27b60553219e1815448764518812097d8d509077131540219e980540866f65480208f592524432c6255032cdd8554cc26f6548421dc54620083715148020d514f5150a7860551329b98a544425c6354021ce191500876852d0110ad185439027b654c0308f990530825c63551209ed81544c29d640c9318f990530871d54d0c32dcd0550087545314542a7590328c27a6094742d5d4f5150b645248510a758f401023c6454021cd18554cc35753d4520ce153204826d62d52309dd85544caac6250c40b6d81430c29d63104409ed95401036752145438f992534425e6394d20d3548320c2d561cc832c7d53534825f6354910dc544400c27860550328f99254483394314142cd54441902776154d20ae19120082756114c20d314c524427561d5220dc547400c25d6394642cbd53524427960d4c218f592534826e621533197d8d52d063d6414f109798e544423d6414f209798c540ca5e6315020cdd50414431d5350842a7593308c25e63d5221da14840442756195120bc181314427860551319798f520425d6394421ad185431033a42141429b98
  | 2 => 0x56407c0000000f00093001b2900900008000f0095c4002000c8c2742c8002e041f000000808965aa915900c4a5c018600052bf805844504b88c20f0183814003f81cec080782cc01703800000a1c81d00190000000180b01c02030b84c0001008401a000000088362b8005c07443eb52001f800160b000500e060101c840200000620d440a4261211024020101800400a002d402020a85c16020a3cc0ea3098041a01a40a40042211ac12039c060080d0d8104e8314000005a0182800016801f655188420dc48550086766194f209798e548425c6354b419d185544c274654c5109b58b548c75853d41429dd8552103e22188110b318943ccb3954103309b58a54442776544010c7550430ca3f64540218f1915344354538c510b558e21c423e6414f218f990540ca5d63150219758e524427860553319b994524434f43149439d594210429d63108409e583548ca756194d20ced0c5050b546154c419e583540c63e6414f209758c54083b04110110d6d8d500876b52d41439d984538823e65151109dd85540
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x5042840061a052000034a1d16014910c32a630284215447250d51ccac8b9882202218c1915148020aa2e620aa010e0d6454832cc68aba064a88618555161cc832c60c2302a8194557614c41442c838a8620061c81484110110c50c4302a8196456314a21442b0b9082a8043585ca3154021aa2e710aa010d447250d510c306b22a419061435d743d0832e20a620880886186418d5008722b18a420a21831506250d31e2286a8880185627588620442c4392862006198148604c510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xb008250d51100309118714c4110110d01731484110110
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s2K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/287+packedAt s2K5 (17064+(h % 287)*10) 10) % 632)
  | 4 => 2*((h/171+packedAt s2K4 (17974+(h % 171)*9) 9) % 473)
  | 3 => 2*((h/16+packedAt s2K3 (1421+(h % 16)*5) 5) % 29)
  | 2 => 2*((h/8+packedAt s2K2 (180+(h % 8)*2) 2) % 3)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffe03ffffc07ff03fffffc0ffff80fcfe3fc7
  | 1 => 0x80fffc07ffff80ffc0fc0fff07ffff0363c7f8
  | 3 => 0xfffff80fffffffff000ffff81fffff83f8ff
  | 4 => 0xff0000000ffffffffffff000001ffffffc00ff
  | 5 => 0xfffffffff00000ffffffffffffe00003ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x86129850a04712300b2c52c429a594542e1bc3
  | 1 => 0x2a54293144890e72c055455525cab55162c5d8
  | 3 => 0x548850a269122495550209a6b093469a83686d
  | 4 => 0x18d162c58e2448e9a69b6030851c78e3f400b6
  | 5 => 0x60e183060c3870ce38e38e38c6006083d9b600
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88ee000000eeaaee88ee000000eeaaee88ee000000eeaaee88ee000000eeaaee88ee000000eeaaee88ee000000eeaaee88ee000000eeaaee88ee000000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40449
namespace PEqualNP.Outside.L_meta_40449
open PEqualNP.Outside.L_meta_40449.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1230000020bd42bc40bf42dd32dd31be40dc43de30dc30df31df43df32
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8010aaa8e651c544c6aaa2184e14142
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
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s3K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s3K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fffe07ffc0ff07ffffc1fff03fe07e7e7e73
  | 1 => 0xfc0ffff81fff07f83f03fe1fffc1ff81b19f9c
  | 2 => 0xfff07fffffffffffc003ffe0ffffffffc1e3ff
  | 4 => 0x7fffe00007fffffc0000fffe0001fe03e0
  | 5 => 0xffff8000000007ffffffffff00000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x48610231448521014b14c0253213212c162e31
  | 1 => 0x19222450c9142b281551521656514b04b09694
  | 2 => 0x20844882122084528082254088a4945141414a
  | 4 => 0xb2cb712483b6b79ce6d83114ef390619fa03e0
  | 5 => 0xc30c61c71c38c6e738e3b9980c201861edf800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e0e0e0e0eaeae8e8e0e0e0e0eaeae8e8e0e0e0e0eaeae8e8e0e0e0e0eaeae8e8e0e0e0e0eaeae8e8e0e0e0e0eaeae8e8e0e0e0e0eaeae8e8e0e0e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40449
namespace PEqualNP.Outside.L_meta_40449
open PEqualNP.Outside.L_meta_40449.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x10000060040dc43bd42df32dd32bf42df43
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x29aa421e350932
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/16+packedAt s4K4 (96+(h % 16)*3) 3) % 6)
  | 3 => 2*((h/1+packedAt s4K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81fffe07ffc1fc1ffc1ff0fff07fc0fd8e7e73
  | 1 => 0xfe07fff81ffe0fe0ffe0ff0fff83ff02f19f9c
  | 2 => 0xfff83fffffffffff0000fff0ffffffff01e3ff
  | 3 => 0x3fffe0000fffffff0000fffc0003fe03e0
  | 5 => 0xffffc00000000fffffffffff00000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa4308231448a44052c85301534264258862e31
  | 1 => 0xc910450c90854a054a4510654a29608b09694
  | 2 => 0x104228821221094a02108aa0894928a301414a
  | 3 => 0x5965b12483ad6e739ad60884ee720c33da03e0
  | 5 => 0x618621c71c318b9ce318ecc8084030c36df800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeee8eee8e0e0e0e0eee8eee8e0e0e0e0eee8eee8e0e0e0e0eee8eee8e0e0e0e0eee8eee8e0e0e0e0eee8eee8e0e0e0e0eee8eee8e0e0e0e0eee8eee8e0e0e0e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40449
namespace PEqualNP.Outside.L_meta_40449
open PEqualNP.Outside.L_meta_40449.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x10000000010000004bc43be439c43fa10f510dc43f910f710df43f110
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x80a046371518433086886610e10ca21e2190434436086887410d10d921a21d3434432886884794e43
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2926390d10
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 10
  | 3 => 11
  | 2 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | 2 => packedAt s5K2 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/17+packedAt s5K4 (160+(h % 17)*4) 4) % 10)
  | 3 => 2*((h/10+packedAt s5K3 (297+(h % 10)*4) 4) % 11)
  | 2 => 2*((h/1+packedAt s5K2 (38+(h % 1)*1) 1) % 1)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xff03ff81fff07f07c7e0ff87f87fc0fc63ce73
  | 1 => 0x1ffc0ffe07ff83f807ff07f87f87ff007c739c
  | 2 => 0x1ffffffffffffffff80007ffffffffff807fff
  | 3 => 0xe0000ffff80003fffffff8007ff80003ff83e0
  | 4 => 0xfffff000000003ffffffffff80000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4948688c512ad3014174a9c49c4e425861c631
  | 1 => 0xca192914324a572802b5a2cc2cc696086c5294
  | 2 => 0x42082208480005288000411411128a180294a
  | 3 => 0x88b2c44920e3199cd4c6300076620c32b683e0
  | 4 => 0x10c30871c70c62e72718c766000430c35b7c00
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0fee0e0e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40449
namespace PEqualNP.Outside.L_meta_40449
open PEqualNP.Outside.L_meta_40449.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x403403850310010c00800000064417410000000803820c00200000000c200000254700900ff10001fc43007f50c01fe53007fcc007fc32007f950077d52007fd0005fe2101ffd4807fd32007f55003fe20007f4c005ff1001ff94801fc54017f14407fc5201ff10805ff5101ff8c801fe43007f54001ff53007f14c03fe5001ff50805fe51017fd0401ff4300ff84007ff32007fd5005fd2100ff08005ff3101dfd4805fd51017f08405fd3101ff54803fc5000ff8c003fc1000ff0c005fd10007f54c07fe42017f50405ff21017f10405fe3101ffd0805fc31007f50007ff20017f90401ff5000ff90007fd20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x86860cdf54940037fac498023ff535400ffeb0e8008ffd4a5402ff8c39809bfc2194c3fbf280a611ffc875002dfec998027fd41cc0037f304a835ff90754047fea9a8003fc435401f7eb0aa00dff14740005fac9a8023fc64d40057e30ea60cbf5894019ff8652a006fe60d501bfe18e8001ff883300dffe412180efe625000bfe29c8600ff10f5007ffe42a8016ff65cc00b7e3288608ffd8b54007fcca980bffe515505bff190a801ff8c130127fe84a9893fd5254c49ff312a610bfd8950047f8a5aa002ff605500bff3108605ff94d43005fac7a0017ff6194c01feb1aa009ff88730055fac59801fff4250011feb26a608ffd515002ffc6521833ff3250019fea92800bff58540007fca929807ff40cc001efb1aa801bf98353007fea7a181fdf4390c0bff98c8605ff0c54304ff843980b7ff2015003fe286602eff04154027fa629800efe6254c01fea9a8005ef50c4300ffa2098023fc5414c0dff292602cffcc4540bff8a2a1817fc6014c0f7f326a616ff98143007fcc6aa023fe5014c51ff186a632ff0c65401df8c429823fd62d4011ff296a601ff08140165fac22a017fc6110c01ff322a000cfd525403ffc802a007fe10d400f7f3226005ffd884303ffa85a1867fe4090c0bfeb0c8605ffcc953137fa4329823fd61d5001ffa1a6007ff18a5405dfac2a00a7fd10d4c03ef1826001ff84150047f8a32a017fd43cc049fe212a608ff98f541b7fc85aa007fd20d40057f30e6004ffd85301a7fc61aa017fc64cc00b7e31aa823ffd0553007fca998022ff61d506bff18ea805ff8c0431affa43aa017fd5390c0ffe31ca807ff58a5416ffe642a01ffc62d0003fe902a008efd52540a7fa2021817ff6090c01ff32a8633ffcca54007fac0a98cffd329500bfe988861eff48343157fe41a98cfff2095011fe31ea006ff8c93003ffe82a0052fd6110c19fe9928023bf5965302ff860a98d7fd31d5061bfa92a807ff109400affca421817ff314c001feb22a024ff4c95300ffe40980d7fd10d5011ff296a830ff90954137f8832981fff4215013fe90e6007ff18c5400f7881a0007fc305000bfeb00861dffc87430477aa82a007fc40d4001cea188600ff1915003ffac22a0177f5314c037eb068005ffcc75311ffc62a9817ff4310c55ff196a61bdf54a43137fca32980afc61d500bffa98a608ffd455403ffea9a1843fd6254041ff908a601ff101500bffc82a1847fd41d4031fe3128600f7d4f4316efaa42a083fd2114c11ffa92a821ff50853087fcc4a8037fd51d001ffea0aa008bfd875000ffe20a8007fe404c00bff1908605ff14d3003ffc83a0002fd60d5061fe312a801ffc435000df8c02180efc62cc003be286a00bff8c54003ffcc7a0006fe63cc01fff30aa005ffcc44312ff82129802fd60950077f3126007ffd0a43
  | 1 => 0x7fe31d40017eb2e8001ffcc130005fac02180afe615500bff3266008ff1875000dfcc0aa01afd624c003ff1828005ff94c4301df8c52988ffd1054c0b7fb108600bf59353127fca4a9817ff6510c017eb18a81cff08343005fac72a017ff6290c11ffaa4a60bff4c540047bea72986bfd5190c11fe28ea625ff8425300efca1a800afe6150c03fe8828005ff59643015f8c3a001ffc6115003fe086800cff9494017ffe20aa022fe654c00b7f31ca607ffd0d400d7fc8321817fc3110c0bff9968600af1915310efaa42981fbf4195001ffb22a600ff54f431aff863aa08bfe6054c5dbe282a807ff10543197fca32a006ff634c00bfeb24a600ff18d400a7f8a221893fe3254c13ff90e6008ff54454005fec8a9822fe65d00017fb02a607ff904540cf788121823fc5094c5fff10aa824df54953015fcc2a985bfc1050c0bff3166007ff5534003ff8a9a18bffc2155001ff21ea001ff94150047f8c9a9817fc43cc003ff286a003bf98954067fc64a006bbd4190c11fe282a800ffd53300077ea821817fe3090c11fda82a007df9515402efaa629897fe2094c0fff2a2a808ff5485302ffec52982fff315000fffa0e8631ff04254047f8a9a8093ff2054c0bff98aa605bf98f50007fc86a8016fc63540037e302a82eff881540f7fa65a1803fd5450c0bfe1868607bf99043047f8a8a8016fc6350041ffa08a61ef7ccb430f5fac5a186ffc5290c11fea8ea601ffc814000ff8819805ffd6150c1dbfa968007ff90b4000dfcc0a981ffc42d0c0bfea98a604bfd85300d7fa2121823fe61d4c3ffe100a623ff98553047f8a42a01ffd62d000f7fb14a805ffcc853137fc4329807fe4050011fea8ea800ff58d5403ffc8221863fe4250c077f3168622ff0815302f7c86a188bfe4054c01de3226001ff8433002ffcc221813fd514c01bffa8e8002bf18554027fc829801fff62d0c23fc886a00effd4b4003ffac62a017fd61cc03bff18e8618dfd4943047fec7aa003fc535004bfe204a601bf1835402ff8c4298977c5094c057e30ca80eff0cb4000ffa4198003ff635503dee9968605ff0c94303f788021823fc62d50057e30e8612ff50b5017ffa42aa007ff504c04dfea0ca605ff1973010ff88429823fd60d4c67bfa94a829ff9075302ffc6229823ff53d4001ff31a8007ff90a54137fe21298bfbf415500bfe990a610ff50950167fa202a0affe3015003fea82600cff5894003ffcc52a017fe6494c0fdf2a0a808f754c5302ffa632185fff5150c0bffa1c8600ff94f400d5fac321853bd4110c0bfe180a62cff4c454067fcc4a0023fe5215037ff2948608ffd4654037f8a49803bbd42d00037fb228000ff59130047f8a5a9863ff5250c057e30ca607ff5834300ffe2198023ff60d4c29fea888607ff997430aff8a42180efe62d4039ff2
  | 2 => 0x30047fea22a023fc60d4c0f7e32e8601ffc4340057f88598006ff604c00bfeb08a61bffd4a43147f821a986bfc5190c01fea9aa008ffd4753007faa8980037f654c003fc2028017ffd8543096faa5a801ffc41d500bff310a608ffd485406ffc43a001bff624c02fff28a8608ff94754047fec1aa01ffc4095025ffa16a001ef101400f7fc65a1843ff4254021bea92a020ff44053005facb21817ff31d0c117e32a8000bfd915002ffac12985fff1050c2ffea0a8608ffd8b531a7f821aa017ff6190c1bfe10e8005ff8c053047faa9a9817fe31cc027fe0808607ff9865400ff840a801ffc63d003dff9068608ff15253057ba659801efe6414c0dbfa92601bef50a4312ffca129817fd3114c5bfe190a805ff94e4303ffcc3a0007fc50d000dff2126008ff54b5003ff8c3a1807fe20d0001ff322a605df5944317ffe42aa023fe5214c0fdfa168010ff5495011ffaa2a9817fc3190c0bff304a605ff98453157fc85a985bfe2050c117f32a8617ff8854303ff680a001ffd43d002bdea108607ff5504303ffc8421813ff514c011fea9ea000af19130197fc432a08ffe4154c057e308a807ff95340046fea5a981ffe40d0c17ff20a8005ff14f43047fea8aa02ffd5150003ff2866010ffcc95000ff841a80cbfc219500dffa926005ffd8730197fa432a05bfc5050c59fe188a82fffd8554047f8a22a003ff654c00bfeb288605ff18253097f885a800efc6250c0bff21e6012ffccb50015fcc32980afe6110c1bfe90e8007bfd974303ffac32a017fe6010c03ffa828027bf58a53047f8a12a016fe63d0001ee29e8615dfd484318ffc412a003fc54cc00bff314a621ffc8053087fa64a8023fc5254c0bff190a605ff0c93003ffca8a181ffe62d00017fb1aa008ffd4b53047f8a3aa0bbfe1055011bfa96a801ff541400077ea9218177f5394c01feb2a860cff1494013ffa852980afe6114c0bff988a621ffd085311ffa62a9863fe6250c29ffa888608bf99730047fec3aa006fc6050c0bff29a6002bf18443047fec3a809ffd2094c0bfe196a600ff58d4008ffe83a8002fd64cc0077e312a030ff481540f6faa5a1857ff5210c11ffa8ea8009f997400077ec898043fc4254003fe186a0009f59740005fac02a03fff4154025fe996a008bfd8b5400dfac1a801ffc4155003fe182a001bfd815000efca0a8016ff6290c0bfe18a6017ff48543006bea729823ff52d500ffe202a81fff9005302ffea72981fff631500bfe1908636ff0cb54137fe4329803fd60550077f3108605ff1905303ffec1a1803bc6454c5ffea0aa822ff8c15302ffea79803ffe315400fffa16860aff50b30027f8a298007fa104c01bff28e8008ff18f5402ffac521807fa30cc00dfe312601eff54b43005fac898003ff6054c077f310a620bf5845303ff883a004
  | 3 => 0xeb14a800ffd4f400edfac3a181fff415500ffea08860cbfd894002efca6a9807fe3054003ff1026008bfd8b53067fc84a0003fe544c06bfea0ea81eff14b4303ff887a0007fe30d4021ff292a02fbf5965414ff843a9803fd434c06bff10ea805ffd9730047fea2a981ffc4255029ff1088607ff50a54005faca2181aff624c00fffb2e8605ff18a431affe21aa047fd31d400bff320a601ff4435006ffe43a0003ff43d400bfe18ea61dff54743047f8a1a9823fe54d4c0bfeb166005bf98f54147fc41a981ffe41d0c11ffa92a627ff54a5307ffa62a8007fd10540013fb2a6027ffd0a530a7f842218c3fd6255011ff31ea000bf58353137fe8329803ff5350c0fffaa68007ff10454067fea4a0006fe6010c15bea966003bf18b540d7fca321823fd62d4c6bfe10ea805ff8c65303ff88321807f8304c04bbf284a61dff4434303efea92a04bfe32d40377eb148605ff0c953027fa429804ffc5010c37bfa94860aff54b300bffe42a1817fc3290c11ff288a82dbf5885412ff84129803ff6550001ff29a8000ffd0d5003ff8cba0023fc50d501d7eb168034ff88354197fe432a00afe61d0c0fffaa4a805ff18643067f864a0033bd425000bff29aa60fffcc55001df8c4aa017ff6010c33fe0848608ff9475303ffca821807fe10d0001ffaa28607ffd974008ffe63a800efe6295015ffa166005ffd964303ff8c42a017ff3294c53fe90ea62bff04054045fec3a9807fa40d00017fb2a6007ff98b43047f8a6a8017fe61cc00fdfa108605ff0c55300ffe41a8043fe32540077e316a007ff5065402df8cb21817fe6090c5dff282a820ff9045303fba8621823fd5114c0b7fb28861cff8c34300ffa41a0003fd5490c03ff902a001ef90340005fecaa0023ff64d4c037f3048602bf9875005ff862a000afc615400bfea9e6005ff4ca5301df8c5a0007fc20cc011fe28aa62fff5855405ff8a2a0023fd62d500ffeaa0a814ff484430b7fc20a1823fc53d400bfe184a627ff10a5300ffc81a8023fd64d40017eb20a604ff10530027fca29801ffc4110c03fe2068005bf98c53047f8a42981ffc4050c017eb1ea007ffd825400ffc80a80a7fd31d4c037f3028605ffccb3002dfec3218037d54d4c09fe30a6001ff503300effa63a1823fe62d40015fb226008dfd485410dfac42981ffd41d00077e314a818ff4814319ffa412a06ffe4290c03fe1866000ef1524307ffac2a800afe61d4c4d7eb0ca614ff9444303ffac42a07bfe52d0c53fe20ea601ff041300bff842a1803fc6355003ee1866007ff9085403ff8c12a003fc635401b7eb0e8000ff19540185fec4aa006fe60d0c21ffb12a030ff5095402ffa659801fff61d000bfe32c8609ffd073003ffac5a180efc624c035ffa8c8607ef1504302ff8c59801fbf4110c01ff31aa005f7ccb
  | 4 => 0x833bf4250011feaa0a619ff8824300df8c0a9817fd3194c0bffa988629ffc8753007fec8a801efc6454c037f32ea026ff44253015fcc3a0037fe31d0011ffaa6a605ffcc65311ffa42a988ffc4154c2f7eb248605ff98a4302ff860a18c7fc309500f7f320a818ff4c94313ffca52980afe6190c0bfe1968632bf5865402dfec329802fd6550c0fffa0ca81aff5064302ffca7a181ffd6095017fe90a8005ffd844303ff884a1816fc64cc011fe316a62abf58b5311ffec2a98c3fe625500ffe2048608dfd485302dfec229806fe6014c0ffe214a807ffd504310ffc8429853ff2110c03ff0826003bf9894313ffe4129823fd63d5001efa988601ff94340147fc21a9893fd6254c077f316800fbfd85501affe43aa017fd6414c016fb1aa801ff8c330045fec5a8047fe41d402fff18a8600bf597430d7fe212181ffd41150237eb0ea030df5495403dfcc9a801ffe43d000bfe98e6008ffd445302ffac421807fd204c06d7eb16a82cff88454187faa4aa003ff6550c0bfe18e8601ff4433002ffc86a182bfe52cc059ff880a80bff94540027fac298093fc6254c0bdfa188605ff8ca53007faa8a982ffe61500077e314862aff48353047fea42980afe615006b7eb0ea81aff8864311ffca2a9817fe5314c0ffe2a68023bfd855303ff882a00a7fe21d4c11fea8ea000ffd8d400eff8a3a1802fd6014c09ff30a6008ff9875417ffcc2aa06bfc2190c11be286a818ff5894300fbc619801fff425500bffa1e6000ff1913007ffaa2a804ffe1010c1fff20aa000df551530c7fec4a1816ff62cc059fe108a800ff995401a7fc21aa003ff6354003fc282a015ff4804302ff86429807fc404c033fe2848607ff151430bdfac2a1897fe4094c03fe0828008ff1405402ffac42985ffc6150c017fb1aa82bff88054007f8caa1817fe6190c0bfe3108610ff189500b7fca0a1817fe32cc009fea0a6007ff1974300ffea0a8053ff1010c51fe206a605ff18653047f8a4a800efc6254c5dfe102a800ffd814318ffca12a092fd6254c11ffb0ea600bfd8d4003ffca921817ff6094c117f32a8001ffc413000ffe4198017fc3114c0bff98e6029ff50753047f8a5a801ffe639500fff2a0a807ff9834314ffe21a981ffd42d0037dfa148607df5505409f7c8021806fc60d0c01feaa28002bf18643015f8c298033ff6250027ff1008630ffcc954066fea4a00027d6510c077e310a82eff0c15402fbca629813fe214c035fe90c8601ffd013002ffec998002fd65cc061fe992a82fff8c55400df8c1a981fff6195011ff296a004ff08530047f8a22981ffc4010c31fea12860bffd454002ffa8621807fe40cc00ffe206a805bfd96430d77e8321817fc53cc059fe908a807ffd8b4000ff8a098023ff63d4049bfa92a627df54a53127fc84a981ffd61d0c677
  | 5 => 0x9530097fc85a80dbfd32d500ffe20ca816ff90143197fe212a023fc5255047feb0aa62eff9815400ffc20a001ffc42d50077e316a605ff14d43045f8ca98022fe6590c0fff204a815f74c84303ffcc22a007fe504c00ffeb1e8008ff95053046fea5a8017fe3110c5ffe98aa800ff19153086fea4a8017fc6090c017eb24a60bbfd85400adfac42186ffd4290c03fe9028005bf98c54076faa5a0017fe6014c057f30ea807bfd885403df8cba00177e6510c31bea928600ff1513002ffec82981fff4250c3bffa8e8605ff90d30047fcc5aa077fe51d0c0fff304a808ffd475003ffa842a01ffc41d0c257eb16a000ff595401a6fca1aa006fe601500bfeb00a600afd915318ffc212a017fe6194c0f7fb08a807bfd9740007fca8a980efc6210c11ffa8aa005ff58a5303ffec7a008bfc4054c11ffa96a008ff1535302ffea721807be4050011ff286a608ffd495019efaa52a0bbfe3055011ff30ea007ffd0b4003efea82a026fd61cc00bff328860eff54b40047f8c5a801efc64540017eb2a8001ff10140137faa32986bff2190c5ffe882a823ff505530e7f821a1806fc6095001ffaa48623bf58553025fac298006fe64d0011feb1ea026ff9065303ff8c1a184bfc32d4027ff2808630ff9495403ffec42a0dbfd20d5047ff882a610bf5895003ff8a82182ffd4150001ff29aa001ff0834002df8cb980b3ff2115011ff286a80fff1855003ffaa9a1843fc3254001fea9e8002bf98530047fca7a8017fe4310c47ff10aa619ef9024305ff842a0003ff6055003ff8828022ff8815303df8c89800efe6290c11fe282a603bf98950037fa8498063fd5250c67fea94a801ffd014001df8c5a1827fe41cc01dff9968007ffd07400bdfec2a181fff541500fffa14a805ff59330047fac3a981eff61d0c33ff0848600ff5915308ff863a8083fc4114c17ff10a8009ff54730006f8ca98003ff644c009fc882602fff18554047f8a529816ff6214c45fe302a616ff0814302ff8c52987b7f52d0c63fe104a80bff1854007ff862a8017fe65cc0057e30e602aff50b530fff82029817de4310c01ffa9a6001fe84350015fcc2a801fff601500f7fb0e8007ff98c54047f8a3a80c3ff20550057f30ca800ff54d4303ffc85a181efe6494c03fe2828005efd0e4317ffe62aa0237f54d4c03ff1028001ffd433015ffc202a017fe6590c0ffea10860eff4cb4003ff8802a023fc5154003fe186802eff90154007fa86a0007fd50cc0037fb028005ffcc943117f820a9813ff214c037fe9048636ff50b54057f8a59801ffe61d0c0fff300a807ff9514003ff885a0003dc635505bfe900a832ff8c654015f8c2a0017fc434c00fffb08a82edf94154007faca980bbfc605500bff184a607ff58054007fea89807bff52d0c057e308a600ff1953003ffe82a1
  | 6 => 0xffe2a28005ff54c43047f8a2aa09f7f5294c0bfe3288607ffd87430c5fac4a18c2fd625500b7fb0e6018ff14943007fcc898003fe545400bfe9948607ff58e54007faa99801ffc61d00117f3288600ff5814308ffa43a808ffc6154c0b7f3188606ff5493000df8c02981bff424c0037fb2aa005ff5973003ff881a1823fc529500fffa0c8608ff9935302fb8a621807fd10d0003ff186800fffd855002ff8612181ffc62d0c0fff32e8007ff507430effe21a1823bf5455003fe102601fff8405306ffa63a005ffe6150c5f7eb0aa80eff94b40015f8c2a181fff4115011ffa94a636df54b54047fea8a9877fe21d0c57fe180a80fff4855003ff8852182b7f52cc011fea96a601bf9825316ffa642a0abff42d4c51fe106a607bf9925410ffa4029873fc50d0c0b7f31ca824ff4815303ff8842a017fd6110c49fea12a616ff8c143057fc8598037ff31d000bff9926000ff54d3000ffa8098063fe5250c0fffa1a8605fecc1300eff843a18a7fe31d4c077f310a805ff8c64303ffe85aa002fd60d0c0fffa1e800cff5094002ff86529823fd52d500bffb00a620ff50453015f8c2a9857fd5210c0bfe324a601bf1824304ffea3980c7fe309502ffe98a8607ffd0843167fc622a023ff62d4011ffa9aa608ff9475003fbe86a1823df5354c2ffe8828601fe94350157fa65a98cffe5295001bfaa2a607bfd8b40007fea6a00cbfd3195047ff90aa603bf98a53057fea5980cbfd1095049ffb12a601ffc834002ffe65a980afe611500ffe300a80eff8cb400e7fc41a187ffc4014c23fe20ea034ff0835402ffca79801ffd65d0c19fe3128004ffd0530047fec9a8017fc3194c03fe1826013ff0804307ff882a801bfe624c0117f328a605ffd885307ffca2a801bfd324c00def9926007ffd8a5400dfac19801ffe54d0c0dfe2126029bf58753005fec89801efe64cc00bfe1966005ff5824301df8c4a0003ff5450017ff90a8008ff18754045fccba1867fe5090c03fe086a020ffc4053047f8a329817fd6194c53ffa0ea600efd915302ffe64218bffd515500ffe21a802fff90554046f8a029817fc30d4c0b7fb14a618ffc81430c7fc64a18dbff32d5003fe082a01dff4874317f7a82aa003fc53d0067ff194a801ff90340047faa9a8023fe5015009ff18a6020ff88453004f8ca9801ffc5490c0bfe3008605ffcc54300fb86098016ff6110c497fb12a600ff55150037ba64980beff615500fffa0ea80bffd854002ff8639801ffc6195041fe108a600bf58f541a7f861aa017fc6114c65ff98ca800b718d5402ff8602181fff4110c11feb06a81fff88053117fc20a980efe62cc00f7fb0ca808ff98b5304ff8a398017df3210c11fe280a605ff4c84302dfcc72181ffe62150117f328a830ff8c954047fca229843fe425400ffe2108600bf5
  | 7 => 0xa00101c048158700322e40801410e00c0500700e0040500002e0f11880600a0081400e038020000090500001081204c0280000e00c000200010260001805e1553081200f0040000085300403004830000014030400860300084500e0000580509c014070360240600000803c03c0699c0b60000101e0060780001102011c000000001540001b0000100d00c0660100000008e0340c807012048428080260000000100008c00006024160010040000040e8000a80ac160370a0000090c0316014030f204019c0400701c0000004c00200400000120138058550601e4018040000041100206608c028420300280001a010068498000000900100000000c4100000cfa4030180900900d0040040000180413e00f120060280700014b0280000001c01410800032000044008000000418d00008e0000086a00003c020120100048b802010000004ae506038010290540481009f00200403804024114428020c6000098000020000b80000200000005114014d30230680801280001e00c038100c8075d802f00c020030020020080f80700c0100e81d0002180584f034018dc00904c000000020000e01a0020b20000480013405c0380c0a80080000c12400c0d863050040008034a80a41a80900a008000012781d803800006004010040160000aad6000028030060060300080c0bc05403004012000038080065040700100e0d001000000018000000020800016202a02c0882b00000c2800003c0e401006070064018020000d00280001e0280800400400c001960100240000200401c010070620040401d006148000140002c4198450440480081105a3e00700d008004110100000000b82800002c0039901a0000001413a058060200060dc068140140000083e02a0101200a002170040b10020001f02101628ff9035302ff8a62186ffd5290c1dfe2968036ffc835403efacba0057ff2010c0bffb24a636ff8cb54047fcc1aa047fe21d4003ffa868001df1415003ffec72a003fd5494c0bffb166005ffd84530b7f8c0a1847fc21d4061fe192a808ff5485400ff82198017ff3290c6bff98ea80fff8855004ffca398007fd50d0039ff0868609ff10730047fea32985ffd5150c33fe1048634ff9035411ff842a9822fc6550c017eb048608ffd5053047fcc9a801ffe41950057e30ea00fff08550197faa32a00efe62d4c03fe286a015df5484303ffc802181b7d524c0017fb028608ff1835400ffc41a80027e6510c077f316a807ff59740117fca0a9823fd61d4057fe100a808ff1875317ff862aa007fc50540017fb2a8600ff50f5000ffca0a0007fe20540317fb128632ef50654047f8a8a98abfc42d4c037e300a830ffd895403efccba0002fd6094c037e304a600ff90d40007fa86a8023fe60d4c55bea96a608ff9535003dfec5a189ffe4294c0
  | 8 => 0x984200300a0d41500b0000586104a03a000000000060000988215200c0100a0220180a80000a0681880300601c0602900002c0325212a006b900e0020a80080b00e274008000b60000b80a0121505280000a0580000a0041a40a80100601c0382f0200041206b02a4b4000510b40000000200001c000000000000100700606402000134058000010541c0008170080100101c0da0610a01e016000088020520000302f15c0600380200259c0189b0060600100000800c0
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf649915002ddf7214f4303e7f75597400067e51d9543006bd32191530079d7050c43005bc7458d500067f52597400467c50590530ff78301953001cfe72d8d40006df2018d541a67e109974003f9c435514303f3f63d52540cebc10d9130046fb505805302cfc745834300cfe7058e54004ff715834302f5d62d4e530067c4219530176fa60d815409ebf20191300467e655533020f5f54d4f4302d7c735515302cfd7359330006be70d91530067c74d9530006dc6218d5402cfd75d8153005bf7454f400063f65d91300467e6514f40004fc7650d50014fc7158f5402f5d64d4e53266be5319153004ff715825302edc6350d4003e7d5458c543175f41d4e53046df7358f541ef9e7250c43006be7619130006bd31d913002e7c3099443004fd725974303f3f62d525403e7f409944325edc4118d541d67c32d9530005df735524302edf32580430067f6555140005dd7315130004fd72d9540044fd70d915009ebe30191300067d2199740004fd7259730046bf5459053006bd61d91530067d315974003ebc4058043006de41d8d54004ff7458f5003e7c5459740006dd51d8d5412f7830d95300073f521915309fba101913003dbc7454f430475f71d4e5325ddd7614f432275d52d4c430467d72195300067d65d52430473f549515300cfc70d95432af5f52d4f4324ebc30d915303ef8405834324f3e65d524303cbc74595301c7bb30d9130006dc60d8d541767d10597400467d7299443005bc7454d300467c7199443004fd7650f50176f8605815403cfe7694f40006de21d8d540b6df3058f4002edc5359443006bf41590532b75e5014f4303ebc6410d50004ff7158f50014fe7159330004ff7259543004fd76d51300cebf6490d400fe7e10195301c6be73d9130014fc71d8154014fe71583530475e70d4e5324f3f53d5243004ff7258343006dc73595403175d10d4e530069f321913003e7c74994430cebe50d9130004ff72582430067f1099443006bc21d9130265bd7315243006de5218d540063d52d91300079d7550c43004ff71d815303ebe711915303e7c74997400467d70994430cebd40d9130004fd7258e543473c31d5254006bf10d9153006de70d8d540067f5259643006dd4118d542aedc50d8d5402e7d4359443206df5418d540467d701953002cfd70d953001cfc72d814312e7f6594d50044fe76d0f500067d74d953003ebd7219153006bd62191300067c42d9530006bf21d913002f1d6550c43044fe76d95400067f51594430467f5258f54006be5219130004fe7619543046fb7058353006be311913000cfc76d4d300067d21195300467d739974001cfc72d8d50006dd32d8d5403ebc64d51301767c1059740046bc54590530467c73195300067f215974025edf4118d5400cfc705974330f5c10d4e5303e7c6455353
  | 1 => 0x504312e7c10d953000cfe70d9130006bf64951531bebf3219130005bf7458d5024f9c53d50430067c32997400067d52d9150006bd4159443206bc51191530067d52d81530067d31d953002cfc73580540fe7d4019530004fd72d8154006bc611915303ebf701915302cfe7695153004ff72d9543006bd41d91300067f52d8d5009f9c30191301a67c50d915002e7e3299443006be31d9130006bd62d913000df87055140044ff7654f4303cfc7458254006be52d9130004fd75d91300467d7119530006de6118d54006bc71d915303e7d7499443006df6398d400067c51594431767f205974024ebf75d91530067e31597400067f21d9530006bd4259353006bf64d513002f9e6550c4302cfe76d533003ebf415944320edf63995431d77b30d953020f5d65d4f430b6fa30d814303ebe64191501767e3059740044fc75583430467f72997400b4ff70591300079e7550c4302f9c43d4d4320edf42d8d540067d20994430067f755913031f5f20d4e532079f53191530073d7519153006be621913003ebc545944320edf75d8d5412e7c70d9530176fa40d8154006bf52d91300cebc4058243006bf41d91300467d719974003e7f41597401d67c43d9530006bd51191532ed7f7255153004bf745954303e7c41597400075e50d8d5403cfd73d81430047f7559130006be40d9153004ff7558043006dd42d8d540fe7f6518d50004bf74595300063c65d91302af5f5214f4312e7d40d953000df87050d30004fd71d95300467f63551530067e5159730004fd7694f4003ebe721913003ebe6419130006be2119153014fc71d81533175c41d4e530067c21d953002efb70580431ce7c32195300073c64d515303e7c4299740006bf621913000dfa70d4d300067c52d953024f3e53d9153005fb7054d3003ebf731913000cfe76951500cebd10d9130006bf641513003e7c40594430467f7099443006bd6519130014fe71d95430447f7299443014fc715973003cfc7458e54005df73551530047d7299740004fd7258254006bf645515324ebf6499543014fe71d91300467f525805420ddd74d4f43046df5358f54006bc60191530067d525825402edc435905324ebf31d9153004fd76d4f4002cfc7358253004ff7259643005f970d0d3003e7e40994433175d41d4e53006be75d9130004fd769513024f9c73d5043005dc73595400067e52597400075d32d9530006bf745954303e7f7459740044fe76d95430057e75991300067e7059443004fd76151300067c50592532aedd6514f43006dc31d8d54176f820d815402cfc745974300cfc7654d3002f5e60d4e5302e7f319944302d7e73d51531ef9d2050c4303e7c645515303e7d415974003f3c60d5254295bd71d52430079d4310d50206bc5019153006bd4159053006bd71d91302059c7550c43006b
  | 2 => 0x6dc20d8d541df9e1050c430067e21594430067e31d95300067f6514d40006de62d8d540067f65d5130006dd6118d540457f74551530067f3259740006bd6490f5002e7e4359443004fe7690d50006bf425935302cfc73d953000cfe70d9530004fd765513001cfe72583540073f52191301767e605515333f3c30d525401cfe725944302ddc7355143266bc31191530e6df30d8d400067d31195302079c531915303f3c63d525402cfc7358243006bc72d913001cfe725935303e7c439974025f5e5418d540067c51d95430067f41d95300467e7099740004ff725935002cff7690f5002f9f6250c43206bf5019153005dd73952530473f70d5254004fd7159743004ff7258f540467e72195300475c70d4e5320f9c40d4c4302cff73593300473d71d52540075f52d8d5403e7d4099740006df70d8d540067f52d915301cfe72d91530067f52d95300067c651913003cfe74d8d500067c21997401e79d2150c43006de42d8d5402ede6318d54206df5118d54004fd725804300cfd735804302ef8305805303ebe731915327ebf53d9153004ff715935303ebe641915301cfc7258f540067f2199740006df7359130146df30d8d5002e7d53592530b6fa60d814303ebc6450d3002cff705805302e7d5359053014fe715964300cfe705944312e7d73d953002f9e6150c4302e7f7399443004ff7458053006bf51191303473f10d525402e7f43594430cebf20d91300067f651513020f5c54d8d54046dc5358f5403cfe74d953003cfd75d815403e7d5458e54004ff7359740006dd52d8d541cf7b3019530004ff7058c5402cfc7614d4003dbc7015243006bc41d91300475f63d515333f3c20d525412e7d10d95300475e72d4e530067c5059743004fd72d91530067c71594430cfba10d913002e7e535944302ddd76d4c430cebe30d913001cfe72d95400467c709944302cfe73d81540067c50594430067e2059443006de5118d540467e65552432aedf50d8d5401cfe725905301cfc72d915003efb40580430067f52d8d400447f72195301ce7c4319530005fb705515002ede6318d50006be611913002f9d6050c43006be511913002d7e7355353006bd5319153006be76191530467e7019530014fc715944318e7d50d954027ebf73d9153004ff71d913024ebf30d9153006bd20d915303f3c62d525420ede64d4c430467f52583540467f72994430067e7259443006bf6119130006bd52191530067c211953001cfc72582540067f651913002ef830580430067d52583430067d5259053004ff7654d4002e7f30994430067d5259253006df6398d500075d32195300067c71d95300457e7510d50004fd7614d401a67c60d5153006de71d8d5403f3d76d5254005bf7454d50004fd72583530067f2119530014fc7158f5003cfc7558f54206bd65d
  | 3 => 0xf72d9540115dd73995303473f31d5254004fd71d8154006df6118d54006bf61d9130014fe7158253006bf42582430047f7259740006be51d913003edf4358c5403ebd721913003efb405825403edc4358f4002edc7018d5402e7e53597300063f52191530067d6554f4300cfc7059443006de2018d54006be61d9130014fe7158f540047f72594432473d52d5043205bf72d50430067d6219530006dc71d8d5402f5f61d4e5302e7c315944302dde73153300cf9c30d913020edf40d8d54014fc715835309ebe20191301c6bf32d91300067e10994430cefa405824302e7d73594430e4ff735913012e7f20d95302fe7d62d515301cfe7259643014fc71d915003e7f425944303cff769513002f9c6050c4302efb30580430067e31195300067f65d91300467c5058354014fe7159053006bc20191530475e74d4e53004fd7158254004ff72d8d5002d5c735535312e7e30d95300067d52595300067d411953003ebc7019130006bd611913024ebc53d915301cfe7259743006bd21d91530467c65d513002ede7118d5403ebc711913000cfe76d8154044ff76d513002f9e64d4c4303e7d43597400065f52d8d540067f411953002f9f6150c4300cfe705925312f7a10d9530006be32d91531a67c10997400447f7299740004fd71d91500067c41d9530006be60d915300cfe76d815302dde75d4f43144ff73595300067d219944302cfc73d913002efb70582430067c50d9543006bc72d915303e7e64d515328f3e50d5243006dc70d8d5402ebf745933002f5e53d4d43006bd425804312e7c5058253004ff72d9530004fd71d81530067f515974002ef8305824301cfe7258254004ff7158f400067c515973002e7c73994430069d321913002edc6390d400075c735535303ebf425804302cff7610f5003cfc7459530006df325834303ebe6410f500067c7059443006f920580430067e52d953001cfc7259330006dd3258043004ff725825400cfe70d8d543057d72d5153006bf62d9130007b91019130004ff71d95400467e7119530006df63d4d402073c50d504302edc735944302f5e64d4e530067d319974002e7d32594430467c6594d4024dbd73d504302dde73d51430cebf73d9130006df10d8d540067d52594430067d5159443205bf71d504303e7e4159443006be62d9130006bf64991300467c6515130006de60d8d540067e515974002f5d60d4e53004ff7258f500047d721953000cfc70595430073d52d9153006bd6219153004fd72590530fe7d101953001cfc7258f4001cfc72d9530014fc715824303f3c61d525401cfc72595300067d52d9130014fc7159540004ff71d95300b6bf40593300fe7c10195300067d62d953000cfe735933003edf4358e54014fe715805402e7d305944302ddf7414f43006bd65d91300067d41d9530
  | 4 => 0x814303cfe7459443006de40d8d540467f5258353014fc715974002f9d6150c430067f621953000cfe7059743007b910d913012e7d70d953024ebc32d915302f9e6250c43006bd321913000cfc75d8153004ff7159130006be71d9130046f850583541e79c2150c43006df6398d540cdbe70d5243014fc715834302e7c329944303f9c4350d400067f6554d4301cfc7258253004fd76153300067d52597300447c755913003e7c405974002cfc7610d501a67e309974020f5e65d4f43006be40593531d67f32d95301df9e5050c430057e76d515302d9f7650c4312f5c30d9530006bd4159643014fe71582430cdbc70d5243004ff7058f5400cfe74597401767e205974002f9e6414f4301cfe725804301cfc72594431ef1d5250c4309ebc501913003e7c419974003f3d61d525427ebd65d524303dbc7454f4020f5d54d4c4303ebc72191301bebe531913002ede7418d5401cfe725973003edf7358c541767f655515001cfc7258c5401cfe725825301cfc7258043004df735954303edf7358e54116f820d81531e79f2150c433273d415535327f3f52d52430067d52583540467f7199740004fd715973030f5e20d4e53006bd611915301cfc725805425edc4018d54004ff745953002ddc735513000cfe76d0d30266bc301915303ebf75191530067f62d95300067f52d8d54116f8605815303ebc64d0d3001cfe72580531ef9c5250c43006df6314d400473f73d525424f3d53d5043004fd7158c5430f5c40d4e53006dc61d8d5434f3e32d52540073f52d9130044fc76d513003ebf731915303e7c429944309ebd3019130006df31d8d5401cfe72d815403e7d419974027ebd65152430067e62d95300047f7558243004ff74595430fe7f20195300cebf6498d40006bf6450d300057d7510f5002cfd7359730006bc42d915312cfe7619530006dd72d8d54005de7618d540067f65991300067c65d9130005dd73951530473f549515003e7d42594430067f75595400067d52582530fe7e30195300067e71594430473f7455353176fa10d81540067f76553530067c4119530265bd76152430067f7559530006bd425824301cfc7259353206dc5118d54004ff76551300067e319974003dbe7414f400067d52d954303e7f7499740004fd7259253006bf101915302cfe76d8d5027f3f52152432e67f62551530067c725944303e3c64d515320edf65d4f430467c72997400ff7a101953000dfa709515034f3d20d5254006bf51d9130006df735954303cff76153303273f415535303e7e7459443006bf61d9153006bc511913001cfe72d9530006bc62d9153004ff72d814301cfc7258353006be10d915303e7f419974003efb70580543357d7255353004fd72595401a67d1099740014fc7158254004ff71595430067d7259443014fc7158053004f
  | 5 => 0x467c71997402069c5319153046bf74593530067f1059443004fd7259643014fc71d95400067d5258f403357f7255353006dd20d8d5403e3c74594430067d3259740005bc7454d50004fd72d953002ebe4359253046bf74593500467c6554d4303f3d63d5254206dc5018d540067c219944303cfc7654f40005fb7055140006bf6490d50006de32d8d5403efb4058343004ff70595431bebc311913002f5e65d4c43006bd2019153006be50d915303dbe75d52430067f61195300067d52d814302ebe435905302f9e4354f4324ebe73d915303cfc7558354006bf21d9153006bc51d91301fd9d7250c430067e6119530004fd72d8d54006bf71d9130004ff7358354006df73593530067f6550d30004fd7654f401767c7059740006dd5218d5403f3d62d5254006bd64191531df9c7050c43006df63d81540063d52d91531e79e7150c431e79d1050c430467f5258c542aedd76d4f4302dde73d524302efb3058243006dd5118d54006dc6018d54004fd725834302f5e62d4e530457f7655353005bf7454d4003ebe7119130004ff7259540006de4118d54014fe715944324f9f32d504300cfe7655140006be2119130006bd5219130006de2118d5402ddc7355243004fd725974003cbc74594430067c20594430067f52595431ff9f7250c432a5bd72d52430067d525974302fd83054d301ce7f32195300467f7319530006bd5119130004fe7650d5003e7f4359740014fe715834309efa1058043005fb7050d302279d42d4c43004ff75593300067f2199443006bd61d913001cfe725954327ebc52d91530cebe20d91301767e6055353004ff72d8d4002d7c7355353006be42593501767d30597400ff5c301953001cfc7259253005df73553300447c75582431767e50d8154004fd70d91530073f549533002f5e53d4f4303e7d4099443006bd75d91300067f51d9530004ff7459730014fc715835402edf7218d540473c72d52540cebe70d9130006bf62d91530067c755913002ddc735525303ebe7319130266bf3119153005f9709515002f5e53d4d3003ebc64551531df9c1050c4312e7f6598d500467e7099443044fc7558f40004ff725953020f9f42d4c4325edf6514f43006bf41596430467c71195300057f7558d40006dc30d8d5403e7e425944303ebd731915302e7e73994432aedf74d8d54014fe7158f400067f73597400067d65195301f79f7150c43004fc765513002cfc7655330004ff7158c5401cfe7258243004ff75583430067c51597400067f61d9530014fe71d8d540067e51d95300067e61d953002e7e535964303e7f755974320ede54d8d54006fb70595402069f53191530067e62195300067f5259330005df7355150014fc71d8d40004fd7259443044fe76d9530044fe75d8143014fe71595300067c6599130004fd71d
  | 6 => 0xc64d515302e7f5359253046f850580540079f41d8d5422ddd72d4c4331f5f42d4e5303ebc6490d5003ebc701915302e7d3199443044ff76d53300b6f860581430067f705944303e7d7459443014fc71d8d54004ff71d8143004fd73d95400067d7059443014fe715804302cff7614f4001cfc725805300cfc74d8143005fb7054d50006bd71d915301cfe725834303e7e405944301cfe7258f4002edc6310d50004fd715825302e7f535905300779101953003e7d43997400067c3159740046df5358c5401cfe725974002cff7559443014fc71d913002e7f31594430467e65d533000cfc7058e5427ebe75d91530067f755824309ebf50191303175e41d4e530473c73d525402cfd74d8143004ff705925309ebe405804300cfe70d8d40014fe71d81430463d76d525401cfc72d954001cfc7259053006be71d915303edf7358f40006dd21d8d540467d709974024ebe63d50433473e21d52542af9c54d8d542aede75d8d54006bd10d915312e7e20d9530006bd32d91300065d65d4c43006bc21d91530067d109944303cfc76d4d4312e7c40d95300057f72d95303473d21d52542673e531915301cfe7258e5403e7e41597401a67f20997400067d61d9530006dd325834303f3e75152430067e74d9530046fb5058354004fd76953300075e5018d540467e6554f43004fd70d8d54006dd4218d540067f52d8154006df72d8d54006be61d915301cfe7258f5003ebe7019153044ff76551400067d515974002e7c43994430467d7319530004fd7258f540067e2159740004ff725925302f5e75d4c43004ff71d81540067f525913001cfe7258f54005dd73153302af5c5014f431f79d7150c433175e21d4e530cebc50d91300067f52d954003dbe74d4d4302f5c61d4e531c6be53d913025ddd7414f4325edf4218d5424f3f75d915303f9c43d51430077910d95300073d52191530cefa10582430467f525935303e7f4059443006df71d8d5403dbf711524303ef8405805402e7c305944302ddc73551531ef9e5250c43004fd765533002f5d61d4e5303e7e43597400473c71d5254004ff735954312e7a50582530067d71d9530006bc10d915303ebe72191530057d7599130266bf3019153044fd70d8d50006bf64d0d300067d6594f400067c6550d3009ebf6418d40006bc6454d3000cfc7650d30006df6310d500067d5258f54006bd31d9153006bf651913000cfc70d8d54146fa305835302f5e61d4e5302edf65d4c4301cfc7258f500cdbe761913003dbd76d50431ef9f5250c430067f329974000cfc7559350176fa50d81540067c10994430073f645515303ebc649515302e7f755944303e7f5458c5400cfe76d51401167f505973002cff70580430067d52596430fefa10580530467c7299443006be32191531e79c7150c43014fe7158e54
  | 7 => 0x8d54014fe71583540473e73d52540473c70d5254004fe76d0d500065f5218d5418cfe7619540004ff72d913003e7e7499740004fd73d915020edf6319153006bf20d9153004ff7159740006df3258f54004fd76d533003f3e54d5140014fc7159130006bf65d913003e7c40997401df9e7050c43014fe71d81540067f2099443046dc5358c540467c6055353006de31d8d400067d32d953003ebf7019130006bc75d913003e7c74594430067f71d95300467c6555140004ff72590530067c75582430067c72d9530014fc715974302e7f3059443006bf611915320f9e74d4f430457f72d515302cfe7359443006bf42d9130014fe71d815320edc42d8d5402f9d6250c4303cfe74d8153006df63581541767f5059740206bf531915303cfe7614f4025f5c5418d54044ff7655243266bc531915302e7e30994430067c71597401c6bc31d91300075f5218d54004fd7159053006bc611913009ebc2019130004ff71d8d540067d52d8d500067f755954303e7e5459743006de4218d5402efb3058053006bd211915303e7c419944312e7e70d9530044fe7610f5000dfa7094d500067f5258e5403e7e7459740006dd71d8d5402cff70d953002e7e32594430467e65d5243006dc72d8d540067d2059443006de6018d54006bf72d915302e7e7359443014fe715913012e7c73d95301ef9c7250c4320f9c74d4c43004ff705944302edd7614f430065e5018d54006bf71d91530067f65d5140006f910d815400cfc70d91300067f65d0d30206bd76d5043004fd7159543044fc75593300fe7e2019530176bf405935000df87054d300067d6554f4003cfd745974012d7e7619530006bc745953000cfc76551400067d61195300467f63d51532071f54d4c43116fa1058f5003cfc7654d43004fd725835403e7d42597402bf5d5214f430067c51d953002c7c76551530475c72d4e53006bc70d915302cfe7695330004fd7610d50004ff7258e5403f3e60d5254006bd52d9130006bf64d815334f3c32d5254006be41d9130004fd7654d4302cff70d9130004fd715953027ebd76d5243004ff72580430fe7c401953003f3d60d5254006be52d91531767e5059350006dd62d8d5431f5d42d4e530065d65d4f43006bd41d91530067d525805403e9c4358c542af9f54d8d540467e6519540006bd51d913018efa105825402ede6318d40006de10d8d54004fe7610d5027ebf52d915303cfc761513003e7f4199443206df5018d54004ff76553300cebe40582430475d72d4e531ef9f2050c430067d5259740014fe71d8d4003e7d4199443006be21d913002e7e31994430475e71d4e5303e7f7499443006bf41d915302f9d6550c4333f3e10d5254014fe7159743006bc65191302cf5d52d4f4303e7f42597400cebc73d913002edf7018d5400cfe70d915303e7
  | 8 => 0x467e71997401ce7e4319530014fe715954002e7f32994433473d10d52540467f5258f5003e7e64553530067f42d95303175f10d4e5303f9e63d5043266bc32191530475d70d4e5303ebc751913003ebf711915303cfc745973002cfe73d9540006dd6318d40004fd74d8153006f9105805303f9f435524300cfe705935320ede74d8d54005f97090d4025edf4018d540067e72d9530004ff715944324f9e73d52430cebf50d91300467c7099740116fa10d815302cff7359730004ff725913024f3f53d504302edc63d4d400067c65d0d301d67c31d95300067f659954303ebc4358c540067e51d95400057c7558d400467f52593500065d52d8d5403cfc76d0d5003dbe7414d400467f701953002cfc7558353004fd72d9543004ff7058e54006dc21d8d5401cfe7259330004ff7158354004df73595400075d52d8d5402efb7058253006be62d91530067f52582430067d321953003e7f43997401e79f5150c43174ff70595401767c2059740006bc65d9130004fd7259543006df21d8d543473d31d5254004fe7655130014fe7159543044ff76d4f4002edf7518d54004ff715964333f3c10d52541a67d30997400067d52d915302cfc735825424f3d65d52430073d52191300067d52d953003ebd751913000cfc7059643005df7355140004ff71597300067d655533002e7f755973003e7e4259740004ff745835309ebc301913002cfc7694d4003f9e6315243006bf7459530004ff7258f4000cfc7650d40006bf6458153004ff725933002cfe76553300067d735974002edd7118d54205df72d4c431a67e2099740014fc71592531e79e5150c43004ff7259743005df7358154116fa60d815301cfc72597400063f52191300067d51d95300067e41d953000cfc73d8143006df1018d5403e7e54594432179e40d4c4324f3c53d9153006fb20d8154006dc2018d5403dbe74d4f4300cfc76551503473f21d5254044ff7654d430467c7019530004ff75591300067e21d9530006be425905309ebf10191300067f71594430067d65d4f430067d72597400059d73d52431d67e43d95300467e731953003cfc74d954000cfc7558f5001cfc725974302dde73952530475f72d4e530467f525805302e7f7359443006bf6454d300475d71d4e53006be1019153014fe7158c54006f9105804302ebc43593302059e7550c4302ef830582530fe7e5058053006dc32d8d540473e70d5254006de7618d54004ff7159743006de6218d540067f72d9530006be60191530067f655514300cfd75580530b4fd7650d30046fb705835401cfe72d81430fe7d30195300b6bd4059330006bd42d913003ebd73191300079f7550c430cebd73d91301767e5059540044ff7654d3003e7f5458e54014fc71d9153014fe7158f500067d52d8d403473c21d52540075c50d
  | 9 => 0xd52191530067c3199740044fd74d81540063d4159443004ff715935020f5d54d4f432773d5215243006bc425935003e7c4259443006be32191301df9e2050c4303ebc649513003ebc7319153004fd71d8d54006bd641913003cfc745805325edf6319543005f970d4d30006dd2018d54004fd715974003e7e7499443004fd715835302cdc735944302cfe73d953024dbd73d524302e7d43994430067f7259443006f910582540073c651913002efb30582530079d41d8d5403cff76151300467f7419530116df3058f5003e3f4159443005bf7454d430cebf10d913020edc54d8d540079f7050c430067e76195300067f4219530006be5019153006dd6318d500067d65552432075f52d4c43006bc62191530467c6554d3009ebd201913002edc6314d4000cfc7058c54006df32d8d4024dbf73d5043006dc6118d54004ff715933003e7e4199740006dd10d8d54004fd715805300cfe7654d3002cfc76d5143004fd7159253006bc211915303e7f405974012e7f50d95301bebf3119130006bf211915303ebe751913027ebf51d915300dfa70d514003dbc7454d400079c7550c431767c30597400057d7510d500467e741953003f3f60d5254006de4018d5427f3c50d5243014fc71593533473e31d52540063f52d91300067d42d9530006f91058f500067e105944303cbe76d91300075f5394f40004ff70593530067e2199740004ff72d8d54014fc715953002cfc7559353006be6519130006bc621913003ebf65d504301cfc72d9153014fc71580541ce7c311953002f1e6550c431a67e60d5153206bc52191531767f10597400057f755814303cff769533002edc7118d54005f97094d5001cfc72d815402edc7218d540067f5258254006bc61d913002cfe73d915001cfc72591300cebc20d91300473d72d52540467c655514320f5f75d8d54005df7359150004ff735935003cfc7459443006be51d915303cfe76d4d43004ff7059643006bf6219153266bf641954302cfe76d8d4003ebe7019130004ff7258353014fc71d8143006dc10d8d541a6bf40d91501a6fa40583540fe7a10195300067d215944302cfc735974003ebc64551300467e6594f401167d505973001cfc7258354004ff71590530075f7355153006be42d91300067f65d4d430067f525954002e7c53594432479d32d50430073f65191302079f74d4c4302cfc7358354005bd7414f40006dd6318d5402f5c62d4e5301cfc7258343004fe7654d400067d651954309f9e30191300069f7650c43006df735953023dbd71d50430067d32997400067f6554d3002e5c7359443046df7358f500057d72d95300067e411953024ebf32d915300cfe7058c5401cfe72592532aedc52d8d54006f910582430075d7518d5402f9e6050c4318efa5058254046fb50580540067e2119530
  | 10 => 0x9530006bf41593530067f52d81530473e71d5254004ff72597400467e65d4f4320ddf74d4c43004fd7258053006de50d8d54006dc62d8d54006bf645513000cfc7058f5402e7c53597300067d52d8d540cebc70d913001cfe72d91301767f705974001cfc72d8d400067d72d9530006bd73d9153006bd101915302ede7518d541c6bf31d9130004fd72d81530067f5258343006de30d8d54116fa50d815302e7c32594430475f5394d5001cfe72595400073f65d9130174fd76551400467d71994430475f539525302e7c73594430cf9e30d9130014fc71d954320edc41d8d5403ebf72191300cebf70d913003e7e43997400067c51d95401767d2059740044fe75d8d40006bc40d915303ebc751915303e7d7459740004ff71d8d400067f715974001cfe72d8d5027dbf72d5243006dd3258f542aedf54d8d54006df6350d40005bc74595300067c61d953001cfe72d8d54044fd73d81530457e75d815401cfe7259350004fe76d513003e7d429974003e7c4099443004ff7158043014fc71595430475c74d4e5303f3f61d525401cfc72d8d5402f9c4350d300467f7119530005dd73d514324ebf65d524312e7c20d953003f3e65d5043006bc64d4d30006bd6495253046bf5459353004fd74d953000cfc7359730006bd4159353006be6119153006bf649515003e7f4299740004fd7158f5031f5e42d4e53006bc64d815301cfc72595400067e42d953003ebd711913000df87050d40004fd725913002ddc735533002f5f64d4e530467e7199443004fd725824303ebe6490f5000cfe70d9543004ff7259443004fd72d9150006bf645515029f3d52d5243004fd72d91300cebf40d913003dbf721524320ddd74d4c431e79c5150c4303efb70582540475d74d4e530467c65d4d4303e7e40597400467e6554f40004ff72d9150014fe71593530079f3219130006dd41d8d540475f70d4e5302edf7118d540b6fa40d814300dfa7090d40004ff7359540014fc71d8d5034f3f20d525420edf41d8d540073d52d9130004fd72582530067d5258353006bc71d9130006de31d8d5427dbf71d52430067f3159740266bf65152430467c6514d400067f525804302cfd70d913002ebf74592530475f5355253004fd7158e54006bc1019153006dc63d815409ebf30191300cebc30d91300067d42195300067e5059253046f8505835330f5e40d4e53004fe7615130014fc7159350046df5358f5003cff76d0f501a67e50d915002e7f755964309ebd5019130014fe71d95300067e7259740006dd31d8d5426dbd7115243046bc54593530467e65195430073c645515325ede5418d542fe7f62d5153004fd7690f50005dc735515003edf4358f4020f5f54d4c4301cfc725964302f5f60d4e530067e505905300cfe7694d500063d65d50430b5dd73991300063
  | 11 => 0x2cfe73d913003edc4358e542aedf52d8d54004ff7650f5003c7d75d81541ef9d5250c43006dd6218d5402e7d32994432079c5418d5400cfc70d953000679101953000cfe705964303edc4358c54014fe7158053004fd725805402ebf7459053006dd2118d54004ff7650d50014fc7158253014fe7158254044fc755913002cfc735925302edd7218d540cebf30d9130044fc76d4d40006de61d8d5400cfc76d514027ebc50d915302f5d76d4e530067e20994430473d70d52540067c10594431a67c209974002d5d76d4e530475c71d4e53044fc7650f5001cfc72582431e79d5150c4301cfc72d954324ebe53d915303cfc7458353006bd311915302e7d3159443006be72d915330f5c20d4e53006be31d9153046dc5358f50006df20d8d54005bf7454f4303d3d76d525412e7f40d9530006f910d815302edc7518d541e79e2150c430fe7f101953033f3e30d525403e7e42997400cebd50d9130006be32d9130006bf6495130004fd74d8d5003ebc64951500073f52d915300cfd7458043014fc7159330004fd75d8d4003ebf7219153006bd2119130005bf7454d30006bf74591301bebc53191300475f635515302edf7418d540067d52593300cebd20d9130006be30d9153005bf7459530004ff72d8153004fd7259353004ff7258053014fe71d95400067d5258c540067e50597430073c65d913003ebe751915300cfc7459740006bd6410f5003ebf7119130004ff7358254004fd7614f40006bf72d91300067d52595430047f72d953031f5d20d4e5302cfc735944302e7d3099443006dd5418d5402ede64d4f43006de52d8d54004fe7614d4034f3f32d525402e7c43594430067f215944312e7c30d95300067f5259253006be3119153006fb70591301767c50d815403ebc64551500067e50594430067d7159443006bd72d91531767d505974003ebd70191300ccbe7619130006be52191530467f71994430067f52d915002f9c6550c430067d651954027ebc51d91530057f7559130004ff75582430067c215944301cfc72d81530fe7c201953003e7e5459740006bf7459643004ff72593530067c6119530004ff7258c54004fd715944303cfc76951301df9c5050c43006be20d9153006bc62d913003ebd711915302f5d65d4c43006be65d91300067e32597400067f6594d400467e72997401767c6055153006df73597431767f3059740004fe7694d40014fe71d8d500467f525905301cfc725935003e7d4059443175bd7499540044fc755804303efb40580540475f74d4e5324f3d53d52430067e42195300067c7259740006bc41d9153004fd76d0f50005dd73d524303cfd70d9540014fc715905302f5c64d4e530067c5259443004ff7358054006bf70d915300cfe7359730004ff725805403f3e63d5254206bf521915312e7f10d
  | 12 => 0xe75d4c4302edc6394d500069f4118d54004fd72595301a67e505835402cfe76d51430079d4310f500067e32d953000cfe76d4d3002f9f7650c43005bd74995300067f52595300467c6555130006dd32d8d4002cfc7615330006dd61d8d542e67d625515303e7d41594430065c5018d540067e2199443004ff715824320f5e54d8d5400df87055150014fe71d915302cfc76953300067f65951300067e52594432d5dd72d4f4302cfc76551430fe7e401953003e7f409974012e7d50d953000cfe76d814330f5e10d4e530067f6559130006bd4159350044fe75d9130006dc6358154004ff70590530073f64d5153005dc735915027f9f53d91531ce7f311953001cfe7258c540467f70997400067d7159740006be6219153145df73595301a67c30997400069d4118d54005df7359540004fd725933025edc4218d5402edc63d0d5012e7d20d9530004fd71d9540116fa30d81530ff5e3019530004fd7158343004ff715925302e9c435905303e7f41594432aedf51d8d540067d215974000df87054d50006bd51d915302f9c6250c4312e7e505825303cfc7458f50004fd7159643006bf20191530067f5259743006de51d8d540067d6514f40285bd721524303cfd70d8d4003e7c54594430e6fa3058343014fc71d953003e7e64551530467c741953000cfc7654d500047d7259443004fd71d913003e7e4199443005be74995300067f5259443014fe71d915002d7e73551530467e7399740004ff7258354006be21d91532069f5418d54006bc645815303ebc71191530467d741953009efa20580430067f52d913003e7c545974312c7e7619530004ff71d9543004fd7159350004fd7158f540067e50d9543046bc545935003ebe6455253004fd71d95430067c62d9530044fc755824303cfe76d913002f9c4354d430057f721953002ede7018d542673c531915302cdc73595400e5df7359130006bc60d91530fe7c301953002e7e439944303ef840580431a67f109974009fb83019130006bf64d4d3002f5e7514f430fe7f4019530014fc7158e542f57d75951530067d52d81540079f4118d540067d52591300067d1059443006bd32d9153005bc7458153006bf75d9130046fb505835302dde73951531fd9f7250c43006df62d8d5412e7f70d95300067d52d95400079d4118d542079f5418d54004fd7258f50006df63d0d50004ff725973009ebe1019130006bd645525312e7e40d95300067f6555130006df6394d5002cff7694f4000cfc7359330006df73595400067d65d4f4032e7d62553530067d5259353006be30191530079f32d913000cfc7458f4012f5e30d95301d67f31d9530004fd7258c54006de1018d54005dc7358154014fc715964303ebc745944301cfe72d8153014fe71597402373e50d504302e7c53596432069c5418d54
  | 13 => 0x8254004ff71582540075f321953003cfc7458253004fd71d8d500cfb830d9130006df32d8d54004fd7610f5000cfc70d8d401bfbb301913003dbc7454d430067f52d954301cfe7258054004ff72d91531df9c2050c4303e7f429944320f9c54d4c4302edc7418d54005bd7414d4027ebf50d9153014fc7158043006de5018d54255bd72d504327f9d73d5243004fd71580540457e7510f50006dd70d8d54005bf74581530063d5219130006dc2118d5402e7f43994430047d7259740206dd65d4c43004fd7258f400467c65951300067f65d51430467c65d51400067f725974027f9c53d915303ebc73191302079f73d50430473f72d52540467e7299443004ff7158f5403e7d42994430fe7f301953009ebe5019130006bd52d9153006df2118d54005dc73551402aedd65d4f430cebd70d91300467e76d515301cfe72d9150006bc211913001cfe7259530006bd42d915303cfe74d9540006bf649915300cfe7690d40006df6354d501767d7059740004fd715913024ebc31d915303ebd7615243006dc31d8d400067d52580430467d729974002f5c60d4e5302efb705805303cff74597400067f2059443006be51191530067f52582530067f319974000cfc70d915302e7c319944300cfe7058f54006bf211913003e7f7459443206dc5218d5403e7e40997400067e32195300cdbe701524312efa1058253004fd72d8d400057c75581430067c655913002cfc7690d500075d5218d54004fd71593300067f65d4d30006bf42d91530067d5258e5403efb7058343006bc521913003e7d74997400467f625535301cfc7258e5409dbc70d504309dbe70d50430059d74d4f4303cff70d954000cfe705905300dfa70d0d30006fb70595300079d32191300067c73597401c6bc53d913003e7c415944302cfc76d533003ebc72191530067f74d9530005be7619153046bf545935003e7c42597400057d72195300467c50580530fe7d20195302c5dd7214f43004fd72d8143044fe7690f50014fe7159730006bd21d9130004ff71d915318e7f50d954033f3e20d525412efa5058253005f970d5140004ff715953002dde73151300075f32d9530004fd70d95430467c5059350006bf7459540004fd71580430063d65d524302ede7218d5402e7d7399443006df6390d4003f3e54d51430467c739974003f3e75d504331f5c42d4e53004fd71d9153004ff72d815402e7e3159443004fd71593530075c5018d54006be41d91531bebc32191300447e76d95300067c621953003ebf75191300473f71d52542073f52d50430473d73d5254266bf3219153014fe7159253004fd76d0d500467e65195301a4ff74595400067f659953012e7f30d9530005bd74d4d43005df7355143114ff70595301767e1059740004ff7654f4024dbd76d5243006bc61d915302dd
  | 14 => 0x3175d21d4e5302edd7018d540473f74551530063f52d91530047d729944302ebe43593302df3d41551530067f52597300067d52595400063c6519130006bf5219130006bc20d9153004ff71d8d5003c7c75583540067e5159443006be20191530067f659954002f9c6150c430067e73597402ed7d725515303e7c4359740005df73552530057c755913002f9f6550c430467f72195300067e71d9530004fe76d4d4003cff7650d3000cfe7650d3003cff705805425edc5418d54004fd75d814303e7d40597400067e71597400067d5258f5003f3e61d525412e7e10d95302df3f415515303cfe76d4f4020ddd76d4f430067c209944302e7e30594430467e65d4f4003ebd70191531767e705974002edc7359053006dd1018d5403ebc6415130004ff715835300cfe7059543004ff71d91500067f5258f4000cfc76d0d3000cfc7059253004fd71582430075f735535303dbf73152430067c2159740005df7355130006be42d9153004fd7694d4002e7f3259443006de72d8d5403e7e4299443114fd7654d3003ebe64952530465d76d4e530073f5495130046f85058053004ff70597431c6bc32d913009ebd1019130206dd76d4c4302cfe76153300067d65d5330004fd7690d5020f9f41d4c43004ff715805312e7f73d95300075f5394d4002cfc73593501a67f3099740006bd6419150005fb7050d4001cfc72d9130004fd73d8154004ff74582530067d21d953002cfc73596433175c21d4e5301cfe7259130014fe71593501d67e73d95302af9d74d4f43004fd7158354006be72d91300065d5218d5434f3d32d5254004ff7558f4002ebc4359253006bc42590530067c52597403175f21d4e531a67d2099740014fc7158c54006fb20d815303e7c74597401777a50d8154006bf6410d5003cff765525300cfc70590532aedc51d8d540067d5258243006dc1018d5400cfc705935302d7c73d515302edc6354d5003dbe75d5043004ff71580540075c73551530067c325974002f5f62d4e5321f9d41d4c430047d72d95301e79f1050c43004fd71d8d40206bf51191532079f54d4c43006bd70d915303f3d65d5043004ff7159540006bd62d91530063f6519130004fd7158f4002f9f6050c4301cfc7259543004fd72d8d50004fd7159540004ff725825309ebc10191300467f739974002cfc765515324ebf6418d54006bd31191300467c65d4d300467c72195300473f549525302cfc73595400067d5258053004fe7695130004fc7654d400067d5259350006df61d8d54006de20d8d540067e32997401767c5059540006bf4159350006df6218d540cebe10d9130004fd7259350006bd72d91300ccfe76191302addf72d4f431ef1f5250c43006bc42d913003cfe76d91501a5bf745954020edc40d8d541ff9d7250c430473e72d525403ef8405
  | 15 => 0x1200500900003300003e2c701100900000800000b00b02301700408800c02a02c01c02b01700a02612401000000100001401800a02f00500102d02a0aa00900600f07301b0ae01f02700003100107801200400001600600600b01600002a01b1b700404b00304706a02200206c00003b07c09600b00000306100700a13c0050a10080df00312411600d0020c100006d00100000f09c01301d00905f03712000300105900a01a00f00000000703701f00200003d0382414a101d00a00103c13801d02000300d01903400000a05f00807002402300101308600404e00100600103d0020460c201000710000f00100600800000a00508a00300601100100c01500000100009000000000407300903600000702a0010d200407001500401a03900500c00400104500302700806a01500000a01202100400300b03000b00000d0940140280350f80010000c900900003507111200200000000014603c01900200106b00300f05c01100d00000f00400907200000207500000005f00901e08603300b00c00007b01a00200401200100702c00000000e00000800003b01502a02900100500000000000200b00702c00100300000b06600500007803200700a0020002c000300200100000600200002a00200100900300e01900300101100300001c00005501405d00001200005100502f00605c08b05b00000805700001e00500000e00601c01403032100603a00429a00600301200b10400005400201000103802900000000301402c00c02002400001300300a12e02700000300500c0020080140dc19615d0a500100000400d0000630210770a302e00502300000028301b07d01004402602a00700000801600900600402410e00703e04a00c01611000400000a00600002302000200101800000002200705b00702b00500400502d00000300006400000300000a00000a02800002601f00016b00700001500000000b0560110eb06a0110ce05000000300e02b09b01608100c00600500006502600907600000500206100000210402102c00100e01f02300800402108100c06400100000200d00200202901b01701000100000100500105b00000c08302108801200000800005d04a0041640031ca07401701000900008200000300300003604300600000f0150390b700101700800603302601905900f00000f01403207501500b00b0000251881eb02b0010a202400100100402c00f02f00e04200501000300b15a01536509702000003c0020000140150010200d600000200404b0067f52d8143006bc52d9130014fc7158f4001cfe72d9543006f91058253006bc4059353206df5218d54004fd76d4d400079d32d9130004ff7158e5401cfe725835302ebc435905303f3e54d524303f3e62d525401cfc725973003ebe63d5243005bd74d4f430467c65d5143
  | 16 => 0x2a03c00401000605208800200100003000905007c55e10d0000040000020ea00200207401b04904e0000120a702e01b00000000000001f00302400300000200400701b02b0040012200aa02000200700100300302600b08d00005000101c00202d01201300400604700300205000a0c102900105d00100200001c00a00200700700004800200303902f01003a00f00201900100900c00101300000401901800a00600000217200000701904624000000900300302400700002b00d0000020c60150080000040140530100060fd0900270ac00600506900c02008500001e01602707800e00301606c01c0000140040160290190000000250cd69805c00206602c00000000603900002e30801400300503e05c01e01500400204a00804801e00600204e00400012f00400d03500509504518105f00100002a00303a00700001700a0e400c09d00200900e00600001101200003d13d00200223c00600300f00401c03504903e01900a00000700000200500b00302601800000022900c00601a03d0000220b90040
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa3c85587644c00147d0ca96c8980dea7a0f21191300147a40ae4b2e8000a75819c16510c110fd0f90cca218021f61c32997400051ec2842322a600a3d85087644c00147b09308ca981028fa1421191530054e422c631aa0058dc835d853500110f90e884ca218022f61e62191530051f432a43226007ab8844416010c014f30010cca218028fe1562191300051f42c643226055a5e8590b635500117f08b92c1298029761642d8d541bf0f298c9a9a6005a5c835c16510c6fd1f04990c8980028f61020594430055bc0ac4322600887e87dd56090c0117b0e106c8a981e2f21172582540054ec2043b1aa80387c875496550c110fd0e104ca218021fa1c21597400051ec2042b28860087d82dd56090c010fb0e10eca98002a760c10191530054fc1aa2322a6408bc875056510c011bf06bb2a898002a7e197550c430052fc2a2031aa800c3f751d1654c0051790ea0ac82980237a1c20d8d5440e4e21ee4b20a64ba9c8454463550070ff0ea96ca98002a760f21191300043ec3ce5b2a601fc7a76443654c00117f0eb08c8a98030fdd375582430043ec3e433288600ad681940635500147f08b28ca980029d60650594430046fc3ac631a8000a76819c16510c0147b09188ca980221fe0972997401c70f29ec9a9a600087f855d9544c00147d0b196c89810387d525018d540053dc2a20b04a608a3e8510964d4001d60c2880c8980023761e42d8d540054ec2041b1aa800a79800856510c015ab03286c6aa07f9ce0510195302645fc3ac92a4a6018f8805c96550c010ff0eb28caa001e8f21365d51400043f43e43b2a600587d855d843d400153b07280c8a993e8fa1420d915300636b92a5b2a8600e71100426510c0b1b906b8acaa00023de0572597300053cc04e2b2e800087d870856510c011bb0e10ec6aa1028fa16321915300637b92a4b2a6000a3f8558b644c0754bd07216ca98002ade0562d913003c3e42ae4b06a86c87d879c965d00014790ab10c8980028f21562d91300052fc1aa4b2e864ca9e830406454c0147b09316ca980021fa1b721953002c3e42cec21aa000d1f759d54310c0b4bd07282ca218029e602211953003d1f4246332e8055a5e85c83635500117b0f328c898003ac18510d91301bd4fc12643226040a5e85080635509393ec8b9ea8a18031b5c952d95400051ec2cc23226040a5c85880635500147f0a988c8a98e3271cf645513020d2ec28e5b1aa80787c855c560d500147b09392ca218029760c21d953003d1e422a4b288600ad980087635500117f08b92c898002b5a042018d540053b40ca1b2a86078be870806454c01d2a83880c6aa12e37e1973952531d52ec3ca031aa800c3f659d2654c0eb47d0b328c8980029760e725944302d2f41842b28860087e87c816510c0b4bd0610cca218031bdc95259730
  | 1 => 0xd0dba2a6a00028fe1161d95300443e42ae4b00a60787c85dd953d000b1bd0f210c6aa1b30f1d152595303554ec1c64322600087f87584654c0110f90fa92c1218161f21d65553301d53cc00e3b2a6000e1c65cc8644c00156d03286c8a99332718c7454d500043fc2ae4b2a6077c7b72440654c001c3a82280c6aa10387d935218d5425d4f424a231aa80087d878ca65d00014eb02102ca21802aee0162d915300637b92a4b2a8000a79809c56510c9317f08bb2a7a00029761432d8d540045ec3c623226037ab886440644c00153b08080c6aa0029761672d8d540046fc3ac231aa800e1f419406355097d2f02a08c6aa0039c44010594430061e3aee8b226000a9d84948635509753d08100c6aa0662fa1e31d913009d4e432643226000a798094565d000b8bf0eb2ea6218022f61e32191303de2e39ee4b288619a9d831cb644c02757501288c8980028f21d41594430063cb84a1b2a860087e87d49644c00b938e6b22a92995796d4250d8d540167838a20b00a600e585084063550814b90a880c6aa0230f9d56410f5025d4e42e8231aa800a3c86d48644c0ab53b08396c6aa00b3c9c510d81540045ec3cc43226000ad58198063550ffc3ceba08c6aa0028f614201915325d4f4202031aa800c5f76dcd54d4c110fd0f190ca9801e2fa1c211913024f4619265b22a600a9d839446454c0b1b9063b2a8980969ea0021d95300070f424a031aa819aba80947644c0715710c886c8980038bd8952d915300667b94e5b1aa800a9d830806454c01c3aa5bb2862195717197735513000636b90c5b2a6000a3d840866510c0117f0eb20c8980021f61f21594430051e436a5b226000a7980904654c0018bee739acba00028fa1421191301bd4f418a4322600087c87549644c0059e0e2882c12a00a1fe1d51d95300051e42ac23226000e954144063550010ff0ab8ac02192747dd073553533d62e41ae4b288639a5e83084654c0014bb0b196c6aa002ae20162d91532052e42a4031aa819a9c864cb644c00153f06a90c8a992667e1973d524303d1f42462b2e8019a9d83dd7644c00147b0a108c8980028f61231997400443e428ecaa26019cb870d91434c00147d0a10ec8981c7878c065191300053dc02e4b288600c74815c96510cab53b09b86c6aa0971e1c36554d300051ec20413288600a5f85880635500195ee5396c8a98ea97a0c72d95300055d404a2322a607c3c7459553d00014bd0610ccba01b38710d5258c540062fb2ee6aa28600a9e86d04635501117d0fb22a89800387e115218d540055ac0840322a60887e870ca65d000147f0a886c8a9a0b2710f7258c5403d1f42442b2886008fb805c96510c0147b0bb26a8980022fa1c20d91530070fa08a031aa800a5f85480635500f0fd0f28acba013f8bd4a52d915300637b92a4b26a600
  | 2 => 0x232195300052ec2c8431aa849a9e830876454c1147d0a212c82984e2fa1b7454d3025d4f4244231aa86cc3c745c96510c0b4bd0738aca218021fa1f52595300056a40ac5b1aa838ab9801c7644c0814bd0b210c6aa002b6a0271d8d540051f42e42322600087d8710b654c09f17d0fa0acb2181e8fe1d65d50430053d404a2b28864fa3e85c836454c9953d06100c8a98021fe1571595400461e32ae932a6040e2f825486454c014b900a90c6aa10387e1165d4c430072c304a031aa800a3e85987644c0f70fd0e292ca218221fa1771d81430443fc12e432a60008bf87590645400187aebb2086a80028f61672d91300046fc3ac631aa861c5f75dcd654c0014d904b08ca980169720d715944300c6f436e6aa26000ad78158b635500117d0fb22c0a9802ae60021d91530051f42e43b226000a3e85984644c001c5f04a90c898002a760c21191300043fc2ae4b226000a3e848c7654c04b4bb06396ca980163720d71594430056b40ce1b1aa808c6f825ca6510c834b90ca96c6aa0029761421d8d540051ec24e4b2e8000c74815c965d000f47d0828aca218029d60420994430443e42ae2b00a600a9d84084635500117f0eb28c8980029760c10594430054e41ac8322a073a3e86194644c0050f90ea8acba00028fe1162195302ad2f42843b1aa805a9e83d91434c00147b0838aca21802a76102018d5400717c12a5b2260088be8790964d400153b06108c8a990667e1974d4f430056ac0ca031aa8038ec825c565500335750038ec898156a721941d8d5412c3f43ea4b04a600a3c86548644c05d4f100a96c0aa0023de05725974003c3ec2aec29e8000a3f845c96510c110f90ab8ac0218028f61021997400074631265b226000c3d741d3654c0010ff0fb10ca980029be0961d95300070fa96eca18860387c875496550081c3ea8a90c6aa00b3c9c51058f500054ec1843b226041c9f635d35350c010fd0f216ca980030f5c941594430147a40ae4b22600087e87087654c0efce6e2880ca980028f21952d91302052f42e4031aa800a3d84084654c0059e4e2886c0a98030fd947454d300063d082e432a60008bd878c86454c010fb0e10ccba0017171cd655533035c3f438e4b2e8000c78805c96510c015b300108c6aa00297a0c21597403b61f3b6ca3226008c6f825c8654c0014bb07382ca218169720f65d4d30007688802031aa800ad5810836355001c3aa5a08c6aa0029e60021997400051e42ac8322600087f87594654c00b4bd06082ca219270f1db64551531d43fc2aed21aa055a5e851cb635509f4790a886c8a9a032710d72590530053cc004232a6000c9f76dd54310c694f100a92c1aa003ac44010d91530051f424c5b2a6000c6d72d8b654c00147908b0eca9800e1f21d525974025d4e422a431aa800a3d848c565d000317
  | 3 => 0x332e8000a9c8650c43540011df04b8ac8980021fe1571583430cc5e43ec8a9a600087d87c8665d0083c3e82b2ea6218029d20572597400055bc0ac4322a600a3d85c806454cd98da84b94cba0156a761071d8d540045f438a3b226049c9c73d915454c8353d08396c6aa00a2f21d41593500051ec2e42322600087d878c8654c0018f100b92cba00028f61442d91532ac6f43c85b1aa855e4f8254b635509f17d0f18ec8a98031be0972597400054fc2264b1ea800a3d85c846454c0117f08b92caa18022f61e611913036d4fc1ac232260008f7815c9654c0ab4bf0eb2ea7a180237e1d6318d500145e43a82b26a63487c8754960d50015ab02100c6aa002ad20562d91530055cc04c2322a60087f855c56090cd947f0ea90c8a992f2719073551500062fb2ee6aa2600887e878ca65d000f47908b92ca218961fe1576151300070e32a64322600087f874416510c81a3cea3aa862181e8fe0541594430147a40ae4b2a8600ab6811036454c0147b0b90ec89801e2fa1e31191300147a40ae4b2a6008c3e655d053d000163f0ab8286218023de05725944327e1e32ee8a9a606ec3e76548644c0010fb0f904ca218029de0562195300043ec38c432a6000a5d830826510c01ce0c2880ca9801697a0c20594432ad2f42ce5b1aa86cc3c745496510c0147b09882ca218e2a7e116318d400061fb2ee8a9a86008bd87144644c09f47d0b396c8a98028f61021597400064fba0e6b2a804ba5c86548635500f17908b92ca2180393d8952d8d5402c6f4384031aa838a9e831cb644c0015b50128ec6aa00297a0e725974024e8fba0e6aa2a6058dc835c965500010fb0f216ca980028f61261d95300070e42a8231aa84c99e87dd54310c059e0e2882c021802ada0420191530443e42aec2a260418df865cf5490c01d1ec4990c89800a3e21d105804320d4f42043b1aa807a3e840856510c8187ee2b2ea82190787d8c64d51532af2ba8ca3b1aa800a5f85504635500147b0b196c8a9907175d763d81540043f438cab226040a3e85c846454c014bb07210ca980031de0572597400043e43a20b288600e1f52d0463550015b50130ec6aa003875494118d540062fba8e6b2a804fa3e851cb6454cd787e83b92ca218028f61642d915303d1f424a0b288600a3f85584644c0014f50138aca2181e2f21172580430073920a2032a6000a3d8414565cc0014bb0738aca218029d20562195300052fc1ae2b288639a5d8714063550934790ca96c8a9802b660031d8d540070ec24a031aa800ab5819436454c0147b09194cba00029761420d8d540070ea0ca031aa800c3f75dd1654c0014f30010acba00021fa1c20594430443e42ae2b0686008bd878c76454cd7878e9a92ca980028fe1561d91300052fc1ae4b2886038ec825c56010c0147b0918eca980028f61
  | 4 => 0x5d00d747f0fa90c8a98031bdc9525954300c5e422eca9e8000c3f725056510c0147d08108ca9801e8fa1310594430051fc22e2b288600a9f8350964d4c0187acbba2a7a01ee9761f5218d540053c402e4b28864ca9e839446454c010fd0ea92c8980029e600319974025e2eba8c7b02a839c5c731c16510c335750010ec898102a72154118d540052ec2e2031aa86fc3e76d48644c0014bb0a108c6aa0023761e6118d540052ec1843328861fa78804c8654c0734f10c880ca9801e8f213715944327d1f42843b22a600a3d850876454c010fb0e10acba00028f61021d953001c76412e2b2a60038bf8750b644c00117b0e108c898002b6a025118d540052ec14a031aa800ab980947644c07153d0638ec89801e8f21171594432052f4284231aa8008f7815c96550c0117b0f196c8a995b17dcc655913035e1e3a6a4b288600ab9809446454c015af02b10c6aa002ad60420d915300c6e41aecaa660498bf865d353d0cf50fb0f392ca219ea97e1d5218d5403d1f424e0b28867ac6e325ca6510c010f90ea92c121802a760e40593530051ec2464b2e800087e870856510c011df04b8acaa002317d8e76d51530064fb20e6aa2a000a5d839c965d000147b0828ecaa18eb171ce70594430fd2e4326432a6000c3f74549654c00147f08902ca218062f2197414d400051fc2ae1b22a605ad8834416010c0156d03300c8a981e2f21171594430443f4388432a607ba5f87d48635506f53d07290c898002b6a0031d8d5402d2e41ae4b288600a5d830816510c018df04b96ca9804eaea0021191300062fb28e6aa28000a7b85441609509f87ccbba2a7a0002b5a066018d540070fb2e64322601f87c875496014c815390ca08c6aa0e78710c6550d3001c3e43aa4b2c86028f8874416090cf58da64b94ca2193e8fa1632d91530051fc22c5b2a6078c7887440654c0014f30010eca981c78e84065191300043fc2ae2b2a6000e1f525046355081cb500280c6aa01697a0c209944302c6e41ae4b288600c6d728ca65d000117b0e108c8a9802a7e115218d5400636b964232a6000ab6819c36454c071bf0e996c6a01f7879d54118d542070fa9aa4322a649e1c835975410c010fd0f192cba000237e0d71591300046ec3841b1aa800e1c835486454c0f17908b92c1298023de057258f542044fc32e7aa48640a9e85d04635500153b0d3aa86218029de0572594430064e3a6e6b2a600587c855c560d4c0147b0938aca2180e2f21d425935300637b92a4b2c8672e3a10197644c09353f08aa0c6aa002aea0021191532654f41ca4322a64f8be878cb6454c0117f08b8acaa18230fdd3765535301e5739285b22a600a5d830856510cd947b0b290c898066a760c71d91300052ec1ca5b2a60038dc874c963d50018dae4994cba013f8ed4250d91530443f4384
  | 5 => 0x98021f61c20594430045fc3ac232260028df874c763550014ed02102ca218029e60031597400045fc3ac8322a67ac5c73549655009953906a88c8a98039c4c510195300064e3a6c6a9aa000a3d851cb644c0014d904b0eca980034754973d52430043fc3aca32a860087d87988654c00147f0a880c8a98029da04209944324d4f41841b22a605a5e839c16510c015ab03386c6aa0031bdc9525944327c5f438c8a9a6007a3e848ca65d00018eae328ecaa18028f61051d95401ce2e398a0b288600a7a800856510c0155f04b08c8980038754b32191300051ec2465b2a6000ad9809c763550814790a988c8a98eb171cf65551300061fba6a4b2a6007a3e841c565d00018f700b92cba0002b6a0021d8d540046fc1ae2b2a8000a79808c4654c00f17d0f188c8a98029761763d4d400147a40ae4b2e6000a5d8308665d00110fd0f90ccba00029ee01525973003d1f42040b288600a5d83d965350001c9ec4a90c6aa0029760e42d95300063cb922032a60018dc865cc544c0059e0e2882c12992f17e1d65d4f430fd3d4048232a607cc3d75d92645403317d0c3a2a69815717197735514301e6739265b1aa800a5d83084654c00f47d0938aca2199f0fdd774595400043f43885b2a601fa7b81440654c001ce282880ca980021f61e611953004637c12e532e807fe1d75d04635500153b06290c8980029761720d8d5420d4f42041b1aa8008de87d8d605509fc6ea328ec8a98061f2197510d500051ec10ca32260198be87d096090c014bb04280c6aa01e8f21120594430054ec262031aa807c3c649d6644c00147b0a106c8a98022f61e32d91300451e436a92a26000a3e86d52544c0011bd0e31ac0aa002aea0251d915300557c12c3b226000c3f655d2654c00f47d0828acba00028f61271d95300046fc1ae2b2a8600a5c8359465500010fb0f90eca9801f0f1db54951300052ec284031aa840a3e850806454c0f47908b82ca218028f61071597400053a40ac5b2a6000e585044063550015b501308c6aa0028f60865d913027d1fc3acbaa486038df874cb635508153d0aa08c6aa0028f61221594430147dc3a21b02a600ad98098763550014e902b92ca21802a760c20d91530147dc3a21b02a86cc6e425ca65d009753d09280c6aa016a720d41590530043ec3864b2e8077e7071440654c0110f90ab8ac02a01e2f21176951301d52f41843b2a60078bc845d8544c00117b0e100c8a980297e0d6594f400056a40ac431aa800c5f735496550c010fb0f210ca980029ea0251d95430055cc04a2322600087d87108654c00157501308c8a98029e60041195300072d286c7b02a855a5e85c8763550011f700b92caa00063e201725944301c3e43aa4b2e8600c3e75d92644c001c3a82b2ea62180a3d20572594430056dc02c5b1aa807a3e840866
  | 6 => 0x55ac0cc0322a67ac5c735c96510c0153f08900c6aa002ae201621915312d3d400e3b2a6000ab980907644c0011df04b8ac0218038d50710594430062e3aee6b22603ac5f651cd5454001d6220080c8a980387e0d52191530070fa96643226055a5e85083635500b4bf0eb2ea6218028f211651953002d4f41c84b20a637a9e83084644c083938c9b9aa8a981e2fa1c51191300074bb0a8231aa8078bc845c9654c0814790a880c8a981e8fa1232597400147c43a20b00a60087d87c816510c010fb05baac8980022fa1c645815327e1e32ee8a9a860087e87c8565d003317f08bb0a89801e2f2107654d401cd2f41c8432a60138bc875096010c734bf0e280c6aa1268f61472d915300717b12a4322a600a3d84988654c0011bb0f310c6aa0028f61462191300443e43ea4b226007a3e841c56510c7153d0610ec8980eb8710f6550d300051e422c432a6000a9d8494063550070f90bb92ca980028f613659513012e3db2ae129aa0008bf87588644c0010ff0e884ca2181e8fa1272597400053cc04a2b28867dc9c735056510c0147b0828eca9810327e1973d52433ef0e39a82b2886028f4815c963d500147b0a316c898002b660251d8d5402e4f43eeca18864ba9e8408463550015b100b16c6aa10317194735514001c3fc3aa5b2a80038ec825c5644c00147d0a216c89801e2fa1e321913035d1ec3ea4322a6028f8874416094c0117b0e28ec8980030f9db64d51530056cc0063b1a804cc3f875975490c838bee6b2aa7a18028fa1462191300051f428c5b22600787c855db544c09f53b06396c8a981e8fa1020994430043ec38413288600a9f8350564d4c01c3eca990c8980162fa1e425905335c3f438a4b2e8000a7a800866510c051e902b92caa010297a172118d540058e42ae0a188600a9e8650c435400f17908b8ac0218028fa1232195300051ec24e0b2886008bf845c5644c0014bd01a90c6aa10327e1974d4f430046fc3ac431aa800ad5810c363550758beca39ac8a800317dcd525954012d3d406a4b04a6078be878c86454c0187ae2b2ea82180a2fe1d41d915303d1f42042b2e800087f855c5644c00f17d0e108c8a993f8be0952d91530054f41c84b26a008c3c659d2654c00117b0f308c8a99ff271cf41590532ae2fb9ea4b2a8600a3e84984654c0814bd0b880c6aa00e1fe1d52d95430054fc32e0a1886038f8874816010c01cad03280c6aa0029de0562d95300054ec24a231aa800c3f65dd1534c00b0fd0f292ca219ae8fa1452191303a54fc1aca3226007a3e849c96510c010fd0fa92c12190387d8f521915303c5e422e2b2a60008ef825c5654c0010ff0eb10ca980ba9e20172597400056b40841b1aa800c3d751d7644c001ce0c2886ca980221fe0972994430063dc02e4b28860087d87c84654c00156d03280c8a
  | 7 => 0x1f8550463550014f700b92cba000e1f21d52594432654f41842322a64ca3c865486454c0147b05b2ec898126a7a0c72d91530055cc0043b22604fa3e85d056590c018bf06b92ca21802a760e52191300061fbaee8b226007a3e840866510c01c70ca886c89812ea72112018d540052ec1842b2e8000a3d8598b644c00147908b08ca980028fa1b52191300052fc2a21b1aa807c3f875975410c0147d0b396c898002b6a002118d540443e42ae4b226000c5d75d8c43540014f700990ca980163720d71580430043ec2ee3b0286008de87087635500187ee83aac121802ad60440593530047dc02e4b2a60008f7815c9644c0110fd0e108ca980028fa1472d91300072ac0ca031aa839a5e83904654c00157300108c8980028fa1262195300443f4384332886008dd8708063550014ed03282ca219078721165d4c430043f43ecab226000a3d859cb6454c0156b03280c8a98038754932191300070e422a431aa8008bf845d9544c001ce462880ca98102972154118d5420f4621285b1aa800e7121440654c0015b700b10c6aa0221f21572582430051f436a5b226000ab9809876454c0b938c6ba0a6a00034754974d4f430043f43e42b28862587e878cb654c00f878c8bacc89800237e0d72595400052ec2e4031aa8008bd878c7644c0015ad03286c6aa002ae60021191530056b40861b1aa841a9e841c7635500147d0810eca9812667e1d7550c432051f42e40322a634a7a8008665d00d7878e9b92ca2195793d4a52d8d540061fba2a4b2a8600a3d85c876454c018bee7a92caa00ba9ea0031597402654e41aa4322a600ab5819c36454c0147908b16ca980021f61f21597400443e42ae2b20a600c6d72188654c03f4f500108ca9800a1f21d51594430045f43843b226000ab78158b6454caba3ea4ba6a7a1802ada0420d91530052ec2e43b1aa80387c8754965cc081c9f04a90c6aa002a76122118d542654f41ca0322a600c3e76d52544c09f47d0b90ec8a98969760f74d95300056cc04c231aa80087d870866510c754f10c886ca980ba1f61f52d81540043f43864b2e8000ab4815886454c4b4b90c996ca980662fa1e32d913000739b0a2032a6000a5d85c8463550014f30128acb98002aee0162191530061fc22e4b28860087d87084654c00187aebb24c8980028fa1271d95300053bc0ae4b2e8000c9f765d54310cf58b8e6a92ca218021f61e32d95300047bc0ae4b2a8041c9c64dcd544c00117f08b8aca98002a7e115118d540443e42ae2b048600c6d7254b654c00b4bd07392ca2181e2f210765513038f0e180ca3226034a7a800c665d000153b0610ec8a99e71ee1d101953027e8fa92e7aa4867bc5c73d49655000156b02206c8a98ba9ea0271597400054ec1ca4322a600a3e84147654c00117f08b92ca9812ea7a131018d540
  | 8 => 0x50000340000116e4000300d0820240400134400c00007000380208110340480a0060360440300802e004018000ea0281f8321d60a80580117c0280003a0620086800006a2d01e80400400c140000063e80217f01c0940306801e024000150060140000718e214020f40300002280500812c000080020000d0040422083c02a0c60fc0c88b01e4b0300000320102f02e01a09451061018000028010120400e9b60020000002013a0d82380400a0180180f000000040023761e4218d540443f43e413288600a3d840416510c0b1bd0e108c6aa0028fa1231195300052e42ac631a800887e87c84654c0059e0e2882c1218029be0961195300051ec16ca3226000ed110043635500147d0b310c8980031bdc952597400055a40ac43226041a5d85dc3635500fc6f02a0aca2181e1fa1f65551300043fc2ae2b2a8600a3d85987644c0015b100b10c6aa0023761c2118d540070fa92643226000ab5819836454c754bf0ab18c6a8002ae60251d915303d1f424a2b288600aac82584644c00117d0e10ec8a98031de0572594430051ec2885b22600087e875496090c5d4f50010acba00063ea1b7050d300051f424c3b2a604ba9e84948635500156902b16c89813f0fdd3525954320d4fc1aa6322a672c3e76194644c081878ca3a2a69800a3e21d105825403c5e438c8a9a6000aba809876454c0156d03306c8a98023ee0172595430051ec2cc43226041c5c76dcd5454c0147d09196ca981b30f21172594433be3c3aa20b048600a3d858c8644c00147f08a92cb218029760e41195300045ec3843b22a607a3e840416510c0717f0ea16c8a99ef171cf52594433d70e21aa4b20a60387c87549654c00f938c8b98a8981569721510d8d540052ec1ca0b2e860887e85dc76054c0155904b0ec8981c2a760e62191300071aa0a20b28860887e87908654c0831bf06bb2a9981ab2710d7258c540fd3d4044232a600087d878c965d00015b301288c6aa0022f61c21d91302070fb20a031aa86cc3f415c96510c9387ee8b2aa92181f2719173951530056ac0cc1b1aa800a3e8598b644c03f4f501188ca980221f215715913000637c12e4b288641e1f631915454c0f47908b9acba01022fa1f6454d303dc3f438e4b28860587e8794565cc00117b0f188c8a980a2fe1d41d91300045fc3ac4322a600a3d858cb644c0010ff0ab92c1219fa1fe1571580530051f42c85b226000e4c624cb654c00147b0b216c898002aea0021d915300726312a5b1aa800a3f85590644c00b0fd0f28aca218028f61632191530fd3d4008232a6000e7221440654c0011bf06b92caa18031bdc952597430071c32a20322600787e8794965d00018dae5b10ca980028f61720d915300636b924232a6000ad6819836355075c3887282c8298028fe1161195300053dc02a4b2e8000e
  | 9 => 0xc0386d0760280000180000e08c2a01f00c0004380000405c470072a83cc00000000034098301260000884d0181e8210020020200280402200c0405d002000050115b8000030060600c80180a0020040780e000054000380cc1bc0e80700c0043b0040100481000000605c8700a0063382897703011c000050060a41d0160020002401700200051840010000120000640200a8010040040002d0023640981e008000000330000b0080fb01a048000000184ec050040000000f04200000001066048024000560f00140000200e000010670d40000880c004018228001360200182e01e04c038001900700682e1300040381a03419c08057000d4411801090014008100060340000443c14c0380300c1b00080400806c268180560800005100c0740000000e26c0d8090300ac010100560ec0e8020cc0000c0000340701000503601c0280a000028070000541080181200e1386080d0000040001b00007c090020020301301a0d2014000ba01c0041500b10407412a2c0dc4301e8820120180000001807401
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x100000008002000c000040000000210400080020427a5f8350964d4c0181d86dd67550c430058c65231440654c08181c7561a7550c430059464e41440654c08181f8654973d5243007185c921440654c001a518344010594430060b611728ca65d000121f985065018d5424c27a63765d54310c8181c7321d415944300487261525046355001870812017259443006161cc805c96510d07a52806065018d5400685a12819406355001e11411411018d54006a460d100406454c01858832017259443
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x9ca
  | 5 => 0x4
  | 6 => 0x9cb
  | 7 => 0x5
  | 8 => 0x6
  | 9 => 0x168a
  | 10 => 0x168b
  | 11 => 0xa0a
  | 12 => 0xa0b
  | 13 => 0x180a
  | 14 => 0x180b
  | 15 => 0xa4a
  | 16 => 0xa4b
  | 17 => 0x198a
  | 18 => 0x198b
  | 19 => 0x589
  | 20 => 0x58a
  | 21 => 0x58b
  | 22 => 0xe89
  | 23 => 0xe8a
  | 24 => 0xe8b
  | 25 => 0x1789
  | 26 => 0x178a
  | 27 => 0x178b
  | 28 => 0x18c9
  | 29 => 0x18ca
  | 30 => 0x18cb
  | 31 => 0x5c9
  | 32 => 0x5ca
  | 33 => 0x5cb
  | 34 => 0xec9
  | 35 => 0xeca
  | 36 => 0xecb
  | 37 => 0x17c9
  | 38 => 0x17ca
  | 39 => 0x17cb
  | 40 => 0x1a49
  | 41 => 0x1a4a
  | 42 => 0x1a4b
  | 43 => 0x749
  | 44 => 0x74a
  | 45 => 0x74b
  | 46 => 0x1049
  | 47 => 0x104a
  | 48 => 0x104b
  | 49 => 0x1949
  | 50 => 0x194a
  | 51 => 0x194b
  | 52 => 0x1a89
  | 53 => 0x1a8a
  | 54 => 0x1a8b
  | 55 => 0x10c
  | 56 => 0x130c
  | 57 => 0x14c
  | 58 => 0x134c
  | 59 => 0xe8591
  | 60 => 0xe8592
  | 61 => 0xe8593
  | 62 => 0x58e92
  | 63 => 0x58e93
  | 64 => 0x58e
  | 65 => 0x1a4d
  | 66 => 0x1a4591
  | 67 => 0x1a4592
  | 68 => 0x1a4593
  | 69 => 0x59a53
  | 70 => 0x1a8591
  | 71 => 0x59a92
  | 72 => 0x1a8593
  | 73 => 0x1a8c
  | 74 => 0x59a93
  | 75 => 0x5cd
  | 76 => 0x74c
  | 77 => 0x178752
  | 78 => 0x75793
  | 79 => 0x178e
  | 80 => 0x178753
  | 81 => 0x1a9791
  | 82 => 0x179a92
  | 83 => 0x1a9793
  | 84 => 0x179a93
  | 85 => 0x18ce
  | 86 => 0x5d8d1
  | 87 => 0x5d8d3
  | 88 => 0x18c5d3
  | 89 => 0x1a58d3
  | 90 => 0x18da53
  | 91 => 0x104ed2
  | 92 => 0x104ed3
  | 93 => 0xed053
  | 94 => 0xed052
  | 95 => 0x1a8ed3
  | 96 => 0xeda93
  | 97 => 0x1a57d1
  | 98 => 0x1a57d2
  | 99 => 0x1a57d3
  | 100 => 0x105a52
  | 101 => 0x105a53
  | 102 => 0x1a5053
  | 103 => 0x1a9951
  | 104 => 0x1a9952
  | 105 => 0x1a9953
  | 106 => 0xccd
  | 107 => 0x1a0d
  | 108 => 0xd4d
  | 109 => 0x59451
  | 110 => 0xd5791
  | 111 => 0x1a1791
  | 112 => 0x58cd1
  | 113 => 0x5c591
  | 114 => 0x5d791
  | 115 => 0x597d1
  | 116 => 0x59a51
  | 117 => 0x585d1
  | 118 => 0x17d791
  | 119 => 0x94e
  | 120 => 0x14a
  | 121 => 0x134a
  | 122 => 0xd4c
  | 123 => 0x1a0c
  | 124 => 0x1a9051
  | 125 => 0xb8c
  | 126 => 0x14c9
  | 127 => 0x184c
  | 128 => 0xd0c
  | 129 => 0x188c
  | 130 => 0x170d
  | 131 => 0x94596
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1629
  | 6 => 2578
  | 5 => 1225
  | 4 => 20
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
  | 8 => 2*((h/48+packedAt gbK8 (1612+(h % 48)*6) 6) % 62)
  | 7 => 2*((h/613+packedAt gbK7 (60273+(h % 613)*11) 11) % 1629)
  | 6 => 2*((h/873+packedAt gbK6 (123744+(h % 873)*12) 12) % 2578)
  | 5 => 2*((h/415+packedAt gbK5 (72275+(h % 415)*11) 11) % 1225)
  | 4 => 2*((h/34+packedAt gbK4 (1400+(h % 34)*5) 5) % 20)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe0f81f80ffc0ff83ff00ff04fd8e7c63ce73
  | 1 => 0x1fff001fff03ff07fc1fff001b62f19c7c739c
  | 2 => 0xe07fffe00003ffffffffffffe38301e3807fff
  | 3 => 0x7ffffffffc0007ffe00000fc03fe03ff83e0
  | 4 => 0x7ffffffffffff800000000fffc0003fffc00
  | 5 => 0xff8000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x26e028059454c849a1390256002c862c61c631
  | 1 => 0x1765000ab5515942a51a56020960b0946c5294
  | 2 => 0x400a5320000222944a44a8a86283014180294a
  | 3 => 0x2339d534698000773880c0cb403da02b683e0
  | 4 => 0x145ce69c78e3bce000103030dff400035b7c00
  | 5 => 0x98000700608030804200c0c0ffdb6df8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40449
namespace PEqualNP.Outside.L_meta_40449
open PEqualNP.Outside.L_meta_40449.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := bs0_5_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 6 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 56 := bs1_3_0
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
theorem bs1_4_768 : Interval s1Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 781 := (concat (concat (concat bs1_4_0 bs1_4_96) (concat bs1_4_192 bs1_4_288)) (concat (concat bs1_4_384 bs1_4_480) (concat bs1_4_576 (concat bs1_4_672 bs1_4_768))))
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
theorem bs1_5_768 : Interval s1Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 801 := (concat (concat (concat bs1_5_0 bs1_5_96) (concat bs1_5_192 bs1_5_288)) (concat (concat bs1_5_384 bs1_5_480) (concat bs1_5_576 (concat bs1_5_672 bs1_5_768))))
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
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 29 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 89 := block_range (n:=89) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 473 := (concat (concat bs2_4_0 bs2_4_96) (concat bs2_4_192 (concat bs2_4_288 bs2_4_384)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 56 := block_range (n:=56) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 632 := (concat (concat bs2_5_0 (concat bs2_5_96 bs2_5_192)) (concat (concat bs2_5_288 bs2_5_384) (concat bs2_5_480 bs2_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := bs2_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
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
theorem bs4_3_0 : Interval s4Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 2 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 6 := bs4_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 1 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 11 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 10 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 20 := bgb_4_0
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
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 73 := block_range (n:=73) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1225 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat (concat bgb_5_864 bgb_5_960) (concat bgb_5_1056 bgb_5_1152))))
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
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 82 := block_range (n:=82) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2578 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440)) (concat (concat bgb_6_1536 bgb_6_1632) (concat bgb_6_1728 bgb_6_1824))) (concat (concat bgb_6_1920 (concat bgb_6_2016 bgb_6_2112)) (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 bgb_6_2496)))))
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
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 93 := block_range (n:=93) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1629 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 bgb_7_672))) (concat (concat (concat bgb_7_768 bgb_7_864) (concat bgb_7_960 bgb_7_1056)) (concat (concat bgb_7_1152 bgb_7_1248) (concat bgb_7_1344 (concat bgb_7_1440 bgb_7_1536)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := bgb_8_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0feeaeee8fee0e0e0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40449.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[0,1]⟩,⟨.or,[2,5]⟩,⟨.and,[7,8]⟩,⟨.or,[1,4]⟩,⟨.and,[3,7]⟩,⟨.or,[2,11]⟩,⟨.and,[0,10]⟩,⟨.or,[12,13]⟩,⟨.or,[6,9]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40449

open PEqualNP.Outside.L_meta_40449 in
theorem PEqualNP.Outside.L_meta_40449 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
