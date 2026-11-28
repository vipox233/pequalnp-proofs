import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37229.Model
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


end PEqualNP.Outside.L_meta_37229.Model

namespace PEqualNP.Outside.L_meta_37229
open PEqualNP.Outside.L_meta_37229.Model
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

def SBf (j : Nat) : Nat := [7, 6, 7, 7, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37229

namespace PEqualNP.Outside.L_meta_37229
open PEqualNP.Outside.L_meta_37229.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1200f800c690174a00000101422a26053ab420131944606230008691140d49b2854e9238787875058010009058e001032001d200638a1520c1ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x12380000500c04005c9e14260060001800440a5a008a4e002200ae0090a0b4400016000200009c78009874009600003a00005210640082005600000062000000006a000608007a340000926c004800002c002a240000322800b6000000aa6e365e00000000b27094008e88540000000000000000a81a1c76000030002e20589a683c84ac72807e4aa68ca23e00000000000000a4b046007c00421e4c66860e00000102010002080206070000000200000800080103010101010000020c050eb7a92876c5250ebea6a15714d429faa2653c544cb9a64194f943419eaa4835f53506b8a6a0dbd4941b6292837b50506f0a0a0e7d4d41ce29a83af5250758a4a0edd4541dda82833c5050770a0a0ce141419f2a0836e52cc6daa598cf952319eaa4636e528c6daa518cf950319eaa0635e53c86baa790cf952219eaa4435e53886baa710cf950219eaa0435e53902baa7205b94a40b6a94819e539033aa7206b94a40d6a94813d519027ca1204f544409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xe04002086ca70a3191320cb0c5314941c6d4c50507185314141cad4850507285214141c394e52902396510010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2724+((h/30+packedAt s0K4 (2484+(h % 30)*8) 8) % 161)*8) 8
  | 3 => packedAt s0K3 (312+((h/2+packedAt s0K3 (304+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 3 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x84882808c489082016514a284a212954133615
  | 2 => 0x11245191091260c580a4148694c652a8c888ea
  | 3 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37229
namespace PEqualNP.Outside.L_meta_37229
open PEqualNP.Outside.L_meta_37229.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc82000748c0b28020508000080bf42bd42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x70000112009200a3300f26aa3a15594632c6a10652d52d069ca518e55043196a9081355110298a4985514530
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
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
  | 4 => packedAt s1K4 (212+((h/4+packedAt s1K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s1K3 (282+((h/3+packedAt s1K3 (270+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 2 => 0x3f03ffc1ffc1fff878383e0ffc3fc1fe94e73
  | 3 => 0xfc003fffe0ffe0fff803fc00fffc3fe0f18f9c
  | 4 => 0x3fffff0000fffffc0000ffffc000fe0fe0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x104000880008000008840422200444840210a5
  | 2 => 0x48a65910ca5138658321a3445642a85a694652
  | 3 => 0x292aaa2146a309aab042e9089aa83342b18b18
  | 4 => 0xb2cd344a943a52d35de84212ed33018cde0de0
  | 5 => 0xc30e387318c39cfc6673739c0e222210fde000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37229
namespace PEqualNP.Outside.L_meta_37229
open PEqualNP.Outside.L_meta_37229.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x5a34e202e100144a01300001c000266c123322000012740125c00000589c31f000001a00a908a160070000a400c2cbc1902a44c2b3c8940f029000500060c000020008302000020c24280ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x32820463c2d144aa533e160880e0a0bc8e5e2b854501e280000082128000079349b00a4b420dc560f279b4a4340006c22002c8005c6008198006b0b17000560fa1400071d8c4e804109bc324c000b400701a95092000c0000c02201a8ea24000747446311b8f083320a50233240689a222704c00123ea00580d001ccf441101ec18421310cce611c02c4e721f1c46400051a06c0318000547f1c9dcbe4500000ba00251d8003d3f16c001c0082400000b800c6001f81420041414083800002c043c040014004000140c0c000c381808000c1c640800143854b0081c2400381824cabaa5a1d794743aea86875e5390edca421db54843af2a0879e5410f9ca421d754843e6a90874d5210ebca221d754043af29c855d5390aeca3215d54642afa9a855c5350abca6215754c42af2a6655c54ccabca3995754332aea9c655e544cab8a89973d4932e721265cd424cab8a29957d4132af298655e53d06baa7a0db94b41b6a96835e53906baa720db94a41b6a94835f53506b8a6a0ed50441af2a4635c548c6baa518d794631aea84636e520c6daa418d795031ae2a063ce520c6baa418f354831a6a90635e510c7aca218d7540319f2a6433d54c86bca790d754f21e6996435f53886b8a710d7d4d21ae29a43cd32486bca610d754c21af29c815d53902bea6a05714d40b7a92816c52502eea2a05d14540af298815d53102dca4205b54840bb288817551102dca5985b54b30af2a6615c54cc39ca5985754b30e6a96614d52cc2bca3985754e30af2a2615c544c2bea4985714530eda82615e530c2bca7905754f20af29c415d538839a65105794d20aea9a413e540827aa8105794c20aea9841cd32082eca2105d54420afa9e215c53c42bca7085754e109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6988000c80010084900b8058e00001c01e480000028000b1400aa980008b032001a2800420011439358a51d0e4f625434395986544cac5619093293195424cb0c545093293588535064d629523193d89508c64d621503196580540c70d544cb2187993538864c654c921b1185324864d6294e409358854cc24d621513093588514c24d6294d208719153482546154d20c3551320834532544209358853c424d6294e10
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (880+((h/16+packedAt s2K5 (768+(h % 16)*7) 7) % 69)*7) 7
  | 4 => packedAt s2K4 (3970+((h/44+packedAt s2K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s2K3 (1036+((h/8+packedAt s2K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf87fffffffffff81fe0fe0fffffffffe463fff
  | 1 => 0xff81f87c1ffc1ffe1ff0ff0e0f07f83fb9d273
  | 3 => 0xfffe007fe0ffe1ffe000fff00ff87fc1c1e39c
  | 4 => 0x7fff0001ffffff00000fff8001fe03e0
  | 5 => 0xffffff80000001fffffffffff0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80820040008000022010012220889080204a5
  | 1 => 0x51245088ca50a8960c506504454550b498d252
  | 3 => 0x6214955146a28baac148b6a089d46685c16318
  | 4 => 0x47596662943acdcd776a14812ee64319ee03e0
  | 5 => 0x8461844318c31171998cd8c9c080042175b800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaaa88aa88eeeeeeaaaa88aa88eeeeeeaaaa88aa88eeeeeeaaaa88aa88eeeeeeaaaa88aa88eeeeeeaaaa88aa88eeeeeeaaaa88aa88eeeeeeaaaa88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37229
namespace PEqualNP.Outside.L_meta_37229
open PEqualNP.Outside.L_meta_37229.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x22688043a09380320078b48515a500c4000429968000000150001600020002e00002af525d120500c4000000300241c7305400e1b307c68a0058f134630480000000001021c0120009581000400cff43df43fe43fd43fc43dc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2684e0000000006f00000728e060008c6d0015000004b800000006a213e000007c001b300011a2100000000600200003015874d094000000077001c400001500000524c19800a40000000900000000000012936702b0010e0000000001900050000000000000000000b8004f0b06e380000000000000000000000000000000000003c8093874000000000000000000001207a653b00000000000000621d00000002d80000000c0000000001c8e60000000006b00001403b00078c2000200000440d00000000019d2c9121a24203e432100000360013a400000000001100000003517c000000000000000000000000000001100001188200000002300000000000000982e00094000b070fc00a20000000000019000000014c00002f22cf6812c0000000259412400001d42e6949800001500000f041178001407000201e6e24a849e2d1e00050160080cba7f00000000027000c600001f000850000000002c800008f001540032001084c9909228000018800003500000ae47000d80020000000009001e800003f1f400050e000a20051802020000000000080800000080000040180000010301c00010080000000280c00000000c02000000404000000800000100000020104c0800010040002025754b43af28e875d50d0ebca721db94843b6a90875e5410f3ca821f394843aea9087cd5210e9aa421d794443aea80879f43d0b3887a167d4f42ce29e853d5490abca7215754e42afa9a855c5350b3e86a16710d42cfa9a859c5350b5ea4a14f95042af298855d5310abca9995715332cfa16659d42ccabca39957543329f2a4653d548cabaa7196b50a32d6a12655e544cab8a89973d4932cfa1265ce424cb3a84997350932c6a12655c514cabea0994f950329eaa0655e530cabca7a0d754f41ce21e836e52d06daa5a0d794e41aea9c835f53506b8a6a0e710d419f2a4633d548c6bca918e7952318f2a4639d548c6b8a918d754a31cfa14639d428c6bca318d754231af2a0635c540c6baa418e7d0831cea10635e510c7aca218d7540319f2a6433d54c86bca790d754f21afa9c435c538875a8510d7d4d21ae29a433e540867aa810d794c21aea9843ad42086f4a010de54021af29c815d5390338872057d4d40ae29a815e53102baa6206710c40b7290816d52102eca2205d54440af2a6615c54cc2baa59867d0b30cea16615e51cc2baa7184fd51309e2a2619f544c2bca8985715130ce2a2611c544c2bea49867d0930cea12615c514c3b6a0985794c309f2a6413d54c82bca7905754f20d6a16415e53882baa7105794d20aea9a41ad424827ca8104f55020af298415d53082eca2105d54420afa9e215c53c42bca7085754e109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | 1 => 0x9a000000066130009052834a800004500000685a00
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x64c5a833e083aa74a43245cb13252484400120002f4600e806814000506181532b59843c00bb940d9d91024c01a00e000f365000b1cadb8d003001c44585104e48245051018a80040050d000d1830004311c39515210f0e6454843a358b53d0a9661d4f42a358853d0a1e64947328719150cca566195132a3592424ca4c6550932c3d95424cb0c6550932c3508514cb0d42d4132a358843d070c4354b41a3588435062d62952319358a548c68d6295231c398a548c61d6295231c358a548c60d629523187d97428c61f6550a3193588540c6596015031c3549420c61e649443187191500c61e64d4e21c3d4d428861e64d4d21c354d42087294254021a3588439028d6210c40c310d521031443544409358854cc30d5250b308799251cc22d621513087992544c24d6215130a3588544c30e621513087588544c30d621513083588544c21c65d093087195424c30d5350b2087191538821c6454d2095185534830d53509208799353c421c6454e10
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x24003806128048300002028282b8cc8a9087419c7655093281ae4322a018c0d729935348682b9086a8881035ca6494730818eca9a84905047154d4248206b94c9a9e21035c86454e10
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (912+((h/16+packedAt s3K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s3K4 (4950+((h/55+packedAt s3K4 (4455+(h % 55)*9) 9) % 381)*9) 9
  | 3 => packedAt s3K3 (2420+((h/20+packedAt s3K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s3K2 (502+((h/3+packedAt s3K2 (490+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf0ffffe0fffc3fc1fe1f87fff0ffc1fe8cf3cf
  | 1 => 0xff07c3ff0fffc3fe1fe1f8707f0ffe1f734cf3
  | 2 => 0xfff803fff0fffc7fe001ff807ff1ffe1838f3c
  | 4 => 0x3ffff00007ffffe00007ffe0001fc0fc0
  | 5 => 0xfffffc000000007fffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x10108022000840002202009110124044041145
  | 1 => 0x224104442450040a0c20882221049418314492
  | 2 => 0x44222a8842a220d4c11155044aa12981828a28
  | 4 => 0xeb5b312aa3aa967775444097cc80ccddc0fc0
  | 5 => 0x88c6221cccc332799999e64e08803111ebe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeae8e8e8e8eeeeeaeae8e8e8e8eeeeeaeae8e8e8e8eeeeeaeae8e8e8e8eeeeeaeae8e8e8e8eeeeeaeae8e8e8e8eeeeeaeae8e8e8e8eeeeeaeae8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37229
namespace PEqualNP.Outside.L_meta_37229
open PEqualNP.Outside.L_meta_37229.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x9500010000c74012166d1004e0000046ac01a043000a3239404009000f002001826015142ea438500940160070189008401f3c988111a484280000044001380003ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461bf428c37a851877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea1061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641ee42c837a85907b50b20d6a1641df32c83dc6590774cb20f699641cd32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e84907b90920dea1241ed424835a849077cc920f719241dd32483da6490734c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10ef99421dd32842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa1221bd42443be6488774c910fb20a21f541443ec62887d4c510fb10a21f521443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810ef99021dd32042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083bf421077a8420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31dfa1663bd42cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f790e31eea1c637e528c6faa518efd0a31dea1463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063bf420c77a8418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21f721443bd42887da8510eb50a21ef99443ee32887ba6510fb4ca21e6994437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8490ef50921ef99243dd32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410efd0821f721043bd42087da8410eb50821ef99043ee32087ba6410fb4c821e6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40ef99681dd32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a852077cca40ee994817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea1081df32103ba64205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28
  | 2 => 0xc0040080a000058088000020240700800000c0080c002000018090000040200100c00001000000000000050180100300603c00400800000004008000000000000100402efca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7c87a16f50f42de21e857e51d0afaa3a15f94342bea8685bf53d0b7ca7a16f54f42de29e85bf51d0b7ca3a16f54742de28e85bf50d0b7ca1a16f54342de286857d5490a7aa9215f94e42ef29c855e5390afaa7217754e42aea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f90d42dea1a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142dfa9a85be5350b7aa6a16f14d42dfa9285af5250b7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050afca8214f95042bf29885de5310abca6215f54c42eea98855d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ef21e65dd43ccbb887996fd0b32dea16657e51ccafaa3995f94332bea8665df54ccbbca9997755332ee2a665df42ccb3e85997790b32eea16659d42ccbb8859977d4732ef28e65dd51ccbb8a39977d4332ef28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85197b90a32dea1465ed428cb5a851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbbc86997750d32ee21a65bf424cbdc84996f50932f6a1265ad424cbde6499778c932bfa8a657c514cafea0995f14132efaa265de544cbbaa8997715132efa9265cf524cbbe849967d0932ef21265ce424cbba84996750932e6a12658d424cbb8849977d4532ef28a65dd514cbb8a29977d4132ef28265dd504cbb8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf29683ee52d06dca5a0df54b41f6a96836d52d077e85a0ef50b41ef99683dd32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52906faa520efd0a41dea1483df32907ba6520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837
  | 3 => 0xd500059c0000000000017000000000a0c0c0005140000010a504758000001fc37c00278292000370401ae130d3800000794002ac00021400245000bf80e000000cbc000000000006ea42048d15ae095378360001f9000ad800000440000000001c40dd74800000001341300000015789e44200149a3f00066c000000000000027b0000d90c29246211cff8c461c000b981b3ae0000000000065ca1000000001b90dc000a597ea5e4d44fc50b38000a6db00000002a9501870002dd12aa73420b4000e600000000000040000beb2d1c8dac00000000000060000005f80000053a150002f3000290b6a8b000804001523b4411b78fd2980017725621e430001b20002c4003310006681e000000000812be5b8449aa80048e001a3000000000002fa6ac000698006d85547e0002662943e00000000005800206de13002646e0010e0943b60e1609e0000001291f813a0000022b000574000c600000000000000124001e8000cd0000004c287c000002c43054c0003da0f93ab5f00023000000000c3c00000000000718c259650cc29c25501c8002c26e200000000000000bb000000000001345c808d70800000330a3109000000000000000000000000000000099000000af9706760000006462e24c37b040b2d6cc236e3e2001b6800000b58bb9010c4869200411dac84ddb1f03e3ad9184e15ed91990d547a0000000000052c602154c678d01b1e33a00175a552ce000350d42b61159f00f0d0845693440f681c4403f340714a700a4489299205d146d09528b42d84c96516525e72d0b20917e4193b04d362415ba20a2e82d81481e53c63cd71583d86e0408002385c4b4000000000000ad382810019f25446b00025a0b000000000000d24f38001f668c3380e62274422000000bb495000352000880005b48d12a31858c001b9ac0360ac8bd357000000000000000000000681e01c000010070020000080b00801c000000020000000300a0100300601e008018000000280380100e008030000000140000000e0180400000200000000030000020020100400180300000800800000020000000000100000000002800000000000000260000080180d0240000480000000806000000000050030000040300500202002000012034048010020000080400001400001000024000000020a40000200200800000006024000080000200102c008008048050080000380000c00002000018018038030000000281300800401002018000000030020040000000201403801008054008040000000801f0020100000001a0000300300200c018020040080980100400800802000034028000020000000000c0500100200a0100000d0240040300600000c0080701e000010040000040080000000801006002054048000020000000401200400001000010068050
  | 4 => 0x1890000d8a101d0000000240037621a1582800019e0007c1794c44c4d12e31223bd472ec50a1d9320003d47345000018e1e10804635e9956a28d0e05d44f8000000000032e178d44a89dc3e00000024e0000000000064a000003470007ed88000614741288004a6000003670000011a810000000000001766fcc827e46c20da5a7110c001a1ad54460009e31322a000002b369a0000025c41ed7462800000ccce980018600000000570000001220000000030200036c003682c0000968001200003c8ae0c600194800000001a80000000000026d000cfc00000000000000003f40007b800000000f20003a897c0000000000000286000000000000004f811000000000001e13987d0042a9064c0c7aa303fc490bdaab522359aa0cd2b43c8000000005fc000003e6000000004f44f4000550000000a00009458c18800000d60df1130000000b9c34b29a4000000000015baf830cd649b24d454a30000000000005302c6560011e0000004508f2bd0000019c9f62e40a8728006c472400352372c0032b07024b4d932f441c0003b81309e1d13381a5923405c8f92226ddb82d956284cc1816650c24a6acd2f0bc49308f2c23b92b80058841c90a06538a54001290000000019f0d6064000000000013e800000224cf000616c68ee945610000000da3a48b552001466ad0970e82d6de5481d948865180948452000be000000ad53faa3500b7c2f26c444238293300b60016c000104000000002ac6241788b0006d9040004de7f5242720000000025b0007980018c1b2b9c4b8000007600000032c0000020b6440018a33617cd0147908000000ca8005f8ba17ba124f20000000024a1f47a0d26bc000000000fe000000001e200000000288a049c2870000002d34c000694c7000374a24141470001e9730006ea328002e50902b0802f069e00155000000108039c40000000013955a000001ab000000f58001a2000000000006040035a000324a0918000001860251fed4c1aabb0868bd1931962a09c002ae528270000002b8c1838a4c3503e9398000002d51d9f74f800000000000cd5029532160004c01d404a5c0018a0c20157780023622935a14000c35680a25f2599902b02a85b8c419305c000000de41a15c021400000017d91a5fe458a780000014c0000054ca68ac9ca000000de9200000000000038e000738003d20003f29f5c4cf4a80005100000015e000ae84b31b5421a4000001c27b8da000000cb113b272563b16e89a6ee73cb4abf6d2000001a6000000000000000010e8b00007380018b35a00000000156001b52de366001700a74ee0005c002474c71a503d3f800000266000000000000005a800000000d858e800380000000000004a13a000678000002cf0003d8000001520003683b00085c1a0005ec7bc000f30560017a81500
  | 5 => 0x8badb0009b8288000003c0000923907d4069b50008e09d0e00002c8d200058ed8c3a800654d951cab94b00cd643160002f487000322670000003040180000026a000000600009c008a1e23a320000004000e5b30000000000008445c000001e24861cc961df10e4dcc68a8000cdc00000000000cc8000000c00011943249c5d0004ba00065a4b00000091b4111a3a4750005ae648000000005912798027617c4000048c000000b300000000000000d391316f096b0da40ce4a000120800578000ea80047c8b00009b60a0014ca28492b1506198598000000003bc7180000004286c8f800674ba8ab94a00019800000000b44002f2
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2528423d6494a109798e528425d6394a108f990528423d6414a109798c528425d6314a10cb949428432d5250a10d3949328434d524ca10e350932843a94248210f24c9208423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58854443356115110c7d53534431c54d4d109758b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425d6214d10d5584534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524434e6314910d358c52443656114910da580524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb149424425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d3149324438d424c910cd15241442d563905109d19541442b5648c510d514e3144274654c510d914a21443a54288510f14ca21442746548510da14a20443e221881109e19520443a94248110f24c920443e121481109798f540425d63d50109b98b540426d62d50108f596540423d62950108fd89540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109758a530431e5454c10c7551530425f6254c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48108f992520423d64948109798e520425d63948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520434e6394810d358e520432e5454810cb551520434e5354810d354d520432e6454810cb591520434e6354810d358d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d525081097d97320425d65cc810c7953320431d54cc810d394b320434d52cc81097d95320425d654c810c7951320431d544c810d3949320434d524c810e3509320433554c4010d554f100436552c40109e596100436952840109dd9510043355444010d554d100436552440109ed9510043695244010
  | 1 => 0x82af6550b20cbd9542c832f5350b20e394d42c832d5350b20e354d42c830d5350b20c795332c831d54ccb20e350b32c82ad648cb20cb55232c831e544cb20c755132c838f424cb20e350932c832d544cb20d394d32c82cf654cb20d3d9532c834f544cb20e395132c834d544cb20e355132c830d544cb20cb50a51c834d3294720ab59321c82cd63c872097d8d548825c63552209798c548825d63152209d984548827561152208fd91538823c6454e208f990538823d6414e209d98453882756114e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d20ab59242482cd63909209b195424832f6550920cb195424832f5350920cb54d42483ab6050920ea181424838d42cc920ab59232482cd638c920e3d09324838d424c9209b195324834f654c920d3195324834f544c920d355132483cb604c920f2181324823e64145208f590514825e63145209758c514832d4214520d34c8514826e65c8520ab59321482cd63c8520ea50b20483c932c81209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c2097d89530825d6254c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420825d65cc820c7953320831d54cc82097d95320831e544c820c7551320834e524c820e350932083365494420cd55251083565394420d554e51083374294420cd50a51083573294420d54ca51083365454420cd55151083565354420d554d51083374254420cd50951083573254420d54c9510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020d9545200827b6548020dc545200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c432f5250b10cb14942c434f524cb10d314932c438d424cb10b558e41c42b5648c710e950a21c43c5328871097d8d548425c63552109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108f99
  | 2 => 0x5350840c754d421032e525084097d97321025d65cc840d394b321034d52cc84097d95321025d654c840d3949321034d524c840e350932103565394440d554e51103665294440d954a51103374294440cd50a51103573294440d54ca51103565354440d554d51103665254440d954951103364354440cd10d51103374254440cd50951103573254440d54c9511023d6590440a798e411031d5390440cb54a41103355190440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401029c6350040c754d401032d5250040cd545401027b65500409b98854cc26d6215330c715143cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb30e350932cc23e64947308f59251cc29d64cc730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b3588438c23e6494a308f592528c32e5250a30cb549428c34e524ca30d3549328c38d424ca308fd91518c23c64546309bd89518c26c6254630a7992318c23d62d51308f992544c25f63551309b988544c26d62151308f994544c2ad6215130c758c544c32e62151308f588544c32d62151308b588544c25e6590d30c7152434c25c6550d30c7151434c23e64149308f590524c23e65d09308f197424c23e65509308f195424c31f54cc930c7153324c31f544c930c7151324c34f524c930e3509324c25e65cc530a7593314c31c54cc530b358b314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c31c63550308fd89540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c25d6510c30c7550430c2cd6210c308f992520c23d6494830cb952520c32d5494830cb992520c32d6494830cb951520c32d5454830cb991520c32d6454830d398d520c34f4354830d310d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c31e54cc830c7553320c34d52cc830c7951320c31d544c830d3949320c38d424c830cd952510c3355494430d994a510c3655294430cdd0a510c3354294430d5cca510c3553294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430cdd09510c3354254430d5cc9510c355325443097596310c29e648c430c7552310c34d528c430d5546310c31d540c430d3548310c355510c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030d3549300c355514c0309ed95300c25e63d53209758f54c832e62953209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20d398a53c831e5454f20c755153c823e6414f208f59053c831e53d0b20c754f42c82cd6390b20d354e42c831e5350b20c754d42c832e5450b20d354d42c
  | 3 => 0xa21d355132887c7614ca21f118532886ad64c8621b358f218863f64542218f191508865f63542219718d508872d4254221d34c9508865e63d51219758f544865e63951219758e544866d62951218f993534863d64d4d218f992534863d6494d219b58a534878d424c9218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540872e62950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992520863d64948219798e520865d63948218f597420871e53d0821c754f420866d6590821ab59242086cd6390821d354e42086e561908218fd95420871e5350821c754d420872e5450821d354d42086af6550821cbd95420872f5350821e394d420872d5350821e354d420870d535082197597320871e54cc821c7553320878d42cc8219b59632086ad648c821cb55232086cd638c821b9586320865f654c821c7951320871d544c821e3d09320878d424c821cb551320874e534c821b3d95320874f654c821d3d51320878e544c821d3551320878d544c821c3551320872d4294421d34ca51086ad64c8421b358f21087a54288421f14ca210866f65484219dd9521087a74248421f1cc9210873a5494021ce552500875a5394021d654e50087a94294021f24ca500873b4294021ce50a500875b3294021d64ca500872d4254021d34c9500873a5454021ce551500875a5354021d654d50087a94254021f24c9500873b4254021da90950087394254021da50950087294254021d6cc9500876a3254021d64c950087693254021d24c9500876b2154021dc88550087692154021dc485500865e6394b409758e52d032d52d0b40d394932d034d524cb40e350932d025e63947409758e51d029d63d0740ab58b41d02ad6210e409798e529025d6394a40cb949429032d5250a40d3949329034d524ca40e3509329025f63546409718d519026f62546409b189519029e63906409758b535026e6214d409b58853502cd6214d40d3988535025d6214d40d3588535024d6214d408f997435031c53d0d40c714d435025e63149409758c525031f53d0940c714f425031f5350940c714d425032f525094097997325025c65cc94097995325025c654c940e3509325023e65d0540a758f415031c53d0540ab58b415031c5350540c714e405025d6294c4097d89531023d6590c40c754e431031d5310c40ab588431025e63948409758e521034e5394840d354e521034e6394840d358e521034e5354840d354d521032e6454840d398d521034d6354840cb90d521032c4354840c794f421031d53d0840cb54b421031e
  | 4 => 0xb94942d065f65ccb419759732d074e52ccb41d354b32d065f654cb419759532d074e524cb41d354932d078d424cb419b98a539066d6294e41b358a539074e6294e419758a539074d6294e419358a539065f6254e41c794f439071e5350e419798e529065d6394a41c794f429071d53d0a41c794d429071d5350a41cb549429065f65cca4197597329065f654ca4197595329078d424ca41a758f419071e53d0641ab58b419063e6510d41ab588435065e63149419758c525072f5250941cb14942506b46150941d3d49325074c524c941e3509325069e63905419798c505065d63141419b988505066d62141418fd95431065e63948419758e521072d52d0841ad587421074e524c841d3549321078d424c841a758f41106ad62d04418fd954110677655044197d8d501065c63540419b98b54cc66d62d53318f58a54cc71c63553318fd8954cc66e62153319b58854cc71d54d0f31c755043cc6cd6210f318f99252cc63d6494b31cb95252cc72d5494b31cb99252cc72d6494b31cb95152cc72d5454b31cb99152cc72d6454b31d398d52cc74f4354b31d310d52cc63f65d0b318f59742cc72e52d0b31cb54b42cc63f6550b318f59542cc72e5250b31cb54942cc71e54ccb31c755332cc74d52ccb31c795132cc71d544cb31d394932cc78d424cb319b98a548c66d6295231ab58a548c71d6395231cb98a548c63d6295231cb58a548c62d62952318fd89548c71e5490e31c7951438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c71e54cca31c7553328c71e544ca31c7551328c74d524ca31e3509328c69d64cc631c7953318c6cd62cc6319758e544c66e62951319b58a544c65e65d0d3197994434c71d5410d31b3588434c63e64149318f590524c72f5250931cb149424c74f524c931d3149324c78d424c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c3197d95430c71c5450c318f992520c63d6494831cb949420c72d5250831d354b320c6d561cc831e3509320c63e64944318f592510c69d64cc431b358b310c65f654c4319dd95310c63f64540318f191500c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e53d0b21c754f42c871e5350b21c754d42c871e54ccb21c755332c871e544cb21c755132c878d424cb219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e21b358e428872f6550a21cb195428872f5350a21cb54d42887a76150a21e9185428878d42cca21ab592328878f424ca21e3509328874f654ca21d3195328874f544c
  | 5 => 0x50d0b4e6294e42c794f4290b1d53d0a42ab98a4350b1c5350d42ab9884350a9e6390942a758e4250a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050aad6294d42ad9865350ab56194d42abd895350b1d5314d42ab58f5250aae61d4942ab5835250a9e63d4542a758f5150a9e6394542a758e5150b355114542a7d8d5050a9c6354142add855050ab46154142a798c5050a9d6314142ad9845050ab56114142c794f4210b1d53d0842d354e4210a3f6550842c794d4210b1d53508429bd954210b2e5450842d354d4210a7661d53329d58754ccb1c5450f32c755043cca3e64947328f59251cca3f64543328f19150ccacd62d5332b598754ccad561d5332c755054ccacd6215332e3d8942cca9e64d4732a759351cca9e6494732a759251ccb555114732a7d9150cca9c6454332a799050cca9d6414332b598450ccad56114332cb98a548cb2e5450a32abd95428cb2f6550a32c7953328cb1d54cca32cb50a518cb2d42542329d986544ca75619513297997434cace62d0d3297195434cb1c5450d32c7550434cace6210d32ab592424cace63909329b195424cb8f4350932e390d424cb8d4350932e310d424cb2f6550932cb195424cb8f6350932e318d424ca9e648c932a7592324cb8d428c9328f993514ca3d64d4532cb508514cb2d42d41328f990504ca3d64141329d984504ca756114132b358a544cad66195132b5586544cacf6255132c7550544cacd64d4932b3987524cacd60d4932e3d4b424ca5e6590932a7592424cace6590932d3996424cacd6490932a3592424cace6190932b3582424cb8f6250932e3d49424cace6550932b3195424cb8f6450932e3d51424cb8c5450932b3185424cacf6050932e3d95424cb8e6550932e3595424cb8c6550932e3d85424cb8e6150932e3585424cb8c6150932e3d81424cb8e6050932e3581424cb8c605093297994424ca9e6410932b3988424cb8d4210932a7993514ca9d64d4532e350b514ca9e6494532a7592514cb8d4294532e3509514cb8d4214532d5544514cb8d42d4132e350a504ca9f6454132a7191504cb8d4254132b5d85504cad46154132a7990504ca9d6414132e3508504cad66114132b5584504ca5e63d50328f596540ca3e64150329798c540ca6e62150328f992520ca3d64948328f597420cb1e53d08328fd95420cb1e5350832cb949420cb1e54cc832c7553320cb2d548c83297d95320cb1e544c832c7551320cb8d424c8329bd95320cb2d544c832d394d320ca5d6294f4197d8953d071d5390f41c754c43d06ad6210f419798e52d065d6394b41d394e52d074d5394b41d398e52d074d6394b41d394d52d074d5354b41cb99152d074e6354b41d358d52d072e4354b41cb10d52d071e53d0b41c754f42d072d52d0b41c794d42d071d5350b41c
  | 6 => 0x2a0001239b98001231d40d982080006100022000027a8b48f724c2360a19091d1a34a2d8c30ac19b8e21591389a9a1ca9b0319c0900a1503400014782300028528106d1749498170a40000c90dc14fa7d9868fb23583d12988916d0fe8302238479322552370001e0134800244109a91a1029400000025e1f100003324093ea6397b13e1d82989870370b20ea25ba20a7000010824917d23a85e9111e7097a571c598a9730000aa9fe9f4a1d21d9ee853052102029a8c0c39341b915000100203401c000290160080200e0b80000001c0180041200300c04001000000044008000020b00401e004000010080160001400101c05401811004014000060040040000100c0000c03000209c00004004000070120060040000208600c0000000602c000060000000080a002028030060200101500900a000000670120100d80404402c0980500201c0600202201c0e80500008800002004014008000201000a80c000004220150060000f8000000001100000200000007000058010000400000280000207c0180100c0c4008000020100486d01a2840400400a034000000020180682103e0340b003022018010000000340000a00a03808804000004030000180e00900202a0180480101a02c0b00703a00415800008008008000080040b000040020000000000000b005000050000000000100d8020040400380000a010000170000081080401e0240000000e014018030000340880300003c0301100006000014008004050000040040180100000403802000014000120040080080c0160000400701c0000480003603802802000000008020000000000203c0440180205a0140280f0040080180400001c030040100040b818000020218000060540080f008000038100140b001000018014040050100000081c00200c030000160481280203e0000d00600000c008290020240206400000010000004014010030000481280b0000180000301400400815000004178160080340081504201c1404f01a0340700c00a01c0000206e00400004028020000000020040500700001801004008004000050040280500502c0000c80200402c010020100280381b0060780100100e010030039b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a7d854310e9c6050c43e350e5210f1d4354843e350d5210f2e6454843d398d5210f2f4354843d390d5210f2d4354843d350d5210f0d4354843c750e5110f1d4354043c754c43d0a5e63947429758e51d0a5f63543429718d50d0aad62d4f42ad98753d0ab561d4f42c754c53d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9f6354342a718d50d0a9e6314342a758c50d0ab66114342ad584
  | 7 => 0x80003a8b11308d225c0271c18f4295036a2822e80005694015aa1a94413523d871a538119c50001f221400000018b96a29396da8f00b2169408000f00ed00014d0000001d913100011a983043a110000e915123d21b0000000000000000af00020108f22b075000209a160e02488509618001572410701cea801e693b19e874a3ca2a12188ca8b11488d26f8811118f3a1599c85803b06205724e8c215609e89b148a2c8bfa9d8cb8670399ad0ef08520da55a680818489d8a090781e58ae02820794e8dda1ba3e2710002829b389c069a0b80001e02e8ca98c9eb0cc1700961861651cb12f1960ba1491131d98548b28ba9a39da1dd9b5a0d24583c12ea67076a3a18095f000000257a2a86f13812f9188000159af9200880740000420981f32321a69251d480a8d3a8d1b0214a2180000000020c14a9339b8957a7090b84318487f0261ae81f0bc937a4487894b00e00010f8931bc00020812827484b809a68a17a0e24702c0bb89101ca2b82c85114c91d21f0351b128d97405781b8002868198970da055092a7e0558b40239898872758c9a0b084a6797803e890a072530e500f2928bf2900eb2009a41e2a791cf03781e8bc11a0bd8b817729c88b80e99722c14122622424616f2171529cc0d4971a602398a49d09c90b8a1988000d1709ae0c70f804d0739ef19e0fca78a9a80001a8f922680000020498e06280015e8338a09be0f782790d8001621e48001691290500608000d78000001609ea80011c8002389811670fba9812e23016e8dc84587d8d00e40998b617c26e01c12d8002391ce14d8140fa8efa1c0f184c8e1003a468150a020aa8a0f681a2451c72339ba97e80486624007991d9931041901928050ca2129de00014c16f997a6284984119192297907b9e18000000000320869f72431e50a29aa0de8b329a1000e808a08f80026400da3080000007a80000010380000004ea5610e8b01ac13580009a82d07c87e0000fe00004280027800000016280000323818fa738001032369f880028ba742540001468791422499948fd82ba510131268228b78001a520e90f04a0002508121b224799884b1c01ed97e18280024d0e280000000000026493900000000026b9c8800000000131925a81a6c00000b834a08a63205a5a290a3786e1faa6d94a1dc105a97a480d91f814800019c2881419e79d61838e48001a60000000000000a680110b05a81d25224187b0001089078000e98000f48b682488e1bc8ce8b19a28a800011380702000000028e9f91060001128000000000000000000138808000710000001ac8000310e58da8d2800098a1e058906a420000ec87d00023113a00000000000018d00000021300006e8d180003b953a0a1ff29900006f8001300000001e80002271f98000d31dc9548001cd8000001c4000128a5c80c80
  | 8 => 0x6811209a0168d1007a92276a661f093a9788b906505fa31829120998030a3b0fa179a580101ec0d71519d6a2509f9fb04d8f21bb1c20e6213a221921990ad83e00681800095e1191070590df1508f989f190a7984490a1460aba668d808209ca7ea6111411682b142a5f27f03c835a2125895b83921e89180884a85c9c99180a22548111739ed1e097a88e85d06787f90ca0296a95f92c22f9050bd08424f29712223317f1b4840a4b87086c8ea9639de968299a5f8000000002229e39530001f780014f0001e606c05e0000aa1f407297c844119a1a2350c60c18858000d41728b38109ea1b602d8081958bea1180013628a81491095404726593f0e32968b09c680000001d85d98ea278328949241602591f00000df9598951fe14380017d8000cf1d000000000006a9d700020fa2480004915500028780024c8001e900003813d0941ff8000001938f50561649a019f8a30eda2f2328eba8c9fc19a06191e98f10186398a2000190d6896a690e70fd0b58a709219f06b0ee89d0898002192808862650db02215b1a71d204e06d9b80000400000001d10ee12a800271a8f9c28a51760000000000001a30000000000000000001bd91fa022728a980000000000180011f0c2a6c8830000000020001b086b9e89fda019db0cc9659632621caa949c106480005f10d1cba6d0000210d615818b2821170aca7d00019d0000be01615a1f384f03f12a06893d84811c1bb9b7a5da3e80c0001f181fa2e11616e27780000021f8e19b29470c80c00001559df06699b1331fc8001c788c2931a096b10c0000e88cd8001c49a8000185059a3418408d80fa6a0000b500000025d1bd13ca838000000000ae8720000000001372518001e2077a030000000ff1a480005a261a2980002e1779b50cf8c79f28c49398d51679459642761750f8a068040f10000a600011ba25800176800291000024210a4a00000012b8001b6883825196800046a500002889ab0a7a8601b27f8d098d991075a4380000024e1ec87614491580026a981a7700012b1f50ab1d79d2a0c8991fa1880f58ce23f06a0361b300000003f97a26b00595d9db9248e39ca028a7204505c1fba7b24fa8580019a9a11b728489005383a175a3c27c23ba062698c416892c9f61d30dd1c39260cd00a11e04c19994b9a59a886424a92d19d98216695ca9d0f62428258e69100f30269af1d59da9b18691951e40fc06029595215c10e0e7a231369ab9c609d84f9c310a92107e83880007717f80015688b1b42899800658001eb9888001a20001179a92568000001271450000000c593f80014e16b87c0001bea5e8060c080015d1ef80018c0001c800029612782f0000002529941ba0000730001cca750a102fa1800029b8000000461bf9ee1660528c51e30b99cd25aa052870ec1011ad8888000028d8
  | 9 => 0x143018a291720c691510496c132a6e85b89388280007a0000e0a831d51699bf00925989e00013c16c9a198900027b96113b9dd2038000178a38001e12730218001aa85b28e0db91b25b0a90cb0540bb20f0001710d581286300027a0af80017b8000001e98001cfa7c9f69d38b72042840001a785184180003d9df80009b9f580024da3f8f0a60895a18a9c0c115880008a80022d26f185a4b0c882aa289fd2121028ff8a5a890a88de0878ad1878f28
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x98e0d6358a548c70739ac52a463835cd6295231a1ae52a48718d0d72951438c686b94a999463435ca544ca31a1aeaa126518c1d76953318c686b94a998c638395162cc631c1aa8b108698d0d74149324c742a10c299263235ca648c531a1ae42a28618d1970151430c616b90c8a8063435cf6550a21a1ae9b2a6510e0f635095088707b2264a8443135ca63d512185ae5326a690d2970d4d4208686baca6a10438359542cc821a1aeba126410d4970d513208686baca899043c254d4294021e12a8994a010f09424ca5008695baa84a8043c294d4254021e12a6a12a010d4b754c950087852a264a8043c25513254021a92e7212a010d61719095008784a1664a80434a5d23254021ac2e3192a010f0b424c95008784a1264a80434a5d32154021a92e790aa010f214288550087a099442a8043c8d092154021e866490aa010c4d7298e51d0286b9ca4a1481235ca6390640c1ce8b10a6a060d745885350286b90a7a1a81435c85350d40a1ae429e84a050d7214d425030732a8499281435c853d0540c18a6b1682a050d7214d4150286b90a7202818354d6210c40a1ae529a842050d739494210307b2a8499081c15093294440a4ae421aa220705424c95110246b94c7208818398d5290440c2cc6a8c822048d7218d401030631aa4a00818518d5150040a1ae42a2879842d7299251cc307aa2c421c61435d2524ca3091ae5324631860d63588544c30739ac42a261835cd6215130a1ae42a4869850d72151434c286b90a999261435c8544c930a1ceaa12649841d76153314c286b90a998a618315162cc530a1ae42a2629850d72152304c286b90c6aa061835516210c30a1ae52a2641850d74949320c287baa8499061c15093294430a8ae421aa218705424c9510c246b94c91886107dd9548c430c1cc8a94621861664546310c246b90c898061071d9544c030c18c8a92601861464545300c286b98caa12410b1d95350920a48e2a9a84905a1711814248286ba0ca99241131d9544c920a88e2aa264905c1711813248306b1a8428a41835913214520a1ae7292841050d725513208286ba4a49904143dd5424c820c1ecaa126410705424ca5108382a1264a88418a5516008420c92a6b00421044d7298f54c4216b94c9a9e21435cc5250b10a1ae8292658844d7218d5484216b90c8a9c21435ce5250a10a1ae9292650860f64d8f5244306b22c6292218a5916014910c92c6b00a488661615805244286b90a6a1221435cc5250910a1ae42a2648850d7414932442873aa8499221431d5424c910c1ccaa12648860c6550932442923aa8510a21511d53288510c50caa124088648654c92044306b22c729021835916354810a1ae529a840850d739494204286b94a899021435d2524c810a1eeaa12640850d755093204307b2a849902183595424c810
  | 1 => 0xd7000000019541e00000001d40012000000000000000c910000000006e800006c67000006e1f8dc1e7c24800a0000000000000036822ae1cb814200239900000000d0ceb200000000040b513cac5c320005a0034d84212b001348e3111820000b8000000001654e4c46894e04f001ac740a2f0000000002b47883630c400000000000bf2280120a567b5800000000000000032d04002100000b52d801a2006d80006c154b54fe00001d800000000000440031d2800002f89a8568001780000000482e4ab6034004980000004e2219200000c800842e800006a30225b2000001d607a00001c46d5a0016e35000000020000b02a96621a0000000291000000000e4221994400002e28816054c801a463490595e41020d8003e0f0000097662a9142300000563b07000fc00458505a28002e838c015000000000000000000000fa004f9e400006e000009d00000e23d4398480e3099d086b339aad308f34800b0bb13034f600180a410482b9ddbc6f0029936b1139296ce14314cbe2f0fb28aa525e8609ca000824186525b1546c3668e03a1b0123172546f800cc00008060300014040200804000102000043e0b82806000403800000d0200c0d078000a020080400031c8001200008000a0304844000002800020102800120800008040000814060002000000000004000101030000191ae5b0a8621c8d721814310e4ab88c0a188743dc94354843a1eeaa1aa421d25719915210ea2b8cc6a908743dd94354843a1ee2a1aa421d0c7050d5210e8bb8a87288878354d6214f4291ae730ea4a148f735835250b06aa2c42a665831954350932a4ce3b2a849948d74987524ca47ba2c1a9265319c66550932b0ce3b2a849958571d95424cac338ccaa1265615c66550932c1aca32a849950e75d85424cb42b08c2a126561dc56050932b08e2b02849950e75181424cac3388c0a1265615c4605093291eeca16a29970542544514cb42a16c2a8265a1508615413291eeca10a09968542984504cb42a12c2282658354d6210f41a1ae529a85a0d0d7394942d0707b2a8499683839d16294e41c1ae8b14a720d0d7294f4390686b94a6a1c83435ca53d0a41a1ae529a8520e0d655093290686b94a7a0c838394d62d0641a1ae629284a0d84715093250646b94c720a83135c86354041a1ae431aa998e0d5458843cc686b94a899663435d2524cb31a1eeaa1265
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2b0000638c854304968142804190581dd94354843905811c14354843a05819d16294e41a05819cd629523180d8795162cc631a05819d16214d40a058298d5190440a058218d5150040a05819cd621513080d8715162cc53080d87991528c430a0582991518c43080d87191524c030a0582191514c030
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
  | 2 => 14
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
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (788+((h/14+packedAt s4K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s4K5 (27286+((h/296+packedAt s4K5 (24030+(h % 296)*11) 11) % 1421)*11) 11
  | 4 => packedAt s4K4 (55826+((h/446+packedAt s4K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s4K3 (11856+((h/76+packedAt s4K3 (11172+(h % 76)*9) 9) % 364)*9) 9
  | 2 => packedAt s4K2 (860+((h/4+packedAt s4K2 (840+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f83f0fc3ffe1fff83f44f3cf
  | 1 => 0x3fe1e1ff0f0ff87fc7f0fc387e1c3fc7bb4d33
  | 2 => 0x3ffe01fff00fff8ff800ffc07fe03ff8c38e3c
  | 3 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2000010000008000001004800240800001045
  | 1 => 0x84484222241500814310441122089286194512
  | 2 => 0x2884954442aa441a9888aa8255412530c28a28
  | 3 => 0xa1d55988aa83552cedaa220479938192ec0f80
  | 5 => 0x3119910ecccc664f36ccf32711020624f7e000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37229
namespace PEqualNP.Outside.L_meta_37229
open PEqualNP.Outside.L_meta_37229.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1000030140080d483001b34017980e8488e000ce1e4e9832900755202e484933e2c200000012d280140f588d71944ac0002a012802c0000000000050200000620208083006c38c00000000020107ff43fe43be43fd43fc43bc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xac008d36971340009890ec1e0b8bc804c001852c0f1c9bc8e000a1f8a8a311001408f001e4e60000000c48e45800000621000e20d19a64aa000003000463d0000000208b4000009000002825194dc000007d368c32011229d390d0b0981b168f63a2188cae0a01a849e302e874001b00068cc4d001452a271e9ac52842c9a4409e4818cb61c351f44c4942a18be75491e0c0670b12d04811a8b81c110491062530aa50423b4f804fe88000fc32003e0a87c5022a904a001c270906c43815004e04040000741860785e4980064a2291dcd02c3a1592e89451c00400000006e0b060e8180800b0604040580800090038503818000a181018b858981120c8d8a8006968a800084000a810004001d8201838082010181000c4f94e439f294873d5190e7aa121dd94443baa88873e5310f3ca621cf94843db288873d5110f6aa221cd544439ea80875e5390abaa7214f94e42cf29c851e5390b3aa7214f94a429ea8c853d5090a7ca6214f94842d7290853d5110a7aa0214f953329eaa6659c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a653f540ca78a8194f94f419f296833d50d067aa920d794e41aea9c833c5350678a4a0edd45419fa82833e54106bca620d754c419faa6633c54cc73c8798e710f31cfaa6639c54cc73c8598e710b31cfa0e639d41cc67ca918cf55231aea9c63b5418c67ea898cf15131cf21a639c434c76a8298e7d5131ce2a2639e424c7388498f5d4531cfa0a63d6414c73a8298f550531caa0a633e540c67aa818d794c319faa6433c54c87aa6390cf952219eaa4435e53886baa710cfd51219e2a2433e540867aa810d794c21aea9843d531086f4a010de540219f29e813e52d027aa3a067cc740ce98e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409e292813f515033e62a0674c540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f552209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c42bca7885754f10ea98e213e548427aa9084f951109eaa221d5314427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x27d42200e179e5a252846ee452456cda267654885184101a621d6210008dae2434a1c1c647b24e60000007400052c0013005c03a16015000021b03008da862c00180010010001041009304040231e1028fc594d5110f166354443955865390a356194e42a55865390b166194e42875865390b156194e42855865390a1c6354042a558443ccb144354732a5584434ca1e63d50328d584540ca3960150328798e52d061c63543418b98b54cc68e62d5331a558754cc69561153318799642cc634655053187996424c6956110931a5592414c6966550531a5195414c6946250531a5d81414c61e63d5321c5d5131c861e63d5121c5551310875131540218798e52d0315514c7409558453502356114d40a558453503166114d408758453503156114d4085584535021c65cc5408719531502356115330a5584438c21d6510c30a5584430c30c4354830c510d510c21e63d53208718d5488315544c7108718d548421c63551108b1895444315544c510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x6901c0029026020001002282b94c6a8887055c4635404290ce532a8298c157198f544860ab8cc729681415c4435483082ae331ea9904157118d548820a3b2a898a21411c9544c510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (912+((h/16+packedAt s5K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s5K4 (4895+((h/55+packedAt s5K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s5K3 (2420+((h/20+packedAt s5K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s5K2 (502+((h/3+packedAt s5K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1e1ffc3fe1fffc1fe1cf3cf
  | 1 => 0xff87ffc1f0ffc7fe01e1fc7fe3c1fe1f133d33
  | 2 => 0xfff87ffe00fff87ffe01ff87fc01ffe1e3ce3c
  | 3 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 4 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x14000408402040004042408804504088045045
  | 1 => 0x21214884894a0c4a10b0a45322849415112512
  | 2 => 0x4212111022900094a201090448092940628a28
  | 3 => 0xb556225281a956735342047932c0c45b80f80
  | 4 => 0x8c6643b9cce32679d9d9f26102303199dff000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8fae8eae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37229
namespace PEqualNP.Outside.L_meta_37229
open PEqualNP.Outside.L_meta_37229.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x789000c6260089780006cb00409d9064a6002c38017000a49f0228dc51f542089978e508474fcebd6838380508cb9302a402d56cdb0000d481e769001500c5c0b6034000000001a2c00080014a180822228b8000040000e00400027fd5009fe54027f55009fc5402ffd4c07fe53007f54c07fc53027fd0c07fe43027f50c07fc4302ffd48017f52017f94801fd52005f54805fc52027fd0805fe42027f50805fc4201ffcc805fe32007f4c805fc3202ffd4401fe51007f5440bfc51027fd0409fe41027f50409fc4101ffcc401fe31007f4c407fc31017fc8401fe21007f48405fc2102ffd4003fe50007f54003fc50027fd0009bf4000ff90009fd40006f50003fc4001ffcc003fe30007f4c003fc30017fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24001ff8412000ff42090007fc104800dffb2e2006bfd9710037fccb88016fe65c400dfeb2e2000bf59710037f8cb8801afc65c400dffb262006bfd9310037fcc988012fe64c400dfeb26200dbf59310037f8c98801afc64c401bffaa6200dff9531006ffaa988037fc54c400dffb1e2006bfd8f10037fcc78800efe63c400dfeb1e2000bf58f10037f8c78801afc63c401dffa9e200cff94f10007faa788033fc53c401bffa1e200cff90f1006ffa8788033fc43c400dffb162006bfd8b10037fcc58800afe62c400dfeb162000bf58b10037f8c58801afc62c401dffa962000dfd4b1005ffca588003fd52c4001bea96200bff14b1006ffe858802ffe42c401bfea16200bff10b10067fe658802ffe32c4001fe996200bff0cb1000dfcc38801bff51c400dff28e2006fd94710037faa388003f551c400dfe28e2006ffd0710037fc838801bfd41c400dfe20e2006ffcc710037fc638801bf631c400dfe98e2000fd4c710037f8638801bff21c400dff10e2006fd88710037fa4388003f521c400dfe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007bf40c4003ff2062001ff5031000f7a8188007fc40c4003ff9862001ff8c31000ffa6188007fc30c4003ff9062001ff8831000ffa4188007fc20c4003ff0862001fd8431000ff42188007fc10c4003fa0862000ffd9510005feca880037f65440013fb2a200aff9951002dfcca88003fd65440017eb2a200aff1951002df8ca880037c654400b3e32a2009ffd911004dfec888027fe64440097f3222009ff5911004dfac888027fc64440097e3222009ffd511004ffca888027fd5444013fe2a22000ffd8d10005fec688023fe63440077f31a2000ff58d10005fac688023fc63440077e31a200affd4d10047fca688003fd5344011fe29a2009ffd0d10047fc8688027fd4344011fe21a2000ffd8910005fec48801ffe62440057f3122000ff58910005fac48801ffc62440057e312200affd4910006fea48801ffe5244001fea922000df5491003ff8a488027ff424400fff2122009ff5091003ff88488023ff324400fff1922000ff4c91003ff86488006ff6144015ffa8a2006ff94510007eca288003fd5144001faa8a2006ff1451004ffe828801bfe4144013fea0a2006ff10510047fe628801bfe3144001fb18a2000ff4c510007ea628801bfc314400fff90a2006ff88510007ec4288003fd2144001fa90a2006ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003dfa022001ff9011000ffa8088007bd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff104400dfd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7bf2150001df10a8000ef485400af7842a0007bf60500035fb028004eed814000f7ea0a0007be5050003dea828001ef1414000f7e60a0007be3050003de1828001efc814000f7c40a0007bc2050003df0828001ef04140007feca98002ff654c029ff32a6005bf99530007faca98002fd654c029fe32a6005bf1953009ffec89804eff644c027ff3226004bf9913009ffac89804efd644c027fe3226004bf1913009ffea89804ffe544c027feaa26013ff1513000dfec69800fff534c007ff29a6003f794d3001ffaa698003dd534c007fe29a6003ffd0d3001ffc869800ffd434c007fe21a6000ffd8930005fec49804bfe624c0057f3126000ff58930097f8c49800afc624c029ffa926000dfd4930097fca498003fd524c001bea926012ff1493009ffe849804bfe424c027fea126012ff1093001ffe649800fdf324c007ff1926003ff4c930007ba649800ffc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6006bf185300a7fea298003fe514c001fea8a6014ff1453009ffe829804ffe414c027fea0a6013ff1053001ffe629800fdf314c007ff18a6003ff4c530007ba629800ffc314c025ff90a6000ff88530007fa429804bfc214c0037fb026001ffd413000ffca098007fd504c003fe2826001ffd013000f7e8098007fe404c003fea026001ef5013000ff88098007ff304c007fd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffe4098007fe204c003fe1026001ff8413000ff82098003ff65480017fb2a4011ff9952002dfcca90003fd65480017eb2a4011ff1952002df8ca90043ff64480217fb224010ff99120025fcc890043fd64480217eb224010ff19120025f8c890043ff5448021ff2a24010ff55120087f8a890003ff63480017fb1a400fff98d2001dfcc690003fd63480017eb1a400fff18d2001df8c690047ff534801fff29a4000ff54d2007ff8a690043ff434801fff21a4010ff50d2007ff88690006ff6248005ffa924002dfd4920017fca49000bee5248005fea924002df54920007daa4900036d5248005fe2924002ffd0920017fc849000bfd4248005fe2124002ffcc920017fc649000bee3248005fe9924000fb4c920017f86490003ff61480017fb0a4000ff98520007fac290003fc614800d7e30a4011ffd4520007fca290003fd5148023fe28a4010ffd0520087fc8290043fd4148021fe20a400fffcc520007fc6290003fd314801ffe18a4002ffc8520017de429000bfe2148005fe90a4000fb48520017f84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001efd012000ffc8090007fd4048003dea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe409000bfb2048003ff1024001fb8812000ff84090007ec2048003fc1
  | 2 => 0x210effcc890812fe644843bfeb22421dbf591210eff8c890812fc644843bde3224204af191210effea890877fe544843bfeaa2421dff15121007fec690802ff6348439ff31a4203bf98d21007fac690802fd6348439fe31a4203bf18d210f7fea690873fe5348401fea9a421cff14d210effe8690873fe434843bfea1a421cff10d21035fec49080bff5248405bfa924202ff94921017faa49080b7d5248405fe2924202ffd0921017fc849080bfd4248405fe2124202ffcc921017fc649080bfd3248405fe1924202bfd85210f7fea29081bfe5148401fea8a4206ff145210effe829081bfe414843bfea0a4206ff105210e7fe629081bfe3148401fe98a4206ff0c521017fe429080bf7214840dff10a4206fb88521037f8429081bec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843dffa82421bff941210dff8a090877ff404843bdfa02421bff901210effa809086ffc4048439ff982421bff8c1210dff8609080bff2048405f79024202ff88121017f8409086ffe104840dfe0824201bfd95500d7fec8a806aff6454035ff322a004bf991500d7fac8a806afd6454035fe322a004bf1915002ffea8a8017fe545400bfeaa2a005ff15150007fec6a8002ff6354033ff31aa003bf98d50007fac6a8067fc63540077e31aa005ffd4d5002efea6a8017fe535400bfea9aa000df54d5002ff8a6a806bff4354033ff21aa01aff50d500cff886a8003ff62540017fb12a018ff98950015fcc4a8003fd6254031fe312a002bf1895002ffea4a80177f525400bff292a005ff54950006faa4a8017fc5254035ffa12a018ff909500d7fa84a8063fc4254033ff992a018ff8c950007fa64a8063fc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa006bf1855002ffea2a80177f515400bff28aa005ff54550006faa2a8017fc5154035ffa0aa01aff905500d7fa82a806bfc4154033ff98aa000ff8c550007fa62a8067fc3154031ff90aa000ff88550007fa42a8063fc21540037fb02a001ffd415002ff6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ffa02a001efd015000ffc80a8007fd4054003fe202a001ffcc15000ffc60a8007fc3054003ff902a001ff8815000ff840a8007fe1054003fe082a000efd95400bf7ccaa0003bd655002fde32a8000efd8d400b77cc6a0003bd635002dde31a8017efd4d400b77ca6a0003bd535002dde29a8000efd89400af7cc4a0003bd625002bde3128017efd49400067ea4a0057be5250001dea928000cf549400af78a4a005bbf325002bdf1928000ef4c9400af7864a0003bf6150001df30a8000ef5854000778c2a005fbf5150001df28a8000ef545400bf78a2a005bbf3150001df18a8000ef4c5400b77862a005
  | 3 => 0xfa846227ff9423113ff8a1188a7ff408c453dfa046227ff9023114ffa811889ffc408c407ff9846203ff8c23101ff861188a3ff208c44fff1046227ff08231037fc211881bfc108c401ffb2a6200bfd9531137fcca98816fe654c401feb2a6200bf59531137f8ca98816fc654c44bffb226225bfd91310077ec898802bf644c44bff3226204bf9913112ffac898896fd644c44bfe3226204bf1913112f78c898812bc644c44bffaa26225ff9513112ffaa898897fc544c40d7fb1a6203ffd4d31137bea69880ffe534c407fea9a6203ff14d3101fb8a69880fff434c407ff21a6203f790d3101ffa8698897dd434c407fe21a6200ffd8931005fec498893fe624c4057f3126200ff58931127f8c49880afc624c44dffa926200dfd4931127fca498803fd524c401bea926224ff1493112ffe8498893fe424c44bfea126224ff1093101ffe649880fdf324c407ff1926203ff4c931007ba649880ffc324c4077fb0a6226ffd4531037fca298803fd514c40dfe28a6225ffd0531037fc8298897fd414c40dfe20a6203ffcc53101fee629881bfe314c40def18a6206ff0c531037b8629880ff4314c449ff90a6206ff08531007fec098802ff604c447ff3026201bf98131007fac09888ffc604c4037e3026226ffd413111ffca09888ffc504c44bffa026225efd013111ffc8098897fd404c447fe2026203ffcc13101fbe609880ffe304c407fe1826224ffc813111ffc409888ffc204c447ff0826206ff04131037fecb1081aff658840dff32c4205bf99621037facb10802fd658840dfe32c4206bf19621037fec91081aff648840dff3244204bf99221037fac910886fd648840dfe3244206bf1922110ffea910887fe5488443feaa44221ff15221037fec71081aff638840dff31c4203bf98e21037fac710802fd638840dfe31c4206bf18e21117fea710883fe5388401fea9c4220ff14e2110ffe8710883fe4388443fea1c4220ff10e21015fac51080bff5288405bfa944202ff94a21017faa51080b7d5288405fe2944202ffd0a21017fc851080bfd4288405fe2144202ffcca21017fc651080bfd3288405fe1944206bf98621037fea31081bfe518840dfea8c4206ff14621037fe831081bfe418840dfea0c4206ff10621037fe631081bfe318840dfe98c4206ff0c621037fe431081bef2188405fb90c4206ff08621037e8431081bff608840dff3044201bf98221037fac110802fd608840dfe3044201bf18221117fea11087ffe508843ffe2844221ffd022110f7e811087ffe4088443fea04421fff10221107fe611087ffe308843ffe1844202ffc8221017fc411080bfc208840dff0844206ff04221007feca90802ff654843dff32a4205bf99521007faca90802fd654843dfe32a4205bf195210effec890876ff6448401dfb224200afd91
  | 4 => 0x81bfe62944057f314a206ff58a51005fac52881bfc629440d7e314a205ffd4a5102efea528817fe529440bfea94a200df54a5102ff8a5288cbff4294461ff214a232ff50a51187f885288c7ff3294461ff194a200ff4ca51187f8652881afe619440dffa8ca206dfd465102feea32881bfc519440dfa28ca206ffd0651037fc832881bfd419440dfe20ca206ffcc651037f8632881bff219440dfe10ca206ffd8251037fcc128806fe609440dfeb04a200bf58251037f8c128806fc609440bffa84a205ff9425117efca128817fc509440bbe284a232ffd02511977e81288bffe4094465fea04a22fff1025118ffe61288bffe309445ffe184a230ffc825117ffc41288bffc209440dff084a206ff04251035fecaa88bbff645445d7fb22a22eff99151025fcc8a88bbfd645445d7eb22a22eff19151025f8c8a8817ff545440bff2a2a205ff5515102ff8a8a8803ff63544017fb1aa22dff98d5101dfcc6a8803fd635445bfe31aa203bf18d5102ffea6a8817fe535440bfea9aa205ff14d51177fe86a88b7fe435445dfea1aa22dff10d51007fec4a8802ff6254459ff312a202bf98951007fac4a88b3fc62544057e312a205ffd495102efea4a8817fe525440bfea92a200df5495102ff8a4a88bbff4254459ff212a22eff50951167f884a88b7ff3254459ff192a200ff4c951167f864a8816ff615440bffa8aa205fdd4551037fca2a881b7e515440dfe28aa206df1455102fe8a2a88bbff415440dff20aa22eff50551037f882a88b7ff315440dfe18aa22cffc8551037f842a8803ff60544017fb02a22bff9815100dfcc0a8803fd6054457fe302a201bf1815102ffea0a88177f505440bff282a205ff14151177fe80a88bbbf4054457ff202a22eff5015115ff880a88b7ff3054457ff182a22bff0c151167fe40a88affe2054457fe102a22bff84151037f820a881bff658c40d7fb2c6206ff9963102dfccb1881bfd658c4017eb2c6206ff19631035f8cb1881bff648c40d7fb246206ff99231025fcc91881bfd648c4537eb246206ff19231035f8c9188a7ff548c453ff2a46229ff5523114ff8a91880efd638c407ffa9c6203ff94e3101ffaa71880ffc538c407ffa1c6203ff90e3101ffa871880ffc438c40dffb146206ff98a31015fcc51881bfd628c4017eb146206ff18a31035f8c5188abff528c401bfa946228ff94a31007faa5188037d528c451fe2946229ffd0a31147fc85188a7fd428c451fe2146203ffcca3101ffc651880ffd328c407fe1946206bf98631037fea31881bfe518c40dfea8c6206ff14631037fe831881bfe418c40dfea0c6206ff10631037fe631881bdf318c407fb98c6206ff0c631037e8631881bff218c40dfe10c6206ffd8231037fcc118806fe608c40dfeb046200bf58231037f8c118806fc608c455f
  | 5 => 0x455202ff8a2a90177c5154871ffa0aa438ff905521c7fa82a90e3fc415486fff98aa437ff0c552017fe42a900bfc2154801ffb02a400bfd81521b7fcc0a9006fe6054801feb02a436ff1815200df8c0a9017ff505480bbfa82a405ff941521b6fca0a9017fc505480bbe282a438ffd01521c77e80a90dbfe4054871fea02a436ff101521bffe60a90dbfe305486dfe182a402ffc8152017de40a900bfe2054805fe102a436ff841521b7f820a90e37f64548019fb22a438df991521c6fac8a90e37c64548719e322a400dfd8d521befcc6a90037d635486fbe31aa438dfd0d521befc86a90e37d435486fbe21aa402dfd8952014fec4a90176f6254805bfa12a402df90952016fa84a900b7c4254805bf992a402df8c952016f864a90037f6154801bf30aa400df58552006f8c2a90e37f4154871bf20aa438df505521c6f882a90df7f315486fbe18aa402dfc8552016f842a90037f605486dbf302a400df581521b6f8c0a90e37f40548719fa02a436df901521c6fa80a90db7c405486fbf982a436df8c1521b6f860a900b7f2054805b7902a402df88152016f840a90db7e105486dbe082a400ffd9532005feca990d7fe654c80b7f32a6400ff59532005faca990d7fc654c80b7e32a6434ffd91321a5fec8990d3fe644c8097f3226434ff591321a5fac8990d3fc644c8097e3226434ffd51321a7fca8990d3fd544c869fe2a26402bfd8d3201ffea69900ffe534c807fea9a6403ff14d3201ffe86990d3df434c807ff21a6403ff50d3201ff8869900fdc434c8057fb126402ffd4932016fea49900bfe524c805fea926402df54932017f8a49900bff424c805ff2126402ff50932017f8849900bff324c807f79926402ff8c932017bc649900bfc324c805ee1926402fb0c932007fec299002ff614c801ff30a6400ff58532007f8c29901afc614c86bffa8a6435ff145321a7fe82990d3fe414c869fea0a6434ff1053201ffe629900fdf314c807fe18a6402ffc8532017f84299003ff604c8017fb026433ff9813200dfcc099003fd604c867fe3026401bf181321affea0990cffe504c867fe2826434ffd01321a77e80990cffe404c869fea026433ff1013201ffe609900fdf304c807ff1826403ff0c132017fe409900bef204c805ff1026402ff0813219ffc20990cffc104c80b7eb2ca206ffd9251035fec92881bfe64944097f324a206ef992510257cc92881bfd64944657eb24a206ef592510057ac92881bfc649440d7e324a205ffd525102ffca928817fd549440bfe2a4a206ffd8e51037fcc72880efe639440def31ca203b798e51037fac728802fd639440deeb1ca200b758e51037f8c72881afc639440bffa9ca205dfd4e5102ffca728817fd5394401bea9ca205ff14e51197fe87288c7fe4394465fea1ca231ff10e51037fec528
  | 6 => 0x1a03000807004030008010360400380b01400c038020040ac0800102a0600a00200c02800003006000048020300640081f00e010018290040140600800004004000028000038050000040080201610017803000014000000220480000200603bfd95531f7fec8a98faff6454c01dfb22a600afd91531f7fcc8a9812fe6454c7dfeb22a63ebf591531f7f8c8a9812fc6454c7dde322a604af1915302ffea8a9817fe5454c0bfeaa2a605ff1515301dfec6a980fff5354c0befa9aa603ff94d5301efca6a980ffc5354c07be29aa603f714d5301ffe86a980ffe4354c07fea1aa603ff10d53007fec4a9802ff6254c7bff312a602bf98953007fac4a98f7fc6254c057e312a605ffd495302efea4a9817fe5254c0bfe292a63effd09531effc84a98fbfd4254c7bfe212a603ffcc95301ffc64a980ffc3254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa606bf1855302ffea2a9817fc5154c0bbe28aa63effd05531f7fc82a98fbfd4154c7dfe20aa603ffcc55301ff862a98f7ff2154c7bfe10aa600ffd8153005fec0a98f3fe6054c037f302a600ff581531e7f8c0a9806fc6054c0bffa82a605dfd415302ffca0a9817fc5054c7dffa02a63eefd01531e7fc80a98fbfd4054c79fe202a603ffcc15301fbe60a980ffe3054c07fe182a63dffc81531e7fc40a98f3fc2054c79ff082a63cff0415302efec9a90177e64d480bbeb26a405df1935202efec7a90177e63d480bbeb1ea405df18f521defe87a90eb7e43d4877bea1ea43adf10f52014fac5a900b7f42d4805bf216a402df50b52016f885a900b7f32d4805bf196a402df0cb5202efec3a90177e61d480bbeb0ea405df187521defe83a90ef7e41d4877bea0ea43bdf107521d6fe63a90eb7c31d4805bf90ea402df0875202efec1a90177e60d480bbeb06a405df183521defe81a90ef3f40d4873bf206a43bdf503521cef881a90eb7f30d4873bf186a439df0c352016fe41a900b7e20d4805be106a439df843521cef821a900aff6554871ffb22a438bfd91520077ec8a9002bf6454871ff322a404bf991521c7fac8a90e2fd6454871fe322a404bf191521c778c8a9012bc645480bffaa2a405dfd515202ffca8a90e37e545480bfeaa2a438df5515202ff8a8a90177c5454801ffb1aa400bfd8d521bffcc6a900efe6354801feb1aa437ff18d5201df8c6a9017ff535480bbfa9aa405ff94d521befca6a9017fd5354801bea9aa405ff14d5202ef8a6a90e3ff435486fff21aa438ff50d521bff886a900aff6254805ffa92a405fbd4952017fca4a900b7e5254805fe292a402df14952017d8a4a900bff4254805ff212a402ff50952017f884a900bff3254805ff192a402ff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a901afc615480bffa8aa405dfd
  | 7 => 0x45220007862ee4983cebac6202f2bec5e43e88ec440000b5609600a08e24e85833c0000003a24be5b67f25c460a3cc4ea774142000000a56b0a0ba0009d874634a0003404d00003ae0920000ecb7400007200000053841e00000031c62aba2ab62160000e4b8254ab846580006d80000000006e86380003f4abc00021035249c1343c60004d2ab86040006ea3726bc000aba000000abe92e33800033450e8d0af86d63c2000b5a60098e87e80245a09e0000005960007b6b3cb166225d03840009e29cca6a4fe6261d0b241c02e4bb22de00094496c1700007ea7000009f2000a4aa7c91271c0086a4bbeac0978ac26d000075e20e0405c87a000043c2d800000084002400026616c000ae45c691a52489c5d64b214c93400058e9b06cc55e00068a4a244aa1c29e4700024fa3b09060628167b87709b27eca1ebba5e053e0aa4904a0446000000898000b62428000682826b4c5fc540a0a664a487a21648fe1e659eac623839223ab5eb1e23048e2329ec8181783440c867477698ab60a760d823600019a0a000002a81a6943b8b4a1ba1628287480002901a64b400000008476c4a46b400009c0480300000c218040480680000300e004030090000b0048010060a80100006000003806000010018140100340e82001201400808008000050010000040100400204c0000002005c08803024004000000020040600b000090060000000200580903002400001004018018040380500080900c00400006000018000020020040080000200000007002000000190040b00000001201c0000700a004000000000300000200001c00003000000010000000040001c00604c0000100c000008030020680200a00c0000780b0100080380001800403008016008010020080140000300a0000a803036004008050000000000300e0102280401801c0302e00e010000010020d41580501400401805012054078180360040100100c014000010120100380a0000000780000205c000070000000000c00e02c0000100e17c01800030008060130080040200f01c0140000900a00401003004000158040000000100103c0000201c00202c0000f0001500380f0080080f8020000000002d0020000200200201c0200200e0240d0140140040000e0220100180602600c0a800014004048120260040101e00e00800000000000008280e403c2381d0080040b0040160000080002800c0581e00e0300600100008c028010020000f80400000411819000008008060080100201200000000008008000118000060000080200004004000024000008000000140000807a0040082f0140041300d01600008000006068028000000882b009000014338000240000301200e0380c83c092040000030020000200a0080000800800c014088020020040b0020040000280000001000
  | 8 => 0x558704a8eb22252b2862e4ca00060e9fa6d208a0f60a6b7c27a7b25189f0910a7a9ca1f8a4640ab3225c1467d0ab064e0667be94030a94814a76eaa0000b88000000782000000000bd00002ac77e2c09241f600000051a00085c00000084a1dc868000000304bd897651c00072200087653499ca9e0c265e426422662246bd2526bd494a0008f00001fe2c69de5b05425b20000009e484ca6e5b45ae76a0008c20226c21cea187148c44e8ae0578a4451e9acad2a1005e0000000000005ac0000002c20883a00008b02aa36e39e1c6ba091486e7fc39ab68808398970bd6a4000048883ebe47203bc5f618a000a6672431a39c9026c60001402cc000a60bf07f848aa620008389164a629c7daace16a9c657eb46a0eafc55a000000320198900a2ebe04120781a4a6c1ea16028e25055c6a86c8ad080a07e4e20800643b265403841cb1407a000000b0ea645108f84f60009a82485aaaa2aa407c92abc0590af43743c00fc8049c2b9a33036c1fa52e5fa000a3e21c9dca5a138b4e4d4396000acc5ce00037e9a418600000078085a8f40267cc36a2b6b6e6126b033eb905608b291c34c7648b477c0003d25924e4bb686a31e71a6f8028afa0004e0b1a8c80000c63802e0000342a729e800004200015811000026e0000d62762c80001fc0005d4000a0c3e6b9c076b987ca0005bebce05815e97266e25e082112740b66aca15a67e1521540000000005f255456a268156256b8c6dc00086c3360006f40009920008de33a000b122ca81205c02c2600cc66c0e00d06b84363ec57667267096e2620004348d263042e66a0dc95a8064306ee5ba17c54610057a6ae794980aae4320000d2000a067bc4da000328564a52b060984768d454c8d632c1023662282da9d49daa96ac83648140005662641b273215035cb3003611ca32b8e32a5526323d44ae61473097c50a8a673449447e43ab9472c4ac1326fa1c235a7d272e8dca3440461688c3d6bea6e07a458032e42c3f2aac3a48d88367540945704648f6b0ca58418a98bae4162be7aa64a66859c2f6106974aec346136032000ae600001ea269ba37601a00067a65c390406000034388000652b526de0002225484a8350bde3545282c49b40a461a93a28c25a1728eea206f24083da67856c64c1941e857c7364606fc7ac8c000000000069a00000000044400020672a00000000000000000000088600000068c00000071004444c0682807b416e8561ca7c80b00c018020c00000e2f04f24b60e62b23be97e9424f41a05bc4ec4ee80022090eb722246e40041a87989360008a0a9ab384f0712a9cba8ba605a1e45141ac2d40f810c5b80a8b080000005a60009d60005e87f0a547baba410e88453073cab400078c08c0008880f474a60c0000009946864964480007660c49503e211eb6c61eb549183e
  | 9 => 0x70b9e17e2d20007f600042000000000038a35e7d40000005503480008be0000000000008ae1b635882c7d8000822000bc65045ea04c02e988a046e2656aaa98c8206367a865a75295c31894680c24041474200009a544aee38cbe66c40541cc000a281e09bc00070ebc80008fa0005e61e227473e0140e812202092c8ce484762ad811810a4ba77a83c6f68245121c84aa0000004101888aa8fc37084e0000000185885c2b42be22ae1b485016823400000022c12826c31422e71e93c3f63ac0104d685292031080e5081f299e8e829800046683abe821a000000b8689a95641a0003fa2142b09f81be294196a2c0001087cea8a688126b7009009cb92b00bdc6409cea4c67c90400000003c1740000003e08101828662549980bc3b45d212ea84086506880a864626ec18444e87249a8345d858a0fa3f83de1a263c61c0004ce050bcca2a2bc1ee6900462e80005ca2428309be00028aaf078e1ae27cb581aa0f2000b800006469544000009580000000000007069d0000000af22863d06105da9c03080004de000a806080000000005dcb029f62dc5e2a8c598000b26a4eb9673800015c0000006ac000adca823ca23e6e65fe30c04a000052a5ca5e85e2265f40000004740000b28ac0007e011674c0005a80000000000004b070c0005de0007e6af6000baa00000012aa301763169c47e86da7aeb6a3068a849e0007e24380b452047c88a0000b67e48c64c21206d46f08a254e3ee24a3a60000000003120ac0000003560004521b02f494c5cc4d8b2e4cc0004c6450768692a00000a940000006425a487c93e3fc000b1000052a0000b81b87900740000000008b61ec5940007de6965a24b89a01c48bc4c4922b3a792b787b0aa818c8f21d212c5f8a029fc12432274e0ce38663e0ca908a22b3e6be01651603a44283245c20850c9b8624b2abb00da7c05000de8e27c2568b5ca90a24a3673a6443febc2288708aea9b64682b8382a38bc418e492332ae8b7e5a0a3a19087869c99a6a6282012a3c5ee218a6827079619287a2a05f070229a06e48c278b501bc0001d89e000016624cb4834e46c39446a2588ca69e2d69f4aa6a8847200020000014e9d27726a08cc5328ba96000053c9660607fe964b04a5000092670a96843e0002e20009620000008b83ea42a756326adeae2b3601c21e9aea1a4808467602721140f0870666ad6a129aa32445ea166766a229646e7582ce06c9528e00708e6000606bee2a630e0000000000a250200029200053a36890c75a00000090a4c83c8a0800026aab27fa1480ee62800000079a6b659a9c8a42574a92882a7e9a6b3478a00079cb7a0007ee71875c63a00038e19e79e928000000728bca2ea2120beb2c0ae2e600078895e7789fe1f447a1de9a293868e00013a00000066000013e000ad4000424000000
  | 10 => 0x86223c8960000560ea4bc8908920004542fa11a0004c00003003dc7441d4afe4dc8940000fe0008da7dc7263020004862b4b1c9ee2fc93081c6021d66ca13c572b769eaa780e297a5822fe1f0b203c448247840c3f0a7463400000006ab4491e000ac488e0d400084222ab4019c7840003783b62023626980000008486aa8a462c85475000084452c5862042a236000000c86086400010465040e6b200082e0004e66ba3ba9823a8bb499037cb8a2a417a1da456b647d689e56e87427e6fe9326ce5362ba4fc7f42ec5841305622d000637a94eb1868440203e2f804803058cbda3d896abbc20a82a5ec7169e65c07c46806184f824445881e0009968e47c67a6648144bb8986284a143aa000556ada6c004e9840002a88ea000a
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7505451015f75505451015fb7405451015fb5405451015ff2205451021df6768c510036f6768c510035f7758c510005f5758c51000777658c51000774658c51011df5738c51001ef6638c51001ef4638c510005f5728c51000777528c51000775528c51000df6708c51000df4708c510036f7608c510037f3608c51013fb7408c51013fb5408c51013ff2208c51001cff764c51000cfe764c51011cfd764c51000cfc764c5100067f654c5101367c654c510005bf744c51004dbc744c510006df634c51001edc634c510037d4314c510005fb704c51000df8704c51000df4764c51001ef4764c51000cf4764c510005f7754c510005f5754c51000777654c51000774654c510007b7744c51020fb4744c510035f7734c510037d7734c510007d7634c51001ef6634c51001ef4634c510047d4634c510217d7534c510047d4534c510047d6434c51020fd5434c510005f7724c51000777524c51000775524c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c51011ff0704c510036f7604c510037f3604c51011fb7404c51011fb5404c51011fd7304c51011fd5304c51011ff2204c510205f67688510036f67688510035f77588510005f57588510007776588510007746588510035f77388510005f573885100ddf57288510016f66288510016f4628851003f77528851003f755288510037f3708851000df6708851000df47088510037f07088510036f76088510037f360885100ffb740885100ffb540885100fff22088510014ff764851000cfe76485100dcfd764851000cfc76485100067f65485100f67c6548510005bf744851004dbc7448510006ef6248510016ec6248510037e42148510005fb704851000df87048510037f0104851000df47648510016f4764851000cf47648510005f77548510005f57548510007776548510007746548510007b774485101ffb47448510005f77348510005f57348510035f77248510037e77248510007e76248510016f66248510016f4624851003fe4624851003f77524851003f755248510007f3704851000df6704851000df470485100dff07048510036f76048510037f360485100dfb740485100dfb540485100dfe720485100dff220485100dfe52048510035f87648110016f87648110034f876481100077b654811000778654811000dfb724811000feb7248110007eb6248110016fa6248110016f8624811003fe8624811003f7b524811003fea524811003f795248110007e9524811000769524811003fea3248110007e93248110007f37148110035fa7148110035f87148110007f0714811000efb614811000ff36148110007f25148110007f15148110007f23148110007f1314811003feb214811003ff22148110007e9214811003ff12148110007e12148110
  | 1 => 0x891002cfe755891002cfc75589100067c755891002c7c7558910004ff7458910006bf7458910004bf7458910024fe7458910004fd7458910024fc7458910006bc7458910024bc7458910004ff7358910006df7358910004df735891001cfe735891001cfc7358910006dc735891001cdc73589100fcff7258910006ef725891024cff7158910006f771589100dcff7058910006fb70589100debf40589100debd405891002e7f76d49100057e76d49100567e76d49100047e76d49100567d76d49100557c76d491002e7c76d491002c7c76d49102467f64d49101de7e64d49102467d64d49101de7c64d49100067f63d49101d67e63d49100067d63d49101d67c63d49101b57d72d491003e7f62d49100167e62d491003e7d62d49100167c62d49100577671d49100577571d49101ce7f61d49101ce7f60d49101cf3f40d49101cf3d40d49101cf7a20d491023f7b10d49101cf7610d49101cf7410d49101cf7810d4910004ff7654910004fe7654910004fd7654910004fc76549100067f655491002e7e65549100067d655491002e7c6554910005bf745491004dbc74549100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100073f74549102373c74549102367f64549101c67e64549102367d64549101c67c64549100067f63549101be7e63549100067d63549101be7c63549101cd7f72549100576f725491003e7f62549100167e625491003e7d62549100167c62549100077671549100077571549101b67f61549101b67f60549101b73f40549101b73d40549101b76f20549101b77a20549101b76d205491022f7b10549101b77610549101b77410549101b7781054910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101ae7c654c91001ede634c910006dd634c910225f67694510036f6769451015df5759451017f77659451002ef6659451002ef4659451005774659451002e746594510037b67494510037b57494510037d67394510005f57394510037d57394510005d57394510057775394510007755394510005f5729451005777529451000775529451000df6709451000df47094510036f76094510037f3609451017f76509451017f74509451017fb7409451017fb5409451017ff2209451002cff765451000cfe765451015cfd765451000cfc76545100067f655451002e7c6554510037745154510005fb705451000df8705451000df4765451002ef4765451000cf47654510035f7755451003777755451000777655451002ef6655451002ef46554510057746554510005f77354510005f77254510057775254510007755254510007f3705451000df6705451000df4705451015ff07054510036f76054510037f3605451015f7
  | 2 => 0x17e7c20d951017e7f10d951017e7e10d951017e7c10d95100567c6559510265f7715951017cff75595100067f7559510004ff7459510024fe7459510004fd7459510024fc7459510004ff735951001cfe735951001cfc7359510004ff7259510014fe7259510014fc72595100567f5259510264ff7159510006f7715951015cff7059510006fb705951015ebf405951015ebd405951017d7e76195100567e761951017c7e76195100067f64195100067e64195100067d64195100067c64195100067e63195100067c63195100057d72195100067e62195100067c62195102277571195102267f61195102267f60195102273f40195102273d40195102277a201951025f7b101951022776101951022774101951022778101951001cfe76d8d100067f65d8d100067c65d8d10046de63d8d1002cfe75d8d10004fd75d8d1002cfc75d8d10004ff74d8d10024fe74d8d10004fd74d8d10024fc74d8d10006df43d8d10046dc43d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10046dc32d8d10034fe71d8d1000cfd71d8d10034fc71d8d10046df31d8d10034ff70d8d1000cfe70d8d10034fd70d8d1000cfc70d8d1013ebf40d8d1013ebd40d8d1013edf30d8d1013edd30d8d100057f7558d100557c7558d100067f6558d100067c6558d10005bf7458d1004dbc7458d10046dc6358d10005ef7258d1003dec7258d10255f77158d10004ff7558d100067f7558d100047f7558d1002cfe7558d1002cfc7558d100067c7558d1002c7c7558d10004ff7458d10006bf7458d10004bf7458d10024fe7458d10004fd7458d10024fc7458d10006bc7458d10024bc7458d1013cff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d10046df3258d10254ff7158d10006f77158d1011cff7058d10006fb7058d1011ebf4058d1011ebd4058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1002e7c6554d10005bf7454d1004dbc7454d10014fe76d89100067f65d89100067c65d891003eee62d89100067f75d891002cfe75d8910004fd75d891002cfc75d89100067c75d8910004ff74d8910024fe74d8910004fd74d8910024fc74d891001cfe73d8910004fd73d891001cfc73d8910006ef42d891003eec42d8910006ef32d891003eec32d8910034fe71d891000cfd71d8910034fc71d891003eef21d8910034ff70d891000cfe70d8910034fd70d891000cfc70d89100febf40d89100febd40d89100feef20d89100feed20d89100057f75589100557c75589100067f65589100067c6558910005bf745891004dbc7458910005df7358910045dc735891003eec625891024df77158910004ff75589100067f75589100047f755
  | 3 => 0x6705471000df4705471015f77505471015f75505471015fb7405471015fb54054710035f7764c710296f7764c710005f7754c710005f5754c710007b7744c710287b4744c710037d7734c710037d7634c71001ef6634c710036f4634c710037d4634c71028fd7534c710067d4534c710067d6434c710287d5434c710005f7724c71000777524c71000775524c710067d7324c710007d5324c71000df6704c71000df4704c71011fb7404c71011fb5404c71011fd7304c71011fd5304c710035f7764871027ef77648710005f77548710005f57548710007b77448710277b47448710005f77348710005f57348710037e77248710037e76248710016f66248710036f46248710037e4624871005f77524871005f75524871000df6704871000df470487100dfb740487100dfb540487100dfe720487100dfe5204871002cfe76d95100567e65d951004dbe74d9510005bd74d9510004ff74d9510024fe74d9510006be74d9510024be74d9510004fd74d9510006bd74d9510004bd74d9510024fc74d95100567f54d95100067e54d95100067d54d95100567c54d951001cfe73d9510004fd73d951001cfc73d95100567f53d95100067e53d95100567c53d9510014fe72d9510004fd72d9510014fc72d95100567f52d95100067e52d95100567c52d9510034fe71d951000cfd71d9510034fc71d95100567f51d9510034ff70d951000cfe70d9510034fd70d951000cfc70d951017e7f50d951017e7d50d951017ebf40d951017ebd40d95102257e76d951002c7e76d95100073e74d95100073d74d95100067f64d95100067e64d95100067d64d95100067c64d95100067e63d95100067c63d95100057d72d95100067e62d95100067c62d951017f7771d951017f3f40d951017f3d40d951017f7a20d951026f7b10d951017f7610d951017f7410d951017f7810d95100067f74d95100067e74d95100063e74d95100067d74d95100063d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067c32d951017e7f71d951026e7e71d951017e7d71d951017e7c71d95100067f41d951026e7e41d95100067d41d951026e7c41d95100067f31d951026e7e31d951026e7c31d95100067f21d951026e7e21d951026e7c21d951017e7f70d951017e7e70d951017e7d70d951017e7c70d951017e7f40d951017e3f40d951017e7e40d951017e7d40d951017e3d40d951017e7c40d951017e7f30d951017e7e30d951017e7d30d951017e7c30d951017e7f20d951017e7e20d951017e7d20d9510
  | 4 => 0x971001cfe735971001cfc7359710004ff7259710014fe7259710014fc72597100767f5259710034ff715971000cfe7159710034fd715971000cfc71597100367e51597100367c515971015e7f505971015e7d505971015ebf405971015ebd4059710004ff7558f1002cfe7558f1002cfc7558f10004ff7458f10006bf7458f10004bf7458f10024fe7458f10004fd7458f10024fc7458f10006bc7458f10024bc7458f10036df7358f10006df5358f10066dc5358f10066de4358f10006dd4358f10004ff7258f10014fe7258f10014fc7258f10066df3258f10034ff7158f1000cfe7158f10034fd7158f1000cfc7158f10036de3158f10036dc3158f1011ebf4058f1011ebd4058f1011edf3058f1011edd3058f10004ff7654f10034fe7654f10004fd7654f10034fc7654f102b67f6554f1002e7c6554f10005bf7454f1006dbc7454f10035f67154f102b7765154f10004ff7558b1002cfe7558b1002cfc7558b10004ff7458b10006bf7458b10004bf7458b10024fe7458b10004fd7458b10024fc7458b10006bc7458b10024bc7458b10004ff7358b1001cfe7358b1001cfc7358b10036ef7258b10034ff7158b1000cfe7158b10034fd7158b1000cfc7158b10036ee2158b10036ec2158b100debf4058b100debd4058b100deef2058b100deed2058b10036fa1058b10036f91058b1002e7f76d4b1023e7e76d4b100767d76d4b1002e7c76d4b1023e7f64d4b101de7e64d4b102ae7d64d4b1023e7c64d4b1023e7f63d4b101d67e63d4b100067d63d4b1023e7c63d4b1023e7f62d4b100167e62d4b1005e7d62d4b100167c62d4b1023f7671d4b100777571d4b101ce7e61d4b1023f7631d4b1023f7621d4b101cf3f40d4b101cf3d40d4b101cf7610d4b101cf7a10d4b101cf7410d4b10004ff7654b10034fe7654b10004fd7654b10034fc7654b1022e7f6554b1002e7e6554b100067d6554b1002e7c6554b10005bf7454b1006dbc7454b10035f67154b1022f765154b100067f7654b1022e7e7654b100067d7654b1022e7c7654b100073f7454b102a73c7454b1022e7f6454b101c67e6454b102a67d6454b1022e7c6454b1022e7f6354b101be7e6354b100067d6354b1022e7c6354b100776f7254b1022e7f6254b100167e6254b1005e7d6254b100167c6254b1022f767154b10007757154b101b67e6154b1022f763154b1022f762154b101b73f4054b101b73d4054b101b76f2054b101b76d2054b101b7761054b101b77a1054b101b7741054b10004ff764cb10034fe764cb10004fd764cb10034fc764cb1001ede634cb10006dd634cb10035f6714cb10035f7765471029ef7765471003777755471003777655471002ef66554710036f46554710037746554710005f77354710005f7725471007777525471000775525471000df
  | 5 => 0x76c71549202df6f41549202df6e41549202df6d41549202df6c41549202d76f31549202d76c31549201b76f70549200076b70549201b76e70549201b76d70549201b76c70549201b76870549200176f60549200166f60549200176b60549201b76f40549201b72f40549201b76e40549201b76d40549201b72d40549201b76c40549201b76f30549201b76e30549201b76d30549201b76c30549201b76e10549201b76a10549201b76c105492000dec764c92001eec764c92000cec764c920005ef754c920005ed754c920015ef734c920017cf734c920007cf634c92001eee634c92001eec634c92007fcc634c9202cfcf434c92007fcc434c920005ef714c92007fcf314c920007eb704c92000dee704c92000dec704c92019fe8704c920016ef604c920017eb604c92019faf404c92019fad404c92019fcf304c92019fcd304c92019fea104c920034fe76d85200076d52d852002cfe75d8520004fd75d852002cfc75d8520004ff74d8520024fe74d8520004fd74d8520024fc74d852001cfe73d8520004fd73d852001cfc73d852000cfd72d85202c67f52d85202c67d52d8520006f751d8520006f451d85202c6f621d85202c6f521d852000cfe70d8520014fd70d852000cfc70d852024ebf40d852024ebd40d852024ef710d85200076d5298520006f7619852003df970985200057f755852008d7c7558520005bf7458520085bc7458520005df735852007ddc73585200076d525852005dfb705852008d7e75185200057d7518520085be7418520005bd741852007dde7318520005dd73185200076d5218520036f66118520006f56118520004fe7694520004fd7694520034fc76945200067f659452002e7c6594520085be7494520005bd749452007dde7394520005dd7394520015ee7294520005ed72945200076d529452000dfa7094520005f97094520004ff7654520004fe7654520004fc765452002e7e65545200067d6554520015ee72545200076d5254520004fe768c520004fd768c520034fc768c520006df638c52001edc638c520015ee728c520005ed728c5200076d528c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520005bf744c520085bc744c52001ede634c520006dd634c520015ee724c5200076d524c520007cd324c52000dec7648520036ec764852000cec7648520005ef7548520005ed7548520007af74485202bfac7448520005ef7348520005ed7348520015ef7148520017e77148520007e76148520036ee6148520036ec6148520007e46148520007eb704852000dee704852000dec70485200dfe87048520016ef6048520017eb60485200dfaf40485200dfad40485200dfea10485200367f7559710004ff7459710024fe7459710004fd7459710024fc7459710004ff735
  | 6 => 0xb705952030cff75595200067f7559520004ff7459520006bf7459520004bf7459520024fe7459520004fd7459520024fc7459520006bc7459520024bc7459520004ff7359520006df7359520004df735952001cfe735952001cfc7359520006dc735952001cdc735952008e7f53595201ccff7259520006ef72595200c67f52595201b67d5259520004ff7159520006f77159520004f77159520034fc7159520006f47159520034f4715952008e7f51595201b4ff7059520006fb70595201b67e50595201b67c50595201b6bf40595201b6bd405952001cfe76d8d20085be74d8d20005bd74d8d2007ede63d8d2002cfe75d8d20004fd75d8d2002cfc75d8d20004ff74d8d20024fe74d8d20006be74d8d20024be74d8d20004fd74d8d20006bd74d8d20004bd74d8d20024fc74d8d2019cfd73d8d20006df53d8d2007edc53d8d2007ede43d8d20006dd43d8d2000cff72d8d20014fe72d8d2000cfd72d8d20014fc72d8d203067f52d8d203067d52d8d20306df32d8d20306dd32d8d20034fe71d8d20004fd71d8d2007edc31d8d20014ff70d8d20014fd70d8d202f6bf40d8d202f6bd40d8d202f6df30d8d202f6dd30d8d2001cff7658d2007edc6358d202edef7258d202fdfb7058d20004ff7558d2002cfe7558d2002cfc7558d20004ff7458d20024fe7458d20004fd7458d20024fc7458d202f4ff7358d20006df7358d202ecff7258d20006ef7258d200967f5258d200967d5258d20004ff7158d20034fc7158d2007edf3158d2019cff7058d20006fb7058d2019ebf4058d2019ebd4058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2002e7e6554d200067d6554d20005bf7454d20085bc7454d20015ee7254d2000dec765492002eec765492000cec7654920015ef75549200176f75549200076f655492002eee655492002eec655492008f6c6554920007af74549202dfac745492008f6f54549202df6e54549202df6d545492008f6c5454920005ef735492008f6f53549202d76e53549200076d535492008f6c5354920005ef715492008f6f515492008f6c5154920007eb705492000dee705492000dec70549201b7e87054920016ef6054920017eb60549201b76f50549201b76e50549201b76d50549201b76c50549201b7af40549201b7ad40549201b7ea105492008f6f765492002e6f76549201b76c765492002e6c76549202e76f74549200072f74549202df6e74549202e76d74549202df6c74549202df2c74549202df6f64549202df6e64549202df6d64549202df6c64549200076f73549202d76e73549200076d73549202d76c73549200076f63549202d76e63549200076d63549202d76c63549202df6f43549202d76e43549202df6d43549202d76c43549200076f71549200076e71549200076d7154920
  | 7 => 0x49301bf5e73549300075d73549301b67f63549301cd7f72549300a76f72549300967f62549300167e62549300167c62549300975f325493022e7c61549301bf5f31549301b67f60549301b73f40549301b73d40549301bf7b30549301b75e30549301b75c30549301b77830549301b76f205493000ddc764c930016dc764c93000cdc764c930005df754c930005dd754c9301a6de644c9301a6dc644c93001ddf724c93001fcf724c930007cf624c930016de624c930016dc624c930097cc624c9300975f524c9300975d524c930005df714c930007db704c93000dde704c93000ddc704c93019fd8704c93001edf604c93001fdb604c93019f9f404c93019f9d404c93019fcf204c930034fe76d853002cfe75d8530004fd75d853002cfc75d8530004ff74d8530024fe74d8530004fd74d8530024fc74d853000cfd73d8530014fe72d8530004fd72d8530014fc72d85300067f52d85300067d52d853032edf32d8530006dd32d853032ef631d853032ef531d853001cfd70d8530256bf40d8530256bd40d8530256f710d8530006f76198530045f970985300057f75585300a57c7558530005bf745853009dbc7458530005ef7258530095ec7258530065fb705853009dbe7418530005bd7418530036f66118530006f56118530004fe7694530004fd7694530034fc76945300067f659453002e7c659453009dbe7494530005bd749453001dde7394530005dd73945300075d5394530004ff7654530004fe7654530004fc765453001dde735453000ddc764c530036dc764c53000cdc764c530005df754c530005dd754c530136de654c530136dc654c5300079f744c5303279c744c530326df644c530326dd644c530005df724c530006df624c5300075f524c5300075d524c53001ddf714c53001fd7714c530007d7614c530036de614c530036dc614c530007d4614c530007db704c53000dde704c53000ddc704c53011fd8704c53001edf604c53001fdb604c53011f9f404c53011f9d404c530004fe7688530004fd7688530034fc768853001dde7388530005dd7388530006ef6288530016ec6288530004ff7648530004fe7648530004fc7648530005bf744853009dbc744853001dde7348530005dd734853002cfe76d952008e7e65d95201b4fd75d9520004ff74d9520024fe74d9520004fd74d9520024fc74d952001cfe73d9520004fd73d952001cfc73d952000cff72d9520014fe72d952000cfd72d9520014fc72d952031e7f52d952031e7d52d9520034fe71d9520004fd71d952008e7c51d9520014ff70d9520014fd70d952030e7f50d952030e7d50d952030ebf40d952030ebd40d952002cff765952008e7c6559520005bf7459520085bc7459520005df735952007ddc73595201cdef7259520005f77159520005f47159520315f
  | 8 => 0xfdbf72485400af3f52485400af3d524854024dbf71485400afb7214854037fae214854037fac21485400afb421485400ddbf704854000dbe704854000dbc70485400debf60485400efbb60485400dfaf204854002cfe76d95300a67e65d95301e4fd75d9530004ff74d9530024fe74d9530004fd74d9530024fc74d95300067e54d95300a67c54d953000cff73d953001cfe73d953000cfd73d953001cfc73d95303767f53d95303767d53d9530014fe72d9530004fd72d9530014fc72d95300a67f52d9530034fe71d9530004fd71d95300a67c51d953001cff70d953001cfd70d95303667f50d95303667d50d9530366bf40d9530366bd40d953002cff76595300a67c6559530005bf745953009dbc745953035ddf735953036dfb7059530364ff75595300067f7559530004ff7459530006bf7459530004bf7459530024fe7459530004fd7459530024fc7459530006bc7459530024bc745953035cff7359530006df7359530004ff7259530014fe7259530014fc72595300a67f5259530004ff7159530034fc71595301e4ff7059530006fb70595301e6bf40595301e6bd405953000ddc7654d3002edc7654d3000cdc7654d3001ddf7554d3001f5f7554d300075f6554d3002ede6554d3002edc6554d300a75c6554d300079f7454d303579c7454d30005df7254d300a75f5254d30005df7154d300a75c5154d30007db7054d3000dde7054d3000ddc7054d301e7d87054d3001edf6054d3001fdb6054d301e75f5054d301e75d5054d301e79f4054d301e79d4054d30014fe76d893009dbe74d8930005bd74d8930096ee62d893002cfe75d8930004fd75d893002cfc75d8930004ff74d8930024fe74d8930006be74d8930024be74d8930004fd74d8930006bd74d8930004bd74d8930024fc74d893000cfd73d8930014fc73d8930096ee32d893034eed32d8930034fe71d8930004fd71d893034edf31d8930096ec21d893001cfd70d89302eebf40d89302eebd40d89302eeef20d8930096ec6258930345fb705893002e7f76d49300a67e76d49300a67d76d493002e7c76d493033e7f64d49301de7e64d493033e7d64d49301de7c64d49301d75e73d49300a75d73d49301ce7f63d49301b57d72d49300967f62d49300167e62d49300167c62d49300975f32d493023e7c61d49301d75f31d49301ce7f60d49301cf3f40d49301cf3d40d49301d77b30d49301cf5e30d49301cf5c30d49301cf7830d4930004ff7654930004fe7654930004fc76549300067f655493002e7e65549300067d655493002e7c6554930005bf745493009dbc745493001dde73549301bf5e53549300075d53549300067f76549300067e76549300067d76549300067c76549300073f74549303373c74549303367f64549301c67e64549303367d64549301c67c645
  | 9 => 0x7101854038fb5101854037dbf7694540005be769454037ebe7694540004be7694540005bd769454037ebd7694540004bd769454037dbc769454015dbd75945400073f65945400bf3c65945400b5be739454037f9e73945400b59e7394540005bd739454037f9d73945400059d739454037dbc73945400bf3f53945400073d53945400adbe7294540005bd729454037dbc72945400bf3f52945400073d5294540225be719454037f3f51945400bfb7519454037fb4519454017dbf709454000dbe709454017dbd709454000dbc709454017ebf6094540197bb609454017f3e509454017f3c509454017fb71094540005bf7654540005be7654540005bd7654540005bc765454017dbf7554540005bf73545400b5be73545400b5bc7354540005bf72545400adbe72545400adbc72545400bf3f52545400073d5254540265bf71545400bfb7515454037f3e515454037f3c51545400bfb4515454015dbf705454000dbe705454000dbc705454015ebf6054540177bb605454015f3f505454015f3d505454037dbf768c540005be768c540005bd768c54037dbc768c54037dbf758c5400bdbe758c540005bd758c54037dbc758c54011dbd738c5400079f638c5400b79c638c5400adbe728c540005bd728c54037dbc728c5400073f528c5400073d528c54021dbe718c54037f9f318c5400b7b7318c54037fb4318c54013dbf708c54000dbe708c54013dbd708c54000dbc708c54013ebf608c54014fbb608c54013fb7108c540005bf764c540006bf764c540004bf764c540005be764c540005bd764c540005bc764c540006bc764c540004bc764c540005bf754c5400bdbe754c540005bd754c5400bdbc754c54013dbf734c5400b79e634c5400079d634c5403879f534c5400b79c534c540005bf724c5400adbe724c5400adbc724c5400073f524c5400073d524c5400b79f324c5400079d324c540255bf714c5400b7b7314c54037f9e314c54037f9c314c5400b7b4314c54011dbf704c54000dbe704c54000dbc704c54011ebf604c54012fbb604c54011f9f304c54037dbf7688540005be7688540005bd768854037dbc768854037dbf75885400bdbe7588540005bd758854037dbc758854037dbf73885400b5be7388540005bd738854037dbc73885400ddbd7288540007af62885400afac62885400af3f52885400af3d5288540205be718854037faf21885400afb7218854037fb421885400fdbf708854000dbe70885400fdbd708854000dbc70885400febf608854010fbb60885400ffb71088540005bf7648540006bf7648540004bf7648540005be7648540005bd7648540005bc7648540006bc7648540004bc7648540005bf75485400bdbe7548540005bd75485400bdbc7548540005bf73485400b5be7348540005bd73485400b5bc7348540
  | 10 => 0x49400af3f32549400af3e32549400af3c32549400073f71549400073e71549400073d71549400073c71549403bf3f31549403bf3c31549400af3f21549400af3c21549401b73f70549401b73e70549401b73d70549401b73c70549401b73f60549401b63f60549401c73b60549401b73f30549401b73e30549401b73c30549401b73f20549401b72f20549401b73e20549401b73d20549401b73c20549401b73e10549401b73c1054940005bf764c940005be764c940005bd764c940005bc764c940005bf754c9400bdbe754c940005bd754c9400bdbc754c9402f5bf734c9400079f634c9400b79c634c9402edbf724c9400af3f524c9400af3d524c9400b7af324c9400af9e324c9400af9c324c9400afac324c940005bf714c94037dbc714c9400b79f314c94019dbf704c94000dbe704c94000dbc704c94019ebf604c9401a7bb604c94019f9f304c94019faf204c9400bdbe75d8540005bd75d85400bdbc75d8540006be65d8540006bc65d85400b5be73d8540005bd73d85400b5bc73d8540006bf63d8540006bd63d85400adbe72d8540005bd72d85400adbc72d8540006bf62d8540006bd62d85400073f52d85400073d52d8540025bf70d8540025bd70d85403a6bf60d85403b7bb60d85403a7b710d85403a7b510d85403adbd76985400bdbe7598540005bd759854037dbc75985400b5be7398540005bd739854037dbc7398540006be6398540006bc63985400adbe7298540005bd729854037dbc7298540006be6298540006bc62985400073f52985400073d529854038dbe719854037ebf6198540007b7619854039dbd709854037fb9709854004db9709854039ebf609854006fbb6098540005bf75585400073f75585400053f75585400bdbe75585400bdbc75585400073c75585400bd3c7558540006be6558540006bc6558540005bf73585400079f73585400059f73585400b5be73585400b5bc73585400079c73585400b59c7358540006bf6358540006bd6358540005bf7258540007af7258540005af72585400adbe72585400adbc7258540007ac72585400adac7258540006bf6258540006bd62585400073f52585400073d5258540007b7615854037ebe61585403adbf7058540007bb705854006dbb70585403aebf605854004fbb60585403a5be76185400bdbe7518540005bd751854037dbc75185400b5be731854037f9e73185400b59e7318540005bd731854037f9d73185400059d731854037dbc7318540006be6318540006bc63185400adbe7218540005bd721854037dbc7218540006be6218540006bc62185400073f52185400073d521854039dbe711854037ebf611854037fb6611854037ebd6118540007b56118540025bf701854000dbe7018540025bd701854000dbc701854038ebf6018540397bb601854038fb
  | 11 => 0x4bc7654d40365bf7554d4035dbf7354d400bf9f5354d400b73e5354d400b73c5354d400b79c5354d40005bf7254d400adbe7254d400adbc7254d400bf3f5254d40005bf7154d4037dbc7154d400bf3c5154d401e5bf7054d4000dbe7054d4000dbc7054d401e6bf6054d401f7bb6054d401e73f5054d401e73d5054d401e79f3054d403f5be76d89400bdbe75d8940005bd75d89400bdbc75d89400b5be73d8940005bd73d89400b5bc73d8940006be63d8940006bc63d89403cdbd72d89400aebe62d89400afae62d89400aebc62d894037dbe71d8940005bd71d89400afac21d8940025bf70d894000dbe70d8940025bd70d894000dbc70d89403debf60d89403efbb60d89403dfaf20d89403dfad20d89403e5bf7658940005bf75589400bdbe75589400bdbc7558940005bf73589400b5be73589400b5bc7358940006be6358940006bc63589403ddbf7258940007af62589400aebe62589400aebc62589400afac6258940005bf715894037dbc71589403cdbf7058940007bb70589403d5bb70589403cebf6058940087bb60589400bf3f76d49400bf3e76d49400bf3d76d49400bf3c76d49400bf3f73d49400bf3e73d49400bf3d73d49400bf3c73d49400073f63d49403c73e63d49400073d63d49403c73c63d49401b53d72d49400af3f62d49400af3e62d49400af3d62d49400af3c62d49400af3f32d49400af3e32d49400af3c32d49400bf3f71d49400bf3e71d49400bf3d71d49400bf3c71d49403c73f31d49403c73c31d49400af3f21d49400af3c21d49401cf3f70d49401cf3e70d49401cf3d70d49401cf3c70d49401cf3f60d49401ce3f60d49401df3b60d49401cf3f30d49401cf3e30d49401cf3c30d49401cf3f20d49401cf3e20d49401cf3d20d49401cf3c20d49401cf3e10d49401cf3c10d4940005bf7654940006bf7654940004bf7654940005be7654940005bd7654940005bc7654940006bc7654940004bc765494030dbf75549400073f65549400bf3e65549400073d65549400bf3c6554940005bf73549400b5be73549400b5bc73549400bf3f53549403bf3e53549400073d53549400bf3c53549401cdbf72549400bfaf52549400af3e52549400af3c52549400afac5254940005bf715494037dbc71549400bf3f51549400bf3c51549401b5bf705494000dbe705494000dbc70549401b6bf60549401c7bb60549401b73f50549401b73e50549401b73d50549401b73c50549401b7af20549400073f76549400063f76549400073e76549400073d76549400073c76549400063c76549400073f73549403bf3e73549400073d73549403bf3c73549400073f63549403bf3e63549400073d63549403bf3c63549400af3f72549401cd3f72549400bf2f72549400af3f62549400af3e62549400af3d62549400af3c625
  | 12 => 0xf40d8550266bd40d8550266f710d855017e7f65985500d5be7498550005bd74985500cdde7398550005dd7398550006f76198550055f97098550075fb70585502267f6518550036f66118550006f5611855000d7c76545500367c765455000c7c76545500057f73545500057f72545500067f625455002d7f715455002f7771545500077761545500367e61545500367c61545500077461545500077b705455000d7e705455000d7c705455015f78705455002e7f605455002f7b605455015f3f4054550004fe768c550004fd768c550034fc768c55002d7e758c5500057d758c550004ff764c550004fe764c550004fc764c55002d7e754c5500057d754c550005bf744c5500d5bc744c550006df634c55001edc634c5501375f534c550004fe7688550004fd7688550034fc768855002d7e75885500057d7588550004ff7648550004fe7648550004fc764855002d7e75485500057d7548550005bf74485500d5bc7448550455be76d954042dbd75d95400bebe65d95400bf3e65d95400be3e65d95400bebc65d95400b5be73d9540005bd73d95400b5bc73d95400073e53d95400bf3c53d95400adbe72d9540005bd72d95400adbc72d95400bf3f52d954037dbe71d9540005bd71d95400bf3c51d9540025bf70d954000dbe70d9540025bd70d954000dbc70d954043ebf60d954044fbb60d954043f3f50d954043f3d50d9540445bf765954043dbf75595400073f65595400bebe65595400bebc65595400bf3c6559540005bf73595400079f73595400059f73595400b5be73595400b5bc73595400079c73595400b59c7359540005bf72595400adbe72595400adbc72595400bf3f5259540005bf715954037dbc715954042dbf7059540007bb7059540435bb705954042ebf60595400d7bb6059540425be76d8d400bdbe75d8d40005bd75d8d400bdbc75d8d403fdbd73d8d400b6be63d8d400b79e63d8d400b6bc63d8d400079f53d8d400b79c53d8d400adbe72d8d40005bd72d8d400adbc72d8d40006be62d8d40006bc62d8d400b79f32d8d4037dbe71d8d40005bd71d8d400b79c31d8d40025bf70d8d4000dbe70d8d40025bd70d8d4000dbc70d8d4040ebf60d8d4041fbb60d8d4040f9f30d8d4040f9d30d8d40415bf7658d40005bf7558d400073f7558d400053f7558d400bdbe7558d400bdbc7558d400073c7558d400bd3c7558d4040dbf7358d400079f6358d400b6be6358d400b6bc6358d400b79c6358d400b69c6358d40005bf7258d400adbe7258d400adbc7258d40006be6258d40006bc6258d40005bf7158d4037dbc7158d400b79f3158d403fdbf7058d40007bb7058d40405bb7058d403febf6058d4009fbb6058d40005bf7654d40006bf7654d40004bf7654d40005be7654d40005bd7654d40005bc7654d40006bc7654d40
  | 13 => 0x8121004ff74d8121006bf74d8121024fe74d8121004fd74d8121024fc74d8121006bc74d8121024bc74d812101cfe73d8121004fd73d812101cfc73d8121034fd72d812100cfc72d812105e7f52d812105e7d52d8121014fd71d812100cfc71d81210debf40d81210defa20d81210defa10d81210057f75581210f57c7558121005bf74581210edbc7458121006bf6458121006bc6458121005df73581210e5dc73581210def8605812101cfe76d8d500cede63d8d5000cfd75d8d5001cfc75d8d50004ff74d8d50024fe74d8d50004fd74d8d50024fc74d8d500cede53d8d5048edd53d8d50006df43d8d500cedc43d8d50014fe72d8d50004fd72d8d50014fc72d8d5048e7f52d8d50006de32d8d500cedc32d8d50034fe71d8d50004fd71d8d500cedf31d8d5002cfd70d8d5035ebf40d8d5035ebd40d8d5035edf30d8d50005bf7458d500d5bc7458d500cedc6358d50485fb7058d5000d7c7654d5001e7c7654d5000c7c7654d500073f7454d5047f3c7454d5002d7f7354d5002f5f7354d500075f6354d5001e7e6354d5001e7c6354d500cf5c6354d500057f7254d500057f7154d502b67c6154d500077b7054d5000d7e7054d5000d7c7054d501e7787054d5002e7f6054d5002f7b6054d501e73f4054d501e75f3054d50014fe76d89500c6ee62d89501ce7f75d895000cfd75d8950014fc75d89500147c75d8950004ff74d8950024fe74d8950004fd74d8950024fc74d895001cfe73d8950004fd73d895001cfc73d89504767f53d89500067d53d89501ce7f52d89500c6ee52d8950476ed52d8950034fe71d8950004fd71d89504767f51d895002cfd70d89501ce7e50d89501ce7c50d89501cebf40d89501cebd40d89501ceef20d8950005bf74589500d5bc7458950005df73589500cddc73589500c6ec6258950005f77158950005f4715895046dfb70589501b67e765495000d7c76549500167c765495000c7c76549500073f74549504673c74549504667f64549501c67e64549504667d64549501c67c64549500057f73549500067f63549501be7e63549501be7c635495002d7f725495002f6f72549500c67f62549500076f62549500066f62549500167e62549500167c62549500c76c62549500057f715495022e7c61549500077b705495000d7e705495000d7c70549501b778705495002e7f605495002f7b60549501b73f40549501b76f2054950004ff764c950004fe764c950004fc764c95002d7e754c9500057d754c950034fe76d855000cfd75d8550004ff74d8550024fe74d8550004fd74d8550024fc74d855001cfe73d8550004fd73d855001cfc73d8550014fe72d8550004fd72d8550014fc72d855045e7f52d85500067d52d855045ef651d855045ef551d8550006f721d8550006f421d855002cfd70d8550266b
  | 14 => 0x6bc65d9121006be63d9121006bc63d91214a73f52d91214a73d52d91214a7b721d912149fae21d912149fac21d91214a7b421d9121005bd70d9121006be60d9121006bc60d91214a7af20d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bc53d912149ebf72d91214a6be72d91214a6bd72d91214a6bc72d91214a6bf52d91214a63f52d91214a6be52d91214a6bd52d91214a63d52d91214a6bc52d91214a6bf32d91214a6be32d91214a6bd32d91214a6bc32d91214a6bf71d912149ebe71d91214a6bd71d912149ebc71d9121006bf51d912149ebe51d912149ebc51d9121006bf31d912149ebe31d912149ebc31d91214a6bf21d912149ebe21d91214a6bd21d912149ebc21d9121006bf70d9121006be70d9121006bd70d9121004bd70d9121006bc70d9121006bf50d9121006be50d9121006bc50d9121006bf30d9121006be30d9121006bc30d91214a6bf20d91214a6be20d91214a6bd20d91214a6bc20d912149ebf10d9121006be10d912149ebc10d912101cfe76d8d21006bf64d8d21006bc64d8d210e6de63d8d2102cfe75d8d21004fd75d8d2102cfc75d8d21004ff74d8d21024fe74d8d21004fd74d8d21024fc74d8d210e6de53d8d21034ff72d8d21034fd72d8d211467f52d8d211467d52d8d21146df32d8d21146dd32d8d21014fd71d8d210e6df31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006bf40d8d21006de30d8d210e6dc30d8d21146ef20d8d21005bf7458d210edbc7458d21006bf6458d21006bc6458d210e6dc6358d21495f77158d21004ff7558d2102cfe7558d2102cfc7558d21004ff7458d21006bf7458d21004bf7458d21024fe7458d21004fd7458d21024fc7458d21006bc7458d21024bc7458d21144ff7358d21006df7358d21124ff7258d21006ef7258d211267f5258d211267d5258d21494ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21006bf4058d210e6df3058d21126ef2058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2102e7c6554d21005bf7454d210edbc7454d21006bf6454d211f6bc6454d21006df6354d2101edc6354d2102cff7654521014fe7654521164fd7654521014fc76545210067f655452102e7c6554521006bf6454521176bc6454521005ef7254521015ec7254521037e4215452101cff764c521014fe764c521124fd764c521014fc764c521005bf744c5210edbc744c521006bf644c52112ebc644c521006df634c52101edc634c521005ef724c521015ec724c52100cfe76d81210edbc74d8121006bf64d8121006bc64d81210defa60d812102cfe75d8121004fd75d812102cfc75d
  | 15 => 0xc74d8131006bc74d8131024bc74d8131034fd73d813100cfc73d8131014fe72d8131004fd72d8131014fc72d81310067f52d81310067d52d8131066df32d8131006dd32d813101cfd71d813111ebf40d813111efa30d813111efa10d81310057f75581311357c7558131005bf745813112dbc7458131006bf6458131006bc6458131005ef7258131125ec725813111ef860581310367f7559621004ff7459621024fe7459621004fd7459621024fc7459621004ff735962101cfe735962101cfc73596211667f52596211667d5259621034fe7159621034fc71596210367e51596210367c5159621004ff705962100cfe705962100cfc70596211167f5059621006bf4059621036f71059621004ff7558e2102cfe7558e2102cfc7558e21004ff7458e21006bf7458e21004bf7458e21024fe7458e21004fd7458e21024fc7458e21006bc7458e21024bc7458e21036df7358e21006df5358e21106dc5358e21106de4358e21006dd4358e211267f5258e211267d5258e21126df3258e21126dd3258e21034fe7158e21034fc7158e21036de3158e21036dc3158e21004ff7058e2100cfe7058e2100cfc7058e21006bf4058e21106df3058e21036f71058e21004ff7654e21034fe7654e21004fd7654e21034fc7654e212b67f6554e2102e7c6554e21005bf7454e2110dbc7454e21004ff75582210067f75582210047f755822102cfe755822102cfc75582210067c755822102c7c7558221004ff7458221024fe7458221004fd7458221024fc7458221004ff735822101cfe735822101cfc735822103e7f525822103e7d5258221034fe715822100cfd7158221034fc7158221036ef2158221036ed2158221036fb70582210febf40582210fefa2058221036fb1058221036f8105822102cfe76d95210f67e65d9521006bc64d9521004ff74d9521024fe74d9521004fd74d9521024fc74d952101cfe73d9521004fd73d952101cfc73d95210f67f53d9521034ff72d9521034fd72d95211867f52d95211867d52d9521014fd71d95210f67f51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210f67c50d9521006bf40d9521186ef20d95210f67c6559521005bf74595210edbc7459521006bc64595214b5f77159521184ff75595210067f7559521004ff7459521006bf7459521004bf7459521024fe7459521004fd7459521024fc7459521006bc7459521024bc7459521004ff735952101cfe735952101cfc7359521164ff7259521006ef72595211667f52595211667d52595214b4ff7159521006f7715952122e7e515952122e7c5159521004ff705952100cfe705952100cfc70595210f67f5059521006bf4059521166ef20595214adbe76d91210eebe76d9121024be76d9121006bf65d9121006be65d9121006bd65d9121
  | 16 => 0x893102cfe75d8931004fd75d893102cfc75d8931004ff74d8931024fe74d8931004fd74d8931024fc74d8931034fd73d8931126ee52d8931126ee32d8931106ed32d893101cfd71d8931126ef21d893100cfe70d8931004fd70d893100cfc70d8931006bf40d8931106df30d8931006ee20d8931126ec20d8931005bf745893112dbc7458931006bf6458931006bc6458931126ec62589314ddf7715893102e7f76d49311367e76d49311367d76d493102e7c76d49314d67f64d49310073f64d49310063f64d49311de7e64d49314d67d64d49311de7c64d49314d73c64d49311de3c64d49311375f73d49311d75c73d493123e7f63d49311d75e43d49314d75d43d49311257d72d49311267f62d49310167e62d49310167c62d49311275f32d49314967f61d49311d77731d493123f5e31d493123f5c31d49311d77431d49311ce7e60d49311ce7c60d49314d73f40d49311d75f30d4931004ff7654931004fe7654931004fc76549310067f655493102e7e65549310067d655493102e7c6554931005bf745493112dbc7454931006bf64549311c6bc6454931005df735493101ddc73549311375f53549311bf5c5354931006ef6254931016ec6254931005f77154931035f471549310067f76549310067e76549310067d76549310067c76549310073f74549314cf3c74549314ce7f64549310073f64549310063f64549311c67e64549314ce7d64549311c67c64549314cf3c64549311c63c64549310075f73549311bf5c735493122e7f63549311bf5e43549314cf5d43549311257f72549311376f72549311267f62549310076f62549310066f62549310167e62549310167c62549311276c62549310166c62549311275f32549310077771549310077471549314967f61549311bf77315493122f5e315493122f5c31549311bf7431549311b67e60549311b67c60549314cf3f40549311bf5f30549311276f2054931035dc764c931016dc764c931034dc764c931135de754c931135dc754c9314c5df744c9314c5dd744c9310079f644c9311a6de644c9311a6dc644c9314bf9c644c9311a69c644c93101ddf724c93101fcf724c931007cf624c931016de624c931016dc624c931127cc624c931016cc624c9311275f524c9311275d524c931007d7714c931035de714c931035dc714c931007d4714c931035d4714c93101edf614c93101fd7614c931005df704c9314bf9f404c931127cf204c93102cff765453101cfe765453116cfd765453101cfc76545310067f655453102e7c6554531006bf6454531176bc6454531005df735453101ddc735453100cfe76d813112dbc74d8131006bf64d8131006bc64d813111efa60d813102cfe75d8131004fd75d813102cfc75d8131004ff74d8131006bf74d8131024fe74d8131004fd74d8131024f
  | 17 => 0x1b67c6054a315073f4054a311476f2054a31004ff755823102cfe755823102cfc7558231004ff7458231024fe7458231004fd7458231024fc7458231004ff7258231014fe7258231014fc72582310067f52582310067d5258231034fe7158231034fc7158231036df3158231036dd3158231036fb705823113ebf405823113efa305823113efa2058231036fb1058231036f8105823102cfe76d95311367e65d9531006bc64d953101dde73d9531035dd73d95311375f53d9531004ff74d9531024fe74d9531004fd74d9531024fc74d9531034ff73d9531034fd73d9531136dd73d9531034dd73d953118e7f53d9531136df53d95311365f53d953118e7d53d953118edc53d9531014fe72d9531004fd72d9531014fc72d95311367f52d953101cfd71d95311367f51d953100cfe70d9531004fd70d953100cfc70d95310067e50d95311367c50d9531006bf40d953118edf30d95311367c6559531005bf745953112dbc7459531006bc64595314fdf7715953118cff75595310067f7559531004ff7459531006bf7459531004bf7459531024fe7459531004fd7459531024fc7459531006bc7459531024bc745953116cff7359531006df7359531136df535953116edc5359531004ff7259531014fe7259531014fc72595311367f52595314fcff7159531006f771595312b67e51595312b67c5159531004ff705953100cfe705953100cfc70595311367f5059531006bf405953116edf30595314f5be76d913112ebe76d9131024be76d9131006bf65d9131006be65d9131006bd65d9131006bc65d91314e79f73d91314ef9c73d91310079f53d91314ef9c53d9131006be62d9131006bc62d91314ef9f32d91314efb731d91314e79e31d91314e79c31d91314efb431d9131005bd70d9131006be60d9131006bc60d91314ef9f30d9131006bf75d9131006be75d9131006bd75d9131006bc75d91314e6bf73d91314eebe73d91314eebd73d91314eebc73d91314eebf53d91314eebe53d91314eebd53d91314eebc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bc52d91314eebf32d91314eebe32d91314eebd32d91314eebc32d91314eebf71d91314e6be71d91314eebd71d91314e6bc71d9131006bf51d91314e6be51d91314e6bc51d91314eebf31d91314e6be31d91314eebd31d91314e6bc31d9131006bf21d91314e6be21d91314e6bc21d9131006bf70d9131006be70d9131006bd70d9131004bd70d9131006bc70d9131006bf50d9131006be50d9131006bc50d91314eebf30d91314eebe30d91314eebd30d91314eebc30d9131006bf20d9131006be20d9131006bc20d91314e6bf10d9131006be10d91314e6bc10d9131014fe76d8931006bf64d8931006bc64d8931126ee62d
  | 18 => 0xc51d8951166ef21d895100cfe70d8951004fd70d895100cfc70d89511167f50d8951006bf40d8951005bf7458951175bc7458951166ec625895151df7715895122e7e76549510357c76549510167c76549510347c76549510073f74549515173c74549515167f64549511c67e64549515167d64549511c67c64549510067f63549511be7e63549511be7c635495102d7f725495102f6f72549511667f62549510076f62549510066f62549510167e62549510167c62549511676c62549510077771549510357e71549510357c715495100774715495103574715495102e7f615495102f7761549510057f70549511b67e60549511b67c60549515173f40549511676f2054951004ff764c951004fe764c951004fc764c95100cfe76d815115efa60d8151034fd75d815100cfc75d8151004ff74d8151024fe74d8151004fd74d8151024fc74d815101cfe73d8151004fd73d815101cfc73d8151014fe72d8151004fd72d8151014fc72d81510767f52d81510067d52d815102cfd71d815115efa50d815115ebf40d815115efa10d815115ef860581510367f7559631004ff7459631024fe7459631004fd7459631024fc74596310067e54596311567c545963116e7f535963116e7d5359631004ff7259631014fe7259631014fc72596311567f5259631034fe7159631034fc71596310367e51596310367c5159631004ff705963100cfe705963100cfc70596311567f5059631006bf4059631036f71059631004ff7558a3102cfe7558a3102cfc7558a31004ff7458a31006bf7458a31004bf7458a31024fe7458a31004fd7458a31024fc7458a31006bc7458a31024bc7458a31036ef7258a31146ee3258a310e6ed3258a31034fe7158a31034fc7158a31036df3158a31036dd3158a31036ee2158a31036ec2158a31004ff7058a3100cfe7058a3100cfc7058a31006bf4058a31146ef2058a31036f71058a3102e7f76d4a3123e7e76d4a311567d76d4a3102e7c76d4a3123e7f64d4a311de7e64d4a3150e7d64d4a3123e7c64d4a311d75e73d4a311575d73d4a3123e7f62d4a310167e62d4a311467d62d4a310167c62d4a3123e7e61d4a3123f5f31d4a311d77731d4a3123f7431d4a311ce7e60d4a311ce7c60d4a3150f3f40d4a31004ff7654a31004fd7654a31034fc7654a3122e7f6554a3102e7e6554a310067d6554a3102e7c6554a31005bf7454a3114dbc7454a31005f77154a31035f47154a310067f7654a3122e7e7654a310067d7654a3122e7c7654a310073f7454a315073c7454a3122e7f6454a311c67e6454a315067d6454a3122e7c6454a311576f7254a3122e7f6254a310167e6254a311467d6254a310167c6254a31007777154a3122f747154a3122e7e6154a3122f5f3154a311bf773154a3122f743154a311b67e6054a31
  | 19 => 0x4e5101c7f7654e510073f7454e5153f3c7454e512b73e6454e512b73d6454e5102d7f7354e5102f5f7354e5101e7e6354e512b75e6354e5101e5e6354e512b75d6354e5101e7c6354e510057f7254e512b57f7154e51007777154e512b7747154e5102e7e6154e5102f766154e5117d7e7054e5117d7c7054e5153f3f4054e5118f5f3054e510067d7558a51004ff7458a51024fe7458a51004fd7458a51024fc7458a51004ff7358a5101cfe7358a5101cfc7358a510f67f5358a510067d5358a51036ef7258a511867f5258a51186ee5258a510f6ed5258a51034fe7158a51034fc7158a510367f5158a510367d5158a51036ee2158a51036ec2158a51004ff7058a5100cfe7058a5100cfc7058a510067e5058a510f67c5058a51006bf4058a51186ef2058a51036f71058a5122d7f7654a510167f7654a510147f7654a510073f7454a515373c7454a5122e7f6454a511c67e6454a5122f3e6454a511c63e6454a515367d6454a5122f3d6454a510063d6454a5122e7c6454a510057f7354a511be7e6354a5122f5e6354a511be5e6354a510067d6354a5122f5d6354a510065d6354a5122e7c6354a5102d7f7254a5102f6f7254a510167e6254a5122f6e6254a511867d6254a5122f6d6254a510066d6254a510167c6254a5122d7f7154a51007777154a5122f747154a5102e7e6154a5102f766154a5117d7e7054a5117d7c7054a511b67e6054a511b67c6054a515373f4054a511876f2054a51004ff764ca51004fd764ca51034fc764ca5102d7e754ca510057d754ca511a6be644ca51006bd644ca5101ede634ca51006dd634ca51004ff7458251024fe7458251006be7458251024be7458251004fd7458251006bd7458251024fc7458251004ff735825101cfe735825101cfc73582510567f53582510067d5358251004ff7258251014fe7258251014fc72582510567f52582510067d5258251034fe7158251034fc71582510367f51582510367d5158251036fb705825117e7e505825117efa505825117e7c505825117ebf405825117efa2058251036fb1058251036f8105825101cfe76d8d5116ede63d8d51034fd75d8d51004ff74d8d51024fe74d8d51004fd74d8d51024fc74d8d5116ede53d8d51156dd53d8d51014fe72d8d51004fd72d8d51014fc72d8d511567f52d8d5102cfd71d8d5152e7e51d8d5152e7c51d8d5116edf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d511567f50d8d51006bf40d8d51005bf7458d51175bc7458d5116edc6358d51525f77158d51014fe76d8951166ee62d895123e7f75d8951034fd75d8951004ff74d8951024fe74d8951004fd74d8951024fc74d895101cfe73d8951004fd73d895101cfc73d89511667f52d8951166ee52d8951116ed52d895102cfd71d895123e7e51d895123e7
  | 20 => 0xcfe76d813219efa60d813202cfe75d8132004fd75d813202cfc75d8132004ff74d8132024fe74d8132004fd74d8132024fc74d8132014fd73d813201cfd72d81322fe7f52d81322fe7d52d8132034fe71d8132004fd71d8132346df31d813219ebf40d813219efa30d813219efa20d813219ef86058132196bf7559251196be7559251546bd7559251196bc7559251006bf7359251006be7359251006bd7359251006bc7359251546bf5359251546be5359251546bd5359251546bc5359251006bf7259251006be7259251006bd7259251006bc7259251546bf52592515463f5259251546be5259251546bd5259251546bc5259251006bf3259251006be3259251006bc3259251036bf7159251036be7159251036bd7159251036bc7159251036bf5159251036be5159251036bd5159251036bc5159251036bf3159251036be3159251036bd3159251036bc3159251036bf2159251036be2159251036bd2159251036bc2159251006bf7059251004bf7059251006be7059251006bd7059251006bc7059251546bf5059251546be5059251546bd5059251546bc5059251006bf3059251006be3059251006bc3059251006bf2059251006be2059251006bc2059251036bf1059251036be1059251036bd1059251036bc1059251004ff7458e51024fe7458e51004fd7458e51024fc7458e51036df7358e5118ede5358e51136dd5358e51006df4358e5118ede4358e51006dd4358e5118edc4358e51004ff7258e51014fe7258e51014fc7258e511367f5258e5118edf3258e51006de3258e5118edc3258e51034fe7158e51034fc7158e51036de3158e51036dc3158e51004ff7058e5100cfe7058e5100cfc7058e51006bf4058e5118edf3058e51006de3058e5118edc3058e51036f71058e51136de7558e51136dd7558e5118edc7558e51006df7458e51006de7458e51006dd7458e51006dc7458e51136df5458e51136de5458e51136dd5458e51136dc5458e51006df7258e51006de7258e51006dd7258e51006dc7258e51136df5258e511365f5258e51136de5258e51136dd5258e51136dc5258e51006df4258e51006de4258e51006dd4258e51006dc4258e51036df7158e51036de7158e51036dc7158e51036df5158e51036de5158e51036dd5158e51036dc5158e51036df4158e51036de4158e51036dd4158e51036dc4158e51036df2158e51036de2158e51036dd2158e51036dc2158e51006df7058e51006de7058e51006dd7058e51006dc7058e51136df5058e51136de5058e51136dd5058e51136dc5058e51006df4058e510069f4058e51006de4058e51006dd4058e51006dc4058e51006df2058e51006de2058e51006dc2058e51036df1058e51036d71058e51036de1058e51036dd1058e51036dc1058e512b57f7654e5101e7f765
  | 21 => 0x5611855222f7621185525677521185521b57e70185520057d70185521b57c70185520067e60185520067c60185520073f40185525676f201855200776101855222f7410185521b57e76d81520057f74d81520073f74d81521c57e74d81520057d74d81521c57c74d81520073c74d81521c53c74d81520073f64d81520073c64d81521bd7e73d81520057d73d81521bd7c73d81520067f63d81520067d63d815202d7f72d815246f6f72d81520157e72d815202d7d72d81520157c72d81523167f62d815246f6f62d815222d7e71d81520057d71d81520067f61d81520067d61d81521b67e60d81521b77a60d81521b67c60d81521b73f40d81521b76f20d81521b77a20d81523177920d81520057f74581520073f74581520053f74581521c57e74581520057d74581521c57c74581520073c74581521c53c74581520073f64581520073c64581520057f73581520075f73581520055f73581521bd7e73581521bd7c73581520075c73581521bd5c73581520067f63581520067d63581520076f725815208f6f62581520057f715815200777715815200577715815222d7c71581520077471581520057471581520067f61581520067d61581521b57f70581520077b60581521b67e60581521b67c60581521b77860581521b73f40581521b76f205815202cfe76d95321ae7e65d95321ecfd75d9532004ff74d9532024fe74d9532004fd74d9532024fc74d9532014ff73d9532014fd73d953255e7f53d953255e7d53d953201cff72d953201cfd72d95325567f52d95325567d52d9532034fe71d9532004fd71d953200cfe70d9532004fd70d953200cfc70d9532006bf40d953255edf30d9532556ef20d953202cff76595321ae7c6559532005bf74595321a5bc745953254ddf73595321d5ef7259532554ff75595320067f7559532004ff7459532006bf7459532004bf7459532024fe7459532004fd7459532024fc7459532006bc7459532024bc745953254cff7359532006df73595321be7e53595321be7c53595321ecff7259532006ef72595321ee7f52595321ee7d5259532004ff7159532034fc71595321ae7c5159532004ff705953200cfe705953200cfc70595321ae7f5059532006bf40595321bedf30595321eeef2059532034fe76d85321ad7e75d85320057d75d853202cfe75d85320067e75d853202c7e75d8532004fd75d85320067d75d85320047d75d853202cfc75d8532004ff74d8532024fe74d8532004fd74d8532024fc74d8532014fd73d853201cfd72d85324967f52d85324967d52d85324def631d8532496f621d853200cfe70d8532004fd70d853200cfc70d8532006bf40d85324dedf30d8532496ef20d8532006f76198532005bf74585321a5bc74585321a5be7418532005bd7418532036f66118532006f56118532
  | 22 => 0x91520053d70d91520073c70d91520073e60d91520073c60d91520073f30d91520073e30d91520073c30d91525873f20d91525872f20d91525873e20d91525873d20d91525873c20d91520073e10d91520073c10d915257d7e76d8d520057f74d8d521c57e74d8d520057d74d8d521c57c74d8d520073f64d8d520073c64d8d521be7e63d8d521bf5e63d8d521be5e63d8d521be7c63d8d5202d7f72d8d520157e72d8d5202d7d72d8d520157c72d8d5254e7f62d8d525776f62d8d5254f5f32d8d5254f5d32d8d5222d7e71d8d520057d71d8d521bf5f31d8d521b57e70d8d520057d70d8d521b57c70d8d520073f40d8d520075e30d8d521bf5c30d8d5254f6f20d8d525557f7658d520057f7458d520073f7458d520053f7458d521c57e7458d520057d7458d521c57c7458d520073c7458d521c53c7458d520073f6458d520073c6458d5254d7f7358d520075f6358d521be7e6358d521be7c6358d521bf5c6358d521be5c6358d521ed7f7258d520076f7258d520056f7258d521af6f6258d520057f7158d5222d7c7158d520057f7058d521b57e7058d521b57c7058d520073f4058d521bf5f3058d521ef6f2058d520057f74d85521c57e74d85520057d74d85521c57c74d85520073f64d85520073c64d85521bd7e73d85520057d73d85521bd7c73d855202d7f72d855202d7d72d85524b67f62d855251f6f62d85524b77621d85524b77521d85521b57e70d85520057d70d85521b57c70d85520073f40d85524b76f20d85520077610d85520077410d855222d7f74985521c57e749855222f3e74985521c53e74985520057d749855222f3d74985520053d749855222d7c74985520073f64985520073c64985521bd7e739855222f5e73985521bd5e73985520057d739855222f5d73985520055d739855222d7c73985520067f63985520067d639855222f6d729855223e7f62985521176f629855222d7e719855222e7f61985520077761985521b57e70985520057d70985521b57c70985520067e60985520067c60985520073f40985521876f20985520057f74585520073f74585520053f74585521c57e74585520057d74585521c57c74585520073c74585521c53c74585520073f64585520073c64585520057f73585521bd7e73585521bd7c73585520076f72585520f76f625855200777615855222e7e61585520057f70585521b57e70585521b57c70585520073f40585521676f20585524b57e761855222d7f74185521c57e74185520057d741855222d7c74185520073f64185520073c64185521bd7e73185520057d731855222d7c73185520067f63185520067d631855202d7f72185520157e721855202d7d72185520157c721855223e7f621855256f6f621855222e7f611855222f76611855222e7d61185520077561185520067
  | 23 => 0x1be5e53d8d52576dd53d8d521be7c53d8d5202cfd72d8d5254edf32d8d52034fe71d8d52004fd71d8d525767c51d8d521bedf31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d525767f50d8d52006bf40d8d52006de30d8d521bedc30d8d5254eef20d8d52005bf7458d521c5bc7458d52006bf6458d52006bc6458d521bedc6358d525adef7258d520157c7654d5201e7c7654d520147c7654d525a57f7454d520073f7454d520053f7454d521c57e7454d525a57d7454d521c57c7454d5259f3c7454d521c53c7454d520073f6454d5259f3c6454d5202d7f7354d5202f5f7354d520075f6354d5201e7e6354d5201e7c6354d521bf5c6354d5201e5c6354d520076f7254d520157e7254d520157c7254d521ef6c7254d5202e7f6254d5202f6f6254d520057f7154d5222d7c7154d522b67c6154d520057f7054d521b57e7054d521b57c7054d5259f3f4054d521bf5f3054d521ef6f2054d52034fe76d8552006bf64d8552006bc64d8552014fd75d85524b67d75d8552004ff74d8552024fe74d8552004fd74d8552024fc74d855201cfe73d8552004fd73d855201cfc73d855202cfd72d855251ef651d855222e7c51d85524b6f621d855200cfe70d8552004fd70d855200cfc70d855251e7f50d8552006bf40d85524b6ef20d8552006f610d8552006f410d85521c5be7498552005bd7498552006bf6498552006bc64985521bdde7398552005dd7398552006f76198552005bf74585521c5bc7458552006bf6458552006bc6458552006bf6418552006bc6418552036f66118552006f5611855200cfe76d815202d7e75d81520157d75d81521c5bc74d8152006bf64d8152006bc64d81521b6fa60d81521b77a50d8152014fd75d81521b67d75d81520147d75d8152004ff74d8152006bf74d8152024fe74d8152004fd74d8152024fc74d8152006bc74d8152024bc74d815201cfe73d8152004fd73d815201cfc73d815246e7f53d81520067d53d815202cfd72d8152034fe71d8152004fd71d815246e7f51d81521b67e50d81521b6fa50d81521b67c50d81521b6bf40d81521b6fa20d8152005bf74581521c5bc7458152006bf6458152006bc6458152005df73581521bddc7358152005f77158152005f471581521b6f860581521c73e76d91525953e76d91521c63e76d91520073f73d91520073e73d91520073d73d91520073c73d91520073e63d91520073c63d91525873f72d91525873e72d91525873d72d91525873c72d91525873f62d91525863f62d915258f2f62d91525873f32d91525873e32d91525873d32d91525873c32d91520073f71d91520073e71d91520073d71d91520073c71d91520073f31d91520073c31d91525873f21d91525873e21d91525873d21d91525873c21d91520073f70d91520073e70d91520073d70d
  | 24 => 0xf74589531f5bc7458953006bf6458953006bc64589531eeec6258953034fe76d8553006bf64d8553006bc64d855301cfd75d85534fe7d75d8553004ff74d8553024fe74d8553004fd74d8553024fc74d855302cfd73d8553526df53d85534fedc53d8553014fe72d8553004fd72d8553014fc72d85535267f52d8553526f651d85532b67c51d85534fef631d855300cfe70d8553004fd70d855300cfc70d85535267f50d8553006bf40d85534fedf30d85531f5be7498553005bd7498553006bf6498553006bc6498553006f76198553005bf74585531f5bc7458553006bf6458553006bc6458553006bf6418553006bc6418553036f66118553006f5611855300cfe76d81531f5bc74d8153006bf64d8153006bc64d81531e6fa60d815301cfd75d8153004ff74d8153006bf74d8153024fe74d8153004fd74d8153024fc74d8153006bc74d8153024bc74d815302cfd73d8153014fe72d8153004fd72d8153014fc72d81534867f52d8153034fe71d8153004fd71d81531e6fa50d81531e6bf40d81531e6fa30d8153005bf74581531f5bc7458153006bf6458153006bc64581531e6f86058153595be76d91521c6be76d9152024be76d91525873f75d91521c73e75d91525873d75d91525873c75d9152006be63d9152006bc63d915258f3f53d91520073e53d915258f3c53d915258faf52d91525873e52d91525873c52d9152587ac52d915258f3f51d915258f3c51d9152005bd70d9152006be60d9152006bc60d915258f3f50d91520073e50d915258f3c50d9152587af20d9152586bf75d91521c6be75d91521c63e75d9152586bd75d91525863d75d9152586bc75d9152006bf73d9152006be73d9152006bd73d9152006bc73d915258ebf53d915258ebe53d915258ebd53d915258ebc53d9152586bf72d9152586be72d9152586bd72d9152586bc72d9152586bf52d9152586be52d9152586bd52d91525863d52d9152586bc52d9152586bf32d9152586be32d9152586bd32d9152586bc32d9152006bf71d9152006be71d9152006bd71d9152006bc71d915258ebf51d915258ebe51d915258ebd51d915258ebc51d9152006bf31d9152006bc31d9152586bf21d9152586be21d9152586bd21d9152586bc21d9152006bf70d9152006be70d9152006bd70d9152004bd70d9152006bc70d915258ebf50d915258ebe50d915258ebd50d915258ebc50d9152006bf30d9152006be30d9152006bc30d9152586bf20d9152586be20d9152586bd20d9152586bc20d9152006be10d9152006bc10d915201cfe76d8d5202d7e75d8d520157d75d8d52006bf64d8d52006bc64d8d521bede63d8d521bf5e53d8d52014fd75d8d5254e7d75d8d520147d75d8d52004ff74d8d52024fe74d8d52004fd74d8d52024fc74d8d521be7e53d8d521bede53d8d52
  | 25 => 0x8010006000000000004e002001800400000f00700000020080000034000006001000400404f003800800000f007800c044001003800000c002000002401c014002800400000e0000008002007001002000600a001800400001500a0008002006025003000200400f00040020010060000000001000000000800500000180be0030000008000004001801400a00b00c0000006003000001c00000e001801400001f002800804400102d001001200800180700000000000070002005000002c000003002802002a0030088000000001003801400800f01800280380000078000000006000000800200000f800000800f003006001c000004800c004002001000000200f0000008038003000801000000a001000c00a00f000016c014000003000c008005001802400600900700000060000008000010005000800401801f000800000a000001000c01c016006800000000100500c800a032005801400a000001800000a0050058000014000000803800a030000000005a00701500140000130010014012004008001405c003001800000a00300180000400000018004014015008001800a00000b8068000001000801000003e5c5be76d91531f6be76d9153024be76d91535bf9f53d91535b73e53d91535b73c53d91535b79c53d9153006be62d9153006bc62d91535bf3f52d91535bf3c51d9153005bd70d9153006be60d9153006bc60d91535bf3f50d91535b79f30d91535b6bf75d91531f6be75d91535b6bd75d91535b6bc75d91535b6bf73d91535b6be73d91535b6bd73d91535b6bc73d91535b6bf53d91535b6be53d91535b6bd53d91535b6bc53d9153006bf72d9153006be72d9153006bd72d9153006bc72d91535bebf52d91535be3f52d91535bebe52d91535bebd52d91535bebc52d91535b6bf32d91535b6be32d91535b6bd32d91535b6bc32d9153006bf71d9153006be71d9153006bd71d9153006bc71d91535bebf51d91535bebe51d91535bebd51d91535bebc51d91535b6bf31d91535b6be31d91535b6bd31d91535b6bc31d9153006bf21d9153006bc21d9153006bf70d9153006be70d9153006bd70d9153004bd70d9153006bc70d91535bebf50d91535bebe50d91535bebd50d91535bebc50d91535b6bf30d91535b6be30d91535b6bd30d91535b6bc30d9153006bf20d9153006be20d9153006bc20d9153006be10d9153006bc10d9153014fe76d8953006bf64d8953006bc64d89531eeee62d89531d67f75d895301cfd75d8953004ff74d8953024fe74d8953004fd74d8953024fc74d895302cfd73d89531d67e53d89531d67c53d89531ee7f52d89531eeee52d89531eeee32d8953034fe71d8953004fd71d89535ae7c51d895300cfe70d8953004fd70d895300cfc70d89535ae7f50d8953006bf40d89531d6df30d8953005b
  | 26 => 0xc000000400200401b00080060090008004018018005800000a000006810801403000280bc00a00100180980100050000018046009002002400e00900080040140150000010036001000007400000a01401ec00a02c002000c016003000005400200800e0028024001000801c000008009802009e023000001c09c0070018030010006000803400801300780380000010018000000001000001c0000020100004000000000000c02000800380c800400100d805c00a001004800006c000000801401000000200140000100018018002006000007400400100000000240100058000006028000000001400100100040200000068004004001000001000a006000004c0000030098058006001000000400600000700080060000068010006008002000806a01300a8000018009004800003400100e001c00e002001800001e008020803c002000000000000c0000010000000002014800000801400b800c00a009008800c006001004000802e00100200040040000000000006003001002800002c000007000000b0000010000000006801005e020019001401600400780040060060010014032019001000800200100000f4002000021800401402900300b4006000006804000c008000800400200100e803802200a0030020016000000803400a00100481d801001f0100028000000000804000000400080cc00200300280280360030028018000002002000800000e000801400402e0028000006000000000806a01000280c40000130088000000001000002400000b00e8004004011001000003a0020000000034000002000c00805a0000024006000000005801c027004000001e0010000000038002002806800c0030000064002000000002801c019014800c00600200080100020030000064008004009004801a001001801c00a01a004009801600000d8000000009007802801601500780cc042003000000c016000000005001a00a002000000001b005804002e0050068000002000000005c0080060008000000002002007c000003000001800a0180000010008001004000002e01e0000000014002018000000000800000a000e006002002000e007006000800e0100120004008000019002c02a0010058000024004006800c03200000380b005000c0068014034004010001404c0000000020016016018801002200000000140260020010010042000000000000e0190018018016001007000400000c000806c01a011016005c000000003800000c000000000402e00000300080400180038000010003000003802a0020018050000007005000000000b002801c000005000004800002800d000801600300600ac014000002803400a01b001001000c00100480d000c005000000c0000230000004010002016000001c005008001000c008000
  | 27 => 0x570780b132c1c8013c841ef2488bdf0ebcb17052c7ae00003a7095c8e20750f3d2184d864074d9716e4000292800027fc3660000fa60000e081da000038803671ff4e5b1828c5632ac5ce420000011180a310307903f9400007e89712824e540ba46f941805080670b451fe4d5e304c7c11864278003004800300a800400a0120010060048015003801c00000600000400020170028030000006000800002600a0000000000034008004804801700580280020070068000028004004000c006006008006c00000000780b401800d0000000026001001001002c000000001c03200500400540000140008060056003012807000c00f00f822c00a002001800003e0000020004016006000000002c0090000000024001005000400800200d0030006013000800c0460070020018000000000000000600400000bc008006000809c014001001000801200000a00040080000078014000004003001000c0020018004008018000803800c001009000802800c0130014002022003001800005b0018000000002000006c00a001000800400001b0028084000004001000400600500b00000020060048008006003000013801200900800000080170090000002007000800000400200000040000000000000000001003001401401b000001c0020000000018000000001800003a00d00100240040030070004024000000006c00001700b000000a0150000058006000001800800000b0028000002006005800c004004000800c01800a000804002e000000800400203100c80440000a3003807400800a001002c00200000300740a6001000000001200800000e4006000006800c030002009000400000100000000080000030030010022000000c0440000068050008003001800c00c000000000c01000600400f0092000001800401401e00f802c022004002802804a004000000000200400080080160130020000008006000002c0600080060004000001000000c000001015800400a00b01a805c044006011800000400400300b801e0010020018002017000000001200000300000120030048004004001003000000001200600000140000140004000001008800002a004001807c00c000000802805200d0008040000007000803c00200100180040020080000018006004000001800200100c0000002001002005400400000800040c6002000007000c0050028000002004007001800400400c000c0020000000000008007000010000800c00a800801c00d00c001001a01c000803c00601e000800000e009001000400800200f801c00000002d002c0080000058004004002016800001a000000000800001d009800404e00c003802800800f00280100b00020000080006000004000000600102f0028002000002005001400700b812800c003000000000
  | 28 => 0x23e44a150fac0f033642db31f40aa2e1c00044000002a84f8b000090517ec6f030ec15302885a700002a500008392bdcf6610b46cc03ec5e92e8ce5d12c032338f45bf28986bb374ce9a2d250c426b0d9143a45d10d186862ea04fd21207553c181111f109853c3000039f4b9b399891420a0a010000ab342ecd9c0f3009d35f88c52050db10c983bc10e0ea140a4fb220a8c2800f000000000000d74e3b0dd48ee00009c000001890000a0e00005b602b03b1339cdd80000fb81df82dc17b80001d344e00c046b0208cf841e445693c6d0e71d6c3dc19bc76c16ac06732fc1b916641910110fef31b8000347cd2a14dc2ef0e010662aec1440e785231aa4b2a42e091c3c988f90b1cbed21d800033e49262430a890d9429c2db855537f013f2858fd43560e4728bc6390000a4b28fcdd60da005e1d8c93c4070a9a02486ff2d88ece21ccff41c786e30000e12032d04c1eac0d8000073d2fb811603145192ba4e1100000003ed4ddf14f4f1e0fccf5732f07f7032093100000000cece400cfca9d3df4000334c63d0ff021730307d70000b8a0550b2900003c222d830f35d4e3a2a5080e23e068e1b6cfda00000001ac90760000165000000023588a21ed4000221cd1021f8000000066b3d90a8b10b800025fcd8900010c000009b52b749331c987ce198c0030fc03fa1634ba502e88451cb89cd0c441cb3948d67262c00010840001c204493da826a07840000000bff0000000170047c00000002fa0b0e1ca835014b46fc25310612708868077403a264437420c507733f488c3e0ca3416bc1cf0f4cef8334840e41680000000d8a30bc9452d507734268000398cd56000024b31a051d261c6c10f388c7232c92a34b000000002a0180091916c45980b8844f235c77f11047d800000001cc4bf32a8c000123000000000000de4d110db40002c6c0002a4c47a289cfd60000e593968aac1fb80e2337c733028400031f8000000037a3f300000f2cea2202860f00009b93ac0486000021021f00003028bc9050c57e115458b1a1469c24948643f7824a2b8cc1c14d0df00e8c62e14604500f545f0413cfc7166c168286070627a00832508ce81a08af90098e21417c63b28dc4620e0c2b93fc82912b986f5390800013acfb33c14ac30f58bdd071421f0000eb6255083d159c656000000000000002b280001d84c0e2fd41d0368c2122a30e17246c6e90d68f6d3498ae129d0e1e33900ed1c9430e1650f5c134c2cc1ec910400a80062df0d3e3ab47001d20b430e84b5801d4c7715786c210bc3b60d584b2405456c34bd0b0324c605299c10f19f83fd3ae8f501300adf1010f171f7404c039449d41d070a1f64e2b319ccc2198898c2468de500402ea06a4bd80000b1213580b80000b59138800042785d21bb4b0c1a74b20216c20c20b500b05f057d27b
  | 29 => 0xe4a281b38e62434c35b0cf432b0b3494b1d0c746010caf20a74a1f2b0505d2c04d9908e8a110764ec2235405015b8d1a1f8cff519e81100e445863a7879f3754f32410402c00007aa21c471505f4d1532e8591000022b00011060ca00003df800000000000cb40000000d4e00010f42eac000000000000002b40000629268c3632f1c71f06ecb5725c81f814a00e400006a313d80003a24beb3a2ce68134000009f4a13274473f130c1863e7cfc933d42390edc00000000491cd888402288e73404aa813488940000ffa1868c6541f8de34228d1e0000a4e00000002b2c4ee28d8df33c0cb463df0004081c54f2d6c6f40c14a3a3cd0bbd0e300001f18c7100006410000aa91c348130000bb62b5431727c4d703b34b38363407b05b44570e210fb11e445802140140800e8f0fd0e9011b0f6330d0a9b34fc2700190a732ed081f1414a330000cc91d587782ec465e3af42f401185f23150ab14360d06000082700000001b740000000000000000032509b40d80aee04c4e414018d312458b413a1057600000003134f2b2d7061000000000000de809b4bd1122c00042dd08717f0626310ccc3256c8bc18301a717f4df90fc81960b28dfd160c9864330f4e2284283189c09603a80250dec35f25b45cb03fc41c3a8c0001e20d463430dc82a5468f2158461125851c0000a6b0e24c973a800511060ec8379d0831e8c502383473540c054c29ec0002718e4f086830d3f388a51c150b52e6484b2e208a00270dba0e3ccd743dc0000000d3b3930d8f40900b60054aeb1e6400028c80000000ac212fc0000e04fd72e340da2970f670aa4a6332a90c21b842591f289551040000141809e37bc8b1309c741082884416201151ec4cf607f05c732e00000000c023b3d07c2ad40003118e650000000168506932b4f3c249c6490000ab20000b7340100002408000000057100c4e6e3d085221f9c0110498bc50da4ef00000eea19606fd367c89334000000f60c4f075c0000b849630000fbd06488632e2c81a288843d2538acf2fd80202d8c0ab35b8158311c552136cdf2354822131d4634360844e3d143510a14a19110c819046c03d09c4000193c00034480000001071016485f1e7477d41a02f202bc000287400f250cfc41ef85f813a07b0325500e26d8e730c1c2d711c10b6401cfc2062c00005dc91f3b8c37607b4bd3000008f18f02a133e03953a48e1a24400700cc4bf8179000000001632decc86203cb4b3b2811a12f908e08c8097383879420d0b05358c7670fa0e8c3800f041678daf01f41a60c849a912d8bd22f34224158c9ef33cc52c41887293a582942f18c190000fff3ad0000000000000000373c5876501c8000000031408c419500010461aac65d000027500004a63d2507000010fe17c4c9c093cc1e3e5484200005f40000967000035
  | 30 => 0x2900010ad3f909a542f08ec2cbc7bb02c4bef07fc8000234cb3000053f01007512720dc31a5cfe20000a9219d06af000037136e0da5177078435445b33c4cfea1158000000000000000001e5c1ea388812e42a4b6d184c7d3000000032c46170bc00953b905303a005b504746a421a400009100000000e8e2f78b4802082a717dc497357c2ac2a5c62112880350724ec0213855b413465a2d30c59018cbce0ecc2422eec4aa151c90d38a0f14153465513c851008b4f7b0000e030000393351c30c17406da37d4b7e237c4760000bec26083ef16d102d2dc800039907df42f8f0b1b14ced3b6830a44146382c58a7e04f4ad70eec57811a4198114400007cc35512dcb4d1e302d412b450c06e80000a58ca104b061237c4af831087c7086d1011d604b942448a60be83363bd432010080001e6c0d91860d1640405893ed059a40f09d8000103623ec000000012440b088f03c80000000bc33e5c00000004a31aa0df700000d20000b15000019e04e420f000000017d40002534fbe25040182b4d09d18d4a1229c44c802a016c3fecd2e11684160d2802b36d01a40dc0d730f9c4080bac1b231f0b2833ec0d33d80e872d44f9606ac67537044142cc10a70dfc9b201a812918c00d140cc2ff000067613684683ec416e1e0833a27f0aea13c00002e5802e118c437431895c1b9c1d3400c59208800003b0471a1db80002334d573d60edb3584d80000032931780000000e3740780003318e7a29740002034ee9142cbca00002c3022c00031688e13ab8aa7384051e221461d19186eb1f8809110681210d38db5000049e2bc472f180c9110684a481704e4e19442e42c00c9e112d0390000da12a000ef1e4cce521ac81223d00b31fc45a82e9cb9a2d540281a9436100f8aa401e825813650f510a47b82318f8808a8a66098825d3a04ab900010a2442ced43174397241ce8a0000000000083f0924a8d2030bc10000ab000006ca2de81aa3ae498d00010980f40fa73000a612d284f50c0cb1d271c84d2670fa2349c3870e7400042042c805e8f5b38d05c43bb89da0ce0efe1adce913f0ca431e9ce4614590de41c86660c60c391f544b105549e51b802d610cc84335310ee2ee89ce22fc6932a390563adcbd741485bd35f44990410a1e19009e204a8bf1108c4f8000000000001eb2b402d30000000000069503e00002978266216400043d90cd0000b5f0dacb2637385620074d6b3260000000000000003d900006bc1a44e95132cad428c4c183c440000000a25049c02310d0dbb3090fe10850d8c09d017141ccdf6000000000009530000ec5000043e13b482400000001bc800012702a4094866d22245c21e290a614850e619e05ac18aca4113050f00000c313220cfc000031508180002bb49e70b386710e900000430d4d0000f4c22e415f343406019
  | 31 => 0x9fc00017680000a1ceff136000000010d628801371a044f708e00000000661000008600002400f6c0001dc07830194fa407d4b831ff10971838da83b809011a6455706cc29b33141af00000001f586ee29a800040650a3000033013445734084e32000053322ecb9709a42da32bc5c81e846730000be92f3cf39206cdc400000000000e0b0a2400015b4000226863f00006521b7c32e00004a80000e8322608100034e4800006bf00000000000f1c176c89f03a036f066c97835d81610598b92000041f003800040c8879000043902c075d00000002044000000068824743ff0518b74000059626f90b240e80003eb4f6b079404723950d70000c8e0000707217800015100000cbc93e08248c035e492135900000000f02418c00042a80000000da0133469a10c45bb33a800043a8ba22500e9441010dc04f8faf31c89b72908f1231883162b10be51e8862306302bf371c556039834d30185b0424048e12bc62f22f4056373027b1f2cbfc1b5c7ea2cccae500000000000ddd1ff802224a02983d2075709181901714ddc1fc80000000dd90000a082c1800005bc60d2f6c5e034800001698c2a00008db08f000022dc77b1b88633000051310d8ded199000000000000af82ed3378e82175907a1f30a5b09782b73f48ab61d1c84f26b410e182407f070c6d23860000000052b3954ed8179462c2a2800000002033b8831e1e1c0001c388171858c3c2ef89a82cc8d442c3c93f00c8e53000089c44280000000d92000000026e8f7319ed049278024522a024c3f8d0b31b3d0f93eec00027f897c0d10b7d0000494173c0001cc905b3aa0b6415acff80fece570525018342c16904bc4de08780e1082c8410404a9c05ccee540981d53e8036421dcd7823c401f3de8cd407d00bf294c58139bc55834e0151191419a27d8bc238300531dc8c4b38b48dc37a89803e8417f26801190f680e911744d53c4078627742b815a8c4c0fd44c23af0d5a13ccac01c04fe6016c8081ffc45916b48e43bb4c8a1ed01c738ccef4000004f3cf84740268d881d7800001b4000399c7522c685a3037c572000078e21b000019a400000003d730986b8174c000000034b2bf400036b0000345c233186c00001040002c88abd00002e33810f6e366d0e500000001a250530cc8cdb1820cff3ce84ea1778a4d000006f0f8098800003de39707c9279104a2480cbe35042ee00009900000c1f0000d683658000443074507f800000000002abc0000f10e0519c0ea53e34b69407c14e099030906100002fe505533d00002b1800029bc00026550420f049f81ad43344248b3d00a442824b472c2c9cb6b0000253042017b00210d212206c411908ef36990c917e80000000965037800007c8de63b840003ec01743204fe70000e3921608af39d8aa006d845300002c1000101301b0c
  | 32 => 0x792252450d272c8da3e8c4b309acf941928a2321d454903e446e02d0306024cd8e109c22e3b4c24d40c4d451f807ed10c8be033b0f61018459516909320628e300c4c8f716a4c49403441d0008055105cb8629b48f608fca8703b015c07d825a0000abf343c40b088cb913a70c53097c0000000f1504883f92dd416000007090dccff0385845f1fd02c9248c8953c600001c6c4ce358000025280000000baf0000c4814282bc1a7c1132520b9506500c106b43e93a6101600008d01be819701dcfd921245150e980900ec062d00008510e6400027500eb067402f0834fdd3cc42f91ba8b9029e82e833c873c0d4c520187c53a1c6080222e83f709382aa355065701d04bd0000f6822b08060000e4500004030000504000000012e06d0000048316000001224a000000b0a2be80003d2cf5d23782e039840a643e88aa437c9c425180dd0a4c7de2c103450c1015d021cd2b311400004c8b253b6457b30b4c05209864707e448115045c93ea030b387c000285c00010ecf411fa109b00304902fa9079365076a0a18cfe2e84dcf12686c0295c2954008de4000035c1730bd60a7ccb900003783b98c9904ec17927701e204280000000d85000083e1a6ca992cb4b78000000041f43ea064c6d81f3c0002c8c43a00002a831e48ad2328e8635881db19f470f301c1b7019803b00000001b2029a27d459742b8425314107b0330a7700000002ec801900000000b6497428b4b1f4014fd83554f240000ebe08dc00042b0adb0000a140000e7b000000022907391f942df18901e82258000214049f1570fc034d083a0844e7f3084bd52b489ea0b18f8a4048bb715984d40bdcd32027c0d64024a882344c870c484980188b473f2814d15c04c7000078d257c3860000b1931c01bf27244b53e1c0b93cfc5e718c40000500bd01d90fba34c09ab3afc0000a384e62bd81363e690cf05907541f0905e01490e82b70038219cc9d0000b520df0d5304cc78b026082e41640002cd8be142340a41c5c2351aa8089042cd0a0ff80763b104cc19fcc3a1f84b112a050941a78ed21878951240c01b334039a356c0000b9c18d000000041b80003aa8c520504dbd0ed0120375cb5a084ce5608740ce1a0c648354000032a41c614bc93b2a78f90333cdee12005bc18102633054dc20f8cd3c34143ed0f20f1d00002f83ba0bcb34d47dc096c00000003a2129c9d03ef05381fa40d734cc17232b8959124400032d400000000003610a2938706072900cdc3808000169400011ac24702949c30d788520068ea63c8000035706802228565121405c320c0000000bad24f4a3d1df006b14a474e00000000ac40002b20f7103343493b5cc610588000000000000000000a04000000000016140003034d0718d800005d40003344f5200000001374e38022102a2e6000017280002
  | 33 => 0xfd51e54a8600000e33efc1bc0000000149835700010ba00007c81d6441323106b90000000002442c000059c0000b240000e8d0ae8a2427b438d26cc970244d0783b402c03e0822714946b63c342ad3d44a9034b4f2d2b88b612560c2e1becbe63cecd662bd4efb23a4d7f1b586151448bb53cdc9df2944d4a1f4813800009f7000088241200000db0ce920cc91523603ac31bcf852d10614000023003f8fdc333902e00003f830880c9067c40700000000ee09af00004ae344d0f312f0a4639c46901a80d6a2bbc000422c0004408deb1ef4eef23750fd2c24c5b32b105101f8a063004e2f07387d00f0020e3d34c402ecc0c013100fa3f8087b41b057a31440bb38507222994cca2e110221b649db08888d938249832a14ce3059c000350890e1d3cedf005898431aceec0d30b0337884a411007fb2428f4030b05841da49fa280cca71130f53195076b0280c33000058f3934d370000385208108c24e853e24a4e1d0ddc54623088c12eb105409dc86a36881e91c0cab43edcb891014bb82574000000109f1af847204f0f2342a0f802840a1c2704ec3303c0003450c7800004bb000070b17cc71301b8c2b07f465f3068ba628e4b9d194c1590e38b1e1d4cf9d00002dd07080003a20ca51cdc0000000d6c103c0000ad4a5840042a300000000000fab3f3c8d323f9025178c906000000000001c8068c8ab24ac3902eb8b213de4e9d2bd0a2116750a019382de0f48000104503730c00000d08b1c177d09c09f109340a059f26c0886272840009bc1b83d58f380470000176000000000001e000001ab05540000f59000000000006200bd4420000000038981813a64f362a7c0003b74b9e39dc0000ac8a9800000003f0400000289393cb0f0f3e640b510fc5ae2dfc0002fd070c000000028ece2c3110000000004d31383392dc508625d8c8b19c8b8522f8d6f3c646673d3c6ba3cc08f00b2c4841b4c14237f8aae0e9410d282c0243f6cc4109b0b39360486f21fc000056c84a04d4324390c0001a1c890000029e205800035d01051538f720c0889b2d08bf01ac40002c3400033548813224bbc000000023245b22584b6f0a2c77123e800033ac000281cbf723d4000112108426f000006b104500007241fbceac146d0a13fe41cc3bdc05a33c0b5d1a300002f1062a00010c514d4cbb3e787600000cb2299074c05f8c8f1818637095872310c1058245c354161c4d724e0f1f29a033300001ee13c4b4e2b1483b000053b1bdc0132d4000030fce4b124c21c2558b9c000026e1c640000000742000022609e4ce6000107f0000f4627f5035000000000000000000ce2227800022c0c1d34e8a7c30109bd1e14114075844d25ccdb33aa4c6d36906921d700210000c3e1f6c4542220d493700e3e140ce0a362c712068867c06082fd30d8fcd0f50
  | 34 => 0x8fb9051423d00d0000100400030c8a55000043c1eb48b30000de91c4085c3e30b65419c6a600000000014f893ddc42a26681800000000000055f0000f091b3422f2f5075f3b44c03389c65000007f628349793b546e6061c00000cc99d37fcf080fc4509435491e1c7454a1400000319800000007d131810110abc000106c0000000ae71acc6de34842f33bc800025f49c500009de23fc0002a0c000139412b2678000298000002b84e935ecc1714c458e0568dc5122909636b886643bccdd17f83b9361c2c5432c0001f505b830450c31a504870f8857400000000f3c00030dc8531a8455a2d9838b000000027acf7506d42180000000000090f0f448ce000069613284ef2da8b6842bc4ec044895000003aa39f00be1cacc4a36e40003b2c5640a480000000d3d00000c330480003564e9b06144351b2c2162bc000000004e3000025c1e6050f39605320000473309434f3a4c89700001c00000afb265c83729e460b20240000664250025066c43c45a228b80000000000353cde01324d4b332c98e3f1871109cc27a23c88a730209750c682901d0068b041c49b23f408e215008128d4d1b0804faa2f009f23894e1504086681b94fe800d849215e416a0aec52434103823fb4347180453911800581ef0ca003b8a721fe83ec2a9407c1199065230c82106c4db009c82ab402856000008150e4800017509cc17fc4f9157482c1e3c000264c00028b0c5c29b800000002551e94c9b269839b2274ec72b340002b809040000cc841704dc00008253ca88991d6902b01c4000000000000009600000b8e21e89f3211c3ba2598f7619b8ad83e6c0000000ad1000033e275cecc11c42a200000000000b530a1104e040014c0000a5a029c0000000000000016b1d101da000000023cc2d242e4b5e2cb8c82000010900000002cdc0003cb80003bf41a026900001b50900000000000000000150000128031c1bcc00000000000000b8f2a3c0003ff43e632c0000098400025f811e273c5533ca000008a0c7b000085d05d8aa200000003a7c36a30e0e070000afc1048d770000dd100000000f1c12820c10f20dc80e043b07772cac7202784219274c00003401ca000022c000090821003ee1a880000bc400000002c235f10db2bcc86e1eb101b06d09fb3f4d0ce348c68d372c34104d0a9643647492d58bda0710c7611a89981390e290558d481b187f5376c8030a980f61910de1442444a25e90d413f823b2cfca0f2380c1b1be09a73dd00990c7503415a0abc3bcce500cd40f41f903841680dbc431ce0f224464224b8ade0f349ae1facc74178800000007e61e90da90e600003980dde00005112d0073b28140002c2095e38a897b11dcdc9328805d123ce1311f84c622d43b22ea8ace235106f00009813f20cc7190cabe2590a3018e8db615f10f83f40000
  | 35 => 0xe1a9c0003aec40d000037d1a2800037487c540e018e1b900004374b0227c0000047d0e03c88ce040682802c410272cec017031c069000093610acf07000000000e4fa53304000222c58c305900c0000be42c5000026c4704391096e20d8a3e1c7000039b43c332580003ea4fcb24d09571e980fd35c4ed600000121970dcd4340b8200000f31db4000201c0004420ba41de429941acc144050d1819dc2360acc000238c0000000c1024bc000039ce490b40000000081c000000036a866a0000b3e0000559000099b342498a00009240d0cd834220d7a438c3ae27987ec29a441936f8b790000d2801084ac3594c801fc096f1efc00116f862510180000bb02e5202ce7000000000000e3627e40002db0e51324887d3bd831b29242021808be21ab4c632cd09371ad023403dc8051ee8f0022c81471208d931ca00780ef50ed0ca8f7f2424ac92b585e80d00d032f9cf6f42acdbf111c58a35745d526ec96932d0a5432981e32e3000024b01063cbc00006a095a116ccb741d4bc82688e0608a40001c082b63230a7d400028f3fa48b800003b513e85dd42c4c2307347891294857000072d32d8000108845e411c0000000000000000025a0edc00000000000000323503f2b68c9a107855011d4dec3aacc0b06c054b2828ff3045c4ba0a30bfb3240bfa34703002fc881d151506a1438a45415ca1a2ea482209fc000000074a3cccbcc04c02fb0c4032500007b7422466021e001c00000001640952000000000000002248e7516e896a1e78000264847f090cc200494f782ee40ca00000000000c570000ef10000ab7149c000000084c24c003f349400038c4a382cf00fc30d40002e80eeb0ea06dc0c20000000000000000002aa86bd34e4eb1000004800010ff00001ae36ac9ee0000a703fb04cf25acb602e7cb7000003e40578d7217bcd4000005c3369cbbf20a49963a149f40000000410c5f90528cef14a86110bd879a062000000007760000fee14d90820000e5f0549050171800043200001d2cd9a0f144ab17b41d22bfc7501b0cb3500000bd4304205002c319099402d3244cf70e7cc7a000048d11ecc091314fb61054a751de80001dd09d50000a910000fc53e0400007ec51a000091200004260f247a80000eb302300d436b40450000f620b108a33d680000000e6a23a86d10000db707445d917840003290e01020020802b47162a1088337eca523ff000017340001108c9f1e58000350cb760b980bc23205b70e70a3c26e07a03ac80001024f980000d020e8000034742600000832268490b21d03c62b64c5f2bf88620790df4036c54325b0a041090acc040c5772ae8000429106429305ea1cf8f441b1c000053c3371a108720138ee7145c6ae20e07210eac5aa33c444532f4ca320bc00040ec28238910990ea43ca18c80000000000335
  | 36 => 0x3678e3f3154fdf00003961cc0f551b546f60950000000000000008463e18e9700010d141b4860001ca50055ce352ce90e11c50ccc09f8a023dc0b6726645d725dcd360fd88554390d19278c1df408cc5822b8eaf0e281a519303e13e4c4e7375087002dc4442168f2723acef909d90bd009c49542d09d208102150894ce1000046f007808440811070db80d514b8f4a35a4000263c4e12588c6a04b50eb00010fc15fc94f11b4e2308f85613368aad2b1cf8f29644a10b541503740467192ceb51ce81783a9cdf8342009b31b03582234cee3c685f62650bfd3fc4e1939b09bf1b247da179832723a028a32a032c42fc5420f746f1412cf0e2c2c0dc18f80f53fd88fc331011839f8d0e18710171eccc841ba05401ea493523484f439e073414506280798c6433e876f37188e6297c5eb0c7cab81ed85ec2cc50440c88ea4000004b376800000000000000000000000000000000000e740ab800035b400000006fe293c0000000f5f07dc1bd31ccbe3076040a1f34d9d1bb00003b18989000094720d4a82000000000000003eb864d063c2bd0704a6c1d9908f22a4781033c0c200006650b441f0000000003c400021946592060a56233c00040f43590000feb000109500c00683d1cf6c28303e53bf02b03f4453c365426738f000000000000000f4320ac3620000000000079c0000ec93d78b932e5059304e825127a4cd83c28bdc403c1231170f351fcce791c9c51f21b4aec2e04aab07b00c639290ca1bbc1be31fc9d611950851f0088e20f029702c8aa60efd10300010e236602682d3cf9c00004fc00010da1a6100811e05070000f6502a44df2460a2b1f0ca780778e6931a43480f7c00001e4f25286c76200000001dd43ad364004a1fe0ccd40bc24813ec00023b4000017cb772ba00000000a47079cd2207c4000196cdca0000000267cf540000efa0770148000000013fc5750000c3d00000002f64f0128a8f9201cc24133003be233000016088b415bcae40000000429400000000000000f2900004b439c82d81ce00003da400032140000df8b801ee4e2e000018339ac33c0000170251000003102fe0000a620000ffe0e50eb80a200000b3cf8e0a3447d29d8bb00000452000000020109d92ff85481888a44140400034a4000154481e386c8803eb09aa2cb02fc36c8ff739787af12a4b18349103e37e8ed
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa77815d952440010fd0c3b2a4880030f1d0765491002c3fc10eca92200587d821d952440018eb023b2a4880031d88476549100063a908eca922000c3f401d9524400187a803b2a4880031bc8076549100063d100eca922000c6d201d952440018f2403b2a4880031d84076549100063a080eca922000c3e76dd15244001878edba2a4880021fe1d63549100043e43ac6a922000a3f8458d524407147908b1aa4880029be09635491001536412c6a922000a76869c552440018e8ed38aa488002d560e71549101b53a432e2a922000c74765c5524400b0fd0bbb264880021f617764c9100043fc2aec992200587c855d9324400117f08bb264880122f211764c9100046fc1aec99220008ef825d9324400917d083b264880022f610764c9100146e43ac69922034a9c8458d324400559904b1a648800355d957394510216aa32ae728a2042d57525ce514400d9aec0b9ca28801b74d817394510006cba02e728a2000d95405ce5144001ba440b9ca2880029d21953945100053a432a528a2000d557354a5144001acae4a94a2880bf1e1c3655451017e3a3b6caa8a2000a7486549514400b8e8eca92a28800359dc952545100053a432a518a2000c3c74d95314400187ecbba262880030f197744c5100064e3a6c698a20069d583dd53144085aaea7baa62880063d219754c51000cf8402ea98a202fc7476d9531440898e8ec32a62882772d1db744c510006d8386e898a2000de220dc931440738e8eda9262880029d219524c5101b63a3b2a498a2000d677254931440015a90c99262882ef1d9d86588510005b2c10cb10a2000c3c74d95214409bcc843b2a42880030fd9774485100061e32ee890a2000cac74d8921440031f50db8242880063d219754851017e3a3b6ca90a2000e6462d9521440898e8ec32a42882532d1db744851000c7a432e690a204dc7876d9520440978f0ec32a4088002da608654811000735c32a49022000b6a8654920440016d10ca9240880039a219524811001735bb2a49022002e68765492044001e5708a9240882ebca2115248110007b140aa49022000f6181549204406dcd6c2a9240880dbd8d855248110007b0a96e29022000b71851c520440017a30638a4088003d85487148110005e8c1ca29022000be1829452044001ec2a528a4088003d85495148110005f0c14629022000f61528c52044001ec2a498a4088003f04c9314811000cf443a429022006ce876485204400dbc0e290a4088006f821d2148110036f043a429022001be28648520440037c10c90a408800bb8219214811001771bb2429022006de276485204400dbc0ec90a408800bb81d92148110005f1c2a429022000be1854852044001ec6ca90a4088003d81952148110007d1c224290220b9fa08448520440017c70690a4088002f860d2148110
  | 1 => 0x90aba2c68800237e0d7458d1000477c12e8b1a20028ec825d1634400117d0e3a2c6880030fdd47458d100061e3a8e8b1a2000c9c74dcd63440051dd0fb92c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031be177258d100063642ee4b1a2000caf40dc9634400195a81b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100245f424eca9a20008bd849d953440010ff0abb2a6880022fe117654d100245e422eca9a20008ef825d953440051d904bb2a68800e1fa1f6554d100061e3a6caa9a2003a5e83d95534400187ecbba2a6882df0f1977454d1000536c16ebb122000a6d821d762440010ff0aba6c4880161f21574d89100046fc1ae9b1220038dc835d362440010ff0ab9ec4880161f21573d89100045fc22e7b1220048bc845cf624400155d09996c4880be1f21b75589100043f43ecab122000c3c74d9562440018b8e7b2ac4880021fa1c65589100061e3a0cab122000c5c7319562441798eee232ac4880030fd9774589100061e32ee8b122000c5f65dcd62440018b8cbb9ac4880161fa1f75589100061fa06eab122000c3d40dd5624400917d0fba2c4880030fdd774589100061e3aee8b122000c3f52dd1624400187aa5ba2c4880022fe0374589100045ec06e8b12200087f855d1624400b0f90aba2c48800237e0d745891001c6e41ae8b1220008ef825d1624400117d0e3a2c4880030fdd474589100061e3a8e8b1220038de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bea5b9ac4880031754b73589100064fa06e6b122000c9d40dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001958e9b92c488003331cf72589100063a3aee2b122000c3e849db524400187b093b6a4880031d88676d49100063a90ceda922000c3f409db524400187a813b6a4880031e88276d49100063c904eda92200087f8758f524400b0f90eb1ea4880028fe1163d49101dd1e422c7a922000a6f8258f52440054d904b1ea4880122fa1276549100045ec24eca92200087f855d9524400117f08bb2a4880122f21176549100046fc1aeca9220038dc835d952440011ef02bb2a4880161f21476549100143f43ecaa922038a3e84d95524400147b09b2aa4880030f1d365549100143e43acaa922000c3f65dd15244163878cbba2a4880021fa1a76549101c51f424eca922000a3d849d95244001878e93b2a4880029b60a76549100061f424eca922000c3d849d952440010fb053b2a4880031b60a76549100061fa04eca922000c3d409d952440018de413b2a4880031b48276549100051fc22eca922038a3c845d952440014bf06bb2a4880de9720d765491000537c12eca922000
  | 2 => 0x97654b100051fc22c6a962038a3c8458d52c40014df04b1aa58800a9b2096354b100053bc32e2a962045c74765c552c400b0fd0bbb265880021f617764cb1000c7b40eec99620008bf845d932c400917908bb2658801a3721d634cb101a54e422c69962002acc8258d32c400d4e90ca92a38800359dc9525471028eaba9eea98e2000d677254931c400d5a90c99263880023de1975487100045ec3ce9b2a20048bf875d3654400187f0aba6ca880030f21574d95100061fa92e9b2a20bd8bf805d365440df17b00ba6ca880030f5d254d95100243fc3aa9b2a2000c5d7394f65440014eb0329eca880030f9da74d95100059cc04e9b2a2000c3e765d365440014bf06b26ca880029720d64d951000537c12c9b2a2000a6c82593654400147d0831eca880028f61063d95100543ec38c5b2a2000a3e8418b654400147b08316ca8800297a0c62d95100052ec18c5b2a2000c6d7218b654400147b0f3a6ca880028fe0274d95100051ec04e9b2a2000c3f875d3654400147f00ba6ca880028f60174d95100051f420e9b2a2000c3d741d3654400147d09b9eca880028f61373d95100062fb9ce7b2a2000a3e841cf654400147b0839eca88003175cc73d951026d3b408e7b2a202fa75811cf654400147d09b96ca880028f61372d95100061f3a6e5b2a2000c3d74dcb654400187ce8b96ca880030f5d172d95100061fa02e5b2a2000c3d405cb654400147d08396ca880028f61072d95100052f418e5b2a2000a5d831cb654409b4ed02396ca880be9d60472d951017d3d400e5b2a204da79801cb65440010fd0f216ca880021f61e42d95100052f41c85b2a2000a5d8390b65440010fd0e216ca880021f61c42d95100051f42665b2a2000a3d84ccb65440010fd0f196ca880021f61e32d95100051f42465b2a2000a3d848cb65440010fd0e196ca880021f61c32d951017c3f43e63b2a200087d87cc7654405f0fd0f90eca880021f61f21d95100043fc2ae8b2a20008df835d165440071b906ba2ca880023be09745951001476412e8b2a200287c85dc965440010fb0f320ca880021fe1d64195100052fc1ac832a2000a5c8359065440014df04b20ca880029b20964195100051f420c632a2000a3d8418c654400147d08310ca880028f61062195100052f418c432a2000a5d8318865440018dae4310ca880022fe1172d8d100245e422e5b1a2000a9e848cb63440010fd0fb2ac6880030f1d36558d1000636396cab1a200087e871956344001878e832ac6880031b1c86558d100061fb2ee8b1a2000c3c65dd163440018decbb92c6880031b1977258d1002c3f43eeab1a200087d82dd5634400187e81baac6880030f5037558d100245f43ee8b1a2000c3f75dd16344001878ebba2c6880022fe037458d100045ec06e8b1a200087f855d1634400b0f
  | 3 => 0x8a924000b2f80dd1524800165b01ba2a490003ca1c3745492058717b06e8a9240b0f2b60dd15248001e5421ba2a4900029be1973549201b536432e6a924000b2f845cd52480b765908b9aa49016b531cd7354920005b5c02e6a924036b68805cd52480b765d09b1aa490002cb61363549205f72731ec6a9240bee4c6358d52480bf6d700b1aa4900dada2037154920007b1086e2a924036a6e869c552480458d8ed38aa49016ecba12715492000596c24e2a92405ab4e839c5524800169b0738aa4900dadaa027154920005b4c04e2a924036a6c865c5524800165f08b8aa49016ecb2117154920005b5c02e2a924036b68805c5524815b8d8ec38aa490003595c471549201b5b5400e2a924000b69801c55248001ec42038aa4900dadaa1f70549201b6b543ee0a924002b6a86dc152480056d10db82a4900db5a9db70549201b6b43b6e0a924000f2b84dc15248001e5109b82a490003cadd37054920007943a6e0a924000d6b73dc15248001ad2e7b82a490002da6077054920006b5b8ee0a924000d6971dc152480031d90cbaa64900067a201754c9202cdc7426c6992400096d85dc5324800117f08baec2900122f21175d85200046fc1aebb0a40038dc835d7614800fad2e0a94c2900465b21d525852000697ba2a4b0a405bd2c745496148001a9ee6a92c29016b531cd525852005eb5b82a4b0a400096f87548614806d2db0ea90c29016f4b9d1521852000696ba2a430a405ad4e735486148001a9ae6a90c2900023de1d61185200053a42ac230a4000e655258461480031d90cb94a29000a5be1d529452002d36432a528a4000c6d7654a51480b7a5ce8a94a2900034b5d152945202d6a739aa528a4000d4d7354a514806dad4e0a94a29001a3e2197094520006b4a92e128a400687c87595514800d4e902b2aa2900031bdd952545200045fc22ed18a40048bc845da31480031d90cb9462900db5a9c1528c5200347c432e118a4000d69525c2314800917d093b262900022f612764c52002c3f428ec98a400087d851d9314800d1b90eb1a629001ab5205634c52000637bb2a498a4000c6c765493148001a5ee8a92629016f4b1d1524c520006663b26498a4059d8c744c931480031d90cbaa429024f2b1db7448520006d4386e890a40018ec865cd214800917d0fba2c7882722fa1c7458f100346f43ea6b1e2000c5f75d4d63c400d1b90ea1ac78800e1f6177654f1000c7b40eeca9e20008bf845d953c400917908bb2a7880122fa1f7458b100061fa96e8b162000c3d52dd162c412717d0e3a2c5880028fe1163d4b101dd1e422c7a96200287d85dd952c40031ed03bb2a5881171d9477654b100045fc22eca9620048bc845d952c400d0f90eb2aa5880da9da077654b1022e3b38eeca962000a3f845d952c407147908bb2a5880029be0
  | 4 => 0x24c0010ff0aba6c4980161f21574d89300146e41ae9b1260048bf875d3624c00187f0aba6c4980030f21574d89300064fc1ae9b126000c9c835d3624c00187ea4ba6c4980030f54974d89300064f98ae9b1260c08bf805d3624c02d17b00ba6c4980021fe1571d893002c3e42ae3b1260048be849d9524c00117b093b2a49800a1fa1f65549300061e3a6caa92600287c87595524c00147f08b2aa4980e28f211655493002d2e432a6a926000c5c7654d524c07147d093b2a4980028f61276549300061e3a4eca926000a6d829d9524c00147f08bb2a4980e28f211765493000537c12eca926000a77815d9524c08b4e902bb2a4980030f1d076549301b52e432e6a926000c5c765cd524c00169f04b9aa49800637219754c930004aec2ee299260008bf845d7614c00917908baec2980023de1d61185300346e41ced28a6000c3e74d96514c0031b90cb9ca29800317d9573945301362e32ae728a600395f8754e514c00b4b90ca9ca298003179d953945301362e32eea98a60018dc865d5314c139938edba26298003661c3744c5300054ec26c498a6039c5c76d49314c06d8b8eca92629800353dc9524c5300043fc2aed10a600587c855da214c00117f08bb442980122f211768853000c6e432e710a60048be849d9214c00117b093b2429800637219734853000696a96e8b2a4000d4d52dcd6548001acaa5b8aca900031d1947159520006b2a90e2b2a40048be87dd1654800187ea5ba2ca900030f54b74595200045fc06e8b2a40008bd80dd165480011bf06ba2ca9000e3720d74595200047bc0ae8b2a40068f4815d1654800117d0e3a2ca9000e37a1f73595200064fba6e6b2a4000c9c74dcd65480018bea5b9aca900031754b73595200064fa06e6b2a4000c9d40dcd654800193ee839aca90003271d073595200347b43ee2b2a4000cb774dc56548001968e9b8aca9000335dcf71595200066a39ee2b2a4000c7752dc5654800196e81b8aca900032d50371595200063bba8e2b2a4000cb7741c56548001968e838aca9000335dcc71595200066a398e2b2a40008bd879d3634800917f0eba6c6900030fd4974d8d200061ea92e9b1a40bf8bf805d3634802b17b00ba6c690003175d753d8d2000566c16a7b1a40048df8750f63480010ff0ab8ec6900161f21571d8d200043fc2ae8b1a400587c855d163480011ef02ba2c69001a3d2057458d200245f424eca9a40008bd849d9534800117f08bb2a6900122f2117654d200046fc1aeca9a40008f7815d9534800d1e902bb2a69000e1f21d6554d2001d2e41acaa9a4056a74815955348163958edba2a4900036a1c37454920014b6c2ee6a92405ad4e53dcd524800165f08a9aa49016ecb2115354920006f1086e2a9240b2b2e87dd152480b7a5d0fba2a4902c78bddb745492058f163b6e
  | 5 => 0x2ad60463185400045ec3cc430a8000a9e83988615000193ae7310c2a0003275cc62185403c68f39ea430a8000d1d73d4861500efa3ce6a90c2a0003475cd52185400ae97392a430a8000d2d72548615000136f0eb08c2a030eece0161185400061fa94ed28a80048bf809da515000917b013b4a2a01bf2dc4276945400065a884ed28a80009bb805da515000187f0abb4a2a00030f21576945400061fa92ed28a8000cbb805da515000187aedb2ca2a0003479cf65945403868fa92e728a80bdc9f605ce5150001b36c0b9ca2a01bf65c4173945400b49fc3aa728a8000a3c8654e515002da3ce6a9ca2a00564fe1d52945400051e432a528a8000c3e7654a515000187aeca94a2a01df479cd52945400068eb9aa528a8000d2d7254a515000137301bb2a2a00024fe157654540004cfc1aeca8a801699c835d9515000135f04bb2a2a00566b2097654540004ddc02eca8a803993c85dc951500df2790ea92a2a00034bdc9525454037d9a40aa4a8a80009bb805da315000193aedb1c62a00022fe19728c5400045e432e518a80009b980dd9315000197301bb262a00022fa1a764c5400049fc2aec98a801793c855d9315000133f06bb262a00026be09764c5400acd6412ec98a80009bb805d9315000193d063b262a00032760c764c5400064fa98ec98a8000c9c531d9315000193e643b262a0003278c4764c5400064e188ec98a80048bf801d9315000917b003b262a000327cc0764c5400064e980ec98a8000cb7101d9315000196a203b262a01be6760f754c5403868fa9eea98a80008bf865d531500011790cbaa62a01be6721d634c5400064e3b2c698a8070b1c8558d315018573700b1a62a00030fddb524c5400061e3b6a498a8000c3f765493150001878eca9262a00034bdc9524c5400ae96392a498a806f99c874c93150001938ec99262a0057631c9324c54037dca40a6498a800093f855da215002f2790abb442a000267e0d76885400b4ce41aed10a80009bb805da215000117f0cb9c42a00022f2197388540004dcc06ec90a8000c3f52dd9215000187aa5bb242a00032e60376485400045f434ec90a800093f855d9215002f2790abb242a000267e0d76485400b4ce41aec90a80009af825d9215000137700bb242a00030fd4876485400061ea90ec90a8000cae211d92150001958423b242a00122fe0076485400245ec00ec90a8000caf201d9215000195a403b242a00032dc4076485400065a880ec90a80008bf865d521500011790cbaa42a00022fe1973485400045e432e690a8000c3d74953654c00917d0fba2ca980030fd4b74595300045fc06e8b2a60008bd80dd1654c0010ff0aba2ca9800237e0d74595300045f438e8b2a6000c3f751d1654c1838beebb9aca98003271d373595305be4e3b6e8a9a60008bd879d36
  | 6 => 0x51f438eca928000c3e871d9525000187ce63b2a4a00030f1cc76549400061fb90eca928000e2f721d9525007147f003b2a4a00e28f60076549400061fb80eca928000c3d701d95250001c5e403b2a4a00038b48076549403be8f39ee6a928000a3f865cd52500014790cb9aa4a01df471cd735494000597c12e6a928015b2e82d8d525000165b05b1aa4a00024fe1d63549400049e43ac6a9280c7e1c6358d525018d67700b1aa4a00028fa1a71549400051ec34e2a928000c3c769c552500ef63d0738aa4a0002c760e71549400051fc32e2a928000a3c865c55250001878ec38aa4a00034d5c471549401b59d400e2a928000b39801c5525000137301bb264a00024fe15764c9400bc9e42aec9928000c9c635d9325000136f02bb264a01be6d205764c940004ddc02ec99280008bf865d532500011790cbaa64a005667a1f634c9400064fbb6c6992801793e85dc5325000127b0bb8a64a000267e0d75d85400b4ce41aebb0a806f8bd8719761500df56d0232ec2a01be2f61f63d85400051e42ac7b0a8016c9c7358f61500df17b0fb16c2a01beada0762d85400064eb9cc730a8000c9f7318e615000153d07314c2a01234e5c352985402369cb82a530a80c5db170d86615002f27d0fbaac2a00024f60b75585400061fb06eab0a8000d3b60dd5615000187eeb32ac2a0003271ce655854000656394cab0a8000c3f751956150001938e632ac2a00032b1c865585400b4cf43ee6b0a8000d1f75dcd6150001a38ebb9ac2a000327d837358540006cdb06e6b0a8000c9f761cd6150001a3eea39ac2a0003471d473585400045f43ec6b0a8016c9c73d8d6150001958e5b1ac2a01be2f21d63585400051e42ac6b0a8016c9c7358d6150001958e4b1ac2a00566ba1f725854000697baee4b0a8000d2c75dc96150001b1ee7b92c2a0003631cf725854000697c2ee4b0a8000d2c85dc9615000195ec1b92c2a00036ad83725854000657bb0e4b0a8000d2f751c96150001a58ea392c2a000363dcc7258540006c6398e4b0a80008be87d896150001938e7b12c2a00572b1cb625854037c5e43ac4b0a8000c9c73589615002b958e4b12c2a01bead20562585400049f43ea4b0a801793c87d496150001a3ee7a92c2a01e3471cf525854000697b96a4b0a8015d2c72d4961500aba76e1a92c2a00024fa1d52585400049e43aa4b0a8000d1f7354961500efa38e6a92c2a00034bdc952585400ae96392a4b0a8054d3b7054961500033750fb82c2a00034edd770585400069c3aee0b0a8000d9b73dc16150001b30e7b82c2a00036adcb7058540006d4396e0b0a80c4db371dc161500df93ec2b98c2a01bf2758573185405ee4fb02e630a8000d9b605cc61500dfb2e20b98c2a00036544173185400045ec3cc630a8000c9d7398c615000193ae6318c2a
  | 7 => 0x2d40d8952540890fd0db8aa4a81171d18771549500153d436e0a92a000e6b62dc152540030f90cbaa64a80029d61421d855000578c0043b0aa0008f787584615409b4ef0ab08c2a80e61f21f625455000c3e432eb18aa0048be849d9315400117b093b262a80061f219754c5500064e3a6c698aa04d87f855da21540030f90cbac42a80122fa1276485500045ec24ec90aa00187c865d5215400147b0d29ecaa0003475ce53d95400be1fbb6cab2a801699e87dcd6550001a3ea5b9acaa000327d837359540006cdb06e6b2a8000c9f761cd6550001a3eea39acaa033b4edd77059540006cdb9ee0b2a8000d9873dc1655000153b0da9ec6a0003475d753d8d400b54f41cc5b1a80168bd8718b635000127f0ab8ec6a005e4f21571d8d400bc9f43eeab1a8000e1c63dd5635000127b05baac6a00030fd837558d400069db06eab1a8000c3f761d56350001c38c63aac6a005aa7a1b6358d400068e3aec6b1a8000c9c63dc96350001878eb312c6a005aa7a0e6258d400061e3a8c4b1a8000d3b75dc16350001a70ebb82c6a033766dcf7058d406674c31ee0b1a80009b980dd9535000187ea5bb2a6a00032e6037654d400045f434eca9a800093f855d9535000133f06bb2a6a00026ee017654d400064fa98eca9a8000c3e531d95350001878a63b2a6a00032714c7654d400061fa90eca9a8000c3c511d9535000917f003b2a6a00122f6007654d400061fa80eca9a8000c3d501d9535000193e603b2a6a0003274c07654d400049fc2ae7b12801793c855cf625000117b0f31ec4a00562f61c63d89400064eb98c7b12800093f855c7625002f2790ab8ec4a000327dce63589400045f438c6b1280cbdab72dc1625000127f0eb1ea4a005e4f21d63d49406570e31ac7a9280c9b3b8058f525000137301bb2a4a00030fa1776549400061ec2eeca928000cb980dd9525000117d0d3b2a4a000267e0d76549400b4ce41aeca9280009b7815d952500df36902bb2a4a00026ee0176549400061f428eca928000c3d851d9525000187ca63b2a4a00030f14c76549400061e288eca9280048bf801d9525000917b003b2a4a00030fd4076549400061ea80eca928000caf201d9525000195a403b2a4a00564fa1f65549400061fbb6caa92801593c875955250001878ecb2aa4a0002c7e0d65549403bd8e41acaa9280c8b3b80595525002b27b0bb9aa4a01df4794f73549400ac9e43aa6a928000a3f8654d52500014790ca9aa4a005b471cd53549400059cc06eca928000c3f72dd95250001c5ee5bb2a4a00028f60376549400071cc06eca928000e2f20dd9525000147d0d3b2a4a00030fdda765494000596c14eca928000b1f835d952500ef63906bb2a4a0002cbe0976549400059bc0aeca928000b34815d9525000167700bb2a4a00030f5d876549400
  | 8 => 0x81baac1108029b60875582210043fc2ae8b04420587c855d160884011bf06ba2c11080e3720d745822101c6f41ee9b2a42008dd83dd3654840917d0fba2ca908030fd4b74595210061ea96e8b2a42008bd80dd1654840117d0e3a2ca908022fa1f40595210245e43e80b2a42008bd87997644840153d0732ec890802a760e65d91210045fc3acbb224200a3e8598f644840147b0b31ec8908762f61c60d91210051f428c1b224200a3d85183644840153d06306c890802a760c60d91210065cb80c1b224200a9e83dd7644840153b07baec8908030f5d475d91210051f42ee7b224200a3d85dcf644840193ee739ec89080387d4e53d91210051f42e63b224200a3d85cc7644840187ea4b86c8908030f54970d91210051f428e1b224200a3d851c3644840153d06386c890802a760c70d91214a557410e1b224293aad821c3644852756d02386c890a52ad60470d91210045f43ca1b2242008bd87943644840117d0e286c8908022f61c50d91210054f418a1b224200a9d83143644852955d04286c890802ab60850d912149d5b408a1b224200ab581143644840117d0f186c8908022f61e30d91210045f43861b2242008bd870c3644840147d0a186c8908028f61430d91214a55741061b224200aad820c3644852756d02186c890802ad60430d91214a45f43c21b2242008bd87843644840b0fd0bba6c6908021f61774d8d210045f43ec8b1a42008be87191634840917d0fba2c6908030fd4b7458d210061ea96e8b1a42008bd80dd1634840117d0e3a2c6908022fa1f4058d210245e43e80b1a42048be84dd9534840117b09bb2a6908122fa127654d210045ec24eca9a42008bf845d9534840917908bb2a6908023ee017654d2100c7c402eca9a42048bc841d953484070fd0fb2aa6908022fa1b7454d210045f43ec8a9a42008bc87d91534840b1bd0fb1aa690a562fa1b744c5214f45f43ec898a42948bc87d91314840117f08baec0908122f21175d81210055cc06e9b024200ab9801d3604840117f08b9ec0908122f21173d81210245f436e8b0242938bc86dd1604840117d0fb22c0908030fdd764581210061e3aec8b024200c9c73d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c9c73191604840193ec9b9ac0908032719373581210045fc22e5b1aa0048bc845cb63540014bb0b196c6a8002a7a1232d8d5001c3e42ae3b1aa0b6c3c76dd153540890fd0db8aa6a800a1f21574d89500046fc1ae9b12a0038dc835d362540050f90ab9ec4a80022fe1173d89500245e422e7b12a03987c8754f62540050f90ab8ec4a81371dd9471589505861e3b6e8a92a037c5c63dcd52540054d90fb12a4a80038bdd36254950007163a6c4a92a005a6f80d89525400b4db01b12a4a833f9a1c3625495067f17a06c4a92a0cfe
  | 9 => 0x50d91310045ec38a1b22629da9e83143644c40153b06286c898802aba0850d913100556c10a1b22629cab681143644c40156b02286c8988028fa1720d91310051ec2e41b2262008be87883644c40117b0f106c8988022fa1c20d91310045ec3841b226200a3e85083644c40147b0a106c898a76a7a0c20d91310054ec1841b22629cab681083644c40156b02106c898a762fa1e10d91310045ec3c21b22629ec9c73193624c4010ff0ab86c4988161f21570d89310045f43ec8b1262008be87191624c47747d0db26a498b4b0f5cb64d49310051ec06c9a9262048be84dd9524c40117b09bb2a4988122fa1276549310045ec24eca9262048bc841d9524c4050fd0fb2aa4989169760f65549310143e43acaa926200a3f84595524c47147908b2aa49880a9b20965549312b63a38acaa9262008be86dd1524c40117d0fb22a4988022f21f64549310062fb2ee6a9262058ee87d89524c4071ed0db8aa4988e28fa1376549310051ec26eca926238a3e849d9524c40147b093b2a4988029b60a76549310051fc22eca926238a3c845d9524c4014df04bb2a4988029ee0176549311b53c402eca926238a3c841d9524c40147d0dba2a498ac38b18b74549311c51f436c8a926200e2c62d91524c40147d0fb22a4988028f21f645493168e1fb96c8a926200e2f72d91524c40147b01b22a4988038bc83645493122d2f436e6a926200c5e76dcd524c4054dd0db12a4988038bd93625493100716326c4a926205a6e87d89524c40b4d90fb12a4988038bdd36254931007163a6c4a926200e4f73d89524c5a1c98e7b12a4988029b603625493100717a06c4a9262d0e4f30d89524c46f4ed0db8aa49880399d8b71549310063abb0e2a926200d57731c5524c401ccec438aa498a7aa7a1b644c9314e64e3b6c89926200e8c62d91324c539b28e3b22649880ab3a1b624c93100746326c499262069d687dc5324c4018becbb9aa2988022fe1175d81310245e422ebb026200ab980dd3604c401573003a6c0988022fe1172d81310245e422e5b02623bc3c74d4b604c471878e8a96c09880b1b1c952d81311a64e3a265b026202ccc724cb604c40917d0dba2c098a722f21b74581310045f43ec8b026200c3f75d91604c401878ebb22c0988032b1cb64581310045f438c8b026200c3f75191604c401878ea322c0988032b1c8645813100657b26e4b026200cac64dc9604c40917d0fba2c7108030fd4b7458e210061ea96e8b1c42008bd80dd1638853917d0e3a2c71081a37a1f5358e210062fbaea6b1c4200acd82d4d638840d1b90ea1ac7108022fa1f4058e210245e43e80b1c420387d85dd9538840117f08bb2a7108122f2117654e210245f426eab0442008bd84dd5608840b0fd0fbaac1108030fa1375582210061ec26eab044200c3f40dd5608840187a
  | 10 => 0xa94a2a8e2f72591529440147f00b22a5288038bc816454a511be2f31ee6a94a200e1f7458d5294401c38e8b1aa52891f17dc96354a5113727b92c6a94a245e547158d5294401c3e80b1aa52880393c816354a5122f2b882c6a94a200e2f745895294401c58e8b12a528917991c56254a5100537c02c4a94a200e2f40589529448bcce20b12a5288034ddd37154a510072ab1ee2a94a200e6562dc5529446f8bcc6baa652881a3721d634ca5101566412c6994a26fab9809d1609457b57700ba2c1288122fa1373582510045ec26e6b04a203c5e7354d609440917d09b92c1288022f61372582511c61f3a2a4b04a2008bf845cb635440917908b96c6a88022fe1173d89510245e422e7b12a20287c855c36254473878eba06c4a8ac30f1db745495152e3a38ec6a92a200e2f74d895254401c58e9b12a4a88029b603625495100717a06c4a92a20697687dc55254401ccec5b8aa4a89171d5d871549510069bba0e2a92a200d34741c55254401ccec438aa4a892e1fa1b70549510043ec2eec992a2008bf845cf605440917908b9ec0a88022fe1172d81510245e422e5b02a20687e87951658c40187ee92a2cb188161fa177458a310043ec2ee8b1462048be87dd1628c40187d0bba2c5188030f6177458a310064f41ee8b146200c9d83dd1628c40187ea5ba2c5188030f54b7458a3149e4f98ee8b146293c9d31dd1628c40117b01ba2c518a4e2fa1c7458a310045f43e80b1462048bc87d01628c4050fb0bbb2a5188022fe117654a310245e422eca9462068f4815d9528c40d0f90eb2aa5188030f1d16554a310363a38acaa946200c3c74dd9528c40147f08bb2a5188e28f2117654a310061e3a2eca946200a6f825d9528c48b4e902bb2a5189171d1c57654a310245f426eab0462008bd84dd5608c5a993ae6326ca9880387d4c64d95310346ec1ee9b2a6200a5d83943654c5a7c3ea7a06ca988122fa1f74595310061fa96e8b2a62008bd80dd1654c40117d0e3a2ca988022fa1f40595310245e43e80b2a62008bd87997644c40155d0532ec898802ab60a65d91310045fc3acbb22629ca9e86d4f644c401c3ecba9ec8988028fa1662d91310051ec2cc5b226200a3e8518b644c40147b0a316c8988962f61c60d91310051f428c1b226200a3d85183644c40155d04306c898802ab60860d91310065cb80c1b22629da9e83dd7644c53953b07baec8988030f5d475d91310051f42ce5b226200a3d859cb644c40147d0a396c8988028f61472d91314ed4f418e5b22629ca9d831cb644c539c6ca3a8ec8988028fa1721d91310051ec2e43b226200a3e851c3644c40147b0a386c898a76a7a0c70d91314e54ec18e1b226200aae821c3644c40155b04386c898a72ada0470d91314ed5ac08e1b2262008be87943644c40117b0f286c8988022fa1c
  | 11 => 0x4c80187f08baec2990030f21175d85320062fc1aebb0a6400c5c835d7614c86f0fb04baec29900317cc175d853200637902ebb0a640587e85dd3614c8010fb0bba6c29900a3760f74d853201c76c16e9b0a64d6c3e75d03614c80187aeba06c2990023de1d61185320045fc22ebb0264048bc845d7604c8051bb07ba6c0990022fe1171d81320245e422e3b0264a8a3e859cd649440147b0b39ac928802aba0a735925100556c14e6b24a2a8a3e859c9649440147b0b392c928802a7a0e72592510054ec1ce4b24a232a3e851c9649440147b0a392c9288022fa1f32592510045ec3e64b24a2008be878c9649440117b0f192c928aa28fa1632592510051ec2c64b24a2a8a3e850c9649440147b0a192c9288030fd4b70592510355b40ce0b24a2d5ab5819c1649440147f0ab82c928aa28f21570592510045f43c60b24a2008bd878c1649440117d0e182c9288022f61c30592515451f42860b24a200a3d850c1649440155d04182c928802ab60830592510355b40860b24a200ab5810c1649455147d0b902c9288028f61720592510045f43c40b24a2008bd87881649440117d0e102c9288022f61c20592515451f42840b24a200a3d85081649440153d06102c928802a760c20592510355b40840b24a200ab581081649440d1b90ea1ac7288122fa137258e510045ec26e4b1ca200a5d858c9639440153d09192c728802a76123258e510054f42460b1ca200a9d848c1639440d5ad03182c728802a7a137258e510054ec26e4b1ca226a5e859c963944014bb0b392c728802a7a127258e510054ec24e4b1ca231a5e851c963944014bb0a392c728803335c87258e510046f43c84b1ca2008dd87909639444d4bd0b212c728802976164258e511352f42884b1ca200a5d85109639440153d09382c728802a76127058e510356b40ce0b1ca200ad5819c163944014bf0ab82c7288c697a147058e510052ec28e0b1ca200a9e841c1639440153b08382c728802b3a087058e5100566c10e0b1ca206ad6811c163944635ab02382c728b4f87d4b4058e515ef4b88680b1ca206ad68190163944015ab03202c72881ab5a044058e510056ac0880b1ca226a5e85c8163944014bb0b902c728802a7a122058e510054ec2440b1ca206ad68188163944015ab03102c72880237a1c2058e510046ec3840b1ca226a5e8508163944014bb0a102c728802a7a102058e510054ec2040b1ca206ad68108163944015ab02102c728adb0fddb7454e515b70f31ee8a9ca23ac5e63dc95394401a6ee9b8aa728a9355dcf7154e5123d37c12eab14a2038de83dd162944011bb07ba2c5288122fa137358a510045ec26e6b14a23a87f8754d62944014db05282c5288028f61b7454a515861fbb6e8a94a200e1e63dd1529456147d0eb22a528aca8f21d6454a5123e1fb92c8
  | 12 => 0x24f603745855200697906e8b0aa40096f825d1615480127d0fb22c2a90024fa1c645855200697ba6e4b0aa400d2c74dc961548052d905b82c2a90024fa1f40585521c49e43e80b0aa4da96f825d061548052d904ba0c2a90024fe1173185521c49e422e630aa4b596f825cc615486f0fb0fb18c2a90df179cf63185520053ac0ec630aa400977875846154801c6ec8b08c2a90038d191611855222d3bc3ac230aa400c77875846154801c6f08b08c2a90038d21161185520053bc1ac230aa447a77825846154801ccf04b08c2a90029d20161185526df33902c230aa400c75615c061548014bb06300c2a90029d60460185520051f4368030aa400e3561d0061548014ef0d080c2a9002d960a101855200697b96e9b02a4da96f825d360548052d904ba6c0a90028fa1874d815200697b90e9b02a4d9d2c721d3605480167301b26c0a90038e98364d81526c697b90c9b02a4b2d2c72193605480167300326c0a90024fe1173d81521c49e422e7b02a4b596f825cf60548052d904b9ec0a90da1f61f63d81521be2f39ec7b02a437c5c7358f605480127f08b8ec0a90e24f21171d8152114b7c12e3b02a40296c825c7605486d0fb0fb0ec0a91171d9c761d81520043fc3ac3b02a43893e87dd1605496527d0dba2c0a92c24f21b745815200697b16e8b02a400d2f20dd160548012bf06ba2c0a90de5720d7458152004b7c12e8b02a400977815d1605488b2e902ba2c0a90024fa1f64581520068e39ec8b02a40093e871916054801a38e6322c0a90de57a1f73581520068fba6e6b02a400d1c74dcd6054801a3ec9b9ac0a9003471937358152006a7b16e6b02a400d1f40dcd6054801a3a81b9ac0a900353c8373581520068fba0e6b02a400d1c741cd605486f8b8e7b1ac0a90da1f21d63581521be2e39ac6b02a400d2f74dc96054801a58e9b92c0a900353dcf7258152006a639ee4b02a44597687dc56054801a6ee9b8ac0a90034d1d37158152006abb9ee2b02a400d5473dc56054801acee5b8ac0a90034dd9371581520069a326e2b02a400d6762dc56054801a6e81b8ac0a90034d5037158152006b3906e2b02a400d37741c56054801a68e838ac0a900355dcc7158152006aa398e2b02a400d67721c5605488b8eb0c38ac0a90034dd9071581520069a320e2b02a400c77631c560548018eac638ac0a911f1dd887158152006b3b10e2b02a400c76601c560548018e8c038ac0a90034dd0071581520069aa00e2b02a400d67201c560548010fd0fb0ac0a91171d1c761581521b43e43ac2b02a445c747158560548051bb07ba6ca990122fa1f74595320061fa96e8b2a6400c3d52dd1654c80117b01ba2ca990022fa1c74595326be2fbaee6b2a64008be87d01654c8091790fa02ca990022fe1175d85320245e422ebb0a640587f875d761
  | 13 => 0x65a326e2b02a400cb7641c56054801968c838ac0a90028fa1b73d91520068fb9ce7b22a400b2f825cf645496165904b9ec8a90028fa1873d915258597410e7b22a4b1b2d821cf645480165b0531ec8a9002cda0663d91520059ac0cc7b22a400a3e86dc7645480163d07b8ec8a9002c760f71d915258597416e3b22a4b1b2d82dc7645480163d0738ec8a9002c760e71d915258597414e3b22a400b2d829c7645480147d0c38ec8a90028fa1b31d91520051ec3663b22a40093e870c7645480127b0e18ec8a92c2cba0831d915200596c1063b22a400a3e86dc3645496165d05386c8a9002cb60a70d91520061fb12e1b22a400d2f625c36454801a5e40b86c8a90028fa1870d91520058f418e1b22a400b1d831c3645496165d04386c8a92c6cb60870d91520059b408e1b22a400b35811c3645480165b05306c8a90e24f61c60d91520058f418c1b22a400b1d83183645480166d02306c8a9002cd60460d91520069cb80c1b22a40093e878c3645480127b0f186c8a92c2cba0a30d915200596c1461b22a40093e870c3645480127b0e186c8a90028fa1830d91520051ec3061b22a4b0b2e820c3645480165b04186c8a9002cda0430d91520059ac0861b22a40093e87843645480127b0f086c8a92c2cba0a10d915200596c1421b22a40093e87043645480127b0e086c8a90028fa1810d91520051ec3021b22a400b1e83043645480163b06086c8a92c2cba0810d915200596c1021b22a4da96f825d363548052d904ba6c6a90038798f64d8d520070f318c9b1aa4dce1e63d0363548014bb0d186c6a9002d360a30d8d521c49f43ee8b1aa400e1c63dd16354801a5ec5ba2c6a90024f6037458d5200697906e8b1aa40096f825d16354801c38c63a2c6a90024fa1f6458d520070e31ec8b1aa40093e871916354801c38c6322c6a90de97a1b6358d521be2fbb6c6b1aa400d2f74dc96354801a58e9b92c6a93779318f7258d5200697b26e4b1aa400d2c64dc96354801a9ec7b92c6a93775318f7258d52004b6c06e4b1aa4ddd4f30dc9635480127d0fa02c6a90e24f21f4058d526e70e31e80b1aa400d2f72d01635486f2bd07ba6c2a90025760f74d855202cb6c16e9b0aa400b658284361548014eb0c086c2a9002d560c10d8552005b2c1021b0aa447c3f625d26154801a5ec4ba4c2a90024fe01749855200697902e930aa400d1e73d926154801a3ce6324c2a900347d9173985520068e322e730aa447c5f625ce6154801a9ec4b9cc2a9117551857398552006a7902e730aa445d57105ce615486f8bce7b1cc2a90df179cd63985520071bb26c330aa400d5573d8661548014bb06304c2a90029d60460985521c49fc3e8130aa40093d87d02615480147d0da04c2a9373479cf40985520068eb9e8130aa43893e87dd16154801a5ec5ba2c2a9
  | 14 => 0xc845c76054c0917d0dba2c0a9ada2f21b74581530045f43ec8b02a6008be871916054dc187eea322c0a9b7f27dcc64581530055b40cc7b22a400ab58198f645487117b0e306c8a9002a7a0c60d91520054ec18c1b22a400ab681183645480156b02306c8a90032e5c060d91525849f43ca1b22a40093d87943645496165d05286c8a92c68fa1773d91525851ec2ee7b22a400c9f739cf645496347d0a39ec8a92c28f61473d915258557410e7b22a4b1aad821cf645496347d0bb8ec8a92c28f61771d91520054f41ee3b22a400a9d83dc7645496155d05b8ec8a92c6ab60b71d91520054f41ce3b22a400a9d839c7645496347d0a38ec8a92c28f61471d915258d1f42e63b22a400a3d85cc7645480117d0e18ec8a90022f61c31d915258d1f42ee1b22a4b0a3d85dc3645480187aebb86c8a90030f5d570d915258d1f428e1b22a4b0a3d851c3645480153d06386c8a9002a760c70d915258557410e1b22a4b1aad821c3645480156d02386c8a9002ad60470d91520045f43c61b22a4008bd878c3645480117d0e186c8a90022f61c30d915258d1f42861b22a400a3d850c3645496155d04186c8a9002ab60830d91520055b40861b22a400ab5810c3645480117d0f086c8a90022f61e10d91520045f43821b22a4008bd87043645496347d0a086c8a90028f61410d91520054f41821b22a400a9d83043645496155d04086c8a9002ab60810d91525861ebaec9b1aa400e1e53d93635496587aea326c6a90038794c64d8d520143ec2ee9b1aa4bfc3d75d0363549b9c3ca7a06c6a90029761630d8d520045f43ec8b1aa4008be87191635487127d0fba2a6a92db0f1db7454d525b70e31ee8a9aa400d2c72dd1535496527d0dba2a6a92df0fd8b7454d525be97b16e8a9aa40093d80dd15354801a5e41ba2a6a937a4fa1f6454d525849e43ec8a9aa4b0c3c76d915354801c38c7b22a6a900e97a1b6354d5200697ba6e4a9aa400d2c74dc9535487127909b82a6a92cb0f5d464d85520143ec2ee9b0aa4038de83dd361548011bb07ba6c2a90163b60b74d85525fe1ebae81b0aa400a758504361548015ab06086c2a9002b960810d85520064f39ec930aa400c9e73192615480193ec8b9cc2a90032719173985520366a30ae730aa400cd573d86615480117d0fb22c2a90022fa1c64585525961eba8c830aa4008f787584615496187aebb26c0a90038e94364d81525961eba8c9b02a40287d85dd3605480187aebba6c0a9002ae60374d81520061eba8e9b02a400ab9801d3605480117f08b9ec0a90122f21173d815201e2e39aa7b02a4008bf845c7605480917908b8ec0a90122fa1b74581525845e436e8b02a4008be87d916054801938e7b22c0a90022fa1c64581520064e398c8b02a400c9f64dcd6054801938c9b9ac0a90032dd93715815200
  | 15 => 0xc00800200000401000000e01c00400400600600a02600000000200200000000e00000000000400e00200000202a00800400a00200800200200000600000000000000000400e00200000000200000000000800000000000800400400000400000000200c00e00000000200000e02200201000400000200200a00200201400401800000200600c00400200000201200001400000600200000200200a00000000000200001000800400c00000400603000800000200801600600000000000200000000000602400000000000400000800400800000800000001000200000200000e00200000200200200800800200600000400400600400001200c00200200c00600600c00400000200400000200e00400400000400000001800000000200201400600600000200400000001e00000000200800800400600200200e00600800200801200000a00002200400001a00400000202600000001000000400400000401600000001200001600600200000201600e00000200400000001000601e00e01200000e00e002000014006000002000000002e5a3d8598b6454c7d17b0e306c8a9802aba0860d915300556c10c1b22a600ab6811836454c0156b02306c8a98032e5c060d91531f51f42ce5b22a6e5a3d859cb6454d6f47d0a396c8a9ada8f61472d91535b54f418e5b22a6b7a9d831cb6454d6f47d0bb8ec8a9ada8f61771d91535b54f41ee3b22a6b7a9d83dc76454c0155d05b8ec8a9802ab60b71d91535b54f41ce3b22a6e4a9d839c76454d6f47d0b90ec8a98028f61721d91530045f43843b22a6008bd870876454d6f47d0a10ec8a98028f61421d91535b54f41843b22a600a9d830876454c015750010ec8a9802ae60021d91530061fa92e1b22a6b7a3e851c36454d6d47b0a386c8a9adaa7a0c70d91535bd4ec18e1b22a600aae821c36454c0155b04386c8a9802ada0470d91530055ac08e1b22a6b7a3e85c836454c0147b0b906c8a98022fa1e20d91530045ec3c41b22a6008be870836454c0117b0e106c8a9ade8fa1420d91530051ec2841b22a6b6a9e830836454c0153b06106c8a9802ada0420d91530055ac0841b22a6008be878436454c0117b0f086c8a98022fa1c10d91530045ec3821b22a6b7a3e850436454c0147b0a086c8a9adaa7a0c10d91530054ec1821b22a600aae820436454c0155b04086c8a98ef0f1d464d89530063a28ae3b12a6008be87d916254c0117d0e322c4a9ae30f5d464d855301c3ec2ee9b0aa6058dd83dd36154c051dd05ba6c2a98023b60b74d85536061ebae81b0aa6e4c9d73d926154dc787aea324c2a9b8b275cc649855370e6ab9ec330aa6008be87d916154c0117d0e322c2a98023de1d61185530055cc06e9b02a600ab9801d36054c0117f08b96c0a98122f21172d81530045fc22e3b02a6048b
  | 16 => 0x35200004240002e2101002c86505f00000ec55e2da9f380006e807b19480f416b433800000044b0001560000792185933c0003ee0001ba80005fc16a9cd80002f200017c40003d43810374e420ad21f80003040001160000cda56929815e8aee0001f48c2400061f000097000056100018880000000001fe84be36604280347b006800000001a000000006347d84b32028000000093000034c92c3373288124000297000000017600037080001e00000e7800000000041898000004e4190863908a5041f900010926260bf8bf0a1400000000000000000e805408ee0b30b780008e400006a9f90f686bb1e8800085e0000001e08000445252806058200000004300000000f818dc5f46f70008b40a9e6bf2bb1934bf61a810580b010887111a048848243210e960c3d80cc24108d87404fe00005b00520002e3000000005100003f4eba07e0001cd050a47e37a94580821131b096a000600c00000000200600000600001000200000a04400000600401600201a00000a00a00c00200800400000000400000000c00000200000000601800600000000000000201400200400200600400000400000002000a01000401000600000000000000000200000000200800601000200000000000400000600000400400a00000200200001400001400600200000000a00201801401801001000200c00001000000200002e00800000a00e00000200200a00a00000000a00200000000400000e01600400601000401000800400000000a01600200000000400400a00400400000800200a00002e00001400400a00002e00000e00a00400200000c00200000800000200200001400c02200000201600400600001c00000000200001600200001400000600c00000600801002000000000000000400000200202a01600200000000a00800400000000c00000e00200400000c00000200200000200c00400000000000200400000600000201200600000000c00600400000200000201401e00400000200200601400200000400000400e01a00000200e00600000000000400e00400000000600200a00200200400a00000400000000600200000200000000400001800e00200200200800600200800400000201200601400400601e00800200200000c01000600400400000200000000601800c00200800000c00000200800000200600c00000601400000801a00001600200e00000000600000801600000400600400200c00200200a00000200e00000000001000200400400000200200600001200000600200c00600000000000000e00000600000a00001400000000600200000801200200200000000000800000800200400400000200000000000400000e00000200c00a00200400e00600c00000200800a00000600400200201400000200e00201c00000001000
  | 17 => 0xb1da0d1c7871dc04c05e80f930100004b21292ae870409e56c00000000007cd25a8000e0e4a0000080800051b1ef800000046e17da018eee0000a200003b200000000000006e23af967c1b2000000000028c00000000000005d7000075c7e80003e51b080004fa0001a50d9a0140001d280004150558000000000000000000049a00017ac76e2ca00000009a44460001e9c32e59c0001d686900d600000000007512d20000b2400026d02f4000000000000084a66701283488be2c52a71ff4d800671422144a30661000000036800028e00002f0345000170c0000003bc80000000001750678d6436225d80002084e50c300003f823e4150000000000339000000084f0aa8d000a41f600019f80000000000000000000000036800000023d950800000000000007f000039198f50842c43df83b800007222f00f40000002f48000bfc0003d887fc0004f800000000001c53618000b72000000000090863f00004290966823a11fb875e0000000e50000000000217800003600006c890c00012180000004ce0000001088000130895000000000006700006741d1800000000000013883cc111394074c3ce4b808a8a907080000000000b1e6460a5832cfa200023c910005c4eb0ec0514e0601e03011045c680800000008d47b6000030c0002ba22900005ee00000000000000630000000d8e67500000000000000ef8000000000146a0fc15e00000018a44d472c0000000000000000000000018900000007fc55a0000f2811806d0e1000095e86815e83210987a8000000022830a2879b6800013d3c280bc0007fb0000000000834106800000073841211709d40100f898b800000000000000008130000000bba3070668fdc8e61c91d88eeccec0000000c6c27600000010345786ac245000025600000000001ca4ad00000008886700001e204c60000000000000000000000000000033b8000ddc56510087bccde3e200000000000003f412f400000033480008ae2470000f34000000419800000084e000000000000000412dc1347ae18a914007800020400000004553398000000000122000000000000000000000002a080009504140000d5c000251051800095682c3f50da47900000b900980003ae00017200000003bf0dc8a780c428300000002a926c8a00cb042c3931becf2e5e80b4901800000011306f847638d1c0001000000000000000000000000000ac85f51fa91e861e1611c79ccc00000000000010907d304491d4ba443c240861c00046333c800087c5b33bb0424a6252e19a8d280003d212b8000fd24fb39d000088400022d000000070038d0640e122de292a14c0000003218e2856e6502429544a9486037c82049be0e32311ea859600008d96ec1ae765000000000000000000000000000a780003d00003068524f341d6000000000
  | 18 => 0x224a31ba000000000025a0c7c4ee00016915ccb145d6000215cbbc86640e800044a09c00021880007b512914e00006810001f806a2233201000000053701593cc3083a7302086800053b3c51c4865c00031b02280000470d3828800000032b80002340f2303971cd323031f98ec8e600000001fdc0007f034380008d600000000010025e300000000001410001f640000d10a700009060001760878356000119102447a000000000000001d2c9866c00023c00013280000790001fd89cc8324068000dde3c61229d849a07042438000c2e00019c800000000000020ec0001cc1fd000000025b0000000fb00343f680000000003540b8000014d000000000000000000000000003888000c8484000000000000000000244e3a7ff0000a6c0000003690304ee40502b68000d9c21711c9ec81f60703a69b2000000004100000001021c280009003d93dd000000000010396780000000b11ec07881f90001a207fa43a2369a940002e41d6860063a6e333892b8f2c2b11409b7507072b0a89bf85845e500000004ba000000205500a0a800000006700002468000000000000000000033c0ad1e1011a539000083c7aa000000000000066e0000000000000359914400075800000000000001ef00006684b00001e3c77a00037f8000c283411461ba40001bb1dd070c66461815f000000079c0001704e9005c0000000afe7a029390c400030c00012e400000000000000ba7c700000000004a10001dd4f0c6eb00003d40000000000f2ce287de3f296acc5446010e0c9cd8a000000148400076c17c09d407c13800005781f800013205a00000832c40000000165000127854e64100012c4ec6000000021c00035308c0ac83720000001a5c35c2b52ed95800000002b798406a82e609085e8ad662708f1a88e785ce00000006fe0000000440e4042b000000000017b0001090c5e4c321980000001951be0e1809a219261000000000017f000000000000000001d0000000068858c000000000000025306280003a81540000c702ae30240921a8f3a3963b703b48760cf3a2949039a00000010b806250700000000000002db1c3c81e5080fc15c49924690000a643c45cb33100007ae65c30d8b70dae29810b07807204c439f9bb000000009884f80b43230001ee4a3c0000000000c1200030f00000008210001d8800073b0001ab80004d32dc000000006f4380000e0209e2498828d702731cb8000b7a0000001554634000080a11c462000000000000010720b800089800000000000007bd1a787380000000000000e2c5200001ad000072f14a9b580000a600504bd06a5c900000000007901bc1c207360b12ed0e9800044e40180001600000c880000003db24d90a90dc68a0000000000000000000000000016d86f0d6e45900009f4e980000000238d3812629
  | 19 => 0x2b0130c904ed24a9b6cffc55731820400000a40f59ea4f3c0001fb1c5cc5600000000002506dc000000000000000000007ba0003c02094e1a000350000021c0000000d2c00007d019163886e62d26d8d30194000170907000000000015300c400000017a84f000000a8000000000000000080000000000000000000000c448ca29e3769e3800033b00000000000000dc1464a80000000138000005b15080008702930e884e505e000000000055c00006382741782f9000139c00000000000000000000db1b640000002b39a441f401f0018da8cca00000000000000000002098bcc3730001f8ce6220c0000000daa0000001a48baa0000000c6000010b00000000000003db800000027243583fc0000001ee123000041f00000006562cd2ab00004b44d700000009fa0000000000b0e0ac3c580000000003e3000000076a08f90780000003ab80000000000000ce87846bc19f80001306310000f1c00000015c1df000037b055000041c7411981d9012c3260000000e86223000000046a5e220e800000048938989a4000000000000000000000003e000000028189f098a1712bd9b98000000126800000000002121503b60001598000e3c00015807100000c0238801c00048e00000009e22ef0001890d2a3a90001534c780000b50294bde7d43418f683140000001098d0a00002711bc7e2000000000073200000001fcd3a35502b0000000447430a1b03fa51136f10a4f8604b16486bccc02150be13310ea00028716443e85233e0945026465d1ad00003b40002538d8094c70c00011f06b61633d786d4ae80003950c3831800024f8de46887ec1ba93500000003d588fc6246960001fe016a67b000049c0227551f5800039000032a066428449734d1e6106e0db00000000000003621ac00003cf0c1800042810000000004203b319889d0e146d30001730af074e0308000eda7f400000807c284323089b904626811786c456860b40f084c22c3ef0f2880c43654831c0000a74000000000107a0001518bf40003ed000000099600000000010c83522330614bce00012a9cd433e000000000043e7bc11094b06547a60168000d30783000000070205f00000009442f000015490ac3e00a519f4512363053800033a3f91048038a968020000bfc82058c09e15c84fe00000000000001c00351dec2ba00015f8e54d1a200353203051e3a1405956408c756301a16ce6e5340320650be472215780000001fa2520000000021000000016482700013c06de8300001a2cef46ad000184c0001dd0000000844000000000013680401412484d60000f70d6000016413f03904cc81900002e057200017297280004aa3bf80009de31329f8e440006640000194bb87100710ed0bda24a3971ad50824f53c09bd010c03b08288ac8721ad1d590c00006c900000010
  | 20 => 0xff253300003f87ce8162d196883e47da00000008fa0192b31a7800a6210001d3c0160000000c50a4450c3b99848b587d60df93dc4900000759bc40006c120c8000bc275b033000000000015300000005f700000005807541c90df40008222a280009f202727f8338bd800020b0ddcff803002000007545002340000000023000000000016e3f78e7c68e0352868000faa00000009081cc51500000000000170000000fe600004780000000f10000e3000065f29a8114c2a1600890000fbe000145800000044a0000c9400000019400007d40000000000b004d800000000000003738eb02064b632b15d400000030d000081c0b700000004602aa000154cc3a76f00015187f624b1af9d101bc77414e000000025e16180000d200019f050000079f2ef8000e4e0002db965831e4dd22d9060d5665a04900005100000000000a8616d2018728ac40001a80a440004120001d9c0000000ef06580006cb3e582e420c00000000e8de005925f839d0560000d50000d202e72c4842000036d0000000d5e00000000000005471711bf07d00002c218e450673932d95f037434903d9d24ea07a516c96e8f482ed3b801e08c8554166126443005e289020092841b00016a46b800041f094070e00000014400000000001e4c98e00028580002a61a428d0000ccc6280000254e3237a1bb1a8c2462060960ab03d40dc00017503420000000598d7c0002950000b400544250d090144c0000117400066a00019aca7a246190007057600018f0a410b40001c700010d2000000000000017324c00004d827a16a00000000000a180000000000f4973c2f200007980010e62f12101bcc000301000082052c0000000d580440000fb80080006860000000ed26e53d1000000064900000000000c62f805f464400000000001d40770000b207c80001ac9be00543642849694fd64d53318bb8e0c85516e908400007404806b0f580e040d00000f849014e944c0000003c681b00008170001e6400033d42c140874a4e80000000efa60804580000005c03eb98f82b65502298000cfe1bd2478470bf00990f081543ea64016c00000003043b880005281563b300000a60001d21f845ec00000000005e614c00000000005d84000e70000752000000000000036f8000000000000102c000000000119c782000000000000000000000000004270f9800000036700011c0e2a00016883d0c320002e98cd86e000000000006d663a00017f501200000018d4814000000192c8a838335c8128d9880f38d93b8c3840137e994c00000030300000000000ee17d800000041719f0bc836e114800000000000000003020382d913048225a61968f589ac00000000002400001af00001d25fa000000000013400019a000000038c00000007d0000000026a7c016f80009e80003f100000000001
  | 21 => 0x2d8037c8e80003a000000000000000000c1485c0359d787c676037b13f0d5447f02ba06cde42c700013700004d1086800000000034015f869c0ba4268000cf00bf2060d0c9523bc299000103e1192f7000000007518019784ce4073c880000008393ca80000000003df04740000001da85d074400000009c00001d22941af40001b70ac00000004be306000000000003896649bc77817a8000e0a7250000000168237000000000082d1278b4c03400900018b078a0000001f3c000597126193c0000000000e082ea2e807603842b80001b6158c000000000000000028242e8c5c780594000124400029f41b045cd6c4f20000b5c00001335d00000008291020000000205403a118d266a90000efcae07b301b99100004bc00000000000440000aac0001670000000b040000000000f420000000000422000113800085a0000cd000000000018680000004c623b0360b5c3883e204fc91022a00010a000000030b00000005a73d69d64ba03080929d18f282da0090a280002a0211983ce3e5cd1e188e0c7600000007f8000000000122c00000c28288b4e641c634788a0e4800000000000001473fa9570b207dc00010d855a2ce29f00000006cf00015108d80003680e4c44079b09518140007e6000000095800000016fce8e0a1000000000000041d0ccc0006b1021800000059839f12e8f8a0003089dac4da0000000000c1c7cc000000000066c2cd000000073d3720660a5e0002d08a180001a019600000008521ae800000087400006c000009700016bcbe81703e40000eb83650549d4c00000000013840000a0000000000057d124800000000000010f4be600000016b400000023c02b87ca00016b21650ec5b40000e2c21e06e3f88308f4664c000161499a458077800049c14828f89bcb2a39d3190a94b0287234489ec00027600000000e60002958000e161a52cd8000274000000000088600042f9e304b01773dc0000b7c0000000000c9c4e332a8e240008143a59b80cb272d34d8000a2e3fc3630000adc64a0af8ef800032f00005f80001930000000000000000078c0005f90000ee400082800017fc6fc22400000004443cc0000000000000000000000039e14d189400069f0078000ad40393ee80002a46203f900000005b11d411340001b32e1000000015900003500000000968ca4e52000000191400000000020390c60002948c180000000d4800059e45600004d800083c00000000000000001674f122b638e180434c5c50e383dcad000000021400480000f213204c455f2c59474da886f00d80fc45c3681e8152432481c22787543103713ed84907340002bc9b440000002e891240006231db07ec69a26543690d0000413000149816c23a000208013e0001749068000319000000000000021a8000000305003000062c6330000000
  | 22 => 0x12c8ab668c0c596349ec6fa12000000000000000000fa41cb0d193a4db07c21ff84b903027133d0f4c00000015400000003982ec94b47602eb3dd84ccd4208800000000b063406496a800000000014040001ed24e8c4052400014380cce1c3240000f24c8e7e72f013b0d4e0000001270d941370240a387cc00000009801286841a300000003ce00016180007c900016f00000000bb0fc000044815100004f2000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x128b16911a892c1d281c8d278f028003249a2b268000001b1f8000000000000010001c000004079f0f800023941804808c298a9399800980201e9da9212311ab800000228caa948100001087260a0180259218ac8d9727130b97a080000e9602061905a508052a0021959e241b8028800006a203950e08818114000010a2050d0004107002c188060430400040840e9800100507a5c63dd1635480141e9718c7458d5200507a5c63d91635480141e9718c6458d520060de1f64584615480183787e1161185520049564c8058461548014709058570185520048de6161d0061548014559318071581520050da5b401c5605480181e85a0f7458a316c40fe6152dd1628c401470905d8715493100507a57739cf644840109f9761b53d8d4000507a5c63dd5635000181e861d76358d400060721463dc9635000181e831d66258d400050b64875189635000141c955cc63d89400060720c76595525000181c7321953549400040fe61761d9525000141c935d876549400050d245761d95250001436919cc76549400050724d701d95250001434915c07654940006071cc865cd525000181c6321d635494000607a0c769c55250001434965c471549400064c5c5801c5525000181c8518d764c94000625204635d9325000109d98ddb634c940006071cc8558f615000141e95dcc6398540006071cc8558d615000182c851c963585400062520473589615000181e732195394540006079cc8654a515000109f985db638c54000427663321d9315000109d980c4764c540006072147658d3150001894811d9324c5400052a640211d92150001ca120440764854000607214835d3624c1b103c9854974d89300042725d84d89314c0014649654871595200056864470dd15248001721911c3745492000519259711c552480019617160071549200054aa5f84dc1524800152a9721370549200049926152584614800105f985cc73d95100060b61172188654400184d835c8621951000718485209db5244001c2940480765491000718485201d952440014659284076549100041d660101d9524400145593040765491000519648101d952440018547660e7154910006152197354a51440015a1921c3744c5100061921b7254931440018667660865885100061a1d9821952044001a636121952481100068a21b84549204400166296a055248110005d064e81549204406d6609660552481100069821981549204406d361985487148110006d060d521c52044001b418354a514811026f181db654852044129aa086e112148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x11000002451a3241615c06154801418532e2c00e2a928000a18299716007154920
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x2
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x138b
  | 12 => 0x138c
  | 13 => 0x138d
  | 14 => 0x138e
  | 15 => 0x98c
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x9cb
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0xa0b
  | 22 => 0xa0c
  | 23 => 0xa0e
  | 24 => 0xa4b
  | 25 => 0xa4c
  | 26 => 0xa4d
  | 27 => 0xb09
  | 28 => 0xb0c
  | 29 => 0xb0d
  | 30 => 0xb0e
  | 31 => 0x1409
  | 32 => 0x140c
  | 33 => 0x140d
  | 34 => 0x140e
  | 35 => 0xb49
  | 36 => 0xb4b
  | 37 => 0xb4d
  | 38 => 0xb4e
  | 39 => 0x1449
  | 40 => 0x144b
  | 41 => 0x144d
  | 42 => 0x144e
  | 43 => 0xbc9
  | 44 => 0xbcb
  | 45 => 0xbcc
  | 46 => 0xbcd
  | 47 => 0x14c9
  | 48 => 0x14cb
  | 49 => 0x14cc
  | 50 => 0x14cd
  | 51 => 0xcc9
  | 52 => 0xccd
  | 53 => 0xcce
  | 54 => 0xd49
  | 55 => 0xd4c
  | 56 => 0xd4d
  | 57 => 0x1a09
  | 58 => 0x1a0c
  | 59 => 0x1a0d
  | 60 => 0xec9
  | 61 => 0xecb
  | 62 => 0xecd
  | 63 => 0xb0955
  | 64 => 0x209
  | 65 => 0xb4955
  | 66 => 0xb4956
  | 67 => 0x249
  | 68 => 0x2c9
  | 69 => 0xd4a
  | 70 => 0xd4955
  | 71 => 0x1a0a
  | 72 => 0x1a0955
  | 73 => 0x1549
  | 74 => 0x16c9
  | 75 => 0x14a
  | 76 => 0x19c9
  | 77 => 0x134a
  | 78 => 0xb1395
  | 79 => 0x4b
  | 80 => 0xb5395
  | 81 => 0xb5396
  | 82 => 0x4c
  | 83 => 0x4e
  | 84 => 0xd5395
  | 85 => 0x1a1395
  | 86 => 0xeca
  | 87 => 0xb0995
  | 88 => 0x124b
  | 89 => 0xcc995
  | 90 => 0xd4994
  | 91 => 0xd4995
  | 92 => 0x98d55
  | 93 => 0x1709
  | 94 => 0x15c9
  | 95 => 0x168b
  | 96 => 0x12cb
  | 97 => 0x1649
  | 98 => 0x198b
  | 99 => 0x134b
  | 100 => 0xb49d5
  | 101 => 0x124c
  | 102 => 0xd49d5
  | 103 => 0x1a09d5
  | 104 => 0x150c
  | 105 => 0x128c
  | 106 => 0xec9d5
  | 107 => 0x1a49
  | 108 => 0x17c9
  | 109 => 0x198c
  | 110 => 0x134c
  | 111 => 0xa0a
  | 112 => 0xb4a16
  | 113 => 0x289
  | 114 => 0x4d
  | 115 => 0x1489
  | 116 => 0x1849
  | 117 => 0xb89
  | 118 => 0x124d
  | 119 => 0xd4a14
  | 120 => 0x1a0a14
  | 121 => 0xd09
  | 122 => 0x150d
  | 123 => 0x1889
  | 124 => 0x1609
  | 125 => 0x128d
  | 126 => 0x409
  | 127 => 0xe89
  | 128 => 0x168d
  | 129 => 0x18c9
  | 130 => 0x1789
  | 131 => 0x12cd
  | 132 => 0x589
  | 133 => 0x1049
  | 134 => 0x198d
  | 135 => 0x1949
  | 136 => 0x1a89
  | 137 => 0x134d
  | 138 => 0x749
  | 139 => 0x124e
  | 140 => 0xd4a55
  | 141 => 0x150e
  | 142 => 0x128e
  | 143 => 0xeca55
  | 144 => 0x168e
  | 145 => 0x12ce
  | 146 => 0x16cb
  | 147 => 0x160a
  | 148 => 0x148b
  | 149 => 0x28b
  | 150 => 0x19cb
  | 151 => 0xccb55
  | 152 => 0xb4cd5
  | 153 => 0xd4b55
  | 154 => 0x1a0b55
  | 155 => 0x154c
  | 156 => 0x178a
  | 157 => 0x148c
  | 158 => 0x28c
  | 159 => 0x19cc
  | 160 => 0xd5455
  | 161 => 0x1a1455
  | 162 => 0xd4bd5
  | 163 => 0x154e
  | 164 => 0x16ce
  | 165 => 0x1a4a
  | 166 => 0xd54d5
  | 167 => 0xed4d5
  | 168 => 0xb8e
  | 169 => 0x1a4b
  | 170 => 0x17cb
  | 171 => 0x164c
  | 172 => 0x2cb
  | 173 => 0x20e
  | 174 => 0x15ce
  | 175 => 0x5cb
  | 176 => 0x1a8b
  | 177 => 0x160e
  | 178 => 0x74b
  | 179 => 0xecd55
  | 180 => 0xd4ed5
  | 181 => 0x170e
  | 182 => 0x1a8c
  | 183 => 0x178e
  | 184 => 0x74c
  | 185 => 0xb09895d
  | 186 => 0xd49895d
  | 187 => 0x2c211
  | 188 => 0x2d551
  | 189 => 0x180a
  | 190 => 0x98d54
  | 191 => 0x180b
  | 192 => 0x180c
  | 193 => 0x1a57d1
  | 194 => 0xb5695
  | 195 => 0x5395
  | 196 => 0x139255
  | 197 => 0x124955
  | 198 => 0xd5695
  | 199 => 0xa0d54
  | 200 => 0xd5995
  | 201 => 0x1a1695
  | 202 => 0xa1a14
  | 203 => 0x151295
  | 204 => 0x180a14
  | 205 => 0x1692d5
  | 206 => 0x199355
  | 207 => 0x1a0d51
  | 208 => 0x140d54
  | 209 => 0x149a14
  | 210 => 0x148d54
  | 211 => 0x180b56
  | 212 => 0x58a
  | 213 => 0x14c955
  | 214 => 0x180e
  | 215 => 0x1a57d3
  | 216 => 0x40e
  | 217 => 0xd5515
  | 218 => 0x188e
  | 219 => 0xbc2d3
  | 220 => 0x180d54
  | 221 => 0x1a0d54
  | 222 => 0xd4754
  | 223 => 0x592d6
  | 224 => 0x75354
  | 225 => 0x16cb56
  | 226 => 0x58b56
  | 227 => 0x74bd4
  | 228 => 0x178b56
  | 229 => 0x1a8d54
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1529
  | 6 => 4365
  | 5 => 2167
  | 4 => 90
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (62172+((h/509+packedAt gbK7 (56573+(h % 509)*11) 11) % 1835)*12) 12
  | 6 => packedAt gbK6 (228435+((h/1455+packedAt gbK6 (209520+(h % 1455)*13) 13) % 5239)*14) 14
  | 5 => packedAt gbK5 (136517+((h/722+packedAt gbK5 (127853+(h % 722)*12) 12) % 3461)*13) 13
  | 4 => packedAt gbK4 (6510+((h/30+packedAt gbK4 (6300+(h % 30)*7) 7) % 119)*8) 8
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fff0780fff07fe0ffff80ffc14689e1cf3cf
  | 1 => 0xf8381f800f07f87ff0f03ff07c6b9769133d33
  | 2 => 0xffc01ffff007ff87ff003fff838c1871e3ce3c
  | 3 => 0x1ffffff80007ffffc00003f01f81fc0fc0
  | 4 => 0x1ffffffffff80000000003ffe001fff000
  | 5 => 0xffffe000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x484010020900880112080210002002045045
  | 1 => 0x81092808542485290a092a068218329112512
  | 2 => 0xd681052b100495052a01254d018c1850628a28
  | 3 => 0x420219cda9d04047cccd80610af01d81b80f80
  | 4 => 0x84045e76cee7e66080860186337ee001dff000
  | 5 => 0xe7278007008084010808060843df5efc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37229
namespace PEqualNP.Outside.L_meta_37229
open PEqualNP.Outside.L_meta_37229.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 8 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 92 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
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
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
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
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_160 : Interval s3Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 14 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_128 : Interval s4Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_160 : Interval s4Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_192 : Interval s4Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_224 : Interval s4Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 228 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96)) (concat (concat bs4_3_128 bs4_3_160) (concat bs4_3_192 bs4_3_224)))
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
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_800 : Interval s4Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_832 : Interval s4Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_896 : Interval s4Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_928 : Interval s4Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_992 : Interval s4Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1024 : Interval s4Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1088 : Interval s4Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1120 : Interval s4Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1184 : Interval s4Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1216 : Interval s4Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1280 : Interval s4Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1312 : Interval s4Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat bs4_4_576 (concat bs4_4_608 bs4_4_640))))) (concat (concat (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 (concat bs4_4_768 bs4_4_800))) (concat (concat bs4_4_832 bs4_4_864) (concat bs4_4_896 (concat bs4_4_928 bs4_4_960)))) (concat (concat (concat bs4_4_992 bs4_4_1024) (concat bs4_4_1056 (concat bs4_4_1088 bs4_4_1120))) (concat (concat bs4_4_1152 (concat bs4_4_1184 bs4_4_1216)) (concat bs4_4_1248 (concat bs4_4_1280 bs4_4_1312))))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_832 : Interval s4Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 890 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat (concat bs4_5_96 bs4_5_128) (concat bs4_5_160 bs4_5_192))) (concat (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)) (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 bs4_5_416)))) (concat (concat (concat bs4_5_448 (concat bs4_5_480 bs4_5_512)) (concat (concat bs4_5_544 bs4_5_576) (concat bs4_5_608 bs4_5_640))) (concat (concat bs4_5_672 (concat bs4_5_704 bs4_5_736)) (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 10 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 60 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_160 : Interval s5Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 165 := (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 50 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
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
theorem bgb_4_64 : Interval gbAtlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 90 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_2144 : Interval gbAtlas 5 2144 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2167 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))) (concat (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896)) (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))))) (concat (concat (concat (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312))) (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))))) (concat (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 bgb_5_1856))) (concat (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 bgb_5_1984)) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)))))))
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
theorem bgb_6_4352 : Interval gbAtlas 6 4352 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4365 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))) (concat (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896)) (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))))) (concat (concat (concat (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312))) (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))))) (concat (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856))) (concat (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))))))) (concat (concat (concat (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))) (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))))) (concat (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))) (concat (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)))))) (concat (concat (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360)) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488))) (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))))) (concat (concat (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 bgb_6_3904)) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)))) (concat (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 bgb_6_4192)) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352))))))))
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
theorem bgb_7_1504 : Interval gbAtlas 7 1504 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1529 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))))) (concat (concat (concat (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928))) (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))) (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 34, 50),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 34, 50),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8feeeeeeafae8eae8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4209568488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37229.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[0,4]⟩,⟨.or,[0,2]⟩,⟨.or,[3,7]⟩,⟨.and,[5,9]⟩,⟨.or,[2,10]⟩,⟨.and,[7,8]⟩,⟨.and,[6,11]⟩,⟨.or,[1,3]⟩,⟨.and,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209568488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4209568488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37229

open PEqualNP.Outside.L_meta_37229 in
theorem PEqualNP.Outside.L_meta_37229 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209568488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4209568488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
