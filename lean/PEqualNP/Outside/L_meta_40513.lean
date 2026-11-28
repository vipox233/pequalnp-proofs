import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40513.Model
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


end PEqualNP.Outside.L_meta_40513.Model

namespace PEqualNP.Outside.L_meta_40513
open PEqualNP.Outside.L_meta_40513.Model
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

def SBf (j : Nat) : Nat := [7, 5, 7, 6, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40513

namespace PEqualNP.Outside.L_meta_40513
open PEqualNP.Outside.L_meta_40513.Model
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
end PEqualNP.Outside.L_meta_40513
namespace PEqualNP.Outside.L_meta_40513
open PEqualNP.Outside.L_meta_40513.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xd431
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffe03ff81fffffffffffc03f1fffc7
  | 2 => 0x1fc07f00fffffffe0f81f01f80fffffe4ccff
  | 3 => 0x1fff8000fffc0ffff001ffe000fffc0f8f0f8
  | 4 => 0xfe0000000fffffffffffe000000fffffff00ff
  | 5 => 0xfffffffff00000fffffffffffff00000ffff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc2450a1402382180318a31a28e2c5150955c3
  | 2 => 0x5489314656449469606a0d49b125596664cc5d
  | 3 => 0xa930a26b6a890ebaad0496dca249ad94b8f0e8
  | 4 => 0x31a2c58d8d1228d4d6b6c091048e3638df00b6
  | 5 => 0xc1c3060e0e1c30e718c718e1c7003820f6aa00
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000faaaaaaaf0a00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40513
namespace PEqualNP.Outside.L_meta_40513
open PEqualNP.Outside.L_meta_40513.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1800800070011424c30010007d6984300ff21ff30dc31ff41ff42ff31de43fd42ff10ff20fe40de31fe30fc32fd30fe21fd40fe20fe42fc30fc41ee21fc43ff43fc21fe43fd21fd43dd43fc40fd41fd31fc10ff40fd32fc31fe32fc20fe31fe10fe41fd10fc42ff32ec21fd20
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x51808202a80820532000007c7000c0001b840000900000210106780050054002000070300000042c000840c0470201cc31886d8a4885794431b6a94215f53486baa6105714d20f3208435f53506baa918dbd4941b6a90819e540c67ea89057d5031af298833c544823aa818d7d5231f2a0843d6510c6eea2905794f40e7188439d43102dca598f10c421af28c876e528433ea8a1e750e40bb288815d540c6e8a29957946319f2a6615d53842b8a2a1f908610e618843d4310867ca818d794f41b7288436c52506dca4205794c439e2a2216d52d07cca210d754c41aea9e857551d0abca790d794c42e7218436f52442dea498d794c40aea98859d540c6bca6105794f42b729061cd43886dca5a0cfd5110b728c433d54cc3ce6210de14141b6292635c53487a86390dd14520e721c437551103c84208790c421cea1a836d52cc6b8a6885755243aea9e815d53c86baa6206750f41bb28e85cd43086bca7084f55031bda82835f53442baa7a0ddd4532afa9a41ce31886daa4185714d41
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x14050140119020102c46150c21a359031086c5640c42187592538421d6595031b1d90310868d640c621a959031086646154830b19863108685640c421c650c50506c46350421e159031087854350421a559031c8695640c421e199031087154354440b818141087465308610
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x681431814108682ba4a610c21215da640c421
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => 2*((h/22+packedAt s2K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/54+packedAt s2K4 (2673+(h % 54)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s2K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/15+packedAt s2K2 (147+(h % 15)*2) 2) % 3)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07fffffe03fff81fffff07ffffe07fcf8fe3f
  | 1 => 0xff80fe07fffffffe0f81ff83c07fffff2733ff
  | 3 => 0xffff0007ffc0fffff001fffc007ff83fc7c3c7
  | 4 => 0x7ffff03fffffe0000007fffc3f803f8
  | 5 => 0xfffffff8000003ffffffffffff800003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x230a144023820880318a30144716426448561b
  | 1 => 0x4526288a4494511606a0d482892a8c892330ed
  | 3 => 0x8a144d54890ea2aad0496958124d5232c5c346
  | 4 => 0x1c58b1e712283bcd6b6c0c522471e723f803b0
  | 5 => 0x1060c1861c30c3718c718e6338018403b6a800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40513
namespace PEqualNP.Outside.L_meta_40513
open PEqualNP.Outside.L_meta_40513.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xc0000de43bc40be40dc30de30dd43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x33080185614143
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => 2*((h/9+packedAt s3K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/1+packedAt s3K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fffff01fffe0c1ffffc1ffffe0ffe00f3f3fc
  | 1 => 0x81f83ffe0fffffe0f83fe1e03ff0ffff4ccc7f
  | 2 => 0xfe003ffff07fffff003ffe003fff0fff8f0f8f
  | 4 => 0x3fffff800fffffc000003ffff003f00ff0
  | 5 => 0xffffc00000000fffffffffffc0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc30011c21041003184c02238e0112181151bc
  | 1 => 0x24425224642884a06a1521449290a4a944c455
  | 2 => 0x1094a4488351094d042a5409252a09528b0a8a
  | 4 => 0x596738914a1dae76b683111239ccc063f00f60
  | 5 => 0x618630e18c61cf98c733999c01888183eea000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40513
namespace PEqualNP.Outside.L_meta_40513
open PEqualNP.Outside.L_meta_40513.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1003dd32ee21ec21de31df32dc31
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3886210d514532
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
  | 4 => 2*((h/9+packedAt s4K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/7+packedAt s4K3 (54+(h % 7)*1) 1) % 2)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81fffff80ffe0c1ff87fc3ffffc1fe018cfe7c
  | 1 => 0xfe07e0ffffffffe0ff83fc1c07fffffe7333ff
  | 2 => 0xfff800fff07fffff0003ffe007fe1fff83c38f
  | 3 => 0xffff800ffffffc000007ffe003fc03f0
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8c30c808e10454031814c0a471d1321884563c
  | 1 => 0x14910111242800a068814408924244a83130d5
  | 2 => 0x28425aa243514d4d0452aac124b5195382c30a
  | 3 => 0x71659cc48a1d6e76b558228247399063dc03e0
  | 5 => 0x418610870c618b98c6633313802001836ba800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0eeeaeeeac8c0c8c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40513
namespace PEqualNP.Outside.L_meta_40513
open PEqualNP.Outside.L_meta_40513.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x617f53486fea09977cc230bda82877e5010afaa920fe54021bfaa261f621087f641107ecc230fd10421fb50506faa020df15130f7a1043fa408c2faa6085b14941bea80857e528cafca1995f94c10bfaa6433f54486fea5887e54331bfa9e437d52c43f680a077cc832be2a061df53502fca821df54e10bf28c657f50486fea918d754c21bf28e81be41506f8a508778c130ee980617d54443f4a021df55330be29c217f52043be86995f54620bea84633e54086faa6905f95030eea9c857c53487f261885f94a41bd28485f9300c3de64995f94221bfa92837e54ccafea5085fd4543bea8c21fa300c3f461887e48020bd28065fa5090afea910df94b30beaa0657e52043da40106f10a41fda00217e50086baa7215f94c41bc28283f85050efca320df94241fca80657e51106baa7085fd4c21bf290837c53482f2a021fe10220df21285fa10043f0a090df94830fc982417c504c7ba8621df54221bf29c837d52d06faa6105f95220bf28c81fb20042fea91077d0e43ae29a43bc43903be8618f64c030bea90217c514c2faa810df54440ef29c217e50082faa7a15f95040dea08837d52cc6faa7a0df94821aea98817d544c7f46090774c832bf2a463fa30883da64195f15021be2a6637d50906fca5a05f55120bfa9a817e51ccafaa421df95110fca00817e53c86fca690dfd5330beaa2437e52082faa7205f55240bfaa0637d51c83b86418df94b10bfa8a417d5010efaa3a1df95031fca8087f521086fca0085f94a42be282655d53082fea7085f14930be29e21df438c3f080085f14e21bf2a2437c548c2fea8885fd4e20be2a4637c52c42fca7a0dfd5120df21c817d53c86dea4a0df95330bf29865bf42d07ee82a0df54c41bf290657e548cafca118df54840bf28663ee21486faa9886f95021bf2a6417e544c6bea6a05fd4e21bf288637e54c86fca3905f54a31bf284217d54883b887995f94341bfa82637a50086faa690fdd0641beaa0217d548c3788420df95042ee996637d538cbbaa610df55132f7190657f50506faa190df54031bfa98217c52502faa1197754c20bfa92877c54c86faa420df54a41bf29c21df430c2f6a090fd8c431be29c417c5050efaa3187794c40beaa6637d540c77a85a0df94240bd28663ed21087f081985f94d20be2a0417d5190bee4310df55030beaa485dd43cc3ee6318f714d40ef996637e510cbf440105f14f20bf290817f524c2fca7105f95331beaa2613d54087bc63985f54640beaa4437e5310ef8a6a17ec4110ee29a83fb40cc2faa3195f14142fd280657d50d0efea898df54910be298417f514c278a890df55020af29c217e53102f6a0a0df15210bea9c41df53506fca221f7ccb30ef98c633f544c2fca8996fd0c43bea86657d5090efca721f750d30bf28083df53486fca7205f94321
  | 1 => 0xae00000b2802030d2238720000607bb2000000b5e14143fd286637e51887da84215f54032bf280637e53d0bf261107b90842bf2808779500ca78a8985f54f40ef994657f544cafea6885f55332fb884217d5290efca7a07dc4010be29821ef20083f681205fd5230dfaa2437d54c83f240885f14d10be28a857c54c82fca61077cc930ef19463ec52506f8a8885794c40bf2a4217e54087f040087ed0310be2a443dc434cb7886207ed0030bea98857c53086fea498df94440fca0261bf40102fca8087714d21bf28c637e5210afea9087e50230be29a817d50086fea0a15f94b41f710241fb108437e8721fed4143bfa92217e508c2fca618df94e21bea8683dc430c7bc62987bc8421bf28c877f53c82faa9087bcca32dea0081fb20c42fca3217790c43be2a441bd4310fde4310df54740bea8887fa30042f8a2a07e4c010bf296875e53082fca610df14121bfa92817d52903f4a010efd0941bf298617e548c2fca8105fd5032df214837d52d0efca11077cc931fda0241f5310c6b8a6a05f54420fc28283de314c6fea78877cc431bfaa0417e5390afea6905f15032fc904217c540c7f080185fd4540bf2a4437f53083f480205fd5030f621443be42106fca1a15f94421dfaa2617d520c6fca3105f95041fb90a437e500c2bca610fec8120be29021f5411077c86a1df54f20be28a87f840c42faa6886f15130bea9c617c53c86fca6885f94a43bf286877e50102fca121de54021fb20883bd42506fca8985f54b40bea88857d528c3bc64995e14121ef298417d5190efca421f74cb30bfaa465df4350efca208778c831af29c857d510c2f8a4885f94743dea10857e51cc2faa2197710e30bea9443fb50487be87995f14520ef21e61dc31cc2faa5985f94a40f621043de5390afaa918df54742bf29461dc430c3de8521774c930bea9c637c53506fea6a0fbd4941be29283bf41906f8a9885fd4d42beaa643f840482faa1217d84110bfaa2437e508caf4a021df94b31bca84857d51ccbbaa7085f95120bfaa621bf41106fca6215fd4143fd102217f54ccafca3a17754c40de2a2437e540cafca988770c530be2a2657f54042fca518dfd5331bea8e617d52882faa198df94f20bea9881bf4290af8a9995f15131f790441de434c2fca0195f94430be2a0217c54487de8510fdcc531bea9e217d53906fea810df14931beaa487dd324c6faa1a17d44010ae29a83df438c6f2a198df54e42beaa4657e52843b86518df94831ef298437e518c37aa810d7d4d21dfa0481dd310c6f8a0a0df54c21df218817f5150af8a2996fd0842afa9a837f54c82fca2105f54e21bea9421dc438c6fca4885f14943bea9061fa404c37c80a05f15330be2a241f820c42fca2215fd4532fda0441ef4250afca1217e44010fca84857c548cbf660985f94f10ef98
  | 2 => 0x12038580011a02004000000f80a0381402068408020380e0a8340081603028000165c802038046a9c80280a0a82603028000060003c120f26a03c020081c1500085c780280b822438dc00022008123080215814111ec0680a0680601014098ba1b8025082a0080802002358120100e1905c000020809eaf806040020702c1d0100d808080000304a1329e00090070020380c000120100000010f50001809c01978028c200812444581f8021080a0681800002028080b00400018000020a0800083c0000602050048929d0720c0045f866118080301c0f01c0000c5480a000141980480800052
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x530865e63152209e58253887984310030d6d0c5050f3b54141219ed8151d0e5c63550109e181548867860544429718d524427a60d5020ced5350486b8644c220c758c544c31c5450d30b6580434cb6852d41419758f54c865e6314c209758c52c423e6494d219e996204423e64951219e596100425e639401097d8d5110a3f6454d109e983540ca5f6355010d618153102b8644c010c7152304c27b6055031d694d30c427661150209758f540865c63551219e58253442d960cc631b9584420863f6454d21d614d300435943540439b988530425d63150219758f54c431d5494c21c7152434c27a65d01209758e544867b6550040b658c400425d63942418f593530875953540219758c524425e65cc93197594430c67b60544429ed9510042d96010e309718d5110b395494021d6580535027960153329e5805350a7960d5021c7d50534863c6454d219e580540c75a435404397d8d51d02d9638c0309758e52d025d63152108f59353c425f6355130e610e408c27b60551308f993530863f6550c4397596320c65e63951219798e509067965100109758f528433a545402197d95300c25e6394b409718d544827960d52329ed81518cb1c54cc9309ed95300c26c6254d10b61814310e7661150329798c548425e63d4a10b6181324c27a60d523197994534863d6414b108f9935284359544c0309e980540ca5d63d50208f997425063e6414e20b6d95300c27960d4c218f990530866d65108219e582539067b6055221dad4850506786055132d64c9500cb5853141419798f54c42796094d219d185534825d6394b419d584540829c644c0309e980540866e6215031c7551530872c5290541ae580439025c63547209e982534866d6215010b618d40102796508010d654e500873a54940219758e500431c5390140c715353486786548110ce150504875b32540329e18151d0e7960d5231ce153504874c53149419e98354cc66c6255131b618d408c27a60149319e98354c8675611503297596530835b654c030c7550430c67b6054910c7952530865e631502097d8d51c82796094b438f990530423e6414810b618143cc298644c0309e597400c23f64549109e58254486786054d21b658043cca5e63d5020b6580430c3685214141cb152214863e64951309758c548823c6454910d6945300c25d63148108fd954210ad960cc4319798c5050a5e63d52109e98252d0e5f6354910cb553420865f6550c439b98b540c25d6314a109798f54c865c6355221d654f108433954100109e980520423d65908419ed81544c73954102209e996404c27960150219e181544871c5414d2197d8d548835953500409798c52c43593254331d654d200835953482109e195304827a60150309e181540c63f6454d209798e534863d6414c109798c53086786550130
  | 1 => 0x7058000629018002400008182605020041000b28080201138081e000900c0003071640600028a4740b05818fc0200004000114000061c129a00603009500800000241a000b81c029a098f4000c01800180307838001400000201a0900c180503054862100014020a0c0056d0a008180e0103974000e140340006000001034018489a003200c02010000080010400c0800010000e9438808000028830044f0180c4400190200000ab189411067a6014c209e583540ca776155120b6991300c25e6394221d6d4f505065c6550d309e594400c2b8644c030b6580328c71c548c530ce153304c23e64d4f109b58853042d86050d3097d8d544425e6314810cb14b425074f53d4941d3d4c5250759524c03097594430c35b544c0309758f548427960d5331b658c40cc35b3254331b658c400c2d96308310ce151404c23d64148109798c540865c63551108f191534426d621503197d8d544c67765484219e181544c6d96010e318fd954010398644c03097d8d548875b53141219798e52d065f63551219718d51d025e6314a109bd95200823d6414e208fd95411067761551329b98b548426f654c8329e580524c75b53d412197596530866f6254d10e690e404c27b6055121c754e431023d64d4f209718d54883385490130d614c504863e6515121ae191304823d6494d21c7951530866f62551319798f540ca3d6595021d694e5090a79658c0109ed952008358534c2209b58b540c2b8644c3109dd95100435853d0140d654e5090a3e6515130cb149425063e6414b109758c540425e65d0d32b6982314c25e6590d30b658c404827860553329b189544435853d41219758f54c8339601513097d95320ca5d63141429e98053c866d62d53318f191534825d6315020d654e40102d96310310d694d5090a796014c219e983530867965c80109dd85534827a60153329ed81544427a6094b419ed81534879b644c0309e9805350b5a5354021d654d5090a6f62551219758e50886d8644c0309dd9541106786054632c7150314c25e63150309e58053c86d86350130a718d401026d62d521097597430c25e63d50219e983548ca5e63150109e982539075953882109ed8154ccb58534c1208f99353c82ac64484219bd954210a796015032b6580320c67a6094e21ce90c5050e6e62d5331d614f50506796015331d654e200823e64150219d185544cad96384010cb189540874c53d4941b658c408823d6414c219bd95210867a60951219e58252d067b60551329bd89544427a6015331b658c200425e63d53209e58354c879a4310330dad4b50506d96010c319798c524431d5410f32d694e500871c544c930ae1814310e5f63551209b988540427a6015031d6d4c505065f654c4319dd95310c71f54d4d219d185544827a60d5021ce551500863d64d4a109e98
  | 2 => 0x13a7e138781216010383c05040085c0003844040
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x600000018069944f00080000c1c32a8b18811061864945300c2a4b96a898061865516010c31c30c829a60086185418d404c28c382a821863469d64390130c30a9304629851873550408830c2a0c099261461cd5410010a32e829a611061a6590e404c30c324a698621161d9544c030c32ea32260185497214d300430c320a698241461c15410f32a32e829a600861854181434c30c322a49806186193544c030c32a8b1880086195458043ccb0c320a698441269d2644c030
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x200081987190534c22081987190534c010c08645c8534c010c08645cb544c030
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 601
  | 4 => 396
  | 3 => 28
  | 2 => 4
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
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/200+packedAt s5K5 (16227+(h % 200)*10) 10) % 601)
  | 4 => 2*((h/167+packedAt s5K4 (15048+(h % 167)*9) 9) % 396)
  | 3 => 2*((h/23+packedAt s5K3 (1372+(h % 23)*5) 5) % 28)
  | 2 => 2*((h/8+packedAt s5K2 (240+(h % 8)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7e03fffe03ffe183f07e1f1fff87fc0620fe7c
  | 1 => 0xfffc0ffffffffffc007fffe0fffffff83f1fff
  | 2 => 0x7ffff03ffc0fffffff801fff0ff83fffc3e38f
  | 3 => 0x8000003ffff001ffffffe0000fffc007fc03f0
  | 4 => 0xffffffc0000001fffffffffff0000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x529861a238a24b80ba17071593c66436206e3c
  | 1 => 0x429220449048014002a2920248889500d14d5
  | 2 => 0x18508488906908a952801246095232a2c2a30a
  | 3 => 0x5162cb312241cdce6b4d40148e6720c77403e0
  | 4 => 0x61830c21c38e11738c719c98c0040305bbd800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0fce8c8c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40513
namespace PEqualNP.Outside.L_meta_40513
open PEqualNP.Outside.L_meta_40513.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904001ffd5001fd3100ff14005fe5200ff04001fd21007f88405ff21007f4c007ff53017fc8003fc40017f90801fe41017f8c805fc4200ff94007fe53017f08401fe4301ff54805fc52007f10407fd5100ff08001ff4101ff14c03fe2000ff90003fc30007fcc407ff51007f50801fd41007fcc801fc43007f44007fd50007fc4007fc5400ff84007fe51007f8c401fd40007fd0c01fd2001ffd4807fc5101ffd4001fd43007fd0007fd54007fd0801fc3101ff95005fc32007f4c801ff3001ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x166200ff90d41037fc6018803fe4350813ff3162007bf19741007fc6290087fc40cc40dffa186231ff59532007fac88801fbe54d0403ff9822006ff4c730015f8c4218d6ff65508057f314623aff1444303ffccba10affc3090405fe212422cff0ca4103ffca92182ffe5148005fe10e8400ffcc84105ffaa69001bfc328c40fffb068400ffd8943037fe639800bfe20d0801dea168206ff590311affaa8a101bfc3210c077e32a2000ff19130007fac498813fc424400d7f3188600ffd0d3221ffea1a181bfc308c40ffe3168601bf58340037faca21853fc4048405ff2968435ff54d4200ffe419800bff5250801fe90e6002ffc854201dfcca18802ff6244001feb1a4207bf99043047f8838800efc654c80ffe30e8643ff54b4300ff88088007fe40cc003fe0822000ff0c54003ff887a00cffc51cc80fff21e8401ff08110117f885988a3fe305040fffaa6821dff109311d77aa821817fd54440017fb226001bf98343007fe65a001aff64cc883ff106863cff94943037fca69810fff53d0c0fde200861cff101311a7fc60a1002fe61d0c0dfea1e643fff90a43007fcc898833fe624c001feb1e2026bf59441017f84090823fc518840fdfa16821cff081310eff8c49883bfc21cc00dfea188607bf99330005fcc32188ffd54cc4037f3008631ffd4d321b7fc61a1077ff204c445ff9066200ff58d4103ffe86a0803ff314400dffb088601ffcc130007fa628800afc628c40fffa1a8421ff0433100ffca0a0003fd32d0423fea928015ff551210f7f8ca98803de434c059ff2148208ff14710197fc8199002ff644400dff98a6200bf58341007fa4288073fc104c40ffe3068601ffd031003ffca9a1806fc6090461ff0826401bf98031035f8c999006ff634c05fffa868200ff191101effccaa1883fe428c429fe0824200f710e31067f884980bffd50d040dfe1808607ffd0f420affeca90897fe5210401fe98a4200ff50e2103ff680a0003fc4348001ff98a4202ffcc9200e7fcc098803fd43c4005f61926401ffc8110015fcc418803fd3250051ff0828206ffd9443047f8c11081ff641104017eb226206ff1933000ffea0a0002fd640c40fff2188227bf59641047fec018807fe205001ffe2a66002ff8852003ff8c7a100afe6250c63ff32a6441ff14343027f8428800bfe42cc80dfeb26600fbf59730035fcc7a081ffd651040d7f31a4000ff9912105fdaa4900effe6050c077e32c4200ff18d4101df8ca9800bff2048401feb0a4000bfd8540177fc65a081fbf411040fffa1a8601ff4831000ff88098007fc204c045fe10e6202ff0ca2100fdc4090007fa104803bfe10a620fffd4b30005fac120847ff535000dff21a8600bf58d10017f8659901bfc62cc057ff304820dff55130017f84290803fd648c449ff1808202ff90a21
  | 1 => 0xbff21d0c0bff32a200dffd95301effea2a1803de314c00ffe32e8614ff0c12103ffec3a00d7fc6550811fe18e2000bf58a43047f883108f7ff6550c4f7fb2c8207ffd9740017faa59906afd650c401ef9926200bfd89401c7fc402180bfe4248405fe9944200afd9121117fc859881bfd600c40dfe1926013ffd4b40047f88318807fe404804dfe2988200ff4cb10007dc4290807ff50c4005fea944207ff9974003ffcca2086efd658c403fe9824026ffd4441035f8cb9881bfb304c003fe1826011ef95140017fc4199037dd534c00dffa9e6406ffd9730047fc822081ffc5450c037f300822dff8c341005fec4a1802fd6244087fea8e8606ef90d4301df8caa1003fd6150809ff212200aff54b1001dfccaa101afc640c40fffa1e8200bf18532017fc411081ffc429047bffa928611ffd514003ff886a0823fc629042fffa9c4201ff88310035fcc72190bfe32d0c87fea868600ffcc94103ffca82180bfd42cc80dff29e600affd4f1003ffc83a005ffe548843dffb2a6203bf9954300fbc6198077fe424c47bfea828610ffc8540007fec299023fe511040ffeb2e860bff15120007f8c890802fd64c400dffb2c8603bf997100cffca41884ffc53d004dfea988233ff95332007fa831080bfd42884017eb244242ff14b43047f8c588023fc648c45dff90e8202ffd492000dfcc099023fc631040d7e31c4200ff50b10017fe859900aff624c843fe106622cef10a41047f8a320823ff63884017eb168200ff50710015fec49084fff51d000ffe21e8438ff14043207faa52181bfe434c80dff3088608ff14631017fca499003fc635087bfea92860aff95310007fcc2a001bfc5350c0dff3286206f790f3003ffac1a08effe5050c01feb128206bf18d4113ffccb208cbfc50cc80dfea988606ff197320f5faca9881bfc5310c017f30e8402bf988430c7fc2018903ff5090c037fb022006ff94d31035f8c6a1006fc6010c01ff18e803dff9454300dfcc0a1002ff634403dfeaa26200ff50e41007fa871882ffe6548005ffa144210ff149400b7f8a110907fe50d0c0dff3266234ff98142005fac89084ffe51d000dffa9c8600ff98d40037fcc41884ffd53d0003fe2862000ff98f1000dfcc0a18fbfe2090c057f3148200ffd0b1005ff8a690017fe534400fff3008201ff1033008dfecaa003bfc42cc021ff1928000ff88740187fc609901fff415000dff3006201ff54140007fac4a001ffe63d0423fea8a800bffd4520007fcc2a10d7ff6550805ff2928400ff90520004facba0003ff604c40bfeb2a2000f7cc930057eaa388007fc10cc00dff29e6200bfd8532005fec9108b7fe10d0453ff2928201ff08330007fcc7108c6fd654c87bfeaa28605df19510007fac898003ff644c40ffe218820fff553300affca690806fc6090c0dff3
  | 2 => 0x43015f8c4a0803df6350403fe2826008ffd93100dffaa51881bfc534c80d7e3266000ff1053119ffaa19901ffc42d0011ffb162000bf59330207fea921803ff424c0077e32c6217ffd422103dfecba10c7ff514c881df2a48606ff8c84303ffaa9a0003fc4148401ff9968207ff9034203ffac5a0806fe604c411ff1886207ff15342157fea4a0823fe510c401ef18e603aff54443037fac3990e7fc5210c03ff1828002ff8cb3203ff884a1873fc604c40fffb2e8400ef19130037f8659801fff43500017eb16203bff0814302ff8a288097ff201042bfe32a4202ffd4b420dffea118807ff3048001ffa0e2000bf58043187f8c0990cffd51cc803ffa022000bfd8f100057ec8980d7ff515087dff2848623ff147310bffaa11083fdd53cc01bff32a6002ff1092018ffca299016ff6544011fe1088231ff54d3200ffaa188003ff604c8017eb088617bf5962115ffc412081fff65d0401fea1a2000ff4c7400bffaa31087bfc514c405ff1944206ff19643007fe63a00d7fc5350813ff1962002ff14a21037ec6218857fc514843fff1046200b7d8d210dffea7188dffc53d0855fea9a8200bf58221007fa8698803ff6150001fea148209ff14b101dff820a180efe654800dfeb286200bf5874300ff8619801bff6290c017eb006201ff101200377a8621806fc60cc86bff28a8401ff08120157fea2a08ffff2190c0fffb1e8027bf98441037be6598003df318c401ff20a8208ff1931005ffaa890003fc414c07bfeb2a8606ff58a43035f8c6a001ffe6310401ff98a4003bf99732007fa8690807ff20d000fff2008200ff58e21037fec321803fd428c459df2148201ff4811003dfcc91081ffc65d0433ef1906212ff0874006ff8a2980fffc5290c75ffa80862bff142411edfecaa1803fd418c43fff304623dff54d43017bc649901bff6090c01ef18a622aff19541067fc849807bfe654c471ff280863cff0854300ff86088003fd3148011fe18c4201bf18132017d8851080efc655040ffe2a0822aff94541037fcc39901ffe43d046fffa8e8402ff4852018ffea899002fd64cc8377f3086208ffd8e41027f8648801fff429040ffba0c8201ff9431000ffc20a001bfc430c401feb148203bf9963103ff8a9a009bff5210403fb0862002bf18b311d7faa421807f810440817eb2c8630ff98132005fec09901bff320c403ff9024008ffd92310b7fca110823ff620c40dff30e6006ff0cb3100ffe809807ffc508c4016e31a4200ffd0a31037fea62180bf72188411ffb2e2040ff54643037f88699007fe40d002b7eb2a4233ffd433203ff8c7a00dffd53d0811fe3244202ff0c921005fac19901bfe430c4677eb2e6406ff8ca43037f86198803fc614c80dfe1826235ff99542017fe649900efe65d0001fea1a6002ff08520037fcc19910
  | 3 => 0xf3024201ff0c120017ee4290807fc50cc071ff080861eff5493103ff880a110bfe52d0c4ffea948228ff08141007f8c69001bfe3090c65ff0866420ffc8631147f820a085bfe1088479fe3128608ff0843114ffe40a080bfd5248443ff1066200ff58e41007f2408800afe64d08037e3006206bf98f400f7fea69881bff4390c01ffb0a400df794d30005bec6a0803fd4244001ff10a802aff5514103fba8621806fe64d00157eb2e2002ff881211a7f820a1006fe609042bffa9a4201ff5031017ffea3a0813fc6244001fea0a2003bf99743017f8429900bfc42d08057f316862aff14d411e7fc84a1803fe64c400bff2a22007ffd0641137fca620803fd424c405f610a4200ff50b3114ff842a0803ff4244003ff0862027ff54241007fa8298823ff650c44ffea8c8201bf18041007fa8398803ff418c40ffeaa68400ff58143005fac420806fe608840ffe2068402ff083420d7f8a818823fc63c400dfe3288602bf1893103f7ca82180bfe42480037f30e201eff9513100ffea0980bffd53d040fff3068607bf19132015fac51086ffd508c423ffb2a8000ff5053003ffea821803fd324c001de3224201fe90340035fcc618857fe544843d7eb1c622cff8ca41047fecb10807fc5044005ffa926407ffd5343017fe40a10c3fe404c80fff30e8601ff08340015f8c598043fe52500057f316823dbf5954306ffaa4980dbfc10d0801ffa166201fe0c13010ff8a198817f55144005fe10a8408ff19031007f88398083fe328c401fe9948200f718d4119ffea99900bee524800ffe202860aff54710007fe8498873fc504c40d7fb286206ff50f3000dfec09005fff548840ffe21a843cffc814300ffc4098003ff604841bffa9a6000dfd951003dfecba080bff424844ffeb2c8202ff14b32007f8c8988c7fc544c827ff29e8002f70cb32127f8402080efe6510c016e31a8206bfd973103dfcc91880bff20d0801ff21a800affd531003ff8842080afe61884073e32a6007bf9913003ffcc3a001fff61d084fffa848206ff193311cffe422181ffd62d0001fea126034ff90142005fac121803fd6250c5f7eb2e820bff595201d7faa021823fc6390401ffa0c420bff94d20037fca6a18dffe51d081ffe28e6001ff04340007fa6518803fc41cc403fe2068006bf98c4106ffca89800bff21cc837ff2a46207bfd974003ffaa82081bff64cc8057e3126028ff90141047f8c0208affe5090411fe080820eff90b30037faa618806fe6090c03ffa066001bf5833001dfcca20803fc414400dfe2986208ffd8221047fc821881ffc545040d7f31c8214ff1812108dfacaa000bff21884037fb228007ff9524103ffac1a101bf5310c453fe3128201ff041201dffc80a181ffc43d0435ffa886207bf9911004ffe438807ffe508c40ffe2a28400bf583
  | 4 => 0x827fe52c400dff3008602bf18943007fc878804ffc51d0023fe29a8005ff54510007f8c6a0003fd614c8057fb228407ff98b41037fea798803fc4148009fe2922007ff18b4111ffaa19881afe6348401ffa0a4206ff94c310f7faa09886ffd518c405ff2168400bf59130005fac1a1013fe32440077f32c8611ffd4540005fcc39801efc6448403de2068000bfd8131007f8c29808ffd51cc40def29e6002bf18a43005fac62087bfd514c401ff20a8006ff0c931017f8a490823fc6510445fe2966204ff989101eff8a2a18bbff20d0419ff90a6013ef5534000ffca19801ffd43d002bfea8a4207fd504410effc649887aff654c40dffb06642bff842411f7fc212186bff520c411fe3046202ff50921007fc62a001bfd43cc405ff902640afd9471003ffac420847fd5350001ffa1c422eff08741037fc6021863fe400c40dffa9e6002bf188310fffc211881bfc64cc80dffb108605ff54910037fe8621893fc3010423ff28a8007bf1974303dfcc99901ffd65d0401fea166006ff8c33213ffea920803ff3250055ff32a8227ffd4e41047f8c12081bfd32cc017fe28a4002bf9893000fec208801aff65cc00ffe2028206ff1824300ffe8090002ff6350801fe18a4206ffd0f32177fca5a0873fe204c433fe210620bbf5952003efaca2083ffd52cc0017eb108606ff0c530007fac6a1002fd644c80f7f3226200ffd0f1011ffca998837fd514c07fff2948607ff15341007fe8298006fd60c4031fe2006201ff8c31003ffc81a081bfd61cc001df20a8203bf9954001df8cb8801bff310c403fea826018ff0803100ffca08800bfc424c803ff106600cff14930157fca6a084bfc32d0001ffb128001ff94130037f864a1802fc6150001ffb1a4007ff58c410d7faa818873fe504c40bffa9a2003bf9974210ffca19881f7e65d000f7f3226430ff10132007f8628808ffd52cc405fe1026407bf9933117ffea5a0807fc30d000dfe1828607ffd8341047f8201881ffe4210401efa186206ff5833101dfccaa0802fe61d0019ff1926002bf18940037fa6218823fc658840f7f3224201ffd411018ffaa89906fff548c401feb046207ffd8f42015fcc59880efc654c42b7fb2a4207ff90b40037fecb99002fd628c401fe9922000ff5073001cf8ca88003fd41484017eb168000ff58930007fac0a081efc644406fff29e8400ffd8d4202dfaca88002ff6350001fe30a8430ff04132017f864900a3fe60504377fb2c6200f7d0d32207faa121802ff644c441ee1946202ff08142007fe8598067ff200c4037fb026000ff4c93111ffea198807be40d000dff30c8601ff88110017f884a101ffc43500017eb222000bf58d21007fec298006fe6050459ff90c8203bf996210affea090807f82048005fe9924207ff10941007f8c899023ff6090429f
  | 5 => 0x9221004feca88003fe644800dfeb2c8640ffd4643007f8c29001bfc320c40ffea0e8000ff58530005fec4a0873fe104c40ffeb068600ff50d41077fe43980027d651040ffe2a68600ffd9121007fc872081ffe54d0005fea924006bf193310a7fc209081bfd62cc40dfe1806206ff8cb310f7fea098806ff6050001fea1a8402fd08621007fcc2a180bfe528840ddfa1c8601ff88120017f86499007ff2050041ff314622aef55141047fec51890fff52d0c11ffb28820dff1953000fb8619801bfc43cc80df79926416ff8c221087f842a001ffe5450c0dff3166002ffcca211bff8a3a1057fe6548401dfa0c8200ff10e211d5faca2180bbc42d080dfe1826406ff1873206dfeca98103fe5190c0dfea9c8607fbd094200ff8a1a00f6fd6490c037f3046205ffd511017ffca7a0802fd62d0c15ff32e20039f9944103ff885a0803fc6344029ff2824200ff10f10017fa8490023fc63884037e3044202bf18841037fccb980effc6050c017fb028408ffd8c41037f8c0218a3fc3050459ff3148200f750d30007fa829001bff64cc047ffaa66206ff9884305ffca890002fd648c403ff0826007ff50f421dff8a0a1803ff32c403dffaa26206f710c3101cfccba0007fd404c001ffb1a4206ff14f430effcc498803ff6050405fe1928403bf99510007fac988007fa2044003ff2028007ffd0e41047fc438800efe654c411fe3146206ff99731107f8a518803ff41cc033ff2106215ffd512101dfccb20803ff625043fff184622bff8c24121ffea3a18a7fc325040fbf3288200ffd893107ffaa398037fd654c055ffb2a8234ff0c142037f8cb98003dc434c8057e3168608ff1883100ffaa19801fbc42104037f31e6007ff5874316ff841a080bfe424c803fe2824004ffc85100a7f8a09080afe625000fff31e8011ff5954003ff881a080afe63cc80ffe20e802abfd954103ff8802081ffc545000f7e3288206bf19431007fe871880efc655001dfe2966039ff9484321ffca3a181bfe60cc4057f3148608ff14441005fec0a08037f654c045ff90e6200bfd9132037fc659801bfd65cc43bff90a6211ffd494003ffec7a08bffc53d040d7e31a4001fe84310017f865a1003fd21d0087fea9e860fff95330037f8639800bff214843bfe2926207ff5534100ffea19802ffc6548001feb048208ff18031007fec2a181efc644c00ffeb0e8006ff90c43017fca59901bff64cc483ff1868600bfd8520007de8510837ff544c06dfe1868407ff50c41005fac321803fd4348001ffa0a2000ff90e2103fbe86a1803ff624c00f7fb2e8602fec8120047fec91080bfe324840def996622dff04341037fa659881bfe43cc801ffa0a6206bfd944300ffaa088007dc304c001fe31a4208ff18841017fc84a1003fd644c80fffb168208ff196410affaa090
  | 6 => 0x5df2128406ff59730015f8c5880f7fd5150c05fe292403cff149431bffea7a101ffe545040ffe2168607ffd0941007fe839880afd62d086bfeb2a840bff54520057f8a988006fc6048479ff1928607ff58041007ba6498107fc20d0c017fb24622abf5924114ffc84a080afc62440017fb1c4208ffd884108ffccaa0002bc6448405ffa944207ff95342037fac32181ffc40d0c037e3068602ffd0942047fec818907fc10d0c0ffeaa68628ff141410177c85a1023fc410c40dfe3066406ff90d30007fcc910847fe535000fff32e8601ff8c11003ffac5a181efe640c401f63128207ff508411eff8caa1883de328c4077f32a4200ffd0d10177f865a0803fd3210415fe29e2000ffcca41047fec788006fc60d0875ffa888624ff88041037f8a79900bfe3248001feb044200bf58331137fea02081ffe62d0c0dff1866207ff10e41007fac58801bff328c40dffa1e6226ff5484116ff861a080aff62508017fb024202bb1894100ffca1a001bfd64cc42ffeb2c4233ffd47320377e8621823fe418840dfeb266400ffd0d31007fec6a001ffd63d007dff2048608ff90710037fec39805ffc5388411fe2886200bf58f4101df8ca9000efe654c00d7f31e2000ffd0d211b7f8a1a1003ff6050c6b7eb2a8400bf1854200ffa8198003fd6150015ffa8e2000af191301d7fca22185fff5188465ff2866400ffd913003ff8a9218c6ff654c801fe18e8042ffc834303ffcc5a001bfe6090c0dfeb166000ff58d1003ff884a001bfd430c40dfeb048601ff84330017dc6599002fe6110c01ff3226407ff90b41007fa65a000afc62904017eb0e8006ff58332047fc63108cffe51cc863fe28a6402bf98b10037faa79901bfc6110c057e3168207bf1913100ffea1a0007fc405000f7fb288208ff8c71003df8cba101fff60d0c27fea968000ff5813100df8c09890bfc21d0c0dfe30e6007bf98641207fea52181fff62d0003ff282402aff1454103ffa8220823fe51c4003f61024001ff08140047fca310803dd43cc02ffea9c423dffd41431affca6a100bbc4250801fe3224025ef9084100ffc41a0002ff6348001ff31a200aff54f10007fa8699047fd545000fffa168007ff19742037facb99003ff644c80d7f31c4201fd0431012ff86420803fd3150011fe3286201ff8c1301dffc40a180bde32cc803fea022013ffd4f401aff8a2a101fff421040dffb066206bfd9031007f86290007fc1050017ffb2a4031ffd9532007fe869800afe6250449fe2808207bf19231037fc871881ffe40d0c0ffeb2e8006ff1833105ffea690007fe1044001ff98a8000bf58f10035f8cb9901ffd42d0005ffa124008ffd8a411effea6a180efc6548441ff2946206ff14e43167fca52083fff54cc001fe90a8001ffd4120017fa6490087fe10cc453ff3128200ff5
  | 7 => 0x9081bfc43cc431ff100621aff54831005fac598837fe514c013fe216200dff54d301c7f8202185bfc4088401ee9966000ffcc910047f8cb1880bfc52d080ffe2a48200efd9121037fa641886bff500c46ffea8e8402ff082210bffaa91080bec4250837fe2a46201ff0c14012ffe42208c7ff504c8057f3122003bf99741005fac7a101bfe5390c01efa1e6402ff8cb4213ffea52081ffd63d040fffaa68010ff0c940037fac421802ff6050c15feaa62003bf19543007fac488002fd63480037e3028200ffcc710007fc428801ffe545086f7eb2e8416ff98221047f821108d3fe5050837ffa946200f74cb3108ff8caa0007ff104400ffe30e8006bf98631005fac7a0023ff608c40d7fb2c860eff94b30017faa499003fe648c47fff9048600ff59131007fec688007fc10c4031fe2806200ff4c7101cffe40218f7ff5450c0dff21e6000ff50831037fcca2181efc648844ffe29c8200ff58121007fa4388093fe5010405ff1026402ffd4b32147fca0a081ffc60d0805ff10a4202bf58b32037fe6498007be405000ffeb2e8439ff08443157facaa081fff411043dfeb2a620bbfd95201affea0a1003dd310c40dfe21a6007bf1912017f7aa9a0823fc218844dfea80820abfd9710037be6218803fd644840f7f3224012ffc8740007fa64a080bfc21cc8017eb008231ff1953203ff8c7a0823fe518c405ff9044207f7d0e4313ffea32081ffc4290c35ff2a06206ff9903105ffea89006ffd538c4057f3168026ff54441007fcc2990c7fe544c803fea868000bfd853000ffe418801ffc4090c01feb1a8000ff90d1012ff8a420813fe5244037ffa8c6208ff90631157fea0a081fff62d0c4bff1908236ff943421f7f841218dfff50d080fff2008602ff54942037fec399043fe4250011fe10e2000bf18520007fcc72081bfe53d0c0dff3266007ff1874203ff8cba0007fe30cc081feaa48600ffd0831047fec0208abfd52504037f3066400ff88530037fec021817fc654405ffe28e8207ff95041017fc40a1023fe519046bffa9a8407ff50f4100dfcc09088bfe52cc44ffea9c821bff99631017fe4290077fe524c475ffa908628ff88141007f8c2a00abff5350401feb224001ff4c3101f7f8212184efd65d0003fea824000bf5873000ffc818800bfe524840dff21a6207ff15043187f8a09901bff62cc005ffa126416ff90221005f8c2a181bfe43cc401ffb122001bf9834109ffaa3a000bec21d0801fe30a8600ff985200e7fc609885ffc548840dfe21c6200ff58d20057fea588003fd42504037e3068200ff90d2119ff8a999017f65144005fea968400bf58a410a7fc6090803ff6448025ff1968006fdcc631007fec888043fc6250005f790c4206ff5844303ffec3a1833fe524c001ee18a6026ffd4c4103fee82a0803ff414800
  | 8 => 0xfd4c31197f88199017fc534400ffe20a80009fd9530005fec2a101bfc6210c03ff186801aff5403106ff8a8980abbe545040dfea9e6006ff0ca43017fe43a101fff43d0013ff2162015ff14d21037f886988d7ff545080dfe29c6206ff98a4303ff88120833fc624c00d7e31a2034ff14142037f8612181bfd6010c4ffeaa48206ff94d3203ffac7a10abff54504017fb1a4215ff94521037f8a7988effe3050c37feaa4623eff14243007fe8218817ff514400dff3266406bf19443037fecb9887ffc208c4017e30a6000ff8c531005fec49801bff32cc00dfe29a6200ff9051003ffea9a101bfe5310c5fffa9e8200bfd85430affea290802fd608c401dfa128208ff04241007f88690803fd6050835fea886200ff58543005fec49888fff51cc401ff18a2003bf997310f7fea29885ffe658840dfe316623eef9024300ffc21a0007fa30cc001ff20a6206bf19643007fc839881bfe320c401ff31a8407ff5874218ffaa0990a7ff21504057f3126200ffd0d201e7fcc4a1823fc108c403ff1824000f7d0e31127fc2020817fe514405ffea968201bf983311bffaa1a1017fd5344069fe3028406f790c4318ffaa29901bff318c40d7fb26620dffd493003ff8c1a080bfc524c801ff30a6017ff94e21037fca79901ffe60d0403fa082202dff88341007fc629087bfe514c401ee31a4208ff19710147f8c0a0802fd64cc405ff192641eff54d3111ffca39881bfd53cc4037e3028400bf58831007fa86a0006fe60d0805f72168400bf587420077ec898003bd41104057f3166000bfd9310037f887980effe1050c01ff31a4000bfd8b10037f8c521803ff605082bfea9a4200ff98d41157faa0a081bfc32d0c11ffb2c822dff14341035f8c690823fc2190403ffa02800aff94f1003ffa85a081bfe6590c0dfb98a6206ff14d30005fac720843fe625002bfeb2a4200bfd9120037fccb9901fff415040fff2168606bfd9330037f861a18d7fd50508077f32e6007ff95341017fe419901ffc62d0011fe10c6201ef1014017ffca3a080bfc4288403fea024001bfd892020ffc21a186ffd658c405fea126435ff54542007fe631080bfc525080ffe2108607ffd074008f7aa8a0037ff514c001ff10e6007bf99041017fc64a1003ff615080ffe2008600bf58732097f8a5a0003fe414c031ff2806200bf59120157faa2a081fff541040f7e32e8007ff983421c7f8402180bfc42cc803fe1062029ff1494115ffc8120807ff30c400d7e32e6007ffd974300ff88188006fc6050c53ff192821fff9023103ffaa82180bff324840fffa168207ef9534003df8c988003fd410c403fc2028000ff8c530187fca09910efd65d0c017eb1c4202bfd8d32007f886880cffd54cc80fff3108201ff84120057facb8800bfc20cc865fe0866406f70c730017e842
  | 9 => 0x8be80300080206200400281c02480001001580111a80080900400201100400980400000780802a8000c78308040b783c01581087483780000500080002380000680680383f80104d02006a81d1db00000002100280b89a00080183081780080100a8008be8140020210208010020578000018078020000001a601e00b84180580200500000200d00004286800103a04900290d00280000000801080400280505705e00700308200281111801401c01d80408f00d0f600100a00080a01400107b0968000920098030010008038feb3180000100088c01984280080400292582281080000100005700180302780d8298010040c90070048048080000d985b80800005e0000000088c980381680009080001101600680481926680080608580480800001980400781603801700000600300000280280b810840007b7e95101f00d80002500180100280200201f80000ab7480100800281300c83f07700480080200680f01083a8340138f980504585584a0120000f90a081781200000080100580c00080001900201183900000000080080000400000080003116b81000100b80480200100000784e00080000700e00000300e8040c200938600102a00200300087a04104e00a1ee07200080480004801b80f00482180680080100581a007fd304400fff31e8412ff94b40167fe412081bfc6190c5ffea8e8208ffd9631005fac598007de304c001fe98a6023bf597311c77c802189ffe539040dfe1866406ffd8b3103ffca8a0007fe404400dff9966201ff04130007fa84a0103fc5190c0fbeb2e802eff14b4101df8cb2081bff314c013fe1962007ff90f40037b864188d3fe105087ffe10c8616ff0c2210d7fea818803fe634847dde2048615ff15121007fa82a0087fe40cc405ff90a6400ff58132035fecb9900afe6210441fe2146240ef552430e7fc8098803fe6444003fe186201fff10231035fcc688003fd214c00fff32e8200fbd8941107fe4118806fc60cc429ff2024205ff15110037f8a79801bfe538c479ff90a861effd4931007f6208801efe64c40037e3046207ffd0c41037b8879901afe63d08057e3168000ffd8d410f7f8a89880bdc324c81fffa8e6000bfd9121037fe649881ffe4210c01ff3226001ffc8130017fca490017ff52440037fb0a2003bf99532007ba6498817ff6544047fe2a6620ddf1953003ffe84a008fff52cc401ff20e6019ff148310cffe4218807fc5050059fe294820dbf59530007fac51881ffe61d0857fe1048200ff4c62116ffca1a0803fe4148419fe10a602abf595411b7fc21a1003df6348401ff21a4002bfd8521037fe879801afc63c4005ffa924200ef50941005dec4a081bfe31cc0017f30e640fff9473008ff8a2a001bfd620c4017fb1a8217bfd962100ffc809801bfc65cc487fe28e8606f
  | 10 => 0x8240118080059e880305d00400000001f00c00a83885b80000200d00582701c0aa01a00380500200000281f00e8028128028050df01980002400503181980000301988501181780182480400201800380b00d80400180200280107f80400100000083480a00800001580080480000000100100785600000e8008003260000059558008010d780100104304980280603282880000100b02c82680280100002e0000000000030020eb17a85080000080400080080100004c01480587180480101e02809f81380100e00800101c80100180080080002000280c02007f00080500002b00904d84b00680302f00002380d80002580002f80680600000000500e00007e07680400501400980100082000000301180309605c01200200780016901001281900003100d8498168008018000008000088130018030b780000000e80080402380081980fb6b00000300380381b0030b00002c580280007201083c00c89e00000000180d03202e80380300021680a07880b8460e58c600080000000700400002003100800e8000b702589d80400000003a00b10f86500c8000008008d802e8020018021c401780100a80080007500082080100000887b00c00580681000a812acd00d00104b03f80000880081701b05f8148dd11c0370000250121c487500400086c00580202200180b02380c00000181d00204680002f0a60050000008cf80100381300000780200002a01788508c816815a0780c0009828010280020040000028068e600080880600080d12c00800100180680001680580000784880300000000a0028820008148010
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc76cc54020ddf7359130037db6090d30036dc7518d41035de73d0930166bf6490521004fe764c910036dc7018d4131e7d30d953001cfe7558b30005f67110d21006bd6419120006ee6018941006bc53191210379e74d0f32036de634c91014f6d7518941006dd75d8d21005fb7050510014fc7650d32014fc7258043166bf42d912101cfe75d8d20044fe76d0f10006dd6318d41035dc7350431006dd634cb10004ff7650520044fe7650b10006df6390541044fe71d8d4003ebc6450d31006dd65d8d2102d7e7598d10036de76cc930036ec3258b310067c72d9510034fe76d8d42006df63cc940004ff7559330004fd74d8e21286dc4118d41006dd70d8d210067c72594411c6bd5019130174ff715912129edc40d8d4103ebc64d0530004fd74d81211c6bf201913003dbc744ca41075fb7058d20004fd7218540006bc64d853001cfc7558a31034fd70d8530005ed72d052100ff271c4110004fe7650d213567d30597400067f654c5300063f65d91300057d7510521046f62198732036f43158643006bc40d9121004fd73d8940004fd75d8542034ff7690f10044fc72d8f10105dc72d0e3106d7c7558930004fd7558231006f77158d212bf5c654c930004ff7558d2103ede6490d30026ec42d891031f5e30d95300057f7558121044fe76d0b100079c6418d210e4fd76cc710036fb3058243036de76cc93103edf4358c4100cfc7018543014fc764c931016dc62cc930014fe72d9110044fc75d8f10036dc6350d40007cf63d8941046f671986433267e43d95300ecfd76cc62101cfc75d81322477810d951000cfd74d8940166bd32d912129edf42d8d41044fc71583421c6bf6418d4000cfe7098732044ff759844301c7c75582410067e73d95101e6bd425933203cfe76d9110004fd729864300ddc7050f3003ebe73191210067f6599110387b55150441004ff75d8d10004fc7650d20006cf63d8941006ed53d8941005dd73d0731046ee2158a31035de74d0d3201cfc7558742004ff725913101cfe7558910034fe73d8940004fd75d9310004fd72d91300067c659911003cfc7458221004ff75580410067d65ccb4003ef44158443036dc644cb31004fd75d8543036f43158443036dc4358a4303edf7358f42006be10d9121006dc70d8d210069c64cc930006de6418d21006bd54d913230ebc3119130004fd74d8b100067c655893035eee54d894100cfe7690d40075ec7250730006de10d8d41006bf64505301defa30d814301cfc75d8d42044ff7598740005fb704c930044fc7598730006ef62905411a6fa60d8142046fb10580411e6ee62d8943006be50d91210e4ff7058d10046ec2158a311f4be761913000cfc7458740004ff764c54003ebc6410530005df7388730036dc634c941014fe72d8d20034fe73d8142006bc65d9121
  | 1 => 0x9130036be4359330004fd7598743395bf7550941005f97010d1003ef84058041036dc634c940194ff7258d20004fd75d853003cfc76d0930006ed71d8941004ff7359121006bc42d911010df77158d10004fd75584430079f64d0d3203edf4358f4000cde768c530034fc7358341015ee7290d4201cfc7558a430067f65d8d10046ee2158b10005dd7010e31046ef7258831006ec63d894103cfc764cb4001cfc75588410067f755822101cfc75d9121004fe764c52001cfc755804300cfc7059231004fc764c941004fd7688530004ff75582410077b65481102467c71d9510015de76d0d3214dee76d8941006de4218d41085f9709912000cfe7058e21004ff7558643004fd7610d20005bc7458910034fe73d8910006df635052102e7e76d95100067c65d8d10004fd768c520046df7358f1000cfe7650d3014cfd769922122f786548110036dc638c5211feee4258a4301cfc7559332006bc521913012fb7211912101cfe7558843014ff7158b10005ef7250d42006ef624c941286df4118d41004ff7650d20015de72d0f320075f6550d301dcff7059130015ec7250d42006dd5018d41286df431854301c7c755824300cfc7018542004fd7558730005ef7250431036f77158443006df2018d4100cfc7018532006df735923129edd6410e312467c20d9510045be7190541006df610c530104de7618d21034fc735864303cbc7458d10006dd638c510004fd70d854300cfe7648510005de76cc93100cfc7098742016ec62d093103ebc7319130036df7018d2103ebe6419131006dc60d8d21004fd76d0520126fa3058041004fd7098732006df63d8941005dd73d0b30006df6390d40036df7518d21016ec624c9313267c32d9530004fd7650d1000cff7658231016de62cc931004ff755913229ede54d8d4122ff25148110006dc75d8d2101c7c7559130004ff7058d21046ec2158b10004ff7358a412f5df7550d30006f950580310079f648c5300067e7159740006bc5019121034ff7658e21106de628c730006df630c5200067f7359740286dd64d0c3105d7c7558d20004fd75185200cede2018d2103eef4258b4331e7d20d9530004fd7650b1000cfe70588411feef2058a430067d6588740004fd7558e21034fc7358b40006bd53d912123df7715891015cfe76191101f6bf6490d40046ef7258b100079f64d8d212cede64cc931004ff764c91003e9c6490d30006fb7059120005f77158d42006dd53d8d41004ff764cb10044fc76d0b10106dc3258a31006df6398d420067c3259740044ff76107300e6f71058730034fc7358243006be54d9121004ef7259131006bd75d9130004fd768854003ef741584431dddd7490d3000cfc70d8931004fd75d814100df8705051003e7e43597402e5de76cc93012eef2058841046bc4159031034f
  | 2 => 0x6f56118520046f671d922103ebc64d0d21086ee42d8940006f77159132006bc6458121014fe72d8141006ec70d8941004ff73582211c6bc1019130006f461cc520006dc74d8d21016fa6248110006bd5119121036de630c51000cfc70d8d410057d751912103cfe74d8131106dd42d8d2103eec4258b41044fe71d894003ebf6150941006bc64cc521046fa1018520006df64d8d21006bd545824303cff76d0e21034fe73d8121004fd768874000cfe7359330016ec6250941006f47159132014fc7359332005ed72d0d3203e7c42594410057d759911003e7e7459740006bc2119130216ee3258b43006be51d9130004f7715913203cfc76d053028f5c650c530005f97090520006be75d9121014fe72d853014eec52d8941144fd76993103bf9e4010d32036de634c8410a6ed2058b1000cfc705874303cfd70185400067f2159740006df6398d21175f77159121046de3158c4135eef40d89412467e30d9510034fc7359110004fd7650d2101cfc7558b3101cfe75d814114eee42d8941006bd71d9130004ff7058a43046dc3158f10046dc634c62100cfc7359330046ec21588410067f655893003cfc76487400cedf764cb31027ea5248110006bc7458d21036dc63ccb4001cfc7558b10034fc7458743185dd72cc9300cedd2118d212467f10d95100cede3258831046f42118530036bc4359031167ae4258a41005bd740c540036dc6350d42006bf640c521116ef2158b31006bf6410521004df7358910014fc76cc5210067f65d8930007db704c930004ff7258043044fe76cca41005dc7350540016ec6288530034fc7648730144fd7650510004fd7558341044fc7518530005ef7259110006bf54d912100cfe7059031006df7359131005dd7290d30006ed50d89412467f71d951035eef41d8941004ff725834329edc41d8d4114eef20d8941046bf64d0621035de74d0c31034fc7358740004fd7098743006df54d8d41036dd7418d21005df7350431006df634c941004fd7559130006df63d812103ebf70191213567d20597403567f7059740034ff76ccb4003ebc751913003ef77158740036dc7418d41004fd76d0910036df30987320067d654c740016ec62cc910005fb70485101f6bc20d9130014fe7258f41035dc73d0431006bc301912121e7c65d0d300067f7558332035dc73885300067f21d9530166be32d9121006df735913201cfe75d8f10044fc7158332004fd76d0b31004ff755923129edc648c530036df3098643004fd71d91200047f7558221036df7118d41036dd7118d21036df608c530184fd7698d20004fd73d9121006f56118540286df4018d41004fd75d8b10005bd740c740037d7614c931006fb7058d20006dc5218d41014fe72d8543005f9700c54003cfc7458b310cede3218532044fc764ca410073c651
  | 3 => 0xe7498730274fe7619120006dd62cc6310067c62d951003ebe751913003dbc744c841004ff7558843004fd7558331166bf20d912100cfc7058b43014fc72d8d10006dc7358910006dc4318532006bf6410d21044fe71d9120005ed7290e2103eec4258b40036dc630c54038dbd7590541014fe725913001cfe7558b10036dc63cc9410067f6550d10046dc6398e21006f4614c53029fd571d0e31004ff764c52001cfc7558041044fe71d8b10006be75d91301ee7c6550d10386bd6550441005df7350540014fc72d9131004fd7218543025ec7258d1029ede74d8d41036de6318d100067f74d9530006df63d0d10004fd75d894103cff765931001cfe7558031005dd748c530006dc1018d41014fc7458742044fc7218530006f7715913101cfc75d912000cfe70d8d101b6ef20d89401c6bd3019130006dd75d8d41006ed63d8941006dd32583311fcfe7619132004fd70d8931016dc624cb31036fb705833101cfe7558d21004ff7458a31004ff7650431006dd65d8d41005f57110e21106dc20d8d211c6bf5019130166bc52d912106e7e76d9530016be6250b410057f7558d40006bf64991300057f755853003e7e40594410fef51098730006df4358a31006dc2118d41016ee624ca3101cfc7558342005bf74487400067f7558031025ec7259110166bc72d9121004fe76d05200eeec42d8931046f81058031166be42d922103cfe74d8e21286dc5418d41006dc6418d21004ff7158b4003ebe6419121016dc764c931036ef3258a430075f654c930004ff70588310cddc724c431016ee61d0a2131e7e70d953001cfc75d9132036dc43588313267e73d95301f6be30d9130004ff725874018e7e654c8411367f7159441036dc43593320067c7558d2003cfe74d8930034fc7358841006bc6488530006f77158d10317bb30d9130004fe7610520004fd7650910004fe7610d20044fc7598443005f471589300067f7059441006be601912135eec41d894100ddc708c530004fd70d9231004ff75d91301f6bf10d9130044fe7690e21006bd54d9131006bf64d0521036de7218d41006bd50d9121014fe76cc521015ec72d0621036dc6310d10004ff7159120004fe7610d100c4fe768c51001cfc75588431feec2158a43046ee2158841045f47150e41006de32d8d41006bc64d8d2100cfe7458b40014fe72d923101cfc7558b4303ebc73191212addf758c530004ff7059221006df20d8d41016bc765094112ebf7650b4129edf41d8d4101cfe7598743006dd50d8d41007b47150941006f610d85322f5dd7550d30005ef725054030ebf321913000cfe70d9132006dd32d8131006ef63d8941037d66110e3100dda708c53035eec43d89412ff9d5490d3000dde704cb30005f77150e41006df7359110014fe76d8941146fa60d81410467e3159441
  | 4 => 0x8d2102d7e7599110004ff755931001cfc7559310034fe73d922103efb4058041005f9700c52012ebe4218542005ed7290d20006bd5458643034fe76d0b31014fc7258740004fd7518530006f7715912100cfc70591312467c70d951000cfe7059332004ff7558c4101cfe7558c41004fc7650910016dc62cc93101cfc75d814300cfe7358b3014dbc7650941006ee651894100cfe76d8143004fd74d8930006bc644c530266dd30d8d20044fc7690f10166be429874203df67190541006bd54d8540014bc7650941006dc53d8d40004df735874012cbf7650b41005dd739912101cfe75d91200047f7558d2001cfe7558d20046bf7459031035de718c530004ff7058a31047d651cc6310ceee4258831007cf6388521006de30d8d21006ef62cc941005bf74485400a4fd7648510045bc7150b4101cfe7558f40006dd6418d2100cfc7058f420eddd72cc931004fd7318542006be72d9130036df7418d41004ff75d9121005bc7458132196fa20583320079c6390541005df7348710044ff75d8e21006df7358d21006df32d85300067f65d0d3003cff76d0b30006bd6450b10046bf4198742004ff7648540036de6318d2003ef74198740006ec10d8941014fe76d8943046f6719873035eec54d8941104fe7618d21034ff70d9130004fe769053114ebd42592211c6bd2019130004fd7498730006bf6450d30004ff75d854329fd671d0e31036ec3258a43006bc62d9130006bf7459132004fd72984430cedd5218d2103ebe5458740004fd72d8f10044ff72d8d2101cfe7558f41017ae74d0a210ceef205883100cfc70d8e2126edf32d8d20004ff7458d20004fd76d0930035dc735053014eee71d8941004fe76d0d20004ff76507300057d7510510004ff7358341006bd64191310cedc4218d210079e53d913003cfe74d8532006df5018d41037d7714c431004ff71582433567c705974003e7d7459740234fe76885100057f7558910046de7398732034fc7610d210de7c658c530004ff7059231006ed52d893101cfc7558231004ff7058b41367d5514c43101cfe7559121107cc21d8d2130ebc3219130004fd7690e21034ff7359330036fb3058043006df63cc51031e7c30d953003ebf7219121006dc735874000df8704851003f9c4350d41005dc7350621006bd5458443005ed72105200079c63d094135fae64d0a21114ff764c6210057f75581310cedf5218d21044ff7690730044fe715903100dfa700c540035de7350b3003cff76d0730014fc7358332044fc764cb10044ff75d9221004fd70d8943106dd72d8d211c79e3019130004ff755884103ebd70191210bd7c7558221004fe7650910034fc7650b3000cfc7358b30006de51d8d2103ebe731913003ebd7319121005f47158d20006df764c431006ef54d8941006ee73d894103cf
  | 5 => 0x1cfe7598732006df6398d400079f63d0941004fd71d8d20005df735053003e3d7519121044fe71d8930006df6350d2103cfe74d8132005dc734851000cfc7058a41005dd71d0e31006df50d8d4103efb705834303cfd73d894308d7c7558540006f5611854300cfc7650d40044fc7159130007d7618c530045f47150a410067f6590510006f47158d20166be21d9121006dd63ccb10004fd7650b3101cfe7518540004ff75d8943166bc21d9121036dc634c51000cfe70d912100cfe76d8131006de5218d4103dbf75d09410067c71d95301f6be10d9130036f7319873214eec32d894113e7c6590510006bc51191300057f7559130006bf64d0d31014fe7218530006bf72d91300079d64d0e31005ef7258141005df7350621006df5118d21005dd720c53000cfc7158f10035dc735083103ebc6450510005ef7250531004bd74d8f1004dec7250710034ff7610f10006bc10d912100cfe70d8543166bf32d912114eec2158742006bf6499120146f71058740034ff7650e41004ff7648740006bf2119130004ff7458732256f52118520067cc624c93003dbc72d0641006df75d8d210067d74d953003cbc7458910005ef725062112ebd2119121014fe7258241006be5219130036f7618c531014fc7258343006df63cc941005dd74cc93035eed64d0a21047e42190521005bc7458532046ed72d8e21004ff7650f10006f7211853001cfe75d894000cfe7058e41037d6710c530007ae54d8941014fe7258d100ae7c6548530036df6210d320067f65d091000cfd71d8910046bc649923118e7c654c910335dd758c730014fd701852000cfe768c530004fd7690d20006bc54d9121005ef7250530005f7714c841036dc63ccb4101cfc7558f40006ed73d8941004ff7258730036be43590311be7c65d0910044fc7650a31016ac625094100cfe7018542046dc6398f10004ff7258643034fc7358a410067f654c910006ef62885400079c6450d3000cdc7650d30004ff7358910004fd72d8d40044ff7518530005fb704c530034ff7610e21005dd744cb30045bd76d0641014fc7258341006ef50d894103eef42588432b6de644cb31004fd7558d2003cff76d0d21006fb5058331004fd7690f1003ebc64d0531044ff7518540006ec7258d10066ec6258930006dc21d8d413267f31d953000cfc70d854303eef7258b40014fc7258e41036df7518d4103cff7650521004fd7558241014fe72d9310034ff7158f10004fd70d8941004ff7258e41006de4018d21006de6518d212467e10d9510044fc768c520034fc7690d20044fe71d9310006de42d8d41005df704c4310073f65191300075f650c530006dd618c7300057d751854200ff361481103567c3059740004ff7258f40007af62d0941005fb7050d40006bd54d814105d7c755852000cfe705
  | 6 => 0xa700c520004fd764c740037db608c530047e4210c521006df6518d21014ec7258d102467d70d95100067f658c530004ff7259110006ef72591310067e7259441036de63cc841007af725044100cfc7058e41046be41592310067e32d9510346df764cb30005ef725813130ebc5319130004fd74d8d102467f70d9510004ff7058b4300dfa708c520004fd755912101cfc7558730166bd20d9121004ef7259110034fc7358241036bf745933103ebf711913013d7c755824100cfe705913229ede648c530004ff725903103cfe74d8520004fd755803103ebe641911015efa2058241006bf644c521046bf65d0641014ec7259110004fd7559332046f44198740005dc7358121006dc32d8d41006bf6490d21005dc7358540007cc6318941044fc7158a31014fe72d9131036dc63d0e2100cfe70d91312ff5c6590d30004fe760c540016bc6250941014fc72d8543006ef70d8941004fe7648540006fb50d814300cfe7058b4301cfe7558b410047d7518542004fe764c540166bc32d91210cedc3218532004fd74d8532036bf7459330006cc6318941006ef624c93014eee52d894103cfc764cb41004fd76d0431046bf7459221045dc714c93100cfe70d8d421e4ff7259132007f37148110004ff7650910036dc6390d41006ef7259221014ff70d8d20006bf649053003ebe71191300067f72d95300b4ff7258910006f421d8543005fb7050d30005dc7350520227f151c41100069e5418d41036f73198643006df6390d41034fc7610d202d75c65cc930004fd76d0d21045de718c531034fe7398740004fe7650d10005df7350531046bc6459310006df2118d41005ef7258530004ff7558b4301cfe7558041004fd7558643006bd5458043044fc7159231006bd64d0a310079e54d8d4101cfe75d8540046ec2158831004fd76d0b1001cfe7598443006bc40592310e6dd3058f100079e5418d41036dc3158331006bf64991320079c7350441014fc764c521044fc71d8d10044ff7518520006bc4259331006bd70d91211b5ef7259120006bc645893001cfc75d8d20295dd750c5300047d75d8f10005ed71d0a210067f7259740044fe71d8943004fd755834312ebe2019121004fd76cc740004fd76ccb10005bf7448530006bf644c9302467c40d9510004ff755873000cfc7058d21036f7715873201cfc7558d200079f639054100cfc70d8910006dd624c431047d6614c431014fe7218540006dc5118d41005dc714c930036f43158730036de63cc91003faf7250b41015dc7210d32006bf64d09301f6be70d9130036dc3258831006bf50d9121186fa20d813200dfa708c530004ff7650530006ee43d894103ebf7219130006bc64d8930004ff75d893003e7d4259441005ef72505200057d7510730005f7714cb41004fc7650931004ff7258341
  | 7 => 0xd400379e7410e31004fd72d8d10005f972c4110006df639052103ebf61d0941006bd6419121004ff7558b31004ff7258f10006dc40d8d21004fd72185301f6bf6498d40005ed720c520006bf73d912112ebd52191210067d658c7400057f7558540014fe7298730005bf7458931004fe7690d20006dc5018d4103ef74198743004fd70d9132005f9701053001cfc7558732167b421d912100dfa7010d2003cfc745823103ef741587430067d65cc740006bf649911003ede6450f30036dc7518d210079f7350441004ff7058c41004ff7358b41106de628c53101cfc7558f41086ec21d8940004ff7158f40006bc51d9121005bd7498d210067c75582412477771d9510005f77150d31004ff7358740106dc628c5303afb551d06412477a20d9510026ec6258910044fc7158f4003ebc64905203567e2059740035df724c930036ec32588311e6ec6250d410067f6548530006df638c540006be6519130004fe7610d2100ddc700c530004ff7159130035dc734873027ebd42d912003ebc72191212cedc64cc931016ec624c94100cfc74987400069c648c53014fac6250941006be32d913001cfe7558b3100cfe705883103ebd76d064101cfe7558740007eb6248110166be52d912100df87050d40036df614c9310cedd4218d21044fc769052001cfe75d8d41046f42118543006f77159110004fd75593310067f65105100069c6418d21004fe76d0530006be54d9130035de7310530006be71d913023ef710d8520006bf6450510046bd741854212ebe425884101cfe755931000cff72d8d20106dd32d8d21004f77158d200d67c650c510034fc76cc520006df7358d20006de52d8d410079d53191300067c6518530044ff7598742005df73592211febd42d9132006de50d8d21006dd768c730004f471591320067f650c5100379f7450f30046f44198743006dc635814112ebf52191210047f755891014eef21d894100feb7248110014fc7259031045f47150831034ff76ccb41004ff705864301cfe75d9310046dc63cc6212477471d95101367c6510510016ec6250940004fd75d8d2001cfe755884103cfc7458831006de10d8d21004ff7650b30006dc63d8121006bc6519130046bc6499221046f44198742037d761cc9311c6bc5019130044fe764cb10006bc648c521014fd7158b10016de624cb3103ebf4158841044ff7258841006bd53d9130006bd73d9121006be5459231044fe76d0a31006bf649853003cff76d0d1000cfe7058843215de7410d32034fe73d9120046dd7318532036ef32588310079c644c93031e7e20d95302b6df4358a43044fe71d8d20046ee215883101cfc75d8931036dc63cc94037f9d5410e310067e62d9530004ff7358b4001cfe75d8132006dc65d8d21006ed6518941005df73505200067c755833200df
  | 8 => 0x7af6290541046bc6499310006bf7459120036f73158443106df71d8d2101cfe7558a43004fd7610530044fc715922103cfd72d8542005f771591320067c7359740004fe7619131086ec6258940006df7359221006de7618d4103cfe76d91210067f74d9510004ff70587321e5dd73991320067f6510d102467d40d95100079f6418d2101cfe755804303cfe74185200067e62d9510016ee62d0b3103ebf75191210f57c755813103cfe74d8530034fe73d9110105de72d0e31006bd5459031014fe72593311f6bd50d9130006bf64d05300067c6559130005f47150d31044fc76ccb100067c6518d1003ef840583431f6bf20d913014eee76189412467f40d9510006ec51d894100cfe70d9221006bf5119121044fc7598732034ff7258843006bd51191301d67c6510d10036dd76cc6310369c4359332034ff72d91321defa60d814329ede648c531046fb1058221005dd7310730006ec50d894101cfc75d9131004ff764c94030ebf3119130006bf64d8530004fd76ccb40165bf7450a41035df7450d300079c640c53003cff765922103ebe645073103e7d415944101cfc75d891003ebe5458341035df724c931007d9708c53019e7e65cc84129edc648c53100dfa70cc510004fe7690d210067e42d9510166bf21d9121106f52198732036df3258331036f83058031046ed72d9221004ff7259310015ee720c520034fd70d9130046f6511853203cfe74d812101cfe75d8143046bc41592310067e7359441105de7210e31014fe76d05210067f6518d100067d6548740004fd71d8d42005f970105202467f20d951001cfc7558b4129edd64d0e31044fc76d0e21006df53d8d40005dd73d073006d7c7558530014fe72d8143006be6519121006be545933201cfe7598643046bf6190541034fc7458b43036dd7518d2110ef710d8530036dc628c730006bc75d913000cfc7059121316bc31d9130005bd74cca4103e7f4359740014fc7258d100eeec20d8931006cf63189410069f64d8d21014ee76d8941044fc7498742004ff75d8d42007cf6318941124fe769051000cfc7650d3003ebc64d0d30035df740c530006f410d8532044fc7650831044ff751854303cfe74d8f100ecff7258d2101cfe75d8142006dd53d8d21004fd72d8540166ec6290541106df42d8d21004ff7258241006bf6410530004ff75d8931004fd74d8910006ef625814117e7c65d0510004ff75d81320067f65d051001cfc7558d21395bd755094103ef74198742004fe764c941006dd5418d41066ee32d8930004ff7558e21004fd75d8142006dc51d8d41014fc725911003e3c4259441006bf54d9130006be531912103ebe6450b101a4ff7059120036f77158730004fd7558d21006be60d9121007db7050d301b6fa2058342005ed72cc5211e6bf4259332036dc639
  | 9 => 0xe72984430057d759913000cfc7058a43045dd76cc63101cfc7558221006ed6318941005bd74cc841006df32d81310067c42d95302cedd64d0f320067c7259740036ef7258b301f6be4058243045bf71504411def850d8143004fd7688730004ff75d8143006bd54d912103ebe64d0e31004fd7558b4135eef43d8941316be73d9130166bc4258a4106d7e7599130167b721d91210067c7559110004fe76cc910046ef72588411f79e4090d3000cfe7058c41034fc76505310067f6518530035df7650f30014fc725923105d7e7510520004fd75d8143036dc648c73000dde708c5301f6bd40d9130044ff75d9310036f7315864303edc7650d30006bc50d9121014fe72586430067c2059441046bf6499231036dc6390d42004fd73d85400eddc764c93100df87050d30146fa10d8141006ed75d8941006df630c521006dd54d8d41004bf7458d2001cfc7558910004ff72591301c6bc30191301ed7c755814314cfd7650521004ff7558342046f81058041044fe71d8f10046f71098730006bc53d9121005bf7458131186fa60d8132006dc62d8d4120efa30583433567d705974003e9d7319130006ec30d8941036fb7058332006bc52d9130006df7358740006ec631894114dec7258141045df714c4310f57e7510531004fd7598643006dc6018d2101cfc75d911000cfc7058a31016de624c930035dc7350731044fc72d9310287d44118d41006bc42d91310467d7518542007af4250621006df6310521036f83058331004fd7558743006de70d8d2103cfe741853200cfe701854329edc54d8d4103ef44158740006df6518d410067f6598d10006dc50d8d41004fd75d8930006df21d8d41014fe72d9120006dc6350521004ff7558740014fc725931001cfe7558331014fc7358732004ff7359310006dc70d8d41164fd72d912110cff764c71001cfe755874201cfe75d8b10014fe7258740166ec42d92210067c6598d10196ef20d8930044fc7158d20006f721d854301cfc75d854000cfe7498740044fe7690f10236f510185200067f72d951001cfe7558b432b6de644cb30004ff7558031006dc53d8d41036de61d0e3101cfe75d8d4203cfe74d8d1003ebc6410520005bc7448510034de76d8d21006f56118532006dd6518d21006dc6218d41004ff7558b40004fd70185420075f6590d300075f65cc930015ec7250d32004ff75d91321f6bf40d91300067c7558910004fd7558c41006be42d913001c7e75d8f10006ec53d8941036de7418d4131f7830d953006d7e7510530004fd760c520106dc72d8d2100cfe7158b10005bf745853000cfc7058e2101cfe7558343004fd72d8143116f621d853200cfc7058443106de32d8e2103cfd70d8d4003cfc76d0931006de54d8d21006ef7258d21004ff7558d1000cfe705922103fb76150941
  | 10 => 0x8110005fb7050940014fc72d9130005df734854003cfe7418530006ed70d8941034fd74d8143005dd73d08312cedc43d8943006df6310e21004ff705884100dfa76c4110004fd7610d213aebd65d0641005bc7458d200067d75d8142006df6310d21014fe729874000ddc7090d30044fc76d0f10006bc64d8121004fd7558740105df734ca31005bc7448730004fe76cc5200067d7059441004fd74d8d21006df65d8d410c6fa20580310067f6588510006bc21d9130034ff7658f10006df4318532006bc54d91300473e655044112eec4218542004fe7650530004fe768c520004ff7650d21014fc72d814139dbd75d0941014fe725931001cfe7558b400067f655913003cfc7458e21034fe749874301cfc7558c41006df70d8d210467f1059441106de42d8d21046f62118542035de73d053103edd4358343144ff7059110046f62198742014fe7650d32004fd7610f100047f7558241004ff7558e41106dc52d8d210be7c6588510036df3158831006be621913000df8704c530014fe725873003ebc64d0d3201cfe755834108d7c7558d40126f51018540005ef72507312477610d95101ae7c6550930004ff70593310067f65cc91031e7e40d9530034fe76d8d20006df74d8d41014fe7258f4003cff76591202467c10d951001cfc7559221005df7348740044fe71d9132006df6418d2103cfd72d81421e6ee32d8943037d661d0c310067c655853000cfe705923110edd73d853016cff7159110004ff764cb4100cfc76505100efcc624c93119e7c65cc910004fd7558742004fd72d8141006bc648c530006bc6418d21005f571d0d31036dc63cc510047e67188521016ec624851018e7e654cb401dcfd7650d3022fe95248110014fe7259330005dc7358910004fd76cc940014fe7258c41006f7211854301cfc75d8d41006bc30d9121004fe76d0d31287d74118d41005f7715894331e7c73d95300067c74d9530044fc7518540006dd5118d4100cfc70d911001cfc75d812100cfc70587320eeee62d8931006df63d0521006df6358141036ef3258843006dd50d8d21005dc7150f30106df20d8d21006bf651912100cfe70584431dedf3058f40046f4618c530006df4358831014fe76d8940005bc7458930004ff7558b411f6be50d9130006dc30d8d41035de73d05300067c21d9510006be40d9131004ff72582312b6df6410d3200cfc7158b10044fc7650f10006bf6519130037d83050d30116ec4258b31004ff76509300ecfd7698e21004ff764c74003ef74158740034fe735903100dde700c5300073c65d9130006f7619854200dde7050d30006de74d8d21214ff735913201cfc7558743037cf6210d32006ef65d8941044fc75d9310036dc63d0d1000cfe7058f42005f771509411feee5258a430067c755803103ef77158743014f
  | 11 => 0x4fd70d8542004ff7258041216de76d0d3229edf40d8d41014ff70d9120006bc64485301e4fd7650d32006bf70d9121006ef6288530107ce3258a3103ef761905410b4fd70d8910005ef72506310067d725944100cfe70d8e21036de6318d2101cfc7558331006ee20d89410079c64cc9300ad7c755812101cfc7558a411f6bd73d9130165be72d0641014fc7258f411e6ee42d89430067f73d951029fd741d8d410067c6519110006df618c530006df7358d1001cfc7558643046f67198743006dc735911003cff76d0a31006f610185320067d715974000ddc704cb30014fd70d8d20034ff7690d202467d20d9510006dd6350e41006ed51d8941004fd76d0d20006bf649912101cfc75d8941034dc73592210067f7259441005f471589430cfcc2118d2100cfe7018532006bf64d0d21036fb70580431f6bf50d9130046bd74d8f10004ff75d8940006ef624c931164fe7610521035df764cb311f5be761913000cfe70984430067c6519130044ff70185302b79c4010d32014de7398732014fc7258231037d8304c930006be40d913203ebe7519121006df7359130004ff715933029edf6410e31044fc7158b300cedc2018d212c5dd754c9300cede620c530006de5118d21004fd75d89401fedd73d9132005f57110d21046ef6188521006df638c520005bc7458931046bf7459310005df73591100067f6590d100067c32d95101c6fa1058043044ff75d8f10004ff7558331014fc76d0d320057f75581320067f654c510044fc75d8b10004fe7688530036df7418d21006bf6488530044fc7598643014fd70d91200f67c654c510066ec21d893000cfe739873031e7d10d9530014fe7258331217ce72d0d32006df54d8d211c6be2019130005bd74cc940014fe725913103efb4058343004ff7559130014fc72d81432067c6590d1000cfc7059132005bf745852003cff7650d32035dc7350631014fe7258343006df6350d42004fd7648740005bd74ccb40005f97090d40004ff7258f410a6fa10d8121106de32987320067e3059441036ec3258843036bc4359332034fc7359331046bc6450621006ef62d09101dfd87050d30044ff7018520316bf32d9130006bd51d912103ef84058043005f671d0d3103e7e405974000cfe7058b3135fe441d8941004fd7558e41046fb1058231085ec725054003cfc745803103ebc6410d20006de2018d41004fd70d8d4215efa4058241004fd7558732005df735073129edd76d0e31006ef6318941006bf75d9121006bf6458121015ee7210d21034ff7658d2035fe741d8941004ff7058a41006bf531913000cfe76d8141176ef6118941004fe76d093029fd441d8d41044fc7518520006bf64d8d21047d661cc631006bd645073100cfd72d85202467d30d9510005ef72591311f6bc10d9130016f8764
  | 12 => 0xe76d0531006be70d912103cff7650e31004ff7558243004ff715833200cff72d912031e7f70d9530215df7359132005bf7458d21036f43158732004fd76cc520005dd7110d3214cfd76d0621044ff7598732006bf648c521004fd760c740195ef7258d20044fc7159120005ef725052101cfc75d8542005df7250d30046dc6358e2103ef441587421fdde7610d320067f6558530004ff7158043016ec62cc941036df64d0c31036dc43986431ceef2158843014fc7258730006be545931001cfe75185420067e735974000cfc70d8d2133ddf754cb3006d7c7559130006bc7458d20005df748c53001cfc75588310067f75591101c7b83019130004fd74d8d20046be4159310005f970d0510004ff7058f41004fe76d09310079c6490d30004fd75d8532037cf724c93114dec7258d410067f65d9110047b65150441036df61cc931106df32d8d21035de74d0e3102e7e71d95100ccfe768c521014ff764ca311f6bd20d9130006be545922100dde70cc930006de20d8d41036de6350e4100cfc73d8131034fc7690d10006ef53d8941035dc74cc631034fc765073000dfa70d0d30046be41592210067c65d9110036de6318d4003ebc64d0d31006bd72d9130106dc628c531035dc735053101cfe755822103cbe76d9121014fe72d8131036df3059031006bc6019121036de7018d21006dd6318d21014fe7458342004ff75d8131036df62d0d32014fd7458b40044ff75d8b10046bc64592310467e7159441044fe7610e2101cfc7559110014fe765052100cfc76cc510006dc10d8d210ceee5258831004fd76d0d10034fe76d8d21004fe76cc9410cdec72504310d67e650c7400e4fd764c51003ebd7319130004fd7559221004ff764ca41014ec7259131035dd76d0f32014fd71d8121005df744c930004ff7458e21004ff7458221004fd7598730006bc75d9121006df70d8d41007d7714c9311567c6550530005dc734871000cfe7059121014fe7258231106dc21d8d2101cfe75d9231006dd51d8d41006bd64d0b1001c7e76d9530005ef7250d3235eef71d8941037cf724c930006dc54d8d21034fe73d8540004ff7650d100a4ff70589103567d1059740006bf53191212b79e5410d32014fc7258f10006f7610c520006bf644c5300073f65d9130004fc7650930045dc714cb31046bf6550441006bd6519121316bc32d913001cfe755834201cfe7558a41005dd70d0d32004ff7650b1014dee7298d41006f7619853014ebf425922101cfe75d8d21006bf64cc5211f6bc73d9130006dc10d8d41005dc735052103e7d4359441006ef62d0931006f76198543005dd728c7300067f6519110004ff7558a43044fc7158b4000cfc76d0d3001cfc75592310fedf30d8d101f79e30d9130014fe7259231036fb30583320fefa30582313b5bf7550b41
  | 13 => 0x9120006f551d8532044fc7518532034fc7650d41006bc6418530107d421d8d2101cfe75591100b6ef20d89102dddd75cc930004fd7650e2130ebe531913001cfc7558d10004fd755822103cfe76ccb41035de73d0b303779e4010e31004fd7650b30004fe76d0d10004fd75d9231034fe7318542006bd5458740006f7619853203ebd7519130004fd7650d20006f46150540004fd75d9120005ed7298d4103cfc7458b10004ff735834203e7f4259441006ed5258a430067c6559110004fc7650d10036de634cb100057f755822101cfc7559131005df7350521006be7619121165be7619121006ef73d8941035dd76d0c3100cfe70d8532006df6390d21007ae541894103e7c40594411feec6290d41006bc6498d21014ff7658b10034dc7358910006bf6450d321f6bf73d9130004fd7610520036dc7218d4100ddc70cc93003e7d425974003eef4258b41034fe76d0730006bf21d9130004ff70591213567f3059740036dc6350d21004fd7558b30106dc32d8e211e6ec21d8943106de72d8d2103cfc76d0d20044fc7688540006df634c52103ef741587420067d654c841006bd5219130035dd768c730046df634c62103edd435804301cfc7559031014fe735933201cfe75d85431a6f8605814200ddc7050d30095fb705912000dde768c5300073e75191210079d5418d4131e7f73d953001cfc7558b300067f65191302b79c64d0d3203dbf7650b41004fd759844301cfe751852003cbe74d8f1003cff76d0b10004ff7159131045bf76504410067f655093001cfc75591210063d6550441014fc7458f4210ef850583310069d5418d4100cfc7098643044fc7158241014fc725844303cfe76d9130044fc721854003eec4258841004fe768c540046f671d9231005fb7050540005dc7359121006bd6450e31006df53d8d41035de73d0a31044fc769053001cfc75d8532034fe73d814100cfe7098742006bc51d9130065ec72505300067e1059441004ff75d91311c6be4058043004fd71d8132005df7350631036de638c51003ebc6490d200079f6450d300eeee32d8931014fe725834101cfc75d8141017e761885210467d75d8f10014fe72d8d41005f471591320067f21d9510005df7348530036ef7258a43036dc439873203cfc7650d31004fd71d8930006df50d8d2100cfe7650510004ff7258331004ff7259331006dd634ca41005f7715813214fac62d0941005bc7458530005df7388530004fd7418520004fd76cc94131e7f30d9530004ff7559331007b77150941006bf52191300eedd3258e21044fc764c84103e7c4259740005f7714c931007cc6388521044fc7158221014fe729874331f5c30d9530015ec725062103ebc645052101cfc75d8530046de3158f10046ec6258b10106de21d8d21006be52d91302a75c658c530034f
  | 14 => 0x7ac7250441036dc315844303edf7358f41004ff735874212dac7250441004fd7598742006df5118d41006bc40d9132046df6398f10045fb72c41100c6fa4058031004fe7610530004ff7158342044fc75d9231106dd20d8d21005dd7010d32034ff7610d21046df6398e21044fc7298730006de1018d21007f0714811003cfe74d89100057f7558d10005df7358520316bc53d9130005f4714cb41036f77158643006ef7258d2000cfc70d8d42006de75d8d41004fd76ccb41006be5119121004fd7690d21004fd73d8520046f970d8f10036dd7118d41166bc6290541014fe73987320c6f5101853003cfc76d0520004df7359110004ff7258243006dc51d8d21015ec724c5210067f655053003cfd73d8143004ff7559131006ef52d894100df8705054001cfe75d9132015dc72d0d32026ee62d8910006de5018d21016de62cc930046f86058231006ed6250a41014fc72d8d41006dc6518d2100cfc7098743004fd70185320079f644c930005bd7290541006df75d8d41046f9701852000cfe764c510006dc52d8d41004fe760c520036f73158730005dd73d0930046bc4159221006bf53d9121015ec7250e21034fc7359221005df73508310fcfd70d8d10044ff72d9121004fd76d0e2112ebc2019121006dc6358941006df72d8d4100cfe70d8941046bf6499221005ef7258d4103edc6450d30046f43198730004ff7458d21046bc415931003cff7659231014fc7259131004ff7258c41006df74d8d21006df5418d41014fc72d8540106de52d8d212467e70d9510034fe73d9310037d7618c53101cfc7558b40036de7018d412cedd76d0f3203efb405804314eee32d894103ebc64d0510005f77150e312b7cd72d0d32004ff75d8941044fc7159031006dd5218d41004ff7558332007af74d8941016bc62d0941004fd75d8d210067d71d9530004ff715933234ddf7550f30046bf6499310166ac6290541004fd739874203efb7058342036dd7610e31006bd6419130036dc7018d21007ad54d8941005dd70d0c31005ef7250e21004fd73d8141036dc638c540006bf645053100cfd721852003cff76d0910006bf6458930006ed54d8941006be545911014fac21d0941286dc4218d41004fd7610e2100cfe705873203ebf7319121044ff768874003ebe701913003ebe645083103cfd715931003e7c7459740004fd7558f42006bf64d893000cfa76c41100067f6559110036df6050d3011d7e7510731006bf511913020edf30d8d40036de634ca41004fd72d9110006df5218d410467e415944100cfe76d8121044fc7159332045f4714c84100cdc764c9301e6df3258f42016ac62d09410067c7359441166be20d9121044fc7158e21005bc745813101cfc75d8d21005f970d0d30044ff701854003ebf7519130015ec72505201a4fd769
  | 15 => 0xe40d8941036dd7018d41035dc7350a31045de71cc931166bd52d912115ebd40d9110004fd73d8b10004fd7558910046f970d8b102b6dc644c93011e7c65cc510166be72d9121006f421d85301ad7e75d814216df771591101f6bc30d9130004fd70d8d41036dc3298732005f77150a41126fa2058041006bd64191320067c6558910046f44198443004ff7458b31004fd72d853029edc42d8d41006be54d9120006df7650f30004fd75593300067c65991302467d71d9510005bc7448710006dd52d8d41005dc73505100467c4159441034fc7358041015ee7290d20006be54d9132006de5418d21006fb50d8141117e421cc521034ff76cca41004ff7058e41005dd70cc631005bf7458132004fd76cc841006ee53d8941004ff75d812101cfc75d8520006be65d9130164fe7619121104de76cc931046f71018520014fc7258c41006bd5459231006dc6518d41006be3019121014fe725803100cfe70d923101cfe75591320067f65d0d10006bf7458910006dc6390521166bf52d912122ff15148110004fd7418530005bf744ca4101cfc7558343004ff75593320075f658c530005f7714ca3121e7c65d0d10006dc63d8141034fc7650b3102d7c7558910006bc6458d21004fd75d913019e7e65ccb40004fd764cb400467c3159441036df604c93003cfc76d0d21006df52d8d4103ebe7219130004fd768c740006ef7259121004fd7558f100079d53d913015ebf40d9110006de60d8d21036df3058a43044fc760c540006de31d8131006be42d911000cfc7058831014fc72d9110004fd72d8543006bf75d9130005de71cc93001cfc755803101cfc7558e41004ff75d814201cfe7559120005de7190d30006dd634c910004fd70d8e2100cff7658241046de614c43103ebf7319130006bd54d9130035dc7358a3103edf7358f40004ff755911012fac2119121004fd76d073027ebf42d912035fe671d0a21004fd75d9131034ff764c52103edc4358f4203e7d4159740044fc7398732035de73d0731006bd6519130106df21d8d210067e325944135eee6488521146bf4059310006bc65d91300fdde710c5302467c30d951001cfe7598740014fe72d8d1003cfc76d0d10007cf624c9300ad7e7519121046dc3158e41044fe76d0831005ef7258540006bf64d051001c7c7558d20166bd71d9121035dc7388730014fd70d8520114ff7158d21045f47150e3103ebc6410d10016de624cb3003ebe64d0b10004fe7650d20006f76198520046dc3158e21044fc729874300dfa71c41101f6bc50d91301febf42d9132005f67190d4101cfe75d8542006ed52d894103cfe76d913200cfc7059332044fc72984430057d759912003cff7650510036df7218d21004fd755923103cff76d0f100079d54d8d41005df73581410edec72505311c6bd1019130
  | 16 => 0x8d41006df5418d21006fb50d81210be7e6588740005ed7290d4200dfa7010520006bf64d0d30046f71018540004fd70986430f67e654c740005bf744c841044fe71d8132166ee4258a4103ebc6450d2103cfc764c740044ff768c7400a6fa1058b10044fe76ccb1000cfc7058f41044ff7518542006ef62d8141004ff725803103cfc76d0910004ff7058e21014fe7218543004ff75d8532006bc645853001cfe7559330004fd72d8d413b5bd7550b41006dd54d8d211e5ec725854300ddc708c73031e7d70d9530006ec60d8941044fc7158a41036dd7018d21006bd51d9130004ff72593300067f65589101c6bf3019130004ff75590310ad7e7510521006be40d9121106dd71d8d21034fc735891031e7c20d95301ee7c6550d3000cfe7690540005f970cc510004fd7559110014fe72986431f6bf70d9130036de7218d210cddc72d0c3103fb761d09410079f640c530004ff7458831004fd7418532004fd7518540005ef725051003e7e425944101cfc755913201cfe75d853203ef7419844301cfe75d8941004ff7458231006ec65d8941006df6398d20006df6398d41044fc768c54000cfe7059131004fd7298740035f6718c5310fcfe7618d10115f77158d21004fd71d9130004fd7558342104fd72d8d210067e74d9530006bf51d9121046bf7459231006f5611853000cfd72d8d20046fb705803101cfe75584430067f7558243006bf7459121004fd7690d100067f2059441005df7359121004fd7650730005de7399121044fc761053003cfe74d8d20004fd70d8d21006df51d8d41005bd7498530004fd75d8d10006be53d9121036de7610d32004fd7558f4025ef621d8520005fb704c5100eef621587320067f7559130004fd7650831004fd764cb4114f6e751894101cfe75d89430069f6418d2101cfc7558f10046ec6258a410067f7558d10004fd7318540004ff7358241047b66150441006dd634c8410057f755893000cfe70d8910085ec725854003e7f745944100cfe76d8132016ee6250a41006ef62cc910036de6318d41036de7518d4114eee74d8941006de53d8d4103ebe64d0731016be62509410379c4350d3114ef6215874203ebd7019130004ff7058443006dc53d8d2100cfc7458b4000efb61c4110014fc7258643046f81058221006de4018d410067d72d9530335df758c730005f47150b31146bd405931003fac4250d42034ff76cc910034fd71d813134ddd7550f300467e75d8f1000dde704c930034fc7690d21006df6358941036ef7258b3100cfe7058742006dc75d8d41016ee624c841004fd73d854203cff765073103cfc7458332004fd72d9131006dc6018d410067f65cc510004fe7690520046f43198443166bc42d922116cff7650710006bf6490520047d6514c431006bd6410f10035dc72cc631006e
  | 17 => 0x6de75d8d2103ebc701912103ebc6490d10286dc640c530004fd7558a41006bc651912101cfe75d9130006be50191210a4fd72d8b100067c65d89103277b30d9530006dc63d05210067d74d9510015ee72d0521006dd5018d21044fe71d8d4203efb7058341004f47158d200cedf2018d21006dc7359121266df30d8d2031e7e30d9530006dc50d8d21004fd755804331e7f10d95300057d759853001cfc75d8940046fb105824114dbd72d094103ebf711912103ebc7219130006fb7058d10034fd72d853201cfc7558241014fc725933003ebd721912104dfb7058520044ff76887300067c74d951000dfa7090540006dc6310521216df32d8d420063c6519130006df63d0e21037d8304c530005ef7258d10186fa30d81320067f658c510044fe71d922103cff7650d30004fd75d9121005dd748c7301c79c30191300de7c658c510006bf65d91302467e20d9510036dc630c52029dde74cc631004ff7359110004ff7558b1001cfe7558231014fe725874303ebe6419132006bd64508312477410d9510004fd7558d10036dd7218d41036df600c530004fc764854000cfe7058a41006bf6410d10166bd72d9121006fb5058043004fd7558841025f97098520036f8305824301cfe75d89313567c2059740005f571d0e31035dc7350730036df7018d41005bf7448510005f97010d200b6ed20d89100067d7359740006dc60d8d41004ff7650a31004fd71d89432cedf43d894301cfe7559131006ec75d8941046f62118532004ff764c841006dc6350941045f671d0e31004ff75d854003ebc64509301a6ef2058b4000cfc70d9221046f671987420057f7558d2000dfa701053000cfe76d0510006de3258f41036dc630c521005df73505100ecfd764c52100cfc70d8d10006de6218d41006dd630c51003eef4258b40045ee7188521037cf724cb31006dc30d8d21004fd73d9110006fb7059130004fd7558041005dd70d0f32035df74cc93003cfe76d9131034fc7358a43007ac6290541004ff7559121004ff7058742026ec32d8910004ff7558f10005bc7458520006dc65d8d41044fc715804300efa76c4110036fb30580310cedf4218d21006bf641052003eec4258b4301c7e75d814235eec6488521044fc7158f42044fc7158843014fe7498742006f7614c530006bd545834103cfe76ccb40004fd76d0b300067c75582210047d75d8142006bd545933203cfc7458732006df63d81410057f755824100cfc764c930004fd72d9310004ff7558443037cf62d0d32044fc7218543316bf31d9130004fd75d89432b6df64d0d32004fd769052003e7d40594412b6dd6410d32144fd76d0710004fd75d8d40004fd75d8540006ed5258831036de7518d21015ee7290e21107d721d8d21044fc7158e41006dc4018d2100ddc7650d30006de40d
  | 18 => 0xd71d0d3214fad741894100cfe70d8931006ee60d8941044fc75987420467e2159441006df7358910037db6050d30014fe72584430a6fa60d8121014fe72d913031f5c73d9530046dc6358e4100cfc70d923101c7c755822103ebc6490521004fd7559131006dc72d8d41006bf6410d20005f771589300067f7558d2000cfe70d8d41036df305883103fb77150441006bf65d9121005ed7210d2115ef51098740005bc7458d21004ff7558742276bd40d9120005dc7348540026ef21d8910006df6390d420077b65c411003cfe74d8b1003cfc7458f102277865c4110006bf64d8121034ff7610d10046f81058231036de6318d42046ec2158a41034fe73d8520006f721d85300063f6519130007d4618c530006de64d8d21044ff7518532006bf6418d210eeee52d893103eef7258b430067f6548510006be62d9130014fe76d8910004fd75d8121005dc7358542006bf6450d3101cfc755824313e7c6590530014fe764c521004fd7518543004fd74d8530005f4714c931065ec7258530004ff76509312addd758c53001cfc75d8d1001cfe7559332004fe76d09100ae7c65485100fcfe760c510034fd735933000cfc7058b3101cfc755874000dfa7010d1002d7c7559110014fe76d8930006ef6250940006dd63cca4120cff7359130006fb705911000cfc705884100cfc7058c41005dd744c930006dd3258730006bd6490f1001cfe7559221006bf6490d100cedc5218d210047f755803103ebe6410f103567e305974001cfc755933112cfe7690521014fc72d8d403a7e44118941005f77150831004ff7259231006dd6318d10005be76d0941047f251c411003ebc6450530037d6718c730046dc6358f1000cfe76cc5100467c2159441006bf648c530164be76d0941035dc7210e310379f7450d30115ec725073101cfc755913003ebe6450a31004ff7458d10004ff7458b100eedf3258e21004ff75d8d21004fe76d0d21004fd70d8532036df3059332005ef7250730276bf40d912000dfa7090d4001cfe7558a3103fac4250a41034fc76cc941005dc7348740006dd51d8d211be7c65d0930006df6358121006ef625094101cfe75d852000cfe7058643014fe72d8d40046dc3158c410cede4218d21006dd6318d400067f6599130034fe73d912103cfe768c740174ff765062103ebd7119130006be65d9121004ff7558231006df63cc521006de6018d4103ede4358343006be10191210067f7558241006ef6518941034fc735822118e7c654c93000cfc7458f40014fe72d85400047f7558d10004fd74d852001cfe7558743004fd75d913212dbc7250441034fe73d8b1000cfc70d9121034fe7318540106df72d8d21014fe7259031004fd7558a310067f65d8910086ee62d8940014fd74d8142036df3258443004df764c43135faf42d0621
  | 19 => 0x8732105ec7250631006dc5418d21046df618c531004ff7458910046f970d9310005bf74585320057d75105200067e74d9510016dc764c93012ebe32191210cedc2118d211f79c4090d3001cfe7558f42004ff7458031005ee761894101cfc7558f42046bc64d062112ef52118542004ff75587430079f64cc930046bf645062103ebc4258841046f67198443004ef725912114eee62d8941014fc7650d42004fd751853200cfe7058f41046dc6398e4100cfc70d854200cfe701852003cbe76d9130004fd75d8520046f41018532106de20d8d2102d7c7558d10004bf7458d21036de7690d30027e8624811003e9c6450d30006bf53d91300057d7510531034fd72d81320067c325944103e7e435944103edf4358f41006bf6499131006dd6390e4101cfe755873029edf439864303edc4358c41047b651d0641005f77158d2003e7d4359740006de60d8d4101cfc75d8142006de72d8d41004fe765093003cfd71d8141044ff7258831005f57190d41006ee63d894103edf4358f42004ff7558341146f860581410057f755852003fb76190541006ec6258141015dc72d0f3203e7c7459441006bd64d073101cfc75d8d4003e7c43594411a6fa20d8142044ff759864301cfe755923103e7f415944103cfc7458d20004fd755884303e7f4059441036fb30583313a7e741189410e6df3058f10006bd64d0e3129edf64d0e3100cfc705903129ede61d0c31014fc725824300cdc735873012ebd3219121005f9708c5301f6be20d9130036dd7218d21044fc7158b43006df6350941105de72cc631014fc76d0521044ff70d9110044fc7298643036de7418d21004ff764c94103cfd72185420467c1059441005bf7458121045f67110e21066ee62d89301c5de7690d30034fc7610d10005bf74487303567f105974003cff7650531015ee74d0a210eeef21d8931005be7498d210079c648c530006bf6448530036dc6310d2103edc4358f4135eef64d0a21046f671d9310166f52198742036de63cca410067c62d95300067c6598530004fd73d8142014ff7658a41034fc7358b41006f76150540004fc764c9400057d7510530006de62d8d41006ef7258d10166bd42d912103cfe760c7400067f6550d30005dc714cb3003ede6450d300067f735944101cfe75d891001cfc755833201cfe7558e41034fd70d893001cfe75d92210467c7159441004ff7558221046df63cc62101cfe75d8d40006bd5319121006df7359121004fe7650931034dc7359031006df63d0d21166bf71d9121036fb705824303cfc74587300067c65d91300079c64d8d21006dd4118d41034ff76ccb1036fd551cc6310067d72d9510004fd7098742014fc7258031034fc7359120005df7350730036de63ccb100edec7258131146f850d8141036dc735903101c7c7558910005d
  | 20 => 0xe5f57198d103567e1059740006ed62d0b31044fc71d9110004fd7098443006f761cc5200473d6550441004ef7258d10005dd71d0c3103cfe74d893117e7c65d0530004fd74d89310067f71d953001cfc755933014eec42592211f79f6490d3000cfc76509401f7b830d913003cfc74583313c79d5410d321f6bd70d9130004fd73d8121036dc7358730006bf645052100cfc70d89410067c42d951000cfe7158f10184ff7058d200067c65d8530035dc7348530044ff7598730034fe76d0b3001cfe7559331164be7619121036dc4359031006f77158910014fe72d8f10286dc4318543016ee6250831044fc760c520105de7618d21176f621d8542004ff7158a430067f715974006d7e7598530035df75cc930006df5018d21004fd76cc54000cfc70587420067d65cc841006be54d9131036df60cc93003ebc71191302ff9e5490d300067f65d0930004fd75d8d422b6de644c930005de7618d41004ff75d8d20036dc3158730004ff7458b3031e7c40d9530004fd7498732034ff7058043005f47158d421f6bc405824300cfe76d8142004df73591310047f7559130006dc1018d21004fd7650f1000dfa7090520006bc640c521046df3198732044fc7518542006bd65d912101cfe7598742006dd63cc91001cfe75583320cede2118d21004fe7688540035de7310730034dc73591210057d75d8142004ff715913202d7e7510510006df53d8d2103e3e75191210067e75d8142046be74d8f100a6f850d812100cfc705922103cfc7458d21046f4610c5200067c7159740004ff75d85301def8605814303ebc641052101cfc75d8930006ef75d8941004fd764ca41037db604c930005bf7458d10006ec725913131e7e10d95301c6bc20191301367c6510530004fc7650d21005dc735894103cfc7458b3005d7e7599120036bc4359331036dc73593321c6f85058043004ff7458332006dd6318d42005dc7359110036be4359332004fd7558332006ef74d89410067d73d95101ad7e7518542006ef72591102b6dc644c931004fd764cb100067d7359441006be4259331016ec6288540044fc7158a43044fc75d9221004fd76cc910046f46190540007ac6488521006ed6250831036de6390e41006bc40d91310fede768c530005f9708c520036df3258043046ee2158a41014fc74d8940006bd641911001c7c755833200cfc705933100cfe70d9110014fe7358332004fd76d0a31106df638c521036f8305833231e7c70d9530006ef51d8941045f87148110034fd72d9132044fc72d9231014fd7358b30006df6350d4003dbe74cca41004fd7648730036ef7258843004fd7559120004fd75d8910004fd71d9132004ff7359120006ef72591200e6fa60d8131004fd768c540004fe7650520014fc725874303ebd7119121004fd71d8940006df439
  | 21 => 0xc3258f4100cfe7058a31004fc7648530005f77150d41036f73158732034fc735903103cff76d0831005dd73d0531035df750c530004fd7558f41015ec725052103ebe64d0831316be53d9130046fb1058031036df7118d21006bf6498d2112eac211912111e7e65cc740034fc735874203dbc74485400379e7410d32044fc7159330005dd73105300063e4259441044fc75d8e21007cf624c931006bf7458d100cfd42118d21004ff7558d20004ff755873203ebe6419130014fc72d8d20006dd6318d20006df634c94001cfe755864300cfe7058b41004ff725874323cff7158910006ef725891029ede648c730014fe72582430067f6598530044fc751854315cfe7610510034fc7359310004ff7358841004ff7650831036df6090d3000df8708851023cff7648710016dc624c930025f87648110035df7590d3003ef8405834203e7e4159740006bc745891000cfc764851012ebc521912100ff361c411030fbb301913016efa1058341004fd74d8131005df7358121016de624c931006bc60d912103ebe545844303e3f415944103dbc7458a4100cfc7058b4101c7c75591102467e40d95100cedd2018d2100cfe70d8d210067c70594410067f215944103dbe74cc841006bd5459310004fd75d911018d7c7558132014fc7650521006bd52d9130006dc64d8d21005dd73d05301b4ff72591200067f65d9130004fe7690d10006bc42d91301c6be3019130044fc7610f10045f67190e41006bf641853003dbc744874012ebc421854215cfd70d9110004fd73d9221036dc634c52101cfe75d8530006f77158d20044fc7650b10006bd545922103ebe7219121034fc7358b10006de5118d410ffda708c5300067e71d9530006dd63cc841036dc6390d211c6bf1019130186ef2058b3003e7f4259740004fd769923101cfe75d8121006ec725911000cfe7058a43035dc73907300ccdf764cb3100cfe70587430057f75591100069c644c93003ebc4298742006bf6490d20006dc2018d41005dd73d0a31006bf52d9130046f71018530005bf74589300067c7558d10036dc7218d2103ebc64d0521176ef2158b4100cfc76d051003e7c405974000df8704c930007d4714c93103edc4358f40004fd73987400067d654cb4000cfc70d8532006bd501912101cfe75d813114cff725912112ebf2019121006be5119130166bf72d9121006de32d8d10046f67198732006ed624ca31006f56118542004fd7690730044fe76cc8412cedc64cc930044ff70d8d100067f6590530004fe769053001cfc7558e2103fac425094003eec4258843106de3258a3135fe571d0a21004ff7558a4103ebe6490f100067f654c9301c79d7319130036de760c530034fe769073001cfc75591203567e70597401a5ed7299120006bf7459110004fd76107301f4fe7619130
  | 22 => 0x8a31006bf64d0531046f43198643005ef7250710006de51d8d41006bc73d9121004fe764c940006ee75d8941005ef72585432b6dd64d0d3203ebd751912101cfe751854300cfc7098443034fd74d8943166bc20d912103e7d74594411defa40d814301cfe7518530004ff7058843044fc7610e210079c6350941004fd76905300cedf2118d21004ff7158b4303ebe701912103cff7159310004ff7158f42006bf7458d21006f55118532044fc7158343004ff75d8542004fd76cca41004ff7558a31106ee3258a310e6fa30d813103cfd72d8d4203cfd70d8540036de4358043036dc31580430de7e658c740034fd71d893103ebc6450d3001c7e7518542005dd740c5300067e3259740046f671d8e21286dd76d0c3101cfe75d913103faf7250941046f86058221286de640c53000cfe7098743006de6018d2101cfe755883110cff7158d10004fd7559031006bc621913003dbe74ccb4001cfe7558241015de72d0d320067e72d9530004fe761053103ebc6450531014fe7690d423a6ef4218542036bf745933201cfe7558f10004fd7650a3101cfc75d8131036dc6450f300067f6510530006dd71d8d4103ef77158742006be5458643104fe760c5213267c31d95300079e531913003cfd71d8941004fd7558243036f83058043004ff7058f42005df7358542006be4059231014be7498742004fd70d9221006ac6488521044fe7159221004ff735804100cfc735873003cfe76cc74000cfc764c53000dfb7248110006be54d8141006dc5118d21037db600c530004ff7558831264fe7618d2003cfc7458d10004fd76d09312467d10d95101557c755814103cfd70d89400067e32d953001cfe75d912103cfe74d8d21004fd70d9131006dd70d8d41006be54d8540004fd764c910006bf7459131007ad5418941006bf7459130014fd73d8132004ff75d8d4024d7e76d9510015ee72cc52131f5f73d9530004ff7258d10004fd760c540285dc744c431015de7210d3200cfc76505401f6bc70d913001cfc75d9130046df7358c41005bf7458d2016ef710d8540005bf7458910004ff7558f41045bc7150941006ee51d89411f79f73d913003cfe76d9120014fc7259331004fd76505310067c73d95100cede5218d21004fd7558b40006de6518d41005dc7350710016dc624cb30007ad64d0a212b6de644c931004fc7650530044fe71d8d1003cff76d0d2007d7e7510730004ff7058743045be71d09410067c7558243044fe71d9130004df7359221015ee721052003ebc6410d2100cff765822103edc6490d30044fe71d9110036df64d0f32006bf51d913003ef8405834101cfc7558341004ff70593320047f7558243046f67198740044ff760c740106de628c53014eec20d89410067e72d9510006fb705891001cfe7558d1000df8704c510006d
  | 23 => 0x6bf501912132d7e76d95301f6fa405824303ebd7219130005f47158132006dd64d8d21005bf74487101ae7c6550910005df7350710006ee6318941004ff75d8910006bc70d912100dfa70d051003cff76d0b3101cfe7559130014fe725804103ebe6419120006ec73d89410067f755891003e7f43594410067f6558d10006bc1019121004fd7598732004ff7458f10046f62118520006bf7458d20014dc764c9310067e42d953000cfd73d8930006de30d8d41044ff75d9231006bf6458d21036df3258730186f86058132005dc73581411c6be501913012ebe2119121016be62d09410ae7e65487400067c6558d10036ef3258b30006de65d8d41004fd7518542046df7358e2103ebe5458043006de65d8d21034fc76d0531034fe73d854200cfd7458041004bf7458d10036dc644cb3001cfe75d8d10004ff7359131005df7358941004ff7158343044fe71d8e2131e7f40d95300cdde724c4311f6bd10d9130004ff7650b31014fc725824103ebc7519121004ff75d9110006be545824300cfc7098732006df6398d1014eec6258941006df630c5400be7c6588530044fe7610f10007af6250941034dc73591100cedc620c530014ff7648510006df51d8d21004fd7558831034fe73d9130046f4319873212ebf3219121046dd73d9231034ff7690e21166be4258a41004df7359121006dd72d8d41004fd75d8d41004fd75d81321c6fa2058043004fd75d8f10004ff7058b3100cfe70d89430e6f86058131004ff764cb40106dc42d8d21017e661d0a210b6fa20582211a6fa40d8142006f7618c53001cfe75d91100067c30594411dddd73991300067c7559130016ec62d0910004fd7298730035de73d0831004fd764c84103dbe74cc94001cfe75d8e2131e7f20d95300047f7558332004ff76485300067f65d0530006de53d8d2101cfe7518532034fc735912100cfc72d8121106df52d8d2100df87050940034fc76cc940044fe7650f10034fe739874203e7f7459740006be51d912112ebc2119121035de73d0730046f671d8b100067d7259740006dc20d8d410067f65d85300067d650c7400069c640c530167ac21d9121044fe7650e21036f7319873003ebc4058043006ee30d8941004fe76cc540006be42d913103e7c415974000dde708c730004ff7059132006bd5459110004fd75d8131006bc72d913000cfc74d8141034fd7218532016ec624c930004fd76d0f10014fe76d89310067e7259740004fd755913200dde7050f30014fe7258e41006ee65d8941005dc7150d30005dd7610e31014fc72d9120034ff76cc740004ff7559120016bc6250b41036df7218d41004fc764c520106dd52d8d2100cfc70d8943005dc7359221034fe76d8d10006df6310d10005f47150d4101c7c7558d1001cfc75d8543006bd65d9130006dc435
  | 24 => 0xc625894303efb4058341046f671d8f10006ec651894100ddc704c93033ddd754cb30185ed7298d2003eef7258b41006bd6450a31006bd62d0641004fd7298743014fe76d0d3212fb42119121014f8764811003efb405834203ebc6490d2103e7d4059740044ff70d891001cfc7558443044fe71d8910044fc715913203ebe76d094103cbc7458d20034ff76cc84112ebd2019121006bd6250441004fd73185200057f7558143006ec6018941006bf71d9130065f97098d2003dbe740c740044fc72987400467e7518542004ff7158d20006cc63d89411f6bf30d9130006dd5418d21305dd7590d3003ebf7019130044fe7158e21034fc76cc910006be73d9121006de1018d4103ebc6450d320cdde72d0c31004ff71588430eeec6258931025ec7250510036ec3258b30034fe7688730034ff7690d1003ebc6490530004ff7358b10046fb705804100cfc7058843004fd74d8132006bf6450930014fc7258331006ef7259132187d8704c9300edec725913103e7c435974000cfc70d9131006ed43d8941006dd74d8d21034fe73d8941034ff7690d211f79c30d913000cfd72d912012ebc3219121045f4714ca310057d7598d10285de744c431036f73198443004fd73d9310005bc745812101cfe75d8930006ef6248510006bc644c52100cfe705933103e7f4059740006de5018d41006bf64585300057f7558141005df734851003e7e74594410047f7559110005bc7458d1029f9e5410e31145f57199110006ec62d81410063c65d913000cfe709864300cfc70d91320edf57198d21004ff75589100a6f8605812114df57199121046df6398e41005dd70d0e310f67c654c53003cfe7498732004fd7559310044fc7610520006f76198540006bd75d9121045bf7590541004fd76d083103ebc64d0930004fd75d8e210067c72d953000dde7090d300067e7059441004fd7598740006dd6518d41006be30d91211367d715944103cfc7458a3101cfe75987300c6fa50580310079f6350941004fd7558b4300cfc7058643015ee72d0d32166be629054103ebe6450e31016f862481100057d751073103ebc7019130004ff75d814103eef4258841006ee70d8941014fe7258f10044ff759874303ef44158743006dc5018d2101cfe7558e2103e7e4259740034ff764c510005df735854031e7d40d9530005f97090540034fc7458343006bc644c930006de40d8d21044fc71582430a6fa20d81213267c43d95303567f20597401c6be10191300379e74d0c31044fe71d814201cfe7558243006ee20d8931005dd71d0f32044fc7158231014fc7458342046bc645922110dde760c5302467f30d9510036dc6350d41005bc7448530006ed624c8410e4fd7698f1003e7f415974025ef521d8520007af6488521046fa10d8b100067f655091029f9c4010e31
  | 25 => 0xc510004fd71d8d40044fc7690e210067f65885300067c2159740004ff75d9120004ff7258443016dc624c931006bc7458d1035eed76d0a21046be6150441037cf724cb30045df764c43103dbf7250941004fd73d912000cfd7358031005dd728c530036dc638c520006dd5118d21005dc7358520005df748c730004fd73d89410067e2059441006de7618d21004fc764c9100369c4359031036dc63cc521004ff745873003ebe64d0a31006dc635812101c7e76d95102cede64cc930044fc71d8910005f471509410067f6550510046ec6258a31006be5459031044ff7459031005dd7110e31004fe76cc940004ff7458331004fd72d9231006dd32d8530046be4159031006be321913000ddc764c9303267f32d953031e7c10d9530036dd7518d4100cfe715931003cbc7458d2112dbe7250441006bc511912129edf71d8d41006dc32d8d10046f81058241004ff7158b3012eee3258841005dd728c5311debd4059330004ff7059031004ff7559221004fd72d8131034dc7358740004fd74d8f10014fc7650941006f76190540006ee10d8941034fd7018530037db60cc930014fe7258043034fc73583421567c655051010efa105833131e7d73d9530046de3158e41004fd7558a4312ebe5219121006dc639054100cfc7398730006df65d8d21004fd7558b10004fd76d0530004ff7558f42044fe76d0e21014fc7259130044fc768853000cfc764c510035df764cb30014de76d0d32046de3158e21006bd54d9120036dc7418d210a6ef2058b1001cfe755903126edd32d8d20004fd7018543005df7358910004fd71d8142034fe73185200067c21d9530004fd7610d10005df744cb3000efb6148110036dc63d0d21006bd53191300cef52118532006bc64985302ef5c6550d30006de70d8d41006ee50d8941004ff7650e2114fe42150521286dc4018d41006bd64d0831014fc7258041005f57190e41004fd75d9221014fc72d8530014fe7259110014fc73d893001c7c7558031004fd71d8143006bc71d9130044fc7650e21046f7109874003dbe740c540004bf7458910004fd73d89100e6fa10d81310fedd30d8d101debf4059330005ef724c52129f9e64d0e31006ed65d8941004ff7558343006bf6450d21034fe7610730044fc7598743014ff7658a31007cc63d8941006bf64d0d32004fd75d893100cfe70d8542034fe76d8d4001cfc75d8943004ff75d8d41004ff7359221005be7498530004ff7558043004ff7059131004ff7558b30006be7619130006dc7359221004fc764c5400073d751912100cfc7018520006bf7650441036be4359331004ff75d8520006df6350d41044fe7198443034ff7610d20046be7498742044fe71d8143004bf7650441047b661d0641004ff7648730005df7350a31034fe7398643014ff7650a411e6e
  | 26 => 0x91802400c001001800000200300400140a400000381580000020510008032022004001800e08a006822000600d002000c00c0ba00e00040280b0000000400a12200f800013a0000f000940000000020000172000131003c09600b5ce000802800301b0004106027000000000000500b0c6000200207680a006400c007809c0b0019002001800a0110000084010027003000801a023120004000602e00000540000020000018016034001000406e0030048000000008000025001400500d0054010000000000800000000080000900050000008004001000000c05a00203480840400090b5800c00400002480280ee0120020028c960010368a9c03429700101f400000415d006c0020ae00000000080124f90048008006000012027001401d817c00a04e000040c04c028007812826e00f02580081a400c00000841d633e030800004800202300040020020060070000000005050800017f00900083b401d06180d001c00e0050004034017012802c01000102b00540040220130058004a5d000001c038000008800403e002000001007202f0038f7816000100180e800000301e0004000000053006002200123180fc020000002001000818100e0254012005000001807000f0078020000010005004c0a40042db0040000000067966800e01100100080064af00c0000000000005802002c00300003640ca00100391ec032066001016000a0000028058016000014805c00600d0358038066003007000001a05002b803c11e02800204700b404c01c800812a00b0358be8000072000007400400300e00300083240c480057aa0045f680ec02400a000825800000200d000c002002000001402a00c0120008002016001802000002f001038402a002024855c006c22019802000000b00200140000a600e800000801c00284d403c06a053801800a095000009000005100489bc03200c000001401001114e81100aa00700880e80740000000720000014043000001400300001403de0be00c84b800200000400c803800e00d833801208400d003405800902f0000034000000013c65800200f800460400001380081b20010af000009c021046f860582410067c65d8930034fc73d913012ebf211912103cfe7688740036dc630c7400cfd72118d210069c64d8d21034fd7158f10036bc4359330014fc7258f40005df7250f303567c1059740005df7348730004fc7650520036dc6310e21004fd7558b31004fe7648530014dc7359332006f651d853203cfc7458910146fa40d8141006dc63d8941006de50d8d41004ff7558f40004fd70d91210fefa205823100cfe76d0d3035eec40d8941005f77150b31044fc76d0d31044fc7598740286de5418d4100cfc71593102c5df754c930036ef3258b31014fc72d813101cfe7558732286df4218d41006df634
  | 27 => 0x6001002823400e004001800019400801804ac2e8028008803401800c009800400604300301ec002009000801c00c0a2000000006800b00e01e01e80cc0830438016013004800400002600180080041a1018003000403000f800801400e048802c31c01101a000001c0520df81100040480da800000000500300000560091550000018016000000029c03b000805400002200f0014006005005000400400700080e002a094000801800c17f002002803000800a805809e01801e823000000400700053fc004002809c01800b0420000018000019023000600000280000020030a8800058201f000828c0c001b000121c012003076865c004000000000800000300100d8178948006a654000001023801c00e00800001a4006025000800001200d000800804a01b0aa800c4fa001002800c002189005802c0000001c38000000038027802413a01601d804004e016000004401801d000803c06200b000001400a020005000001c02c00428080100560ea800128008d773002c008002014002800001e01b002c01200202280280020c701b80f80201f003481f00121f800100cc060023158805000001f016822400800500c802811c01500611dc240000015875c002001001000002a0a000114bc06600f00e80c801c005005804813405903285640660d00df00000c016c00880040140280000028002002000002c00200c0008014004033000802c00a00f0bc00080820230010010000012013000000067e00e800051001c00580700cc01e00000242181bb012804012200e00100240fe028000005804e00e01700000be008067004804801100000e000000a059802407e000007000003a004010000812604f00280184c6000037003402c00500f807c000021000801c02c0090438040000000001001002802d00534f0006003003800c004010008001002615f004083405e1fa000811c0001af001000c050000010800003a02d0b60070044013001000005a03800280d00040013b780f40a801d022005000200100784f000e05162c00000000000028004004003003846c00a00d00600380700000140c7c060006002000001400f008000844c015008800815c01c085000c000007013021c0a400100082b000402e00000000000d6038803429a00500008f4006004005800000c02100a000ca4600100000040f600b46d0054000000005810416004100a80040060010ea81c81900450080074006028000008002e01800001d403600000c001c00200304906e42e20400150150026007052800801c00106c000003a01907580a4074a7801f80085520041378000000006000008c026070059000800000507900d018003200080040000010c800000ca033046849c106006003800000e04800680185d600901a04f402e00200e80300bc029002001400001c0
  | 28 => 0x2980a80081d5010800000000000a800c01e07d00200080020170168078002012000097001e00401b8218012007006803400c000012005000001100b000005405d00080d000003400a800000400001f305001603800180fc05600000c801c046004104800400023a008094c7cc01d028823409801805389fdca400c00000700720f9000001c00431a04380301540a3000120000001008900080500000ca800447e0170290044ac601300f80a000804802c80040484d401b0030fb8004006001400000d03a806800000009286f40000020078000008001000001000a022057007402202200000101b259201000001fc001012802006052b00100607d200c145001417c000003004c01400800501540a604501e800810a0000420204038013003004000004f00d81f818c017002800009c027002000001602601d004804a00000300581cc0070000028096011001803c0020140010eb044e09c00900cc6ca0000ad803403400700000080560110008120002026011001400200400002b8002d0d0b3047c0020000048004000000022000000e007000001c19021300a006800000b00f00144760410048068002024002800c1ec00102480580060092dd0000002000041000c03400a006000000000201a80040720005f581b80000050d1801401816d000000440c000001008c00000600000042560020320140008000002000001800200e82b82de010000013003e003001814c030035006000c000009001014400200000403bc02800003000000d4194007800002c0d5001026403e000014817800001e00081d8012070000000002017e0130140000015005000003211c0078004104daf014112c00a03303200a8000008000861406600000800200180000000008056001000006000202200080000400030148158058006015005825400c00580100020da55d013c032241014000001c028001801800601900000240300000048ae0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87d85dc1648c40187eea3a2c6880023ee0175591310056a41ac230a40008bf845d563484a153d09900c6a08023761c2018d410061fba8e8b122000ace839806250471938ec3226498002a7e116518d210364f31ae99948200ccc7218d605040153b08288c6a081a3b21d5258a430446e43ac69962082a9f83594644c00d938c6ba664a00063721973d05300063632ee4b0a6000a9e83980644840159f04b2ec6a098aa7a0c72d91300061eba8ebb224200c5f65dcd414400d53906aa2c81880387d946490d300366a31ce221a4200a9e8414763484031f100baac8188faaea0021d91300054f41ccbb224200a9f8359464484018deea392c6880030fdd47458d2000672310e2a1a8200a9d84983634840117b0fa90c8980038b59772504410062e3aec6b028200adb805976350459958c53b684a0802ab60a101912100566c1ccbb12828ec9e76d9063484018eeca38ac4980063e2017558d210047dc02eab222090a3f845c965104015ab02280c6a0802b520532d85300346e432e518a6200c9c64dcd604840f1bd0fb1a8690802a760c211913000477c12ec99220078be87144644c00d1bd0e280c69081f8ddc565504411c6cd380c918a6000c3c751d16348001c6ea328ec8908030f196749853001c3f43eeab222000a9e84980634840117d0fb22c6908022fe11755913000733a8ca3b128200a5d85c836350401938c8b90629814ea7211638c5100066639ee4b122000cac74d8921440031d90cb90629000327dd3635812100566c1ce1b128200c3d75d53644c001938ec31a84a08032719373885300056c402cbb1a8248c7a76d9710440011bd0fb1ac0a081e2f2117558d200062eba8ebb1a8200e5751947634840147d0b316c8980022f61e651912100667b1ee4a0a4200ab980087644c0014f700b8acba001e8fa12205944100477c12eab224207a3c84c856510407878eb2a6c8980063b21972105200061fba6eab048600e8d74d8c62504331bf0e996c29800333dcf62581410046ec38a1b1a8200c6c7219564440d54f100b9acba000637a1b73485300061fb28e8b122019ccc7218d4148401958e4b2283988032bdd0725913110566412c718a20008ef8758c625040f17908baac02194f8795354d8d410146e41aed992828ae8c2119363484015b100b28c6908223b21d52588310346e41aed21a42008dd8714063504018baeba9ec6a014f2761c648c53000672310e2b126063a5d831d3654c00d1bd073b282900021fe1570d89430061ebaec9322400387e87dd560cc801c3d0a320c690803279db63d09410346e41aeab224200e4e7518c625040147b03212ca2080a3b2097610d100064fbb0e6a0882088f8865c0414800193ec839a82880029760c21d95100061e3a8c8b024200a5d8518b635040153d06206c8908222f21176d0530
  | 1 => 0xf0eb18c6a081f271d1634c8410346e41aec21a42018de86dcd414c0c74bb06396ca98002ab60b71d91300043fc2aeca122000aeb8059462504051bb07bb265a0002a7a0e42d911029c6fc1aeca0e6019ace82d0d620c4014bd07392cba000237e0d764874001556412c8a146200caf64dc9414c0a1c3ca9aa0c6a0802aba0875d91300046fc3ac831a4208c3d415d4615080157700a88c89801e2fa1f52191300346e41aec90e8061e9671190314c00b0fb0e10eca88002976146218d4100566c1c21b128200cb4641c5624c00187acbba2642080387d955418d4100726baec63128200c6c75dc9634400159d05300c6a08230fd05751854200566c10a1b1a42018fa86dc1214400147d0a216c898002a760e10d91210cd67416a231a4200adb80597634840187884ba8c2a1002ab60850d91212864e320e6a0a2064c5c73d95414c0a7938c9b9a829894ea7a1050d8d4131d3d406e3b2a6000a9e8499763484011df04bb2868800e37e1d53d8d210061ebaec820a4200a9c8458c63440014bf06b8acba00bb2bddb42506210467230ae418a400087f855db424400d1bd07b8ac1a1003175d763105210066639ec490a20008df835d561d00071df0ea96c49880e3de1d51d85320043fc2aed21a4000c5f75d8d605040f47d05212ca2080327d9373485300043fc2aeda1a2000e1d54d4863504fdc3860328c8980038bd95541894101c3e42aed21a40088f8865c231480070f90abb6648814f27193735053043cd7c3ac9a144200a5d851d36348401958c9b92629081e2f21172185303f70eb98ca322607da3e85994644c04b958e4b1282209ef271ce54593320043fc2ae1b1262008fb805d564cc84159d04286c690802b5a045018d410045f43ec8b126000cb474dc5634800193ae8218c29900676e1d708c53000636396caa0a6000c5e7518c41484010fd0e3aac8880030fdd77458d1001c3f43eeab048200abb8054c644c0070f90abb2848809a8f61372594410052ec1842b2e8000a9d84140635040187eebb22c2980032b1cb64505310046f43ec6b12820387c855da434400117f08bb44298003279d863d094101c3e42ae13088600e5765d86314c00117d0dba24298002ba20165d89414a55bc22c230a8400c9e74d8e634840153b08290c6a080e1f21676105300046ec384231a820087d85dc162cc4014bb06316ca880021fe1f651053012e56390c898a42028dc835d564cc80159904b18c6880023be09765073035d57420a3b1282028f8865c0434800f87ce8b2e64208021fa1c755891003e4e3b0c8a1a6000c3e769d464484119c8e2b12651880297a1464d8d210064e322e518a6000a6c855c362504070f90abb26488003171d4635812112d57416a23224200c3d751d7644c00f179083b2829801e2f21c64485300051fc22e7b2a2000
  | 2 => 0x1511913031d2ec1ee3b2a60008df835c76050801c3eca324629800333dcc72591310051f42043b2a208cad78159063484011ef0eb08c2900031799773487400063c3aee0b122000e1d5454863504010ff0abb442980229da04705944135f17428c910a420387c855d943480070f90abb0629021eaba1954189410043ec3885b2a603e8be87d4f644c001878ca3a2c48806637a1b73505210054f41cca3224207a3e84dcd65d000f539073b0c898002bc60021d85300063a328e2b126000c7875dc164440f395cecaa6c4a0802aee0165d912103c5f43ea6322420087d87c81651040117f08baac6900021f617705933101c3f42ee0b266200e8c64d8e214840193ee9b9ac8908032bddb72504410045ec38a23224250a9e8414863504031bd07bb285981229ea0072d95100046fc1ae9b12200387c855c0614c8b393b0e326649819297a0c74d953000567414c1b1a82088f4815d9434800153b0828ec6909f6a7a1a531913000567c1acbb128200caf741c963440070f90ab80c2a1803171d463581410052f418c5b2a2059a9c8458f32440c353d07a88c89800237e0d76885400056741c21b128200ab5840876150c01958e5b22c29800e1fa1f7558d100064fba0e6b122007c9e645cf428c4111e902bb28418802a76135118d410047bc3ac230a6406c9c635d263484014bd0b906c6a08022f61f53191300064fba0e6b222000ace8299463504031f100baac99900317d9473505100046fc3ac618a2002acc8258f324400d1b906baac81881f2719173d09300061eb2ae818e8000a3c845cb654c00f17908baac4208fae620153d91300052ec2e4031a8292ec74118c62504010fd0e32ac2980021f61c42d95100046f438c6b0282028dc8758d32440111e902bb062900031b1977258d100052ec1c85b2a60008be87087644c0014f700b9acba000a3b20976505310046ec3c8431a8262a9f8458c635000155904b20c89880237e0d75591300043ec2ee0b168200adb8059463504cb8bae6328c898003331cf72592210047dc02eab2260078be849d9214c0011bf06baac88808237a1c4358a31006563a0e4b1a20008f7815d5644c8018f0cbb8242880022fe117559121006363a8c4b028200acf82594635040153d07086c8908031b1cb655051003c5f426ec90a60008fb805d5644c8018b8cbb9a82980028fa1021d953035e56326e4a0a4200e8d7418c625040155b05a88c8908faa760c75d91300046f43841b1a8200c3f651d1624c00f17d0fa98c8980023760e76485400064e320e29926061e8f72191324c05955d04286c89080e1fa1b75585300046fc3aca31a420087f855d9434400d1b906baac8900030f1d464585303e64e39ca8b222000a9d83d53644c11593cec320c69098e9ea0072d95300345e43aa8b2664078be87dd162440011b
  | 3 => 0x1b1282028de839db32440014790ab86c8908030fdd77458d2030d4f41e42322600087d87d94414c0011bf0eb18c68801f0f19175991303553d404e4b2e80088f8865c2414802747b09b9acba000327dd063581210064e3a6e6b1a20198de87d0d620c40156908b08c299002a76126018d210054e41ac8322206aa78805c565d0001d18c5b1a84a08031e1db65481100051f42ce3b226000aad82140644840157700b28c89094327191740c53001c5e43aa8b222000c3e425d461508070fd0fbaac48800e1f21576905200062fb9ce6b2e8000e1c6594f644c00159b06286c4a08021fe15764c9100046fc1aeab2242008bd87d4b644c0014bd07082ca208032b9db62d094103e1e322ea20a4200dc4211cd414840117d0e322c6908023761e1018d410051f428423226000a3d85084644c0010fb0bbb2848800333dcc72591102b64ec38c89926000e1d65dcd411040555d0db1284a081f0f19175991200346e418eca0a60068dc835d831d00011bd0e286c6a08062f21176487400062fb2ee6b12203e8be879516090c01878ebba2c69019297a0e42d95300054ec20ebb1a82008fb805d561d0cc74f50010eca98003935d4631894100667b9ee4b22420087e8710b654c001878ea3a2c488002ab608301912100556c10a63224200ace8618c62504a153d08280c6a080297a1474d8d2145d4f430c831a4287ea421190314844b55d04280c89080237a1c50d8d2144752108c998a42028ec821d94148053958edb1284a08029760c72d95100051e42ac832260068dc835d5620c4f5938e6aa2c818802b52056318d200043fc2aeda0a6000ccc731c964440d755d083aec4a080333dcc7258d100046e43a64b0e60088bc87551648c4011ef02baac8900222f21d545903100477c12eab2262088f4815d563480014bb07082ca20802b560450d8d2100572c08a1b128200c6f751896050401d18c5b1e84a08030f5d074d95300062e32ee6a0a2038aba80948644c01187ee2b2a822081e2f2117610d210055ac08a1b2242068dc8718d414840147b0a216c8980fb279db648c5300043f43843b2a20008bf87590644800187aebb2082980021fe157610d1001c3f436eab12200087f855da2150001998c7b928290802a7a0e70d912100746316c89926089e8c211906348401998c439ac4a08029760e725974000746aa6c63128207c3c745953210401968e9b8ac690803871946490d300070ec28c9b1a42018de86dd2314c00153b07386c89080aaba1b62d094100566c16a231a42008be87191624c00187acaba664209eb271cd54587400061f392caa0882008de8708763504014bb07216ca880022fe11764c9102cc6e432e99926000c3e65dd121d0001d1ca8318c4a08021f61c21597400064fb20e6b024200aad8414762504010ff0ab86c4a08e2ae20
  | 4 => 0x3504031bb07baec29800237e0d7558d2100746320c710a4279c9c7355164cc80153b07306c8908021f617705884300557c22ca3128200c6f75dc963440011df04bb284880022fe1d641912102c3ec3eca20a200087f855c261d0c0f57509a82c021802b5a0450d8d210054ec1ea2322600387c855db434404d4eb02382ca20803a355063189410043fc2ae130e8400acd8214063484011bb07b8ac1a10e2aea0021191300054fc1ac832242008df835da21d0001968e838ac690002a760c52191300066bb98e2b2264008df835d93244001d28c830c629800335547764c4310052ec2843b1a8200cac74dc962440a153908b1862880030f1d764589300062eba8c620a420387c855c36488401958c8b9662908032ddd37158d2000637b2ee4a0a6050e1f8555063504c553d0610ec89814237219740c53001476412eab226200c3f75d91624c00157300108c89818b271cf644853016657392c5a0c8200c6f75dc964440015a906b08c2a10021f61e75d81420064e3a6e6b1220208de861cd414840193ee821ac518866b3a085018d210cd66412c618a20008dd8790b63504014bb0a396c6a0802b32096318d4100566c14c1b1a8200aad8414362504014bd0a10ec6a08022fa1f644853035f172a6a9b128200aad84994625040159d06286c4a08028fa16621913001c3f43eeab006200a5c835c565d00031dd0db9282900032719073581210346e41ae3b028419ccc72589310c40117f08bb243980033918871589430054f418a1b224200c3c651d1624c0014bd07216ca8814237e1971d0e310146ec1ee8b166000e1f5495363484018beebb9ac48801f0f9d1650c7400046fc1aeca1c4200a9d8499763484f9938e72a2c91080297a172018d410056641aca31282068de8708063504011f700baac89081a3720d75587400045ec38a03224200e8e5418f62504011db0f318c4a094ea7a1021d8d410043fc2ae1b224200c3f65dd1214c0018beea31ac0a080a3ba0a76505300062fb2ee690a6006c9c639d26348401858e4b2a8220802a7a0e101912100747b18c520a8200c6c75dc9644400147b0b396c8981229ea0021d951043d57436c520a82038bf87553644c00147b0938eca980021fe1576cc91000477438a1b128200a5e8519063484ffc7660328c89801e8fa1021597400054ec26e1b1a42038bf87553644800156d02286c8909432761c640c53000573408a1b128200a9d8314364484a153d09a80c6a080327dd37358d210043fc2ae030a8600a9d84d4f635040d1b906bb443a0002ab61075d89412b64f438c89926000cdb709c3634840153b08286c690802b360e601894100637b2ee4b222000c3f75dd1644c00f17908bb08690002a760e101912101c3f43eeab226000a9e8414463484ad1bb0fb1c86a10029e60021d95300056741cc
  | 5 => 0x84e8f61372597400043f438eab1a2000c78655c0434400d1b906baac0219921fa1c75580310070fb28c99926000cd473dc564484070fd0bbb242980021f6177650d100043fc2aeca1a400087c865d4414c10987cedb28c89800237a1c40d8d210052f42ee1b1a8200c3f65dd1614c12bc70a0aa2c0218021fe1576cc9400051ec2885b2262008f7815d943480011bb0f328c69080317dd473591101046fc32e518e6000a9d84144634840193ec8b9cc89080e1fa1776505300046ec3843b1a8200ada8008763504011bb0e106c6a0803a3188635094101e1e3aca8b04860087d85dd9424c101c3b0632ec898002a760c50191210045fc22eab1a20018dc865cf424c0010fd0e32ac8980030f5d764985300051ec2440b288200ce7721c5644c8018d8e5b2ac2980022fa1c645812110666312e518a6207c3e7459732d00010fd0e10eca9800a3720d74d893001c5fc3aa9b226400acc8259763504070fd0bb82c5988022fe1d65191303553d40042b2e8000c9c64dcd214c001c3aca39a82208222f21d54593100061fbaec8b024200c3f75191614c0070fd0fbaac1109ef2b1ca545911000667b1ee4b028200c5f651cd644400187cebb24c2980030fd9774589100056dc02ca31a427ac9c7355164440010ff0abb4829821717dcc65591300045f438c890a6000c5f75d8d604840187eca3a2c29800a3760f75d913201c3e42aec20a6000c6c75d8960504018becbb9ac888002bae0165d89410062e3aee6b2220008df8759463504051bb07bb265a081f2e1917010d2000666310e6b122000a79801cb654404d47b08382ca20802b560c21d85430054ec264031a8200e1f5394f64484a753d083aec6a08021fa1c215974012e56310e890a20088f4815d5644c8033b50138c869801a3720d76885400056741cc63128200e1d5494063504018f0cbb8282880030fd9774589300055ac08a03224200ad980087635040193ec939cc8908023ee017558d210070e328c918a600087f855d8414c04b95ce432662908223721d634c8410466b28eec98862068be87d91434840d938c6ba063a00023de057558d202b54e422c6992208da9e84990634840d1b906baac8880030fdd0755824300ced406e6a0a6000e8c6218f42504011df04bb086880022fe1d641913100637b2ee4a0a2000a9e8499463484031b906bb2439800676a0373885300062e328e6a0a20568dd86dd132cc0c90fd0e3aac12180393d4e53d89410056741ce1b12820087f855d831500019c8e5b8ac68800e1fa17705884100556c24c03128200c3f65dd121440018b8ea39ac8880029e60021597400065bb26e2b126000a3d8498b654c0011bb0f996c29800317d9773485100043fc2aed20a4053c9e71190314c00187aebb2082900063e201755913201566412c69922000e1d541406
  | 6 => 0x1c3e42ae1b2262879ae87dc94110401958e9b92c6908033318f72581410052f418e5b2a2007cac645c8434840199cedb18c4a0802a76105018d212ce4e326e4a1a6000a9d83980644840117f08bb28488002a76135018d4100476c3cca31282088f8865c0434400d938c6ba062a01aeaba1050d89410346f41cec90a80008be87d4b644c0c353d06290c89818b8794f53d913003d1f426e4b288200a5e8508463504070ff0ebaec0a10031b5d475d894100657ba6e4b1a2000c6c65dc9414c0051bd0fb1a64a080395d4651d8d410046ec3c21b1a42018dc865cc414c0071bf0ea9ec6a0802a7a0c50191210051e422e5b2a2063a7a801d3654c0019a8c638a84a08023de1d61185300051f424c5b2a6000caf64dc9614c00117d0fa9ec890802b360e60d89410052f418e0b2882388bc875516010c331b90cb8e86990023b60a76505303253cc06e3b2a6000c3f65dd163440011bf0eb18c6a10022fe1172185300047dc02eab244207a3e84dc965d000187ae83a6ca8800e1f215768854000672396e2b226200c5c65dcd214c00153d09b86c6908030f197744853000c6e432e899260298ec86dc960504011790fb22429819297a0f71d95301c5cc402a6322600087f855c0614c80159d07328c4a081e8fa1373594410062fb9ce6b2882008bf8759464484051d904bb2839800e1f21570987423f70f180ca32260008f78758461500c94bd06396ca980032b1d37258d1000656310e8b1262208de8784363484011bf06bb2868800363dcc725044101476412eca1a2000c7775dc5634800117d0e322c29806733188734851000566c14c031a8200a9f84597634840187acbba243a0002b56045018d2104476432e421a4206cd8635c031480070fd0bb82c91894e37e0d764c7400063632ee4b22200087f855c3644c8019ae8638ac8991921fa1c755833243e57388c910a4200ccc73dc964484014bb0a108c6a0803876146418d2130e4e398c910a6000c3f651d163440010fb0bb82c5a180317dd773591100046ec38a031a422c8bf845d921d00010fd0fb2ac498002a7a1050d8d210062eb2ee690e800087d85dd9214c0018b8cbb9ac488142a7a102118d410054ec1ccbb224200c9f741cd64484411bf06bb243980022f61c51191300346e41aec21a2063c5e76d96314c00195ee8392c8880031799473487400054ec26a5b1a820387e85dc162d0c010ff0ab84c221a27a50846418d2103e4e322e620a6000c9c74d8d60484018d8e5b2ac6880faa721953d913000746318c520a826bcac64dc9414c00156d02280c8908030f5d754d912100637baec4b028200e4c62d95324c0018e8ebb8ac69000237e1d6318d210061fbaee8b122000a3e849c7654c0010ff0abb6849814f27193748c53001c3e42aeda0a60008f78758461508010fd0e3aac12
  | 7 => 0xdf8758e31440011f700baac4880022fa1f64581210051ec2ce3b22602ccac72d91414840d1b906baac4881eb271cd54592210052ec28c9b1a4200ad880597634840117f0eb20c8980038719653191300061e328e8b0a60038ef8754b625040117b0e10ec8980223e21d50580310045fc22eca1a2000a79809c965d00ad938c9ba26498002a7e0d51191301f64e3b6c8a1a6000c6c72195614c0c353d07290c898002ae60252191300147cc06ebb22402ccac625ca415047d17f08bb082981929e60074d95300063bb2ee2b126000c6c65dc9414400147f0ab20c89800317dd473589100052ec1840b2882208dc87d8d4148401c3d0a326c6908021fe1570d92210046ec38a1b1a42008ef825d564440010fd0fb2ac8980fb271db644c9300070fb28c89926000ccf73dc9644c523c70a0aa6c0a08030f19774485100064e3a6e6b1a42078be87140644840155f04a88c890803171d773591300061fba8c8b024200c5c65dcd21440010ff0ab86c89894f271927190d300061e32ee8b126000a5e8518b635040195ee5396c89819297a0c21d95300062e328e6b222000a9d83948644c00187ecaba4c2980031e1977050d3030e4f438c818a600087e87195624c001c3ea92a0c6908e3279d8648c5301f54ec18e5b226000e1d5454463504014db04382ca20802b9e0563189410054ec24ca31a42008ef825d943484c98b8e7b2a429800e1fa1776509300043ec3843b2a60078bc845d5634400f17908bb0868800e1fa177058b410046f438c6b024200acc825946350401c38ca326649801a2f21176d0d210054ec26a7b1a80018dc835da41cc00155904b20c8880031e19570cc5100043f438cab122007c9c649ce644840147b0810eca9800f0f1d6545911012d57410a632242068de87100634840193ec9b9a829081f2719173991210147743ee4b1a20008dd87990634840153d083aec69094ea7a1051d8d4103e1e322ea20a6000c3d655d332d00011bb0f328c6a0802a7e116318d210045fc22eca1a4000ad681140634847db34e1b2462980032ddd0715913212c5e43ac4a088200a3d8598b644c113d2e42320c690803875535118d410145f43ec8a1260008bd871436448401c3eca32062980021fa1c755822100572412c230a6000c5f651cd6244001d18c9b1264980023761e10d8d410064e324e3992600387e85dc16210c0187eca3a24288002a721165d8d210070fa9ca63224287cae76dd3625040157309a86c0a0802a760c40d91210045f430e890a6061c9f72191324c0070fd0bbb284880030fd9474485300056cc004231a8200a9d83103644c8031b906baac39800676a03748c5300043f43ecab1a202687c865d44144001c5aca3928220803171d7735891049d6bc1ac230a64018be86dd1215000f17908baac6908032b1c864585300
  | 8 => 0x8bb264880028fe1570d91210364e39ac8a1062008df835d943484015d100b28c4a0a1fa99c4648852103c5f438a2322420087e8719564440011bf06bb284880031d597714c8410463a38aca9908200c3c651d16344001878ebb22c0908030fdd4645893000556c10ebb226000a3c845cf65440c3938e6322429800aaba0b64509302cc6f43864b1e8200c3c75dd162440011ef02bb2869080e1fa1f7558d2003c5e422ec90e60028f4865c443484c353d06108c8980030f1d77458d100066db84e1b1a8225aae82840644840d1f301baec298002b560e10185322b64e322e521a6000c3f659d2614c00f878c8ba8829000f0f9d554d814103d1e422e4b28828fad58199463484b3938c8ba66498003175cc73d95100045ec3ea7b226007e2e8290965104018d8e432ac6880022f61c51d91210062fba8c6b024200c5c75d8d60484070f90abb48298002ad20564191320061e328e890a6000a9c8359764484019aee638ac6900031b1d472591100054ec1cca3224253a9e84d4b63504018f2eba86c0a18030f9d7649913001c3f42eec9922000a5d831c165104051d904baac6880032dd90715893003c5e422eab122000aad84d4f62504014b90ab18c6a00031b1cb65591100054ec1880b246200a9d84d4f63484a7938c9b9a829080e1f21576cc9400070fb28c8a1a600087e871d5644c0033b50138e64981bb27dcc64585300045f438a3b224288cb77119163484018baeba9ec690802b5205325873000666398c4b0282038bf87553644c40517908bb68498142a7a135118d4100566c1cca3128200c9f641cd4148401878ea3a2c68801aa720d54593320346f43ee6b1220068dc835d843884031bf0eb0c6398003339d863189410062e32ee6b2220068ef865ca438840f878e8b2a43a000e1f21570d91320061e3a8c8b1260198dc87589310c40117f08bb0629001e2f210764854029c6fc32e918e6000a3f845cb654c001938e839ac488197175cc65d85300cc6e432e418a600387c855db424400153d09306c69080297a0c21d95101f54ec1ee3b2260018de86dce214c10f55d0db244290802a720d64191210062fb28e690a2000c6c751c9634410187cec328c898002b360850d8d410061e32ee8b12207ee3830194644c001878cbba2c298002ae20165d912103d1f420e2b2e8000ccf731896050401b18e639282208021f61770588410045ec3cca3226000a3d8408765440ad938c8ba26498002b360a65d8d410061f3b2ea3224200cb7741c563480019a8c7b8a84a0802a760c21d91300447a40aeab224061a9c83544644c0015b500108c6a08029be1570d89410445e43ac8a10620387c855da214c041998e5b1a8290803a355063d894100636baea5b128200a9d84d4863504018baeba9ec6a080237e0d75591200052f428e5b1a82018
  | 9 => 0x715913200566c10a031a82018bc865d031500e9b4ee438a84a08028fe1172d95100043f43ecab222006cd8635c0315000187aea324c2980023761c4018d2100666396c6b02826baae84d4f625040f47d08382ca208063b2197290d2001c3e42aec18a8000ad583087614c00193ae9b1cc6908062f21974cc9400054ec1e4232260028ec825d564440c5938e7b228298002b3e096318d410147743ee4b222053c9c645d2314c00f1790cb9482a08021fa1f65585300047bc0aec9922000cce72d8e635040d1f50fa82c0218030f19474485100062e328e6b122056a9e86d91324c00199ee7b92c888096aba0830191210054f41cc1b224200c9c76d8d42504051bd0fb1a64a01fb8760c65191300043f438cab1a2002aac8259142c4041998e5b1a6290803331cf72591100056ac08a1b1a82068de870846350401c38caa98c8980022f61276485300070e328c818a60008df835d5624410f35d0fa12831094e37a1c63505210066a39ee2b122050c9c641c5434c0013a902ba264980b22fe1d62d06410054fc1acbb224200a5d85dc363504018e8ea38ac69000339d8871509410062eb28e690e8000a9e8414063484013a902ba2659800327d9373581210043ec2eec9922000c9c7418d604840f17908bb062900031bdd4725911000667b9ee4b244200aae86950625040159d0732ec4a080237e1d63cc9100446e43ac699482008ee87d89605040153b083aec6908021fe1f651051000c6e41aed10e6000c6f65dc9614c00117f0eb20c89900297a0c21597400051f42ce5b226007c3c645d4644840d1b9063b2429800f0f1d5545824300c7c402eab224200a6e821c16510401958c43a2c488083339c962cc6311c54e432a632260008bd87084644c00d9b0c6b8086880022fe1d64191100061f3a8c930a6000c3c655d2614c00147b0810acba000237e1d6318d400061e32ee8b1a2007cac645cb41484010fd0fb2ac488002b62016518d4103c5e422ed10a60008dd87103634840d1b906baac910986a7a1b640c53001c3e42aec21a200087e87c8165104011bd0e31ac4a080237a1f63581210054ec26e1b1a826be2d85192214840117f08baac4880021f61776505300065a326e2b1260008df8758c63480010fd0e3aac690002a761051d8d4129d4f420e5b1a820387c855db424c00117b0e28ec8980023761e1018d2100567410a1b1a8279cac7255164440a153d08288c6a0803939d7631894100667b1ae531a820387c855c3625040159906b2ec4a080237e0d75591310064fbb6e6a088200c5e75d8c41484011db0e286c4a080237e0d75592210061f3aec820a4200e1d83909651040117d0e286c8908222fe1d6490f1001c3f42eeca1a20028dc835db32500015a902b18c6a104e8f610715974001c3e42aeca1a2000a5e83081651040f179
  | 10 => 0xb0680140000a024004098110043f80403103405c150150080140600400e0c80100700c2201300101e0380181603e0001880400e2180000d1240040000903c058a000000203000000004044008160260680000a00009c0182100000ccc73d896050401958c9b92c2980222f21d6450b100045ec3ea7b22420387c855c36250c0117d0fb22c2981dea760e62191300070e328c8a1a6000c3c72595411040153908b18c6908029761770d8d2103e4e322e7a0a6000c5c651cd21440031f100baac9108022fa1c51d91300054ec20e5b1a8200aac8655062504014bd0a310c6a0896ab20951191210045fc22eca1a4200c5f65dcd414c0c3c3ca7a98c8980032bdd8725044100673b90e2b1a4000aad84d4b62504070f90ab86c4988023ee01755903101c5fc3aa9b224200c3e75d90414c10d9aee231ac0908232d947765044103e5a324e221a4238ab88054c644c001998c5b9ac4a098f171db6550d3000ced406e690a6000a3d85988644c00187aebb24c89801e2fa1c21191300052f42ee1b1a422e8ef865c74288401958e5b2282880021f6177058a310046ec1ceca0a4000c5c751cd62440015c904b08c2a18223e219700c5200055c402ca3224200aae82dc7644c0111790eb22851898e1f21b75585300051f42843b226063c5c76d95324c00159b05328c6a080e1fa177058a310065aa8eeca088200a3d85087644c0015ad02286c6a0802976146418d210054ec1881b226207a9e86d91434c00117b09bb24298002b3e0d65189413e64e39ca8b206250c9c641cd41484011dd0e312c0a08063e20175591312854f426a431a8206ccc635ca63504111790eaa2c9108023de1d611854329e4f438c918a600087f855da4344001c3d07212ca20803175d475d8d210061e3aec8b0a60208df8758b318c40d938c6ba665a000a3720d76ccb4101c3e42ae1b2242028dc835db32d00c94f300396ca980032b1cb6450530007472a6c63128262a9e831d7644c0c393d0e32664980063e20175587430043f43885b2a2000c6f65dc9634400153b08286c6a08023be1d65189410045ec3ea63224208ce47158932104011df04baac6880030f1d774591300054e422ca31a4206cd4639c643504019aec638a86a0802b3a085018d410070e328c899260508de87d8d414840d1bd0e280c6a0802a7a1353d8d210063c3aee0b22607baae8419462504014bb0610eca980063720d76507300346e41aeca122026a3d84dcd651040159d0532ec6a081a3720d74d891001c3e42ae130e863ecb870d91434c00153906b28c89080e1fa1f75582430346f43c2031a42538df8758e43904018e8cbb8ac4980021fe15760c5200063bba8e2b1a4003c3e7555161d000193ee9b9ac48820f875cf651913031ead386cb18a6081a3e86194644c125d8882318c4a08033510c
  | 11 => 0x700803b0000643a80a0181442e80102204c0180a03c12c03801008020000285d40c0000000260840e8670020300180502a03c0100700a0000f000046004150070ae2080580f02e00c000430260145780501400c5718b002068408e100200c16800000084058450020000080001a024150000020080581300001c0b0080020481c00a05004c0c8430301900c80100023c00032000410000090000101900200005005000006028020120300040b06908e001290010b60040300b0ea5f4008030022580000000a1580f041000028018000180400003e0600a838825004098000012ac04c0083b0020300000500a0380200f0080003402c1800382180004c01c0504b0140048605a0000e8010ca0020140580c10600c0000000c0102480508602ca481f10c00407007046030048150560440e000004024010230020141e0970360040007f016000030070042100000301400c070b20020980000100c0b02e82a00a000000000e41840100002003c260020003f00081a0180000000100c0a80203701c028010010160100000b000038160350c606c0d80e00025c0a0000b40002780a000002390080060d00604405200c0902c000014000090480040180201006c01011000000221dc10c210108000021380300d006028040020000680086e0080208301a0000040400d46a00402008004d680900735001c0000504000c0500100e0281500801c0bc1201b048000020000000000d82e0000142180100209c020000202000606b00001800804000044058080000280002f00202c0780001615c5900e004348000140000001500a042034208010088780281c0b00a816003036008000000100000117e00e054010010240142600f01c1e8038000e00ec00012006020000001200502d00000c0201907c00403c038040143ec01800000000188000000140300300c1801400101006cb100802a02401
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2200182d981c9655044100703597731c9411040189464205744c9300068555181140635040182e981c965504413f6862006554c644c001a0d546085018d413f7069c065192314c00103d98194744851043e0ba1d65dc94110401c0d651cc7250441
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x6
  | 4 => 0x94b
  | 5 => 0x94e
  | 6 => 0x4
  | 7 => 0x5
  | 8 => 0x2
  | 9 => 0x138b
  | 10 => 0x138e
  | 11 => 0x98e
  | 12 => 0x9cb
  | 13 => 0x9ce
  | 14 => 0x168b
  | 15 => 0x168e
  | 16 => 0xa0b
  | 17 => 0xa0e
  | 18 => 0x180b
  | 19 => 0x180e
  | 20 => 0xb09
  | 21 => 0xb0e
  | 22 => 0x1409
  | 23 => 0x140e
  | 24 => 0x249
  | 25 => 0x24b
  | 26 => 0x24e
  | 27 => 0x144e
  | 28 => 0xb49
  | 29 => 0xb4b
  | 30 => 0xb4e
  | 31 => 0x1449
  | 32 => 0x144b
  | 33 => 0x16c9
  | 34 => 0x16cb
  | 35 => 0x16ce
  | 36 => 0x289
  | 37 => 0x28b
  | 38 => 0x28e
  | 39 => 0x148e
  | 40 => 0xb89
  | 41 => 0xb8b
  | 42 => 0xb8e
  | 43 => 0x1489
  | 44 => 0x148b
  | 45 => 0x1849
  | 46 => 0x184b
  | 47 => 0x184e
  | 48 => 0xcc9
  | 49 => 0xcce
  | 50 => 0x1709
  | 51 => 0x170e
  | 52 => 0xd09
  | 53 => 0xd0e
  | 54 => 0x1889
  | 55 => 0x188e
  | 56 => 0x589
  | 57 => 0x58b
  | 58 => 0x58e
  | 59 => 0xe89
  | 60 => 0xe8b
  | 61 => 0xe8e
  | 62 => 0x1789
  | 63 => 0x178b
  | 64 => 0x178e
  | 65 => 0x18c9
  | 66 => 0x18cb
  | 67 => 0x18ce
  | 68 => 0x138956
  | 69 => 0x98956
  | 70 => 0x209
  | 71 => 0x1549
  | 72 => 0x14c9
  | 73 => 0x2c9
  | 74 => 0x4b
  | 75 => 0x124b
  | 76 => 0x15c9
  | 77 => 0x12cb
  | 78 => 0x1609
  | 79 => 0x130b
  | 80 => 0x24d
  | 81 => 0x249d6
  | 82 => 0x9c256
  | 83 => 0x144d
  | 84 => 0x1449d6
  | 85 => 0x9d456
  | 86 => 0xccd
  | 87 => 0xcc9d6
  | 88 => 0x9ccd6
  | 89 => 0x170d
  | 90 => 0x1709d6
  | 91 => 0x9d716
  | 92 => 0x3c9
  | 93 => 0xe89d6
  | 94 => 0x9ce96
  | 95 => 0x1789d6
  | 96 => 0x9d796
  | 97 => 0x10c
  | 98 => 0x130c
  | 99 => 0x17c9
  | 100 => 0x134c
  | 101 => 0x5c9
  | 102 => 0x169456
  | 103 => 0x168cd6
  | 104 => 0xcb
  | 105 => 0x168e96
  | 106 => 0x1049
  | 107 => 0x140d
  | 108 => 0xb4256
  | 109 => 0x16d456
  | 110 => 0x59451
  | 111 => 0x59456
  | 112 => 0xb8296
  | 113 => 0xb9496
  | 114 => 0xb8d16
  | 115 => 0xb9896
  | 116 => 0x20d
  | 117 => 0x185496
  | 118 => 0x184d16
  | 119 => 0x58cd1
  | 120 => 0x58cd6
  | 121 => 0x104b
  | 122 => 0x104c
  | 123 => 0x194b
  | 124 => 0x194c
  | 125 => 0x585d1
  | 126 => 0x5c591
  | 127 => 0x14114
  | 128 => 0x5d791
  | 129 => 0x597d1
  | 130 => 0x59a51
  | 131 => 0x17c591
  | 132 => 0x17d791
  | 133 => 0x5d8d1
  | 134 => 0x25253
  | 135 => 0x40a
  | 136 => 0x296d3
  | 137 => 0x28253
  | 138 => 0x29453
  | 139 => 0x25493
  | 140 => 0x25853
  | 141 => 0x24293
  | 142 => 0x149453
  | 143 => 0x24bd3
  | 144 => 0x29616
  | 145 => 0x104b91
  | 146 => 0x24215
  | 147 => 0x25453
  | 148 => 0x29493
  | 149 => 0x104591
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2111
  | 6 => 4477
  | 5 => 1515
  | 4 => 11
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
  | 7 => 2*((h/710+packedAt gbK7 (78107+(h % 710)*12) 12) % 2111)
  | 6 => 2*((h/1548+packedAt gbK6 (214896+(h % 1548)*13) 13) % 4477)
  | 5 => 2*((h/568+packedAt gbK5 (89385+(h % 568)*11) 11) % 1515)
  | 4 => 2*((h/3+packedAt gbK4 (770+(h % 3)*4) 4) % 11)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff07e01f81f07fff83fe00067b19fe20fe7c
  | 1 => 0x7803f8001fffff81ffffffff19a4e6603f1fff
  | 2 => 0x8003ffffe001fffe0ffc1fffe1c70787c3e38f
  | 3 => 0x3fffffffe00000fffe000fe07f807fc03f0
  | 4 => 0x3fffffffffffff0000000fff80007fffc00
  | 5 => 0xfffc00000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x887b01628590702a93a33206020908ae206e3c
  | 1 => 0x508828000aa29481248444aa08a062600d14d5
  | 2 => 0x11152aca001294c0969195461470582c2a30a
  | 3 => 0x2239cd6d35400288e739018b607b8077403e0
  | 4 => 0x4442e71b1c79ce71c0020060dff80005bbd800
  | 5 => 0x6780001c00600c4100400180fdf6d750000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40513
namespace PEqualNP.Outside.L_meta_40513
open PEqualNP.Outside.L_meta_40513.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := bs2_5_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 2 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 6 := bs3_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 28 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 396 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 601 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 11 := bgb_4_0
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
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 75 := block_range (n:=75) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1515 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 bgb_5_672))) (concat (concat (concat bgb_5_768 bgb_5_864) (concat bgb_5_960 bgb_5_1056)) (concat (concat bgb_5_1152 bgb_5_1248) (concat bgb_5_1344 bgb_5_1440))))
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
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 61 := block_range (n:=61) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4477 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 (concat bgb_6_576 bgb_6_672)) (concat bgb_6_768 (concat bgb_6_864 bgb_6_960)))) (concat (concat (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248)) (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536))) (concat (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)) (concat bgb_6_1920 (concat bgb_6_2016 bgb_6_2112))))) (concat (concat (concat (concat bgb_6_2208 (concat bgb_6_2304 bgb_6_2400)) (concat bgb_6_2496 (concat bgb_6_2592 bgb_6_2688))) (concat (concat bgb_6_2784 (concat bgb_6_2880 bgb_6_2976)) (concat bgb_6_3072 (concat bgb_6_3168 bgb_6_3264)))) (concat (concat (concat bgb_6_3360 (concat bgb_6_3456 bgb_6_3552)) (concat bgb_6_3648 (concat bgb_6_3744 bgb_6_3840))) (concat (concat bgb_6_3936 (concat bgb_6_4032 bgb_6_4128)) (concat bgb_6_4224 (concat bgb_6_4320 bgb_6_4416))))))
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
theorem bgb_7_1536 : Interval gbAtlas 7 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 95 := block_range (n:=95) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2111 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 bgb_7_1152) (concat bgb_7_1248 (concat bgb_7_1344 bgb_7_1440))) (concat (concat bgb_7_1536 (concat bgb_7_1632 bgb_7_1728)) (concat bgb_7_1824 (concat bgb_7_1920 bgb_7_2016)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0feeaeeeafce8c8c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4243114176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40513.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,5]⟩,⟨.or,[1,2]⟩,⟨.and,[4,7]⟩,⟨.or,[5,8]⟩,⟨.and,[0,9]⟩,⟨.and,[1,2]⟩,⟨.or,[10,11]⟩,⟨.and,[1,6]⟩,⟨.or,[8,13]⟩,⟨.and,[3,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243114176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243114176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40513

open PEqualNP.Outside.L_meta_40513 in
theorem PEqualNP.Outside.L_meta_40513 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243114176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243114176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
