import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40441.Model
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


end PEqualNP.Outside.L_meta_40441.Model

namespace PEqualNP.Outside.L_meta_40441
open PEqualNP.Outside.L_meta_40441.Model
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

def SBf (j : Nat) : Nat := [7, 7, 8, 8, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_40441

namespace PEqualNP.Outside.L_meta_40441
open PEqualNP.Outside.L_meta_40441.Model
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
end PEqualNP.Outside.L_meta_40441
namespace PEqualNP.Outside.L_meta_40441
open PEqualNP.Outside.L_meta_40441.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x153010414401c01c60000c90000402c508f10e000fd43fe10ff41fd42fe31be40fe43fc31fc21ff31ff42fd20bc40fe42bf41fe20fd21ff40fe41fc42ff43ff32bd41fe21fd31ff20ff30fe40fd40fc20fc32fe30fc43fd10fc40ff10fc41fd41fd30ff21fc10fd32fc30fe32
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x87069df83260c000243c1833218005001421100001ce020400014800004a080444001c817a08206001c499af29c815c534427aa2205dd4530bba8a415d5308278a8885714d42b6292615e53c86dea4a0dd14530af298213d54c827ca0205b14910b62928378505075ea4a0ce141419faa2619f53506bea6a14f550109f2a6213f54442f6a0a0db94a319eaa6215f5348338a6a0e794e40aea9c433e50d0678a8994f55221b6a94636f5244374a0206e14141aea98215c534827ca8085754e40b7290213e54cc27ea9084f952319f2a4436c5250e7ca9905b94830b7294816d520427aa3205754f21cea9c813d5490678a0a0d794c209eaa0433e50902bca710cf55231d729481cd320cadaa5206e100109eaa6616f5250ebea6884f15130b6a9061bb50506b8a6a0d7d4d419faa2653c5448358a4a0edd45419f2a063ad52902dea4984f950219faa241b840c4278a9085d145209f2a0836e52cc6daa598cf55031
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1058003ca148505071b53141418e59440043185314141a3191320cb0e5394a40c314c525072b5214141
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s1K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/51+packedAt s1K4 (2484+(h % 51)*7) 7) % 92)
  | 3 => 2*((h/9+packedAt s1K3 (304+(h % 9)*3) 3) % 8)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 3 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x84882808c489082016514a284a212954133615
  | 2 => 0x11245191091260c580a4148694c652a8c888ea
  | 3 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0faaaaaa0f0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40441
namespace PEqualNP.Outside.L_meta_40441
open PEqualNP.Outside.L_meta_40441.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x210604000900024710004124300400240008d001fe30fd21fe43ff10fc30fe40fc31fd41fc40fc32fd43fc41ff41fe21fc43fe32ff32fd32fe20fd20fc42fd40ff42fd30fc20fc21ff30ff31fd31fd10ff40fe31fc10ff43fe41fe42ff20ff21fe10fd42
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2837d520c7de85907714d20efa1c877e53082fca5197b88620ef29e43df310c6fea6085f94c419faa2217e53906faa3a05f14d40bea9c437e548c6f8a910df54843be2a2217e530c6fea89857d4d41be29c217c5150afaa7a05f55021efa9a417c524c67ca818df94f21bf280877d52d02fca7215f55331ef98c63ed52cc6faa9905f14e20fba8a877e51906f8a8987bd0a42fca80437e540437a84214f15110fca84857e53d02fea990df54e32deaa661de438c2fea9997bd4910beaa6437e508cafca3a1df14f10bf2a2637f53c86fea6a0f7cc230f729663f741907bc87995f14141aea98837c53486faa890f7d0d43bea98837d53c43bc8621df54041be2a063be54cc2f8a8085fd4930bf29087ef52506fca210df95130bf28c857e510c2fca2205f54a21bf29421bf4290b7c80a07e48210bf284437d528c2fca7205f55310f6214437e51042fca9986f95031ee990637d50ccafaa7185b54830bf290637f504c77a8621f794c41bea8881ef42483da4210dbd49109f2a6615c53482f8a9985f54f42bf2a061f741506faa88857d4d20bf29461dd328c7da6410fb14910bf290657c514c2faa4886f50040bf28687bf41106faa5a0df14e21f790c437e500cbf441085f95110fb88021dd430c37e87205f94042bf288657d520c2fca6205f54720f7190437f52442f8a099774c832be2a6217c540c2faa3185fd5020bf296817d51d0efea8995fd5210bf296877d50d0ef4a010df55031bea9e83ed320cad8a4a1dbd4941bea84637e5090afaa3215f55330bca8485ef4250afaa5885f54331bf28885f610442fea2907b10b32bf290837e5390efca9185f94331fc980617d538427aa9985f94342be29a417d5310aeea2a1f70c630bea88877c54c83dc64194f55031bea94637d53443be6418df94030b6292217c53082fca6195f14b10bf28c87bf43102f8a6a15f54730fc206217f52506fea6906f90a40bf2a6657f54883bc63187bc8020ee21863f850506faa9205f14943be28243df328c7de41105f94720be282877e54cc6fca990f790c30df210817e53c43b88718fed0310ee29a837f54cc7f4a010df54643ef980617f52043f4a1215f54232ee194617d510cb7ea8906f50e40be292217d52907baa620df95221ef990657e54487be8618fd8c431ef19265f940103ea8220efd0d41fd982617d53882faa9995f95043fa28a877d53902fea890fdd0431bf2a6217f514c2f8a9195754f21f7290217e5410b7e8721df55132bea9661fa300c37aa818df54c21fd88221bd43103de8410df54a10fa98863f641107bc8698d754c42bc28283ee21486faa9105f54321fa10c217f54482fca1085f94d21dfa04817f5150af8a098fb4ca21f721085df438c77e84217b54810bfaa4657c53c86fca9905f54f20bf29621f721843da40107b94a40
  | 1 => 0xd548c6f8a8995f94f20f790e417d52d0efaa6205fd4143bfaa443ef420cafca6085fd4e10bea9e433f54482fca121f714d10fba8a41dd434c6faa3a17dcc531ee188617c54842faa121df94040be28a87bf4310efaa9195f94c42be28a417f52842faa2215f15332ef19461fb405037c82205f55243bea80657e50d06faa4205f94230ef994657f52c42fea0a16fd0f41fd984617c54883de64995f95020bfaa2637f53c82faa3995f55032fb98c63df53442fca520df54d20ef188617d50086fca120df95210bf28481be41507f080085b94a40bfa9a817c51502f8a6a0df94332be2a241ec42482f8a4a05fd4132bea86857e51883e88218df14c10f799465745150efea710df94031ae29a217e51d03f62108770c830de214817d544c6faa5105e94242fb90c437d5390b7c84a15fd4121fb108437e54103f680085fd52319e2a2417d54906fca6887750f31bf290816e520c2bca6217d48421fd90241ef21483f480207bd0a21beaa261f7214877884205f94220bf29221bd43d06fca91057d4d10bf298437e51902fca0107b08420beaa4617751483ee21085f54241bfa82837e53482f0a0a1df54640bea8c21dd53d03f220085f94c30bf288837e5310efaa521df15231fda82837e544cafca5207d10731bf28841fb5050efca221fb08620ef29885f8400c2f8a898fed0240fa880217c54486faa3195f55120f7a92877d50886f8a6885f94b41be290217c54086fca710df94632bf29663dd300c3da43905f54c20b6a94817e520c2fea810fb4cb20be29421fb20882faa8185fd4540bfaa065ec52506faa2187ed0030bea8683de53d02faa690df94f42b7290217d5010afea2997790f31bf29c217e5290afea6107750d32bf29e83f840482fca010df55221ee988637f53443e8a2905f15032f7196417f53882fea4a05b54810bf28e857d538c77883205b54b31dfa0c83fb40483da42905f54841bea8087de320c3de85995f95232eea1c617e51ccbde4210df14f20bfaa0617e518c2fea2a1df54a40bf290215d53d03bea6a0db94b31beaa0417e540cafca8905f95041be2a6437f540c6fea9185f94821bea8841f840882fca190d794c41bea80637c53087f08198778c531bf28e61ec42086fca5985f54810bf28c437d54042bca790df94631bfaa021f920082faa598f750f32bfa9e217c54cc6e8a2907750c43fda0441f920442d8a4a0dfd4d42dfaa22179500877882205f94041f699241ed520c3f420085f94010beaa4857e528c6fea9905794f40dea0883fb40cc2faa9085f54e41f6a10857f524c7bc86995f15020bea98217e510c6fca521df95031bda8287ec420cafea8885f14142be2a461f421043dc64907e88020be28a657e508c7ee42086f15110bf2a0437c52506dea4a1fb14943bfa9287fa20442faa1217b88420bda8
  | 2 => 0x613280601ca0400100ec39004420000c0044a0145100002038041400c2c4010000335811000001103946c2a000050bc0b014130083300c010ac0000c02000040ec2c0202c000650000108400040060080000000000640000403443000250301f00c03000390001e0000c0000a014030780000000058152880b0100001800000000300066c09010130000b0000708c060800c0180400d3c01c00030000640902cf60542b000000000305c00000030201e064031b0050040201c020000c0241403c10038c2054030d834028030300602c000703109c0400000000030002202c01008000780a0580a0007503c000680500817048011ac09000000001412c000001e0540202418024030542900001014042ac000802f004170002f00c0009c0113400020000003d0640107c0d0000700c000941a0001203c090501600c0001817018120000c05c00000020140100c0300400054010244c004000042d0081f008000144c2380600400bf290415c53506fea610fe14143be29261ee20482fea9887b94830bf29c41ec42c837e80207b8ca21bf290857f54cc3baa790df54620dea1a83dd5310bdaa5206f15120fba0e63be41903bc60985fd4d21df21a877
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x14110677615513297d8d52442cd6310821d9146204835453d45208f59053c42cd63c84219b58a53442796510030aed81431026d6294d219bd89511025e63150329b596320873b60553308f99053c82ac6250c408fd95401023f6454d2197d8d5090b585310120b918520082e8604c920ae582421026e62d4c10da54b409026c6255110b358b318c66e62d52319b58b54cc66f6255132b358b310c66e65d0920cb153524427b654802097195434c71c54d4d20d350d52cc67b65440109e983540871d53d0441ce181540c76852d4143e5d0f410c67a60d5032d954b210431d5410c31ce55040cc27561150309dd95210863e651512097597430c66f62551319ed81544c66f6254630ce191500879543d07318f59053886776544010d94c851483693254021ad185431025c63547429ed81544865c63540219bd8951d0e7561150209758e524436852141419d586544825d6314a108f990530427860551329bd89540c7385488110c715053443346155031dcd445050f645214543da14a20442d46350441cdd53514826d62d4c109b588538427561d52308f990538863e6515110dc1475050e7a60150219e583540ca6f6255310d514f415071c54d4d10dc1444048278605533297d95300c36952d0030da54a100436921540219b59442087345414520d31895310b1d544c8319e59610042776155120d3d4c525063e6494d20d314c524426c62546309798c54c426c6255310e650c400c2db6050c30d9d4b5150e6c654c92097d8d544c63d6414c219798c540c69d640c430d9185520427661150208f992538426d6215010cb18954cc2796510010c715053482cc6250c30d354a310c26f6254d10cb54842902796014c21d6d4c505074f53149109758e544c27761549109d185544c25c63542419ed95300c23e6414f108f59253443585314141d390d52cc74d4354830ab18943902d46150d32dac85500873b64540219b58b548c65d63152219e983548ca9d631084097d954310e746154d209718d511023f6550842d5d4c51482766115030ce904505074d520c4309b98a50d075b6354021d9145214826d62d50309d987548ca7661153329b98854cc7394314141ced81540c755510c430b3189438c2766194d20b5185430c27761551318f99253442cd6310b32ced50404826e62943439b98a534426c62551319b988530826f654c832ba58a401023c6454d20a7590318c25f63542418f59352c426e62150109e983548c6b46150e409e583548c65d6395110d314c525071d54cc831cbd5352442cc6250f32c714f435065d6510c318fd91508ca3f6550c43da54b400434d528c8309d185544831f54d4d209b58854cc73554d04318f191534427960d5321a7593300c26e62951109d185544ca3d6494d209798f54c876852141439b58b54842d46150e30
  | 1 => 0xcb7051141439798e534425e63952209758f52c426d62951108fd91500865e63d4b109e583540867b6054d21c7553430c72f6255031c7151434ca5d6394a41c7d53534431d54cc431ce583544825d6315321da580524431d544c4318f1915008769524401097994534425f63547429758c540866e62d5230d5185531076b4254242d914a104423c64549108fd91534423f64542319ed8154442d563107319b997214827765504418f596540c6f16008610da14b50506d46150c43d9d485150f4e4354830b5587320c75b53d41419798e520865e63d5210a758c429026c6254d108fd91524426d6510832dad4b505067b60553328f992544825e6394910d5d0c5150f5b6054f409bd89544867b6055130b5185434c679601502197d8d500867860550319718d518826f6255130b358f214825c63551109b98b54cc74f53d49419b18954cc27a65d01209e181548869d63d00409b988538425d63150209d987548c35753d45208f59053c837160145209e58354cc72f54109209e181534876842540219798c544865e63150108f592530c36b52141419798e544433454d45209b988520425f654c832a758c419025e63952109758c54c826d62150309d594410c65f63551209e980520423e6414c219ed81544cab46150f41d514c514825c6354910da548400425d63d52108f592524434c5310920b358c424836a32540219718d54486e5618c821d618d500867661d4c209b98b540426f62553308f990540c67a60d5020d3d4f52442776154d2097596430c2f061482109d587530834c538c9209798c54c876442145209b988504c74c53d4910dcd475050e5f63544409b58b548c26d62943438f592538425d6394821d614f505066e62949109798c528426c62551309e195204435853d01209b98b548426f65480208f992544431f5414d209e181544c67a60d53318f191508cb1c6355031dad09500865f63546209dd95310c63f65504419e583530871d5350441cbd50524436632145209ed81540c6cd6310b20d314f525073754145209b18951d0f2c62550319b988530434c53d09209ed95401025d63153109b98a53c42d963d00309b58a50d067561153329e181544867561d5232ba580218826d6294f109e980530866f6548421dad485050e7b60552219798e544825f6355121b358f21c825e6590d319e98252d066d6214c10ce151204423c6454231ba580210826e62d50309e98354c865e6315221a758f40902e462440108f590530425e6315021d9d08514825c63542429798e534825e6315320cb58b544825d639522097d8d544434d6214d209b988540c36452d45439798e529065c63551209d586534837051d0120d618d5090a7a60d4c2197195434ca5d63952109d594210426f65508429758e54482b86444010ced0c505065f654c431ae18
  | 2 => 0x301c3e010183004101e8940001000885a0400020220009814ec04030d8000f03801b6430000000210a98cd81a310185a0000014d2090601c620217800100305000360c008a8ee000e8201401001f40a006780004000b019ce0204820120700014000600134000b000296200110000c0000944100d00a10142e00014064c070b0003f2301c1206008006e074b8240443001303019048109e830f000001100000041d1e0701849000f80a01060483020310240402001c436250103f0a0a1b0083207098a91c76168976451c8520c7d50534429d63104409758f54c872c5414910b518543cc66e65149108f191534866d6594810a7593308c3e02188210f8c85208427761551309b588504c66c62550318f992524426d6588420b358f218866d62d5010b9584420863e6494c309b98b540823e64d4b109e58252d06d46150f32cbd8954cc33854c41109758c544876b52d4143ba5824210a3f6454d20ea108404826c62544409798c54082cd6310a219758c540427661951209bd89544435b6354242da548400c25e6514d209e583548
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x80036005823c192058058654c6050441c30c831aa010c4d7614c4248322b18a390a418555161cc831c1aa8b166218d61711095008784a1aa420061515cc4214520ac2e3192a010d907150c400c3842988420241581c132145209c4ed90a410863061181540c6a238a86a9061455d743d0431c50c4302a818d30745805148390210a220241511c54354b31c2ac8a88621861454185434caa4b9e42a80438a1915244010c1ac8a9062185897310840482c43928620061525cc4254021
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x420b008150d52100309098714c4210120b01831085110120
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
  | 4 => 2*((h/178+packedAt s2K4 (17974+(h % 178)*9) 9) % 473)
  | 3 => 2*((h/16+packedAt s2K3 (1421+(h % 16)*5) 5) % 29)
  | 2 => 2*((h/8+packedAt s2K2 (180+(h % 8)*2) 2) % 3)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffe03ffffc07ff03fffffc0ffff80fcfe3fc7
  | 1 => 0x80fffc07ffffffffc0fc0fff03ffffff23c7ff
  | 3 => 0xfffff80fff80ffff000ffffc1fff03c3f8f8
  | 4 => 0xff0000000ffffffffffff000001ffffffc00ff
  | 5 => 0xfffffffff00000ffffffffffffe00003ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x86129850a04712300b2c52c434a594544e1bc3
  | 1 => 0x2a44293144892452c055055512caa59922c55d
  | 3 => 0x549850a269120eb5550249a6b8935652c368e8
  | 4 => 0x18d162c58e2448e9a69b6030a21c78e3f400b6
  | 5 => 0x60e183060c3870ce38e38e38c3006083b9b600
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88cc880000eeaaee88cc880000eeaaee88cc880000eeaaee88cc880000eeaaee88cc880000eeaaee88cc880000eeaaee88cc880000eeaaee88cc880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40441
namespace PEqualNP.Outside.L_meta_40441
open PEqualNP.Outside.L_meta_40441.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40618a0000876d408000701c4820c7143ff43fd30fc42bf42fc30de30fd20fd41fe32fd43bc40ff42fc41fc32fc20ff41fe20ff21fc40bd42fe30ff10fe40ff40fd10fc43be40fe21fe41fc21fd31fd21dd32df32fc10fd40fe43dc30ff30fe42fc31fd32ff20fd42ff31fe10fe31ff32
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x61bd32102faa810ef90e40ef2a6657c548837c87a16f50e40dea1461be4350f7ca32077cc941be2a221dc528c3f660987e48210df99481bf420837e85205f94e10bf29e837e531037a84195f94c31ef29843dc53507ba64a0ef50d42de21081f6210877a84985f14940bea9c41df518c378a2a177d4d40afa9a41bf544c6fca4205fd4930dea90817e51902f8a7907708430df2a621dd53c83f641105754c42aea9461df4390ef8a2a1ef90020be2a6437c548c2fea890efd4142ae28265de324cb7e85996fd0930ee996417e5310efea918efd0921de206617c53442f8a2996f50f42eea9883dd32c42fca020778c630eea1a63be4250afaa510f754f10bfa9a83bd21903ba85185f15131ef99463bd42ccbba6518f754c20bea88817d54482faa3a1ef0ca40bf28441bd54c867aa818df94c20dfa9e85bc40043bc84187b88420ef29c85de43cc7bca0184f94240fb98a63de410c37ea8985f55320be2a6413e54c87ba63185f14d41ee2a0617f544c37c80986f14c40cea1061ee4210b7ea4205f94c42eea9843df528c2f8a4a0f7943329faa441df320c37a8410d794f21f710a43dc408c2fea9885f55332bea98837d520c3ba642077d4332bfa9c43be54c837aa3a17754732bea88657d5490fba6420f7cc840efa1a87fa50086fca118ef10110bea9e417e528cbf440105f55331fb08221f721042fea0a15f54241bea9c61de504cbbca7905fd4143ef298417d51c837a652077cca32be2a4657c5150afca9197714d40af298437c53087bea818778c320faa88417c52442f8a8996fd0a30dea12657c544c33c801867d08309eaa465dd518c27aa810ef10210be2a4637e52906f8a9885794230bea8e61de30483be60185bd4910eea1e63dd548c2faa3a177ccb20bf280657d538427aa8105f55110dfa0c837e53106f8a29877cc931bea9621bf42086fca598f750c43dea9a85dc418c37c85205f94d21bf28485dd324c7b86318778c310de2a2615e50ccbba65a0f754532df20461f521c42faa710f7cc841ef996217f5150e7ca81977d5332f7908433f54482fca99877cc831afa9c417f528437a8520df94f20ee18021ef524437a85987d88510bea9e21de53c43be8718774c831bf28483bd540877e84996f10e41ef99241dd53d03be86995fd4b10de290817e5110efca42173d4932bf296617f54cc2fca310cf55242bfaa6415d53087be83185794e42f610c41dd5310afca3996fd0b30efa1e657e500c37a84085f14810ee996637f544c7be6520f74c920be2a421df32d07ee43085f54d20de2a2413c544437aa7a15f94c32ef28861dc30442faa7195f95030fda04817f53c437aa5205f95210ef18041bc539037e42205f95310ee21c617d5010ebaa790df94f10f7190657e50107ee4310efd0a41ef29461bd40103bca790dfd4d10
  | 1 => 0xe52d02fca3214fd5110ef190617e53d03ec438857d4d10beaa483be5350a7ca1a17b08420dea10817c54cca7ca818d794f10df18c81de304435ea4a177d08309e2a241bf4290bea8220df54b30fa90a21de520c2baa7216f50921dea1a83dc428c3bea6885f14e10df988813d521037e84196f94142dea1465de518c2fea8105fd4520ee988617f5150afca9995fd4c20be282437c53c42fca3a05f94c21ee18641ed210877ea8886fd0441dfa98817e5190efca421df54c42bfaa443df32886faa918efd08429f2a041dc514cbb882186f50b21efa1c63bd21103ee4290f70c310ee18861bf420c37c86206f90030bea9083bd42c837ca0205f94a31bea8465dc424cbbea4186f50831bf28863de400c3b885996f50a21dfa1c877c50506faa910f710e31dfaa2417d518c37a849077d0c30bf28461bd51102faa8086f50b10ef10c61dc304837c65207750630be29a855f535037aa2a16f10020bea9683fb405037e85886fd0f41dfa1465bf52903b88618fd08410efa08613d54c437e63205f94d20f699065df218c2fca4185f94332bea8463dd420c2faa5087714132bf28643de308437aa8106f94e40dfa16417c534867aa99877cca10ef98c637f514cafea7085f54732bf28481bc408c2bea6a0dfd4e20dea18877e5390afea7906fd0d42be2a0637f548837a86206f94440dea16837d53086faa9195f55031dea1663dd328437c8620ef0c840fba0a837f5250efaa718df94820de21e857e520cb7c81905f54031de20261bf42107ec6218df54843dfa1887ee20482fca72077cc430de20c81bc31902e8a2907710c30bf290217651083d8a4887ec4110df20621df32c86fca8196f55320de2a263fb108437c80904f55321fba8a417d51082faa790ef95232dfa16837e54c877c82a0f754a30efa18637e518c7ba81185f95120bfa8283be5210378a910774cb21beaa2437f54ccbbc61105f94743de21a85bf43d0bbc86185f94641ef99281ef2088378a52077d5132bfa9283bf42482faa90877cca20bf28085bf43902fca2085f54b40bf28443dd32503f240886fd4942bea9221bf4190378a3a15f54343bea9a217e52443bc65186f90d42beaa0416c52443b860105f94730beaa441dd32882baa7a05f54221df208817d528833880185f54032ef98863f9401037a85205f14e20f799265f7318c6b8a6a05f14143efa0461fb308c37c84205f95043efaa4617d548c2b8a6906f54142de108817e53442fea8907748430fa10c217d530837a84106f50f41eea9061dc54ccafca820efd0b31bf29c87bf32102fca7106f10e40dfa8881dc51ccafaa321fd4c431bea8c65de434c7ba60185fd4c21ef996817d5090bb8a9187d44010ee19061dd320c2fca2207795030ef21887be540cafaa9217750c30ef29883df53506fca518774cb40ed28
  | 2 => 0xcafea6a05f54642dea08813c5050b7ea2a14f15130bf280437f504c6fca121df94a40dea14217e52d0efca3104f15131bea86657e540c7bc60987750e30bf2a0857e53d0bb86518774c921ef28a65dd54ccbf420086f10a40bea8c21dc50ccafca021df14131ef9086175510837ca998774c832f799465ed20082f4a010f715132bfa9a855e53082fea8887e90040eeaa061de544cafaa3105f95020eea1e65df324c2fca1a1770c220f7a1285f451483ba80186f55232beaa0657c54483ba86996f95020cea1887dd324c2faa898dfd5331df21c83bc5350b7c81087dc4010ef10861bd42106faa020df94630bf2a265bf42102fca5a0ef50441df19081bc53d0b7a84a06fd0a10beaa621dd510c3b8a2185f94331df2a043dc520c37e8510cf95042dfa8685df51ccb7c62207dd0641de28c817d544c27ca9986f50941efa9c41f9300c37aa8195fd5021ef21461bd42882faa521df54a31de10c817d52102fca1195f94720dfa18817f53c877aa3205f15021ae29a217950086fea4086fd4742bf28021bf42c86fca3195f54f40dfa1263bd424c6fca710ef100309faa263df400c2f8a5085f14d40bea8683df524caf8a8107750430ef28e657f54043b843187790932ef990435d53106baa4185f14931af29885f521086baa7905fd5232efa8a65de42ccafaa6206fc86409f2a6219d428c2faa4085f54b31ef29e817d51902faa010df95121df2a063bf42502fea2a07714d20ef99461dc534437c43206750b32dea1681dd32086f8a4985f15331df20281dd328c2faa9984f54a40be2a243bf42882f8a9987754e42efa8861be40882f8a2a05f54442dfa8c815e5310778a0a17e88110dfa1463f920083baa0995f14d20dfa08817e52087dc431077d4d20be296217f544cb3e85997bc8621ef20c61f6411077882206fd0b40bf290637d540c3bca6215f94020bfaa643dc53882fca898ef10c41bea94617d549037a62207e8c030de18881de548c37881905f54b43bf288437f53483be64885f95231bf298219f428c3be61185f95110beaa643bc40c437e81205fd5210bea9063de310c37ea7207d94420cf204617c504cbee21085fd4940bf2a6637d510c2f8a6085f54740ee992213e540877ca2a15f15221aea9e219f32902fca2216f55031efa82657f514c33e84994f95320af28061df32cc3b8a3185794f20ee994833c548837ca6206fd0831ce99481bf42506fca5886f50a31eeaa265dd32cc2fea498f78c010bf29487be53d0b7a83205f94343ee988637e500c6fea9187710030be29e437c54042fca790f74ca21eea8665bc404837aa9985f14e21bf288657e54103bc6298f7cc810af29865bd420c3f441085f14c20de98c81ed4210afaa720cf55032bea84877d53487ba64086e94040ae29a83bc43102baa7195f14142f7a14857
  | 3 => 0x9c010000c0005a01211832000180080401004081640800d66006008020c0460a0180e80019013a30001e038080040001e0781e0087e0000000216070540000006e8205993260000082e020b6039a8670001380a158064b0260000030802098340a2d40080050ad00006a5b0023c00a0606c0080409826000005600207000008660104226002050440b0000000c5a01a148000022201838191560111801014000040c83e0000a0b810c28ca00002010800b05c768be0481c088003700255000150460182a008000002eca0c0003c00d800080f80100c0100205007558011b002008588182a000323301e01022d10040500600152288220a832020282591800806000041f8061c804270ee0001c0000000154006b84c854248006c8720a81c1e026020005e9b20009802850075b8328349d83c0383f4b1346f007648080a8eaa50084b82a0101434806070520d000a50000000e0380a0900004012060000080800844004d848054030000c86c03804010286d05400802010a61c830000be5d8000182c2f1520e804018ac2000c00994079b20b86a0200835990200401a00016808030c40b80200018438000001e0101a38efd4d42af29e81be41902eea2905f14520eea16657d50cc6faa6084f55320dea1221be40cc3be63185f95130bf28683dd424cb78a8887710830dea9c81dc434cafaa190f7d0a30bea9c857e54043b887995fd5030ef996637e53906faa5205f55132bf2a6417e548c3ba64106fd0810deaa6217f504cb7c42207790d32de20441f9100437ca5205f54f42ef990657e548877ea9106f90010bea9c813e501037aa1a15f94742bf28883de438c378a1a15f94c30be2a065be54c86fca810dfd4d21bf284217e52106faa7a0d714e20fca80437e510837a84217790f32ce20461de408c3be652077d0b32bfa98217f540c7be6490df54443dfa00817f540cbbe84995f54a41f7900417d5010abaa6105f14943df20221bf42442fea488770c2109faa261bc511037ca3a177cc820cf990817c540c2fca2187754f21bf294219d32103f640905fd4121df286857e54883ba65205f54342bf29485dd218c33a84996f54c40dfa1a833e548
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x524423e64d4f21c715332482db6055132a798e429029e64144309758c54c831f4294030c794e40c831c54d4d2097d8d51d0a5e63151218f191524429e6310840c7151328831e5454f20d5d46304831c54d4d1097d8d50087374294420c754f42c869d64148308f997219031e5390020c7553320829e60d0932ab588531029c6350441d5546300832f52901109798e52906d5611533297594420c34c52cc910d9146204831c540c110a758c421025f6550c438f992510423e6015131c714f428829e6310a40a798f519029e64946308f992528c31d54ccb10cd144404823f6454d21cb549420c25e63d4141c795253c871e5350b10c7d4e539029d6314542d354a420c25d6394841a798c5150b3454d4520d6983538831d53d0841ce951500863e65d0910d54c8514831c6355031a758c429025e6394a10ae983428831e5454f108f592524423e64d41329d984530831c544c931971815310a3f6590020d3d8f52443345190120b6980540c38d424c821e3d8942cca3d6414c10b6980548c23e655091097596420c3645288510cb14b42442f160084108f19150cc65c6014d1097d8d544825d6510c31ad58750d0a9d6490932d9584524423d65900208f994321033a5494021c755332c869d64d41329799430482b66114a40a7593308c23f6454e218f99053c871c5414d108f592528c23f6550832c7549428c35a6014e20cb949420425d650c0209b189534425d6594c218fd91508c63d6414b10e6cca50102ba6014a40dc580514829d6210230c7d51328831f42943328fd91500ca5e63d41219d984540c3555354420c7150534825d639491097195410c36452841108f590530831d53d08208f99053087a54248421a798e521025d63d5210a7181428c23c65d0931ce191500863e6414e21c754d42c825f6550630c7d53534431d54cc832c7953320863e6414c108f993530825e63d4b10c755230c83375414520a7590310c31e5494f1097997324c3555114732ae18142c42b56114f4297994534425f6254f109798f54c829e63d4342c7d954310f1d52cca409ed95401025e63948409b98a544425e65084308f59421903994294030ae983511031e544cb108f992544429d6408630c750d5110e5f6254f40c7d4d425065c63542418f59252cc25e6314c219dd95310c6d66114a308f59053c86da60cc920c794d42c865e6394b10a7d91514ca5c63540418f982540865d6590c30b358a300823e64150318f990528432d52d084197597210c23f6454321a7993504cbd03044010d318f524425e6590830a718d411025f654c821a758c211031d5415332c795332c831f540c110c3549321023d6414d21ae980539023c64543329718d511029c604c840a7990328c25e658c110b5185504ca5d6394640c714d435072d52d0b41a758c51d0a5d6214d41
  | 1 => 0xcb1d5390c41c7942400c25d654cb409798e544831f5495230c714f435074f524c930c750d5210f395494021c7151324825e6314c20ce982501023c6055032c7d53324c2ae6214440d5144304823f654c440c755253c435453d45208f992520c29e64cc2308f58a54c423e65d0920c714f424829e60cca40b6983518c23d658ca40ae181321031c53905419798c54c825d65c86308f992520829d648c830a7992520c32c52101109718d544871c5450d319b988540c3655188420cb54b42d023d650c440b3988510c31d544cb108f191510c23f6454331c7d52304834c524c910c7553320865e65cc9419718153c869c6050c43c7d4d424431d5410c318f596540ca5d631522197d8d548823e6494821c794d420863d6414931a7592420c25e6590932c7550434cb4c53d49108f59654082cd6215332cb14a40442bb6048440a75924310e3c6454021a718142cca3e6510130c7953320ca9f6354142b3d89544cb8e524c840b6181328829d63144409d597210429e60d08309798e520823d6494831c754c400823f65504419b98a534425d6394a109b98854cc63c605502197597430c65d65cc8219e580530874e524cb41ad584521037151480208f994329025f654c832c755132c87645248510c754e400823d6494a10c794d42d029d64d4630ce983548825c65cc940c755253c872f54d49108f588544c63e60950329ed81544ca3e64d412197d8d50906ad62902209b994524423e65509318f99252c42ae6214c409758c520431d54ccb209758f5050a5c6550d328f99421902766194d209798c540ca5c63547429798f54842cd6295132c7951320863c64543218f99353c8398400c020b6980518c39932940408f590528431e53d08418f994311029e6314742a6181420c2d860508309b588540c23f6510020c794c40c831d524ca40b6983540c2d661d52308f597211031c535091097d8d5010b355110440f8886204425e63d5032a7191310c31e540c3109b588540425d65ccb10c7153324c31f540c2209d59421042b66114f42c795332082d96090430e3549420c23f64547328f592520ca5e6394620ab58853d0a3d62d51309dd85534831e54cca32a7590510c31c548c531b6980218c29d6314a408f99053c42d66114830d3d49324c71d544c8329758b534438f52509329b988530431d5314c40c795132c863f62550319d98754082b76154d42ae1815150ab86050920a759051cca5c6355120a7990310c31d5350b10c795132c831e5310020cd95151082d76154132a7d954310e9d6414a308f992544c63d65d0832a798e51902d66115332a7d894310f1d544c820d5cca510832f521011097d9532082ad62144408f593530863e6494620b5984540c23e658ca40d3549320423e64d4f10d3d49324423e60950319d185544823f6454031da58
  | 2 => 0x540c310cb150524425f65cc8419718d540427a6014c21c794d420832f52509109798c528434f53149109758c524431c5450c30c714f425023e6494832bc580218435b32540218f993530871e5350842da14a204425e6315021ced09500863c60553218f594319031e5454c2197997434ca5e6394b40e3d89420c2d56114a30c7d4f425025d63951308f191534863d6414910dc88550086d8604c810c3549420c23d659084097594210c2d461551329759532c43355114440c7551320863e64951309bd95320ca3e64150209d185534829c6354142b6983328829e63909429758e520865c6355220a7181424ca5d6314940d314c52442ba6014840a7993518c3354214520a7590318c2db6048430c7951320cad86055132c7553430c67a60d5021cbd49425025d6314b108f590524c39a60100309798c52442766115332c794f420cadb60545329e580540863d6414e21cb54942cc63f655084297980534429e6408430a758f5050b4d52484308f58b544c63e65d093097596320c31e5350e4097d9532c427661148109798e524429e6310440c795030c82756195120c754f411071f548c110cdd09510826f6548020c754c43106b46154142a758f40103986050830a798c521031f544c9309798c54c863e64d41319b189544423e64149108fd91518823e6495120c7952530871d544cb208f58a54cc35753d45209718d50d07573254420a758a400c35732d4520c795332cc32f64d4910ad587539023c6454e21a798c419023d64148108f197424c2d8604cb40c754b420c31f5414d20c754d411063d6295031a758e421031f53d0a209b988540423d6550b1097d95300c23d65d082097d95410c25c654c940b9185200823d6494410c755153c433742d4520a7992324ca3e6494d10a758e429029d640c830c754c43d0acd621503097d8d524423e6494b30a7993210c29c6454532c755153c825d6394b419b98a5244335511474297195434c69c64544309758e520431c5490d31c7550300831e544c820d3549420c25d6315310d618d500869f644c630cb9514210a9d6494630cd945419023d6494821ae980519025d654c8418f595420c75532944208f982548ca5c6354042c7151324c29d63d0240a7d8d511025d658c0208f59742c42ba60d4e4097d8d50d07365110020d3588538825c63549109798f5050b4e524c840cbd50524423f6255310cb549211031d52cc840e6181321031e5010030c754d420863c6454d109758c540429d63c8440d3d48304434f53d49108f59542cc32c54d4910a758c411025d63d50208f1974244356514c630c714d425063d62d5110cd94640082756115020cb588548838f6250932c7150308825f63544408f996404823c6454031a719151ccb1d54ccb308f592520431c53102209d58454cca9f6354342c7508504
  | 3 => 0x332f808620842d761551329758c5284398400c210a7590210c31c5390140ae980211038d424c920c7d4e405031d5494c21cb19352442b661d4e40a7181420c35932940218f191508c65e65cc9409bd95210873751946408f59353c431c5350a208f195424429e640c830c754c5350b555114430cd544400831f54cc93197d9732d025e63946409798e520425d6394a41c794f42c431f54d4d208fd97420c67561d5020a7191300c25c63540218f99352c431f5310120a758c521023e6494b31cb1494244298604c840abd895350b37519012097d8d51882cd620c22097995325039b604c840a7592520c34d52cc830a798c321027561150309dd85544829e6494a30a798f5050a3d64d4f218f19151ccb1d540c3208f592530c38e52508309758b535063e6494a10cb54b21102d8604cb108f195424831f548c220c795230c431f5390120c7d4c408825d6315020a7d91300c31e5450e308f992520425d639521097996304831f5390220c750a50ccb1f3294040d354b320c69e60d0a3097d9532d02ba60d4c4097d9732c425d6510630c795253c833751101208fd91508869d63d4342a799350cca3e65c8440d54c9510831d5350841a759350ccb1d5350820979825308798400c110ad98750d0a776544010c754b428c335519002097d95321075532d4520a7992320c2da60904308f596431063e64149318f594321023c6055232ae983521031d5494c209e583530863e658c8409798c54886b86050a2097996428c23d64d4131a7d9150ccb1f5414e2097997210c25d63151219ed95100427661d4c20a7592528c25e63d5321c714d4350b1d53d0b20c7950300829d6414532b6181321025e6094c41d5d46518c23d65100208f195424c65e6394d2097994410c23d6595021a7990528c35551145329bd89544427561d5230e6d0a500c31d5410f3297d8d50c86746155132c7152304431e54ccb21a7d91504ca9c6354542c7549321026d629511097197325071f54cc920e3d4b424cab56114c40b6980520c2ad6210220ced0a500863d64d4f208f990520425f63550109758b535033754d452097d8d544429c644c4319ed8153486ce6215030c715143cc71f53d0941c7d4f4248356510c020c754f42d031e53d0b219ed95300c23d65950319798f54c431f5410e318fd91538823d64948308f98254c865e6315020cb949420c23e6414f209ed95200825e6510a308f59251882cd62d53329798e548829e640c6308f191538831c540c1209718d50c863f65500409798c540c71d544cb30a7593210c23e651513097596530823d6494820c794d42c823e6414930c754f4290b1c539022097994420c23d6215110a7592324cb1c5310120aed815350ab56114a40c714e404832d52508109758f50486ad62900208f589540834c520c11097d94300831d
  | 4 => 0x755253c823e6515120d6982500c2786054d21ae980219023e65d0940c794c40c439b60508309798c520429e6408630a799051ccb8f624c8408f994319031f53d0910c758c544c74e534c832c750e5010e5d6395110ae181211025e6394821a758a408c3355494420ad1855350aad6210020ae1815350a5e65cc9108f59253842756114c20d3949320425e65086308f992528c69f6454430ad185425069e63144408f195311029d638c840c7553310c71c54cc910b358a308831d54150308fd89540823c6454032d618e500871e53d0821a7983321031e5454f219758f540869e64108308f593538429e64c8630d358b53882b9608c440d5146304831d5210230971815390b1e54cc83197994304425d6294f108f588544c355510c0209798f540825c6054c219758e548825f6550030a7993300c25e6394a40c74ca5010357510c120c7552300823f65d0b108fd95420c71e548c320ab58b53d0a3f6550b109758c54c872e5250b3197197324425d6510c3097588534431d5310320a7990424ca3d64d4c20c754e40c831d5290230b9189100438d424ca218f596321031e53508419dd85544cb5b32940219e98052043c532484219d987548c23e65101108f59252c425d6510a309e195204427661150208f59053c823d65d08218f59742cc27765484219e983530863d650ca4097996434c79a5010030b6181324829c6150c4397d95310c79a5090030b5587320c66f6254d10d594e510834f528c1108fd95420825e6394b41a7d8d411023d65d08318f99052c4355510c430b6181514cb1d5454c21a798f211023e65084409e583540863d64d4121cd150514831d5410c30b5185324c63f64544309758f54c42ba60d0920cb549321029d6390942c714f424429d648ca30c7d5132482ad6294d42b6980510c25c6354221aed81321031c548c220b5584540c25e6395210ced91500871d54cc83197994534825c654c920a7d8d419025f6355121c754d42d02e96008620a7588400c29e63c8640c794f42d02b86050b30dc546200825d6394b408f590514ca3f6454910a7990514ca5e65106309798c54c429d64cc03097d89530831d53d0b10a7191318c23e64946308f997435065e6094f2197983535067b605512197d8d5090b354294420a7d8d401023d6494d108f996404c371215402197594218c2746548510c754a400c31d42940309798c52c425f658c020c7150538825d65d0030a798e529025d6294f4097597321065c654c941a718d401031f54cc910cbd49425063f654c6408f992530c23f65d0b30c7548400c25e6094c429dd8552442b96008440c7551530825d63d41419758f54c82b96008640b6d81420c23f6454d20a718d50d0a9d63948408f191518823d6414f10d64c950086b66114840a798c529031c5450f32c795132cc2d561d4
  | 5 => 0x51ccb5653544208f997424c63f6454c10c7153328831d54cca32c794f4210a9e6010030c7151324434d524ca31b3588510c29e63084408f593504ca5d63946209b58854cc69e648ca30d5d4c514823e6494e10d3549328c2ba60d4640c7d5053442b86050830d6d8d500875732145209758e529031f5390110a718d51d0ada60d52308f990540867965840108f592528c65d6394410a758f519025d6315021c7d4d42482d661d4332c794f4290b1e544c831ce19250087365494420a798c219023f6454d10c7952300832d5250a41cdd0851483395454021a7d8d5150b1c548c130ae980531025d65ccb40cb58b548829d63106409718d50d0a3e6515131e3d89329023c64542219798c525031e5350832a718d511023d65c86409718d5090a9e639084097594410c23e65901108f994544433a6015220cb54a321023c6454c10aed815150a5d63145429e181544865c6355221c7549420c33542544208fd91500869d63946409b58a534423d6494e20e3549321034d6314910c7d4d428829c6454332ae9823110356518c0209d586534825f6354342c714c404433542d45208f992520c74d52ccb30a7d8d51d0a3e6494e20979825390a5d6294c4197195324431e54ccb10c754f420866f65508428fd95420871f544c931d6d8e500863d6494630c7152304829d640ca30c7d50304825e63145428f181540c71c5450d32cb590524425c65506308f195319031c5390110b5584520c2d960086309798e510423f6550c439758e544829d63c8640ae980511023e6494910d654d500865d63948408f180544423e6494d208f990530825e65cc920c7d50438c23e6414532a798f401034c528c110e6980408c31d5390310c754c40c42f06148210c795153082b860508108f590530863e65101209b588530423e6550930a758e52902776550441d654e500874e631491097589530831d548c310c7153324c78d424cb20b6983528c23f64542329798c540423f6255330e3d89428c276658851097596428c25f6354221c7d5332882cd620c02097d8d548863e6015110a798f4090276619512097d8d544c2da60d4430cb990524431f54d4e209e98054087b04044010a798342cca5d63d4b108fd9542cc35553944209798f540865d6394820c754c53d0b355114542c7952530823d6494d208f191534823e64150329e583548c6d96008430d694d500865d6214d40b6980528c31f544c910c754d4210ab761541429d587530829c6454132a7593218c23f645433297995325071c53d0941ad587421065d65cc8209798c525065e654c910c7d08504cb4d52c843097d89531065d6394b10c755153c875a5394021e610030c823c655093097d8d544c6da600843097994424cada60d4830c754d42c872d52d0840c714d424831e5390310d514c514834d524cb41c
  | 6 => 0x9c040060de1580881f0160700000e002008000220421f89fc20004004028580060000100302006c0288a1b602c000d9000008000222720980280e15a0000600f26a0780000700a0001800201205c0080e3881ac0001405e00001033008ae0199fc00098c88019002008188000220450780007c330ea00002c0108a00403c0000080095401c0080c000a84000010003b47c81b00e00400801006054040020d600c350000001f0048000040000981400600c018710cc000000070261b4038340020601380082a04401053000000018070060013f98700e0bc0e00f000d242180401b08c00014014000060010c60004880600e01004b8501c0241d0010000a00804100c0180b8040080040000215e0340502f008018080800260080a83d06065c3600601631c0600552607c0f8dc00c0245302100000c058001800c424000010014020060820003980200a0180b001024004d60000120280003a18e0b0010b00b2424009250de06c048210000003a80732a1300989500e3780180002a0a0000e50000784600526c035cf811022180030020040c0000430480000b80a0201900884702c00df48040042f1df80202a024000000006680780000a068280520000000c0200000202a80301c0517700008e00c0303101600c1304564a040069200520c800b9ca020e81201100000c0280000a058000000001a400023028000cc8010003880080f07e0080001a00409440805036008010220002580985f0000085e0140160080000211200001019012000000000100640d0050460042c80401c0142581e5420480080410e01c038231c00341401c0000141e8113120080203503c0001e8040260dc000000140e0030090780340280a03217c0017d0000100281f01e018018000d81063e6414d219e181544cb2d5250a40ced92500865e639484197181531065f63540418f59352c425c6355110c7d52304c25d6314941a718d419023d6508440c7153538829e64148308f59252cc71d5415132ad984531034d52ccb319e983548c74f52cc910c714d425034d524c84097997218c33554544208f993538429c604ca40c754f4210b1f5350940a7d91310c29d6308640c794f42c831d544c8319798e534425c6354620ae98352902d86048430b5587548c31d544c4319798e544431d5310c408f983544c7394294021ce509500865d63d5321c7d4c404431e53d0820cbd4b424429e609003097980535063c6454232a7d91
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20c041010034002004458511180812800112140dc0012ac28300740812614001281000b1c0420b341400ca28e8a88a299689421813248306aa2c418041895895110020c1aa4302841861952181321030a2a0c299263855516115332c2aa8b0e6418e18531814288306a9ac429881435c85450c30c12a4302642060f545883088226b90caa08610e1c16550831a2ce9a8ca31849a70d8d511030ab22a228861431d5424c92085ae432a62206155358453d0b0a298c2a1283459c75394e40e12a4302642050d7294d42d0286b94a6a162192548604c840e10a4200608862952181321030ab1aa228881455c45450f32d80c4182200855070544514cb12b12a228881621c1424c920c2ac8a88a39960c655093248384a1264a8043435ca544c831e12a5b02642051671d50438c28ab88a8a1861459c75495230930e0b26421850d7295132c42c4b908018041261c16494830c30a8302651051673d46519028a39aa228a85835516215030c2aa6b08a62061563544411028c382842826585192514c630c32ca200601070952d81420c28a38aa629a85261c163c8440c28c728a832060d52181321028c382a629a8585591510c430e428490aa010e18531814248384a90c0a1061261c16394840a30e0aa0a89968952181321028a38aa821a65c15093214520a30e0a1ca021d1870550434ca86b94a89966191589510c0208b0e0b2a6420e0d6354b2110286b90a8a1e63915895114430c1ea6b1081106156354451d0b06a9ac420041a2588400c020ac4eb10c408861553587421068d386a821c63865486050830a60e0a10a29051471550544cb06b12a4200618694c6050b10e22a2200601050f7250d5210e98382a228a85825486050830a1ae529a8420ea0621011004344a90c0a1061541c13214520c30a8302649041c76551310c745290c09908186950604cb10e826490aa010e8a52181420c28cba88018041925486050830934e1b22a21861554584540c306b22a5908618a5486050830
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x2402020001b00805093214520a088058d52c8440d01421c13214520a0982950604cb10c0975588400c020a088059152c8430a098294c6050b10d0172544400c020c09655c8400c020e0162544400c020
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 7 => 2*((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/23+packedAt s3K6 (768+(h % 23)*6) 6) % 48)
  | 5 => 2*((h/346+packedAt s3K5 (27459+(h % 346)*10) 10) % 1017)
  | 4 => 2*((h/469+packedAt s3K4 (51110+(h % 469)*11) 11) % 1345)
  | 3 => 2*((h/51+packedAt s3K3 (5488+(h % 51)*7) 7) % 112)
  | 2 => 2*((h/10+packedAt s3K2 (600+(h % 10)*4) 4) % 10)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 1 => 0xf03fffe07fffc3f83f07fc3ffe1fff03467cfc
  | 2 => 0xffc1ffff83ffffffc007ffc3ffe1ffff878f1f
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x218408c5109040014b098044c022425818b171
  | 1 => 0x64889143212205281542a429521496094254b4
  | 2 => 0x821122080a44225280844a82254128a2850a0a
  | 4 => 0xcb2dc4924876ab9ce6d06223b9980c33e80fc0
  | 5 => 0xc31871c738733e738e77330311030c3f7e000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40441
namespace PEqualNP.Outside.L_meta_40441
open PEqualNP.Outside.L_meta_40441.Model
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
end PEqualNP.Outside.L_meta_40441
namespace PEqualNP.Outside.L_meta_40441
open PEqualNP.Outside.L_meta_40441.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x10934d04000100000108c000140180301043007000fc42fc30fe21fe41ff21df43fd30fd40ff10fd32fc32ff42fe30dc43fc41fd42fc10fe31ff41fd31fe32fd41ff30ff31fd10dd30ff43fc31fd21fe10fd20ff40ff32fc21ff20fc20fe40fc43fe20df30fd43fc40fe43fe42
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1168000002840000001025418002017980824480220008001381800a149800000009000000504006000210010120800d1e0000002000070002bca7205714d42af2a6615e544c27aa810f64c210ed20261785050b3886a16710c40ae29a8379500c7b6a0985e94241ae29a813d548427ea898d754c21ce2a2615e530c2f4a1995e54332bd280637950906f4a010cf15121aea9c613e54842baa7085d54420ce218839c43902bea6a0cf95232aea98215e53906f0a090d794e20ae29a437651082bca6206710f429e2a261d9404c238a8985794e42baa8c813e54083b260104fd5121aea86879f544c2f6a090dd94640ec986417a5010ebca7085e54043af29c875d5390abea690ded41429eaa4655d5010ebca821d754e40af298415e53086e8a2a15754e419eaa0415f53502baa6204fd5130eca80875e53042baa6106795043bba8a85da5010ef2a010cf95021aca80875f5350abaa7106710e419e2a2635c54cc2b8a898764c110
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4984c131140048298644c110c65513008351514c020c6152404c298644c320c510c5150a996010e40a658043d0a996010d42a619130082996010e419658053506596094e42c610e5090698644c210b4586404c3196015130c610c5050a996010c41c6551308421e649513096195404c21c6454c108719153883144394640
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x200401688b808628a85445c04394640c20a8b0c809841876551300820c3b2a89842184191514c020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s5K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/65+packedAt s5K4 (2430+(h % 65)*7) 7) % 90)
  | 3 => 2*((h/15+packedAt s5K3 (950+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/16+packedAt s5K2 (294+(h % 16)*3) 3) % 6)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03fffc0fff87f07c3f078fff87fc0fe307e73
  | 1 => 0xffc0ffff03ff83f803ffff0fff83ff003f9f9c
  | 2 => 0xffff07fffffffffffc007ff07fffffffc1e3ff
  | 3 => 0x7fffc0003ffffff80007ffc0003fe03e0
  | 4 => 0xfffff800000003ffffffffff80000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x948614462892d30160ba189a9c66425a302e31
  | 1 => 0xa192208a192215280152a9032ca29608169694
  | 2 => 0x420841104240005284004220410928a0c1414a
  | 3 => 0x8b2cb62490735b9cea6b008a76720c337a03e0
  | 4 => 0xc30c438e38462e7338c74cc004030c3adf800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0fce8e0e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40441
namespace PEqualNP.Outside.L_meta_40441
open PEqualNP.Outside.L_meta_40441.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x403403850310010c00800000064417410000000803820c00200000000c200000254700900ff10009fc43027f50c09fe53027fcc007fc32007f950077d52007fd0005fe2101ffd4807fd32007f55003fe20027f4c005ff1001ff9480bfc54017f14407fc5201ff1080bff5101ff8c809fe43007f54009ff53027f14c03fe5001ff50805fe51007fd0409ff4300ff84007ff3202ffd5007fd2100ff08009ff3101dfd4801fd51017f08409fd3101ff54803fc5000ff8c003fc1000ff0c001fd10027f54c07fe42007f50407ff21017f10405fe3101ffd0805fc31007f50007ff20017f9040bff5000ff90007fd20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x92a213ff1095004ffca8a0007ff5054005fa20a8204bf18f410bffcc6a0816fe655000bde2a2a805dfd4a54115fec4aa002ff64544357eb16820fff8cb40067f8a6a009bfd2195003fe102a020ff081540b7f864a087bfc425440bff282a200ef5534104ff8c1a0816fc654402bfe1028201ef10140107fcc0aa02bfe5150047ff982a802ff0874104ff8c7a0012fe63d0417dea128009ffd8341007fca888002ff6155005de20e8217ffd4d41006faa8a88177f525403ffea1aa209ff10b4104fee82a0877fc6054427bea92a009efd0b41067fca6a000afc61d0001feb2a2002ffd4551117fec4aa053ff4354013fe314a805ffd495104ffea92a027ff4150013feb1e821dff88151007bec6aa017ff535503ffe982a21dff9815101df8c52a03ffd32d001bfe32a801eff90951007fa82a004ffc3254013ffb168001df941500b6fea4a081ffc5344043ff882a800ff5514000ffe20a808bfc6255005ff28a2025ff0c65404ff8872a01ffe534401ffe296800cffcc5400dffe61a0832ff635000bbfa8aa801ff5414004ffec32a012fc6354003ff1868005dfd495403ffcc68800afc615000b7fb22a80cff58d40025fcc6a8826ff6295017ffb128002ff085510d6faa5a08177f5254413ffa1e8201fd8411004ff882a0027fc62d040dffa122000ffd855402ffea6a801bfc6244001feaa22019ff08341017fa42a080bff3144005ff8868209ff58b41017fa8288007fd504401dfe28e8001ff48140017f862a0827ff65d0003fd2068009ff98b41077fc63a0027fe43d0013ffa12801aff0cb4100ff820a007fff3054413fe21a8201fe0411004dfec7a081bf92044001fe322a222ff4855404df8c88807aff62544137fb2e8201ff0c140087fa63a0017ff5054443fe18aa80bbf5894002ffca52a007fe10d0047fe31aa818ffd514104ffa85a0007fc40d00097e31e8009ff10d540d6fea5a089bfd3295005fe20a2002ff4874104ff8c5a0027fc5455025fe18aa014ff10d500affc60a083fff21d0037ffa9e8223bfd8d5402ffea2aa007fc1044013fe2a28001bf1815411ffa62aa083fc605503dbea92a203bf1894000ffa40880837e5055013ff31e8201ff9034002cf8ca88017ff545503fffa1aa200ffd915102ffea8a8077fc2054429fe31aa005ff9515109dfec4a8027fc63d043dfe192a209bfd8b4004efea92a01bfe6244013fe21e821aff8cb41017fe8288093fe30950096e31aa802ffc855100dfcc9a0017fc5295013fe32e820aff8854004ffcc5a0033fd535002f7eb1a8202ffc415105ffaa4a0027ff63d0043ff10aa803bf989540bffc86a0807fc304400ffeb1a2022ff4c954017f863a0803ff6055005ff0868207ffd8d10015fcc2a8003fd5150017ff9928026ff8ca54057fcc2a007bfd3254447ee31aa804bf18d10
  | 1 => 0x2fd6550003ffa028009ffd874012ffc432a027fd6195001be32a2020ff04154067fc86a001bfc5244005fa28aa201ff9014000ffe21a0027bf42d000bfea9ca822ff48154004facba0027ff42d0405ff98e8209ff9834100ff820a8017ff5254003fe902a026ffcca54035fec488007fe3044005ff10a8209ffd0f4001df8c4a8007fc405000bfe29aa209ffd8e5400ffc20a000bfe31440017fb0aa005bf19541057f8a2a0027fb405000dff1922005ff94254015f8c2aa00efe6250013fe2a28221ff9855405ffa84a000bfc41d040ffe31a2027ff4c254007fec2a002fff215000fff21a2005ff1515000df8c0a88277e54550097e31aa20fdf54b40005fecaa000aff6154403ff9868005ff94d5102dfccba0893fc2095019fe98a800cff18d400b7fe64a0807fe1044017ff2928004bf18e54017fe428800bfd5150433fe1868217ff54d410b7faa4a086bfd20d0405fe0868205ffd4a5400dfcc0a8807fc4044013ff214a801ff0834004ffac7a003ffc32d0001df2a2821fbfd8d5113ffe612a027fd4395045ff992a800ffd95100c7f8caa080bfc514400bfea9aa805ff5495400ffc8088042fd63d000dfea122005ff55151025fcc72a00bfd31440037e3068216ff9094102ffaa2a8017fd5254027ff992a002bf9874000ffe40a008bfe4255001ffb222000ffd8151017faa3a080bbe41d0413ff31ca821ff1855404dfcc88800bfc415442fff9828201bf18141007fec2a8043ff53d004dbea94a81fff18d5102ff6a0a803f7f52d0041ff102a809ff1534104ffac12a007fe50540137e322a209ff1095409ffc84a800bf641d0437fea9e8215ff881410b7fea4a081bf5214403dfe902a223ff4c154017fc43a080bff5150447ffb1aa812ff0855004ff8c3a005ffd3050433ff2868202ff0415104ff8852a007ff40440037fb02a001ff4c1500a7fa86a8003fd615000b7f32a2005ffd49540d7faa5a080efe62d042ffea1a8205ffd42540d7fe65a0807fe2054013ff2168209ffd0d4102ffea2a8012fe6350403fe2828009ef9534109ff8c4a803ffd21d0001feb02a802ff88551007fac8a802bfe4150047fea1aa81dff0c15100ffe60a800bff1050427fe90aa001bf98154077f863a000bbc4150413fe21e8009bfd8e5402ffea72a01bfd6244005fe10a8201ef90140017fea3a0807ff20440037eb068021ff085540f7fcc4a8802df6355013ffa1ca81affd4b4102ff8a8a8897ff109503dff992a200ff591100c7fea0a085b7d5250413de2a4a803bf18b41016fca2a885bbf4250413fe2128209ff50f4104ffccba080efe6295033ff1068215ff18141117f864aa006ff60440077e312a806ff9491000ff8a088027fe629500bfea9aa209df1515402ffea0aa09bfc329503fffb1aa222df54954017fc828806ffd30d040bfea
  | 2 => 0x4000fe8208802f7f52500297eb1aa001bf98141067fea6a0037fe65500057eb0e8203bf98b40007fac0a080aff6554401ff322a000ffd8141007fecaa0827fc41d0005be28aa209bfd8b410dffca7a0817fc53550057f30aa800bf59541017fe82a0802fd6544001ffa0aa006ff0c91000ffe2088027fd62d0029ffb1aa001ffc815004ff886a008ffd6355035ff9068209ffd0b400bffec6a0827fe5455003fea022012ff9055002efea8a8806fc609500bff292a00bff485400b7fec4a0817fe5154003fe0868002ff8415102ff8a0aa017fe519503ffeb1aa201ff1415002e7ea92a01b7f52440017fb2a2002ff1455104ffacba0017fc539500bff292a81eff5095103ffea68805aff6250411fe32a2009ff18254057f862a004bfe21540457eb12a802ff4c551007facaa0837ff5450001fea8e8000bf58654077fc43a000efc6250403fe1868002fd88510005facba0012fe6344019ffb1a801effc815102ffca72a027fc54d0013fe2168005bf19540017fc82a8806ff6554003fe9868004bf18d41057f8c2a0043fd53d0001ffb22a009ff5974101df8c488067fc50d040b3f32e8000ff58554017fa4288027fe54504077f3128200ff5915104ffec52a006fe60d0403ffa868007ff10d10005fac3a000bfe515042ffe29a8204bf98d5402dfacb2a06bbd42d0445feb12a802ff0c51013ffe632a002ff6054401feb0aa002ff90741065fac6a005bfd6250435ff2968205ff94154135fac52a027fd60d040bff28aa800ff5514107ffe65a003ffd52d00057f3268216ef50941005fec8a800efe6244013feb14a805ff94d54047fea888063fe655042fff29a8209ff1065407dfac5a0002fd6095013ffaa6800bff589400b7f8c4a084fff4254049ff104a81effd0951017fca2a888ffe6355001fea0aa000ff1911000ffca1a0093fc309501fffa96800bff4c940127f8212a057fe505042ffe31a8209ffd0a5402ffca6a8057fe6050403fc2028026ff4825405dfec4a0003fd6054401deaa28200bf5834100ff860a800bff3150429ff31aa002bfd8541025fcc7a0007fe3050017fe3128009ff9874004ffca9a081eff634402dff3128205ff9495104ffec5a0817fc5054423ffa8e8009ff98f4000ffc41a0033fe635003dfe312a207bf58d1002ffaa6a808fff3155017fe2928015ff0c141015f8c32a00bfc4150429ff98aa01bff14f4104ff8c32a007fa304400bfeaa2a009ff90b4002dfccaa080bfc105040bffa8ca805df14154077f843a00077c50540077f312a209bf9925404ff8a92a027fd43d0017ff1928009ff55341107f860aa027fc4155013ffa12a812ff10550015fcc2a0027fc6395013ffa1aa806ff4c910004feca88012fc635502dfe9028225ff0865404efacba000bbe415040bfea94a81cffd4341057fc62a000
  | 3 => 0x80304c1802804000960080e01c4e022870840307c0205c028b07b00c120000d06c2a00811058000303205c2f0306f014163500d04c077f312a005efd525404ffc812a08bfe325500bfe292a008ff151100b7f8a4a085bfd325040bffa9aa202ff8851004df8c8a80037f654403d7eb12a209ffd534109ffc64a8006ff61440057e30aa001ff9414000ffc40a000bfd3150405fe98e820bff9894012ffc632a027fe43950097f31a8014ff90d50017f862a880bfd5144041ff182a800ff59540007fecaa0027fe65d000ffea9a2016ff5094103ff26088027fc409500dfea922001ffc834005ffea4a006efd63d0427fe992a006ffcc91000ff8a1a000bfd2154403fd1022022ff9895402ff8a4aa02bfc2150027ffb12a006ffd8910127fc212a007fd305001bffa8a8017ff58d4104ffecba089bff2195005ff18aa209ff50a540b7fc64a0806ff645003ffe21aa20cff50d4002ff8a32a02ffe4250013ff20e8001ff1015000ffca088002ff6150003ff182a009ffd8f4104ff884a003ffe52d00037f304a802ff08510005fec88809ffd3195035fe2968204bf18d40017fc62a084bfe615400bfba8aa205ffd51510d7fa65a0816fe65d0005ff28e8200ff99151107fc80aa00efc62d0047ff21aa81fbf58d51017fea288026ff63d0043ff18aa806ffd4910017fe43a0807fe2044013fe2028213bf5895000ffa6088003fc6454033ff1868220ff841540a5fec6a804bfe3154005ff0828216bf58941097f8c2a809bff20950477eb1aa809ff95340037fc848801afd6244013ff304a815ff9014105f7e84a0027fc405503fff31aa209ff1974003ffa868800bff21504037fb028002ff145410b7fca4a087bff6254427ff312a01dff1015100ffc20a8007ff5050013ff2068209bfd974002f7ea8aa04fff2154045ff90aa80eff9474004ffe84a0827ff6095045fea12a80fef50b4004ffac72a04ffd4254001ff3222001ef1034002ff8a2aa007ff3050021fe29e8014ff4c55000ffc80a8002fd65d044f7eb1ca805ff1455002ffca8a8057fc5050417bea928000bfd9541017fc63a0802fd6444013ff21e8210ff94f4000ffea08800bfe415040dfe2122009bf1974104ffe86a007ffe4354403fe1028000bfd814100f7c81a007bfd6254443ff20aa813ff5895004ffa83a000aff6450445ff902a803bf18951047fcca88017fc5095013fe206821eff8c9510effc80a88277e65d000bfe292a209ff50b41005fec0aa00bfb1044013ff20ca805ff14d5000ffe20a000bff3154417fe1928016ffc814103ffe8688027fd54d00057f30ca801ffcc1100effc60a8807fd50d00137fb2aa801ff483400bdfec6a0843ff31d0005fe28e8209ff9865404ffac3a0007fc204400dbea922009ffd074000ff0a0a8053fd63540097f31aa009bf197
  | 4 => 0x4048120300f0000401001078662a0320340228012150110980e2103c1b80001c000003300c03008e31dc440b0440280c150090b06b0140003062008b20104c000000080a0185a01c090300100088050e60480702000010057b460048000000309c0005c000000313801018020c00000804308030000704401004ab60800030bf0b00c49040000f3008194394f0040007ccf7846d0842c1645e0c0080081600000018520a40700c211785a15808000130080106009360150040e0340d028001c4080241027c010102103c3b07c1e0005e4ec040283d038000151a000000007b0e4080103113c3a004290040b1dc0c0004108c0500827000020ac02000a103c6a148261fe3001c050042003c0500001010094580200429bf80105d2b00c590d82402c2000000008cf0100903c040685c8386c000482b4040e030014020ec02
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd73597401667f71d951011ede74d8d54004fd7358654236dd50d8d54005df7359540006bc43d911001cfc72d81410e67f52d8554236df52d8d541067d505974001cfc7259540006df735954001cfe725974116ef710d85500047f75591101677a20d95100c73c5055141004fd76547400067f755951004e7c74597401b5bf7255141004ff7259110186bf40d91500467e7619510056f661d8540014fc7458341006bd425911011edd74d8d5404cfe745825404cfe74d9510065dc735854006e7f52595400067f65d91100c73c6555141004fd72583410079f73553410067f5258341014fd74d95410067e6319510004fd7258740024fc73d95410bddc7359541004fd72d8141004fd73d8550004fd71d9540124ff755954017e7c41d9510004fd72d9540004ff72d95100067e72d951004ef840582540067f65551410c67c65595410067d6554740004ff73d8151004fd73d91510067f525874001cfc725874001cfc72d954102cfd71d91510eefa60d81510067d5259741236df50d8d540467f52d95100c67e65d95410067d52d8540006dd62d8d54004ff7159540236dd51d8d541067f50597401067c705974018e7f52d81510067f621951002f3f74551510067c43d9510004ff73d9110024fc73d81541067d305974001cfc7259541015bc76551411667d50d95101a73e50551410047f72d951002d7e75d8154004fd735951004ebe64191500147c7655151014fc71d911002cfc75d814100cfd75d855000cfc74d8141005df7358141004ff73d951000cfd71d9110004fd72595100067c62d951008e7c53597400aefa40d814118dfb7058550006bf649915002e7c655514108e7c5159740024fc73d91100aefa60d814104f3f75551410067e53597400473f54951100067f735974004fb761551410067c72597401677410d951004cfd75d855410f7471551510ccff7159110236dc51d8d54024fc7358341024fc73d91511067d70597400067f651911004cff71d954102ebe65551410e5f7715915104e7f425974001cfc725951004e7c4059740024fe73d9110106f820d81540075e50d8d54004fd75d81411067f205974017e7d51d951000779301951000cfe70d915104cfc76d0550005df73595411067d10597401667f50d9510024fe735825400cfe7655140004fd75d911004cff70d95400067c325974017f7621d95100467c54d951001cfe72d951004f3c65553411667e70d9510004fd70d855422edf42d8d5401cfe72d91501667d30d951004f3f755534101cfe72d915117e7e71d951006e7f52d95400157c76551510457e759911004e7f4159740006dd21d8d5422f5c54d8d54006fb7059510004ff71597400077521195101067c5059540014ff70d911001cfe725865404cfc7458654024fc73597401267d50d9540015be7195141
  | 1 => 0x974002ebe6595141024fe7358654004fd72d815404cfe74d855001cfe72d91101577a3019510004ff72595410067c6319510004fc7650550236dd52d8d540067f525911001cfe7259110004ff7259740014fe7655141024fe73597410c67f54d95410067e3159740004ff73d95410067f32d951004dbf72951410067c42d951001cfe7258254004fd74d815102cff76551410fddc735915101cfc72d911004cfd71d81410067c65991100065d52d8d54024fc73d85501677610d9510004ff735974112ef6515865410ef461585540047f725974004cfe74d95400067d73d9510004fd725974110fb47155141004ff725954004fb76195141196f551d8550004fd7258654014fe7458341024fe73595100067f74d95101067d20597400a5dc7359150185bf74595400047d72d951008dfb705915004cfd745974000cfc7059541004ff73591100467e65d95100067d525834104ef44158740004fd73d815404e7c415974000cfc70d911000cfc70d8554004fd73d954101cfc72d85500067d5258740024fc7359540024fe73d855422f5e54d8d54006dd20d8d5404fb441551410067d52d8554004fd7655110006bd641915000cfe7059741024fe73d814101cfc72d81510067d52d8151024fe73d815417f7b10d95100067d52d951002cff7655140006bc43d915110ef651d855400cfd7458341024fe735974001cfe72d855002cfc7559110024fe73595400057d7219510004ff735954104efb40583410067d5259540004ff73d81541067e50d81541067e6055151004ff725874000cfe70d8540005ef725854000cfe70586540c67f5259541024fe73d9151005df7359151007792019510006df72d8d54014fc715954004cfd70d8540006bf42d854002cfc7558740004fc765511002c7c7559110005df73581540c73f5255141024fe73d81511067c6055151004fd7359540006dc61d8d5401cfc72d915110f3d5155341024de76d8d5417e7e31d95100ecff70595101077a50d8154056f641d854004e7d5458654004fd73d9110096f661d8550164ff755951010cff7159541024fe7358341004ff72d91501667d20d95100067e621951002e7c6555110014fe7459741004fd73597410e67f5259741004ff73d81410073f6555141014fe71d9540024fc73d954004fb44150540104fd7655140004fd70d954101cfe72d854002cfd70d915004e7f755974104e7c435974010f3d51551411647e7619510006bd42d814122edc41d8d54024fc73d9510004ff735865402cfe7558740004ff7654540004ff75591100157e71551510e73c5055341024dc735974001cec725911008e7f52597400067e50d954102ebe655534104cff769511002cfd71d81511f5bf72553410067d72597402365f52d8d5401cfc72d95400067d52d95400067f7559541004f
  | 2 => 0x4ff72597410073f64551510067e63d9510014fe715974002ebc655514111edc75d8d54106f8605815404ef7415865400cfc705974105dec72585401cdbd7295141004ff7058654004ff705954102cfd70d85500067d52591100067f6555140126fa5058254006de72d8d54004ff7655110006f9305825402e7c6595110004ff7358341014fc75d85500bddc73581412375f51d8d5411ede75d8d540075f73551510067e505974111edd75d8d540057f7558540005bf7454740004fe76545400067c73d9510006dd72d8d54006de42d8d54006dc71d8d5416cff7159510236df51d8d54006dd70d8d5408e7f52d8154236dc50d8d540067d42d951006e7e65d9540005ef725911011ede76d8d54024dc735954104e7c7655151004fd73d8554006ef725911019e7f52d9150006bf6499151024fc73d855400cfd71d951004e7e415974001cfe7259740006df62d8d5410ef641d8554004fd72d815100cfe76d81540067f63195102375c50d8d540067f62d95100467f53d951004e7f4059740004fe765055004e7c5459741004fd769511022edf40d8d542379c54d8d540acfd7699110004fd7358740024fe73d8550004fd72d915004ebf4258740006de41d8d54024fc73595100067e74d951021f5c7355151014fc7459741146bf40d9110006de60d8d54004fd7259541014fd70d951004cfd75d81541567f61195101067c50d8154014fc71597401ef3d5255341007777155151006bc42d9151014fc71d9510004df735911004ebf4258341006fb20d81510067e53d9541015be71553410067f52d8141006f77159510004fd7258254015f4715511004e7e64551510067f72d951001cfc725911019ebd54d915004c7d75d815404e7c425974004ebf615514100cfc70d95410067f75595400e73f52553410077930d951004e7f54586540067f32597401af3d52551411067e305974004e7f7559740004ff72d9540004ff72d954104cfe74d8151014fd75d8151024dc7359540004ff7359740004ff715825404f3c54551400067c73597401667f40d9510024fe73d9541024fc73d81410067f73d951003ddc73591101867c50d91500067c6559110015be7155141004df735954117e7e41d95101557e76d9510024fe7359110006dc73591100067d5259541004fd70d9151004ff72d85540077521d9510004ff765474012e7f51d95410067f715974000cfe70d9110006bc42d911022edc42d8d5410cfd765514102ebc76551410067d63195101967f52d8550006bf745954001cfc72d855404e7c645515104cff7659110004fc7654540024fc735954110dbd7595141004fd72d9510006dd71d8d54006df70d8d54004fd75d8540004fd72d855402d7f745515104ebc655534100cfc70d9510014fe76d8540004ff72d85401667e30d95100067d525
  | 3 => 0x6211951004e7c5459740005fb705054004ef7715874022edc54d8d540cefa10583411bf9c735514100cff71d9110006dc21d8d540067f6599110024fc73d85400c5f5719915101cfe72d9541004fd7358341006dc635855404e7d43597402379f54d8d54236de52d8d54006de61d8d54004ff73d855004e7d745974004ebf619514104cfc7695110006be43d9150014fc74d85400c67f52d9541006df20d8d54007b77155141004fd7359110006dc62d8d5404dbf75551410067e735974012e7d51d95411667f30d9510004ff72d81410077920d95100067d62195100057f72d95100065c735974004e7e405974011edd54d8d5400cfc70d91510067e325974008e7c52597401667c70d951004dbc7454740014fd75d9151005bf74545400073c6455151004fd735825400cfe76d81410067d52d9150004ff72d855004ebe6419110004fd73d854002cfc75d8540006f7715954100cfd74d9540006bf4259110006de40d8d541067e50595400067d72d9510236dc52d8d5410e7f51597411067c105974017e7c21d951001cfc7259741004fd72d85400057d759911002cfe75583410067e51d954004e7f435974011dde76d8d54006dc10d8d5410ef421d855410ef661d8554104ff7059540006df63d8554004fd73d8141175fb7059510004fd72d911000cfc71d81410067e52d95100067d735974001cfc72d9150004ff725834104ebe7695141014fd745874001cfc72597400cdf7715911004e7d405974011edc74d8d540067e215974004ebe64191510067d5359740005ef7258141014fe71d8154014fd74d8141006f77159110184ff74595400c67c50d9541005df735514004cfe76d91500067d52d8141146bd40d9110006dc72d8d54006de21d8d54004ff72582540067f65551100067e62d9510004ff73d8554024fc735974104cfc74d95400c67f5258654014fe71595402375f52d8d5401cfe72d815100cfc7650540106fa60d815402cfe76d954000cfd74d8540157781019510014fc76551411667e40d9510006df63581540467c52d951004cfe745865402cfe75d911006d7c75585400c67c53d954100cfc7655140014fd70d911004e7d4259740006dc635815406df97099150006dc7359740065dc7355140004ff7558740004fd73d81510067e32d951001cfc72d9510004fd71d81541667f20d951004ef840583411667c10d9510004df73597400067d715974000df87055140206bf765534104efb7058341004ff74595101567f60195100067f43d951000cfc7058654006dd42d8d54004fd7359541004ff735874000cfc70d8540024fe73d95100acff705911008e7f5359740015f471551410c73f52951411667d40d95100eefa50d815100cfe74597400067d52d855004f3f65553410067d53d9510004fd72d954117e7e21d9510
  | 4 => 0x81540067f725974011ddc735855404dbf7655341014fe71d911004e7e425974004cfd70d9540006de20d8d5402c7e76d951004cfd71d95410057d72d9510004fd7259740006bd64191510067e715974002e7f61551511667c20d95101b5bd72551410adf57199110014fe76d8550024dc73591100067e7259740004ff72d81510eef820d8151055f970991100067c72d95100057f75581410067f2159740024fe73d915001cfe72d81410067f63d9510005df7355110126fa30582540067d52d9541014fc715825401cfe725954112cff7559541014fe7158254006be42d9110006bf7459110024fc735911006e7c6559540056f46158540006df21d8d54024fc73586541e73e505534102f7761551511d5be7695141006df73595410067c7159740004fd725911000df870505400467c65595100047d7259740096f461585500067f3159740004ff72586541667e10d95100eefa10d8151024fc73d915002ebc6595141024fe73d95401577a20195102267f52d915100cfc74597400067d3259740004fd72d85500467f54d95100cef710d85400457c75591100067e515974004cfc7459510106fa40d8154004fd71d915003ddc7355110236df74d8d540067c755911017e7f51d95100067e53d954011ddc735815404efb70582541667e20d951004cfe76d91101667d71d9510005fb70551400057f7559110004fd76d0550236de50d8d54065dc7359540006bf7459541005df7358554006bd6419110005f77155110006bd42d8540236de51d8d541657e76195100467f5259510006fb20d8154006f721d85540067e42d951000cfc745874017e7f21d951001cfe7259540004ff73d915004ef44158654024fe73d854000cfe70d951000df8705511000cfe70d9541005df73585400067f52d911002cfe75d814104dbc7454540006dc60d8d540067f6559110004fd725954000cfc75d8151006fb705954006e7f54d9540004ff735954004f3c5455141004ff72d9151006de62d8d54006ec725911002cfe76d9541035ec72591100067d63d951002cfd74d85541067e705974020e7d625515101cfe72d815422edc40d8d540067f755911006e7f52582541067f3059740004fd74d951001cfc72d854001cfe72d9540006bf64991101ff9c73553410067d32d951001cfc725834100cfd75d91500157c7155151006f7615054004e7e54597411667c40d95100079f735514120e7f625515100cfe70d8554006bf42d81410067d52d81540075d52d8d5419ebe54d91500067c63d95100067c6519110004ff705974117e7f31d9510024fe73595411667c71d9510006dc735954000cfe7458740004ff73d9540006dc63d855404cff7459740014ff70d9510004ff72d9110226bd54d91510067c2159740006df63585540eef860581510067e525974015f7
  | 5 => 0x20000080a0b4000000101c0000017029a2004fe76551100467c53d951004cfe76d9151014fe71d9510106fa10d81540aef860581411677a30d95100067e73d9510004ff73582540067d62d95101867e50d91501debf41d91510067d74d9510014fc71d815404cfc745825401cfe725874016df771595100067d43d95100067f42d95100067c31597401667f70d95101ddbf7459541004fd73d95101667d70d951001cfe72595100067d3159740004ff725951001cfe72d85540067c62195101067c3059740014bc7655141006be43d915102cfe7559110006bd4258341006dc63d8154015bc7155341006de70d8d541067f10597400e67c505974102cff7659510014fc71d91500aefa10d8141006df10d8d5404ef77158654005df735911022edf41d8d54006df7359110006dc70d8d54005fb705511001cfc72d8154226be54d9151024fc73587401067c205974014ebf41d91101577610195100067c32d9510096f651d855004e7e435974004ef741587401067e2059740004fe76951101667c30d95100067f52d8540004fd73d9540015bc71551410067d52d91511067f705974010f3f5155341006be43d91100067d2159740004fd74d8550024fc7358254004fd72d915102cfe75d854002cfc75583410067c74d95101267f50d954004e7e545974004cfc765474004e7d415974022ede54d8d54005df7359150004ef7259110014fc71d9540016f46150540075fb7059110006df63d815400cfe7059541006df71d8d542157f725515106e7c53d95401677810d9510006bd42587400aef71058740005df735514114ebd41d911017e7c31d9510004fd73d91500067d5259510006df735974017e7d31d95100ecfd75d951006e7c51d9540004ff76505500457f721951015f7b10195100bddc73551411dcff7459541004fe76d0550004ff7359510006fb705911010e7d515974110f3f5155141144fe76191100067d52d911002e7e65547400c57c755814110ef710d8554006dc20d8d5402e7c6555140015bc719514117e7f41d951000cff71d9510006de71d8d54006bc43d91501667f10d951022edf75d8d54014fe76d8554006dc735954104e7e74597400065f7359740004ff73d915100cfe76d81510067e43d95100067d5258654004ff72d81542157d72551510067d525825401cfc725865415774101951004e7f74597400067c65d9110106fa50d815402cfc75d9110024fc73d81511c73d52951411067e1059740014fe71d9150004df7359540004ff73d854002cfe76d9510024fe7358740005f77155141236df54d8d540067e53d951001cfe7258341006be42d915117e7d41d95101f5bd725534108e7f515974004efb40582540067f6595110006de10d8d5401cfc725825417e7d21d9510004ff75583410b5ec725814102cfd74d
  | 6 => 0x6001c3a05c0c01513060050013d0482a08c200a405018040000000c0031c0103806030c50140f015a40090d0000b000010185f00c09048017d8020683023815238486800242019068a70000b0080004c05020160608c5bc1700c05018046fc1d01403044c8094004c81d06058a4c313e402220000000206804004160e407000630080b0b8080302a1ac140f03d0680101c020008601c077b00004c06048007140508c000308f2bc0000030020190002c0042100c000087101c0801c0300000000010000000174104010382e05c07528000040352a430101701000000151d0000000300003000cc00c010043f01422014ce091370340403809ab00704405008007ac8d000000040400cbf0683318002018160bc0300c1f0fc0600800000cf00c0503800001240040a040015c4000019600c030000603003028000040a0d8110080101001538010e02e0080160c0006c1202416000000000201c0c4e013000046f812000001400d0180100000018036b003000130981f000840081e0cc06001520040000802038050201854b650343900c00000000280b004070101005401058000000b0011500400010010200001c0000c950001200002014000058d078020000a15404004010caa31040d004120180002806008190180a0385c00404048523a45901000030000300002433070c506d2800c00054000700d0100201001014050100612c3c0281a0100004015000010000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5f65dcd64440010fb0e196ca880be9e60072d95100063632ee4b222000c5f735c965d00014f70a982c12a0829e20172597400062fa96e6b2e80048dc835d954440014bb0a10ec6aa0261fa1e535974001c3fc3aa5b2a8000a5e83dd3654409f0fb0f392cba00029e60253d951000636b90c5b2a2046a5e851c763550078d8e4a92c88800e3ba1f72591100054e41ac83222000c6c751c964440011bf06b92caa00022fe1173591100043f438cab222000a5d85c8363550018b8e7b2aa8a0802b560660d8d5422d4f42041b1aa800c5c73d9564440018b8ea39ac88800393d8952d8d5404d1f426caaa2200587e85dcf605440147b09196ca88127171cd52591100053cc0042b2e8000a5d8308565d00014f700a92cba011aa761072d8d5400636b96c5b2a2045c5d85dcd65d000147d08316ca880b21f21b75591100246e41ae4b2a2000a5e8318865440011f700b92ca880268fa1232597400246f43ee6b222000c6f825cb65440018dee4a92caa094f0f5d764991500056d404c3b1aa82cc7870d9554440011bb0e106c6aa00237e0d76547400061fba4e9b2a2000ad58108363550010fb0f216ca880031dd97715511011d2f42ce5b1aa800c5c65dcd644400147b0a216c8a880237a1c63585541653d400e7b2a2000c5c735c965d00011bb0e10ec6aa00327dd073591100043fc3ec432a2003c6c72d49644400147b08316ca8800e3b20973595100061eb2ee8a8e8000c9f741cd65504014b906b16ca880123720d72591102364e3b6e6aa28200c5f751cd64440110fb0e316ca880029e60253d95400045fc22e4b2a202f87f855c364544011bb0f216c6aa00f2b1c9425911000637b92a4b2e8200c5e871cd65d00018df0bb92c8880039694363d815404c5f426e7b0282028bc845cd60d04014bb07ba6ca88002b520562d8d540053cc0062b2e800087f855cd65500014b906b92cba000297a0c21597400045fc22e4b2a8200c3d741d365440071d904b9ac88811a97a1721d8d540052ec2c85b1aa8238dc86dcd605501347d09392cba012b171cf52591100062fb9aa4b2a82008df835c965d00071d904bb2a8881530fdd7745954100666398e4b22200587c851d9544400147d08310ca880023be0973591100052ec2841b1aa80087d879cb654408f938e6a12c88800317e0d72597400045fc22e6b2a200987e8794965d00018df04b92cba00161f21572591100062fb9ee4b2e8000a5e839c965d005f4f10c986ca880021f61773d81410051ec20c432a2045a9e841c763550018d90bb92c8880031b1cb65591100052ec18c432a204e87e871c965d000147f08b1eca88116a7a1072d8d5400636b92a5b2a2000a5c835c565d00070f90ea92caa011aa761370d8d540056bc0ac5b1aa800a9e8390b645448b4bd0e39acba00039a18920d9510
  | 1 => 0x90fa92c8880023de0572595410046f438e6b2a82058bd84dcf605500147b09392cba0003171d773591100056d404e3b1aa80087f855c964440014bf06b16ca88123271cf42591100062fb9aa4b2e80008de87d8d61550010fd0e216ca880021f61e32d951000637ba8e4b222000a5e8390b65440018dee5a92c88800e1f217725951023727c12a5b1aa800a3c8458865440018f700b92cba00b29d21921d95100046fc1aebb028200a3c8458f65440091b906b92cba00031e20172597400043f43ecab222000a3e841cb65440018bee6a92c8881169761471d8d541653d400e5b2a20098bc845cd609508b4bb0bb86c6aa0021fe1573583410062fb2ee6aa22000c5f7354965500091bd0fb9acaa000317dd4735954004d1e422e2b2e80008bd84dcf60544015ad02106c6aa0063e20172595410246f41cecaa22046a5e85c83635500147b08396ca880262fa1373d81512354ec20e3b1aa80087e8708565d00014bf06b92cba000237a1c10d8d540062fb9ea4b22200087f855cd65504a58baea31ec0aa00317d4b73595401053d40042b2e8045d9441dcd54504015ad03306c6aa116a7a1021d8d5400667b98e4b222000e6462484654400117d0fa12c8880b29d60774d95100052f418e5b2a2000a5f835c565d008b63d09286c6aa0021fa1e32597400056c402c5b1aa84dc3f75dd165500091b906bb2a3a00029e602515974004c3e42eeca8e80008df835c965504018bea5b9acaa08031720d72597400046fc1aecaa22050c5c701cd65d008d4bd0a396c6aa0161f21573591100043f43c85b2a200087e870c965d00011df04bb2a8880161f21573583410051fc22c432a2000a7585c8761550010fb0e10acba0116a7a1370d8d5400c7d43ee0b2220038bc8750964440014f30138acba00161fa1f75591100046ec3821b1aa800c5f739cd65d00011bd0e106c6aa147179c073597400052f418c5b2a2000a5d8318b65440090ff0ea9eca880bedc20530d95100052f41ce2b2e8020a788054b605500b0fd0bb9ec0a091a97a1642d8d540056cc0043b1aa800a3e848cb654401317908b92c12a0031b5c952d95400043e43aa4b22200087e878cb65440010fb05baac88811a97a1420d8d541553a4324232a2000a9d8408763550091bd0fb9acba00029d60652d951000636b92a5b2a820987e87d9554440070ff0ea96caa08268fa1071597400051e422c632a200087f855d9544408b4b90ca96c6aa0021f61e63195100046f438e6b2a800087d870c965d00014bf06b10ca880123720d725954101c3e43aa4b2e8020a7a800c565d000155904b20c888117175d763d81540056cc04c3b1aa846c5c65dcd54440011bb073b2a8880021fe1d631951000657ba0e4b22202bb70814c065440011ef02b92caa00021fe1572595100056d40043b1aa800
  | 2 => 0x365951100046fc1ae4b2220098bc845cd65440018dae4310ca88143179d463d81542be4fba0c6b0aa80087f8758865440018dee4a92cba00031b1c865591102352f42ee1b1aa856c9f7418d60550574f10c980ca8800317dce53597400247c43a60b04a80087d87188654408b4bb0a396c6aa0029d606505974128e2f3b4a1b1aa8558bf845cd60d04070f90ea92caa081237a1f73595410043fc2ae6b222020a7a809c565d00018bae729ecaa00029be0963d95101653ac08e5b2a20008bf845c964440015b30138ec6aa0029720d621951000536412c7b2a20008bf8759064540018bae729ecaa092e9ee0162195100046fc1ae4b2a202fc7471d9554440018b8e7b92cba0002a720d641915001c3fc3aa5b2a2000adb8058b63550014bb06396ca8800237e1d62d8d542952f41ce6b2e8000c6d72d88654400147b09192cba00161fa1c621951000667b9ee4b2220008bf8759064440031ed0db8aa8880029de0552597410147d436e0aa22000a3d8590b64544090f90ea9acba00021f61f21597400043ec3cc432a200287d85dcf60544014bb0b90ec6aa00237a1f63581540046f438c6b02a800e4c6254b63550091b906b92caa0116c721152d8d540073231243b2a2000a5d839c565d00091bd0db9ac0aa0162f61372d81540043fc2ae6b2a2049c5c73549655045f4ed02396ca880023be097359510006ca38ee6aa282018be86dd151500010fb0f192cba0127179d952d8d5424e2e39aa4b2e80008bf845cd655002347b0838acba00123720d75d814100c5e422eca8e80028f4815c965500010fb0e216ca88127171cd52595400062f42ee6b2e8045c5c76dcd545440147908b16ca8800297a0e50d95412346f43c85b1aa800c5f751cd65504010fd0f90acba00262f211725951000637b92a4b2a20008fb805c965504998eeebb8aca880029be0963195100062e398cab22202ba788648065440011dd0e392c8880021fa1c32d95100046f43843b1aa800c6f65dc964440011bb0f316c6aa002a7a0e42d911000536412c632a2000a7b805c965d00018d8ebb92c88800f2b1cb42591100062eb98e7b2a2000a3f8458c654408b1bd0e39acba00be9e21920d95100054ec2041b1aa8008fb805c965500018dee4a92c88800327dd073595400052ec2ce5b1aa80387c8754965d048d4bd0a10ec6aa0029760e72597400045fc3ac8322a200a9c83590645445f4f301ba6ca880031bdd772591100062e39ecaaa2200287c8759551d005f4f30039eca88003175ce53d95100046f438e6b222000c5c73d95545000117f08b9acaa080e1f21d52595100066639ee4b222009a3e8408565d000147f08b16ca880031bdc952595400043f43aa4b22200087e87d4964440014bb07216ca8800317dd773591100051ec2042b2e8046a5f8254b635500b0f
  | 3 => 0x868600929139e8a40009b480013000000877378740215000111c0d0421820012d040447c0300402010b84414003f0008845001fc020804801941801914ba0a7f804c40400288022d0f0187e0e12c6c28041a81c001c0009008c33d0d8960b170101a721580002050000090001705a22af0f118840273070be1d1f0000200548f0720106000443f0e03e1e0519054820c0088c0e1f00b4c9e08060740517b09b9ec0a08028f61
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40fe61741d3654400184d835c86219510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x6
  | 6 => 0x94b
  | 7 => 0x94c
  | 8 => 0x94e
  | 9 => 0x5
  | 10 => 0xa0a
  | 11 => 0xa0b
  | 12 => 0xa0c
  | 13 => 0xa0e
  | 14 => 0x180a
  | 15 => 0x180b
  | 16 => 0x180c
  | 17 => 0x180e
  | 18 => 0xa4a
  | 19 => 0xa4b
  | 20 => 0xa4c
  | 21 => 0xb89
  | 22 => 0xb8b
  | 23 => 0xb8c
  | 24 => 0xb8e
  | 25 => 0x1849
  | 26 => 0x184b
  | 27 => 0x184c
  | 28 => 0x184e
  | 29 => 0xbc9
  | 30 => 0xbcb
  | 31 => 0xbcc
  | 32 => 0x1049
  | 33 => 0x104a
  | 34 => 0x104b
  | 35 => 0x104c
  | 36 => 0x1949
  | 37 => 0x194a
  | 38 => 0x194b
  | 39 => 0x194c
  | 40 => 0x1489
  | 41 => 0x130a
  | 42 => 0x2c9
  | 43 => 0x14a
  | 44 => 0x14c9
  | 45 => 0x19c9
  | 46 => 0x198a
  | 47 => 0x134a
  | 48 => 0x1a89
  | 49 => 0x138e
  | 50 => 0x124e
  | 51 => 0x130e
  | 52 => 0x104b91
  | 53 => 0x104b93
  | 54 => 0xb9053
  | 55 => 0x104b94
  | 56 => 0x194b93
  | 57 => 0xb9953
  | 58 => 0x74a
  | 59 => 0x1a8a
  | 60 => 0x105851
  | 61 => 0x105853
  | 62 => 0x185053
  | 63 => 0x105854
  | 64 => 0x28e
  | 65 => 0x104bd3
  | 66 => 0xbd053
  | 67 => 0x104bd4
  | 68 => 0x148e
  | 69 => 0x1a4d
  | 70 => 0x18ce
  | 71 => 0xd0c
  | 72 => 0x188c
  | 73 => 0xd4c
  | 74 => 0x1a0c
  | 75 => 0x15512
  | 76 => 0x19d4d1
  | 77 => 0x1a9951
  | 78 => 0x1a0d
  | 79 => 0xd4d
  | 80 => 0x14c
  | 81 => 0x134c
  | 82 => 0x5cd
  | 83 => 0x1a9051
  | 84 => 0x1a9952
  | 85 => 0x1789
  | 86 => 0x59316
  | 87 => 0x59496
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 874
  | 6 => 1021
  | 5 => 418
  | 4 => 2
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
  | 7 => 2*((h/298+packedAt gbK7 (32338+(h % 298)*10) 10) % 874)
  | 6 => 2*((h/438+packedAt gbK6 (49008+(h % 438)*10) 10) % 1021)
  | 5 => 2*((h/139+packedAt gbK5 (24662+(h % 139)*9) 9) % 418)
  | 4 => 2*((h/7+packedAt gbK4 (140+(h % 7)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe0f80fc0783fff83ff00ff067d8e7e307e73
  | 1 => 0xfff000fffffc1fffc0fff0019a2f19c3f9f9c
  | 2 => 0xf07ffff0007ffe07ffffffffe1c301e3c1e3ff
  | 3 => 0x7fffffff800007fff00000fe03fe03fe03e0
  | 4 => 0x7ffffffffffff800000000fffc0003fffc00
  | 5 => 0xff8000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x12e02882ca1812a9a1990256020c862e302e31
  | 1 => 0xb25000552aa4132a48a560208a0b094169694
  | 2 => 0xa00a53100044a4044a24a8a861430140c1414a
  | 3 => 0x82739da9ab0010a773c80c0cb603da037a03e0
  | 4 => 0x85ce6ce3c7739c001003030dff40003adf800
  | 5 => 0xcc000700300621004200c0c0fdfb6df8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40441
namespace PEqualNP.Outside.L_meta_40441
open PEqualNP.Outside.L_meta_40441.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 92 := block_range (n:=92) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 92 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 44 := bs1_5_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 112 := (concat bs3_3_0 bs3_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_960 : Interval s3Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1056 : Interval s3Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1152 : Interval s3Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1248 : Interval s3Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1344 : Interval s3Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1345 := (concat (concat (concat bs3_4_0 (concat bs3_4_96 bs3_4_192)) (concat (concat bs3_4_288 bs3_4_384) (concat bs3_4_480 bs3_4_576))) (concat (concat (concat bs3_4_672 bs3_4_768) (concat bs3_4_864 bs3_4_960)) (concat (concat bs3_4_1056 bs3_4_1152) (concat bs3_4_1248 bs3_4_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_864 : Interval s3Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_960 : Interval s3Atlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1017 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 (concat bs3_5_288 bs3_5_384))) (concat (concat bs3_5_480 (concat bs3_5_576 bs3_5_672)) (concat bs3_5_768 (concat bs3_5_864 bs3_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 48 := bs3_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 90 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := bs5_5_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 2 := bgb_4_0
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
theorem bgb_5_384 : Interval gbAtlas 5 384 34 := block_range (n:=34) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 418 := (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384)))
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
theorem bgb_6_960 : Interval gbAtlas 6 960 61 := block_range (n:=61) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1021 := (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 (concat bgb_6_576 bgb_6_672)) (concat bgb_6_768 (concat bgb_6_864 bgb_6_960))))
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
theorem bgb_7_864 : Interval gbAtlas 7 864 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 874 := (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 bgb_7_576) (concat bgb_7_672 (concat bgb_7_768 bgb_7_864))))
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0feeaeee8fce8e0e0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4243120352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40441.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,4]⟩,⟨.and,[0,6]⟩,⟨.or,[0,1]⟩,⟨.or,[1,2]⟩,⟨.and,[2,8]⟩,⟨.and,[4,9]⟩,⟨.and,[5,8]⟩,⟨.or,[11,12]⟩,⟨.or,[3,7]⟩,⟨.and,[13,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4243120352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4243120352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40441

open PEqualNP.Outside.L_meta_40441 in
theorem PEqualNP.Outside.L_meta_40441 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4243120352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4243120352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
