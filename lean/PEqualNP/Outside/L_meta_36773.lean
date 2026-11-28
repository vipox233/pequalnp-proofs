import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36773.Model
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


end PEqualNP.Outside.L_meta_36773.Model

namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat) × List BoundPool

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2.1
def apools (g : Atlas) := g.2.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SBf (j : Nat) : Nat := [2, 8, 7, 7, 6, 6].getD j 0

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
      testAll (k,ws.length,ws,preCov true ws,apools g,links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ p ∈ apools g, ValidPool true (roots g) (target g) p) ∧
    (∀ a ∈ first g, faithful r s a) ∧
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
        exact decode_faithful _ _ _ _ _ ready.2.2.1 _ ((selectLive_sub _ _).subset ha)
      · exact ready.2.1
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
      exact poolCut_sound (ready.2.2.2 k i hi hn) _ he h.1.1 hc

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

end PEqualNP.Outside.L_meta_36773

namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def s0K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (i*3) 3
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 1 => 2*((h/1+packedAt s0K1 (3+(h % 1)*1) 1) % 1)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffde73
  | 3 => 0x6f9c
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff8205
  | 2 => 0x2552
  | 3 => 0x1958
  | _ => 0
def s0Atlas : Atlas := ⟨1,rawDecor 14 s0Pos s0Neg, 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x120090010400410000000404400d604001300800000000104504028058000100000064600024ffc42ff31fd30ff41fc32fc41fe21fc40fd40ff40fe30fd21fe41be40fc30fe20fc43fe32dc30ff20ff21fd10fd43fe31ff42bc40fc20fd20fd31ff10fe43ff43fe42ee20f410fc21fd41fe40ff32fc10fd32fc31ff30fd42fe10f610ec20de30
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x21cc30883ba6598f750e30faa0c63bd540c6dca418df55020de29c817d53d0bbaa3185fd5232bf286877f53886faa710df94031aea98857d548cbda64107dc8610f6a14657d501077886207bd0942fbaa4217d52d0fda8490df551219f2a6216e52d03f280207750d32ba28a61bf42902eea2a07d94730fa294217d52443dca5985d94442f7184417f530827ca9987d0c210d620441df438c37c80107750030b6a9621bf52103baa5185fd5030de204617451482fca7a17dc8621ef90c61de500c3d8a3107710030bf2a4415d53c83da84215f94e20df2a6217c53c86f8a6906f90220f728041f5548437c80887b0c820eeaa0617d500c7da65105f94221bf29a217551cc3be61185f95131bf28463df320cafaa6905f54610dea00817e50883bc86187d08010f6aa0417d51d03bc63185f54430bea8483ee52106e8a2a05f54a43bfa8a41d5310c6faa810efd5120aea9e81bd43d07eea2985f94443bea90217e53843ec43086f94640faa0c21be40843b863185f94a30fb20c217e510cbea20085714d40f6194417e5310be8a2906b50842f7a9841be41903eaa7086f50441be29841dd53106fca518fd54810be2a6637e50083ec40087d8c431fba9c21bd43902fca1197d10610deaa641bf329037c86205f14542dea8c81ed52c43b4a0186710030bf280217d5490f7e84a0df95010bfaa665ee52d02faa42077d4430fc90041f650043b843186f10210bf28c81f250043ba64186f94440faa8e817e54cc27aa810fdd0a10fba9421f642843f620885f55221fb204217c53486fea0a17d95010fb18a437c548c3ee64087d8ca10de28c81f543042fea8887dd0210bf28e617f52502fea8085f95132bf28c43f521843d840885fd5330bf28083f621043dc63105f14543de99081dd53c83dca9105f94a41be28243be40cc2fca3197794c21bfaa243fb10842fea7885f54f21bfa9a41be404c3d4a0105754c41f629841bd42506faa2207750630bea8465de418c2faa5186f14440f6104217e50d0bda60105fd4b10fb20c637d53883eea8085f55320fa21421be31903ee4008770c830df990817d5090efaa190df15021f710221df518c3b8601077d4830f6996437e52087de43105f54e30bf29061ed43082bea6a05f94743f799041dc518c2fca6187b50e20de18c817c52443ea60085f14e20de19081de30043ba87995f14143ae29a217e5010f7e43205f94431dfa8c81f631042fca890efd0842ef21c61f730042faa5a0f7d5030f7104216d52cc3bc8621df15032deaa065de428c2f8a5085bd4930eb18421df428c3d8a710778ca30ef99061dc535027aa9905fd4530bf28c63be400c2faa3997d0c410beaa221e521086f8a8106fd0441bf29221f541486fca3905fd5131bfaa241ef328837ca8197dc8410bfa8a85f4218437e87a0df15310
  | 1 => 0x6510cbda85105794c42bea9e41be54086fca790dfd4532bfaa4637c540c2fca7217714d20dfa1887df318c77a62206710230f7aa041f710042fea818fd48010bf28085f432842f8a2985fd4a10bea94417c51482f8a890fb4c620bf29883ef324cb7887205b94220fb28e81e420043be6218fd54a10ef10861ef51882fca2217b946209eaa065be53102faa610f790d32ee10861bd529035c81107d4c621dfa08817c514cafaa9186e94040bfaa261dc30c83dea7105b94020df21c81dd328c37c42205f54830bfa8263dc328c37ca99877cc430bf29c87f443042fca9905f54a40efa0861f751503b8a2185f55120f7a9261df430c33c80185f15220ee98863bf311037881905d54443fd200817d51cc3cc40087ecc130bf2a461ef21087de4310df94b30bea9c85ed320cbd841887b48020bf2a043ec43082f8a818df95031bf29843dd5310afea6885d54442bf284837d5190fbc80187b54841faa0021ee204837ca0207d08210f6a96617c548caf8a7886fd4440fc880213f544c2faa620efd0c40beaa4817e5310feca2217750830be2a2615f53483dc85194f95320dea1081df53442faa818df95032bf29021ef4290beaa6087bd5220bf29083de510c2fca5a0fb88310bea9821dd310c2f8a4a0fb14930dea98817e529037ca5207d84110b7a92817d54cc3ba8621df54c20beaa6657f53502fea790df548439f2a0437c54886f8a9907e4c030dfaa221fa10043ba64195f95020eea9e817f50506fca1205794230beaa0617e54483e880087d88210dea1a83ed42c87dc8490fb90842fb290213e540c7dc6490fd90c10f6204417d508c6faa720df55331ef18261dc528c3eaa221fb10e20efa9a41bd329037c81186750c43bfa92217d548c6f8a4085f55032fb29c217e53c837a86a16f90942bf29c43ec40083ee65087b50020fa290217d53487d8a910750c010bea8c657e530cafca720fd50e10bf29a417e51102fca421df14131b6292213c544c2f8a8885f94030bea9c657c538427aa818df14f20ef180417f54c877aa810fdd48109f284817d528c6fca4195f14c21bf29e837e54c43ec60087b54831ef99461b440043ea61087b54c20ef294615e53c42fea4085f94321bea9681dc30c42eca3a05f54f10ef18221ee54083da811077150309eaa661f454043e863085fd4f20bea9663ee43082fca6085f15010dea1e857c524c7b860907d4c810bf29621bc32902fca0195f94742ef21e653e540cbbc61107d94c10bea9483f730842fea498fb14420bfaa065cc3008378a6205f94f40de206213c54442fea6a0f754830ef184217e54842faa5086f90541ef298836e52107dc4290ef10120ef29e217e528cbf641107d8c610baa8865ef52443b886187b90e20f690843dc418c3dea4a05b54841f718041dc548c2fca3996b10020fa19
  | 2 => 0xc3ee84086f10a40f7208417e5190bec8290f78c1209faa2217e50cc6faa198f750a30f7194417e544c2fea810df95040bf28841ec20043ee210877d5230dea1085de520c3ee80085f15120f620841dd300c2baa610efd0e40efa94617e53083eea6087ed0140bf290637d528877ca818f794c42bea9083dd318c3ea42085fd4c10ef18861f442043dc84105d94730f720c417d52c42dca5987b55220de2a261ee51082faa7a06790230beaa2617d51083c841087d48210bea8c41be21902fca9196f10330fd98461f65110efea6a15794f20ef28c61dc310c3f440105f55310fa28a617d540437c62207b10620faa0c43dd324c6d8a4a05f14d40fb20c43bc21902fca6205f54443fa988637e54ccaeea29077cca32bf28683ed51883dc40087d55010df20641bf419037aa7206fc8440ef20861bd54cc3de85106f0c4409e2a241f443842fca210efcc640de29081f741506faa1a1df54442bf29663d630042daa421df95321dea88815d53c43daa2105fd5320f690841cd320cbdc85107d50531fd180617c54ccbcc41086f50b41faa04213d54c42eea2987bcca32bea9c81f421042dca421fb88420de200617e54106fca0205794f40bea9e837c544cbdaa421df15231de908817f5150efca3185f94332fba0821ef40882fca618dbd4910df202817c53506f8a6085f15210ef186217d500cbeea2907d14c10dea1481f731043ee86085f95043f690c41bc40042f8a0a15f94243f621441dd410c3bca9187754f10bea96617651c8378a8905f54630df290817f524c2eaa3905fd4143df29c81bd319039c60107d90531fa20421bd54c43de40107bcc420fb20021bc52903b882185f94a43efa9a81f542043d842105b54b40fd902417f548c3ea4210ef50440df20881dc30043dca6107d54730bf29421ee53883b887187750d31bfaa6637d54c879c61107bd0420bea98817f53086fca2185f54e31de208816e52c42fca7207d90e10bea8087df32cc7a8610877d0830df2a641f531042fea8105f14930bf28c41de540c2fea7107bd0c20bf28485de420c2fea8997750f319f28081de320c3dc43105f14d10bf2a6637c515036c80087b08620be29287dd548c3de871077d0d43ae29a41ef20883eaa2215fd4943bea8e87f4538436881086f90840beaa263ee40082faa9215f94b43f7a0c41dd408c2f8a0a0f7d0030fb18421dc53443d8a4a06f8c840dfa1485bf42102eca1087d88421ee21061ee52c43ea6290fbcc620ef18a63dd210c37ea5207b94843dfa00817e51d03dc8590df95231bea84857c5350b7e86a17b8cb21dfa1c87be40c43b881187d95210be28265bc42103da62105f54042fa994217c525035c80106f08440bf296817d510cb7c80907b90220ef992637f54882fca8885f94410fb98a637d50d06faa6887b94831bea9063f
  | 3 => 0x530730060082f800002004000160120004f01b0002080196a0000000002d00807c0000304c024040060060083080e0000244d80000c0000004600e1b82396f0520bc000161c0c240010d010034001ce102098008e20660440505a01a3240209c0880100000003803c8180900000001816012064130000002c4000ee00c0000980000009c1200d01a0040186d20e8740001b00634c0403351603c0280003a0180180b00a0701b80548c000000150000301900a000008008f2064020158140020100180703006c00030000004018010008e85915c0441900603a03201c0a87b01605c0485f2fc050020f800e6a80180014c0002f8041820680501b00007408005004024008fe0000300b8010009700021700602c460001de0042800700003008b9907a1380504b0040240000014002c0002500a01009843002288ae80100003c008053ee1600300201600c0800131000c1900000802400018006630e680c1dc0284b04600c0500000c0042f4000020300080282e0062e8000001885d4010060000002a00622c0380400501a0002b00e05c010000000005f00e800036020020c80083490685d0003880002903200c048000aa01828000008000090052d01c80600b0040104488d2ce00400011028604348050000040509905e0001580e1a600006808044010003e7004090000442aa0080000201e010b680606c0100005e0020377e8320dfd5210efa0461de324cbee41086f50c43f618041ed41882fea090fdd0610f7188417d51c82faa3a17dcc610bf28461ec54082faa1a1770c110eea8861dd218c3b885187d0c010fba1c21bf43506faa9087d54432be2a6617f52506d8a4987754c21bfa8265ef30083d862107d15210bf29041f531843b861105fd4d21de20041df4390f6c81085f54642dea0c81f451502f8a990efd0f42ef29e817e5290bde80105f14b10faa14217e52102fea910f750c30f629221bc41903d884105f15131af298837e53c437880887b54e20f698441ef21083ee4290f714830faa08837f51503ec8220ef900109faa241bf42d07b861087ed0240bea9885ef30882faa920df94441faa0821f652843dc84997794f20ef21e63ed52d03bc43187bd4420df19481f641043e882086f10220bf28c837e5190efaa7087dcc631b6a90637d508877ea8985f54021bf280437f53842eaa3a07d8c621ef18641765110fd863106f90a40beaa2657d54882faa32057d4d10bfaa621df318c2fca910ef54840bf28421f741907dc64196d50441efa0c61f551c82faa1997b50932f69924376510cb78a8886fd0240af29843bd21903dc64107d8c810f618441ed410837a86205d94010fb28e417e540c3bc8698df94842f7a1041de408c37ea6206f90d43be29c43df210c2fca690df95042fb21021bf53903da841077cc030af28061bc404
  | 4 => 0x12008070138002220283b0000ae7400100300c0280400000600803b7e00c0c4000060020200183c03c01
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x54310f1f5390140b558f40042ad62106408f59253882b464440109dd855010acd6210c30b6980518c3a440082108f59353c834553484219bd8950d0f2c52101308f590524c7665148620cd153514c3ca508c020b358b408c23d6494410d554c53042776544010ab98b40902d663c80109718d50d0a7460544438f19153442ea6014c20c754c40c42766510a10ae98052902cd63c8020c750e5010f376550441d514e10442b6610ca409d18550d0ee7624c210c7d535348275658c4109d987540ca3e6414e21cd952510ca5e6315020ab593308826d6510c20ec10320042756590410ad990318427b655004097d95310c71c5414d10ce982501026e6215131cb552320cb1e5390310b5984320c2d763502109b588544c63e6494620a7990510c3c430080109b988540c66f6548020bc980530423d6595021a7590310c25e658c1109b588540c3a840cc020ad99330842e6610ca20cd95151cc2d76344010a7590320c34d3294032c754c531029d6394a409d59740042756114943a798c419023c64542328f990540ca5e63145429b98b504c6ad6494620ab98841902756115330d394e20c431d5454c21c7d52304831d540c320ab588411026e650c4209bd89544829d6308640d9d4d210863e6015110e3508428c2da60d4a309d986548823d6414f20b358a548c2e661c8220cd152104423d650ca408f99440482b66194a40d5146304c2ae6214440cd50650106af6448020ab99051082cd620c4309ed81544cad563d0210d954a51cc25f63551219b98853042ce6310620ab98b401031c54d4d10b9185300838d4310e208f99440443565354720c754f4210a3e6494a109b980524423d650c640d95495110ecd6308620b6980548c2ce62cc0309d195314878e408c2209d58454ccb2d425444297195434cab664c8010b6983520c32c5488120d314a30443375414530b558e310c6b564148109b18152106b6610c8408f990524c71e5310310d394e52c4390400c010cd95151c826e6294410ab19130882d663d0010b598c42043a52108640b3d8d20082cd6395220c354d4210acc624c030d3d51320cbc43008210b6983518c33651103209d98654482746154242ad99310043a55448421a798c511023e6095032d5549310c7375410610ad99021042756115132d5d4e104434d5394841cdd46519029e6310440b918940042b56494e10f40c3200426d6295110e9484211029d6308440aed81321029c644c0309b98854cc23c6015110d3d4c525027661d4132c755153c827565104109d584540832c5290140cb54a40cc3555390441cbd4a404c31c53901209bd89501065f6354342ad593100425c63540429d9825110a6d62153309bd9521086e8604c4209d185544ca5d63946409718d50d073654947309798e548831f548c130a798e51902ea6014420
  | 1 => 0x823e6494c30cbd5020442b564904418f19153482b4644c0109718d50887365150640b998841042b76150040b998b4084354518c1209ed9510042d66315010f18c2200432d52103108f590514cbc8400c020c795153c423e659013097994418c2ce6308620ba181410825d65084309bd954210b6552504419798f504863e64951109dd9521086cc6250d329dd855010f54534c621c794d439023e64d4f109798e51902b56110840b6983548c25c6354321e5902308425d63951309dd85544836652947309d986544c31d5454f109b99441882766115021e994941106ad640ca209b588548c69e6308640ba18143082b66494e10cb95152cc25d6315320f20c0200429d6314840d3d4830442e46148020b998854042d463505319bd89500c6d66310610dc98250042ad640c620b558c21842ea6015020a7d91300c3553194031b598f108425e650c1208f994311029e6394a40d590d5110fc63088210e510230042776155132c7552530866f6254243b3988438c26e6294630b958b300423d6494e10cd54451103675208610cd551310c77165940108f191500ca756194d10d3d4e538831d5494f10f14c431083355454432b398230082d46348010cb94a40cc2ad620c640b3988310c3954310e10d314d324866d62d41319799453443355110440e310030882b4644c210ab593208825e6395110ad19120842e56194e20ba98351082756195130d394e52d025e63948209b98a548c2d56110e30d350d5210f2c5290130e910020042e56110c209b988540c32d4354843d914921042ad6414c20d9544510835653947208f59252442d763500109d984540c6b46150d419b58b5050ee56215010b5586548c3a54250521b9988418423e6414c20c5551310c6ad6210c409b99441082ea60146209d9825110ee66114c20b358c51082746154232e990020842e7624c0109bd89508c79543944439b1895090f1d5390310a798c21102d76150030ba980548827661d4f20aed81311034d5394b10ba98053883365494720d354830c425d63d4121b958b3084395544c4319b58b540c6f36050c10d5cc9510cad56194a308f992524425e63d53208fd91508c65f63542429758f540872d4294042cd55251cc2b6640c410ad9933004355510c4308f992510436652947408f992520823d64148109b59730082d561108309b9885350745524c431c795253c42ba60146409b9825210f4d5388310d954951cc25e63150328f191500865d6590c308f191500c6ad620c4409758c52506776154d10e5102308431f54952309758f5050ad463482109d982510cad46344010cb94840cc26d62d4141c7951530865e6510830b3588510c26c6254241c754d41107c5524c4319798f5050a6d65108208f99054086ba60d48409d586534833651903209b189500c65d6508630a7d9
  | 2 => 0x640ca10b598c21842e661d0020c715143cc63d6414b10cb95152c426c62543439758e529032e5494b30b398c540836452d4530d99495110e796584010b998730083c53254432f154d21087565354442d3548320c31e5090030a75924310f655254740cb55152cc2cf62502309758c54c87aa6010020cd55221086756114c20d914b515023e6495130b558f10042b8604c4408f992544838d320c840d394e521071d43548439758e524425c6354242ab980400829d6408630ad59320842b5640c6108f993530869d63144409758f54c425e6315010e5100308431c539014097d95300c32f5290110cd144404c2776548010d9d4b514c30d43548439b58a518c2da6014830ae181321031f5310120b958a210872d5454b109d98652903355415010cb15142486ae640c820ae98353102cd62d0030d994951cc26d6214f10e6942400c27b6054d21ad59252842ae620c640d9d4a52843e33008010b918121086d66115030cd15141886e662cc210cb148404434f5294a309d58453c82f260d5010ab590210835453d45208f99053c82e5620c610cd55041043655108420d954a5110e5d63d4b10d394a30c42af644c220b6d81420c35753145208fd9541106e56110a209b98b53c434d5390842b958841043375414520f294030082766510810a758c419031e50100308fd9150c87545314540b958432082ae6090020ad593300426d65d00209bd89534831d5415030cdd46405026d6294d20f298030882e4624c2108f993504cacd6310820c715053482e662d00109d584548cb2f5210110d3548520c3a840080109d185544831d5494f20e9549411065e6394d20b598e528436752d4540cb551210874c534cb21cb54a40c433552504419d587540cb2f54149109b988540431e5494c21b558f1084398400c020d3551320ca9c63500409798c544865f63551309e181544ca776154910e6940400c25e6315021d95095110ad66194a308f992518c31f6550c43ad584429029d6494a30b9185400838d4210830b6181420c2db60484309798e52442766115020bad8141083a8400c020c7d50304831f548c110ad986539023e6415031b9d8540882d663c4010c7151434c66d6215010ab98a53902d66310410e594d411065f6354341ad59330842e56115020cd153514831c5350d42cb153524c2ad6210e40bcd81320434d5394b40b5587408c32f4354843f8d0020043954310c10cd151410423f65508429d185534834c520c110bc59650042d56308410b358c41882d4614c030c7551320cae561d00208f19150c875553544429bd954008396408c0109d58652442ac6250d42c715143cca3d64d41319d9845250ee56210610e9900200423e650ca409798e53442776155130e9951210872f54d4910cd55151cc2b46448010e3900308826d62145439b594438
  | 3 => 0x109d18550ccacd6394620d594230042d6639521097597400c2ce6294630cb15352442da6015030b358f400823d6494a108fd91500ca6d650c820b958b10042ae6210c40f194d21087354254442ab58a519026f62542419b5963208354534c4109798c52043575394e10b918941486ae620c4409dd95400429d6310440c95095110ad46350210b5587400c2b7644c210b958730083e250080109d986548c32c5450b21c7d5030443655294740d554c310431d5390320d394d328834c53d4940ad586529023d6414e21b998831842e66194e20d5144304826e6510e209d98454c83675284110d9d9521086b56110c40b5984438c2ba60148409798e528423d6494630d994020042756115032b6181410c2d461502308f191508c65d6394410d3d4c20442e56214c10c750d5110fd2600c210ea9424008396400c010b558c41042b56194e409bd89544c67661d4142e9102208434f53d4910ab58b409032c5414930c754c40c826e6094841d954852042746154342b358f208836652486109758c5150b57654c4318fd91534423d6494d109dd855090e6c6254331e554d411075543544438f99053c869d6414830b398e518826c65509218f993504866c6054843b3189408c25d6395220cd151414c6776154242b9185308831e548c310c795230c82ce63c8020d3942300823e6508440f10c220042ae64c80208f992538434f530ca20ab99053082e66110c20c9549411065d63d5320e2100300825d6594c219d1855010f56534c610b5984520c2b66414c10d394d52106746054442cb54852102e562c4210b398a548c23d6414d21d5d46304c32d52d0441ae98352902ea60d5220ad590310426c6255130e350d424ca7561d5330a7990218c23d6494c30b958843042ad64144209b594310825e6315031b5584540c2b66114c408f99431902e46150921ea94040082ce6310820b598c21042e56210e1097994410c32f5488120ad590320434d3254432b598c52042756510c109b596420831d548c310cd54d41106b56114c40b398f400826e62d4141b3988430c31f5390120d314c525033754d4530ad59320042e7614c020cd146404c38d5350842e510030043355454720ab58b401031c5350d41cb95020c42d661cc230b558c4184396400c210a7590510c23c6454331c7d4e539026e6215021bc98352042ae6408420b958831042d56110c309b1895010754534c521b998b30042cc6350220aed8121102e4624c0109b98b54c439a6010230c3551320cb8d320ca40ba983538838e544c8328f59251882756588410cb14a40442d661d0230ab992538832e54548318fd91508cad5610ca309b189544c6d7654c4318f592534829e640ca30cb553210865e6394410cb548421032d5408310d3d4e20483675448421d554d41107c43088210ae98351102b5
  | 4 => 0xb98a53442ac6448020ad99052043a84008310bc983530423e6494a309d185500cbc52108630a758c4210275650c810bc18142043645188120c755030c42ce6395220979825310b4d5354b40ba983530823d64d4f10ae983519025d631531097d8d54482766115330d354d210863d64d4b109b18950d065d6315121ab98a51902d563c82108f59053c42b46150040b6181210c3675214530d5d4630482b56114840add91200426d6294410d394d52c434e524ca30b958740882776155110e9508420425e6395120bc18132042e56114c20b3588540c25e6094c21bc98353842d661cc030cbd52204426d6295130d9548210439a6010030b958b408433754952108f19152443c5320c8109718153086d76348010f8980208426c6254231cd146404823d6414c21c7553320ca6c6255110ad587401038c408c0209d19541486d46350010f14c832842e462440109d98754cc2e66294e1097994304432e5250a40a7992518c2d6600c0108f99253443374254442bc980548423e6414c10e990220042cc6348020c554d411066e6294e40b9d95210869e640c6309dd85508ca756510e10cdd0d5110e5e63153209b98853c425f6354241b3d89400c26f62551109b588530434f528c130ab988439029e640c830e54c4319025c6550d319758c540829e60100309b588540c72f54d4930e950a5110a6f654c0209b19532486f260148109b594318834e500c020b3d95320cb355494432d5d46518c31e5454f20d98c9510cbe040080109d98653902e56110e209dd9541106d561cc2308fd9150087c83008310d554630c82e66088010a7590210c2ce6214430d314c524423c6454d21d955121086756115320e6100300423e6414f10add91208427561d5320b5584320c3954110630cd50d5110e6e650c620cb150524429e64cc230b3d8d40082e56195220f14c4318827761543428f596540c65e6394a40e350d5210f2d5494b30e950842842b7644c010c7d50438c2e6620c4109d59720042ae64cc0209b181520c63d6595032cd14440483d03008010a758e51902e762440108f994321027b6548020b5d8d208434e5354b40d394830c426c6550932ab990310825f6354221f494230042e561c80208f992534823e6510130f4980300425d6510830cb952520c63e6414532d914a104431c548c110e9102200425f6354042bc980540433454505219718d500867565108109ed81544c65e6314c21b5984428c2e56294e10e990220843a54110420e54c43110356514c63097d8d54442db60504308f99052c42766114c21b5185400c23f64540318f59252082756194e20a7982400c2eb6050c20b9984420834f5314910ae980531035753d4540cb15020443665254740ae98051103d3400c0109b594410823e65901108f99353c834c5308110d314f52443e03008
  | 5 => 0x53843553254432cb95220c43375484110c754d4210a746154243b9d85308829e64cc030cbd50524c25d6314b10b998843042ae6408620b5185434c6766194e209b189534431e5310320f1949310c6cd638c832c9551210866f6255130cd94640cc2f260d5210a798f401032c52509419798c54c426d6294d10ab99251883365110330cbd50428831c540c110d354c20c42b56414c108f59053c872e5494b1097994218c2776154032d9d48515032f5290140ae181211023e6414810971815310ace6215030a7593308c2d56314810b9986548829d64946309d98653482ea60d4620b358b308c2e56295210a798c42102d661108308f99253882766114f20ea980408823e6515120ab592538831f5414d20b3588418c2e661cc220f14ca510cb2d5350842ab5924210b555114430b9d85200832d5494b10cd55251c83375110130c754f41107d2500c010b9987408825c6355120ab18940103645214540b5d85300c2ce62d0230b5987400c398400c3209718d5010756518c320d6982500c275650c410cbd52548836532544329b58b54c42d561cc0309758c540425e6314941b998a548434d5354b10d5940300423c60550219799453482b5610c8409798c54886776154d20b558e54842ad64086209b58a548c2f26014a10ab990328833654544328f990534866d6294e10b5984328c3565354740cd150514c26e6294910ad584329031c54d4d20b6980510c2ad64cc0208fd95401034d53c8421cb942400823e6095021b9988438431c548c1309b98854c432e5450a209d58753c834d5350842add9541107555354720b9584328829d6310a40b6983510c2cd6310a209b9885150e6d6214d419d994320426f6254d10b998454082d56394a10ad98740102d563c80109d994430438d4310c20d554e21086ad6214c40a798c521029e6414830ae983539032e5290310b6980528c366529444397980534426e6510c20c715230482d66110c308fd954310ee6610c820b558c54042ea60d5020f00c020042e4624c5219798e54842ad6294e40b998720083b040080109bd8950d06e562d0010ad185425071d544c4319758e544425e6508430a7990210c3b040cc010cb55054083e26008010cd146405025d6510630b918540882cd63084209d98754c831d5310c408f994544c32d5454831c550d5110e5d6510c30b358a518c38e408c020ab19130082b561d024097594428c2ce6210630b398c410834e5308310c795030c826c62540439e181534866e6214c21c795030c4335544842197996304825f6550c43b5181310c66c60149109b994524434c534c820cb94040082746155130cbd4a529023d6508640d354d521074d524c4318f593530867b6055121bcd81420427661152328f594311033754d4520cb94840c435753d4520cb55042082cc62500309
  | 6 => 0xae561c8220ab990318826d62d4f10c795253c826f654c832c714e404425c6014d109758c540869d63d0240cb151424cab661148409b98854cc66f6254331b9d85400826d6510620ab993308827561952209dd8550cca6e6295210e9504418826e62150329718d544425f6354321ad984429034c5388110b998b10043b26010210cd552310c6b46050441e3900300825d6395210e350e5210f453254432e610030c4335519033097d95400c32f5210130a7590318c2e561108209d594328423f6454221d99095110bb250900109e181544c6cd63d02209d1855010ab564086109b98a544425e6094c41ad98240042e762502109718d509063d6414c209758e52843575314540cb15220442af6550842cd94240042ce62104309b58b54cc3355110320b358c41082b6640ca10e3551320cae66110a208f590530429f63500409798f52c4365528c431a71814310e5e6315321d554e5110ae561cc2209b98b5050ecd63150209dd95310c71d5410c309758c52042d561148308f19150ccbe25088010c7d4e404427661d41438f59350486746550531f18c020043954354443ad99252843c521084309e181544875453145208fd9152442cd6210e30ad984431025d6394620c755230c831c53101109b98a544c3b0400c0109d586528c38e5350842b318d424cb665088010b558c428434f53881109b58854cc63d64d41328fd91534829d640ca30add91100434c524c931c7553310c757544c4318f191508871e5390320b358b300c25d6395120a758f40102766115032ab59031083645214530c7d50534432d544c832d954a41106b66110e40b398c21082ad640c820d594e51d031c5450c30a798f409032d5494831b398c42883365450610b998b108425d63948209d99432843555394720d3d95320ca3f6454331ec94040042d4614c9318f59432102b56110e40c7151434cb35511033097181531073650100109798f5408757510c1209b58a51902756195230a798c42902ad64c8020b3588318c2eb604c420d554430c834d52cc431cb15142083d0400c0109dd8550d0ece62cc230b9984438836521940218f99640482d661952308f181540ca6e62152319d5875050a756194a40e310030082ce63c82209798e518825f63540219d984540c34d5314c20da98250083c5324c521cb55220c42f06050c10b3d89300c3555354740b6983540c2766194a30cdd46404c31f53101109d9845350aae6214c409d587504cb4c528c130ad98740902ae64c82209798f50506d6608c0108fd91534867561150309d58653903c630082109ed95300c26d62951208f59421103a04008010b398c51082766510e10e5951310c6ce63d022097994428c23e64d4b10c7d53534423e6508640a7990310c25d63d41419758c54887954110430abd89401023e60950319b98a
  | 7 => 0x80040c8070020100000e01412c0089c0060140b0020020240200027e030150000160940606e0480300402b00002c2708c11400c520000000001580001401c1903e0021240282e3400240407b0120000880600a018350010100306a8000040000701f02e1200681f0300402780d0020000980d0060940600b0701940381a0705a805354024018040000002a00607304e0201480001803000074000018160eb0200e41e0000000340700003802c020020080782e01e01004c098020001040100800807800030004060000110360000580c002098300050200001780700a0480001500802c0a82804e0280882300600005001176038040010420180a03c0180180e2190081f00000100200c1802f00810c0f8020a80003f01a0080100a01200e024000016fa1c40581603801c0381000405c3b0880460044200200002c69029038298000110180180000300606c0401f0024800081500c0100102a0261380001400c0081b00002c674018010180100280f0020040c01a0000681400b0140000381218a0280181700201801000000000260070040e814008100da81681d0060a8100010000fc00803014034000e1016010a680008a7602380006a0680600000611c000097c8024000010140000983802001801859002004000002280100000e01c0ac018320020780f00100e0bc238010000140381e5a00580988b00400006002012060e58d400013ad663c8210b398b400c23c60550319d59442842756195110d9549310c7675194620b3588410c35653944429d59730042ce600c020ad99320842ce620c6308f990530874f528c1108f592528c2d663d0210d314e20483a54254442d554d21087b26010010cdd4640482af644c0209b58854c42ae6210440d5551310c78c408c2209718d544874e43548439d98454cca5e6314b10d5d4c318423e6515110ab1814210a6e65881109d586544829d64cc030b318d40082f26014e109b98b54cc26e62d5031ae980539026e6094831cbd954210b2d5250441b5d85408c2756114d42b598c4284395435053197d95320ca5d6510430ad98040043ca600c020b9d89400431c540c120cd54640c826e6508110ad993108426e6294640d9d46204825f6354910ab588511035453d4540ad990320429e6494a309798f54c42b66408610cdd4440482e66214c10d354a30c426f6254043b918940842b564c4210d354c32082766115132d554e51d034f53d49409dd9530042746054432cb54840cc26d6295210c7951438c32c5450a32b998020043345414520ad59021042756508410c714c404825c63549108fd9150ccacf6350220d954d210866d6294e40d594430c82b66110840b5584428c2766114c20cd151418c65f6354041bc98352843cb400c020b558c420427561d4143b9185324863e64d4131b3181320c
  | 8 => 0x2e804056000090000000200d80000a0400b0050060c41e80000c0040d8240c40540391705a12c2e80007000402002198004000470441f03e00700a0040200802232429004408010010440240182c00d03c04c0301a018030041370040f40e0250061182d002010041a380000007c9080700691402805002038028000021040800015801c3080103e008798010000400a039162ecc2981c00005c008ef01e0001500300603c02805004064090000000003020b014028028070000000002f008090020000100000a0010180ac1280600a044060130100001000800800c128007f802007800076a540880000a3b41f88201a024150000040300881200401403007002028008150602c80b8
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1952571151424cb0aa18c0a88879158f5208610d44c4206600849870590210c292382a4a08838354c6050842a18e0a1aa421f05544ca510ca8aba0a698a43515d65348421a50e0a14a0216156454c3104286382a899065895486050441a90e0994a01961554181310c70b32a8220c61315c46350932c4ac8a9042084d07058c4204254382c818841321c16310420a2ae62a28290d4571949328c3c02046010021914c86054432a60e0a0ca020e25655044108286ba0a699243899954210a10c1a86302a421d2571151428ca92b94a2a0c81511c1524c431a2ae928a631849574185324c64ab98c2a1283515c6534ca20a30e0a1ca021e854358443082e138e8018041515c8534c410c8aa6b086410625541812108782a9ca4a088389d516210610a8ae7292430860e65508428c2e03824210861515c7544c832d0ac4a0883186146550d414c722b1ea529421a15096110a3094ae430a86a0e0d5458c42082e13846010021895935208610c2aa63028220d9070504410c292b88a8a1041495d65448421a1aeb2a2641960f5358a5390342b226419021455cc545062194ae83126290e25545884104342992c219481641c1310c440c8aca988621064665484218c306b2a8421061c154d4254442c1ea8b14a9185447054d21087832a2a69084391595320c810a2ae329a872070a540c020c4342b1a4210881a1589310c440c2cca9886320625625445110268382c221061895496114840a8ae229a641050d7215143cc72332a6419421581c12194021c1aa8b10a81852574d4d210868a382a6a0883435ce5250a40a4ae52a2830861563d465190312a10c0a8885e01003088010a48e0aa24210d1571151430c28ab88a6a1a85859954310e10d44c22066010706535494110706b2a6419081855516310410c4aa8b08841052572151418c68ab9ca8a0c218354d6214c40a1ae82926498d8870508420c2c53848018041895954210810a1ae829a6410685435844388342b22641942185d516310610a1ae629284a0e4753584328828ab8ca8a1c612c1c1640c810c8ac6a88a210592709003004322b1ea328c41c194d4254442a8ae7aa24210e15635444110306aa0c099065435d2534ca20e0aa8a926218f80400c02004306b26a529461839954310e20c2ac9a9ca70854572d51310c6a2b9ca290c41689d33008010d0ac690843204c571189434cb0aaa2c221861a150d6210c1094ae830a6490e85624c4319030632a86a126583d516395220b80e0990640864552584320c292b90a8a0821435d2524ca30c8cca988631061754584438c342b224210c618358d5210840d24c8186400868562504410c342a12c221061c154d5250441e0ca8992a2196475358a53842863aa86a1265855915114430c8ac5a8ca3187125110030c8313aa2c32a441435d0534cb21
  | 1 => 0x402c1c6e0b8ba0014818010a030c82e006880144061902c00060b008000700060280c0d81ca012040100e26008140e960680806c1198382c800112862000106db4043283a14055b0182a010782012160880010070101c0402040040049091b4cf210000802030180c4a1209840000900000020513a0002310304c03835516315020930e0b18422062465509414870aa9ac2218818958b51946409c0e0b08861060d64548520c262b98c4a0a4383995320ca40c2ac6a88a220685635084204306aa2c421861c150d5254443f008018041086456354852042c43828621841681c14110420c2aa8b08a818782400c02004306b22a619041435c85450d31e0aa929a4210e85435884384270382c421821455cc5450410a28e0aa26218ca8705883110313aa2c52a42191589510c430a2ae929a6308645635442108382aa2a69084391d496194a30e14a6200418860f54588438c30aa9ac22988191195324c521e0aa6a14a2216256548421102e139e8010021899952108640c4ac8a88a21052571949429028aba0a698c43681c14210810a8ae6292420852571951428828a38286a888785591510c430b10e099064205457294d3184385290801862185d516395210b20e0a188608685644c4310828ab88a8a1e6589d516110a20d0ac6a108508617535865390307aa2c621441435ca5350e40a8ae528a63185a0704842110286382a6a1085855954310c1094ae231286a162564d465188292ba4a290c4191d4d6194e20c8aa6b08a61064562544510c382a1ca4a8887435ca5450e30960e0b086420625545885404342b1a8220841835915314c20a48e0a12a2214c870588410c30ab2a6218881511d5324c521b44e1200400851571151434ca86b98a8a1643895895110440a48eaa128290e2752586529030baa2c32a461895915214810a2ae728a832062564d4a5284322b2a4210861835954310c2098ae630a8490e47535883184312aa2c22a041435ce5450a20d0ac89084218685325843210306b26a619441455d6544c431d0ac8988631050d731514208292ba4a490c21855954110430c1aa6b1086206156454c5304262b90c6a0a63541c13194031c2ac9a8ca3187054354a5110f12a92c221081a498c40c8010a88e0992a21961564d4c3184306b1aa4290819158d5208410a4ae8292420870554949310c68a3aa86a0a63455d0534c410c4ac8a88421050d72151430c342b1a8220c41315c86150d31a1ae429a86a0d0d731514248706b22a419061c1951524c431b84e5a006008645531812108706b26a729c41915496114830c8aa6b10a6086455358831042e03826218841855516315010a4ae42a28298e4552181310c706b1ea529481899954110620e0aa8992a2
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x358170028040000b0021022400401c0001001c81631c14110420a808058d2108440a808058d4210810a80805096110830a808050d6210c10a0880550604c832a808050d6110c20c81621c14110430a108050c6054443a80805912108430c81641c12108430c81421c16110830a8080589310c440a20805486050441c81321c1610c840a8080591320c810c81641c1320c810a8080591310c420c81431c16110c20a1080550604c431a808058d4110420a088054c6050842c81641c1310c420a20805506048421a80805894110430a408054c6048421a40804c86054432a4080548604c431a80804c9610c840c81631c12108440a088050c6054843a108054c6050441c81621c1310c440c81631c14210810a20805086054442c81431c16210c10
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1062
  | 4 => 1615
  | 3 => 309
  | 2 => 36
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
  | 6 => 2*((h/51+packedAt s1K6 (768+(h % 51)*6) 6) % 48)
  | 5 => 2*((h/403+packedAt s1K5 (28674+(h % 403)*11) 11) % 1062)
  | 4 => 2*((h/573+packedAt s1K4 (61370+(h % 573)*11) 11) % 1615)
  | 3 => 2*((h/110+packedAt s1K3 (15141+(h % 110)*9) 9) % 309)
  | 2 => 2*((h/26+packedAt s1K2 (2160+(h % 26)*6) 6) % 36)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xf807f00fffe01ffffe03f83f83ffc1ffd11e3f
  | 3 => 0x7fff00fffe01ffffc003ffc1ffe0fe1e3c7
  | 4 => 0xfff800000fffffe01fffffc0001ffff07e03f8
  | 5 => 0xfffffffff00000001fffffffffe000007ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x83010a0a0224242402c58458422c210866cdb
  | 2 => 0x5552aa694651d4948f02aa2aa35551ad51162d
  | 3 => 0x46a4c94a6a9491d9175604336919b48e61a346
  | 4 => 0x64c68d8d8d191911db9b36a0421e39c47a03b0
  | 5 => 0x87070e0e0e1e1e1e1de3c73c739021087dd800
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0a000aaaaaaa0aaa0a000aaaaaaa0aaa0a000aaaaaaa0aaa0a000aaaaaaa0aaa0a000aaaaaaa0aaa0a000aaaaaaa0aaa0a000aaaaaaa0aaa0a000, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa0010200a01d14f0030482c000e3c44c0fd42fc31fe43ff41ff42ff31ff10fd41ff21ff20fe40be40fe30fd40fd30fe21fe42fe20fc41fc30de30fd32fc43fd21fc21fc32fd43f421fd31fc40bc40dc30fc10ff40fd10f721fe32fc20fe31fe10fe41ff43fc42ff32fd20ff30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x5c3800802a020224001452c00001128845e69e80000009c140c00108201b3100048d10e818084000003a0400100000111e000000a08401040057c54021bd280437b5050f3080185d14520ec180413e54086eca3994f94040eda00615c53502eca2204f15130db90881b421902f6a0997594430aea9e417651d0a7aa918f554430ae29a85785050abca7905e94241db90c817551cca7ca1206e10320cea18875d53906bca610cf55310b629221b8400c2dea4885714d209f2a4637a508c6e8a2a14fd5130bda828577514caf0a0a1ee940409faa221d4218c2bea6884fd5132f210c413d54c82bea6905e54231bc28265e421082baa610ee10330eb29843d4210c3aaa610f5c84309f2a661b8404436aa2205d54742daaa0437551102baa7a04f95032aea9e2176510c2eca410ddd4520af298855e508c2eea2a1760c320dc204219c400c37080107994821eb90c61f2500873c801857940309eaa0435e53d02eaa3105794f10ec2006176518836ca2204f55032db2a0439c408c2eaa21876940309faa2413e54c42f2a120d754c429eaa66174514cabea6a04f15110ae29a219e408c2eca310cf151329e2a2417950086bea6a14f95320ec18221d8308436842205794e41
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x40806b0006768424e4c84400c31a540c320c614c40443315110030ca14840442986050c43d454d50087a02110020961815310b18540c110a6982400c2d16110030e4944400c3c0210c0208e181540cb926110030e4084400c3315454021d2148304425565084308d594211031a5310320e4584400c3915110030
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x4000922ed288801849176084400c288ba84220061445d66110030
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s2K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/67+packedAt s2K4 (3159+(h % 67)*7) 7) % 117)
  | 3 => 2*((h/15+packedAt s2K3 (912+(h % 15)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s2K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xff01fff01fff01e0ffffff03ff03ff007f9e7c
  | 1 => 0x7ffe07ffe07fffff03f01ffc1ffc1fffb8e38f
  | 3 => 0x7ffffffffffffffffc001fffffffffffc0ffff
  | 4 => 0x800007ffff8001ffffffe0001fffe001ff03f0
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x94c3111c5122a602cb2a7212721390c1b8e3c
  | 1 => 0x2a149322432468e50156896509651a54b8a285
  | 3 => 0x442844448848810a5408128a528a44a940555a
  | 4 => 0x68b16689120ecdb39a6cc0c21cf38831ed03e0
  | 5 => 0x70c1870e1c70f1dce38f1cf380c210c1f6f800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaee00ee00cc00eeaaee00ee00cc00eeaaee00ee00cc00eeaaee00ee00cc00eeaaee00ee00cc00eeaaee00ee00cc00eeaaee00ee00cc00eeaaee00ee00cc00, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x800a210101a045102040383584285098fd31de30fc32fc43fc42fc10fe42f421bc40ff40fc40fd20fc31fe31dc30fe10fe41fd10fd42ff42ff21fe20ff30fc20ff43fd43ff41fe21ff31fe32ff10fd40fe40be40ff20fe30fd30f721fc21fe43fc30fc41ff32fd21fd41fd32
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x288400005c60002181095000000c400100aa04d09a730d010400580541801a0a00280003c080021838000306900020ca40b240000004100460835714d40cea18875c5350baaa2184f15132afa9a413e540cbb060104f94240ae29a4177514827ca9905754e41db288817a50906eca310f5c8430dc200613e548c67ca0206d950219faa2617651d0b74a0207c94021bc282873f54442bca6215ed4142ba28a65b421902eca31075c8630bd28043785050a7ea8996e10330afa9a213d54c82eea2995e94231ba28a415e530867ca9986e10110bda8265b551102eea2a15d54440aea9e817651ccabca1186790230aea9e213f54482bea6a14f55231ce20061b840842baa6215d94430db90881745150af2a010db14910f210c419c408c3b061905d94821af29e21d8400c2eaa2184f15110cf200615e500c3a842185d54732f8a80435d53c82f2a120cf95310dc20041d653086f0a09957d4d40ed280615c534427aa9985754c219eaa065d4218c2bca7905d54742ec18221b7219027ca810ed55021eaa984398400c2eca2204f55310b7a9221d830842eaa3104f15120bda82875e53907b680187908420bca84633c544c2bca7a06e10320f3290433d54087aca2186d08440
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x4000d421000004802018060cc55150087285210110c614c40442586054c42d454d50086356508440e4944400c3902110030f008430083926110030d2148304429a6090030c6150304431a540c32095594210c2986050c43c694c40c833151100308e181540cb932110030e4584400c2d16110030e4544400c3a02110020
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x20922ed288801851175984400c288ba84220061245d82110030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => 2*((h/22+packedAt s3K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/67+packedAt s3K4 (3159+(h % 67)*7) 7) % 117)
  | 3 => 2*((h/22+packedAt s3K3 (912+(h % 22)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s3K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xff01fff01fff01e0ffffff03ff03ff007f9e7c
  | 1 => 0x7ffe07ffe07fffff03f01ffc1ffc1fffb8e38f
  | 2 => 0x7ffffffffffffffffc001fffffffffffc0ffff
  | 4 => 0x800007ffff8001ffffffe0001fffe001ff03f0
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x94c3111c5122a602cb2a7212721390c1b8e3c
  | 1 => 0x2a149322432468e50156896509651a54b8a285
  | 2 => 0x442844448848810a5408128a528a44a940555a
  | 4 => 0x68b16689120ecdb39a6cc0c21cf38831ed03e0
  | 5 => 0x70c1870e1c70f1dce38f1cf380c210c1f6f800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0e0e0c0c0eaeae0e0e0e0c0c0eaeae0e0e0e0c0c0eaeae0e0e0e0c0c0eaeae0e0e0e0c0c0eaeae0e0e0e0c0c0eaeae0e0e0e0c0c0eaeae0e0e0e0c0c0, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x480f910be40fa10bc40bf41bd41
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x26aa2206c50510
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
  | 3 => 2*((h/1+packedAt s4K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3ffc07ff07e0c3ff83ff07fc3fc0f019e77cc
  | 1 => 0xfc0fff83ffffffc0ffc1ff83fc3ffffee388ff
  | 2 => 0xfffffffc007fffff0001ffffffc00fff03ff0f
  | 3 => 0xfffffff800ffffffe0003fffff003fc0ff0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x58644718a494940b3a127425c06469188e33cc
  | 1 => 0x9248909042084804a5094a044292a48a28055
  | 2 => 0x30891220694909550421294aaa8084b3015d0a
  | 3 => 0xa2ca2442480d2a6694a408433312c023540ea0
  | 5 => 0xc30c38738e71cfb8e739ce70222308c3fbe000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeee0eee0ecc0ecc0eee0eee0ecc0ecc0eee0eee0ecc0ecc0eee0eee0ecc0ecc0eee0eee0ecc0ecc0eee0eee0ecc0ecc0eee0eee0ecc0ecc0eee0eee0ecc0ecc0, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x8000fa10bd41bf41bc40be40f910
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x76282884d54440
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
  | 5 => 2*((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/9+packedAt s5K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/7+packedAt s5K3 (54+(h % 7)*1) 1) % 2)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3ffc07ff07e0c3ff83ff07fc3fc0f019e77cc
  | 1 => 0xfc0fff83ffffffc0ffc1ff83fc3ffffee388ff
  | 2 => 0xfffffffc007fffff0001ffffffc00fff03ff0f
  | 3 => 0xfffffff800ffffffe0003fffff003fc0ff0
  | 4 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x58644718a494940b3a127425c06469188e33cc
  | 1 => 0x9248909042084804a5094a044292a48a28055
  | 2 => 0x30891220694909550421294aaa8084b3015d0a
  | 3 => 0xa2ca2442480d2a6694a408433312c023540ea0
  | 4 => 0xc30c38738e71cfb8e739ce70222308c3fbe000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0eee0ecc0, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q4K3 : Nat → Nat
  | 0 => 0xcd32
  | _ => 0
def q4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def q4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q4K4 (i*5) 5
  | 3 => packedAt q4K3 (i*16) 16
  | _ => 0
def q4I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q4K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt q4K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def q4Pos : Nat → Bits
  | 0 => 0xc3fffe0ff0ff0f87e1fc3fff0fe0fe0f49f673
  | 1 => 0xfc1c3ff0ff0ff0f8fe1fc383f0ff0ff0b6cb9c
  | 2 => 0xffe03fff000fffff001ffc03ff000fffc70c1f
  | 3 => 0x3ffffff000ffffe00003fffff000f80fe0
  | 5 => 0xffffc000000000fffffffffc00000000fff000
  | _ => 0
def q4Neg : Nat → Bits
  | 0 => 0x48400222010010002024048901222222005231
  | 1 => 0x8940446240140110620c4119104a24a212c294
  | 2 => 0x108aa8842aaa88ab1112a822aa04494cc50c0a
  | 3 => 0x32933108a882aacd95422042cc94c044e80d40
  | 5 => 0x231a21ccccccccf6d99b327088188188ffa000
  | _ => 0
def q4Atlas : Atlas := ⟨4,rawDecor 47 q4Pos q4Neg, 0xeeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0, q4N, q4R, (fun _ _ => 0), q4I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q6K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0xcd32
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def q6R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q6K4 (i*5) 5
  | 3 => packedAt q6K3 (i*16) 16
  | _ => 0
def q6I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q6K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt q6K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def q6Pos : Nat → Bits
  | 0 => 0xc3fffe0ff0ff0f87e1fc3fff0fe0fe0f49f673
  | 1 => 0xfc1c3ff0ff0ff0f8fe1fc383f0ff0ff0b6cb9c
  | 2 => 0xffe03fff000fffff001ffc03ff000fffc70c1f
  | 3 => 0x3ffffff000ffffe00003fffff000f80fe0
  | 4 => 0xffffc000000000fffffffffc00000000fff000
  | _ => 0
def q6Neg : Nat → Bits
  | 0 => 0x48400222010010002024048901222222005231
  | 1 => 0x8940446240140110620c4119104a24a212c294
  | 2 => 0x108aa8842aaa88ab1112a822aa04494cc50c0a
  | 3 => 0x32933108a882aacd95422042cc94c044e80d40
  | 4 => 0x231a21ccccccccf6d99b327088188188ffa000
  | _ => 0
def q6Atlas : Atlas := ⟨4,rawDecor 31 q6Pos q6Neg, 0xeeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q7K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x4000003d107b10f021e8c3c987920
  | _ => 0
def q7K2 : Nat → Nat
  | 0 => 0xca942042650c10a9428c2650e20
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q7R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q7K4 (i*4) 4
  | 3 => packedAt q7K3 (i*15) 15
  | 2 => packedAt q7K2 (i*26) 26
  | _ => 0
def q7I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q7K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q7K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q7K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q7Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdaf1333c71ce7c93
  | 3 => 0xffffffffffffffffffffffeffe3fff81fff0ff
  | 4 => 0x73ffc3cffe0f8f1c
  | 5 => 0x7cfffc0ffff00fe0
  | _ => 0
def q7Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa51c664c1c636c91
  | 3 => 0x1020800080840026
  | 4 => 0xc44281524092518
  | 5 => 0x38802aa49204ac0
  | _ => 0
def q7Atlas : Atlas := ⟨4,rawDecor 58 q7Pos q7Neg, 0xffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x4fc987810f621e483d187a20
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x2000000a9428c2650e209943042a50810
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q8R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q8K4 (i*4) 4
  | 3 => packedAt q8K3 (i*15) 15
  | 2 => packedAt q8K2 (i*26) 26
  | _ => 0
def q8I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q8K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q8K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/22+packedAt q8K2 (104+(h % 22)*2) 2) % 4)
  | _ => 0
def q8Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdaf1333c71ce7c93
  | 2 => 0xffffffffffffffffffffffeffe3fff81fff0ff
  | 4 => 0x73ffc3cffe0f8f1c
  | 5 => 0x7cfffc0ffff00fe0
  | _ => 0
def q8Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa51c664c1c636c91
  | 2 => 0x1020800080840026
  | 4 => 0xc44281524092518
  | 5 => 0x38802aa49204ac0
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 54 q8Pos q8Neg, 0xfffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x10007930be6164c3d185d30
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x2650e30
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q9R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q9K4 (i*4) 4
  | 3 => packedAt q9K3 (i*15) 15
  | 2 => packedAt q9K2 (i*26) 26
  | _ => 0
def q9I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q9K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q9K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q9K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q9Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbbc933e39cef90f
  | 2 => 0xfffffffffffffffffffffffdff1fcfc1ff31f3
  | 3 => 0xeffe3f3fe0fce3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q9Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff44626420c62a905
  | 2 => 0x208401040840052
  | 3 => 0x110080490080228
  | 5 => 0xe202ab2520ad80
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 46 q9Pos q9Neg, 0xfff0fff0fcc0fcc0fff0fff0fcc0fcc0fff0fff0fcc0fcc0fff0fff0fcc0fcc0fff0fff0fcc0fcc0fff0fff0fcc0fcc0fff0fff0fcc0fcc0fff0fff0fcc0fcc0, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x200dd30f26164c2f987a30
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x2650e30
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q10R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q10K4 (i*4) 4
  | 3 => packedAt q10K3 (i*15) 15
  | 2 => packedAt q10K2 (i*26) 26
  | _ => 0
def q10I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q10K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q10K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q10K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q10Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbbc933e39cef90f
  | 2 => 0xfffffffffffffffffffffffdff1fcfc1ff31f3
  | 3 => 0xeffe3f3fe0fce3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q10Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff44626420c62a905
  | 2 => 0x208401040840052
  | 3 => 0x110080490080228
  | 4 => 0xe202ab2520ad80
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 30 q10Pos q10Neg, 0xfff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x400177105e30d84170c3b087410
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x320c020e02004340c010
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q11R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q11K4 (i*4) 4
  | 3 => packedAt q11K3 (i*15) 15
  | 2 => packedAt q11K2 (i*26) 26
  | _ => 0
def q11I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q11K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q11K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q11K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q11Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 4 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 3 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 4 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 57 q11Pos q11Neg, 0xaaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q12K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x30003b085e30d84170c37107410
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x200340c010c830083808010
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q12R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q12K4 (i*4) 4
  | 3 => packedAt q12K3 (i*15) 15
  | 2 => packedAt q12K2 (i*26) 26
  | _ => 0
def q12I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q12K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q12K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q12K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q12Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 4 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q12Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 4 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q12Atlas : Atlas := ⟨4,rawDecor 53 q12Pos q12Neg, 0xaaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000aaaaa0a0a0a00000, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q13K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x100023b087410bc6170c37106c20
  | _ => 0
def q13K2 : Nat → Nat
  | 0 => 0x83808010c83008340c010
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q13R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q13K4 (i*4) 4
  | 3 => packedAt q13K3 (i*15) 15
  | 2 => packedAt q13K2 (i*26) 26
  | _ => 0
def q13I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q13K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q13K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q13K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q13Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q13Atlas : Atlas := ⟨4,rawDecor 45 q13Pos q13Neg, 0xaaa0aaa0a000a000aaa0aaa0a000a000aaa0aaa0a000a000aaa0aaa0a000a000aaa0aaa0a000a000aaa0aaa0a000a000aaa0aaa0a000a000aaa0aaa0a000a000, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x4023b085c30dc41b082f187410
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x400320c020e02004340c010
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q14R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q14K4 (i*4) 4
  | 3 => packedAt q14K3 (i*15) 15
  | 2 => packedAt q14K2 (i*26) 26
  | _ => 0
def q14I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q14K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q14K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q14K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 3 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 4 => 0xefff0fffc3f8
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 3 => 0x244e89aa3346
  | 4 => 0x1888ee3323b0
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 29 q14Pos q14Neg, 0xaaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000aaa0a000, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q15K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q15R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q15K3 (i*4) 4
  | _ => 0
def q15I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q15K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xdbf19f3f1c3f8d9c
  | 3 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 3 => 0x1101502242244a0a
  | 5 => 0xe091ab493064f40
  | _ => 0
def q15Atlas : Atlas := ⟨3,rawDecor 43 q15Pos q15Neg, 0xeeaaeeaaee00ee00eeaaeeaaee00ee00eeaaeeaaee00ee00eeaaeeaaee00ee00eeaaeeaaee00ee00eeaaeeaaee00ee00eeaaeeaaee00ee00eeaaeeaaee00ee00, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q16K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q16R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q16K3 (i*4) 4
  | _ => 0
def q16I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q16K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q16Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xdbf19f3f1c3f8d9c
  | 3 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q16Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 3 => 0x1101502242244a0a
  | 4 => 0xe091ab493064f40
  | _ => 0
def q16Atlas : Atlas := ⟨3,rawDecor 27 q16Pos q16Neg, 0xeeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00eeaaee00, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q17K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q17R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q17K3 (i*4) 4
  | _ => 0
def q17I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q17K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xdbf19f3f1c3f8d9c
  | 2 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 2 => 0x1101502242244a0a
  | 5 => 0xe091ab493064f40
  | _ => 0
def q17Atlas : Atlas := ⟨3,rawDecor 39 q17Pos q17Neg, 0xeaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0eaeaeaeae0e0e0e0, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q18K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q18R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q18K3 (i*4) 4
  | _ => 0
def q18I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt q18K3 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def q18Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xdbf19f3f1c3f8d9c
  | 2 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def q18Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff40640108248920b1
  | 1 => 0x24ac285909932594
  | 2 => 0x1101502242244a0a
  | 4 => 0xe091ab493064f40
  | _ => 0
def q18Atlas : Atlas := ⟨3,rawDecor 23 q18Pos q18Neg, 0xeaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0eaeae0e0, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x4020803c187a10f041ecc3d907910
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x809843442a10910aa42cc2690f20
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q19R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q19K4 (i*4) 4
  | 3 => packedAt q19K3 (i*15) 15
  | 2 => packedAt q19K2 (i*26) 26
  | _ => 0
def q19I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q19K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q19K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/15+packedAt q19K2 (104+(h % 15)*2) 2) % 4)
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0x5af0f9cf1f8707cc
  | 1 => 0xffffffffffffffffffffffefff3fffe3fff8ff
  | 2 => 0xfffffffffffffffffffffff3ffc1fffc07ff0f
  | 3 => 0x7cfffe0ffff80ff0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0x251e929704b163cc
  | 1 => 0xffffffffffffffffffffff9022800121122055
  | 2 => 0xc44350a4844cd0a
  | 3 => 0x38821ac92608ea0
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 15 q19Pos q19Neg, 0xecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xc0030403024609800300004500e00040000c400008000001fe50005f94001fe40006f90001fd30005f14001fd20007f14001fd53007f4c801fd54007fd0c01fc54007fd0801ff53007fd4801ff50007f95001fd40007f8c001fd50007f88001ff54007f10001ff40006f10001fd52007f50c01fd42
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xca000af19130006fa6428002fd63d48017eb1e8400bf58c40007fecaa100bfa108800dde0848009df906500077aa8a1843fc3215001bea90a000ef50a400377a4320002fd654c809ef18c6000ff1913205ffc2099003bd42100017fb2c4000bf58f540076ac220047ff321501ffea0aa600cf94240005fac5a9827fd419401bff082a400ff1815302f742020003fd544c80dfea8c8005ef48440004fccba0003ed524c813bea8ca000dfd51520077ec520002fd63140017fb2c6000bfd9543005fac899003bd4350801beaa2a600df4ca50007eec299002ff6590025fe98aa800ff18152007da8499003bd6210001bab08a00cef505420067ca0200037d5294001fea1c400cff4c5420077a872000ffa104c017ffa0a640eff545430077a862003bff6150c01dea9c8000ff54e20075fac2a1803fe644c819dfa0a8402ff506200377a832000aff61880013fb2a8000bd58440046fc2028003fd548c009fd0846000ff4ca4004cfcc028003fd321000f7fb0a8000de98050005fec8a9802ff63508019faa4a804bfd863000578c8a8003fd5290001dea988000df58c500777a82a181bbf6190013fe90ca009df4c650007f8c0a1002ff64880017eb168602ff54620006faa7a9003dd434c801dd3008006ff4c64005ffa829904bfe1055001fe32a6406ef54640007fac899032ff615081dff08286009f19530007baa699002bc644801bfea0aa409df8c6500377c4320003ff544c801bfa9aa400bf588500077ca8a103bbf4150c13fe98ca000df5085002f7aa220003fd428c001fea1aa404ff4863005fe8c299002fc6054811be908a000bf58854046f42028017bd311000bdb3088000bf18153005fac62a033fe1050811bb308a000cf5505406dfec2a90037d43140017eb108012ff4855402f722020003fe654c8013fb2a4000bf1813204efec328002bd64d4001bfb1ca00bff54532035fec320002bf64540017fb2a6409df84250005fac72a003ff6454801dea1e8406ef4c640006fac42800bfd3188001bea98a00dffd8552046f2202803fff6154c01fe3026400bfd9152007fa6428002fd62d500b5f3048009df94650005fac52a003be5450c1fbea8aa600ef4ca40004f8ca900037d4294001beaa4a006ef18640075fec2a18237d4114001bfb14a000ef4c8400357cc020003bd529001f7eb0aa600dfd9250007feca99002fd65508017eb2a8601fe84120007fca899003bd5210005f710c4000dfd5153027fa831801bbe31900017fb2a840fff84153004feca98003ff6550c19ffb0a8400ef55142067faa2a1003fd654c801fe2a26400afd913004ef82128002f7614c801ffb22640bfb485320057cc9a8003fd4294001beaa2a406ff486400077e86a1003bf63900017fb128600afd9120005fec8990033c50900077fb0a6009df48650
  | 1 => 0x8060f85000003b85c145004914121a01010000400810183000000021402000000d0016454046f80002da128880071020000003688b080040080020010026c9e010a00010090800c3005000f4360000000020101808000200970162a6f108469827000a833010858a0003800000600220520e04000a20b01a8800380700000002305c14140000001bea1ca009df18650055fec2a8002f56114017ee98a6408df4c450004facba00027c6550013bf10ca000ff54a30007da65100037d5394009fea8c6012bf585540077ac620003fe604c8177fb0a6400bfd89530377c212003bfd2150c01feaa44000cf14040007faa6a1002fc6050c113f304a000bfd8d5206ffa62a902fff514c801bea9aa40fff48553087fc642a003fc6050c037fb0a4000ef55240007fa6528017be1010017ffb0a6400bfd8e20005fec918003ff6454c17feb0a640ddf5455204dfec32803f7f5154c01dfb2c8000ff54e4006efea2a9032fd615081b7eb0aa40bbf58532007fa872801bbe51900017e3028400f74ca3007dfec2a981bbe4190013bea
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x57199132004fc7654a300057d74d8a50006f73258440005bf744c840005bf7254e40006bf64151321375d314c850006f761181320073f54951320076d524c850004fd76d51320a6df614ca300063d5458c54004ff7358850005bd754ca40004ff7159542005b87054840005ba70d8e400ef3a101424012dbf7150e40004fd71d8e2011dbd7154e400bfb4714c840005dd73d51321aef753d853205fe472d8532005bd7395142006f775d8532004ff7118152007b87054840004fe70d9153007743258450004fd71d95321a6f742d8532006f565d8532006ed624c8501c7e461549320057f754c850006f63258440005b8704c8400067d541815205ef532d8532006f550d85321376d214c850005dc7050d320f7b4714ca40004f870591321e7d46154d320057f7250e50004ff764c840006f764d8532005ec7054932005bf7358840007d7714ca30007787050c50004fd7615132004fd7218143006f540d853209fcd314ca20005f870595320075d534c8500bfba104c840004fe7615132006f76198132005bd75d8e40006bd4118143005f7714c850006f674d8532006fa1018142005bd764c840004f571d8e20005bd744c840006f461595321a6f620d85320073d43508501873d4150e5016d7f714ca50004ff71d8e20015e4714ca20006f570d853217d7f7150a50226bf6150d42004ff71595431773d4150a50025d4714ca30004bf74595320057e75191320076d424ca500c5bd714c8400076d624c85000777714c8500a7cd214ca30207cc32991320057c7054d520067f51d8d52205df7359132004ff71d8d420057f7358850006f671d8e2000577714ca50007b432584400057f73508500d5bd7154840007787050850006f532584500075d434ca50004ff7358854006bf41d8d42006be54d8d42007cd534ca20004f87059542007cd5350932005bf7354840007cd524ca30006f46118132007e7714ca20006fa1018152005bf7258c4010dbd7154a40004fd71d95430073d5415132006f554d85320057f7454e500fdbd714ca40006bd54181430057f7254c500057a70d8e50006f564d8532004fd7218153007ac64509320079c6450d320df3d5154c400063d54588540079d634c840005bd7295143007b932980400073d5354840005ba70d8a40005be7419532006f840181521cdef7154932006bd41181420057f744c8501afd643d853219d7f7154e50006f850181430077532584502367f6154d520b73a1094040085be7695142005ec7050932005bf7354a40215ef7259532004fd73181420cf3d5154840004fd71181430057d71d925015d7f7150c5005fd473d8532004ff7118143004fc7650d52004fe70d9532004fd73181520057d754c850006f474d8532004ff71d8d52006f461d9132005bf7250c40007ad424c8401a6f752d8532
  | 1 => 0xca300067f54d8d520075c6554d32006f454d8532005f7714ca401573d4150c500bf9d314c84018d7f7150e50004ff7258c5009fea104ca20007b732584401577a1050c5000776325845021fcc3299532004ff7159532005dc7054d320057d72d51530079d534ca40005bd71d9640006ed624c84022dbf7150d420057f744ca500067d5318152005f7714c8400057d74d8e500076c65549320057d75191320075f5454d32006bd63588401c7cd31549320067d5418153006f465d8532006f774d85321aef553d85321d79f4150d321aef530d8532004fd71181521e75f5154d32006f574d85321c76f51549320075d434c8500f79d314ca401fdef72591321f7cc32191320043f76550540bfad214c8400067d51181520057a70d8a5014d7f7150850006f765d8532006f475d8532006f53258440006f575d8532006be54d8943004fd71d9230005f8704c8500079d534c8400067f65151321a6f552d853209eef614ca20005dd739513200577714c850006f84018153004fe70d9543007ad524ca401e7cd2154d32005bd75d8a40006f740d85320067f5159532004fd764c8501afd653d853205ef572d85321477a1050850006bf41d8943086ee32588540dfba1054c40035b4714ca400057f7454a5000778704c8501a7e420d8532005bf754ca401473d41508500f7ad214ca40005f77159132006b56258440007b7714c840007b63258440005f57199532004fd7118153004fd71d91530cfba10548400857e76d5152006b542584400067d6519532006fa70d8e200076d424c850004fd71181421d7d46150d32007ae54509320057f7559132004fc7654d42005bf764c840006bd6350840004fd71d9640005bf7350840004fc70595421bdef71509320079e5450d32004f870595430067563584501a7e642d8532004fe7695132007d553d8532006f850181420057d744ca500067d63548500d5bf71548400067f54d89530057d764c850007e552d8532004f771595320067d65d5132006fa1018153004fe70d9132007b7714ca400067f51d8953007d8704ca30007cd424ca301b7af415093220fcc3219532004fc7059132006fa10181430067d63588500057d71d8a5013776614c8500bfb6614c84016d7d714ca50006bf64991320af3a1014040005bf7254c40004fc7654e20006f461d953217d7d7150a50004ff7258c54005bd754c8400057c7559132005f77159532087cc3215132006bd64191321eddf7154d32004fd71d91520078d43509320e5bd7154c40004fd71d9132007cd434ca20006f664d85321aef630d8532004fd71d96301a6f520d853210dbf7154a40006bd4358840005ed72d5132006f43258450004fc7650a3015d7d7150c500057f764c850007e8704ca20004ff7118142006f654d85320067d5118153004ff764c850005f
  | 2 => 0x5000bc270384000230c008000d0001c700e2f0b42e0000010120c27054400c011ec30350480402002480bb4311221016080000cfa081b021462a1182c2200048103c0a4c80088362581800000001000240381400021400018063d02c4c2202850002e07958298b0da2c0001518007c000000ca4c80080000480002802490705cd803019a88cf1008040c002403000000004c0000150207e0a000e8001f0014c142f00010020f0893d7e0c0800800040780036010603800004c8010e01019b4021a070a00e000580808001342000fe0001006000b0649c291173d5154e40006f770d8532006f461981320073d5354a40006dd634c850005bf74595321a6f542d8532005bd7419532004ff711815313774714c8501675d314ca50004ff7358840005dd7315132004fe76d5132007ad624c8401dddf7150d32004fd7695132007793298050005787050c500076f54549321073d5154a40007cd4354932006f470d8532007e542d853221ddf73595320067f659953204d74714ca50004fd764c8401a7c432d8532005bd71d8a400057d71d8e500a7d4714ca30004ff71d8943005f8704c840004fe70d9152005bf7550e40004ff7118132006bd5418142004fd7118132005ed7215132006f750d85320c5bf714c8401b7cd3150932006f760d85320073d4350a50005bc74595321aef543d853200777714ca5008d7e76d51531676d214ca501d7cd2150d320075d634c850006f46159132004ff7159132005f7714ca50004fe70d9542005bc7050d42007b53258440006f73258450006f665d8532004ff71d89530057f7250c50005f57198132005b7714c84000578704c850007b87054c400079d434c840004fc7059532006fa10d8e20006f43258440006bd6495132006f464d85320fdbf714ca40004fd71d9620005bf7550a400074d5354932004f7715913209fe4714ca2013d7d714c8500057d744c850007b8704c84005ef573d8532006755358450005b87054c40004ff7258c40125bf7150a401a7e652d8532005f87059132004fc7650e20006f571d8e2000578705085023d7f7154d521377a104c850006dd634c840006f63258450006b563584400e5bf7154c40005bd71d8e4014d7d715085018d7d7150e50006f754d8532005b7714ca401afd430d85320057f7350a50006f675d85320067d5358850007773258450006bf41591321aef743d85320047f7559132006755258450005ed729513213d7f714c85011dbf7154e400057d73d5152006b54358440004fd71d92200057f7354850005bf754c840006f670d853208edf3258c54007d543d8532004fc705954308dbe76951431b7e461509321957f7154a50004fd71d954216774714ca50007ad524c840006756258450006f560d85320057f7258c50004f87059532006bd43181420a7da104
  | 3 => 0x9bc0056850042000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9b9861c15210001a6ca1b8a65200038e55050181420055ac2064b08a000c3d54dc96315001a72c838284280035c203714c8500053ac3464b08a000977815d532140012f3023828428002ad6123258440004dac36e29908000ce9621c13214001a9aa6382a499003e14c832584400053b428c9b0a64009b7815d9321000167100a1a8428002bc6045018142006b9308e0990a000a778254d6114001c9ac6a926428003710c97199532005a6c1ea8a926400b1d84195534c8014ef06b12c228002ae2014318142006d4b10e0a908000ab8805506050c01b64c238264200025e201744c8500047c402ec2a26400e8d4358932100a769f02a9aa499002ade0943584400063a282e3b1c4000e95434c961100a3e88c2a9aa499003a950a325844000578c0880302a600d73711c132140015d304280c0a1002ad618325844000578402ebb0a6400ab586cc96110001ae4c238284280030f553735885400746b1a849908000e65528c961140012f30c38264280036c58470548400053ac2864b08a000ec5320c9611000156b083aec299002ad61332584400053c402a6302a400c3d75590644c8014eb0c992c228002ad21170d8532006b8388e0990a000b4c8054d524c8018f70a382c8990023de05764c840004e643aa6a126400d3450dc5329000171900a1a84990032d90171d8e20005b440284990a000ab7845c3614c8010ff0cba26428002bc604501814300752a1264b088000ab880590644c801a72ca382a6200029d21570d853200732a9264b08a000db370dc532100016e100992c2280026e201754ca4000786a9aa49908000979811c13214001ad2c43826428002e6201534c840004bac36e2990a0009b7815d5329000137302382a4200023de0576951320055bc22cbb0a6400b4d82d51534c80156f08b06c2990029d61474d8532006a6194ea3226400d2d545c8544c8013730c382a6200030f99171d92500053ac28c9b0a6400e39541406050c014e90aa06c2990034e5907050c500055bc22ebb0a6400d99631c1321000136f02ba264200038e5504018153004bdc08e0990a000b35840c961140014ef0aba6c299002ad61370d8532247c2196e29908000d72611c143140011ef02bb6a899002bc60440181520069ca98e0a908000cb774185654c801ae2c238284280023d61e65d85320053ac2a64b08a000b588050d32140019e0c2382ca990032e21070595320063c428e0b226400f854350b614c801a6ca1b8a64200036a588704c8400055c402c92a26400d59631c1431400176100992c220003710c971991320be5b306e29948000d39651c152100012f30c3828428002dce0532980500045ec3ec82a26400a7485583614c8010fb0fb28a899002ea201524c8400071aaa0a9b0a64009bb811c15310001ad2c4382842813be11854350932
  | 1 => 0x86430cc09912fd10cb714ca5000678308e0b226400af080597614c801d4ac5192c220002ece0532980400055ac20cbb0a640093f855d93210001d2ac6992c2200023de1d32584400059ac2864b088000af3805d7614c801caac6992c2280039958a32584500047ac0ce1b2a6400e39541006054801b6101b8a6420002ad61350d85321663b306e2990a000b2d85191424c8011ef0e992c2280029d61832584500055b426c1b0a6400ab78258d61100011eb0fb0cc099002e360e54509320055bc22a1b0a64009b9861c13210001d4ac4992c2200029de1560d85320061eb2ae832a6452d4f7154d524c801c9ac6b1264280024fe15744c8400053ac2e81b0a6450b8f8150d424c8014ef0ab86c2990030f15171d96400047bc0aec990a000a778258d611400196880b8ec7100029d61b3258450006e8388e0994604cec432184604c8012f30c38286280034e5047050c50006d9b88e09908000d39431c14214001a72823828428002ad61a325844027ec7b8a86a126400d3450dc53210001caaa7992c2280026e201754c840004bbc0ae8990a000dc4325c6604c80156b09b06c2990029d61432584400053c402ca32a6400ab5840c961100014eb0bb86c2990026de05754c840006acb18e0990a00087f87594654c8011eb0f38ec710003c350d424ca50007a299064b08a000db0711c1321000117d01ba2ca99002e360a5450d32006d9308e0a988000a78805506054c95e8865b8a6428003630ca74195320071baa4a9b0a6400f0d53549329000156f06b12c2200025e6047050c5000732b1264b08a000ab684dc3614c80117f0cbaa64200033658c704c850004dcc08e09908000ab5864c9611000156d083aec2990032ed047059132006f0388e09944000af0805d3614c8010fd01baac8990036350c70509320055ac2264b088026c7660dc5329400137302382a6200025ee0470508500063b282e3b1c40008f7815d8544c8012f100ba265280039554d32584500047ac3cc9b0a6400d39511c153100014e90ab26c2990034e544705484000579c02cbb0a64008f586dc532100018f6a2382ca99127e10cb714ca400049fc22ea990a0009bb811c13210001b62c2382a6200036658c7054c400055bc1a84b088000d1d545cc544c801b64c2382a4200029d616325845000786a1a84990a000ab880550605080187ccab8ecb200032ee1070595320053bc1aa4b08a000ab4845d7614c80156908b2ec2990035ce03714c850004bbc0aec990a000a78805506054801c9aa6b1264280023d61c61981320f65b306e299080009bb811c152100019e6e030ac8990022fe1d64191320047ac36e2990a000cf370185654c8015e700b26c2990025de1d32584500049fc22ec990a000af3805d3614c80156908b06c2990025ee047050c500074aa1e64b088000
  | 2 => 0x40c408001a8e808050081400035300026090c0a40e2300000000c0f8001a00078140a0223000002a01800083d010041a3d00030b4060282400bb00000f618968005800020381a7b118083608000200e4f0582000d90e00008040001000760387002320180c1c020a8a412010c01000021400052030681c0e00029082e000099006020100800010627000000000400010e8700006051c03207020000165b0832aa4990026de1d32584400053b42ec1b0a6400ab484543614c8013990ea1aa499002c76146450d320074ab1e64b088000c3d76550544c801caac7992c228002bc20164d85320053bc2ac9b0a6400a76851d3614c801e8aa6a96c2990029d61760d85320053a42ae9b0a6400a7880597544c8014ed0ba06c299002ada1065d85320053bc2a81b0a6400a7585cc961140014ed0bb86c299003b14c832584500059c402a6a9080008f5819c3644c801b6701b8a64200025de05744ca500049fc3aa82a26400d71611c14314001d1ac6b1264200031ddd46159132006b9b86e2990a000ab684d43614c89bd8
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc000000000710200206f8806d100d0003c03810060ca3cf0c00060800034420300090001a85844c83258440005c2241535493210001b05854c832584400070c991611c14214001a45854c8325845000551654325c6654c801a5163201325845000463660329d0654c801585940c97199532006a1611320c96114001471961c4704c850006c250c805093214001545950c971981320071458d611c143140012b19620132584400049c644805506054801c616258470508500052c658711c1321000127191201541815300543650329d4644c801c196458c7050c500048de6154153614c801330906103258450006c1611320c961140abd40321c4704c85000706595631c15310001c32655847054c40004cc241850c96110001c3265584705484000698588804c96114001c4963588704c8500049c241850c961100012b09061032584500070a595621c15210001c8963588704c840006c254c8054932100a9d80321c4704c8400068a5518214060508014389059574195320070a591621c142140012719620132584500068c951811406050c01a33546044018153006a1619320c96110001c32645847050c500068cd51811006054801a45864c83258450004ac644805506050801438905d954151320068c95181140605080150d950ca741953200453660329d4644c8015489054c70549320060e5d480590644c801545950c9719913200562241431c1424c801585940c97198132005c2241435093214001585940c9719913200691615320c961100012b1912015418143
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x208600aa0281844c8325845000548140c2a64192c22000344032658711c132140015805030899064b08a000ac0281854c83258440
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x5401b40c9961c4704c850
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x98a
  | 2 => 0x128a
  | 3 => 0x9ca
  | 4 => 0x12ca
  | 5 => 0x10a
  | 6 => 0x130a
  | 7 => 0xa0a
  | 8 => 0x14a
  | 9 => 0x134a
  | 10 => 0xa4a
  | 11 => 0xcca
  | 12 => 0xd0a
  | 13 => 0xd4a
  | 14 => 0xe8a
  | 15 => 0xeca
  | 16 => 0x74b
  | 17 => 0x74c
  | 18 => 0x104a
  | 19 => 0xcd292
  | 20 => 0xcd2d2
  | 21 => 0x14112
  | 22 => 0x134112
  | 23 => 0xcc112
  | 24 => 0x10cd2
  | 25 => 0xd4112
  | 26 => 0x10d52
  | 27 => 0xec112
  | 28 => 0x10ed2
  | 29 => 0x15312
  | 30 => 0xcd312
  | 31 => 0x130cd2
  | 32 => 0xd5312
  | 33 => 0x130d52
  | 34 => 0xed312
  | 35 => 0x130ed2
  | 36 => 0x130d12
  | 37 => 0x130e92
  | 38 => 0xcc152
  | 39 => 0x14cd2
  | 40 => 0xd0152
  | 41 => 0x14d12
  | 42 => 0xe8152
  | 43 => 0x14e92
  | 44 => 0xcd352
  | 45 => 0x134cd2
  | 46 => 0xd1352
  | 47 => 0x134d12
  | 48 => 0xe9352
  | 49 => 0x134e92
  | 50 => 0x134d52
  | 51 => 0x134ed2
  | 52 => 0x16cb
  | 53 => 0x154c
  | 54 => 0xd0cd2
  | 55 => 0xccd12
  | 56 => 0xd4cd2
  | 57 => 0xccd52
  | 58 => 0xe8cd2
  | 59 => 0xcce92
  | 60 => 0xeccd2
  | 61 => 0xcced2
  | 62 => 0x58b
  | 63 => 0x188c
  | 64 => 0x18cb
  | 65 => 0x5cb
  | 66 => 0x1a0c
  | 67 => 0x1a4b
  | 68 => 0xe8d12
  | 69 => 0xd0e92
  | 70 => 0xecd52
  | 71 => 0xd4ed2
  | 72 => 0x16c113
  | 73 => 0x16d313
  | 74 => 0x16c153
  | 75 => 0x16d353
  | 76 => 0x240d3
  | 77 => 0x252d3
  | 78 => 0xe8d0cda
  | 79 => 0xe8ccd1a
  | 80 => 0xd0cce9a
  | 81 => 0xecd4cda
  | 82 => 0xecccd5a
  | 83 => 0xd4cceda
  | 84 => 0x240c11b
  | 85 => 0x240c15b
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 29
  | 7 => 278
  | 6 => 476
  | 5 => 310
  | 4 => 61
  | 3 => 5
  | 2 => 1
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/37+packedAt gbK8 (754+(h % 37)*5) 5) % 29)
  | 7 => 2*((h/120+packedAt gbK7 (10286+(h % 120)*9) 9) % 278)
  | 6 => 2*((h/200+packedAt gbK6 (22848+(h % 200)*9) 9) % 476)
  | 5 => 2*((h/138+packedAt gbK5 (18290+(h % 138)*9) 9) % 310)
  | 4 => 2*((h/48+packedAt gbK4 (4270+(h % 48)*6) 6) % 61)
  | 3 => 2*((h/8+packedAt gbK3 (405+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3fc1ffe03ff80ffc1ff807c0127f679d9e77cc
  | 1 => 0xc0fe03ffc0fff03fe0ffffffedb8b8e2e388ff
  | 2 => 0xfffffc0000ffffffff0007fff1c0c0ff03ff0f
  | 3 => 0xffffffff00003ffffff8003e00ff03fc0ff0
  | 4 => 0xffffffffffffc0000000003fff0003fff000
  | 5 => 0xff00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x9402ce20938825c01c83641801b238c8e33cc
  | 1 => 0x4844012a484a920420d2969484b828a0a28055
  | 2 => 0xb2ab540410952cab5a00412b3140c057015d0a
  | 3 => 0x10b39a54b20104339c2560023a00d503540ea0
  | 4 => 0x20fde39f3ce7cf010841820c3fed0003fbe000
  | 5 => 0x3c21001820060802108604303ff6fef8000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 8, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 7, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 6, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 5, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 6, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 5, 0, gbRaw),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 5, 0, gbRaw),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 5, 0, gbRaw),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 5, 0, gbRaw),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 5, 0, gbRaw),(0x3030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303, 5, 0, gbRaw),(0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033, 5, 0, gbRaw),(0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333, 5, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 4, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 4, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 4, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 4, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36773
namespace PEqualNP.Outside.L_meta_36773
open PEqualNP.Outside.L_meta_36773.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_1_0 : Interval s0Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_1 : Interval s0Atlas 1 0 1 := bs0_1_0
theorem alls0 : ∀ k ≤ 1, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 36 := block_range (n:=36) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 36 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_96 : Interval s1Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_192 : Interval s1Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_288 : Interval s1Atlas 3 288 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 309 := (concat (concat bs1_3_0 bs1_3_96) (concat bs1_3_192 bs1_3_288))
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
theorem bs1_4_864 : Interval s1Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_960 : Interval s1Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1056 : Interval s1Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1152 : Interval s1Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1248 : Interval s1Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1344 : Interval s1Atlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1440 : Interval s1Atlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_1536 : Interval s1Atlas 4 1536 79 := block_range (n:=79) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1615 := (concat (concat (concat (concat bs1_4_0 bs1_4_96) (concat bs1_4_192 bs1_4_288)) (concat (concat bs1_4_384 bs1_4_480) (concat bs1_4_576 bs1_4_672))) (concat (concat (concat bs1_4_768 bs1_4_864) (concat bs1_4_960 bs1_4_1056)) (concat (concat bs1_4_1152 bs1_4_1248) (concat bs1_4_1344 (concat bs1_4_1440 bs1_4_1536)))))
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
theorem bs1_5_768 : Interval s1Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_864 : Interval s1Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_960 : Interval s1Atlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_1056 : Interval s1Atlas 5 1056 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1062 := (concat (concat (concat bs1_5_0 (concat bs1_5_96 bs1_5_192)) (concat bs1_5_288 (concat bs1_5_384 bs1_5_480))) (concat (concat bs1_5_576 (concat bs1_5_672 bs1_5_768)) (concat bs1_5_864 (concat bs1_5_960 bs1_5_1056))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 48 := bs1_6_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 24 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat bs2_4_0 bs2_4_96)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat bs3_4_0 bs3_4_96)
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
theorem bq4_3_0 : Interval q4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq4_3 : Interval q4Atlas 3 0 1 := bq4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_0 : Interval q4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq4_4 : Interval q4Atlas 4 0 1 := bq4_4_0
theorem allq4 : ∀ k ≤ 4, ∀ i < count q4Atlas k, checkRow q4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq4_3 i (by omega) hi
  · exact allq4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_3_0 : Interval q6Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_3 : Interval q6Atlas 3 0 1 := bq6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_4_0 : Interval q6Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_4 : Interval q6Atlas 4 0 1 := bq6_4_0
theorem allq6 : ∀ k ≤ 4, ∀ i < count q6Atlas k, checkRow q6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq6_3 i (by omega) hi
  · exact allq6_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_2_0 : Interval q7Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq7_2 : Interval q7Atlas 2 0 4 := bq7_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 6 := bq7_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_4_0 : Interval q7Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_4 : Interval q7Atlas 4 0 1 := bq7_4_0
theorem allq7 : ∀ k ≤ 4, ∀ i < count q7Atlas k, checkRow q7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq7_2 i (by omega) hi
  · exact allq7_3 i (by omega) hi
  · exact allq7_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_2_0 : Interval q8Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq8_2 : Interval q8Atlas 2 0 4 := bq8_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_3_0 : Interval q8Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq8_3 : Interval q8Atlas 3 0 6 := bq8_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_4_0 : Interval q8Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq8_4 : Interval q8Atlas 4 0 1 := bq8_4_0
theorem allq8 : ∀ k ≤ 4, ∀ i < count q8Atlas k, checkRow q8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq8_2 i (by omega) hi
  · exact allq8_3 i (by omega) hi
  · exact allq8_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_2_0 : Interval q9Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq9_2 : Interval q9Atlas 2 0 1 := bq9_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_3_0 : Interval q9Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq9_3 : Interval q9Atlas 3 0 5 := bq9_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_4_0 : Interval q9Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq9_4 : Interval q9Atlas 4 0 1 := bq9_4_0
theorem allq9 : ∀ k ≤ 4, ∀ i < count q9Atlas k, checkRow q9Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq9_2 i (by omega) hi
  · exact allq9_3 i (by omega) hi
  · exact allq9_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_2_0 : Interval q10Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq10_2 : Interval q10Atlas 2 0 1 := bq10_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_3_0 : Interval q10Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq10_3 : Interval q10Atlas 3 0 5 := bq10_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_4_0 : Interval q10Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq10_4 : Interval q10Atlas 4 0 1 := bq10_4_0
theorem allq10 : ∀ k ≤ 4, ∀ i < count q10Atlas k, checkRow q10Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq10_2 i (by omega) hi
  · exact allq10_3 i (by omega) hi
  · exact allq10_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_2_0 : Interval q11Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq11_2 : Interval q11Atlas 2 0 3 := bq11_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_3_0 : Interval q11Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq11_3 : Interval q11Atlas 3 0 6 := bq11_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_4_0 : Interval q11Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_4 : Interval q11Atlas 4 0 1 := bq11_4_0
theorem allq11 : ∀ k ≤ 4, ∀ i < count q11Atlas k, checkRow q11Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq11_2 i (by omega) hi
  · exact allq11_3 i (by omega) hi
  · exact allq11_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_2_0 : Interval q12Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq12_2 : Interval q12Atlas 2 0 3 := bq12_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_0 : Interval q12Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq12_3 : Interval q12Atlas 3 0 6 := bq12_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_0 : Interval q12Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq12_4 : Interval q12Atlas 4 0 1 := bq12_4_0
theorem allq12 : ∀ k ≤ 4, ∀ i < count q12Atlas k, checkRow q12Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq12_2 i (by omega) hi
  · exact allq12_3 i (by omega) hi
  · exact allq12_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_2_0 : Interval q13Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq13_2 : Interval q13Atlas 2 0 3 := bq13_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_3_0 : Interval q13Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq13_3 : Interval q13Atlas 3 0 6 := bq13_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_4_0 : Interval q13Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq13_4 : Interval q13Atlas 4 0 1 := bq13_4_0
theorem allq13 : ∀ k ≤ 4, ∀ i < count q13Atlas k, checkRow q13Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq13_2 i (by omega) hi
  · exact allq13_3 i (by omega) hi
  · exact allq13_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_2_0 : Interval q14Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq14_2 : Interval q14Atlas 2 0 3 := bq14_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_3_0 : Interval q14Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq14_3 : Interval q14Atlas 3 0 6 := bq14_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_4_0 : Interval q14Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq14_4 : Interval q14Atlas 4 0 1 := bq14_4_0
theorem allq14 : ∀ k ≤ 4, ∀ i < count q14Atlas k, checkRow q14Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq14_2 i (by omega) hi
  · exact allq14_3 i (by omega) hi
  · exact allq14_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_3_0 : Interval q15Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq15_3 : Interval q15Atlas 3 0 1 := bq15_3_0
theorem allq15 : ∀ k ≤ 3, ∀ i < count q15Atlas k, checkRow q15Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq15_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_0 : Interval q16Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq16_3 : Interval q16Atlas 3 0 1 := bq16_3_0
theorem allq16 : ∀ k ≤ 3, ∀ i < count q16Atlas k, checkRow q16Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq16_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_3_0 : Interval q17Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq17_3 : Interval q17Atlas 3 0 1 := bq17_3_0
theorem allq17 : ∀ k ≤ 3, ∀ i < count q17Atlas k, checkRow q17Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq17_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_3_0 : Interval q18Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq18_3 : Interval q18Atlas 3 0 1 := bq18_3_0
theorem allq18 : ∀ k ≤ 3, ∀ i < count q18Atlas k, checkRow q18Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq18_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_2_0 : Interval q19Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq19_2 : Interval q19Atlas 2 0 4 := bq19_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_3_0 : Interval q19Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq19_3 : Interval q19Atlas 3 0 6 := bq19_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_4_0 : Interval q19Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq19_4 : Interval q19Atlas 4 0 1 := bq19_4_0
theorem allq19 : ∀ k ≤ 4, ∀ i < count q19Atlas k, checkRow q19Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq19_2 i (by omega) hi
  · exact allq19_3 i (by omega) hi
  · exact allq19_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 61 := block_range (n:=61) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 61 := bgb_4_0
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
theorem bgb_5_288 : Interval gbAtlas 5 288 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 310 := (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288))
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
theorem bgb_6_384 : Interval gbAtlas 6 384 92 := block_range (n:=92) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 476 := (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 86 := block_range (n:=86) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 278 := (concat bgb_7_0 (concat bgb_7_96 bgb_7_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 29 := bgb_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_2 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 2 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq4 (cert : Complete q4Atlas) : Lower true (roots q4Atlas) (target q4Atlas) 5 := by
  have ready : Ready q4Atlas (asRow q4Pos) (asRow q4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 5 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 5 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 5 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 5 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 4 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 4 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 4 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 4 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0eeeaeee0eee0ecc0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq4 : Complete q4Atlas) (certq6 : Complete q6Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 8 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 6 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq4 certq4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 6 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a : Sig) 5 :=
    slice_correct (ms:=fixRows 4 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa : Sig) 5 :=
    slice_correct (ms:=fixRows 8 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 16 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : Sig) 5 :=
    slice_correct (ms:=fixRows 32 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0x3030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303 : Sig) 5 :=
    slice_correct (ms:=fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0x330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033003300330033 : Sig) 5 :=
    slice_correct (ms:=fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 : Sig) 5 :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 5 :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 4 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 : Sig) 4 :=
    slice_correct (ms:=fixRows 8 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : Sig) 4 :=
    slice_correct (ms:=fixRows 8 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 5 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373984 * 2 ^ 32 + 4007718080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36773.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.and,[0,6]⟩,⟨.or,[2,3]⟩,⟨.and,[0,4]⟩,⟨.or,[1,9]⟩,⟨.and,[0,8]⟩,⟨.and,[8,10]⟩,⟨.or,[9,11]⟩,⟨.or,[5,7]⟩,⟨.and,[13,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4007718080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4007718080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36773

open PEqualNP.Outside.L_meta_36773 in
theorem PEqualNP.Outside.L_meta_36773 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373984 * 2 ^ 32 + 4007718080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373984 * 2 ^ 32 + 4007718080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq4 allq6 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allgb)
