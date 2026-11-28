import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36725.Model
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


end PEqualNP.Outside.L_meta_36725.Model

namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
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

def SBf (j : Nat) : Nat := [7, 3, 8, 6, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_36725

namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x4b00e0061c089e0400070d40002c1001041000240007ff32fc31fc43fd31ff42fc10ff41bc40ff31fe20ee20fd40f610fe43ff20fc32fd21be40fd42fe40fe30fe42dc30fe10fd41fd43ec20fe21fc40fc41ff43fd30ff10fc42fe31de30fe41ff30ff21ff40fd20f410fd10fd32fc21fc20fc30fe32
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x2c5b00610012011a02021300000c060000004d0012000203082d03030000052a1c00000000010041020000020f01050201012201260012007b0010010000071e020003123c00360b01050000042806000a1600bda82635d53c82eaa3906b10020af298836e508827ea8904f95332af29e853c544c678a890cf95310bc282833c544427ca0204f553329f2a6615c53486bea6a0f908010ba28a61cc30883a861085754f10cea18875d53086bca7904f95031db20021da500c2eea2986d10010d6a1085ce308827ca9195b54a43bb284213c54483ac61085b14940af29c853d548cadca420d714d20b7296813f544c6e8a2a05bd4931b6292613e54086baa620db14910f810021f250043e680085b54b40b7296213d54cc3c841085714d40ce20461d030042daa418fccc010b6a96617b50486eca0086d90210f3100217651c8374a0205714d10d720441b440842dea4a0eb10220afa9a415e530867aa9884fd5110b728041f030043b060085dd45409f2a641ce30082d8a498d754f409faa2436e5290ebca788760c310e6180415f534873c81187c10010f5280415d5390af6a0a0d7d4d40bba8a419e400c39a64196c10010f0100217451482b8a6a0db14941ce2006178504c678a8985b94b43af284613d54086dea4a04fd5130d7200417850486bea6885b54b10aea9e85d430043d040084f94240b6a9687e620842daa420ee10310af280613d54c82eaa3987cc80109eaa063d630043d041885b94b30bb28e817551d02dea4985bd4910dc200216e520c6bca7a05d94730
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x8120104200043006e262d0010e810220042b26090010b498f40043c03088010ac99330042d2608c010b498f20043c23008010e81002004392400c010ac99320043c03008010b898b3004390408c010b898220043a24008010e21003008390400c010
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
  | 6 => 2*((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s0K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/83+packedAt s0K4 (3888+(h % 83)*8) 8) % 144)
  | 3 => 2*((h/13+packedAt s0K3 (722+(h % 13)*5) 5) % 19)
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
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
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
  | 2 => 2*((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffd5f1c71f878f1e93
  | 4 => 0x66fe07e3f80fe31c
  | 5 => 0x78fff803fff003e0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff8010000008810025
  | 3 => 0x2a2caab1c52a5a92
  | 4 => 0x1945b496d44ccb18
  | 5 => 0x78926db666893c0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 57 s1Pos s1Neg, 0xaaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaaaaaaaaaa00aaaaaaaaaaaaaa00, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x210604000900024710004124300400240008d001fe30fd21fe43ff10fc30fe40fc31fd41fc40fc32fd43fc41ff41fe21fc43fe32ff32fd32fe20fd20fc42fd40ff42fd30fc20fc21ff30ff31fd31fd10ff40fe31fc10ff43fe41fe42ff20ff21fe10fd42
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4217d52882faa018fd54420dfa0481de318c2faa021f754e21bea8663f5210877e8320df15031bf29885bf54482fca820cf95321df2a6657d51d03be6218cf95020b7296633e540c2faa9885f15320bf29e837c52443baa720df94d10bfaa043f531086fca720fb10932ee994637e530c6eaa321df15331af29c85ed32887ea8390ef50441bfa98437e53102fca3a1df14543af29e85dd5390b7e8520dd54732af298817c524c6eaa3215f95232bf298657d51d0fb8a6a07d94732deaa4637d52d07e88318ef90f42ee21a637d500cafca790dd94430ef990637e53d0a7aa990db14940bea8685fb20883e882087d8c431f6a9683dd43cc2bca720df14132dea1c85ef21c82faa8887b90832bf2a263ec21882fea8186f90941bfa8285ee520c2eaa3195f95230bf28463fa40102faa9987790e31f6a94877c53c837e84217b94b43be298215d53d06fca810df94b31fa188217e51882f8a8995f54021f6908437f52842fca12177cc730be28263f510042faa9206f15110fb18e217e52106fca7205794f21bf29421ad4210afea2a07d8c510f6192437f52c42f8a910dfd5032b7a9281df53442f8a4a05f14d21bea88817c53c87f681207b08420ef996617d50c87ee20085f94042bfa8a61de53d07eca3217b4c832bea88853f544c2fca9087bc8520bfa8a65bd43d037a8620df15232beaa663f55190eeca3995f54d21faa8c857e5390efaa6217b10a209e2a2217d54843dea4987794c10be28a417f53442fea9187dcc631bea8e657e52087dc6590774c530f799643bd41d02faa818f78c931bfa98217e51ccb7c86a17754f41bb28c65be43d06fca121fb50b20f729683ee42087dc43105d54420f7294637c53442faa890f714d10aea9c83f920083eaa3996f50841bfa9021ec424879a64196fd0740bea8e61bf4310ff260187d10610bf28087bd4210b7e8220df14d42afa9a417d52442f8a6107b14940be290213d548cbdc64905f94321afa9a213d54886fea4a07b50920fa20c43dd4310efca7885fd5132bf28c657c538437a80207b10820fb98821bf43502faa421db94b41bea9c835c534437c80a06f55010df2a643dc43cc6fea6905f54e21bea8085f5310c6f8a898f70c830beaa6417f548c6fca9887dd0631f799465f741043dc42106f50a41fb082216e52d0fda85995f94832fd882217c544c37e85215f55242f7a14657d5190af8a0a0df55231fba8a617e510c3e863085f54632bf28e41dc328c2faa7185fd4941eea9821bc43103ee21087d90441bb28c85ef52503bc6298df94041f619441f5410877887207b90842aea9c437e54cc2faa8997d88510bba8a41df430c3b887997bd0b219f2a465bd54c86daa521fd10521ee99065de53083e86310df95132f721443f651103f280207d88710ef29e857e508c37e85a05f55332
  | 1 => 0xd50886f8a2984f95231dfa12815d53102faa8186fd5110fb98a63ef32882f8a918fdc8621bf28c83ed21483bea6a05b94a31b6a96837d5390bd885195b54b43be2a0217e53c82fca6087b48020be2a6437e51107daa5a1fbc8421be282437f54483b86498df94342df20a837d52106eca3a1df94021df2a465ef32486f8a9997d50441f7216417e508837e8721fbcc820df21c817c53502f8a4a0ef90c40f6a90817c524c3ee4290fd54742beaa0417e50d0fdc6410df55131bea8e857e54883b886185f94032efa1a63bc42902fea4886f10f42bf290817e51902faa7085f95010bea94815e53042fea098df54c209faa2217f50506fca7086f55020faa0a217d520c7dc6510df94e20fa108217f504cafaa3905f94b10deaa665ef42882fca990df94830bf29a43f631086f8a7105fd5220eea9e85bc42103dc84904f15120dfa18857e51103b887187ecc130bb28e857d538c7ea83885fd4d21df20881ed42086fea6a15fd5330f6216437e50ccafca5197d54743f710a437e548c6baa610770cb31bf29661bd42503eea2a05f95020f7216657e52d03eaa2205f94842bf2a061dc434cbde4310efd0e42bf284817f544c6fea8985f54c10b7a92617f524c2faa9187d14530dfa1c836e5290ef8a7887e44010fa28a81be41902faa990db54a41b6a96637e500c7bca720f78ca30bf286637e50103ba6218fb0cb21be296217d5190ef8a2a04f55010bfaa021be54082faa118df14542bfa82877c534837c86a0f74c030fa98e437f53c42baa6086f10d42bf29463de320c378a8905f54b43be29c43bc42d07bc64995fd4121fd100416e52907baa790ddd4530f6a14433d54cc7ba8619774c730bfa98415d5390afca8207bd0820ef21887ee52043da84217b14910bf294617d528c2fea7907b94b31ef21c657f540c6f8a810df54e40fa10c217c514cbca4210df951309f2a4437e51082b8a6a06f90d43bea8483de5390afaa7107dd0541bfa92877551d0efca998f794c40f629261df4350eb8a6905f54610bfaa421be42103daa598df94631dfa0081de304c37a86215f54041bf2a641ed528c77aa998df94a43faa88616c52442faa520df94831bfaa621dd430c6f8a8886d50441f7a1485df320cbbe87995794e21be2a243ed32086fca2085dd4540df214817d54087f661185f54b31ee992617f53882daa4187d88421b6a90817c540837884a0f7d0f319faa241bc544c2fea8105f14a10bea88657e52442e8a2905f94341bf2a241ed52042faa920df55221bf290417d52103b8a690778c430dea1c837d53d067aa8185d54440fa28a41bf431077e87a07b8c832f6a10653d54082fca520ef10440af29e83bc41903ec8210df94740bfa8a857d5490f7c85a0df94742bea8c817d520c27ca8085f94e42beaa465de434c3eca3a15f94c30fd88
  | 2 => 0x980200c04028220f8e1025490a8780212c0100b2c000000110500832c45030141100a13e651f41518c0e048151aa6708c0e0082202046014270a82b0704c03c0845c110000e07c32154690a4890140006866050031202d07815020140043312c1c25457000055500c01425048020085986031000020094200c0600c020ac00046a40500500000020210042210c090980b0783100003010044600400812094010341701c0103197050000080002815000090080e000010b0490280000005040050100003400000041351d030800000a0480000406004090205f03c000040203c06018023f4080580301000054000440c010160000ab300f01c0a0300a028370506c970140201704402144031fc75002fca7a05f54d10fb28c65ed32c83ec82885d94643fd18061df438c2faa3106fd0841f729081f5410c6fea790fd48710fb208637d53c82f8a0a15f94630fb20e217e52d06fea9995b94810bf2a221dd438cbea42887dd4520bf2a085ee5290efca5a1f794f21bea8485f641cc6bea6a05f94431efa1a657c54882fea910f750d30fa18a437e508437c84a17d94420efa9a417d50d06fca421dd14530b6a946375510c37a82a07b0c820dfa0a81de430cafea710fdcc621bf284437d5110efaa610fdcc610bea9e857f53503daa418778cb31fba0c21f7210437a86a05f54420bfaa221bd540c3de84a15d54742ee18861ed32483be6519770c630fd902417c530877a8621fed0140efa1c877e500c2fca2195f54d20ef98a617e54487ec6390ef95010fa98a21f4414c6fea7087d54632eea98817e53082faa7a05fd5232bea84657d50ccafaa5884f95331beaa2417c5050fba6418df15120b6a90216c524c3de64995f54343bea9c655d53d0bf420085f94442bf2a0657e520437a85a077cc631fba0c43df324c2faa8197bd0921bf2a063dd438c6faa3185f54b30f6a94837e51886fca6905d94440beaa2617e5310feca321f7cc030df2a4637e529037886a0dfd5320bea98837e51cc3ee8320fdcc521fb28861f651d0efea2a1df54a31f7904417e530873a8621fd4c710beaa0217f54c86f8a8195f15210fba0a63bd54887baa6107d50731bf28483de430c6fca710efd5130bea9421f7414877ca910fbd4910df2a061df308c37ca998df94c41bf28c85bd548cabca6105fd5331bf2a443de43cc2faa121ef10f41f7294837f535067aa918df54f21ea988633e54ccaf8a8185f55220f690e413d54ccaf8a9185f94010fb90c217d53102faa5a05f54a21ee996616e520c2fea2905b94840bf28c87df328c6dea4885f95043bea90217d510c2faa521fb88120be2a6217c5250efca5215f94443fb20e437e51086f8a9985f95332ba28a817f524c6fca0105d94420bf28465ef424ca78a8987bc8020bea9e217c53507bca710d754f21bfaa2437
  | 3 => 0x4050090a40f030070040402c13a641a01a9f00005094370b069000001302900400020200040f72c0d0000615400014010081115505320000109e0000e00000098051042010805020010
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xd52442e662cc531d554f410434c5314910d3d4f5250355530c5219d5875250f2e5494b31d3149314c3375410610e9909410871d5390f428f99443507356115110e510d41cc63f65508418f59352c42cd63908428f191538832e5450a21b558e41c876552d0631d5d0d51ccb6451c8520d514f514825d65d0c30cd152104431e54cc6319d58653c833451901409b588538425d6395121d9185520427461540428f99454442776154042cb553420823d6414a109b98a54c43645248510b558e214425e63d5020d514d214423e6494421c7952438c7575314540d554f100423d64d4c21cdd0c515023c6454021d9908514831c54d4d109b988504c76552440108f590504874d53d0a429b98a54cc27561d53308f99741502756114c20c7552538866e65d0921cd145415025e63d5032b5987438c2776154032d314f214826e6294d10d594e31c86e5628c7109758e54c826c65509209d596410c65e6315221b958a310c65e65d0d31cd552510c32c5414910cb14942502e661cca20ad592314431d540c4309d987540874d5394810b398e218834c53909208f592534426f655082197596530826d62152309bd89534431c5414d10d354d20082ce63d0b21b398b434c65e63d48108f59352042b561d0e41cd545401034d5310b218f99252c434d5394b41b5586438cace63d0a429bd89501071e5350a419d986544c2ce62d0c309b596210825f6355120d358a53887676548421cd952510c25d6314141cb55042c867561d4f208f59053c866f6254d209bd95320869f6550c43cd55151082e661d0820ab59321886e562904319dd85544c23e64947309b189534427661d4c20ab58b419073454485109758e51c825d63d5310d5544310c2d563904319d98453882b561d0e428fd91500ca5e6315010cd10d511023f6454a309758f540866d6215030cd55251082e662d0541a7593310c6e56290721b598f410432d54cca32d394e328873551d0040b59874350e3e65d09408f997435032d42944428f592524433554d0631b3189300c31d5454e21ab191200834d5354840d354c32082766194c42ad993310425d6314121c715143cc2b561d0c42b958642c823f6454a108f596540c25f6354910b598743ccb1c53509409b596420cacd62cc730c754e421033461550108fd9153482ae64cc932e390f428cad6618ca30cb55342c866d6215231c7151314c26c6254630b3d85320ca6e62d5021c794d4390ae661cca32d954a51d0e3e64150309d195314433754d4530d9584524434e5350a219b996324825f654c8329dd95410866d650c82097596530431d53108409b98b535069c644c0309798c548836652547438f191518834f53d4910b998b418434d528c8309758e544427661d49439d59631087354394642ab992214872c52901408f993530425d6395131
  | 1 => 0xc3555354420cb551528c754514c530b398a310c23e6494d20d394e52907a542904219bd895010e3e6414e10ab593210863e6494c329b58a544c7645348421d510d51cca5d658c4309b988540c23e6510d42ab98a43d0b2d52d0040b598f419072c43548409bd95320cb2d42540428f99353082e661d0a20d54c5500c75553944209798f544878f4390b329b98a53d02d7654c431d3151320caae6290c409758f525066f65508429718d50106e56290421b598f418874d520c4309b98a51d036452d4530cd58654cc6e661ccb21a758f4210ace628c531d990a51ccad56390421cb1522048275650c410cd151414432d5488420c7153324c355518c430ab58b431063e64150109b58a54442ad62d0e43a758f4290a756194b309b98a5110f4d6294f428f593538865f6355210b998b41042e661d0a328fd91538427661d50208fd91500c63e64948219758e51d0357654c431d958652d06b66190f419b98b530866d6294f10d5951310c71d4354043c718d54cc6766195330a758f421066e6295130d954b41906ae6290541c795253082b664cc621cd185548c6d663d0531d994a41cc6766194f209718d548423d64d4f208f590504c72e548ca219b98a544c75553d0641c7550434c67561153328f596431033454d45309b58b54cc67565904219dd95310c74e544c832c7d50438c356524c431cb152324831c5350d40a7593318c66f65508329b596320871c54d4d20cd508515036653484219798e544831c5450c32ab992218829d63d05409d58754c829e648c430ad993314c71d5390440a758f41d02b66190e40d590c514c2756195121b598f218426c654c9208f99253486e661d094297994434c63e6494b30d5147314c3365490721a7593320c65e63141219d98653d02e562907109d58454082ad62d0540b558e41c432f4314940d354c32487673254420c794d43906e5618ca21b558732cc27665d0521b598f21486e56190920c754c43d065d6315210ad993218874e52cc631c7551530427561d4d42d354f32c874e4394a3197997314c2d561cc8328f992510c63d6494c32b3d91320cb4d3254032cb15142483655108420d5d4c31842cd6290e31d554c210425d63141428f99252442cd63c8421cdd0e5190e5d658c8309b98b54cc76452145409d185544c2d6618c932cd185548866e6510932d3d4c52442e662cc621d9109518ca5d63d4810cb10d52d06e5628c4219b1895010ed661d0d32d914a10442756115232ad986435071d5494f218f992544833554547328f992510ca3d64d4d21ab58b41d0336544c7219798f54c43c5320c6218f99353c423f6454620b9586420caae64cc820d514c51482756194d20cd58654c876742546329b58b54043545384110cb550420826e62d4543cb189540831c53d0540b358e428866d6294d219718
  | 2 => 0x62d5031b398f42486b561d0a42ad9864250b4c6254f219d185528c25c63540429d996214423d6494832e550c418c6b664cc631b998b414c6766115232b918121086ae6290f418f592530876742546428f994544827b6544010c795153c86d5638c4319e596100432e5490a21cb94d4210a3d6494720d9cc9518ca3e6414c209b98a53106756114142ab58b4310ae5618c8219d1855010e3d64d45329d597410429e648cb31d954a5190f2e54c8621d314a304c33554cc4108fd91500872d5410932c7151324c32c5450821a7593314c23e6494f10d5151310c65e650c9319d984548c3344354742e3d0c424cb4c534c8218f99353c871e5454e21cd550410431e5490e32b5181310c6ce62d0e30cb549401034d538842097195434c23e64d4b109d9845050b3454507109d586544c72d54cc820ab18940102ad62d0e41ad58742d026e62152308f59053882ad648c9209d586544ca6f62552308f99353887c7320c521d394e52d065e6395021cd94941106ad62d0e429b59742082cd6290d30cd95231c87555354742cb552520c26f6254630d554e51d0ad56190c31b358e42ccb2f54d4930d9949510c32e54948309ed95200834c53d4940a7593328c74e5354a41d394e521026d65cc820a7992314c6ae64cca20cd94d41106e662cc631b398b4350e3e64d4532b358b318c6d561cca32d518553907355110440cd550414865e65cc930d354c420829e6390a40b358e42086776548421d594d41c873643544409d987548cb1e5494c108fd95401025e6314c209718d519026e6590920d554d100426e62d5030c7151430c65e6510d32b958a31443c4324c721cb949429074d53d082097d95430ca6c6255210cd553318879643d0631ab5924210a6d62d4f10ab592320cb8c43d0932a758f429072f5414930c7152304c23e64d4931e350e420cb665294643cb14b425026e6215010c794f4390a3d64141329b58a544c2b765504419d9875350ab66190a40cd550418866d621533197994534825c6354620cb55332c86766195120c7d5353482ce62d0f32d558453442766195032cb95252043665254440cb50e529063e64141319d185500caae64cca328f992530c73654547328f593530434d4314930cdd0e5190a6d6214c108f191534829e6390941d354d520431e53d0a41d9149414432c62553219798e521067661d5330cd95241cc65f654c4318f990540836752d4530b358b310c63e6510941d558653d066e6295110ab98a419035453505109d584540c25d6510c30ad986425065d6590c31c7151434c34c52cc930d994a51d0f2f54d49109758f54c825d63948419758f54c875653544409b58a531067665d0531b958a21087354154041cb95142ccb4e53c86219d987540ca5d63d5221d394e428871d548c430d954a510c2b66190d42b5185300
  | 3 => 0xc41cb153524c2766194b40cb54842d076432544209d586544c36654484219d9845050f2f5410a209b98b540cb9743907318f596540423e6414e209758f544876552cc410d354c32c86e662cc6109d586534863d65904409798e51d03355454430b598f21043555354642d358853482756194b40d594e51083665254643a7593324c3565354420cb951520426d62d5030d954841042cd62cc530b998b419066e6215331c794f419063e6414132cd553318c7c5328c4219bd89539034f4354a439b189519027561d4c20a7992318c31c5390140cb189548ca6d62d4d41cb14b415025e6314141b5587320c63d6494f10cd550418c7555310621ad993214865f6550c31d350e528c65e6314c10d514f5150335540c621d9d4821843573214530cd90951102766114c20d554f318865e63153219d5845050e7661d5030d394d52103964350431ad185401026d62d4543cb552528c71c53d0d40b358a4310fa74210521cd55031043355494632b5586438c6b66190f42b998b314869c6050c43e5d0c414c65c6354a10cd952510823f6454e208f59253c83565354742c754e43d066d6590821cb150524c27661953209b994324866d6215210cd150514831c5350540d394b328c676650c521b998b418874d5354b41cd553210434c534c9208f992520cb8d4310a32d590e518cae462440109d984530423d64944329d58454883646154a318f593530825f63551109758f540827561d51328f59251087365454420b598632cc63e6414c109b58a5110f5653947429d987544cad46344010d9547200829d63d044197d8d51902b46444010cd90d51d0a5d6394442c715053483653214520d9151210866e65c8520c7951438c6ae6290d439718d544426e6214810ab58b41106756194843d354a310c2cd63c8720b558e414427b654c030a7992320c26d62150109b988530431f54d4d10c755153082cd644c832ad59241106e661d0a428f592534865f6355220cbd5052442e661d0b21a7992324c65d6395120cb90d52d07344254440d914521483555394642ab59232c825d6395310d9549511031d43948439b99442486d663d06319bd89544834c5348520cb153214831e54cca319b58a534425e63951108fd954310ace62d0d32b9586428871d544c030d3149324c23f6550c43abd854210ae564484219798c548433554c86218f993520427561d53329d9865210ece63d0932cb550210831f5414d10cdd08515032c54909209b58a51d033454d4520a7d854310e6e62141418f992530875653944409ed95401025c6355220d3d4c32882776154e409dd85538827561953209d58654483665294440a798e4250a9e6390440b958a414425c6355120d31895390b2f4394a419dd855010e5e6395310b95864210b355410531abd954210a756114e20d5545300c26e
  | 4 => 0xf994544c23c6454a30d514c51503665250731b5987434c66e62d4f109b594420831d6395231cb951528c6e763484219d98454083645288510c7550434ca7561d52329758e52d033754d4520b5587328c66d6295132cd55341042d56190d309dd85524425c6354a409dd85548c26e62d51318f992544423d64944319b58b54c423d6414e10ad587421075453885108f593524c65f654c831c755043cca6e62d53308f99251c834c4354b31a7d894310e3c6454032cb54a421025d63152209d185538832d52108409d9964144364524c5109798f540c71d540c830c755343cc71d6395232d514d3144365520c410d354e529074f654c832cb553200825e63d5010ab59232886cd6290e32b398a318c3553214530cd152414436752d4540d9485500875753145209798f54086b564884218f59052042cd6390b20ab1814210b655254743b9586420867661d53329bd89538432d540cb219758c520433451d0540d954b210426d6214141f18c931086776154d108f59253482b5648c431cdd0a5190a7661951328f992520c63e6414121b9185200833554c4010cb548411032d6295332cb550428cad663d0610cb55152cc72d4314940d3949328c7345488510d50c9510c2e56348421d554f2188755530c6219798f54886b5648c721ab99332c86ce6388521cd55341886e662d0631d3549300c34c534cb20e550e410c66d6294f40d5d0d510c2776155220d5146304c32d54d0a32e390d420ca6f6254031c795253c86746154e409d987530869d64cc73097d8d544c3656194b31c7550430c2cc6348020add89411074c6254c20b9987324cb1d53d00409dd951004334544c510a758f41906d661d0e43b598743cc72d54948109dd95410c72c5450b209dd8554442b664cc610ad18141106d7624c4319d587540ca756195330b9987324863e64d4c21d514d310863f6454910c755032cc72d62952219d19521443c432cc5218f191500c66d62d4c108f990538863d6494b10b358a43cc3355494732d9545200825d6315321b358f214825e6314a109d98652cc25d6394821add8d41106ce63d08209798e51c834d53cc8208f19152842776155120b598f414871d5390b41c7951328c676658c51097d8d5010a3c6454d10cb95242cca766114810d354c210835753d45209b58b540c72e4354840ad587435023d6414e219b99452443655294440b5986324c63f6454d10c754c43102b564887109d185548c2ad64c8720c754c42d072f65508429b988538434e5394810b358a430ca5d63951329b5885050f365454430cb94b429073454504319b189548c3375414530ad99331486d6618c8308f592520c74c5314940cd952518ca3e6414a10ad986431031d5350040cd54641102b561d0f40d510d510c2b664c86108fd954210a6e62d50109798f525063f6550
  | 5 => 0x524431c6355030d550e518ca6d6295330d3548320c3646154a41cb151420cad56388421c7152434c3645188120d954b410427565c8410cb551200826c6255130d354832cc6b66190d438f59642102d56190c438f191518c2766510531d9d48514c25d6314a10cd15231443556194f21d314e204827665cc521d994a510c25c63540218f191538425d6315010ad587429065e6315020d5d4f51503a442d0521b9586324825d63d454297996434c25e63d53219d58754082d663d0541b9987424863d6595020ad59231c43563254430ad592214434d53948409b189501075553d0621d518553887355454632cb151324823f6550441d554d51102756510410b3181320cae661cc820d394d52042b561d0940cb15121482ce638842097d954310f2e544ca219d18554882ce63d0a209758e540876552c40109d98753c823d6494730ab98a439034f43548308f99253442cd638c8329d584504ca6d62953109d185529036632145209798f5150a77654c421d554c410432f4394a43a758f425026d6295031c7951530435553cc4109798f52c42746550510cb94b419075653546429798e52c43645214530b998b414865e63948218f59353c426e62d4c109798e5110b546154c108f99353486cd6390920cb550424869d64ccb309758e51086b561d0842b9586320ca7661d532097d8d518836552cc6319d58653d031d4394443d314e32482ae62904409758c540826c6254e10b558e21c429d64cc8329bd9521087655210631c7552320c2d661d0c30d950851482ae6290d41cd95141cc72d6215120c755043cc66f62546409d594210435653907219dd85534825e6514d10d310d520c3375414520b598f21887365494732b398f428ca7561d5030a758f42d039443d0531a798e42102d7644c4319b98853082746155120cb951520c26d62141319bd89544426e6294f10d394d328866e6295031c7553300c32d540c820d5547300c26f62551309d984504cb4c5350920cd150514c2746154d209b98a5244356534c721c794f4290acd6390832c7d954310e6d6294730ad5874310ece63d09429d584548c36452905109b988548c6776154a30ab593214832d5454830c718d54ccb1f5414d20c7951438ca6c6254031c7552530825e6394d1097d8d501065e6394d209758c548863d6414c209d59731043354314540d354d52906af6350842c755343cca3d64948219758e52c431d5494c10cd95141c865f63540219d98454ccb4f4354b319d994414865d6590c328f59252cc33554084108f590530431e5494e219758f52c435543145309b988548425f654c030c7553430c32d5290b41b958632c83545390510cb54a411036552544309dd95411075653946429bd8954842e56190b329d5865310b1e54cca32c755232cc6b661908409b596520426c6254e408
  | 6 => 0x2006106674070121280d8068850000044b021002104040002000040b00f00600c228000c00027a8060480000200307c0080100502202c0100a00c4680201a00202c160051d816c0000002806c37005142014010000000201182e6fe4280081100a52c3584f01c0c0248020000101d01541024c6a0090001083f8024cc020070cf004018020d82d01180400000a0141d25302402c0102f024054000030000443d000412000e0800030368078020040740386400e000000000580387200212c000030eb0060000300001a094018030000180781e0000180181d0262680001400008804002020038010110060680f8020000800003d0080f416065006014008480200080000500e01005800000028010060000200a052000158001240000440eb510d4004140260040dc0400001a084008260000840a0020120040003a01801c0081e0520e0bf80500a0100003f23600c0d01918e0000080400c8680c00045c0080400402515c0603c04810c36002000188001500702200c8020121d4160a802e10006802000004040030000895380200e000158100c04fa5e63944218f191524426e65cc921a7992328c2ae6488420b558643cc2cd6290c31cdd95411071e5454c208f99253c82766115030ad99321042ae64cc9219b988540831e53d0e41b5591310c72e5494a31b958a31c869e63906409dd8552902766115010d950a51cca3e64d4f20d5cca518ca9c63500409bd95200823d64d4f21d554c310426d62951219798e52d02ce62d0f318f990520434c53d4910b5586430cb2e5454b318f992544c32c52505408fd91518c34f5314940d554f210425d6394910a75924310e9e6390b41d354f200826d62d5330e910941c86ad648c821c755153c86cf654c832b398b4390e5e631414297d8d529023d6494c31d95462108364528c510b558e41106e76448421b958a41106e662cc410ab58b43502d561cc930ab98a4350b8c4350b329b98a51cc2cd63c86219d586540cb4c52cc530d914b515031c54cc5308f99053c869e63905419d987540c74e4314930c754c411025f6354a10cd551100426c6255110cb55252cc6ad62d0f409758f540426d62d51319798f54c83644254420d514e3144354534c710d34ca510cae56290731cd15141087675214540ab58b4310e5e6314810d954821042b561d0c41d5d0d5190ed56390731ad5874390e5e65d0d32cb15352442e661d09329b997424ca9e648c932e9508418875553944409d986534827661152209b98b54c429d64cca32d354b300c26e6214143ad98642d07674254420d914921c431d6315130d394d52d071c53d09409b58b548c7655254643c754c43d0a5e63953209798e544874d528cb31cb551520425e6315030d354f42c86b5648c421b9d9521087365454632c754e431026e62d52319798e
  | 7 => 0x680c00e038488171120003088801c000018056460f0000040000a81000205a33006801020028000290980143b87e026000098050160101e8110140a80098d0000240713e012084108020060052608c0160040600f014000ca02600200c008021180080c80b0be1c4190650180fc0d004038298128070024504980410005002065000064000000d009c0200000c0004a83f7b209000002000004140050020dc02800044040000010060280080d0020081781200601401820024360760070540d40b8060142000780107401c0580a01e000070040000dc0801800c0200309c028068008000360300b0000f6024010030000b00241d0120041984701e0106100403a0100000001
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x18d2571d0e5290722a9cc5a082143dc94394843c1ac72968320c8d72d954310e8b3a4a4988639198d52c8410c1ac829e42906155498f4104312aa4c598c43315cf6548421a8ce7a12a2104557614e414429338ecaa1085459ce4254440a8ce7a12a3216455398b418872231a42a80439118d5244010a2ce9192a2184357695231c8712aa4c3a16438350c625404392ae63028220e155418d1004312aa4c3996438954861500408aaed29c8390e255498b418870632264a8065255c76250c4389ced2a2641960e5458a438c707322a7108410bdd95488420a8ce3a1aa521e266454b310430aa98c2a008183191524c03094ae3b2a84216466354b41907072a2c790c43315c8604c43192ae9b2a6218d2572d0e5190b2229ac31924185d8e5350441c1aa931462186445358a414430a2a2c321a618555263d06218aeeca9e42084377655321886a339ca89084307dd9548c43094ae43028220e0d5498e2108292ba46428a418359252cca31858ecaa2401054671d0d52cc6a2b9c8428a41855905388510c2aa931e420850f7550e420cb22a94c319061499ca435474289aed29c8510d4673d952108722b18a6908438994961d0a41c1ca6b1687214a5741812108646b9ecaa10858594d61d0e41a2ae9994a31960d5398a431021abb0a918a2119dd952d041089eeca9c421060d5498f42c861bbb2a998c638550e6194843c18a8b1c849060d5398a4110307322a79904185d964350431c28a8b0e649861554185300c30b322a798821459d3654c431a4ce929a4210e4652587328c70a31aa2a008191548614c030a1ce7b2a842151574cc8514c32329ac520e4389951629073189eeca9e841054673d09518cb0aa9cc3216830ddd954cc410c8aa630a401060e6454f32c87072a2c598c638599153cc62194ae2302842161553986431029338c86a96838999152c841089aec29c849060e6454a320c306aa4c5a1861499cb6550441c2ac828e629854672d0d51cca9338c86a9081895506148020c2ca6b0e8520e24645491004217bb2a9990418518d415404192ae83026218e0c6454d2008233bb2a5988218359252cc631c2ca8b0c871954672d0d510c322a9cc3a1485315c7644c832c4aa930e85196155498632cc6a3394a898863851516388510c1aa931e85196166454f2104322b18a390a41439d443d0932c1ca6b168320e0f6590d420cb13322a310841155d8538851091ae9b2a641954672d95310c706b20a71924185191534401094ae3b1a84214667694d210868b38ecaa18878599153c8621c4ca8b148390e1564151310c68ab9e8428a81295cb655044185aed2a46510e4462545300c3122a2c520a218398d5290440c8ac6294828842f7655332c8722a9cc5a0c839158e5290731c18a8b1e429062654586428860e3b2a898061515c64394a31
  | 1 => 0x4210262b9ec8908439198d5188420a4ce329a842160d6394b429061a3b2a888021235cc605084292ae23028621e455398742c86a2b948728c65891894154041c1aa831a401061665d0c414c71232242a8043255cf625044191cec21a859941d76953318c70bb24a8988639194d6190a218a8eca9a20085457290c514c252ba6ca908438315162cc530c2ca6b0e85216155398643d0b13312a320881235cf6150842a4ce521aa2206265458642ccb07322a51966391189315403186eecaa66310e0e6354a421022bbb2a7a0c438514d61d0d40c4ca8b0c6510c657614a3144322a9cc598c438355262d0f32c1cc6a9485a0e445358a31442323b2a488021519c7654c832c48a4b0e84a060d6494e3288722a94c319663199da5448421c1aa6312802060e65d0c424cb0629ac5a0a8107dd9548c830a4ae5a18a2a064653586328870ab24a718e43515c643149308ceeca968318d177550e410c712b20a518a21259d84350731c4aa93166318ca572d8d4110713322a598c63839516290e32a8ce3a1aa41861554987430c312322a2900418594d61d0e4298ae5b2a6218e1663546411021abb0a910a21459ce5250441c1aa83126018614644c5500c62b3b4a8988638555261d0f32c8ac428e629842f76553328cb07b24a899065195d85290510c8ac62944288624545864248306b24a790c439194d628c721c28a6b0e84a042d761523248312aa4c39946523dd94310a32c1ac82a2641952674cc9518cb12b10a3a0a8189951628c721c1ac8296649860e6454a310c20ebb0a998a61859516390731c8cc4a8c62184c572d91310c6873a6ca99065891895150040c4aa831220086255498b418c72229ac32124185191514c030a2ae7a14a32161654586438c712b20a510a21839516390b32c1aa93168798c4d7614f2148312aa4c3990418318d5250040c18c6a12a02162564147214828b3a887a0a638955262cc41094ae9b1a4210e245458a3144322a9cc3990418950861540428aeeca9e820844f7654f42c86933a6ca908438555261d0f31c8aa6312200861563147415032231aa2900419114961cc930c2aa931e8318e4532185500ca62b98c0908430b5da54c8621a2ee2a1ca221c4d7694f218862bbb2a790c43439cb6550c43c8cc6a96820852572d0e5190f06a1cc528887235d3614c832c2aa930c64184977650c418c7072a2c7214438550c6154043c2ca8b1c8390c8d74181320caa338ca899065255c76550c43c48a8b0c64906255498b410430ab20a718a218595161cca31c8aa7316620848d72d854310f0729ac5a1c838554e6190f41c28a8b1c828852571d0e5290e8b39ecaa08838359052cc530c1ec729a84216455398732c860ebb4a9994658398d429444298ae3b2a641960d6314b425030aaa4c790c43075d854cc93083aed2a665
  | 2 => 0x22370a87800230480004080580c00041a8000a00390080a020200044040c018e2040100400010e02802055d85c9a02000c81000600002c000021002000000c4a1b138040806048000032000000a1b0f2802c0a002204a05028004603060780049258045afe02858160701818be130006814010085800000e80804c13b9300e3900000242c0300c000100838c60a110fd2c120c2907a9401815fa00350780805a4ce529a8220e1654587328ca16bb0a990a418955261d082091ae43028621e0d5398a43d070629ac5a1a81499d332544208caed2948398c9573d954110712b20a8908430ddd954c8410a4ae3a18a4a060c5458a434c2a2b9c8528e65839913294432c1ac629682a041f7655232cc6a339686a8c87315c4604c832c4aa530c85a0e4553987420830aa9cc321081255d3624c431c1aa931e84106466354b418c70b322a318861131d95348020c1aa731487a162552986
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x80f87590544c83281787590544c431
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 830
  | 4 => 1423
  | 3 => 364
  | 2 => 2
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
  | 5 => 2*((h/276+packedAt s2K5 (22410+(h % 276)*10) 10) % 830)
  | 4 => 2*((h/488+packedAt s2K4 (54074+(h % 488)*11) 11) % 1423)
  | 3 => 2*((h/142+packedAt s2K3 (17836+(h % 142)*9) 9) % 364)
  | 2 => 2*((h/7+packedAt s2K2 (120+(h % 7)*1) 1) % 2)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffc0ffffffffffffffc3ffff
  | 1 => 0xfc1f03f83e07c0ffff1c1c1f0e0f87c3fd5293
  | 3 => 0xffe003ffc007ff03ffe01fe00ff007fc3e631c
  | 4 => 0x3fffff80003ffffe0000ffff8003f83e0
  | 5 => 0xfffffc0000000003fffffffff00000003ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4000008000000000000202100108040000425
  | 1 => 0xa946659194aa95d1cb0d0d1a268d168b9d5292
  | 3 => 0x30caaaa28d353456d56217484ba42738ae6318
  | 4 => 0xa294d34529a1a69b66b742108dce72113783c0
  | 5 => 0xc318e38631c638e3b8db9b9ce10844223bf800
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88eeaaaaaaaaaaaa88, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x20021000ed20bd43dd439d43ec21ee21ef20bf43de43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x3002000080c6a1a418d438871a8610d914520c6a1e418c5250f1ea4a1c755243
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x283d9543887054314520a19875250e0c6550d20
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s3K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/16+packedAt s3K3 (216+(h % 16)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s3K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffff83ffffff81fffe0ffff83ffffe71f1ff
  | 1 => 0xe0fc1ffc1f83fffe1c1ff0f07fc3c1ffae4e4f
  | 2 => 0xff001fffe003e1ffe01fff007ffc01c1cf8f8c
  | 4 => 0x1ffffffc01ffffe000007ffffe01f00ff0
  | 5 => 0xffffe000000001ffffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x40080088010000002022011108044444009095
  | 1 => 0x8a312910ca2550960d0c90a2324288b8a6464a
  | 2 => 0x465a5229474a832ae2172a055ca8150d4b8b8c
  | 4 => 0x94a39c429460d5cd5741888867333811f00d60
  | 5 => 0x18c31873187319f19b99ccce06222021fd6000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaea8888eaeaeaeaeaea8888eaeaeaeaeaea8888eaeaeaeaeaea8888eaeaeaeaeaea8888eaeaeaeaeaea8888eaeaeaeaeaea8888eaeaeaeaeaea8888, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x31110400000ee21ef20dd43ec219d43bd43ed20bf43de43
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3010180c6292871d5490f1a86906350c21c7a928764514831a87906350e21
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x44108319543483054314520a19875250e0f6550e21
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
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
  | 4 => 2*((h/17+packedAt s4K4 (144+(h % 17)*4) 4) % 9)
  | 3 => 2*((h/16+packedAt s4K3 (216+(h % 16)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s4K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fffff83ffffff81fffe0ffff83ffffe71f1ff
  | 1 => 0xe0fc1ffc1f83fffe1c1ff0f07fc3c1ffae4e4f
  | 2 => 0xff001fffe003e1ffe01fff007ffc01c1cf8f8c
  | 3 => 0x1ffffffc01ffffe000007ffffe01f00ff0
  | 5 => 0xffffe000000001ffffffffff80000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x40080088010000002022011108044444009095
  | 1 => 0x8a312910ca2550960d0c90a2324288b8a6464a
  | 2 => 0x465a5229474a832ae2172a055ca8150d4b8b8c
  | 3 => 0x94a39c429460d5cd5741888867333811f00d60
  | 5 => 0x18c31873187319f19b99ccce06222021fd6000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeaea88ea88eaeaeaeaea88ea88eaeaeaeaea88ea88eaeaeaeaea88ea88eaeaeaeaea88ea88eaeaeaeaea88ea88eaeaeaeaea88ea88eaeaeaeaea88ea88, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x10502000000000000bf43dd43ee21ef209d43ec21de43ed20bd43
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x600a00017c7a92878c5250e3aa921e350d20c6a1c438d43086c8a2906350f20
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc150c514828661d494383195434820f6550e21
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
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
  | 4 => 2*((h/17+packedAt s5K4 (144+(h % 17)*4) 4) % 9)
  | 3 => 2*((h/16+packedAt s5K3 (216+(h % 16)*3) 3) % 8)
  | 2 => 2*((h/1+packedAt s5K2 (152+(h % 1)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1fffff83ffffff81fffe0ffff83ffffe71f1ff
  | 1 => 0xe0fc1ffc1f83fffe1c1ff0f07fc3c1ffae4e4f
  | 2 => 0xff001fffe003e1ffe01fff007ffc01c1cf8f8c
  | 3 => 0x1ffffffc01ffffe000007ffffe01f00ff0
  | 4 => 0xffffe000000001ffffffffff80000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x40080088010000002022011108044444009095
  | 1 => 0x8a312910ca2550960d0c90a2324288b8a6464a
  | 2 => 0x465a5229474a832ae2172a055ca8150d4b8b8c
  | 3 => 0x94a39c429460d5cd5741888867333811f00d60
  | 4 => 0x18c31873187319f19b99ccce06222021fd6000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88eaeaea88, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def q5K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q5K4 : Nat → Nat
  | 0 => 0x800d004000008040000000000000098060fa43f887e18fe20f841f043f987f32fc63f443e907d30fc61f8cbe10fc30fe41f4c7f90ff10fc21f4cbf98fc32
  | _ => 0
def q5K3 : Nat → Nat
  | 0 => 0x114000100004008518090104000364000000000708004002750c10ad42042d90420af42442750c20b6410c2790c10af424c2b10910cd320cad50632ae42042d504309e43c86d90632d5310c6d90732ae420c27d0d209d43886d504209e43082d10530ae428c6b50830ae42cc6dd0530ac424c2d50732ad42cc67d0d109e43886750f21e521086dd05209c43442d10520ad428c6710d20
  | _ => 0
def q5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q5K5 (i*4) 4
  | 4 => packedAt q5K4 (i*15) 15
  | 3 => packedAt q5K3 (i*26) 26
  | _ => 0
def q5I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt q5K5 (4+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/29+packedAt q5K4 (360+(h % 29)*5) 5) % 24)
  | 3 => 2*((h/34+packedAt q5K3 (1014+(h % 34)*6) 6) % 39)
  | _ => 0
def q5Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 3 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 4 => 0xe6ff07cff81f8f1c
  | 5 => 0xf8fff80fffe00fe0
  | _ => 0
def q5Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffff4010000009040025
  | 3 => 0x2a264a4642496692
  | 4 => 0x1942d41a90932b18
  | 5 => 0x78486ad24c24dc0
  | _ => 0
def q5Atlas : Atlas := ⟨5,rawDecor 60 q5Pos q5Neg, 0xfff0f0f0f0f0f000fff0f0f0f0f0f000fff0f0f0f0f0f000fff0f0f0f0f0f000fff0f0f0f0f0f000fff0f0f0f0f0f000fff0f0f0f0f0f000fff0f0f0f0f0f000, q5N, q5R, (fun _ _ => 0), q5I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def q6K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x18045d32da657cca6996e32
  | _ => 0
def q6K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q6R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q6K4 (i*4) 4
  | 3 => packedAt q6K3 (i*15) 15
  | 2 => packedAt q6K2 (i*26) 26
  | _ => 0
def q6I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q6K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/8+packedAt q6K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q6K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q6Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 4 => 0xebf03f3f80fec3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q6Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 4 => 0x150aa0690a94c28
  | 5 => 0xe082ab24a14e80
  | _ => 0
def q6Atlas : Atlas := ⟨4,rawDecor 51 q6Pos q6Neg, 0xeeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def q7K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x10000c4d32dc65b4cae995f32
  | _ => 0
def q7K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q7K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q7K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q7Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 5 => 0xf3ffc03fff00fc0
  | _ => 0
def q7Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 5 => 0xe082ab24a14e80
  | _ => 0
def q7Atlas : Atlas := ⟨4,rawDecor 43 q7Pos q7Neg, 0xeeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88eeeeeeeeee88ee88, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x118006d32dc6574caf994d32
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => 2*((h/8+packedAt q8K3 (75+(h % 8)*3) 3) % 5)
  | 2 => 2*((h/1+packedAt q8K2 (26+(h % 1)*1) 1) % 1)
  | _ => 0
def q8Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 3 => 0xebf03f3f80fec3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def q8Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 3 => 0x150aa0690a94c28
  | 4 => 0xe082ab24a14e80
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 27 q8Pos q8Neg, 0xeeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88eeeeee88, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def q9K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x22236196d20de65bc83610ee21
  | _ => 0
def q9K2 : Nat → Nat
  | 0 => 0x40208e438869105208c43482990732
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 3 => 2*((h/9+packedAt q9K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q9K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q9Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffebfc79ffe387fe4f
  | 2 => 0x72ff81cffc070f8c
  | 5 => 0x7cfffe0ffff80ff0
  | _ => 0
def q9Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018100104912095
  | 1 => 0x142322862122c64a
  | 2 => 0xd49751b48546b8c
  | 5 => 0x38241ac92608d60
  | _ => 0
def q9Atlas : Atlas := ⟨4,rawDecor 39 q9Pos q9Neg, 0xeaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x1a00036196f20dc43bccb610ed20
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x8404a4414829907328e43886310d20
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 3 => 2*((h/9+packedAt q10K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q10K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q10Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffebfc79ffe387fe4f
  | 2 => 0x72ff81cffc070f8c
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def q10Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018100104912095
  | 1 => 0x142322862122c64a
  | 2 => 0xd49751b48546b8c
  | 4 => 0x38241ac92608d60
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 23 q10Pos q10Neg, 0xeaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888eaea8888, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x103610ed20dc43bc836196f32
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0xa441482390e21a641cca310d20
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
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
  | 2 => 2*((h/8+packedAt q11K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def q11Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffebfc79ffe387fe4f
  | 2 => 0x72ff81cffc070f8c
  | 3 => 0x7cfffe0ffff80ff0
  | _ => 0
def q11Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018100104912095
  | 1 => 0x142322862122c64a
  | 2 => 0xd49751b48546b8c
  | 3 => 0x38241ac92608d60
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 15 q11Pos q11Neg, 0xea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88ea88, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x4090202c8a008445007b88401fe53007f0c401fd30007f50001ff40007f15001fe41007f10c01fd53007f8c401fc51007f14c01ed20007fd4001fe54007fcc001ff43007f55001fe51007fd5001fd43007f90c01ff53007f54001fc41
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a800ff50d50057f842a1803fd654c001f6a9a4000bfd915005ff82121803ff1054c0fff0808600ffd8e4100ffca49801bfe6294435ff192a800ff44153007fec928857fe10d4c017eb068600ffc42540057cc92983ffe1014c01fea9a8000bfd9641057fca4a1803ff6394401ffb2c8206ff8ca51007bca718803ff10d50013f32c8600bfd9631005bcc7aa003ff10d0c017f3088605ff8ca41005fac898002fd6550039f7904a800bf58243007facb20802ff655002ffe080a814fbc8253057d842a1803ed4348001beaa4a2009f59643007faa89801bfe4294401fe88286009f59743007fa21aa07bef20d5001bea9aa000bf596410067aa82a002fd658c437ff084a800bf98654007fac6a8003fd10950016eb1ea800dfd5150097d842a9847fe4054c017f308a800dfd4e51007fa21a180ffe6254039f610ca800bf580540057ac9a9802fe61d4c3df610ea800ffc405409ff8212983bef20d0c017fb2a6000ffc4243067d84321802fd6010c33fe082a800ef55241097fe42a9803fd1090c01feaa46200bfd8d50007fecb18802fd60d4c01ffb1a8000bf58e510073a8621803ff648c401eea1c621dff8435402ff8c520803ed5388413ff0828611ff84153077d843a1803fd4394405ff292800cfbc82430067ea92a002bd6494c01eea1a6000fb50e21097de40a9803bd4350001fe880a800ff58e51005fac918803be5450035fe10aa800ff50553007fac898003dd534c017ff0848618fbc80540cffc20aa0035d5314c1bff0868609ff0814307ff8202986bff215502bfe086a600bf9875408ff840a9802fd6014c03ff2126000bfd9130007fe2129803bf43500017eb1c8200ff54e41005facaa181ffc1010c35f7902a804ff98a31027f8c518803ff1055031f6108a803ff189500a7d84329803fd6494401eea9c6200ff59231006faa8a8003fd1014c017fb1a8002ff18940007fec8a8002fd64944017f308a600ff4c554007fa2129803bd4390401f6aa24000ffc4353017fc64a0003ff1014c01bea9ca203ff8c9500bffc202a04bfe4254c01feb1c8200f790d30005bac72a002fe6190c01bfaa4a206ff18a51007facb18802fd654c001feb22a000bf58354057fe40a1813fe428c403fe3126000bf5825301ffc84a8003fd1010c0bff3148200ff545430057cc9a9817fe5290405ff3128010fb084530d7d842aa0037f5354013ff2828600bfd9231007fe2021807fe624c001fe886a608fbc804309ffc2129803de438c4017eb04a800ef9524104ff820a1802fe6194c25ff902a616fbc8353007feca980027e65d0c01deaa28000ff58d40007facaa006ffc109503bfe086a800ffd9130007bca698002de63950017f30e861affc8154007daa910803ff1050c01dfa1c820afbc8143057fe42a1803ff6354001ffb2a8000ff44154
  | 1 => 0x1128280803098020b03a00b8400816f01b80e0300050716870282802d9fa485030b188687596a0386820b1c8688098081018a000a1c011016200410898009138300038b8c93208309223780078035f5394c11f61088616fb0875308ff820a9843ef2014c25fe10aa619ff8c15406ff821a1813fe528c433fe1
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x66144254004ff764405405fcf2090d300057f7544353006ee21d9150006f51058e51085ec72c4053006be64c4253006bd64c4253005df7350553007ce2150d300079d6350e41006f66144053006be61551400067e1099643004fd7098454006ec2158e410066f2099743006ee21d91300deef20d9540006be1099253004ff76c43540077710d4e51005df734414312fac21551400073d64552510075d5344053127ac21d0d400067c6154d500eeef20d9150004ff7559130004fd75d8d40005bf7444153005bf74442541ff3c10d5254005ee7155221006ec2159641006bd6455231007b51095241004ff7058e51006ed6054e21004ff76c4343006ef2098453004fd7058e51006be61d0d400057f7550553006ec2158043006dd6344354007ae43551201d74f2054c53006f661c4243004ff70596410067c1059643006ef20986431e74c21d4e53006bd6450e5119f6c2154e51005ef735512018fac2155241085ec7244053007b7105524104fad4050d20006f510d92310073e4155150007ae2155140005bf7444054004fc71583540079e4150e310057f7544054004ff7059251004fe715913008fcf2054d3008def7054d2013f6c2154d500073e5155241006de6150d30056ee6150e2105eef20582430cdef7055120006f51059251006ef2098443006f510d9631004fe71d9130006be619514009eef20d9530006be41592310eeef2058354006af20592530eeed20d9150004fd7650e51006ec2198653005ee7155120006ee2158e41095ec72c4153006ec2198743006dc1098f54007771055251006ac2159253137ac219514004fcd3050d200073f54c4254006e42198653007b710d0e41006ef20d9641007d71050e31006e42198743006bc6150d40004ff76c4253005df73440540076e53552210079f6450d300067e109974306eed20d8d40004fc71d9130006ef20987530057f75441540067e65c4243004fc7158343004ff76442530077710d5251004ff76c435305eed20d91300057f7544343004ff73596410075f6354d500069d43984430053d75d0d40006de6344354065ec72c4243006f710592310067d5059631006be42d91500067e65c4343005df73443540067e5159631006cf2098f5404f9d4050d30004fc715825406eef20d8d40004fc71d9540006de31d8d501ff3e10d52541cf5c1054c53006f71059631167cc2190e3116fcc2154e310076e2154d500edbf7459540005bf744414307dde7694d30005df73441540079d6450e310075f6554d30004ff73595400076e5154e21006f66144043004ff764c554006ed6050e210066f2059743007af5450e210057f75440430067d6054e51006ec2158054006ef209875405ebd40d913004faf2050d4017fac2150e41006dc1098e54006ac2159353006f710d9631006df6350d50
  | 1 => 0x95400e5ec72c42540ef6f20d5150006bf74595400073e5155140004fe71d9540006be4259231005ec7154d20006bd4059231005ec7150e21007d71054e31004fc7158054007cf5350e2104def7050d2015fcf2050e31004fc7159130006be6444253006f661442430cded7055120004fe7650d500cf6f20551501a76f20d4e51004ff76c4043004fe71595400055d7590e31187af20d0e411b76f20d5251004fc71d8d50004fc71582531af6f20552510067f7559631006dd3058e51006f661c43430067c1099643005ec71551200076e5454d20005ee7150d200067c1099743007d71090e310066f20996430057f75441531bf9e1050c43007771054e51004ff7058e41006f661c4253006ef2059231006cc2198f54005bf74545432072f20d5254006bd64c43531df5e10d4e53007b51055241006be6150d40006ef2059631006dc6150d30006de6190d30006f510596310067d5059641006be10592530075e3154d50006ec21d9150005df7344153006cf2058e540af6f20d4d5011fac2150d40007ce2154d30005ee7154d20007d51050e31004fd7098653006ed2059251005bd7550d40006de3258e510063d5458054007b510d0e41004fd74d8d500ceef20595400e5ec7244254006bd74d9641004ff76441530057f7544143006ec2198753005ef7054e210067e6155150006ef2058e510067e61d5150005dd73d92310067d60d5251004ff7459631004fd7058e41006be10993530067e52d9540006e421987530a5ec72c4253005ec7150d20006cf2058f54006ef2059251006ec21d8d400deed20d9540006be10593530066c2159643006ec2198454007cf5350d20004ff7644353004fe71d8d50006be64443530ffcc2150d3009eef20582530deef20582540053d74d4d500067e52d9530006ef20595430066c2159743005dd7550d30006cc2198e540067e6544343007b71050e41006be64c43530067d6554e411ef3e1055054006dd73d9631007ae2150d40006bd40592510059d7395241004fd7059231004ff76c4254006ec21d9130006be42592510073f5444254004fc71d8d40007751055251006de6154d30006f51059231004fd7098753004fd7654e41006f710596410073d54c40540067d60d4e51006dd6050e31197af2095241004fd74d9530006dc1058f54006df7359130004ff76443430079d43c40430053d74d4e51004fc71d9530004fc71580530067f75595400057f7544354006ef20d9231005ef7055221006de1058e54096ee6154e21006ef725954308fcd3054d200077510d4e510067e5159641006ef20d9631005ef7355221006ee21d8d40004fc7158353006ef209865409eed20d95300059d7494e31006de1098e54004fd70d9231006f661c4254006ec2158053007ae43552210075e5154e310067e61d4d50006f
  | 2 => 0xf5ec72443541ef3c1055054006ec7259543006de1098f54006cc2158f54004fd70592510076e21551500b5ec72c43530075f5344253005dd7690e31007751054e51004fc71582430c5ec72c40540d5ec72c4154006bf64551300079f6350d40006bd60d0e41007d71094e310aeed20d8d50167cf2090e31006ec6150d20006ec2159540004fc715953017faf2050e410059d73951400063d5498454007ce3150d20006ec21595430067e6154d50006ec21d92310067e10596430079e4150d30006ee21592310057f7544053006f661c4353004ff7059231006bc10593530dfaf2095140005dd7694e31006ee2159631006ec2159251075ec72c4343006af2099253004ff7458e510067d65c4343006af2059353006bd6444253004ff7459530006dc6190d30006f66144253005df7344053006ec21d95400067d65c4243007cf4354e21006de6194d30006be41d9130006de32d8d50006ec2158254006f661443431bf9c1050c43007ae4155120004fd70d9641006f661c4354004fd70596410aeef20d8d501c78f2050c4316fcf2054e31006ee2158e510067d60552510067e10597431f72f205505404eef205913008eef20595300065d53580530073f6455150045ec72c40430cf6d5055120005bf7444243006dc6154d300067e52596310d5ec724c554004ff76505531d74c2154c530beef205805406eef20583430b5ec7244353006df6354d40004ff7359251005ec7154e21006de63c4254006f710d96410057d76d52510c5ec7244054006ec21d96410076e5155120005ef7050e21006bd6444353004fc71580430ceef6055120005bd7695241006ee21595400d5ec72441540067f7559641006dd63c4254005ed7550e21004ff7558e41007d51090e31075ec7244343006bc10992530addf7359530107cc2190d30005bf7444253004ff7644354006ec2198453004ff76c4053005ec7155221177cc2194e31007d51054e31006ec2198654006ed2059231005bf74440530076e5454e21006f661c4054007b51050e41006bd6095241004ff7644243006ec2198754006ed2059631006ee2159251006e42198654006af2099353006dd6090e310077510d52510067e6544243005ee7154e210057f754c5540aeef2058353006e42198754006f510596410079e3150d40005ee7150e210067f75595300057f7544243006dd6344254004fd7098743006bc1099353006ee21d9530006dd6354e41006ec6155120006f71058e410073d5444054007cf4354d20005ed7550d200cf3d5055140006de31d8d40006ec2158243004fd74d963110fcc2154d300bd7e76d5150045ec72440430067f655513009fcf2094d30005df7344243006ed2058e51006ec2198443004fd7098654006dd6054e3118faf2055241006ec21d9530004ff7654543006ee21d
  | 3 => 0xd70986430d6ee6155221006de1058f540075f53c4253005bd74d9641006dd63c4354006cf2098e54005ef7550e21007b71095241004fd75d91300067d6544343006bf6450d50004ff7644043006f710d9231006ee2159130004ff7559231007ae4150e21006bc6155140004ff76c4054006bd6050e41006ec21d8d5008f6d5054d20004fd70d9631004fd73d9641006f7105925108eef6054d200a5ec7244253005bf744c554006dc6194d300076e5154d20006ee21595300057d76d4e51006bc61d0d400067c61d51500057f7544254095ec7244153004fd75d9231004fe71d9530055ec7254543005df73442540073d655524107eef2058053006de3258e41006dd73d9231006f661c40530043f7655054006df7359530006ee2159641005dd73d9631007ce3154e21005bf7444354004fe71d915015fcc2150e310067c615515003eef20580430073f6555140005bf7444154006ec21592310067f6554d40006ef2058e41095ec72505531af6c2155251006f51058e410065d5398453006bf7459231005ef7454d20006ed6055221004fe7654d40006f66144354007af5450d200067d6544243007d51094e310de7d50d95400cfaf2055140005bf7444343117cc2194d30055ec72c41431476c21d4d50005bf7444353006f510d96410075d6354e51006ef2059641006ec2158353006ef2098454006ee21d8d500067d5259543004fc7159543006de6344254006ac2199353004fe71d8d40004fd7098453005bf74440430066c219974314f6c2155150006ef2098653006dd6350e51007ae4150d200067e5259641005dd7550e31004ff7644053006dd6094e310067e51d9540004fd765513006faf20d0d40004fd73d9150005ef7550d200075d6554e310053d75d0e4108f5d5054d30187ac21d0e41006ec6154d20006f661c40431b76c21d5251006bd425954309e7d50d9530006bc61951400059d7494d3008f6f2054d501df5c10d4e530069d43580430066c2199643005df7344253004fe71595300075e5154d300076e515522104eef6050d200057f754425319f6f2054e511e74f20d4e53006ec2198643055ec7244143006ed2059641006bc1059253004fd7059631006ec21596311cf5e1054c530067d65552310045f7654c530067e51d9530006ef2098743006e42198643004fd7098443007ce3154d20004ff7059631005df7354543006dc1058e5404ded7050d200f5ec72c4354006be41d9150004fe7655130004ff7059543006ec2158253006bd605524103dbe76d0d40007ae415522108ded7054d20006f661440540075d53c4053004fc7159540006bf74591300079d4344043007ce3150e21004ff76c4243004fd7655231006dd32595431a76c21d4e51197ac2195241006ec2158e51006de63c4354006ec2158354006ec21d9631
  | 4 => 0x440820a0000654501401000970044b08c010401008c039509801121014040286300c4b05833005ec00029020080142d8d44e00c2b04000008260003878808000070a0120a0002d04409000004a133a4511835030110002d0000200000050000084000c000003d00002054020000219c88014219600a0263e01400078000e00301824020351c8270640c0041625809034050001701001134010100804c00154000000f3580007412164ac13c1106828308080d4133189b0800900d433884706c000247328c0102c000c81f02c01000a53d424048980041700c030302b244340002205400248020a4050c843000160904b0209c02804044040000a02c041dc1504005034000001a0000326c0f05000008ed0643506c160646602800144030b00f000092802a00023000000157f02c061c00e0941401c0020c060cfad4055120006de32d8d40005bd7550e41004fe7655231005ef7454e2106ddf7359130006f71058e51004fd70987540067c1059743006ed2058e41006be42d9130005df7344343004fc71d91500055d7590d30004ff76441430bdbe76951400076e5355120004fd73d95402072c21d5254004ff7644154006cc2158e54004ff76442541c78c2150c430057d7550d50005df734435304fcf2050d301f72c215505403dde7690d30006ec2159130006ec2158343177cf2094e31065ec72442430055d73d5150006f66144353006ac2199253005df73440430055d73d5251006ec21595301576c21d5150006dd3058e4107d7e76d4d50005bd76d0e410066f205964305eef20d91300057d7550e510067c61d4d50004f
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9d74186534c001d8b0610cc3218034b08574d4d500051ec24a3b2a8000e2c541c96550c79a98e5a9e21298021f61b75443430069abaa21a1c82008df835c261950019c8e530a21a9802aba0a10992530064eb26e6884a600c3e10dd95415001c9b07902cb218034bc8175d0e410053741420b2c86008bd841c76354001d4b0810cc3a18eb531c953440530043fc2ae130c8600ce4710856014c0117b0e082c9a98022f61071d95300062ea9ae1308a647e4e54c8163d5001a98a6baa8710803175ce61d5150006a629aeaa1a4040d2c72d5310950015d30010ec6a8003391ca614425400726c2e40b1ea800c3d541c560150019aee730a21a98030f5d160d4e510043ec382132c8600d2f749515348001d886210ac728802a760c10592530071aaa4c2880a800a5f8654f1014c01d884230a8698002976141098f540071aaa4c3880a800a6e828426590c010fd0f32a212192393d0c21596430064eba2c129c6200d957344254904014db0010ccba1803a950c21987541fe1fbaee8b2a8000c3f765511015001a6aeb8868720803a310c21595430063bbacc2884a600c5d731875454001d4ca810cc3218034bdd25454e2100666394c7884a80087d851c56090c019c8e230aa8900029760c10597430072aa9cc2880a600ea5540866190c011e902bb2a898002ab6002159253005674142131ca800a5e868c55354001c98a7b92caa1802b36002158e5400574c0042b2a80008bf845c26194c01b1e40ba4a6980028f61010596430061e086ecaa0a800e95439851010c019c8e530a21a180317dd953c40530046f43cc6884a800ae980087655000117b0e084c9a9803391ca61443540054ec202131ea800c3f76d511095001a5842bae87208038bdd4215935300566c0042b1ea800ce4729851090c01b1842b9ca9208021fe157059231005674102131ea800a9d8304264d4c01b2ae8884a7188032750c715804300717ba042b2e860093e87d51109500193cc9b9a21a98029b6002159743007162a640b2a8642f0c43951534800193ee8b1a21aa003b160c2198653006cab9e212a48239e4f2054d6014c01d884230c86980024f613754425426747aa042b1ca80087d851c560d0c011bb0db9a212a00237e0d705925100726a9843308a600e55539871014c01a6ae8886a7288039908461551500069610aeba1a8000a3d8504164d4c014dd04084cba18031b1ca65442430061eb2ee888686008dd8704263d5001a58a8baa869000237e0d7059641006a7902e7aa4a2008bd870426494c0193ee8b1a212a002ab60021993530074aa1cc38808600e8d430866110c01b1842b9ca8a000267a1d43440430055741021324a600cac7259110d4c014bd0d28aa698113c31535350e2100732a984330ca800e65540866194c01c9b0610acb21917c310e5454e21
  | 1 => 0xaea30e86a00029760c10596430062f32ee68848600a9d8404163d500147b0b20ec8a80021f61c105974300672394c3886a8009e9801c55448001ccb0a10cc3aa002b960021986530064eb98c32a28000e8d840856395001d1b0610ac929802976141058f540054ec1821324a600ae9800856010c01c58a810acaa18028fa1a515514000672394c38848600ae980085654c00193cc9b9a212980347d5373442540052ec2820b1ca800c4f20dd95314c01c9eeb902c7aa0029760c10996430046f43ac6884a844f0c53d514388487e188729aa8900028f61010597430062ebaac121c6200cac725911094c01958e532621298030f5977444243006a7b9ca6aa44200ace8204163950014db0010ccb218021fe1570987430054ec2020b1ca800ccc7258d10d5001a5e40ba6a728803a908461951400074621e40b2a863ed2c7255110150015d30010ac12a0022f61c105925300574c0042b06a800aae8204264d4c019c8e210ac02a00353dd75350e210061fbaac8884a6008dd831c5609500185e41bb2a82a003b10846194d30006a629ee8a9a4000c9f7498d109500155d03902c92991bc310e535522100666394c7886a800d4c215cf549440155b0010cc92992b8b94c21593530055741020b26a6008be8799110d4c01d484230a86a00022f61071582530067238842b2a6000c3e65dd11090c014bb0b18ec6a80038b6142159353006c621aeaa1a4000d4c215d6438c401c98a6392caa18022f61b74442530056740e40b1ea800c6c7259510d0c01d484230aa8a00032b1c964c4353006a629ee8a9c4200c2c21dd9541500159d05084c7aa003555cf10d52511c6c639287880863de2f2055160150012bd0fa9a21298028fa1a41551500062ea98e2b00a600ccc7258d10950018beeab1a212a12b8b90c215974300746c2640b1ca800acd80086639500153d0d18a86a0003a3dcf20592530068fba6a6884a600cac7299110d4c018d8e532e21a192fa3d4f20592530055741420b26a600d8c435d54388401d1a8610ac0218022fe1170596310061eaa2e1308a800c9d435c26110c011bb0638ac1aa003a310f72595430061fbacc8886a600e4c53c816550c0147b08084cba18031759773443430053740e40b2e8600d5575c42438c4012bd0ea9a20298039314c21595430054ec1c20b24a600c3f76553101500127d0eaa2202a0022fa1d64443530043ec3820b2c8600ce4729871094c0159d03902c72a002ba600215805300727b9842b2c8600d4f205cf545400187aeb30e86a00021fa1e654434300636394cb884860087d851c763500014bf0ca9a2029803275ce61951400055740e41326a600a5d8584163d50015d30010ac898003391ca61c425400636392cb8848600ea441085648c401d484230e86a0003a360f20592530068fba2a6880a600
  | 2 => 0xc71d95400053740e40b2c8600ce471185534808fc9e87902cb218038b61320597430056741420b1ea842f0c54d0d53480011d90cbaa86900029ba0a10597432378629c86aa44200a3d850416494c01d1ee610ac929803331c963c4254004f4c00e2a1a4000cac7299310d4c019aee730a21a18021f61b7544243006aabaa2121c6200cac729911094c018eeeb30a212a0034bc8174d4d50007632184330ea600a3d8584164d4c014bb0728eca98002976141098e5400574c0042b04a600ccc7298d10950014dd03904cb218028fe19544405422f862a686a9c4200e8d43c826110c75a98e4a9e20299034b1cb54442540043ec382132e863cd4c72d4d1094c0187eeb3222129802aba0a10993530062f086eca98a60087e875951090c0193ac9b9a21a98039908461d4d5000717ba640b2e8600ae9800856015001ccea810cc3298032ddd261442430067238842b008600cb77498510d5001a9842b9ea8a8003391c421595400043f43aca8868600ace81c8263950015d30010ec6a00039914421596410067238842b226000aae820416494c015cb0010cc321802ba60021d91500062eb9ac1aa4a200a3d849456590401aaae6886a9288039961421987530045f43cc8884a600e4f73c816590c018beeab1a21aa0039914421596310054ec2420b1ca800c3d7498753540019c8e530e21a98036310f7550d200064fbb2868808600d2c54dcd54884014bb07082cb21803170437654c530062fbacc6884a800aae81c826494c0153b06082c9a98034b153735512000733a984330ca800e4d530856014c015d30010ac1218038b55320984540075220842b24a2008dd86dcd10d5097d1ea9902c72a0028fe1954c40540061eba0c3a9aa00095d83dd51094c01c5eeb902c9a98039908461d51500046ec18e3b22a03bc5f75dcd654c00187ccbba221a18038b61720593530062f32ee68868637e8f2050d6010c01d1ee810ac72a002b36002198f540052ec182132e8600d8c43dd54388401d8ca610cc3a1923939502158f540053741020b2e8600ae580086619500193ee931a21aa0023ba1c215954300726a9e41308a600aad8008564d4c01b1e40b9ca9208038b55021984540051ec2420b2e8600c5d65dcd1090c0127b0bba221aa002b3a081058f540062eba8c321a6000d2f205d743500014dd05084cba1802ba60021d913000746218e4b2a8600d4f75d4d434807da58e4aa6202a00237a1e634435400574c0043b2a60008ef865d54388471b18e4a1a2021803b154c21987430064eba4c329a6000a5d83945658c4015d30010ac1a980353c817590d30006c7902e72a28000d4f7394d5448001d886210ac720907c314f5450d20006c610ae929a6000d8f205d2538c4014db0010acb21803391ca61c43430051ec2821326a600c9f7650f1010c0187
  | 3 => 0x740ecc0c84006290a000031d00118000b04038060c060442824018c02a00048c40e040c00c0c3300000681900014469b1c000148305048242b018003a0501a6c020e0783c00222d8180e080582c0221179e40a00008011c05002407a02088220a0105808002200074103305004b0450081800173b49c0341021ac1a9c5e80c02270803e480209098124100014800f251a0009b1187d68030000464f80580c1e811d0088e22170000447099e80a30002342c040b898d400ccc7298d10d50015cb0010cc3a1802aba0a105925320f862a6a6a1a40008bf845c261d4c015cb0010cc3a9933a3d4c21592530068fbaa868808649e2e43c8165d0c01d4b0810cc32a00237a1d63443540062fbacc6886a800d2c545d54388493c5ca7902c9a98030fdd5644435300762108c2a9a6000d8c215d2538c4019c8e530a21298022f61b74443530062610eeca98a600c5d75986434c0014dd04082cb21803655d31094e310051ec2821324a600c5f7654d1014c011bb0e082c7aa003530857590d300043fc2ae0b1c8200aae81c8164d4c0187aeab0687208032b1c964c42530046ec3820b1ca800c6c7299510d0c012bb0bb9a21a9803275cd60952410056740e4131ea800d2c215d35394401998e4b1e21aa002b3a0a1058e540069aba621a9ca200e2c54dc96550c014dd04084cb218027a6007154d200045fc22e0b1ca200c5f76d4d1094c01c9eea10ac7aa002a76101098e5400697baea8a1a4000a3d840426590c01d8a8610cc3a9803990846154d500047743e40b2a8600e4d8508563d50011bb0e084c72a003a3dd32058e5400574c0042b068600d2f75d5143884019c8e230a86900022fa1d644425300572c004330ea800a9e86905434c001a3aa9b9a202a00353c817590e3100753a184330ea800e2d8408565d0c018d8e4b2e21a18038b550215805400636392ca8848600a6e81c8265d0c010fb0a38ec89800237e0d7098754005674102131ca843f0c5390d544800117b0838ac1a98023760
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40105d96a1d53440530050ba5c54c816550c9560e93dd4215935326583a57730856494c0181f86dd153440532944b66054dcd548840144e9714f205954300703a1320dd95314c0166190084615515000591a47730856590c0141f9655373440540051364021dd95314c0144e920437654c5324d83a4f75c8164d4c01a295460021580540058325443dc96550c0184c8614d7550d200040fa5f8655110150018e07160021595300045366375d4d434800142e9284376550540070361021dd95314c8b50e9414f7454e21006381c58008560150016c1900846194d30007115cc211875454001c857308461951400044b66375d5143480018e07160021591300071154c710856014c01c0d84c837654c530060b218545d5434809160e94dd42158f540070360c21dd9541500142e97150725954326c6366043dd54348001c257508461d0d400070960421dd9541509760e95dcf20592530071160421dd95314c01c85431c4215804300552640215cf545400144e9714c725954300562640215d2534c09f12d9815373551200069254d800856014ca314d9814f7454e210070955071085601500184c72e1953c4053005a16525308661d0c8950e9510f7550e210050ba4810dd954150016c1900846154d300060b1cb86551101500142d90087765505400513a4720dd95314c8550e9414f7454d20005b064021186434c00184c72e19534405300623e18435d5438840105d980437654c5323543254435d543884016619008461d5150006381c5800856014c0141d940437654c5300589a477408565d0c0164593d502198653005a164e540866190c9360e93dd3205974325583a4f7408565d0c9560c9510c215954300589a477508564d4c0142e97153725954300513a5c53dc96550c8f60e94dd72058f54006a250d800856010c01549900857590d3024d8325443c816550c016a19008461d0d4023543a4c54dcd548849d14d9814f7454d200060b1cb86553101500103d96a1d544405400703a1021dd95314c01c0d83c837655054005a8640211855450001c85740846194d300040f66010dd9541508350e9510f7550d200050ba4720dd954150018e0716002158043007095d021187535400188c8610d7550d2000562640215ce5450001c46810877654c5300598640211875354001661900846154d5024583a53730856590c015299008575d0d4000703a0c21dd954150015299008574d4d5000583254431c96550c0114d98dd75350e2121d43254435d5434800141d93043765505423d83a5373c816590c016a190084619514000703a0f20dd9541500184f8614d7550e21005a864021185435000142e971502159543006381c580085655000144e928437654c53005b064021185434c08750e93153735512000709a0421dd95415001c45750846190d30
  | 1 => 0x4002001c000002c0045800180000000000040000088005120010000983800e201060e0598162040000000a02721038022045820e20000002c0800000009000020300000000008000018550000000030004000040009000080280044b66375d51438849960e95dd02158e5425d83a5774c81639500105e97e1953440532846366043dd5438840144e9714c21595430060be18545d54388
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2000000000000010004c72420110000d105cd9008461d515000481d4e4a887b92caa180380583a0421dd95415001c10aa0e2c0042b00a800e01612810877654c53006842e8c804230ea6a80034417564021186434c0018064a90c21aeaa1a4000e1054c71600215805300441b504a886392caa180220ea825443dc96550c012075392a218e4b2a8600e2050c7160021580430060192bc3086baa87108034817464021186534c001a40b9b20108c32a28000d085d59008461d0d40
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4206b1aa09510f725954300400dba2548610d7550d2000400dba2578610d7550e21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x9cb
  | 2 => 0xa0b
  | 3 => 0xa4b
  | 4 => 0x144b
  | 5 => 0x148b
  | 6 => 0x14cb
  | 7 => 0x589
  | 8 => 0x58b
  | 9 => 0xe89
  | 10 => 0xe8b
  | 11 => 0x1789
  | 12 => 0x178b
  | 13 => 0x18c9
  | 14 => 0x18cb
  | 15 => 0x5c9
  | 16 => 0x5cb
  | 17 => 0xec9
  | 18 => 0xecb
  | 19 => 0x17c9
  | 20 => 0x17cb
  | 21 => 0x1a49
  | 22 => 0x1a4b
  | 23 => 0x749
  | 24 => 0x74b
  | 25 => 0x1049
  | 26 => 0x104b
  | 27 => 0x1949
  | 28 => 0x194b
  | 29 => 0x1a89
  | 30 => 0x1a8b
  | 31 => 0xe89d3
  | 32 => 0x1789d3
  | 33 => 0xec9d3
  | 34 => 0x17c9d3
  | 35 => 0xe8a13
  | 36 => 0x18ca13
  | 37 => 0x104a13
  | 38 => 0x194a13
  | 39 => 0xeca53
  | 40 => 0x1a4a53
  | 41 => 0x104a53
  | 42 => 0x1a8a53
  | 43 => 0xe9453
  | 44 => 0x179453
  | 45 => 0xed453
  | 46 => 0x17d453
  | 47 => 0xe9493
  | 48 => 0x18d493
  | 49 => 0x105493
  | 50 => 0x195493
  | 51 => 0xed4d3
  | 52 => 0x1a54d3
  | 53 => 0x1054d3
  | 54 => 0x1a94d3
  | 55 => 0xe8591
  | 56 => 0xe8593
  | 57 => 0xec5d1
  | 58 => 0xec5d3
  | 59 => 0x1a57d1
  | 60 => 0x1a57d3
  | 61 => 0x104751
  | 62 => 0x104753
  | 63 => 0x1a9951
  | 64 => 0x1a9953
  | 65 => 0xe8996
  | 66 => 0xec995
  | 67 => 0x104994
  | 68 => 0xe9416
  | 69 => 0xed415
  | 70 => 0x105414
  | 71 => 0x150ed5
  | 72 => 0x20ed5
  | 73 => 0x151054
  | 74 => 0x21054
  | 75 => 0x150e96
  | 76 => 0x20e96
  | 77 => 0x98e96
  | 78 => 0x98ed5
  | 79 => 0x99054
  | 80 => 0x140e96
  | 81 => 0x140ed5
  | 82 => 0x141054
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 26
  | 7 => 231
  | 6 => 729
  | 5 => 491
  | 4 => 124
  | 3 => 17
  | 2 => 3
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
  | 8 => 2*((h/15+packedAt gbK8 (676+(h % 15)*5) 5) % 26)
  | 7 => 2*((h/77+packedAt gbK7 (8547+(h % 77)*8) 8) % 231)
  | 6 => 2*((h/250+packedAt gbK6 (34992+(h % 250)*10) 10) % 729)
  | 5 => 2*((h/163+packedAt gbK5 (28969+(h % 163)*9) 9) % 491)
  | 4 => 2*((h/104+packedAt gbK4 (8680+(h % 104)*7) 7) % 124)
  | 3 => 2*((h/26+packedAt gbK3 (1377+(h % 26)*5) 5) % 17)
  | 2 => 2*((h/8+packedAt gbK2 (276+(h % 8)*2) 2) % 3)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffc07fffe03ffffc07fffffd09ce3e71f1ff
  | 1 => 0x7c0ff8381ffc1f03ff83e07fef6b5c9ae4e4f
  | 2 => 0xf800fffc01fffe003fffc007030739f1cf8f8c
  | 3 => 0xfffffe0000003ffffff803f83e01f00ff0
  | 4 => 0xffffffffffffc000000003ffc001fff000
  | 5 => 0xffff0000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8420004022002108400421108000012009095
  | 1 => 0x684458190ca41a119483422f07294c8a6464a
  | 2 => 0xd00aaadc2174b402ae9680541b0529714b8b8c
  | 3 => 0x4210f36af406108433e739e023b83e01f00d60
  | 4 => 0x8420fc73799f39cf00c2108043dfc001fd6000
  | 5 => 0xe73c2040401821080304210083efffac000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 7, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 8, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 6, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 6, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 6, 0, gbRaw),(0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444, 6, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 5, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_36725
namespace PEqualNP.Outside.L_meta_36725
open PEqualNP.Outside.L_meta_36725.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 19 := block_range (n:=19) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 19 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 144 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := bs0_5_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 2 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_96 : Interval s2Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_192 : Interval s2Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_288 : Interval s2Atlas 3 288 76 := block_range (n:=76) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 364 := (concat (concat bs2_3_0 bs2_3_96) (concat bs2_3_192 bs2_3_288))
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
theorem bs2_4_384 : Interval s2Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_864 : Interval s2Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_960 : Interval s2Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1056 : Interval s2Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1152 : Interval s2Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1248 : Interval s2Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_1344 : Interval s2Atlas 4 1344 79 := block_range (n:=79) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1423 := (concat (concat (concat bs2_4_0 (concat bs2_4_96 bs2_4_192)) (concat (concat bs2_4_288 bs2_4_384) (concat bs2_4_480 bs2_4_576))) (concat (concat (concat bs2_4_672 bs2_4_768) (concat bs2_4_864 bs2_4_960)) (concat (concat bs2_4_1056 bs2_4_1152) (concat bs2_4_1248 bs2_4_1344))))
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
theorem bs2_5_576 : Interval s2Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 62 := block_range (n:=62) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 830 := (concat (concat (concat bs2_5_0 bs2_5_96) (concat bs2_5_192 bs2_5_288)) (concat (concat bs2_5_384 bs2_5_480) (concat bs2_5_576 (concat bs2_5_672 bs2_5_768))))
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 9 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 9 := bs4_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 8 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 9 := bs5_4_0
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
theorem bq5_3_0 : Interval q5Atlas 3 0 39 := block_range (n:=39) (by decide +kernel)
theorem allq5_3 : Interval q5Atlas 3 0 39 := bq5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_4_0 : Interval q5Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq5_4 : Interval q5Atlas 4 0 24 := bq5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_5_0 : Interval q5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq5_5 : Interval q5Atlas 5 0 1 := bq5_5_0
theorem allq5 : ∀ k ≤ 5, ∀ i < count q5Atlas k, checkRow q5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq5_3 i (by omega) hi
  · exact allq5_4 i (by omega) hi
  · exact allq5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_2_0 : Interval q6Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_2 : Interval q6Atlas 2 0 1 := bq6_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_3_0 : Interval q6Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq6_3 : Interval q6Atlas 3 0 5 := bq6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_4_0 : Interval q6Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_4 : Interval q6Atlas 4 0 1 := bq6_4_0
theorem allq6 : ∀ k ≤ 4, ∀ i < count q6Atlas k, checkRow q6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq6_2 i (by omega) hi
  · exact allq6_3 i (by omega) hi
  · exact allq6_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_2_0 : Interval q7Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_2 : Interval q7Atlas 2 0 1 := bq7_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 5 := bq7_3_0
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
theorem bq8_2_0 : Interval q8Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq8_2 : Interval q8Atlas 2 0 1 := bq8_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_3_0 : Interval q8Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq8_3 : Interval q8Atlas 3 0 5 := bq8_3_0
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
theorem bq9_2_0 : Interval q9Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq9_2 : Interval q9Atlas 2 0 4 := bq9_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_3_0 : Interval q9Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq9_3 : Interval q9Atlas 3 0 6 := bq9_3_0
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
theorem bq10_2_0 : Interval q10Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq10_2 : Interval q10Atlas 2 0 4 := bq10_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_3_0 : Interval q10Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq10_3 : Interval q10Atlas 3 0 6 := bq10_3_0
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
theorem bq11_2_0 : Interval q11Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq11_2 : Interval q11Atlas 2 0 4 := bq11_2_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 3 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 17 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 124 := (concat bgb_4_0 bgb_4_96)
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
theorem bgb_5_480 : Interval gbAtlas 5 480 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 491 := (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480)))
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
theorem bgb_6_672 : Interval gbAtlas 6 672 57 := block_range (n:=57) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 729 := (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 bgb_6_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 39 := block_range (n:=39) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 231 := (concat bgb_7_0 (concat bgb_7_96 bgb_7_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 26 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq5 (cert : Complete q5Atlas) : Lower true (roots q5Atlas) (target q5Atlas) 6 := by
  have ready : Ready q5Atlas (asRow q5Pos) (asRow q5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 5 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 5 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 5 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 34, 38),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88eeeaeaeaeaeaea88
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq5 : Complete q5Atlas) (certq6 : Complete q6Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555 : Sig) 7 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 8 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 6 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff : Sig) 6 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 6 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444 : Sig) 6 :=
    slice_correct (ms:=fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq5 certq5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 8 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 4) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff : Sig) 5 :=
    slice_correct (ms:=fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 5 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 5 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372970 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36725.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,1]⟩,⟨.or,[3,6]⟩,⟨.and,[1,2]⟩,⟨.or,[0,8]⟩,⟨.and,[1,4]⟩,⟨.or,[4,5]⟩,⟨.and,[5,7]⟩,⟨.or,[7,11]⟩,⟨.and,[10,12]⟩,⟨.or,[9,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36725

open PEqualNP.Outside.L_meta_36725 in
theorem PEqualNP.Outside.L_meta_36725 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 3941264008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq5 allq6 allq7 allq8 allq9 allq10 allq11 allgb)
