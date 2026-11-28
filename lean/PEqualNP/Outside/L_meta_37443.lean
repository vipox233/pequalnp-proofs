import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37443.Model
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


end PEqualNP.Outside.L_meta_37443.Model

namespace PEqualNP.Outside.L_meta_37443
open PEqualNP.Outside.L_meta_37443.Model
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

def SBf (j : Nat) : Nat := [7, 4, 7, 4, 8, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 84]

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

end PEqualNP.Outside.L_meta_37443

namespace PEqualNP.Outside.L_meta_37443
open PEqualNP.Outside.L_meta_37443.Model
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
end PEqualNP.Outside.L_meta_37443
namespace PEqualNP.Outside.L_meta_37443
open PEqualNP.Outside.L_meta_37443.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37443
namespace PEqualNP.Outside.L_meta_37443
open PEqualNP.Outside.L_meta_37443.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x5c354a1301400008000250024a00106c1263e28012347401300000005aa00070000000000088b18ac72a2abc027405c19038b0c8f4888b1e028c00600067c000000008702000110630a02ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30fd30fc30ff20fb20fe20fd20fc20f820ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x210c05e8f00000000000000000b11800ae002780000003c1151889250ac000000000ec1639000d6151f0009600439207e0d33000000a000002e1f000382207150000a0000000005d001a4f81a009b800500a0651400000004e6a00104005b2f0006a313d03cee6237894860000018400400000000004800ac4600000000000000ce1b00000520012000427b001c10c00248006c00420a00000001c400440e8480013001a000003a9f49a000011ce68500070000032800a6001c000a410271605a742e000008b001900000000d0003d3183000020400000004116476180017cf200000000000000005c3c00204002230130aa8e00150000000144000000078007e1ba20da0019000fe3a001b11a8300200002c018e4c2331316880030300041a06010000040002000201000502010003000205000000000300020000060204000006030100030201010200bb28e877551d0eeca321dd54643cea18875e53d0abaa7a15d94742baa8e857a50d0af2a1a14f94a42afa9a855c5350aeea2a15d14542bda8285785050a7ca4216b948429f2a6653d54ccaeca3995d54732bd286657950ccabca5196790a32ce214653f544ca78a8995dd4532ba28a657b504caf0a0995794832e7290659e420cb3884195794f41aea9e835e53906baa720ed504419f2a6633d54cc67ca918cf55231ea98863b642c87688590f58cb21ea196433e548867aa910d794e21aea9c437651886f4a110de542219faa2433c54486bea690d714d21bda82437850486eca410f994821db21043b442087ac6410f50c821afa9a815c53502dea4a05b14940bba8a817451502bca6205754c40bb2888175511027ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2eca2185d54430dd21641b842c83b46590760cb20f990e41f021c827ca9104f55220af29c415d53883588510730ca20bb28c417551883c843105e942209faa2413c54482bea6905714d20bba8a417451483588410730c820f2108417a52083d4a4107ad0820dd21041b842083d084106a10820f599041da32083b064107a0c820e419041f321083d442107a08420f810841e0210827ea8884f15110afa9a215c53442dea4885b149109f2a0213d54042bca6085754c10
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x28038290050001e48001a61600c70688010042020010c0018b84420c821b298f42082e261d0820aa98a42082aa64cc820b898732082ca628c820e210a320838a420c820e210832083a042c8420f00cb21082aa6488420b298e21082e26188420e890821083a04208420f08c821083c03208420
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 144
  | 3 => 19
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
  | 4 => packedAt s2K4 (4272+((h/48+packedAt s2K4 (3888+(h % 48)*8) 8) % 251)*9) 9
  | 3 => packedAt s2K3 (752+((h/6+packedAt s2K3 (722+(h % 6)*5) 5) % 29)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffc07fffffffffffffe03ffffffffff87fff
  | 1 => 0x1fffff803fe01ff00fffffc07f01fc07ff98c7
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xe0ffffffc0001ffff00fffff8001fff80fe0f8
  | 5 => 0xffffffffffe000000ffffffffe00000fff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8412f412493145192922b025cb532d4a982b5b
  | 1 => 0xa82554f61354cb28ea45f2e0553154c7ab98c5
  | 3 => 0x10498124a28292424489454aa6a49a9545d5ae
  | 4 => 0x1d8e26473b1b1c8c88ee79b340c1e3e18ee0f0
  | 5 => 0xdef038783c1c1f0f0f0f9e3c78f903060f7e00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800ee00aa00aa008800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37443
namespace PEqualNP.Outside.L_meta_37443
open PEqualNP.Outside.L_meta_37443.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 1 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x929a514631a4a49a1e04b290cca43395518615
  | 1 => 0x84a8d4ca52a3a90aae5c15b2456c91a0d4b2cc
  | 2 => 0x284102908409122040a949451251444a8a596a
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xe0e0e0e0e0e0a0a0e0e0e0e0e0e0a0a0e0e0e0e0e0e0a0a0e0e0e0e0e0e0a0a0e0e0e0e0e0e0a0a0e0e0e0e0e0e0a0a0e0e0e0e0e0e0a0a0e0e0e0e0e0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37443
namespace PEqualNP.Outside.L_meta_37443
open PEqualNP.Outside.L_meta_37443.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c3eca3185d94630bea8c61f5518c2eaa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ee62887d0c510fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f7cca31ee994637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831bea9063df320c7ba6418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fb20e43f541c87ee6390fd0c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087ec8210fd50421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x121a418cf1c1000220002491627d8471ab39e2612981d0006100024c46e00017a754f02e8ab28300083c0023f0925cc6c80025c7291610e4ce7ec000402da0582e8aa502700a29a246c6f4aa93c42a5500f00f0a2a30fc0092504cc9e8fc0009040004636e9d88780032c9113a07547a4d8981d711e42000007298648448fa2f4000000c614c1f10d95c23e001009a44d0720da1e91e2000002884cc6801f9681c6454ff8152f85ecb200810e2d4001630000003b9ef1589cc15a4d0ce9493ea563647c1368001042d8118db252000f60000006d40016e0d651c5b800000001448a81ca3e5402330527303a00006a000a827e000a1832857000a4c08a3423c000850f34b6484fe8bb4007701f05502e6e41300033a000000000b6034000000184fc0000004e3f400160132000001760061581b8000007d04924e2d810495a7c1a030809975336000059830000012412d4b0000d29d21de8787c0e13e40013d80037e268309e82d49bcb289f00013125a0300078cafa2910079c5382a0f09683f0a41a4810ac08408e0000fa0b0001c0cc1f50000012a8000b80011180013c2cc0028e44053c640cc0de0488a1d13c46e8df0ab048894480b83b44b03d96f00c8681d1e60f498c652123c04ecc324630a000d515b52a988cd28717c0149a9cb4302a42f8001887611d8394ca0cc000004740006b1d54e2564b82770001280ca351b4458739d61b80b0229a835c2f4291ee13a1a4ef8b0000a101c1e41e823400000284360c60003120001e80001c060081700c000640001425000240500000c09010020841307800000010000201004000000c4000000000403010000400000002004151041b000090280300c000100005000004010080a00408010130000a0000402c0802c1f02807004070002b0940101401000040680001c25024060200202c0501c0003c0400800000430000400c0001003014000100500c05044000040201c5601c0b0000107c05008010183c0040000402034140000401c01004030101d00005020000000a018070200402004000130004100403008000000101804074030000800420004020180a0081e0042000809060110280000000014020240805c08008010000b0000601403014010200000c000080b008030bc090240106c1dbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e85f651d0aeca3a15f54742faa8e857551d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857
  | 3 => 0xea3b24306724200000031a3c00034ced8362706b4c68000dc6c5300af09674c780952ae000459a70bc000ba0424147cccc9af1ec884d4927000374a682d52c8401e06c44c410269071ee8514900048e2f02c00442c445410302068c10403b31442ca98c92c225d250484a23c865844376408fc85450a725189c21a88ac0020e18e4f8000830008e0fd0001020811780009c67d060000008344500048a001360322cc4a92780000070d4b8002365c4af1132684982825914a518519930ec000a01092f2528299fe0205387209c25e2fd469522f04412e000274164000e9000620f69234644c8a194815c8a8009192ee5f8488cd22e5887716b2ba59cd998e45a5f54a1014a0199039001723b056a8f2e497d3d2573a00713f991360000e21f75167748e8c03e2280000ff1683780008631e008a22910009a83907d13660538169126874c024044487cce17f000990ca12040c000629c71a28e4001cd3783ac3400000025800000000000e28000004c4c58004860010121c248824a08cf000448002240004dc398002b4718829ea37035d2a0c14e4524c10181c084cca9b60860c48e0283ca1fd359ce4220b8d32690d4388910c31aa2500d08514213cf085a1be00031000000000000fb1cc1e4590641ea8f9371510426b11387145c468460220da4950299714497412800230864050fe1daa290b9fc3a86851401b0009e40000e30e0001a0e80284e400000520978001de3d668c00000320180a5a6
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x153c82776154f209d18553c823e6414f208f59053c823e64947208f59251c825e63952209758e548827661152209d584548823e64d4e208f593538827661d4e209d587538823e6494e208f592538823f64546208f191518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d209ed81534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d614f204836451881209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c755153083586054c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083655188420d654f3008279650c0209bd9520082e461480209ed9520082d863480209798c54c425d63153108fd9153c423c6454f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b10b518d41c42b5640c710ad59221c425e63d52109758f548423e64d4e108f593538423e6494e108f592538423f6454a108f191528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d10d5587534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452443345490510d914a41442746550510b518d414436452505109d997314433454cc510d914b31442b5640c510cd1503144357530c510d914831442766588510ad592214436452885109d19521443645248510d914a104423d65950108f990540427661150108f993530423d64d4c109d987530423e6414c108f590530426e6214c109b588530423e64d48108f593520423e64148108f590520425e63148109758c520427661148109d597210433554c84109d59421043355408410cd553100427965840109dd9510043355444010b9189100427b6544010
  | 1 => 0x63f6550441a718d41106776550441b518d411066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc67a60152319e580548c63e6494a318f592528c69c644ca31b6181328c63f64542318f191508c63e649513197d8d544c67761551318f994544c73454cc531c7152314c63d6595031c718d540c73461550318f990540c71d54d0c3197594430c71d54cc831a7191320c71d544c831b5d85320c6d8604c831cd553410c79743d04319d594410c794431043197d95310c69c644c4319dd95310c6b4644c4319798f54c865d63d5321cd58654c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c87576154f218f99053c863d6414f21cd95241c86d46350721cd95331c86b5640c721cd95031c8755530c7218f993538863d64d4e219e983538867960d4e218f990538863d6414e21cd5532188675619512197d8d544865c63551219ed81544867860551218fd91534863c6454d219dd85534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520863e64944218f59251086756590421b518d4108675650c421ad59031086e5620c421ad592210866f65484219dd95210863f64540218f191500865f63540219718d50086776154f409d18553d03576154f40d518553d031d5390f40c754c43d031d53d0b40ad58742d031d5350b40c754f41d029c6350740c754d41d02b46150e409dd8552902746154a40a758c429029d63d02408f994435025e63149409758c525023e65d0940ad587425023e65d0540a718d415023f6550c40ad185431023d6590840a758c421025f63544409718d51103576354440d518d51103374354440cd50d51103364254440cd109511023d6590440cd54641103355110440a758f401033551d00408fd95401033551500409ed95401031d54ccb30c755132cc2d8604cb309d987548c27561d5230c758e548c27661152309d584548c31e5490e30b5185438c29d640ca30cd952518c3355494630cd951518c3355454630c7952318c29d640c630c7950318c355510c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d641493097997324c2d8604c9308f990514c23d64145309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2d46150c308fd91520c23c64548309dd85520c274615483097596320c29d640c8308fd91510c23c6454430a7590310c2d9600c4308f992500c23d6494030a7593300c25f654c0309ed95300c27661953209d58654c825e63153209758c54c823f6454f208f19
  | 2 => 0x2603044d1171c26bc0001018a72c001ba17c444541360003acf020d4064210980032626cfb8002a811cd30060004a84a8d800069c4193e0341a10480c004000002011fa0000010e15c6ec07918308000e809405c548b414f30665cb8836000558df9420000000700000013400013000098938002b268c791103ba480360220a40603a00038400000199000000001ee3f8000000003be000b5000000000b000013e158000001f200000097000000138000000f0000bb22c5982b8000da000b184e0c83287f00b0664148f8ab154000000001ac2dc4603f250434891d60de3105c0310000007b000416760000e720681c00000000500000003827885d067388290000000b4000618002642245299a2523189e000288000001e70d200039000000004190000f00806000010140203c0000c050040402800038000080f00000000020080a00400018090040100003010100000000400004030001901c080040102c0101005000000040000c0600404004000340600000008030000001400010090040000002020000100a0000000805004000040200004004000000300008038040000200000044060080004008000000040202c0000c10004210000200006018000180f00401014020140000c00010010040500000000020280101001000010000a00000000040100201000000090080200c0300c0d028030ac07070000080500e776154a439d1855290e7661942439d5865090f574314543cd90c5150e3f6550c43ad1854310e5f6550c43b51854310eb46150f4297d8d51d0a5c6354742d5d8d51d0b546354742cdd0d51d0b354354742ad5874290a5f63542429718d5090a3e65d0d42ad1854350a7661141429d5845050a776154c429d1855310b576154c42d51855310a3d6590c42c754e4310b1d5310c42c754f4210ab561d08428fd954210b1d53508429bd954210a7661153329d58454ccad46150f328fd9151cca3c64547328f99250cca3d64943329d98650cca7561943329d987548ca7561d52328f992518ca3d64946328fd91508ca3c64542328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132c758c544cb1c5490d3297195434cad46150d32cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb705114132d690c504cb594314132d68c8504ca3d65950328f990540ca5e6315032c7553320ca5f654c832c7551320cad8604c8329bd95320cab46150f41a758c42d065e6394a419758e52906b561d0a4197d8d509065c63542418f997435071c53d0d41c714d43506b46150d41c714e425063e6510941a758c425071c5310941d514f415071c53905418f59643106b561d08418fd95421
  | 3 => 0x2b0820000000000000008f00000000000098241081192d8000000e32487342c0001d8000000000007b0a18462bc000f40003586384b1bc04a768f499b006000f58000004980002c000000001d20b627800000000000658b4000124e992f3a20002e965000000000ac0004b0000003183d4001800f00bc000530845f8b900018e244a88053ec7ec728ad2fa0007d8000000740001c0003e8038001cc6b43511b130000770e911c7141c89943008c31a150dc2087686017e5044683830c1d41a9061d078cbb0f1126000001941e8838409cc000300dc0000000e8c500000068000000000198b211d000000eb8002721c0898af000000c817a000000ec98b3e82d48509d432000001aa2de634a60003da00000073244454f9800000000ad91c3bc34c158000000005900024a000002121661e41ea00000570531782682f1029353c2170c28a72d26d41402a3fa6c0809c30000005097400000095953000534000ff24236cad0111c47210b20c0ec000c905409405c001a538e7940011a000000000001e0000001c00006c80013f014000000000bc574fa821262000720001987c8000a037a48c00001000000ca886000000b39f81a87510b8160000000001525a2000000009e000d98da10a528d492e28e0c0fc8f80806d88f0872f241c5e8dc00009000000000658be01426e624000081c0000002022002c4e71880001140013800000000000330144000000be73c310192e67708a0d1368378c10ce27a1646c8f73442880900021e2480019d4348440007742835c519be0f8000001c90005c0611ab0000003d0482ae000a70611e67bc3f07f1722d80000000076cb106b33863cf31b9394140000000007f8000000000000000001a000328713482c0b7000040810678ef110334168411aa3241f15f000000a80fc0005140003b03c818001ea3e2228db81f0000dca5800362408a40c83e0210a487d3fe1ec8484300083c149043f4644d713a266340001873c85ec1910c000584cf10b1d4000d40000680000013b3aa5b400000000554a317f3425ac6e8001380240004b1521102a975008000bb80030237c0020a33e7186908b00006c0000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4c01620000700d0152d00130053c40110c05c62404826002803805000018000001f451c55310c42c2aa6b0e84215147158c544caa838a862826586550604c832928e6b0e8420e1463185540c60e3b2a89906386550604c831a28e6b0ca990c357695031c868a38aa621e818554d61d0b40a2ae6212a22051473544411030ab1aa3a008186550604cb30a28e2b1ca91841d76950318c28a39ac22a2219118c525051086aec2a06288625641483144312b20a510a21895506244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8b08148754d61d08428148754d61d0b40814865cc42544408148758d51d0040
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
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (20138+((h/221+packedAt s4K5 (17928+(h % 221)*10) 10) % 797)*11) 11
  | 4 => packedAt s4K4 (22272+((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xff80fff80fff83fe0fc0ffe0ffc3fe0363ce7c
  | 2 => 0xfffffffff03ffffff000fffffffc1fff83ff8f
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 5 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x290a22312209208052c92909280532a82e10b5
  | 1 => 0x43266450e492259605585b285a43541962c65c
  | 2 => 0x8414888241a4422aa020945294a80952816b0a
  | 3 => 0x1658d12489074b4d39b20610e7328063d40de0
  | 5 => 0x1860e1c70e3873f1ce3ce79c06231183fbb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeae0eae0e8a0e8a0eae0eae0e8a0e8a0eae0eae0e8a0e8a0eae0eae0e8a0e8a0eae0eae0e8a0e8a0eae0eae0e8a0e8a0eae0eae0e8a0e8a0eae0eae0e8a0e8a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37443
namespace PEqualNP.Outside.L_meta_37443
open PEqualNP.Outside.L_meta_37443.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c3eca3185d94630bea8c61f5518c2eaa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f661907e0c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ee62887d0c510fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa8265fb504caf6a0995f14132fc2826578504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f7cca31ee994637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831bea9063df320c7ba6418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21fb20e43f541c87ee6390fd0c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087ec8210fd50421fb98843f431087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x60000018d366880d01c948c2cd1aa4d1b0248bd000000000000004c249800000000000c78000fc5ec1580028e798001680f0000001b6438000000004c63c0ac9ef12a55c238000006b08727a06a1bd0b0004a634c101b045651000000470000a0004000000001c10004b40024206c4e80004d0440000020615c000108000008b80000040000000000000000000001da3746f9063f000000000230000000003ac0004c8d5000000cf8000460000000000068c001a60005b0a123b0008982280021e1500000000000000000000761168000000000019b00076d4980000025c62800000210000154e05907428d4cc0005c8000000003b891000000be8c000000113a0b30a1a1250a5000124000c800a7c4b7800000000000000000014ba673e40005a27e276594f400028c829418830001f400000000000001970000000000000023d2e800000000bf000000000000740000e53915f27c364ba0004d6000001e70000014a8002260004ea5026e5dd4525235c4002f8004ca80c0026f21a980190c44b26d1421993e82f8cf000000000ca000000000001a515000000000344008000002081808f82c00003800000522428000000a00000e8000000000000019a514000003a60001d1f30849e0150730000009900a3bc000e0116000794001b2000000001711fe2b0000001ac5a4000000bc000000f5000820e79b920e0000025809c8fca7016000584d491d00018c000000030060280300600200c0080000a0000180002e0040100400601000002006008000000020000080600000000000006010018010060000100000000000001008000000090020000200300e00c0400300a0000380900a0000200001a00003800002000018000000100000300c00400800000000000100100200080900001c0000000001009005004000010000060080080501a00000004012000000020020000000200601c00800000000018030020040180100003c0200200402c0400100001c018000000100080300400002000004008018030020080000000800400005000014010000060040000200600400001000008000070000080600100204c0380000600c000010000380000000201400001008014008010020000001200000001017000018020250060000080000000800001bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e85f651d0aeca3a15f54742faa8e857551d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857
  | 3 => 0x17088c7d0000000001f80005c00045a3e1560000012900053c4104c4da7c09a0000002dc002194280012380000000000000010728000004ac000c305a13e58c001fd4ee28ce294b3aa9547c91a0306e070a71000a3d150004bc420f58001760000000039a0005a871000600000004e80000000000000c000000d6000000000780000007c0ac00000000000000718000000013a8000a66f000240000000cd2304680000008e1e69fc5e9a13a8000c88aa3ea000000003020002509a240000000002b6000ef8f40ec000000002dc0003705700000023000218329120000008e8a526e4c848c0000037c9d8d59b73a2308c715235e2843d06120645433a8e1022190f01e06e85540800000000001fb3da32cb00000363f0290e23ba42c00000462930069e109e8688a05c07c844b90254d28d9228d223229d07000000000de80028293c0015e5182b4dd027000524c180004c0912da21086000000003760000014d0008e40e0001d8001351d20000000000000000000000204350002900003700000049600031000000768000000005c0001c4162a502c8000001c08d89e00000000000000000000001fa24c002880021742425c0245a8bf9781783440012a00081400000000968a80cc266000fca2f4262c92200000039000000000001288002da00033006420398f0000000001060751f60010f9103d80000006d1ee0000001a00036800179000000a60000006c544833100000c91a85244bc000001920010918714c7188e20f0f6000a98002244240015c0000640020142e0000000032a21c00000000000002020000bcb30000000002c00039878892000000000d2287000000000e947a0000f93d000000f2000000000000003ec000000af0000000020400072c9e030000924c50001ae0000021b3a05cc3618c1440e0000001b6444000000000007c00002e00018a5f13003d2712500000114896262624038000000005f800286560e18002729cc001d7000708002820260000021d4906a87915a4d00000026c0004c0049670209ec351350006d54b0002ac2a47f20919e0d00009b0005ac4680018c5883ca2502869c0009c4a8a00c80652ea0004500027ea180010537e545458444301040000000062c738de000000000001c02206380000000000000000000000000fe0005817c4c4000000000007dc779c7000000000000000308f0002ec00061928304290680000000a0000000000000000000000000000000000f1993244520288000007fc608003905740002900039400000120000c20000006713e800464000001ea25c4840003b0008a0e722c2583b8000f60002500023326c6593ca852560005000000090d1e27c16c1005d0ea3d2834808690c8000ee19d3dc000000001180007880000045c428002a8000000890e4661208000003ac0003d01
  | 4 => 0x46e0000005b0000442580035a554fe00027095c2a800444000670003100000002d3f449c001fe000000001d900081c00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x153c82776154f209d18553c823e6414f208f59053c823e64947208f59251c825e63952209758e548827661152209d584548823e64d4e208f593538827661d4e209d587538823e6494e208f592538823f64546208f191518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d209ed81534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d614f204836451881209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c755153083586054c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083655188420d654f3008279650c0209bd9520082e461480209ed9520082d863480209798c54c425d63153108fd9153c423c6454f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b10b518d41c42b5640c710ad59221c425e63d52109758f548423e64d4e108f593538423e6494e108f592538423f6454a108f191528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d10d5587534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452443345490510d914a41442746550510b518d414436452505109d997314433454cc510d914b31442b5640c510cd1503144357530c510d914831442766588510ad592214436452885109d19521443645248510d914a104423d65950108f990540427661150108f993530423d64d4c109d987530423e6414c108f590530426e6214c109b588530423e64d48108f593520423e64148108f590520425e63148109758c520427661148109d597210433554c84109d59421043355408410cd553100427965840109dd9510043355444010b9189100427b6544010
  | 1 => 0x63f6550441a718d41106776550441b518d411066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc67a60152319e580548c63e6494a318f592528c69c644ca31b6181328c63f64542318f191508c63e649513197d8d544c67761551318f994544c73454cc531c7152314c63d6595031c718d540c73461550318f990540c71d54d0c3197594430c71d54cc831a7191320c71d544c831b5d85320c6d8604c831cd553410c79743d04319d594410c794431043197d95310c69c644c4319dd95310c6b4644c4319798f54c865d63d5321cd58654c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c87576154f218f99053c863d6414f21cd95241c86d46350721cd95331c86b5640c721cd95031c8755530c7218f993538863d64d4e219e983538867960d4e218f990538863d6414e21cd5532188675619512197d8d544865c63551219ed81544867860551218fd91534863c6454d219dd85534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520863e64944218f59251086756590421b518d4108675650c421ad59031086e5620c421ad592210866f65484219dd95210863f64540218f191500865f63540219718d50086776154f409d18553d03576154f40d518553d031d5390f40c754c43d031d53d0b40ad58742d031d5350b40c754f41d029c6350740c754d41d02b46150e409dd8552902746154a40a758c429029d63d02408f994435025e63149409758c525023e65d0940ad587425023e65d0540a718d415023f6550c40ad185431023d6590840a758c421025f63544409718d51103576354440d518d51103374354440cd50d51103364254440cd109511023d6590440cd54641103355110440a758f401033551d00408fd95401033551500409ed95401031d54ccb30c755132cc2d8604cb309d987548c27561d5230c758e548c27661152309d584548c31e5490e30b5185438c29d640ca30cd952518c3355494630cd951518c3355454630c7952318c29d640c630c7950318c355510c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d641493097997324c2d8604c9308f990514c23d64145309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2d46150c308fd91520c23c64548309dd85520c274615483097596320c29d640c8308fd91510c23c6454430a7590310c2d9600c4308f992500c23d6494030a7593300c25f654c0309ed95300c27661953209d58654c825e63153209758c54c823f6454f208f19
  | 2 => 0xf1e22142680001e548288330ec5c8d017540232c579d402005cba1c117414cc41d110e3d09113934a7bc469382686e44f87e1342c42a173316000ff0553660004a13e2d24dd05000220080000000981747313b000000d3000000758b2800094654000003aa0000000040c31cd100036e340000420ae0d509832420668761d80f6100f890503a06000000000000940002f8000000000000010497d00075c0001b078064420000007704d8c64181a0888c22b0290710691042582419f000000001c431e0007b0a836a51cec80000042c0000022600008931050524002022c48507200007a19c5f0003e0738ac9eb38609c9a800000000820ea28a000f10003d06f0001b6000140000000004bc4980000028c81000000000560000000000000000000400000020000200000024070380401c070040100c050040400000000020000002400000010440200001028050040800400008090000001001018000200200005004080000200000008030400200800004030040101403008090480404c00000000480002804010000080200404000050000500006034000000f000090100200003000000140201401000000100b018060180200800008010000200000004060340300402024000040300003000030080c0000a008000100f00400008000000304c01010010040000c060140000c050000002005000000080100c0501c06012776154a439d1855290e7661942439d5865090f574314543cd90c5150e3f6550c43ad1854310e5f6550c43b51854310eb46150f4297d8d51d0a5c6354742d5d8d51d0b546354742cdd0d51d0b354354742ad5874290a5f63542429718d5090a3e65d0d42ad1854350a7661141429d5845050a776154c429d1855310b576154c42d51855310a3d6590c42c754e4310b1d5310c42c754f4210ab561d08428fd954210b1d53508429bd954210a7661153329d58454ccad46150f328fd9151cca3c64547328f99250cca3d64943329d98650cca7561943329d987548ca7561d52328f992518ca3d64946328fd91508ca3c64542328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e6515132c758c544cb1c5490d3297195434cad46150d32cdd53514cb3454d4532cdd50514cb345414532ced53504cb3854d4132dcd47504cb7051d4132ced50504cb385414132dcd44504cb705114132d690c504cb594314132d68c8504ca3d65950328f990540ca5e6315032c7553320ca5f654c832c7551320cad8604c8329bd95320cab46150f41a758c42d065e6394a419758e52906b561d0a4197d8d509065c63542418f997435071c53d0d41c714d43506b46150d41c714e425063e6510941a758c425071c5310941d514f415071c53905418f59643106b561d08418fd95421
  | 3 => 0xb68a70003f00005839e83440800000448070da2dc50877012190860d60001767e45a8003a4000e11cd000000fa8001123e4ca15421c7c8f21ae29c630619210003501b0000de74cbf9973e60ec0600019404ca615c00027000217000000738661ea7dc179ed06000048000000000c10620000004e8b0000784001bf0001e48a15733a1b09995b1bc00000000034000350000000008c00000000000000000078000000000000013d0000002f0001da46cc08001000005b9081a233c000000e479c001230006a8c712e0000a8600ab370000f31762565900000111e4240680018a4300008c380578000000a4000c680000000000000000000000003be480c31de00000cd21a32ce16c591fd000000d580000076c23927000000001320000002e0002f20003800025253cd69030000006b0000002780000020e7fc10800004628d8000000000da000408000001901ee684a50781b60001c0003f4658001f800064418800396000000000f87a8c0000000000001920005a0001930001e800000000000000001b00dc0014b000000af8c10006780009241c000001c521a1384b9171f0054000ad0000000000020c000000560002f4000000001b8000d90d60e4001da05c0000013f1be5dc001190000242c90a000254aa800000000000000000006900005a468001251fa4e880800114000a400019a000001c80002840000041e12c7f0bf028800c21782802948f0a00005f8121612de71c001870002e444029192000e519c130000000a90002890a9bd0003305a02b23e8204193614c54c671603dc000001e92787d00f800000000f0189000000001830003c06a80004a0000000000078d0b1b20003cc39800000000119c90446f8000630e80002f8001666a000000000814001302c60002d0002d410c5e0002e27300000000013c1a0002f66e8bd0004060000012d2a035cd7800000000b60001d243c6220b08c0003681c010000ae9510000000580001481c001fb3f8184001414220000000022a1804c8450e20007900016c00043000154244b5877434000208fb286000740493ca0fc72800000000e3000000490719461c27741f0ef1f4000698eb22c4a88e8000ca558d39851ba0000001611c4b0001980002e1090750007d8000000000000000000022c0007d0000000000020066c000002cc3fcf6000000000001703a000002800288000000dc3760e8160070c86c48e14d0886a4ad12615c010cc82600c8647007
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x73c03095802c00020000463405c05444800146050c829140e4c0826847a4581451c55310c42c2aa6b0e84215147158c544caa838a862826586550604c832928e6b0e8420e1463185540c60e3b2a89906386550604c831a28e6b0ca990c357695031c868a38aa621e818554d61d0b40a2ae6212a22051473544411030ab1aa3a008186550604cb30a28e2b1ca91841d76950318c28a39ac22a2219118c525051086aec2a06288625641483144312b20a510a21895506244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xca08148754d61d08428148754d61d0b40814865cc42544408148758d51d0040
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1164)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 860)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xff80fff80fff83fe0fc0ffe0ffc3fe0363ce7c
  | 2 => 0xfffffffff03ffffff000fffffffc1fff83ff8f
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 4 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x290a22312209208052c92909280532a82e10b5
  | 1 => 0x43266450e492259605585b285a43541962c65c
  | 2 => 0x8414888241a4422aa020945294a80952816b0a
  | 3 => 0x1658d12489074b4d39b20610e7328063d40de0
  | 4 => 0x1860e1c70e3873f1ce3ce79c06231183fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0eae0e8a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37443
namespace PEqualNP.Outside.L_meta_37443
open PEqualNP.Outside.L_meta_37443.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x210058018c300c831c3b38d8401027a0007800020026b83f2a0c9242843a8a01b8000b800200000472c3260029400241d49a5544025806a6643c660222861513187cd8d2a00000000000000011830e06085010000102140008e0214000000407fe5401ff55007fc5401ffd0c07fe4301ff50c07fc4301ffd0805fe4201ff50805fc42007fcc805fe32007f4c805fc3201ffd0407fe4101ff50407fc41007fcc401fe31007f4c401fc31017fc8401fe21007f48405fc2101ffd0003fe4001ff50003fc40007fcc003fe30007f4c003fc30017fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c690023ff4348011ff21a4008ff50d20047f88690006ff6248005ffa124002ff90920017fa849000bfc4248005ff9924002ff8c920017fa649000bfc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf18520047fe8290023fe4148011fea0a4008ff10520007fe6290003fe3148001fe98a4000ff0c520017fe429000bfe2148005fe90a4002ff0852000dfec090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001ff4c12000ff86090007ff2048005fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffc2090007fc104800fffb262007bfd931003ffcc98800efe64c400ffeb262007bf5931003ff8c98800efc64c400fff2a62007ff5531003ff8a988003ff63c40017fb1e2000ff98f10005fcc788003fd63c40017eb1e2000ff18f10005f8c78801fff43c400fff21e2007ff50f1003ff88788003ff62c40017fb162006ff98b10015fcc588003fd62c40017eb162006ff18b10015f8c58801fff42c400dff2162007ff50b10037f88588003ff32c400dff1962000ff4cb10037f86588006fe61c400fffa0e2007ff9071003fec838801ffd41c400ffaa0e2007ff10710007fe6388003f731c4001ff18e2000ff4c710007f86388003f431c400dff90e2000ff88710007ec4388003fd21c4001fa90e2006ff0871000dfac188007ff40c4003ff2062001ff5031000ff88188007ff30c4003ff1862001ff4c31000ff86188007ff20c4003ff1062001ff4831000ff84188007fe10c4003fb0862001fe8431000ff82188007f410c400bffb222005bfd91100077ec888002bf644400bff3222003bf9911002ffac888016fd644400bfe3222003bf1911002f78c88800ebc644400bff2a22005ff5511002ff8a888003ff63440017fb1a2000f7d8d10005bec688003fe63440017f31a2000ff58d10005fac688003fc63440017e31a2000f718d10005b8c688017ff434400bff21a2005ff50d1002ff88688003ff62440017fb122000fbd8910005dec488013fe62440057f3122000ff58910005fac488013fc62440057e3122000fb18910015d8c488017ff4244009ff2122005ff50910027f88488003ff3244009ff1922000ff4c910027f86488006ff614400bffa0a2005ff9051002fec8288017fd414400bfaa0a2005ff10510007fe6288003f73144001ff18a2000ff4c510007f86288003f43144009ff90a2000ff88510007ec4288003fd2144001fa90a2004ff0851000dfec088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001ff4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff1044001fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xbff2088405ff104420ffb88221017f8411080bec208841fff084420fff04221077fec89083aff644841dff3224203bf99121077fac89083afd644841dfe3224203bf19121077fca89083bfd544841dfe2a24200ffd8d21005fec690803fe63484017f31a4200ff58d21005fac690803fc63484017e31a420effd0d21077fc869083bfd434841dfe21a4202bfd8921017fe849080bfe4248405fea124202ff10921017fe649080bfe3248405fe9924202ff0c921015fec29083bff414841dff20a420eff50521077f88290803ff3148401ff18a4200ff4c521007f8629080bff2148405fb90a4202ff88521007dc429080bfc2148405f610a4202fd08521007fec090802ff604841bff3024201bf98121007fac090837fc60484037e302420effd012106ffc809083bfd404841bfe202420dff8c12106ff8609080bff2048405ff1024202ff0812106ffc2090837fc1048419ffb26600cbfd9330067fcc99800efe64cc019feb26600cbf59330067f8c99800efc64cc019ff2a6600cff55330067f8a998006fe63cc019ffa1e600cff90f30067fa8798033fc43cc001ffb16600bff98b30015fcc598003fd62cc0017eb16600bff18b30015f8c598033ff42cc017ff216600cff50b3005ff88598003ff32cc001ef996600bff8cb30007fa6598003dd32cc017fe1966000ffd8730007fcc398002fe61cc001feb0e6000bf58730007f8c398033ff41cc019ff20e600cff50730067f88398003ff31cc001ff18e6000ff4c730007f8639802fff21cc001ff10e6000ff4873005ff84398006fd60cc003ffa066001ff9033000ffa8198007fc40cc003ff1866001f78c33000ff46198007fc30cc003ee1866001ffc833005ff64198007fe20cc003fe1066001fe0833000ffc2198007fc10cc015ffb22600abfd9130057fcc89800efe644c015feb22600abf59130057f8c89800efc644c015ff2a2600aff55130057f8a898006ff634c015ffa1a600aff90d30057fa869802bfc434c001ffb126000bfd893004ffcc49800afe624c001feb126009ff18930015f8c49802bff424c013ff212600aff5093004ff88498003ff324c001ef9926009ff8c930007fa6498003dd324c013fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530005f8c29802bff414c015ff20a600aff50530057f88298003ff314c001ff18a6000ff4c530007f86298027ff214c001ff10a6000ff4853004ff84298006ff604c003ffa026001ff9013000ffa8098007fc404c003ff9826000fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007ff204c003ff1026001ff0813000ffc2098007fc104c011ffb224008bfd9120047fcc89000efe6448011feb224008bf59120047f8c89000efc6448011ff2a24008ff55120047f8a890003ff63480017fb
  | 2 => 0x310d7f8651884efe618c429ffa0c6214ff906310a7fa8318853fc418c401ff98c6200f7cc631007ee631886bff218c435fe10c6200ffd82310cffcc118806fe608c401feb046200bf582310cff8c118806fc608c429ffa046219ff902310a7fa8118867fc408c433ff1846219f78c2310cff86118867dc308c435ff9046219ff882310cff84118867fe108c433fe0846218ffd91310c5fec898803bf644c4015fb226218ff9913101dfcc898863fd644c4317eb226218ff1913101df8c898863bc644c4075e3226218ff951310c7faa898863fc544c431ffa1a6218ff90d310c7fa8698863fc434c401ffb126200bfd89310bffcc49880afe624c401feb126217ff18931015f8c498863ff424c42fff2126218ff509310bff88498803ff324c42fff1926200ff4c9310bff86498863ff414c431ff20a6218ff505310c7f88298803ff314c401fb98a6200ff8c531007bc629885fff214c42ffe10a6200ffd8131005fec09885bfe604c4037f3026200ff581310b7f8c098806fc604c431ffa026216ff901310c7fa809885bfc404c42dff1826216ff0c1310bffe409885bfe204c42dfe1026216ff841310b7f8209884fff640c4277fb206213ff9903101dfcc81884ffd640c4277eb206213ff1903101df8c81884ffe540c427feaa06213ff150310adfcc61884fff430c427ff2186213ff50c3109ff88618803ff620c425ff3106202bf98831007fac418802fd620c425fe3106202bf1883109ffe841884bfe420c427fea106212ff10831007fe6418803df320c425ff1906200ff4c831007ba641884bfc320c4297f3086213ffd043109ffc821884ffd410c427fe2086200ffcc431007be6218803fe310c401fb1886200ff4c431007ba6218803f5310c425ff9086212fdc8431097f8421884bf4210c401ffb006211ff9803100dfcc018803fd600c4017eb006211ff1803100df8c01884fff400c423ff2006213ff5003108ff88018847fe300c423ef1806211ff0c03108fb8601884bff200c423ff1006211ff0803108ffc2018847fc100c421ffb244210bfd9221087fcc91080efe6488421feb244210bf59221087f8c91080efc6488421ff2a44210ff55221087f8a910803ff63884017fb1c4200ff98e21005fcc710803fd63884017eb1c4200ff18e21005f8c710843ff4388421ff21c4210ff50e21087f8871080afd6288405ffa144202ff90a21017fa851080bfc4288405ff9944202ff8ca21017fa651080bfc32884057f30c4210ffd0621087fc8310843fd4188421fe20c4200ffcc621007fc6310803fd3188401fe18c4202ffc8621017de431080bf72188405fe10c4202fd08621007fec11083ffe60884037f3044200ff58221005fac11083ffc60884037e3044210ffd022107ffc8110843fd408841ffe204420fff8c22107ff8611080
  | 3 => 0x3002010008000040200280700400041ffb266420bfd9332107fcc99900efe64cc841feb266420bf59332107f8c99900efc64cc841ff2a66420ff55332107f8a99900afe63cc841ffa1e6420ff90f32107bc8799083fd43cc841eea1e6420ff10f32015fac59900bff42cc805ff2166402ff50b32017f8859900bfe32cc805ef1966402fb8cb32017f8659900bdc32cc801ffb0e6400ff98732005fcc399003fd61cc8017eb0e6400ff18732107fe8399083fe41cc841fea0e6420ff10732017fe439900bfc21cc801ffb06641fff9833200dfcc199003fd60cc8017eb06641fff1833200df8c199083ff40cc83fff2066420ff503320fff8819907ffe30cc83ffe1866402ffc8332017fc419900bfc20cc83fff086641fff043320f7fec89907aff644c801dfb226400afd91320f7fcc89900efe644c83dfeb22641ebf591320f7f8c89900efc644c83dde3226403af191320f7fca89907bfd544c83dfe2a26402bfd8d320f7fe869907bfe434c83def21a641eff50d320f7ba869907bfc434c8057fb126402ffd0932017fc849900bfd424c805fe2126402ffcc932007de649900bfe324c805ef1926402ff0c932017b8649900bec324c801ffb0a6400bfd8532007eec299002f7614c801ff30a6400ff58532007f8c299002fc614c801fa30a6400bd185320f7fe829907bfe414c83dfea0a641eff10532017fe429900bfc214c801ffb026400bfd8132007f6c099002fb604c83bff3026401bf98132007fac099077fc604c8037e3026400fe1813200df0c09907bff404c83bff202641eff501320eff88099077fe304c83bfe1826402ffc8132017fc409900bfc204c83bff082641dff041320affec998856ff64cc42bff3266203bf993310affac998856fd64cc42bfe3266203bf193310affca998857fd54cc42bfe2a66215ffd0f310affc8798857fd43cc42bfe21e6200ffd8b310e7fcc59880afe62cc401feb166200bf58b310e7f8c59880afc62cc42bffa16621cff90b310affa8598873fc42cc401ff996621cff8cb31007fa6598873fc32cc42bffa0e6215ff907310affa8398857fc41cc439ff90e621cfdc87310e7f84398873f421cc401ffb06621bff9833100dfcc198803fd60cc4017eb06621bff1833100df8c198857ff40cc437ff2066215ff503310dff8819886ffe30cc437fe186621cffc83310dffc419886ffc20cc437ff086621bff043310a7fec918852ff648c429ff3246203bf992310a7fac918852fd648c429fe3246203bf192310a7fca918853fd548c429fe2a46218bf58e310a7fe8718853fe438c429fea1c6214ff10e31007fec51886bfe628c4057f3146200ff58a31005fac51886bfc628c4057e3146214ffd0a310d7fc8518853fd428c435fe2146200ffcca31007be651886bfe328c401fe9946200f74ca
  | 4 => 0xa860600189323844694d3261112068000ba37aa1800000000bb97759c049bcc0035dbb58d7714683dc620001fb000000fc80009e3a6001e20000007440000000160c000000015eae13bf0003290a4c0000f58000000000000047e972000005d3000000000000000002f0b4495742f01a07d8000bd0f80012100064f000ac000000ab000370d806696422ed536312dedd118000000598af0000000000055c0026900000022a8480052a0027f000c40fe8001da000002a857c3c133400392d92ae26a000000000002a2ac04f44a2e000026800618b40000004c42545b400068000388000000013a07a800001a617c8062717a0376bd55941b1e8003a865a6ebf4000b4e2191c024002b724315738648178bdca4e966d5cc4000775026558edff143303b124f0dad7c859480fab11268f23de81cc5a36441c9c0000031f00166a9445cdb220127e74b3e0000000000000002167001914000000001f6e63129d597b29457000001e746678cbce306082a538a1300000000000000cd2003368001d4770000000008a468800770001081aa000e7000000000000005a22c0cf8000003d800000000000000b62270000000000000149cfc27c0014700000000072d7c55ccc60011c000c1890ac55300000020b000baa050e480000000000059000010000030000000080300000c00000010018000000000000000101c010028000000000580500000000807012004040060120200000000001000005000014038090020180000102a000010010040000380000404000000000018008080060581080000201001001000000030010020000100a00a0000400401a0000300300000c040000020000100400200003006008004008100000180000000001402800012000010000120080000400c00000000004000060040300000280100e0040001801200401801000010000000140240200f00000002813008034000010040180300000200001003000004010020000000480000e0000080200200400801008024040010160000a8000000000080202601800001002028030000140040000000201804800006000000000000040000a0000100080300200000000008048000010060000080e00201c0000f00c0080100300a010008030000080080c0000000a804002004018080020040100300400002803004000008080000040080000a038010000020000000700000c00800000014000010020000400200a0000000900602c0181401200c00013000000008040020000400200000000000008000018000000080280e00a098000000080000100000001400001012030010000020080000000a0080000300000000003006034000010140000001d01400c000000160000200000a00400800002000000000060000000400000000000008020000110060000100200000
  | 5 => 0x146800000db5779d036071d77f3510a08e5587400000000000000000000005f09b9a4b4748c0002b80040000000000670000ea16b800378000005ec7d1b2c000000012a40000047e2aa4e0000000009f800001358dd3fcda8cca0f19e258002a50003e343ae90003c40007b39e0018530f000b606706aca4478df617000000000c3800000b240000000000000000000001985920f2002565b4000c9400000000000003e13dd9b15e023329960801c651cad873678d98ad75cbe4720058a28f16517671644e94184ce18763899fa37496334001a134400079b0753e1e761643ac6c8433dbf6b7394d5c4232e0010b72a0008358d8006ca00118800000414001310003900021b000041b38c10001d9b04005a600000129000000002b10000010a000185b3ac8000000000489b80004ac0030b01a45d42f430c8894c8f32c30b316f1f50009100091a0d40900000009cafe002388000000000000000000000000bf80005365d14737b2ca098d37c5db09f4907f36fa96c954ca00adea4b23a3a3ca0000321221cba9a50865c6a6c4fa75902768000000001793bdd63a9000001026aa5f8be8000007a40000000015b61058d8c7c600022b82535416eba0c26496c0030a7ccb1c0003200105000098000000002e30009b3581c2c654793ccb821624af900000063000000b64002013b27b76a1ab03eaa8b125b2fe6c8d9833000c081b0150004055ca56958000128f780000000000000a14001750000006900000074800000542000002570a90000013b000000c38003a70000024c4c8db0002d8800000000dc6e3299ae8000000000001d4b4a6950000000043364db2720fcd600035a2466b4000001f8000004f45c8000001f0000001490000018f000000682000000007980000041c88400254000000001f4e3a000000000000000030b80068d100004ab000000983d4000332188f0a7f96886a9e691a140024d86800000510cdd8c1f2800708088000009c192eec0000012f8596d7b8ebb35615c33e480c56db523a66383335091971c20eac25b8b33da292b58c42d0caf0f8002a417c00276cf105cbc8000000008a0ce800000000b959c0000000046a519982d9d6444c6b079000d41849b93bc858cc400000cfe8340064634f854a23401ef4580000052999c001beade002e200085eb6c0021aaaa00000000676d48000000013632e058000000003590015d32fec800196c2b0006d04a000000a8c00112524a833994547c78ad6c25a4b001a10000004ee0000000000000133000000b7400000000fac004db9955ae6f84e000000000002e000043000c44822a900000000000000cc2ea890eddd78001862300a882c006de7cfad0000008ed3d95f0001368d869e72000000630009a600000000cac000001424f00008700023cdd1db80029400050464000
  | 6 => 0xc7cb2e10000960db0440000011100067c00041800000000000004a7000f08140001f6000002705aa002495080000034e0000007ea030000000000000028ee00004e39d83f80000014b21400000000000000009c96b8000a2000000000000006ae8a388c3468da75f52095b6512b10e5b8a028004b09a2d613b67ed42db274000ee9d83659a0d9ed183030000115200c5cda8da1648707d0002800004b95d000d36c7b4b54c9143d2d21b266e39157ed000139eed800c22b292a8001f20000068c8210f2159a8a780000000000000000060b554e8000003a4b16b4bb9b9ecf02d1540010625e5ef59d4af4f038c152ca2a3ffd50000ef66bcde7ce3c0008d0ba0e80000014b800000c98002cf0000000004600000000000000000000002df000002d0800000000000000016f8000008b40010f1b03fdb1a9c20708d7d25de8115888aaf93439c860000000009f812c0435c000000000011cc001cc0001c0002c015000093000000002930005b84ea285e2cc8000001edbad0880040c7879000000088c002948500018d0006289dda081b0ba001aca1d494d48104003ee35200000260530e88610009ca001203bb0000014100000000021b3d2d600000000000578000000000011d2e103e7c8001a6c7ed717bb5eb9cb31773c0000e2800000001347010000000f222b3a000e58a05d116c00000000bf01e929948a9c4940c0006dda40b400094cacb34082aec00116518b1c8825eaf451000000000dac000eb000b70c101200a000c180000000000274d6c0005885c2a0000000006b84890212755e99c0000000000000178000000001ee984d6d5c000000000000002e20000034f85c4577263d322011870291090000027c000a88311814fc6019353d80000116c526ae22c52d280a10000036389d0003000000019c240000009b4951e0dfe000002c36101b841d4e02600019320c4c54ca1a156d3dc111eed1462493c82da8f00000155176306700005570000008f800000dd990b7f0015e00031464d6bc9b6486a8b534d0000009b93abbe8b1401f018ed11b0a7817e000002bf68ad3b791f80000000000045e0009048d5122836b58e25a000e3000186000b64004cf0d5721be2c84b2000003783d464a8244845ba999200040c29ee1c80321225194fa00000237800a7a002e50d8aca95d3d0740f7330005637be000004670017e8be000000000001690000023ab1a000e98ad23e22000000432a7600000472824bd629556acd5a3152b4ccc100ec4862280000005d5500700000000000000000000000005514bc00369000001926900001c165aad0000000024100000000184078000002a40000005a80045995400361800be673c006a200000000000bd500dd2bf85ec039cc000cec0015980039b912e00b07b0001f12da084d74004566c4d7c000000
  | 7 => 0x2c0d2247ae18000001a5028001a24a2661230000212e9c081ed8a0032852a5a43599b14e38e4f02bedc659899b082c00000000000000715736830999e80007c000002b3bae000d8eca0de0000000039a4c9b003ba6a4991b447000342000003a3424000004c612c00000000b04000001f600141c000003d00000056a00122c0039466a00340000000b0b000626f6f416c3c8000970000000017d800000000000840000000000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb704c91000df8704c91000cfe76cc51000cfc76cc510006bf64cc5100aebc64cc510006df63cc510006dc63cc510006ef62cc5100e6ec62cc51000dfa70cc510005f970cc51000df676cc5100def676cc51000cf676cc51015df774cc51015df574cc510007b764cc510157b464cc510006f763cc510007d763cc510006f563cc510007d463cc510005f572cc510007e762cc5100e6f662cc5100e6f462cc510007e462cc5100e6e462cc51000df670cc5100dff270cc510007f170cc51000df470cc5100def760cc51008cfe768c510006bf648c5100a6bc648c5100cedf638c510006dc638c510006ef628c5100d6ec628c51008df6718c5100dcff764c51000cfe764c5100b4fd764c51000cfc764c510005bf744c51002dbc744c510006bf644c5100c6bc644c510006df634c510006dc634c510006ef624c5100beec624c510005fb704c51000df8704c5100ccfe760c510006bf640c51009ebc640c510006df630c51008edc630c510006ef620c510096ec620c5100cdf6760c510006f6760c51014df7740c51014df5740c510007b7640c510147b4640c5100ddf6730c510007d6730c510006f7630c510007d7630c510006d7630c510006f5630c51008fd4630c510005f5720c510007e7620c510096f6620c510096f4620c510007e4620c510096e4620c510007d7320c510007d5320c51000df6700c51000df4700c51008ef7600c51008fd6300c51008fd4300c51013cfe7688510006bf6488510086bc6488510006df6388510006dc638851007eef6288510016ec628851013df67688510136f6768851012df7748851012df57488510007b76488510127b46488510005f67388510005f47388510007d76388510007d4638851006df5728851007fe76288510016f66288510016f46288510027e46288510016e4628851000df6708851000df4708851007ef7608851007fe6208851007fe42088510014ff764851000cfe764851006cfd764851000cfc7648510006bf6448510076bc6448510006df6348510006dc6348510006ef6248510016ec6248510005fb704851000df8704851000df47648510016f4764851000cf4764851011df7744851011df57448510007b76448510117b46448510005f67348510005f47348510007d76348510007d4634851007df77248510007e77248510007e76248510016f66248510016f46248510027e46248510016e46248510007f3704851000df6704851000df4704851006ff0704851006ef7604851000dfa76c411000efa76c411000cfa76c4110007bb64c411010fb864c4110007db63c4110007d863c4110007eb62c4110007e862c411000dfa71c411000ff271c411000efb61c411000ff361c411010ff241c411010ff141c4110007f331c4110007f031c4110007f221c4110007f121c4110
  | 1 => 0x8d10014fe76d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910026ee62d8910004ff74d891001cfe74d8910004fd74d891001cfc74d8910004fe73d8910004fd73d8910006ef42d8910026ee42d8910006ed42d8910026ec42d8910026ee32d8910026ec32d8910014fe71d891000cfd71d8910014fc71d8910026ef21d891007cff70d891000cfe70d891007cfd70d891000cfc70d891007eef20d891007eed20d891013dee76d8910014ee76d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d891007fe771d8910007e641d8910007e541d891007fe610d891007fe410d891007fe810d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef43d8910006ee43d8910006ed43d8910006ec43d891007eef71d8910026ee71d891007eed71d8910006ef41d8910006ee41d8910006ed41d8910006ec41d891007eef70d891007eee70d891007eed70d891007eec70d891007eef40d891007eee40d891007eed40d891007eec40d891007eef30d891007eee30d891007eed30d891007eec30d891007eef10d891007eee10d891007eec10d8910005bf745891002dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910026ec6258910165f77158910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910004fc7358910006dc7358910004dc735891007cff7258910006ef7258910164ff7158910006f7715891006cff7058910006fb705891007dee7618910026ee761891007cee7618910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc631891013fe5711891013eef6118910007e64118910007e5411891013eef601891013fe6101891013fe4101891013fe81018910004ff76cc910004fe76cc910004fd76cc910004fc76cc910006bf64cc910106bc64cc910006df63cc910006dc63cc910006ef62cc910016ec62cc910004ff764c910004fe764c910004fd764c910004fc764c910005bf744c91002dbc744c910006bf644c9100f6bc644c910006df634c910006dc634c910006ef624c910016ec624c910005f7714c910005f4714c910005f
  | 2 => 0x6de72d8d10006dd72d8d10006dc72d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d100cedf71d8d100cedd71d8d100ced571d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df21d8d10006dc21d8d100cedf70d8d100cede70d8d100cedd70d8d100cedc70d8d100cedf40d8d100cede40d8d100cedd40d8d100cedc40d8d100cedf20d8d100cede20d8d100cedd20d8d100cedc20d8d100cedf10d8d100cede10d8d100cedc10d8d1002dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10025ee7298d10005ed7298d100b5f57198d10004ff7498d1001cfe7498d10006be7498d1001cbe7498d10004fd7498d10006bd7498d10004bd7498d1001cfc7498d1008cfe7398d1008cde7398d10014fe7298d10006ee7298d10014ee7298d10004fd7298d10006ed7298d10004ed7298d10014fc7298d100b4fd7198d10006f57198d100dcfd7098d10006f97098d10005bf7458d1002dbc7458d10006bf6458d10006bc6458d10005ef7258d10025ec7258d100ddf77158d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d100dcff7158d10006f77158d100b4ff7058d10006fb7058d100ccfe7618d10006bf6418d10006bc6418d10006dd6318d10004ff7418d1001cfe7418d10004fd7418d1001cfc7418d10006de7318d10006df4318d10006de4318d10006dd4318d10006dc4318d10014fe7218d10004fd7218d10014fc7218d10006de3218d10006dc3218d100ccfe7118d1008cfc7118d1008cff7018d1000cfe7018d1008cfd7018d1000cfc7018d1008edf3018d1008edd3018d100cdde7618d10006de7618d100ccde7618d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d1008fd77118d10007d64118d10007d54118d1008fd61018d1008fd41018d1008fd81018d10006df7418d10006de7418d10006dd7418d10006dc7418d10006de5418d10006dd5418d10006dc5418d10006df7218d10006de7218d10006dd7218d10006dc7218d10006df4218d10006de4218d10006dd4218d10006dc4218d1008edf7118d1008edd7118d10006df4118d10006de4118d10006dd4118d10006dc4118d10006df2118d10006dc2118d1008edf7018d1008ede7018d1008edd7018d1008edc7018d1008edf4018d1008ede4018d1008edd4018d1008edc4018d1008edf2018d1008ede2018d1008edd2018d1008edc2018d1008edf1018d1008ede1018d1008edd1018d1008edc101
  | 3 => 0x5760c710195f7740c710195f5740c710007d6730c710006f7630c710007d6630c710006f5630c710007d5630c710005f5720c710096f6620c710096f4620c710007d7320c710007d5320c71000df6700c71008ff2700c710007f1700c71000df4700c71008fd6300c71008fd4300c71000cff7688710014fe768871000cfd7688710016ee6288710006ed628871000dfa7088710005f9708871000df57688710016f5768871000cf5768871018df7748871018df57488710005f67388710005f47388710016f66288710037e66288710007e56288710016f4628871000df6708871007ff27088710007f1708871000df4708871007fe6208871007fe42088710164ff7648710165f77648710186f7764871017df7744871017df57448710005f67348710005f47348710007e77248710016f66248710016f4624871000df6704871000df47048710175be76d911002ebe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d911016fb771d911016fb471d9110007b651d9110007b551d911016fb610d911016fb410d911016fb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006be32d9110006bc32d911016ebf71d911002ebe71d911016ebd71d911016ebc71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf21d9110006bc21d911016ebf70d911016ebe70d911016ebd70d911016ebc70d911016ebf50d911016ebe50d911016ebd50d911016ebc50d911016ebf30d911016ebe30d911016ebd30d911016ebc30d911016ebf20d911016ebe20d911016ebd20d911016ebc20d911016ebf10d911016ebe10d911016ebd10d911016ebc10d9110006bf64d8d10006bc64d8d10004ff74d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df43d8d10006de43d8d10006dd43d8d10006dc43d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10006dc32d8d100cef571d8d100ccff70d8d100ccfd70d8d100cedf30d8d100cedd30d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d100cfd571d8d10007d641d8d10007d541d8d100cfd610d8d100cfd410d8d100cfd810d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10
  | 4 => 0x8520006f44118520186f62118520186f5211852000cfe7018520014fd701852000cfc701852013eee201852013eec201852013ef51018520004fe76cc520004fd76cc520004fc76cc520006f761cc520006f461cc520004fe768c520004fd768c520004fc768c520006df638c520006dc638c520004ff764c520004fe764c520004fc764c520005bf744c520045bc744c520004fe760c520004fd760c520004fc760c520006df630c520006dc630c520015ee720c520005ed720c520006f7610c520006f4610c52000dfa700c520005f9700c52008df671d8f10004ff74d8f1001cfe74d8f10004fd74d8f1001cfc74d8f10014fe72d8f10004fd72d8f10014fc72d8f1008cfe71d8f10006f671d8f10006f970d8f100cede30d8f100cedc30d8f100b4fd7698f10006df6398f10004ff7498f1001cfe7498f10004fd7498f1001cfc7498f10014fe7298f10004fd7298f10014fc7298f100dedf3098f100dedd3098f10005bf7458f1003dbc7458f10004ff7458f10006bf7458f10004bf7458f1001cfe7458f10004fd7458f1001cfc7458f10006bc7458f1001cbc7458f10006df7358f10004ff7258f10014fe7258f10014fc7258f100dcff7158f100b4fd7158f100b6f47158f100b6df3058f100b6dd3058f10006dd6318f100cdf67118f10004ff7418f1001cfe7418f10004fd7418f1001cfc7418f100dcfe7318f10006de7318f10014fe7218f10004fd7218f10014fc7218f100ccfe7118f10006f67118f10006f97018f1008ede3018f1008edc3018f10036ee62d8b1013df671d8b10004ff74d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10004fe73d8b10004fd73d8b1006cfd72d8b1013cfe71d8b10006f671d8b10006f970d8b1007eee20d8b1007eec20d8b10014ff7658b10036ec6258b10004ff7458b1001cfe7458b10004fd7458b1001cfc7458b10004ff7358b10004fc7358b10006ef7258b10014ff7158b10014fd7158b1000cfc7158b10036ec2158b1006eef2058b1006eed2058b10004ff76ccb10004fe76ccb10004fd76ccb10004fc76ccb10006df63ccb10006dc63ccb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10005bf744cb1003dbc744cb10006df634cb10006dc634cb10005f7714cb10005f4714cb10005fb704cb1000df8704cb100b4fd76cc7100b5f576cc710006f576cc71019df774cc71019df574cc710006f763cc710006f563cc710005f572cc7100e6f662cc7100e6f462cc71000df670cc71000df470cc71000cff768c71000cfd768c710006de638c710006dd638c71000dfa708c710005f9708c7100dcff764c710005bf744c71003dbc744c71000cff760c71000cfd760c710006de630c710006dd630c71000dfa700c710005f9700c71000df5760c71008ef5760c71000cf
  | 5 => 0x6f721d8530006f421d85300def710d8530006f76198530005bf7458530055bc7458530005ef725853004dec7258530006f56118530004ff741853001cfe7418530004fd741853001cfc7418530014fe7218530004fd7218530014fc7218530006df3218530006dd3218530006f72118530006f4211853008ede301853008edc301853008ef5101853008cfe76cc5300dfd830cc53000cfe768c5300cedf638c530006f7618c530006f4618c53000dfa708c530005f9708c53000cfc764c530005bf744c530055bc744c530006f7614c530006f4614c530005fb704c53000df8704c5300b7d8304c5300dcfe760c53008edf630c530004fe7688530004fd7688530004fc7688530006ef6288530016ec6288530004ff7648530004fe7648530004fc764853000dfa76cc13000efa76cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc13005efa62cc13005ef862cc130007db32cc130007d932cc130004ff74d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006df43d8d20006dc43d8d2000cff72d8d2000cfd72d8d201bedf32d8d201bedd32d8d20004fe71d8d20004fd71d8d20014ff70d8d20014fd70d8d201b6df30d8d201b6dd30d8d200ecfd7698d20006df6398d200eded7298d2004df97098d20004ff7498d2001cfe7498d20004fd7498d2001cfc7498d201a4fe7398d200ecfd7298d20006ed7298d20004fe7198d20004fd7198d200fcfd7098d20006f97098d2005efb2098d200fef82098d20005bf7458d20045bc7458d200fdef7258d20005f77158d20005f47158d2005dfb7058d20004ff7458d20006bf7458d20004bf7458d2001cfe7458d20004fd7458d2001cfc7458d20006bc7458d2001cbc7458d20006df7358d200fcff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d200ecff7058d20006fb7058d2005cfb7058d201b4fe7618d20006dd6318d20004ff7418d2001cfe7418d20004fd7418d2001cfc7418d200fcfe7318d20006de7318d20006df4318d20006dc4318d2000cff7218d20014fe7218d2000cfd7218d20014fc7218d201aedf3218d201aedd3218d20004fe7118d20004fd7118d20014ff7018d20014fd7018d201a6df3018d201a6dd3018d201aefb2018d201a6f82018d20004ff74d852001cfe74d8520004fd74d852001cfc74d8520004fe73d8520004fd73d852000cfd72d8520006f741d8520006f441d8520136f621d8520136f521d8520014fd70d8520166f710d8520006f76198520025f97098520005bf7458520045bc7458520005df7358520005dc7358520035fb7058520006f56118520004ff741852001cfe7418520004fd741852001cfc7418520004fe7318520004fd731852000cfd7218520006f7411
  | 6 => 0xc2158b3005efb7058b300eeef2058b3005efb2058b300eef82058b3000cfd76ccb30016ee62ccb30006ed62ccb3000dfa70ccb30005f970ccb3000ddd76ccb30016dd76ccb3000cdd76ccb301dedf64ccb301dedd64ccb30016de62ccb3005fce62ccb30007cd62ccb30016dc62ccb3000dde70ccb300ffda70ccb30007d970ccb3000ddc70ccb3005fdb20ccb300ffd820ccb301b4ff764cb30005bf744cb30065bc744cb30005f7714cb30005f4714cb3005dfb704cb3000df8704cb301b5df764cb301aedf764cb300079f744cb301d79c744cb301d6df644cb301d6dd644cb30007cf724cb30016de624cb30016dc624cb30007d7714cb30007d4714cb3005fdb704cb3000dde704cb3000ddc704cb300efd8704cb3000dd8704cb3005fdb204cb300efd8204cb30065be74d8730005bd74d873005dee72d8730005ed72d8730006f76198730004ff749873001cfe7498730004fd749873001cfc7498730014fe7298730004fd7298730014fc7298730006df3298730006dd32987300cede30987300cedc30987300cef51098730004ff745873001cfe7458730004fd745873001cfc7458730004ff7258730014fe7258730014fc72587300b6f71058730006f5611873000cfd76cc730006f661cc730006f561cc73000dfa70cc730005f970cc7300b4fd768c7300cede638c7300ccff764c730005bf744c730065bc744c73000cfd760c73008ede630c730006f6610c730006f5610c73000dfa700c730005f9700c730004ff7688730004fe7688730004fd7688730016ee6288730006ed628873000dfa7088730005f9708873007fe82088730004ff7648730004fd7648730004fc7648730005fb704873000df87048730014fe76d893004eee62d8930004ff74d893001cfe74d8930004fd74d893001cfc74d893000cfd73d8930014fc73d893004eee32d8930004fe71d8930004fd71d893004eec21d89300feef20d8930005bf7458930055bc745893004eec6258930005f77158930005f471589301a4fe76cc9301a5de76cc9301bede76cc9301cedf64cc9301cedd64cc9300eddd72cc930016de62cc930016dc62cc93000dde70cc93000ddc70cc9300fedf60cc93000cfc764c930005bf744c930055bc744c930006ef624c930016ec624c930005f7714c930005f4714c930005fb704c93000df8704c93000ddc764c930016dc764c93000cdc764c9300079f744c9301c79c744c9301c6df644c9301c6dd644c9300fddf724c930007cf724c930007cf624c930016de624c930016dc624c93004fcc624c930007d7714c930007d4714c930007db704c93000dde704c93000ddc704c9300efd8704c93000dd8704c9300eedf604c930004ff74d853001cfe74d8530004fd74d853001cfc74d8530014fe72d8530004fd72d8530014fc72d8530
  | 7 => 0xc621014ff768c621014fd768c621006de638c621006dd638c621015ee728c621005ed728c6210e4ff764c621005bf744c621085bc744c621014ff760c621014fd760c621006de630c621006dd630c621015ee720c621005ed720c621096f6610c62107efa60d822100cff7658221015ec725822107ef8605822107fea2058221004ff745822101cfe7458221004fd745822101cfc7458221004ff7358221004fc7358221014fc715822107ef8305822107eee205822107efa205822107eec205822107ef81058221004ff74d8d2101cfe74d8d21004fd74d8d2101cfc74d8d210d4ff72d8d210d4fd72d8d210d6df32d8d210d6dd32d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21006df6398d210bdf57198d21004ff7498d2101cfe7498d21004fd7498d2101cfc7498d21094fe7398d210e4fd7298d21006ed7298d210bcfd7198d21006f57198d210e6f72198d210e6f42198d2100cfe7098d21004fd7098d2100cfc7098d21005bf7458d21075bc7458d210e5f77158d21005fb7058d2106df87058d21004ff7458d21006bf7458d21004bf7458d2101cfe7458d21004fd7458d2101cfc7458d21006bc7458d2101cbc7458d21006df7358d210bcff7258d21006ef7258d210e4ff7158d21006f77158d210e4f77158d21004ff7058d21006fb7058d21004fb7058d2100cfe7058d2100cfc7058d21006f87058d2100cf87058d210d4fe7618d21006dd6318d21004ff7418d2101cfe7418d21004fd7418d2101cfc7418d21006de7318d21094ff7218d21094fd7218d21096df3218d21096dd3218d21096f72118d21096f42118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d21006dc3018d21014fe76cc521014fc76cc521006df63cc521006dc63cc521015ee72cc521005ed72cc5210e6f761cc521094fe768c521006de638c521006dd638c5210d7e4218c5210e4ff764c521014fe764c5210bcfd764c521014fc764c521005bf744c521075bc744c521006df634c521006dc634c521005ef724c521015ec724c5210bfe4214c5210d4fe760c521006de630c521006dd630c521096f7610c521015ee7188521017e67188521016ef6188521017e7618852107eee608852107eec608852100cfe76d812106efa60d8121004ff74d812101cfe74d8121004fd74d812101cfc74d8121004fe73d8121004fd73d812100cfc72d8121014fd71d812106ef830d812106efa20d812106efa10d8121005bf7458121075bc7458121005df7358121005dc735812106ef8605812105eee62d8b30014ff7658b3005eec6258b3000df87058b3005feb2058b30004ff7458b3001cfe7458b30004fd7458b3001cfc7458b30014fd7358b3000cfc7358b3005eec3258b30004ff7158b30004fc7158b3005ee
  | 8 => 0x7d671cc831005dd71cc831007d571cc8310d6de61cc831097d721cc831097d421cc83108dde70cc83108ddc70cc8310e4ff764c831005bf744c83109dbc744c831005f7714c831095f4714c831005fb704c83108df8704c831005df764c8310e6df764c8310079f744c8312379c744c831236df644c831236dd644c831095df724c831007cf724c831016de624c831016dc624c831005df714c831007d7714c831005d7714c831097d4714c8310d6de614c831097d7214c831097d4214c831007db704c83108dde704c83108ddc704c831007d8704c83108dd8704c831005dd72cc43122fd721cc43122fd421cc43108dde70cc43108ddc70cc431225dd738c43121ede638c431225f5738c43121ef6638c431007d6638c431095f6728c431095f4728c431007d7328c431007d5328c431005f5708c431217d6308c431217d4308c431004ff764c431005bf744c43109dbc744c431005df764c431006df764c431004df764c4310079f744c4311e79c744c431005df724c43120ddf714c431206de614c4311efd6514c4311efd5514c4311e7d7414c4311e7d4414c43108dde704c43108ddc704c431005f7764c431006f7764c431004f7764c431007b7744c4311e7b4744c4311fdf7734c431007d7734c4311f6f6634c431007d6634c4311efd6534c4311efd5534c4311e7d7434c4311e7d4434c431095f6724c431095f4724c431005f7704c43108efa60d803100cff765803108ef8605803108fd83058031004ff745803101cfe7458031004fd745803101cfc7458031004ff7258031014fe7258031014fc7258031006df3258031006dd325803108ede305803108edc305803108ef8305803108ed8305803108efa205803108ef81058031085be74d8e21005bd74d8e21095f671d8e2107dfa70d8e21005f970d8e21004ff74d8e2101cfe74d8e21006be74d8e2101cbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e2101cfc74d8e21006ed72d8e21094fe71d8e21006f671d8e21094f671d8e2100cfe70d8e21006fa70d8e2100cfa70d8e21004fd70d8e21006f970d8e21004f970d8e2100cfc70d8e210bcfd7698e21006df6398e21004ff7498e2101cfe7498e21004fd7498e2101cfc7498e210e6df3298e210e6dd3298e210e6f72198e210e6f42198e2100cfe7098e21004fd7098e2100cfc7098e21004ff7458e2101cfe7458e21004fd7458e2101cfc7458e21006df7358e210bedf3258e210bedd3258e21004ff7058e2100cfe7058e2100cfc7058e21006dd6318e210d5f67118e21004ff7418e2101cfe7418e21004fd7418e2101cfc7418e210e4fe7318e21006de7318e21006ed7218e210d4fe7118e21006f67118e21096f72118e21096f42118e2100cfe7018e21004fd7018e2100cfc7018e210bcfd76cc6210e6f661c
  | 9 => 0x820582310cef810582310c5be76d91310c6be76d913101cbe76d9131006bf65d91310073f65d91310063f65d9131006be65d9131006bd65d9131006bc65d91310073c65d91310063c65d9131006be62d9131006bc62d9131006be60d9131006bc60d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d91310c6be73d91310c6bd73d91310c6bc73d9131006bf53d9131006be53d9131006bd53d9131006bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d9131006be32d9131006bc32d9131006bf71d91310c6be71d91310c6bd71d91310c6bc71d9131006bf51d9131006be51d9131006bd51d9131006bc51d91310c6bd31d9131006bf21d9131006bc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d9131006be30d9131006bc30d9131006bf20d9131006be20d9131006bc20d9131006be10d9131006bc10d9131014fe76d8931006bf64d8931006bc64d89310beee62d8931004ff74d893101cfe74d8931004fd74d893101cfc74d89310beee32d89310beef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d89310beec20d8931005bf74589310c5bc7458931006bf6458931006bc64589310beec6258931005fb70589310b5f870589310d4fe76cc931006bf64cc931106bc64cc931014fc764c931005bf744c9310c5bc744c931006bf644c9310f6bc644c931006ef624c931016ec624c931005f7714c931005f4714c931005fb704c9310b5f8704c931006bf64cc5310aebc64cc531007b764cc53124fb464cc5310e6f662cc5310e6f462cc531006bf648c5310a6bc648c5310079f648c5312479c648c531006df628c531007d7618c5310cede608c5310cedc608c53100cfe76d8131006bf64d8131006bc64d81310b6fa60d8131004ff74d813101cfe74d8131004fd74d813101cfc74d8131014fe72d8131004fd72d8131014fc72d8131006f731d81310b6fa30d8131006fb20d81310b6f820d81310b6fa10d8131005bf74581310c5bc7458131006bf6458131006bc6458131005ef72581310bdec72581310b6f86058131096ee62d8831014ff7658831096ec6258831097e42158831004ff745883101cfe7458831004fd745883101cfc7458831096ec3258831096f47158831096f72158831096ec2158831096f42158831096e42158831004ff705883100cfe705883100cfc7058831096ef2058831014fd76cc831016ee62cc831006ed62cc831005f671cc831005f571cc831095dd76cc831016dd76cc831014dd76cc83123edf64cc83123edd64cc831095dd72cc831016de62cc831097ce62cc831007cd62cc831016dc62cc831
  | 10 => 0x8132006bf6458132006bc6458132005f77158132005f47158132006f76158132006f461581320eef8605813205dfa76181320eefa7618132006fb6418132007bb6418132006bb6418132006fa6418132006f96418132006f86418132007b86418132006b864181320efd973181321b6fb6318132007da4318132007d943181320fefb6218132007eb32181321afda32181321afd832181321afe83218132006fb6118132007f36118132006f36118132006fa6118132006f96118132006f86118132007f06118132006f061181320e6ee62d8b31014ff7658b310e6ec6258b310e7e72158b31004ff7458b3101cfe7458b31004fd7458b3101cfc7458b310e6ee4258b31006ed4258b310e6ec3258b310e6f77158b310e6ef2158b310e6f72158b310e6f42158b31004ff7058b3100cfe7058b3100cfc7058b31006ee2058b310e6ec2058b31014fd76ccb31016ee62ccb31006ed62ccb31005f671ccb31005f571ccb31094ff764cb31005bf744cb310adbc744cb310e5f7714cb31005f4714cb31005fb704cb310ddf8704cb310adbe74d8331005bd74d83310e5ee72d8331005ed72d83310defa60d833100cff76583310def86058331004ff745833101cfe7458331004fd745833101cfc7458331004ff7258331014fe7258331014fc72583310def830583310defa10583310a5be74d8a31005bd74d8a310d6ee62d8a310cdfa70d8a31005f970d8a31014ff7658a310d6ec6258a31004ff7458a3101cfe7458a31004fd7458a3101cfc7458a310d6ee3258a310d6ec2158a31004ff7058a3100cfe7058a3100cfc7058a310bcfd76cca31005dd76cca310bedd76cca31266df64cca31266dd64cca31016de62cca31016dc62cca31005dd71cca310cdde70cca310cddc70cca31014ff764ca31005bf744ca310a5bc744ca31016ee624ca31006ed624ca31005f7714ca31005f4714ca31005fb704ca310cdf8704ca310d5df764ca31016df764ca31014df764ca310079f744ca3125f9c744ca3125edf644ca3125edd644ca31007cf724ca31016de624ca310d7ce624ca31007cd624ca31016dc624ca31005df714ca31007d7714ca31007d4714ca31007db704ca310cdde704ca310cddc704ca31007d8704ca310cdd8704ca31005dd76cc631006dd76cc631005dd72cc631257d651cc631257d551cc6310cdde70cc6310cddc70cc631005f576cc631006f576cc631257d653cc631257d553cc6310e6f662cc6310e6f462cc6310cefa60d823100cff76582310cef860582310cfda3058231004ff745823101cfe7458231004fd745823101cfc7458231004ff7258231014fe7258231014fc7258231006df3258231006dd3258231006f731582310cefa4058231006f940582310cede30582310cefa30582310cedc3058231006fb20582310cef
  | 11 => 0xf5be7498532005bd7498532006bf6498532006bc6498532006f761985320edfa7098532005f97098532005bf74585320f5bc7458532006bf6458532006bc6458532005fb70585320edf87058532006bf6418532006bc6418532006f56118532004ff741853201cfe7418532004fd741853201cfc7418532006f74118532006f64118532006f54118532006f44118532096f5211853200cfe7018532004fd701853200cfc7018532006f61018532006f410185320e5f67618532006f67618532006f76418532007b76418532006b76418532006f66418532006f56418532006f46418532007b46418532006b46418532097d77318532007d64318532007d54318532007e73218532097d63218532097d43218532097e43218532006f66018532006f46018532006f77418532006f67418532006f57418532006f47418532006f65418532006f55418532006f45418532096f77318532096f57318532006f74318532006f64318532006f54318532006f44318532096f77218532096f67218532096f47218532096f74218532096f64218532096f54218532096f44218532096f73218532096f63218532096f53218532096f43218532006f77018532006f67018532006f57018532006f47018532006f74018532006f64018532006f54018532006f44018532006f63018532006f43018532096f72018532096f62018532096f52018532096f4201853200cfe76d8132006bf64d8132006bc64d8132006f761d8132006f461d81320eefa60d8132004ff74d813201cfe74d8132004fd74d813201cfc74d8132014fd73d8132004fe71d8132004fd71d8132006fb40d81320eefa40d8132006f940d81320eef840d81320eefa30d81320eefa20d81320eefa10d81320eef810d81320edfa76d813200cfa76d8132006fb64d8132007bb64d8132006bb64d8132006fa64d8132006f964d8132006f864d8132007b864d8132006b864d813205fdb73d8132007da43d8132007d943d8132007eb32d813205fda32d813205fd832d813205fe832d8132006fb61d8132007f361d8132006f361d8132006fa61d8132006f961d8132006f861d8132007f061d8132006f061d8132006fb74d8132006fa74d8132006f974d8132006f874d8132006fa54d8132006f954d8132006f854d813205efb73d81320eefa73d813205ef973d8132006fb43d8132006fa43d8132006f943d8132006f843d813205efb72d81320eefa72d813205ef872d813205efb42d813205efa42d813205ef942d813205ef842d813205efb32d813205efa32d813205ef832d8132006fb71d8132006fa71d8132006f971d8132006f871d8132006fb41d8132006fa41d8132006f941d8132006f841d813205efb21d813205efa21d813205ef921d813205ef821d8132005bf74581320f5bc745
  | 12 => 0xc74587320bedc73587320bef62158732004ff705873200cfe705873200cfc7058732006f561187320fefa60d833200cff76583320fef86058332004ff745833201cfe7458332004fd745833201cfc7458332014fc7358332004ff7158332004fc71583320fef830583320fefa205833227dbe76d91320f6be76d913201cbe76d9132006bf65d91320073f65d91320063f65d9132006be65d9132006bd65d9132006bc65d91320073c65d91320063c65d91322779f73d91322779c73d91320079e53d91320079d53d91322779e32d91322779c32d9132277ac32d9132006be60d9132006bc60d9132006bf75d9132006be75d9132006bd75d9132006bc75d9132276bf73d91320f6be73d9132276bd73d9132276bc73d9132006bf53d9132006be53d9132006bd53d9132006bc53d9132276bf72d9132276be72d9132276bd72d9132276bc72d9132276bf52d9132276be52d9132276bd52d9132276bc52d9132276bf32d9132276be32d9132276bd32d9132276bc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d9132276bf21d9132276be21d9132276bd21d9132276bc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d9132006be30d9132006bc30d9132276bf20d9132276be20d9132276bd20d9132276bc20d9132006be10d9132006bc10d9132007af64cc93226fac64cc932015ee73cc932017ce73cc932016ef63cc932017cf63cc93226fce43cc93226fcd43cc932006bf64d8532006bc64d8532004ff74d853201cfe74d8532004fd74d853201cfc74d85320e6dd73d8532006f741d8532006f641d8532006f541d8532006f441d85320e6f621d853200cfe70d8532004fd70d853200cfc70d8532006f610d8532006f410d8532006f764d8532007b764d8532006b764d8532006f664d8532006f564d8532006f464d8532007b464d8532006b464d85320e7d573d8532007d643d8532007d543d8532007e732d85320e7d632d85320e7d432d85320e7e432d8532006f660d8532006f460d8532006f774d8532006f674d8532006f574d8532006f474d8532006f654d8532006f554d8532006f454d85320e6f773d85320e6f573d85320e6d573d8532006f743d8532006f643d8532006f543d8532006f443d85320e6f772d85320e6f672d85320e6f472d85320e6f742d85320e6f642d85320e6f542d85320e6f442d85320e6f732d85320e6f632d85320e6f432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f740d8532006f640d8532006f540d8532006f440d8532006f630d8532006f430d85320e6f720d85320e6f620d85320e6f520d85320e6f420d8532
  | 13 => 0x400000100100900000000500000100500100400000000000200b00000300600800200500100100f00600000000300800b00001a00d00300400000100f00500000000600600000500a00300100000a00f00700000800000400800400600000001600e00a00000b01000100001100801000000000300200100100700000000400100200000902501100701700000000103500900100000200201200000000b00000200200000000000100400700100100002900000000000600700100000a01700301e00700100000000100000a00103300300401601800800500000100400200403700000301200d00000300206100200500100000600000000200000800000400000300200800300000100500801100300000001200801101200100102900300600000400200000401f00b00200100202200001300100900000000100000000000000000000000000600b00002100100f00000000200c00300300100300800000601900000000800500000400101000100102200000100000c00301100300000300800100000200300000000000000500100003600000100005900600000b00000300100500000400100100c00100400000a00901000100400100000900100300101a00900000500000200501400300000200100005700101000000300400f00401400200300100000c00600000800000b00300c01100001702900600301300400002102100700001a00c00000600200500101000000300000000700000100000100000100700000300800000200000700000000100e00d00000600000a00100000100100300b00a00400100500000b00100000100000001801200100600a00100d00000000000400101d00200000100a00300000500000000600101300300000401c00400500000d00400300200000500100200c00500200900400300900101400200200401500000200700000101700301200100301600c00000000000100200400500000000000600200000800400000200e00200400100900200a00000200200000000000000301400300100001f00000000500b00002200401000000000500800100100100100200f01000100800000700801c00100100100000b00100000100100f00000503203e00d00500000000000100100200700d00600100400700500300000000000000100300700e00f01700400400000b00200000200100e00200f00000100000000a00900700000600100200800001c00000000200000001400000300500700c00c00a005000003003003006f76198732004ff749873201cfe7498732004fd749873201cfc74987320d6f5219873200cfe7098732004fd709873200cfc7098732005bf7458732105bc7458732004ff7458732006bf7458732004bf745873201cfe7458732004fd745873201cfc7458732006bc745873201cb
  | 14 => 0x80a40003cb0f5800003124f9c8053200017b14e00003942449b7470428d800081a0000ee8dd5bd513f308000135cec85eca3b0000c3042d00000000000000000000f3e13f000215c0005d40840000ccf8b9be19bc49c4070b2a10941f44201cb8fd6b3224d17804680003e623008300000000e293783e55b121f20f60007c70000b9c2527473ed0000c404d6000163acc700019c88ae8ae1942188e8e23800016898e4aa26198001c788ba1ba3fe5c3065c39f0001dc271804f81920b66b91a39c389ec9e445431322a86ab79c31962746820003f6a0a04230d93f4212c2727750000000efc449395dd5467a711bb3422c427510a9ec09c3b450eb1ec43449c4ec0000cfabfc0000201ba900c1318aec7a0c7822a0ee04d829488c1d90000cf411382c13c0db31d845d4bbc2bc2280879e1e4ee8960b014e46d40081f200007107633940000fa002f3b994507000000cb00005a483180020c20002470000a00f6640300022b81f200000015b00003a31e8889ad7600000014a80000000ae000016432a059d0440046f9a07229c24271d0361df0000846c22cb1004947c21e0e583f5443458227ab457c1409592c25f3ed3899af87e42ec3cd10700002e90e88268ac944e02c92843144a019f11642ca087af6a2ca21d5e10fdcde85536f311b1aa800063d37fa2e28e37a2bbe80040007afb400c3043801f00000d00300000100100100100d00b00000100c01301e00000e00200200300000000200500500600100000e00e00001601100000e00c00a00400200100400501900001801800000000000400b00100300001100000500200000500400700003900900202900e03a00600600100700400400600100b00100e00300101300000400a00001700100000701000200300700000000000500702200900000400000000500300200001a00700500000300200b00300301500e00000b00000101200600002600b00200700100100000100c00201200000600100200600700600000000100000004f00400200a00300802100000900200200002200500200000b00600000d00700d00102900000000400100000501900000700400100400000000000300000a01e00600500200101601100200000103600d00500100800500300400100300000000200900100100100f00000600700000d00500001600300000000c00100200400002300000501400000900500000000400900400000106300200400a00c00300002100e01601e00400600000a00000b00000000200000200100800600102200000900200200100400000a00c00101600001100000100200b00100000000700000100400200100806300000100700400400200000b00600300101400000400200100600000c00000200200100900800200200200100100b00100400300300000000001800c00
  | 15 => 0x14520c883000a921192220005bf3e2800087e62a0e38000000000081d08e1631a79960dad0cc0000001254a065a010c8118e7469c2879b207f648e19840000001040dbc00028200038c0000e3100008300000004b636d40007943c70000852a0428c2be0000c826780c2c0001e00000dcdce03aa0001dd8cd0000187b8322c6d6034420006e4f888af0001de2ec286b0d01d9c0000000ae9a5c2414b38d318b869a2620e09a650ba69f00000000000001298f60000000394800004b2093740000000748b80c05c0000003bbd8084c6397a38095805c00000022e426a11036680000a8000280002487f4cb03117043d535300020220000000001a28fd10003c8800000000430e8000a8410697aa0cc00069300004e8ce24390dae2be000000077939c9ec00000000007e94330001fd624c87c0b75f5a4e45d23c59620e7e1ff0ed8db41f80f319b0c086d54da80012a8bbc0003e880001da0ad0001ffc0000002ad98a00004fabaacdc600020ba48800008439881c1be000000003688d463e25436c92a0c8c5df285c9f8dca75a13e4bc6b174383da9722276415bd79a3498872ca020e14b8e78a06618010c82853931b30b8519c3bb20c86c0679405227cce877405b852048825812e05befb313e1410df82d07e71f7132414c7da9051cb870156db0507483685a30000c401b56fe4518dd11141b217c958cebe1371918130b1a66e1b200008d2886000000115d7ee1124e5b03554c09683d0a400fe000153681a6b22e300005694400001ef2cd45d93160d8a7d62b33082086678203bda0e78fe300fc27000015e2b11f6084868a4010001d7400000039880000005dd2b903f4b948a8197967000000043f91280005e04309dba4535772e40aa83497d886c400000088e00011de59a88f35703580005e90c08432af24dd0001564f8402b0b9858c14e74f2cd8e0400000040980000007ef91147ec4ce35840c4038b004c032654fc00000020c1ef69340000c5cc588311f4a0f9534a6246f43880009022180e580a11327e9032873c77000040b8c980000221fc8df04526751f80adcb212bf290cdbe5680d3245a0fe0007d605a8a9400050905203b6e2c35f0000000daa5a19e0d7d49a246c44696100000003a18708b183ac0a5dd7a4840003d340004ca4b736d1ee09656a50a3000081e21f2e61d50000754b3580010fc19d2b740003f087241280000000000000266a6a0000c4cfa0000000000000030e5bc03917380006de1128cc4cfa81b0de4000000000000000000000000000000000000000de459c288291ca98f5c26a2c3860c53c000319c328cc85a480009b000000000016c910089b000000000000000010c800035bb2e88f8e900004459a8c3bc68c0b39b9ab0a6382289c0b0da184000026000081a1571274f3c1a816b8b04cb2224253883
  | 16 => 0x6907464f29e8ea89f32c3000000000031201e00004683e00000000c4e0002c7986c23a455c290c62390832b890d750ea0e426115780000000000000b7a4e33ad82e028d01610a8f4c2fa52502f14dcff65fd37c9b5000073414200004de34f35bd70e0005c23bcc0000000c51dfc23400038e43b93ccc2445e0afc29641668b41d97e40000ce17d13e873900002f8000000000000000087600028c00000000c7c2c86540003b50000feab44000176800000031e31580000003ba0001e8ce6a000246844851a0000000000a8800026d85acaf00003774220000147a6c0b120007c61cecaa2e1233537b8dcc6b46f417a583c6c674a1939ccc0825eb1631f3636074a8bd0430e976b89d21a1c0e34a22229242ab83320a0131e31c5c305f1c9ccc53fd3a88f001aa39c1e15d5a4fe47093e00440924dc0560d84afc2a907113505ca5300499c0437e1ee057089e03a61514d18446e1804214950c97e8a61db8eb834a4b19ad52402fc6132fd92291303681c79930b9e2971a89ec66b672f38399371525683cc5c446f67ec9b280162ff62108081e8fb87990cf5a5086705082e1cf50887490941d260e0000001920826d387a4d9e6ca740a1344105c42d38d124a08a0000003a60e6e2ef38900000009aa8bb8000bce0003541180688000000363142c5ee75631257b60002fc00013e506708e18a00001b6000000156830c6a632d964884c88106f8718d4e8a09131e188cb58b000013c00003e3690d64df549328b2168a3a0000220000ef45aa0eb1d5c47200032693fc4220003ed8c7e74e79d0ce5e82ea629b20340002de4b9140800000000000000007ea6e00002268b694fe3b500010201ddbcfd330a8c11305e1e6e8c418f0b4c6b40002830000000d74134bc387e43771321ed0e6c80b7620bd9b4c8c84581b899c0ada7c499f9c281467940a797110226c91d98ba8b5c2e40e8c0c255043eb9e0ac0a6c1530001f2a63800000a95a51040002ec01e00001bc3248c188d03c50000000b3e000085847c7bd0003118bac00057027722b112e5f211b986441a6ba800000025e668c5a8fd87882d43a3c97434559714796043c819f33392f504617432260001907691948c5aaf726d1bf8a40b707371a00f24f9c3a10e7220c7e71bb14500000007c29ea18100ac87a361119e5283ff0001ef4eb20000000b0e18060b16f8dd400041e26440000000000000d8700f0000f4d2000000000cf04f0fd500013088685920000c107410902f40efcae0e060d49cc932114089538a8c4caa47f806b40003a60000000000e0a00000017f07ae5451d40b407f723a000000019e0002d2000032406710d8e6000002c1ca8000f2a00039c8ff0000682291847a910565434000077e0000000000cd000043c0000000874000000054e000000059eeb909729703e203015
  | 17 => 0x30444142a00089200005fc00000012d88f45246e232b00005c021e377de9d01e0000000ef0a6144243998c20428b38001e9e0006b42a783400002512a50c5200000000380000003e725a8fa89de5dc2369b7c0660ea80019dc0000d9a95800000060100018d695e48f11e048cfa46af000181c2543f40001d6ece61560001652a453db00003802402203135484dae4a617e8d1cb762c73a21f6e88262408a475b0b8124b12d2ed0846e79ce9140adf0510001b9c44b08a0bc400090d7888cda06ed582078d6185caf63f106a20803261611011e0c38850508e4c443f30f9c08c1ccb3458607302caa5850d8000478d5676c0000ac80006340001a400005db11580006ac13136b0000f30465008038400020c85c9a0435c88725f01ee82a096422400011232500020b200027a10e876200000029412f622580e3c5c81ca5253423c0f303155e83ac10588160f82dad6d09ca6ee3c64000a2d7fa218051c8697fd00001d43700004481aa4857152b128c240000b143522ec70900000000006fa000000000020034e0fe816c7de3afbfec000ca67299bc103021b5544041d9e7bc0002e800000006661efc93cb2c0ab05107a8bfe000424d64505c000035a2dc0004f7b220614c8b00029f000000000000005e0d7003500000000007ad0000ed829a6b33069e2a0003f73f01470b6a4ba38d10d0387354c5d02ecb1258210a00f461e11521ed674ed15332840a804e24ac0001e867166b911393850823f833480901d05fa08b1db4d8a4b034d0000acc0000000bcb06a83594885b506d68e3974a6000072a8000ad85aa0000000000a2240a04393807c484e800168e0ee36900000005cc81c3ae1b2816806685a40007be0f0800194677c4463319f7250c1d7aa08ab43860c2319a158fc8847c2399f82b21723e5875c80a114390904cc8a0003fc4370f100000739d346848b4078ccc0b208b1000000052a47733b20780000a838700000006d101492cc299466a88c00105461ac1a20d26a47ba27a800008b0002608000f4a000000011ed360004509bbce461fcba102702bd814b85cddc00047906bc00051c00000000000005638eac000000125085d21c5dc7970001088000000420210f1220000fa8000e2e7bb00010d836600012c8a8cbd75f5adc98680000f100000003810002e483be9c84eb062008026127d324004ca364941c50a7c00043544f000090a000352143e98c2061e19b700006b136e4394f5000038584ca82015035b00000006922f6112cf99085000189edc67363d48168aba3502db0d7800012b43786db0925c010240002060000a75c2a9a600000006400000003328ec4b2b000455c0000002ce9ff05c40004c5bb718e858400045920960007a220b5520e81606c3b00b505245c0c442d8b7414226de178f6164f9168750c1267c3c613
  | 18 => 0xaae14c0000000dd800000014380000000000000b966360e0d1b880c7790001e80000000000000065f5220229c6490c48c2570c0a2587f32139584fde5d31708f0898600000005ee000319a7c00006ec0001a584d64826370cfc5d840800000005b70ce2760df0a2c97816c00012a46560001d1118c0000000001398f5651733016268a458aa850000ff84b09628000c2c812000101c98a3ce060869c3800d70c040003481fa2635ee40007cd31482500000003791814000000000144c0f8197000008ec1c30b0001cf82601ca26f9bf09fa0000000000caf00000019bc00000023248c40000000001278f350d2292021a9da8360000d2017457d0000000b2800008fcc804e87f93c7000000084503f8c146dd0000002150000246015157c00000025c194417e3e9135a0c00000003f8175cca50001a189542be73005353a0bca1b50001d0047e0570001498f9214500015c50dc0b33e2d8c67960001ea92600007ce8000000f770762b780000004a335400000000000000000a6300014e800000000000022b60001882bf8000b4200035fa2880008460f8800000081517180000006eb3929f56be21091d69e340001ed075a07c00000026688047330913db85500a644c05289a482f5e600020bce56228824400031a00000000004c000022d914cd5a000000000000000037e800048a000000145600020332900650f68212ed18880007f60825fda7600003b7e1c095600045656983ca0000001c08000473ae287bc3b25641fb4000eed00016d17901047f414b000100200027e1ec4df70000000b2000000000000003c000033d8000c8000000007d111200010960fcef05ac0001d4e979819c360094a9c164111db6c56a21700003a800084d00005c282461b8000da60000001e305ea00057500011f8e2500030f80000007e6000143400066c00022aa7063dc0078e4ce1131a04e9ba49f616a3efdf78edb2320001f7aed0349000190ae540000401c200004b1000040800041d280892c55e5f000019708fe38580f9154a9266586c04ceebb54022b470aaac27bb391638c392de32703ec787210af50000fe57140001984fff8ad0e4821103a7f20fac000b1f03637b082018e840a8f0000e00000000000000033a00000000000000a58000af46960000000fca000000000000042a36180003bd7d33fbd8b46ce7dd8911f7413650c800224cbaa7be83000006258940000000c600000000000a640003d206a406363e9d49dc0e3600024b041600000026703a5178257034c9300f30001c340000ba0003e622cc8fa4858001084cb400014380006020eb8001fac3be58d8001992ad474b22b141c00087d000000017b1dd1da04e06092640c48c000000000000c646210001d015541d90991001210ede00d28d045c70324a01f8798e8a2d94011ae60360
  | 19 => 0x36200000001dc5f700014ec0000001079d164a40002e88536bed7468000476ef5562a1d00000002f20000000d7a16e18ac000f1b00000016ac3e400000000004704ad0001f8c00083d00004147ca6ed1081dfcd220001029024ffc6620000000a7965803400000000003431f2e0003dd24ece94fd3827000000019a48fc31111c61475237d1a88d4000000004cc0008b827890b86d852d167959c86e0be87613285a6000342213059f36e4348000fdb19a2bc43dc5f67449aa80000000000000000c0684309e9adc00038430f0dc0a7f09e3188d5c2f33fa172dd3848042b3de027c72412e16b0e8a000043226a14400a1e098687dc8103d206ad3640f57810001fd43a942c2c512d0c385b304d5b1c0007042d380006761cd00003682cc69e43283ee7a00bd000000047639000000000000aa00008cc3ec000181e2d851900030a00000000000ba8000ee400000000000000000000f3cc7600040348b001d0000f45e0865d3138b11348000823ba08000c840002eb0e18c877df0000000c1879300000002ee0790000ae894a3723ec85223d27804038d660e24992ac1cb50120d380002403d61d292f800066e5100320f84000000000038c8044970ad11ca85e826000030c21c0000000000000524c5580000000000001110f4200036000000000000b48f3457600000000007891183c7461a3326cf00e0000c795e719c0af833b7c0415862c0000f60000000b3c3bd00016a4bc6047201c140fdd4663f88000f2400019ec000ac43ab04190685b822f0f81c9042c8163961b40c86404b4e854e35e00031f202cf900000dc533ce645af31fc0000000000001f600000000f5c000f6c000396dc7101309896d9d940001e740194544ea82c1e40e9800000034488b901a7ca18700005443c0800000030900000011c83c28a532800282f80003b320dc65a57632380004860000409d1857a49219140002d50002f79ea8698152387a030bdc5122f741d10c625e150800000000020c82805b0000000196a00006f0001b2cfd45f400000009d260580000003460002db92700fa1341109f0ed9c00038f8000000000000052400076b0888eba00063f09207f00c28140001c260004c7000121e03c5740001e980000000000000850422ad28000000000033d818a7d28936c009ab7c63500000000005a8149a0f0c6d04e2d8005000042c8001c5e8d60000e61e6600085300000e80001e341c8b2c00000019059780fc278160003068c0000ad8000a650000d580e45e6000102cb8e0006e41f180000000001ec8538000000181811b0f200036086603c40001154a90d300c88331faea780002e6a0e08d46e600016b400008f0658dbc1ba26618a98c85ba45f3fb9ffaae100003d80000341f3a7ba0fab19533c1203fc00000023c51680f900018d80000000de17f0
  | 20 => 0x221505f0c60000c5cc94160a4196544e004b000000063068f00017e09a025029780007720d11559d40aa002301a14644448184585decaf3813bd811ec9e8790c244554f643283c80c860766afc4e1e4600065500000000000860d50968f9e00623d00000000002308000e1a00007d40000000000f99a540000c941f0e689d400000009e40dc000083906c0d100000001200000000024fccdb700000000000000b044edf501ea7712a9802c0004a433f951c55826e08c8b8905a17041111d0a186fb1999f845fe6f8bbba1600000000850eb6288301bdf8c841373070ff15861187850000686f1e78f8de91c4a0c5731d849a009a0122e3d3e20000003ea9050f65769b27621062344801301a45782e82c19eb02b06a132f9af00940550c88000ec02480f60d700000004029a0c0000003880000fae0003af147c0000003781f8909e0000001ad4adc44f427c0005e221780000003620f2166069aa9656b317a0922ae11b1b30630a0885f173527257254cc3000008793178e9d9b4e445f30db91cc22b06a4214000e832b38b44cb6af534a32cc51660852700000000005983041b84cae09534299628ce4240bc92c8e7685b3df00005c900021e8a705f0855092c0000003c13f600000000000001ac20000001d7800044612704900000006c440ca1400c614310ae1280001b610980000000000000000b260003c2000000078923a8e444e61a12fb17880008310000e6a6482ca01b8c74ac0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe64655046244001d48c8a08c488003b118d411891001c5f426ed99220008bd84ddb32440011bd07bb664880022fe1176cc91001c5e422ed99220028dd8718f324400717d09bb264880022f613764c91001c5f424ec99220008bd849d9324400117f08bb2648800e2f211764c9100046fc1aec99220008ef825d932440011ef02bb264880023ee01764c91001c5e420ec99220128f4811d932440031f1003b264880022fa1b744c9100061e32ee8992204ecac62dd1324400117d0fb2264880022f21f644c9100061fbaec89922000c3c75d91324405b970e1b22648800a37a1f634c9100064fba6c69922000c9c74d8d32440339b0e1b1a648800327dd0634c9100064e3a0c69922011cd87018d32440011dd0fb1264880032bdd3624c910006563a6c4992200fce870d8932440031ed0db8a64880032dd93714c9100065a326e29922000cd763dc532440019a8c7b8a64880733918b714c9100065bb20e29922000cb4641c532440019aec638a64880033518c714c91000673b10e29922012ce4621c532440011f50db8264880032ed93704c9100065c326e09922000cd863dc132440179d0c5b826488047369c063cc51016e5b3b6c998a2000e5765d8f31440395c904b1e6288047359d863cc5100e672312e598a201cae686d8b314401f9ccedb16628809f399d862cc51000753b20c598a2000ea46418b3144001d8ec63166288003b118c62cc5101745f436e898a2000c3c65dd13144001958c5ba262880022fa1f644c51016c5e43ec898a2000c3f75d913144001878ebb22628800327dd3634c5100064e3a6c698a2019cd870d8d314400193ee831a6288003271d0634c51000657ba6c498a2000cac74d8931440019d0c5b826288117b118a730c51008de9404e618a20018f587d8c3144001d2ec9b186288003a5193630c51008d6ac3ec618a2019cd587d8c31440011ef0eb18628814ab5e0d630c51009572412c618a20128f4865c831440259c8c4b90628804ab9a1b620c51000763b1ec418a2000ea7641883144001d48c83106288003b1d8c620c51028f62318c418a2000ad686cc83144025d88c59906288002b5219320c510097623126418a2011bd0804c83144001d48c5b2442880733918a738851009672310e710a2000ec462d8e21440a19acec31c4288003b1188638851008e6c380c690a200fce870d8921440031f50db8242880033618f704851016e5a3b6c890a2000ea462d9121440031ed0d39a42880733918a734851009672310e690a2019cd476d8d2144001d88c5b1a4288047351d8634851000762310c690a2026ae686dc921440059c8edb92428803f781c3724851001573436c490a200fce476d89214405b974edb262088067369db63c411008e6d3b0c7882200fcea76d8b10440059d4ec3162088003b218c62c4110
  | 1 => 0xd0939ec4880022f61273d891001c77c3a85b122000e2f65d9362440014dd0b326c4880029b61664d89100056741cc9b122000acd8399362440014df0ab26c4880029b21564d891000567c1ac9b122000acc835936244001c5eca326c4880038b19464d89102d752c08c9b122000e8f64d8f6244001d18c9b1ec488163b160763d891000557424c7b122000aad8498f624400155f08b1ec488002ab21163d891000747b20c7b122000e8c6418f6244001d48c920ec48803eb921941d89100053742ce9b122000a6d859d3624400159d073a6c488002b360e74d891000573408e9b12200fae5811d36244001c5ea92a6c4880038b55054d891000557426e7b122000aad84dcf624401f5cb03b9ec488002ba60373d891000557424e7b122000aad849cf62440014dd0ba1ec4880029b61743d89100053742e83b122000a6d85d07624400717d0dba2c4880032b18b74589100045f43ec8b122000c3f75d916244001878ebb22c4880022fa1c64589100061fba8c8b122000c3c7519162440c396ee2322c48800327d9373589100064e326e6b122000ccc62dcd624400193ec839ac48800327190735891000666310e6b1220008de87d8d624400193ee9b1ac488003271d363589100046f438c6b122000c9f7418d6244001938e831ac48818335dc4635891001c5f43ee8b122000c3f75dd162440010ff0aba2c48817e1f21574589100046fc1ae8b1220008dc835d162440011df04ba2c4880023de0574589100045f438e8b122000c3f751d16244001878ea3a2c48800327dd373589100064e3a6e6b122000c9f741cd6244001938e839ac4880032bdd37258910006563a6e4b122000ccf73dc96244001998e7b92c4880032d1d371589100066a39ee2b122000cd873dc162440bd95cedb20c4880038bd9764189102ef52b8ec831220008ed8799062440014dd0b320c4880029b616641891029d57424c83122000ace83990624400159b07320c4880023be1d641891000537c2ac83122000a6c85590624400159f06b20c488002b320d64189102e573c0ac8312205baae8619062440b595cec320c4880038bd94641891000716328c83122059ea5811906244001d4ce2320c488167a95c464189102cf53080c83122059ea41019062440b199cedb18c488003a3d93631891000746326c63122057ec581d8c62440afd8ae3b18c4880023b61e631891000557424c63122000aad8498c62440a359d07318c4880023be1d631891000557c22c63122000aac8458c62440ad5cf02b18c488156b3a1863189102a6673b0c63122000e8f6418c6244001d18c8318c488143b1e04631891028762b88c63122050ec61018c62440a1d8820318c488143b2040631891029d73434823122000e64659046244001d48c9208c488003b118e411891013d72432823122000
  | 2 => 0x272d8d100056b408e5b1a2019ad5811cb63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b63440014bd0ba0ec6880029761741d8d100cc6f43e43b1a20008dd87c87634400153d0990ec688002a761321d8d100061f3aec931a2000c3d75d92634400195ce5b24c6880030f9d46498d100061eba8c931a2000cae72192634400193ce9b1cc688003275d36398d1000667396c731a2000caf645ca6344001958c8b94c68800333d8d7298d102fc3f42ee931a200087d85dd263440051dd05ba4c6880023b60b7498d100045ec3ce931a2000c3e759d2634400717f0eba4c6880030f9d57498d100061ebaae931a2000cae749ca634400195ae9394c68800a3be1d7298d10006573a2e531a2000cad745ca634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac72191634400195ec9b92c6880032b1937258d1001c5f43ee8b1a2000c3f75dd163440010ff0aba2c68817e1f2157458d100046fc1ae8b1a20008ef825d163440051d904ba2c6880022fa1c7458d100061fba8e8b1a2000c3c751d1634400193ee9b9ac688003271d37358d100147743ee4b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000657ba0e4b1a2000cac741c9634400199ee6392c688003391cb7158d1000674396e0b1a20008df8758c634400153f08b18c688002a72116318d1000567c12c631a2000acc8258c634400153d09398c688002a76127318d1000567414e631a2000acd829cc63440014bd0ba18c688002976174318d1001c6ec3c8631a20008dd8710c634400117f08b90c68800e2f2117218d100054f4206431a2000a9d840c863440cd93cedb20c68800387d976418d100046ec3cc831a2000a5e8599063440014bb0b320c688196a7a126418d1000567414c831a2000acd8299063440011bf0eb20c68800297e156418d100052e42ac831a2000acf82590634400159904b20c688192a7a186418d1031e4f3b0c831a2000e1f651906344001c38ca320c68818ba56046418d100054f424c431a2000a9d849886344001d28c9208c688046b52194118d100074a3228231a2000a5e859d063440014bb0b3a0c688002b5a047418d1008d6ac08e831a2000e1f549506344001c3aa82a0c688002a7e117218d100054e422e431a2060ad7815c863440015b700b90c688002a7a107218d100054ec20e431a2000ad6811c863440235ab02390c688046b6a007218d100056cc00e431a2000ad681d0863440015ab03a10c68800237a1c4218d100046ec388431a2000a5e8510863440014bb0a210c68800297a174118d100052ec2e8231a2000e954110463440231bd0f908c6880023761f2118d100054f4264231a2000a9d84c84634400717
  | 3 => 0x418a4000ce57218431480051f10cb8062900033618d700c52001c5f43ee8b1e2000c3f75dd163c4001968e3ba2c7880021fe157458f102fc3e42ae8b1e20018f4815d163c400117d0e3a2c7880030fdd47458f100061e3a8e8b1e2000cb4711d163c40011bf0eb18c78817e1fa177418f100043ec2ee831e205f87e85dd362c40010fb0bba6c58800237a0f74d8b100046ec1ee9b1620008f681dd362c40d95cd03b92c5880022fe1176ccb1001c5e422ed99620028dd8718f32c400717d093b265880022f612764cb100047b40cec99620008bf845d932c400717908bb265880723de05764cb100146f43ec69962019cd870d8d32c40239b0e031a65880063d618714cb100e47bc32e598e2000cda635c031c40031eb0fb1863880023de1d630c71009672312e418e2000ad586cc831c40015af0c9906388046f4201320c71000c7ac30e710e20008bd8799764440d747d0b32ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec8880022fe1d65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91103551f430cbb222069c3e7619764440d1c6b0232ec8880028fa1662d91100051ec2cc5b222000a9e8398b644400153b07316c8880038d19651d911016d5a432a3b222000c3f759d7644400187aea3aec88819eada0475d911016d5ac08ebb222029ab681dcf644405b56b03b9ec8880028fe1573d91100051e42ae7b2220008be87d4f644400117b0fa9ec88800387d4e53d91100051f42ce5b222000a3d859cb644400153d07396c888002a760e72d911012d5b408e5b22202dab5811cb644400117d0e296c8880022f61c52d91100054f418a5b222000a9d8314b644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644405b17d0fa8ec8880022f61f51d91100071ba8ca3b22202d8be87c87644400117b0f90ec8880028fa1721d91100051ec2e43b222000a9e83c87644400153b0790ec8880bb2d5c464d8d1000c7ac0ee9b1a2000a5e85d0f63440014bb0ba1ec68800e37e1d43d8d100054f42065b1a2000a9d840cb6344001c3ecbb26c68819ba55c764d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c6519363440c7d2b02326c68818fa55c464d8d100054f424c5b1a2000a9d8498b6344001d28c920ec688066b521941d8d100056b40ee9b1a2019ad581dd363440014bd0a3a6c6880029761474d8d100056b408e9b1a2019ad5811d363440335b5003a6c688002b660074d8d100070faa4a9b1a2000e1d54153634400153d09b96c688002a761372d8d100cd6ac0ee5b1a2000ad980dcb634400153d09396c688002a761
  | 4 => 0x388401974e8b86c7108032e5d170d8e210067938ae1b1c4245ad681d8e63884011bf0eb18c71097e1fa177418e210043ec2ee831c4200ce5729c463884259ccc2b90631080e2fa1373582210045ec26e6b0442128f681dcd608840717d0fba2c6908030fdd77458d210043fc2ae8b1a425f87c855d163484011ef02ba2c6908023ee017458d2100c7c402e8b1a42008be871d1634840187eea3a2c6908030f1d47458d210065bba6e2b1a4200cb474dc563484031f50fb82c6908032edd37058d210065c3a6e0b1a4200cf371dc16348401976e8382c6908032e1d07058d210066db98e0b1a4200ceb721c163484019e6e2382c69080237e1d6318d2138d6bc0ac631a4200ad88058c63484bf0fd0bba0c6908021f6177418d210056ac0c6031a4219ad88058e31484011bd0e31a629080237e1d630c52138d6bc0ac618a4211ad88058c314840117f08b9ec09080e2f21173d81210e47bc0ae7b024200cd8601cd604840717d09b8ac5980022f6137158b300146ec1ee2b166000d9870dd132cc001ba0e1b8a65981c335dd8714cb30006e8380e29966042ad683d8661cc0335b100994c3980023de1d611873008e6d31ae018e60038be84dda21cc00117b09bb4439800e2fa1276887300045ec24ed10e60008bf845c7624c00717908b8ec49800a3720d71d893000672310e2b126000ce7621c5324c0259c8c438a649802f3a18b704c9302764e3b6e89926000d9870dd1324c0399a8edb8a6498003741c3714c9300966a3b0e29926000dd0701c5324c0033b50fb826498077361db704c9300047bc3ac230a6052ad783584614c0015c904b08c29817e1fa1774185300043ec2ee830a6011ad8804c8614c0015ab07908c2980da76e1d32cc13000d6c43265982600bec8624cb304c0014bd0ba1ec69017e1fa177498d200043ec2ee931a40008f681dd263480011eb03ba4c69000e2fa1f7458d200061fbaee8b1a400087f855d163480bf0f90aba2c69000237e0d7458d200047bc0ae8b1a40008f4815d163480011f700ba2c6900022fa1c7458d200061fba8e8b1a4000c3c751d16348001938e9b9ac6900032ddd37158d200065a3a6e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000cbb74dc16348001970e9b82c6900033cdc77058d200067838ee0b1a40008df8758c634800153908b18c690002b52056318d2037d6dc02c631a406ead9809cc63480014bd0ba18c6900023761c4318d200045fc22e231a40038bc845c463480014ed0ba0ec2900023de1d61185200055a422c230a4000ad48358461480db5cf04b08c2900022fe11731852001c5e422e630a4000a7685d04614800717d093b262900022f612764c5200045fc22ec18a40038bc845d8314800717d083b062900022f610760c52000c76432e
  | 5 => 0x88022fe1d65d91310051f430cbb226200c3e76197644c40147d0b316c8988028f61662d91310051f42cc1b226200a3d85983644c40187eeb3aec8988030f5d475d91311e55b40ee7b2262008be87d4f644c40117b0fa9ec89880387d4e53d91310051f42ce5b226200a3d859cb644c43153d07396c898802a760e72d91310045f438a5b2262008bd8714b644c40153d06296c898802a760c52d91310045f43865b2262188bd870cb644c40147d0a196c8988028f61432d91311e54f41ee3b2262008be87d47644c40117b0fa8ec8988038dd4651d91310045f43e43b2262008bd87c87644c40147d0b90ec8988028f61721d91310054f41e43b226200a9d83c87644c40147d0b386c8988028f61670d91310c55b40ce1b226200ab5819c3644c40117d0e286c8988022f61c50d91310055b408a1b226200ab581143644c40117b0f186c8988028fa1630d91310051ec2c61b226200ab6818c3644c40156b03186c8988022fa1c20d91310045ec3841b226200a3e85083644c40147b0a106c898802a7a0c20d91310054ec1841b226200ab681083644c40156b02106c8988022fa1c10d91310c45ec3821b226200a3e85043644c40147b0a086c8988022fa1f64589310061fbaec8b126200c3c75d91624c401970e1b22c4988022fa1c64589310061fba8c8b126200c3c75191624c401970e0322c4988032ed9370589310065c326e0b1262008be86dd1324c401878cbba2649893e2fa1f644c9312745e43ec89926200c3f75d91324c401878ebb2264988032e1c3644c93100674386c49926200cb764dc5324c401968c9b8a64988733918b714c9310065bb20e29926200cb4641c5324c401976c9b8264988032e193704c9310072bb2ec318a62038be86dd1604c4311790dba2c0988022fa1f64581310061fbaec8b026200c3c75d91604c401958e5b22c0988022fa1c64581310061fba8c8b026200c3c75191604c401958e4322c0988032bd93725813100656326e4b026200d9774dc5320c401b28e9b8a64188733561b714c83108ced43ee09906200dd371dc1320c401b36e83826418803661d0704c831006e9b88e09906272dd0711c1320c48bb8e42b96621884a75e1d328c431096e3392651886242bd0804ca310c485ba460b846218803271d3764c4310066b28eec9886200cd551dd9310c40193eedba262188032d1d3764c4310066b29eec9886200cd553dd9310c40196eedba26218846b6203325803108c6e43a64b006211ad8804c9600c4bf0fd0bba6c7108021f61774d8e210047b40ee9b1c42018fa80dd363884011f301ba6c7108022f61e74d8e210061f3ace9b1c42038bf875d3638840187ceaba6c7108030f5d574d8e210065b3a4e3b1c4200cb5749c76388401974e9386c7108032e5d270d8e210067938ce1b1c42018fb875c36
  | 6 => 0x53cc2cc9b026400af281993604c8015e303326c0990029ee1564d81320053c42ac9b026400af381593604c8015e102b26c0990038ed9464d81320071c328c9b02647ae9983193604c801d30c921ec09902eb621943d81320ed7543665b026400eb364d87604c801d60c9b0ec0991dfb460f61d81320055d424c3b026400ab984987604c80157708b0ec099002ae21161d813200759b20c3b026400eb064187604c8014f50b3a6c0990029e61674d81320057940ce9b026400af1819d3604c8015b5063a6c09902eb660c74d81320071daa4a9b026400e3954153604c8014f50ba1ec0990029e61743d81320055d426e3b026400ab984dc7604c8175b307b8ec099002ba60b71d81320055d424e3b026400ab9849c7604c8014f50ba0ec0990029e61741d813201c5f436e8b02644e8bc86dd1604c801970c1ba2c0990022fa1f64581320061fbaec8b026400c3c75d91604c80117d0e322c0990030fdd464581320061e3a8c8b026480c9f73191604c80196ec9b8ac0990032d193715813200678306e2b026400cb7641c5604c801968c838ac0990033c18071581320047b43ec2b026400cb774d85604c801968e9b0ac0990023da1c61581320065bba0c2b026400cb474185604c8ff9aee630ac0991fb2e9db64181320071db2ec8302647de9973d90604c8011f30f320c0990029ea1664181320053cc2cc83026478aba84990604c8015e503320c099002bc60664181320047dc3ac83026400a7b85590604c8014f10ab20c0991f2b6e0d641813200579c0ac83026400af081590604c8f75750c320c0991eb2e9d864181320071db28c83026400e3865190604c8f3d3306320c099003a69cc64181323cf4cb98c83026479e9a32190604c8f3d3064320c0991e2b6a1a43181320072c32c863026400e986490c604c86b5b10ca18c0990039619543181320074c322863026477cf276d84604c801d66c9b08c099003ac19361181323b768c1ec23026476ed173d84604c8011f30f308c099002aea1261181320055cc24c23026472af281984604c8011f70eb08c099002aee1161181320055c422c23026475adb83584604c8e95e50c308c0991cf3c9d8611813200759b20c23026400eb064184604c8e1da706308c0991c3b45cc611813200769218c23026400ed143184604c801dc664308c0991c3b48c8611813238768190c23026470ee032184604c8010ff0aba2c59897e1f2157458b3101c7643a84b166212ce6621c5328c49d93eedba2651880355dd7714ca310966bbb0e299462199da87dc1328c4179b6edb8265188d736dd8704ca31006cdba0e09946200d98741c1328c401ba6e23826518803741c4704ca310043fc2ae8b04625f87c855d1608c4331bd0f992c118866b6201325823101c7c43a80b0462008bd87997644c40147d0b32ec89
  | 7 => 0x7585d07614c8071ef0ea0ec299002ada1010d85320055ac2021b0a6400e3765d93614c90bd2ae7b26c2990029da1664d85320053ac2cc9b0a6400af280993614c8015e301326c2990029de1564d85320053a42ac9b0a6400af380593614c8015e100b26c2990038dd9464d85320071a328c9b0a6482e9583193614c905d2ae6326c299003a519243d85320e56a43287b0a6400ab684983614c80156b09306c299002b5a0f74d85320e56ac1ee9b0a6400a76851d3614c8014eb0a3a6c299002b5a0c74d85320e56ac18e9b0a641cae6821d3614c8015cb043a6c2990038dd5254d85320071aaa0a9b0a6400a7685d0f614c8014eb0ba1ec299002ada1370d85320055ac26e1b0a641cad583dc3614c8015cb05b86c299002ada1270d85320055ac24e1b0a6400ad6831c3614c8395ab06386c2990023da1c40d85320047ac3881b0a6400a7685103614c8014eb0a206c2990023d61e30d85320055b42461b0a6400ab5848c3614c80187cebb24c2990030f5d764985320065d386c930a6400c3e75192614c80187aea324c2990032e9c064985320065b3a6c330a6400cb574d86614c8019e4e1b0cc2990032ed9170985320065c322e130a6400cf3615c2614c80117d0fb22c2990030fdd764585320061e3aec8b0a6400cb870d91614c80117d0e322c2990030fdd464585320061e3a8c8b0a6400cb870191614c801976c9b82c2990032e19370585320047bc3ac230a6400ab784584614c80156908b08c299002bce01611853200578402c230a6400a7685d04614c8014eb0ba08c29900e3d61e41185320045fc22e030a64038bc845c0614c80156d08080c299002ad610101853242e5b3b6c830a6400e3765d90614c8011eb0f320c2990029da1664185320053ac2cc830a6484ab684990614c8015e501320c299002bc60264185320047bc3ac830a6400a7785590614c8014e90ab20c299002bce01641853200578402c830a6483ab686190614c90596cec320c2990038dd9464185320071a328c830a6481e9583190614c801d28c9218c29904ab521943185320074a3228630a6400ab684980614c80156b09300c2990029da1674185320053ac2ce830a6400ad6831d0614c8255ab063a0c2990038dd5254185320071aaa0a830a6400a7685d0c614c8014eb0ba18c299003a550c43185320055bc22e030a6400ab4845c0614c8ff5af06b80c299002b9e0970185320055b420e030a6400ab5841c0614c8015ad06380c29904ab560c701853209573410e030a6400ae5821c0614c8015ad07a00c299002b560f40185320047b4388030a64008f587100614c8014ed0a200c2990029d61440185320047ac3c6030a6400ab6848c0614c80156b09180c29900e2fa1271d81320045ec24e3b0264038fb87503604c801c76cbb26c0990029ea1664d81320
  | 8 => 0x400001000800000400400400000400000001800800000800000400000006000800003802000400000000000000c00000800800000000800000800000000c00801001400800000400400400800c00000400000002000800000c01800800000000400800000000c00c00000800c00000400800000c00001400000400000001800400002000002400400800000400401000800000000000400400c00800400000400801c00800400400000000401000800001401800401800800000c00800400400000001000000000000000c00000800400800c01400800000000400000000800c00400003000401000000400000800000c00001004800800000001400400000001001000c00800c01000800c00400801400801000400800000000801000401400000000000000000400800400800000000000c00c02000c00000000000000401001001001400c00000000000000000400800000800000c00000001001400400000000000400000000400000400400000000801000800000000001c00000801800801000400000000c00001400c00001000400802000400c01400400401c00000401c00402400001400001000400800000000000001000402800401c00000000400000002000000000002400800c00801800400001000800000000000000c01c00000801000000400000004000000000400800000802000800000000000000400c01800c00400c00000c0000080180180717d0fba2c3990030fdd774587320064e39ee8b0e640087f855d161cc8bf0f90aba2c39900a3720d74587320061fba8e8b0e6400c3c751d161cc801938e63a2c3990023de1d61187320045ec3ccbb22648aa3e85997644c80156d0332ec899002ad60665d91320055d404cbb226400ab980997644c80117f0eb2ec899002ade0565d91320055a40acbb226400abb80597644c80157100b2ec8992268fa1865d91324461f3b0cbb226487e1d83197644c801c38cb29ec89913aa721953d91320051f42cc1b226400a3d85983644c80156d03306c899002ad60660d91320061fbacebb226400c3d751d7644c90d53d063aec89913aa760c75d91322745f43ea7b2264008bd87d4f644c801c3ea729ec89911aa7a0f71d91322754ec1ee3b226400a3f855c7644c8014790ab8ec8990022fa1f51d91320045ec3ea3b226400e3751947644c80147d0b386c8990028f61670d91320055b40ce1b226400ab5819c3644c87553d06386c89913aa760c70d91320045f438a1b2264008bd87143644c80156d02286c899002ad60450d91322745f43c61b2264008bd878c3644c80147d0b186c8990028f61630d91320055b40c61b226400ab5818c3644c80117d0e086c8990022f61c10d91320051f42821b226400a3d85043644c89f93ae6326c29900a3760f74d85320053b42e83b0a6400a
  | 9 => 0x80a188a390c2074cc8001c40000fe018c000f30000be02006ed64c000002301310941129a18ca8000b8d8a9e180000015a8b00ae1730000000001bf80000003bdddc000000000000000bc8000000000000000001c80000000000001db40004d40011bc0021d9f01a38000000000000000000000000000b700005d8000001eb03fc000000000000000002190db05600000011d0ac8518c28000001fca128000000001520000090001a316393b1c98000001fa40023b16f8000000001f28808c4e31800000043c000000000001d18000b0c001268000000000001908000000000001950000002208001164c70000bdd0f80000003b0a400000000011a80008500000000000021340000000000000000000020e025000000000000000000089017202c7040000000013c0000830cc0000499c21ed0a01b58000000000001f4068a308000000000000000001af0001fa14d95cc0000706cc6540000580000000000000f0b48f188680000000000022389508711380020fc10a1700000b8218001e00000000000000001b78d511a40000000019180000000000000000018980000000000b0000c64af0000388d70001ad0781540000000001358000699fb9bd0bf02d0ba5d686b0001e704d8000000000e1942d9b9b442307fc001ac9f70001d8236955a0c85d0000d286220d1af5ef4da1ea8384000000959642330000000000001764908000000001d000000000020245812884200000000001e800000147a13c000000000001b810e0910001570000000dbc5e0000b10e78000000520000000000000999190d18000000001a700000012c80020e4a287b80000000000017c80000000000011b16800000000004c95d07380000005992ba3719c9d91f758517d88805a05a976cb38c20001440000000000000000c88000a880001f0000a65510000000ac19900000000000000000000000018a0000bd6218001038000000000be81c40007695d8900801234000001338000a680000000000000000014c0f79dc57b40000004b400040210dfd8001e09c780001b526471c0000000000000000007400000000000014321b13b5240001b8882de80001ff8000000000001758fc00000000017b8001be0000000000001185cf9ec800000001000800400000001000000000000000801000400000000400400000000400000000c0000100040000000040080000100000000000240040080200000180000100000040000100e400000001c01400000000000000400c00c00c00000801c00000400000000401001400000402000c01000000000801000400000000400801400400000800800000c00000800000001000000000000000800800000001c00000000401400802800800000400000000000000800401000000000c00c00400000000001400002000000000000
  | 10 => 0x11e92189c9f31b50000000000000001a684a80000000012f00980019d1198730fec001970000e48500000000000da80022f08400017740009d800000063c0002100000000000019100000004882095280000018d0001c01068000000001cb2270088000001df0e517c0001a88f28000000e1c328000de0c911093e00000000000000000000000015a40000000000000000000000000000014600000000002600024604fc7f88d8000bf80000000000000000017000011c800177df20001468149e6a3c01841346b4248b980601206106e47505f9360548e686d8000b853c8000001ce0000000000000000000000000000002098000000000360030f086240013a8002088001c7c478c6800017800000000110000000206e2b1dc000000207a450001f8901a020001980000000000aa4000000000dc0001a00000001e40c485596e16d22a8000000000000a594100012498b0001330eea3e0000816379ff0000001e7c948000000000000000000000b40000000000000000000000000000000000000cd90d80000021c8000798000001ca0000000000ae80016f1cb4001df4001a60dd0f71888001f089d4fc80000018c0a700000000004b0dc8ada3a02a5168000000000000000001120ba8000cd18490c8f982424186fc84ca480006f18f1f617fd8699b14d0001e100007880000000000000000016c8f51e89b68000002290c955811c0280000000c60000001f50bd8000000000e9000037d8f8359709d300000015387206c4000e21070000000000000af618003800140800000000000169800208c000b61821f6dc580017600000008580015314f0000001fe00000000002a863566981c3e40004f6260f20000000b2c0000017e1e600e99c0bb98c8000000000000000774000b687f40000000020b00000000000014463c939a200000659fc0920d58d24cf9e30001b18000000000001cd8d30000a54528001931a5203c05238150c0018380019e9c11d4120d6b8540000a61c756f4000000000de8268001a40c505649900000010a00000010843040000017191da108000ca40002f0000000424000000000001390000bd00000001c0000f68ad00000000021680015d4e600022300016cc0c1b6e070fa8ac52b1938ec00000000014390e81b0000000000000000000000000001010805d480000009d000169000034800035d5ea480589a540004381014500000000006451e00014a8000002148b797d1bca1f0848829b480000016880017880000001f50000016641e0af8a91de00004ac000040001e491800000000000000020a4000000000002280001db15f9d340000000000000000000000023580000000004c00000019408bc0000012e00000015a10b00020a0000000001428000000000f881a8c6c000000002288000001498000002028481
  | 11 => 0x23f80000014c4000000000001bd800000045913000023d3697f1831230228009f922482f8000fa0000000000000000671058001afc0000000012e85f0001e5a2112600024916200020900016c4119b64bb0001f15d8a1500024580012d8a6c0f8460000aaa4798d800000000092a05a29c770161ea04291703540000014000000000000017703d00000014e00002a0000000000000000000000000000001220cb80000010480015c19980009ea000819858d9891971dae80000000000000000000000006c00000000015900000000000000020f1c60000001f59d59ab0002214728000000f918407085500000005b8000000001948afc0000015c9cc80008f1188000000000000000000000c81828ab23b80021a40000000000000000000009f80000000014820f8000001b380000021249f14891a239173e19c000180bc13486e0eb0290eb88e8860001a220318b8d88000001c90b800000009e2340ff0000002351e294e4001d7000000000119c000002278ec8000002439b4117819012d1505e8aa03d93ba400000000000001cd00004704313d1d08b500003400004906ac000001079ef9228002184f01d9a228000811b71cfd418001c680000000000004f8e5800000156032087830061dc38000000001508000000000000000000001f48000c12119f680000023a9118000000acd259a993a053248894400077d318000000001e8ce380000024a80000000e201908c0000021a17294c880c0011400000003680000022f83780011f1cb9f78d9cca09680784b9ccc5913bd3e951917e1387797683f8000e4041c7946f8d903c1e521100d944e4080007a2338a18000000000000000001be8000001f9a4223e8000f4829c8b4289bb07195dd55c2e90a565a0a8000000000000fe9ec0000000000001a90570000000000000000001ac030a1b8000000000000000000000001300c7c000000000c99d290500015480004f00020e80000000000000020d8000c78398604344000330d20390e805b0000000000000c00189b9e469458a086e9bf19615994ccd08435739c88000b899683111b84a07f0b583257f8000001add26c9880001c9380000001e940023480007d0cb14b0000d0c000001c500004dc00108000041000066062c0008a4e281ba0096d80003e06a1b080004e8000000000000000000001f1c000000001eb82700000000000000019a0000020d80aac0020dc000001610002161a100000016a80019017908e0000000000000000964000000000f58b1507481c000d48ee18900000013098808b8000000001250000c04ab82fc7580002e0000001f80d38000000000001e7813a0340015680010306083b80000014e800232093a140c397a17b0001d218716600011de4b19e0081c297502780000007022b8001c493700011040000000000
  | 12 => 0x1c70bf41a122c00000000000000000000000000181000016831dc3000000000247525c0000000000001d09b9da00000000000000000000000001106a8000002311b30000001ce8001dd4930000000001704258c30002130001dc86b9aa0618001cf1efc000000001a580000000010905c8bc4000000000ff8000b280000017780010f1b98000000000000000748fb80000021e80019580000000000000002d4001d5197a120ce92f845400000000000220cd79a282b00000000012116500022680000018e0ed80482340009a9d380000018e8000000000898e09860001bb8000000ef00005119280000000000020500007e94a0000000001564f800017a8000000000001ae0002250000000000f108c8508b3e4a04e1160000000001b8495d678140dd88a00000000000000010d1dcc000ea0000f39600000000440001c8d0b8068001ee19d8000001a49ad4001389a809600012700000000015c4001fe8000000c08000001db8000d10000f6000000249e42800060000000000000040d0088d1685eda0f5d3c0000000000020c14f91480015f1da97dc000000000000ce0000734000678405a5c6c80000009bc0008b00000000008340000000012987c92812553d9e380001500000009b0bec628000000001350000001b3c002199e25471f11b20000000b180000000013d4001d620c4000000128cf00010a967000000000000000000166c468978000000000668001ca93ce2e00020497e4001df9dea2c8000000000000000465878000fd8000000001200000028002440000000df000000217a3980003c9a780000000012d0000000000000000000000000002498c180006800011100022a1d784514fc000000000000000001d114dde20a78000000e303e8000790408b20000002038000002410000000000001dbc0000000000000000008ac0000000000022d80000000000a01dd18e081caca816a0b90000000001dec001b240003a000052400000093c000000002448e700006395000011d53400009a07620600181f8298000000000000000001781ef08a9afa0117998184196e90203f6258444651618000001bc00007e0000011c195b00008f8002244001ee8fb21f80000024b8b321a81e4e98c58970d413799f14b93f8000000d049821d0000000e10000538001578712068000001e98001061c098023886d07aa084f40000000000000001ba9320000000000d950292c0001bddfd0000000000000000000e880022e80000022a40022d000236124d6c1ab8ba0001dd0d2c1316095500021580021c00000000009c00022415883a9b60a223d109c0010423d9a0d2a1238df8000000000000000000000000001d5cea96b13294496283523288380005696480000000015ac000001720a5c001dd97480000000000002dd6ec001d542ca040a1
  | 13 => 0x178c0020b8000ed00001cca991f80012a9cc1b00e140014200006300007c02d8000000000000a50000000000000001aa8000001ce4000000000000001ba01bd1749b516c0004480002393f0000000000000000000000e001580005c21e00000000001d8000000000001089b10000001fb0000000000000380b240d0000001099f18001794000000000000001e840000000003ec79c001a083f0a30d60db80000004d0000000370000000000001e90000000001cc59203380000000000000000000000000008895e0001740000000000001c957e8000c540013c4c402c031a2214f647000051e298d0127a4c22c0000000000000000000002100000000221f39710b082b8fd07d800000000127c0000007b08c1630cacef99f95ed5b80014264c93ac640000001fa80a80000000004756fc0008223f0d6906c649b1c000001b9000198a43149000217c0005780019a8691b2800000129000000033d209ad80c8199158
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x3140011c2022060000000103f985d475d91320048de6154153614c8012379855054185320048ee6154153604c80103f985d475d91310040fe61751d7644400121f9855054d8d1000487e6154150634400122f9855054d8910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x94b
  | 5 => 0x94d
  | 6 => 0x138b
  | 7 => 0x138d
  | 8 => 0x98d
  | 9 => 0x9cb
  | 10 => 0x9cd
  | 11 => 0x168b
  | 12 => 0x168d
  | 13 => 0xb09
  | 14 => 0xb0d
  | 15 => 0x1409
  | 16 => 0x140d
  | 17 => 0x249
  | 18 => 0x24b
  | 19 => 0x24d
  | 20 => 0x144d
  | 21 => 0x16cd
  | 22 => 0xb49
  | 23 => 0xb4b
  | 24 => 0xb4d
  | 25 => 0x1449
  | 26 => 0x144b
  | 27 => 0x16c9
  | 28 => 0x16cb
  | 29 => 0xcc9
  | 30 => 0xccd
  | 31 => 0x1709
  | 32 => 0x170d
  | 33 => 0x138955
  | 34 => 0xb0955
  | 35 => 0x94b15
  | 36 => 0x140955
  | 37 => 0x95415
  | 38 => 0x124b
  | 39 => 0x209
  | 40 => 0x24955
  | 41 => 0x94255
  | 42 => 0x16c955
  | 43 => 0x956d5
  | 44 => 0x1549
  | 45 => 0x1489
  | 46 => 0x289
  | 47 => 0x138b15
  | 48 => 0x4b
  | 49 => 0x139415
  | 50 => 0x138255
  | 51 => 0x1396d5
  | 52 => 0x3c9
  | 53 => 0xcb
  | 54 => 0x15c9
  | 55 => 0x12cb
  | 56 => 0xcc9d5
  | 57 => 0x1709d5
  | 58 => 0xcd695
  | 59 => 0x171695
  | 60 => 0xb4255
  | 61 => 0xb4256
  | 62 => 0xb56d5
  | 63 => 0x25455
  | 64 => 0xb5455
  | 65 => 0x256d5
  | 66 => 0x144251
  | 67 => 0x1456d5
  | 68 => 0x24b55
  | 69 => 0x16c253
  | 70 => 0xcc255
  | 71 => 0x170255
  | 72 => 0x144b55
  | 73 => 0x16cb55
  | 74 => 0x16d456
  | 75 => 0xcd455
  | 76 => 0x171455
  | 77 => 0x170cd5
  | 78 => 0x178b
  | 79 => 0x58b
  | 80 => 0x24211
  | 81 => 0x20251
  | 82 => 0x25451
  | 83 => 0x20291
  | 84 => 0x25411
  | 85 => 0x21451
  | 86 => 0x216d1
  | 87 => 0x144211
  | 88 => 0x145411
  | 89 => 0x28211
  | 90 => 0x29411
  | 91 => 0x21491
  | 92 => 0x21851
  | 93 => 0x148211
  | 94 => 0x149411
  | 95 => 0x6
  | 96 => 0x25551
  | 97 => 0x29551
  | 98 => 0x28251
  | 99 => 0x29451
  | 100 => 0x25491
  | 101 => 0x24291
  | 102 => 0x149451
  | 103 => 0x954d5
  | 104 => 0x2d491
  | 105 => 0x2c291
  | 106 => 0x1494d1
  | 107 => 0x1482d1
  | 108 => 0xb0211
  | 109 => 0x21411
  | 110 => 0xc9d3
  | 111 => 0xd693
  | 112 => 0x240d3
  | 113 => 0x256d3
  | 114 => 0xc253
  | 115 => 0x25693
  | 116 => 0xd6d3
  | 117 => 0xd453
  | 118 => 0x16c0d3
  | 119 => 0x16d693
  | 120 => 0xc593
  | 121 => 0x580d3
  | 122 => 0x59693
  | 123 => 0xd793
  | 124 => 0xd8d3
  | 125 => 0x1780d3
  | 126 => 0x179693
  | 127 => 0x252d3
  | 128 => 0x592d3
  | 129 => 0x58253
  | 130 => 0x596d3
  | 131 => 0x25793
  | 132 => 0x24593
  | 133 => 0x1796d3
  | 134 => 0xcd7d5
  | 135 => 0x5d793
  | 136 => 0x5c593
  | 137 => 0x1797d3
  | 138 => 0x1785d3
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 43
  | 7 => 882
  | 6 => 2237
  | 5 => 1178
  | 4 => 9
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1258+((h/20+packedAt gbK8 (1118+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (37133+((h/409+packedAt gbK7 (32634+(h % 409)*11) 11) % 1960)*11) 11
  | 6 => packedAt gbK6 (118860+((h/957+packedAt gbK6 (107376+(h % 957)*12) 12) % 3790)*13) 13
  | 5 => packedAt gbK5 (75370+((h/489+packedAt gbK5 (69502+(h % 489)*12) 12) % 2835)*12) 12
  | 4 => packedAt gbK4 (642+((h/3+packedAt gbK4 (630+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fe03ffffff807ff80ffffffd8733f8cfe31ff
  | 1 => 0x80ffc0fe01fff80fff07ff802f9cd8f363ce7c
  | 2 => 0xffffff0001fffffffff80ffff01fe0ff83ff8f
  | 3 => 0xfffffffe00000ffffff0003fe0ff03fc0ff0
  | 4 => 0xfffffffffffff0000000003fff0003fff000
  | 5 => 0xff00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2920059693284292800a9caa88310b842e10b5
  | 1 => 0x8862c0aa315ac885a907ad018b9458b162c65c
  | 2 => 0x52956a004095152952d00255300aa05a816b0a
  | 3 => 0x10d9b34d6401810e7ce5400635c0f503d40de0
  | 4 => 0x60fe3cf1f9e7e7c0184184183eff0003fbb000
  | 5 => 0x7c10208181060600608608603f7ffeec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37443
namespace PEqualNP.Outside.L_meta_37443
open PEqualNP.Outside.L_meta_37443.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 19 := block_range (n:=19) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 19 := bs2_3_0
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
theorem bs2_4_128 : Interval s2Atlas 4 128 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 144 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
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
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
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
theorem bs4_4_512 : Interval s4Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 bs4_4_224))) (concat (concat (concat bs4_4_256 bs4_4_288) (concat bs4_4_320 bs4_4_352)) (concat (concat bs4_4_384 bs4_4_416) (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_160 : Interval s5Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_224 : Interval s5Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_256 : Interval s5Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_320 : Interval s5Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_352 : Interval s5Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_512 : Interval s5Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 bs5_4_224))) (concat (concat (concat bs5_4_256 bs5_4_288) (concat bs5_4_320 bs5_4_352)) (concat (concat bs5_4_384 bs5_4_416) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_64 : Interval s5Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_128 : Interval s5Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_160 : Interval s5Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_224 : Interval s5Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_256 : Interval s5Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_320 : Interval s5Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_352 : Interval s5Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_416 : Interval s5Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_448 : Interval s5Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_512 : Interval s5Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_544 : Interval s5Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_608 : Interval s5Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_640 : Interval s5Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 9 := bgb_4_0
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
theorem bgb_5_1152 : Interval gbAtlas 5 1152 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1178 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152))))))
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
theorem bgb_6_2208 : Interval gbAtlas 6 2208 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2237 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))))) (concat (concat (concat (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344))) (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))))) (concat (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))))))
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
theorem bgb_7_864 : Interval gbAtlas 7 864 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 882 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 43 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0eee0eae0eae0e8a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4007717600 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37443.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[0,6]⟩,⟨.or,[4,5]⟩,⟨.and,[3,7]⟩,⟨.or,[3,8]⟩,⟨.or,[2,9]⟩,⟨.and,[1,10]⟩,⟨.or,[2,8]⟩,⟨.and,[0,13]⟩,⟨.or,[12,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717600 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717600 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37443

open PEqualNP.Outside.L_meta_37443 in
theorem PEqualNP.Outside.L_meta_37443 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717600 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717600 * 2 ^ 32 + 3940608160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
