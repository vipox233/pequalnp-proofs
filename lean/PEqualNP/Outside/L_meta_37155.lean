import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37155.Model
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


end PEqualNP.Outside.L_meta_37155.Model

namespace PEqualNP.Outside.L_meta_37155
open PEqualNP.Outside.L_meta_37155.Model
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

def SBf (j : Nat) : Nat := [6, 5, 8, 6, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37155

namespace PEqualNP.Outside.L_meta_37155
open PEqualNP.Outside.L_meta_37155.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x19030000000000001408020000000458071a2a048038001e000018000005000bf43de43bd43dd439d43be42bc42de32dc32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x51c001812c4000101440598040c00147552438e292871f5150e38a0a1c754c428faa4651d540ca3aa7a0c7553318eaa2631d531023ea9184755030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x200098086983548ca0c625513186181544c60e62d5230
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (302+((h/5+packedAt s0K4 (272+(h % 5)*6) 6) % 40)*6) 6
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 22)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffff81ffff83fc1fffc1fff83ffe07e79f3f3
  | 2 => 0xe0ffffe0fffffffe07ffe0fffc1fffff9e3c7f
  | 3 => 0xff03ffff03ffc1fff83fff07ffe0ff81e7cf9c
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x421888c428905040594c09498129212c28d1b1
  | 2 => 0x882111024122208a0291209224124a50922446
  | 3 => 0x444a22481a440314a8265204ca409505454a98
  | 4 => 0x96b3c4929076b5e734c318c7739c0619f80f60
  | 5 => 0x18c3871ce38739f9c73b9ce063181861ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37155
namespace PEqualNP.Outside.L_meta_37155
open PEqualNP.Outside.L_meta_37155.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfc07ffc07ffc0783fffffc0ffe07ff007f9e7c
  | 2 => 0xffffffff81fffffc0fc07ffffff81fff98ff8f
  | 3 => 0xfff81ffffffffffff0007ff03fffffffe0e3ff
  | 4 => 0x1ffffe0007ffffff80003fffe001ff03f0
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2530c4471448a980b2ca9c854e43390c2b8e3c
  | 2 => 0xa85108890c9122940552251992c90a54983685
  | 3 => 0x10a255122122852950284aa4251654a960c15a
  | 4 => 0xa2c59a24483b36ce69b3030939e58831dd03e0
  | 5 => 0xc3061c3871c3c7738e3c73ce018610c1f6f800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaf0a0fa00f000faaaf0a0fa00f000faaaf0a0fa00f000faaaf0a0fa00f000faaaf0a0fa00f000faaaf0a0fa00f000faaaf0a0fa00f000faaaf0a0fa00f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37155
namespace PEqualNP.Outside.L_meta_37155
open PEqualNP.Outside.L_meta_37155.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c3dca5185b94a30bea9461ed528c2daa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef19263dc324c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x26400000000045c9c0000864ec838002ac790ed16532c44cc7000416000b48232480000007e2ae0000000012a000a791f4a0001031994d40006fa8400000057016000799299880dc11c131c21180003024000000071a8c3ce7280000000069c630be104030000000002c4000001b0465158004ca314288000000c0000003e2000df8f10aa4cc360fe3ba85800000000588e4a8e3de811339080004fc0000234a7dcbe2973069252f0c942a2813f9dc1864054302e000000770004820000021d3ea0000000450a24c3d00038c000d700047c0004801a3987b8001b1012000000c00000000026b1229480011118473cd4800000000000000000000000000000123800396358340000b46ac6714509616c909e101c92cbd06f432354790000000003184c3800e43b0a60fa0293a2703383d1000424686440001d00061ce70b6000000250531100c4d91fc3422d507a2c00052c0006747a7540003d0008ec000000002149406d4c439870a7a446000a481e00088475000000000000b3000001188000000014680000047400233238000000000000010a0450006c0c589c0068440000047293031000526000e89393300009b0000000000c8543b06993217d25e9bc720000006e8ea0f544059d1c1183360446b9e317a001010000009187c8000000000000037c76c0015e09a0007c0000e046c000212de500000a850e394000001740004c800234000cf83a0000008b1c40000000000100000200000806002018000000040040100000a0000000000000c0080c00400c0000000000c0000200000c05008002000008000100080681d00e01c030080020000000101801000000000008000050000080000000400401001004008010010000000300000e03c0100000600c008070160140000000203c01007002028000000000000200100e0600200600c0280000501001004000000020030070000140000100600400007004004018030060000200100e0240180200003c060000000280100100002c0180000c0080000300800400016000000008000000000500500601c01802000008008040000000000000800000019016000038000020100500100600c0080000000400000002000070030240040000400000001800000004020000040000380100000403000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x137077000000000001009dc1900022a424d21440921ec7985c4aa000a603c000294550000007e42ea18000000001304600000018a2d02b0e6800000340270dc4b66d0449e525c0000002c284000000000000000a000200000000002e0001060000002193612c44c00000000000000000bf0000000000025600000203000561040004366f4fe8ff2ea000ff24e308000000003a4000b3179020000000000000004925a082000001c80b0070b68cf1823dcf4a7c13e0001482f5205901d8e723ca4512a6830c5d87b13c16057cb60000000012e000000110451c546e000058af1901904b8d900000000000000a3c000594fa000000000004945b8e800000000197000838000201d20009aa6342e234409023a69340006a000000000fd04e66944a800440b4900612f0118a42710000000005f000000000152442d02b800000000f400031a48d2c17b178758569322fe6780000029a1fcb08b900005c000000e6000000754c2004001ad44400100800516000e8000000000000000000000000000000000078000001301711526490812d3000a8d413d0000000003400012094800000000000003b240d2ba420005f80000036a93c6ea6600000000000116000ad8f0448000000002e43792402800051c000000006f0950003d88a0b019d136564ad00012c1940025f4f0964d01ed0f821000000000000001511de000ef800000000028000002e04f1ff0009150509a0007782b1930006ec470000000dd068000009744c281000000000000000000010f4e4814002440000aca816e000060f000f0000910394a1b487921a792e61001f9461882ec0022e0a049833141214388068ab26829c5087145a7a87021c1460001a94e44e438000db2d470d190004783ec638005280011f8002b807d440004547d8040000000000381200000134904144a093f0b219a849369524260013a9554a26b0fa0002ba01876a3520c0004780000049cf90000003e8690002626dcd18000001a4aa000000000e0800026000000940000000014350600125000000000b58004ac00000000148000ca83e4344dc9d0000000000010b4f69cc000001d8000000520006d80000035e00000000000000dc0001060006585e20a6e40010d2c64f80001b31e0001b1aa04a0cd1d0742287aca99820007cc6a00000075c0000036634cca276000430358380f2000001e210e87cfc000000000c4910224689451740003f04e8000e40014918c3f68d8fd177198345148ca3e013cc2a5438e000000001d68bc0000052c0014a800000000c080041
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x53c82cc6350b20ab59032c823e64947208f59251c825e63947209758e51c82ad64c87209798f548825d63d52208f993538823d64d4e208f992538823d6494e208fd91518823c64546208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534834d62d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cb152424826c6550920b318d424826e65cc920cb15332482ad640c920cb150324834f530c920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d990851483654214520d9cc8514836432145209b99721482ad64c8520d914721483645148520d9146204823d65950208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530826d6588420cb552210832d5408420cb553200826f6548020cb55120082e461480209ed95200826e62953109b58a54c425e63153109758c54c423f6454f108f19153c426f6254f109b18953c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e63952109758e548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6494e108f592538423f6454a108f191528425f6354a109718d528423e6414a108f590528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d594210435953cc0109e594300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xc63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c71d6315131c7152434c65c6550d31b3189434c72f54d4931cb153524c72f5414931cb150524c71c548c931a7590324c71c540c931d3d48324c73b54d4131ce153504c76b52d4131da14b504c73b5414131ce150504c76b5214131da148504c75a4314131d650c504c75a3214131d60c8504c75a31141318f596540c63e64150319798c540c71d54cc43197d95310c71d544c431b6181310c677654c4318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798f548865d63d5221cb58a548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538874f6254e218f990538863d6414e21cb95242886cc6350a21cb95332886ad640ca21cb950328874d530ca21ab593218866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b318d420866d650c821ab59032086e5610c8218f992510863d64944219798e510865d6394421ab593210866f65484219dd95210863f64540218f191500865f63540219718d500866f6254f409b18953d034f6254f40d318953d031d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d02ad62d0740c754d41d02ac6250e409bd89519026c6254640a758c419029d63d02408f994435023e65d0940a718d425025e63145409758c515023e65d0540ab58b415023f6550c40ab189431025f63548409718d521034f6354840d318d521032f4354840cb50d521023d6590840cb54a421032d52108408f596411032d5290440a758c411032d5210440a758f401032d52d00408fd95401032d52500409ed95401031d54cc730c755131cc2d8604c7309b98b548c26d62d5230c758e548c26e62152309b588548c31e5490e30b3189438c32e5494a30cb552528c32e5454a30cb551528c31e548ca30a7590328c31e540ca30d3548328c29d640c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d64149308f990514c23d641453097997314c2d8604c5309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2cc6250c308fd91520c23c6454830a7590320c2d9600c8308fd91510c23c64544309bd89510c26c625443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x94266d01000000021817974000000de0002aa1c8e01af3127986785f0d8668659000ae5f00017e2c2000002040007ac7b000000828000170005d40018434a43000000000000858001d6488850000000f80014d0000000002d0000000100033c00000000422000b10c92326e1081794300ac001d3000284f79210006cc378001ee148bb8000000e4388111402b0f80b32022c10b9ec066000001030027089b83b0003342120d2d4064788950ca4904500000055000000000000b280000024ce21260646e83b18b382540c71cb2880010a1232e01e0c40b53b6868d410239a75ca8971106000870920884cc61160008360cf8972e628c2d9573f80c4d60f03d00840000004e818f200000018c4d0000001900019029e720000ce1d46880001600002006014050000000800010010100000c03004000080400000004080a4010000200000008080180800400004020000601007000000040000003004030040101000018020000103c01014090380000809020020340401001000010003300c1101812034000000000c0100003004040140101c00014000002c01005010070780a0000400003054020040501c12000010040602002000000040200003000010000000002008000140005000004110300206c02000060000000403000000040900004000010440b0042200c0003c0b01c00028010080a00c0300c0400802000020326f62546439b1895190e6e62942439b58a5090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518ca3f64542328f191508ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540cb1d54d0c3297594430cb2d54d0832e3d0f420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320caac6250f4197d8d52d065c6354b41d3d8d52d074c6354b41cbd0d52d072d4354b41cb54a42d072d5210b41a718d42906ad62d064197d8d509065c63542418f99743506ac6250d418f994425066e62141419b588505066f6254c419b189531074f6254c41d3189531063d6590c41c754e431071d5310c41c754f421063f6550841a718d421071d5350841c754f41106ad62d04418fd95411071d53504419dd95411066e62153319b58854cc6cc6250f318fd9152cc63c6454b31a759032cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508
  | 3 => 0x5303a0003ce380408c81f28485e800080444690d11203b45e00000045c0013400014c0003c0603188a0250000005d8001680003d9f20000007c108000000ef1e30da2e0e813f0006e40003723c7b8000000000010700c36e00000000020528a4a0907a758ac00017c00000000000238000000000007a09b3b24d80000032c81c6380036a1e40000018a6344a00038e000cc17f07085400000000780d889e27a0d5079ae0523bc0504823877c000e514c000000a5046000ad8000007c4000002503f4000001483f898939174000d219d1be3a04e969000000000002a412c079ab0001e8f98e30c4864bd15c0124f8001a1000000000003547a4e3000086000000000007f4000001ae7680000030a000c1050000000000002c82a82280003c000000000b0000990842520002f00034e000001480ba330b61054024b07d92a07e054268d01326fc0192d418234000000003e80015f28039d028733fc5f4708f23240009c00027607cdb1be0000d812195000800059533da224ca1181860b803000138000000e6030374d903a0fa3cc878ff2d6118cc9672826b45f96842c3046c9420e0754e48ec1aa6185381c00070ce5077130000130c41804805b8d4256000b917800082c331d400000000000000000001471941500015d08e000000872dc6c0c61ce0ac600000003e80000018f0000000013c000000898003987443f0003b80006d8220000003e0b630e2886f0a800018400197000748278da1641308b12f22a5b4000fc0005680a0552f60143380e2cc808720a903a7d50186030250c928910542bc890ee29c6706b00010a170cd8800000008806a000048849273f2468c89bd28a5d87110d0d02b8000001b87fc0016f0fe1d4461dd2bc1689d01b08246c589a02c647400135000518d4800000794000ad0500000000000027c001a30000000000000000037106000000c182c314000fb00012c000000ab000788a58f539e0200d0003f48200000002600024800000000349302ac0001a15900000035800000760fb80011e6ec0380009c128411070a2000458001d2000069ea326220001f834c34c0011f38a7ec820001724b8f085
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x4c724c40e5d80000004800002cd5081913c40000c00020001402800000005400560000000208800a0838318c6255032a18e6a9085a0d0c7254c4310706a9ac5a0883431c9631513183aec2a06498d487250c504c68cba0642826386550604c431a18e6b14a910c2d769503288686392a621e818354d62d0740a18e6a90842060d635484110306b1aa5a008186550604c730a18e4b1ca91841d76950328c28639ac42a2410b5d8540c920a88e6a10a290525740c85148312b20a390a41895506148020
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xc2008080c8754d62d044180c8754d62d074080c8758d521044080c8758d52d0040
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20359+((h/221+packedAt s2K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s2K4 (22272+((h/179+packedAt s2K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s2K3 (1273+((h/8+packedAt s2K3 (1225+(h % 8)*6) 6) % 48)*6) 6
  | 2 => packedAt s2K2 (243+((h/1+packedAt s2K2 (240+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xfffffff81ffffffe07c0ffffffc1ffff23fe3f
  | 3 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 4 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 5 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x290a22310489208059492909281232a84e10d5
  | 1 => 0x42144440c9124116029052325241455120e62a
  | 3 => 0x8526a89243a426aaa8289d489cb4181ac34b4c
  | 4 => 0x1658d12492074b4d34f20610e7298063b40db0
  | 5 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaacc88ee888888eeaacc88ee888888eeaacc88ee888888eeaacc88ee888888eeaacc88ee888888eeaacc88ee888888eeaacc88ee888888eeaacc88ee888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37155
namespace PEqualNP.Outside.L_meta_37155
open PEqualNP.Outside.L_meta_37155.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa1660240a288033808001bdf43dc43df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x68108e2a26538505069aa598d354830
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
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s3K3 (111+((h/1+packedAt s3K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fffe07ffc0ff07ffffc1fff03fe07e7e7e73
  | 1 => 0xfc1ffffffffffff81f03fe0fffffffff918fff
  | 2 => 0xffe07ff81fff07ffe003fff0ffc1ff81e1f39c
  | 4 => 0x7fffe00007fffffc0000fffe0001fe03e0
  | 5 => 0xffff8000000007ffffffffff00000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x48430231448521016514c0513213212c263631
  | 1 => 0x11042442091082280a41120a44644a509088c6
  | 2 => 0x28894890d2242d52a09265609a919505615318
  | 4 => 0xb2d6712483b6b79cd3d83148ef390619fa03e0
  | 5 => 0xc31861c71c38c6e71ce3b98c0c201861ddec00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8eaeae8e8c8c8c8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37155
namespace PEqualNP.Outside.L_meta_37155
open PEqualNP.Outside.L_meta_37155.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230fd20461f9408c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f480987e50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53482fea2905f14520f790a41ed21483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fda0621f840c43f461887e4c310fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f680087e10010fd18021f930043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1217e94242bd284857d5090bf2a1215e54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0fed4141bda82837c50507f0a0a0de14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198fe94331bd286637d50cc7f2a198de54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f710d31bfa92637c524c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621fb18c43f531887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487ec6290fd4c521fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e51087de4210fd88421f690843f521086fca010fe94021bd28
  | 2 => 0x9000000b720b13444c000004c64347e83036c58cf11af4648b05d0001d254d001ef36a6c5468102428f53d1170546e0508f13004dc9a1c30001d0550400d46a00011e11a3e0e30b44f632ca602e4e613424a930c4760d61080003093a89833825c7a8ee1825f00f0180cc000eb8d64784bc318f03786b9082550009080000043c4c48393e000080fc8ad1088d00a9b200037c5d95f00e158002012bc690851d10005fcad2152867c4730a70dc000000e44c2448751323820010988a3283b09c1ff3dc5cce82680009e12624b0e20004709200012c531843ee214981bb23e9dce900036e26d438004d894d4b01c4fa0000022d1ba00008800000444ab800000000ba8330001a028a3a0009bc0004a12aa1000046450614999b03c64e49023e1321689100000085002800394000b428a4ec9d13504709c350e40191b6640361ad0c82a477893100529418de19a870020160423400588b05e9388e12a48a93ca425404620c37a582ba6f4fd8b251876919a8500038c00172000000000001aa17c040342ac968e5a4712c5349f99d3ba994ca80024c3147b8001f40f09d21d4da00128000000a2c2a966082394d990605a52c6b9ab198000cf2442a4184958af20a0000017a45c000000000ae0001a831000000002903da9980013530e79d119930001dc242403d090d4889028c5e44e0fc01403d1b8fb15c000000000001b5370ca000000408004541e909029228000e000043e0000000017e588a80001d01702225f018160800001700011800000407048000041800c010000000c00004000200f000000000100c0300003000190000200c01018020080500c0a0000002c00024050000f01001008000180401806038010240500412018010080700c24004040000501c2c02802000090040f000080000200c0000004008060040201800004000080000c0b0102a06805000050240803c000002500004008020080100801004020180001400008270b804028030082300400000010a80000000000010080b03c0101c05018000000c000090240d0080304808008060100105c0a0000000001058000000a050000000000000024010040300802020030040000800000040080502015014010100100c0400019008000240402800000080000f0181c0000400400bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021fe94043bd280877d5010ff2a021de54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x24631800000000494eb1cc0000000001f280000bd98e0f02740011947e000cd2724d23c917a591629443803e4e00003924927859c6481b40881c438383be000d018925000000000000644ea000000000000004300f48a80014a9f1088000001f85a9a638ea09031a33a67840000021e40932000456a54a8a7f0f6904012030264743e9d544e3ccfc13d34e5041920c0bc5d00008c0001a47598c352280820002eca185f0004ac291448a34420008d043000194be8002e03b4001b946c208001ce31a000d51f6000000b50c30c060d040004529893c825000000001e437e68401873252000b88001ce8343e06b28419d408000006f9338000006600000039a000aa9ec13e088000004402200d0892c2034cb8d13b6a49291e600095d02a02000570c1091000001389e0000a38faa242f005c000004bc3d06c0394140000012732483c0005217a710cd8002480008da5b1c4824f483a0002501b0000ba7c1479884ba42c8810e0005b0fe8123b80000016f29c000000000000009b00000000000045180000000000007ac0a0002da51ccb1030007085c8004364240000007e62c582173145647c800000000000d942c2f0000000b66880000048c5110712c11e404b015b4707142c9ba0fe000000002c8000000000006d0000ff1907e8298fe276038fa0e14760b06792e2180ec13086000000000002d20003c800000a00001181c0000698a816c7f0f50540004591887500092000165002000ff0000007640e8000001300007628a888bb9cf4b88d4ac27e1ec1411302b25a000bf04f1880000000013ca20a78421a40dc670dc4948640002849a000c7a253e4288aa0ac3e67940000630c67cb58c70009ac598003920914ba390002dc6d2943bc2ad301813320250d027000000d294
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2434c25c6550d30c7152324c29d640c930c7150324c2d5610c930b6980324c29d64cc530c7153314c2da60cc530c7151314c354514c530ce152404c39a43901309e195404c39943501308f596540c23e64150309798c540c27a6015030c7553300c339548c03097d95300c31d544c0309ed95300c339544c0308f99353c823d64d4f208f99053c823d6414f209d98453c82756114f20ba18121c825e63d52209758f548833860552209798c548825d63152208f993538823d64d4e20c7952538831d5494e20d6982538831e5454e20c7551538823e6414e208f590538833954d0220b658c4088339548c220ae1913088339544c220d694d30882ba64c822097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d208f990534823d6414d208f990514823d64145209798c514825d63145209e99740482d963101209e19530482b8644c120ba18930482ba64c81209e983540825e63150209758c540827661150209d584540823f6454c208f191530823e6414c208f59053082766114c209d584530827a6014c208f992520823d64948208fd91510823c64544208f992500823d64940209798e500825d63940209bd95200827b65480209798f54c425d63d53108f99353c423d64d4f108f99253c423d6494f108fd9152c423c6454b1097d8d52c425c6354b108f99052c423d6414b109798c52c425d6314b10b658c40c42b8644c310ae99320c425e63152109758c548423f6454e108f191538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6494a108f592528423e64951109ed81544423e65151108f992534423d6494d109e582534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524427b60549109e996204433854881109e19520443385448110ce153104425e63d50109758f540426e62d50109b58b540423d6595010ce181540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530435a6094c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810da181520423e64148108f590520425e63148109758c520426e62148109e980520433954d0010da54b40042796510010b658c400436952100109e5963004339548c010da54a30042b8644c010ce551300435a534c010da549300427965c8010ae993200436952c80109e594200436952080109e596100436952840109dd95100427b6544010ae19110043695244010
  | 1 => 0x65d6314141d698c50507596314141ce90c50507384314141ced0850507394214141ce904505063f6550c4197d8d521065c63548418f59642106ba60908418fd9541106b860504419dd95411067a60d53319e58354cc71c63553319e98054cc6796015331c755343cc6d96010f31a719132cc73a5494331ce55250cc73a5454331ce55150cc71e548ca31c7950328c6d5610ca31c7953318c66f62551319b189544c67b60551319e181544c65e65d0d31b6580434c63e64149318f590524c67a60149319e580524c65e65cc931a7191324c69e648c5318f990504c63d64141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c65d658c831b5584320c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c67a60d53219e58354c865f63553219718d54c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c863e64943218f59250c865e63943219758e50c865e63d52219758f548867b60552219e181548863e64d4e218f593538863e6494e218f592538867a6094e219e582538863f64542218f191508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c715053487556114d21d514e3148674654c521ced53504873854d4121d6d4f504875853d4121ced5050487385414121d6d4c504875853141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219d984530867a6014c219e580530875553884219bd9521086776548421d554d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b2154021da485500865f6354b409718d52d02ba6090b409798e51d025d6394740ae18141d02b96010e40a718d429029e63906408f99743502ba60909408f994425023e65d0540ae181415023d6590c40c754e431031d5310c40ae580431031d53d08408fd95421029c6350840c754d421023d6590440a798e411031d5390440c754c411031d53d0040d654e401023f6550040c754d401027b6550040d654d401027661d53309d58754cc23f6454b308f19152cc29d640cb30b558432cc23e64947308f59251cc29d64cc7309b98b548c26d62d52308f992528c23d6494a308fd91518c23c64546308f992544c23e6515130c758c544c3396015130c715
  | 2 => 0x71cd69f41ca038e78803c23dcda9900460ec4221120446cf81783fe83906a0b2905dc571d233c1802519137e4bd018003402a46c9d90be7f4fd0e33f804085839332424c692e0e2000ad00016e09c618f01b43ecc502f23c10004000028624b40301500e000000372374a39f3014434508002886f00017e3aa61050083000388449b41f44fca9a131c83482617522c2f40e90330e558f107f27426cc60c20d885c069e815a2382d8fe08c53ca59c22087dc3e9943100006000009a8403d0000b8158ac80000031c8f98509e740be00006c34c7c13707e63c0012c000000a602c0001609c8000d6000d800040a780740002de000750000000001d1220000550102500c528ad8b617c000001170004a8000d01e6000ff1ed3d68302ca0a01200c02008090000800003008030201406400018190640303005000000000103000004010500805c03018060a40c0a00e020040040400c00020010080b0680200802014000041301400000050002b0281e000000000d0000001c00100030043100c010000100c02020000000500c0a004000001c024000302b00000070040b0000081e0a000008000301401001008100000600000000010540000c250005f054060000800002000020300004800000010040300007000030200b01c030400000406034030040c06009000000181b0700005000078080041c03c0100001008010fe7a6094b439e58252d0e7b60547439e18151d0e3f6550c4397d954310f3b4354043d690d5010f394354043d650d5010e5e63947429758e51d0ab96010e429798e5090a5d6394242d698e5090b596394242ce90e5090b384394242ced0a5090a7a6014d429e5805350b5a6014d42d65805350a3e65d0d42c714f4350b1c5350d42c714e4250aba60909428f5964310ab96010c428fd954210a9c63508429bd954210a7b60544429e1815110a7a60153329e58054cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548cad96010e328fd91518ca3c64546329ed81518ca7860546328f992508ca3d64942328f992544ca5f63551328f994544cb1c548c9329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cad96010c3297d95320ca9c644c8329bd95320cb365494432cd552510cb365454432cd551510cb574354432d510d510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cab96010f419e98252d06796094b41a718d42d067a6094e419e582539075a6094e41d6582539071e53d0e41c794d439071e5390a41ae982429071e5310a41c794f419063e6510d41ae580435063e65d0941a718d425069e63905419798c505
  | 3 => 0x10a9790007c8ca9002e61d8c5800008000b900742457c349d4348800f49da36e070259a628c000008222c8000ba07b0a610c091f12a0578918c61b02300100003e0000019a00044ce594e0000000c0001e2000000b2054000839c135c000000000000001a1b1366000208f419e000d41363ac358561c50001240019211458cef1011fa1a06299d146000df000126468ec08f2604c43516b0bc1b8d38b80fc29c4e09f2663e47f90f0007242a20f3ca5545897609c268dd87027c3d80d93b2a8000121a3232548d61970005e8a18852c076ccb11802e36c891dc2844ac169513984d46203214c000b62161821f04a13c1cc454c714115e0f40b13814a570cd8552c418cbf97d4122d0c006d3f06e85d9082484743c0e01725b800086000220b49a54102e8f78001aa3ac06198000734e30b3240258239d33ce2604a8c80ba7ec4882b1be1490c8bf006084000ef24a0007e0a43cc700760000000ccac00030400103800000414931ea1a85240000021c7109917101e068141df2ca25c738d10000007a8653567283387424e790410923ae00000087000000ab8c93c68503102603c685008b52143b4229aa1e4810a00e91604b400166364000c08cb242278fa9450004a4321ee3a21d4d7800194110b5170218450fb000000574e400b026204b39b80520f0558000c20f8770311bc7b0de85a2501cc4e8e11446a4668904306d88e1862f62642813405c6883300020c0010d000040000000000002f00013d3f2338b68aa33e1dc6b99c0001bc0004802270ca68cc2227742b8050840d42888d40c000000720007386e1930004401b87930622c000002c20640000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x5545d01881c200044014000e30d2431160003cb48a4d80403d0440303465c05350d42c30a730484a15197018d540caa8b8086a8865451d13254432a32e129a8720e1a53982429068c39a8428283469ce4114141a32e031aa998e1654584328c64cb9cc121281265cc6050540c32c6b00a89841d76150324c30a2a2c219261075d854cc530a32e6302a91043876551308828cb98c0aa0219258d5210010870ecaa26008628645493004315322a5900218a1915244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1a00108198714e60909428198794e6090a41819861cd4214141819869ce4114141
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
  | 5 => packedAt s4K5 (20138+((h/221+packedAt s4K5 (17928+(h % 221)*10) 10) % 876)*11) 11
  | 4 => packedAt s4K4 (22272+((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s4K3 (1265+((h/8+packedAt s4K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x83fff81f0ffe3e1f0f878ffe3c0fe0fe41f673
  | 1 => 0xfc3fffe00fffffe00ffff0ffc00ffffc7e387f
  | 2 => 0xffc0fffff07fc3fff007ff0ffff0ff0387cf9c
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa88688c49314620782c189962469225a40d631
  | 1 => 0x1108110224280060050a102840824ca01a2846
  | 2 => 0x8122248014004891004a20289209208854298
  | 3 => 0x52acc492880cab32a9d0088d32cc0433680d60
  | 5 => 0x6330871cce7133dcce674cc0230818c3f7b000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfce8fce8f8c8f8c8fce8fce8f8c8f8c8fce8fce8f8c8f8c8fce8fce8f8c8f8c8fce8fce8f8c8f8c8fce8fce8f8c8f8c8fce8fce8f8c8f8c8fce8fce8f8c8f8c8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37155
namespace PEqualNP.Outside.L_meta_37155
open PEqualNP.Outside.L_meta_37155.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1c2e29508006d41f460168000b13000000029482cc0700000272c89280243430302440000050e84005470c3c8448f0014002344102b000000026641038108040030c0c1011604302ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fa20fd20f920fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x4800000000000000000188000000016830e4003401103c00092104013934009c014ce00461482854b0a8d0d800b924c0016d1c98509070dc2c80b5450078201874004d54895c013c000038f1312c00fc5c0000c8c400000170008c00016010a51564ed58a000f8840001800000017c1d4000006d784400000000d47d840c00f4000129510cbc00589400002518406468ace9081574000000cc0e00022a0600020002000400023a002e0002040800020a000000000206200206013e5390e7aa521cf94c43cf298873d5210e7ca7a14f55242bd28485795090abea6a15714d42cfa9a853c5350b38a6a14714d42d7a92853e5410af4a0215e540429faa6653c54cca7ca9194f55232ce21c657a508caf2a1194fd51329e2a2653e540ca7aa8196710c32bb2886575510caf4a0195e54032af29c835d53906f6a0a0de14141ce21e633e548c67aa918cfd51319e2a2639c434c6dea498db14931bda826378504c67ca990cf55321bd286437950c867ca810cf55021af298435d53086f4a010de54021b7290816d521027ca9184f55230b7294616d528c27ea8984f151309f2a6413d54c835a85906e90e20dc21c4179528837685106e50a20d6a1241ba434837086907ad4920dda1241ea424837284907a50920d4a1241eb32483d064907ac8520f490a413e540827aa8105e940209faa2213c544427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1400131100000004822c63003ca1c305150e24834018c082961d6510c32c510d510ca696214141c310c524c61c6355321a318d42c82986350a20a318d42482a96210d20aa59242482986350920b218d424838b6350920aa18d42483886350920a218d42482ab64cc920aa5903248388430c920b858432482a964c8520
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x110004897610c324834021ac219241221cd64c8520
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s5K5 (841+((h/15+packedAt s5K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s5K4 (2937+((h/33+packedAt s5K4 (2673+(h % 33)*8) 8) % 157)*8) 8
  | 3 => packedAt s5K3 (833+((h/7+packedAt s5K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf07ff03e1ffc3e1f0f8ff0fe3c0fe0fe0f3673
  | 1 => 0xffffffc01fffffe00ff0ffffc00ffffc71f87f
  | 2 => 0xff81ffffe0ffc3fff000ff0ffff1ff0381cf9c
  | 3 => 0x1ffffff0003ffffff000ffffe0003fe0fe0
  | 4 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x150d1189262a6207828938962463225a071631
  | 1 => 0x22102204485000600510412840844ca0306846
  | 2 => 0x412544910282268990089a82a921920a818298
  | 3 => 0xa5889241018893229a2000d12c804315a0d60
  | 4 => 0x8c610e399ce333dcce4cecc0230118c3edf000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8fec8f8c8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37155
namespace PEqualNP.Outside.L_meta_37155
open PEqualNP.Outside.L_meta_37155.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12800f028d223179d00e000000d4d1e000100956858801e045395ca53003e183b06e21a36366552458885bb0601d322a0022d28949006640b004660e172639e804e18081010638000120c4800e087012640180017fd5005fe54017f55005fc5401ffd4c01fe53007f54c07fc53017fd0c05fe43017f50c05fc4300ffd4803fe5200ff54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803fe3200ff4c803fc3201ffd4401fe51007f54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc2101ffd4001fe50007f54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842004fdc4210007f62108003ff65440017fb2a2000dfd9510004feca88037fe65440077f32a2000ff59510005faca88037fc65440077e32a2000df1951001cf8ca88033ff64440197fb222000efd91100057ec888033fe64440057f322200cff59110065fac888033fc64440057e322200cef1911001578c888033ff5444019ff2a2200cff55110067f8a888003ff63440017fb1a2000ff98d10055fcc688003fd63440017eb1a2000ff18d10055f8c688037ff5344001ff29a2000ff54d1006ff8a688033ff4344019ff21a200cff50d10067f8868802fff62440177fb12200bff9891000dfcc48802ffd62440177eb12200bff1891000df8c48802fff5244017ff292200bff5491005ff8a48802fff4244017dfa12200bff9091005ffa848802fbd4244017fe212200bffcc91005ffc648802ffd3244017fe192200dffd4510007fca288003fd514401bfe28a200cffd0510067fc8288033fd4144019fe20a2000ffcc510007fc6288003fd3144001fe18a200bffc851005ffc428802ffd2144017fe10a200dffd4110027fca088003fd5044009fe282200cffd0110027fc8088033fd4044009fe2022000ffcc110027fc6088003fd3044009fe182200bffc8110027fc408802ffa2044017fe902200bfe48110027f84088003ff1044001fd8822004ff84110027ec2088013ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff59410005faca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010015fcc808013be64040055f3202004ff5901003dfac808013bd64040015eb202004ff19010025f8c80801fff540400fff2a02007ff5501003ff8a808013ff63040097fb182004ff98c10055fcc608013de63040016f3182004ff58c10005fac608013dd63040016eb182004ff18c10025f8c608023ff5304001ff2982000ff54c10047f8a60801fff430400fff2182007ff50c1003ff88608013ff62040097fb102004ff9881000dfcc408013ee6204003773102004ff58810035fac408013ed620400176b102004ff18810025f8c40801bff520400dff2902006ff54810037f8a40801bff420400ddfa102006ff90810037fa840801bbd420400dfe2102006ffcc810037fc640801bfd320400dfe1902009bf98410047fea208017fe5104001fea882005ff1441003ffe8208017fe410400ffea082005ff10410007fe6208017fe3104001fe9882005ff0c410037fe4208017fe210400dfe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x3fc610c02bffa886000ff94430007faa218057fc510c029ffa086014ff904300a7fa8218053fc410c015ff988600aff8c430057fa621802bfc310c027ff9086013ff8843009ffa421804ffc210c0097f3006004ffd4030027fca018013fd500c009fe2806004ffd0030027fc8018013fd400c009fe2006004ffcc030027be6018013fe300c009fd1806004ff4c030027ba601802bf9300c009ff9006004ff88030027fa4018013fc200c00bffb2e2000bfd9710097fccb8800efe65c4001feb2e2000bf5971002ff8cb8800efc65c400bffb262011bfd931008ffcc98800afe64c4023feb262011bf5931002ff8c98800afc64c4023ffaa62011ff9531008ffaa988047fc54c400bffb1e2000bfd8f10007fcc78802afe63c4001feb1e2000bf58f1002ff8c78802afc63c4025ffa9e2000ff94f10007faa78804bfc53c4023ffa1e2011ff90f1008ffa8788047fc43c400bffb162009bfd8b1004ffcc588006fe62c4013feb162009bf58b1002ff8c588006fc62c4013ffa962009ff94b1004ffaa588027fc52c4013ffa162009efd0b1004ffc8588027fd42c4013dea162009ff10b1004ffe6588027fe32c4013fe9962009ff0cb10097fea388017fe51c4001fea8e2005ff1471008ffe8388017fe41c4023fea0e2005ff10710007fe6388017fe31c4001fe98e2005ff0c71004ffe4388017fe21c4013fe90e2005ff08710097fea188013fe50c4001fea862004ff1431008ffe8188013fe40c4023fea062004ff10310007fe6188013fe30c4001fe9862004ff0c31004ffe4188013fe20c4013fe9062004ff08310027fecb08012ff6584009ff32c2003bf99610027facb08002fd6584009fe32c2004bf19610027fec908012ff6484009ff3242002bf99210027fac90803efd6484009fe3242004bf1921007ffea90803ffe548401ffeaa4200fff15210027fec708012ff6384009ff31c200abf98e10027fac708002fd6384009fe31c2004bf18e10087fea708003fe5384001fea9c2010ff14e1007ffe870803ffe438401ffea1c200fff10e10027fec508012ff6284009ff3142001bf98a10027fac50803afd6284009fe3142004bf18a10077fea50803bfe528401dfea94200eff14a10077fe850803bbf428401dff214200eff50a100777a850803bfc428401dff994200eff8ca10077fa650803bfc32840177eb0c2010ffd4610007fca308003fd5184021fe28c200fffd061007ffc830803ffd418401ffe20c2000ffcc610007fc6308003fd3184001fe18c200effc8610077fc430803bfd218401dfe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fd1042004ff48210077f24108013fc2084009ff8
  | 2 => 0x3000dfcc518013fd628c0337eb146004ff18a30025f8c518067ff528c033ff2946019ff54a300cff8a518067ff428c033dfa146019ff90a300cffa8518067bd428c033fe214600affcca300cffc6518067fd328c015fe1946004ffd8630027fcc318002fe618c009feb0c6000bf58630027f8c31806fff518c001ff28c6000ff546300dff8a31806bff418c035ff20c601aff506300d7f8831802bff318c001ff18c6000ff4c630057f86318067ff218c033ff10c6019ff486300cff84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009ff9846004f7cc230057f66118013ff208c009ff1046004fe88230027fa4118067f9208c009fe1046000ffd9530005feca980037f654c0013fb2a6018ff9953001dfcca98003fd654c0017eb2a6018ff1953001df8ca980037c654c0073e32a6017ffd91300bdfec898003bf644c0015fb226017ff99130015fcc89805ffd644c02f7eb226017ff19130015f8c89805fbc644c0055e3226017ffd51300bffca89805ffd544c02ffe2a26018ffd4d30057fca698003de534c001fea9a6000f754d30057f8a69805fff434c015ff21a6017ff50d30057f8869805bff624c02d7fb126016ff9893000dfcc49805bfd624c02d7eb126016ff1893000df8c49805bff524c02dff2926016ff549300b7f8a49805bff424c02ddfa126016ff909300b7fa849805bbd424c02dfe212600affcc9300b7fc649805bfd324c015fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530005f8c298063ff514c001ff28a6000ff545300c7f8a29805fff414c02fff20a6017ff505300bff8829802bff314c001ef98a6000ff8c530007fa6298003dd314c015fe18a6016ffc85300b7fc429805bfd214c02dfe10a6018ffd4130027fca098003fd504c009fe2826017ffd0130027fc809805ffd404c009fe202600affcc130057f66098013fe304c009ef1826016ffc8130027fc409805bfa204c02dfe9026016fe48130027f84098013ff650c0097fb286004ff9943001dfcca180137e650c0073f3286004ff59430005faca180137d650c0013eb286004ff19430025f8ca18013ff640c0097fb206004ff99030015fcc818013fd640c0297eb206004ff19030025f8c818053ff540c029ff2a06014ff550300a7f8a81802afe630c015ffa98600aff94c30057faa61802bfc530c015ffa18600aff90c30057fa861802bfc430c009ffb106004bfd8830027fcc418006fe620c009feb106013bf58830027f8c418012fc620c027ffa906013ff9483009ffaa41804ffc520c027ffa106013efd083009ffc841804ffd420c027dea106013ff10830057fe641802bfe320c015fe990600aff0c830027fec218013fe610c0017f3086004ff58430005fac21801
  | 3 => 0xda84a004ff14250027f0a128013ff4094009ff204a004ff50250027f88128013ff2094009ff104a004ff48250027f84128012ff6554041ffb22a020bfd9150107fcc8a800afe6454041feb22a020bf59150107f8c8a800afc6454007ffaa2a003ff9515001ffaa8a800ffc5454001ffb1aa000bfd8d50007fcc6a8003fd6354001fe31aa00abf18d5001ffea6a800f7f5354007ff29aa003ff54d50006faa6a800ffc5354041ffa1aa020ff90d50107fa86a8083fc435403fffb12a01fbfd89500fffcc4a8006fe625403ffeb12a01fbf589500fff8c4a8006fc6254007ffa92a003ff9495001ffaa4a800ffc525403fffa12a01fefd09500fffc84a807ffd425403fdea12a01fff109500fffe64a807ffe325403ffe992a01fff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8002fc6154007ffa8aa003dfd455001ffca2a800ffd5154001bea8aa003ff14550107fe82a8083fe4154041fea0aa020ff10550007fe62a8003fe3154001fe98aa000ff0c5500fffe42a807ffe215403ffe90aa01fff0855001dfec0a800fff5054007fda82a004ff94150026fca0a8013fc5054009be282a003fe14150107fe80a8013fe4054041fea02a004ff101500fffe40a8013fe205403ffe902a004ff08150057fecb9802aff65cc015ff32e6003bf99730057facb98002fd65cc015fe32e600abf19730057fec99802aff64cc015ff3266002bf99330057fac998076fd64cc015fe326600abf193300effea998077fe54cc03bfeaa6601dff15330057fea79802bfe53cc015ef29e600aff54f30007baa79802bfc53cc015ffa1e600aff90f30057fa879802bfc43cc015ffb16600abfd8b30057fcc598006fe62cc015feb16601cbf58b30057f8c598006fc62cc039ffa96601cff94b300e7faa598073fc52cc039ffa16601cefd0b300e7fc8598073fd42cc039dea16601cff10b30057fe659802bfe32cc015fe996600aff0cb30057fec39802bfe61cc0017f30e600aff58730005fac39802bfc61cc03dffa8e6000ff94730007faa39807bfc51cc03bffa0e601dff907300effa8398077fc41cc015ff98e600af7cc730057fc639802bfd31cc001ee98e600aff0c7300e7fe4398073fe21cc039fe90e601cff087300f7fea198013fe50cc001fea866004ff143300effe8198013fe40cc03bfea066004ff103300e7fe4198013fe20cc039fe9066004ff08330027fecb18012ff658c009ff32c6003bf99630027facb18002fd658c009fe32c6004bf19630027fec918012ff648c009ff3246002bf99230027fac91806afd648c009fe3246004bf192300d7fea91806bfe548c035feaa4601aff152300b5fac71806fff538c015ff29c6000ff54e30057f8a71806bff438c015ff21c601aff50e30057f88718013ff628c0097fb146004ff98a
  | 4 => 0x89ffc624c4037e3126227ffd493113ffca49889ffd524c44ffe2926227ffd093113f7e849889ffe424c44ffea126227ef5093113ff8849882bff324c44fef9926227ff8c93113ffa649889fdd324c415fe1926229ffd4531007fca298803fd514c453fe28a6228ffd0531147fc82988a3fd414c451fe20a620affcc531057ee6298803fe314c401ef18a6227ffc853113ffc429889ff6214c44ffe90a6227fd4853113ff84298803ff604c4017fb026200ff98131007fac098803fc604c4097e3026229ffd413114ff8a0988a3ff404c451ff2026228ff50131147f8809889fff204c44fff1026227ff4813113ff84098817ff650c4157fb28620aff9943101dfcca1882bfd650c4017eb286205ff19431055f8ca18817ff640c4157fb20620aff99031015fcc81882bfd640c4497eb206205ff19031055f8c818893ff540c449ff2a06224ff55031127f8a81882afe630c415ffa98620aff94c31057faa61882bfc530c415ffa18620aff90c31057fa861882bfc430c40bffb10620abfd8831057fcc418806fe620c415feb106223bf5883102ff8c418806fc620c447ffa906223ff9483111ffaa41888ffc520c447ffa106223efd083111ffc841888ffd420c447dea106223ff10831057fe641882bfe320c415fe990620aff0c831135fcc218897ff510c40bff2886200ff5443102ff8a218893ff410c40bff2086224ff5043102ff8821882bff310c415ef9886205ff8c431057ec621882bfd310c401ee988620afd4c43111ffe4218817fe210c447fe9086205ff0843102ffec01882bfe600c4097f300620aff58031005fac018817fc600c44bffa806225ff14031127fe8018893fe400c449fea006224ff1003111ffe401888ffe200c447fe9006223ff0803101dfacb28013ff64940097fb24a004ff99250015fcc928013fd64940457eb24a004ff19250025f8c92800fff5494007bfaa4a003ff9525001ffaa92808b7d5494007fe2a4a004ffd8e50027fcc72802afe6394009feb1ca000bf58e50027f8c72800fff5394007ff29ca000df94e5001ffaa72800ffc5394007be29ca022ffd0e50117fc872808bfd4394045fe21ca004ffd8a50025fec528013fe62940037f314a004ff58a5010dfac528013fc62940097e314a003ffd4a5001efea52800ffe5294007fea94a021df54a5001ff8a528087ff4294043dfa14a021ff90a5010ffa8528087bd4294043fe214a021ffcca5010ffc6528087fd3294043fe194a004ffd8650027fcc328002fe6194009feb0ca000bf58650027f8c32800fff5194007ff28ca000df9465001ffaa32800ffc5194007be28ca022ffd0650117fc832808bfd4194045fe20ca000ffcc650007fc6328003fd3194001fe18ca021ffc865010ffc4328087fd2194043fe10ca004bf98250027fea1280137f5094007f
  | 5 => 0x415101efea0a880ffc5054461ffa02a230ff90151187fa80a88c3fc405445fff902a22fff8815117ffa40a88bffc2054415ffb2e620abfd9731057fccb9880efe65cc415bf32e62039f99731057facb98802fd65cc415beb2e62009f59731057f8cb9882afc65cc415ffb26620abfd9331057fcc99880afe64cc415feb26622dbf59331057f8c99882afc64cc45bffaa6622dff9533116ffaa9988b7fc54cc415ffa9e620aff94f31057faa79882bfc53cc415ffa1e620aff90f31057fa879882bfc43cc415ffb16620abfd8b31057fcc598806fe62cc415feb16622cbf58b31057f8c598806fc62cc459ffa96622cff94b31167faa5988b3fc52cc459ffa16622cefd0b31167fc85988b3fd42cc459dea16622cff10b31057fe659882bdf32cc415ff196620aff4cb31167ba659882bfc32cc45dffa8e6200ff94731007faa3988bbfc51cc45bffa0e622dff9073116ffa83988b7fc41cc459ff90e622cff88731167fa43988b3fc21cc415ffb06620aff98331025fcc19882bfd60cc4017eb06620aff18331177fea1988bbfc50cc45bffa06622dff9033116ffa81988b7fc40cc459ff906622cff88331167fa41988b3fc20cc40bffb2c6200bfd963115ffccb1880efe658c401bf32c62039f99631007facb18802fd658c401beb2c62009f5963102ff8cb1880efc658c40bffb24622abfd9231157fcc91880afe648c455df3246202af99231157fac9188aafd648c401deb246200af5923102ff8c91880afc648c455ffaa4622aff95231157faa9188abfc548c44f7eb1c622bffd4e31057fca718803fd538c415fe29c622affd0e31057fc87188abfd438c415fe21c6205ffd8a31135fec51889bfe628c4037f3146226ff58a31135fac518817fc628c4037e3146226ffd4a31137fca51889bfd528c44dfe2946226ffd0a311377e851889bfe428c44dfea146226ef50a31137f8851882bff328c44dff1946226ff4ca31057f8651882afe618c457ffa8c6205ff94631007faa318817fc518c455ffa0c6205ff90631157fa8318817fc418c415ff98c6200f7cc631057ee631889bff218c40bff10c6226fd88631137fa431889bf5218c40bfe10c6205ffd8231007fcc118812fe608c401feb046200bf5823102ff8c1188afff508c457fe284622affd0231157fc81188abfd408c455fe2046226ffc8231137fc411889bfd208c44dfe1046200ffd9531005feca988a7fe654c4077f32a6200ff59531005faca988a7fc654c4077e32a6228ffd9131145fec8988a3fe644c4057f3226228ff59131145fac8988a3fc644c4057e3226228ffd5131147fca8988a3fd544c451fe2a26229ffd4d31057fca698803fd534c415fe29a6228ffd0d31057fc86988a3fd434c415fe21a6227ffd893113dfec49889ffe624c4037f3126227ff5893113dfac498
  | 6 => 0x9ffa1aa60aff90d531a7fa86a982bfc4354c67ffb12a633bfd895319ffcc4a9806fe6254c67feb12a633bf5895319ff8c4a9806fc6254c07ffa92a603dfd495301ffca4a980ffd5254c67bea92a603ff1495319ffe84a98cfbf4254c67ff212a633ff5095319f7a84a98cffc4254c15ff992a633ff8c95319ffa64a982bfc3254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa600bf1855301ffea2a980ffc5154c07be28aa634ffd05531a7fc82a98d3fd4154c69fe20aa633ffc855319ffc42a98cffd2154c67fe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff18153025f8c0a980fff5054c07bfa82a603ff141531a7fe80a98d3fe4054c69fea02a634ff1015319ffe40a98cffe2054c67fe902a633ff0815301dfacb28817ff64944657fb24a232ff99251015fcc9288cbfd64944657eb24a205ff19251015f8c92880fff5494407ff2a4a203ff5525101ff8a928817ff6394401ff31ca20abf98e51007fac728802fd639440bfe31ca203ffd4e5101efea72880ffe5394407fea9ca200df54e5101ff8a7288cbff4394465ff21ca232ff50e51197f88728817ff62944637fb14a231ff98a5100dfcc5288c7fd62944637eb14a205ff18a5100df8c52880fff5294407ff294a203ff54a5101ff8a5288c7ff4294463dfa14a231ff90a5118ffa85288c7bd4294463fe214a231ffcca5118ffc65288c7fd3294463fe194a203bf9865101ffea32880f7f5194407fba8ca205ff1465101fe8a3288cbff419440bff20ca232ff5065102ff883288c7ff219440bff10ca231ff4865102ff84328817ff6094401ff304a204bf98251007fac128802fd609440bfe304a203ffd425101ff8a12880f7c5094465ffa04a232ff90251197fa81288cbfc4094463ff904a231ff8825118ffa41288c7fc20944077fb2aa230ffd9151185fec8a88c3fe64544057f322a230ff59151185fac8a88c3fc64544057e322a203ffd515101efea8a880ffe5454407feaa2a230df5515101ff8a8a8803ff63544017fb1aa200ff98d51007fac6a8803fc63544157e31aa203ffd4d5101ffca6a88037e5354407fea9aa203ff14d5101ef8a6a88c3ff4354461ff21aa230ff50d51187f886a88bfff625445f7fb12a22fff9895100dfcc4a88bffd625445f7eb12a22fff1895100df8c4a880fff5254407bfa92a203ff9495101ffaa4a88bf7d5254407fe292a22fffd095117f7e84a88bffe425445ffea12a22fef5095117ff884a88bfff325445fff192a22fff4c95117ff864a880eff6154407ffa8aa203fdd455101ffca2a88037e5154407fe28aa203df1455101fe8a2a88c3ff4154461ff20aa230ff50551187f882a88bfff215445fff10aa22fff4855117ff842a8803ff60544017fb02a200ff98151007fac0a8803fc60544097e302a203ffd
  | 7 => 0x201001400000400000000400800000001600200200200c00200000400000400c00400000000400200000600400400000a00000200600000800000000200200200400600001000800400200000200000401000400000400201000000000200600a00000200400200200000a00000600c00600000000000800000401000000000000000200800200200000000200a00400400000400400000200000400000000200000200200000800400000000000000200000a00c00000000200600200200200200600200000200000400000e00200000800c00600600800200800000000200000000800000000000000200000400000000600000200000000200000600200000201200000000400000000a00000000200200200000e00201000400e00200400200000000200600200200000000200200000000201000000000600000000000200000000200600200000000e00000a00800200200000400c00600000000000200000400600000c00600c00000001001400200000000400000600800001000000000400000200800001800200000000800200400200200000400400800200800200200000400a00400000000000000800600200000201000200001400400400000400000800000000000000200000001600600a00200000200000000400200000200400400200200000200000200000200200000400000000a00400000000600000000400000600200600000000000600003bf59653057fec92982aff6494c15ff324a602bf99253057fac9298dafd6494c15fe324a60abf1925301ffea92980ffe5494c07feaa4a603ff15253055fcc72982bff5394c15bfa9ca603f7d4e5301ebea72982bfc5394c15ee29ca60affd0e53057fc872982bfd4394c15fe21ca60affd8a53055fec52982bfe6294c037f314a60aff58a531adfac52982bfc6294c037e314a603ffd4a5301ffca52980ffd5294c07fe294a635ffd0a531af7e85298d7fe4294c6bfea14a635ef50a531aff8852982bff3294c15ff194a60aff4ca53057f8652982bff6194c15ff30ca600bf98653057fac329802fd6194c15fe30ca603ffd465301efea32980ffc5194c6dffa0ca636ff906531b7fa83298dbfc4194c6bff90ca635ff886531affa43298d7fc2194c15ffb04a60aff98253025fcc12982bfd6094c017eb04a60aff1825301ffea12980ffc5094c07be284a636ffd02531b7fc81298dbfd4094c6dfe204a635ffc82531affc41298d7fd2094c6bfe104a60abfd95531a7fec8a98d2ff6454c01dfb22a600afd91531a7fcc8a980afe6454c69feb22a634bf591531a7f8c8a980afc6454c69de322a602af1915301ffea8a980f7f5454c07ff2a2a603ff551531a6faa8a980ffc5454c077fb1aa603ffd4d5301fbea6a982bfe5354c15bf29aa60aff14d53056f8a6a980fdc5354c6
  | 8 => 0x13ec0000000011d80000000000005d98c83bc180900a40f3c9b80012b40000008940000000000000011a42c13ac0000011014241500000000000018b40000000000000009f1674000000210a78120000000b5400000000017c000000d0400141400000000000000000000000000000000001400196414d5ec8840000002e80012e91ece099dc000abc3d56880019e00000000011689480180000000001cd2a8964000000000000000000acc000e2d3b4000bcc0010994e8dc08981d0000000ee49f92b034165c95c000000000c14000000f28afd4dc0015480a00000014f40000000000010ad6600000007180015b98680003111a0000000a5c000000e7503800000000153c0000001ed41c7b000085c00000070c000000000d15520000001621298000a70eb1154e1c3d8000d7400136430800000000000000000000000000000069400039c0007489a4000000820000000a0c00000129c0017e0000f2c00000000000000093108531800000097068400106800000079928528d8ec0006500000000017d4ae85f0d554d8c056e01f00000018a4000000000fa40011900000005ec0003e1704588d80e28084001880000001760000bfccdcccc398750d8800173000000000185c83559025c57c0012450311c844c1c8cfc0018d5208000d589411bd7512f800015c0000413517080000016bc5c00017c4f4c5210881f80010611b4ea8000300984000f8d44431d0580012d1818000aec1c40000000000007c40000000d000000000000126cdc8510a9d7716300010fc0000000000003d0000244000000000000000eb40000003c40940003ec000118000b50f68190000000000ecc00000000083c000000000a0518800000035935400191c00042836800156000000080125c00000022c9882ad73cbf400040c0000004580000000000003b80000000010e400018c6ac0000019500006980000013b00000000015a52700006580014954108d8b3800000001001600000c00400000a00000200400200e00000400600000000000000a00200000a00000200000800200600000001400400000800200600a00000000000200000000200000000600000200c00000000000000400000201000000400000000201600200000000200200000400400400000000400400000200000000200000200000400400600000000400000000200400200000200400000000400400000000000000800c00800800000000202a00000800200200000c00c00000a00000800c00000400000600000200000000000000000000600e00200800000000400400000000200000600000000000400000400200000200400400200000000400a00200600200000400000200000a00000400000000400001000001800000a00000000200000000000000200200200
  | 9 => 0xc200000009097dd64ca50280001210ff40000010b000057000117d7380000004116180013f40000000000006a00012b95e14c8d94000be87fc84c00118c000000a480000000006240640000000004680000011f0584bf9048050001644000000e6801d7a8001450000000000000000000000000001128e3c000bbc0010a4000000000000000000f1000082c000000001430938b8d2f00e0000000f1ca100005617694740000000006b8000a85144ed800000000000063c0014400013207440000015503803dd544a98000000000000000000000000aac4600dc0008cc0000001f40007bc00172400000052d3dc0011b00015780005fd5e80000014d00016b4001554000a300000011dc000000001468000000000d6c00018901c0000014f9200000e800000000000018f45acb6000167cab41300000000012e40000018118e80006bcc299008383a948c0000009582d00011a80000016d400000088c184000680000000540000cf95a194c0017bd5997b000012c00152c00000c0000000000000019319ccec59188e43240c9460cec0000001d80000011e00000013340000000000007a8000c08000000198000000000000ef00007380001e1178c680000000006c40000008440000000000007d151c0000000015fd250be00006787f4000e38000c50000000000000000e616cc19590c000000f0cbb0000000000f000000008407e45440000004d40000015312dc0000000000000000000000008dc00000000050c000000000000000000000000fe999942c0000000000004380004300006312380000d94fc000000000a80000001158000000000a4c0016100000000006b40000000004ec0015050740000006a80000006d1220000000f9000054d0000001a000080c000000000000000f500000012249140003f0508000000000720d700014c0000000000000000000000248000704000978a60f341258e102c69c00000000000019c00000000000162c0000017903217840017f4000164000e1400000047cfdd79c0000008800004180002082fc0000004980000018a00000000000000000000000000000014711c17e8000000fa00c00000004950e853d014cd8c842917ccdd91b86ed99c530aa8ebc558cc9870000b3c0000000019c4000000c400004b0001890408bb825859169d6a42b00000011842c90900010d400062c00000076926494c1a98085bc0005758e452848c000efc000bf0af461c8b48ac000000ab000192400000041c00000000000139d138ff000132c0012bc000000000000fa8000ffd6580001a49e0640000b9d3094cc00148800156d0f80000000000011700014380000019452308bc0011ad98184085935c260000000000b4c0003f4000bd504400000000002c99c001938a90b5c0016f000000100c000000001684000
  | 10 => 0x3f9278204b88cf5638060b5846c45c088c3000000111800000000000000053800000000000171c0000000000007080000000018bc0000c4b7c00000000000000000000067c00033400109c0a89240000014a00002f530c0000540000000000000000015b4b003607613d8cb00000000016500000000016c000000108d5d0628000000000000000a2c4000005b8000000d9ca559c93cc619774af0da8001624000850000000c780000017d0000a2160c000000bdd63570c00000140c000000001368000000000000000000000000000000f180018300009a865c0014a40006c00001588089047b80000000004656a000135844457800000075811d4d4ef40000000000003ac2a4000000001994998000000d4cf6400150d95c5d08b00016d8c90000e8c155954f215b086c0000000000000000000000000000000000019ac000000c252ec8616ac2280008e97800017452c95c421800000000064c0000001dc00000068c000001828000e5c0000000000000000000000000016640000000019040014ec0000000000010c0000100000e50000000000549778e204f566c3450a8000d900000000000000000000000005c90c4000c94000000000000cd0000dd00003c18dd07c8680019a8388a64b140fd149758ee993c0000014e41b8b04000000c18000000000ae00000004acdbc00000000155d6f9824000000f496d13740000014540002dc0000000008780000000000000000000012a04500005196141b400000000192c0000008e131d38c000f14d1c000000000c9c0000000000000000013483280009c19c000000081000038c9ac730fd40007293000000000009740000000000000013380000000000000000019400000000015d4000000874000000c38000000000c2c2880000000000bd9203fc0000000009200000000004c800000000000120d2fc00146d52523c6d5838000394000000fec0b00000007a00001e80000004a57fd9097f01780005e8c8c00000000114c00000158560000197c00000004cc81568ca92d8c0d0791300011e87ac0000000000007757180010047103e58004dd8cc7ecb94d00174cb403c5a0fe45980000000000000000001480017a0ce5289408de8de14640000004e4000000910c70000000000bb4484000000dac000000000000298edd97124c0000003cd60549c0000012c00000007940001447000000008c93e557c55d8500018457c00000000000017d8000000001020000000000000a380004c40000000000007f0000000cc00000019d800000103400000071400000035c00000000114176c0000000000002d45e4000000000000980000580000000000000ba4000000d497108657c8fcd2554b00003040000000000000000000000000000000000000016c80004b80000000000000006d80000000000000
  | 11 => 0x11e400000181ce5800000000000000013d8d0000f886dcba8764000000d200f975585800000000000055400104c0005c40009cc00000000000000008d50000103d698000000000000000000240000000000108b2957449d7f84e8478e195f15e40000f40000001fc6080000005148a80000000000000014bc0000004a800000147983400159400012800079d0dd9a0000d681040b4ddc6e4000000000ce87e859c0004b40018ac000000000000000000000000f6d0e0000424000000000000000f60f940009d19bd854000000d405640005d4b340000000001b00002316f4000000aa40a545d198000000000000994fd000000033822431475c0002f824cfb56a80000004900017ac0000005b4000df40000000006900000012180000000001ac0000008b8284000d640001700b98b000000091800000000026921d06c0000012f4c34944c98c4421c0009d87d90d056d1d59780000000000010ec000d384886210bc00182c0000000000013256e8b1c00000000000000016c001928000000b10000b4175c09148000039000112c0000017146040000008fc000000ed510c000ad400183c0019b54000002a8b900005cc000df90180000000016ecb7490c00005879051d690c5967066137d394b086392040000000015ac0013898f94f00013a09c8d980000002cd8c40019d40010b49bc0008a00000000000009e4474000788c7c0000000000000013e00000005f80009500000000000013c000000092d4aca3496d5bc370000000e000018f0000000000000000000070a1800184ca583740f09b03485a974996c00000000000400000000117400000000154c00066400000000000000187c00037c000000008bd986c0008c12800000000000012580000ec00000000000170189c0015880007404f800000093c0000000006e000000000172c0000000000000000000000000000004042e0000000d255a8614000d10d08df000174d88d4293106709fc000e0c000001340074de4780000000e70000000000000000000a7d510000000000000000000000000000038000000000000001934000be4e65514ed00016e4cac6c8000000000c1c4fc00034c000e492d400000000000000198c000000000000000aa00000000000012900008f47781d4000000000000fc86fcf5c00186145896800000007c0000000005680006b03e8000c60000000d5c000000001580000034960cf0fbc7a40000000006f8a688d427d7940006753785040000000000014b4d1800060c0000000004a1028f400003a40018a87cc6a47e12cc27158c000000000000000000c3ce90000000000000ce0001984448000001194550eb978d2e0000000000f30434000214000000000000000000000000000000000ad112515000006c00000000000000
  | 12 => 0x284cce84000000000000000000594bc87351c40000000000000008c4000000a00000000000000000000000000d78000c5522c00000188800000042000000000009800000000000133000000000000000000000123534c000000001065094d0c00000180441597497c9d4e940314196fc000000000af80006341602f06687700008f95f4a6d4e1108000000000000000cb94900003b0d44000000001498000000000784000e34000000fe0e4ca8c0000806f0fd8000000000000add0500000000000000005a43a00000010400000000016c5968000001360eac71c0000000000000e828d05c000294e9c0000009a1849228000000cc5054001734b6d9d0069214b68c6d2404d93bc000000f980000000000000018640000000000000004e0d2c00187400000035400048127c0e515c3640000000000005e00002518940013fd2600017e400000113400093568cdfd13c610db00000000010246f400180c0004bc000000fc0bacea5384000000000ba1680b98000d3c00000000089c4c00000000000000000000000000000002d800000058c000000000c5c274000ee000000161c89000000000000066d0f0000f08000000000000000318000000000fb00010700015413f0b440000000011cd3e80008140ac000dc56091fc000000000a44000000a3c0006454480000012c4bc0264001180000000fc40000009540003c880411511c0000003b4000000e30000000000000000378bec000000000f54b8000076d3a48f000000147c0000000000000000002780000000018d8ac0000d349e80013280000000017a40000018fcc74000c49564000000f9c0000000011040000000000000000005000000000014340000013d0000000020078b70648d840000019b1765558da4000000a8825400010d8b8f44000a24000000000000001120000000d60000000000000000000000000000000000000fac00177c000b84e799580000000007b422000074ce6c0002b40000000000013b80005dc000000c4c000000000000000000000000000000a150f432d59d990000044001114000000e40000000000000e7cad80000000000016413055c8b493d4f04cbc0000000010b8e1133d5f80000000000000010a0a2800148400000000000000029c82842c234000000000000000b0c000819538000755404d7c7dd2a4000000000000000000000000000dcc001820000000000ec93a9728ec13c8001910385380000e540016b86ccf712ad2740000008d09ecca000000000000000000000000000136c0015dcc6487d4c53f9571628f780012680000007c877c000000000000000000b640009b4689884000000654000b200000000002ec5f5988e443512951f4140c880017b82380cc0000000000000000000000017980d400000072c4d18c020000043c000000
  | 13 => 0x9f45b009c000ab80010c8000000dd4000000848000001160000000db4000000ac943d5cc0000000000000010cc7f80000007c00000015d8000a94000000000000000f75518ef8ff8000b19249788d28000000000001398000000d50fb8000000001740110e88000f5800000098c9dc4717200000000000000000001380019156486000011f804800000165563d01137153400026c000534000000db80000000000005244f13908300019600004400015289288551d0000824f849c5694135508c102c46e8000000000000a08000e98000000001678000000000000000000000000e254b8f7c0000000000008a40000000011115c0bc40102e47d4f2581400073c888f8119c81c000000000b24000000b7800000091c0014a8000eec7250080000000001c116c0000000000000000017b40000001e40019b823c05c00033d668000024000cd4ea144cbd04540002b8000e042bc001314000000000001344000c000000000000001bc000d3016878d9a433000194830d3c40000000016dc000000000b30f380000017ec0016b0d8c000000a1c000000000000000990870000000ded0810d80014200000000000018788ec0000002a0ca4ac4da000116420cb2ca74ae436d8980
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf2158c1002ede2158c10006dd2158c1002edc2158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de5058c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc2058c10026df1058c10026de1058c10026dd1058c10026dc1058c10054ff7694c10024fe7694c10004fd7694c10024fc7694c1001e7e6594c100067d6594c101b6be6494c10006bd6494c10056de6394c10006dd6394c100475f5394c101aeee6294c10004ff7654c10024fe7654c10004fd7654c10024fc7654c1001e7e6554c100067d6554c10005bf7454c1003dbc7454c101a6be6454c10006bd6454c10056de6354c10006dd6354c1019eee6254c10005fb7054c10025f87054c10006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ae7458810006ed7458810006ad7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810036ef715881002eee7158810036ed715881002eec7158810006ef515881002eee515881002eec5158810006ef415881002eee4158810006ed415881002eec415881002eee315881002eec3158810026ef7058810026ee7058810026ed7058810026ec7058810026ef5058810026ee5058810026ed5058810026ec5058810026ef4058810026ee4058810026ed4058810026ec4058810026ef3058810026ee3058810026ed3058810026ec3058810026ef1058810026ee1058810026ea1058810026ed1058810026ec1058810094ff765441001e7e65544100067d6554410186be6454410006bd6454410006de6354410006dd635441017eee6254410006ed6254410004fd76cc4100457e75cc4100057d75cc4101767e65cc4100067d65cc41016ebe64cc410006bd64cc410056de63cc410006dd63cc410166ee62cc410006ed62cc410004ff764c41014e7e654c4100067d654c410146be644c410006bd644c410056de634c410006dd634c41013eee624c410006ed624c41002fd4314c410025fb7644010006fb7644010004fb76440100077b75440100077875440100277a6544010027796544010007bb74440101c7b87444010027ba6444010027b96444010027da6344010027d96344010026fb6244010027ea62440101bef96244010027e96244010006e962440101bfbb42440101bfb94244010025fb7144010027f3714401002efa6144010027f2614401002ff25144010007f1514401002ff23144010007f131440101bff3214401002ff02144010
  | 1 => 0x9010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901003ebf715901002ebe715901003ebd715901002ebc7159010006bf515901002ebe515901002ebc515901002ebe315901002ebc3159010006bf215901002ebe2159010006bd215901002ebc2159010026bf7059010026be7059010026bd7059010026bc7059010026bf5059010026be5059010026bd5059010026bc5059010026bf3059010026be3059010026bd3059010026bc3059010026bf2059010026be2059010026bd2059010026bc2059010026bf1059010026be1059010026bd1059010026bc1059010056df7598c10056de7598c10056dd7598c10056dc7598c10056df7498c10056de7498c10056dd7498c10056dc7498c10006df5498c10006de5498c10006dd5498c10006dc5498c10056df7298c10056de7298c10056dd7298c10056dc7298c10006df5298c10006de5298c10006dd5298c10006dc5298c10006df4298c100069f4298c10006de4298c10006dd4298c100069d4298c10006dc4298c1002ede7198c1002edc7198c10006df5198c1002ede5198c1002edc5198c10006df4198c1002ede4198c10006dd4198c1002edc4198c10006df2198c1002ede2198c10006dd2198c1002edc2198c10026df7098c10026de7098c10026dd7098c10026dc7098c10026df5098c10026de5098c10026dd5098c10026dc5098c10026df4098c10026de4098c10026dd4098c10026dc4098c10026df2098c10026de2098c10026dd2098c10026dc2098c10026df1098c10026de1098c10026dd1098c10026dc1098c10004ff7558c1001cfe7558c1001cfc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c10024ff7358c10026df7358c10006df5358c10006dc5358c10006df4358c10006de4358c10006dd4358c10006dc4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c10006bf4258c10006bd4258c10006df3258c10006de3258c10006dd3258c10006dc3258c10054ff7158c1002cfe7158c10054fd7158c1002cfc7158c1002ede3158c1002edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c100069f4258c10006de4258c10006dd4258c100069d4258c10006dc4258c1002ede7158c1002edc7158c10006df5158c1002ede5158c1002edc5158c10006df4158c1002ede4158c10006dd4158c1002edc4158c10006d
  | 2 => 0x6bf640c510126bc640c51001cff765411006cfd765411001cfc76541100067f655411001e7c6554110006bf6454110106bc6454110005f77154110005f47154110027f01054110004fe76cc11002cfc76cc1100067f65cc1100f67c65cc110006bf64cc1100eebc64cc110006df63cc110056dc63cc110005f671cc110005f571cc110054ff764c110004fd764c110054fc764c1100057f754c11006d7c754c1100067f654c1100c67c654c110005bf744c110065bc744c110006bf644c1100bebc644c110006df634c110056dc634c110005f7714c110005f4714c110027f0104c1100067f65c41100967c65c4110006bf64c411008ebc64c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41100077865c4110007bb64c41101dfb864c411002dfb72c41101d5f972c41101cfbb42c41101cfb942c4110025fa71c4110026fb61c4110027f361c4110024ff75594100267f7559410004ff7459410014fe7459410004fd7459410014fc74594100467f54594100067e54594100067d54594100467c5459410004ff7359410054fc73594100467f53594100467c5359410004ff725941000cfe7259410004fd725941000cfc72594100467f52594100067e52594100067d52594100467c5259410006bf4259410006bd425941001cff715941002cfe715941001cfd715941002cfc715941002e7e515941002e7c5159410024ff7059410024fe7059410024fd7059410024fc70594100267e50594100267c50594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100063f42594100067e42594100067d42594100063d42594100067c42594100067f32594100067e32594100067d32594100067c32594100467f715941002e7e715941002e7c71594100067f415941002e7e41594100067d415941002e7c415941002e7e315941002e7c31594100067f215941002e7e21594100067d215941002e7c21594100267f70594100267e70594100267d70594100267c70594100267f40594100267e40594100267d40594100267c40594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267e10594100267d10594100267c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010004bd7259010006bc7259010006bf5259010006be525
  | 3 => 0xc71d9110006bf51d9110006bc51d9110006bf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d91101e6be70d9110066bd70d91101e6bc70d9110006bf50d91101e6be50d91101e6bc50d91101e6be30d91101e6bc30d9110006bf20d91101e6be20d9110006bd20d91101e6bc20d91101e6be10d9110066bd10d91101e6bc10d9110054fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006bf42d8d10006bd42d8d10006de32d8d10006dc32d8d1002cfe71d8d1002cfc71d8d10024fe70d8d10024fc70d8d10006fa20d8d10006f920d8d1006d7e7598d100057d7598d100067f6598d100067c6598d10065be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d100057f7558d1006d7c7558d100067f6558d100067c6558d10005bf7458d10065bc7458d10006bf6458d10006bc6458d10005ef7258d1005dec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d10006bf4258d10006bd4258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10006fa2058d10006f92058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10056de6318d10006dd6318d10054ff7694d10004fe7694d10004fd7694d10054fc7694d100067f6594d1001e7c6594d10006bf6494d101b6bc6494d1006f5f5394d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d10005bf7454d10065bc7454d10006bf6454d101a6bc6454d10084fe76945100067f659451001e7c6594510006bf6494510196bc6494510024fc76545100067f655451001e7c6554510006bf6454510186bc6454510005fb7054510025f87054510024fe76cc510024fc76cc51006d7e75cc5100057d75cc5100067f65cc5101767c65cc510006bf64cc51016ebc64cc510006df63cc510056dc63cc510025fa70cc510005f970cc510004fe768c51006d7e758c5100057d758c5100067f658c51015e7c658c510065be748c510005bd748c510006bf648c510156bc648c510024fc764c5100067f654c51014e7c654c510006bf644c510146bc644c510006df634c510056dc634c510005fb704c510025f8704c510004fe760c5100067f650c51012e7c650c510
  | 4 => 0x951006e7f51d9510024fe70d951006cfd70d9510024fc70d951006e7f50d951006d7e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067f62d95100067e62d95100067d62d95100067c62d95100073f42d95100073d42d95100077a20d95100077920d95101f77610d95101f77410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95101f67f71d951006e7e71d95100067d71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f21d95100067e21d95100067d21d95100067c21d95100067f70d95101f67e70d95100067d70d95101f67c70d95100067f40d95101f67e40d95100067d40d95101f67c40d95101f67e30d95101f67c30d95100067f20d95101f67e20d95100067d20d95101f67c20d95101f67e10d95101f67c10d951006e7c6559510005bf7459510065bc7459510006bc645951006cff75595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc7459510004ff7359510054fc7359510004ff725951000cfe7259510004fd725951000cfc7259510006bf4259510006bd4259510084ff7159510006f77159510094ff7059510006fb70595100057e761951006e7e76195100047e76195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067f62195100067e62195100067d62195100067c62195100073f42195100073d42195101ee7f61195100077a20195100077920195101ef7610195101ef741019510065be76d9110066be76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ba20d9110007b920d91101e7b610d91101e7b410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91101e6bf71d9110066be71d9110066bd71d9110066b
  | 5 => 0x2edc3158f10054ff7694f1002cfe7694f10004fd7694f1002cfc7694f1001e7e6594f100067d6594f100975f5394f10004ff7654f1002cfe7654f10004fd7654f1002cfc7654f100067f6554f1001e7c6554f10005bf7454f1008dbc7454f10005fb7054f10025f87054f10044ff765471002e7f655471002e7c65547100957e75cc7100057d75cc71002edf63cc71002edc63cc71002edf634c71002edc634c71001cff765431002cfc765431001e7e65543100067d6554310005f7715431002df47154310056de63cc310006dd63cc31002df671cc310005f571cc310054ff764c3100057f754c3100957c754c310005bf744c31008dbc744c310056de634c310006dd634c310005f7714c31002df4714c3100267f7559610004ff7459610014fe7459610004fd7459610014fc7459610004ff7359610054fc73596100867f5359610004ff725961000cfe7259610004fd725961000cfc7259610006bf4259610006bd42596100867f5159610024fc70596100267e50596100267c5059610004ff7558e100067f7558e100047f7558e1001cfe7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e10006bf7458e10004bf7458e10014fe7458e10004fd7458e10014fc7458e10006bc7458e10014bc7458e10026df7358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e10006bf4258e10006bd4258e10024fc7058e10026de3058e10026dc3058e10026fa2058e10006f92058e10054ff7694e10024fe7694e10004fd7694e10024fc7694e1020e7f6594e1001e7c6594e10056de6394e10006dd6394e100875f5394e10004ff7654e10024fe7654e10004fd7654e10024fc7654e1001e7e6554e100067d6554e10005bf7454e1007dbc7454e10056de6354e10006dd6354e1006cfd76946101f67f659461001e7c659461008777519461001cff7654610024fc765461001e7e65546100067d6554610005fb7054610025f870546100857e75cc6100057d75cc610056de63cc610006dd63cc610025fa70cc610005f970cc6100857e758c6100057d758c61007dbe748c610005bd748c610054ff764c610056de634c610006dd634c610005fb704c610025f8704c610007d5310c610025f976c421002ef976c421002dfb72c4210205f972c42101ffbb42c42101ffb942c4210027f271c421001cfe76d951006e7e65d9510006bc64d9510004ff74d9510014fe74d9510004fd74d9510014fc74d951006e7f54d95100067e54d95100067d54d951006e7c54d9510054fe73d9510004fd73d951006e7f53d951006e7c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d951006e7f52d95100067e52d95100067d52d951006e7c52d9510006bf42d9510006bd42d951002cfe71d9510024fd71d951002cfc71d
  | 6 => 0xe70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300265f30594300267e30594300267d30594300265d30594300267c30594300267f20594300267e20594300267d20594300267c20594300267f10594300267e10594300267d10594300267c105943001cfe7598430004fd759843002cfc759843002cff7498430014fe7498430004fd749843002cfc749843002cff729843000cfe7298430004fd729843002cfc7298430006bf4298430006bd4298430024fe7198430026f6719843002ef64198430006f54198430056f7319843002ef4319843002ef62198430006f52198430026f61098430026f41098430004ff755843001cfe755843001cfc7558430004ff7458430014fe7458430004fd7458430014fc7458430004ff725843000cfe7258430004fd725843000cfc7258430006bf4258430006bd4258430026f77158430006f64158430006f54158430056f73158430056f43158430006f62158430006f52158430026df3058430026dd3058430026f61058430026f4105843002cff7694430024fe7694430004fd769443001e7e65944300067d6594430004ff7654430004fd7654430024fc765443001e7e65544300067d6554430005fb7054430025f87054430094fd75d971002cff74d9710014fe74d9710004fd74d971002cfc74d9710054fe73d9710004fd73d97100967f53d971002cff72d971000cfe72d9710004fd72d971002cfc72d9710006bf42d9710006bd42d971002ef671d971002e7f51d971002ef970d97101f67e50d97101f67c50d971001cff765971002e7c655971002e7f7559710004ff7459710014fe7459710004fd7459710014fc74597100967f54597100067d5459710004ff7359710054fc73597100967c5359710004ff725971000cfe7259710004fd725971000cfc72597100967f52597100067d5259710006bf4259710006bd4259710024fc715971002e7e515971002e7c51597100967f505971001cfe75d8f1002e7e75d8f1001c7e75d8f10004fd75d8f1002e7d75d8f100047d75d8f1002cfc75d8f1002cff74d8f10014fe74d8f1002ebe74d8f10014be74d8f10004fd74d8f1002ebd74d8f10004bd74d8f1002cfc74d8f1002cff72d8f1000cfe72d8f10004fd72d8f1002cfc72d8f10006bf42d8f10006bd42d8f1002ef671d8f1002ef970d8f10004fd7698f100957e7598f100057d7598f1002edf6398f1002edc6398f10054ff7658f1002edc6358f10004ff7558f1001cfe7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f1002edf7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f10006bf4258f10006bd4258f10006df3258f10006dd3258f10024fc7158f1002ede3158f10
  | 7 => 0x4530004ff7654530004fe7654530004fc76545300067f655453001e7c6554530006bf6454530186bc64545300075e5354530005de76cc530056de76cc530055df75cc5300575e75cc530005dd75cc5300575d75cc5300055d75cc5300075f65cc5300075c65cc5300079f64cc5302379c64cc53022edf62cc53022edd62cc53022f9f42cc53022f9d42cc53002edc61cc530025de70cc530025dc70cc530056df60cc530057db60cc53022fda20cc53022fd920cc530024fe768c5300c57e758c5300057d758c5300067f658c53015e7c658c5300bdbe748c530005bd748c530006bf648c530156bc648c530225dd738c530006f7618c53002ef4618c530025fa708c530005f9708c530024fc764c5300067f654c53014e7c654c530006bf644c530146bc644c530006f7614c530006f4614c530005fb704c530025f8704c530024dc764c530005df754c530005dd754c5300075f654c5300075c654c5300079f644c53021f9c644c530216df624c530216dd624c5302179f424c5302179d424c530055df714c530057d7714c530007d7614c53002edc614c530007d4614c530006d4614c530217d6214c530217d5214c530007db704c530025de704c530025dc704c530007d8704c530056df604c530057db604c530217da204c530217d9204c53001cff76541300c4fd7654130054fc76541300067f655413001e7c6554130006bf6454130106bc6454130005df7354130055dc73541300075d5354130027d83054130024ff75594300267f7559430004ff7459430014fe7459430004fd7459430014fc74594300ae7f54594300067e54594300067d54594300ae7c5459430054ff7359430054fe7359430054fd7359430054fc73594300567e53594300567c5359430004ff725943000cfe7259430004fd725943000cfc72594300ae7f52594300067e52594300067d52594300ae7c5259430006bf4259430006bd4259430004ff715943002cfc71594300ae7f51594300ae7c5159430024fe7059430024fc70594300267e50594300267c5059430026df3059430026dd30594300067f74594300067e74594300067d74594300067c74594300567f73594300567e73594300567d73594300567c73594300567f43594300567e43594300567d43594300567c43594300067f72594300067e72594300067d72594300067c72594300067f42594300063f42594300067e42594300067d42594300063d42594300067c42594300567f32594300567e32594300567d32594300567c32594300067f71594300067e71594300067d71594300067c71594300067f41594300067e41594300067d41594300067c41594300567f31594300567e31594300567d31594300567c31594300067f21594300067e21594300067d21594300067c21594300267f70594300267
  | 8 => 0x6be52d9130006bd52d9130006bc52d9130266bf32d9130006be32d9130006bd32d9130266bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006bc51d9130266bf31d9130266bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d9130266bf70d913025ebe70d91300bebd70d913025ebc70d9130006bf50d913025ebe50d913025ebc50d9130266bf30d913025ebe30d91300bebd30d913025ebc30d9130006bf20d913025ebe20d9130006bd20d913025ebc20d913025ebe10d913025ebc10d9130005de7694d30056de7694d300c5dd7594d300075f6594d3001ede6594d3001edc6594d300c75c6594d3001e5c6594d300079f6494d302579c6494d3024f9f4294d3024f9d4294d30005dd7194d300c75f5194d30025de7094d30025dc7094d30056df6094d30057db6094d3020f5e5094d3020f5c5094d3024fda2094d3024fd92094d30024fc7654d300067f6554d3001e7c6554d30005bf7454d300bdbc7454d30006bf6454d301a6bc6454d300575c5354d30005fb7054d30025f87054d30057d83054d30025dc7654d3001edc7654d30024dc7654d30055df7554d300575f7554d300075f6554d3001ede6554d3001edc6554d300c75c6554d300079f7454d302479c7454d300079f6454d302479c6454d300c75f5454d302475d5454d300c75f5254d3023f5d5254d3023f9f4254d3023f9d4254d30005df7154d300c75c5154d30007db7054d30025de7054d30025dc7054d30007d87054d30056df6054d30057db6054d300c75f5054d3023fda2054d3023fd92054d300067f65d85300067c65d8530006bf64d8530006bc64d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d8530006bf42d8530006bd42d8530006f721d8530006f421d8530006fa20d8530006f920d85300c57e75985300057d75985300067f65985300067c65985300bdbe7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300c57c75585300067f65585300067c6558530005bf74585300bdbc7458530006bf6458530006bc6458530005ef72585300b5ec72585300067f65185300067c6518530006bf6418530006bc6418530006f5611853001cfe7518530004fd751853002cfc751853002cff7418530014fe7418530004fd741853002cfc741853002cff721853000cfe7218530004fd721853002cfc7218530006bf4218530006bd4218530006f7211853002ef42118530024fe7018530024fc7018530004fe7694530004fd769453002cfc76945300067f659453001e7c6594530006bf6494530196bc6494530055de7394530005dd73945300075d539
  | 9 => 0xd70d95300c67f50d95300c57e76d953001c7e76d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d953020f5f73d95300067f62d95300067e62d95300067d62d95300067c62d95300073f42d95300073d42d953027f7b30d953020f5e30d953020f5c30d953027f7830d95300077a20d95300077920d95300067f74d95300067e74d95300067d74d95300067c74d953020e7f73d953027e7e73d95300067d73d953027e7c73d95300067f43d953027e7e43d95300067d43d953027e7c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300063f42d95300067e42d95300067d42d95300063d42d95300067c42d953027e7f32d95300067e32d95300067d32d953027e7c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d953027e7f31d953027e7c31d95300067f21d95300067e21d95300067d21d95300067c21d953027e7f70d953020e7e70d95300067d70d953020e7c70d95300067f40d953020e7e40d95300067d40d953020e7c40d953027e7f30d953020e7e30d953020e7c30d95300067f20d953020e7e20d95300067d20d953020e7c20d953020e7e10d953020e7c10d95300c67c6559530005bf74595300bdbc7459530006bc64595300c4ff75595300067f7559530004ff7459530006bf7459530004bf7459530014fe7459530004fd7459530014fc7459530006bc7459530014bc74595300dcff7359530006df7359530004ff725953000cfe7259530004fd725953000cfc7259530006bf4259530006bd4259530004ff715953002cfc71595300f4ff7059530006fb70595300057e76195300c67e76195300047e76195300067f64195300067e64195300067d64195300067c64195300073c64195300063c64195300c75d73195302767f63195300067f62195300067e62195300067d62195300067c62195300073f42195300073d421953026e7f601953026f7b30195302775e30195302775c301953026f7830195300077a20195300077920195300bdbe76d91300bebe76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130005bf72d9130005bd72d9130006bf62d9130006be62d9130006bd62d9130006bc62d9130267bb30d913025f9e30d913025f9c30d9130267b830d9130007ba20d9130007b920d9130006bf75d9130006be75d9130006bd75d9130006bc75d913025ebf73d9130266be73d91300bebd73d9130266bc73d9130006bf53d9130266be53d9130266bc53d9130006bf72d9130004bf72d9130006be72d9130006bd72d9130004bd72d9130006bc72d9130006bf52d9130
  | 10 => 0x873000cfc7258730006bf4258730006bd4258730056f77158730056f73158730056f43158730006f62158730006f5215873002cff7694730054fe7694730004fd769473001e7e65947300067d6594730055de7394730005dd73947300075d5394730004ff7654730004fd7654730054fc765473028e7f655473001e7c6554730055de735473028f5e5354730005fb7054730025f87054730055df764c730006df764c730005df754c730005dd754c730056df624c730286dd624c7302879f424c7302879d424c730057d7714c73002ede614c730287d6214c730287d5214c730025de704c730025dc704c73001cff7654330054fc765433001e7e65543300067d6554330005df7354330055dc73543300075d5354330027da30543300267f7559630004ff7459630014fe7459630004fd7459630014fc74596300de7f5359630004ff725963000cfe7259630004fd725963000cfc7259630006bf4259630006bd4259630004ff715963002cfc71596300de7f5159630024fc70596300267e50596300267c5059630026df3059630026dd305963001cff7654e30024fc7654e3001e7e6554e300067d6554e30005bf7454e300d5bc7454e30005fb7054e30025f87054e30057db3054e3001cfe7598630004fd759863002cfc759863002cff7498630014fe7498630004fd749863002cfc749863002cff729863000cfe7298630004fd729863002cfc7298630006bf4298630006bd4298630026f67198630024fe7098630026f61098630026f41098630004ff75586300067f75586300047f755863001cfe755863001cfc75586300067c755863001c7c7558630004ff7458630014fe7458630004fd7458630014fc7458630004ff725863000cfe7258630004fd725863000cfc7258630006bf4258630006bd4258630026f77158630024fc7058630026df3058630026dd3058630026fa2058630006f92058630026f61058630026f4105863002cff7694630024fe7694630004fd76946301f67f659463001e7c6594630004ff7654630004fd7654630024fc765463001e7e65546300067d65546300dd7e758c6300057d758c6300d5be748c630005bd748c63002ef6618c630006f5618c630025fa708c630005f9708c630006f6614c630006f5614c630057d4314c630005fb704c630025f8704c63001cfe76d95300c67e65d9530006bc64d9530004ff74d9530014fe74d9530004fd74d9530014fc74d95300c67f54d95300067e54d95300067d54d95300c67c54d9530054fe73d9530024fd73d9530054fc73d95300c67f53d9530004ff72d953000cfe72d9530004fd72d953000cfc72d95300c67f52d95300067e52d95300067d52d95300c67c52d9530006bf42d9530006bd42d953002cfe71d9530004fd71d95300c67f51d95300c67c51d9530054f
  | 11 => 0x14fe74d8550004fd74d8550014fc74d8550054fe73d8550004fd73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d8550006bf42d8550006bd42d8550086f651d8550086f551d8550006f7619855006df97098550005bf7458550105bc7458550095fb7058550105be7418550005bd7418550006f56118550024fd751855002cff7418550014fe741855002ebe7418550014be7418550004fd741855002ebd7418550004bd741855002cfc7418550054fe7318550004fd73185500467f53185500067d531855002cff721855000cfe7218550004fd721855002cfc7218550006bf4218550006bd421855002e7f511855002ef65118550046f551185501ee7e50185501ee7c50185500247c76545502ae7f64545502ae7d64545500057f735455028e7c63545502a67f62545502a67d62545502a73f42545502a73d425455001d7f715455001f77715455000777615455002e7c61545500077461545500077b70545500257e70545500257c705455000778705455001e7f605455001f7b6054550004fe76cc550004fd76cc550054fc76cc55001d7e75cc5500057d75cc550004fe768c550004fd768c55002cfc768c55001d7e758c5500057d758c550105be748c550005bd748c550004ff764c550004fe764c550004fc764c55001d7e754c5500057d754c550004fe760c550004fd760c55002cfc760c55001d7e750c5500057d750c550025fa700c550005f9700c5500567f7559730004ff7459730014fe7459730004fd7459730014fc74597300f67f54597300067d5459730024fc73597300567e53597300567c5359730004ff725973000cfe7259730004fd725973000cfc72597300f67f52597300067d5259730006bf4259730006bd4259730004ff715973002cfc71597300f67c51597300f67f5059730055df7654f300aedf7654f300575f7554f300575f6554f3001ede6554f30056dc6554f300575c6554f300079f7454f3029f9c7454f300f75f5454f3029f5d5454f300f75f5254f302975d5254f302979f4254f302979d4254f30005df7154f300f75c5154f30025de7054f30025dc7054f300f75f5054f3001cfe759873002e7e759873001c7e7598730004fd759873002e7d75987300047d759873002cfc759873002cff7498730014fe749873002ebe7498730014be7498730004fd749873002ebd7498730004bd749873002cfc7498730024fe7398730024de739873002cff729873000cfe7298730004fd729873002cfc7298730006bf4298730006bd429873002ef6719873002edf3198730056f7319873002ef4319873002ef62198730006f52198730004ff755873001cfe755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc7458730024fc7358730004ff725873000cfe7258730004fd725
  | 12 => 0xf4258e50006bd4258e50004ff7158e5002cfc7158e500c67c5158e50024fc7058e500267f5058e500267d5058e50026de3058e50026dc3058e5027d7f7494e502ed7d7494e5001d7e7394e5001f5e7394e5020e7f6394e5020f5e6394e5027e7d6394e5020f5d6394e500065d6394e5027d7f7294e502e57d7294e502df3f4294e502df3d4294e500057e7194e5020f7a7094e5020d7d7094e5027f797094e50005797094e5001e7e6094e5001f7a6094e5020f5f3094e5002cff7498650014fe7498650004fd749865002cfc7498650054fe7398650004fd739865002cff729865000cfe7298650004fd729865002cfc7298650006bf4298650006bd4298650026f6719865002ef65198650096f55198650024fe7098650024fc7098650026f61098650026f41098650004ff7458650014fe7458650004fd7458650014fc745865006e7f54586500067d5458650004ff7358650054fc73586500067e535865006e7c5358650004ff725865000cfe7258650004fd725865000cfc725865006e7f52586500067d5258650006bf4258650006bd4258650026f7715865006ef6515865006ef5515865006e7c5158650024fc70586500267f50586500267d5058650026f61058650026f410586502d57f74946502d57d749465027d7e73946500067d63946502cd7f72946502cd7d72946502c73f42946502c73d429465001d7e719465001f7671946501f77661946500067d61946501f77561946501f77a70946501f57d709465000779709465001e7e609465001f7a6094650054ff76cc650024fe76cc650004fd76cc65001d7e75cc6500057d75cc650056de63cc650006dd63cc65002cff768c650024fe768c650004fd768c65001d7e758c6500057d758c650115be748c650005bd748c650004ff764c650004fd764c650024fc764c6500057f754c65001d7c754c650056de634c650006dd634c65002cff760c650024fe760c650004fd760c65027d7f750c65001d7c750c650025fa700c650005f9700c650024fd75d8d50004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500dede53d8d500dedd53d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d50006bf42d8d50006bd42d8d5002cfe71d8d50004fd71d8d5020e7f6598d50006df6398d500c5f97098d50005bf7458d50105bc7458d500f5fb7058d502767f6518d50056de6318d50006dd6318d500247c7654d500073f7454d502bf3c7454d502be7f6454d502be7d6454d5001d7f7354d5001f5f7354d500075f6354d500567e6354d500567c6354d500075c6354d502b67f6254d502b67d6254d502b73f4254d502b73d4254d500057f7154d500077b7054d500257e7054d500257c7054d50007787054d5001e7f6054d5001f7b6054d50024fd75d8550004ff74d8550
  | 13 => 0x95310067d5259531006bf4259531006bd4259531174ff7159531006f7715953114e7c5159531004ff7059531006fb7059531004fb7059531024fc7059531006f87059531024f8705953114e7f505953101cfc7654d310067f6554d3101e7c6554d31005bf7454d31145bc7454d31005f77154d31005f47154d31174fe769453101e7e65945310067d659453114f77519453101cff765453114cfd7654531054fc76545310067f655453101e7c6554531005df7354531055dc735453114d7e758c5310057d758c531145be748c531005bd748c531055f6718c531056f7618c53102f5e758c53102f5d758c53102f9e748c53102f9d748c53102ddf728c53130ddd728c5313079f428c5313079d428c53102dde718c53102edf618c531057d7618c53102fd6218c531307d5218c531005dd708c53101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d8131004ff72d813100cfe72d8131004fd72d813100cfc72d8131006bf42d8131006bd42d8131006fb50d8131006f850d8131006fb60981310057f755813114d7c7558131005bf7458131145bc7458131005ef725813113dec725813114d7e75181310057d7518131026fa6018131006f9601813102cff755943102e7f7559431004ff7459431014fe7459431004fd7459431014fc745943112e7f54594310067d5459431054fe7359431054fc73594310567e53594310567c5359431004ff725943100cfe7259431004fd725943100cfc725943112e7f52594310067d5259431006bf4259431006bd425943102cfe715943102cfc715943102e7e515943102e7c5159431004ff7059431024fc705943112e7f505943115cff765443102e7f655443102e7c655443102ddf764c431006df764c431004df764c43102edf624c4312f6dd624c4312f79f424c4312f79d424c43102ddf714c431057d7714c43102ede614c43102fd6614c43102fd6414c4312ffd5414c43102fd6214c4312f7d5214c431004ff75580310067f75580310047f755803101cfe755803101cfc75580310067c755803101c7c7558031004ff7458031006bf7458031004bf7458031014fe7458031004fd7458031014fc7458031006bc7458031014bc7458031004ff725803100cfe7258031004fd725803100cfc7258031006bf4258031006bd4258031056df3158031006dd315803102efb7058031006fa4058031006f94058031056fb3058031056f83058031006fa2058031006f9205803102efb105803102ef81058031004ff7458e50014fe7458e50004fd7458e50014fc7458e500c67f5458e500067d5458e50026df7358e500c6de5358e500c6dd5358e5027e7c5358e50004ff7258e5000cfe7258e50004fd7258e5000cfc7258e500c67f5258e500067d5258e50006b
  | 14 => 0x31fb7315923102fb4315923102fb62159231007b5215923102ebf605923102ebc6059231006bf7559231006be7559231006bd7559231006bc7559231156bf735923131ebe7359231006bd735923131ebc7359231006bf535923131ebe535923131ebc5359231006bf7259231004bf7259231006be7259231006bd7259231004bd7259231006bc7259231006bf5259231006be5259231006bd5259231006bc525923131ebf3259231006be3259231006bd325923131ebc3259231156bf715923102ebe7159231156bd715923102ebc7159231006bf515923102ebe515923102ebc515923131ebf315923102ebe315923102ebc3159231006bf215923102ebe2159231006bd215923102ebc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006bc505923131ebf305923131ebc3059231006bf2059231006be2059231006bd2059231006bc205923102ebf105923102ebc105923101cff7654e3102cfc7654e3101e7e6554e310067d6554e31005bf7454e31155bc7454e311a6be6454e31006bd6454e31005f77154e3102df47154e31057d73154e3112cff765463101e7e65546310067d6554631186be6454631006bd645463102ddd76cc631056dd76cc6310575e75cc6310575d75cc63102f5e65cc63102f5d65cc63102f9e64cc63102f9d64cc63102edf62cc631316dd62cc6313179f42cc6313179d42cc63102fd661cc63102fd651cc631007d551cc6310067e65982310067d6598231006be6498231006bd649823102efb6098231026f860982310067e65582310067d6558231006be6458231006bd645823102ef86058231004ff755823101cfe755823101cfc7558231004ff7458231014fe7458231004fd7458231014fc7458231004ff725823100cfe7258231004fd725823100cfc7258231006bf4258231006bd425823102cfc7158231006df3158231006fa2058231006f9205823102efb105823102ef8105823101cfe76d953114e7e65d9531004ff74d9531014fe74d9531004fd74d9531014fc74d953114cfd73d953114e7f53d9531004ff72d953100cfe72d9531004fd72d953100cfc72d9531006bf42d9531006bd42d9531054fd71d953114e7f51d9531024fe70d9531004fd70d953114e7c50d953114e7c6559531005bf7459531145bc7459531005ef725953113dec7259531005fb7059531005f8705953114cff75595310067f7559531004ff7459531006bf7459531004bf7459531014fe7459531004fd7459531014fc7459531006bc7459531014bc745953114e7f54595310067d545953115cff7359531006df735953128e7e535953128e7c5359531004ff7259531006ef7259531004ef725953100cfe7259531004fd725953100cfc7259531006ec725953100cec725953114e7f525
  | 15 => 0xd4258331056fb7058331006fb4058331006f84058331056fb3058331056f83058331006fa2058331006f9205833115cfd75d963102cff74d9631014fe74d963102ebe74d9631014be74d9631004fd74d963102ebd74d9631004bd74d963102cfc74d963102edd73d963102cff72d963100cfe72d9631004fd72d963102cfc72d9631006bf42d9631006bd42d963102ef671d9631024fe70d9631004fd70d96310047d769963102e7f64996310067e649963102f3e64996310063e64996310067d649963102e7c649963102e7f62996310067e62996310067d629963102e7c62996310073f42996310073d429963102e7e619963132777319963102f74319963102f76219963100775219963102e7f609963102e7c609963101cff765963102e7c6559631006be645963102e7f7559631004ff7459631014fe7459631004fd7459631014fc745963115e7f54596310067e54596310067d545963115e7c545963115e7f5359631004ff725963100cfe7259631004fd725963100cfc725963115e7f52596310067e52596310067d525963115e7c5259631006bf4259631006bd425963102cfc715963102e7e515963102e7c5159631004ff7059631024fc705963115e7f505963115e7c505963102d7f765963115e7f765963101c7f765963102e7f64596310067e645963102f3e64596310063e64596310067d645963102e7c645963102e7f62596310067e62596310067d625963102e7c62596310073f42596310073d425963128f77315963102f74315963102f76215963100775215963102e7f605963102e7c60596310067f74596310067e74596310067d74596310067c74596310067f735963128e7e73596310067d735963128e7c73596310067f435963128e7e43596310067d435963128e7c43596310067f72596310067e72596310067d72596310067c72596310067f42596310063f42596310067e42596310067d42596310063d42596310067c425963128e7f32596310067e32596310067d325963128e7c325963115e7f715963102e7e715963102e7c71596310067f415963102e7e41596310067d415963102e7c415963128e7f315963102e7e315963102e7c31596310067f215963102e7e21596310067d215963102e7c21596310067f70596310067e70596310067d70596310067c70596310067f40596310067e40596310067d40596310067c405963128e7f305963128e7c30596310067f20596310067e20596310067d20596310067c205963102e7f105963102e7c105963102dbf7659231156bf7659231014bf765923102ebf6559231006be655923102f3e65592310063e6559231006bd655923102f3d65592310063d655923102ebc6559231005bf7259231005bd725923102ebf6259231006be6259231006bd625923102ebc6259231
  | 16 => 0x8d5117dec7258d51175f77158d51005fb7058d51005f87058d51056de6318d51006dd6318d5128d7f7494d513557d7494d5101d7e7394d5101f5e7394d5128e7f6394d510075f6394d510065f6394d5128f5c6394d5128d7f7294d5134d7d7294d513473f4294d513473d4294d5102d7e7194d5128f767194d5128f757194d5101e7f6194d5101f776194d510057d7094d5120e7c6094d5102d7f749455133d7d749455128d7e73945510067f639455102d7f72945513357d729455132f3f429455132f3d429455102d7e719455102f76719455102e7f619455101f7761945510057d7094551004ff74d8151014fe74d8151004fd74d8151014fc74d8151054fe73d8151004fd73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d8151006bf42d8151006bd42d8151096fa50d8151006fb40d8151006f840d8151006fa20d8151006f920d8151006fb6098151005bf7458151185bc74581511f67f6518151005de7318151005dd7318151026fa6018151006f960181510567f7559731004ff7459731014fe7459731004fd7459731014fc74597311767f54597310067e54597310067d54597311767c5459731054fc73597310567e53597310567c5359731004ff725973100cfe7259731004fd725973100cfc72597311767f52597310067e52597310067d52597311767c5259731006bf4259731006bd42597311767f5159731004ff7059731024fc70597311767f50597311767c5059731056df30597310067f74597310067e74597310067d74597310067c74597310567f73597310567e73597310567d73597310567c73597310567f43597310567e43597310567d43597310567c43597310067f72597310067e72597310067d72597310067c72597310067f42597310063f42597310067e42597310067d42597310063d42597310067c42597310567f32597310567e32597310567d32597310567c32597310067f71597310067d71597311767c71597310067f41597310067e41597310067d41597310067c41597310567f31597310567e31597310567d31597310567c31597310067f21597310067e21597310067d21597310067c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067d40597310067c40597310567f30597310565f30597310567e30597310567d30597310567c30597310067f20597310067e20597310067d20597310067c205973114cfd769473101e7e65947310067d659473101cff7654731054fc765473101e7e65547310067d6554731005df7354731055dc7354731004ff755833101cfe755833101cfc7558331004ff7458331014fe7458331004fd7458331014fc7458331004ff725833100cfe7258331004fd725833100cfc7258331006bf4258331006b
  | 17 => 0x1767c51d8553024fe70d8553004fd70d85531767f50d85531a5be7498553005bd7498553006bf6498553006bc6498553006f76198553005bf74585531a5bc7458553006bf6458553006bc6458553005ef725855319dec7258553005fb7058553005f87058553006bf6418553006bc6418553006f56118553054fd751855302cff7418553014fe7418553004fd741855302cfc741855302cff721855300cfe7218553004fd721855302cfc7218553006bf4218553006bd421855302ef6511855312ef55118553024fe7018553004fd7018553006bf64d8153006bc64d8153054fd75d8153004ff74d8153014fe74d8153004fd74d8153014fc74d8153004ff72d815300cfe72d8153004fd72d815300cfc72d8153006bf42d8153006bd42d815302cfe71d8153004fd71d81530f6fa50d8153006fa20d8153006f920d81531a5be7498153005bd7498153006bf6498153006bc649815319dee7298153005ed7298153006fb6098153005bf74581531a5bc7458153006bf6458153006bc645815320e7f6518153006bf6418153006bc6418153026fa6018153006f9601815302edf6398e5102edc6398e5102edc6358e51004ff7458e51014fe7458e51004fd7458e51014fc7458e5114ede5358e5114edd5358e51006df4358e51006dc4358e51004ff7258e5100cfe7258e51004fd7258e5100cfc7258e51006bf4258e51006bd4258e51006df3258e51006dd3258e5102cfc7158e5102ede3158e5102edc3158e51004ff7058e51024fc7058e510547f7654e510073f7454e513673c7454e513667f6454e513667d6454e5101d7f7354e5101f5f7354e510567e6354e510075e6354e510075d6354e510567c6354e5135e7f6254e5135e7d6254e5135f3f4254e5135f3d4254e510057f7154e51007777154e51007747154e5101e7e6154e5101f766154e511f57c7054e5102efb6098251026f86098251005bf7458251195bc745825102ef86058251004ff7458251006bf7458251004bf7458251014fe7458251004fd7458251014fc7458251006bc7458251014bc7458251004ff7358251054fc735825106e7f53582510067d5358251004ff725825100cfe7258251004fd725825100cfc7258251006bf4258251006bd425825102cfc715825106e7f515825106efa50582511f67c5058251006fa2058251006f9205825102efb105825102ef81058251004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d5115e7f54d8d510067d54d8d5115ede53d8d5115edd53d8d5128e7c53d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d5115e7f52d8d510067d52d8d51006bf42d8d51006bd42d8d5115e7c51d8d51024fe70d8d51004fd70d8d5115e7f50d8d51006df6398d5114df57198d51005bf7458d51185bc7458d51005ef725
  | 18 => 0x4003000000000002cff7498653014fe749865302ebe7498653014be7498653004fd749865302ebd7498653004bd749865302cfc7498653054fe739865302cfc73986530567f53986530567d539865302cff729865300cfe7298653004fd729865302cfc7298653006bf4298653006bd429865302ef6719865302e7f519865302ef6519865315ef55198653056f7319865302ef4319865302ef62198653006f52198653024fe7098653004fd709865315e7c5098653004ff7458653014fe7458653004fd7458653014fc7458653054fc7358653004ff725865300cfe7258653004fd725865300cfc7258653006bf4258653006bd4258653056f7715865314ef65158653056f73158653056f43158653006f62158653006f52158653004ff7058653024fc7058653056df3058653004ff7458253006bf7458253004bf7458253014fe7458253004fd7458253014fc7458253006bc7458253014bc7458253054fc73582530567f53582530567d5358253004ff725825300cfe7258253004fd725825300cfc7258253006bf4258253006bd4258253004ff715825302cfc71582530c67f5158253056fb70582530c6fa505825320e7c5058253056fb3058253056f83058253006fa2058253006f920582531a5be76d91531a6be76d9153014be76d915336f3f75d91531a73c75d91533779f53d915336f3e53d915336f3c53d91533779c53d9153005bf72d9153005bd72d9153006bf62d9153006be62d9153006bd62d9153006bc62d91533773f52d91530073d52d91533773c51d91533773f50d915336ebf75d91531a6be75d91531a6bd75d91531a6bc75d9153376bf73d915336ebe73d91531a6bd73d915336ebc73d9153376bf53d915336ebe53d91531a6bd53d915336ebc53d9153006bf72d9153004bf72d9153006be72d9153006bd72d9153004bd72d9153006bc72d9153376bf52d9153376be52d9153376bd52d9153376bc52d915336ebf32d9153006be32d9153006bd32d915336ebc32d9153006bf71d9153006be71d9153006bd71d9153006bc71d9153376bf51d9153376be51d9153376bd51d9153376bc51d915336ebf31d915336ebc31d9153006bf21d9153006be21d9153006bd21d9153006bc21d9153006bf70d9153006be70d9153006bd70d9153006bc70d9153376bf50d9153376be50d9153376bd50d9153376bc50d915336ebf30d915336ebc30d9153006bf20d9153006be20d9153006bd20d9153006bc20d9153006bf64d8553006bc64d8553054fd75d8553004ff74d8553014fe74d8553004fd74d8553014fc74d85531767f54d85530067d54d85533267e53d85533267c53d8553004ff72d855300cfe72d8553004fd72d855300cfc72d85531767f52d85530067d52d8553006bf42d8553006bd42d8553176f651d8553
  | 19 => 0x180040340010008010008000001000400a000000002800200100200040280030030010022001000800001c0000008000000000002000c0020080010004008005007000c01400d0048000008020000000000200000000ac000018000001c00001a0008000014005003800800e0050048028068000000803801600100d0008012002001002c000001000008c00200901b8000002056001800c00200b000004000c010000800c01400a0060004002002000805000000e00b800802800900f801000c016000000801a00b0000004002004002004001a0070000010000001000803c022002000001402200100b000800000000400500000000008000000000000001800000b006002402600a00000000060000038008004000001000c0040040048000002007000803000402c0040000000002000806c04200100080000000000078038004003008000800600f002801c000000000807800e000001000400000d02280040000010020008002000001000400a00000200000000060000020000009004800c00000200380bc016003001808c006001006800002200200000080060040018008004000006809400200600080380000000008020002007001802000000100800000000000000110008004000000001600000800300040000000004008000002000402a0000048000002000003801000e0000030000002000002800400000000200180040110000018000003002800002c011000000000400b00f8000002001005800c0180000018000032014000800c00e0070000030000005001002400c003006001c006000000001401c008002808401c008002000003200000b000000000000080c800a0000010010002006000000000000200900040040060000004000000000000000e00000100d00040000010028000000006802400c008001800002e0010008048000006019800000600000c0000010002003800000e00000280300020030100004002002001800401e003000804006000000000040000010030000004004000800402a0000008004000008017001c000007000000401600000100280020000010004004001002811c01e011000800400000a001801400000000180100020030010024024006000003c0020030000000004006000000004800200180040080000000000004008000002000000c000000004200a003000c00a002000801400200600900f40040010008018000001001002c006001009800406e000000800000400900d000000200500300100140080008044000000003000000e001000007400000500000100020000000004004004000801400000000380080000030078000004000000000c00e009001803c02e0040230000016001000001c00000b0008004002000000801800c003000002802400e0000004010000002000
  | 20 => 0x201d977a4c71560ab40003c70f902885be12c015af291b4ad2410b238b2400000000017fa3b320b163915e14e4d5048d7ee000371866003a0000c600000000004d88d6cdc861d64798c593c9f93c7ab746fe8b0340325c7de5d80001218000a8522f92a800831d2e680011d8000489266189800060d29e13687512af80011867da38d90f8f9c74011110c525e9930000a2c00000033e255446a3dc46600000865e4244000033a6f4000000000000000024608460005b185d8000333412800000088900018c800000000007cc0006aa00000e40002d95aa93c800093000030e06aa00045d9e885e2a8f2129ef097a817593a0214e49032eb9c64cf25ee2f9a8c00b6c504be321c78694547da3a52861562242140c2239122db054cee9fd08b97095ec8d43fd030173a1b607d30d85d00028000050001000000000a001000000400200a007002800a0070030008000000005003400600000080200260040000000006001001006801602500080780020040080030010003009006800c007000801400001d00280200020060240000012000001800c00600100a80000080010060008046000000800000400d00000380000060148038010002000001c000001007001c00000d001802800e000003006401800100000a000203300d80000000020040008008007002800c08800f0080028004003000001c004006000002000600f003000000201a0008000014002007800000800d000801401c00200000d400800700100540200010000000002002003005403000300100000100030010000002007002000c006002000802400002b002000000000200b8000004003000800000c0050020010012005003800005e00f0068000012000001800401000f000000801c00f005800400c001010000800400400880040000050010000028000000000004800000900000120010038010002027000000001000500000000000000008008068003000000c008000001002801c004009800000000300180280140120040004002003000001400c001002805800000700a800000600e01b801801a000000005400400000b800000a005000000000e00300d000400a004004000000000c001800402401200200080000020038020000008000000000600300100180000000000050000005001002400600200b00480180020080008000018000005400a01600000000000040000004020000007003c004002011006c00c00e0150008006001000001000000a000001800400100380240020210000008022007006003c02a000000000400e00000580000000000008000008003000000001600300300000000040000008002002000003803e00500300080060030070028000006000003801600000b001c0020000008014006006002802c00a00f0098004000001003001401200
  | 21 => 0xcc97711fabb81d80000000000e1e44300007580007b808a0a6984082c5548000000000000229d2a200000000008b039a5658d198600000002fa800000000000000006db000000000025a0000b9000013e250800000000000000000000004df800049800036980017ae00054615f800065e0000000bbc30e1c21424118ad82f7a12c09ec3e1fe2acc4e831219e03f8fc2000600b2680008d232000000008b45b280018ec74a5e61dd495a18549f80d90b46b300000014b45f42930164000b0e1be198d0146ef195ade944429f00000018b60002c624d400037e000000000018e6491ec446000000013700001e73e62da140c7550bb9fbc0bc60c21fae78c407745310ec0d3425436626bcf300001f221711a02414e800003c20000002530bd29e60238000000000380000188218a1a80000a020184c32a10c2475912f847cad0c0a2080b0caee07536b0000a080a94a586b000015a04b8000000c4a00023f918c0001ec27e0ade61700000000000000000000162bed2862e0c0003962f900000000000001c1c0006b00cf95a4f3e4d21baa6944e4bac00000a0782653183800178c0000359e74d3c00038e114c000000439800000000000011341c81500002b0d38011936b849c93000005f0ef80000005e78000000bcb000000013a5bd5ed22340004082738e015948ac00000000000c7000000188097359d1f2c00080f3e794b95ce7103d2a9e904058028a1f5c81e00029d2c800004e30000a700020002ed00000003521a600015346f547729a162ac8a0000ba88d83b847992292224b43a18000eaea2828313ed3ec7955cbaddc9b60000152df81aca1e2e73284d9a898061a164baa5270bf20a956400039397dd84cafc152a34576081b2f0ad3ca7c00000d9de06208cf458800154a000336132d6be7f3306af7c0009010000570550a3e3b9aa4c86000002800000000002b19ba12789ab312942cb5291f0001aed0900004668e2811e0000000000da40460e8800000000e000000000000018d0000f0671464f9128e5e0005f72e1400000012e00000000001ed8000f5000005280000000000a98000f3c000342165c0000001912c247b200007b84247bec49077800055647f0001d04f7ac4b1fba2a51aa00054f800019000000011b80000004070444a0412d4c180013a20000002dd804c1cb2438130bd45e85068050e1095d04d00010c281a09724f86bc89c4d7250166e5672749bb01381bc557a470a0a9645921528c389094b587f47504770408a58b74a8a5c0170555094936f86fc0002423ce00241fa1a300002dc00000000005bca0e7a317e8000e7e0004a686642b2ac63db80004b685143fa41c81c5af000226910a0001ce299153c2b300005258cca9003427757e4c16116aae98d66b73ee98553c496c0a9000081600000001d000030a41
  | 22 => 0x5b4c9400036803b9620aa33c99a394468472a1118d36c7cd13308955886a45b08f149d00001832bc579027053f27651920000000ff83d40005530db150644031d126895c65651e284d5a01c54988aecf3400035700003eab990f32a084ca7690000000ae200030c000003c4dd00016ad32e0000002124f188a238080000006b94c202a945caf02be135590abd161d01c4000ca235780000ccbc92e2a3fcaa4c31572322099438c000000000078500001343440004a0a9b45888c13d49bd8000000249992400000051e845800006a00000016904a603f869cb807bb33998983b40633fe005cd6c87430f10e9436a5c03681b96cc1ce25c179ca2004b5059decbc457902080000007ca00008603ba000000018400000044a800027064800016f896632d56612301940000f605b00000002408e252c21704a7800002a0004ab2ae51f053351388809124f14e51615150a712e386c91ea3e029517642e41d01db800000000018000000009911de1a319269190fa073d8e29682d0850c0c07161d7830800000030d98295d6682349313c0000000000668000c650ef8db80f634900000016bcbc047300007dc0c500014ec8eaca30a41b9c14269d00000003dc0000672378e9e7322d4039c5ce0005f187ac2f0bc21cfafcc00000009005e55f200035180017120003c119c05a66eb00030d174800000003890dc00000000000000003c800002262a6000012000091e5c98a5c0009ce1548bc0214acd0002364000000308153c0660005a231f44f8a022bd1f78bac9ee0fb915000042128b0000fa830300002d01cc9604cd06bc93a811485800011c0003780200000bb20002ba5656b4a39a92012a800050b06dc00030b18d872899000018400000005b63fe8a156464a51aa1019886bb12e32d045406a020391f0c46a1a0b30fa0b924c358c04c0b9464c2b680a58ea78e0012131118000362000146c23e00000000003982aeb0a86ae92600002787d490e39e30ccdc0000000232840a035354000129c332033a0b42a800000000000003cd2389ff80000001898000ab0a3b1c1800000000000000000000251df92ac4343e232918bcf4800029aa08d05e0000000500a8000000026a54bebc143e80017e80005c89f253be51a0000e6c9e8a5327e05ec764c04641881c00c000473a0d0ed6b175969f18e40aea09111e12e2630471195cda265f4958944ec422f03e22e85e833b1bb84940002b8280087148806f2110d9c0000855b5840594e44238d000017e21b0002374000000000152d0e200032585a8000ac00001c0d622000569a02d74e5603db2a190ee3c90001ca13a800000000000002cc000000120a54d4e18000e901036482bfca306e523b00011b000032800000008df000243ce7ca964d6a55cc26995604a768bec66a31a2ebd86e6da00002e50
  | 23 => 0x74c70d10f0ac036668d1b8a9b0d7e85b2ab0e50c0800033da0710507245ba28e47d263e0000ca96b80000001d610d85480002adc9be5250cdacc4e8c91345222e53e88e55f3210934c2a30c419fc000abf0002c50fca8f437c211803e0001d8ad58000afa609259d8460e119300013fc4f007f89dcab47e400011d16a285e360aa7400028f267abf40005ed548ae684ec7e861da9c18d44d950bb0a164c4ec39613cd33e0000002a558f41b84e09f20c5a706241133493ca7300921012f03d0290af144d60005409d4ca5a7ff3f38000fd457d00026d40000003e12901140000000000178850852a211176e2596299398fb27bf32d21952e877131c85a0e222400000e5c2883d702003e11fa007208870c2b0104099008498053d4c800009ea5156018facaeaa0f08e0cd94f850d1d29330eec14a4c9174454e1b964104185920c13bcad0d67290a23dab9835c730519829d47e0000001bec00000000000005b40000b00000e685623589e48d0c348001a4a80000000e4800190c0003f1293516e845000134110cb5040c2d4c3042691ca97d45ccbb457100005082cd0000000d849040000c70f543412c30648200000000000172a00045292112c438e16f129d86ab0604b00014dc00032da6dc000bd615fa870cc80000001174f5a0005da800000085701d8a1cc1c97e000000000007a1360000300c1300000000000000000234384000121800169c1fc5c40a3000034744eb0b0000abc01624b44bc9474d0800088e6693e208b8e3e1900000b940006ee0002fe000038b2ad9750ba60921601f58cfaa5910606b400056560813dc5e60000000e8c0004bb0000000d30a9814da5a848a2214c3a4414749eb11c0a78c767671190b20e4a59933b229906a0275cb1a882fe6ea63f8a18bf69cf12204a438c67522a838091c7e93638e3c33c6550000000ee01e51e000006cc9f55e380018c400048ea9ec00000042c15ec1da0002e7933937c1b50000da491a80c3278c558beaa417c884c9bc2313cb8d00eca022187ab518f06e64f60f9c3fc3bd19a9c25372441262a4a45ba00062c000000000005b28e04f00002ca1bb4a24b3500018095588c203c99d020e36b2dc32341b200041fb1380001350001319670aec62d2d2c0685bc545800000000009f9c880000000001bcc7f40dc4eaa650aaa87249080000009c74171d74000000486295506c9481628ca167e00019a27716509f335a0000e8a4d30000cc4000bfa0000000000000000000000000000023900000f6638000000048b00032658c62244c6000000034d0000000b0867a2990000be000045580000000004f900005d60004048f450d697d1c900000ba3143028cf40000d252ea9f400000009e800000039e0002c34c8239959b0e9cc66a0c429abcd1202261d6b01c000bf90001f6c6e80000
  | 24 => 0xf0172c2c450a06a966c9625463559170e5c3ba4b30b581122d220287500348b8291a2118569342a62bdd5841ef0000b44596c7b000155d000c5d05c17409588915f432040007fb56385158da0a3395800000030c4c5311130458a63a302d44214b0f89d1c65eaa052287044081e4630143c0f000c1440b28fe8892356a9404c48eb2a9878c6962ed1ae09ec8de2585f4af8060226f247963c5d20d40fc204d68444b0df241868a856298ade57aa1f012492657e0a12171b2987a61893e90984a1c0f43859b6174c89b5ca1da8478bb300000011643d526b221ce7681e26ba5186889a400000017d80003159cc567c8a125d0b8882eb8f00000003f43de613a6352c665c41d000010cb825ae8000eee854191800169a0000002cf12b60003af07e5642afb3d816985b03ae4670634542ab0000002d02c8ad0001c993c67725baaeecd642672f000000000003a61e00dd27b400003351c07600000000858aa703eae940400005e719c900a10c1ac80016b20000001d980000000001e6c2782f843c2cf4f8625009b092006246d0002c207a87ec1a184a084e8830002b047cc47928bab1570200000000018e681017080009a800012e96c0a88bfe63c9670d1227a58200001be5131e100007ba2081d0ab200000003999e2000008a535ad1c00011847880008f45733e81fb57ba9235102af975a9282f303c00004c20001488000b521520124502c170d809c5204b34228a138132a3516322657f87a049c8a4d8d2000493a710d9400000000000000005b012f80007ba59908280000000001ae001a0000002e48000bab2b0a96d7a66c544f00004125aa5189c8d1b642b3c21c304fa976276a09d07887619f0c6476c92c5b7059d40a6a70270014bbe3e10eb9ce82e693316da7581983512f1a38c0841415c69ec8eb874434b00006425ff5001c78d8c00002200dd11e44c0000000bcaafe1238fe03ecb6d445ac050023d264daaad83a1a904f9f700000100000001312a5636e1c1000021f0c58000000000000000000074b0ec800000000000020c012200021a80000008bf00887600000005bda2d400000000013fc00000017f26e987200055aa68d1ee0005fab2540946f11b98f20c6e3613210650aa8721415afbc3085b11e508a06f6000430000000000004c00000003c43e982900000000000a348188750000000a8ab9c3c4800000000027700000000bc0002b58b5c5a3053268095e0005fd80005de0001b6ad3000000032c00000000000dd800137aa242c59df93966fd5e81868e309b35289be8b3045234797211f8b8a2ba0de0356ad15cda0088fc86853fa0f80003fb4dda3152b818300000000000004b49e4400092e505148042a000000280c0003f200003e4e3abff0502250888b074c2afad8c8bb617d88f400015b00009d400026400009cc
  | 25 => 0x5810337333243484003863600012b42bd62a84a80e035f1d602e81a24240000000000adb0b88bb800000000015640b037000531212de00041ba14987e0d33673070bf8c183a82820d3234f5ec1858a50000000125588c9581078980000b8b1372dc8a708bd0caaaec8c2a460be0d8c10e0562398d60ce23820dd09b45065bf582936824809335f18e115c387000188400031e04d8584000bb80000d080001653b60694000000000230000000000000005c04370d4127c41ac2e06f22390521a663f000139a8790002b807e60003160000000a8700008e58842cf000008c0004a25f8abe000044924e02c11ec0dd0000fd90245b22959d84000c8b10a1fc828433036588d17b811523290682ae98150a90a10fc00002a9e9d614000000000185a000127906400000010895a8000b7d28e94793900004f38000e7042a0570eed3da23b3288840f7c53007507fc58e7a15a4acb8010c1164e1ce487832c11d09387b402f300000043ac56508119c0d29cc42197e10d40000002da4b200000002491852660327000000081f09880014bc45a5d516b0a6e3e555899e071a33f20a889cb986f23d9aefc9281695b897e42c66655981e195ea201427871c9b0b005c6182ca7254e5552ea43f66813ad8b70000c8905698d80008071001f15634a9246e0000fee1b108d0e801ae8ef5008448ec600000011a400000056d10d0870c4536a181c0c41de4378dc80004563b686040003ec000291c1c68881bb180c8d40bd48b87b552e5830eaad5177807753a1004000b641ab1a8493600035494d0d0a4a020e000073ac8058e22d8fe21e23d303cc9c803d50a065c1968f907d900124400056b8001616a8e06d128ce2e40a00029a4000c5100020c80000002bc000000000050c00000e600049280015d00004d809483a49723ca18258b23f953c8194df82c21d488b140800025431512dc0002daaf0d64a11043380000000e81fe9eb08e06b514c80008cc0004659c08d2e000303000000058700000000004a917b0000eac0545791464000b2f00000000008d30001ed40000001ff80015aa8bc529000000044609304392645490a8825071000017a80010760003f000011c233800031798aec912b60001316b5a0000000b220001e30000dfc30d00011f4a5e7f60002e600000000c316057c4bae029003cb3e5bb4e993840c80e900018202c800000020cc0005b464e85346fa000000299800091600021c000077d0000e0453a000331224c9ec000016800000015f5ecaf503540ac34999b440610d000000132c0005b8227cfbe8ea2f6164d02a6195309d49908a5800b217d94a74d37c9df185e0b3382aca92109c6550989c530019637814440c9a21e62b3d2f22ff5d197c4b6e5a54a130903d2b2215a0c5c75611d12b3050a521a41da218943eab83ec0b5c5122ce
  | 26 => 0x403191cf020c60be87a149c459277868146434e55682ac2d60003cb120c0000004f43015538000000000000043b63911800008140c380000004b75071f1c3389501bca2585a800051594fc000263000200c0000004b80c14cfc1084f08ca428ca495bc0fc4cb2b1f1269a281ca69f2a38000b663f454a246cf5e51b5f386591467e35210000000b8430a32300000002b2188821e000000000046c3ce530000065c1750000f585740822340d80368a9b5ab8dbc00066b594800096c0004bfa7bd772ba05b5064c4fc6e12c10bdc42eb1b515000056400027c16b400000043696741b06ba00000000007e60002074cce000455220800000021c80000003a4272aa240000003c3954441c7d52d00000000b0f361800000037a01700000000d0201000179a2800002b8437a07200029a8c54ba265200f877295900000006b42940000f8c0002c100000016189f1151168883654353b9d2400005a5ac000162c4bc3b7800000000061089fc0006de3e02d1545ec614d61fe4110ca84f508640000f50e00000c7a7d15ef21355da0000000000ae4988114ab393bcb870002c795ca30927d00000b883108280011aec0f1da90506223392750730562be4000232023600052080000000000000000e7a000000000079e8f234804d087aab461923b45e475f00018f08265410859e34ba48e801d19105149a812b95ac0005fa4fd800060449755101b13b05a464b27c13f822b12525d4e6e1dc0792358424af400008a82dcc981939a0ce1451c095a674000c061f6ae40efeba1248a9d57c28553f715984961c45c31345940b1d3faa128aec0900ba00000000b200012e49c00000002d0000032000029bc000536606863d71ca6520918a560499b41124557a400021791414ae00046200000002aa09d0000e1c000000275cc5c00025a80000000005890000e2ac5c000000145200048d0e40b12000000000112e41800016e418800000981f8adc0000000d9400000006da6f00003a228f80010f800000005e856a0000180000f724b20002b248bc52c34a800063e3aa3488000ed0936275a87470a000148193553213749031a02666a6202307884c98f23215fd44c49008f20e055ca4a0002c6541200006485545f8a4317d1e286bac25262183c2720003d71bfc0000b545f31dc000b670002af546e00000000000000000789d388060003f597f55c643214700000003f51492f6c5220004fbb134cdca4b0000af192865d31faccc64800052790b881a33a32329212747ab2582664000ba855b0d4cef400035628948ae42956e2034e6c6544bd84ed3d200000030300009530191a958f800000000011e05dc14a9b5536403c15badf03905eb16823e93a40451e58b554ecade4409a206c4b4611b944587a0000001620b2c00020f1a50f820001350c103b69c92b8102
  | 27 => 0x41cb1b844698e134015cab834a6338e192bc5c34f280010c6c1928180001d60002ed800029e62807e00018780cf30f80000004c100027080000001c9a5b44aa02451a000181c00049d800085a000581a1040009a75df00000000005ada45180400000013f44f24c956c9b6551031821980000000004e29cb40000000000575836b9f56f99141504365962228e52000000113c000000000020d0ba0004c0163507a4f900019bd2f4c521299e2c40410230098d56d89522712bbcd9055e0c893f96e60af00024dc0000000979d0800069b60fa6713c80005169c480000005b7a200dba87b4eda8b00003f052600000000003898ad92ca5dd4ff80fcb2a00000000000001a10000000000000540281d294233123000057c7f80af000041648510b02114ce0000002c4c000bba49c1a7118e0002ff0da90080005f280000001213f827800000004349bdc62c41d5b100009248b300027e8aa005300000000001cd000053000000000000017ec0004af800000000000012580007994dc0a088d600015c8abc94844e34391c80006bc5bfa84400041f00e14f0dc4a190002098e5400040ca510b3459e3b71af4d92364600017c000095000000000000049e971028e0002228000ea899e59da190d80a8d3121d9188e6682310da03a66434801984116325000169c1762ec43d12fcd9e68b557298ca4875a000000184400
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xad8805d563040014bd0a3a2c608002976147458c100070faa4a8b182000a9e849c9630400153b09392c608002b5e057258c1002d6a40ae4b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b182005ad6811c963040015ab02392c608012b6a007258c100056cc00e4b182000a9e84949630400153b09292c608012b6a025258c100056cc04a4b182000a9e84149630400153b08292c6081caa76124258c1000747c1284b182072e8f2050963040e5d1a40a12c6081c6a7a104258c1002f2b28ea2b182000a9e84c85630400153b0990ac60800317d4d7694c100243fc3acb2982000a5f835965304001c3ea6b24a60800e97a156394c100243e42eeca9820028bc84dd9530400117f08bb2a60800a2f2117654c100247c402eca98200487c875955304001878e8b2aa6080022f61b7454c103761f32ee8a982000c3d65dd153040db93cc7ba2a6080032b98b7454c100045f43ac8a9820008bc8759153040091b90eb1aa60800327dd16354c100064e3a2c6a982000c7965dc153040019b2c7b82a608002aba13755881000556c26eab102004aea80dd5620400d5d301baac408002aba10755881000556c20eab102072aad879d162040e3d54213a2c4081cebae01745881002574402e8b102000caf875d16204001d5700ba2c4081cbaa201745881039657b82e8b102072cad705d162040e5d5420ba2c4081c6aba10745881000717aa4a8b102000aeb8055162040095d100aa2c408002aba13735881000556c26e6b102070ae7815cd620400b5c902b9ac4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac408016b9a04735881003572c08e6b102004aea801cd620400d5d30039ac40800393d4e535881000557c22a6b102000aac8454d62040015d700a9ac408012ba20153588100257540486b102000ae98090d62040014dd0a21ac4080029b614435881002f3328ea2b10200387e855db31040091bb06bb662080ba1fe1975cc4100061f322eb988200ac5e635d731040018dcc4bae62080221fe1d65cc4100043ec3acb9882000c3e75593310400187aeab266208003179d563cc4100062ebaac79882000c6e7558b31040018daeab1662080123720f764c41002f4a18ac89882005ad48158d310400bd8862b1262080032e1d376440100063dc2eec8802000c7885dd9100400197709bb220080032e21376440100065da16ec8802000cb942dd910040018f6edbaa20080031edd875440100069c3a0ea8802000cbb76dd11004001cd6eab1220080039a1d5624401000755422c48802000ea9845891004001d56e8b122008003aa1d1624401037f71c0ac48802005ee08158910040099d6e2b122008013b8dc5624401002f7128ac48802005ee2315891004001dc2c4a8a2008003b85893144010
  | 1 => 0xaebb2462880031e197704c5100063bb2ee2a822000c77651c550440159a8c6b8e60880021fe15764c11001c3e42aec98220008bf845d9304400517908bb260880023be09764c11000c76412ec982200087e86dd53044001878c9baa60881075c043754c11026c3f43eca982204f87c87d953044001878e9b2a60880022fa1b744c1100061fb2ee89822000c3c65dd130440ef17d0fb2260881322f21f644c1100061fbaec89822000c3c75d9130440091ed0db8a60880fb1e9db65c411001e3d3b0cb8822000e38641971044079974edb2620880123e20174594100243f43ca8b282000c3f7495165040090f90eaa2ca080121fa1e52594100051f424a4b282000a3d8494965040094f501292ca080121f21d52594100061fba4e8b282000a7b805d165040094f100ba2ca0800317dce73594100051fc22e6b282000a3c845cd65040094f100b9aca080129ea0243594100053cc0486b28200087e8710d65040010fb0e21aca080028fa1272594100051ec24e4b282004a7a809c965040014f301392ca080028fa1072594100051ec20e4b282072a3d849096504001c5f04a12ca081cb8bc8142594103971690284b282071a3e84109650400147d09192ca080028f61232594100043f43864b28200087d870c9650400147d08192ca080028f610325941002d3b40864b282000a75810c965040094f500192ca080029e60032594100051f42642b282000a3d84c85650400187eeb3aac8081daaee0175590100255c402eab202004aba809cd64040eb5730139ac8080028fa1473590100051ec28e6b2020728bd879c964040e957700b92c808012ae201725901000657c12e4b202000cbb805c964040e597100b92c8081c62fa1c72590100045f43ca4b2020008bd87949640400957501292c808002ae60252590100045f438a4b2020008bd87149640400117d0f192c8080022f61e32590100045f43864b2020008bd870c9640400147d0a192c8080028f614325901002d5b40864b202000ab5810c9640400957500192c808002ae600325901002f1b28ea2b2020078be87c85640400117b0f90ac80800387d525498c100054f424a53182000a9d8494a63040095b501294c608002b66025298c100054f420a53182000a9d8414a63040e553b09214c608003a3e094298c1039747902853182072e8d2050a63040e353d08214c608002a7a132198c100054ec264331820048de87d4d63040018beeba9ac60801237a1f4358c100246e43a86b182000a5e8510d63040014bb0a21ac6080163d2057258c100246f43c64b182000a9e848c9630400153b09192c6080123721d3258c100052f42864b182000a5d850c9630400153d08192c608002a76103258c1002d6b40864b182004ada800c963040018beeb3aac608002a7e117558c100054e422eab182004
  | 2 => 0x421d91100054f41843b222000a9d8308764440795750010ec888002ae60021d91101c55b40ee1b2220008be87d43644400117b0fa86c8880022fa1f20d91100045ec3e41b222000a3e85c83644400147b0b906c8880032bdcb20d911000657b9241b22203cea82048364440015ab02196c688002b660032d8d1000754a1241b1a2000c3e74d96634400187ce832cc6880030fd957498d100061e32ae931a2000c3e75d92634400187aebb24c6880030f9d46498d100061eba8c931a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac68800a2fa1b7458d100061fb2ee8b1a2000c3c65dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440018decbb92c6880031b1977258d1000657b26e4b1a2000cac64dc9634400187eebba2c6880030f1d77458d100045ec16e8b1a200087f855d163440070f90aba2c6880023be097458d1000c76412e8b1a2000c3f751d16344001878ea3a2c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880032be137258d1000656426e4b1a200087f855c963440070f90ab92c6880022fe117258d100145e422e4b1a20008df835c963440011ef02b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100045f43e84b1a20028bc87d09634400187eeba12c6881ef0f1d74258d1000657b9684b1a2001cac72d09634400117d0ea12c6880022f21d4258d100061fbaa84b1a207ac3c75509634400195ee4a12c6880072b1c94258d1000672396e2b1a2000c7875dc163440f38f0eb102c6880073a1ca2058d1000c7c43a40b1a2078c787548163440039d0e4902c688003aa5092058d100046fc3ac631a2000acc8258c634400117f08bb4a68800a2f2117694d100052ec1ecb29a2000e1f53d92534400517d09bb2a6880022f6137654d100145f424eca9a20008bd849d9534400117f08bb2a68800a2f2117654d1000477c12eca9a20018ec825d953440011f700bb2a68800a2f2107654d100543f43ecaa9a2000c3c74d95534400117d0dba2a6880030fd977454d103761e32ee8a9a20008be87d9153440011790fb22a6880fb1e1c365545100065c326e0a8a203d87c865d73144001878c8bae62880fa1fe1f65cc5100043ec3ecb98a2000c3e75d93314400187aebb2662880032e19170cc51001c3e42ced18a20028bc849da31440570f90cbac62880030f191758c51002eb8082eb18a200087f87d96314401b0fb0fb2c62880030f9d3658c5101545e432e918a2000c3f655d23144001878caba462880022fe1f648c5100645ec3ec918a2000c3e75d92314400187
  | 3 => 0x5b2a2000e2f8250b654400147d09196ca880028f61232d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100053b40865b2a2000a75810cb654407d4f500196ca880029e60032d95100043f43883b2a200d87d87107654400147d0990eca880028f61321d95100043f43843b2a200d87d87087654400147d0810eca880028f61021d95100052f41843b2a2000a5d83087654407d4f50010eca880029e60021d95100051fc22e1b2a2000a3c845c365440010fd0fa06ca880021f61f40d95100043f43e41b2a200087d87c83654400147d09906ca880028f61320d951000716a1641b2a2000e2d42483654407dcd040906ca880030f19774595100145f43ee8b2a2000c3f75dd1654400117b05ba2ca880021fe1574595100047dc02e8b2a20008be871d1654400187eea3a2ca880021fe1572595100045fc22e4b2a20028bc845c965440011bf06b92ca8802a3720d72595100045f43e84b2a20028bc87d09654400117d0ea12ca880022f21d42595100065c3a6e0b2a200087d8799065440010ff0eb20ca880029ee0164195100051ec10c832a200087d87988654400147d09310ca880028f61262195100053cc04c432a200087f87588654400147f08b10ca880028f21162195100052fc1ac432a2000a5c83588654400147d08310ca880028f61062195101ed3d400c432a2000a3e86d0865440014790da10ca880030f9db42195100051e4328432a2000c3e765086544001c70c9100ca880029e21920195100071c3224032a2000e6b624806544001e5284900ca88002dc20520195100061f3b6cbb2220008bd87997644400147d0b32ec8880022fe1d65d91100051f430cbb222000c3e76197644400117d0db96c8880030fd9772d91100061e32ee5b222000c3f655cb6444001878cab96c88800a2fe1f62d911000656b96c5b2220008bd8798b644400147d0b316c8880028f61662d91100045fc3ac5b222000a3f8558b64440014790ab16c888002a7e0d62d91100054e41ac5b22200c8bd8718b644400195ae4316c8880038e19620d91100071c32a41b222000dab724836444001d50c4906c888002ec20520d91100061eba8ebb222000a3e859cf644400147b0b39ec8880022f61e72d911000657c12e5b2220008be871cb644407957500396c888002ae60072d91100045f43ca5b2220008bd8794b644407957501296c888002ae60252d91100045f438a5b2220008bd8714b644400117d0f196c8880022f61e32d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100055b40865b222000ab5810cb644407957500196c888002ae60032d91100045f438a3b22200c8bd87147644407917d0f90ec8880022f61f21d91100045f43843b22200c8bd87087644400147d0a10ec8880028f61
  | 4 => 0x50c0090fd0f292ca180028fa1252594300051ec24a4b286004a7a80949650c0090f90ea92ca180030fdd274594300051f424e4b286000a3d849c9650c0094f501392ca180029e60272594300051f420e4b286000a3d841c9650c0e3c3e61a12ca181c7874c342594303951ec2484b286000e2f82509650c0e5c3e60a12ca181cb874c142594303971790284b286072e2d20509650c0e347d08212ca180028fe1171594300051e422e2b286004a78805c5650c00147d0838aca180028f61071594300043f43882b28600087d87105650c00147d0990aca180028f61321594300052fc1a42b28600aa5c83485650c0010fd0e10aca180021f61c21594300051f42042b286000a3d84085650c0154bd0610aca180029760c21594300253d40042b286000a7980085650c0151b906b92c2180123d21d41584300247a43a42b08600487c85dd9510c00117f08bb2a21800a2f21176544300063cb2ee0a88600587c8755165c400b0f90ea92cb880022fe0974d8f100145fc3e85b1e20008bd87d0b63c40f787ceba16c7880030f5d742d8f100045fc3a85b1e20008bd8750b63c40f587ceaa16c7880030f5d542d8f1000657b9284b1e2001cac7250963c400b1b90e992c7880161fe1d6594f100052fc1acb29e20008bf845d953c400517908bb2a7880023be097654f1000c76412eca9e200a87e87d9553c400b9a8e2b1a618800e1fa1f7558e100145f43ee8b1c2000c3f75dd16384001878ebba2c7080022f60b7458e100043fc2ae8b1c200387c855d1638409717d0e3a2c7080030fdd47458e100061e3a8e8b1c200087f855c963840070f90ab92c7080022fe117258e100145e422e4b1c20008be87d0963840051790fa12c7080030fdd74258e103de1e3ae84b1c20008be8750963840011790ea12c7080030fdd54258e103d61e3aa84b1c2078c787548163840039d0e4902c708003aa5092058e100045fc22ed29c20028bc845da53840074b90ab1ca7081061fe157654e100045fc22eca9c20028bc845d953840090f90eb2aa7080123721d6354e100562f31aeb98c2000c5d7558f318400187ae92a6ca8800a1fe1d54d95100051f424a5b2a2000a3d8494b65440030ff0ea96ca880028f60864d95100051f424c5b2a2000a3d8498b654400147f08b16ca880028f21162d95100052fc1ac5b2a2000a5c8358b654400147d08316ca880028f61062d95100051f43685b2a2000a3c86d0b65440f787ceda16ca880028f21942d95103d61f3b285b2a2078c7a764836544001cd0c4906ca88003ca50920d9510005b840a41b2a2000c3d741d3654400147d09b9eca880028f61373d95100062eb98e7b2a200087e8710f65440010fb0e21eca880028fa1272d95100051ec24e5b2a2000a3e841cb654400147b08396ca880fa9ea0072d95100053cc00e
  | 5 => 0x812eaea0371d91302655cc06e3b226000a3e859c7644c00147b0b38ec898132a7a0c71d913025d4ec18e3b2260008be87147644c00117b0e28ec8980022fa1f21d91300045ec3e43b2260008be87087644c00117b0e10ec8980028fa1421d91300051ec2843b22604ca9e83087644c00153b0610ec89812eaea0021d91300055cc0043b22604c8be87d43644c00117b0fa86c89812f8e94350d91302645f43e41b2260008bd87c83644c00147d0b906c8980028f61720d913000657b9641b226000caf72483644c0074bd0db2ca698003179db6594d300070e32ec929a6000c3c74d95534c0838f0e1b2aa6981f22fa1b7454d300061fb2ee8a9a606ec3c65dd1534c0fb17d0fb22a69812e2f21f6454d3020e2e3b6caa9a606ec9c76dd1534c097938edb22a69810756dd47054d300547cc06e9b0a6000ad583087614c0015e30010ec2980073a1c920d853000754a1241b0a6000ee321483614c00187ce9b2cc2980030f9d065985300061fb2ae930a6000c3c655d2614c00187cebb24c2980030f5d764985300061f3a8c930a6000c3d75192614c0830f90dbaac2980021fa1f65585300061e3a6cab0a6000c6c72d95614c0010fd0e32ac2980030f1d0655853000636390cab0a60028be86dd1614c0971790dba2c2980030fd9774585300061e32ee8b0a60008be87d91614c00187eebb22c2980030f1d7645853000656396c8b0a60008be87191614c00187eea322c2980030f1d4645853000656390c8b0a6000c6f65dc9614c0018d8cbb92c2980032bd93725853000656326e4b0a607cc9d73190614c0011ef0eb08c298002b9209611853000e573928430a6000cad72508614c00117f08bb4a29800a2f211769453027e2f39ecb28a6000c5f655ce514c001938c8b9ca29802a57e1d539453001d2e432a728a60028be84dd9514c00117b09bb2a29800e1f21476545300062e3b4a6a8a6000d1c645d7314c001a3e84bae62980034750975cc5300562fb02eb98a600ad5b605d7314c001ab440bae62980035648175cc530004afc3ecb98a600095d87197314c001c38c832e6298003475d764cc5302743e432eb18a6000c3c645d6314c0010fb0fb2c62980030f9d3658c5303e45e432e918a6000c3f655d2314c001878caba462980022f61f648c5300061f3aec918a6000c3d75d92314c0018f0cbb82629801237219754c53020e2e3b6ca98a604ec5c76195314c001c38c832a629812f271db644c5300072bb28c298a6000e5465185314c001d2ec830a6298003a5190614c5300056b438c298a6005cd687185314c00b5af0430a6298002b5608614c5300074ba10c298a6000e9542185314c09f8b8e7b2aa09800317d977354130024ae43aa6a826004a5c8654d504c0096b100a9aa0980121fa1e54594300061fba4a8b28600487c875516
  | 6 => 0x51e43285b2a607ac3e7650b654c09f4f10c906ca981e31e9d920d95300073431241b2a6000f2942483654c00187ae83a6ca98107171cd73d95300051f424e5b2a6000a3d849cb654c00147d08396ca980028f61072d953020d3d400e5b2a604fa79801cb654c001c5f04a16ca980028fa1232d95300051ec2465b2a6000a3e849c7654c00147b0938eca981069760c71d95300043f43883b2a600087d87107654c00147d0990eca980028f61321d95300043f43843b2a600087d87087654c00147d0810eca980028f61021d953027d2f41843b2a6000a5d83087654c0834f50010eca980029e60021d95300051fc22e1b2a6000a3c845c3654c0838f0e0b86ca9813e1fa1f40d95300043ec3e81b2a604f87e87c83654c0010fb0f906ca980028fa1320d95300051ec2641b2a6000e2d42c83654c001c5a84906ca980030f19774595300145f43ee8b2a6000c3f75dd1654c00117b05ba2ca980021fe1574595300045f438e8b2a6000c3f751d1654c0010ff0ab92ca980022fe1172595300145e422e4b2a60008f7815c9654c00b1e902b92ca980022fa1f42595300145e43e84b2a60008be87509654c0011790ea12ca980021f61e64195300043fc3ac832a6000e1e73190654c001c3ae6320ca980028f60864195300043ec3cc432a6000a3e84988654c00147b09310ca980029e60262195300043fc3ac432a6000a3f84588654c00147908b10ca980029de0562195300053a40ac432a6000a3e84188654c00147b08310ca9813a9ea0062195300051f4368432a6000a3c86d08654c00187ceda10ca980028f21942195300061f3b28432a6000e3864880654c09b4f10c900ca980038e191201953000735b124032a6000e6862480654c001e5284900ca980030f9db65d91300045ec3ccbb226000a3e85997644c00117f0eb2ec8980028fa1865d91300061f3b0cbb226000e1d83197644c00117d0db96c8980030fd9772d91300061e32ee5b226000c3f655cb644c001878cab96c89800a2fe1f62d913000656b96c5b2260008bd8798b644c00147d0b316c8980028f61662d91300045fc3ac5b226000a3f8558b644c0014790ab16c898002ade0562d91300055a40ac5b2260178bd8718b644c00195ae4316c8980038e19620d91302655c43241b226000e3865483644c001b56e4906c898003aa18920d91300061eba8ebb22604ca9e831d7644c09753b063aec89812eaea0075d91302655cc00ebb22604ce1e53d4f644c09953d07b96c89812ea760f72d91300064f41ee5b226000c9d83dcb644c00117b0f396c8980032be0972d91300045f438e5b22604baba801cb644c09957300396c8980022fa1e52d91300045ec3ca5b22604baba8094b644c00157301296c8980022fa1c52d91300045ec38a5b22604b8be878cb644c00117b0f196c89
  | 7 => 0x7885580604c40b0f90eaa2ca188161f21d52594310062f42eec9886200c5d85dd9310c40193e85bb262188032750b764c43101c3f43eeab0062028be87dd1600c40187eebba2c0188030f1d774580310045ec16e8b00620087f855d1600c4070f90aba2c0188030fdd474580310061e3a8e8b006200aad821d1600c4010ff0ab92c01880e1f21572580310045fc22e4b0062028bc845c9600c40117d0fa12c01880a2f21f42580310061fbae84b00627bc3c75d09600c40117d0ea12c0188022f21d42580310061fbaa84b00627ac3c75509600c40395ce4a12c0188032b5c9425803102f6808262b006202cb874901600c40b1f10ea02c0189e71e1d6205803102c7c43a40b006278c7875481600c401d5284902c018816bc205205803127d2fc3ac729ca04ec5f8758e5394001c3e84b1ca728003875096394e500043ec34e329ca00093d849c653940832f70cb84a7281371ee197094e500069dc22e129ca000d38845c25394001a7684b84a7280034e5097094e500145f426e6b0ca0008bd84dcd61940010fd0f29ac32800237e0d72586500546e41ae4b0ca00087f8758e519409f8bce6b1ca3280f61fe1d61946500562f31aeb98ca000c5d7558f31940018beeab1a632800e5e215700c6500046fc3ac631aa06dc3c76dd1535407b0fd0db8aa6a80022fe1173d85500145e422e7b0aa0008f787584615400187ea6ba0c2a80022fe09741855002e1fa8ae830aa005c3d515d0615400187ca0ba0c2a80030f14174185503243fc3aa630aa000c3d7454c615400517f0fa10c2a80022f61f42185500045fc3a8430aa0008bd87508615409d0fd0db9aa2a802a1f21676cc55002c3e42ced18aa00487c865d531540092f100baa62a80022fe11760c5500145e422ec18aa0058f8865c031540150f90eaa2cb980061f21d52597300045fc12e930e60028bf87d0a61cc00117b0fa14c3981ef0f9d742987300061ebae8530e60008bf8750a61cc00117b0ea14c3981eb0f9d542987300061ebaa8530e6000caf7250961cc003958e4a12c3980063d21d215873002c3ec2eeca8e60048de83dd951cc0a38bca7bb2a39801276201754c730024ae43aa6a86600387e87dd5618c07d8be61baac3180fb174c375586300043fc2ae8b0c600387c855d1618c0091f100ba2c3180021fe15725863001c3e42ae4b0c6000c3f75d09618c0f7878eba12c3180030fdd542586303d61e3aa84b0c6078c7875481618c001d5284902c3180030f5d254d95300143fc3aa9b2a6000a3e8494b654c00147b09296ca980061fe1d52d95300051ec10c9b2a6000a3e8498b654c00147b09316ca980028fe1162d95300051e422c5b2a6000a778158b654c0014e902b16ca980028fa1062d95300051ec20c5b2a6000a3e86d0b654c0014790da16ca981ef0f9db42d95300
  | 8 => 0x82a0acb188028fa1321596310051ec2642b2c6200a3e84dc1658c40147b09b82cb1894697a0c70596310052ec18e0b2c620087e87d01658c4010fb0fa02cb188029ba08405963100536c1080b2c6205a7681101658c4014eb02202cb188021fa1f20596310043ec3e40b2c6200a3e84c81658c40147b09902cb188038b50b205963100716a1240b2c6200a3e84081658c40147b08102cb188169da0420596310053ac0840b2c6200c3e65dc9648c40187acbb92c9188022fe1972592310061f32ae4b246200c3d655c9648c45517d0f312c9188032bdca625923102d5b40cc4b2462028be87589648c40195ee4b12c9188030fdd6755923140d5bc0ae6b246263e1e53d4d648c40117b0f392c918816ada0672592314055ac0ce4b246200a9f835c9648c4c753906b92c91880327e0d72592310064e41ae4b246200caf825c9648c40117d0e392c9188022fa1e52592310045ec3ca4b246200aba80949648c40157301292c9188022fa1c52592310045ec38a4b2462008be878c9648c40117b0f192c9188178d94751592311545f43e42b2462008bd87c85648c40147d0bb82c9188028f617705923100557410e0b246200aad821c1648c401972e0382c9188022fa1f50592310045ec3ea0b246263a9e83141648c40153b06282c9188022fa1f20592310045ec3e40b246200a3e85c81648c40147b0b902c9188032b5cb205923100656b9240b2462008be87081648c40117b0e102c9188030f1d16554e310045ec36e8a9c626ec3e65dd1538c40187acbba2a7189ba2fa1d6454e313ec5e43ac8a9c6200c7565dc5538c40b1f10e902c118803aa509205823102c6ec1ee9b2a62008bf845c3654c40517908b86ca988031e19470595310145f43ee8b2a62008bd82dd1654c4011df04ba2ca988063b20974595310047dc02e8b2a62048f8805d1654c40117d0e3a2ca9880a1f21d54595313fe3c382a8b2a62018ee87dc9654c40195ee9b92ca988032b1d3725953100657c26e4b2a6200cac84dc9654c40117f08b92ca9880a2f21172595310047dc02e4b2a62048f8805c9654c4011dd0e392ca988032bdd07259531006563a0e4b2a620187c87549654c4038d8e4a92ca989fb1e1c152595310045f43e84b2a62028bc87d09654c40195ee5a12ca988072b1cb425953138e5c38684b2a62008be87509654c4011790ea12ca988032bdc9425953100e5639284b2a6272cb870509654c401976e9b82ca988032e1d3705953100675b96e0b2a6200ce872dc1654c40197685b82ca988032e50b70595310063dba8e0b2a6200cbb741c1654c401970e8382ca988033adc8705953100674390e0b2a620a87f87596514c47d4f100b2ca29880317d97735453102eca18ae918a6200caf7250b604c403958e4a16c098802b660c50d81310047dc3ac03026200a
  | 9 => 0x601815102c6e41ae8b2e620a87e8795165cc40187ee92a2cb9882a1f21d54597310543f43ca4b2e6200a3e8494965cc40147b09292cb988029ea0252597310053cc04a4b2e620187c8754965cc40517d09b82cb988022f61370597310061fba4e8b2e6200a5f835d165cc4154b906ba2cb988028fa1272597310051ec24e4b2e620aa5e839c965cc4014bb07392cb988029ea0272597310053cc04e4b2e6200a3e841c965cc40147b08392cb98a0b87cc3425973141d1ec2484b2e6200e2f8250965cc507c3e60a12cb98a0a8fa1042597310051fc22e2b2e6200a3c845c565cc4014df04b8acb988029b20971597310053dc02e2b2e6200a78805c565cc45d0fd0e20acb988021f61c41597310051f42642b2e6200a3d84c8565cc4014bf0690acb9882a9720d21597311743f43842b2e620087d8708565cc40147d0810acb988028f61021597310552f41842b2e6200a5d8308565cc4014f50010acb988029e60021597310051f426e0b2e6200a3d84dc165cc40147d09382cb988028f61270597310552f41ce0b2e6200a6e829c165cc4014db05382cb9882a97a0c70597311752ec18e0b2e620087e87d0165cc4010fb0fa02cb9882a97a0e40597310052ec1c80b2e620aa5e8310165cc4014bb06202cb988029ba08405973100536c1080b2e620087e87c8165cc4010fb0f902cb988028fa1320597310051ec2640b2e6200e2d42c8165cc4154bd07102cb988029760e205973100716a1240b2e6200a3e8408165cc40147b08102cb9882a97a0c20597310052ec1840b2e6200c5d65dcd51cc4015d304202c1988063e21d205833100e7439240b066200ea94248160cc40117f04ba6cb1880a2fe1f42d96310045ec3e85b2c62008bf8750b658c40117b0ea16cb188028f60a649963102f0f98cc932c6205e1d31992658c40147d09314cb188028f612629963102d3b40cc532c6200a3f86d0a658c40147b0da14cb188028fe19429963102c3f43ca8b2c6200c3f74951658c40b0f90eaa2cb188161fa1e52596310051f424a4b2c6200a3d84949658c4014f501292cb188029e602525963102c3e43aa4b2c62028be84dc1658c40117b09b82cb188028f60a64596310051f424c4b2c6200a3d84989658c40b4ed03312cb188179988662596310051fc3684b2c6200a3d86d09658c4f787eeda12cb188028fe1942596313d61fbb284b2c6200c3f749d1658c4a38bce7b9acb188028fe1173596310051e422e6b2c6200a6f825cd658c4014d904b9acb188029ee0173596310053c402e6b2c6200a3e849c9658c40147b09392cb188169da0672596310053ac0ce4b2c6200a7a809c9658c4014f301392cb188028fa1072596310051ec20e4b2c6200a3d84909658c401c5f04a12cb188028fa1042596310051f42464b2c6200a3d848c9658c40bc68
  | 10 => 0xb0ca6018f4874856194c0517d0fba2c1299330fd4f74582532661ea9ee8b04a6008bd82dd16094c0187ea3ba2c1298030f94374582530061e286e8b04a6008bf845c96094c0517908b92c1298022fa1f42582530145e43e84b04a6008be875096094c011790ea12c1298063e21d20582530053dc2a40b04a601ce8724816094c01d5284902c1298022fa1b72d91530145fc3ec5b22a600cad72d8b6454c0117b0f316c8a9802aea0262d91530055cc04c5b22a6008bf8758b6454c6917b0e316c8a98032b5c862d915336d1e432a5b22a6008bd879cb6454c0195f04b96c8a98022fa1c72d91533751f428e5b22a66da3d851cb6454cdd17d0f196c8a98022f61e32d91533751f42ee3b22a66da3d85dc76454c6947d0b38ec8a98028f61671d91530065bb8ce3b22a6008be87c876454c0117b0f90ec8a98022fa1c21d91530045ec3843b22a66ea3e850876454c0147b0a10ec8a99b6a7a0c21d91530054ec1843b22a600aba800876454c015730010ec8a9802aba0a70d915300556c14e1b22a600a3f855c36454c694790ab86c8a99ba8fa1470d915336d1ec28e1b22a66da9e831c36454cdd53b06386c8a98022fa1f20d91530045ec3e41b22a66ea3e85c836454c0147b0b906c8a98032bdcb20d915300657b9241b22a6008be870836454c0117b0e106c8a9a130f5d464d855301c6ec1ee5b0aa685c9d731926154c0117d0fb22c2a98032b1cb64585530045f438c8b0aa600cac721916154c0195ec9b92c2a98032b19372585530065db26e0b0aa600cb864dc16154c838f6ca382c2a98032ed9070585530065c320e0b0aa6008f7875846154c0117f08b80c2a980a2f211701855300c7dc3a41b02a600ea9424836054c0195ce5b24c0a98032b9c8649815300657b22e5302a600cac645ca6054c099d0c0b94c0a98033a5cb60981530145f436e8b02a66d8bc86dd16054c0117d0fb22c0a98022fa1c64581534261eba8c8302a67dc9d731906054c011f70eb00c0a9802976144358e5102c6e43a64b1ca26dc3f76dd153944530fb0db8aa7288034ddd37154e510145f43ee8b04a200c3f53dd1609440117b05ba2c1288030fd4774582510061f286e8b04a200c3c50dd1609449b0f90ea9ac1288030fdd153582510045fc22e4b04a2028bc845c9609440117d0fa12c12880a2f21f42582510045f43a84b04a2008bc87509609440b1f10e902c128803aa50920582510046fc3ac631aa251a5d87d8e53544018bb0fb1ca6a880387d0b6394d510070ea16c729aa20087c865c2535440127f08b84a6a880e1f61f639455128e2f39ec728aa20387c865c2515440127f08b84a2a88fb1e18170945510053cc2e81b02a200ae98210360544031f70e906c0a88073a9c920d815100754a1241b02a23ec5f655cc60544011f70eb00c0a8802ae211
  | 11 => 0x87aa241c08090dd2dd97a0001b48000000000de00000027b046aefacfa6b23a0001202bc80011a8000ea1bb9f5072919ae28000eb25004a0d1abe0e90001bd8000001878c78002b30ff9a59b82f20002b217b0ac2cc83e0e10e78b680ba849f88000cc96f88f901ac52aa9ad92b83d0dc80600000028716880009b00000003c0000aa0000218000001c8800000061a260289b700014280005d8000000000000001490b9a4927f8000000c69921e49a21db000400802000c00000800400000002001400000000401c00000400400000000400000400000000c00000800c00006800800002c00800001c00000000001401001001002000400000000800401001401000400c01c00000c01800001002401800c00000400c05c00800000001401400400400801000000400c00400800400c04801000000001000401801001000400401400c00802800801c00800800003000000400000001000000000800001000c0000280000000000ac00001000004800c06802000c00402000400c00400401402402000401801400000000c00000000001000400000400c00000803400800800000c00800800000000801000000000000400002800400001400000400801000800000401401000000400000000401001008001000400000801801400400000c00400000401c00400000000000403c00000000400800c00000c01800800001400000801c00c03400800000c00000000000801802800c00c00400000000003800000000c01800001c00000800003001000400002000000002801401004000800000c01800000800000c00000000001001800804001400800000801800800000000000000400402401002800400001800400001800000c01401801400000000001401c01c01800400c00000806c00c00004000801000400401000800c00001c00000000001000000c01000000400402000001400000001000000c02400c00c00400000c00401000000000800000001000800c00000c00003800000402c02c05400004401000400000800400000c01802000800400000403800000000c02001c01c00401400000001800c00001000000000000400000002800803801000800c00c00002400000c00400000000c02002c01000000400000401c01000001c00c00c00400802000000002000000400400800000401c02400005802c00000401c04800c00000c00400000000000000000002c00400004400000400c00000000002007000400001000000400001002400002000001404400005000800c03804c03800000401800400000c01800400404801000c014000c787ea6ba4c32998f0f54d74986530045fc12e930ca605c3f515d26194c0b87aa2ba4c3298030f14174986530145fc3e8530ca6008bd87d0a6194c0117f0ea14c3298022f61d42986530546e41ae4
  | 12 => 0x6687980014e1a180007317f00a2c3a8f9cb934ac2215a8b92d0aaa1125e8a409214480002c0000000000001ac0002868000000001d18000e08e80000000000bc80000015fa920b080000009c0000ca00000000000000023d8000a011720280025c80000015c11f2778000000110000002b90001e3804859af500000004f8000e48001d1161000000000076ae38208000001a080019380002784f0000001728000001c90501b5a3b1572e680026d2409a428d95802813380006680001c2991230001238a509e86f8000002a40d282718b8002de1bd0fb16ea661e1a7f185800156a6280012a0a998a8001980000002ba8492be8000001149ab9aaae71368099c597d0db09a8e1a09ae407084400007116aa002ea0000001ff8002d382600008e14f1ad00026c0000df85b1850001d6a410000000000001be98d0002da80000022c000000135024ad2aa00002e604c24c1aa0000001d59d880000000000000000000000000022f0000000000000f000000000023a8af2c78000ce8ed00015899e800107a749ff0000002e928f0000000149a300019d99086900012180000000000007427da6784482585a1090c480000000014a00008a0f18002170000119ed00009782e0008b7a7a8242062b02b8af12209dfa201b02148639a11b3a302498000001a02370362df254ac193ea108e221e2e89e58c40e3a128001b215586a0002cbaf6ac4a792c6113af0a1397c994a282450ff0ad8002729ae1869840da90b002276974aec1620879ee0fdaf01ca8f31e91891c527e91b80000000022300013e0000002fa02c80000000000000000015100025f0000000ec0b880000018600012f23e29a0e52442ab8948898cc18f2d4152253ab29668f90000758002742bf02b1fc86f1a28d992880009d00000010b8000001bf0000a585b8cb07600021ea4a89100000003c8000000fe8131a999611a0000000000001040002d60001ea293800062a429530000000001c2acf005a470000000001798000000002f1a528000001178002b50000000c600029307815e9240682552b0a8e1472d880000000000000018e8140000000000000001d01140000da1ae94f85c0d38b30c080010203b0688001af19e2430a787d9ba0b42af0000f69438bb83914220e07d02da50a6da5981f80015f1300671c69d38918621c400000020b17e93f29b0000000002328000000180000001802988678aca0ca0c2e4ad000008680016280000000000000028a845a880000000330002380002152b7b000000002ac0c28d8927a2b0d52090b600012b17300000017500029e8f48000000000000faa479638000b1a7720410285d08caa800000026aac0abb181a238001f900000003197200026a1c12a09a50000be2d682383804895a8a680c8e680025d11580000020380000009d800000169
  | 13 => 0xcab61ba80004e00000a8002d10001912541778001258719708340d11f00001600000001b680022b8001160000de80000005faae01087b80000000024b8c98000000000000409cd0002ea8f812fa6f2690f89f28121f99001f6a348212ff80000029f9880aeaa29cb1ec24e0349c4a580000dc23612823c2191d094c2ce07c21b80016b8a20af9a794a9932c29c02080d90d02998c3a2920a25a80000009700020880000025900014c8000001dc80028d0002632a78508a180000019500000000000028180000018c0000000000000c32bd00000018980000000013c0001919979c7abc29d8002398002d31de8f08338002b42c316d00000000022d9feac000000004a8000002db00000028a00000000000000015d8000001c80000000000001d624f0000f598b19b1330002f72559fb0000002458001eb0128e614e8000558002980ce00018f89300025f854a29a808001ee97b8000d5800269a0f000181000000000000289800271ab495000001595caf600021a27d0001f400000000000029094100008388295d1df22f87b0be8000db9ed8ad0001e2911258a781c601b1e688700024c80012e8000000a38000001c18000002840000000ee27baad8ae0002788000bfa2e0882a50000000000001431e98170000b72178000000000000000002fb819167a3e8d300d1220000001a70001650451c38000298002c686617100000000000000000013b0000000000000000000001cf00014b2d48000000889120002fe0b48311d51b88000002568000001768000792468560000000000ab0000540000000000000000000000002d500000006404d8378000001450001f20000000000328000001608a60000000002dc0002d720480029608b0000f98c5800000207000000216135a6b8860d600000000017d8002199808f12eb88f19013d2e00002e780001f0000000baa94ada08d8001529f72f993121b0000c90002d98000001d820080f000081af80bc03500886e18319400002b8001760000000001e818480021314096f00013a2eca1800000000011c0002919080002e0aee2dfa288579262338e2a119101fa826a9c8002c71b51e78530752bf8000000000bd0001700001d98001ce80024187ca310c10a28388001b10e72e21fd940110961800148000019afd0000000000842e516c0000fd00019c0eb90e27a12d957a101f80ca8000000000000002aeaa92a6800064a6380015400013c86a9690420b227106d0b59bf8d810705680012910e8000002ed00000019ba0e8b91d48000399270000002d580029e0002078f401d9488001e020d86014b85281000c25713f8479318e9a1c0e8aa1a812d82258000001bc0000000000001378b027625218202320f80016e0002cb0000001648002448848000000001959eca3faf3000078ac910680000022aa
  | 14 => 0x1519dc1e080000000028902001c97c26201a8000480e30001680000000002271308fe0002359f08000000000000000000001de00000011faaf8cdab81cd9ca00007016629c0000000cd1a80002a98b82aa000000118a51ad22fa85924da018001fe16a17700005225baf490d1b30d08001af8001f610980000009a00000000000004614600002aa839be03a00000000016406b06c13210128293b8000958001eb8002fb2e98a82b6947895150a9721f0c50a09e89089e13008000000000000001c21b09030a10001190001759719789498772b980020d1049a90000000fa2bd9658800002482b395519d21f80000002eafc1d400003da9298e00010d80000028887208c2eb1a6885a030432ad198a0694d87ea0515a092aa10079f110c1e222180b1f30a70632a30e40c204723680000026487e08e8002ab2750b38000778369459fbaf793417e0001f59591229b9aa3a7e0bf1c30498000002389fa0001d700000000009f0000000000000000000000000000000000371f38f600000000000000000007480100028213700013a8fbaf5a8e8d72309d2a250000581990000000000000f78000000000cf2600001cc8612390000001740001f49b79208ab8002670e00b529427980000010f98c8002228001dd00008d2ca8bdace8fc8588000001d780026e8a300024e8002e329aabb80016b0000002f280013800025b2318000000a897fade99a98dac989b85a8000000000000000bb000000000116a0b8000f70c022a0cfa4222211d8960001a48000000938001560000608000ba00000015e00000009c9630000eda5d87380011c9251dda8008104000e00007a00800000019f0002db83089fa4f8000001298160fc0000000000000000001398001f18ee80501e8c8800006ab10b280000000015b10629ba4d1e700011b2fe80e8000001388002f900000000002a0000000001871b18002861418220c727c80010f05ca5106da3321a8000002a20002b72c811d1a61e5000000265a350002900a49181838eca6c81a10580004b00025a0d217a99c8000000002a58000000909b90000000000b11cc273a730320000001038000000000000000000002dd0000002e82d91efaa600000000000027580010080000006e8ef167042acc0e5aaca400002248030000411bc80004c84e80001e0820000698002a880000000000014d0000a900000402d000089000041aef2640000570000550968000000000000000000002c400fa16a1c90a99700028582f8cb80007f0000999129e40f22c59c722d00000010c800218a1d0000001548000000001a39b629d00000000025e02f1538d780008aaff00180020aa6f8000000138c800001528c00000012a93d8002958df1468f3a4600028b00000026529f05380021da950001ef0f2a7012125c0519390efa60999af
  | 15 => 0x2cd8000000000002c11fc2278070000002d080000020596d80000022680025780000028c9268000001b29cfa5600006c89918a2ba0300001fd00000028780007f8830002120d423d18280000283f1329da0000000000001d9000000000000296a438851daa8326e09000397381ba9782281d0940d4a6100001780000000023400000003fa2c80010500000005e80000000012c8001a88168002f8a3bab18d68c196c88b80000024b1f78dd8002212688000358438000000000001e32ed8000001bb00003b9aca3ca0112c000291124898ab580011e8001ab2a70002d180006519680020200d8000000001d21d30000002850000001ce1152c89132d7880a68000000192865a4a00000000000000000006b988800000000111aa480000000000015984b9791ea8000002ee94410a00000000009e0000002e10000000002f38000000000000f5000000000248aca00003e8ea8000188000000000002cd00000000000000000023f02927080017800011e2f41361db9e600015b89800004d05f00005e2378000000002618001b40000002dc83a8000000002e592e1c999a25300000000021400002519fa722fd85122eae1a7c232
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x687850e10f084028b01304c01b06744803e54b80005059104349000040319003861c000000820455c20d20c0141d9314174986530050764c50dd16094c014a89750920582530050764c50dd1609440182f7560874580310060b1d5821d1600c4050ac985c942580314370a1d542481600c40141d9314174185500050d644505d0615410dc287550920586300058a25942483654c10dc2a7650920d95300058a64864480654c0016299418920195300058a25942480654c0014aa96dc920d91300070a19772483644c001d094248175cc5300060761c64197314c001a8582508614c5300052a25d42481638410dc28755092058e100058a25942483654410dc2a7650920d95100058a648644806544001a306420520195100070a1977248364440014a8975092058d1000e2a21d42481634410dc28755092058d100052a25d845891004001c28751d16244010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa88688642052019510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x2
  | 6 => 0x4b
  | 7 => 0x4d
  | 8 => 0x4e
  | 9 => 0x138b
  | 10 => 0x4
  | 11 => 0x94b
  | 12 => 0x94d
  | 13 => 0x94e
  | 14 => 0x124b
  | 15 => 0x124d
  | 16 => 0x124e
  | 17 => 0x138d
  | 18 => 0x138e
  | 19 => 0xcb
  | 20 => 0xcd
  | 21 => 0xce
  | 22 => 0x9cb
  | 23 => 0x9cd
  | 24 => 0x9ce
  | 25 => 0x12cb
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0x168b
  | 29 => 0x168d
  | 30 => 0x168e
  | 31 => 0xa4b
  | 32 => 0xa4d
  | 33 => 0x134b
  | 34 => 0x134d
  | 35 => 0x24b
  | 36 => 0x24d
  | 37 => 0x24e
  | 38 => 0x144b
  | 39 => 0xb4b
  | 40 => 0xb4d
  | 41 => 0xb4e
  | 42 => 0x144d
  | 43 => 0x144e
  | 44 => 0x16cb
  | 45 => 0x16cd
  | 46 => 0x16ce
  | 47 => 0xbcb
  | 48 => 0xbcd
  | 49 => 0x14cb
  | 50 => 0x14cd
  | 51 => 0xecb
  | 52 => 0xecd
  | 53 => 0x17cb
  | 54 => 0x17cd
  | 55 => 0x94053
  | 56 => 0x94055
  | 57 => 0x138953
  | 58 => 0x95393
  | 59 => 0x138955
  | 60 => 0x1489
  | 61 => 0x2c9
  | 62 => 0x14c9
  | 63 => 0x139253
  | 64 => 0x125393
  | 65 => 0x17c9
  | 66 => 0xb49d3
  | 67 => 0xb49d5
  | 68 => 0x9cb53
  | 69 => 0x16c9d3
  | 70 => 0x16c9d5
  | 71 => 0xec9d3
  | 72 => 0xec9d5
  | 73 => 0x17c9d3
  | 74 => 0x17c9d5
  | 75 => 0x1789
  | 76 => 0x130c
  | 77 => 0x14c
  | 78 => 0x5c9
  | 79 => 0x134c
  | 80 => 0xb5693
  | 81 => 0xbcc
  | 82 => 0xed693
  | 83 => 0xed695
  | 84 => 0xbca53
  | 85 => 0xbca55
  | 86 => 0xeca53
  | 87 => 0xeca55
  | 88 => 0x14d353
  | 89 => 0x1354d3
  | 90 => 0x1354d5
  | 91 => 0x17d353
  | 92 => 0x1357d3
  | 93 => 0x1357d5
  | 94 => 0xb4253
  | 95 => 0xb4255
  | 96 => 0x144b53
  | 97 => 0xb5453
  | 98 => 0x16d453
  | 99 => 0xb8c
  | 100 => 0x19cc
  | 101 => 0x14cbd3
  | 102 => 0xbd4d3
  | 103 => 0xbd4d5
  | 104 => 0x17cbd3
  | 105 => 0xbd7d3
  | 106 => 0xbd7d5
  | 107 => 0xed4d3
  | 108 => 0xed4d5
  | 109 => 0x1a8c
  | 110 => 0x178e
  | 111 => 0x4953
  | 112 => 0x56d3
  | 113 => 0x1889
  | 114 => 0xd09
  | 115 => 0x5813
  | 116 => 0x5515
  | 117 => 0x49d5
  | 118 => 0x5995
  | 119 => 0x10c
  | 120 => 0x98e
  | 121 => 0x128e
  | 122 => 0xd0e
  | 123 => 0x188e
  | 124 => 0x589
  | 125 => 0x58e
  | 126 => 0xd49
  | 127 => 0x1049
  | 128 => 0x144b15
  | 129 => 0x1456d5
  | 130 => 0x188c
  | 131 => 0xd0c
  | 132 => 0x74c
  | 133 => 0x58b56
  | 134 => 0xd0996
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1657
  | 6 => 3241
  | 5 => 1538
  | 4 => 33
  | 3 => 1
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (67933+((h/552+packedAt gbK7 (61309+(h % 552)*12) 12) % 3518)*12) 12
  | 6 => packedAt gbK6 (169608+((h/1080+packedAt gbK6 (155568+(h % 1080)*13) 13) % 4279)*13) 13
  | 5 => packedAt gbK5 (96886+((h/512+packedAt gbK5 (90742+(h % 512)*12) 12) % 2456)*12) 12
  | 4 => packedAt gbK4 (2376+((h/11+packedAt gbK4 (2310+(h % 11)*6) 6) % 40)*7) 7
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc3e07c1ff81fe3e01fe03fc33f907e0f3673
  | 1 => 0xffc007fe07ffffc001fffffccc81f8c71f87f
  | 2 => 0xf07fff80007fe0ffffe1ffc030f0e1f381cf9c
  | 3 => 0x7fffffff8000fffffe00003f00fe03fe0fe0
  | 4 => 0x7fffffffffff00000000003fff0003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x54c0e4140c99096320d3209581139036071631
  | 1 => 0x90c00292022328401044b2a04480688306846
  | 2 => 0x60512c80044d48294a41948090b02152818298
  | 3 => 0x426514e590000d2959801032b00da015a0d60
  | 4 => 0x487b9e7396779c010601060c3efd0003edf000
  | 5 => 0x8e00180318061002181018303feefdec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37155
namespace PEqualNP.Outside.L_meta_37155
open PEqualNP.Outside.L_meta_37155.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
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
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 539 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96)) (concat (concat bs2_4_128 bs2_4_160) (concat bs2_4_192 bs2_4_224))) (concat (concat (concat bs2_4_256 bs2_4_288) (concat bs2_4_320 bs2_4_352)) (concat (concat bs2_4_384 bs2_4_416) (concat bs2_4_448 (concat bs2_4_480 bs2_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 664 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 (concat bs2_5_512 bs2_5_544)) (concat bs2_5_576 (concat bs2_5_608 bs2_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 33 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1536 : Interval gbAtlas 5 1536 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1538 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))))))
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
theorem bgb_6_3232 : Interval gbAtlas 6 3232 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3241 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)))) (concat (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376))) (concat (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600)))))) (concat (concat (concat (concat (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))) (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)))) (concat (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))) (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))))) (concat (concat (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))) (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816)))) (concat (concat (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))) (concat (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)))))))
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
theorem bgb_7_1504 : Interval gbAtlas 7 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1568 : Interval gbAtlas 7 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1600 : Interval gbAtlas 7 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1657 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))) (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8feeafce8fec8f8c8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813032 * 2 ^ 32 + 4274583752) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37155.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.and,[1,3]⟩,⟨.and,[0,5]⟩,⟨.or,[1,4]⟩,⟨.and,[0,9]⟩,⟨.or,[2,10]⟩,⟨.or,[4,5]⟩,⟨.and,[7,12]⟩,⟨.or,[11,13]⟩,⟨.or,[6,8]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4274583752) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4274583752) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37155

open PEqualNP.Outside.L_meta_37155 in
theorem PEqualNP.Outside.L_meta_37155 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4274583752) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4274583752) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
