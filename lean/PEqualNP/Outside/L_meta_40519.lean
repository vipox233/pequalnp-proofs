import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40519.Model
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


end PEqualNP.Outside.L_meta_40519.Model

namespace PEqualNP.Outside.L_meta_40519
open PEqualNP.Outside.L_meta_40519.Model
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

def SBf (j : Nat) : Nat := [8, 5, 6, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40519

namespace PEqualNP.Outside.L_meta_40519
open PEqualNP.Outside.L_meta_40519.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x10cc0010c000104a0c97810c50800011800c8fc41fd40fe43fc31fd10fd32fc32fe32fd42fc10fe42fe10fd21fd41fc21ff42bc40bd43fe30fe40ff31fc30fc42fe20fe41ff10fd20ff43fe21ff32fe31be40ff20fd31bf43ff21ff40fc43ff30fd30fc20fd43ff41fc40
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x4417d53c43e8a2985f943319eaa621bd5250efea8885f14b10dfa0c817e50d07baa7a15f94643eea1887bf438c2fca3206fd0c31beaa2617e534437a86186f50d21fa988637c54cc6fca3996f50f41dfa10817f52443e86208770c830de282873d54086faa1a0dfd5320bf298837c51502faa3205f54a20dea9687bd51d0efca2105f14532dea1883fa20082faa5a05f54242bea9c83de320c7bc87987dc4210dfa8c81be41507eea2986f90310bfaa463bf43886faa8185f15220dea1a217e50842fca190dfd45439eaa661be5050f78a4205fd4930bf28685bd43842fca0216f95320dfa1e437e5390efca0207d50441ef19461fa10042f8a898df55031beaa4857c528437a42205fd4f10ef188617751482f8a0a0df95320bfa96217d51ccafca810fdc8410bfa9841bf411037e86106f8ca40fc88021bd43ccafea9986f50d41be29a837c524c6faa6886f50c32ef99065ec218837ea4a1ef90320be2a421be50d0fbc8618d754f41de20881bc42907de40105754c40bf29e85be4350f7842205f94620fa908433c544c3b862186f14e40efa9a21bc404437a8718cf95031bea94637e511037ea8887790c32cea1a61df4350f7881986fd0e41bea8841bc40843f641885f14c10bfaa4437e530837ea5207bcca20be29e417e539077a86216f50f31dfa9a87be400c2fea2905f14e10f7908437e50ccafca4217714d21bf28e417e5110afaa3986f94b43dea1683bc5150efaa5186fd0a42dea0881be531037e64205f14d42bfa8a81de53d077a87106fd4743ae29a415e53103be8721ef54543df218817d51c83d865107b88521bfa8263bc21903be61185f55120bfaa265bf434c37a43205f95040de2a241de438c77ca818df540429eaa4877d548ca7aa998dfd5131de190817d530437ea5a1ef10640ee19463f741507e843085fd5321deaa6637d5110b7ea8905f550329f28481bc42102faa890df14d40f629221be540cb7ea7205f95020dea1c617d5090f78a4a1df94742fb082217d528437ca810df95130df20421be404437c81987750e32bf2a0617f548437a8618df55321bea80637e544cafca7085fd5331bfaa0637d5110f7c8420df15321bf288617c548877e86205f94443bf28483be311037a84a0f70ca30bf29e817d518cafca208770c831de20441bd41902baa7a15fd4c10df994817e508cafaa7194fd5110be2a4637f5250f7aa7205f54831bf29663df318c67ca8195f54830df98881ec21082fca4197ec4110afa9a415f53442f8a710df54440df21c817f53c837ca2a1ef50e21be2a461bf434c77e86905f94820fd88421bf435037865206f0c440dfa8287de53d0afca7216f50d42dfa18217d53d06faa8887bcc820bfaa0217d5010f7a8790df15332ef98863bc42902fca8215f54b31df2a0617d508c6b8a690dfd4931
  | 1 => 0xd52902fea710ef55332dfa1e857d50d0b7a86a05f94432bea8665f6310c6f8a2a1efd0842dfa8a87bc50d0f7ea890df95230bea9841bf438cbba8618cf15230bfa8a65bd54c42fca8905bd4910be2a465bd43903f480205f54f42ae29a217c540cb7e87905f14142bea9e417e53487bc60985f94020bea9a43bc54486fca218de14121f7102417f54ccafaa3106750e31df202617f53442faa910dfd4d20dea0883bf52102faa7a06f50c43ef21887de324cafaa5886f90a41fc10621ed4210afaa9886f14a40bfa9a836f524c3bc6298df94030bea9c437d540877aa1a1df54810de98881bd401037880907ed4121af29e85fa300c37880085fd4121bf29483bc42106fca318df94730de2a461df53482fca6215f54910bea96877f548cae8a2985f54e20dea1081bf430c37ca32057d4d21cea1e617e518caf8a4a1df15030f719065bd43d02faa7085f15132bea98839d430c77e8610efd0f41dea1c857c53086f8a690df94243dfa1a437e53d067aa9995f54743de2a221bc43103d8a4986fd4440bf28843be50103dc84217ecc230de98c81de320c27ca998f74c431be29221bc439037e8620df94f20df292877e540c7e8a2904f14143eea1a619d53102faa9984fd5130dfa1c87bd43cc27aa6205f94032be28a61f421042f8a4a0efd0d10bfaa0657c53c86fca410cfd5121dfa1e6177514c2faa110efd0e109eaa6417c53c433a86197dc86219faa461f510043f680a05fd4810bf29843be405037c80906fd0d419e2a241ef324cafca12079484219faa241be40042fea7086f90840bf284413e54c42fca1a1df54041df2a6637d50cc73ca6206fd0f32bea8c617e53902fca418df94021bea94817f52502f8a4986f50f10dfa00817c544c33ea6a1efd0a40fda04817e5190afaa010df54b41dfa1865bd429027aa7204f15121be2a0637e52d037a86996fd5230df288817d5490378a3205fd4142bf296217e51106fca710f74c832dfa9881ba50102faa7187b4c832dfa1c637f534877ca3a1ef50f20de206217e5010fda40106fd0c429f2a661bd32902fea2987bcca32bea9c857b50486faa1195f94b43bfaa6217e53c87be65194f15110bf294817f504cafaa921dfd4a10eea9e837d54cc6fea810ef50e32de29687f9300c2fca898df54840bf28083de328c67ca9995f94a10f690843be4250afea790df94740ef980617d5290efca9086f55330ef21c65be429027ca821fec8120bea8483bf438837a87a15f54a41dfa0c837f54082faa0195f95231dea1085f7314c6fca8196f4c840fd900217e544437aa6205f14131dfa1e63be521037aa2204f94343bea9c63bf544c37aa8185f94843de20061bc40c82f8a7105f15010fb98821fb304c2fea6a16fd0240be29a21be32103dea4985f55230bea9087bd43086fca118df94810f790
  | 2 => 0x210149203c000000002c1c00010000010c000000022401a000110580000000010d5078000000200c050240b00c1c03c0100001000060007a0600b03004014890740b0140504a6103400040590200c020050080504c340046a04400008020f4000340d020030002b0241011803028930fc0504c01018400440303c1104c08024070040101c012b00e074020500000c0002c0009c020640000c00000180080100001010030e40e02c1c000003283d0546d08c0000c1702c000180000c0001c01000e610cc5010080000a0500000402180510000404c0002c0200c000040115c7e068149fc08000090680b054390a00106c000b00642400000000240906800248950000c104a4000150001f0180007402000950100005084020673a4970d81a000000002f0600500008000060381b008000302f00013000353fd42360000080403006000000001f28015000040240007c370000f3982d0001006c16004000105d0181000000000620004d11c010137881184f55030ee980617f540c378a6204f55031ef18c61bf4310efca998f750f30bf2a083bd434c6fca910df54643f790c43bf4350b7c42205b14910bf296837c544877e87205fd5220bf29c41ee218827ca9906f0c640af29e837c540837c81105d14520df18c817d5310afaa9105f55020bea9881bd43082fca3a1df54343be29281ec320827ca0205f94f10ef298817d544cafea2a15f55332beaa641bf31903ee63087bd0942bfa98433e54087b863185f94a43fc28243bf211037a8720df94230bea96617d52886fea0a0fe48020de2a261be54cc2f8a810df15120fa18c21f8200437aa818df14121beaa483be54c423aa6207714d10bea8c857c5050f7aa9906f94e40dfa1c85dd53102fca6905f95220df204617f544c3ba86195f95232fba8a41de434c2faa190efd0b41bf28c836c524c2faa420df95121bf298217e51886fea9187ec8220bf2a6217c54c437aa8197dc8521bf28485f621087dea4886f50d30bea8e81bc40082fca6185f14520bea8c217e520c37e87a05f94031bf298637e50042fca6195f94a31bf290817f53502fca110dfd5121df208817c53483bea690df54d20bf2a021be21902f8a2a15fd4941df294817f5050fde85215f14c20df2a6657e53102fca821df948419f2a0617d54042fea8905f94c43fb90c217c504cafaa7205f54742df90c81bf50d0ef8a4085f95321dea9081bc404c2faa610e750e32fca00813d540cb7a86205f55231dfa12837e52443ee8320f750e31bea9e437e52cc2fca9985f15330fb98c637d548437aa810df15320dfa0883bd5050f7e87885f94a32f7108417e54ccafaa2196f14743bea8861f641106f8a8885f94630bfa9c41bd51902fca5187dc4010ee29a41bc511037a86085f94a42df20041bf434cb7c83205f55131dea1a41b
  | 3 => 0x2b98a000010001c00821064494f81f00000150280301601000214000c8020140500c810000203800294000500b02c12024bb0100c1fc1905
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x7430863c6055032dc147204825d6315020c7989531031e6154c40b9d95210871f6554c408fd954310f1c5350c21cdd44404829d63103208fd94400c23e6414f10d9148514c31f5350d429718d520432d4314930c750d508c71e53940409b189544c6786054d21f818121086f061480209dd95310c63d65d0c328fd9743c429c6050c328f59253c823c6454a308f58f544426c62551108f59253083585314121cb14a404c23f6454032c758c544c3385414121abd895150e3d6414b10c7193534869f63546409798c520429f6354a408f594329023f6454321b9185200831e5350f218f191508c71f548c630c798e540865f6355120ae98353103676548421a798c53103986050d308f59543c833754d4530c758e54c431f64d4d10c718953102756115020d514c514831d53108408f98254cc72d43d4930cdd0c51483954314530e694e501023e65d0d218f180544423e64d4131c794d438831c54d4d20c7193534431d5350e42c7d85531031d548c8308f990538871e6395031cd150514825e63951108f58c54486766114c208f99352c42986050d309799453442bb604c440a758c40c425d63d4a109798f52c4367521453097d8d520423e650c840c754d438431f53d0d20e350c524c2ac6254143a758c400438f434c832b9181210863d64946208fd9150cc63d63550308fd95430c29e61d4d439dd85544831e6414d10cb153524423e6494820cbd4a404c25f6354910c754d52103732114121c794d439029d63100208f992538836551084209b98a524423c6055332cd50f514825d63951328f195211033a60940408f992538867b6544010cd153514c31f5414d219b988548c7c763484219718d5190ae462440108f982540867765484218f594400c23d65cc640c715353486ba60d4a40c7d935348795438c431c794d43d0a3d65900309758e524429f6550c32a7590328c737519012097d95300c31d6414d10bc181210874c53d49108f992528c31d6154c408fd91528c66e62150108f996404823f6550c218f590538832f54d4910bc580310431d53cc440ad98750d0e3e60950319bd8953442b46154143c714f43442b761541439758c540423d6414f108f590524c63d6395320e9d0d210871e6395320e6d0d300c31e6414d20a798f429029d6490c329ed95401026e62951109dd85544cb1d5394440c7152434c23c64549108f590530831543145309d58753c82ba6014e40add855250e3d650c6408f59421102756195120c794d431031d53948408fd91518c31d530c8408f593504ca3c6454420c750d500ca5d63951219d594310427b60549108f59053c865f654c832c754d511033754d4520a758f4210a6f6255130e350f524c25d6590c31ae983539023d65d0c31c754d430425f63551108f980544423d6494630c714f434872c5414910
  | 1 => 0xc27b654c030b358a430ca9d6310030c754d321031d5350440cb148404c23d6494c21e3d89438ca5d63d4b108f597311031f6550e318f99053482ac6254543c750e52cc23d64d41218f590538425f6550c43a7181438cb1f5350d409758c548829d6490c31ae181434c32f43d4930d3548320c71e5350e10cd5445150f1e5450f30ab988511031d530c440ab58b50d0e3d6590c409d58653482d5610c831c754f42103564314530c794d430423d64949108f191500c7a840480209d986544831f540ca308f597430c31e5450c31b5185300c35453841109d586544c25e6394910a758c511021d63950219e982534863d64d4f10d5d4c514833a60d52309e59420042ba6014440c7d93534831d5390c40e550f514c29d6395021cd54451d0fa55448421c750c514c31d5350e40c7d95430c73451101308f99253487c46348421cd1535148395430c4108f592520831d54cc030c7d4d435065c63549109bd954210abb6048440a798f511034e4314930c7d4d434423c60553318f992510429e63d0440cb50c524431c5414d109b98b53c431e6395032a758e54c42cc624c030c7d4e404423f6590030aed81321035453d4520ad984521036752d45308fd91500c69d6310110c754e411023e64d412197994534863f6355310c754f42d06ba60d0d309ed81534869e63d4840a798c511025d63153218f990534432c5290110c7193534825f654c4319b58b53c423e6510110cdd0f514831d63950218f997329023d65cca409d185534838d430ca209e181544cb1e6414d218f994544863d64d4131ae181438c29e62d4d438f992518823e64150328f590520429d64cc631a758f429031d4394832ad185435063e6095032e9191210871e5350c20ce980548c26f6255110a758f511031f6550d308f992544823e6415030ae1815150e5e63150209d984548ca3f6550040ab98851d0e3e64d4a10ae983438c31d5310440c754c511023c65486408f59743c823e65cc6408f990530829f6550c31c7d50534431e5350f41c754e321023f64546329798c54c871e6454c40a758f4250795430c610a758e400c2756115232c7589531031d540c4309b58a544423f6454332c794d438863e65d0d10b8181210873b54141218f590534423d6494e209798e5348397434c4319b588548c6ad6214440a7d92304c33943d4121a798f421023d6494c30a758f419073543145309b994524425d6395320cd146404c23c64540219dd85534431e6454f418f992530871f5350f108f596540ca3e609533297195434c29d6310120e9d91210863c64540328f597430863e65cc840cbd48404c31d43947309b98a544c23d6414e218fd91534823f6355030c754f511029d63953208fd9743c82bb60486408f58e54c431f5350c21a798f419023e6494c109e580530871d6414d208fd9
  | 2 => 0x63d0b41a75835350e3c6454331a7d8d211025c6354021c7d4d43c83976150e31c7d4f434425d63951318fd8d540863f64542329b98a534429d63902309718d544423f64542319e181544c65e6395120ae1815250e746154032c754e42102ac6250d42c754d401023f64542218f592534425f6354021ae983521023d6414c218fd95411063e65084408fd8d54c82b8604c840da14b104431d5348440ae18143c431d5350c20a798c521025d6395120ae181311023e64d4f20c7552310c3375110130e350c320829d640c8318f191520423d6494d21d3d4f524431c5310120ce50c50486ba6014a40a7593320cb1d53d0f418f99053c863d65d0f108f19153482ba6014c40ba18121086756114c208f994544c23d6414d218f992524423f655084297d8d529063d6494f108f58e54086d86050d30ae181219029d6594c409ed81544863e6414b108f990534871d43540318fd91520431f548ca308f592530ca3e64d4132c758e54c823d6414d208f992518c2e86244010d5d4f514825e6394d218f994219023e6414c218f99543482b86050c208fd9153486796094d21ce993504863d65950318f990538431e6454f428f592538863e6495130ae181430425c63551209758c520431c5414d219b988530426d62150108f992544869c6050c31ab98b50d0e3e6494c32ced53504863c65d0d21c7195438c66d6214c10a758c521023e64951108f594219034c5388120c7d95438ca9c6050f30c754d421029f63486409718d529033751901309798e54c831f5394e408f59253c872f43149108f59053c831d53d0c42c754f43d0a756508410c7181531033543d45309798e544866d6294d108f181540c69d63d04408f596540871e63953109d986544c31c5350d208f197434825e6394d10b958a210871f6550c32c714d43c823d6494a308f994329023d6494c31c750d508ca7860551218f99353087995394040ad584521023e6494a109799453482776544010d6d4f504871f5350d219e982544863e6510130c7550320c63d6494a10d550c514c23d63d5120a758f4290a5c63551218f996404423e60151218f995434866f654c8328f19153486746155132cb5485250e3e65151108f191534426c6254d108fd9543c423f64544208f990520431f5310110c7590534869d63d0640b518d100423e6414f20cb50f524431d4394831c714e40483374314530f8084200431e5350c30c7185531031d5350e418f59352c434d4314930c754d438831c6550d30cb54852d0e5d6395310ae983511031c5350d41abd895050f2f5290110c754d42d076452d45308f596421063c6454a31c754e501023c6454630d3d4c52442ba6014840c7d50534833b43d4121cb148404429d63103309798e540863f654864097d8d5190a3f6454a30c754f401029d63d0840cbd0c524
  | 3 => 0xd308f990538825e6315220d6d4c504866d650c8209b58a544c3946150e3197d8d529029d6310210ced90504863d6414c108f992530c71e63953309e582544865d6315210c714c404439b6050d30c7d4c404823e65d0d208f58f544871f6550f308f59253043645284110ced0c504863e64149319798e54c431d53cc8408f992530c23e6494d20e9484211023e6414c108f590514ca3e6494e10a7d9543cc27761540328f994544829c6348440ec101100423f6454910c714d43c426f6548421c7d53308c23e65101208f997435029d63d0441c7d53534425e63d4a10c754f43d02ba6014640d9146204827a6014c21c754c52103375414530c7550320c25f6354420c754f41102ad62d0c42e3189438ca3d6550c21ad58750d0e3e6415031ae983519025d6395110aed815250e3c6550d108fd91534432f54d4930a7592434c31d5350f21b5586430c65f6354640c7d53534863d6595030d314c5244354518c130a7181438c63e6494f208fd9543c823d650c4409758c54886cc6348020cbd50524c23c6550d21cbd50524429d63101308f181540863d64944108f1954348398404c0309ed81544c63e6494f109bd89534829d64cca328f594321033743d4530e950d210871c5350d21c7951430ca3e60d51218f992534431c5414d208f99353c423d63151108f191508863c64543329b189500c79943cc130c7195438ca3c65d0d10cd150514c31d5314c40a758f521023d64d4c218f597321023e650c6409dd85524433543145208f592534831d53d0c41c754d43886746155120ae181211023c64542329dd85534827b6055132a758c408833451901209798c548867765504419b189544c34c528c130c754e211031f5390120a758c408c26f6255131f8d81210869c6354a40c754f211031f540c6308f19150c865d6590c32e9484219031f5350d20c754d311023f6454021c750e510c71d4394a31ad98452d0f3964d4121d9d4821842746155130c714d434432c54149309bd95200825c6354a418f995434423d64d4f20c7d4f434871d548c831ce153504872f43d4910c754e311035853d4121e350e320ca5e6315030c754c431023d6494e108fd9521102ad6214743cbd48404431d544c030c714e404429c6348640cb153524c31d5308440ad58452d0eb46154943c714f434831e5450c43c758f548c36552084108f99731103a654484219e596100423e65901309dd85544c23d6550f10c754f43103386414121cdd50514831d63152308758e54c825c6354640c750c524c23d63151208f99253c871c5350d42c754f521036a21141219d98753c823e6494c208f191518ca1c6550d3097d8d544867b6548020ba58032082b86050f208f990514ca3f6550c32c750e518cb1d43944328f99431102b561d0c41c7d53534831f6254c409d986534829d
  | 4 => 0x2200b500040a990d100400044030000502400078380002508c030e52a0140f0241e01c0d0200318c130cc6608026010001840f00005894130080c03c150040801c6400407024010d000000120005100c22158070041098c010040030c1e0340d02c0019455004650e003000074e415084024ac080000d04a910200011c01042650c800004000d81f000027644500874008150050600074000271500007810004000080504430000125b81d01805000090305b1b01a0101709c283200c004720fc000000005c21008030800a0a43f13c002b80b0102902c49000200041b000410000007c00175cc0241200019004000b432014050a00b014cc000a601401000011141b01018064174fcbe0000000afc00c0e004140280000c0b0404f0040308c0019066000d201020000e902c09004000000701c001380a038000000000006130010080a0346200c00004070000211c170140109c5801000184630002a090530405e0345c088030d0081ac040400c0141b00c00004de048003dc005b8133b80103f1e6054c40a7593310c6bb60545439718d51082766115020a718d519031c54d4d108758e54c423e65d09418f195434c26f62540319798c548423d64d4a109758e540865e6315010c350c524c23e65d0d30cd144404823f6550c318f990540869c6050
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x7b020900050d00010c462985082402240206001e0c040b0500000104081c093800070000410920060d16000b00120200030f060502000300101c000b0827a2ae3322a6206195318121102c43828619041985942108010c2ac6288809869063101100420eb9cc928821075d85310110c32c7306a91860d53588511030aa18c2a8065895952108440a30e0a1aa018e0d43189500c687396a6a1e21a85506048421c2aa6b08a4205907050f514c20ebb0a620241451c14314530d46e83024210d85739512108698382a228a87435ca6454f4183eeda9880905087050c524c30ca98c0a1841075cc654844083ae7320a5884e07158032082983828628a61681c12108640a2ce232a871960d63d484044312a92c229687291d94348421c1ec8294609841d73180544430d3a8c0a1a61c41c14314530e0a86290a29841f7359421902c438286292614a1c14314930c32a630286085157199153d0b8438286292618654f604c440838eca9a4220591731011004351a18c090843075cc6055021d40c83024210e0d63d48404c20fbaac720061461c16254c40d40c2202401041d73994211020eb98c8a84438654f6048440a30e0a18a2986c063181210870bb20a31826183595430c820a32e6320a090d907050c514c312b12a228e87521c14314930a2ce3b2a8698524715485250f4431080980614a1c15214943a1ce5b2a869861563d444048287b92c2a9881459c66454c40c2ac230aa620518705855310292392a228a87681c12108440e26e0a18a29870b7050c524c28c3828629261451c56254c40870e0b2a8610e156550c310420eb98c8a8643075d46348440e0aa6908422061b5318143c82a83828628a61465d4404c030a1ce432a8718c1d7598f421028c38286a8065621c143d4930a20e0a18a29851975d0d300c292bae869084307ddb531011083ceca9a42206a062101100420eb9cc9a8243459c75350f20d2286b00620861563d44404c270392c018821c150f521453083aeb31e82205197399350487503a0c09084385550614c030c1aa8312601849a75181434c361b18c090843a8d906048421d20c2202601841d7399252843512a0c090843a850c6048421a18e4b0aa62041d73992520830aa9cc229081075ce6494620d08c831a4210e1953d813210287394c8a9881641c1430c410a1ae5322a62060d63148404c30ab18a2202418358c5210110c36a63028788688631012008306b10c4a988145dc56254c4083ae7306a890c1e76d4d43086863828629261465c05350c21d1286b0064107054314b514c2c4b9880900418354e6214440
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x8828127000c0100026b220000010000000000d01531c12108440a81831d06048421a04825846154c40b008050c52d4530c81431c9600c4109048754d2108440b008050f5214530b008050c5214530c81731844048020c21651c12108440c09651c1430c820c81431c5600c820c81731884044010a818395060484218918718c4044010a1281d4c6050f20a04815886254c40a0a82d4c6050f10a21851d06048421a08805886254c40a2185d0c6048421a108050c6154032c11651c1430c410a088050c6254031884865ce54484218898718c4048020a10805846154c40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 27
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s0K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/337+packedAt s0K5 (21654+(h % 337)*10) 10) % 802)
  | 4 => 2*((h/308+packedAt s0K4 (33554+(h % 308)*10) 10) % 883)
  | 3 => 2*((h/62+packedAt s0K3 (7056+(h % 62)*8) 8) % 144)
  | 2 => 2*((h/30+packedAt s0K2 (1620+(h % 30)*5) 5) % 27)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffff01ffffff03ffffffffc0fffc7ff1ff
  | 2 => 0xffc07ffffe03fffffc0fff03ffff07ff9c7e3f
  | 3 => 0x1fff80fffffc07fffff03ffc0ffff83fe78fc7
  | 4 => 0xe00000fffffff80fffffc0000fffffc3f80ff8
  | 5 => 0xffffff000000000ffffffffff0000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x24450a211c48912200b2cb4512c04a4429b0db
  | 2 => 0x48931452243922452c055522a55904a994562d
  | 3 => 0x110a269448907489555026a889aa9032c68b46
  | 4 => 0x9c2c58e8912240ee9a6980c30e34e703780db0
  | 5 => 0x1e3060f0e1c3870fe38e38f3c038c623ff6000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40519
namespace PEqualNP.Outside.L_meta_40519
open PEqualNP.Outside.L_meta_40519.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xcc32
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
  | 0 => 0xfffffffc0fffffc0ffffffffff80ffff1ffe3f
  | 2 => 0xe07f01ffffffffff0781e07c0fffffffe493ff
  | 3 => 0xff8001fff03f03fff801ff800fff07c0f8e3cc
  | 4 => 0x1ffffc003fffffe00000ffff800ff03f0
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x220a100460821040188a228462884a4a092615
  | 2 => 0x491462c88514c18b0320c868853194b46490ea
  | 3 => 0x8526b55123a856d568497b2129da4706b8e34c
  | 4 => 0x1658d9a24a0e9b66b5ec12424e6ce218df03b0
  | 5 => 0x1860e1c38c30e3b8c6719c7380708420f6d800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40519
namespace PEqualNP.Outside.L_meta_40519
open PEqualNP.Outside.L_meta_40519.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1030205030050022dc31ef20ee21ec21dd30de31de43dd43de32ed20df30dc32
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2300b228a411d54cc298a4a1c755031
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/18+packedAt s2K4 (192+(h % 18)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s2K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7fffffc0fffff03ffff83ffffc0fffe7c7e3f
  | 1 => 0xf81fc0fffffffffc1e07fc1e07ffffff9393ff
  | 3 => 0xffe000fff03f07ffe007ffe007ff0781e3e3cc
  | 4 => 0xffffc007fffff8000007fff801fc03f0
  | 5 => 0xffffff00000007fffffffffff8000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1082880460822100622880a231484c94242615
  | 1 => 0x224511488514822c0c832414429191689190ea
  | 3 => 0x5149aa9123a82d55a125cac094ea460d62e34c
  | 4 => 0xe5963ce24a0eb79ad7b06291273ce431fc03b0
  | 5 => 0x861830c38c30c6e319c67319c0308041db5800
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaacc888888eeaaeeaacc888888eeaaeeaacc888888eeaaeeaacc888888eeaaeeaacc888888eeaaeeaacc888888eeaaeeaacc888888eeaaeeaacc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40519
namespace PEqualNP.Outside.L_meta_40519
open PEqualNP.Outside.L_meta_40519.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x644058b00018a15608070b02a5010c72c7ff32ff21fe32de31fc30dd30fd20fd41fc42fc43fd43ff42fe20fe42fc20ff41fe40fd42fc40fc32fe30fe21ff40fd10fd31de43de32ff10fe41fc21fc10fd21dc32dc31ff43fd40fe43fd32ff30fe10fc31ff31ff20dd43fe31df30fc41fd30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8400c2844001c05644000dc000050900048081038040014000888000000102001540c700000004801640c0050008418087444181c0450080c080058000c133a86a157d5031bba8a415e53102bea78857540329f2a0415d538833a86205754c42afa9a415d53c86bea8195794f41afaa46376511027ca8195754c41baa88415d500c6daa5a0db94840aeaa0655c5250ebca5985b94b41eda82615e5310e3aa818d754c10afa98439d43d0abea8984f95221ae29a415e510cabaa7a15794431aeaa2613d540433a87a0db94810aea846574514827ea8904f55032af290635c524c2bea6a157553309f2a0213e540c6baa6205b14910af298215c53486b8a2985d94742af298855c53506baa7086795032ae29a215f53486bca7205794f21af29c433c54482bca7a179484219eaa0419f5450f3a872047550329e2a2216f52442baa7184f55321af294633d54cc33aa8194fd5110b6a90815c53c433ca818e755330af28c875f548cabaa818d754f40ae298437551d0abca7a05754e40af28e619d43506bca31957d53309f2a6615d53082b8a7907394832ae29a855d5090e3aa99857d4d10af298415c5150eeca2105755243af290653e54c867aa910d755231cf2a6615e530c2bca620d754231af28c635d548caeaa2205754e21af29c215f53506bea0a1cf55031af29c41d6510c73aa818d754f41afa9e415e528cadaa4085794a43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x80002008060080000000f0042028000000009398b548c65661d523287596540c61d64145308759253883154354742a31894350a1f6454231c350d52102946150d4187592518ca54615513087d91508ca1d6414d2187590524c21d6414c21c550d511021d6414f208759053c42596014c2187592528c61d6595032c350d52d064c625513087592538421d6494c30
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/23+packedAt s3K5 (768+(h % 23)*6) 6) % 48)
  | 4 => 2*((h/65+packedAt s3K4 (3618+(h % 65)*8) 8) % 134)
  | 3 => 2*((h/36+packedAt s3K3 (988+(h % 36)*5) 5) % 26)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffc1ffffff81fffe0ffff83ffffe78f1ff
  | 1 => 0xe07e0ffe0ffe1ffe1e0ff0f07fc3f83fa74e73
  | 2 => 0xff800ffff07fe1ffe00fff007ffc3fc1c78f9c
  | 4 => 0xfffff8001fffff000007fffc001f80fe0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x20800440004000022100111100449080810a5
  | 1 => 0x49149488652830960c8690a22a4290b4a34652
  | 2 => 0x85252910a351032ac10b2a044ca82685458b18
  | 4 => 0xd659ce254a1d55cd77a1888977330319f80de0
  | 5 => 0x18618c398c6199f199cdccce06220421f6e000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8eaeaeaeae8e8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40519
namespace PEqualNP.Outside.L_meta_40519
open PEqualNP.Outside.L_meta_40519.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0xc01470c00810000130042400411c008014d002000ff42fc20fd43fc21fd42fc40dc31ff43fc32fd30ff10fe43ff21fe30fd32ff40fc43fd31fe42fe31fc10ff30fe32fd21ff31dd30fd10fe10ff41fc41fd20fc31fd40de31fe21ff20fc42ff32fe41fd41df30fc30fe40fe20
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2617f54c42fca321df54e32bf29a21de51cc2daa4085794e40efa16617d53083baa118f70c831fc98061de31842faa2215754c20beaa263ef21887baa620774c831ee18c41df30842fea818df94d20efa1863dc31d03be65985f54642ef90e615e53082baa118df95130be28a87df53442f8a2987750b30ee18843df540c7b863905754e40bea8887dc31887bc87997e84010bfa9283de31c86faa5a0df94020bf288437d50d0bba61085fd4141fd88421df4350fbe42987750a31bf2a081dd54cc3dc8499778c410ef98e61df428c6fca420f7cca31ee29a83dd424c378a88877cc930ef98a61bf41107be84985f94621eea1a657d510c2fca4107d50441dfaa221be41103da4010770c630ef98c63ed4210bbc64985f14930bfa9a417e51082fea790ef55321fb10a217d53c87ba83985714530de20881dd438c6baa790ef90d43be296217c540c3dc8510dfd4132bfa82637d53c82faa520df94a32f7994657e54c83b86220770c530bf28487de5310bb8a6885f55332f721641dc41cc2f8a8995f54e41bea98437f54ccaf8a2a17714031bfaa441f920082faa5885f55221be29a83bd4310efca0185714d41bf2a0615e510c6fca5a1f794031ee20c63dd414c3be600877cc120beaa0437c54083b882987795330bea8487df30083da8499770c730deaa021ef324cbde4210df14532bfa8243df30c42f8a6087790c31bf29221dd418c7da8410fdc4210bf29c83ee52102faa59877d0431ef18841ef21c83b86290df94343eea9c217f524c3ba60105f54843eea1e61bf41906fea6a05fd4a10f6a9087de31482fca010ef50842ee98241de510c6dca421df95041be2a463bf4210b7a84a05f94c30ef292617c51503da859077cc220bf29481df51cc37e84a05f94b40ee98021fa40102faa8904f55010fa90a217d52886fca218dbd4910be29e43dc310c3bc63885f14f20f6292217d54c82fca9085f55010f7190657d538c3f28020774c310ee284637e5190bbc83987794b30ee21063df4390efca1a0df94c40af29861df528c7b865985f94810bea80877d51843ba86985fd5231ee988637f54cc3be86195f94031ee99065dd328c7bc8318df94230eeaa063dc21cc37ca8087b54840ef20a61bc41903b8a818df54031bf284817c54486f8a0a1dfd4530df212857d538c7bea918fb88420af298817d520c37a82a05f55031ef29c217c524c7bc6310df54f41dfa1c877c54c43dc40905754e30fb20883de520c6faa2105f54d20faa0e217e53d07d842105f94840ae29a437e51902f8a6105f94e20dfa0e81df438c6faa6215f94a43efa96617c52842faa3985f15130ef18c41df544c2fea9187bc8020fb90c437f544c7be86987714530bea8665f710042fca3a15f95010bea9083dd32cc3f440105f55321fba0a833e54042faa020d794f41
  | 1 => 0xd53882f8a9197b94b41efaa6617f54442fea498df94821efa9063de310c27ea8885f95043df2a0415f5350afaa5a077d4530f6908437e548c2fea6a17750c43ee98061dc31c87ba63985f95132be282637e51883bc6298f710330dea1a855c53c42faa4085f54c40af29e437d508cabca6215f54221eea9e836e52043bea6a0fdcc531bea9e85dd51cc2f8a9085f94a30beaa441de53d07bc62207710130beaa621dd314c37a8220df15032efa9a85df420c7ba8418df95221bf294837e500437a8520df95330dea1e857d5490b7e8520df94032bea9c43ed52d06fca598ef95321ef190637d52d0ef8a6887bd4910ee2a2617e53d0b7e8621df94743ef98863dc5350bec6218df95042fb082217c54ccaf8a4086f55032bea9a43f651082baa6205f94c32beaa6637e518cafaa9195f15221bfaa2417d52cc77e82a05f54f40beaa2657c54042faa9985f94042bf29e21f521c42fca1215fd4540eea1e65de508c6fca4195f94c31f690e41df30443de8521774c110ef206617e53c82fea8995fd5321be28285f621087ee8320df54a40bf28c61d6510c7dc85197710431bfa8a41dd410c6b8a6887e44010ef18a21f5310c7bca518df94843bea8c87de514c3bca918df94342bea8e41dc42cc2faa3a05b14910eea0661fb10443f680a05f95020bf29843be41507bc62a077d42319f2a0417c53503bc6320770c420bf28c83de404c2fea6105fd4143ee21463dc424c3b862906fd0d42bfa9c417f53506eca2106f50040faa88417f54c837e87a15f14d20b6a90877d5090afaa920efd0b40eeaa261dd404c2f8a9107710c32f7a12857e54883b8a690dfd4532bf28441fb308c3bca620778ca31eea80633d54c86fea890fd94440ee188217c54086faa521fd50510bf2a221df320cbb863885f94442bea94417e518c7da85197790431bf28865de4310fbaa2985fd4f20b7290817e50c86fea4887b94843bfa9621dc434c2fca890df14d42bf29c857e51cc3da8510dfd5210fd180615f53507dc84905f94210bf28821f521087ba8618dfd5221ee2a661f510043bea690df94c43bea80857c51483bc64995f15120eea98857e54c87be87195fd4c10ef298417e54cc6faa8185fd4943ee21e61bd41d02daa4207755231ef2a0637f53886fca221d794631eea9841ee42086fca220fb54810bfa90217d5490fb8a3985fd5010bea8e857f540c2fca710df94b41eea9e43f551102fca5987d90510fd982617e540c6f8a998df14943bf29c81be40502faa3997bc8520ae29a857e51103bc85987710e31be282837e50106fca6107754a31bf2a4653e54c86bca3985fd4c21bf28e817d508c6eaa2105fd5021f6a12417d53903bc8518fed0240bfaa4657c54c83bc65985f55110bf2a2637d54486f8a898f790930bea9e21db504c2fca021df54440bfaa
  | 2 => 0x148a816299e04c826188f00118a1080000112510020381000812000160980201826030d2058147e81e0012979864428f208838540061da0a0381a4680009802168140c0a4018820581c01808120d6000000380631806018103880a3a8302602009acc0080e2180200000040000100400092000080a00a0001404000c28020008c14800088000080e010740aab8021001a0380892e000960000e0101e0080800000000001b04c03000060040380a03000170fc3114e000000000c0603000054108025b00e0681a0005e018022f8000101e01800000001202817014000c00c8a200030000080000602816130be0f00a0481c0281e048660001a000180e0560101a130000001e000800e0c6018c6d0000008500b0100a8188486609196018002a80c00042020d60203201800028291f0f4008000c97c020060a064468220c000018540000c3e0100183e240000382201078aa12e074ac036fd0a429f2a0657d5390bbc439877cc230deaa041dd520c7bc869977d0330aea9e83dc31443b862a077d0f30aea80637e508c7bca790df95032bea88657f53c42faa9187b48520bea80655e53883ba6110770c640aea98857d520c7bc63a05f54e10bea86877c52506eaa2206fd0040bfa8a85dd324c2fca120df94a31df20c817d518caf8a48877d0130ef98641fb20483baa6085b54b41fb20e21dd30c83bc6210df95231bf290637e5290bbea4985f95310ee10a617e51c82faa9087788530be292817d53042fca6087714a31ee21c657e50103bc63905f94232efa9e21df504c2fca690dfd5331bfa8a877f53842fca721f70c9309eaa0415e53842baa7085f54630ef18c61de544c2faa9205f55130be29a43de53042fca110df54743ee19463de53882fca790df54021ef18261ee21883dc84215754c10ee292617c504cadca5a0fb88521dea16817e54482faa8105f94f40ef994655f534437ca8195f94732bfaa041de53902fca1995f54d10ee290637c548c2bea7885f14c21bfa9a217e510c2eca2206f50841bf29621df41cc3baa5986fd0240bea8643dd53902faa620df54a10f7904417d51903bea018dfd5032be29c21f721486fca9995f14121ef99063ec21883bc86985f94e109eaa065de43cc3f641105f94830ee296617f53486faa3105794c10ee218637d540cafca810df54910bfa92817c54c86fca198df15330d6a10857c53883da64195f94a10ee90e617e531077e8420df54e20beaa463f621c43ba42987790e31ef18e61de31487dca4087715231eea92617d50cc6faa4205f54a30efa0c63f7318c7bc8418d7d4d21bfa82857e5310bbe82985f54241bf29085dd53882faa1a0f70c610ee29e217c53c43be60185f15110be29c43de314c2f8a818cf15110bea94635
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4548823d65950329d98452042da60150319758c52042d66115031c7151434c25d60d4d41b5987420c6ad62d0740cb50a5110a3d6494821cbd0d5210ead62d06418fd9541106d461551309b58b548c65d65d0c329e596100434d520c440b658031c425d6014d419799631487655188420b5987528c65d6510a31c7953300432d52104409758c528432d54084209718d544825d63940418f596540425e639432197d8d5210755510c4209b58b530429d6414231d9547200825f658c6409798e50086766195132e350d424cb555354420b358b51cc29e640cb30c7d50314431d54d0c32cd55251082766114c20b3588430c74e5394810d5946311025e63943419758f51502d9600c64097994428c66d6590821d354832cc32d544c8329b58a54487355444010b398b51cc25f654c0309d58753083596014f10a7592528c67b6055121a7590320c6d66110130c718d540cb1e540c4109798c540c2cd6215330f10c5210867661152208f590528438f6350842b6980214c34d52148318f596540825d6394b10a7590500c65d658c4409798e524430d5350842b6980520c6d561d0831d3d4a528c65f63553209798c54086ad64c8421d350d5210e7765484219b588540c71f5414d109b988540c25c6154c42ad58742106ce62d06319798e50d0a776544010d5d8d510825e63d5020cbd954210a5d60d4d42b658352cc3576394420d3548524c31d5494f218fd9152442ad62d05409759741cc31d544c832c795031c863e6494b10b3988404c25e65108319798e54c425f63546409758f514826d659481097185539025f658c420a7990320c6d9608c4109b994524432d5454810a7191514c25d6314121b6980414c25f65507308fd91518825d6314940c795153c873654944208fd91534827b65440109719521cc26d62151309758c54482cc6350a32a7590324c2d96015031d3149304427661d4c20d354d4210a7661150209758c505067960150219758e50d0ad9609513097596319023e6415020cb150524425d63d4542d9549100425d658c4209718d519025c6154c408f99053c874e4354843b5984548c65f6354642d954a511025d650c640b658351cc2d661908319b189544c3555354440d5d44314825f63547409758f548431d53d08428fd95401025f63550219758c548423f655084297997434c25e6514d2197594430cace62d0730d5945300834e528c44097d8d544825e6394042a7590520c78e53508429758e500865c6354620979865310a5d6315021a7593214c2ce6210d3097d8d52d023e6414c20cb15352442ad649084297996404c31d5410c32c7550544c25d6054c10a7990520c6db60545309799431442d9600c52097d95428c65e63d481097d8d544c69e6494a31c7551300423f6454d1097594318835653544208f993538863d6414f20
  | 1 => 0x82db60549309b588505067960150318f590504865d6394241cd546411032e5454810d35885350b1d5410f309719541cc38d4210a31b3588404c25e6314c109d987548cb565394420d554e511023e6414c2197d9542cc26e6295310d55463110355514c020d314f524426e621533197d815310b1d5494c10a7990500c6ce6210e31d394d52d065f6355121cb552320cb665294440b5185524c25c655093097d8d544ca5e6590d329798c530826f654c8329799442cc31f544c110d554730082d96014b30d394b30042cd6210d30a7191524c2d76154930b658031042cf6255130ab1894350a5d631502097597414c2746155130a7990328c65d631522097195428c63d6590440d354a31102d661cc3108f993520425d63153209718d54c42d66114a31c715031442d9600c620d3149324c356510c430b658354cc25d63952219dd95411074d5354b419b58a54443546354440d5546310838d4210b309798f515025e63d4a10a7993214c2d960945308f590530865e6394a419798c505065c63549109d98754082ce6210f30b558440cc25f654c020b5987520c757510c540cb54a411023d64148109798c540cace62d523197d94310431f5495231c7552530829e640c9308f593520431e544c010d394831042ce62151309759730043546394440a759052cc25e6395110c715053443576354440d354e52d067561150309d185544825f6354742d394d520425e65cc1108f590530825f63549109b189544425d650c410c7d52314423d6494b10c7951530425e63d52109d984540c26e6215031cd15241443566114f109b98b54042cd6210e319718d51d025f63551109b588540427b654c03097195434c25d65c8530b358b548c65d63d5221cb15142c825d6014d219b58b540436552544409d984540425c6548530cb151428caad64c85209718d51082d4614c110d5146314c2ce6210c319b98854082cd6214031e3508420c63e6494a31975805350a5f65504319d584530829d64149309798c525031e5494c20b358840cc2d9600c540c7d533044355510c440d5144214c25d658c43097d94318834d520c8318f191534425d6315321d5147214c25f6054f41b5d85544c29e641493097986538825f650c640cb95252042ce62142318f59053c865e63152209e980540869d64d47309b588548425c6550d328f99053c826e62153309798e548865d6510930cd544411031e548c4109b98a524425d6094f41d594e511025d63d5220c7d5353442cd6210f309798e509065f658c4108f990540ca5e650c521cb949429069e64d4a31b5987548c65d60d4d21b5586420c65f654c0109759442cc25f650c440d394e521025d63949109758e529065d63d5010c795231c86756195132b6580520c72d54480208f99253442ce6214031c795253c872c52509409d58
  | 2 => 0x6548020b3189544c25e63940419799453442cd6210c3297994404c25d63940209d9845050b565354440d3d4f524425e63d5221d9584524431d54cc0109b189534436551084209719542cc32f5414910d3148314431d540c7219718d54c823e6494910c7553320ca3c64549109b195424ca796014c218f592524434f528c5109b988505067a601503197996314434d528c4108f993530825f635444097596318823e6414a1097d96318831c544c110d354852cc25d6510c3197d95214c33551500409b98b548c6cd62d07309798c548435553944209d185534832d4254042cd553100426c655092097195304425f658c440cb151424ca5c63546429bd89544c31d5410c31c795231083954110431c7152314435661d4f109758f54c863e65151108f99054042ad64c87209b988548425d63948219d19521442cd6210e329798e500425c6114d109718d52d026e6214c109758e544875451d0530c7550310431d5454f21ab5932188756510c730d314c524425f6354442cb50d5210e5d6594c209dd85534825d63d48109758c540423d6494d10cb54d4210b355454420d354b300425d65c87309bd95200825f6355310b5987540c7d130440109798c544825f63547209e980530865e6314121d394d521025e6315020d3d4b304425e6394d21d3949300425f654c4319798c520425e65cc5309798c54c872d5250040979875350b5661944318f191518825c63544428f590530425c63548419798f514825e65c853097986531025e6194c20d658353c42cd62d0431cb552210838d42109309718d51c825c65508319b98b530425e63951219798e500826e6215130d954b100434d5394810b358a548c65c6550530c7550310831e54cc020ab58b411072d54c80208f592528c66e6215230e318d4210a5c6354742c7551530825d63940429798f540429e6414231b3588540c66d62953109b189519026e6294d10cb151424825f63544209798653902ce62d043197997414c25e6314142b6582524c2d56110130e354d4210a3e64948219bd954210a6d6215331d5144414c27561150209798f54c863f6550c43d354e521023c6454d20d5144314823e6414121b398a548c6af65508429d58754083356115110975825310b4d520c41097596430c67b65500409758e50c866d6294d10cbd53524425c6355121f48c5100427561d523297d95320cb4f520c5109b58854cc25e631532097d95420c74e524ca319718d54086d960147309b98a544c66d6588420a799321cc2cf6254530979845350ad66114831b3189514c3365454420d394a31042e561908218f593530423e6414930c7153304429d64d4a3197594420c6776155130c7950310831c54d4d1097994424c23d6414930c754d4210b1c53d0d429799741cc26e65c8520d394e52d066f6254640c7951530
  | 3 => 0x2c910080a27c000000d000010c4000000105007000153e4003e84327402008000005205400030090e0097c40a3b801000001e08707023064030c0060000819c070006f028070f1760a8001740000c000100f025a0024b100005030090b4053f807020121807f00018220390540200c1300001008114406700415000140144f030090bc04010002bc300006a0000b12401000150140d0100903815018000480400078000000dc0618560000052201e01867034000317700404000a400c20004271cc00000500b01c10c2d000010a81513c0a00197004080b801004018340d00002014110101a1d01a0041f0080401007008000542300cca77c2809818008041500704c1c0040201800000000001501c12070122240018c1b26015008230000304c0e0000f0300704c160080005400020050902700c00004000143004444004890b0040287f0005f8800f00d3200d3948c0101c772042d00000000000841502276611523097d8d518825c635511097185538823e65d05409758e544425d6594c109b58a548c6cd62d05308f992544427561152309d195414427761551208f99053042756114142cb951428875463944209bd95210874c528c5109dd95310c71d5454c10b6580214c23d64d4c20b518530c425f6550c43d9949511027860551219718d52c42d661103309758e50d0764528851097d8d52c426e6295231c7952530425e63d5030c7551300831d54153309b988520425e63d52209758e500425d63942429b98a54442d96015330b6d81544c32c5450821d5144315029d64c8730b398840cc25f650c420b3588508c65e6314a10cd547401034d5354840d5946310831d54cc0209798e520874d53908428f59353c871d54150319b588548c25d658c4109758e508865f65487309758c5050b1d548c721d3d4c524425e63d4542c755231042ce62d0530a7590328c69e6414b3097984534425c6154c209758f540829e64d4730b398854cc23e64d4f21cb552520426d6215030d314b3044356518c630e3d0d428cad661cc11097d95414c34d524c010d5947300831d548c42097594310825d650c440d5d8e51102cd6215130b3988540c66e621503297d8153c874f524c1109798e5090a5d65cc0209758253c865e6394b10b358b418c74d5354810d3948311029f6454930b658231c425d65d0431cb54b4010356510c4409bd89534426f62551109718d511031e5450e319758e54c435a534c0309758f52843655148020c7951300826d6295131a7d91514c25f6054c108f99052042d960105309798e508866d6214c109798e534435463544209798c540429d640cb309758e544c63e64d4c109b988540423d64d4e2197d95424c25e65c8730d5944310827b
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x5006283048040002404140100041cc000000114010d44002b000040000c1aa8b108618e0d54588540c788aa2608802186551600c410c8cc428e829850c7550d424cb06b22a429661435d2524ca31a1ce9a94a518e0d64548524c306b22a41906391148614c110ca4c2b00a78860d5458843cc286b9ca8a1443925496014831ca0a2b0062a050c72550544c294b80a8a10438599051c8530a18eca9a842160d54588430cb2828ac018a41439d95350842a1ae62a28410e1954580540c70732a8421463431c55350842a1ee0a9a842160d65508420c686b98a8a164143dd54210a31a1ae8292649850d731494250306b22a429063835954210b30a28e2aa0a89860f5458a548c706b26a529463435ce5250a41a1ce5aa4a918e0d54588544c306aa2c42a66192549600c410a1ae52a28718e145418530442863a2a42926183591520cb30a88e2a90a49860d65508424c2863aa8421261165c065508318a8e2b28849850d72151434c3a0a926088021435cc5450920
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc2000c05641c5521493080c875954210930a0481595421093080e879954210a31906819d95350842a04815516215130
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s4K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/274+packedAt s4K5 (21627+(h % 274)*10) 10) % 801)
  | 4 => 2*((h/281+packedAt s4K4 (29678+(h % 281)*10) 10) % 781)
  | 3 => 2*((h/39+packedAt s4K3 (2744+(h % 39)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s4K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe1fffff07fffff81fe1fc3fffc3ffffd18f1ff
  | 1 => 0xfe07e1ff83ff87fe1fe1fc383fc3f07ee74e73
  | 2 => 0xfff801fffc1ff8ffe001ffc03ffc7f83078f9c
  | 3 => 0x1ffffe000fffffe00003fff8003f80fe0
  | 5 => 0xfffffe00000000ffffffffffc0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x202080110001000022020048880492100810a5
  | 1 => 0x44914222194a08160c20c41114412168634652
  | 2 => 0x8852554428d441aac1116a8226a84d0b058b18
  | 3 => 0x1d659989528752cd77542204bb320633b80de0
  | 5 => 0x1186110e631864f19999b32702200843d6e000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeae8a8e8a8eeeaeeeae8a8e8a8eeeaeeeae8a8e8a8eeeaeeeae8a8e8a8eeeaeeeae8a8e8a8eeeaeeeae8a8e8a8eeeaeeeae8a8e8a8eeeaeeeae8a8e8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40519
namespace PEqualNP.Outside.L_meta_40519
open PEqualNP.Outside.L_meta_40519.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x1093000000020000050810401427406c7003006000fc42fe21fc30ff43fe41bf40fd30fd40ff10fd32ff42fc32fe30fd31fc41ff21fc10fe31fc21ff41fe32bd40ff30ff31fd10dd30fd20fc31fd42fd21fe10ff40ff32ff20fd41fc20fe40fc43fe20df30fd43fc40fe43fe42
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2617f525077e81987790b30bf29687de324c2fca190f714930beaa2657d52886fca3206fd07409eaa041bf32d027aa8185f55021bf286653f544cafea810ef94d40bf284657f51502faa5a05f55241ef986417d544c2bea6a0dd94420bea9a437e50103ba61885f94443be2a241bd40083bca3987ed0140ee10e61da404c37a80987795130be29a81bf400c2fca5205f54720df20a81dc404c3bc87986f90c42bfa9a43bd54882faa32077d0e31bfaa0637e52c43ba87985fd4532efa06617850486fca420df54031ee980217f52c42fea7905f94643bf28c85bc42d02faa7105f54830bf294837f54c837ea7a05f55010cea1887fa40102fea9995794e10bea8c213f544867ca9184fd5131fc880217f53483ba80985f94641bfaa243dd514c3f620885f54d20f6a1085dc438c6baa6087ec8220de21c837c514c3ba43985f95020fb90a437d54483ee6298f790330df90a817d510c278a890df14d41aea9881dd308437ca9105f94030bf286635e53902faa221df55320ef298217e53483b887195f94632dfa9a81dd324c33a81984f95010bf2a6617e544cbde85215f54043ee196617d521077a8220df15310fc28243bd548c3bc64995f54a20bf2a08799404c3ba85986f8c540bea9e41bf50503bea3985f54f41beaa4857e51d03b6a0987d88710ef99065df53506fca8905f54e31be2a221df4350efca7105f15230ee19063bf40043de411077cc110fca80873d54903f281185f14b10ef98a61bd54842faa6216fd0310bea8885df424c37ca5a05e94043dea1a817c53482fea6107710d30be29e41bc215027ca81877d4b30dea0641de53902fca61977cc230ee984419f404c2fca120efd0210beaa4617c514837ea890df54221bf29861be53d02fca6885f15330dfa9281df30483bca9985fd5210be29c435c5350b7ca9185f54730dfa08837c548c7baa7085f15220be2a641ed320cabea6a16f15121bea9021f641106fea990df54c21be2a2657f524427ca9085f94743bea8e657d5090b7ea2a06f50842dfa00813d54883de40107750730ee98e61f710043be86195f94631beaa443be42502f8a0a1df54440bea92213c544c6fea2a1774c431ee20e617f50487be65985fd4d41de210837e54486fea790df94f42de29a81dd300837c80a07e90130be292637f504cb7a42a05f94230be282837f524c37e63a05f54642dea18877c53c42fca820ef55010deaa061ed52042fea098f7cc631dea9a817e5090bb8a9985f94843bf288437d518cbee21085fd4f10bf29485bd32d03bc82987750c43beaa0617e511037887a07b8c832beaa0417f524c6f8a2a1fbc8720bfaa241ef21086fca9995f95021dea0221be439077887215f94e219f2a4417e53843be8721f790c43dfa1681bc32502fea899770c730fba0c83bd408c3b8a5985f94810
  | 1 => 0xd214c2faa9107e50040ef984217d538cafca9085f14a10bf2a061bd400c2fca721d754e10bea86877e54c87ba81985f14941fd90241dd544c37e82a077901309f2a0817f5150ef8a9195f94b31be29e437c5250efaa2105f95042ef98863bc544cb7c87a05794c40bea80837f54882f8a090df55110bea8e857f540cafaa3105fd5231de2a263dc324c376a0a05f54331beaa263de524c37ea8995f94020bfa9821dc328c77281186fd0320bf29661be215037886216f08740aea98417c540caf8a8186fd0d40bfa90217b50487ba65985f94840fd20461bd54083be6110774c110df2a061bd21d02fca9105f94441faa0883f551083baa6086f90541df21c85dd524c2fca790f710f30bf2a6217c544c6faa998fd88510bf29061dc514c2fea9986f50f40dea9681dd53102fca4196f90b40cfa0661df31cc2faa7206f95010ef182617f5050afca010df94342ee218637d53106faa990d714d219eaa0217e50883bca7085fd5230fc100216d52042f8a810f7d0b30eea12617d5090efca720df94430ee982417d518c27ca8106fd0842dfa1887dd314c3bca7105f54e30efa1c65f820c42fea0a1efd0240f290843bd40042faa3a05f94043bea9683df54cc2fea8187b48520dea0621f7318c6bea690f750530bea9461f5310c6faa3a1df94b41f790c43bd325037ca2a05f94a32cea02617e518c3f280987714d41ef19661dc414c3be65195fd5232baa88415d538837865a05f14542dfa0c837e52442faa7a06fd0110df98a81f521c437a81085f55031ef19063df324c2fca6085f14132bf29043f74150778a2a06fd0e43bf2a4637f53842faa5205f94420bf28683bd40102f8a81077cc020ef20e617e53082f8a7085f95031be2a2617e500c7bea49877d4130bea8643bc42906fea710d714d41bf28c417d5290feca2105f14d21dfa0461dc53486dca4087d48421bfa9a81de52cc2fca218df54042bf2a0817d53d0afca6217e94043dfa1281dc424c378a4a05f54b30be2a665dc314c2faa7085f94231beaa621bf40483f460185f94c43fa88021de314c6fca0195f94820fda82433d548c2faa520df55210ef90e61be4250b7e87a06f90c41de21a817e50d0f7a83a06f50b40efa9a43bf52d03ba60185f94041fd98461ee4210b7ca9086f4c740efa0a617e5308678a8995f94730df28e81bf51d02f8a6107e88020bea88657d520c6fea2986f90841beaa2437d500877883a05f94621bfa92817d508c7f640086f50220fd906217d53083ec20885fd4d10ef28a617e528c6faa1a0df15221dea8a81dd52cc3bc639877d0d30bf2a6417c504c6bca7105f94842be290217d53c87bc42985fd4520be2a643be21d02faa921ef14f40de28e81bc52d02fea7106f0c740df21a815e530c37c64a05f95331f710a437e544c6faa518df94c40efaa
  | 2 => 0x2009a603012000000006c268027b80004004000340300c050300006408800000100480204888038000c0a80002600004058080284c088040405409084000200229016000010800789e068e00183c31800000023d0241100002000050bc0e002000a2008080000c0000e010001221a0a0d4020002d01e6d8a60400e0b80086800078002a002068001c01804802000020781e000ec0983c288080004a00036070480694a8180806006108102180a000000c00000010008280e8780084c0300e078000f87e518140680e0002833904478160f0020b8300100e0288606834000021a80000802038080600210802004dc01026020145c852010042800a050360007220802000064d05a0e0242f94e0300012802018020291c0003c00034001b00000e021100380202010098001a8001e028090160c8240100000224138121b03800028002e42180005804010001000e14000080a003000030000f000378de0f0140e8022f026050ad7e53903be42985f54a10bea96637d53102f8a818dfd5331bea98217f544c6fea8985f14e20dfaa263bf40883bca6107b88120bf29487bf4290bbc6518f7d0730be29221df300c2fea0a0f754730ee28e617d508cbb885985f94a30bf2a2217d540cafea6a17ed0240df196817e544c3b886195f94742dea92817e54887f240107bd0942ee990657e548c2faa4207bcc932fa90a217c524c3b8a8985fd5020ef10e61f6310c6fca110efd0020de20a81ee520437a84a05f95032be2a2437d54cc2faa710d754e40f690041df43cc2f8a6886f50120ef18a617e510cafea8085f55332bf28821be42906baa7185f54342fb90c437e50842fca5a06e50130de98a817e540437c83a05f94a10be2a663de53102fca2216fd0130bea9621bd41503ba869877d0c31bea8c877e53c42f8a6085fd5110be29843be4350efea910df54d10fd08021dd530837aa3a05f94d21beaa465fb304c2fea4a1df14d42f6908437e50902fca9195fd4c21beaa481bc42502f8a2a05fd5310bf28e417e53c82fca0086f54f40bf29e81dc40cc2fea5085f54f10ef21261dc5350bba61905f94e42efa9a85dc214c27aa9085794c10efa0261bf21d03de42907b48720eca0261fb10843bea2985f54b43ef21a617e51ccbbaa7205f14940dea0661be52503be60087754e20be282855e53082fca7a0df94831bea9087bf32502f8a2997bcca32de18a81bc43106f2a021df15010bf28487df30c42faa720ef8c740bea9c85dd54cc2faa1997e4c030df2a0417e53106faa120df94042beaa463f621086f8a9085f54032bf29863d
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x251082766114810c7550430c65e6314121c7d50438c65d6510c328f593538426e62148109d98753082d76155130abd89535025e6394d21b6195404c39943540439758f548834d53948108f19153483994150130c7551538435b53141218f590528427b6550040e68c9404c23d60151319b98853042ba60cc9409798f540831d53d0240a7d8d51d039a215013097195434c31d53d022097d9542cc27a601533297d8d54c425e6394042c7952538431943540439758e500832e54948109798e50906b960945408f59250cca776155120d694d300c2b86048740c754d401031d53502208f19531d029e6390140b6582544c23e64150309758f540823f65500208f191520c66d6214c109ed95100429f6454b309798f548825f6355320cb94b400434d5214930a718d21d02b96014b4097195424c25f654c832c7551538829c6350b40d594d510825c6354841c7553308c29c644cb30b6980434c23e6414810cd947400823e6495131a718d425039b50d0130cb949400434d520c831a718d21502d960949308f58054487595390040a71894310e5d65cc020cd945400831d53d0040e6501300839932501308f992544cb994394043c7953308c23e64d4e219758f548866c62551109758f52042b960cc940e6595404c2d5610c83197d95300434d524c010a7d9132cc2b960d4740e6105404c25d63141218f59353c86b761549409d98754082db6054930d6982539029c6448530ce552300c39b50501309758e5090a3e64d4c109718d52d03652154021c750d5010eba6090d40b5d85524c25c63551218f19152c42b56110841cb54852502756114c20c795330082776548421c7553300425e63150108fd95325025d6394041c715143cc29f6448530ce150504865e63152109798c5050a3d60d5121b658054cc25c6355320f1484214c3686054810ced50504865f6054c109e58054cca3d6494030a718d411063d6414e209e18154486b96010c41c794d400c26f6550842a7d954310f5a659013097597300436952c8010d354852cc23f6454f20f8181210871c5414d219798f528423f64544328fd95400c2f16108310b9d95210863e6494030ab18951502da60101308f994544cadb6054530cd551510831e54cc010b6593504c3994250130c7553308839b63501308fd9521d031d5314d40e6145404c31c5450d309e195404c23f6454b30a7d91524c2b96490130c7d50438cad461549308f590504865d6014d21e650130043c463484218f590504c71e53d00308f592500cb2d5210b40c7551300c23e6415020b6d81214c23f6454f10e6d85404c33551145408fd954004355514c0208f593530831e544c210c75515308399435013097d8d540863d6414c21b6592404c27461551209e582544865e63d48108f597400423d6595010ae58f50502796584010
  | 1 => 0x871f5414d21ce153504872d52108418fd91534869f6050c43cb54852d031e544c0308fd9151cc25c6354b10ae5804390a3d6494221d614f504866f65484218f990504871e54cc2209d984540831e5494c10a718d52d02b960147408f99352842da6590130e919121086b960d4b40e650130c831d53d00208fd9532d035a4354043a718d51d025e63951218f19532503a76448421c7952530825c6355021a7191314c31d535002097d8d544ca3d64d4e209798f548425e6314c209e980540c69d648c13097583534865f6354442e6cc5404c31e53d0010abd89515029f63487409798e5090a7765504419b18953442786054d219758c5050b1e5454e109b58b53042da60109308fd95215031e53d02108f994544c6ba6008540ced53504871d5410f30c794d400431d54cc210aed81215023d60d5131c794d408431d5410d30c7553300833b65501309e582534863f65500409719542cc23f65508428f19153442b46154d408f580544ca5d6395121d6d8f504865e63942219b988540431d541513097d95300823e6414e108f99250cc65d63943418f99353882ba600c5409798c528423e649402097d8d51c823d6494231d3149324c3e36048421b698e404c33a50500309758c540871d5314f409798e501063e64d4f219b98b548c63c64547209b189544c31e53d0020cd54441d023f654c7409bd89544426e6215031a7191324c23c654cb409b58b540429f63545408f990504c7555114730e6501308426e62d4c10ba18121c82b960cc54097583535069e648c130c794d40082b960085408f583544ca3e6414c21d658c504875863d412197996404c29f644c930e6185404c2b96094940b618121cc25f6354b40d394d520434d520cb3097d95310c65d631521097994534863d64940108fd91534433451505408f99250c863d6595020e6085404c2b9600c940ae980325039843501309719541cc29c644c4319d584540ca9f644c73097195214c26d62150109e580540865e6394020c795130082d96014b30d394b300426f6255130c755054cc23f6550441c7551300435651cc020aed81515029c6454b30c7951300433964141219758e509063d64d4e21ab189535029e6410130e6501300c23e64942219758153042776544010ae181215023d649432197d8d51d03655244010c755253883983150130a719131cc29f6354b40b6d81544c25d63d5210c7551308825d6314a10b658352cc23d65d00309d587548ca9d6490c43c7953300c36552c4010c794d408825e63d50308fd91520c65e65d0d30975805350a5f6355110e6949404c3e121c83108f19152cc31e53d0240a758e40502796508010c7152324ca3f6454720b6980414c27a6014c21c794f408833864d4121cb552520429d64901308f5905204398655013097195414c3555354420cd95
  | 2 => 0x6348540f148421cc2b96014f40c7152314c7555114530b6980214c2b960d4f40b6995404c23c6454910b3189514c23c65485408f19151cc31e5494e20975835350a5d6394010d554431cc29c63549409798c548825e6315020add85535025d63d5010c7d53534863c6454432bc18121c42ba6010d408f19521d02da60d0930e6500404c31d5350210cb551520425e65101308f191530863c6454f209e980540c27561d5020b658051cc23e6494021a7191514c31e544c220d9547200829c644c8329d587530823d6414e10c7553300c25e63943218f590504ca5e631502197d8d544865f63551318f593520426d65948109718d524439b43501309e982544867a6015331e6502304c2996490130d354d520423e64951218f99253486db604873097d95214c23d6494021d594e510829c6150c43d5547300825f65507308f994544871d53d02109798c540c25f6354910e6109404c29f6354940c795330842766114c20b958a21086cc6255130cb951520423d64942329798e50d079852501308f993520439832501308fd954310f1d544c210e6995404c23e64d4c209bd95200839962501309718d51c833a6454043c7153534865e6314810ce551300c31d544c0209758c540427b654c030e6501304825d63150209718d544439a51501308fd9153086cf62551309798f540429f6350740e6585404c32d52d0010ae582535031f6550c43f1d8d210866f654c832e68c5404c39b6050330e9484215029f6454530a7d8d415027a6094d21cd951510826e62d5010cb5494004399404c110e6501308825e63d5321e948421d025e63d5221c79515388354514c5308f590530823d6494d2197580535067b6054910c754c43d023c6454d21aed8121d02b96010c429dd95310c69c63508429d195214425c6548730e6d09404c39a41501309e580540cad96010c328f992500433554944208f992500ca5e6394021b6580438ca3e64943329758e5010b9a4350130cb149425031d5310c41d6d4f504869f6454730b6181214c25d6315220c794d40102da60d0d30c794f401031d5410c32e650130c426d6215031d9149214439a4250130c7951530823d6494331ae580315029c6354540d698d5010f9b6250130c754c4310a5d63942218fd9531502756115020a7191524c27661d5232a7d91314c31c5390541e6985404c3676548421b6580424c39b41501308f990528434e524c01097596530825d6394321b6580438c756514c0209d185534825c6354740e6cc9404c2b96010e418f596540c25e6314c10b6583414c33551d00208f590530423f6454d208f195315023c6454f10ce951401026f6254d109798c505067461551308f990538833b4354043c7552530425f6550530d614c50487355150020e6989404c25d6394342d698c504865e63940109ed81534
  | 3 => 0x5a9c001000b09802000d3084020f4b600050000002b001018e00642208429044008a80300c0005410000190151e15801000000180200026000040600300cc50083809811298101a8ff0501a19c06170120044e00c0105c09034080f42000c4008c19005e0024077bc00018010a80200c2400c016200153c100480a00635314030000d0542100009004090040116c110004206001004d100c0400016001a500c0a14811008120e40d02c001dab50080000c110080006c396440004c10368010000b001c001c3f13d7b09c070092f0203d018720c80004818014080241b03c001140a0000500002018070100d01c052b00610c37104a4008000a00001819000010001f2b096008080300000017014000f80004c690240e04dc5008038e41600000228240000000c001400000007024000480300809000010506b008040080200800000000a800004200580bc75515304355539442097d954310f355114740b6580430c63e64d4e10ced95408c23e6414132e6545404c25d63d5321b5185544c23d64d4c10aed81525036551480208f992508ca3f6454b10dc18151082b46154940c755253842d960d09309b58b548c69c63507408f990540433a60952309759653042d960945308f990530425d63148108f592500c79b52501309d984540caba60cc5408f59250083985450130ce951408c39b6050130e6d91404c39b5450130b6983414c39b5150130c7552530825c635444297594430c71d53d0010a719151cc27a601502197d95424c36451485208f992500c63d65d0020e6c85404c31e5454c109798e50d0a7b65480209dd85544c25c6355120b3d89514c25f654c0308fd81540425d6394021e64c5404c398635013097d9521cc23d64d4a10e6d95404c3595350040e6485404c27960150319e58054cc6d960d5330a7d8d425033943540438f58154042d960d47309718d54c425d63d4a109e980540ca5f6355120e6549404c31c5390942a7d8d42d025f6354b10ced93504874d52cc010e6189404c23e6414c20aed8153502d96010530d650d5010ebb6550230a719121cc27b60551218f992508c69c6350540ce195404c2d96008530c754d400423f64549109758c50506796014c21ce990504865f63548419dd85534829f6448730d914921c431c5350d40d394e520429f
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x83418000047050250088020020202723810c00080420c50008010808600680020000f0e10d81060011b1586d516010e31932e031a42a050c73548525028a38aa629a81261d92150130d4242b0042a049970191214c28b38ea821c65261d95150130a18e4aa0a89861464145314c2c5b92a2a0261491d52108540932e8302429858872545404c360318c090843c45445150130936eca8a809851b7550d5010e8cb82a898021865516010c31a28e2aa0869860c64149324c30caa2c02a661a81906048421e22a2a02601051474544514c22cb80c6aa0438518c5150540a18e4a98a6a061b54580438ca4cba4c010a61865916314121a36eab12809849b76549404c30db26c7a824364dc55250130932e630242a059371595404c2c5b92caa0261865516010c32a30eab0a80985147354451502c838ac4a026164dc56250130a18e8a90a49854472544514c2a23aa4210a6146dd56150130a1ce5aa08718d8b72585404c286392a821a61621c96150130a36eca1aa021e195358053d038928a8098041c2549404c010a48e2a90a4a061965195404c292392a228a818654d6010c41d12c4312809859071595404c28a38aa82a261461d52150130c30caa1a809870a52501300424dbb242a0261e04842150130872e0322a610e9161185404c24cb9cc010a818654d6010c42d8242b00429851b7050d5010e4c3b2a4a0261641c55250130a88e2a90a4985187250d5010e8dbaa42a0261621c96550130e12a429280985187150d5010f06318a4a1281461d56250130
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x210004004000100700b00825445150130a1281d516010e32a80864842150130a80825846150130a08825946550130a10815946550130a0a82d516010e31a08865485250130a10865445150130a10855846150130b00854842150130b00815485250130a80815886250130a08855886250130
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
  | 4 => 2*((h/265+packedAt s5K4 (28652+(h % 265)*10) 10) % 754)
  | 3 => 2*((h/49+packedAt s5K3 (4165+(h % 49)*7) 7) % 85)
  | 2 => 2*((h/18+packedAt s5K2 (840+(h % 18)*4) 4) % 14)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83fffe0fffffff03e1f0f1ffe3fffffc40f1ff
  | 1 => 0xfc0ffff03ffe1ffc01fffe1ffc3f81f87f3e73
  | 2 => 0xfff03fffc0ffe1fffe00ffe1ffc3fe0787cf9c
  | 3 => 0x3fffff0001ffffff0001fffc0007f80fe0
  | 4 => 0xffffc000000001fffffffffe00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa041222208251100b05821324264a8a44050a5
  | 1 => 0x92284419248202c00a15204a40905501b2652
  | 2 => 0x10a48884869002554200944128825411858b18
  | 3 => 0x5acb3129241d559a753a0111d3301866e80de0
  | 4 => 0x630c21ce38e199e399cce9980220618776f000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8fce8e8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40519
namespace PEqualNP.Outside.L_meta_40519
open PEqualNP.Outside.L_meta_40519.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x8c02811640012ff1677085843c1005442880ec0057007f88407ff4200ff04007ff43017fcc809ff5100ef50009fc51027f54403fd40027f54c03bf4000ff0c005ff3100ff94007fd4201ff10401fd3200ff88001fe31007f08409fc5201ffd0403fe4001ff10805fc53007f4c403fe10027fd4803fe30007f8c803dd30017f90c07fd41027f94803ff5001ff90805fc3101ff50c03ff2000ff08001ff21027fd4c05fe5301ff95003fc50027f54803fd2001ff15007fe4100ffd0003fc4001ffd5003fd5000ffc4005fc43007f48403df3001ff55003ff30017f0c803fd3000ff44009fe51
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xa24213ffc432103ffa851901bfd10084017eb146221ffd06320057ec890803fe628c405fe21c6206ff540210dffea91881ffc208c80f7fb1a6402ffcca3104ffe8610817fe510840bff28c420cff5012102ff8c01086eff648c441ff8846415ff50f210fdfaca99047ff4188417fea844202ff94e31107f8a119047ff438842ffe1026200afd91320f7fa849900bdf304c80bffb146207ff9802103ffac610817ff64884037f3026202ff54d3107ffea29081ffc63c8401ffb126219ff59531017be6098817ff658c40fffb0c640dff90d2103ff8659081eff65c8425ffa9c4214ff14f210f7fcc89900bff308c819ffa824202fdcc631017fea71882ffe60884075e322621dff181320bffa4098877fe204c837fea0c6215ff1072102ff8a31886bfe608c419fe9024202bf58e31007fc6290883fd108c819ff0824221ff9063203ffaa51908bfc518c80bfe324621aff582310eff8a09900bfc434c43dffb226407ff993210d7fc211880aff634c4417eb046402ff8c13101d78c89901eff6408415fea98420eff5912100df8c098863fc644c40ffeb284207ff90a2110ffaa919077fe404c805fe1826202ffcc6310cffcca9880bfc308c40bfe0846200ff98532107f88119033f71048445fea8c6407ffc832109ffa219082fdf3088431fe2126218bfd9131017fc609906aff608c40def9804211ffd5221097faa71086bfc408c41dfea1a4207bfd942102ffec11080bf7314c401feb146207ff081320bf7e809881fde324c80fff2946407ff109320bffca09881ffc52c8443fe2a4641cffd4a310dffe8518883ff508c80dff200420eff105210bffac09882ffe3088401efb1a420bff90221067fe209086bfc508c43bdfa026419bfd953103ffa8590877fe504c80ddfa004202ff94d3202ff8831882ffd608840dff1804207ff4cb21017fe611885ffe204c41d7eb224200ff4c72109ffe819081ffc420840f7f3146407ff0822103ffe641081ffe424c839ff32c6207ff08021017fe629906bff508c421fe21c4207bf18f2103ff88510846fd6488417ff284420fff19521107ba611904ffd50c8441fea04640dff98d2102ffc831881ffe6408445ffa8c6402ff10d3205f7e811081fff2048423ffa144205ff19421025f8ca9881bfe5008405ee1946202ffcc931017fc871904aff658842dfea9e4215ff9532109f7a819080bdc318c831ffaa26207fdc8621067fa609080bfe534c417ff104421effd513202ff8c61081fff528c841ff0846407ff482320c7fa829880bff324c81bfe29a4207ff8802102ffec01085fff604c43bfeb02641cff546310edfec099003de314c405ff1946200ff4c521025fcca10806fc604c8077e3244204bf1952101dfcc91881fff21084097f32c4202ffd4d3109ffa619081fff2188439ff2946218ff90931
  | 1 => 0xffe654c83dff2a26407ffd8f2106ffca69081fff64c841fff32a4207bfd8021017de6499076fd604c817fb8844215ff907210dffe831886bfd508c40bff28c6217ffc813109ff82190817fc4108427fe186421aff9023104ffa8610817ff108840bfe20c4202fd0c531077fa829080bff438c40ffeb264205ffc4021107fc811901ffc428c8057fb126407ffc8132025fcca9083fff534840bfe3044200fbc862103ffc849083ffd5248405fe29a6202ff8c23203fde421081efc65c8435dea046215ff55321015f8c69080bfc324c405ef98c6202ff14d320c7fac898812fe658c80bffb2c4200bf58f2103ffac91900efc644c40f7e3264200ff5893108ffac91080afe63c842ffea826213ffcc321005fec71080bdf308c4077e324621cbfd9631067fac090863fd424c4197eb144200efd9121077fc829085bfc51c841bff98a4207ffc8021077fe8490826fd6408413ff2a04203bf191321077e811901ffc324c841ff2846405ff18231067f86090833fc104840fff904421aff5023103fec421084afd658842dfea8e4202ffd0d3109ff88190803e5210840ffe1904202ff4c9310bf7a809880bfd538c411fe2984200bf185320ef7a809901fff65c84037e3046407ff0ca21035fac010863fe544c421fe29c420fff14521107f8211901ffe208c80bffb28421eff5913206ff8c690833fc5048439feb2c6221ff506320cff8a498803ed21084057e31c420bef5022103ffccb19017fc648842fffa026207ff98c2103ffca59081ffc524c805fe21c6405ffd923103ffa8410803fd614c805fe9826200ff4c421007dc4290857fc54c840fff9946400bf9863203ffaa590833ff304840dfe980421dffd01320adfac990817fc64084097f32c6218bf59131007fa631080bfe308c40bffb184202ff94e320dff8851881ffd32084197eb024221ffd523208ffcc91085ffd104c40ddea004202ff0c5310b7fea390803ff614c835ff1046200efd91310d7f84118803fd328840f7fb1e4200ff1893105ffe811083ffd51484037f3026400f78ca3107ffea49080bff538c827ee9864211ff9522103ff8a41080bfc314c825ff32c4207ff94921077faa89081ffe428c819fe2024206ffd002103ff8a51086ffe428c435ff284621aefd02310effaa099053fe43c843bfe882641bff5923102ff8621083ffd65484097f32a6205ff1962103fd8651905ffe404c42f7fb026207ff8c9210f7fe829901ffd658c805fea9a6405ff8842105ffa6110806fe608c43fff28a6407ff4832109ffea19087ffc654c83d7fb226400bf58e2104ffe821083efd6548405ffa1a6402ff0c23205fea211081fff52c8401ff18e4207ff99232087fcc71080bff318c827ff0864207ff986320fdfeca99033dd304840fffa146405ff0c62103ff8c11902ffd108841dfe2
  | 2 => 0x32037fc2010812fc658c40ffeb04641eff9053209fbe619080afe638843ffe28a6402bf9863103ffec919017ff108c43fffb2a6407f70c9320fffea29905ffc404c40ffe1946401bf983210cffaa498802bf644c40f7e3126207ff8c932025fccb9084fbf40c8419ff3024219ff5453109ffc819080bfd438c427ff2864206ffcc021007fcc49887bfd544c827f69064207ff0812103ffac19080bff438c80ffe2164205ff9042100df8c010806fe6008417ff9844219ff9493109ffc619087ffd514c80f7e3246405ff1442103ff8419083ffd534841dde3224220ef5023202ff8a310863bc644c42fff3026200bfd853208dfec91081fff658c843ff2a46400bf58c2103ffca499023fe4308419ff2024207bfd82320d7fe4118877fe104c8037f3044207ff14a32007fac710827fd540840fff1904202ff90d320fffaa49901bfc4008437ff3246201bf98121107fe811907bfc544c817fe2044211ff55221017fc869881eff60c842ffea026203af191210d5fac11885ffc604c41fffb2a4207f7cca32004facb9085fdd304c405fe984640cf7cc121055faca1084bfd5188405fe18c6407ff8ca21017f8a71888bfe518c80fff290421dff481320cffea298833ed2048433ffa926207ffc852103ffaa410877fd404c83bee982641eef19132017b8629881ffe5288405fe9846217ff84131097faa5108127e65c840fff1064217ffd413104ff8a810806fc60c840fff9964202ff0ca310cdfaca9880bfe314c437fea14620cff8c12103ff88490877ff504c81f7fb2a4201bf18231107faa119063fe644c40ff7906421fff595320f7f88299003dc634840bffb20421bff552310a7f8879081ffc65c8433ffb2a620affd442102ff8c518863ff644c401ffb1a4206ff50021037ba601080bfd328c417fea044207ffd8232005fec49886ffe548c43fffa92640cefd01210e5facb18853fe53c842bffaa6420bf74c221115facb1902fff508840ffe3246413bf58321097fea310833fe5048433ff28a6207fdc8521087fc871082ffd2088427fea064207ff99421037fea01080bdf308c839fe2946216ffd4f2103ffa401080bdc438c4056e31a420effd91210d7fe8118833fe20484017fb1a4221bf59232017e86318817ff608c40fff2164207ff1932105dfec110817fe310840fffa904202ff50d310affa839085fff104c43bff8826407bfd932101dfcc899037ff324840f7f3104205ff8c6210cff8ca9882ffe1088425ffa94420ebfd912101dfcc810863fc414c40fff1964211ff50a210ddfac91881ffe63c84057fb0a6211ff50e2105dfac110817fc318c42f7eb026202ff50d32017faa71901efc650843bffb026405ff1963106ff8869081efc630840fffa164214ffcc721077fea890833ef2048427fe2864207bf98a310d7fa211887
  | 3 => 0x1440b0000a1302a008b7000090004a19403008090009a0502e0200000011008067f000000010480700c013bc2129c00000370c2bd05c27024ec0000c3d00e3a41e04001000112f02500800ac45600401218310046f0e0002200501040004590005302c000b00f06c000021602021194700041d0501d0000a0401f07c0000400274400400c2580105c6b1ac5431c0a0200008c0306800028000100003c00024901d80000c121a4282f41b0e0050e5dd004fe0400606403004740000200c190504600000070790d00f03cdf0000306c712bc0401c160044a5181a0043f01800000070203865804018480180f5c8050f82f000100081b0ac0a00c640000a018580000108c00784000159d20401000129c8040988104001000011481514c61000580c8040040a17804008b201804198000000801aac99c0135c05009880300c0dc0f02c2201c44224030181800c09020530000f1d0430542500400005c4077fca89081ffc32484097e32a641eff191320eff88099002fd618c8077f3264205ffd8e2100df8c11083bfd4248433fe28a6208ff10c210e7faa51886ffc548c431ffa126202ffd4d3205ff8a110853fc31c841dff3224216ff94721025fcca99023fe530840f7e32c6409ffd502102ff8c710843ff3288405f61926407ff90821005bec690803fd324842bffa0e4202ffcc5310f7fa8299073ff518c421ff29c4200ff58d2101dfcc898833ff6048419dea02420cff5412100dfcc119003fc614c80ffa908420affd4c210d7ba611881ffd65c8405ff21c6207ff59021007fc4290857ff43c842ffe0826202bf98c2103ff8a49080bfd438c80fff306420cff44121015fcc690887fc418c801dfb22640cffd0121025f8cb1086bfd208c41dfe3224203bf9922108ff8a91080afd638c82d7eb2e420cff1812104ffa821081ffe65c840ffe9084207bfd8c210eff8209901ffc618c805ff1926207bf19021017f8609907afd644c82ffe282620cfd4412103ffac790847fd41884037e3024205ff0422105ff86110863fd544c405f7994641effd0932005fac69081fff60c84197fb024208ffcc42103efacb9081fff208c81bfe18a4207ff5863203ffe841081eff658c8077f3224202ffcc13107ffca29081bfc3008421ff98c4218ff9053103ffac01086fdf438c4077e3224202ff4c13203ff8c19084bfd658843bff3026407bf9862102ff82010863fc544c41dffa0a4202ffcc13203ff8cb1900bfc538c80f7fb246407df99721077fe8690863ff414c4077f3246406ff14021057faa21082efe610840bff20c4207ff982
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe74d8931004ff75d8532137e74148421006bd60d9131006de50d8d21007c47348421007d51018d2103eee6218931007cd628ca3102fe464484211aebe31d913102fd4314c6210079d4018d21006bd71d91321aebd53d913102fe431484210067c435972113fe6754842111fa74048421006be75d912101cfe7458e21006bf50d912102edc3158e21016de634c721006df634c521006bd50d9121004fd75d8532006be70d912100cfc7058d21137e55448421004fd7458f2102fd6718c5311aebe73d9131006be70d9132006de51d8d21004ff7058e21007b510d9121006df64d8d21007a77448421006dd30d8532004fd74d8532006dd40d8d21014ff764ca210067d7459721024fe7558f210069f6418d21006bc70d9121006dc54d8d21006bf70d913102cfc7158c21017d7618c531024fc7558f2100cfc701853212fe731484210079f6418d21016de634ca2103cfc764c721046df3058c21006de6518d2106edf30d8d210079f4018d210069f64d8d21006ee52d8931004fd70d8532004fd7058f21075bc744c921006be60d9132004bf7458c21004fd7498632006df634c921004ff7558f210ce7e654c72102eec6298a31006dd75d8d21006bf4058a31127e57048421006df40d8d21006bc31d9121006bd20d912102fe71048421006df42d8d211d6bf32d913203ef77158632014fc764c92112fe64348421006dd4358c21175dc748ca310047d75d8e21006be72d913111fe53048421006dd43d8d21004bd70d912100cfe701853202eef6298a3102cff75185320067c415972117ebe32d9121007cf638852101cfc74d8532004ff7058a31006bd50d9132004ff70d8d21176dc3258a31004fd75d893102ded76c8621006dd72d8d2103fe56448421006bf72d912106ef63158632006dc41d8d2111fcd3048421086df30d893115ded7088521006bf31d912102e7d75d8e21006bd30d912103fe77148421006df60d8d2117ebf21d912102edf618c531014ff764c521176dc32d8e21006bd405863203cff7158a3117ebf20d9121006bf75d9131024fc75d8d2103e7f2059721006bf75d912100cfc70d8532006bf64d893100cfe70d8d211aebf71d9131187cd30c8621006bf4058632014ff7658e2111fe630484211afb431d9131006bd4058d210067d735972102fe66148421006bf10d912103fe66448421006dc60d8d2102fe451484210079d30d913202fe76048421006dd6018d211d6bc31d913202cfc7598632084ff7258d21006bd20d9132137e7434842116edf6118d21177d721d8d2103cfd7318532024fc7558c2103df67188521006bf50d9131006ed62189311af9c31d913106cff7358d21007af20d912102edc6358e2113fe751484210b67f7159721006be30d9121006bc73d9121006bd60d9121004fd7058d211cebc52d9132
  | 1 => 0x853201cfc7458a3103ef721586320067d654c721004ff74d8532024fe7598632006bf60d9132004fd70d8931006f5511853206fd4314c521006bd40d893102cfc7158e2101cfe74d8e21006be50d9131004ff7058d210067f30597210067c7059721006bf4058c2113fe5534842103e7d325972103fe665484211aebd31d913106ede7618d21006bf40d8d2101cfe749863203e7f42597210067f405972102ef41018532004fd70d8d210ddde748ca3102cfc71d8d21006ed2058a310c6be76d91311aebf30d9131006bf64d8d21006be63d9121006de41d8d21006bf20d9131024fe7558a31137a474484210067d4359721006bf71d913217fb421d9121006be51d9131016dc638c7211aebd32d9131177d5718ca31006bc20d9131006be10d91310057d7598931006be65d9121005bf7458931006bc645893103e7c2159721006bf7458d21186ed60c862100cfe7058a31024fe7518532006bf4058f21014ff764c7211d7ac32d9132004fd70d8e21006dd30d8e21006dd3058e2102cff75d8e21006ef2058a31187af40c8621196dd608c53102ef65118532176dc52d8d2103cfc7258f21157cf30885210a6dc4358f2103f6e75c86210b67c71597210c5bc7458931006bc63d91210065d305972106edf3058a31016de618ca311d6bc30d9132006be65d913201cbe76d91320069c6418d210067e7459721006bf40d893100cfc70d8e210079c6418d21177ce628ca311d6be73d9132006bd53d9121006dc64d8d21137e67448421006bf50d9132006df638c52117ebe52d9121004bd74d8e211aebf73d9131046f53118532004bd70d913111eed604842102fe44148421006de6418d21006df6388521004ef7648421024fe75586320069d30d913101cfe7458c21006ef7648421006bc64985320067e7059721006dc65d8d21006be73d912101cfe741853203ef42158632147e57448421014fd7158c210f5bc74585320067e7359721006bf32d912106cfd72d8d2117ebc21d9121046df301853202ebd74d8e210067d70597210067c7459721006df7358d21006bc30d912103dec724c52102ede3158c21004fd7058a3102def708852111fe7504842111fe5504842106edc53d8d2106ede43d8d21006de60d8d21006bc64d8931007d710d8d21024fe7558e2102cff709863203cfd7258c21086df3258e21006dc40d8d21006dd30d8d2106dde76d8d21024fc7558a310e67e658c721006dd70d8d21024fc7558e211d6bd72d913211fa54048421006bf52d9131005bd70d912103fe66348421024fc75d8532137e54148421006f5105863202eec2158a3102eee6148421006dd6418d21176dc42d8d21004fd7458632004ff70d8931004fd75d8d21004fd74185321d6bd53d9132024fc75d8931076be71d9121005bf7458532006be70d913101cf
  | 2 => 0x6dc50d8d21004fd70986320a5f7715893102ddf708c531016dc634c921004ff74d8d21176dc21d8d2106edc30d8d2103f6d75c86211d79f30d9132004ff7458c21005bf744c621006bf30d912102fe651c8621006bf644c9211d6bf72d9132007cf20d8d21006be51d9121046de5358c210067c735972111fc5304842102cfe7158c21006bf64189311b5be76d9131006f651d8532007cc6388521007d71018d2111fe47048421005bf7458d21004bf7458d21006bd75d912101cbc7458c2106ede53d8d21004df70d8d2103fcc324c92102cff7358c21006bc52d91310fd7e75985320a6df30d853200cfc7058c2103cfe7258c21006df6018d21005df70d8d2103cfc72d8d2116ede3218532007af64885211d6bd31d91320067f73597211cebe72d9132004fd75986321cebf73d913202dee7188521006dd634c72103edc3258c2100cfe7058f2102cff70185320067c4059721006dd65d8d21006be50d9132006bf60d912117fb721d9121024fe75d8931007b710d9121086f5319863203eed76c8621006dd42d8d21176de72d8d21006bf70d912106edf3058d21137e6544842116fd72118d210a6df3058f21006dc6018d21084fd73d8e21086df309863203cfd73d853202ef6719863203cfc764c521004de7618d21004fd75586320079d30d91210067d658c72102eef60c8621004fd7558a31006be65d9131006be51d9132014fe76d8d21006dd3098632006bf4018532006bf6458931006bc60d9121006bc60d91321d6bf30d91320069d30d91211aebc53d913106edc315863203dec724c7211d6bd32d91321af9f30d9131005bd74989310067f705972103cfc725863201cfc7458632005de7618d2103e7c4259721006df72d8d2100cfe70d8532006df51d8d21004ff7058f2112fe44348421006bf65d9132006bd75d9132006be71d9132006de40d8d21006df74d8d21006bc70d913202eef6188521006be75d9132004fd705863202df4714ca2102cfc7518532005bf70d9131004bd70d91320069d30d9132006f76198532004ff7558632006de75d8d210a4ff7158d2103ede3258c211cebf20d9132004ff7558d21006be75d91310dedc648c531006df54d8d21006bf60d91310e57e7598a3101cfe74d8532006f5611853212fe6734842103e7c7259721007e7734842103cfc7258c21017d6618ca311c5dd708ca31176dc72d8d2103fe56348421006bc65d9131004fd7018532004ff70d8532176df71d8d21004ff7058632006bd40d8d21006bc7458d21006bd4058c2100cfc7058632006bd70d9132006bf64185320067d405972102edf7358c2116fd42118d2102ef63118532006bf70d9132006dd10d8d21006dd305863219ddd708c5310b67e715972102eee7688521007cf734842106cfd764c52102def7648421004fd751
  | 3 => 0xf31d8d210cd7e75989311a79c648c53111fe44048421004fd74d89310c6bc644c521006df10d8d21006bd65d9131046de4358c21016dc638c52102def7148421007e57348421006bc10d9131176df638c721006bd40986320067d715972103e7d425972103e7c3259721006e7764842103e7d215972111fe6704842111ee56048421006bf4058d2101cfe74d8d210f6bc644c921006dd3058c21006de6018d210057d7598532006dc6418d21024fe75d8532086dc6388521006dd60d8d21006bc65d9132004ff7058c21006bc70d9131006f77158d21004fd74d8e21006bd52d9131006dc6518d2103e7e725972102ede3158e21006bf409863200cfc7058f21006bf6458d21076be76d9121006bc65d912100cfe709863201cfe7458a31006bf6488521024fe7558d21006bc6418931167ac64885211d7af32d913206edc6358d2101cfe7458d21005f7714ca21006dd71d8d21196df608c53108dbc744c621006df75d8d21176df21d8d21086ed32d893103fe565484210067e4059721006dc51d8d21004fd7558d211d6bd73d913202cfe71d8931004ff75d8931005bf744c521006bc64d8d21006bf7458c210067d1059721006bd10d9131006ef7258d21076bd72d9121004ff7458f2111fe540484210f5be7498532006be60d9121006bf648c521006bf51d9131006bd51d9131006de30d8d21006bc53d91211bedd608ca31006bf64d8532006be50d9121006df43d8d210a6f631d853211fe65048421086df30d8e21004ff7458e21024fe75d8d2111fcf3048421006de20d8d2103e7e2159721006dd30d8931004ff7458a31006dd52d8d2103e7e3259721137e45448421006de74d8d21006df6418d2111fe73048421006f71058632157af4088521007e5314842102cff74d8e21006df65d8d21006bf64989311aebe32d9131006df52d8d21176dc628c53101cbc7458d211d6be31d91321aebd71d9131004fd7558c21006bd65d913216edc3218532005bf744ca21176dd628ca31084ff764c42103cfe72d8d21006bf72d9131006de10d8d2103fe4214c92102cfc729863211fe74048421086df3058e21016dc634c52102fe65148421006bc75d9131075bc7458d21006bf645853201cfe7458f2106ddf7018d21127e7704842102eef6048421007cd20d8d21157e5108852117ebe72d912102ef63198632004ff7558a31005f4714c921147e77448421006df53d8d2100cfc7058e21137e543484210079f648c531176dc20d8d2102ef671d8e21006bf75d9132176de42d8d21006dc10d8d21006bd4058a310067e4159721006dd634ca21006bf644c521004ff7558e211d6bc53d913202fe76448421157ad4088521006dd51d8d21004fd7058e2100cee7688521024fe75d8e210a4fe768c52103dee768852100cfe7058632187cf30c8621
  | 4 => 0x8d21076bd71d912113fe551484211cf9c32d9132024fe7558c2100cfc70d8d211cebc72d913202fe710885211d6be53d9132006bc10d9121004ff75d8d211cebc20d913203e7f2159721176de32d8e2117ebc32d91211d69f30d9132014de76d8d21006bc75d9132004fd7458a3106edf32d8d21006f410d8532006bf73d912102cfc75d8e21137e75448421006bd52d9121006f551d8532006dd3058a31005bf744c7210067e3059721187ad40c8621006ed52d8931157cd308852102cff70d8e21004fd7458d2106edf3058632006de64d8d21006dc74d8d21006bc6458d2100cfe7058e210f6be76d91321ddbe76d91320c5be749893103e7e2059721006bf51d91211cebc32d913203fe76188521006bc60d913111fe5104842102fe763484211aebe30d913102cfc74d8e2118fe551c862108ebc6488521005ef724c521006bd70d9131004bf70d9121006ef6298931005f7714c921004ff7558c210067e1059721014ff7158c21006bd51d9121006dd64d8d21006bc51d9131005bf70d912103edc3258f2102cfc74986320067f435972101cbe76d9131007af744842103fe66048421006bd4058e2111faf404842102fe4604842100cfe70d8931004bf70d91310069d40d8d211cf9e32d9132006dd50d8d21075bc744c5210debc648c521007d510d8d2106eed3258a31007c77348421006df50d8d21006f5109863202fe641484211979d408c531006de65d8d21007cc734842103e7c20597210247e75d8e21006bd52d9132006bf4058e2100cfe7058c2103fe560484210079d40d8d2103e7e425972103de77648421006dc70d8d21086ee32d893102cff7498632005dd7018d2103fe77648421015de728ca3100cfc7058a3103e7d7259721006dd41d8d2102cfc764ca211bedf608ca31006bd4018532006bc6498931006bd73d91211aebf53d9131006bd10d912102edc3158c21006bc72d9131006df41d8d2102e7e75d8e21076bc71d9121004fd7058c21006bf51d9132024fc7558d211979f408c531006dd20d8d2103cfd71d8d21006bd40d8532006bc6418532005bf744c921004fd75d8e2106ede71d8d21005bf70d91320069f40d8d210065f305972102cff759863203e6f20597211aebd73d91310079f40d8d2102cff7418532005bf744c4211aebe53d9131006bc50d9131006bd51d91321aebc30d9131006bf40d8532176df20d8d2103ede3258f21006dd54d8d210079f64d8d211ae9f30d91310067c3059721004fd7458c21006bf64985321aebc32d9131006bd72d9131004dd70d8d21137e4744842117ebc52d9121005dd70d8d21006bd10d913212fe4534842103edf7358f21006bd4058f211cebe32d9132017ce728ca3102fe46548421176de52d8d2113fe4754842102fe63148421006f61018532006bf65d913106ed
  | 5 => 0x2e010020002d006bc71d913217ebf71d91211d6bc73d9132006dd3058d211aebc71d9131024fc755863211fe610484211afb731d913103e7f32597211d6bf31d91320a6df3158f210c6be71d9131005ef724c7211d6bd30d913200cfe70d8e21006de54d8d2102eed72d8e2111fe430484211bf9d408ca31006df70d8d2108dbc744ca2101cfc7458e2102ef710986320057d7598a311aebf32d9131004fd7558e210adbc744c72103e7f7259721006ee20d8931006bc64d853213fe75348421006df6518d2106eee3258a31006dd3058f2114fe775484211cebe52d9132075be76d9121006bc51d912101cfe7458632006be20d9121006bf52d91210067d415972101cbe76d9121006bd50d91310063d4059721006bf10d913203ef7618852100cfc70986320de9c648c531005bd70d913101cfc7458d2111fe450484211bf9f408ca31006bc7458c21005bd74985320079d30d913102eec6258a31006bc645853200cfe7058d21006de70d8d2106cfd768c72106edc43d8d21007cd2018d2111fc7304842103ef72198632006dc75d8d21006be10d9121007ad20d912103ee76048421004fd74d8d210067f415972101cfc7458f21004ff7458632004bf70d9132006f610d8532006be60d913112fe6534842103e7d205972101cfc74d8d2106ede63d8d210063f4059721004fd7558f210dede648c5310067c31597211cebf21d9132175df708ca31006bc50d9132076bd21d912102cfc7158a3102dde718c5310067c1059721006bf65d91211aebc31d9131006bf53d9121004ff74d8931005dd718ca31006bd20d9131004ff7458d21177d421d8d2102edf7358e2117ebc72d912101cbe74d8e21006ec20d89311d6be30d913202cfe71d8d21006bc51d913201cfc74d893117ebc20d9121137ac74484210066d2059721007cf2018d210067f3159721006bc75d912102fe661c8621177d6718ca3102cfc7418532006be20d913202fe4634842114fe57548421005bd70d913203cff7258c21044ff764c621006be20d9131006bf52d9132006dd5358c21006bd70d9121006bc50d91210069f30d912102ebe74d8e21006df4358f210079f30d91210079c64d8d21006be10d9132006bd65d91211aebf31d9131006bc10d913202ef421986320067f1059721006dd6518d21006dd30185320067d3059721006bd40d8e211cebc21d9132006bd75d913102fe41048421006bd60d913203de67188521006be53d912102fe7654842104dbc744c4210067e4359721006be52d9131006dd53d8d2111fad404842112fe4734842100cfc70d89310069c64d8d211aebc73d913106df571989311aebd30d91310067f7459721006bf40d8e21006bf10d913102eee2158a3111fe64048421004fd7458e2103cfe729863201cfc7458c211d6bf53d9132006dd74d
  | 6 => 0xf40279000010719040600000178010382e0040000c3b05c00b700d00075054050e401718060400d010342380a348000b800194140000901001014000200200412030012141b1ec9300c000082a81c09790060022e5a40001400108600040e04806020500402400c0e0281a00800028020044c04c0f00c6103413004000000001c862180a09c0c0f49802c020b1460002109433010060000309402010010380002c6d008af01c160143b0240002c0002c00030180002b55c02324140c4010001800d760780702c03000000006900000016492dc5ac68250200f4670c014e2024020018d0588b002f20e1a807c0555c0c07c01064030280300000108030580000400a1401004140243d0840003402000cca4920000070418700401080250b81f16c540009e080280281a0005f0449e01800048160c03d000180b000260b46d07e5d40602d240242d00c9d0b4047300001418004007a67e0002000c1625410940800781f00471004000b40007c040040403814d1c000186c01802000060081e028075980d026dc95c01941b5138010fc22060040091a0163d0283b0f8009081348c0401c509340901012c1c000d85b0001e024050002c044030600e01c0700c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9f305d363884090f90ab82c3190028f21560d91210051e42a21b226200e1d85190634840117d0e322c299002972156018d210051ec2060b2e4239aae82043644c8019b2e1b00c6908032e5c360d91320f45ec38c1b226400a3d859c7644c8090fd0bb86c2990e6a760c70d91320045f43c61b224207a6e8290165c840117b0fa06c7108123be1d52d89310045f43ca1b226426ab681dcb644840153b09086c6908030f9d464985320066db8260b18420d8dd8704363484018790ab86c8990baf1a1c7348421175e241221b1a4200a5e8518363484031f100baac690802ab60810d9121005664324031a42008dd879906348401c3b0ba06c690907279db40d8d210043ec3882b2e422eace8204363484015390c986c89080387a146418d21005e3c06e69084200a3c8544364484014bf06b8acb908022fa1c10d91310045f438c8b126200a9d83997644840717f0fb06c899003275c340d8d210064eb8261b226400e1d404c165c840f4dd04182cb908eaa7a0e20d91320061f32ee898e42008bd87843644840193ee8982c6108030f5d740d8e21006563a6ec9084200c3e75d92624c45f55d04386c8908030fe1570d91311ced210ee89924200a9e84883634845d1b90ea0ec69080237a1c50d8d210146f438c031a423b8be87d9132484014bb0a306c690803b1580734842100752b06e89084200a9d84143634840197700b86c899002a760064d8d210045f438e1b226400c9f744c1634840f4dd05182cb90802f12052018d210043ec3820b2e42038bc87d01634840153d07286c890803e1cc374484212154f41861b224200a9c8358364484010ff0ab80c299002e920520d91210054f43281b1a42008bf8750363884014bd07082cb9080387a1740d8d210045ec38a3b226400c9f74dcd634845dc9ca5a96c6908beaba0850d91212461f3ae81b1c4200a9e86cc3644840117f08b82c61081eb32093058c21005d3c22629084200a9d84183634846b53d07106c8988ba37a1e10d8d210045f43821b2242008bd80dd163084015b700b28c69080317cc175d8e210047bc0ae0b1a42008de87043634841d17b0e306c890802a7a186418d210051f42ce3b226400cd9704c3638840153d09320c6908e62fa1c7458c210051f42ce5b226200abb8059764484018dacbb926390802a7a1353d8d210054ec18a1b22422d8df865c6328c4011bf06b82c69080327dc130d91310045ec3ccbb22424ea3d8490165c84011df0eb10c4988022f61e70d913202d7343eec9084200a9d8384364484014bd0a086c6908022fe1d65d91310054f424ca31a4226da687dd1210840717908b82c610802f160073484210051fc2a21b224200a9f8459463484011bd0f106c6908023761c50d8d2100666986ec908420087e87d0165c840193887ba6c6908028f6101059721
  | 1 => 0x100b28c690802a76106018d210046f43ca1b1a4200e1f404c165c84015af02b00c6908eaa7a0e10d913217c5e43ec898a4200a3c855c3644c80153d083aec690802a7a0e65d91210045ec3c41b22422ead48644363484090f90ab82c6108022f6037458d210054ec1ce1b226407c6c7259531c84015ab03328c69080327dd3634c5210054ec1ca1b22643ec9c744c163084011790ea02c610802ad20560d91320047dc02eab1a4200e2d4048165c84011bf06ba2c6908063721d3058c210066db8260b1c423ae9b804c3644c8090f90ab82c6908022fa1c30d91211ad4f41c21b226200a9d8304364484014bb07382cb908030f21570d912100667986ec9084207a6e829c165c840159b05328c6908029ee0171597210045fc3acbb226400ccf761cd21084010ff0ab82c3190028f21560d9131005ca40a61b226235a9e83083644c401b88e039a4210802a760e50d91310054ec26a7b1a42008bd878c3644845f56b02386c8908d7a6e0130d91310045f438a3b224200c3e75d92614c80147f08b8acb9080327dc06418d210061fc2ae1b224200aaf82583644c40117f0eb06c8908bb339db63885210054ec24cbb1a42008bd8798364484011bf0fb00c69080336e0170d8d211edd343ee89084203c9c7450d630840f4d904a0acb908032bddb74484210051fc2ac1b226200aad82143644846d17d0fb2262908b7710c8714c9210051f424e0b2e4200ab581083644c40156d0332ec8990032e5c060d91310745ec38a3b224200f8540dcd210840153908b00c6908029761474d8d210046fc3aca31a4200aae82043644c43117b0e28ec8988021f61f40597210046ec3c41b1a4200c9c435d163c840b1e902b82c61080237e1d6018d210054f4328031a4200ad686c40634840717d0fba2c6108028fa1010597211cc5e436e8b0a6400ab681143644840153b07306c8908038ee014059721005d2c06e89084200a9d83883644c4015390da00c69081739a1f764842100536c1420b2e423aa9e831c3644c80117d0fb22c690802b9e03764842117d5a43221b224200cbb805c3644840147d09182cb90802b620165d8d210045f43c41b226200a3f855c3644c40117f0eb2ec8908032719170d8d210064eb8261b2262008bd87943644840f8d8c4bacc4988029720d71597210045f43ea7b2242008bd879c3644c4031dd0db9262908d7279db648c5310054f420a1b1a42008be8788364484014bb06082cb90802a7a126018d210051f42420b2e42038bc845d5634840156b02286c890802a7a0c50d91210052f428e9b1a4239a9d831d7644c80153d0da06c6908028fa1420d91310064fb8261b226400c3d75192614c80153b07106c8908030f5d464989310054f420a3b1a42058dc8754d630840153b09286c69080393cc1205972117f17296a5b224200
  | 2 => 0xe53d912101c5fc3e81b1c42018f487441618c80153b06386c89889ae921131484210054f41c41b2242008be87191634840153b06086c8990063721d3058d210045ec3cc1b2264008be87147644c4735390c986c899002a760c10d91310051ec2821b226200a3d841c165c840153d06086c8908032ee0170d91310051ec28c1b224200a3c855c3644846b53d06386c8988030fa1f4059721135d2422e69084200a3e84dcd65c8401c3a81982cb90802a760364d8d2100572c06ec90842008be86dc364484019caa3bb2421080327dc330d912100536c1060b2e4239aae82143644c8014bd0ba06c69080395d4651d8d210046ec3881b1a42008be87d91624c40153b06106c898802b5a0470d8d210054ec24c1b1a4200a9e84183634840117d0ea02c69080e2fa1b7458d210064f986e8b184200c9f305c3644c80155d04286c8988121f215701853200556c10e1b2242008bf87583644c80117d0e286c899002a7a0e60d91210066cb8261b1a4200a3d85083644c40147f0ab86c890803275c130d91210074db0261b226400a9e86d0063484010ff0ab82c6108028fe1560d91320051f428c1b224200c9f70d9063484014bb0a326c6908eaa7a0e50d91320045f43c21b22644a87f8744165c840193ec8b86c69080e2fe1f60d913117dd241221b224207ce581dd92108403974e0a00c29900336dc13058f210051f42821b226400a6d828c165c84014bd0a300c69080297a0c10597210052ec1c20b2e422dbc482440634840717908baac6108bbb1d83734842117ed338ec910a422dbc687dcd2108401c5e80902cb908038dd4651d91310052ec28c031a4200c5d751d7634840fcd700902cb90802a761010d8d2100536c1020b2e4200cd970180634843117b0e306c8988063721d3058f2126d1f42080b2e4200a6d85083624c401938c8b80c6908029761410d8d210064e31ee8b1a4200a7585043614c80153d08086c690803279d94018d210054fc22c1b1a4200c3c7459531c840193ee0a06c6908022f61e60d91310045f43ca1b22622eace821c3634840117d0e286c890803e11d373484210054ec20e1b1a4200bc580dcd210846b53d07286c898802a760c70d912117d5741021b224200c9f30dd163484014bf06a0acb90802ab60a65d91310064f986e1b226200cd7631c53248401972e1b06c890802a721165d8d2125f2790660b2e4200a9d80190634840117b0f386c890803719c0734842102c6e43a86b184200ab88059764484a153d0db24629881e9ba0a10597210046fc1aeab1a4200cdb704c1634849bc5e41a02cb908028fa1410d91210045fc3ac1b226200a3d85043644c8015cb02106c4988022f61f52d913100657a06ec9084200a3e840c165c845db8eedb9a421080327dd3634c92125d2f41860b2e4200a9e831c364484015b
  | 3 => 0x1b1a422fda776dd1210840147b0a086c890803a91d3764842103d3741020b2e4200c9d744c3638840187aea3aec8990028f613735972100557414cbb226200ab681083644c47553f00986c899002b6e0165d8d210064fb26e1b1a4200ab581997644c80153b09106c6908fb279d130d8e210054f424cbb1a4200a5d85dcb6348401f08e839a421080237e1d6418d210045f436e1b2262008bd87883644c46b53f00986c898802a760e50d9121006ccb828031a4200c5d75d4f634840147b0b396c8988030f5d540d8e2101c5f436e8b12623ac9c63dd1324848753b07186c890803275c140d8d210055bc0ac1b2264008be87043644c80599cec31c42908023761e40d8d210045ec38a1b2262008be87d01630840153d09a96c690803e1d03734842123e1f3aa81b1c42048df8754f634840117d0fb22c2990028f61270597210072698240b2e42008dd8718063484014bd07382cb908032e5c140185320054ec18a1b226400cb970d83644c40117d0e106c8988b6b52191018d210062ebaa61b1c422ddc7761cd210840117d0ea02c6108032e5c060d91211e6e3438e69084200c3f855c3644c80117b0f086c8990123de1d51d85320054f42421b1a4200ba780dd12108401f0ee9b9a42108029e20171597210054f424a1b1a4200c3d751d7644840b8e8c2bacc2990063720f7058c211ae4e31ee898a4200c3d75d92614c80117b0e086c89900237a1e40d8d210045f436e1b2264008bd87997644c401d3700a06c6908028fa1070597210054e43281b1a42008dd87943634847553d06286c899002a7a1230d8d2103d3741080b2e4200a5f8558363484031bf0e986c7108022fa1f52d91210052ec1880b2e42008bf845c1634848d8bcea986c71080327d917018d2100556412c1b22622eacc824c3638840153b09386c69080327dce73d91210051fc2a21b22641687e8704165c840117b0f32ec899002b360c20d89311ad4f418a1b22622fcae76d9221484015cf0cb9a4210802b3e096018d2101e4f3a287b1a42008ef825c163484014bb0ba06c6908028fe1510d91310061f3a8c931262008bd87d4b644840153b09328c690803a9503764842117c5f43c21b224200ace86c80634840b5a902982c610802376027618d2100536c1080b2e4200a9f8358364484011bb0f300c690803279d86418d210052e41a82b2e4239b8c824c3644c8019b2e1b06c69080387d5254d8d2100566c10e1b1a4200cb970183644c80117b0e186c8908bab3a0850d8d21007c2986e890842188bd87043644c40193e60b86c8988ea2f21f644c92100c6fc3a61b1a4200a3d848c165c8401d8a61bb2421080327cc370d91320b536c10e0b2e4200a5e85193634841d17b0e086c8908029760c705972103c76412e0b18420d8dd87183634845b59904980c29900387d4
  | 4 => 0x44c87553d07386c89901e9ba08705972100672baeec90842008be871c3644c499c9e40982cb9085a9da0470597210045ec3c41b226400e9b604c3644c40153b07386c8908022f61e10d91310054ec20a3b1a4200acd820436348401d8eec39a42108022fa1f4058d21006e2ba8e690842358be87843644c40147f0ab86c8990029be0941597210052f428c831a4200a9e84983634840193ae1986c890803b158373484210074c30261b22641687e8710565c840193ee93a6c690802ada0450d9132007c3ba0e69084200aad82143644c40153d07386c8908ef279d930d91320045f438e1b224200f85401cd21084014bd07202cb9080327dc130d91210054f424e1b1a42008be87147644c80155b04086c898896f1e0073484210052f42883b1a4200a9c8359764484014bd06202cb908fe37e1d41d8d210146e41ae830a6400a9d83843644c40153b07086c89900327dc340d8d211ad4f41ce1b226200ad58114363484018790ab86c898802ada0450d91311cd57410ebb2264008f787584614c8018bee739acb908029721560d8d210061ebaec93126200c3d751d7644c47553d063aec8990022f61e50d91311f64e3a260b1a4200a9d83883644c8031d90e902c5188022f21d4058d210054fc1acbb224200cd970183634840117b0ea06c7108028f21570d91310074c30261b226200ae582043614c80117d0dba264908029721510d8d210054ec06c831a4200e1e85193634840193ceda00c6908038dd4651d91210064e3a6c698a423aa9e83043644c85d5ab02386c69080339dd776484210054ec24c031a4200ab581143644c8014bd0bb96c6908022fe117558c210064e3a6e6b1a42038bf87d83644840153d08300c6908063721d3058e210064e3a2c698e4207a6f8048165c840117f08baac690802976146418d210052fc2a21b1a4200a5d85107634840717d0dba2c299002ab60810d91320054ec20ebb1a4200c6d75d8a624c40187b0fa02cb9093e9b60a70597211b64f3b261b2262038df8750f6348401d3700986c8908029761470d8d211f64f3b261b224200dc7751cd210847517d0fa96c8990b7b1d8073484210051e42a21b226400ab581143644c40717d0fba2c690802e9e1173484210054ec26a5b1a4200a5e851c363484634df04b8acb908022fa1e50d91210064e326e1b1a42008bd87143644840153b06286c8988bfa9d8374484210054ec26e5b1a4200c7575d86614c80178902906c6908038750c435972100763bb6e69084200a9e84dcb634840117b0fa96c8990028f61210597211cd4ec1ee3b2264008dd87994634845d998e5b1a6290802a7e1165d8d210054e422ca31a42008be87143644c40153d07086c89081e37a1f4358f210070ec28c9b1a4200a9f8458063484011bb0f086c6908022fa1f52d91312064f3b28
  | 5 => 0x3c86a260ec0181c000020c80a03106028060100a1e006b000002004001f40100e1bb5866b14000620007e2d02010800088047b8622a17ace94e0106400184010121101a0c820cb9884a01a0a012258169184e05014048c00780008031708021f020b78000680c7b15a00000000000284e0281e000340083e0000030812170000b88006010a68dc021066283e0106409800008665600809840f398000828010000b0022700a0ea1a30826000049381a408754202201886000082e80c2d0220281407106138060486e0040e0100602800009c80002a038540180e00000068661ca8a010000b008f580e0981087990000000081a0003a010ba2f06804800008120180000006030000014e01ac800004049481189200000008aa0983202220010382b0020100c0096c0102e1b81ca1804001ce0184a000700409c0f0f62fa1b744c5210043ec2ee1b0a6400a9d8318364484014eb02382cb90803a9d0376484210054ec1ce1b22624ca5d838c165c84014bb07202cb908eaab60875d913200656a06ec9084200a3e851c3644840193cedb20c6908d6a7a0c10d913100536c1480b2e42008bd87083644c40117b0e286c899003e1d0073484210051e422e2b2e4200a3c85583644c80153d06306c89080237a1c40d8d210051ec28e1b224200a5e831c165c840199eedb9a42108173994776484210054ec2461b1a4200acd8214363484015ab07080c2990eaa7a0f71d91322255b408e1b224200c3f749d165c840717908b82c69093b8bc81405972124c3e43a20b2e4200e5b804c165c840153d08386c6908028fe1560d91210070fa0660b2e42038bc87d0163084015ad02286c6908022fe0174d8e210056ac1821b0a6400a9c8458363484014bf0ab00c690803b1cc3764842100753bb6e89084200a3e85043644c4015390ca00c6908022f61f53d91210045ec3ca1b226400c3d65dd131c84010ff0ab82c690802a721b40d8d211d45f43c41b226400c9c74d8d324848b93ced986c8908022fa1c7458d211cf17296a5b226400aad821436
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x200040270500014009002b0000010001cc070580734842100551654701cd2108401e09404c120597210052664064dc36348401ac380583734842100626a19705006348401584974c37448421006266117018063484015c0905d4734842100561a5f401cd2108401e81605037348421006a8e0160dd12108401b818050073484210053125d601cd210840158497500734842100526640645c06348401e81604c3744842100471660701cd2108401898865c14018d21006b0601601cd2108401e81605007348421
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x50000d2025d604c374484210069012eb028039a4210802c41a51c1601cd21084018c04bb00a00e69084200a306a0705807348421
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x209
  | 7 => 0x3
  | 8 => 0x20c
  | 9 => 0x20d
  | 10 => 0x20e
  | 11 => 0x1409
  | 12 => 0xb09
  | 13 => 0xb0c
  | 14 => 0xb0d
  | 15 => 0xb0e
  | 16 => 0x140c
  | 17 => 0x140d
  | 18 => 0x140e
  | 19 => 0x1549
  | 20 => 0x154c
  | 21 => 0x154d
  | 22 => 0x154e
  | 23 => 0xb49
  | 24 => 0xb4d
  | 25 => 0xb4e
  | 26 => 0x1449
  | 27 => 0x144d
  | 28 => 0x144e
  | 29 => 0xcc9
  | 30 => 0xccd
  | 31 => 0xcce
  | 32 => 0x15c9
  | 33 => 0x15cd
  | 34 => 0x15ce
  | 35 => 0xb0211
  | 36 => 0x20b11
  | 37 => 0xb0214
  | 38 => 0xb0215
  | 39 => 0xb0216
  | 40 => 0x20b15
  | 41 => 0x20b16
  | 42 => 0x140b11
  | 43 => 0xb1411
  | 44 => 0x140b15
  | 45 => 0x24b
  | 46 => 0x144b
  | 47 => 0x148b
  | 48 => 0x155411
  | 49 => 0x155416
  | 50 => 0x144b51
  | 51 => 0xb5451
  | 52 => 0x144b55
  | 53 => 0x148c
  | 54 => 0x28c
  | 55 => 0x15d451
  | 56 => 0x1455d1
  | 57 => 0x178b
  | 58 => 0x160c
  | 59 => 0x40c
  | 60 => 0x20b14
  | 61 => 0x28b
  | 62 => 0x9cd
  | 63 => 0x24d
  | 64 => 0xa0c
  | 65 => 0x180c
  | 66 => 0xb1695
  | 67 => 0xb09d5
  | 68 => 0xb1395
  | 69 => 0x168d
  | 70 => 0x9ce
  | 71 => 0xa0e
  | 72 => 0x180e
  | 73 => 0x2c9
  | 74 => 0x14c9
  | 75 => 0x168b
  | 76 => 0x9cb
  | 77 => 0x180b
  | 78 => 0xa0b
  | 79 => 0x154996
  | 80 => 0x58a
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 792
  | 6 => 1023
  | 5 => 753
  | 4 => 21
  | 3 => 5
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/28+packedAt gbK8 (1664+(h % 28)*6) 6) % 64)
  | 7 => 2*((h/278+packedAt gbK7 (29304+(h % 278)*10) 10) % 792)
  | 6 => 2*((h/362+packedAt gbK6 (49104+(h % 362)*10) 10) % 1023)
  | 5 => 2*((h/251+packedAt gbK5 (44427+(h % 251)*10) 10) % 753)
  | 4 => 2*((h/28+packedAt gbK4 (1470+(h % 28)*5) 5) % 21)
  | 3 => 2*((h/8+packedAt gbK3 (405+(h % 8)*3) 3) % 5)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff03e03e0783fff0ffffffc19e8c7c40f1ff
  | 1 => 0xf01fc003ffffc1fff07f01fc66973a07f3e73
  | 2 => 0xf001ffffc007ffe0fff87fe0387183c787cf9c
  | 3 => 0x1fffffff80000ffff80003f81fc07f80fe0
  | 4 => 0x1ffffffffffff000000003ffe0007fff000
  | 5 => 0xfffe000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x110d00a20a410129204c92850082040c4050a5
  | 1 => 0xa102c00148aa4125101205a822831a01b2652
  | 2 => 0xa020554c4004ca409a904d40985182c1858b18
  | 3 => 0x80459a76a7500108ece601832d81dc06e80de0
  | 4 => 0x889e39b39e7739c0044060c37fe000776f000
  | 5 => 0xccf0001c01806210088008103f7deb70000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40519
namespace PEqualNP.Outside.L_meta_40519
open PEqualNP.Outside.L_meta_40519.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 27 := block_range (n:=27) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 27 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 144 := (concat bs0_3_0 bs0_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 883 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 (concat bs0_4_288 bs0_4_384))) (concat (concat bs0_4_480 bs0_4_576) (concat bs0_4_672 (concat bs0_4_768 bs0_4_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 34 := block_range (n:=34) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 802 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := bs0_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 26 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 134 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 48 := bs3_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 56 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 781 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288)) (concat (concat bs4_4_384 bs4_4_480) (concat bs4_4_576 (concat bs4_4_672 bs4_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 801 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := bs4_6_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 21 := bgb_4_0
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
theorem bgb_5_672 : Interval gbAtlas 5 672 81 := block_range (n:=81) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 753 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 bgb_5_672)))
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
theorem bgb_6_960 : Interval gbAtlas 6 960 63 := block_range (n:=63) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1023 := (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 (concat bgb_6_576 bgb_6_672)) (concat bgb_6_768 (concat bgb_6_864 bgb_6_960))))
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
theorem bgb_7_768 : Interval gbAtlas 7 768 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 792 := (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 (concat bgb_7_672 bgb_7_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 64 := block_range (n:=64) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8feeaeeeafce8e8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4243122344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40519.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.and,[2,6]⟩,⟨.or,[1,7]⟩,⟨.or,[2,6]⟩,⟨.or,[5,7]⟩,⟨.or,[0,4]⟩,⟨.or,[0,1]⟩,⟨.and,[10,12]⟩,⟨.and,[8,11]⟩,⟨.or,[13,14]⟩,⟨.and,[9,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243122344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243122344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40519

open PEqualNP.Outside.L_meta_40519 in
theorem PEqualNP.Outside.L_meta_40519 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243122344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243122344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
