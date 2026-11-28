import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36795.Model
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


end PEqualNP.Outside.L_meta_36795.Model

namespace PEqualNP.Outside.L_meta_36795
open PEqualNP.Outside.L_meta_36795.Model
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

def SBf (j : Nat) : Nat := [4, 4, 8, 6, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36795

namespace PEqualNP.Outside.L_meta_36795
open PEqualNP.Outside.L_meta_36795.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36795
namespace PEqualNP.Outside.L_meta_36795
open PEqualNP.Outside.L_meta_36795.Model
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
  | 2 => 0x3f81fff80ff03fffe07c1f83ff07c0fff48e4f
  | 3 => 0x3ffe03fff0003f81ff801ffc1ff800f818f38c
  | 4 => 0xc00003ffffffc001ffffe0001fffff001f03f0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8080080881200400028822842108520a413495
  | 2 => 0x155531946a456968f0551523564684d5948a4a
  | 3 => 0xa64d5aa528e9b22b75c219e91bd20ae0d8d38c
  | 4 => 0x3469a3464c8d234db96750421ce72c411e0360
  | 5 => 0x3871c3878f0e3c71de7b9e73908430861fec00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaaaa0a0aaaaaaa0aaaaa0a0aaaaaaa0aaaaa0a0aaaaaaa0aaaaa0a0aaaaaaa0aaaaa0a0aaaaaaa0aaaaa0a0aaaaaaa0aaaaa0a0aaaaaaa0aaaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36795
namespace PEqualNP.Outside.L_meta_36795
open PEqualNP.Outside.L_meta_36795.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x3a40440725308cb88364c49a323d3803c5108008706860aa1100160000c000051f24a40002a74b264000881061831d500400810f05108cff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xe817d53d03baa7a05754f40dfa1e81bd43d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037a87205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53102faa6206fd0c40dea18817e52102faa4206f90840de210817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc37e87986f50f30bf296617d52cc2fca3985f54730bfaa4617e548c2faa9185f15230bea9c61bf438c3bc87186f50e30eea1c619d438c2fca5185f54a30ef19461dc328c2fca3185f54630ef18c61dc318c2fca11877cc230fd984617f544c2fca8985f55130be2a261bf434c37a86985fd4930be292617f514c2f8a2987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c37e86187790c30dea1861dd430c33a86185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83dc65907b4cb20bf28e417d51c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837e87106f50e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20dfa1a41bd43483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20dfa1841bd43082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43ec63887d4c710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10dfa1c21bd43842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10dfa1a21bd43442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec62887d4c510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c530437e86086f50c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0x75150af8a2a17d14542ba28a857f5050af8a0a15f95042bf29885de5310abca6215f54c42eea98855d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665bf43ccbbc87996f50f32eea1e659d43ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232beaa4657c548cafaa7196fd0e32dea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1a65de434cb7a86997750d32cea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea96837e50d06faa1a0df55241bf29c837d539077e8720ef50e41bf294837d529077c8520ef10a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41dea1a837f52507dea4a0dbd4941be29283ec52506d8a4a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077e8620ef50c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998efd0f31ef21e63bd43cc7ba8798e750f31bf29663ee52cc6dca598df54b31f6a96636d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63bf438c77a8718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c77e8698f790d31dea1a63dd434c73a8698dfd4931be29263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf290637d520c6fca218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790fdd0721fa20e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c43bf438877a8710df54a21f7a1443ec42887dc6510fb4ca21bf28c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43bf434877a8690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610efd0c21dea18437e52087de8410fb10821f719043ed32086fca210fdd0421fa20843f631087ea6210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a07794f40af29
  | 2 => 0xb21d50004802c86d1b614c0028539e8dc0024432e354b4aa756a000e60001d835d47a5c1125014929b3769d0a8a1f44a8d8e9a7a42884c2891a1d22803410505c3fc7c045048a2c1a9d70280806a11c3a2610ff0df0a833452044064ae8a481b03270522929276198d6a6305021c25124194ac80000000000079000000140001e30000010085e0001e41d8220002c0000001c45dd5700057041872a762701840000047e7a02f8843ba83d1588334869d240f44ca330000002b8000a70000c69191a17d2b46347d0772825584c8002789bc5d825000574a98002660006829c31c0000027f000000ec90800051c0808b0007d0002930005e00009b0006b1060001265bcc28784b27fcf9ab1000860dc2a11f842c000000000010ca830000000005725000061a6d0ea001449af0008900000006c0006794f0004113e0f700045c9785a2b2001430002d40a52012537a00053800000000000ce0100008e8000002dca90002c68ec0009c436878212212e63f8000005524448614c1782786c9d238a5acd40093cc43c4b25a0f8820a11b149c8cc5a1de33c4c92b20435c990c00004241010b8000100180003800068241a80000004008140980800002000080380e010020181404000010000000c048000181807008168420001a0500a0305a0680c00802090080000810000008300500e0000604002040000100200808018240a0020101e00800000080000802810018060001a000180100c0b81400006018160000c0680408000000060000600004090000200c0480000000018000080000006078160081c108020381400000078000301e00012000000180e0780000012030120080803800018521b8020f00001804018000b0100801a0200201006010020b0080e80210000010000000600812038000000e0400600804018020700a000100103c0100001806000000000000800048160000c05002008040180a008001780a0580c0002000002010017e52d0efaa5a1df94743bea8e877e50d0efaa1a1efd4b43df29687bd52d0f78a5a1efd4743df28e87bd51d0f78a3a1efd4343df28687bd50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa9287be5250f7aa4a1ef14943dfa8a87be5150f7aa2a1ef14543dfa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542fba8a857
  | 3 => 0x2ca000002a4534698df2940000009ba580fe43800123434000000002dc1c81182a3c4758cf8eb3224b4bd85c2be0380000026a5fd1623c2c2011558b2000000950004c216c5f2380e6408001c2000a9451000066000f7000030001569503720014f13a00094055869002000000000006080000c000000faaaa22495d540ed55846c9f24a06060cbb2a222a9f4a18004e02d4c80814d401cca1ea000000b68712fc2b0001df04e00061000000000000001882a45f80000000000121142accf09010265e540000000514f89985220000000025c35821a354a4a600023011c8a8000f3400400f586b41c56d3ba4d3f8001481cb0000006389f0001911100009aabc73a6702e5f00918a3ca64ce805d54c88c0b0e3120ac14508007c0f4a300010c000930001de374c400008e0013315e000360130005469f8000003de700528000926d920a9f09634c8a0940d46701081c4042c4f02275403d84d06c0b032d1f04c2cc4ac1618b1bc274869194ea138cd22d02a440fda6b26066cc30a638c000000e4000684378f01100012880002221521a8122c7708980b2142bd17a1c0aaa1cfb84601a81451a034227a4b12684f279125a710cea309b070414a58000c12e4909192202e20000014415a68c8fa280003455c80000076cb38001743f4da2b70009a49117a31e460fc14a38e0b4d987a12e000e19a91700280007e1147208182f5044e4dd08f4e61b8d5134000000c0a4f11801400127130750328001f600000278000000750000565d49893f004a7400000212980001602968180000623c00131199000001130912aa0fc0022e0000000000043a00000000000380b800039a69514800000000001f60007100026c41a000ab8000006fc599ca0fa7f4001bc000000ce80027a0000000001e9794b95848e8c45728809e7c9261b53243694a9c942a7e91e96842c6ad1d052000a34732723b0384f61871dca647883700094cf383c1d07b4ba1a00e80012e8aa0000007c8b951c6242b0620ec9b85b0c608297c241f90000001c00036e000002554160005410731800c0016c3b4688000000f6659080c54925347a839000ad0410d21926545ea7b000370a408d412ad86003147296ce70002a8000d903403e0004a81a0c00740f0003e0a1049000190000d80000000010383a0004b12a0000000
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xe548823e6494e208f592538823e6414e208f59053882766114e209d584538831f5350e20c714d438823d63d51208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e65151208f58c544831f54d4d20c7153534831f64d4d20c7193534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d208f990534823d6414d2097994534831f5414d20c7150534831e6414d20c7590534834d6214d208f997434823c65d0d20c7d4f434831c53d0d208f995434823c6550d20c7d4d434831c5350d20d314e324826c654c920e350d32482e8604c920cdd53514833454d4520d5d4f514835453d4520cdd0f514833543d4520cdd5051483345414520d5d4c51483545314520cdd0c51483354314520d98c851483653214520d9146204825e63150209758c540827661150209d584540823e6494c208f592530823e6414c208f590530826e6214c209d98453082756114c20c794d430831d5350c208fd91510823c6454420d954421082e960084209bd9520082e461480209ed95200825e63153109758c54c423e6494f108f59253c426e6294f109b58a53c423e6414f108f59053c431e5350f10c754d43c423e64d4b108f59352c425e63d4b109758f52c4395434c7109b98b548426d62d52109798e548425d63952108f992538423d6494e108f990538423d6414e109b988538426d6214e10c7d4d438431c5350e108f993528423d64d4a10d9d48218423d63d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58c544431f54d4d10c7153534431f64d4d10c7193534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d108f990534423d6414d1097994534431f5414d10c7150534431e6414d10c759053443556114d108f997434423c65d0d10c7d4f434431c53d0d108f995434423c6550d10c7d4d434431c5350d10cbd53524432c54d4910d3d4f524434c53d4910cbd0f524432d43d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524432f4314910cb50c5244354538c510d914a3144274654c510e550d3144364524c510bc181314436452841109798c540425d63150109b988540426d62150108f992530423d6494c108f990530423d6414c109b988530426d6214c109d984530431e5350c10c754d430423f64548108f191520423e64148108f590520425e63148109758c52042756508410d954821042f160084109e59610042776544010b9189100427b6544010
  | 1 => 0x863d6414f21c794d43c871d5350f21b558c41c8795434c7219798c548865d63152218f992538863d6494e218f990538863d6414e21c794d438871d5350e21b358c428878d434ca218f58f544863e64951219bd89544867761551219798c544865d63151218f994544869d6315121c798c544863d6315121c758c544861d63151218f992534863d6494d219b58a53486756194d218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f997434863c65d0d218f995434863c6550d21c794d434871d5350d21cd153214872c54885219798c540865d63150219e980540867960150218f992530863d6494c218f990530863d6414c219e98053086796014c21c794d430871d5350c219b59442086cd6310821b9584420866d658c821b9586320878d434c8219d59441086d56310421b958841087a442104219d59631086e5628c421e550d31086e562884219bd9521086ac64484219dd9521086b46448421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121086e76348421b958d21087a74348421e950d21086e460484218fd91500863c645402197d8d500865c6354021c799153d031d53d0f40c794d43d031d5350e40a758c429029d6310640a758f409031f5350d40c714d43502b86050d40c754f43102b960d0c409dd8552102746154840a758c421032d52108409bd89511026c6254440a758c41103355110440a758f401023f65500409ed95401031f6550e30c7195438c39b6050e30e6181438c23f6454a308f191528c31d4354a309dd85528c2746154a30a7590328c23f64546308f191518c31d43546309bd89518c26c6254630a7590318c29d64cc2309758e544c26f62551309b189544c27761551309d185544c26e62d50309b58b540c27661d50309d587540c23d6595030c798e540c23f63550308f58d540c23e64150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c25d6590c30a7592430c2d96090c308fd95430c31e5450c30a7d95430c31f6550c30cb952520c32d5494830e350e520c32f4394830cb50e520c31d4354830cb951520c32d5454830e350d520c32f4354830d390d520c32d4354830d350d520c30d4354830d354a320c29d640c830cd952510c3355494430e550e510c3665294430d954a510c3374394430cd50e510c31d4354430cd951510c3355454430e550d510c3665254430d9549510c3374354430d590d510c3354354430d550d510c3154354430d5546310c29d640c430c750e500c29d64cc030e650e300c25f654c0309ed95300c39b434c0309798c54c825d63153208f99253c823d6494f209d98653c82756194f208f99053c823d6414f20c794d43c831d5350f20e350d32c827661d52209d587548825e63952209758
  | 2 => 0x801018014024000010020000100000200c0000000e0000380a02802402001004000018010120040180200a0040080200a0040000000200c00004002000000000000080000300000000000000000000030040000000300000001000000020008019dd8552d0e746154b439bd8951d0e6c6254743add8552d0eb46154b43cb54852d0eaf6254743ab18951d0f355114743ce54050d0e9d62d4d43a75875350e9e60d4d43add855250eb46154943aed815250eb86054943cb5485250eaf6254543ab1895150ebb6054543ae1815150f355114543abd895050eac6254143add855050eb46154143ce5405050e3f6550c4397d954310f1e5450c43c754f43d0b1e5350e42c754d4390a5f63542429718d5090b1f5350d42ab1894350b3743d4542cd50f5150b374314542cd50c5150b674214542cd9085150b1e6454c42c754f4310aad62d0c42c794d4310b1d53d08428fd954210b1d5350842ad1854210a6f6550842b91854210a7661d53329d58754ccb1e63953329d98454cca756115332c795143cca9f6550f32c7d9543ccb365494732cd55251ccb954394732cdd0e51ccb354394732c750d51ccb365454732cd55151ccb954354732cdd0d51ccb564354732cd50d51ccb554354732c550d51ccb1d4394332b9987328ca3f64546328f191518ca3f64542328f191508ca7761551329d185544ca7b60551329e181544ca9d6490d3297195434cb1f6550d32c7195434cb8f6250d32e3189434cb8d43cc932b9987324cb1d43d4532c750c504ca3d65950328f990540ca5e63150328f992530ca3d6494c328f597430ca3f6550c32c794d430cb1d54cc83297d95320cb1d544c8329bd95320cb1d53d0f41c794d439071d5350e41a758c429065f63542419718d509071f5350d41ad185435072f43d4941cb50f525072f4314941cb50c525076452d0541cb14a415071e6454c41c754f43106b561d0c41c794d431071d5390841a758c421071d5310841c754f411063f6550441c754d41106ac62504419dd9541106e462504419b98b54cc66d62d5331c798e54cc66e62153319b58854cc71e5450f31a7d9543cc71f6550f31cb95252cc72d5494b31e350e52cc72f4394b31cb50e52cc71d4354b31cb95152cc72d5454b31e350d52cc72f4354b31d390d52cc72d4354b31d350d52cc70d4354b31c750e50cc63f6454a318f191528c6e662cc6318fd91508c63c64542319bd89544c66c62551319ed81544c6786055131a7592434c65c6550d31c7d95434c71c6550d31e5d85434c7946150d31c750f524c79543cc531b998b314c71d43141318f596540c63e64150319798c540c63e6494c318f592530c63d65d0c318fd95430c71e5350c31c7553310c65f654c431c7551310c677654c4319798c54c865d63153218f99253c863d6494f218f99053c
  | 3 => 0xf2800000000e39390000000000005495c00012000594738243024840b00048a000d00004a62440004300000000000000000ef8000000003511700026831a0f2d082000000000000038000000011780000028c00000000001268f90000000a90320a00000101000000d2800000000000000000010287a1c859c000010ea810000000000000000043e0000008732a001152173fa38400000000208000004440006c00000000089000000000000004840010f000000000000c52de880fa86d3a20011f0000003340019b000000f50003840000000010a1bd0821b1482d8799824d83e0d3042000000b18000000010893500000043025000000000272bc61400000000000000ad17a760000003980a0000000765f4421d41685a8db0000000008f00022c000000000000007b9e7000000da800000000bc0004c40e8000000100000022700000000000000000000000001c8000000000e05a800000000000001008e0e5000000000000000000000025c000838ce800000000000000003400000046a00023035000938f400026e00003000000000cb9de0000000000000000000052000000000001a8000788003500011e8001de05000152000560000040000000000000096000000000000000004ca184728001b2001250d23e65b4001f60000006a88f4a0000c582f3dc31c002640000006f8a7152000000002c2000010000000002ea3741a5dc3a000216868001dc0000007e800000530000000060000000000000010800000000ff80003c000000000000000000010200000000000000000a60008307d057000574fc81c4be000c61bf30e000000440003f0002150e20d80026f0002b0000001c600000000000000280000008d00000000000000000486000c7800000440001a74c20000b800184000001000008ccaa800000000000003a6000000dc08a000000000000007f00000000000000000000c68050000000017f4da2c8f581d3cc234b80002fc618ac9f218c16ccf0004988fd1200032c5f1349b746486045a3b00006000000000518189d024c0003216b000000000002261cc00000000000ff000000000000000000240000041600000133000000341844620003b02619c000001a32549511280045225000000000000000cf000000d083c2c847523a6300000000000000002004008010000100080000e030000040040100080000a0000700800a0000000801600800806006000010060020040000000000000000002028000110000100000000200001810008000020020020080100d0060000080100000c0100101201402000002004000000020000000000e00001002018030008050060040180200000003001000004000000000000080100800c0100000e004000000000000100100a008000000000000000000000402002012004000010
  | 4 => 0x1d53ae08c651c80e032c4906016e4bc7494a0b481c000004027d000055290980000000008d8820000000009883e00000000000330790000a50be5407027048c034c980035e7241900000000000000000000000004ba0406f09c0000009a06e3589a02c800000598dd918248600a88fb2322e800000000434c893200035800000000000c19a200084800000332000000000005e8b70ab000000000000000287fa5b000000bb00000024c3e25a218144970003785a4e29a924e6c8760c83f614d20a160441951e2090001a40001b35c7e00014b000000000001da00000096026734000004aa2a8dc8474000006d9fa1ae470508c90005c8a0800000000000000004ec00000000000000000000000000000043800000000000001f00006ac00000000000f112b0000008d17300000000000000000ce12d2be638e78000000008d9aa06e5591680000084c0000011800000000000000100000000000012828447c0011100000000000000000000000f6000000000003c0000002b426c00000000000001942600d000090000000000000000000000000000000000000000001ba0008c000000000000b10e2246000001b401e000000000bc000000002d8570000cc000000000000005e4088300340ac001074a20003b9f700051c000004325ec0002c496000000002b6998d8a671829201c94e4726e09f99f2922e00004f20400074041188000f8a6b0b08983e8e6000418d822840c254c91c33b4000001ce1d4000f180003e6f80027111c000e007e06627ca193a186001371401628b86884924a0385f09d01812c0000000055c5714400000000000000000330000004e01700021e76d0a05622800000019144000001080000012ca0a000874000784580000009e0006200006700000057990000000001ed38c1b000000000000f00000007a49600009c000000000007f0000da0004f400000080515158992e8000e580000000000000000000d200012e2e400000160000000004a400000000000000000003c2001108000000000000000013000054000534000000b8000000290000000004800000000129130000311d621420c05800112000000c022a0000024400000000000000748000001ea6f40000000000000000000000000001ba0000000031293c000b32e200035800000580900000000012b000000000000bb0003c8452020003b800000000000000000003d0000000000b52f1c44800001f84d000000002230008e8000001781e4ee80017e0000026a000000440000005d4500003b23ac000000000000000000034cc514f3de2a10193c382488cd0003660000010935a0003f8f6000128a9936000924aa0000000000000027c000000003d88701e80000
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xb9a00179b11980e94020a9e1d07909882a4a41121a0228885838a0d991615a5199385170e070c9a88000b1f9c209c8686049ba30013238300008f0c018014801f002210000400099e80091296a10100000000000f801d950d12029a020c4821c682090c00181180ce01245808b001015247154852d0e92392a228e8725dc562d4d4391ee4b0ea6a1d24715485250e94382a429287491c95114543a60e0a88a2a1d28725405050e9838aa028287491c94314542c1aa6b1686214a47158b4310b0aa98c2a1085a150e61cc932a48e2a18a4a0e15535874310652392c3a18838354c6250441d0a873166298d0d7294d434868ab8ca6a1a43071d95350d21a30e0a9a8690d15731532148686b98a910a43291d1618c821b0ae62108210e856310841086523a2c518843235cc644842192ae63224210ca6749912108662b98c890843615cc6448421d0ce63224210ca5731912108742b98c890843215cc6448421948e8b1a4210ce07058d21086523b68690843291d94348421d0ac6a1a4210e0d63548421029238aa4210818558d5110440a48e4a88822061543d85528c306a1ec4a8c61c150d5294430e0a87292a21870543549510c28ab8ca6a1e41455c45350e20c1ac8b10a69050c7550d324830632a8699241a250c604c920e0a86990a290560704c8514820eb98c8a8841491d15108420a1ae529a878850d7214d438420eb9cc9a9421499d35208610c2ac8b08a6885147550d314430a32a8698a21c150c524c510d2286302628866052181314420eb98c8a9021491d15208410
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x10070296240c0660120014202c06c05531c562d0c42c05531c961d0c418848758d4348421a808058d4348421c05631c55210840c05631c95110440a088550c604c920d01431c13214520905831d15108420905839d35208610a108550c604c510e0143148604c510905831d15208410
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 6 => packedAt s2K6 (756+((h/14+packedAt s2K6 (672+(h % 14)*6) 6) % 51)*7) 7
  | 5 => packedAt s2K5 (21203+((h/233+packedAt s2K5 (18873+(h % 233)*10) 10) % 922)*11) 11
  | 4 => packedAt s2K4 (26076+((h/208+packedAt s2K4 (23788+(h % 208)*11) 11) % 1327)*11) 11
  | 3 => packedAt s2K3 (3850+((h/25+packedAt s2K3 (3675+(h % 25)*7) 7) % 91)*8) 8
  | 2 => packedAt s2K2 (800+((h/4+packedAt s2K2 (780+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffff03ffffff81fffff07ffc1ffff9e3f1ff
  | 1 => 0xfc0ffffc07f07ffe0f83ff87ffe1e03e9c7e67
  | 3 => 0xfff03ffff8007ffff003fff87ffe003f1f8f87
  | 4 => 0x3fffffff81fffffc00007fffffc7e00ff8
  | 5 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x98208118912010005284b0088c02298821b0ab
  | 1 => 0x296312287244a49605a15485352142928c5665
  | 3 => 0x50c5a45120e9492ab04269505a540525168b86
  | 4 => 0x628a3882448c0dcd29680c4463999607c00d50
  | 5 => 0x830c30e3870e71f1ce738e6603111807fb6000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800eeaaee88eeaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36795
namespace PEqualNP.Outside.L_meta_36795
open PEqualNP.Outside.L_meta_36795.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x6485674080a0000419400283bf43bd43bf42bd42df32dd32be41bc41be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xd004009a28a851d531066ca3205354830
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
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (111+((h/1+packedAt s3K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc1fffc0f83ff87f0f83fe1ffe1e07fc1a67d9c
  | 2 => 0xfe1ffff003ffffff003ffe1ffe007fffc78e1f
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x840088a200808002284c02240229109408b0b1
  | 1 => 0x9449186425240a505a15214d21432584a25594
  | 2 => 0x89221014a4844a50422541254044a29450a0a
  | 4 => 0x295c4249606d57399683111b99960309f00f40
  | 5 => 0x3198738e738e67cee73b998311180c31ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36795
namespace PEqualNP.Outside.L_meta_36795
open PEqualNP.Outside.L_meta_36795.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x9500010000c74012166d1004e0000046ac01a043000a3239404009000f002001826015142ea438500940160070189008401f3c988111a484280000044001380003ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xc817d519037c83206f10640bf28481bf40903f681205fd4d40efa9a815f53502f8a6a07714d40ae29a817f52502f8a4a06fd0940dea1281df32503ba64a05fd4540be28a81fb405037c80a05f95040bf298817d531037c86206f10c40bf290817d521037e84206f50840ef99081dd32102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9985f94b30bea9661bf42cc37a859877ccb30ee996617e51cc2faa3985fd5230bf2a4617d548c2f8a9185f54e30efa1c61dc438c2fca5185f54a30dfa1461bd428c3be6518774ca30bf28c617d518c3bc6318770c630bf28461df308c3f661185fd5130dfaa2613f544c2fca8985f55130be2a261bc544c278a8985fd4930be29261bf424c37a849877cc930ee992617f514c2f8a2987ecc130ef182617f540c2fca8185f55030be2a0617e530c3be86187710c30bf290617d520c37e84186f50830ef99061dd320c2fca2185f54430ef18861dc310c2fca01877cc030fd18061dd300c3f260185fd5320bf2a641be54c827ca9905f55320deaa6413d54c82f8a9905fd4f20bf29e41de53c82bca7905f54f20eea9e415d53c82f8a7906fd0b20dea1641df32c83ba65905f94720bea8e417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c417d528837e85106f50a20ef99441dd32882fca3105f54620f710c41ec21882fca1107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41bf424837a849077cc920ee992417f51482f8a2907ec8120f7102417f54082fca8106f950209f2a0417d540837aa8104f55020be2a0417f53082fca6107794c20af298417d53083baa6105754c20be298417e520837e84106f50820ef99041dd32082fca2107d94420bb288417d51083eaa2105d54420f710841ec21082fca0107bc8020fd10041ed20083f240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7885fd4b10bf296217d52c42f8a5886fd0b10dea1621df32c43ba65887d88710fa90e217f54842fca9085f55210be2a4217f53842fca7085f54e10be29c217f52842fca5085f54a10be29421bf428437a850877cca10ee994217d51842fca1087e88210fc90421f710843f621085fd5110dfaa2213f54442fca8885f55110be2a221bc5444278a8885fd4d10efa9a215f53442fca6885f54d10be29a21dc53442b8a6885fd4910f7a92216f52442fca4885f54910be29221ec52442d8a4886fd0910dea1221df32443ba64887d88510fa90a21fa20443f240887ec4110fb082217f54042fca8085f55010be2a0217f53042fca6085f54c10be298217f52042fca4085f54810be29021bf420437a840877cc810ee990217e51042fca0087dc4010fd08021f510043f220087c44010
  | 1 => 0xd518cafca1195f54232bfaa2657e544cafaa8995f15132efa1a65de434cbba86997710d32dfa1265ee424cb7a84997b50932d6a1265ef324cbbc64995fd4532be28a657f504caf8a09977d5132ef2a265dd544cbb8a89977d4932e7a9265df424cb3e84997790932e721265dd424cb3a84997350932c6a1265dc424cbbea2997794532eea8a65dc514cbbea0997794132eea8265dc504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195794c32bf29065bf420cb7a841977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e837e52d06faa5a0efd0b41dea1683df32d07ba65a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42907be6520f74ca41bf28c83bf41907ee8320df94241bea84837f53507bea6a0d7d4d41be29a83dc53506b8a6a0dfd4941be29283bf425077a84a0f7cc941ee99283f7415077c82a0dfd4141be282837e54106fca620df54c41df21883bc43106fca420df54841dfa1083bd42107be6420f74c841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31bea9663bf42cc77a8598f7ccb31ee996637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31dfa1463bd428c7be6518f74ca31bf28c63df318c7ee6318df94231bea84637f544c77ea898cfd5131bf2a2637d544c6f8a898ef151319e2a2637f524c6f8a498efd0931dea1263df324c7ba6498fdcc531ef18a637f504c6f8a098dfd5031bf2a0637d540c6f8a818df94c31efa1863dc430c6fca418df54831dfa1063bd420c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790efd0b21dea1643df32c87ba6590df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d528877e8510ef50a21ef99443dd32886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690efd0921dea1243df32487ba6490fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821dfa1043bd42087be6410f74c821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e817e52d02faa5a06fd0b40dea1681df32d03ba65a05f94740bea8e817d54902fca7205f54e40df21c81bc43902fca5205f54a40dfa1481bd42903be6520774ca40bf28
  | 2 => 0x1700027c100df28138067d1e2525d07f00b050000484901c800037c4000021a3c15ba3253441d3001f016094df845050001358003d2368000001345dc001d9298000002ba0000013800046a8608206e00043c8980201400c0240001b01e004018080000040080600e03c01001012000008040100000200400e00c3080103c00c010000440480281a00c000018010100040980006203800000002004018040000040000203007c010010140180002c01c01800010004004008060000040080100400803017050018070040020080200d0240500000500200c00018012000000000020440080f0080180280600e0000b8130020140900000400c0600501a03c0200000002c0000300000002010070008030060080080000000a004078020100200080001202000800000030000000000240000f02a000018010120b4048350000040200200204c0280100400c0081701003c048050080040180c0040000f8000060040100000002006001000000088030240940c0020060080100c002004000060140100000100002000000004008010050060600100d002038020030000280100f028018090000020000080100a00c0300201c000010050097e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621e750c43bf29087ee5210edca421df54843f6a90876d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85be43d0b7a87a16f10f42bf28e857d51d0afca1a15f54342dfa9e85be53d0b7aa7a16f14f42dfa8e85be51d0b7aa3a16f14742dfa8685be50d0b7aa1a16f14342beaa4853d5490afca7217794e42af29c857d5390bbaa7215754e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7c86a16f50d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a16fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5150b7ca2a16f54542de28a85bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42ef298855e5310afaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87997790f32eea1e65dc43ccb7e85996f50b32bf28e657d51ccafca1995f54332efaa665de54ccbbaa9997715332efa16659f42ccbbc85997750b32cea1665dc42ccbbea3997794732eea8e65dc51ccbbea1997794332eea8665dc50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195754e32bf29465bf428cbdc85196f50a32f6a1465ad428cbbe65197bcca32bf28c657
  | 3 => 0xab32c4eca9aeb2582c424a8f03a738108f955895076a0759077136a4139e75ce307d4341e16a1440000008f98418495c0000005830d4fa450000ac0012b0d0238000000001b4001573b65b1240c60326d0000000003946c8d2000400480d538e704000e22942e86b0003fa000a3217000000092204c868cfb8002809593498d2180016c2492780000f0420006a1451e04fc618b29eb4126c03292231e760110b944a2e078af63baa347522c4940004a85957a1ec000000000014f2055e8bb8e58064602051a0c751804c25116508938889924e4ad48124c3d8778438771661f0539602f4b0caa1f80ea69d14ae935e418279610006e4982ab3cc94c0000f59a4d0001715b240d36124000a4800072292a1cfb2c55f20d00002d2d0570000f231c8dc000f30002740020e000001542f00740016d0715da6d40000000000184000000000ea894000280001a03427f8dd054000ab97d2763fe2f4dd8644c46c8442db1f6304d9800318000c8a3607a234bd9310d8000002ea00047447a99512a94c0ace582180000000009090784e00080cfa8000001d1820006041680003c000260cc00000088c260000004b800164000a800030a2b23e1582bf52a84c002d11988f4a903930435c562f30006683c8d136c0000016b5c6ab517aaf43ec0c7e2154b63352684626c994f08101c89e4000000003818000007cbbc5d80a358a853f8005e4b480019d3ce59c96a0001a64077a22000655808001220002a91e4b046c8081b27eb94d68415f6360f82942acb74eb0e75041ad3d9930000007d000000000bb07a30a000001450bc0012016342c0002e0633d41f97f89f000984cca125e23d87307326e05d7aab6194b842fa1900632c189102aa000000001a8acd588b535c080d30e1448030000002e0b7184800000001520000ec82c678003ca000ed000144000022df0008ed7f1ca286945318621a6374622f72fe38d679b148e56cdea7d1924d4e22e400024c4e24624caa5081091064204f0000e00000014f46252163ab44dc534afade000134fd0971488195920c3c614d7e9944020c8e2a025acaf90a0671ea77cb71172142b4a08005266000018b272000242970005600000006c3000000008ea20000000000011f0000007cd1f8002a0000de2040005a4bc0004e800000000496b80e80ce3da4e0ae9cc4ee28cc1800088000071882de000000005380000017d11486c000ab54400000133000000000003a80005f000000a40578000000fd278d04b80d49d0001424f4001190000002c01a3d0878e92ca0123d17127c0000dca89f22240014019c336000000820007ec770000002b941a2b0000000c23310c10c002270480cc942c92d4ae05a0fe386b541d929238008dc06a536b316210e0b699d10800000000000000009c400000000828001a40005b568000
  | 4 => 0x25f4cc000000db0005d4000513e83200000100000000000000174918000ac898d2a390705c8e48005720bc0000016e468309f1312050000004740014c1f9488000b10004bc0016100000008c0021d4b40000000060ca14582a739a26c3780045ca8d2c8b6000a185f9730000003f9ee0000000000000012c290a653a2a482ac6052000000845cc000000000000013991400061c6f1270000000021c2640c08597c4aa5785e1d31ee9407418a1129e83492f1fe844a130700eb2c0aa6818a2a0bc9ef04c15d470e93c8258000ec1248b5532bb522820002aa4de65c000004f0598002d722a198bf24333c8a8a5ac014a070000eb1549a842925450b4d7611860a2c8ba02a28e7446e1e25ce2307e82741a8e145811384020952f82b4a595e27529c6dd2e9a9132014002fc35422cd11
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c2097d89530825d6254c208f990530823d6414c209798c53082766114c209d584530823e64948208f592520825e63948209758e520823d65d0820c794f420831d53d08208fd95420831e5350820c754d420825d65cc820c7953320831d54cc82097d95320831e544c820c7551320838d424c820cd95251083355494420d594e51083555394420cdd0a51083354294420d5cca51083553294420cd95151083355454420d594d51083555354420cdd0951083354254420d5cc951083553254420d9546210837151880209bd95200827b6548020dc545200825e63d53109758f54c423e64d4f108f59353c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c438d424cb109798f548425d63d52108f993538423d64d4e108f992528423d6494a109798e528425d6394a108f990528423d6414a109798c528425d6314a10e3509328423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f588544431f54d4d10c7153534425d62d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d1097588534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524434e6314910d358c52443656114910da580524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb149424425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d3149324438d424c910d914a21442746548510bc18121443685288110f888620442786548110bc185204425f63550109718d540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530423e64948108f592520425e63948109758e520423e64148108f590520425e63148109758c520427661148109e980520432e5250810cb549420434e524c810d3549320438d424c8109e59610042f161840109dd95100427b6544010bcd9510043736544010ecd9110043b06444010f4d8d10043d06344010f8d8910043e06244010dcd4910043715244010ecd0910043b14244010f4cc910043d13244010
  | 1 => 0x86786054d21e3509324865e63d50219758f540867a60d50219e583540863d65950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530863e64948218f592520865e63948219758e520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420865d65cc821c7953320871d54cc82197d95320871e544c821c7551320878d424c8219bd9521086776548421ce95250087395494021d694e50087595394021ced0a50087394294021d6cca50087593294021ce95150087395454021d694d50087595354021ced0950087394254021d6cc950087593254021dc885500877121540219798e52d025d6394b40cb54b42d034e524cb40d354932d038d424cb40ab588439025e6394a409758e529032d5250a40e3509329025d62d4d4097588535025e63149409758c525031f53d0940c714f425031f5350940c714d425032f5250940ae181425025e65cc94097197325025e654c94097195325038d424c940c714e405031d5310c40ab588431025e63948409758e521032d52d0840ae583421034e524c840d3549321038d424c84097d8d511025c6354440cd54441102b960104408fd95401029c63500409ed95401026e62153309b58854cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb30e350932cc27661d52309d587548c31f5410e30b3588438c23e6494a308f592528c34d524ca30e3509328c23d62d51308f992544c25f63551308f994544c23d62151308f990524c23d64149308f997424c23c65d09308f995424c23c6550930c7d53324c31c54cc930c7d51324c31c544c930d3d49324c38d424c930b6181324c31c548c1309b988540c26d62150309d984540c275611503097594430c31d5410c30b3588430c23e64948308f592520c32e5250830cb549420c34d52cc830b6583320c38d424c8308fd91510c23c6454430d5544310c2d9600c43097d95300c29c644c0309ed95300c25e63d53209758f54c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c831e5454f20c755153c823e6414f208f59053c831e53d0b20c754f42c831e5350b20c754d42c831e54ccb20c755332c831e544cb20c755132c838d424cb2097d8d548825c63552208fd91538823c6454e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d20e3509324825e63d50209758f540827661d50209d587540823d65950208fd89540823d62550208f990540825e63150209758c540827661150209d584540823e64d4c208f59
  | 2 => 0x6550932e3d8d424cb8c6350932a7992324ca9d648c932e350a324cacd6295132b3d89544cad76155132b5185544cadb6055132b6181544cb1d5415132b3593524cb8f52d093297996424ca9d6490932b3996424cb4e6590932b3592424ca8d6490932e3d89424cb8f5250932b3995424cacc6550932e3d91424cb8f5450932e3151424cb8f6550932e3995424cb8d6550932e3195424cb8f6150932e3985424cb8d6150932e3185424cb8f6050932e3981424cb8d6050932e3181424ca5e6510932a7990424cace6210932e3508424cb8d42d4532e350a514ca9f6454532a7191514cb8d4254532b6d81514cad86054532e3508514cb555114532e350b504cb8d4294132a7d91504ca9c6454132e3509504cad76154132b5185504cb8d4214132d6540504ca5e63d50328f596540ca3e64150329798c540ca6e62150328f992520ca3d64948328f597420cb1e53d08328fd95420cb1e5350832cb949420cb1e54cc832c7553320cb2d548c83297d95320cb1e544c832c7551320cb8d424c8329bd95320cb2d544c832d394d320ca5e6394b419758e52d072d52d0b41d394932d074d524cb41e350932d06ad6210e419798e529065d6394a41cb549429078d424ca419758b535065d6214d419798c525065d6314941c7d4f425071c53d0941c7d4d425071c5350941cbd4942506b4615094197997325065c65cc94197995325065c654c941e3509325071c5390541c754c43106ad6210c419798e521065d6394841cb54b42106b561d0841d3949321074d524c841e3509321063f6550441a718d4110677655044197d8d501065c63540419b98854cc66d62153318f99252cc63d6494b31cb94942cc72d5250b31d354b32cc78d424cb319e983548c67960d5231c7d50438c6cd6210e318f992528c63d6494a31d3549328c78d424ca318f58b544c63e649513197d8d544c63e65151318f588544c63e64149318f590524c63e65d09318f197424c63e65509318f195424c71f54cc931c7153324c71f544c931c7151324c74f524c931e3509324c6d4614c931c7152314c66e62150319b588540c67a60150319e580540c65d6510c31c7550430c6cd6210c318f992520c63d6494831cb949420c72d5250831d354b320c6d561cc831e3509320c65f654c431a7191310c677654c4318fd91500c63c64540319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f21c794f42c871d53d0b21c794d42c871d5350b21c795332c871d54ccb21c795132c871d544cb21e350932c865f63552219718d548863f6454e218f191538878d424ca218fd91508863c645422197d8d508865c635422197d8d544865c63551219ed81544867860551218fd91534863c6454d219ed81534
  | 3 => 0x888c924c0000010999d168900ed800436528120a900000000000000000001d7000059729a82780000001b01013000000000000001f22ae0240012a5a4000000002ea03800140540000201e43866306980020eb14001ed3c65092d9175d26bc4c81c1ae8e11a8d637c000ad0000aa000000715d84c09729608e4342daa20005887027a5147e95b85809c65d65928572938f715f000000001a5000bb8000002d4a4400000334001142ef59e6145f02c53224124062330955328ea3000007b9e64580016e9c6000834908000140f0480000404000120000000c0806802004010000003c07034000400000001000090040002401000010540200c0200005000000000101405014000841c030020000e0000d0080100c16028040000002c010080101800038000180002006004100040100c000040601c03084090001400406008040000000000008170000c00004008000100c00406004010040600c0100000010010040100c0801800008000100e030040000000c000440100c010780d00001008030340000000054000080a03c0501406008080000000c0001400018000000100c0001008000030000004c030140a0040200418000080000901818008050100601c070000000002010050680001c0a0080d02402068010040b000000240103006008030740001c0001000008230200a00c0800420000030700701c04038120281101402a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a71854310e9c6050c43e350e5210f1d4354843e350d5210f2e6454843d398d5210f2f4354843d390d5210f2d4354843d350d5210f0d4354843c754c43d0a5f63547429718d51d0a5f63543429718d50d0aad62d4f42c754c53d0aad6214f42a7d8d51d0a9c6354742cd54451d0a9f6354342a718d50d0b395014342d398a5390b1e53d0a42c754f4290aae6290d42c714d4350aae6210d42a798e4250a9d6390942ab58a5350aaf6254d42add855350ab46154d42aed815350ab86054d42c754c5350aad63d4942a7d8d5150a9c6354542aed815150ab86054542cd5445150a9f6354142a718d5050ab76154142ad1855050b395014142c794f4210b1d53d0842d354e4210a3f6550842c794d4210b1d53508429bd954210b2e5450842d354d4210b1c5450f32c755043cca3f64547328f19151cca3f64543328f19150ccacd62d5332c755054ccacd6215332e3d8942cca9f6454732a719151ccb555114732a7d9150cca9c6454332d654050ccb2e6295232cb951428caaf6550a32cbd95428cb1e54cca32c7553328ca7761551329d185544ca7b60551329e181544ca5e65d0d32b398b434ca5c6550d32c7151434cb1d5410d32b3988434caad6490932b398e424ca6c6550932e3d0d424cb8e4350932e350d424cb8c4350932cbd95424cb2c
  | 4 => 0x7343a8e45b4af40029b582758d60c518e0008c8bd1bc3c539a6d2144541400056443845a8c23c8b40026641c3201b18234c4693da8859c044001863469f80ca6229ea492989815c6050225c48e010a319b00063c219b541099104a2b0e62c8221ae0c6000770003a2031392024e85cc36ad02685b4aa0863845143b83e4ac0006e0000000996b2670e03987c929548000d08005d6af80c0002f89d89b800000b203f9ea25aac00026e4823488a01f3160ec7d0004b4001539b20bc0000029a0d68786700005a47c000005b8460240d14ee74c0b99e194aa0000e20008dc001d05464ec000d909a950000000000002b2ae0000015f800000198000b84320006d1f30009e00029e2c67540d232042610a8a693b81943208c36619c5824b55a1f40a800248b84000004022084214b5208f0000000029bcb38aa4489c41cac61feb6000000394395738004fe238d6887000000000cd0002516f2492f4bc46f80052e258b21bd0f00c95b1f1374000bf1685c07680019444202c000003100e86da8b110750911832bc724cc86e3ee98cbc1cc5521d0500000f6440d88a65e01243b28d0940fc9c2e8000504fc04b28830003000218b9000000166000000003140000000047a5bc0000012e00160013000928000cb06e000001872642f0888000004cc8b1f64ba000492d408a6d13e952150794000002fa639212520008d8000000d083c001d25080000685d4747211fa164220000025e0005dce0a180000009a85f27e7ac00000000000f480016a00000000000a70539b6298a0414aaa2a6961718f50a47f80000014a000efad100a801281590000014380009e0003c83c2e07f4812ea000a389314d1b0625308220007b0001010003f80026c20ab5c000e93f8000001433e8424231715042acd00004c02787a16c0d8bb4138004725e4f00d020c000ae000238b54000c653e26c178fb5786f0b0a340463b5102230a238c6ea9d47c8741996e462000000002241404f800000000129e254c0752c8c44d43f060883100480000cf44e85c0022e32ab980000015a5d0ab0c31423c8b000044a93ca800000000000000000b0d1d8cc43e2dc000001926c10e2bb17448cce20705c78415a155b21f95884159a001660001e62ecc99f9344224988004ea0015600033eacc0009340600058a680008a4aaa431d8911651903ba384039474f2181449580e45755283048a3e0cb06f418b25080e73542457111d0f85244282017e1848426b2f67100012f0008c15d294068aac89a050006e4000003de95c000000a65c8000545be268c88eb568000001e80707006a0002ec00000000424000001ff25889893a850049181891b26c234f39bb2000780007a370270001c515e000001a451e000e7835000000000104140000010b5060016d800526000d58001e03bc150e807a
  | 5 => 0x11e6dc61042028a00e713d3bc3d80009516c9345620b3b29440005740c7ec95800290b105105a000abd508a30b8ae00513e2742e4ec16624a6fd3e00000069ce580358e851699a90b2a54522983ea9c117a1a102000000002fe001612b502443c0016b38e0000000031a538b29390000007ea332b68a8818002d20004e8690007c0078d50d4a180025f114000820000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x6c98ed1d08940d4138e85d34c4349cac3000cc054400d0f1184424fd140104747890003c00b84cb40124541c208c000800d4607c01293c0000001951105868a4010c00f4c86400014c8000000028a9202c10e440012c84000000f800c050d948dcb0e130008800384800a000700014bd003048010000190600080120030800240800e042050a004800143dc94354843a1eeaa1aa421d0f7650d5210e8638a86a9087431c14354843c1aa6b10a7a15147154c5350a8c382a629a85451cd5114542a60e0a88a2a1518735405050a9838aa028285835516215332a28e2aa0869951870550434cb0632a86a1265451c55415132a30e0aa0a89958771595424cac238acaa126562dc16550932b10e0b2a849960d65195424cac5b82c2a1265621c16150932d0ac230a849958771581424cac238ac0a1265a25806050932d1285b02a29968942181514ca8a3a2a228a65c15095114532aa0e0a88a29968542d85504cb42a10c2a8265461d15014132e1284a80a09955071540504ca86b90a6a12838514c6150941c1ccaa1264a0e0d53588431068d386a821c6383d516210e31a1ae42a26498d0e75509324c70a2a0c299263835516210c31e1284994a010f09424c95008686b90a6a12818614c6050940c1ccaa1264a060d53588431028b38ea821c6183d516210e30a1ae42a2649850e75509324c30c2a0c099261835516210c30a1ae4aa26410705424ca5108382a1264a884183d9363d4910c1ac8b18a48850d7214d4244286b98a4a1221435c8544c910a1ae8292648850e7550932442863aa849922183995424c910c18caa12648844d7218d5404216b90c8a9821435ce5250810a1ae929264086a0641891004360318c4880212c1d94244010e42a4a1220084d0764c910043a0a926488021e05093244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2587591430000d088c8014009402a04815946550932a08805946550932a80805846150932a80815806050932d01421c15114532d01421c55014132a058214c6150941a0a80d516210e31a0582150614c931a098214c6050940a0681d516210e30a0982150604c930a80865093244010c80765093244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
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
  | 5 => packedAt s4K5 (23882+((h/259+packedAt s4K5 (21033+(h % 259)*11) 11) % 1028)*11) 11
  | 4 => packedAt s4K4 (31162+((h/251+packedAt s4K4 (28652+(h % 251)*10) 10) % 995)*11) 11
  | 3 => packedAt s4K3 (4361+((h/28+packedAt s4K3 (4165+(h % 28)*7) 7) % 113)*8) 8
  | 2 => packedAt s4K2 (860+((h/4+packedAt s4K2 (840+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81fffe07fffe1f07ff0ff0ffe1ff81fa39f3f3
  | 1 => 0xfe07fff81fffe1f83ff0ff0ffe1ffe05c67cfc
  | 2 => 0xfff83fffe0ffffffc000fff1ffe3fffe078f1f
  | 3 => 0x3fffff0001ffffff0001fffc0007f80fe0
  | 5 => 0xffffc000000001fffffffffe00000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa4308231442420014b013012602484b018b171
  | 1 => 0xc910450c848022815105104a2092c10c254b4
  | 2 => 0x104228820291115280888aa115425146050a0a
  | 3 => 0x5965b124921d559ce6aa0881d9901867680fc0
  | 5 => 0x618621c71ce199e738ccecc811006187b7e000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36795
namespace PEqualNP.Outside.L_meta_36795
open PEqualNP.Outside.L_meta_36795.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1904440075810a802e00c002ca50852490f1b1601422268c30e147002618695aa28348014a007833ab40004e2001f00804800881d50c24011c2141091ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x60072708a5e6aae42002e4e84beaaa00004307e2018b00a5200008c90b28eb45a9c640c3c827a3a78969214741c80c22a004802560e24ac28607c10502246bc6c006e320068b800762644c0588812a8a43e86349e38b6a662009400ba009800005400002c4ca240001a9a5c163600c44a660000081e00001018c04c40011c0000016b03000e0c1000420014000408112045970d6e5210edaa421cf55242af29c855d5390b5ea4a14f95042af298855d5310b3e85996750b32af28e653e548ca7aa9195754e32d6a1465ad424caeea2995d14532e7a92659f424cb9c84996750932e6a12658d424cbaea2995714532ea28a6554514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96835f53506b8a6a0d754a31cfa14639d428c6bca318d754831cfa10639d420c6bca218f5944319f2a6433d54c86bca790d754f21ea18e435f53886b8a710eb50a21afa9a435c534867ca810cf55021af298435d530875a8410f50c421bd280437950086bea6a05714d40af298815d53102dca4205b54840bb288817551102eca3185d546309faa2613c544c27ca9904f55320af29e415d53c835a85906b509209f2a0413d54082bca6105754c20bb288417551083a863885794e10aea9c213f5444278a88857d4d10ae29a216f52442d8a488750c510
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x818029100000040d4c01492c21140cc1cf04e4851b009407254214532a3592424cb8542d4532c3508514cb854214532c5d08514cb464214532c5508514cb454214532c1508514cb0d5250831c3d4d428870d5350821955943108785420c421ca509500875031540218b588544c2546154f20c354d42c8344520c510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x210605655083108780a1062a8043411c55350b20
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
  | 5 => packedAt s5K5 (826+((h/15+packedAt s5K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (2904+((h/33+packedAt s5K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s5K3 (833+((h/7+packedAt s5K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffff81fffc3e0ff87f0ffff87fe07d19f3f3
  | 1 => 0xf81f0ffe0fffc3f0ff87f0e07f87ff82e6ccfc
  | 2 => 0xffe00ffff0ffffff0007ff007ff8ffff070f1f
  | 3 => 0xfffff0003fffff800007fff0003f80fe0
  | 4 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x10c2008c200840011809012318092118085171
  | 1 => 0x32441114645004506883104528824b0862c4b4
  | 2 => 0x4108aa2082a222a60444aa0845509463050a0a
  | 3 => 0xe596cc494a3aab3bb550881276640633b80fc0
  | 4 => 0x861888718cc333ccc666cc9c04401843d7a000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0eeeae8e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36795
namespace PEqualNP.Outside.L_meta_36795
open PEqualNP.Outside.L_meta_36795.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1f840a900b919b1297109d8008830580079100142000209e120f821a00000000150d948293158c868e0e9a818d0b05000000049c1e89011893800721099c8008060c001980218a168396181b97809f1d190f068400108001c00704040930b001c0060f38003017fd50057f54017f95005fd54015f55005fc5401ffd4c01fe53007f54c07fc53017fd0c05fe43017f50c05fc4300ffd48037f5200ff94803fd5200df54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803df3200ff8c803fd3200f74c803fc3201ffd4401fe51007f54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc2101ffd4001fe50007f54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2000ff59510005faca88033fc65440077e32a2000df1951001cf8ca8802fff64440177fb222000efd91100057ec88802ffe64440057f322200bff5911005dfac88802ffc64440057e322200bef1911001578c88802fff5444017bfaa2200bff9511005ffaa88802f7d5444017fe2a22000ffd8d10005fec688003df63440016fb1a2000ff98d1004dfcc688003fd63440017eb1a2000ff18d1004df8c688003dc63440016e31a200cffd4d10007fca688003fd5344019fe29a200bffd0d1005ffc868802ffd4344017fe21a200affd8910055fec488003ef624400177b12200aff9891000dfcc48802bfd62440157eb12200aff1891000df8c48802bec624400376312200affd4910056fea48802bfe5244015fea92200adf54910057f8a48802bff4244015dfa12200aff90910057fa848802bbd4244015fe212200affcc910057be648802bfe3244015fe992200af74c910057f86488033ff5144001ff28a2000ff54510067f8a28802fff4144017ff20a200bfd9051005ffa828802ff54144017fe20a2000ffcc510007fc6288003fd3144001fe18a200affc8510057fc428802bf62144015fe90a200afd48510057f84288033ff5044001ff2822000ff54110067f8a08802fff4044017ff202200bff5011005ff88088003ff3044001ff1822000ff4c110007f8608802bff2044015ff102200afe88110057fa408802bf92044015fe1022000ffc4110007f62088003fe1044001fb0822000ffd9410005feca0801bfe65040077f3282000ff59410005faca0801bfc65040077e3282005ffd901002dfec808017fe64040057f3202005ff5901002dfac808017fc64040057e3202005ffd501002efea808017fe540400bfeaa02005df5501002ff8a808003ff63040017fb182000ff98c1004dfcc608003fd63040017eb182000ff18c1004df8c60801bff5304001ff2982000ff54c10037f8a608017ff430400bff2182005ff50c1002ff88608013ff62040097fb102004ff9881000dfcc408013fd62040097eb102004ff1881000df8c408013ff5204009bfa902004ff94810027faa4080137d5204009fe2902004ffd08100277e8408013fe4204009fea102004ef50810027f88408013ff3204009ef9902004ff8c810027fa6408013dd3204009fe1902008bf98410037fea208003fe5104001fea882006ff1441002ffe8208017fe410400bfea082005ff10410007fe6208003fe3104001fe9882000ff0c410027fe4208013fe2104009fe9082004ff0841003dfcc00801bff5004001ff2802000ff54010037f8a008017ff400400bff2002005ff5001002ff88008003ff3004001ff1802000ff4c010007f86008013ff2004009ff1002004ff48010027f84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0xbfd400c025fe2006009ffcc03004fbe6018027fe300c013fd1806009ff4c030007ba6018027f9300c023ff9006011ff8803008ffa4018047fc200c001ffb2e2000bfd9710087fccb8800efe65c4001feb2e2000bf59710087f8cb8800efc65c401fffb26200fbfd931007ffcc98800afe64c401ffeb26200fbf5931007ff8c98800afc64c401fffaa6200fdfd531007ffca98803ffd54c401fbeaa6200fff15310007fec788002ff63c4001ff31e2009bf98f10007fac788002fd63c4001fe31e2009bf18f10087fea788003fe53c4001fea9e2010ff14f1007ffe878803ffe43c401ffea1e200fff10f10047fec588022ff62c4011ff3162001bf98b10047fac588022fd62c4011fe3162001bf18b10047fea5880237f52c4011ff2962008ff54b10046faa588023fc52c4011ffa162008efd0b10047fc8588023fd42c4011dea162008ff10b10047fe6588023df32c4011ff1962008ff4cb10047ba6588023fc32c4021ffa8e2000ff94710007faa388043fc51c401fffa0e200fff9071007fec838803ffd41c401ffaa0e200fff10710007fe6388003fe31c4001fe98e2000ff0c710047fe4388023fe21c4011fb10e2008ff48710047ea4388023fc21c4021ffa862000ff94310007faa188043fc50c401fffa06200fff9031007ffa818803ffc40c4001ff9862000ff8c310007fa6188003fc30c4011ff9062008ff88310047fa4188023fc20c4001ffb2c2000bfd9610077fccb0800efe6584001feb2c2000bf59610077f8cb0800efc658401bffb24200dbfd921006ffcc90800afe648401bfeb24200dbf5921006ff8c90800afc648401bffaa4200ddfd521006ffca908037fd548401bbeaa4200dff15210007fec708002ff6384001ff31c2009bf98e10007fac708002fd6384001fe31c2009bf18e10077fea708003fe5384001fea9c200eff14e1006ffe8708037fe438401bfea1c200dff10e1003ffec50801eff628400fff3142001bf98a1003ffac50801efd628400ffe3142001bf18a1003ffea50801f7f528400fff2942007ff54a1003efaa50801ffc528400fffa142007efd0a1003ffc850801ffd428400fdea142007ff10a1003ffe650801fdf328400fff1942007ff4ca1003fba650801ffc32840157eb0c200effd4610007fca308003fd518401dfe28c200dffd061006ffc8308037fd418401bfe20c2000ffcc610007fc6308003fd3184001fe18c2007ffc861003ffc430801ffd218400ffe10c2004bf98210077fea108003fe5084001fea84200eff1421006ffe8108037fe408401bfea04200dff10210007fe6108003fe3084001fe9842000ff0c21003ffe410801ffe208400ffd1042007ff4821003ff2410801ffc2084001ff8842000fdc4210007f62108003ff65440017fb2a2000dfd9510004feca88033fe65440077f3
  | 2 => 0x300c7fc8318063fd418c031fe20c6009ffcc630007fc6318003de318c001fe98c6009ff0c630007b86318053ff218c029ff10c6014ff486300a7f84318026fe608c033ffa846000ff94230007faa118067fc508c031ffa046018ff902300c7fa8118063fc408c013ff9846000f7cc23004ff66118053ff208c029ff1046014ff482300a7f84118003ff654c0017fb2a6000dfd9530004feca9805ffe654c0077f32a6000ff59530005faca9805ffc654c0077e32a6000df1953001cf8ca9805bff644c02d7fb226000efd91300057ec89805bfe644c0057f3226016ff591300b5fac89805bfc644c0057e3226016ef1913001578c89805bff544c02dbfaa26016ff951300b7faa89805b7d544c02dfe2a26017ffd4d3004ffca698003fd534c013fe29a6016ffd0d3004ffc869805bde434c02dfea1a6016f750d3004ff88698057ff624c02b7fb126015ff9893000dfcc498057fd624c02b7eb126015ff1893000df8c498057ff524c02bbfa926015ff949300affaa4980577d524c02bfe2926015ffd09300af7e8498057fe424c02bfea126015ef509300aff88498027ff324c02bef9926015ff8c9300affa6498057dd324c013fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530005f8c29805fff514c001ff28a6000ff545300bff8a29805bff414c02dff20a6016ff505300b7f88298027ff314c001ff18a6000ff4c53004ff86298057ff214c02bff10a6015ff485300aff8429805fff504c001ff2826000ff541300bff8a09805bff404c02dff2026016ff501300b7f88098027ff304c013fd9826000ff8c130007bc6098057ff204c02bff1026015ff481300aff84098027ff650c0137fb286009ff9943001dfcca18027fd650c0017eb286009ff1943004df8ca18027ff640c0137fb206009ff99030015fcc818027fd640c0257eb206009ff1903004df8c81804bff540c025bfaa06012ff95030097faa81804b7d540c025fe2a06009bf98c3004ffea618027fe530c013fea986009ff14c3004ffe8618027fe430c013fea186009ff10c3004ffec418026ff620c013ff3106001bf9883004ffac418046fd620c013fe3106001bf1883008ffea4180477f520c023ff2906011ff5483008efaa418047fc520c023ffa106011efd083008ffc8418047fd420c023dea106011ff1083004ffe6418027df320c013ff1906009ff4c83008fba6418027fc320c013ffb086009ff98430005fcc218027fd610c0017eb086009ff1843009ffea218003fe510c001fea886013ff14430097fe821804bfe410c025fea086012ff1043004ffe6218027fe310c001ef1886009ff4c43004ff86218027dc310c023ff9086011ff8843008ffa4218047fc210c0297f3006013ffd4030007fca018003fd500c027fe2806012ffd0030097fc801804
  | 3 => 0xf312a001bf989500effac4a8076fd625403bfe312a001bf1895001ffea4a800f7f5254007ff292a003ff549500eefaa4a800ffc525403bffa12a01defd09500effc84a8077fd425403bdea12a01dff109500effe64a8077df325403bff192a01dff4c9500efba64a8077fc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa000bf1855001ffea2a800ffe5154007fea8aa003ff145500f7fe82a807bfe415403dfea0aa01eff10550007fe62a8003fe3154001fe98aa000ff0c5500effe42a8077fe215403bfe90aa01dff0855001dfec0a800fff5054007fda82a003ff94150006fca0a800ffc5054007be282a003fe141500f7fe80a807bfe405403dfea02a01eff101500effe40a8077fe205403bfe902a01dff0815004ffecb98026ff65cc013ff32e6003bf9973004ffacb98002fd65cc013fe32e6009bf1973004ffec998026ff64cc013ff3266002bf9933004ffac99806efd64cc013fe3266009bf193300dffea99806f7f54cc037ff2a6601bff553300defaa99806ffc54cc013ffa9e6009ff94f3004ffaa798027fc53cc013ffa1e6009ff90f3004fbc8798027fd43cc037eea1e6009ff10f3004ffec598026ff62cc013ff3166001bf98b3004ffac59806afd62cc013fe3166001bf18b300d7fea59806b7f52cc035ff296601aff54b300d6faa59806bfc52cc035ffa16601aefd0b300d7fc859806bfd42cc035dea16601aff10b3004ffe6598027df32cc013ff1966009ff4cb300d7ba6598027fc32cc013ffb0e6009ff98730005fcc398027fd61cc0017eb0e6009ff187300e7fea398003fe51cc001fea8e601cff147300dffe839806ffe41cc037fea0e601bff1073004ffe6398027fe31cc013fe98e6009ff0c7300d7fe439806bfe21cc035fe90e601aff087300e7fea198003fe50cc001fea86601cff143300dffe819806ffe40cc037fea06601bff103300d7fe419806bfe20cc035fe906601aff08330007fecb18002ff658c033ff32c6003bf99630007facb18002fd658c033fe32c6003bf196300c7fec918062ff648c031ff3246002bf992300c7fac918062fd648c031fe3246002bf192300c7fea9180637f548c031ff2a46018ff552300c6faa918063fc548c02b7eb1c6019ffd4e3004ffca718003fd538c013fe29c6018ffd0e3004ffc8718063fd438c013fe21c6014ffd8a300a5fec518053fe628c0037f3146014ff58a300a5fac518053fc628c0037e3146014ffd4a300a6fea518053fe528c029fea946014df54a300a7f8a518053ff428c029dfa146014ff90a300a7fa8518053bd428c029fe2146009ffcca300a7be6518053fe328c029fe9946014f74ca3004ff86518003ff618c001ff30c6000bf98630007fac318002fd618c001fe30c6019ffd4630007fca318003fd518c033fe28c6018ffd06
  | 4 => 0x827fe650c4077f3286209ff59431005faca18827fc650c4137e3286209ffd903104dfec818827fe640c4057f3206209ff59031115fac818827fc640c4137e3206222ffd5031116fea81888bfe540c445feaa06222df55031117f8a818826fe630c413ffa986223f7d4c3104ffca618827fd530c413fe2986209f714c3104ffe8618827fe430c413ef2186209ff50c31117ba8618827fc430c413ffb106209bfd883104ffcc418806fe620c413feb106221bf5883104ff8c418806fc620c443ffa906221dfd483110ffca418887fd520c443bea906221ff1483110ffe8418887bf420c443ff2106221ff5083110f7a8418887fc420c413ff9906209f7cc83104ffc6418827fd320c443ee9906209ff0c831125fcc21888fff510c401ff2886200ff5443111ff8a21888bff410c445ff2086222ff50431117f88218827ff310c413ef9886209ff8c43104fec6218827fd310c401ee9886209fd4c43110ffe4218887fe210c443fe9086221ff0843104ffec018827fe600c4017f3006209ff58031005fac018827fc600c447ffa806223ff14031117fe801888bfe400c445fea006222ff1003110ffe4018887fe200c443fe9006221ff0803101dfacb28083ff64940417fb24a020ff99250015fcc928083fd64940417eb24a020ff19250015f8c92800fff5494007bfaa4a003ff9525001ffaa9280837d5494007fe2a4a000ffd8e50007fcc728026fe6394001feb1ca000bf58e50007f8c72800fff5394007ff29ca000df94e5001ffaa72800ffc5394007be29ca020ffd0e50107fc8728083fd4394041fe21ca01fffd8a500fdfec52807ffe62940037f314a01fff58a500fdfac52807ffc62940037e314a003ffd4a5001efea52800ffe5294007fea94a01fdf54a5001ff8a52807fff429403fdfa14a01fff90a500fffa852807fbd429403ffe214a01fffcca500ffbe652807ffe329403ffe994a01ff74ca500fff86528003ff6194001ff30ca000bf98650007fac328002fd6194001fe30ca003ffd465001ffca3280037e5194007fea8ca003ff1465001ef8a328083ff4194041ff20ca020ff50650107f88328003ff3194001ff18ca000ff4c650007f8632807fff219403fff10ca01fff486500fff8432800efe6094007ffa84a003dfd425001ff6a12800ffc5094007fc284a020ffd0250107fc8128083fd4094041fe204a01fffc82500fffc412807ffd209403ffe104a003bfd95500f7fec8a807aff645403dff322a002bf991500f7fac8a807afd645403dfe322a002bf1915001ffea8a800f7f5454007ff2a2a003ff551500f6faa8a800ffc5454001ffb1aa000bfd8d50007fcc6a8003fd6354001fe31aa009bf18d5001ffea6a800ffe5354007fea9aa003ff14d500f7fe86a807bfe435403dfea1aa01eff10d500effec4a8076ff625403bf
  | 5 => 0xb3104ffe6598827df32cc413ff1966209ff4cb31157ba6598827fc32cc459ffa8e6200ff94731007faa3988b3fc51cc457ffa0e622bff9073115ffa83988affc41cc455ff90e622aff88731157fa43988abfc21cc413ffb066209ff98331005fcc198827fd60cc4017eb066209ff18331167fea1988b3fc50cc457ffa06622bff9033115ffa81988affc40cc455ff906622aff88331157fa41988abfc20cc401ffb2c6200bfd963114ffccb1880efe658c401feb2c6200bf5963114ff8cb1880efc658c451ffb246228bfd9231147fcc91880afe648c451feb246228bf59231147f8c91880afc648c451ffaa46228dfd5231147fca9188a3fd548c451beaa46228ff1523112dfac7188a7ff538c453efa9c6209ff94e31007faa718827fc538c453ee29c6228ffd0e3104ffc87188a3de438c451fea1c6228f750e3104ff88718893ff628c4497fb146224ff98a3100dfcc518893fd628c4497eb146224ff18a3100df8c518893ff528c449bfa946224ff94a31127faa5188937d528c449fe2946224ffd0a311277e8518893fe428c449fea146224ef50a31127f88518827ff328c449ef9946224ff8ca31127fa6518893dd328c413fe1946209bf9863114ffea318803fe518c401fea8c6229ff14631147fe83188a3fe418c451fea0c6228ff1063104ffe6318803df318c413fb98c6224ffc8631127fc4318893fd218c449fe10c6200ffd8231007fcc118802fe608c401feb046200bf58231007f8c1188a7ff508c453fe2846228ffd0231147fc81188a3fd408c451fe2046224ffc8231127fc4118893fd208c449fe1046200ffd9531005feca988037f654c4013fb2a6227ff9953101dfcca98803fd654c4017eb2a6227ff1953101df8ca988037c654c4073e32a6226ffd9131135fec89889bfe644c4057f3226226ff59131135fac89889bfc644c4057e3226226ffd5131136fea89889bfe544c44dfeaa26226df55131137f8a89889fff534c413ff29a6200ff54d3104ff8a69889bff434c413ff21a6226ff50d3104ff88698897ff624c44b7fb126225ff9893100dfcc498897fd624c44b7eb126225ff1893100df8c498897ff524c44bbfa926225ff9493112ffaa4988977d524c44bfe2926225ffd093112f7e8498897fe424c44bfea126225ef5093112ff88498827ff324c44bef9926225ff8c93112ffa6498897dd324c413fe1926227ffd4531007fca298803fd514c44ffe28a6226ffd0531137fc829889bfd414c44dfe20a6209ffcc53104fee6298803fe314c401ef18a6225ffc853112ffc4298897fd214c44bfe10a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c09889fff504c44ffe2826226ffd0131137fc809889bfd404c44dfe2026225ffc813112ffc4098897fd204c44bfe1026209ffd943104dfeca18
  | 6 => 0x1fe324a202bf1925101ffea92880f7f5494407ff2a4a203ff55251186faa92880ffc5494401ffb1ca200ff98e5104dfcc728803fd63944017eb1ca200ff18e5101ffea72880ffe5394401bf29ca203ff54e5101ff8a72880f7c5394461ffa1ca230ff90e51187fa87288c3fc439445fffb14a22fbfd8a5117ffcc528806fe629445ffeb14a22fbf58a5117ff8c528806fc6294407ffa94a203dfd4a5101ffca52880ffd529445fbea94a203ff14a5117ffe85288bfbf429445fff214a22fff50a5117f7a85288bffc429445fff994a22ff7cca5117ffc65288bffd329445fee994a22fff0ca5101dfcc32880fff5194407bfa8ca203fdd465101ff8a32880ff45194461ffa0ca230ff90651187fa83288c3fc419445fff90ca22fff8865117ffa43288bffc2194401ffb04a200ff98251005fcc128803fd60944017eb04a200ff1825101ffea12880ffc5094407be284a230ffd0251187fc81288c3fd4094461fe204a22fffc825117ffc41288bffd209445ffe104a203bfd9551177fec8a88baff645445dff322a202bf99151177fac8a88bafd645445dfe322a202bf1915101ffea8a880f7f5454407ff2a2a203ff55151176faa8a880ffc5454401ffb1aa200bfd8d51007bec6a8802df6354401ff31aa200ff58d51007f8c6a8826fc6354401ee31aa200b718d5101ffea6a880ffe5354407fea9aa203ff14d51177fe86a88bbfe435445dfea1aa22eff10d5116ffec4a88b6ff625445bff312a201bf9895116ffac4a88b6fd625445bfe312a201bf1895101ffea4a880f7f5254407ff292a203ff5495116efaa4a880ffc525445bffa12a22defd095116ffc84a88b7fd425445bdea12a22dff1095116ffe64a88b7df325445bff192a22dff4c95116fba64a88b7fc32544077fb0aa203ffd455101feea2a880ffe5154401bf28aa203ff1455101ef8a2a880ff4515445dffa0aa22eff90551177fa82a88bbfc415445bff90aa22dff8855116ffa42a88b7fc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a200bf1815101ffea0a880ffc505445dffa02a22eff90151177fa80a88bbfc405445bff902a22dff8815116ffa40a88b7fc2054413ffb2e6209bfd973104ffccb9880efe65cc413feb2e6200bf5973104ff8cb98826fc65cc413ffb266209bfd933104ffcc99880afe64cc413feb26622bbf5933104ff8c998826fc64cc457ffaa6622bdfd533115ffca9988affd54cc457beaa6622bff1533104ffea798827fe53cc413fea9e6209ff14f3104ffe8798827fe43cc413fea1e6209ff10f3104ffec598826ff62cc413ff3166201bf98b3104ffac5988aafd62cc413fe3166201bf18b31157fea5988ab7f52cc455ff296622aff54b31156faa5988abfc52cc455ffa16622aefd0b31157fc85988abfd42cc455dea16622aff1
  | 7 => 0x900000100900000000200400000800301300000500600000200000c00000400400300d00000c00000100200300500000000000100100500600500000100100001300a00000b00000302900100100200100500000000000100400000800100600000100000600000800100400200100000300000200100400100100200100100000300100100200100000700200100000100000100000200900100000000700000000b00200000f00000000400400000000000001900300200000101300200200200000b00003700001dfacb29827ff6494c137fb24a609ff99253015fcc929827fd6494c697eb24a609ff1925304df8c92980fff5494c07bfaa4a603ff9525301ffaa9298d37d5494c07fe2a4a609bf98e5304ffea7298277f5394c07efa9ca603d7d4e5304ff8a729827dc5394c13ffa1ca609ff90e5304ffa8729827fc4394c13ffb14a609bfd8a5304ffcc529806fe6294c13feb14a633bf58a5304ff8c529806fc6294c07ffa94a603dfd4a5301ffca52980ffd5294c67bea94a603ff14a5319ffe85298cfbf4294c67ff214a633ff50a5319f7a85298cffc4294c13ff994a609f7cca5304ffc6529827fd3294c67ee994a609ff0ca5304ffec329827fe6194c017f30ca609ff58653005fac329827fc6194c07ffa8ca603ff1465301ef8a3298d3ff4194c69ff20ca634ff506531a7f883298cfff2194c67ff10ca633ff4865319ff84329827ff6094c13ff304a600bf9825304ffac129802fd6094c13fe304a603ffd425301ff8a12980f7c5094c69ffa04a634ff902531a7fa81298d3fc4094c67ff904a633ff8825319ffa41298cffc2094c137fb2aa632ffd9153195fec8a98cbfe6454c057f322a632ff59153195fac8a98cbfc6454c057e322a603ffd515301efea8a980ffe5454c07feaa2a632df5515301ff8a8a980eff6354c07ffa9aa603f7d4d5304ffca6a98277e5354c13fe29aa609df14d5301fb8a6a98cbff4354c13ff21aa632ff50d5304ff886a98c7ff6254c637fb12a631ff9895300dfcc4a98c7fd6254c637eb12a631ff1895300df8c4a980fff5254c07bfa92a603ff9495301ffaa4a98c77d5254c07fe292a631ffd095318f7e84a98c7fe4254c63fea12a631ef5095318ff884a9827ff3254c63ef992a631ff8c95318ffa64a98c7dd3254c13fe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff18553005f8c2a980fff5154c07fe28aa632ffd0553197fc82a98cbfd4154c65fe20aa631ffc855318ffc42a98c7fd2154c63fe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff18153005f8c0a980fff5054c07fe282a632ffd0153197fc80a98cbfd4054c65fe202a631ffc815318ffc40a98c7fd2054c63fe102a603bf59651187fec9288c2ff6494461ff324a202bf99251187fac9288c2fd649446
  | 8 => 0x39200032400000055a0000f25e41e40000009608625fa6a2acc81686e0000000000000001560000004cc79c9664ee000478802000d0e542a607124ba7285a26f03b400079e00044e92229cb0a0000003ca00040402ab5c0003a6ce06d832e000b7800066400034a2ec8920000006c600000004c63a84882800017600021200000002e0000000000000000008d8000c3200000051800484a0008420081880000000000000004340000ba6a89deb92492afe3e000049a70e0400009523c00000bc5eaa9c6144de000b24cd2046cca00078ac9c000000000000000000000616000000b5a83e092000c70a3400000000051c50e98ebcc000000cb6000ac260e0000000008120000005f400000065e87439013a2280000007ea0000000000000000000005742440006940000000000000000002840008fa00060a7fa42c2a40005ba3fe548000000000000c047f650c5060003a8000000abe748aca00045a00066263ed2c000000c8a00002a00000300100400800000400f00500000503c00200100101200002e00200100800000000100100000500000000000000100400000100000100200000100000000200201200400600a00100000300000000100300100300b00000500200501000d00300500f00f02000000300300000500600000000100000001600000100400900700400000100c00000000000a00500700100200000000b00000200000000000800c00100100100600300000000000000000100d00500300000000000000000000000100000200000700e01a00000100000100200500300900000300000000600000301600000100000000400200200900200000000200400000500100100000100200300500300800001100000100000300200400100300900c00700000000600900100100400100100000100101100200100200900200100000e00300a00400000000102500400800300000000000000000600700200200d00400000000000000300200700100700000000301400500100000000000c00000000100000400100000900100700200000000200100e00000000000300300000e00c00100000100e00000100000500000200300200000100300800000000200000700000100200000100300200000000300000000000000400c00100100200200800000000000400100100100600100200800300400700300200400000200100000a00000000600200100000000900500500500101d00000100300300300200000900000000000000000300300000300100000400f00400200500100000000100600200100e00800400000800100001700000100000000000100000400100900500a00100500f00a00000000300100600700a00000000100300100000000000100200700c00000100600000600000600500000000600400000400000000
  | 9 => 0xb80000005540003103360000007b00009aa00000000000000000038ccda000d7a0000002f8000b2c584d029087ec000442bf24f80006420004f00000000000002e60000000000000009366920001683c4c9024e5120008aa00078e000762770d5250a46232036ec4e86ca38be41da1520e822eafc0ce7082d45245bc790bd009e62030622cd483320d0c1a0a094620c4d29c0788c48b48a2494e13eab4120bd22781ba09a27c8dc69693409c4569f854641275eb50bca55c2a045c49c140088596962538a5a7844e09fe858a84ca891e1c24b6138aec724af2226cb072041cbe8000000a98000000000906d30b4481c65abc62bc6be7b69d04ac05600099219872cb7c63825e134aac8f467a000000d32372000bf822268471a000260000000742000d2a000000000000a745520000007389f69d600016c000d261d00002525de0deb8e0008e288a68a9303263ba0009be000000b8800000000000085c1ee0000fc3fa000ab2d06000c5838e000c529ac0f41e6776c624b80740007682b0522ccccae0e078c0007d41d2000030a08000cd60000008c2000bb8000840b460000002d800000059cbcece8998c168ce3669f2bb459012621405ace2cf21240d81ca00042a37013c36a1943d422a000272ac81b8210a220000000000000000000005260008d600000000000260c7825440000002c8a4870a000a3a0007642d2b4c000000000466000d180000001a8328d6c31c000000d2e7c6bc4000000000d0a6f2000000000986000cb214a0001320c60000000000000700000002206260000008a2a8e7500000c898a000d5857640e8a00003627a47220004ae6c09fc00088e7f0b3c34c0000ae7268e67b800ed24c2e5b600000039c0001fc1a0bfa7cecf400058245410cd54c929ea9ce07a000000000000000c1c0000008365a4000a6c238c1000007ca4e31e00000075200000000087e0007e40428e05c0000c6618e8da5b095426ca6e00000000000000099c6de00000092a15e1b43ee000a660860ac8a6bde0008540000001fe60210ec4089669010000000000006e2985d82660000005089966440004ce000000b9ad66368ca24208003ccae005ca628506c417200000000046c990a803a20000000000000000000004820009e8000000bb67c8304184a92d16b6a000a1e3c63ce000b147b4048d760000001ae0004fe0000a8000000000aa69dc00061c000a2e000000000000000000bf638262c000a2ac0a4180005aa92c53a000250000000aba17a01a16a314b3098cb56c8e0003c20000006dac22000aa80007eed5c0000000000004a4628000000000810000000a54822c60000b723f22c60008aea6a35e736714034000670aa2000000a52000000000000000380000d56c464ecc7a000b869ec2ce5be0000004360000000007dea78378000000
  | 10 => 0x963d0000000000000000b7e83852872e2561700aa1b200068c2b809861e3447e23bea320006b200082e67e0000002645d0000ac0000976000406000b2ebdcc6c03c000aaa000000000000650000cee0e2c341d4a40c3a3a03fc8fe000d5e6bc0006040000003582ae7040009c80000000000000003d80000002be28a0006d218200051e71684e6ae000000abc00036c6b4000000a7a0007dcd3e4d40004aa000000000cd846e7aeaf40000000008a4b3a000000b28000000556a189b6b4a8867e80002debf05b4d600000000000000003881506865002a661a7548902ac7064f28cc97e47608e166a1600000024c6c800000000000000049ea50000c20000b0800000000000000000000082064c23e0000005b80000000000001100000008c820095a000000000000276000d5000000086469a8842ca000000000118000000000a449848987d825a8a8b8a8d091c85684c5e295897aa4a02237e56c000000ca071ca9483aae44940000000006300005700005044464e27106b83e479ad143a4b2678600064a0000c2c6e000000d70c0847a8ec0001d8b740c40e66181a48b4322cc6bc869c8ba00000082688000098800000094419c54c9d8606000000000000b0c1362245a840ace40a200000058c0003e26b61f039831218639e0a40000000000005200000000003f4000000a060000000000000009a45e80006460009c646800000096c00097200000000000076e000000d2800042e80ca96c8cb4e0000002e0308490000000000000000c4a50200000062e000a7c5660000000000003000002bab220000000000006f8732be24c2000000a20000000c724260000000000000000000000000665d46e462a77cb64b82ac497c654000000668000a145a0540b6c0008780000000000000000ee0003f60009480001e07ca000d745f6458000000bbe2fe95089ac0280474ec0c12c920aee1c02b40000000008940001ac00067c4c015a4fc21a0004a682a8ee000978000282360cdc00018a4d671ed40268c882e452eb3848eb620001fa10a0be032a8c0000006ba0000000005cc7960008c6b200c0cbe47c000bb000028c0005ecc2ad1e1c89da4d0666000000000000b0e000bd881ec24824000d62000000000000000ae20000008767e60000ec1461de45e028000234580c944bcd4491a000a309a6af800000032ac5403695686a560b5e59a5e6b96c862fa90c0000005e03b0000c683ec0000008ca0004305723dcc9ea04cbc00000055e338640000730d3881a46a3aa0005342948f200074471875a05453e39634e7c287ab80000020636000000942026b32000000c7444a7a85584222909c4000000ba81d66d0a640e42cc0000000003b2000ae800000000000011a0000009826e6242000000000000000180000206000000c5a000000a0a000000c
  | 11 => 0x1aa4be0000000005c44ca0fe0003641f28fccd0280a56058bc0b600000000000000000a6ca66e80005a652c9a0452c76a260000006825b22dc12ea2c74000021c2f2038d3a9ba00099a37c33a9d42da000b5257a5920008f8000cf600000000000038a0000ca00056200a0d29bc00000079400000030c0006cc3f80cc9b47fe00092800000001c000d208ac000000550000354000000072bd63deab0cc40007d29b08bc342cacb584703b672a3ac37a00014437493e2e8cba8b814c844532a0c2320008c000033e000c14bb2b7a0b20004b258eb2a0008d2000a120000000001920000b44f49e6b407584240da2700009641cc0000000000000000000000008ea4a0000974000c1e2c2d36000610900c12000938000ba67d08e87aa00001497089c2407c0000204000116cd4ad017e6e266a656792becd6aab600023a7a6a8a33451a04467800043a80a914000c00000000000000bd47801905f816234600000024826e9a29fa0008f66c21602c499e2b60009b8142a86230bc20000004e4a58860d00c44000000caa0005d200049676091870cc640001306ea7cc00021e00000608cd4c69843235ad6800000080e598aae174bae86600000000058ac0ed340003ead0c00093cb7651000000041e01811e35000000026a20ac9618cc289d29e29ae000000d2253c000c18000a3c53604a06a1b05ca6dc7f2832000000a765d64147f8632c369323b80ea00074a00006c1dc00000031817c000000d640005f2000d0800000000000006465c000000ba00000000008d44165308c4000000d7852a25ca5c1960005fe0000000001067e00001f60005c2486b180005865c8cc80000000000600000009f40000000007b2000cfa660a10000000d7e0000000000000003d60000006760000900002a8000000000bf4000000384aa401002c7a000000068e0000006a4000000cf0b6e0006b00000000000007660000001580000000008bea72ab83bc000024ad80000000000000000fa8060009261ec0004d8000aa0448000000000000000000000000000a1c4e600000000012220e588ae6050000b34000d5a1b66f6c7eb0200075675c0521785f00b086873a00c0d4d10068000aeaba47ba000000b9404e00085a00095c000000baa000000a464fabfc3d24409e462291244c5ae4a8a1a8b61a611211c8342082026aa6d44c6a88000cce00000000063416ea9e34030a25400000000066c41000040200000035c0006d66ce000000a7030200000000005e9160004744da0002f043833cc4c7c4d0443ecfea5e000000600b060000000009ee000000000000000ace88c93a96ea82000ad419e39a2460000000008522860000006ca00085e0000007bc0007a2000cc2a4c03a57ea9a400ade8083e8000000000000000bfe0006fa000000000000000c5000067200000
  | 12 => 0x394cecaf02e2000000000000000b9e000000000cb400015c0000004080005ce330000000000980830a900000940001022c05c69b20008461f400088800000000082c0000000000000004b00006880000000000004985ac00074c000c26000d3c3da00000000000000000000001291028eb3e6ac0005fc00028830eba20002a22fc9cccf8d4261264e000c3094c0f81ea5ee000356a280000001088b27781f8b9895e48a46083c870000c566ec0007340000006a073c3f0000700000b1c00048c000000000bba0007746586a68f0c3e92e216b84000b1e14eb8c48468012873e6fc7be000cfc3ae60857ca0266e7da0f01e2d468140f6b160001e80b696a00000008a0000dc00000000023cca40000001ce29a0b80000004800000009a887c000292d1a0008822747fc37654a2d0b12af6d1200003e4b4000000ce6000cde00000090a2585da0001144280009f0000d6e444000000b42000000c82818c98000ac60000003e600000007e000000000000000cea43c772000000c84000648000ad69400800000003160d66fe76ac7c1c6000000ad2c5e7d6514000000000a7e1a20003480009c20005dca6800056840cbe6b9032c4e819a016674d7cadab684727acadc000c0651629e154bac488c786524c4000464b04352b368b0062bee2d6b002f4000b1a00059e54e076000b66000000000a0e0000008de0001bc77ac2c0781648720002f624a000000b540000000000000000000009ca2ee62427e4c8c3cbbcbea0006ee000c380000009680000000003c81c400047ea3e702b7012a27a00063c0004a22180000000000000004dcd4e41a76cb102ead72924994000000afa0000000821046f456a262d4abe0c4256490ec6a4ea29679889ea0031a7f4d1c6e056ec8094acc0c5c000450000746a360000004f6578a4269e084000bda0005940000002b28e490201e000b9c0000000001be2362aac9a14800000077e9e0386904000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe6394c10006dd6394c100375f5394c10004ff7654c10004fe7654c10004fd7654c10004fc7654c1001e7e6554c100067d6554c1004ede6354c10006dd6354c10084ff769441001cfd769441001e7e65944100067d6594410005fa7094410005f97094410084ff7654410005df7354410005dc7354410004fd76cc410004ff768c41004cfd768c41004ede638c410006dd638c410005fa708c410005f9708c410004ff764c4100057f754c4100357c754c41004cff760c410004fd760c41004ede630c410006dd630c410005fa700c410005f9700c410074ff769401001cfe769401001cfd7694010034fc769401001e7e65940100067d6594010005f67194010005f57194010074ff7654010004fd76cc010004ff768c01004cfd768c01004ede638c010006dd638c010005f6718c010005f5718c010004ff764c0100057f754c0100357c754c010005bf744c01002dbc744c01004cff760c010004fe760c010004fd760c01004cfc760c01004ede630c010006dd630c010005f6710c010005f5710c010046f576c4010206f764c4010206f564c40102077754c40102077554c40101fef762c40101fef562c40101ff7752c40101ff7552c40101ffb742c40101ffb542c40101ffd732c40101ffd532c40101e5f571840101def66184010025f9768401003ef9768401000cf976840101f77b54840101f77954840101eefb62840101eef962840101ef7b52840101ef7952840101efbb42840101efb942840101efdb32840101efd932840101e5f971840101defa6184010007f26184010004ff76440100057f75440100357c7544010005bf744401002dbc7444010005df7344010005dc7344010005ef7244010025ec7244010005f77644010006f77644010004f77644010007777544010007747544010007b774440101b7b474440101b6f764440101b6f564440101b77754440101b7755444010007d77344010007d47344010007e772440101afe472440101aef762440101aef562440101af7752440101af7552440101afb742440101afb542440101afd732440101afd532440101d5f770440101cef66044010007f25044010007f150440101b7f340440101b7f04044010007f23044010007f130440101aff220440101aff12044010005fb7644010006fb7644010004fb76440100077b7544010007787544010007bb74440101b7b874440101b77b54440101b7795444010007db7344010007d87344010007eb72440101afe872440101aefb62440101aef962440101af7b52440101af7952440101afbb42440101afb942440101afdb32440101afd932440101c5fb7144010007f371440101befa6144010007f26144010007f25144010007f151440101b7f341440101b7f04144010007f23144010007f131440101aff221440101aff12144010
  | 1 => 0x4110227e862c41102277b52c41102277952c4110227bb42c4110227b942c4110227db32c4110227d932c411022ff241c411022ff141c4110227f221c4110227f121c41100067f65841100767c6584110006bf648411006ebc6484110006df6384110006dc6384110006ef628411003eec6284110055f6768411000777658411000774658411021df7748411021df57484110007b76484110217b46484110217775484110217755484110007d76384110007d463841101cdf772841101cdf57284110007e7628411020fe4628411020f77528411020f75528411020fb7428411020fb5428411020fd7328411020fd53284110007f3608411020ff2208411020ff120841100367e65d9410034fd75d9410004ff74d9410014fe74d9410004fd74d9410014fc74d94100367f54d94100067d54d941004cfe73d9410004fd73d94100367c53d9410004ff72d941000cfe72d9410004fd72d941000cfc72d94100367f52d94100067d52d9410006bf42d9410006bd42d9410006df32d9410006dd32d9410084fe71d9410006f671d9410074fe70d9410006fa70d941001cff76594100367c65594100067f7559410004ff7459410014fe7459410004fd7459410014fc74594100367f54594100067d5459410004ff735941004cfc73594100367f5359410004ff725941000cfe7259410004fd725941000cfc72594100367f52594100067d5259410006bf4259410006bd4259410006df3259410006dd325941001cff715941001cfd7159410034fc71594100367c515941001cff705941001cfd7059410034fc70594100367c505941001cfe75d8c10004fd75d8c1001cfc75d8c10004ff74d8c10014fe74d8c10004fd74d8c10014fc74d8c100067f54d8c100067d54d8c10004ff72d8c1000cfe72d8c10004fd72d8c1000cfc72d8c100067f52d8c100067d52d8c10006bf42d8c10006bd42d8c10006df32d8c10006dd32d8c10004fe71d8c10006f671d8c10004fe70d8c10006fa70d8c10004fd7698c10006df6398c1004cff7658c100057f7558c100357c7558c10004ff7558c100067f7558c100047f7558c1001cfe7558c1001cfc7558c100067c7558c1001c7c7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c100067f5458c100067d5458c10006df7358c10006de4358c10006dd4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c100067f5258c100067d5258c10006bf4258c10006bd4258c10006df3258c10006dd3258c1004cff7158c1004cfd7158c1004cff7058c1004cfd7058c100357e7518c100057d7518c1002dbe7418c10005bd7418c1004ede6318c10006dd6318c10025ee7218c10005ed7218c1004cff7694c10004fe7694c10004fd7694c1004cfc7694c100067f6594c1001e7c6594c1004ed
  | 2 => 0x6ef51d8910006ec51d8910006ef41d8910006ee41d8910006ed41d8910006ec41d8910006ef70d8910056ee70d8910056ed70d8910056ec70d8910006ef50d8910006ec50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d8910056ed10d8910074fe76945100067f659451001e7c6594510006bf6494510186bc6494510006df6394510006dc6394510006ef629451017eec629451001cfc76545100067f655451001e7c6554510006bf6454510176bc6454510005df7354510005dc7354510006df6354510006dc6354510006ef625451016eec6254510067745154510005fb7054510005f87054510004fe76cc5100067f65cc5101667c65cc510006bf64cc51015ebc64cc510006df63cc51004edc63cc510006ef62cc510156ec62cc510005fa70cc510005f970cc510004fe768c5100067f658c51014e7c658c510006bf648c510146bc648c510006df638c51004edc638c510006ef628c510126ec628c51004cfc764c5100057f754c5100657c754c5100067f654c51013e7c654c510006bf644c510136bc644c510006df634c51004edc634c510006ef624c51012eec624c510005fb704c510005f8704c510004fe760c5100067f650c51011e7c650c510006bf640c510116bc640c510006df630c51004edc630c510006ef620c51010eec620c510007d5310c510084fe76941100067f659411001e7c6594110006bf6494110106bc6494110006df6394110006dc6394110006ef62941100feec629411001cff7654110064fd765411001cfc76541100067f655411001e7c6554110006bf64541100f6bc6454110006df6354110006dc6354110006ef62541100eeec6254110005f77154110005f47154110004fe76cc1100067f65cc1100e67c65cc110006bf64cc1100debc64cc110006df63cc11004edc63cc110006ef62cc1100d6ec62cc110005f671cc110005f571cc110004fe768c1100067f658c1100ce7c658c110006bf648c1100c6bc648c110006df638c11004edc638c110006ef628c1100a6ec628c11004cff764c110004fd764c11004cfc764c1100057f754c1100657c754c1100067f654c1100be7c654c110005bf744c11005dbc744c110006bf644c1100b6bc644c110006df634c11004edc634c110006ef624c1100aeec624c110005f7714c110005f4714c110004fe760c1100067f650c11009e7c650c110006bf640c110096bc640c110006df630c11004edc630c110006ef620c11008eec620c110007d9300c1100067f65c41100867c65c4110006bf64c411007ebc64c4110006df63c4110006dc63c4110006ef62c4110046ec62c41100077b65c41100077865c4110007bb64c411022fb864c411022f7b54c411022f7954c4110007db63c4110007d863c41101bdfb72c41101bdf972c4110007eb62c
  | 3 => 0xc6218d10006cc6218d100075f5218d100075d5218d100079f4218d100079d4218d10007d64118d10007d54118d10007d62118d10007d52118d10007da2018d10007d92018d1004edf7518d1004ede7518d1004edd7518d1004edc7518d1004edf7418d1004ede7418d1004edd7418d1004edc7418d10006df5418d100065f5418d10006de5418d10006dd5418d100065d5418d10006dc5418d1004edf7218d1004cdf7218d1004ede7218d1004edd7218d10004dd7218d1004edc7218d10006df5218d100065f5218d10006de5218d10006dd5218d100065d5218d10006dc5218d10006df4218d100069f4218d10006de4218d10006dd4218d100069d4218d10006dc4218d1004edf7118d1004edd7118d10006df5118d10006dc5118d10006df4118d10006de4118d10006dd4118d10006dc4118d10006df2118d10006de2118d10006dd2118d10006dc2118d1004edf7018d1004edd7018d10006df5018d10006dc5018d10006df4018d10006de4018d10006dd4018d10006dc4018d10006df2018d10006de2018d10006dd2018d10006dc2018d10006dd1018d1004cff7694d10004fe7694d10004fd7694d1004cfc7694d100067f6594d1001e7c6594d10006bf6494d101a6bc6494d10006df6394d1004edc6394d100675f5394d1019eec6294d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d10006bf6454d10196bc6454d10006df6354d1004edc6354d1018eec6254d10005f77154d10005f47154d10055ee76d8910056ee76d891000cee76d89100076f75d89100076c75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910007af74d8910007ac74d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d89100076f54d89100076d54d8910007cf73d8910007cc73d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e771d8910057e471d8910007e641d8910007e541d8910007eb70d8910057e870d8910006ef75d89100066f75d8910006ee75d8910006ed75d8910006ec75d89100066c75d8910006ef74d8910006af74d8910006ee74d8910006ed74d8910006ec74d8910006ac74d8910006ef54d89100066f54d8910006ee54d8910006ed54d89100066d54d8910006ec54d8910006ef73d8910006cf73d8910006ee73d8910006ed73d8910006ec73d8910006cc73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910056ee71d8910056ed71d8910056ec71d8910
  | 4 => 0x8d100075f54d8d100075d54d8d10005df72d8d10005dd72d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d100075f52d8d100075d52d8d100079f42d8d100079d42d8d10007d641d8d10007d541d8d10007d621d8d10007d521d8d10007da20d8d10007d920d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d100065d54d8d10006dc54d8d10006df72d8d10004df72d8d10006de72d8d10006dd72d8d10004dd72d8d10006dc72d8d10006df52d8d100065f52d8d10006de52d8d10006dd52d8d100065d52d8d10006dc52d8d10006df42d8d100069f42d8d10006de42d8d10006dd42d8d100069d42d8d10006dc42d8d10006df71d8d10006dd71d8d10006df51d8d10006dc51d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df21d8d10006de21d8d10006dd21d8d10006dc21d8d10006df70d8d10006dd70d8d10006df50d8d10006dc50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d100657e7598d100057d7598d100067f6598d100067c6598d1005dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10055ee7298d10005ed7298d10006ec6298d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10005ef7258d10055ec7258d10006ec6258d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d100067f5458d100067d5458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d100067d5258d10006bf4258d10006bd4258d10006df3258d10006dd3258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d1004ede6318d10006dd6318d10006ec6218d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5418d100075d5418d10005df7218d10005dd7218d10006df6218d10006de6218d10006dd6218d10006dc6218d10007c
  | 5 => 0x6df3259510006dd3259510074ff7159510006f77159510084ff7059510006fb70595100057e76195100667e76195100047e76195100657f74195100057d74195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100657f72195100057d72195100067f62195100067e62195100067d62195100067c62195100076c62195100066c62195100073f42195100073d42195100075f32195100075d32195100077641195100077541195100077621195100077521195100077a201951000779201951005dbe76d911005ebe76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d91100073f52d91100073d52d91100079f32d91100079d32d9110007b771d911005fb471d9110007b621d9110007b521d9110007ba20d9110007b920d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d91100063d52d9110006bc52d9110006bf32d91100069f32d9110006be32d9110006bd32d91100069d32d9110006bc32d9110006bf71d911005ebe71d911005ebd71d911005ebc71d9110006bf51d9110006bc51d9110006bf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d911005ebe70d911005ebd70d911005ebc70d9110006bf50d9110006bc50d9110006bf20d9110006be20d9110006bd20d9110006bc20d911005ebd10d911004cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10006ec62d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d10006df53d8d10006dc53d8d10006df43d8d10006de43d8d10006dd43d8d10006dc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d100067d52d8d10006bf42d8d10006bd42d8d10006df32d8d10006de32d8d10006dd32d8d10006dc32d8d1004cfe71d8d1004cfc71d8d1004cfe70d8d1004cfc70d8d1004cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d
  | 6 => 0x732c4210237d532c4210005f976c4210006f976c421023f7b54c421023f7954c42101ddfb72c42101ddf972c42102377b52c42102377952c4210237bb42c4210237b942c4210237db32c4210237d932c421001cfe76d95100667e65d9510006bc64d9510006ec62d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100667f54d95100067e54d95100067d54d95100667c54d951004cfe73d9510004fd73d95100667f53d95100667c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d95100667f52d95100067e52d95100067d52d95100667c52d9510006bf42d9510006bd42d9510006df32d9510006dd32d951001cfe71d9510064fd71d951001cfc71d95100667f51d951001cfe70d9510064fd70d951001cfc70d95100667f50d95100657e76d951001c7e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100057f72d95100057d72d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95100073f42d95100073d42d95100075f32d95100075d32d95100077641d95100077541d95100077621d95100077521d95100077a20d95100077920d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100047f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100065f32d95100067e32d95100067d32d95100065d32d95100067c32d95100067f71d95100667e71d95100067d71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f21d95100067e21d95100067d21d95100067c21d95100067f70d95100667e70d95100067d70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f20d95100067e20d95100067d20d95100067c20d95100667c6559510005bf745951005dbc7459510006bc6459510005df7359510005dc7359510005ef7259510055ec7259510006ec6259510064ff75595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc74595100667f54595100067d5459510004ff7359510006df7359510004df735951004cfc7359510006dc735951004cdc7359510004ff7259510006ef7259510004ef725951000cfe7259510004fd725951000cfc7259510006ec725951000cec72595100667f52595100067d5259510006bf4259510006bd4259510
  | 7 => 0x96100767f54d96100067d54d961004cfe73d9610006de73d961004cde73d9610004fd73d9610006dd73d9610004dd73d9610004ff72d961000cfe72d9610004fd72d961000cfc72d96100767f52d96100067d52d9610006bf42d9610006bd42d9610006df32d9610006dd32d9610006f571d96100767c51d9610006fa70d961001cff76596100767c65596100067f7559610004ff7459610014fe7459610004fd7459610014fc74596100767f54596100067d5459610004ff735961004cfc73596100767c5359610004ff725961000cfe7259610004fd725961000cfc72596100767f52596100067d5259610006bf4259610006bd4259610006df3259610006dd32596100767f51596100767c50596100757e75d8e100057d75d8e1001cfe75d8e100067e75d8e1001c7e75d8e10004fd75d8e100067d75d8e100047d75d8e1001cfc75d8e10004ff74d8e10014fe74d8e10004fd74d8e10014fc74d8e100067f54d8e100067d54d8e10004ff72d8e1000cfe72d8e10004fd72d8e1000cfc72d8e100067f52d8e100067d52d8e10006bf42d8e10006bd42d8e10006df32d8e10006dd32d8e10006f571d8e10006fa70d8e10004fd7698e10006df6398e1004cff7658e10004ff7558e1001cfe7558e1001cfc7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e100067f5458e100067d5458e10006df7358e10006df5358e10006dc5358e10006de4358e10006dd4358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e100067f5258e100067d5258e10006bf4258e10006bd4258e10006df3258e10006dd3258e1004ede6318e10006dd6318e1004cff7694e10004fe7694e10004fd7694e1004cfc7694e1001e7e6594e100067d6594e100775f5394e10004ff7654e10004fe7654e10004fd7654e10004fc7654e10064fd76946100067f659461001e7c659461001cff765461001e7e65546100067d6554610005df7354610005dc7354610005fb7054610005f8705461004ede63cc610006dd63cc610005fa70cc610005f970cc610006df638c61004edc638c61004cff764c6100057f754c6100757c754c61004ede634c610006dd634c610005fb704c610005f8704c610006df630c61004edc630c61001cfe769421001cfd769421001e7e65942100067d6594210005f67194210005f57194210034ff765421004cfd768c21004ede638c210006dd638c210005f6718c210005f5718c2100057f754c2100757c754c210005bf744c21006dbc744c21004ede630c210006dd630c210005f6710c210005f5710c210007d9300c210005f576c4210006f576c421023ef764c421023ef564c421023f7754c421023f7554c4210236f762c4210236f562c42102377752c42102377552c4210237b742c4210237b542c4210237d
  | 8 => 0x4fd74d9710014fc74d97100867f54d97100067d54d971004cfe73d9710004fd73d9710004ff72d971000cfe72d9710004fd72d971000cfc72d97100867f52d97100067d52d9710006bf42d9710006bd42d9710006df32d9710006dd32d9710006f671d9710006f970d97100867c50d971001cff76597100867c65597100067f7559710004ff7459710014fe7459710004fd7459710014fc74597100867f54597100067d5459710004ff735971004cfc73597100867c5359710004ff725971000cfe7259710004fd725971000cfc72597100867f52597100067d5259710006bf4259710006bd4259710006df3259710006dd32597100867c51597100867f50597100857e75d8f100057d75d8f1007dbe74d8f10005bd74d8f1001cfe75d8f100067e75d8f1001c7e75d8f10004fd75d8f100067d75d8f100047d75d8f1001cfc75d8f10004ff74d8f10014fe74d8f10006be74d8f10014be74d8f10004fd74d8f10006bd74d8f10004bd74d8f10014fc74d8f100067f54d8f100067d54d8f10006de43d8f10006dd43d8f10004ff72d8f1000cfe72d8f10004fd72d8f1000cfc72d8f100067f52d8f100067d52d8f10006bf42d8f10006bd42d8f10006df32d8f10006dd32d8f10006f671d8f10006f970d8f10004fd7698f10006df6398f1004cff7658f10004ff7558f1001cfe7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f100067f5458f100067d5458f10006df7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f100067f5258f100067d5258f10006bf4258f10006bd4258f10006df3258f10006dd3258f1004ede6318f10006dd6318f1004cff7694f10004fe7694f10004fd7694f1004cfc7694f1001e7e6594f100067d6594f100875f5394f10004ff7654f10004fe7654f10004fd7654f10004fc7654f10005f77154f10005f47154f1001cfd769471001e7e65947100067d6594710005fa7094710005f97094710034ff7654710005df7354710005dc735471008774515471004cfd768c71004ede638c710006dd638c710005fa708c710005f9708c7100057f754c7100857c754c71004ede630c710006dd630c710007d5310c710005fa700c710005f9700c710064fd76943100067f659431001e7c659431001cff765431001cfc765431001e7e65543100067d6554310005f77154310005f4715431004ede63cc310006dd63cc310005f671cc310005f571cc310006df638c31004edc638c31004cff764c3100057f754c3100857c754c310005bf744c31007dbc744c31004ede634c310006dd634c310005f7714c310005f4714c310006df630c31004edc630c3100767e65d9610005de73d9610005dd73d9610074fd75d9610004ff74d9610014fe74d9610004fd74d9610014fc74d
  | 9 => 0xf628c13028edd628c13028f5f528c13028f5d528c13028f9f428c13028f9d428c130006dc618c13004dde708c13004edf608c13004fdb608c13004e7f7559430004ff7459430014fe7459430004fd7459430014fc745943009e7f54594300067d545943004cff735943004cfe735943004cfd735943004cfc735943004e7e535943004e7c5359430004ff725943000cfe7259430004fd725943000cfc725943009e7f52594300067d5259430006bf4259430006bd425943004edf3259430006dd3259430004ff7159430004fc715943009e7f515943009cfc705943009e7c505943001cfe7598430004fd759843001cfc7598430004ff7498430014fe7498430004fd7498430014fc74984300067f54984300067d5498430004ff729843000cfe7298430004fd729843000cfc72984300067f52984300067d5298430006bf4298430006bd429843004edf3298430006dd329843004ef67198430006f64198430006f5419843004ef7319843004ef43198430006f62198430006f52198430004ff75584300067f75584300047f755843001cfe755843001cfc75584300067c755843001c7c7558430004ff7458430014fe7458430004fd7458430014fc74584300067f54584300067d5458430004ff725843000cfe7258430004fd725843000cfc72584300067f52584300067d5258430006bf4258430006bd425843004edf3258430006dd325843004ef77158430006f64158430006f5415843004ef7315843004edc315843004ef4315843004ed43158430006f62158430006f52158430004ff769443004cfe7694430004fd76944302867f659443001e7c6594430006f66194430006f56194430004ff7654430004fd765443004cfc765443001e7e65544300067d6554430005df735443004ddc7354430006f66154430006f5615443004ddd768c430006dd768c43014ede658c43004edc658c43004edf648c43027edd648c43027f5f548c43027f5d548c430275df728c430275dd728c43004edf628c43026edd628c43026f5f528c43026f5d528c43026f9f428c43026f9d428c43004dde718c43004fd6718c430006dd618c430005dd708c430266de608c43004fda608c4300ccff769403004cfe769403001cfd769403004cfc769403001e7e65940300067d659403004dde7394030005dd73940300ccff765403004ddf764c030006df764c030004df764c0300075f754c0300075c754c0300079f744c03025f9c744c03004edf644c03025edd644c03025f5f544c03025f5d544c030255df724c030255dd724c03004edf624c03024edd624c03024f5f524c03024f5d524c03024f9f424c03024f9d424c030005dc714c03004ddf704c03004fdb704c030246de604c03004fda604c0300867e65d9710084fd75d9710004ff74d9710014fe74d9710
  | 10 => 0x9130006bd71d9130006bc71d9130006bf51d9130006bc51d91302a6bf31d91302a6bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d91302a6bf70d91300b6be70d91300b6bd70d91300b6bc70d9130006bf50d9130006bc50d91302a6bf30d91300b6bd30d91302a6bc30d9130006bf20d9130006be20d9130006bd20d9130006bc20d913001cfc7654d300067f6554d3001e7c6554d30006bf6454d30196bc6454d3004f5c5354d30005fb7054d30005f87054d300067f65d85300067c65d8530006bf64d8530006bc64d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d85300067f54d85300067d54d8530004ff72d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006bf42d8530006bd42d8530006df32d8530006dd32d8530006f721d8530006f421d85300bd7e75985300057d75985300067f65985300067c65985300b5be7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300bd7c75585300067f65585300067c6558530005bf74585300b5bc7458530006bf6458530006bc6458530005ef72585300adec72585300067f65185300067c6518530006bf6418530006bc6418530006f5611853001cfe7518530004fd751853001cfc7518530004ff7418530014fe7418530004fd7418530014fc74185300067f54185300067d5418530006de4318530006dd4318530004ff721853000cfe7218530004fd721853000cfc72185300067f52185300067d5218530006bf4218530006bd4218530006df3218530006dd3218530006f72118530006f42118530004fe7694530004fd7694530004fc76945300067f659453001e7c6594530006bf6494530186bc6494530004ff7654530004fe7654530004fc76545300067f655453001e7c6554530006bf6454530176bc6454530005df735453004ddc73545300067f658c53014e7c658c530006bf648c530146bc648c530006f7618c530006f4618c530005fa708c530005f9708c5300057f754c5300bd7c754c5300067f654c53013e7c654c530006bf644c530136bc644c530006f7614c530006f4614c53004fd4314c530005fb704c530005f8704c53004fd8304c5300e4fe76941300067f659413001e7c6594130006bf6494130106bc64941300bf7b509413001cff76541300bcfd765413004cfc76541300067f655413001e7c6554130006bf64541300f6bc6454130005df735413004ddc73541300067f658c1300ce7c658c130006bf648c1300c6bc648c13004dfa708c13004efb608c1300075f658c1300075c658c13029ddf748c13029ddd748c1300079f648c1302979c648c1302975f548c1302975d548c130245df728c130245dd728c13028ed
  | 11 => 0x67f73d95302b67e73d95300067d73d95302b67c73d95300067f43d95302b67e43d95300067d43d95302b67c43d95300067f72d95300047f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067f42d95300063f42d95300067e42d95300067d42d95300063d42d95300067c42d95302b67f32d95300065f32d95300067e32d95300067d32d95300065d32d95302b67c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95302b67f31d95302b67c31d95300067f21d95300067e21d95300067d21d95300067c21d95302b67f70d95300be7e70d95300067d70d95300067f40d95300067e40d95300067d40d95300067c40d95302b67f30d95302b67c30d95300067f20d95300067e20d95300067d20d95300067c20d95300be7c6559530005bf74595300b5bc7459530006bc64595300bcff75595300067f7559530004ff7459530006bf7459530004bf7459530014fe7459530004fd7459530014fc7459530006bc7459530014bc74595300be7f54595300067d54595300ccff7359530006df7359530004ff725953000cfe7259530004fd725953000cfc72595300be7f52595300067d5259530006bf4259530006bd4259530006df3259530006dd3259530004ff7159530004fc71595300e4ff7059530006fb70595300057e76195300be7e76195300047e76195300bd7f74195300057d74195300067f64195300067e64195300067d64195300067c64195300073c64195300063c64195300075e43195300075d43195300bd7f72195300057d72195300067f62195300067e62195300067d62195300067c62195300073f42195300073d42195300075f32195300075d32195302ae7f60195302af7b30195302af7830195300b5be76d91300b6be76d9130014be76d91300073f75d91300073c75d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91300079f73d91300b79c73d9130005bf72d9130005bd72d9130006bf62d9130006be62d9130006bd62d9130006bc62d91300073f52d91300073d52d91300079f32d91300079d32d91302a7bb30d91302a7b830d9130006bf75d91300063f75d9130006be75d9130006bd75d9130006bc75d91300063c75d9130006bf73d91302a6be73d91300b6bd73d91302a6bc73d9130006bf53d91302a6be53d91302a6bc53d9130006bf72d9130004bf72d9130006be72d9130006bd72d9130004bd72d9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d91300063d52d9130006bc52d91302a6bf32d91300069f32d9130006be32d9130006bd32d91300069d32d91302a6bc32d9130006bf71d9130006be71d
  | 12 => 0xc74586300067f54586300067d5458630004ff725863000cfe7258630004fd725863000cfc72586300067f52586300067d5258630006bf4258630006bd4258630006df3258630006dd3258630006f75158630006f45158630006f64158630006f54158630006f62158630006f52158630006f56118630004ff7694630004fe7694630004fd769463001e7e65946300067d6594630004ff7654630004fd7654630004fc7654630005df735463004ddc7354630006f6618c630006f5618c630005fa708c630005f9708c63014ede658c63014edc658c6302f6df648c6302f6dd648c6302f75f548c6302f75d548c6302eddf728c6302eddd728c630266df628c630266dd628c6302675f528c6302675d528c6302679f428c6302679d428c63004dde718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c63004ede608c6300057f754c6300cd7c754c630006f6614c630006f5614c630005fb704c630005f8704c630005dd760c63004edd760c63011ede650c63011edc650c6302e6df640c6302e6dd640c6302e75f540c6302e75d540c63004ddf720c6302dddd720c6302d6df620c6302d6dd620c6302d75f520c6302d75d520c6302d79f420c6302d79d420c63004fd6710c630006dd610c630005dd700c63004fda600c63001cfe769423004cfd769423001e7e65942300067d659423004dde7394230005dd73942300cf7b509423009cff7654230005dd76cc23004edd76cc2302cedf64cc2302cedd64cc2302cf5f54cc2302cf5d54cc23004ddf72cc2302c5dd72cc2302bedf62cc2302bedd62cc2302bf5f52cc2302bf5d52cc2302bf9f42cc2302bf9d42cc230005de71cc23004fda60cc230007da50cc230007d950cc23001cfe76d95300be7e65d9530006bc64d9530004ff74d9530014fe74d9530004fd74d9530014fc74d95300be7f54d95300067e54d95300067d54d95300be7c54d953004cfe73d95300bcfd73d953004cfc73d95300be7f53d9530004ff72d953000cfe72d9530004fd72d953000cfc72d95300be7f52d95300067e52d95300067d52d95300be7c52d9530006bf42d9530006bd42d9530006df32d9530006dd32d9530004fe71d9530004fd71d95300be7f51d95300be7c51d953004cfd70d95300be7f50d95300bd7e76d953001c7e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300075e43d95300075d43d95300057f72d95300057d72d95300067f62d95300067e62d95300067d62d95300067c62d95300073f42d95300073d42d95300075f32d95300075d32d95302b77b30d95302b77830d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d9530
  | 13 => 0x97300067d5259730006bf4259730006bd425973004edf3259730006dd3259730004ff7159730004fc71597300e67c51597300e67f505973001cfe7598730004fd759873001cfc7598730004ff7498730014fe7498730004fd7498730014fc74987300067f54987300067d549873004ede4398730006dd4398730004ff729873000cfe7298730004fd729873000cfc72987300067f52987300067d5298730006bf4298730006bd429873004edf3298730006dd329873004ef6719873004ef7319873004ef4319873004edc3098730004ff755873001cfe755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc74587300067f54587300067d5458730004ff725873000cfe7258730004fd725873000cfc72587300067f52587300067d5258730006bf4258730006bd425873004edf3258730006dd325873004ef7715873004ef7315873004ef43158730004ff769473004cfe7694730004fd769473001e7e65947300067d6594730004ff7654730004fd765473004cfc7654730005df735473004ddc73547300bcfd76943302b67f659433001e7c659433001cff765433004cfc765433001e7e65543300067d6554330005df735433004ddc73543300ce7e65d9630005f671d9630005f571d96300ccfd75d9630004ff74d9630014fe74d9630004fd74d9630014fc74d96300ce7f54d96300067d54d9630006dd73d96302b67e53d96302b67c53d9630004ff72d963000cfe72d9630004fd72d963000cfc72d96300ce7f52d96300067d52d9630006bf42d9630006bd42d9630006df32d9630006dd32d9630004fe71d9630006f671d9630004f671d9630004fd71d9630006f571d9630004f571d9630006fa70d963001cff76596300ce7c65596300067f7559630004ff7459630014fe7459630004fd7459630014fc74596300ce7f54596300067d54596300ce7f5359630004ff725963000cfe7259630004fd725963000cfc72596300ce7f52596300067d5259630006bf4259630006bd4259630006df3259630006dd3259630004ff7159630004fc71596300ce7c515963004cfc70596300ce7c505963001cff7654e3001e7e6554e300067d6554e30005fb7054e30005f87054e3004fdb3054e300cd7e75d86300057d75d8630006f7619863001cfe7598630004fd759863001cfc7598630004ff7498630014fe7498630004fd7498630014fc74986300067f54986300067d5498630004ff729863000cfe7298630004fd729863000cfc72986300067f52986300067d5298630006bf4298630006bd4298630006df3298630006dd3298630006f75198630006f45198630006f64198630006f54198630006f62198630006f52198630004ff755863001cfe755863001cfc7558630004ff7458630014fe7458630004fd7458630014f
  | 14 => 0x57d709465000779709465001e7e609465001f7a609465004cff76cc650004fe76cc650004fd76cc65001d7e75cc6500057d75cc650006f661cc650006f561cc650004ff768c650004fe768c650004fd768c65001d7e758c6500057d758c65004ede638c650006dd638c65014f5c538c650004ff764c650004fd764c650004fc764c6500057f754c65001d7c754c65004cff760c650004fe760c650004fd760c6502b57f750c65001d7c750c65004ede630c650006dd630c6502b75c530c650006f6610c650006f5610c650005fa700c650005f9700c650004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500ce7f54d8d500067d54d8d500cede53d8d500cedd53d8d50006df43d8d50006dc43d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d500ce7f52d8d500067d52d8d50006bf42d8d50006bd42d8d50006df32d8d50006dd32d8d50004fe71d8d50004fd71d8d50006df6398d500bdf97098d50005bf7458d500f5bc7458d500e5fb7058d5004ede6318d50006dd6318d50004ff74d8550014fe74d8550004fd74d8550014fc74d85500767f54d85500067d54d855004cfe73d8550004fd73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d85500767f52d85500067d52d8550006bf42d8550006bd42d8550006df32d8550006dd32d8550076f651d8550076f551d8550006f76198550065f97098550005bf74585500f5bc7458550005df7358550005dc7358550005ef72585500edec7258550085fb7058550006f56118550004ff7418550014fe7418550004fd7418550014fc74185500367f54185500067d541855004cfe7318550004fd7318550004ff721855000cfe7218550004fd721855000cfc72185500367f52185500067d5218550006bf4218550006bd4218550006df3218550006dd3218550036f65118550036f551185500367c5018550004fe76cc550004fd76cc55004cfc76cc550004fe768c550004fd768c550004fc768c550006df638c55004edc638c550004ff764c550004fe764c550004fc764c5500057f754c55001d7c754c550004fe760c550004fd760c55004cfc760c55001d7e750c5500057d750c550006df630c55004edc630c550005fa700c550005f9700c5503157f74941503157d749415030e7f649415030e7d64941502b67c63941503057f72941503057d72941502fe7f62941502fe7d62941502ff3f42941502ff3d42941502ff5f32941502ff5d32941500067c619415001d7e709415001f7a709415001e7f609415001f7b609415004e7f7559730004ff7459730014fe7459730004fd7459730014fc74597300e67f54597300067d545973004cfc735973004e7e535973004e7c5359730004ff725973000cfe7259730004fd725973000cfc72597300e67f525
  | 15 => 0x92098031004ff75580310067f75580310047f755803101cfe755803101cfc75580310067c755803101c7c7558031004ff7458031006bf7458031004bf7458031014fe7458031004fd7458031014fc7458031006bc7458031014bc74580310067f54580310067d545803104ede4358031006dd4358031004ff725803100cfe7258031004fd725803100cfc72580310067f52580310067d5258031006bf4258031006bd425803104edf3258031006dd325803104efb7058031006fa4058031006f9405803104efb305803104edc305803104ef8305803104ed83058031006fa2058031006f92058031005f671d8e50005f571d8e5009dfa70d8e50006df6398e50004ff7458e50014fe7458e50004fd7458e50014fc7458e500be7f5458e500067d5458e500bede5358e500bedd5358e502b67c5358e50006de4358e50006dd4358e50004ff7258e5000cfe7258e50004fd7258e5000cfc7258e500be7f5258e500067d5258e50006bf4258e50006bd4258e50006df3258e50006dd3258e50004ff7158e50004fc7158e5004ede6318e50006dd6318e500cdfa7018e502b57f7494e503557d7494e5034e7f6494e5034e7d6494e5001d7e7394e5001f5e7394e502b75e6394e502b67d6394e500075d6394e500065d6394e502b57f7294e503457d7294e5033e7f6294e5033e7d6294e5033f3f4294e5033f3d4294e502b75f3294e5033f5d3294e500057e7194e502b77a7094e500057d7094e502b7797094e50005797094e5001e7e6094e5001f7a6094e50005de73d8650005dd73d8650035fa70d8650006f76198650004ff7498650014fe7498650004fd7498650014fc74986500867f54986500067d549865004cfe7398650004fd73986500067e53986500867c5398650004ff729865000cfe7298650004fd729865000cfc72986500867f52986500067d5298650006bf4298650006bd4298650006df3298650006dd3298650086f65198650086f55198650006f64198650006f54198650006f62198650006f52198650004ff7458650014fe7458650004fd7458650014fc74586500667f54586500067d5458650004ff735865004cfc7358650004ff725865000cfe7258650004fd725865000cfc72586500667f52586500067d5258650006bf4258650006bd4258650006df3258650006dd3258650066f65158650066f551586500667c5158650006f64158650006f54158650006f62158650006f52158650006f56118650075fa70186503357f74946503357d749465032e7f649465032e7d64946502b57e73946502867e63946503257f72946503257d729465031e7f629465031e7d629465031f3f429465031f3d429465031f5f329465031f5d329465001d7e719465001f7671946500077661946500067d61946500077561946500077a7094650
  | 16 => 0xc5310075c658c53114e5c658c53138edf648c53138edd648c53138f5f548c53138f5d548c531365df728c531365dd728c531386df628c531386dd628c5313875f528c5313875d528c5313879f428c5313879d428c53104dde718c53104edf618c53104fd7618c5310067f65d81310067c65d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d8131004ff72d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131006bf42d8131006bd42d8131006df32d8131006dd32d813113d7e75981310057d75981310067f65981310067c6598131006fb60981310057f755813113d7c75581310067f65581310067c6558131005bf7458131135bc7458131005ef725813112dec72581310067f65181310067c6518131006f9601813101cfe7518131004fd751813101cfc7518131004ff7418131014fe7418131004fd7418131014fc74181310067f54181310067d5418131004ff721813100cfe7218131004fd721813100cfc72181310067f52181310067d5218131006bf4218131006bd4218131006df3218131006dd3218131006de311813104e7f7559431004ff7459431014fe7459431004fd7459431014fc745943111e7f54594310067d545943104cfe735943104cfc735943104edc735943104cdc735943111edf535943104e7e535943104e7c535943104edc5359431004ff725943100cfe7259431004fd725943100cfc725943111e7f52594310067d5259431006bf4259431006bd425943104edf3259431006dd325943111cfc715943111e7c5159431004ff7059431004fc705943111e7f505943114cff769443104cfe769443101cfd769443104cfc769443101e7e65944310067d659443104dde7394431005dd73944312875c539443114cff7654431005df735443104ddc735443104ddf764c431006df764c431004df764c4310075f754c43111dde754c43111ddc754c4310075c754c43111d5c754c43137ddf744c43137ddd744c4313775f544c4313775d544c43136ddf724c43136ddd724c43104edf624c43135edd624c43135f5f524c43135f5d524c43135f9f424c43135f9d424c43104ddf714c43104fd7714c431366de614c43104fd6614c431007d6514c431007d5514c43135fd7214c43135fd4214c431005dc704c43101cfe7598031004fd759803101cfc7598031004ff7498031014fe7498031004fd7498031014fc74980310067f54980310067d5498031004ff729803100cfe7298031004fd729803100cfc72980310067f52980310067d5298031006bf4298031006bd429803104edf3298031006dd329803104efa7098031006fa4098031006f9409803104efb309803104ef83098031006fa2098031006f
  | 17 => 0xcfe72d9531004fd72d953100cfc72d953113e7f52d95310067e52d95310067d52d953113e7c52d9531006bf42d9531006bd42d9531006df32d9531006dd32d953104cfd71d953113e7f51d9531004fe70d9531004fd70d953113e7f50d953113e7c50d953113d7e76d953101c7e76d95310057f74d95310057d74d95310067f64d95310067e64d95310067d64d95310067c64d95310057f72d95310057d72d95310067f62d95310067e62d95310067d62d95310067c62d95310073f42d95310073d42d95310075f32d95310075d32d95312877731d95312877431d95310067f74d95310047f74d95310067e74d95310067d74d95310047d74d95310067c74d95310067f73d95312867e73d95310067d73d95312867c73d95310067f43d95312867e43d95310067d43d95312867c43d95310067f72d95310047f72d95310067e72d95310067d72d95310047d72d95310067c72d95310067f42d95310063f42d95310067e42d95310067d42d95310063d42d95310067c42d95312867f32d95310065f32d95310067e32d95310067d32d95310065d32d95312867c32d95312867f71d953113e7e71d95310067d71d95310067f41d95310067e41d95310067d41d95310067c41d95312867f31d95312867c31d95310067f21d95310067e21d95310067d21d95310067c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95312867f30d95312867c30d95310067f20d95310067e20d95310067d20d95310067c20d953113e7c655953113cff75595310067f7559531004ff7459531014fe7459531004fd7459531014fc745953113e7f54595310067d545953114cff7359531006df735953114cdf7359531004ff725953100cfe7259531004fd725953100cfc725953113e7f52595310067d5259531006bf4259531006bd4259531006df3259531006dd3259531164ff7159531006f77159531004ff7059531004fc70595310057e761953113e7e76195310047e761953113d7f741953113f3e74195310057d741953113f3d74195310053d74195310067f64195310067e64195310067d64195310067c641953113d7f72195310057d72195310067f62195310067e62195310067d62195310067c62195310073f42195310073d42195310075f32195310075d32195313967f611953139777311953139774311953101cfc7654d310067f6554d3101e7c6554d31005f77154d31005f47154d3104fd43154d31164fe76945310067f659453101e7c659453113f77519453101cff765453113cfd765453104cfc76545310067f655453101e7c6554531005df735453104ddc73545310067f658c53114e7c658c53104df6718c53104ef7618c5310075f658c53114ede658c53114edc658
  | 18 => 0xd725833100cfc72583310067f52583310067d5258331006bf4258331006bd425833104edf3258331006dd325833104efb705833104efb305833104ef8305833114e7e65d963114f5c53d963114cfd75d9631004ff74d9631014fe74d9631004fd74d9631014fc74d963114e7f54d96310067d54d9631006dd73d963114edf53d96312867e53d96312867c53d963114edc53d9631004ff72d963100cfe72d9631004fd72d963100cfc72d963114e7f52d96310067d52d9631006bf42d9631006bd42d9631006df32d9631006dd32d9631006f671d9631004fe70d9631004fd70d963101cff765963114e7c655963104ddc735963114f5f53596310067f7559631004ff7459631014fe7459631004fd7459631014fc745963114e7f54596310067d545963114edf735963114e7f535963114edf535963114e5f535963114edc5359631004ff725963100cfe7259631004fd725963100cfc725963114e7f52596310067d5259631006bf4259631006bd4259631006df3259631006dd325963104cfc715963114e7c5159631004ff7059631004fc705963114e7c505963101cff7654e3101e7e6554e310067d6554e3114ddf7354e3104f5c5354e31005f77154e31005f47154e3104fd73154e3101cfe769463104cfd769463101e7e65946310067d659463104dde7394631005dd739463114f5c539463114f77519463111cff765463114ddf735463104ddc7354631005dd76cc63104edd76cc63114dde75cc63104ddc75cc63104ddf74cc6313b5dd74cc6313af5f54cc6313af5d54cc63104ddf72cc6313a5dd72cc63139edf62cc63139edd62cc63139f5f52cc63139f5d52cc63139f9f42cc63139f9d42cc63104fd661cc631007d651cc631007d551cc631005de70cc63114d7e75d82310057d75d8231145be74d8231005bd74d8231006fb609823101cfe7598231004fd759823101cfc7598231004ff7498231014fe7498231004fd7498231014fc74982310067f54982310067d5498231004ff729823100cfe7298231004fd729823100cfc72982310067f52982310067d5298231006bf4298231006bd4298231006df3298231006dd3298231006fa2098231006f92098231004ff755823101cfe755823101cfc7558231004ff7458231014fe7458231004fd7458231014fc74582310067f54582310067d5458231006de4358231006dd4358231004ff725823100cfe7258231004fd725823100cfc72582310067f52582310067d5258231006bf4258231006bd4258231006df3258231006dd3258231006fa2058231006f92058231006f9601823101cfe76d953113e7e65d9531004ff74d9531014fe74d9531004fd74d9531014fc74d953113e7f54d95310067e54d95310067d54d953113e7c54d953113cfd73d953113e7f53d9531004ff72d9531
  | 19 => 0x8d5111e5c5118d51006df4118d51006de4118d51006dd4118d51006dc4118d51006df2118d51006de2118d51006dd2118d51006dc2118d5104edf7018d5104ede7018d5104edd7018d5104edc7018d5111edf5018d5111ede5018d5111edd5018d5111edc5018d51006df4018d51006de4018d51006dd4018d51006dc4018d51006df2018d51006de2018d51006dd2018d51006dc2018d513d57f74945513d57d74945513ce7f64945513ce7d64945510075f63945512867c63945510075c63945510065c63945513c57f72945513c57d72945513be7f62945513be7d62945513bf3f42945513bf3d42945513bf5f32945513bf5d329455101d7e719455101f76719455101e7f619455101f776194551006df63d8151006dc63d8151004ff74d8151014fe74d8151004fd74d8151014fc74d81510867f54d81510067d54d815104cfe73d8151004fd73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d81510867f52d81510067d52d8151006bf42d8151006bd42d8151006df32d8151006dd32d8151086fa50d8151005de7398151005dd7398151006df6398151006dc6398151006fb6098151005bf7458151175bc7458151005df7358151005dc7358151006df6358151006dc6358151005ef725815116dec7258151006df6318151006dc6318151006f96018151004ff7418151014fe7418151004fd7418151014fc74181510367f54181510067d541815104cfe7318151004fd7318151004ff721815100cfe7218151004fd721815100cfc72181510367f52181510067d5218151006bf4218151006bd4218151006df3218151006dd32181510067e51181510367c5118151036f9501815104e7f7559731004ff7459731014fe7459731004fd7459731014fc74597311667f54597310067d545973104cfc735973104e7e535973104e7c5359731004ff725973100cfe7259731004fd725973100cfc72597311667f52597310067d5259731006bf4259731006bd425973104edf3259731006dd32597311667f5159731004ff7059731004fc70597311667c505973113cfd76947312867f659473101e7c659473101cff765473104cfc765473101e7e65547310067d6554731005df735473104ddc735473101cfe7598331004fd759833101cfc7598331004ff7498331014fe7498331004fd7498331014fc74983310067f54983310067d5498331004ff729833100cfe7298331004fd729833100cfc72983310067f52983310067d5298331006bf4298331006bd429833104edf3298331006dd329833104edc319833104efa709833104efb309833104ef83098331004ff755833101cfe755833101cfc7558331004ff7458331014fe7458331004fd7458331014fc74583310067f54583310067d5458331004ff725833100cfe7258331004f
  | 20 => 0x6fa2058251006f92058251006f96018251004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d5114e7f54d8d510067d54d8d5114ede53d8d5114edd53d8d51006df43d8d51006de43d8d51006dd43d8d51006dc43d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d5114e7f52d8d510067d52d8d51006bf42d8d51006bd42d8d51006df32d8d51006de32d8d51006dd32d8d51006dc32d8d51004fe70d8d51004fd70d8d51006df64d8d51006de64d8d51006dd64d8d51006dc64d8d5114f5f54d8d510075d54d8d51005df72d8d51005dd72d8d51006df62d8d51006de62d8d51006dd62d8d51006dc62d8d5114f5f52d8d510075d52d8d510079f42d8d510079d42d8d5114fd751d8d5114f5c51d8d5114fd451d8d5114edf75d8d5114ede75d8d5114edc75d8d51006df74d8d51006de74d8d51006dd74d8d51006dc74d8d5114edf54d8d5114e5f54d8d5114ede54d8d5114edd54d8d510065d54d8d5114edc54d8d51006df72d8d51004df72d8d51006de72d8d51006dd72d8d51004dd72d8d51006dc72d8d5114edf52d8d5114e5f52d8d5114ede52d8d5114edd52d8d510065d52d8d5114edc52d8d51006df42d8d510069f42d8d51006de42d8d51006dd42d8d510069d42d8d51006dc42d8d5114edf71d8d5114edd71d8d5114edf51d8d5114ede51d8d5114edc51d8d51006df41d8d51006de41d8d51006dd41d8d51006dc41d8d51006df21d8d51006de21d8d51006dd21d8d51006dc21d8d51006df70d8d51006de70d8d51006dd70d8d51006dc70d8d5114edf50d8d5114ede50d8d5114edd50d8d5114edc50d8d51006df40d8d51006de40d8d51006dd40d8d51006dc40d8d51006df20d8d51006de20d8d51006dd20d8d51006dc20d8d51006df6398d5113df57198d51165f77158d5104ede6318d51006dd6318d5114dde7618d51006de7618d51006df6418d51006de6418d51006dd6418d51006dc6418d5111f5f5418d510075d5418d51005df7218d51005dd7218d51006df6218d51006de6218d51006dd6218d51006dc6218d5111f5f5218d510075d5218d510079f4218d510079d4218d5111fd75118d5111f5c5118d5111fd45118d5104edf7518d5104ede7518d5104edc7518d5104edf7418d5104ede7418d5104edd7418d5104edc7418d5111edf5418d5111e5f5418d5111ede5418d5111edd5418d510065d5418d5111edc5418d5104edf7218d5104cdf7218d5104ede7218d5104edd7218d51004dd7218d5104edc7218d5111edf5218d5111e5f5218d5111ede5218d5111edd5218d510065d5218d5111edc5218d51006df4218d510069f4218d51006de4218d51006dd4218d510069d4218d51006dc4218d5104edf7118d5104edd7118d5111edf5118d5111ede5118d5111edd5118d5111edc511
  | 21 => 0xd541855311edf53185533967e53185533967c531855311edc5318553004ff721855300cfe7218553004fd721855300cfc721855311e7f52185530067d5218553006bf4218553006bd4218553006df3218553006dd321855311ef55118553006f72118553006f42118553004fe7018553004fd701855304cfd75d8153004ff74d8153014fe74d8153004fd74d8153014fc74d81530e67f54d81530067d54d8153004ff72d815300cfe72d8153004fd72d815300cfc72d81530e67f52d81530067d52d8153006bf42d8153006bd42d8153006df32d8153006dd32d8153004fe71d8153004fd71d81530e6fa50d8153005f67198153005f57198153006fb6098153005bf7458153195bc7458153006f9601815304cfd7518153004ff7418153014fe7418153004fd7418153014fc741815309e7f54181530067d54181532ae7e53181532ae7c5318153004ff721815300cfe7218153004fd721815300cfc721815309e7f52181530067d5218153006bf4218153006bd4218153006df3218153006dd3218153004fe7118153004fd711815309ef9501815314f5c53d8e5111df671d8e51006df6398e51004ff7458e51014fe7458e51004fd7458e51014fc7458e5113e7f5458e510067d5458e5113ede5358e5113edd5358e512867c5358e51004ff7258e5100cfe7258e51004fd7258e5100cfc7258e5113e7f5258e510067d5258e51006bf4258e51006bd4258e51006df3258e51006dd3258e51004ff7058e51004fc7058e5104ede6318e51006dd6318e512875c5318e5114df67118e512857f7494e513f57d7494e513ee7f6494e513ee7d6494e5101d7e7394e5101f5e7394e512875e6394e512867d6394e510075d6394e510065d6394e512857f7294e513e57d7294e513de7f6294e513de7d6294e513df3f4294e513df3d4294e512875f3294e513df5d3294e51287767194e510057d7194e51287757194e51005757194e5101e7e6194e5101f766194e510057e7094e51006fb6098251004ff7498251014fe7498251004fd7498251014fc74982510767f54982510067d549825104cfe7398251004fd73982510067e53982510767c5398251004ff729825100cfe7298251004fd729825100cfc72982510767f52982510067d5298251006bf4298251006bd4298251006df3298251006dd3298251076f95098251006fa2098251006f92098251005bf7458251185bc7458251004ff7458251006bf7458251004bf7458251014fe7458251004fd7458251014fc7458251006bc7458251014bc74582510667f54582510067d5458251004ff735825104cfc7358251004ff725825100cfe7258251004fd725825100cfc72582510667f52582510067d5258251006bf4258251006bd4258251006df3258251006dd3258251066fa50582510667c5058251
  | 22 => 0x4002006809c02e00400080100080060000024006018000800401a0000000008000004003802800a002005801000a009003800001e003007000402800100000ac016003000810401e00600b0074012001000002400000d000000001000e0098020020003006001001a000000000007601801000b0042005000000c01e00900a0000000004017800001202c000800005800500500040040010000008014033007000400200200600540240070038020000004005003000000000100dc00000201700300140040098004016009001804006e00e001800400605b00800000000110028000010000004ff7498653014fe7498653004fd7498653014fc749865314e7f54986530067d549865304cfe739865314edf539865304edc5398653004ff729865300cfe7298653004fd729865300cfc729865314e7f52986530067d5298653006bf4298653006bd429865304edf3298653006dd329865304ef6719865314ef5519865304ef7319865304ef43198653004fe7098653004fd709865314e7c5098653004ff7458653014fe7458653004fd7458653014fc745865313e7f54586530067d545865304cfc7358653004ff725865300cfe7258653004fd725865300cfc725865313e7f52586530067d5258653006bf4258653006bd425865304edf3258653006dd325865304ef7715865313ef6515865313e7c515865304ef7315865304ef43158653004ff7058653004fc7058653004ff7498253014fe7498253004fd7498253014fc74982530ce7f54982530067d549825304cfe7398253004ff729825300cfe7298253004fd729825300cfc72982530ce7f52982530067d5298253006bf4298253006bd429825304edf3298253006dd3298253004fe7198253004fd71982530ce7c519825304efa70982530cef9509825304efb309825304ef83098253004ff7458253006bf7458253004bf7458253014fe7458253004fd7458253014fc7458253006bc7458253014bc74582530be7f54582530067d545825304cfc7358253004ff725825300cfe7258253004fd725825300cfc72582530be7f52582530067d5258253006bf4258253006bd425825304edf3258253006dd3258253004ff7158253004fc715825304efb70582530befa50582530be7c505825304efb305825304ef8305825304cfd75d8553004ff74d8553014fe74d8553004fd74d8553014fc74d85531667f54d85530067d54d8553004ff72d855300cfe72d8553004fd72d855300cfc72d85531667f52d85530067d52d8553006bf42d8553006bd42d8553006df32d8553006dd32d8553166f651d8553006f721d8553006f421d8553004fe70d8553004fd70d8553006f76198553006f5611855304cfd7518553004ff7418553014fe7418553004fd7418553014fc741855311e7f54185530067
  | 23 => 0xc00400a803400000000280140260030078014004004000806400800800000040060030088000014000000000001000100e005800a000000004401600300e800000a024000002c0000020030018000008000006c00800100480380060010070018000001006008c0100080000000000001000000c002001003801c00800b0060000004015005801c00a00e001800400201300e000000e0070020004002003001005c00c0010000000004000000001000000d000800000c00500080340100000000000008009000800400400800c0014022000011000000c0130000038002000000001001200c009004000c000000800800e003001804c000002000000c00001401e801c00a003002800400000001500cc0080180048008046007001000000001600a007400a008000000000200000000bc00c004001000000200300400100000350078010000006000000800000101a804c004008003800401a027006800000e0030000018002002007001000400b0008000002009002003003e002005800c000000000017801e01400100c401200000080740060060070170000001002000000800000d8018020000000006400a005002000400000000e800804c00b006802001000200200180000000018078008020001800400a00400000100080060000178012000001002c00602f00280040020000018084000031008000400a00500a80140000050000000030000003000001c00900080000080080020060004003000000000800200180140060050010000000007001001000200200100300020070000028036001006800c028000002800000800000d80580040010020008006002003800c03e000013803801600200b00280100060030028002001008000804c009003801c006006000000c05000000a009c006004019001000c0000268000030000001001c00000300380100500000020004000002003000004200e004801403000b000000400600b000001400400000b801000200e0000028000033003003800000000100c800402600e002003c00901b0000004008000800400a002003800401a00f00200ac000003008803000000e00000a400e00200d0040002001001801c0660120020000000004002816802000c0028000000008007801800001d0040000004000000002c090009000800002200e002800000e0000018020006008001801c0380020000000018001002803c00a0010010078070002000802002c00b00880fc01200100e80d803c00e00d000000802d001803401e013000002c0020090020010006007000006402200000f000400601900080080b800800d80100060000030034034001002000402000402d80040400000230000006009000800c01604100180240240000008064004002006007c00a006000003000a00100080240
  | 24 => 0xce8be20001cfa6a00003c100000000004a30000a5cace9524df2be43289f54440b9d28054c0000504d42000438ba6800096e00024bc6f8b8d4848000ef6ba5539951106ec4678787c400008200015bd94c0000000000a564b21e68acd9e60004eaae391e47f811481008cc99a379b81c05a24637686a4fa89ae660283da90dc01cea85d2e671e48b06041a8c1d3f115cc8200de0ab33081b8d9158f050c6f0000190a4c4d866f435e16c0a4a248000001c000001800c00200e0028020022005008006c00200200b800400e020003000002e00000b005000401700880240180040228010008002004002c016009000000000400100780040020080030020004006003000c004000000000005001900a80040140030048008000003002800800601d0028020004006005003c010001006800000e01700900800000030000084002006003001002e01b00f0020058003000000001e00d000000009400100b00140000200038000014007000001400600100880000000060000000002000013001c0000030028014000001000002c002000001801401e000008002400e00400e001004c00200080100100000020010010002003802c014000002800000200e000000401a00900000040020000028030004000000800409800e00000340000190000034010002001800002c02b0038004000013002800000c0010000018000002004804c004000002801000c0080008000008002007000c004000000802808400f00300440020050000014000006001000c07e00401a00040000010018000002000002800000201f0030008002000000000000000c000003802200000a00700000000100014008000002800401a00300200380020000018008006007000001000401c006004000c000000000c00400e001000c002002007000400001b000003c004000000003000600e0010000000000000002800c00000080180080000008000000000018801c01000000000080080030080038008010001800000200100080000080030000018014002000007400c0010010010000002000808c000009003800001200000100480020010128068006005002809802600d0010038008000000001800800e004007c0040090008008002007002000806a003001805402000100700040120090080028010000000000400e00c001801c02000e001802000c037004800c008001000000000a000000804400800400b000000800000480040140110038008000001001800400400b0008000000003001001400a001007800802c003000003c014008029800c0200010000000002000000003400c001005801000000200f8018004004002800000001503700dc008000000800400202a000004002c000007800800003e00080040000070000018166006001000400a00500400e80020030
  | 25 => 0x53267682d8026dc65740001dda2ac6ea110cf780002feb4a0d6a0000d20000000da9000314185200076bb2897d669a47f2151630be12a088f0b5add51258a0c83a1060ac37e8b50e740cf904445417055c3868f3e3c6582b9c07fe0f92ca8000dd0577239a2f930028654e1524bf40006ab85f90806ef249835598211843827a1b5436d4e11cf196c5e05fe2ea05dcbf96a380d8e8c0002ec960ddcc00048816148b00001e8846467aa20330800113c55461f19754023e93dd1f00576f0578e129db38db97680819078f13049af71d0412d34e189819c16704628856b09ba496268d446c6021b9c41d64a250001850a78abe21c1e90d5cd8d0810d9d4d85be73503c8a760630e3800007600026800001a29fc3ab9ccd82e9c5000240da2a77274c9211aee0003b480010c48967692315ad82470190174c2e64f0000000508ddc71f14e049e00015190c1cc048642c887c960a8918b1bb03b8b8f3edad099c88017148e91798b391521330e7ae8766ca7c539833a38ea77447447c34407213dc4dc5afb93008edc73ee18f0dea8f93e5b99882abcf48a294d140e5262b9d2d5149cb1fc015123c59067824609d8a5117fbb616d41e36ac2aa025ef1e3a92a3932c7f96a6302941cc730271a49dd407677d9a100d2be5306a4d161a88c0698a4d2982650570a754fcd8b04ea3e972a32465505a92f0e4d515b9b042a87c4c117e1b32b0b72412d592c70362c18403d6195466b01ca8405f66d21f49e6c6c30d2b2cf1a0be581052800066a000004933eeae0000e440000005e0a0c09383220d718d00007a30eca405950cb73aa1ff1afa7893c2a744018000423b418a209d400013382de6045cf00000d0cea2e78ca80000001f9a5689bc31445880003f60000002e900001fc39580000002fb0000000ad22fd723b190f5407416b800000066f049301485891c14fb17895009b18632ec7400000002a10174a070001358fe41610000ac10a03b27618140ca03b60003518ecc3f535630616fa6702d00bb0d8c00019820083e8cc86a9b1a13561b71d8b26cd76d9518400000001490ed1d203c09f72d90efdc567002fb80004b4cdc76b2ed4ce660c000188c94c950300800187e0000f7090976c0da785a1bc03e77f5b893602cc90841d1478b02c935fc262d7b43233263788d7457d0ba0e6c01c18b374b5b963eb610000001278e5961d04dd7f4cf10ce0c9c0000005a780c41dc00040c8e589d0bef318800000080b00025e4b260006210cb0056b222140c3c0003f94528cf966cb542c7af54116c673fda29c83c0593d81cd042c15b0001ff4000000119000026c18f0000fb839c9264f6938400035b6048bbd3be96300018a80006d40000d3423600000022ad0404b6767067400000032d80015e653d17d0e151babdd6069049910b3e461060cccacd34e79
  | 26 => 0x3398f140004d08000000a5d3f50001de600075895442dcce302e10f979000000000009680006b896e4866234348a1fc70492e47614b12869134798000e88d755a80071b680253e380011a2e3911c2aa98f03e862b1e5400099848c8fc866a4c80dfb3d1de4eb44b69bd941826b751291cf44ae951e041c0eab8500036c95d80000001c9c6d00005fe80005429530d61a2cef80000000001b5e4987529e74000942000196563a41300000014faf01112bae000000000000012a86e21f8bb79b1e0004ef2969a8239c756000088cdba62e238ddce00079380009e25991bebb042ca0006cba18cab83904c1b8299ea09a0000dfd6fc24d762a68805cbe84f5ba310766ea01a150075012b0001e65e203414551375dd270722200001ca4bd00000bc00000040f2705c70000000000198e49d5e001094c6e3b31582ad07c0000b98000000000243a71dc1c0006458001b7c00000023d40003d226a00017c0dd664d1c4d2e4dd7000180c0006af1e39bb80009330ef800007aa7b5a687152ecd1a65a80000002893c10000000c8c21517addf0a8b78cb12db66a5b52434848100f83f3165811ad3d39a85ece7e31f1682cc1b3a0000000468ffc14e67baa803cceba5a3290d18e13800014600000000000b60326e916691ad9b920006de3669b6eb190000000cd6e4f00036300001ca6688cc505cb535112d6d132c69757ae01cbebaf0002f5012a70d2b2a2dd0b85887630ac92f80005e3933d53455058b927c00000055b800088a00000003194a00005b211b41da69d2c480010421a0491aef000078865c323c27caea75528346e87d82ea94d4276ad752c98598f684b57f20b485a488254800124800041212140000000003740f6a10b5d69ca5dfc1c34c924540000cd00018e8c009e236483b1bee00029f2f881106930659408000ace1568f581009932348d55318c104ba0b00bd00640a82c8d4a8b560a3a590000f2d28d00000000713728000ad80005732a883705e1000029c7709cd2e58480420cc5706800159e00000037ccb6e5c307aaf1023cabb16701c1d0a54f62d8be0000b2e000246d9980007729f5d172df90003728b703bb6270e0c976bc21469e4d882d8e21d1a589c877028da84c1e078e3400bb4000d9200010247168866650e34518a345b4a1f995882632ba7cd27e6c81b2b09c3a2add37f005c5d24173cc31209d4e1e3d3afec95698a71e8d316fe8c40003049d7ea8c17b9960cfad860de11440aa3586d8a700edabe3543a214210ab93f0a21cbaeba34ed020da7000000024694ac0004078bd9496dd8000a089506b522f799a536e47f5090d4c0000000f2399475ac95061b640eb69674570d5c4ea2e46b996a8c7ca93011038c334be7433025d800af070091d8e1001a78901cd5a60e469a8001a4a5c5134af0d8c41f20de92f9560
  | 27 => 0xd0b50e0db9826acc196899cb38ee30002e64c04d8152bba5d818883000243865c97b06c08985cc000331000079ed8504b0cc9abaa8d783000109e0000000001e4c89c2c01c5cb0e22716435143981094a4a2fc0000002758001698000000014d618ddf35f2240c44d420003780ad671b26280006a81607771d1c0008416b0a8f54dac9c6b30000ec41cd6201d7540a5ae2e10001ba43e127924e18d6e11000394d4660bd0a030acfa0cdf28b02e1a2c7906151be178c0cc06b8f880006dc31c097112683876e80015de0004a79e3096e0007440d3cd36f0d2878a9481452210a31a9cf44244a41ddcbd23e42ed32100466b7428a1202ecaed16e8ea528ea0b2be29915cee0961c2ae802236211f9345584a8f307b5e9a06cba40616517b65db0002ab12b2e9b000157444290a58d08615421d7759952de2e38f46cb9c82e46f959e8cf0a460a640f80006808a4717b8602d00295031f489c68ff087aca16ceb0e0000af83a499d0000000cf40006020000000779401b1b5df40001dd2af4ce40240c726551809f03432eadc264f416229d12cc3932871c157080bf3849db00003c3486243dc0600012b2dc08de4bf3c7ad740001850152bf4b9c511000220823800016180012aaee15188000f22edf00023a4000e280000001aac00019fb4b4dc2e0b00015e00000000001569ad2a9e7470001464cbc4da1df433c4682d28f75cfa9b6704356d250be61e5204c74cccf67b3b51142c4955298e462ed491d585fc592392769b608f5e21978face8f98c1a71aa8d8538130225807514403009a20bc3801d31ed3c8141027b0989c6523a28b7213b2de2a30b5cb802d4d047233a0508eaa41940c00015e4e6d22639b857063d3a12324000c86192b5c069cbd671fae7d8aa5f0388ab1824a58c0948b7155a13f7640a68000060238888041eb7248f9bf13b2000646b18d9f4e9d76037f95a454329a08bd386d050acb5f889a96a41e8a580c218d5b1aa54650271332368d2160002b007dc9a4026026b03d5b66186bf800000000024537a16f224c42e8f640000004d689b933268140d3544e4000005d8000df614b3d880006080005c90000a946072e932d00000006a90000000e1c656a1589b20001ae8000c9c00020d8571c802912523989d2c6bf028a2c82e22f22c208d8ac852900209dd5647012c32bd1b9e3d76b194a98a88df55717c89161e22210149a881c134fa494ebe57501f1d145743136493a554bccdd2061e800000006412e4c000c2647e98c0000912000000000000071a33796ee2e14ca0888b52cd66d2803ca4c3b51932129aa83ef72c0d140008752a2a5700001572d32c9902e00015f9088472e2c0000445c860150e58d182203ae36698217d80f44d786e898e63547e1e481f80104d9a9619f80003089170dccad042d9a94f6c000265
  | 28 => 0x605e1c66cce38d18794d454600017d0bdaa7c0000001dc40c73678619728f0e4e480008ac4fc0000000f7c4cd0003491e5ca966b59474f9cb2f58e2aa5cbaf2448680781deb7504c96885c4b87739ad70a8ee14542a6c0846bcb49531f536a6d120d0a802a613c3fa1a98aaac9f33c266c598da66588de4a5a21165ca7e5bda299051169d362b9a22b89f00000000000e190a6a4c4c29a9caf61d60000fdd932a4036ba22400072c63b861c63a4c6309372ddc0d9600036891784ff00024c8cb80a958489ccf343811061d4cfcad343f7000000025856aa5110e635a31200015b421b4f5102c0000003b98000d80000297392846a0006182b7da1852844ab6d47ecce127492b80000002e497010504343e98bf1056a2f0000e28160ea83d08000000a52772162c92a8af6dc20511aae2719c22280000005bb2cc48524c94f0049990e0bc44a0160000c5f42d34cc000c151bb1490000ca02df8000000d045c480011869a93720c405442f01c230bc8d4000000141c00065e5bd21a80009aa2ff000007ea4a0af9d7088e0002068ccc00000015a096c48a00036cb9e17d20b14038000fc66c51ae06640500004720878ac4e3c6bc81300f24c218c98b11ecb250000001c3a0001d630f17ece0f1900015d289e65ba0698000e3745aa3851eed746fd8000c5ac531f5a62115881600db7918586db4cbb07c1d427a1572904000000404b8c879298e00036d9bfa4e556425fc4589270df3529a76b241548d843a09042b800e4ff4a605ecb70400008433cabec000ebb5d500240000006ee977000010578c0db00007586a6957937872f6109d311dca4239b17fc52400037180000d40003373af1c2aa273ba80000000001eda0fc000000698adb9a740df16599a15fec526262698c36a7741b11894144482309281c4a80d5220488d2ae6372487549dad5e1000ff9d24d116488c359f24774c3ab0d7164a13c301f8fd88b06e2aecc686c39617348ce72b830fb23b5952a294652409a4466c2af9f18a0ce1f72d00000007bd02dba10c88eab31b8000e28e8d23232858448ce12812657020003788000f9e0004bb8000000e6164f0dad68e7670eda7e15c6c5a00000010985910a8a5f432c000000000155e15501e0e95daa0006ae2584000bb04fa209c0000002b33c1000070a2e392491741523691398eecdf86b2228d190a6538b2e89e58c72790b96dab40000000000bf2a6b20214003cac7e49b1ca89f676012004c9c2e3ea0003bad94874132d1f7c9f44ef45d9ce115a8d268eaf156bc15e00027c9c541c976c800158ad3f7378000fc0eec1de81fc000d1455e317588ed0000000002d2bf10898000f7e9d659d92b05a60dd07490001500f72f188040000000310e844ec960508b051d0c0003030e5d0527d60000cac8ba51f5acb9443604ad6a5935db0
  | 29 => 0x1a42e2ef14d927248f21009810642e8099ad80d94e5756e0d598020e81ec1660288ead1fd93f8900ef445408cd1a8a72047913cfeeb1445b36a0c4067b2ac19dc34e00059f8001894ef9121bca56ae63b640bb6c3b01d40599e2c2724896960c702f83503d60000804e300000dbddb4021753b6802f49d71cc0abc00049136ab2380002311a5b3803082e31b839d8f90bf257c3c1d804c7c6b015a90d08606f3800000026851aa39c4cc00021b30d4d548556cc21c91088da694909830006550a91d035000019a1e052f400014d9ed0000f0838618d90d2a6e537ad2cadcd874b81eac000663037a19c7105791038270000000763800000038e16397d4e4a0004c8116cda6ccb0c481dd93aad8375880dddeaf71751f093fed171e7126c1b6e0448391014080a10253a70c2a1fe28600000000000000000218e6877838b8796bb868c0001d129692070575ade23b2ba0291a1cd2e00001f074e00059c16d598c056128a01117ade60000000a900000002f40000e8a328800080a00055f8a99ca800000000010389b238f8000ca4b866218b94db076800008ac42ece750daa40028ceb725ae6d11ea3772a80000006b203d8f4054e6a82158811772a7854886e55621a3178800189e62f424ac3cc520852d78ff0caaafc22f8001df80000f9a340d4043f000199d27c0183bf11d44a4ea458800018dcb35358a59453cdbf00034409ea3c22c10af0a5e0c0000000180ce1b1092eb11020005f72f49d3c7eb0000000f88000421b1bce5008a4bf3198000dcc00025ac00000027b0305d6c5120002e71b7600008500000003180000384c5062578b1a51bd21fa5e688f486200028983ec65eb210d8b97175230900029851de000000000000087a0000000e420004dd8000dfe000298800014a6dd61a2200000cbd1e2bb349aa95d2ab83586ee43c60b300d12270b65f1b088aa30000023acbc4b7b00001c80000001222824000ab30001f9c00000059628607e8f233ca1fcc0009e101980016e67d9596bb30000eb04c229d513a0445da1a1d43237b05006c99facd74dc19d4c5c0aa5720458318dbd47c201413e68a6c4b8d80005b377b1f05b14a1e4753b11d008e04632a0406eb9833b1648000b4400037b80000000690cec4ba000712000032e0001809b9cf52000043000154c0fd0e232403e0007248217977c9450409bf49b42593f7a78c35a8233029a08cfe3fd38e137c3d0ae52efb4c89cec970bb9cc00008cc61b12e05b485f75e94e468e3723d935f12ac0004d389c184000000000000008e24b129e55883752412378000dfc1480bad5283be0002c1c51e7b354b80004bcb5a5b41fd4b147ed722819cf2c55900017cd5ea73236b0d816260c45d30f7d00c4a216d80000f446b2a932b977a0000000001e0082a4889a2400000030fabd81124e234
  | 30 => 0x26184600005b6092800000054311b9b600001de00017e60002f30d24f4a6483d31e1d0840000000000000c37612afd4fe089a0001e5c000000000095575c0002c72c040000000000001d942280000fb593000051f226dd8400000000009c000000037fdd46000000000000068d00000006bcb6f00000007725bb1cf0000000bed000202113e81063f88dc000c747111a1416e000000369de3a8573472c4800c4af3703b44f70000571069415e2c23a5341c94a12e6403bfda1e11d167992c7c0da147da919e4a421000365145840f0aa0000b9a1fd0001c983ba3a327c0f5067200043c39adacadf234b94fda7261c3b0ac5400024977ab8987e06424c4ad280006b007390197149db655ae45ad05fb0d500000bcefd0000000ee292b0000000c86cb00002a0800000021aa7a4fe227f0909cdc0005bc0ad3aa56ccbf718186d4a402135b102b47ce7121f601144e4427000000114c64a51d80000007b76e685ad338bb71fd098c1580001ca00008c65032280001014000320900cde0b064fb1b2d582df64309cb8c642b76b530b478000073c8c1800004b460acc95ace5000000000000000000a516363a247304a8bd800078a00006e24c3000174c09e00000000000005080001705d6eb334f39b7c4120900f4a8c00000462e8a33de1200066d80006e600022c932c9623696f1b28d06a0005a0aaacc1c929189000000048e0002be84f000017f280166e86b0001d904c256300028599f0cd028b80004f2b8c42c0020000000000342400000060e00014e0254000060800017d0001301686ef10068588cbe000612184c3d400074091956d6b783cf22494ced19143800000026f2e321b4224aa33791f0d83688e16901e14c480e29d2c286d40914b7994dcfc6ab0000000754dd100002d06f4d1e00033fdd16496000166c0000000003334d3c00000020c4d32dda4fd0af45be7f620e00015800000758a38000e563a82c01816c311540e00684aca6fa33510005970592a48d8800040a956c35e13546b80007120000000001a4ecb279407e00000000001f29bbc000652ac4400018a5388000172dac4a880015bc2f32770000cdae31102800126e22e50d0a5595e5e418f0001a02b6d75aa35800082c6a71f55762d3e7101d348941901a917298a231553fb1c15b285222906885a81b46792d4418486422a13dd1ca0d90678405c420003a020e4000123664aec800050b68d99f85b23e34c6989db905140002e8005851c0868001cc859d6af80008762cd3ce27bc4165c80002f3945492125e0c152ea3cc5e88d98414df165fab1dc046ce6ecb589690bea224b4ac7aa6096cdb938e5a00046c2fd149c4db43609b0c8e7060003194688c593af10057bc21a3d68edcd66b496e18685912a2d4982415c8cc7900005d58eaa3f24a0f945947780050b04a
  | 31 => 0x5acd781caa4888829d3326aa61c181c27812e84c143362271dad6401042cf8001404def695187509acb30652a7409276a280b8e8e48e71000000120c8f40000000e300e63cd99512be9ce4ff3354000d9f17c8278c1600028c800000081155b2f90fa216d43a27106fcb904c8b3946349685939b78e86c3d27ca4e80000003b2b0206360007338000fd0035595b8489fac3b553849c19058d3e2b311d7ce697209424ba893b68f91edd4cacd0b1ac0c83e32959e39fc0001ed2b9047de440000003ae491800036d11e5bcadce188b420ccc8db02d03807cc70400016d8006d674e900000003991208000000000000142800019879500007189e568506cc38c8a90002a20df46b824f28400828792d084018ec9bf09d2235db8b451af99f15dc8760003b3cafc00000035ec78811448b9a404e80001a50530e768dc0b200011a60002d6000076043d0a6800000052173bb818604d3032b00000fa0003f201b0bdca4d23f36b8a6648d1a8abc5b4895b07b168d12e50525d28a0ea21152a71de90ca13d03338b436c7020002875c0a1910001ad11663370871b31ab268f0a7b88c446d880003499bc23b33109179aaaa663dd9a89168e000002b5000070f697800000025f6898000086bd70000388a6000070b3610afe000341800172c000000173000000055225c45048b82e215e85a247d5ff2c10b34a0320a31100d6833000040d88ace974185e5cf65fc6e9979ca4eb886b91bdd47048100026e48640005dd3a6009005738727403240005df88701e282552f8bd050030e62697a947286e1d79c54bba4c464a01b98664aa1b1b50caa61e74fe8238edc9dc5ffbc459d0d8366c2720f920000a287d5d923d308b8a2129cd9e69b2110c8ac714a53044d5aa1f2d588f93b096c70c9980d48470749a561e56e9f106a5194aad6d4a0ad00aac0fa0fca8b84d438716f1ee5b84a4500cba80000dea000000031046000036ad2961ec000000108ad503ff800000099e0000000000e8f5b2b76cc32c1959a02d4b7477400000015d612829bb7ac4fa20839126059d87ae21ca535846d022b08b1428c24e5f8101d44841622d33b95a230a31fa06c000723000120c35678478d2ad19de783478b710fbac2835e8a044489a413f00011d000010e800000002723600016f80000003078000000000000120039a3ad1ea103a00055a8838ae219b0962c204da8772338000d3000017019c400095e0002eed340f0c14c0a29cf800000027b0bb08f0142a924000c0e68919183fe54d5e980000003b44e500007b8bc921280004ae5bd0001f699fcdf554fa4b4a084c11ef125c4042b900018cc83000000000000000fe23d000055656d07fa4d5592bca6a01f352ae0003a4800039eb29163000137a0384d621ed3f6b2a00000016aa2f50799ae4690d763aca899be00000
  | 32 => 0xa7a36800e8b623c85ce8d9149e9e449ea0d000076f092222de369c667d9455dee7565d392e5e144f0490114c000640690330c3bcd4f259af7cec66a33a7005800414864539d5e06a9b51d2c595c274f3ef00001922aa53b021ce7c00074834f03760002eb000056c9a5000226131e84e630b64d69c7e926987bc000ca704a33897b0e105c1034018a73161901b5196a6972f00001302641589268000d3700015d8000ee82f29aa40006492e80000f008465702a6456a42f0001b04000c852b40784040ea10000b542d85b4051b6b55005f6183b43445ae446f629704c4c832d228504a659e63d11e1a383594091b1c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87f8754b65040038dce4a96ca080031b5c952d941000e5739285b282000cad7250b650400399ce4996ca08003335c932d941000726a9265b282000e8d424cb65040050f90bba2ca0800237e0d745941004c6e41ae8b28200287c87551650400187ee8aa2ca080061f217725941000c3e43aa4b282000c6f72549650400399ce4992ca08003335c9325941000726a9264b282000e8d424c9650400587ce8aa6c6080030f5d154d8c1000e37392a5b182000c6d7254b630400395ce4a16c6080032b5c942d8c1000c6fc3a65b182001cce724cb630400199ae4996c6080039354932d8c1000746a1265b18200387e87dd563040010fb09baac6080021f60b7558c100051ec20eab182000a6d821d563040010ff0aba2c60800e1f2157458c100043f43ea8b18200387c87d5163040010fd0eaa2c6080021f21d5458c100161f3a2a8b182000c3d7455163040051b90ea1ac608003875514358c1000c6e41ee4b18200087f855c963040070f90ab92c6080023d2057258c100043f43ea4b18200387c87d4963040010fd0ea92c6080021f21d5258c1000e37392a4b182000c6d72549630400187eeba12c60820b0f1d74258c100061fbaa84b182081c3c75509630400395ce4a12c6080032b5c94258c100062fbae64b182080c5c75cc963040031b90e992c60800317dd53258c103fe2e3aa64b182000ccf724c96304001c9aa4992c608003a35093258c100056a40a64b182009c5e635d4630401393cc6ba0c60800237e1d6318c100062ebaac63182000c9d7458c630401399cc6b90c6080033358d7218c1004c6f41ced2982000a5d83d9653040074b90ab1ca6080023da067654c100043fc2aeca9820028be841d9530400117b083b2a6080063ba087654c1000476c10eca98200987c8759553040071b90eb1aa60800e1fa17768c4100043ec2eed18820028be84dda310400117b09bb462080a697215638c4100066cb1ce11882023a5c8558c31040018eacb38ca00800e1fa17768c0100043ec2eed1802000cd5639c630040031eb0d38860080032d1d3764401000672396ec8802000c7754dd910040018eaa9bb220080031dd4b76440100063aa96ec8802000cb742dd9100400196a85bb2200800335ccb76440100066a996ec8802000c7776dd510040018eeec3aa20080032dddb74440100066bbb6e68802000cd7761cd1004001b88e439a200800339ddb7244010005b9c2a608802036bb0844c11004001970e9bb220080033a1cb76440100063daa6ec8802000c7954dd910040018f6a5bb220080031e54b76440100065da16ec8802000cb942dd910040019b665bb22008003364cb76440100063dbb6ea8802000c7b761d51004001976edba2200800336ddb73440100066dbb0e68802000ceb76dc910040017a706a8a2008002dce153144010
  | 1 => 0x90ab9ec4880031bdd573d891000557c22e7b122000aac845cf624400195ee8b9ec488002b3a1c73d891000667438e7b122000e4f751cf6244001c98ea39ec488003a3dd073d8910007463a0e7b122000e4f541cf6244001c9aa839ec48800393d4e53d891000477438a7b1220008ed8714f624400155d0829ec488002ab61053d89100053742e87b122000a6d85d0f6244001c5aa9a1ec4880038b55143d89100047743887b1220008ed8710f62440014dd0a21ec4880029b61443d89101ad75406e3b122000aae84147624400155b0828ec4880023ba1f41d891000476c3e83b122000a6e85d0762440014db0ba0ec4880038b55341d89100056741e83b122000acd83d076244001c5aa8a0ec4880029ba1441d891000536c2883b122000caf74dc3624406b5cd03b86c488002aba1350d891000556c26a1b122000a6e85d0362440014db0ba06c4880038b55240d89100047743881b12200a8ed8710362440014dd0a206c4880029b61440d891000716aa081b122000ace83103624400159b06206c488002b9a0440d891000572c0881b1220008de86dcd51440018becbb9aa2880a71719773545100064fb26e6a8a2000c9c64dcd5144001998c5b9aa28800237a1873545100062fb28e6a8a2023c5c651cd514400193ec839aa28800327190735451000666310e6a8a2084d54511cd51440471bd0fb1aa2880a63721f635451014c6f438c6a8a20098dc8718d514400199ee7b12a288003331cf62545100063db28e0a8a2009cd8639c331440010fd0dbaa62880030f193754c5102862e31eea98a2000c6c62dd531440e50fd0fb2a62881421f21f654c5100061fbaec898a2000c3c75d9131440018beebb1a6288003171d7634c51000637baec498a2000c6c75d8931440019b6c63826288026b5219310c510425aa42a6218a2000e57654c431440d7d88c498862880031dd94715411004e6a31ce3982200087f855d930440070f90abb260880022fe11764c1100145e422ec98220008ef825d930440031d904bb260880021fa1b754c1100061e326ea9822056c5c63dd530440018d8c5baa60881561fa1f654c1102b43e43eca9822000c3c74d95304400117d0dba260880030fd97744c1100061e32ee89822054c9c63dd13044001958c5ba2608820e2fa1f644c1102a45e43ec89822000c3f75d913044001878ebb22608800317dd7634c1100062e3aec69822000c9f74d8d3044001938e9b1a60880031bdd7624c110006363aec49822000caf74d893044001958e9b1260880033918b714c1100066bb18e29822000ce4621c530440135b10c98060880331d9db658411001e3b3b0cb082200bcb676d9210440019acedb1c2088027359d8638411000762310c7082200ace676d8a10440050ff0eaa6ca0800b0f9d154d94100061eba2a9b282001
  | 2 => 0x464d891000752c08c9b122000a6e86d5362440014d90daa6c4882271b9db54d891000717b26a9b122000e2c64d5362440014dd0caa6c4880029b21954d8910446373b2a9b122000e2f645536244001c58c8aa6c488002b3a1b73d8910006673b6e7b122000d4f75dcf6244001c9ecbb9ec4880039319773d8910006c7ba6e7b122000e8f64dcf6244001d18c9b9ec488002b3a1873d8910006673b0e7b122000e4f651cf6244001c98ca39ec488003a3d9073d891000746320e7b122000cce76d8f6244001c9ecbb1ec4880039319763d891000747b26c7b122000e8c64d8f6244001c9eebb1ec488003931d763d891000747ba6c7b122000e8c74d8f6244001c9ea9b1ec4880039355363d891000476c3cc7b122000a6e8598f62440014db0b31ec488002aba1263d891000556c24c7b122000ace8398f62440011df0eb1ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec488002b3a1863d8910006673b0c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000e4f7518f6244001c98ea31ec488003a3dd063d8910007463a0c7b122000e4f5418f6244001c9aa831ec48802ab9a1b71d89100075232483b122000f255450762440017c100a0ec48802abaa1b70d8910006d5ba6e1b122000a6d84dd762440014dd0b3aec488002aba1275d891000556c24ebb122000ace839d7624400159b073aec488002abe1175d891000556422ebb122000acf835d7624400159906baec4880029ba1c75d891000637438ebb122000a6d841d76244001c5f0bba6c4880038b21774d891000717baee9b122000e2c75dd3624400195ce3ba6c4880032b1c774d891000656b86e9b122000a6e859d362440014db0b3a6c488002aba1274d89100056741ce9b122000acd839d362440014df0aba6c4880029b21574d891000567c1ae9b122000acc835d362440014dd0a3a6c4880029b61474d891043d73408e9b122000ae5811d3624400155d0e3a6c4880032ba1c74d891000717428e9b122000e2d851d36244001c5eea3a6c4880038b1d474d891000753408e9b122000ea5811d362440014dd0faa6c4880029b21f54d891000717ba6a9b122000e2c74d53624410d4db0b2a6c4880038bd5254d89100053743aa9b122000a6c875536244001c5f08aa6c4880038bdd154d8910007163a2a9b122085a6e8515362440018deebb9ec4880032bdd373d891000667baee7b122000e4f75dcf624400189eebb9ec488003335d773d8910007263aee7b122000ccf74dcf6244001d1ee9b9ec48800323dd373d891000666ba6e7b122000e8c74dcf6244001c9ea9b9ec4880039355373d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d89100056741ce7b122000a6f855cf62440014d
  | 3 => 0x231a2000acd82d046344001c3aa8a08c68800297a144118d100052ec288231a20098de87c8463440011bb0f908c68800297a172118d100052ec2e4231a2000a9e84c84634400153b09908c688003a350a2118d1004c6f4384231a20008dd8708463440014bd0a108c688002976142118d100054f4204231a2000a9d840846344001d1a84108c688002b6a002118d100056cc004231a2000a9e84d40634400153b09a80c68800297a174018d100052ec2e8031a2000e1d5490063440131bd0e200c6880023761c4018d100052f4288031a2000a5d851006344001c3aa8200c688002b3a084018d1000566c108031a2000ad68110063440015ab02200c68802637a1f2018d100046ec3e4031a2000a5e85c8063440014bb0b900c688002a7a132018d100054ec264031a2000e8d42c806344001d1a84900c688002b5e052018d100056a40a4031a20098de8708063440011bb0e100c68800297a142018d100052ec284031a2000a9e84080634400153b08100c688002b5a042018d100056ac084031a2000a5f8544063440014b90a880c688002a7e111018d100054e4222031a2000c5f539da534400117f08bb4a68800a2f2117694d1004c6e41aed29a20008ef825da53440031d904bb4a6880029760f6594d100070fa9ec929a2003a5c85d8e534400517d09bb2a6880022f6137654d1000c77416eca9a20008ed82dd9534400117f08bb2a68800a2f2117654d100046fc1aeca9a20008ef825d953440031d904bb2a6880261fa1f6554d1001c6f43ec6a9a20008f686dc553440019c8c5b8aa6880027ca037154d100063bb28e2a9a2000cd7631c553440019c8c438aa6880029ba1b75d8910006373b6ebb122000a6e861d762440018dcec3aec4880031b9db65d891000536c26cbb1220008ed8799762440014dd0b32ec488002aba1265d891000556c24cbb122000ace83997624400159b0732ec4880023be1d65d891000557c22cbb122000aac84597624400159f06b2ec488002b320d65d891000537430cbb122000c6e7619762440014db0832ec488002aba1b74d8910006573b6e9b122000e2f65dd36244001c58cbba6c488003691c774d891000557430e9b122000cae761d36244001c5eca3a6c4880038b19474d8910006573b6c9b122000e2f65d936244001c58cbb26c4880038be1764d89100071642ec9b122000e2f75d936244001c58ebb26c4880023b61e64d89100053742cc9b122000a6d85993624400155d09326c488002b3a0e64d891000566c1cc9b1220008ef8759362440014df0ab26c4880029b21564d891000567c1ac9b122000acc8359362440014dd0a326c4880029b61464d891000557430c9b122000cae761936244001c5eca326c4880038b19464d891000717428c9b122000e2d851936244001c5eea326c4880038b1d
  | 4 => 0x344001c9eca310c688003931946218d1000747b20c431a2000e8c64188634400199b0e310c68800393a146218d1000726c28c431a2000e8e841886344001d1b08310c68800393d506218d1000726aa0c431a2000ec5811886344001d9300310c68800297a1b5218d100052e436a431a2000c5e76d486344001c3ec9a90c688003871935218d1000727b16a431a2000e4c62d4863440014bd0ca90c688002972195218d100062f3b2a431a2000e1f645486344001c38c8a90c688003535c95218d1000727b12a431a2000e4c62548634400153d0da10c688002a721b4218d100064f3b68431a2000e1f65d086344001c38cba10c688003a3d8b4218d10007463168431a2000a9e8650863440015390ca10c688003279d94218d100070fb2a8431a2000e1c655086344001b1ae4a10c688003a3d894218d10007463128431a2000e94649046344001d88c5208c688003c55514118d10007623128231a2000bd08050463440015ad0d108c688003b118a2118d10007c2a144231a2000ec4624846344001d90c5100c688003f08862018d10007c4a124031a2000a5d82d50634411d8bee5aa0c68823e976165418d100070faa4a831a2000e1f84550634411fc3ce8aa0c68823f875d15418d100052fc12a831a208fc5f72550634411d4bd0a2a0c68800317d517218d100062eaa2e431a20098df825c8634401399f04b90c688002976135218d104662fb96a431a2000c5d72d4863440131bd0f290c6880023761e5218d1046d2ec2ca431a2000a9e84948634400153b09290c688003335ca5218d1000666b92a431a2000a5f845486344001c9f04a90c68823717dc95218d1046f27392a431a2000c5d72548634411bc9ae4a90c688003135c95218d1004c6f438a431a20008dd8714863441194bd0a290c688002a7a105218d100054ec20a431a2000a5e85d0863440014bb0ba10c68800387d534218d100070eaa68431a2000ad681d0863440015ab03a10c68800387a174218d100070ec2e8431a208ac9f72d08634400193ae5a10c68800387d4b4218d100070ea968431a2000e9681d086344001d2b03a10c68802637a1e4218d100046ec3c8431a2000a5e8590863440014bb0b210c68822ea76124218d1000666b948431a2000a5e8550863440014bb0aa10c68800387d514218d100070eaa28431a2000ccd725086344001c3d0aa10c688003876154218d1000747c128431a208bc9f725086344117d1ce4a10c688003275c94218d1045f46b928431a2000c8d725086344001c3ea4a10c688003875494218d1004c6f4388431a20008dd8710863440014bd0a210c688002976144218d104554f4208431a2000a9e84144634400153b08288c68802637a1f4118d100046ec3e8231a2000a5e85d0463440014bb0ba08c688003875534118d10005674168
  | 5 => 0x800333e0f7258d100043fc2ae4b1a200387c855c9634400117f08b92c68800a2f2117258d100046fc1ae4b1a20008f7815c963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880021fa1f5258d1001c3e43ea4b1a2000c3f74d496344127878e9a92c6880031bdcb5258d1000e36396a4b1a200087e8754963440010f90ea92c6880030fdd15258d104961e3a2a4b1a2000c6f7254963440038d8e4a92c6880022fa1f4258d100145e43e84b1a2000c3f75d096344105878eba12c6880032bdcb4258d1000e5639684b1a20008be8750963440011790ea12c6880030fdd54258d1040e1e3aa84b1a2000caf725096344003958e4a12c68800237a1f3258d100062fbae64b1a2080c5c75cc9634400193ee9992c688247271d33258d1000667b9664b1a2001ccc72cc963440031b90e992c68800317dd53258d103fe2e3aa64b1a2000c9f744c96344121938e8992c68800333dc93258d1000e6639264b1a2000e4d524c96344001d1a84992c688003391cb7158d100046fc3ac631a2000a5f8558c63440014b90ab18c688002a7e116318d100054e422c631a2000acf8258c634400159904b18c6880023760a7618d100062f3b6ca31a2000a5d84d9463440014bb05b28c6880023761e6518d100054f424ca31a2000a9d84994634400159d05328c688002b360a6518d100046fc3aca31a2000a9f84594634400153908b28c688002b3e096518d1000566412ca31a2000c5e7619463440014bb08328c688002976086518d100064f3b6c831a2000e1f65d906344001c38cbb20c68800387e176418d100070e42ec831a2000a9d82d9063440011bb0f320c68800297a166418d100052ec2cc831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100052f428c831a2000a5d85190634400193cec320c68800387d946418d100070e328c831a2000e1e851906344001c3b0a320c688002a76086418d100074ac08c831a2000a5e86d5063440014b90daa0c688003179db5418d100070fb26a831a2000e1c64d5063440014bd0caa0c688002972195418d100062f3b2a831a2000e1f645506344001c38c8aa0c68800237a1b7218d100062fb2ee431a2000c5c65dc8634400193ec9b90c688003271937218d100062fb2ae431a2000c5c655c8634400193ec8b90c688003271917218d100046fc3ec431a2000ccd72d8863440011bb0f310c68800297a166218d100052ec2cc431a2000a9e84988634400153b09310c68800237e1d6218d100052fc2ac431a2000a5c85588634400153f08b10c688002a72116218d100046ec38c431a2000a5e8518863440014bb0a310c688002a7a106218d100054ec20c431a2000ccd721886
  | 6 => 0x54ec2643b1a2000e8d4288763440011bd0e10ec6880023761c21d8d100052f42843b1a2000a5d85087634400153d0810ec688002a761021d8d1000746a1043b1a2000ada8008763440015b30010ec68800297a1770d8d100052ec2ee1b1a2000a9e84dc3634400153b09b86c688002a7a1350d8d100054ec26a1b1a2000a5e85d0363440014bb0ba06c6880038755240d8d100046f43881b1a20008dd8710363440014bd0a206c6880029761440d8d100070eaa081b1a2000ace82103634400159b04206c688002b5a0440d8d100056ac0881b1a20008de87c8363440011bb0f906c68800297a1720d8d100052ec2e41b1a2000a9e84c83634400153b09906c688003a350b20d8d1000746a1241b1a20008de8708363440011bb0e106c68800297a1420d8d100052ec2841b1a2000a9e84083634400153b08106c688002b5a0420d8d100056ac0841b1a2009c5c635d6634400187ce9b2cc6880031b9cb6598d100061f3a0cb31a2000c6e72196634400187ecaba4c6880030f1957498d1004e4e31ae931a2000c3e75d92634400187aebb24c6880032b9cb6498d100061f3a8c931a2000c3d75192634400195ce4324c688003179d76398d100062ebaec731a2000c9e74d8e634400193ae9b1cc688003339cb6398d1000637b2ae531a2000c6c655ca634400195ec8b94c6880032b1917298d1000667b1ae531a2009ccc635ca63440018dcea314c6880031b5d46298d10006573a0c531a2000cad7418a63440010fd0fb2ac6880030f1d36558d1000636396cab1a200087e871956344001878e832ac6880031b1c86558d100145f436e8b1a2000c3f65dd16344001878cbba2c6880022fa1f6458d100061fbaec8b1a2000c3c75d916344001958e5b22c6880022fa1c6458d100061fba8c8b1a2000c3c751916344001958e4322c6880063ba1b7258d1000637b2ee4b1a2000c6c65dc9634400195ec9b92c6880032b1937258d1000637ba8c4b1a2000c6c75189634400195ee8312c6880032b1d06258d100043ec26eab1a200087d82dd5634400187eebba2c6880030f1d77458d100061fc2ee8b1a2000c3c85dd1634400117b05ba2c6880021fe157458d1001c3e42ae8b1a20008df835d163440011df04ba2c6880063b2097458d100061fba8e8b1a2000c3c751d163440010fd0faa2c68800e1f21f5458d100061fba6a8b1a2002c3c74d5163441138d8e5aa2c6880021fa1d5458d100043e43aa8b1a2000c3f745516344005878e8aa2c6882231b1c95458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f85dc963440018d90bb92c6880032be137258d1000656426e4b1a2000c6f54dc963440018daa9b92c68
  | 7 => 0x4c62d4b63440014bd0ca96c6880029721952d8d100070fb22a5b1a2000e1c6454b6344001a9ee4a96c68800393d8952d8d1000726312a5b1a2000a9e86d0b63440015390da16c68800387d9742d8d100070e32e85b1a2000e8f62d0b6344001d18c5a16c688002a7a1942d8d100054e43285b1a2000e1f6550b6344001c38caa16c68800363dc942d8d1000747b1285b1a2000e8c6250b6344001d28c920ec688003c555141d8d10005e840283b1a2000ec4628876344001f0a8510ec688003b218a20d8d10007e110c41b1a2000f894248363440015ab03baec688002a7a1275d8d100054ec24ebb1a2000ace829d7634400159b053aec688003175d475d8d100052f42ce9b1a2000a5d859d3634400159d053a6c688002b360a74d8d100052f428e9b1a2000a5d851d363440015ad023a6c688002b560474d8d100052ec16a9b1a2000e1f549536344001c3f08aa6c68800387dd154d8d100070e3a2a9b1a2000a5f8255363440018bea9b96c6880031755372d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d100062faa2e5b1a2000c5d545cb634400199f04b96c68800297a1472d8d100052ec28e5b1a2000a9e841cb634400153b08396c688002b5a0472d8d100056ac08e5b1a2000ada801cb63440015b300396c6880029761352d8d100062fb96a5b1a2000c5d72d4b63440011bd0f296c6880023761e52d8d100054f424a5b1a2000a9d8494b634400199ee5296c68800333dc952d8d100052fc22a5b1a2000e4f8254b63440018bee4a96c68800393dc952d8d1000627b92a5b1a2000c5d7254b6344001c98e4a96c68800237a1c52d8d100046ec38a5b1a2000a9e8414b634400153b08296c68800297a1742d8d100052ec2e85b1a2000e1f54d0b6344001c3aa9a16c68800387a1742d8d100070ec2e85b1a2000c9f72d0b634400193ae5a16c68800387d4b42d8d100070ea9685b1a20008de8790b63440011bb0f216c68800297a1642d8d100052ec2c85b1a2000ccf7290b63440014bd0aa16c6880029761542d8d100070faa285b1a2000e1d5450b634400199ee4a16c68800387a1542d8d100070ec2a85b1a2000e8f8250b634400193ee4a16c688003a3dc942d8d1000647b9285b1a2000c9d7250b6344001d18e4a16c68800387d4942d8d100070ea9285b1a20008de8710b63440011bb0e216c68800297a1442d8d100052ec2885b1a2000a5e85dc763440014bb0bb8ec688002a7a1051d8d100054ec20a3b1a20008de87d0763440011bb0fa0ec68800297a1741d8d100052ec2e83b1a2000e1d54d07634400159d05a0ec688002b360b41d8d100070eaa283b1a2000a5e8510763440014bb0a20ec68800237a1f21d8d100046ec3e43b1a2000a5e85c8763440014bb0b90ec688002a7a1321d8d100
  | 8 => 0x610ec888002a760c21d91100055d40043b222000ab980087644406d56d03b86c8880022fa1f50d91100045ec3ea1b2220008be87c83644400117b0f906c8880028fa1720d91100051ec2e41b222000a9e83c83644400153b07906c8880032bdcb20d911000657b9241b2220008be87083644401717b0e106c8880028fa1420d91100051ec2841b222000a9e83083644400153b06106c888002ada0420d91100055ac0841b222000c3f745536344005878e8aa6c688003175d753d8d100054f420a7b1a2000a9d8414f634400159d0429ec688002b360853d8d100052f42e87b1a2000a5d85d0f6344001c3aa9a1ec68800a37e1d43d8d100070eaa287b1a2000a5e8510f63440014bb0a21ec688002b3a0843d8d1000566c1087b1a2000c6f7254b63440038d8e4a96c6880032bdc942d8d1000e5639285b1a2000ccf72ccb63440014bd0b196c6880029761632d8d100054f42465b1a2000a9d848cb6344001c9aa5196c688003a350a32d8d1000c6fc3a65b1a2000ccd724cb6344001c9aa4996c688003a350932d8d100052f42865b1a2000a5d850cb634400153d08196c688002a761032d8d100052ec26cbb1a2000a5d82d97634400153d0932ec688002a761265d8d1000567414cbb1a2000acd82997634400153f08b2ec688002a721165d8d1000567c12cbb1a2000acc8259763440014bb0832ec6880029760865d8d100070fb2ec9b1a2000e1c65d936344001c3f0bb26c6880038721764d8d100054ec16c9b1a2000a5e8599363440014bb0b326c688002b3a0a64d8d1000566c14c9b1a2000a5f8559363440014b90ab26c688002b3e0964d8d1000566412c9b1a2000a5e8519363440014bb0a326c68800387d9464d8d100070e328c9b1a2000e1e851936344001c3b0a326c688002a760864d8d100074ac08c9b1a2000a5e86d5363440014b90daa6c68800387d9354d8d100070e326a9b1a2000a5e8655363440014b90caa6c68800387d9154d8d100070e322a9b1a2000c5f65dcb63440018b8cbb96c68800327d9372d8d100064e326e5b1a2000c5f655cb63440018b8cab96c68800327d9172d8d100064e322e5b1a2000ccd72d8b63440014bd0b316c6880029761662d8d100054f424c5b1a2000a9d8498b63440014bf0ab16c6880029721562d8d100054fc22c5b1a2000a9c8458b63440014bd0a316c6880029761462d8d100054f420c5b1a2000a9d8418b634400199ae4316c68800393d9462d8d1000726328c5b1a2000e8f6418b6344001d18c8316c6880033361c62d8d1000727428c5b1a2000e4d8518b6344001d1d08316c688003a361062d8d1000727aa0c5b1a2000e4d5418b6344001d8b02316c688003b260062d8d100052f436a5b1a2000a5c86d4b6344001c3ec9a96c6880038719352d8d1000727b16a5b1a2000e
  | 9 => 0x52d91100051f432a5b222000a3c8654b644412587ceca96c8880038bd8952d911000716312a5b222000a9e86ccb644412393ced996c88800387d9732d91100070e32e65b222000e8f62ccb6444001d18c5996c888002a721932d91104864f3b265b222000e1f654cb6444001c38ca996c88800363dc932d911000747b1265b222000e8c624cb6444001e1aa4996c88802eada1b71d91100069bbaee3b222036bb280dc76444001d48c510ec888003aa18a20d9110007d110c41b222000dab72483644400147b05baec8880030f5c775d91100061f386ebb222000c3c70dd7644400147d0b3aec8880030f5d475d91100051f438ebb222000c3e871d7644400147b043aec8880030fdd773d91100051f42ce7b222000a3d859cf644400155d0539ec888002ab60a73d91100051fc2ae7b222000a3c855cf644400187eeab9ec8880022fa1c53d91100045ec38a7b222000aae8214f644400155b0429ec8880030fdd772d91100061e3aee5b222000c3f85dcb64440018790bb96c8880022f61e72d91100051f42ce5b222000a3d859cb644400153d07396c888002a760e72d91100051fc2ae5b222000a3c855cb644400187eeab96c8880030f1d572d91100061fc2ae5b222000c3c855cb644400195f04b96c8880022fa1c72d91100051f428e5b222000a3d851cb644400153d06396c888002a760c72d91104cd5b408e5b222000ab5811cb644413157500396c888002ae60072d91100051f43ea5b222000a3c87d4b644400187ee5a96c8880030f5cb52d91100045f43ca5b2220008bd8794b644412f47b0b296c888002a7a0e52d91100054ec1ca5b222000a3e8754b64440014790ea96c8880038be0952d91100061fb92a5b222000c3d7254b644400117d0e296c8880022f61c52d91104b51f428a5b222000a9e8314b644400153b06296c88800387dd732d91100070e3ae65b222000c9f72ccb644400193ae5996c88800387d4b32d91100070ea9665b2220008be878cb644400117b0f196c8880028fa1632d91100051ec2c65b222095a9d838cb644400195ee5196c8880038b54a32d911000657b9265b222000e2d524cb6444001c3eea996c888003871d532d911000747c1265b222000c9f724cb6444001d1ee4996c88800323dc932d91100064eb9265b222000e8c724cb6444001c3ea4996c888003a394932d91100070ea9265b222000e8d524cb6444001c1aa4996c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c888252a7a0c32d91100061fbaee3b222036aba80dc7644400117d0e28ec88802e2f61c51d91100045f43e43b2220008bd87c87644400147d0b90ec8880028f61721d91100054f41e43b222000a9d83c87644400117d0e10ec88802e2f61c21d91100051f42843b222000a3d85087644400153d
  | 10 => 0x32a2000c3d74d9065440010fb0f320ca8800297a0e64195100052ec1cc832a2000a6e8299065440014db05320ca880021fe1d64195100052fc1ac832a2000a5c8359065440014df04b20ca880029b209641951001c3f438c832a200087d87190654400187ae8320ca880030f61c64195100051ec10c832a2000c3f721906544001c6b02320ca880030f19172195100043fc3ec432a2000c6d72d8865440010fb0f310ca880028fa1262195100051ec24c432a2000a5e8398865440014bb07310ca880021fe1d62195100051fc22c432a2000a3c8458865440014bf06b10ca880029720d621951001c3f438c432a200087d87188654400147d08310ca880028f61062195100052f418c432a2000a5d8318865440018dae4310ca880038b190621951000636c38c432a2000e2e841886544001c5b08310ca880031bdd0621951000636ba0c432a2000e4e831886544001c9b06310ca8800399604621951000734c00c432a2000a3e86d0865440014790da10ca880030f9db421951000717b168432a2000e2c62d0865440014790ca10ca880030f9d9421951000717b128432a2000e2c6250865440014bd0d990ca88003179db32195100070e3266432a2000e4f62cc86544001c98c5990ca880029721932195100062f3b26432a2000e1c644c86544001a9ae4990ca8800393d893219510007263126432a2000f0d424c86544001c68c9208ca880029d21941195100069aba28232a2000b70805046544001cc8c5108ca88003c950a21195100053a4324232a2000e68628806544001ec443100ca880029e219201951000794a124032a2000a3e86dd7644400187cedbaec8880028fa1875d91100061f3b0ebb222000c3e76d97644400147b05b2ec8880022f61e65d91100051f42ccbb222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb2220008bf87597644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147d0c32ec8880030f9d865d91100051ec10cbb2220008be86dcb644400187ecbb96c8880030f19772d91100061fb2ae5b222000c3c655cb644400517f0fb16c8880032b5cb62d91100045ec3cc5b222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b2220008bf8758b644400147f0ab16c8880028f21562d91100054fc1ac5b222000a9c8358b644401717b0e316c8880028fa1462d91100051ec28c5b222000a9e8318b644400153b06316c8880032b5c862d911000717b28c5b222000e2c6518b644400195b0e316c8880038ba1462d911000716c28c5b222000e2f7518b6444001c58ea316c888003a3a0c62d911000746c18c5b222000ea58118b6444001d5300316c8880028fa1b52d91100051e436a5b222093c3e76d4b6444001c5ec5a96c8880038b18b
  | 11 => 0x440010fd0e10eca880321f61c21d95100051f42043b2a2000a3d8408765440014bd0610eca880029760c21d951000716a1043b2a2000a7a8008765440014f30010eca880028fe1170d95100051e422e1b2a200087e87d0365440010fb0fa06ca880021fa1c40d95100643ec3881b2a2000a5e8310365440014bb06206ca880029ba0840d951000536c1081b2a2000a768110365440014eb02206ca880021fa1f20d95100043ec3e41b2a2000a3e84c83654400147b09906ca8800297a0f20d95100052ec1e41b2a2000e2d42c836544001c5a84906ca880021fa1c20d95100643ec3841b2a2000a3e84083654400147b08106ca8800297a0c20d95100052ec1841b2a2000a768108365440014eb02106ca880030f197745951000656390c8b2a2000c5c65dcd6544001938c9b9aca880031719473595100064e320e6b2a2000c6c65dc96544001958c9b92ca880032bdd06259510006563a0c4b2a2000ccf731896544001998e6312ca8800a2fa1f74595100061fbaee8b2a2000c3f85dd165440018790bba2ca880022f60b74595100061fa96e8b2a200087f855d165440011bf06ba2ca880263720d745951000477c12e8b2a20018ec825d1654400117d0e3a2ca880030fdd474595100143e43aa8b2a2000c3f745516544005878e8aa2ca8823f171cd545951044636392a8b2a20098de87dcd65440018beebb9aca8800327dd373595100064e3a6e6b2a2000c5f54dcd65440018baa9b9aca880023760b73595100062fa96e6b2a2000c5f751cd654400193ee839aca88003271d0735951000c7743ee4b2a2000c6f75dc9654400195ee9b92ca880032b1d3725951000667b9ee4b2a2000ccc73dc965440018df0bb92ca880031b217725951000657c26e4b2a2000cac84dc965440018dea9b92ca880031b553725951000667c1ee4b2a2000ccc83dc965440010ff0ab92ca880022fe1172595100145e422e4b2a20008df835c965440131b906b92ca880023ba1c725951000637ba8e4b2a2000caf741c96544001958e8392ca8800333dcc725951000666398e4b2a200187c87549654400187ee8a92ca8824b0f1d152595100062fb9aa4b2a208dc5c7354965440018dee4a92ca880071b1c952595100045f43e84b2a20028bc87d09654400193ee7a12ca8822b271cf425951000657b9684b2a2001cac72d09654400117d0ea12ca880022f21d42595100064fb9a84b2a208bc9c73509654400195ee4a12ca880072b1c942595100046f43e64b2a20098dc87cc9654400193ee9992ca88247271d3325951000667b9664b2a2001ccc72cc965440011bd0e992ca880023721d32595100064fba264b2a2090c9c744c9654400199ee4992ca88007331c9325951000726a9264b2a2000e8d424c965440010fb093b0ca880021f60a76195100043fc3ec8
  | 12 => 0x38bd8b42d95100071631685b2a2000a3c8650b654410387ceca16ca880038bd8942d95100071631285b2a2000a5e86ccb65441018bced996ca880038719332d951000727b1665b2a2000e4c62ccb65440014b90c996ca881ff179d932d95100070e32265b2a2000d4f724cb6544001c9ec4996ca880039318932d951000786a1265b2a2000e34649076544001a6ee8a0eca880038d19141d9510005b840283b2a2000e64628876544001e4a8510eca880039918921d95100073431441b2a2000f62218836544001cd0c4906ca88003ca50920d95100043ec16e9b2a2000c3f845d365440010ff04ba6ca880030f5d074d95100053b408e9b2a2000a75811d365440014eb03b9eca880028fa1273d95100051ec24e7b2a2000a6e829cf65440014db0539eca88003175cc73d95100043f43e87b2a200087d87d0f654400187ee9a1eca880030fdd143d95100043f43887b2a200087d8710f65440014dd0421eca880029b60843d95100043ec26e5b2a2000a3e849cb654400147b09396ca8800297a0e72d95100052ec1ce5b2a200087f845cb65440018df04b96ca880028fa1072d95100051ec20e5b2a2000a5e831cb65440014bb06396ca880029da0472d95100053ac08e5b2a2000a7a801cb65440014f300396ca880021fa1f42d95100043ec3e85b2a2000c3f74d0b654400187ae9a16ca880030fa1f42d95100061ec3e85b2a2000c3f72d0b654400187ae5a16ca880021fa1e42d95100043ec3c85b2a2000a5e8390b65440014bb07216ca880021fa1d42d95100043ec3a85b2a2000c3f7450b654400187ae8a16ca880030fa1d42d95100061ec3a85b2a2000e2f8250b654400187ee4a16ca880030f5c942d95100043f43885b2a200087d8710b65440014bd06216ca880029760c42d95100062fba665b2a2000c5d74ccb65440018bee5996ca88003175cb32d95100070fa1665b2a2000e1d42ccb65440010fd0f196ca880021f61e32d95100051f42465b2a2000a3d848cb65440018dee5196ca880038b50a32d951000637b9265b2a2000e2d424cb65440018bee8996ca88003175d132d951000727c1265b2a2000c5f724cb6544001c9ee4996ca8800313dc932d95100062eb9265b2a2000e4c724cb6544001c3e84996ca880039390932d95100070ea1265b2a2000e4d424cb6544001c1a84996ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca8800297a0f71d95100052ec1ee3b2a200087e87d0765440010fb0fa0eca880030fdd341d95100052f41e83b2a2000a5d83d0765440014dd05a0eca880029b60b41d95100061fba283b2a200087e8710765440190fb0e20eca880021fa1f21d95100043ec3e43b2a2000a3e84c87654400147b0990eca8800297a0f21d95100052ec1e43b2a2000e2d4288765
  | 13 => 0x64eb9a85b2c2001cae7250b658400195ae4a16cb0802637e1f32d96100046ec3e65b2c20008df874cb65840011bb0e996cb080039354932d961000746a1265b2c2000cd6735c765840014bd07baacb0800a1f21d54596100061fba2a8b2c2002c3c7455165840030f90ea92cb080031bdc9525961000726a9264b2c2000e8d424c9658400147b093aec7080021fe1175d8e100043fc12ebb1c200387e85dd363840010fb0bba6c70800e1fe1f54d8e100043ec3ea9b1c200087f8755363840010fb0eaa6c7080030fdd154d8e100161e3a2a9b1c200387e85dcb63840010fb0bb96c70800e1fe1f52d8e100043ec3ea5b1c200087f8754b63840010fb0ea96c70820b0f9d742d8e100061ebae85b1c2081c3e7550b638400187aeaa16c7080072b9c942d8e1000656b9285b1c2080c5e75ccb63840018baeb996c70800637e1d32d8e103fe2f3aa65b1c2000c5d754cb638400199ae4996c7080039354932d8e1000746a1265b1c2000ad4814cb63840018eceab8ec70800297a176398e100061fba2a8b1c2002c3c7455163840014bd0bb9ac70800317dd75358e100054ec20a6b1c2000acd8214d63840051b90ea1ac70800b271d14358e100070eaa286b1c2001cae72509638400195ae4a12c7080063721d3258e1000667b9264b1c2000e4d524c96384001d1a84992c70800237e1d6318e100052fc1acb29c20008dd839d953840a14bd07b2ca30808f1799473546100062eb28e6a8c2029a5e85d8e31840018b8eab1a63080023761f630c61011d2f42ec618c2009cd6635c4308400187ea9ba6ca880030f5d254d95100053ac0ca9b2a200287f87553654400187ae8aa6ca880031bd4b72d95100051f424a5b2a2000a3d8494b65440014bd07296ca880029760e52d951000c3fc3aa5b2a2000c6d7254b654400199ee4996ca88007331c932d95100072729265b2a2000e4d524cb6544001d1a84996ca880030f5d364d95100052f41cc9b2a2000a5d8399365440014dd05326ca880029b60a64d95100052fc1ac9b2a2000a5c8359365440014df04b26ca880029b20964d95100643ec38c9b2a2000c3d74193654400187b0e326ca880028f60864d95100071ac08c9b2a2000c3c64dcb6544001878c8b96ca880031b5cb62d95100051f424c5b2a2000a3d8498b65440014bd07316ca880029760e62d95100051fc22c5b2a2000a3c8458b65440014bf06b16ca880029720d62d95100643ec38c5b2a2000a3e8418b654400147b08316ca8800297a0c62d95100052ec18c5b2a2000c6d7218b6544001c58c8316ca880031b61c62d951000717420c5b2a2000e2d8418b65440018dee8316ca880031b5d062d951000727418c5b2a2000e4d8318b6544001ccb02316ca880039a60062d95100051f43685b2a2000a3c86d0b654410587ceda16ca88
  | 14 => 0x542885610c0031e90e90ac218026b520d215843004c7ac3cc32886003a7485586510c0531bf06bb2a218027171cd655443004e6a39cc2a8860098f487585510c0139a8e6b0aa218027359c5768c43014d2e42ac31886009c5e73596500c001938e9bb2601800317d53764c0300062eaa6ec98060008df82dd9300c0011bb05bb2601800317d4b764c0300062ea96ec9806000c9f42dd9300c00193a85bb2601800317ddb754c0300062fbb0ea9806000d1c741d5300c00193eedba2601802637a0f74d97100046ec1ee9b2e200287f8755365c400587ce8aa6cb880030f5d154d971000c3fc3aa5b2e2000c6d7254b65c4001c9aa4996cb88003a350932d97100143e43aa8b2e2000c3f7455165c40030f90ea92cb880031bdc9525971000657b9284b2e2001cac7250965c4001c9aa4992cb88003a350932597100043fc22ebb1e200087f825d763c40070fd0bba6c7880021f61774d8f100061f3ace9b1e2000c3d759d363c400155b053a6c7880030f9d574d8f100061ebaae9b1e2000c3e855d363c400187b0aba6c7880022fe0974d8f1001c3fc3ea9b1e200087d87d5363c400587ce9aa6c7880030f5d354d8f100043fc3aa9b1e200087d8755363c400587ce8aa6c7880030f5d154d8f100164f3a487b1e20028df8750f63c400593ce8a1ec7880038755143d8f1001c3f42ee5b1e200087d85dcb63c400517d09b96c7880022f61372d8f1001c3fc3ea5b1e200087d87d4b63c412787ce9a96c7880030f5d352d8f100043fc3aa5b1e200087d8754b63c412587ce8a96c7880030f5d152d8f100145fc3e85b1e20008bd87d0b63c410587ceba16c7880030f5d742d8f100045fc3a85b1e20008bd8750b63c410387ceaa16c7880030f5d542d8f1000657b9285b1e2001cac7250b63c41018bceb996c788003175d732d8f1048e4f3a665b1e2000c9d74ccb63c40031bf0e996c7881ff179d532d8f100062ebaa65b1e2090c9e744cb63c400193ae8996c788003335c932d8f1000726a9265b1e2000e8d424cb63c400587ce8aa2c7880030f5d15458f1000657b9284b1e2001cac7250963c40031b90e992c78800333dc93258f1000726a9264b1e2000e8d424c963c40011bf0eb18c78800a2fa127694f100045ec24ed29e2000a5f8359653c400517d093b2a7880022f6127654f104d6aa288e6a8e209ab54854c431c40139b4c6b8063880023761f630c3100062f32ce7b2c20098de83dd365840011bb07ba6cb0800a1fe1d54d96100061eba2a9b2c208fc5e7355365840131bf0eb9ecb0800317d5173d96100062eaa2e7b2c20008df825cf65840018bea4b9ecb0802637a0f72d96100046ec1ee5b2c200187f8754b658411b8bce6a96cb08003175cd52d961000636b92a5b2c208ac9e73d0b658400193ae7a16cb0822f279cd42d961000
  | 15 => 0x832cc2980030fd9574985300061e32ae930a6000c3e75d92614c00187aebb24c2980030f9d464985300061eba8c930a6000aad82192614c0010fd0fb2ac2980030f1d3655853000636396cab0a600087e87195614c001878e832ac2980031b1c865585300145f436e8b0a6000c3f65dd1614c001878cbba2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614c001958e5b22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c00155b04322c2980032b1c8645853000637b2ee4b0a6000c6c65dc9614c00195ec9b92c2980032b193725853000556c10c830a60008f787584614c0015c904b08c29800b0f9d154185300061eba2a830a6000e1d5450c614c0038dce4a90c2980031b5c9521853000e573928430a6000cad72508614c001c9aa4990c298003a350932185300056ac1e4230a6000ea542084614c0015e300108c2980022fe1176945300145e422ed28a60028be84dd9514c00117b09bb2a2980263720c76545302b62e39ecaa8a6054c9c73d91514c0018becbb9aa2980a71719773545300064fb26e6a8a6000c9c64dcd514c0010fd0dbaa62980030f193754c5300043f43eca98a6056e5431d95314c00187eebb2262980030f1d7644c5302b53cc06cb2826000e3b50d92504c0ad8b8e7b2aa09800317d9773541300064e326e6a826056c5e76d96304c0adcb6c1b2c609800f179d8658c1300070e320cb1826054c9e76d92304c0131b906ba2ca180261f21d54594300061fba2a8b286009a5c83551650c0030f90ea92ca180031bdc9525943000726a9264b286000e8d424c9650c00517d0838aca180022f61071594300161f3a2a93086000c3d74552610c00195ee4a14c2180072b1c9429843000726a92653086000e8d424ca610c0131eb0f20cc2180038d551419843000c7ac3c433086000ea542886610c0070fd0fbaac218143171cf75584302872a18eeab08600087d84dd5610c0010fb05baac21814317ccb75584300051ec20eab086072c5c731d5610c0e5ca8623aac2180021fe15745843001c3e42ae8b0860098dc835d1610c0010fd0faa2c21800e1f21f54584304772a18ea8b08600087e87551610c0010f90eaa2c21800b0f9d154584300061eba2a8b08608fe5431551610c0010ff0ab92c21800e1f215725843004c6e41ae4b08600087e87d49610c0070f90fa92c218233950c752584300043f43aa4b08600087c87549610c11bca862a92c2180030fdd742584304161e3ae84b08608ae9431d09610c00187eeaa12c2182070f1d5425843000657b9284b086001cac72509610c117d2862a12c21800317dd532584303fe2e3aa64b086000ccf724c9610c001c9aa4992c218003a350932584300056a40a64b0860098f487505610c001c6aa8a0ac218026b520d415843004d6a41c42b086000ea
  | 16 => 0x5d91300061f386ebb226000c3c70dd7644c00147d0b3aec8980030f5d475d91300051f438ebb226000c3e871d7644c00147b043aec8980030fdd773d913025d5d406e7b226054e1e53d4f644c00187eebb96c8980030f1d772d91300061fc2ee5b226000c3c85dcb644c00117b0f396c8980028fa1672d91300051ec2ce5b226054a9e839cb644c00153b07396c8980032bdca72d91300051fc2ae5b226000a3c855cb644c00187eeab96c8980030f1d572d91300061fc2ae5b226000c3c855cb644c00195f04b96c8980022fa1c72d91300051f428e5b226000a3d851cb644c0a953d06396c898002a760c72d91300051f43ea5b226000a3c87d4b644c00187ee5a96c8980030f5cb52d91300045f43ca5b2260008bd8794b644c13b47b0b296c898152a7a0e52d91300054ec1ca5b226000a3e8754b644c0014790ea96c8980038be0952d91300061fb92a5b226000c3d7254b644c00117d0e296c8980022f61c52d91304e51f428a5b226054a9e8314b644c00153b06296c89800387dd732d91300070e3ae65b226000c9f72ccb644c00193ae5996c89800387d4b32d91300070ea9665b2260008be878cb644c00117b0f196c8980028fa1632d91300051ec2c65b22609ba9d838cb644c00195ee5196c8980038b54a32d913000657b9265b226000e2d524cb644c001c3eea996c898003871d532d91302a54fc1265b226054e8f824cb644c00193ee4996c898003a3dc932d913000647b9265b226000c9d724cb644c001d18e4996c89800387d4932d91300074729265b226000e1d524cb644c001d1aa4996c8980038354932d91300061fbaee3b226000a3e859c7644c00147b0b38ec8980028fe1571d91300051e42ae3b226000c3f755c7644c00153f06b8ec898152a720d71d913000557c12e3b226000aac825c7644c00117d0e28ec8980022f61c51d91300045f43e43b2260008bd87c87644c00147d0b90ec8980028f61721d91302a54f41e43b226000a9d83c87644c00195ee510ec8980022fa1c21d91300045ec3843b226000a3e85087644c00147b0a10ec898152a7a0c21d91300054ec1843b226000caf72087644c0015750010ec898002ae60021d91302a45f43ea1b2260008bd87d43644c0a917d0f906c8980022f61f20d91300051f42e41b226000a3d85c83644c0a953d07906c898002a760f20d913000657b9641b226000caf72483644c00117d0e106c89805a2f61c20d91300051f42841b226000a3d85083644c0a953d06106c898002a760c20d91300055b40841b226000ab581083644c0018f6ca382a698002ab60864d85300061fba2a9b0a6002c3c74553614c00395ce4a16c2980032b5c942d853000726a9265b0a6000e8d424cb614c0015ab0610ec298003a950821d853000578c0043b0a6000c3e74d96614c00187ce
  | 17 => 0x2a60008be871d1654c00187eea3a2ca9800a1f21d54595300061fba2a8b2a6002c3c74551654c001938e9b9aca980021fe1572595300045fc22e4b2a60028bc845c9654c0011ef02b92ca980023d205725953000c3e43aa4b2a6000c3f74549654c125878e8a92ca980031bdc952595300045f43e84b2a60028bc87d09654c00117d0ea12ca980022f21d42595300064fba664b2a6091c9c74cc9654c0031b90e992ca9800327dd132595304864e3a264b2a6000ccf724c9654c001c9aa4992ca98003a350932595300043ec24ec32a600087d829d8654c0010ff0fb20ca980030f5d364195300043ec3cc832a600087f87590654c0014bf06b20ca9800e1fa1c64195300043ec38c832a6000c3d74190654c0014dd04320ca980029b608641953000596c10c832a6000c3d87190654c001c3b06320ca980038ba0864195300051ec10c832a6000e2d82190654c00145b04320ca980030fdc864195300052f4348632a6000e1c6490c654c0014b90ca18ca98003475d143195300070e3228632a6000c3c645c8654c0010ff0fb10ca980031b5cb62195300043ec3cc432a6000a3e84988654c00147b09310ca980029760e62195300043fc3ac432a6000a3f84588654c00147908b10ca980029de0562195300053a40ac432a600387e87188654c0010fb0e310ca980028fa1062195300051ec20c432a6055a5e83188654c0018dae4310ca980028fa1b42195300051e4368432a6000c3e76d08654c0014790ca10ca980030f9d9421953000696b928432a6000e2e62508654c001c5ac4a10ca9815b179db32195300070e3266432a6000a5c864c8654c0018bcec990ca98003871913219530006a6b926432a6000e4f624c8654c001e1a84990ca980028fa1b75d91300061f3b6ebb226000a3e861d7644c00187cec3aec8980030f9db65d91300051ec16cbb2260008bd87997644c00147d0b32ec8980022fe1d65d91300051f430cbb226000c3e76197644c00147b0432ec89805aa7a1b73d91300068fbaee7b2260008be86dcb644c00187ecbb96c8980030f19772d91300061fb2ae5b226000c3c655cb644c00517f0fb16c8980032b5cb62d91300045ec3cc5b226000a3e8598b644c00147b0b316c8980032bdca62d91300045fc3ac5b226000a3f8558b644c0014790ab16c8980032bdc962d91300055bc0ac5b226000ab48158b644c02d17b0e316c8980028fa1462d91300051ec28c5b226000cad7218b644c00147d0da96c8980028f21b52d913049e1f3b6a5b226000a3e8654b644c0014790ca96c89824b0f9d952d913041e4f3b665b226000e1f65ccb644c001c38cb996c898243279d932d91300070fb2a65b226000e1c654cb644c001b1ee4996c898003a3d8932d91300074631265b226000f0d524cb644c00187ae7baec8980028f60b7
  | 18 => 0xc0010fd0fa1eca980021f61f43d95300061fba687b2a6000c3f7450f654c0010fb09b96ca980028fa1272d95300051ec24e5b2a6056a5e839cb654c0014bb07396ca980021fe1172d953000637c12e5b2a6000a3e841cb654c00147b08396ca9815a97a0c72d95300052ec18e5b2a600087e87d0b654c0010fb0fa16ca980030fdd342d95300061eba685b2a6000c3e87d0b654c00187b0fa16ca980030fdcb42d95300061eb9685b2a600087e8790b654c0010fb0f216ca9815a97a0e42d95300052ec1c85b2a6000c6d7290b654c0010fd0ea16ca980021f61d42d95300061fba285b2a6000c3d7450b654c0018dae4a16ca980030fa1d42d95300061ec3a85b2a6000e2f8250b654c00187ee4a16ca980038b9c942d95300061eb9285b2a6000e2d7250b654c00185ae4a16ca980021fa1c42d95300043ec3885b2a6056a5e8310b654c0014bb06216ca9800317dd332d95300062eba665b2a6000c5f72ccb654c0018bae5996ca9800387d0b32d95300070ea1665b2a600087e878cb654c0010fb0f196ca980028fa1232d95300051ec2465b2a6000c6f728cb654c001c5a85196ca980031bdc932d953000716a1265b2a6000c5f744cb654c0018bae8996ca9815b93e0932d95300062fb9265b2a6000e4f724cb654c00189ee4996ca98003175c932d95300072639265b2a6000e1f424cb654c001c9c84996ca980038750932d953000726a1265b2a6000e0d424cb654c0014bb07b8eca980028fa1271d95300051ec24e3b2a600087e87d07654c0010fb0fa0eca980030fdd341d95302b52f41e83b2a6000a5d83d07654c0014dd05a0eca980029b60b41d95300061fba283b2a600087e87107654c0010fb0e20eca980021fa1f21d95300043ec3e43b2a6000a3e84c87654c00147b0990eca9815a97a0f21d95300052ec1e43b2a6000e2d42887654c0010fd0e10eca980021f61c21d95300051f42043b2a6000a3d84087654c0ad4bd0610eca980029760c21d953000716a1043b2a6000a7a80087654c0014f30010eca980028fe1170d95300051e422e1b2a605687e87d03654c0010fb0fa06ca980021fa1c40d95300bc3ec3881b2a6056a5e83103654c0014bb06206ca980029ba0840d953000536c1081b2a6000a7681103654c0014eb02206ca9815a1fa1f20d95300043ec3e41b2a6000a3e84c83654c00147b09906ca9815a97a0f20d95300052ec1e41b2a6000e2d42c83654c001c5a84906ca980021fa1c20d95300bc3ec3841b2a6000a3e84083654c00147b08106ca9815a97a0c20d95300052ec1841b2a6000a7681083654c0014eb02106ca980030f197745953000556c10c8b2a60028be87dd1654c00187eebba2ca980030fe1774595300061e42ee8b2a60008bd82dd1654c00187ea5ba2ca980021fe1574595300046fc1ae8b
  | 19 => 0x32b5c942d963000c6fc3a65b2c6000ccd724cb658c001c9aa4996cb18003a350932d96300066ab9ce3b2c6000c77549c7658c0018eaa938ecb180031d94e71d96300063a29ce3b2c6000c77529c7658c0018eaa538ecb180032dd0a71d96300065aa14e3b2c6000cd7329c7658c0019aa6538ecb180031dd5171d96300063aaa2e3b2c6000c77525c7658c0018eaa4b8ecb180032dd0971d96300065aa12e3b2c6000cd7325c7658c0019aa64b8ecb180029da0775596300143e43aa8b2c6000c3f74551658c005878e8aa2cb1800297e0d545963000c3e43aa4b2c6000c6f72549658c00199ae4992cb1800393549325963000746a1264b2c6000a7685d86618c00587ce8aa4c3180030f5d1549863000657b928530c6001cac7250a618c001c9aa4994c318003a350932986300055ac20a330c60028f587906618c001c6aa8a0cc3180063d61e219863000752a144330c6000c3f74551618c005878e8aa2c3180031bdc9525863000e36392a4b0c6000caf72509618c003958e4a12c31800333dcb325863000726a9264b0c6000e8d424c9618c0015ab07a8ac318002ad61051586300147a43a82b0c6000e3554505618c001d4a8510ac3180063d21d21586300047bc3ac230c6000c7475985318c0018e8eab0a631802736981760c6300062eb2ae72846000aad82193654c00187ea9ba6ca980030f5d254d95300052ec1ca9b2a600287f87553654c00187ae8aa6ca980028fa1252d95300051ec24a5b2a6000a5d8394b654c0030ff0ea96ca980031b5c952d953000e5739285b2a6000cad7250b654c00199ee4996ca980039394932d953000726a9265b2a6000e8d424cb654c00517d0938eca980022f61271d95300061eba6c9b2a601787d87193654c00187ae8326ca980029ba0864d953000536c10c9b2a6000b2d82193654c00187b0e326ca980038760c64d953000717410c9b2a6000a3d82193654c001c5b04326ca980028b60864d95300070e32487b2a6000d1f7450f654c001c38c8a1eca980030f19372d95300061e322e5b2a6000c6d72d8b654c00147d09316ca980028f61262d95300051fc22c5b2a6000a3c8458b654c0014ef02b16ca980029d20562d95300bc3ec38c5b2a6000a3e8418b654c00147b08316ca980031b5c862d95300051f43685b2a6000a3c86d0b654c10587ceda16ca980028f21942d953040e1f3b285b2a6000d2d7250b654c001c5cc4a16ca980038b58942d95300070e32665b2a607fc5e764cb654c001c38c8996ca9800353dc932d953000727b1265b2a6000e4c624cb654c001e1a84996ca980021f60b74d95300061fc22e9b2a600087f825d3654c00187ae83a6ca9815a97a0c74d95300052ec18e9b2a6000a6e821d3654c0014db043a6ca980029da0773d95300053ac0ee7b2a6056c5c735cf654
  | 20 => 0x6c41c40b0062018f887481600c4135b106902c018803aa50920580310057840a40b006200ad681d8e639400187ea9ba2c7280030f5d15458e500146e43a86b1ca000a5f8550d6394005938e8a1ac728003875514358e5000636b92a4b1ca001cae72509639400195ae4a12c7280063721d3258e500052fc2a64b1ca000ccf724c96394001c9aa4992c728003a35093258e500046fc3ac631ca056a5f8758e53940018bf0eb1ca72815b17dd16394e500062eba2c729ca000a5f8258e53940014bb04b1ca72815b17dc96394e500062eb92c729ca000e1f4258e5394001c3a84b1ca7281561fe197094e500049fc22e129ca01c97b865c253940ab8f70cb84a7280034ee117094e500069c422e129ca000d3b425c25394001a7284b84a72815b56cc97094e50006ac992e129ca000ad683d86619400587ce8aa4c3280030f5d1549865000657b928530ca001cac7250a6194001c9aa4994c328003a350932986500147ac3c8330ca000e355450661940031eb0f10cc328003a950a21986500061faa6e8b0ca000c3d7455161940018dea5b92c3280032bdc9425865000e5639284b0ca000ccf724c96194003998e4992c32800393549325865000746a1264b0ca0028f4875056194001c6aa8a0ac328003a950a215865000c7a43a42b0ca0008f787584619401d0ff0eb0ca3280421fe1970946500049fc22e128ca000c7575587319400517d09bb463280022f613768c6500062ebaac718ca09ee545398431940131f30d380632800e5e215700c6500061fba2a9b1aa002c3c7455363540014bb0ba1ec6a80038755343d8d500052ec2887b1aa000acd8210f63540018dee4a96c6a800637e1d32d8d5000666b9265b1aa000e4d524cb6354001d1a84996c6a800237e1d6318d500054e422c631aa000c3f745536154005878e8aa6c2a80072b9c942d855000656b9285b0aa000e4d524cb6154001d1a84996c2a80023de1d61185500161f3a2a830aa000c3d74550615400399ce4990c2a8003335c9321855000726a926430aa000e8d424c861540070f90a3b262a80022fe11760c5500145e422ec18aa0098f8865c031540139b0c6b8062a80261f21d54597300061fba2a8b2e600187c8754965cc0018dee4a92cb9800393549325973000746a1264b2e6002c3e7455261cc00187ae8aa4c39800b279d143987300070eaa28730e6000caf7250a61cc003958e4a14c398003335c9329873000726a926530e6000e8d424ca61cc00587ce8aa2c3980030f5d1545873000657b9284b0e6001cac7250961cc001c9aa4992c398003a350932587300063b32ce3b2c60008f681dd3658c0011eb03ba6cb1800a1fe1d54d96300061eba2a9b2c6056a5c83553658c0011ed03b96cb180023d60772d963000c3fc3aa5b2c6000c6d7254b658c00395ce4a16cb180
  | 21 => 0x87195604c40147b0832ac0988030f1d0655813100636390cab026200c3f65dd1604c401878cbba2c0988031bd9772581310063632ee4b026200a3d84194604c4011f70eb00c09880b0f9d154181310061eba2a83026201c6e72548604c4018dae4a90c0988072b9c9421813100656b92843026200e4d524c8604c401d1a84990c098802b5205321813104c6e41ae8b28620987c87551650c40187ee8aa2ca188269720d545943147e2e39aa8b2862098dc83dc9650c4131b906b92ca188023d205725943100c3e43aa4b28628dc5c73549650c4018dee4a92ca18a2b271cf425943145e4e39a84b2862238dc874c9650c401c9aa4992ca18803a350932594312852e41acb2886200c5f54dd9310c4018baa9bb2621880237e0b764c4310046ec16ec9886200c5f52dd9310c4018baa5bb2621880327d0b764c4310064ea16ec988627295e87dd5310c4018beedbaa621880317dd8754c4310058ec20ea9886200cd776945310c447aa8eb28a62188267521d514c4310066bbb2a29886200c3f74552600c405878e8aa4c0188072b9c9429803100656b92853006200e4d524ca600c401d1a84994c0188263e61e40980310071caa48130062018f987882600c401d5284904c01880e1fa1f75580312b62e39eeab006256e5830dd5600c4010fb09baac0188021f60b75580312b62f996eab006255c5c731d5600c4abcb0603aac01880a2fa1f74580310061fbaee8b006200c3c75dd1600c4a9938e7ba2c018953a60c374580310061fc2ee8b006200c3c85dd1600c40117b05ba2c01895327ccb74580310043fc2ae8b00620387c855d1600c40187eea3a2c0188030f1d4745803141e4e398e8b006200aad821d1600c507d30603a2c0188021fa1f545803101c3e43ea8b006200c3f74d51600c405878e9aa2c018a3b960c354580310043f43aa8b00620087c87551600c40187ee8aa2c01880b0f1d1545803147f2c182a8b006202c9c7450d600c401c3aa8a1ac018802b620143580310043fc2ae4b00620387c855c9600c40117f08b92c01880a2f21172580310043f43ea4b00620387c87d49600c40187ee9a92c018a4f0f1d352580314672c186a4b00620087e87549600c4010f90ea92c0188030fdd152580314961e3a2a4b00628de5830549600c40117d0fa12c01880a2f21f42580310061fbae84b006282c3c75d09600c515d3061a12c0188022fa1d42580310045e43a84b006200c3f75509600c503878eaa12c0188072b9c9425803100656b9284b00628be9830509600c4018beea992c0189ff171d532580310064fba264b006290c9c744c9600c40199ee4992c01880393549325803100746a1264b006200ad8804c9600c405970e9202c0188038e552405803104d6c41c80b006254e9a43901600c4131f10ea02c018826b620d405803104d
  | 22 => 0x10eca988029760c21d953100716a1043b2a6200a7a80087654c4014f30010eca988028fe1170d95310051e422e1b2a620087e87d03654c4010fb0fa06ca988030fdd240d95310043f43881b2a620087d87103654c40187ee8206ca9894297a0c40d95310052ec1881b2a6200a6e82103654c4014db04206ca988029da0440d95310053ac0881b2a620087e87c83654c4010fb0f906ca988028fa1320d95310051ec2641b2a6250a5e83c83654c4014bb07906ca988038b50b20d953100716a1241b2a620087e87083654c4010fb0e106ca988028fa1020d95310051ec2041b2a6250a5e83083654c4014bb06106ca988029da0420d95310053ac0841b2a620087f855d1654c4011bf06ba2ca9880a1f21d54595310061fba2a8b2a6229c5f73551654c4010ff0ab92ca9880237e0d72595310047bc0ae4b2a620187c87549654c4538bee6a92ca988031bdc952595315064fb9e84b2a629fc9f73509654c40195ee4a12ca988072b1c942595310046f43e64b2a62008de874c9654c4031b90e992ca9880333dc9325953100726a9264b2a6200e8d424c9654c4010fb093b0ca988021f60a761953114e2fb1ae832a6200c3e865d0654c4018790cba0ca988a70fd8d741953114e0fb1ae832a620093f825d0654c45987ec2ba0ca988034dcc574195310069a18ae832a620087f87d90654c40187ae9b20ca988021f61e64195310061eba4c832a6200a5d83990654c4014dd05320ca988029b60a64195310043fc3ac832a6200c3d74590654c4014bf06b20ca9880e1fa1c64195310043ec38c832a6200c3d74190654c4538bec6b90ca988021fe1f62195310061eba6c432a6200c6d72d88654c4010fb0f310ca988028fa1262195310051ec24c432a6200c3d74988654c4014bb07310ca988021fe1d62195310061eba2c432a6200a5f83588654c4014ef02b10ca9880e1fa1c62195310043ec38c432a6200a3e84188654c40147b08310ca988030f5d062195313952f418c432a6200c6d72188654c40127b0fa10ca988030f9db42195315070fb1e8432a620093d87508654c40187ceca10ca98a7f87d8d421953100717b128432a6200e2c62508654c4014bd0d990ca98943179db32195310068eba66432a6200a5e864c8654c4014b90c990ca98803179d932195310068eba26432a6200d4d724c8654c401c9ec4990ca98803c35093219531005aa40a6432a6200c77651c5534c4a14eb03b2ca298943171cf65545310062fb2ee6a8a6229c5c65dcd514c4534bd0db2c629894395d87658c5310058ec20cb18a6200a3d84197604c40587ce8aa6c0988030f5d154d813100657b9285b026201cac7250b604c401c9aa4996c098803a350932d81310051ec20cb302625087c86dd5604c4010fd0fb2ac0988030f1d3655813100636396cab02620087e
  | 23 => 0x5823100746a1264b0462018f887481608c401d5284902c1188023ee1d60182310061eba4a9b2a620287f87553654c40587ce8aa6ca988030f5d154d95310051f424a5b2a6200a3d8494b654c4014bb07296ca988061fe1d52d953100636b92a5b2a6200ccf724cb654c401c9ca4996ca988039354932d953100746a1265b2a62008bf845c3654c40517908b86ca988030f5d364d95310061fba4c9b2a6200a6e82993654c4014db05326ca988030fdd164d953113c3ec38c9b2a6200c3d74193654c4018dae5b16ca988028fa1262d95310051ec24c5b2a622787d8718b654c40147d08316ca988028f61062d953100636b90c5b2a6282c3e76d0b654c50387ceca16ca988038bd8942d95310071631285b2a627fc5e764cb654c401a9ee4996ca9880393d8932d95310072631265b2a6200f0d424cb654c4016a902996ca988021f60b74d95310061fba4e9b2a6200c3f845d3654c4010ff04ba6ca988030f5d074d95312862e39ae7b2a620087e87d0f654c4010fb0fa1eca988030fdd343d95310061fba287b2a6250e1c4350f654c4010fb09b96ca988028fa1272d95310051ec24e5b2a6250a5e839cb654c4014bb07396ca988021fe1172d953100637c12e5b2a6200a3e841cb654c40147b08396ca9894297a0c72d95310052ec18e5b2a620087e87d0b654c4010fb0fa16ca988030fdd342d95310061eba685b2a6200c3e87d0b654c40187b0fa16ca988030fdcb42d95310061eb9685b2a620087e8790b654c4010fb0f216ca9894297a0e42d95310052ec1c85b2a620087e8750b654c4010fb0ea16ca988030fdd142d95310061eba285b2a6200c3e8750b654c40187b0ea16ca988038be0942d95310061fb9285b2a6200c3d7250b654c4010fd0e216ca988021f61c42d95312852f41885b2a6200a5d8310b654c4018bee9996ca98803175d332d95310062fb9665b2a6200c5d72ccb654c401c3e85996ca988038750b32d95310043f43c65b2a620087d878cb654c40147d09196ca988028f61232d953100637b9465b2a6200e2d428cb654c4018dee4996ca988038b50932d95310062fba265b2a6200c5d744cb654c4a1c9f04996ca9880317dc932d953100727b9265b2a6200c4f724cb654c4018bae4996ca98803931c932d95310070fa1265b2a6200e4e424cb654c401c3a84996ca988039350932d953100706a1265b2a625087e87d07654c4010fb0fa0eca988030fdd341d95312852f41e83b2a6200a5d83d07654c4014dd05a0eca988029b60b41d95310061fba283b2a620087e87107654c44f0fb0e20eca989421fa1f21d95310043ec3e43b2a6200a3e84c87654c40147b0990eca9894297a0f21d95310052ec1e43b2a6200e2d42887654c4010fd0e10eca9889e1f61c21d95310051f42043b2a6200a3d84087654c4a14bd06
  | 24 => 0xaa2008dd8710063544474bd0a200c6a8802976144018d510070eaa08031aa200ace82100635440159b04200c6a8802b5a044018d510056ac088031aa2098de87c8063544011bb0f900c6a888e97a172018d510052ec2e4031aa200a9e84c80635440153b09900c6a8803335cb2018d5100746a164031aa200ccd724806354401d1a84900c6a882637a1c2018d510046ec384031aa223a5e8508063544014bb0a100c6a8802a7a102018d510054ec204031aa200ad68108063544015ab02100c6a88a795d8763945510062fba0c728aa200c5d7418e51544a14bf0431ca2a88029760863945510062fb90c728aa200c5d7218e5154401c3e8431ca2a88038750863945513962f388c728aa223e567118e515440587ce8aa6c0a88030f5d154d815100657b9285b02a201cac7250b6054401c9aa4996c0a8803a350932d81514266ab88c7302a2008de87d8d605440193ee9b1ac0a8803271d3635815100666396c6b02a2008de8718d605440193ee831ac0a8803271d0635815100666390c6b02a200ccf63dc96054401998c7b92c0a88023ee1d60181510061fba2a8302a201cae72508605440195ae4a10c0a8807339c9321815100666b9264302a200e4d524c86054401d1a84990c0a88261f21d54597310061fba2a8b2e620187c8754965cc4018dee4a92cb988029de05525973100726a9264b2e6200e8d424c965cc40517d09b82cb988022f613705973104e2e39acaa8e6200c3f7455260cc405878e8aa4c1988072b9c9429833100656b92853066200ccd724ca60cc401c9aa4994c198803a350932983310061fba2a8b066202c3c7455160cc40395ce4a12c1988032b5c9425833100726a9264b066200e8d424c960cc4011f501ba6cb188023e60374d96310143fc3aa9b2c6202c3e74553658c40187ae8aa6cb189429720d54d963100c3fc3aa5b2c6200c6d7254b658c4031bf0e996cb18803335c932d963100726a9265b2c6200e8d424cb658c4050f90eaa2cb188030fdd154596310052fc1aa8b2c6200c5f53dc9658c4018bea6b92cb188061f21d52596310052fc1aa4b2c6200c6f72549658c541c3ea7a12cb18a7f87d4d425963100657b9284b2c6201cac72509658c4531bd0f992cb188a697a17325963114d2f42a64b2c6200ccd724c9658c401c9aa4992cb18803a350932596310145f426e0b2c62008bd84dc1658c4538bee6b2aa7189cb5514c7154e310062eb2ae728c6250d5475947318c4533af0ea8e63188030fdd154982310161e3a2a93046201cae7250a608c40195ae4a14c11880393549329823100746a126530462018f987882608c401d5284904c1188030fdd154582310161e3a2a8b046200e1d5450d608c4018dee4a92c1188071b1c9525823100657b9284b046201cac72509608c40199ee5992c1188039354932
  | 25 => 0x4015ad02206c6a8802b560440d8d510046f43e41b1aa2008dd87c8363544534bd0b906c6a88029761720d8d510054f42641b1aa200a9d84c836354401d1a85906c6a8803a350920d8d510046f43841b1aa2008dd8708363544534bd0a106c6a88029761420d8d510054f42041b1aa200a9d8408363544015ad02106c6a8802b560420d8d510046fc3ac631aa2008dd87990635440159d05320c6a8802b360a6418d510046fc3ac831aa200e1f6455063544011bd0db90c6a8803335cb6218d510046ec3cc431aa200a9e84988635440153b09310c6a880237e1d6218d5151d6bc0ac431aa2008dd87188635440153d08310c6a8802a76106218d5100666b90c431aa200d4d725486354401c9ec4a90c6a8803635c94218d5100747b128431aa200e8c62508635451d4bf08aa0c6a888f87e115418d5147f0f3a2a831aa28fe1d7455063544014bf04aa0c6a8a3f17dc95418d510052e40aa831aa200c5f545c863544018baa8b90c6a882733e097218d510062fa92e431aa200cce525c8635440199aa4b90c6a8803171457218d510052fc22a431aa28ca5f825486354447c9f04a90c6a8a3717dc95218d5146f27392a431aa200c5d72548635451bc9ae4a90c6a8803135c95218d510072bc0aa431aa200a5c815486354401ca902a90c6a888e97a174218d510052ec2e8431aa2a2e1f54d086354401c3aa9a10c6a8a8b87a174218d510070ec2e8431aa28ac9f72d08635440193ae5a10c6a8a8b87d4b4218d510070ea968431aa2a2e1c51d0863544131bd0f210c6a88023761e4218d5111d2f42c8431aa200a5d85908635440199ae5210c6a888e97a154218d510052ec2a8431aa2a1e1f545086354401c3aa8a10c6a8803335c94218d5150f0f42a8431aa200e1d855086354401d1f04a10c6a8a2f27dc94218d5145f473928431aa200c9d725086354517d1ae4a10c6a8803235c94218d5150f0fa928431aa200e1d525086354543c38a2a10c6a882637a1c4218d510046ec388431aa223a5e8510863544014bb0a210c6a882637a1f4118d510046ec3e8231aa223a5e85d0463544014bb0ba08c6a8803875534118d51005674168231aa200acd82d0463544474b90b208c6a880297e154118d5111d2e42a8231aa200e1d5450463544474bd0a208c6a8802976144118d5104c6f43e4231aa2008dd87c8463544474bd0b908c6a8802976172118d510054f4264231aa200a9d84c8463544474b90b108c6a8803335ca2118d5100746a144231aa200a5f8548463544474b90a908c6a882637a1c2118d510046ec384231aa223a5e8508463544014bb0a108c6a8802a7a102118d510054ec204231aa200ccd720846354401d1a84108c6a8802b6a002118d510056cc004231aa223a5e85d0063544014bb0ba00c6a8803875524018d5104c6f4388031
  | 26 => 0x29761632d8d510054f42465b1aa200a9d848cb6354401c9aa5196c6a8803a350a32d8d5100c6fc3a65b1aa200ccd724cb6354401c9aa4996c6a8803a350932d8d510052ec2865b1aa200a9e840cb635440153b08196c6a8802b3a0a64d8d5100566c14c9b1aa200e1f645536354401c38c8aa6c6a8803335cb62d8d510054f424c5b1aa200a9d8498b635440153d08316c6a8802a761062d8d5100666b90c5b1aa200d4f7254b6354401c9ec4a96c6a88039318952d8d51006c7b9285b1aa200e8f6250b6354401d18c4a16c6a88a697a1674d8d510052ec2ce9b1aa200c9f749d3635440159d053a6c6a8802b360a74d8d5114d2f428e9b1aa200a5d851d363544534bf08aa6c6a88a787e1154d8d510070fba2a9b1aa200e1c7455363544014bf04aa6c6a880317d5372d8d510062eaa6e5b1aa200c5f52dcb635440199ca5b96c6a88033354b72d8d510046ec3ce5b1aa229a5e859cb63544014bb0b396c6a8802a7a1272d8d510054ec24e5b1aa200c5f545cb63544018baa8b96c6a880333e0972d8d510062fa92e5b1aa229a5e851cb63544014bb0a396c6a8802a7a1072d8d510054ec20e5b1aa200a5f8454b63544534bf04a96c6a88a793e0952d8d510062fb92a5b1aa200e4f7254b635440189ee4a96c6a8803175c952d8d5100726392a5b1aa229a5e85d0b63544014bb0ba16c6a8a8387d5342d8d510070eaa685b1aa2a0e1e85d0b6354401c3b0ba16c6a880327dcb42d8d510064eb9685b1aa2a0e1f52d0b6354401c3aa5a16c6a880237a1e42d8d510046ec3c85b1aa229a5e8590b63544014bb0b216c6a880333dca42d8d5114d2f42a85b1aa200a5d8550b635453fc3ea8a16c6a88038755142d8d5100667b9285b1aa29fe1e8550b6354401c3b0aa16c6a8803a3e0942d8d510064fb9285b1aa200e8f7250b635440191ee4a16c6a8803275c942d8d510074639285b1aa29fe1f5250b6354401c3aa4a16c6a880237a1c42d8d510046ec3885b1aa229a5e8510b63544014bb0a216c6a88a637a1f41d8d510046ec3e83b1aa229a5e85d0763544014bb0ba0ec6a88038755341d8d510056741683b1aa200acd82d076354401c3aa8a0ec6a88a697a1441d8d510052ec2883b1aa2298de87c8763544011bb0f90ec6a88a697a1721d8d510052ec2e43b1aa200a9e84c87635440153b0990ec6a8803a350a21d8d510046f43843b1aa2008dd8708763544534bd0a10ec6a88029761421d8d510054f42043b1aa200a9d840876354401d1a8410ec6a8802b6a0021d8d510056cc0043b1aa200a5d85dc3635440153d09b86c6a8802a761370d8d5114d2f42e81b1aa200a5d85d036354401c3aa9206c6a880237a1c40d8d510046ec3881b1aa229a5e8510363544014bb0a206c6a88038755040d8d510056741081b1aa200acd821036354
  | 27 => 0x6b9285304a600ccd724ca6094c01c9aa4994c129803a350932982530063a28ae3304a600c3f54dd16094c0517d0fba2c1298030fe1774582530061e42ee8b04a6008bd82dd16094c0187ea5ba2c12995327ccb74582530061e286e8b04a600aad821d16094c0187ee8aa2c12980b0f1d154582530045fc22e4b04a6028bc845c96094c0187ee8a92c129a4b0f1d152582530045f43e84b04a6028bc87d096094c0117d0ea12c1298022f21d425825300e5739284b04a600cad725096094c0193ee8992c129a43271d1325825300667b9264b04a600e4d524c96094c01d1a84992c1298030fdd154d855300e5739285b0aa600cad7250b6154c01c9aa4996c2a9803a350932d85530053ac2843b0aa600ad5830876154c01d4a8410ec2a9802bc60021d85530047bc3ac230aa6a4ad7835846154c0587ce8aa0c2a98030f5d154185533952e41aa830aa600e4d524c86154c01d1a84990c2a98029d61721185530056ac1e4230aa600ea5420846154c015e300108c2a98022fe1170185530145e422e030aa602c3e745536054c0187ae8aa6c0a98039354932d815300746a1265b02a6008fb875806054c0187ee8aa0c0a99569720d541815300e5739284302a600cad725086054c01c9aa4990c0a9803a350932181530161f3a2a8b1ca200c3d7455163944018dae4a92c7288063721d3258e510052fc2a64b1ca200ccf724c96394401c9aa4992c728803a35093258e510046fc3ac631ca22995f8758e53944a14bf0eb1ca72880317e1d6394e510052fc12c729ca200a5d8258e53944a18bee4b1ca728803175c96394e510070fa12c729ca200e1d4258e53944e50ff0cb8ca7288b25de197194e513963bc32e329ca200d37425c65394401a6a84b8ca72894355cc97194e51006aa992e329ca200c3f745526094405878e8aa4c1288031714d739825100e5739285304a200cad7250a6094401c9aa4994c128803a3509329825100c7cc3c41304a200ea942482609440187ea9ba2c12880a2fa1f74582510061fc2ee8b04a200c3c85dd1609440117b05ba2c1288030fd4b74582510061e286e8b04a200c3f745516094405878e8aa2c1288031bd4b72582510045fc22e4b04a2028bc845c9609440187ee8a92c128a4b0f1d152582510045f43e84b04a2028bc87d09609440117d0ea12c1288022f21d42582510064fba664b04a291c9c74cc9609440193ee8992c128a43271d1325825100667b9264b04a201ccc724c96094401c9aa4992c128803a3509325825100c7c43a40b04a200ea94248160944011f70eb00c1288030fdd154d8d510052ec2e87b1aa200e1d54d0f63544051bf0ea1ec6a880b279d143d8d510070eaa287b1aa200a5d8510f635440159d0421ec6a8802b360843d8d5100637b92a5b1aa200caf7250b6354403958e4a16c6a880
  | 28 => 0x5000801f000008c00200600d80180080010018000002000000801c01a00900700000140040020034000000000801009401a012001000401e001003003000000080340060040028014004007000802c00200100000280060060000018000012001001801e00b010800001401d0058068008000002800c01800a000004400800c0018038040004001003403a038000000000401c006000001600200300cc00404a00081b000c00500080000000050050004026012003802000800200100040000150018014002002000000c0020400028008002000002802c00a00700200040180000100000008000005802400a0020000034016000000000c002004008800c0040030038024000038000000c0a0010001800002400400a8004000001006006c056008003003c072000003003000400200e801407e02201880000060040000000008005002800c002001001000c00000d008000402c0140018000008009000000c01a00000180000060d3001000001a000000000001200200200080120030188020000000003804c004001000800800402e001801c00e01400480000000000010000084054005800800c001000000400a0050038000008001002002c0020010000000000016005800c00800100a80ac02600000a000001a000001005800200f001000008602b014003401201b0000000012018002000000001d00680700040090018004000006000000000400e000000c00a017000001400e016000004c0360100000000006008000000007e00e00e800002c019001000800c00000601d404e00700080040020000008034024000000000003400300600580000010010020000009000004c010000015801c000004000806801c02501780180000000090000012001000000803e000001801400e000002802c0000110138000004009000802c01000000200c400001f003800000c009027000000a00f01d801800e003006011401600d0018014010003000800802401b000800400202300100000100080010000000002003000000200000400000280000000014060000005802007c001004812400800000000000080000180014000000003800c000000000000401c01e007800400001300c000000401000180540440080008004018000000000000000400680040100000038024000002000800001e010001804c000000001801c00000000000040120390028038006004000000000001000a0000006022011001400200500000b0f9d154986530061eba2a930ca600caf7250a6194c03958e4a14c329803335c9329865300726a926530ca600e8d424ca6194c0587ce8aa2c3298030f5d1545865300657b9284b0ca601cac725096194c0199ee4992c32980393549325865300746a1264b0ca600c3f745526094c05878e8aa4c1298072b9c942982530065
  | 29 => 0x180040044028001002006c00400001400000220120000028002000002804001600a0028004000014002800c00801e0030020012004000002403800b004804000e03a001001000400e000000000000300000d8004000007001000200a00100000040010010000014081006000400a036006001000001400c80200000020008010022009000000004e000000000003405400280580040000120030000005002000400600500c804400a09e008001c008016000801800a005000005000a00100b0000012005002800000c0000008050000012001000c032000001808c002001004800004c00100a001400e000009000002e03a00800080000000038014000019007005c01e000002802400005b000000005a000000000000a00a000001001800a001803401000401e8034000001006000c004002001000400402300200c000c00000000280120000000000002000000003c00200b008000400a00801d803800c001000807c00800600301080020000000028020002000000c004007001001401e0000008058002002010802402a004001002c016012000000c0180010008008032000000000401c01c00f806c00000b000817000e00b0008000004006004803400a000007000c04800b003001c0000030000018004001022001c006016004001c00c0110038018000001005000c00c000000000403000f0010024018045004001400a000000801001e00100100b403e005000007400e007002006409c00a000001400e0000018008028002004004402600000780300120170058004002006004800001801400080080000000090008004006000800000001900e801c02200100a0038000020005801400600c002000000e00600100380060080028004028000002000000000001f8000006001015800000200d00080180020000048004002001000813006e0040018000004000003808000202c001802c024003002001400c03e01d8000002044010800802600300b007000000000b80a0006009015800001a000001000000800201000100040030068020062000002007802e00700c80000c00010010154000011008001403406e000802000c005001804c006000000802800400b00a0000010004008000400a000005803c00a00f0008008004057007801c000004000000800800800d8088000002000000802c000002800000200400f8004000010002000c0000020038020000004001000400000300301c800401600000340020010088010000002000001c000000003800400600d027001000200d002802c0240020030000004010003000000c000002806401600000600280780000010000044000000002000200000d000000e001000003400200200f00ac00a012000000c00200500f000003401c001800c0120000000000002001003800c0020000038
  | 30 => 0xdd20a158880000000542e002f4000b195810a517b460404700f00646e543b220d45422e13e36ac3dcf2e28f00012c2b4665512a432600036537d45d614e195215006e2141a700012743c33d8a9d400006f4b423ccc4e6681488000a3400000000d5a5200000003c942c0003219b8072400060d9431a3c00015f800187e00079b0598000e6f06a1eecc061737602248000000000260c0000000002130f4a00000019d98ca60f0928000da62f1000000168e8aa00020d00006726be00000000006ec2659e6687222d8df08d8ce676babb5c8c583172056164c4a03a736c481e0000002ebce3cefa380b33185e3b91392d9c8fa0003cfaac5576000000000000000000000009046c20a4836c0000000000000c526f632d8000000e176ca23443ac7685bfacac0bee180000000000757000282493e00046d985d74aea81962b7c13c0e909a1d2889e0000510729176199000000102651b1aa0000fee000546a774a2200036f88540006c13f69165b7ecd374c0c74000000373392c4406a20e306f4022432735bc9c6ccd8623f81e00008d204d1d0495477a789019cce20004d7a2755e40002e4bc3000061637180017fe69f04800010740006d29f884a203e3ec0fd0adad451f48001b100001029891e3ed4200009817ba00044992b5456000536208036800000038c4000b200cab3e5d5cbbc6c9800186eef200006ac000c0258195990340000000308b566ed553000000041d31197a0b3cc894e3800000098725ea8c84e81e9345b0d4000f195f09b794f29f5184bc10000219000000000056550839340383480000000c92bf02c7a5ad8520004a8a07000071370e3be40000000001f300000004f29570e326862160079cdc0001adb465254b1e07e000077083c0002b9c0000003230000fa6000674a208d3a00068b8000298be72b50ac5e5a1e500011c81d084663189a9e76d163338708d6a2a85cc04795108e64462808d301811f1af893fee250f82500db2b370449180572906109b00400002244f24b858c0004aa8be49e4ec416ab5c16ac50a7171ff14ae0003fb22e0000738000052d60800059ea090e1226c61d0000cd44270530a1c600d7e248035d6e045a0c91ddd0c628941f21715862e133fa2d5e6eaf014d08dc06676f0a03bdcaa00030020040008002800400c00a000000405600201b0034006001000800c00200001300180ee000003800c000045004000406200000780940000010010010026000001001c02c0020108018006035000000c00a001000012400806c00080700100000000000002001002001c00202a00b00000040070000024002001000001401600c002000800e030006801c01800e00000280000020070008048002000000001400001c803000000001b8004020001000001401404a000000005c00000200080b0
  | 31 => 0x2e24c335919b8752b853ef8eb4d088576d00021d4687402d38e8fccc2a4ee256535453f280245cd924736951d914ac6882142a2859463f0a0a25c1f459b778ac59250add0c62860ed645429c28807b460905f009d3f87a76fe126d90e91e61235c57b6a3c27a075439c8310afb3e02bc07c75389410dcb1819f92e801cd1d224156034c91962a0001a100522a48134cf23e854f32604c6023525040ce5e1ba0000000000af40002d48bbe00000032557040005c480016b40001749fe035ed003d0b659d1093531131b935680f48a9dd827a59c253a53c3b022c2e68200956a4619401812764412e9af006da53139fb095946c55678bca100e45220aa590092d9f4b800009fa08f294adf40006fc729830d8e8c920ae244056ebb8420319d0165ed2b0a5810f8f070572e703c08ca3e20000b2840e1bb8a60578d9511e0001bd8b570e9b60d9a20004df00015d48c700000640008950b180007f60005502ed487822b12087f4ffc8a25262f91e2af100000d2c7fcd6a25a0bb0000a4926e0000000c2d3c487700006450001c3d2363d9609afa0f5a000000000060e2a344235d1110c4527d0000000bee03293dc0000002ef2aa8b584ff21a369c0009040003979d12786319ac1d5fc5084708998000232211095525218e101ad6d714150300206c9f0563665a494ef88c4790b075a16000161046dd1e00003d8e8520ebab727966579c6cd6408000dba00045f06b8090466769372403ae9c52e9deca9a3854090bc800059d47280000000003162160894082645bb4c000b7b57ca4990f47511fc8b4dd3ca13332b6447da4ec64c9255a58adc1ec0a48fe837f01407b00003ba6ae00013f680c3dfb0a17404da7769aa502ec7c3f7a1209a2eb467a83d91d02a0297966188847e000354c69269b5c68000b344710be911c262e9941a9e88a6c0004a23a95d966c809d2e85328bea300907c1d41b240f9e340000002f519390763021f131006ca00000004449348590001f2d394d593550e512c40005eb3920dd8c2c705800053a05b0e23a8572c48f1450000c3a00000020001184e858700004d2c232d4000131e0004862da40007921a30c342701d40dc8001050e944e92f258dee8a2c334f9b96631481377977a2e8683a9ccf4c0000001c48b6a0306522714daa57917d9339aa4acf13737a05025b36890001668000343aab80000000003b284ec258000164c63408123b0000aac3bb129b1a8f32d0a3a5800162699e6f30c940000006090001196ab8094000000065d768a01534200000000000000001e500015ac6b300001b40000860ad17e800009133a842998651d79c36e969eb81196800102ccf72b71e90870000662a3756940eb190bab1b204fc1b139303f297700000018b43ab00000000000006edbcf40000000000000566020396971914a000
  | 32 => 0xc00626d1c0834d5aa1d103d62390332bbc6e804a466038d45e85a2bd3349112dfa2428e251da5ba0000000000050698000000000000000001e6a2242700000001f42e18091816c4635b179839282678b2c2533a99f4ebb6c08d21720000000000e13104a52c2dc3315c407354140b1403349800095e16e0675114bf5000000136a743000000158e00013c205458e5c100000014aa86c4ed21ed1a82de66532e9c566443afaa8ccf8df65a1bba5cbea1d69f90dc000a306f01d64fc67600001bfc0000006b0abc47181c80003868f66e1d0003aadcd00005088c181503b26d780015f00000c227bdb86338000031c0009df1429dfc95c2fd23cb57d6440002f62b259b600000028d80000000000fbd4b097e18504b8c64de32a91490526a3d214b94819cb8f29088846e066353280012ea0000002cfdc04a376889511e3a49c0179ccd6a089c592093879a404529b0412b68694d9b140000aec0000ab1b02000096ab9000007d21f890191a0007498000f8e7b24c5b845bfead1309327cbeae7850696c86c64926a580015282f054b2e7879000000026c947c0004f81788ea600000000006d400054229ac53e20d44c95e08189d60000edc0881610000001500000293ae6c90e65f6dc0ed50de96c0000e4d7f07e904facbc52a4431840e356ecbae3f9824c7cce470c4b0ed90860d37f38fc4841ad1f28b65ab0c3100020ac972bcd673a3dc0005d264e3b988de3270ef04ace30ee312f3534ee0e400000000476000520800033e07e00000002ee56b5b686d51fe2cb000270574876a04db12d952938072ab54e4c71c7579110ca60002d090d800071500034ec9f600000025d0160000000330014ae7d6263a492f40005300ef800071649e22a4a6a504363ade01489414642c718663d05b02f140006ee5b9b03c7f000071c9e7425eccf1131ed4926664767aba5b9ce814f8b08179691d730b500e621155ee0c6012a20c2d108941f0b486e995b04c88f401d9a5dd0a01a065317046cdd6598800106c00045f800000000055fb8b12420004d398a8a32c971220aec0003d60b68001a7ad664f4000000003813d0000fd4e097459a699c4c173cbb2f8360b0654322e86ac6ef4a4b5dc2947553358c7c3b4e2a2db1d3c8d422353a19585e868149cb0d13c881139283d02580a022699f4cf4a5c37a8a1814e88b4e70000bfe50e4d038b5168418066a7b88dc4ee4603b74674eb92b20000d50ab200001c4faeb4b1ea8001c5eb4571004980e426b1f602705ce08b24b1ee57e662b35f3404ecae420002f5c29000016da1443ce0000000d30000ada015915d258db2209307cbde5fc4a1364872e28c45b0dc51dc000447abed2be00000000007b88c50002d4c41e6bb6aa3b196841b3658102c56ccb9675aa0d1d892451622402a42bd3db11ed80864272a830
  | 33 => 0x20eea0790c000018005180c1293448cb581c302dce6cd330f89154a460342c8b4c88ee5db471aa7c24e0e72cb26c119e4a641bb89885aea21d12709c0a2e600033b8a2ac642b8bab466c7dd3fd94dc9121563180d642c49431c73940000e0d06ca0b9064adb04394f531cb7e5f0285de7e15463d82116d8c690a19d1c96210f3578c2cdf005c66a1a65e60b2c3942e1037c6486b739c5944d8f056afad7a21a257aa96ca4a6fa2fa25bc6641780ec8000c6e55b59394c08ac0003e08001806acd2088015b4428b4712c51e7403d0000000000480000298c6f68433a10554f285f145400016f44c97040000000dc2542a36800025447b175d44e1ed0000a080004c7379b2f4d78b921b43bb8c0e72475f0bb4b04bad2ab861c55c5b745e27341b8dd15019751b1610d0cb0000bb20007591e6db98a1e3f20b588c82e31a98fa9674d9d3dc377000000000004141cc0006638dc94709c413396980000004e5971518600000013c1d3ed364598f3c13a5da6300001bc80000001a0db9ad1b22609c051c001539293d9509845bb80000000005410ac1010419296b7a8cc257b67000000000005be0000e0663c00000010bed04000289197eb41742004d76854a1bea54c5805bd04c947c0000007208000e18aba02c94993b00000e19425d6e3784c88001042c4a55281b051061c0b59f6cb9e28d594b0e52f02a159c3859b146354bd8b15968f3e2d78c5d81875b3c505a5a185a560c105ca82d2e489b068e14d650fd39dc8743243c895658a63014a830505ba6c32511780ebcf0b6f82788a2c3e418d80000007140000000a80b6808a13885e62105008c984da000281bae94a07cf3c78c3c45edb930d80018a285d5969ea59c20005ae010475e73a0001330aa648871bb7194686551a11a24be673025da968b2000058f800152400000000000002a20c29e80000000703b690a2000000011e8dd6ba373d922955636013c938c34e2d24c41b1005a76178d00000000df4220d400005f6251a9b57ec8b946681740eea975292b80b628d05240000232a3300026ddc6cd4901f8d1c3460c12a738e0df600078133688487d95e933cd2d46da52031601a0b931a7b855b1a000417b1e8632b593e1a78447e129308b579350bf90000001d823cb22493200001455fbb43cd04c2e00034d1642c220000000c320005b105459d00bf55605d57e2ddd0000a596c85aa2ee962823aebd69b82516be6a00ba13040000005cabba90da7ff000206144c784064b488c282cd7248d5d1ae3eb22fa364c742c8367865d7545813f71c6c4fe49943e9840766ca138012d5214df86a238c831468e621b9987ce21f34b39a4e8a1a154584ec2026bd6ec9add566b6548c2cedc185726442568d26a6600005eca24bc13b486e089682733da9a13ec7aa68d3cd4000dd0464ab05d662f
  | 34 => 0xa70288ffc416a140ee9340c6c265219a3ece8c2711e302b05ee0da1071f019408e72fd904105a1185feb5ed36281034898946b8543523b8f4212f170789a78d5c0c6122914d2344cb09501b8b24cac057b988da2842587bca408c0883d1b2390aa9336b913948b039c1d00f106d68af1b0b0f0ce043b540b7c940e1532cf81a19b027b3cd16c14086d05d49a296ea00362baeb05deb0d2ff162cfa85e76ea2558000337339ac30dc46a571405c06082021290000a903c70559274e10c0d154815ddecea000019815723e01ed800098c5770000eb9bd6dbe00014f942aae878f2f293d48fa00027b49f26a170022ad4520a356bb5457b257646b12349decfc26b265d2d20f937b8db80000000b29058000edf366053d56e8df13ea4255cc4462feb950c821040e28b50b72c701a1a0b0d68d1f062a2dc00000000034b4000d785213394ca4c1c2e103487e4d9e0d400019660000003338f9436923ab865c684db00035bc9660000001cac7a80005699250288ed01cca06440ea2d2e608cdac4edb4fa009456a922424bcd13bcf3203200013905600003188000d680830fccc500000003b800000003a609dc000723591800062a000000000000055173600018226d83dd24209a87de08b99440f412218f24708ba7af0000ef0000df30c8389c45227572c0000bc2000000119ceb07522aa80004b27ce46f31b144672e47482d53003202c0253400083832d0000c983791fb3b513d24be00021492cc0004d6b77d35800010e251de1a0ec14f0e1ddfa7bd4720ccc000d4800022b1a6200053d32e1b824d219494706182a44fc97c1cce10800034943f049120d0178500b991f888689b0d670001cdc2b60fd204ad74e682003f58361db00dd01c8c7096c71f30d06b1cf2d8e0219961560c965542f78d5875a0bb228043a9ba5dbbb692f2d391fa88c412e07565ba6fcba2a4e1399d9c81a6506f3a038d7ee8700004685ea5f75fd000145086b2a31c85462000305957c46ad1428a000000071d0000e699884420000b883b68c638700000360006358cf0176000788a1980007402ba2750000000712000000000004c1c8925628f48f800000000043a8000ea88140001a347f8b4d54d144c99e7960000000c409364fc118577c6b10000e09a500002d21b1800035e00003105887f2754a9a800048367198284543804fd22692dc2ea690092491cb63358000004223a00038400004ac00000019645ae6411a489aa7ae0001b14b1200009f000147e000222a7dcfb400000000000000000001c19b760000cd00008c6b610002c20cd24f520a20959263300d4bcb176233e5ef885982c727378aaf973ed731ca86a85540d54eab6b58e6d8758da3f914604e748b460422cab5992c49cb2cfe2f2a990b7eef81cc0c8958a4a8201b5a50cac6148711003fc2b403a28
  | 35 => 0x5793447d200011b400061e0000320ee64fe270a5292f8b1d2a7b6b02fcdfe5e187dca8e0006bf80b81de0733cc3ce46e675c000000043cac0336000071400064800013ce00067800000000621e900010c800068724fc00023e0fa800117a00000023607580004f1b8500000006a83a082ae90314d8000f1600077580000520003de29b8000ad930c29140000007183c8c86a58c63b0000d480000783cc41c20000002c14f6eb153cf31e53e48b147ca6f4f56c3672220749d2c9e157a520f1800076f3c949cea7c0001f58b769115ec0001b6ea625f3211c31a86a1ee8cecd74a8c4aea8491fa1230003b71db22472df2f4092e234055355d51298109999655bc58d3658e58c2a97d36901c08ca9011e60920c0aded0f30a992ca0f71d18784058ebb3403a685c0daa62eb1a0b9c4862d1bbf95f4ecd4ff10200a6e2926f2b61ad6c754b3842d52060264025d9bdcdf16fe9d214ceec9217943c2fedc46eb841c3ae0b34022815262bfb20e17b93d8ccd6d326705707f94f589f8706abd32b9838c704740cf3c2136c7813da02293487491138935b32d24168063d5fa779326a4019ac71a5c3b83c17448b2ad33187627f51d50d68efc38f4780e45128a9336dbcbc67a6f060c87bdde002614235d93240095e30f25a38b8b0f93435c44d976b00331d6ccc20e90ff40162ba5289329d0cf3c70330c878a85625fa6695d6ea611e94b12e4af3353b6682f21e22ca9db93301a434e34182ce4a10260988cda88539622987682282051dd10ee4c02621b704de82325c30ac22600f430aed95ee8f53c3ad3194edb6736975840ce8c0001279990268425258c000a9d4e620350fecbc78c2bb8000ca62f2356839639b2ae8fc1e0a00000000015fe9ae642a43c21800065db1981c800040f0401ba4000367000023e42a5ba21806dee9b43997e40c2d024a2a41596253453095a56e2e7e00000012e6e5638100100000004539261b5cf140000ea13b6e9d00f8000ceeb550003c885b445c385a9fdd782ee0fd8f780000003e490b810600009b0ac8444ef42992695784130604adbd8906b9342b7284ba7d11baa16db6600000111f01dceaa57e06dc0000002a293cd8ac5a059992bc00017c4969ae00008707399509d6aa77792221819e1cc6a1800084641e0000cd1e40a7b3518001774168240800139ee7529cb66c8400b90002c40a16ae30001fb1c0200029e3014586e21348064400000039d8001722c30693b7200008c22c21a3d392ba72611eb18bedf71bd3ca841020414b8001d8646831e8e797de198189abd9d84147722a0fd09a8012ee00005be93400023c56d40002133b59d1a1bb06f0d00672c47570af118bcc91414b07861c92766c8f015c479366aa0e4ad0d09793095cff4012025886cae6b3509ca4c1cc8bb30810b607a67be795a97c5f45
  | 36 => 0x4918000cbc000000145c00032318b19f88368c1379264c6a4cf200018e4124647000113949645e32e00000004d74053105cb800078301fc000000309800151cb3900029e107a98a5c315f4dceace20380000001c76fd8001c9c3fa37c8000000e0342586205ae04743138ed7e4a0e49baad11aae6a6a3bbcc37e6261d336d5d62c7e1bb0d551480003e2b4d578e98902b1e0c41422403b190179e00073e2a909789fd78080000000b25ea16d19c800029d00018e40066f2a13c06c0580003a5973a24c2e394a084a00000000007c22ff4de000000000051c82d80007350000e9c0007c87848700fa00000001a5180e99b5ff3c3866aecc0003229c240006de9aad8e200059b1414ae000064e9ba81fc68c6d4000000000010b8b3c00054b4ec8214fe234a36b233928c6083951d40340c770b63a0d76400072b95fca44000000387cbb0000401a82ddca0001a29ca547419c777b9294860006648001a7060c6ab0fdc9c0470789b3bd71cb2a08933f51020000881c14000c423888000000b3c6d49df57caa715d412c8e1a1860f1959c014c8c5f634f0b2e38b592b9c0ce8520781a9780000001f72cf8168f0a0002a6c000ee71dfa21d584e3550d33ed4185eb6c204903be7fd43f26e1ceca9525215314e07724ac2b100000003ae80003ecbf4000000151e3585a893ad8f08912788000000142676b2bd40c9206bcb48c7480000000a65b802ab2958000000ae52e5ae31438a1960532b8f84a7e299940865c1ea0e798f90e2b405510d9099a13f00026ed77276c4a732d873eee84a93a55590df439e2fb4860e4344d800000000053b39d12a80456f1398017045000000000002f675228d5b464051db3c70e080006b6a5fc0c64ea72eade5598d4e383b371d8e5a94dca87c74a40638b859111c00063ea5b4000c9b3f2a74dcc60003f028ed25e76221caad51e44dd0352b28f100003e6bb200000000e8a70d1d490d37a26300000000002e0040264b475898498a4620c58c1557880231d83ec0002c954cae511f8eec705000144a9716d0b0e00006ad39e9e391a600000011451c00006c11cc80000003f3a7ccd4c1b6569316565c91449f00000003df5cd2c697f89d164a0001a94eff629353dbb42be31a18854fa000148000130a25f4468001346f1b6c038f930424f0000481c4657e5000000c9448c3179b5d130311419b755b300006f7a66581c841006bbf1a8238134a8d117982ce5ea8001aba86800c36259065f2000356c9a67666f095bd61446b218b630486ef5027af8c96e8802869e002de3d13b6869408490b21f33781c4000215b13c5fc6623ce2c2dd1ceb0534aa60fc2bd312b18b934c1322e4312584295c6e38db0080351276bb843288b01ceab5105402a27207f1a745883ab1b8577ea5901d0259aaaa870548154d80a5426f9
  | 37 => 0x297005c00000000019e1cf4d460a680000d236765a8a950445072dc321865e5d5337800195a2f86a61004aa8850598193c26ed051eb961c0001b150d9001650000168b86d264be9477a83db0a7a855b000191e5e348b00511b815d00032940006e800000000004136f497a487a24a1e1396d3c05ad30fb098faa00000000008045f8728b374000cfa07aba019ecb6b0f40d7dad84b00001418e9a0006762dc99a010e076800000094c0000485600c9a0000001c66f4009e13999aeb4900035f43789d036a15f1ce4db40001bf515a000548ad78000a2e636a19c00e24b5659210a760002b1000187c8455a71f18ccc000000337ce20a44000000000000000000000002cc0000849e00000000000000029c1180000000aa73f83134000d2f6fca6186209123d820259d43b060400000000001e700016cca2100027000000005d33c3c1967953032e899fe0006e78b05688c7f18a36f028c0002c28e11c3c00062d9c810f058e0cd9cf8b9416a7073ae0fd00d125288e1dc885373fa2c81c09956e282f055a50108b0e40000000000000155a0001a08054f205bc069a27d6024d92e80001a2637e27b00007820000e817106560002951b9071008d5d83b14000c066818b943e685e0002e5c6bac150c1a799daa3bd23c20c026a17a0f23a4158cd636bd1f71dc4aa100b0000ec62a732a07056dc8a107f9e09df6cc1035b3d1cb462d690a6402c08ae6ba800000025a210896dd2ebc82babafd84e0000002258062d154abac5d552000116a3e138c0000ffa4f4624c3d3b8b5900000006ce26a42b2c4e3bc0000000a9c00034ac00078500000001ac98d0000a0c000879000000000000071e0000430a6f5c82e0d55e739767047000025c181b4415a0bbb7328040000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x184d855c86218d100062361172188634400184d876146218d100062361d841886344001a89846006218d1000613a1972548634400184c865c95218d1000703d91725486344001c0c645c95218d1000513e5f62548634400144d971895218d1000623a1972508634400188c865c94218d1000703d95725086344001c0c655c94218d1000523e5f62508634400148d971894218d1000781550625046344001b11542014118d10006b01888050463440016849650a2118d10006a1a194288463440016c2968862018d10005a225942480634400144d92d517218d1046e1361572948634400188d845ca5218d1000613e11725486344001a15546074218d10007035c952d086344001a15856074218d100061361572908634411788d845ca4218d1000613615725086344001c0f545c94218d100070355172508634400160d92a154218d1000583e4985508634400168691e094218d1000703a15725086344001c0d855c94218d10007035cb525086344001c0d725494218d100060761d54d046344001a0d5460b4118d100062361d420846344001a89426002118d100060761d541006344001a0d546084018d100068555181100634400188d8750b2018d10006a150881480634400144d939db75d89100052364e76dd362440018a6861c774d89100068961581193624400144d959db73d89100052365276dcf624400144e96dd773d891000613a1b75dcf624400148e96dd373d891000623a1b74dcf6244001c0f65dd373d89100070319774dcf6244001c0f75d9373d891000703dd464dcf6244001b215420141d89100052364e71dd362440014a9909c774d891000523e4d70dd36244001a258560474d89100060ba1f74d53624400182c87dd154d89100058964474553624400144d94dd773d891000523e5175dcf6244001c0f75dd373d8910007031d774dcf6244001c0f95dd373d89100070325774dcf624400144f955d373d891000703dd474dcf624400144e97d5373d891000703dd354dcf624400144e9755373d891000703dd154dcf624400184e87dd473d891000623a1f741cf624400182e8755341d89100068355183d07624400182e8755040d891000683551831036244001a255460440d89100040fa6075d91314400141d941d7634c5100050b65075d89314400142d921d3654c1100052364874d8d30440010ae981d3624c11000d13e5d524cb650400384f8754932d8c1000e23e1d424cb630400106d9221d5458c1001c0f26174551630400103d9421d5258c1001c1b26172549630400142d92dd54258c100052924572509630400144e975493258c1000703dd5424c9630414bc0c755093258c10006151d4814c96304001a85422053258c100071154932dd91004001c85424cb76440100071254932dd91004001c89424cb7644010
  | 1 => 0xd1325d524c9654400184e8754932595100061321d524c96544001c0f745493259510537031d1524c9654400148e9750932595100052325d424c9654400188e8750932595100062321d424c965440018358760464195100061360d72188654400184d8760c621951000683611831886544001a298460062195100058364c62508654400160d92191321951000613219724c86544001c0c645c9321951000513e5f624c8654400144d97189321951000583650624c8654400160c96509321951000683219424c86544001c0e7650932195100060d219745046544001931742014119510005892594288465440016289650920195100068a219424806544001a0d8560c62d91100058364c6254b644400160d9219532d911000523a5b724cb6444001c0f65dc932d911000703197724cb644400160d9518932d911000583a59524cb644400160c9654932d911000683219524cb644414dc0e7654932d91100064ca0375dc764440014aa96dc920d911000507e4d71dd7644400142f925c775d91100050764e70dd7644400142d929c375d91100050d64670dd7644400142d92e1772d91100050b64885dcb644400160d921d532d911000703dd7724cb6444001c0c75dc932d911000703e57724cb6444001c0c95dc932d911000523a5c724cb644400160d951c932d911000703dcb524cb644400148e9794932d911053d83656524cb6444001c0f7254932d9110007035c9524cb644400160e9754932d91100058325d524cb644400188d83dcb20d91100068561581193634400144d9219772d8d100052364864dcb6344001a898460062d8d1000703d937254b6344001c0c64dc952d8d1000703d977250b6344001c0c65dc942d8d10006c45508050763440016849650a21d8d10005a2259424836344001615911d154d8d100051364b54dcb634400188d84dca52d8d1000613e137254b6344001c0f7254b42d8d10006136177290b634400184d85dc942d8d1000703d537250b6344001c0d54dc942d8d100058364a8550b634400160f9261542d8d1000703a177250b6344001c0d85dc942d8d10005a1a447250b6344001689901c942d8d1000703dcb5250b6344001c0f7254942d8d100048765285dc7634400181e8755341d8d100068355182d07634400188e8750821d8d10006a250980087634400128d92a1370d8d1000607a1d541036344001a0d5460840d8d100068555181103634400188e8750b20d8d1000613e1783dc9634400188f84e0f7258d1000513a5d524c9634400144c975493258d1000e1321d524c96344001c0f745493258d10537031d1524c9634400148e975093258d100052325d424c9634400388c875093258d1000703dd5424c9634414bc0c755093258d100068561581190634400144d921957218d1000523648645c86344
  | 2 => 0xc00142d92e1772d91300050b64885dcb644c00188d83dca72d913000583648754cb644c001c0f75dc932d9130007031d7724cb644c001c0f95dc932d913000703257724cb644c00148e971c932d913000583654724cb644c001c0f72d4932d913000523a5e524cb644c15160d9594932d913000703dc9524cb644c001c0d7254932d913000583a5d524cb644c00160c9754932d913000607dd7835c7644c00182f75e0971d91300062360f72087644c0018ab7260021d91300062360f72c83644c001a858350821d8530006a850980087614c00142d929d365985300050b64a74196614c00182e7560864985300060b5d582192614c00182f7560864585300060b1d582191614c0010ad981c864585300042ba6064dc9614c001aa14260021185300052364864dcd514c00142d92193754c5300040f65287d95314c00185431a1f654c5300040fa6075d91314c00148d9219373541300058364864196304c05381f736107558430006071cd841d5610c001a1431610755843001c0f26174551610c00103d9421d5258430006150c487549610c00144e97549325843000703dd5424c9610c14bc0c755093258430006151d4814c9610c001a854220532584300052364874dd9300c00188d8250b764c03000543648741d5300c00182e7560a74d8f100060b5d5829d363c400141f9755143d8f1001607e1d5450f63c400142f925d542d8f100142ba637250b63c400144d9754932d8f10537039d1524cb63c4001c0d7454932d8f100052365d424cb63c414bc0e7550932d8f10007035d5424cb63c400388c875093258f1000507652659cf658400184d8754932d961000623e1d424cb658400188d8750932d961001c0fa6374553638400103d94e1d52d8e100051365d524cb638400388f8750932d8e1052f039d5424cb6384001c0d7550932d8e10006159d4814cb6384001a854220532d8e100050d652755c7638400121d94a176398e100048765285dcd638400581c875514358e10005076507558d318400160d9494932d9510006836118318b6544001a298460062d95100058364c6250b654400160d9219132d951000703193724cb654400160d9418932d951000583259424cb6544001a0c8650932d951052f039d9424cb65440016249650a21d95100058a25942483654400142d92a1d42d95100050be498750b654400144f925d132d951000513653724cb654400160d941c932d951000703dcb424cb654400144e9790932d951000703dc9424cb6544001c0d7250932d951000513a5d424cb6544001c0f7450932d9510007035d1424cb6544001c0e9750932d95100070365d424cb654400181f7460f41d95100060bdd182d076544001a0d8350821d95100068a509800876544001a0d8350b20d951000613e1783dc9654400188f84e0f725951
  | 3 => 0x3100613e097258e5394001a0d825096394e50007035c94258e5394001529922117094e5000742509325c253940014359499671d963000e23e1d424cb658c0014549355271d96300050d650539c7658c0014659214e71d963000711549329c7658c001c85424ca71d963000711549325c7658c001c85424c971d96300048d65285d86618c0058348755141586300050d65075985318c001435941d5614c63000583652524cb654c00182d7460864d95300060b61d82193654c001a0d8360864d95300060ba5d82193654c00182d9760864d953000683a4d82193654c001a0d9360864d9530005836486490f654c00160d9219143d95300050b64864dcb654c00142d9219172d95300060b6117218b654c00182c865c942d9530005892456250b654c00160d9219332d953000583648644cb654c001c0c64dc932d953000583650624cb654c00160c9650932d953052f039d9424cb654c00182d7460874d95300050b64a8750b654c00142f9261d42d95300050b65f8250b654c00160d939c942d9530007035c942ccb654c00182d8750a32d953000513e49744cb654c00144d94dc932d953000583650724cb654c001c0f72d0932d953000513a5e424cb654c001c0f7250932d9530007035c9424cb654c00144e9750932d953000703dd1424cb654c001c0d7450932d953000703a5d424cb654c001c0d9750932d95300048b64a849c7654c00181f7460f41d95300060bdd182d07654c00182d8750821d95300068360d42087654c001a294260021d95300048b648845c3654c00182d8750b20d95300068360d42c83654c001c0f745493259530537031d1524c9654c00148e9750932595300060b5d182190654c00181d8760c64195300060b61d82190654c001a0d8360864195300060ba5d82190654c00182d97608641953000683a4d82190654c001a0d9360864195300060b60b72190654c00160d921924319530006072197450c654c00141d971914319530005836486450c654c00142d9219172195300060b61172188654c00142d929d942195300060b21972508654c00142d9798942195300058364e62508654c00142f9758942195300058924562508654c00160d92193321953000583648644c8654c00184c865c9321953000703191724c8654c00144f97d893219530007039d9424c8654c00142d929db75d91300050b64a761d7644c00142d929db65d91300050b64a76197644c00141e96dd773d91300050b64b65dcb644c00142d9219772d91300142ba637258b644c0018a77220562d91300042be617218b644c00160d9219532d913000703d97724cb644c001c0c65dc932d913000583654624cb644c00160e9654932d913000583259524cb644c14dc0e7654932d91300050764e70dd7644c00142d929c375d91300050d64670dd7644
  | 4 => 0x5440160f926154218d5100585245855086354401c0f525c94218d5100703a15725086354401c0d855c94218d5100703145725086354401c0d725494218d510060761d54d046354401a0d5460b4118d5111c8726154504635440184d855c82118d510062361172084635440188d875082118d51006325c9800846354401a89426002118d510060761d541006354401a0d546084018d510068555181100635440184d855cb2018d510062361172c80635440188d8750b2018d510061360b7218e5154401a0d8250863945510051364b53dc9658c401c0f53dc9425963100e2a21d42481608c40160d9494932d95310060bdd182993654c40103f985d064d953100583650624cb654c54bc0e7650932d9531006c1508814cb654c40103f985d074d95310050b64a8750b654c40142f9261d42d953100513e49744cb654c40144d94dc932d953100583650724cb654c401c0f72d0932d953100513a5e424cb654c401c0f7250932d9531007035c9424cb654c40144e9750932d953100703dd1424cb654c401c0d7450932d953100703a5d424cb654c401c0d9750932d953100607dd183d07654c40182f7460b41d95310068360d42087654c401a294260021d953100607dd183103654c40182f7460840d95310060ddd181103654c401a0d8350b20d953100613a1d524c9654c40188e87509325953100e2321d424c9654c54181f63e0974195310050da58315d0654c549c17630c57419531006075d183990654c40182d74a0a64195310060b5d182990654c40181d74e0d64195310040fe6174988654c40103d985d26219531006075d183988654c40181d74e0d62195310060d5d381588654c40103d97a1062195310040fe6174188654c40103d985d0621953140607a0d74188654c54181f6361f42195314fe07d8d87508654c40182d87d8942195310060b61c62508654c40181e865d3321953100495244864c8654c40181e865d1321953100607219744c8654c40184e865c9321953100613219724c8654c40144f97d893219531007035d3624c8654c40150d97509321953100683a19424c8654c401a0c865093219531007039d9424c8654c401915742053219531006515c8814c8654c401b0542205321953101e079d984196314c40103d981d065581310060b61072195604c40103e9819774581310050b65065dc9604c401a8542205321813100623e0942dd9310c40181f76610754c4310060bdd5821d1600c40182c756087458031006231cd821d1600c401a883060874580310050725d5450d600c401a195420143580310050b64b75509600c4050ac985c9425803100513a5d524c9600c401c0f745493258031537031d1524c9600c40148e97509325803100703dd5424c9600c54bc0c7550932580310050e25d54901600c401aa14220520580
  | 5 => 0x77000000308410000001668b90a84e396000002665000001080021a1a849a3c3887e939a3d0000000c0392e06c40820a0008bc001e000075c001ba000000000004da00000000338a184b04d26a0000024c000000508000000008a0000009880000000000081800000654000000000000000000000000051000000000000000008c0000160006b00036c000811f9000000cea680003fc00000014944920dd00000000000000000001e30000000000000007d25000000000001bd00201800401005004018018010000580000000600400804000000000020000040080300600005000008010000000160080200000000c018000000000080100801c0c0000000100100201200001000004004038000000440000000000400801002000000010080000380000000c06803000008000010000000080100800400800002008000000080040000100400001004000008010070000080280100000000800000010000000020040000100c00000002020000000000040000080000200c058060060080100500c0000000e0040140080a0000000000400a00002800004018000010020000300100200c000000040080000100000001006000018018020100000500200a004010000040280000700200c01001002008030000000040000000000002800004030014359414571982530050ea4085dd16094c050ac985c9425825300703dd1524c96094d4dc0c74549325825300523a5d424c96094c01a858350821d8553006a8509800876154c0181c835d15418553006a8509800846154c0184f825c96394e51007035c94258e5394401d05424c97194e5100507650535ce609440144d9214d739825100703dd1524c9609454dc0c74549325825100523a5d424c9609440148c9750932582510052a25d42481609440188f7460a74d8d510051364b54dcb635440148d9494b72d8d5100613e137254b6354401c0f7254b42d8d51006136177290b635440184d85dc942d8d5100703d537250b6354401c0d54dc942d8d5100583e498550b6354401c0f52dc942d8d5100703a177250b6354401c0d85dc942d8d5100703dc95250b635445381e8755341d8d510068355182d07635440188e8750821d8d51006a250980087635440128d92a1370d8d5100607a1d541036354401a0d5460840d8d510068555181103635440188e8750b20d8d510062361172188635440148d971894218d510051364b545c8635451b44d959497218d5100523652525c8635440141d941457218d5100513648515c8635440184f845c95218d51007115cb81548635440121d942055218d51006135c8815486354401c45722055218d51007035c952d08635440184d855ca4218d5145e23611729086354401254916154218d5100613615725086354401c0f545c94218d51007035517250863
  | 6 => 0x491a6338001001f6000e8000000000a221d1a46281a0a502e000418000000000985c49c0e000000000000cc00000000129000000538de0f800000000000000000000000001b400000000000001430002d4000000001a000246000174c4a473aa26d2d80033c47ca31e600000000000256000000164ea000001f74585ec6415216000142800000688cd07e0b2340840000003bc001253848b4181873e036c8d0000000012e8000f600000165000000bc00000095800000000000002134f8000001c60640000c8e30005448700000000000000000808d28aa000000011ff00221c4d139012384a60000004c8d617c000000b38b14b2000001994203980011c0ae3900000034000042a23000000fd8002f2658000333920011b8a21480000000000076400000000000001e93a400000000000204a78c50002bc390f4000000000000d80003307d4627f8648002da000d7000000000000002b6000f425411c465361230007d85f9df00054c0006401e07060000000000002611fc16000000000560b183500051408a530000002525f3245d8311e44723802101435610414800000000da12a2ba2dc1716e3de000b88001b20000005600000000000000000b4800000000000001dc000140004bc0000000047c0000000030a0dc0008949e0f4b08bb4288e85d13e43e63c001bf000000001563f8000001b8000000ed8240003e40000000000000140000000001481e2000b30004501e8000000000011a80000000000004000750e8800000414c126b0c6218678c2000730001012247a800000470000000000009d83c000000894711d64320f13d8df30086c06a0e000815212831040000000000000085000000000000000003dd00a34000000bd1093500fc3a2060ca1800013f34c000f700047e09cdb9fd0009f4f60000004e933800000000b9800000000000c72420203b8000000001005400000000000000000728001b813c000fc3c49a8000a80a000097800000000000000001840015a000000000000009700002d372260571a90008d8001e1000074001220ec2d8ed0002503780017e418498c999f000000000bc1101c000000000178fa85315a000c08000000003489f000000000000000000000048200000000336000c69f34c89f8001271e64f000255000000001884ee00000000000000000000009c07681a0000000000046674c660000f20e8ba8003e80010000031620074a5001c0000023020c9e50b87c41a3c12697f2b881ce69470563b1049c7000714000000dc0000a9203600f8018000006a8000000900011394b00045c000e70000010880012e0000013600000000000000000000000006b4001de282001158f50000000000000055c00000000000000520006900000049665c00000000000000000002f8128d10009d11d800000a1000000
  | 7 => 0x276000000000000000014d00082000000000000001310800011907f1380000000000044400000000000000000000013c0002845d0000000002e10b0c6000000219c100000000269000168f69c81d600074000000015079620000005a00000069c0000048a9c4880074245651316b448000608bd2942ac0015f20e738000000d690c8f16f044079058a000000124a2108a000001770000005600011a000d7986000328001c33ba3e8388002660b11486f2922a50185b0002c8001eb23a4c0878cd0004b400094268729379682a82547ea2a3f09204618e4e49fc238da434000420120007c400000054000518003066f90e0f636a000618924c088800000018540b21c02704304500000017c0001b2d819c4f04614c95d3d0310000004c98c346a045384c328240898260007940000022a000b500000000000000000000000002160000000000079c0005505e98c000064dc000000c406c1d4479a12520000017d000644b92180887c800000000760000d537600110000000000000000000000000043c4dc000000006c92c04b0006400000000000000000000000000ea000968658d700022c119cf27a000001600764b86c00025800000000000000000000000000024000000000000504000000000009946a000000000d98f20000008b0000005790207313a2448d8001720000000000055400244000000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x82d71d510c24028f0000140c001604e6064050804400004cd4808200810e50000a03688835d1541855300601b28b9102a90c6a8802844a161572508635440160250b0ab928431aa200a036a0515c94218d5100502942432e8990ca98802844a1219724c8654c401806cbd0ca126432a6200c0365c8650932195310054094243284990ca98802905a7508814c8654c401222d1126aa4e3b2c6000c03a5d9360864d953000601b2ec9b04320ca98002a08a064d82190654c00140ad20ea40a64b086000a11688752053258430007008eaa1102992c218002815a49d4814cb6384001422d14ea40a65b1c2000e019d54220532d8e10007402a831100a08c688002815a41d4814c96304001422d10ea40a64b182000e011d5422053258c10
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x400800006000200060059728486509321953100600997281936086419530004805ba1d5422053258430004805ba9d54220532d8e10004805ba1d5422053258c10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x4b
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x124b
  | 8 => 0x138b
  | 9 => 0x4
  | 10 => 0x94b
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124d
  | 14 => 0x124e
  | 15 => 0x138d
  | 16 => 0x138e
  | 17 => 0xcb
  | 18 => 0xcd
  | 19 => 0xce
  | 20 => 0x12cb
  | 21 => 0x9cb
  | 22 => 0x9cd
  | 23 => 0x9ce
  | 24 => 0x12cd
  | 25 => 0x12ce
  | 26 => 0x168b
  | 27 => 0x168d
  | 28 => 0x168e
  | 29 => 0xa4b
  | 30 => 0xa4d
  | 31 => 0x134b
  | 32 => 0x134d
  | 33 => 0x24b
  | 34 => 0x24d
  | 35 => 0x24e
  | 36 => 0x144b
  | 37 => 0xb4b
  | 38 => 0xb4d
  | 39 => 0xb4e
  | 40 => 0x144d
  | 41 => 0x144e
  | 42 => 0x16cb
  | 43 => 0x16cd
  | 44 => 0x16ce
  | 45 => 0xbcb
  | 46 => 0xbcd
  | 47 => 0x14cb
  | 48 => 0x14cd
  | 49 => 0xecb
  | 50 => 0xecd
  | 51 => 0x17cb
  | 52 => 0x17cd
  | 53 => 0x94053
  | 54 => 0x94055
  | 55 => 0x95393
  | 56 => 0x5253
  | 57 => 0x95253
  | 58 => 0x5393
  | 59 => 0x125393
  | 60 => 0x4953
  | 61 => 0x124053
  | 62 => 0x124055
  | 63 => 0x138053
  | 64 => 0x138055
  | 65 => 0x124953
  | 66 => 0x124955
  | 67 => 0x95255
  | 68 => 0x138953
  | 69 => 0x138955
  | 70 => 0x139253
  | 71 => 0x139255
  | 72 => 0x9d2d3
  | 73 => 0x9c0d3
  | 74 => 0xc9d3
  | 75 => 0x9c0d5
  | 76 => 0x1452d3
  | 77 => 0x1440d3
  | 78 => 0xd453
  | 79 => 0x1440d5
  | 80 => 0x14cc
  | 81 => 0x12c9d3
  | 82 => 0x12c9d5
  | 83 => 0x9d2d5
  | 84 => 0x130c
  | 85 => 0x14c
  | 86 => 0x134c
  | 87 => 0x1692d3
  | 88 => 0x12d693
  | 89 => 0x1692d5
  | 90 => 0x252d3
  | 91 => 0x12c253
  | 92 => 0x252d5
  | 93 => 0x12d453
  | 94 => 0x1452d5
  | 95 => 0x134a53
  | 96 => 0xa5353
  | 97 => 0x134a55
  | 98 => 0xa5355
  | 99 => 0x14d353
  | 100 => 0x1354d3
  | 101 => 0x14d355
  | 102 => 0x1354d5
  | 103 => 0x17d353
  | 104 => 0x1357d3
  | 105 => 0x17d355
  | 106 => 0x1357d5
  | 107 => 0xb4253
  | 108 => 0xb5453
  | 109 => 0x24b53
  | 110 => 0xb4255
  | 111 => 0x24b55
  | 112 => 0x144b53
  | 113 => 0x144b55
  | 114 => 0x2cc
  | 115 => 0x16d453
  | 116 => 0x1456d3
  | 117 => 0x16d455
  | 118 => 0x1456d5
  | 119 => 0x14cbd3
  | 120 => 0xbd4d3
  | 121 => 0x14cbd5
  | 122 => 0xbd4d5
  | 123 => 0x17d4d3
  | 124 => 0x14d7d3
  | 125 => 0x17d4d5
  | 126 => 0x14d7d5
  | 127 => 0xcce
  | 128 => 0x170e
  | 129 => 0xd0e
  | 130 => 0x188e
  | 131 => 0x10c
  | 132 => 0x24956
  | 133 => 0x95a93
  | 134 => 0x95053
  | 135 => 0x95493
  | 136 => 0x104b
  | 137 => 0x1a8b
  | 138 => 0x188c
  | 139 => 0xd0c
  | 140 => 0x1a0c
  | 141 => 0xd4c
  | 142 => 0x1a8c
  | 143 => 0x104c
  | 144 => 0xccd
  | 145 => 0x170d
  | 146 => 0xd4d
  | 147 => 0x1a0d
  | 148 => 0x95715
  | 149 => 0x94cd5
  | 150 => 0x95a15
  | 151 => 0x94d55
  | 152 => 0x95295
  | 153 => 0x95415
  | 154 => 0x25396
  | 155 => 0x9ccd5
  | 156 => 0x9da15
  | 157 => 0x9cd55
  | 158 => 0x138256
  | 159 => 0xd1456
  | 160 => 0x189456
  | 161 => 0xd0256
  | 162 => 0x188256
  | 163 => 0x25556
  | 164 => 0x25456
  | 165 => 0xd0cd6
  | 166 => 0xd4cd5
  | 167 => 0xcc94d5d
  | 168 => 0xcc9cd5d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 68
  | 7 => 1728
  | 6 => 3887
  | 5 => 3905
  | 4 => 647
  | 3 => 25
  | 2 => 5
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1922+((h/22+packedAt gbK8 (1768+(h % 22)*7) 7) % 82)*8) 8
  | 7 => packedAt gbK7 (70848+((h/576+packedAt gbK7 (63936+(h % 576)*12) 12) % 2759)*12) 12
  | 6 => packedAt gbK6 (203411+((h/1295+packedAt gbK6 (186576+(h % 1295)*13) 13) % 4665)*13) 13
  | 5 => packedAt gbK5 (247308+((h/1301+packedAt gbK5 (230395+(h % 1301)*13) 13) % 4687)*13) 13
  | 4 => packedAt gbK4 (47655+((h/215+packedAt gbK4 (45290+(h % 215)*11) 11) % 1248)*11) 11
  | 3 => packedAt gbK3 (2073+((h/8+packedAt gbK3 (2025+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt gbK2 (464+((h/1+packedAt gbK2 (460+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff03ff03fc0fffff83ff807f49e8e7d19f3f3
  | 1 => 0xc1ffc1ffc1ff07807fc1fff80b69719ee6ccfc
  | 2 => 0xfe1ffe0001fff8007ffe3ffffc7181e3070f1f
  | 3 => 0x1ffffffe0000007fffc0000f81fe03f80fe0
  | 4 => 0x1fffffffffffff800000000ffe0003fff000
  | 5 => 0xffe0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2200230024008a3180248126002062c085171
  | 1 => 0x414140d440d10505284092b02128309462c4b4
  | 2 => 0xb41aac02112ad00846b425458c518143050a0a
  | 3 => 0x101cf76ab408401277390060ce81da03b80fc0
  | 4 => 0x211f398f39bce65c021001810ffc0003d7a000
  | 5 => 0x3988200c20308460042006060fffedf8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36795
namespace PEqualNP.Outside.L_meta_36795
open PEqualNP.Outside.L_meta_36795.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
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
theorem bs2_2_0 : Interval s2Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 13 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 75 := (concat bs2_3_0 (concat bs2_3_32 bs2_3_64))
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
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 626 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 bs2_4_192) (concat bs2_4_224 (concat bs2_4_256 bs2_4_288)))) (concat (concat (concat bs2_4_320 bs2_4_352) (concat bs2_4_384 (concat bs2_4_416 bs2_4_448))) (concat (concat bs2_4_480 bs2_4_512) (concat bs2_4_544 (concat bs2_4_576 bs2_4_608)))))
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
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 699 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 (concat bs2_5_192 bs2_5_224)) (concat bs2_5_256 (concat bs2_5_288 bs2_5_320)))) (concat (concat (concat bs2_5_352 bs2_5_384) (concat bs2_5_416 (concat bs2_5_448 bs2_5_480))) (concat (concat bs2_5_512 (concat bs2_5_544 bs2_5_576)) (concat bs2_5_608 (concat bs2_5_640 bs2_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 42 := (concat bs2_6_0 bs2_6_32)
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
theorem bs4_3_64 : Interval s4Atlas 3 64 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 85 := (concat bs4_3_0 (concat bs4_3_32 bs4_3_64))
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
theorem bs4_4_736 : Interval s4Atlas 4 736 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 754 := (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat bs4_4_288 (concat bs4_4_320 bs4_4_352)))) (concat (concat (concat bs4_4_384 (concat bs4_4_416 bs4_4_448)) (concat bs4_4_480 (concat bs4_4_512 bs4_4_544))) (concat (concat bs4_4_576 (concat bs4_4_608 bs4_4_640)) (concat bs4_4_672 (concat bs4_4_704 bs4_4_736)))))
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
theorem bs4_5_768 : Interval s4Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 779 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat bs4_5_96 (concat bs4_5_128 bs4_5_160))) (concat (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)) (concat bs4_5_288 (concat bs4_5_320 bs4_5_352)))) (concat (concat (concat bs4_5_384 (concat bs4_5_416 bs4_5_448)) (concat bs4_5_480 (concat bs4_5_512 bs4_5_544))) (concat (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)) (concat (concat bs4_5_672 bs4_5_704) (concat bs4_5_736 bs4_5_768)))))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 5 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 25 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 647 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 bgb_4_192) (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)))) (concat (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 (concat bgb_4_416 bgb_4_448))) (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat bgb_4_576 (concat bgb_4_608 bgb_4_640)))))
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
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3905 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664))) (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)) (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)))))) (concat (concat (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 bgb_5_2144))) (concat (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 bgb_5_2272)) (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400)))) (concat (concat (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656))) (concat (concat (concat bgb_5_2688 bgb_5_2720) (concat bgb_5_2752 bgb_5_2784)) (concat (concat bgb_5_2816 bgb_5_2848) (concat bgb_5_2880 bgb_5_2912))))) (concat (concat (concat (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008)) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 bgb_5_3136))) (concat (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392)))) (concat (concat (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520)) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 bgb_5_3648))) (concat (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 bgb_5_3776)) (concat (concat bgb_5_3808 bgb_5_3840) (concat bgb_5_3872 bgb_5_3904)))))))
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
theorem bgb_6_3872 : Interval gbAtlas 6 3872 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3887 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672))) (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800)) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928))))) (concat (concat (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 bgb_6_1152))) (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))) (concat (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)) (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 bgb_6_1920)))))) (concat (concat (concat (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 bgb_6_2144))) (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400)))) (concat (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624))) (concat (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))))) (concat (concat (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104))) (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360)))) (concat (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616))) (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872)))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1728 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608))) (concat (concat bgb_7_640 (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832))))) (concat (concat (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248)))) (concat (concat (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344)) (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472))) (concat (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568)) (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 68 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0eeeaeee8eeeae8e0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373992 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36795.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.or,[2,3]⟩,⟨.and,[1,7]⟩,⟨.or,[4,5]⟩,⟨.or,[0,8]⟩,⟨.and,[6,9]⟩,⟨.or,[2,11]⟩,⟨.and,[0,8]⟩,⟨.or,[12,13]⟩,⟨.or,[4,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36795

open PEqualNP.Outside.L_meta_36795 in
theorem PEqualNP.Outside.L_meta_36795 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
