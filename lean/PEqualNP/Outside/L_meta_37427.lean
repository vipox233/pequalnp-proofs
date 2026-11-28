import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37427.Model
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


end PEqualNP.Outside.L_meta_37427.Model

namespace PEqualNP.Outside.L_meta_37427
open PEqualNP.Outside.L_meta_37427.Model
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

def SBf (j : Nat) : Nat := [6, 4, 4, 8, 8, 6].getD j 0

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

def mirrorSteps : List Move := [swapRows 33,swapRows 67]

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

end PEqualNP.Outside.L_meta_37427

namespace PEqualNP.Outside.L_meta_37427
open PEqualNP.Outside.L_meta_37427.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x81c900034300b3c510608a40c38100000033009be41bc41de31dc31ee21ec21be40bc40de30dc30ee20ec20fb10f610f410f810f010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x120092c26044434170003000003854cf58800d5001950401c000000a0200200439c06510431d220843c4310873080186a10020e41804172508436480086c10010e918021d030043c440087808010d920821b041043a46208740c410f110821e02104366a8086c15010e9a9821d053043c6a4087814810
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x40083105414c10c815052043405314810
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 25
  | 2 => 3
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
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 23)*6) 6
  | 3 => packedAt s0K3 (723+((h/8+packedAt s0K3 (675+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s0K2 (117+((h/1+packedAt s0K2 (114+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffbf83ffffc00fffffffc03ffff0ff
  | 4 => 0xffffffffffdffc1ffffff003ffffffc03fff0f
  | 5 => 0xefffe0fffffffc00ffffffc03ff0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffff00884212c95264b12dd2d2d2d777
  | 2 => 0xffffffffff011084255264a95256e565656bbb
  | 3 => 0xffffffffff42790849bb48d2649b7039b9b0dd
  | 4 => 0x2423d08e238ee388e3b9b03e3d0e
  | 5 => 0x18421ef03c0f03f0fc3e3e303ee0
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xc0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000c0c0c000c0000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37427
namespace PEqualNP.Outside.L_meta_37427
open PEqualNP.Outside.L_meta_37427.Model
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
  | 2 => 0x3f80fff807f03f81e0fc1f83ff07c0f8149ecc
  | 3 => 0x3fff03fff8003fffff001ffc1ff800fff8e30f
  | 4 => 0xc00003ffffffc001ffffe0001fffff001f03f0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8082000890800400021422842108520a412c55
  | 2 => 0x955699947525692af0ad15a3574686d0d496cc
  | 3 => 0x264caaa52469b269758219691ad208e598c30a
  | 4 => 0x3468d346464d234db9cb50421ce72c411e03a0
  | 5 => 0x3870e387878e3c71def39e73908430861ff800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37427
namespace PEqualNP.Outside.L_meta_37427
open PEqualNP.Outside.L_meta_37427.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x3f80fff807f03f81e0fc1f83ff07c0f8149ecc
  | 3 => 0x3fff03fff8003fffff001ffc1ff800fff8e30f
  | 4 => 0xc00003ffffffc001ffffe0001fffff001f03f0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8082000890800400021422842108520a412c55
  | 1 => 0x955699947525692af0ad15a3574686d0d496cc
  | 3 => 0x264caaa52469b269758219691ad208e598c30a
  | 4 => 0x3468d346464d234db9cb50421ce72c411e03a0
  | 5 => 0x3870e387878e3c71def39e73908430861ff800
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xaaaaaa88aaaaaa00aaaaaa88aaaaaa00aaaaaa88aaaaaa00aaaaaa88aaaaaa00aaaaaa88aaaaaa00aaaaaa88aaaaaa00aaaaaa88aaaaaa00aaaaaa88aaaaaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37427
namespace PEqualNP.Outside.L_meta_37427
open PEqualNP.Outside.L_meta_37427.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x24000000000609a856100170a780250e20c832024ea9000002138446812c7c02600003004e4902200a8014166800036086232a2870f0000008018310b1404c0048ff43fe43fd43fc43ff42ef42fe42fd42fc42ec42ff32fe32fd32fc32ff41f741fe41fd41fc41f441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x6617d52cc3de85987b10b30bf28e617d51cc3ee83987d10730fda0661f840cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5187bd0a30f621461de328c3b865185f94630bea8c61f7418c3e88318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa9261ef524c2dea4985f14930f6292616c524c3de84987b10930bfa8a61f7514c2eea2985f14530fa28a6174514c3ee82987d10530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4187bd0830f621061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861f7410c3e88218778c430ee188617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83ee83907d10720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ef32883d865105f94620bea8c41f741883e883107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f7a1241ec42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483ee82907d10520f790a41ed21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef42083d884107bcc820f6190417e51083eca2105d94420bea8841f551082eaa2107dd0420fa20841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10f7a1621ec42c43ee83887d10710fb18e21f531c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10f7a1421ec42842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910f7a1221ec42443ee82887d10510fb18a21f531443ec42887d48510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52043de84087b10810bf28821f741043e882087dcc410fa18821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf421077c8420ef10841f621083ac42106fca220efd0441fb20883bd41107ea8220df94041bea8083f654106eca820ed95041fba9883f653107eaa620fd14c41fba1883b743107ec8620fd50c41daa1883f443107eea420fd94841faa9083f452107ee8420f9d0841fb21083b642107ea8420fd10841da21083e442107488420fdcc841fb19083f532107e86420fdd4041fb28083f550107e8a020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998df94b31f7296636e52cc6faa598fb54b31b6a9663ef42cc7d88598fdd0731fa20e637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31bf29463ee528c6dca518df54a31f6a94636d528c7de8518fb10a31bf28c63f7418c7e88318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898dfd4931be29263ef424c7d88498fdd0531fa20a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831f7a1063ec420c6fca218fdd0431fa20863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fbd0b21f621643ef32c87d86590fdd0721fa20e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887de8510fb10a21f719443ed32886fca310fdd0621fa20c43f731887e86310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21bf29a437d53486f8a690fbd0921f621243ef32487d86490fdd0521fa20a43f731487e86290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821f7a1043ec42087dc6410fb4c821bf28843f741087e88210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d03de85a07b10b40bf28e817d51d03ee83a07d10740beaa4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5207bd0a40df21481bc42903d885206b10a40bf28c81f651902eca3205f54640faa8c817551903ee83206f90640de20c81f4419036883205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40dfa1a81bd43502fea4a07bd4940b7a92817c52503d8a4a05b14940f7a1281ec42502fea2a07dd4540bba8a817c51503e8a2a05d14540fba0a81f441503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4207bd0840df21081bc42103d884206b10840bf288817d51103ee82206f90440de20881f4411036882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf29
  | 2 => 0x2024008100000300100b0000280400500c01400002046004020000000280100100400c150030000000000d07201002000000004068090140000000f02001400000000002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf29487ee5290edca521df54a43f6a94876d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1fdd4543bba8a877c5150fe8a2a1dd14543bfa8287fb5050ef6a0a1df14143fc28287785050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42bf28e857d51d0afca1a15f54342f7a9e85ee53d0bdaa7a17b14f42f7a1e85ee43d0bda87a17b10f42f7a8e85ee51d0bdaa3a17b14742f7a8685ee50d0bdaa1a17b14342beaa4857e5390afaa7216fd0e42dea1c857e5290adca5216fd0a42f7a14857e5190beca3215d94642bea8c85f55190aeaa3215f94242bea84857f5350af8a6a17bd0942df212857f5150beea2a15dd4542be28a85f45150ae8a2a15fd4142be282857e5410afca6215f54c42dfa1885bd4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0217b95042b72a085ae5410bdea6217b94c42f6a9885ec5310bde86216bd0c42f721885ed4310b5a86217b10c42f7a8885ee5110bdaa2217b14442f7a8085ee5010bdaa0217b14042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332f7a1665ec42ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f7a1465ec428cbbe65197bcca32bf28c65f6518caeca3195f54632faa8c6575518cafca1195f54232bfaa2657e544cafaa8995f15132f7a1265ec424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41f7a1683ec42d06fca1a0df54341fba9e83f653d07eaa7a0fd14f41fba1e83f643d07ea87a0fd10f41fba9683f652d07eaa5a0fd14b41fba1683e742d07ec85a0fd50b41fa21683e442d07ee65a0fd8cb41fa99683f432d07eea1a0fd94341faa8683f450d06faa920df94e41bea9c83bf439077a8720df94a41f7294836e52906faa520fb54a41b6a9483ef429077c8520ef10a41f621483ac42906fca320dd94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0fbd4941b7a92837c52507d8a4a0db14941f7a1283ec42507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083e
  | 3 => 0x4f0003cc0ec833400087dd560006608dc0d0e12cea982d28428c898230a71b6d9c000af000000002c1000574691076441956313a00058549b160fa7140004e53e5fcafb5d172179019830140013b2e11fc830f4b0c166c84fa8b560cd089a96d39e0018e1093ae0006d0c5586635b48dd0d4085229456ae744c701f4c0000252832444b401b5044e0000000066a4999f1ea5746d8e9000000785a5a1b53037d0483700094107a0e40843118359426b9535a546f04fdbb2a21a24dc4e18f0002f42da903fa000f181661e51d7da363f88a0c90962c0130f58a30789209412a40a001b20660009e833b482269f4cb287238214ba35f27a26d2c2ad68c52cbba2f33e954298493a8db56b02b03a9004ead956277800302000d0cf9372374b8c002a9188000000003c82e00000000066c5e0004a6cacaf1945aebe0ab3665503704a9b2578088000d824a000070000ae455940071340002b1e01d0718c40ec0d247c0014d0c26656d0004bcd391c032000630000001c464cb61d50000996a2065faa3da09b44f8d248516466c8a5119404e450d7a00024862cbb1b852cba9829293b6b10419cc53a0ccd21102920fcf6800554004002866d4dbcc8a8b0009048c9be64a0a5441f6000000000000006b103aee4d2861848000006bdaaa1e156d4c778a10000652fb0d25e92559abe10cc2c012b449cd28000a45b83a84a224030854d31fe000000000006ee1ac0002337ab145f91645458c988c705013c9e1216024e0409cb2848d0cd1fb160155210b244a1c583b3d54e2e993800442a44640be5ea5643c92b1a61f1338005bcbadb610d5b0618e827319e108d197c00098d590f6402964000e55f817d8d80049e2d1930e9010448ee00000005c00000180000002974560012907e0000019e00000010c8026f53cb21a8800672001602e90966d40036115ac64b732a3ca61daf00f00200c0c8050010020100000e0100000080c0000140b00000200c05802000014008000000540000701e000008070120100100e0060000380402c00c0001e00a018008010080040280c0000240982f03a0040f8210020481e0080940480100a0040000201c00e03c088000000040204c00200c05000002004008060420200000000c00c0700000001c0200000013c0280a00e0040000401c0100480100800402002000000000000180040380100802800803070040130010080040003301a018028000060480202200000c040010000400281300a000000100180300480100206800000004004040010020200680e0120140000500203800800008050098040020080080c0080240001e0000182c80300001c018010020100280d03c00006009008034000030140000000600c0440300100c160000070460040480d01800c018180020cc0080201200c0080003a000028090
  | 4 => 0x531e24f6cfcd81f122e728d482a17685d8534d556b91768641248f9739f80b882c062b60b08e4ba82c50a5601cb3b0ec22c4b800140d609f044000c687197e0e6b8136170304000b428c2285994526800093023800204481188e71aa001388005fc5e48708a234048f42f3648329580870009fc61000314b34002104b40e12e8a96620001735a182be4791d81e07cc4120a3a600037834000b44660000a000000000000b4846000000000ab800378000001623e80000000068e2b89a2663445f4b485d5928eca09512b46e567a160003980002d1920010d0005aa759653751320d93709f6d062413b1248c40cf78745723b57794e380411b823300000028b736686b55f848610c44aa3446300500024a2de9100011e0005ecca9c42d61e15225c06aa040027439ab994490b2e2000002cc69e704ee9800000000008f6b8bfc31b62222820c20a5110104a802412232d819c20008b189ab53563583d0f111ab08e1939294000b981b040bd80986d6744b11ea623543b817b71038af4310fa21e684683633926c5401c716e000000930ea8c95b9a8000000a997a6ca9d4001274f09a96d9ee0003cc000002a4888189f00000000013b000520003234ee0000000000065d1a8b61f853c001ec01e338982026dc001bc8005e26819780051a001873290001dc00000236554000f536e9e4b2b3363a8b42903059c4d8cf34c30a261578005c4990809183ce570e721f04a76461a4708a0011d0a80000011fb2c0000005129c4860008eb2e35c0002021c3fe00002acb11c2b14d1bf528c7d6e97201a6cc390680223ece427e3be694ceaa52f02106b8e4600ab92d8545a00787c2994a28497bb104c23518f1bb0748b89936b4e0a3858b041e86042c83e320aed96a560f6d80370fd00cd49412b83302419bb320fe3350cb54112a81089054da420048000000012680024695d6395b670180998de478994b50d9000bc0002925423dc970005a6ba0758000000401ea205d80018a80009a000003173b40014a800000d595180068a02c7f9f941a1c0a23205367e90024b1008758a2f26b60547c800298380360aa428dd0002fa34eb7cce0c600
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x520082ac6448020b318d20082e46148020d9545200827b65480209798f54c425d63d53109b98b54c426d62d53109bd8954c426c62553108f99353c423d64d4f109b98b53c426d62d4f108f99253c423d6494f109b98a53c426d6294f108f99352c423d64d4b109798f52c425d63d4b10cb95042c432d5410b10cd95041c43355410710e910841c42e5628c710ad19121c436452487109b98b548426d62d52109bd89548426c62552109bd89538426c6254e108f990538423d6414e109b988538426d6214e108f993528423d64d4a10cb950428432d5410a10cd95341843345410610e910841842b664cc610b998b318436752086109b98b544426d62d5110cb98b544432d62d5110cd587544423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109dd85544427461151108f994544432f6215110cb18854443376115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b18953442776154d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49109b993524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c53149109b990524436561149109b997424426c65d0910cbd53424432c54d0910d3d4f424434c53d09109b994424426c6510910cbd50424432c5410910d3d4c424434c53109109d997414433454d0510d5d4f414435453d0510d9d4b414436452d0510cdd5041443345410510d5d4c41443545310510d9d4841443645210510e91084144276658c510cd1523144354538c510b958a3144364528c5109d1953144334544c510d514d3144364524c5109d99621443345488510d514e214436452885109d19521442b46448510cd15121443545348510d914921443345484110d514e104436452841109b98b540426d62d50109d987540426f62550109b189540427761550109798c540425d63150109b988540426d62150109b98b530426d62d4c108f990530423d6414c109b988530426d6214c109d984530426d65948109b992520423f64548108f19152042ac6454810cbd91520426c6454810cb191520422c6454810d9185520426e62148109d984520426f65d08109b597420426f65108109b594420432f5410810cb150420436652d0410d954b41042756510410cd95041043665210410d954841043a442104109d59731042b664cc410b998b310436552cc4109d5943104365520c4109d597210436552c84109d59421043655208410d954b100427965840109dd9510042b46444010b518d10042e46244010d9549100427b6544010
  | 1 => 0xc2766494430d9d0a510c3644294430cd951510c3355454430d9949510c36552544309d191510c3674254430d9109510c27765d04309d597410c33654d0430cd553410c36652d0430d954b410c27765104309d594410c3365410430cd550410c3974310430d9948410c3655210430e9108410c2ce628c430d5546310c33954d0030e6d0f400c2796510030e610c400c3a84210030ec104400c25f654c030a7191300c2cc624c030b5185300c27b654c030ae191300c25e63d53209758f54c827661d53209d58754c827761553209d18554c823e64d4f208f59353c827661d4f209d58753c823e6494f208f59253c82766194f209d58653c832e5410b20cb55042c82e5618cb20cd95041c83355410720e910841c82ac64487209d987548827561d52209dd85548827461552209dd8553882746154e208f990538823d6414e209d98453882756114e20cb953428832c5410a20ab99332882e661cca20cd95041883355410620e9108418827661d51209d587544832d62d5120cd987544833561d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551209b188544823e6515120cbd8854483376115120cd184544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d20d3588534826e65d0920cb153424834f53d0920d314f424832f5410920cb150424834f5310920d314c424826e658c920cb152324834c538c920b9586324826c654c920cb151324834c534c920cdd53514833454d4520d5d4f514835453d45209d993514836742d4520d910b51483375414520cd15051483575314520d514c51482766414520d9d0851483644214520d98c8514836532145209d997414827465d0520cdd53414833454d0520d5d4f414835453d05209d99441482746510520cdd5041483345410520d5d4c41483545310520e9108414826e65c8520cb153214834c53c8520d914721482ac6448520cb151214834c5348520d9145214832c5488120d314e204836451881209b98b540827661d50209d587540826f62550209dd85540827461550209798c540825d63150209d984540827561150209d987530827561d4c208f990530823d6414c209b98853082766114c209d584530826d6510820cb950420826d65cc820ab99332082e661cc8209b59432082766494420d9d0a510836442944208fd91510823c6454420ad191510833764544209d191510833464544208d19151083674254420d910951083673254420d90c9510827765d04209d597410827765104209d59441083375410420cd15041083a442104209b59621083655188420d9544210836551c80209bd9
  | 2 => 0x5214540cdd0c51503354314540d9d08515036442145409d997415035753d0540d514f415036752d0540d914b41502766510540d5d4c41503545310540d9d4841503645210540e9108415035853d0140c714e405032c5290140cd146405026f6254c409b18953102776154c409d185531023d6590c40ab98a43102b66190c409dd8552102746154840ab98a42102b66190840cb54c42103aa6010840ea580421032c42944409bd89511026c6254440e910b41102ae6290440ad98641103a74210440e910841103355310440cd94841103b26010440ec580411032c4294040cd10650103a84290040ec106401023f6550040a718d40102ac6250040ad185401027b6550040b618d401026e62d53309b58b54cc27661d53309d58754cc26f62553309b18954cc27761553309d18554cc2766194b309d58652cc32e5410b30cb55042cc26e62947309b58a51cc3365410730cd55041cc3a44210730ea10840cc3b041103309b98b548c26d62d52309d987548c27561d52309bd89548c26c62552309dd85548c27461552308fd91528c23c6454a309dd85528c2746154a30cbd50428c32c5410a30e3d0c428c2d6618ca308fd91518c23c64546309bd89518c26c6254630cdd50418c3345410630e5d0c418c3a44210630b398a318c26e62d51309b58b544c27661d51309d587544c32e62d5130cb58b544c33661d5130cd587544c23e64951309b98a544c26d62951309d986544c275619513097d8d544c26f62551309b189544c27761551309d185544c27b60551308f994544c32f6215130cb188544c3376115130cd184544c32f54d4930cb153524c26e64d4930cbd50524c32c54149309b990524c26e65d09309b197424c32f54d0930cb153424c26e65109309b194424c32f5410930cb150424c33754d4530cd153514c36752d4530d914b514c27664d4530d9d0b514c36442d4530cdd50514c3345414530d9d48514c36452145309d990514c3674214530d9108514c27665d05309d197414c33754d0530cd153414c36752d0530d914b414c27665105309d194414c3375410530cd150414c3675210530d9148414c3a44210530ce153304c31c548c130d314a304c354518c1309b98b540c26d62d50309d987540c27561d50308f596540c32f6295030cb18a540c3376195030cd186540c26f62550309b189540c27761550309d185540c31c6355030cbd89540c32c6255030cdd85540c3346155030ce181540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30cb952520c32d54948309b992520c32e5454830cb551520c26c64548309bd97420c26d65d0830cb953420c32d54d08309bd94420c26d6510830cb950420c32d5410830e3d0c420c34d528c830b5986320c3365494430cd552510c3665294430d954a510
  | 3 => 0x1319e181544c72f5410931cb150424c67665d0531cd153414c6d663d0531cd950414c7a44210531ad993314c6e662cc5319b988504c66d62141319b98b540c66d62d50319d987540c66f62550319b189540c63e6494c318f592530c72e5410831cb550420c6756510431cd950410c7355410431b558c410c7a44210431b958a310c65f654c4319dd95310c63f64540318f191500c66f62540319b189500c65e63153219758c54c863e6414f218f59053c872e5410b21cb55042c86ae64ccb21b998732c873654d0721cd15041c87a44210721b958a31c865e63152219758c548863e6414e218f590538872e54d0a21cb15042886e5618ca21cd95041887355410621e910841886b664cc621b998b318872d62d5121cd587544863e64951219bd89544867761551218f994544872f6215121cdd84544863e6494d218f592534866d6294d219d586534863f6454d218f191534867b6054d219e181534866e65d0921cb15342486e661d0921cbd50424872c54109219b99732486ae64cc921cb15332486e661cc9219b994324872c540c9219d997414873454d0521b998b41487375410521cd15041487a442105219d99731486b664cc521cd15331486e662cc5219d9943148734540c521cd153214872c54885219b98b540867661d50219b98b530867661d4c218f992530863d6494c219b594420872e5410821b9584420866d658c821b9586320866f654c8219d59441087365410421b958841087a442104219d59631086e5628c4219dd9531086e562884219bd9521086ac64484219dd9521086b46448421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121087665448421d915121086e76348421b958d21087665348421d914d21086e460484218fd91500863c645402197d8d500865c6354021d9485500866e6294f409b58a53d02766194f409d58653d02b86050f409d98652d02756194b409b98a51d026d6294740e910841d02ae6290e40ad98643902b66190a40cb54842902ad6510a40cb594429032d5310a40cb10a51903665294640d954a51903a44294640d9d0a51903364294640cd10a51903644294640c910a51903665254640d954951903a44254640d9d0951903644254640d994b419036552d0640e910b41902ae6290640cb94a419032e5210640cd54441903665210640d954841903a74210640e910841902b56510640cd59441903355310640cd94841903a65210640c994841903a552106408f997435031c53d0d40c714d43502b86050d40d3d4f525034c53d4940d3d4c525034c5314940cbd0c525032d43149409b997425034f53d0940d314f425026e6510940d3d4c425034c5310940d5d4f515035453d4540d9d4b515036452d4540d9d0b515036442d4540d5d4c51503545314540d9d485150364
  | 4 => 0xb54c429076652d0641d954b419072c42942419b997425066e6510941d9d4b415076452d0541cb14a415066e6294c419b58a53106ac6250c41add8543106b86050c41ab98a42106b56190841cb54c42107a66110841e9584421072c4294441b998a41106e56290441e910a411063f6550441ab18941106776550441b9d8941106e46250441e9109411072c429404197d8d501065c63540419bd89501066c6254041cd99254106b56395041ad98a54106b66095041b998b53106e562d4c41b998a53106e56294c41d554c531079653d0c41e554f43106b662d0c41ad98343106756590c41ad59243106e66290c41b958a43106776550c41b9d8943106e46250c41bcd8143106f06050c41add9543107376550c41e5d8d43107a76250c41ad18943107a46250c41a918943107b36050c41ad18143107b06050c41ac18143106b66410c41b598f52106d563d4841d9548521076654d0841e995342107a743d0841e950f42106756590841b998a42106b56590841cd59642106b56390841ad98a42106a66290841ad98242106776550841e950842106b56310841ad98842107a66210841e994842107a55210841ad98042106e66410841e999042107665410841e995042107a74310841e990c42107a54310841e910c42107a76510841e999442107a56510841e919442107a76310841e998c42107a56310841e918c42107a75310841e994c42107a55310841e914c42107a76010841e998042107a56010841e9180421067665cc8419d59732106b664cc841ad59332107a442cc8419d9963210675658c841add9232106b4648c841e910a32106b7644c841ad19132107a4424c841ad99032106b5640c841e910832107a442d4041e910a50106d76354041b518d50106e76254041b918950107a44254041b598c50106d56314041b998850106e56214041e9108501066e62d53319b58b54cc72f6295331cb18a54cc73761953319bd8954cc66c6255331cbd8954cc72c6255331cdd8554cc66e62153319b58854cc72e5494b31cb55252cc66e6494b31d958652cc72e5454b31cb55152cc66c6454b319bd9742cc66d65d0b31cb95342cc72d54d0b319bd9442cc66d6510b31cb95042cc72d5410b31cd95341cc76652d0731d954b41cc7365410731cd55041cc7665210731d954841cc7a442107319b98b548c66d62d52319e983548c67960d52319bd89548c66c62552319b988548c66d62152319b992528c63f6454a318f191528c6ac6454a31cbd91528c66c6454a31cb191528c62c6454a31d9185528c66f65d0a319b597428c66f6510a319b594428c72f5410a31cb150428c76652d0631d954b418c7365410631d9948418c7655210631e9108418c6b664cc631b998b318c76552cc6319b98b544c66d62d51319bd89544c66c62551319dd85544c67b6055
  | 5 => 0x53d0ae76154f42b918553d0ae66114f42b958453d0ae66190f42b958643d0ae76150f42b918543d0aeb6050f42ba18143d0b8d4310f42d9d4651d0ace6314742b358c51d0ace63d4342b358f50d0ae661d4342b958750d0ae66194342b958650d0b1e5350e42ad1854390ab86050e42cdd0e5190b354394642d9d0a5190b674254642d9d0b5150b674214542cd9085150a766194c429d5865310aaf6250c42ad1854310ab86050c42b99864210ae561908428fd954210ab461508429bd954210ae76150842b91854210a5f63540429718d5010a7761540429d1855010b2e6495042ab58e5410aae6195042ab9825410ae661d4c42b95875310ae66194c42b95865310b4d5314c42e394f4310b8d53d0c42ab9874310aae60d0c429b5964310aad6490c42b99864310ae56190c429bd954310ae76150c42b91854310aeb6050c42ba1814310aaf6550c42cbd954310b8f6350c42e9d854310aac6150c42e91854310aa46150c42ead814310aac6050c42ea1814310aa86050c42ab9904310ace63d4442b358f5110b655114442b3d8d5010acc6354042b9d855010ae46154042b398c5010acd6314042b99845010ae561140429d98754cca7561d5332cbd8a54ccb376195332cd18654cca7761553329d18554ccb2f6255332cdd8554ccb3461553329d98454cca756115332cb95342ccb2e5410b32cb55042ccb365494732cd55251cca766494732d9d0a51ccb644294732cd95151ccb3554547329d19151ccb674254732d910951cca7661d52329d587548ca7a60d52329e583548ca7761552329d185548ca7661152329d584548cb2e5410a32ab993328cae661cca329d992518cb674294632d910a518ca3f64546328f191518cab46454632cdd91518ca746454632cd191518ca346454632d9d09518cb644254632d9cc9518ca7661d51329d587544ca6f62551329dd85544ca7461551329ed81544ca7860551329b997424cb2c54d0932b398f424cb2e5410932ab993324cae661cc9329d984504ca7561141329b98b540ca7661d50329d587540ca7761550329d185540ca3e6494c328f592530ca6d6510832cb950420cb2d5410832b358c420cae5618c83297d95320ca6f654c8328fd91500ca3c64540329dd85500ca7461540329bd8953d066c6254f419b98a50d066d6294341d5d4e53d06e76254f41b918953d06e66214f41b958853d06e66290f41b958a43d06e76250f41b918943d06f36050f41bc18143d07954310f41d9d4a52d06d66314b41b558c52d07a66410b41e9d0c42d07a54310b419d99732d067565ccb41ad99332d06b564ccb419d99632d0675658cb41b598f50d06d563d4341b998b50d06e562d4341b998a50d06e56294341c794d43906ac6250e41ae181439072f4394a41cb50e529072d5210a41ab594429072d6510a41c
  | 6 => 0x16e0d400017b8d50001792710c59f982b9a687f0188868000878dca5f8000000a99580bf8930ef00005d8529cd00027582900f98d0002900e51590001b98b589d8608002892158000470000001c69dc82307b89685f0001cb21190c1fa800244977898a1e0f21481ad962a400ab00e22b19fa0e91b8f1a2521d08a0d78428001338d880013e81c8a00110ee1690000831d811906d0002398a10bd23200017f9bf84c22684b29b2701308e6a0f94d2581db2160c400000017e23c1729820018010460800080f006010020030060d4000070020000c85402e0080080600c0040700300401c068010000340000000000000003008000020040000001680200200c0281701e0000100500204c168000020180b802004044148010180000000004603400000002014000020000104180102214c00806002018030090020080500300008c1001100004802002008000040060560280202405e0000000003400c0b80a042034030200540400080e000024318150020680180300a0981285700a0000081400404c000000120041b80200200c030130020000000402e04010804008000028000580a00401900e0300200000a0000101106602c040000020000000500c00812801012008058000020140880a01c0080580d02a0100180201e0100380100002c0800100e0080680500602c0000103a0280000203e0100200401400404000006000028010320380001b0140140603d02801000801006000010190020040000003001c0300401c0040000b0060000580b0080a0010070040cc0000000e0240180300407022810016000000290080042d80400005c000010020bc000040000040001f00a000000020100700d00000e0042200e00e010000000060140080300c00c000010080380080100003c000020120041a80200c00c0300400e000000120040000680001e0000300002c15800801030000008230020000180300a00c1680000401c00008026000000010040100e80602e00002802002048030030020040301000002c0080000e01c0480c0080201b00e0000000480d0080181e80000e0900e00b000004090040020001d0000000881880f00c0000182004402801800016028000009dd8552d0e746154b439bd8951d0e6c62547439b98a50d0e6d62943439d98650d0e756194343cbd0e5290f665294643d954a5190f374394643d99495190f655254643ab98a4350eb66190d43d9d4b5150f6452d4543d9d485150f645214543dad4b5050f6852d4143dcd475050f7051d4143dad485050f685214143dcd445050f705114143d6d0c5050f3a43141438fd954310eb86050c4397d954310ed86050c439d9865210e7561948439b98a5110e6d62944439bd895010e6c62540439dd855010e7461540439dd8553d0a746154f429d98650d0a756194342d3d4e
  | 7 => 0x1da9ce87226d0b800000023000018180000000000022f17b1249aa10783f0001ba95589b88700025c00020a88500014920592712a00000014310901219883488e19c9ce16e9839710000e28400c680000005e80018695080029a19f1d10882120e884c8f007a80007680019e0000000000510d800016b1b10000002228000ed80000000005a1e080003d021165067954a25a7e27901403e0b78b421400003f8001e30130002260001749e58990809a28ec8570000000000731ea0741b519617c28026a06a19389582d9c0a179898059698b18f714ea8298a91f8598c4a20a471520df00481a8e8255a1a0d211319491a163a6a93c170a61209a6c141176a021299402898001098000002530001f892e92621ba749b08081f61b588b80016790c8000fe03898e0000000000001b006612a8001438f60811828ac8f08000b62860b718613500000f1a89e3a3a13a163233a2d9b28089951d791b1138e780000025d00022c96615f17c95680316d8001d9068112a2c1cd80004090b1bca350e58d081a1bc2271f4a3b1a605d0a3a6c8dd8baa13077a981bf1a39dfa4c9bb881a5785b1af03705324e0cd19b9d01fe8070e20001c328ea8b18c00009ca2802ea9729d0ab9b6923a781c28000700cf94c8000ce1a21e12061f400028f80013c9fd00007195d83a8f38000f90fc09e0bc0000000251e20840f98c804128800009a24a00012c15b8ea0000100199210508001ef8360798090480f68492832838c907e8c70d30000379979850548c1122000236206a9d99e88a80029128d0000a68738889000620bb1020750000168001fb1a115a00010d0001a9a4100d1ae91e8618000001e29e884200010f0ea8488860119760000248591b723d9cf9de17a19280002fa138009458241a024b80014b1d42969488000000d681b1c91c78b48a222b9b6082853829a299d1a7c27c9fe1780c510889808fa009369291c580018ba788000be81b80000014d96a2568000001cb9058ff1429da16803d9f09ac97f13f9992309920002750b28001d29789c000000009f2630001d68000000000001dd9a480028200000011d8b6a7d27a8c024f9f300000000025e1bd1060579848fd9018eea14a38a089830dea428278099318890c319a1ff8ad1b7a98957999a0115a8e003180c0db2680a4994021a4c1d39a41fb8330b3a54115a2889421a92586715187fa5a87b03903e8611511029980f806d8f59b199d94c035934a6f9f522397213124327f147897a458a90cc82b1dea941648000a40000000000079910271619b81bb1c80912048469eb98b017a0d09aa368b098126b1110000559cc0001f91540000002888000000322390261dd1c3a738eb00003380002a000094800000043a8400000000000000000026897ea0b2358001e812323b8b880004510700
  | 8 => 0x6c80019b1050020041b90ba0501250001a805f91c80007920796f8000aa9550152909b218f90809087c06e9399f79620bf00013f1140898bd800287a63a960f880025887080ca9317585a80000000005209e80024d13b17a88da7600015e800210056944a2428a1361df0c3a042310b99ed2919180050c228525004d27423780012787284f0019f21600a812da0e25b01f085921a8d95323f8be17307c96c11724d86c89fa2d08c82c80683a0ec0010b10ae04e8f41a90af08b099a72a9c18f00018025da441a587e0002598b52659799528901149e922a1a79dc12b14f20700016ba668c786b97402695618827e92ba408000c289296101ea9aa769e70459fc9eb1378ce84996683b9208518171372481109201179f3a560aa10da7b8561ec9cf09d09607103b208262a10a8c8328a7a511359a0a6e80000014a06a81e20ba0f11c10420d91a91e1ca24905827080b916942251a5c93d84f8a29ae229126a978a50b32591e982a9771e40da87d0000eb80010112d078800000220232a479a50650772620db8001aaa7a14f9288fa1461b419719d0ca8a72419e786f8340002460002110449d093895700022482e1340a8a7180e9c10a18a303c0f30038a5a94a6418e8000001d705b8000d00001fd80021715c00000000011880028e00009c1a300000000000026e187000031191a218bc80016580025b8000002811672660748000000000d29b8a7787826d97195d0dd16d26080001c00025523a8000d5a809ea97380002d1d60da2670002868002468ac1048002028688002770d9243a1880b2921d31441fc0918cd9d98138cc02c14500020c1030fd00017d23c80012f8e404e1f69e628b90f8161be80023424200022e0c08839ba0fc9501ab1d590e2181ac14084b8f508d1f189508493225728f09b0d629ca372849c215f8f4a319e4893a1e9c70d9a9994b897185a72020a49a3328c1aba2e839a7da488b925a0000921ee98a1468c98001b30001c188f1fa11623e08206595b0001888000760002509e680000000001d06b0ffa3ea1ca1b2650001c880d93b800000000000295a9916f15980024f00000004314984a03514aa030af97525398c9300668ae802a000001a185c00002000001d9c41e18629b480019a80000016aa85a8a8e71be05e0301228de1b381f90a2601a70c88648ad8149d506913d1ee06e25f2169e513298921c2278f79118e1a3d12e21508c17da92a5e8d3863a7f8461c987a0cb1cc9330bba6f25280a8288dc0a624522a98da6b9ed9c60cf2211ca9ff13aa81a199068fb8f115394e03c9908c18e61d484410080a2939f11f295882f25484d9f803092c910212960987841a0386f0550d1980a6790a8002190000a08588000698000e4a1f24e8ed13921f8f2a4a9d20001240d49931e00280df8e98001bd9f700010ba09
  | 9 => 0x229af82598411519c0128fa9958d70ca0000478cba951ef1ad0000061688c622f8181f5a69a2200011226913e0e30000ef8368190b21db80026482220506400000006300014188ea0c80011d0382732520e08002348000fe87d80023f12829b8e101084aa1d90e95e0000fb0e387592f27991f23816415c86c00005c9382231ec0001198000001c5015a7b060023a4b0001701968000e920a2871f00000d11d89900b01c4a61a018000540801471039
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20ca6761095010743b1884a8083a118c4254041d0cc6210a020e856310850106923a2c329663491c95410731a48e8a908398d277510841cc692ba88420e6389dc46454a31c48e2322a518e2464185528c695386a821463491d152d0631a48e8a908318d2775108418c6923a2a598c638999152cc631858e8b10a098d2472550410c712b288420863a158c4210431948e8b146218d157315041c86523a2c518e43435cc5410a21948e8b0c6510d0e73d88544868b39ec22a2438915261d092185eec2a66490e245498732487122a4c5a0a430ddd854cc521c48a93166290ca47458632086523a2c518843299d26448421c4eca3224210e27751912108712324a890843891905448421948e8b1a4210ce07058d21086333b4a690843499d25348421c48c929a4210e246414d21086923a242a8043891912154021c88c690aa010d287050c52502983828628a81499d44210540c4cca21082a07075310841503822988420a81491c55310840b10e6b0084205247254c41102c839ac0208810d1d16194b30a48e2aa0859842c7458a51cc292392a820e61499c75410a30a4ce5aa0831862662987544c312310c22a261499c75410930c4cc8216a29852672d50414c2933a6a420a61499d44210530a48ea210829862665108414c3123288420a61891886195030c48c430aa81861863181540c314310c0aa0618c1846055030a48e2aa0841860d65d0c420c31232084a8861491c95410430c2acba18821852474548410c293ba88420861495d44210430c4eca210821862565108410c314b2884200618c5944110030a48e2aa085904a47458632c821b3a6c2a9c41499c75410920948e8b0c649062454586324832229ac3192418999042d4520c4cca2108290624651084148383a988420a41c114c4210520c18c829a429062464145214821a3a2c3a984189dc86454420c48e4322a21062464d09510831232084a8841499d33254420c48c9992a210624640c95108293396a820841455cc5410420c4eca21082105247454621082923a2a210841491d151c8020a48e8a8a401062464545200832231aa290041491c95410710948e8b1463886246414921c42173a6c4a9c21499d35208610a48e8b08a488524711504244293396a820a21499d35210510a4cea2108288524751084144383a988420a21c114c4210510948e8b1462886245458a314432229ac518a21195d8528c510868ec2a242886146414d2144312320a490a210b1d162d4c10c4ee2322a408624711915204312320c2a9021499c7541081085aec2a0840850d7315042042923a2a5a0821491d15210410a4eea21082084677654b31042923a2a5988218999152cc410a48e8a9062085247454b21042923a2a410821491d152c40108c8eca922008524745491004312322a4880219118d5244010
  | 1 => 0x190407254b749831241e0ec9351178e0850007432880033c600100248ce005fb38fe1b638383c000027c7e00089280021000000000002dc009e538012a00001180000000016498002c09e00461e936db2d80000510829400002c340c6001f2703e274b9b186414880078d60000156000100c5c154380146c50014ce84400199665704b68fcc60d1751e2337000c0382680000002ca58d43506ac532e1340006400469c53445451dc8008099cc181400305ae830b01000001a22dc4a60b950da0f000a50ca00034c4c0000000000000001a8cb311ec0e00002400081212d99ab500330007c448007a390312d3a36001f46e0000001480a0020000de141685ee050938161c0c328f22d5637c8edc32ae508d84a2a97ca815b00ea5619b257abb3488800d53080170c8003104805280951cc26880178d956800923b001bc000000349742a358b0aaaf2e0e904525a10c245f57000000382c0401058280002008240406008300e060d0200400000101e0502800000c038201209008400805000000a00008000c09000101003018080a090002c08020000c0605040040000000040008048002a040052a7290c5050e9938c8628287621c14310f42c34a630287215307050e5190a5238ac72a085299c6609504294ce330686216a061d814310b15b28c0a1885a2d8c6050c42d46c230286216a0611814310a9238aa821665891904254732c4ee4322a31962472191518cb1232684a8c65499d33254632c48c9992a31943474584504ca9238aa821065291d1618c832b20e0a1887a0da07050c42d070d298c0a1c834a1c14394a41948e4b1ca820ca6729825410653394c1a1883a818b6050c41c66ca3028620e93631814310751b10c0a1883a81886050c41b40e0a1e8420ca57690c4210692bac862108368dc14310841b40e0a188420d8673d9442106c2b9eca21083619ce6510841b0ae73288420d2575d8c4210692bacc621083a158c631084194aed2988420f055314c4210693baac02108361dcd6010841b08e6b008420d867318042106c2b98c0210838999442cc841c4aca2166420cb270d9232107133288519083295d8420c841b0ae621064
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x2ac4808cc0010006280d480e21d20a0683dc86454632a0683dc46454a31a0683dd46448421827871925348421c047418d2154021c047414d618c920a0683dc86454420c047418d5148020c047414d628c510824845d8528c510a0683dc464548108248799152cc410824871915244010c047418d5244010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
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
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (788+((h/14+packedAt s3K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s3K5 (27286+((h/296+packedAt s3K5 (24030+(h % 296)*11) 11) % 1069)*11) 11
  | 4 => packedAt s3K4 (55826+((h/446+packedAt s3K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s3K3 (11798+((h/75+packedAt s3K3 (11123+(h % 75)*9) 9) % 300)*9) 9
  | 2 => packedAt s3K2 (860+((h/4+packedAt s3K2 (840+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffff81ffffffffffffff0fffff
  | 1 => 0xfc07f03ffe03f80ffe0f83f03ff81f80f4c7cc
  | 2 => 0x7ffc0fffc000ffff003ffc0ffe000f8f8f0
  | 4 => 0xfff80000fffffffffffffc0000ffffffff00ff
  | 5 => 0xffffffff0000000fffffffffff000000ffff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1430108202489040805284b14518a2a6015b55
  | 1 => 0x5952a58c643922d79605a155366a9b0a74c5cc
  | 2 => 0x52a4c316a89074ebaab0426d94b6ca14b8e8f0
  | 4 => 0x60c68a28d122468d4d29680820c71c58de00aa
  | 5 => 0x83070c30e1c3870e71ce738e38041060efb600
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeaa8a8aaaa0000eaeaa8a8aaaa0000eaeaa8a8aaaa0000eaeaa8a8aaaa0000eaeaa8a8aaaa0000eaeaa8a8aaaa0000eaeaa8a8aaaa0000eaeaa8a8aaaa0000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37427
namespace PEqualNP.Outside.L_meta_37427
open PEqualNP.Outside.L_meta_37427.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x9000553000c00012007510b000002b4e0001b4630002503800a3490000106000f2610c9452155000e000164a0cb803c850093e700111a3c02010010c0001100000ff43fe43fd43fc43ff42ef42fe42fd42fc42ec42ff32fe32fd32fc32ff41f741fe41fd41fc41f441ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x6617d52cc3de85987b10b30bf28e617d51cc3ee83987d10730fda0661f840cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5187bd0a30f621461de328c3b865185f94630bea8c61f7418c3e88318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa9261ef524c2dea4985f14930f6292616c524c3de84987b10930bfa8a61f7514c2eea2985f14530fa28a6174514c3ee82987d10530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4187bd0830f621061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861f7410c3e88218778c430ee188617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83ee83907d10720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ef32883d865105f94620bea8c41f741883e883107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f7a1241ec42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483ee82907d10520f790a41ed21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf29041ef42083d884107bcc820f6190417e51083eca2105d94420bea8841f551082eaa2107dd0420fa20841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10f7a1621ec42c43ee83887d10710fb18e21f531c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10f7a1421ec42842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910f7a1221ec42443ee82887d10510fb18a21f531443ec42887d48510fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52043de84087b10810bf28821f741043e882087dcc410fa18821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf421077c8420ef10841f621083ac42106fca220efd0441fb20883bd41107ea8220df94041bea8083f654106eca820ed95041fba9883f653107eaa620fd14c41fba1883b743107ec8620fd50c41daa1883f443107eea420fd94841faa9083f452107ee8420f9d0841fb21083b642107ea8420fd10841da21083e442107488420fdcc841fb19083f532107e86420fdd4041fb28083f550107e8a020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998df94b31f7296636e52cc6faa598fb54b31b6a9663ef42cc7d88598fdd0731fa20e637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31bf29463ee528c6dca518df54a31f6a94636d528c7de8518fb10a31bf28c63f7418c7e88318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898dfd4931be29263ef424c7d88498fdd0531fa20a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831f7a1063ec420c6fca218fdd0431fa20863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fbd0b21f621643ef32c87d86590fdd0721fa20e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887de8510fb10a21f719443ed32886fca310fdd0621fa20c43f731887e86310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21bf29a437d53486f8a690fbd0921f621243ef32487d86490fdd0521fa20a43f731487e86290fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821f7a1043ec42087dc6410fb4c821bf28843f741087e88210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d03de85a07b10b40bf28e817d51d03ee83a07d10740beaa4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5207bd0a40df21481bc42903d885206b10a40bf28c81f651902eca3205f54640faa8c817551903ee83206f90640de20c81f4419036883205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40dfa1a81bd43502fea4a07bd4940b7a92817c52503d8a4a05b14940f7a1281ec42502fea2a07dd4540bba8a817c51503e8a2a05d14540fba0a81f441503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4207bd0840df21081bc42103d884206b10840bf288817d51103ee82206f90440de20881f4411036882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf29
  | 2 => 0xc0400100204801001000008008000000140000100000800006006000008000000000000000000c000030080000000000202808002006048000000140000000400000afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf29487ee5290edca521df54a43f6a94876d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1fdd4543bba8a877c5150fe8a2a1dd14543bfa8287fb5050ef6a0a1df14143fc28287785050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42bf28e857d51d0afca1a15f54342f7a9e85ee53d0bdaa7a17b14f42f7a1e85ee43d0bda87a17b10f42f7a8e85ee51d0bdaa3a17b14742f7a8685ee50d0bdaa1a17b14342beaa4857e5390afaa7216fd0e42dea1c857e5290adca5216fd0a42f7a14857e5190beca3215d94642bea8c85f55190aeaa3215f94242bea84857f5350af8a6a17bd0942df212857f5150beea2a15dd4542be28a85f45150ae8a2a15fd4142be282857e5410afca6215f54c42dfa1885bd4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0217b95042b72a085ae5410bdea6217b94c42f6a9885ec5310bde86216bd0c42f721885ed4310b5a86217b10c42f7a8885ee5110bdaa2217b14442f7a8085ee5010bdaa0217b14042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332f7a1665ec42ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f7a1465ec428cbbe65197bcca32bf28c65f6518caeca3195f54632faa8c6575518cafca1195f54232bfaa2657e544cafaa8995f15132f7a1265ec424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41f7a1683ec42d06fca1a0df54341fba9e83f653d07eaa7a0fd14f41fba1e83f643d07ea87a0fd10f41fba9683f652d07eaa5a0fd14b41fba1683e742d07ec85a0fd50b41fa21683e442d07ee65a0fd8cb41fa99683f432d07eea1a0fd94341faa8683f450d06faa920df94e41bea9c83bf439077a8720df94a41f7294836e52906faa520fb54a41b6a9483ef429077c8520ef10a41f621483ac42906fca320dd94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0fbd4941b7a92837c52507d8a4a0db14941f7a1283ec42507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083e
  | 3 => 0x2000f28bb32a5756f14d0e478487000000000551da000c797c000000000f91881c41998c800000da0ffb370008402721d0006b8002836d84680019004e0000012a000000aa083438b6c00000000000002e5000430000002e6320000e900021912000332000001560002294f9ed000001b312e578b24000000009c01280065227c00000544c208c0000000fcb105e4aa000000000004ac00000000000000000000009f80031e7a41db780006ac258a56ca6f40000039c0017187b5408f4000000000000000013c3f800000582000000000000002d80040a7518b0000000000011e00000000000552b34ef000090b4d2b0545220d83989b00000000000000000002f9000981ba800000000002cb450000b602609e00000102000000000000000000001f000000000006b2000422900008098b80000000000136000000000005f659573ab8000000998000000000d800000d70001b115ed6c00000000000000233c65440018e0202800028d44acb8002006ee000223382d20000019f000dd8ac9380d0670252fc6ba618d784c580b898d8004d61000028400000196800000ab853800000000c6b3f000a8c00182000000d0800000000001963349b80000000000169045000c600000067200000000000001ac3544d2044000000000745ea440000006580000057c000000000000030b000000f308700069cec87e0000000021b000000002595288040000000000000000000000000000000000000000000000017300001818000002254c1d300000000041000000002cf0001d0f58001500000000014c48c001f65d27b0000a933cc48d4a6f1440c175a343fa5a80000000047400000000068bea6a0009e0000002f8000faaa824c020000003f4000002c70ec00000000000000fa0e50fe0019980060a42da897f0006d000029000de4cc00000000000000000000001300306dc0000080300201400002008000008060060040000000a01401800000044090010000240100200600400801000000018010020000180000000002002008018060020000080700000001401001000014038030020300280200200000002004004000030020000080200e0380300500400003800000000010000000000500200c0240000000e0000680100c01401001008004000000060000000000000000807002000008000020000080000401c0200200001001002008008020030020180080100a0080000a00a01800800000024008000020000100000c0040000100a00000000004018010010000000000b0020040100b000000010030000000100e0020080080000c00c000010060040001100000403000004000008000020000080800601000802000000030060040000080b000000008000000000000300800002800002000050000020040080200e00000000006004040010
  | 4 => 0x1a8738000004ed6e800000000cb8000008806200050e26869277286000b21216a6d053f80000075da49b2532d481792d0003ac00020000000000000000005f80047e3040024330e000388531320013191f0009ec000f4000984000d900000000000148af8b3b27344b311a83e36c6990a00d1f87909480034a00178915000000001d8316940732c40000019b097000994a02e849e000001171688ad400004ba8849f0d012851093800000c4190a2e5480000533b1c28e800091138531398b84585d80000054aa798716f39a8bc4591920a6506315011a5b96a9ca0ee828c521715cbd47aaaa27ac4cfc8003dc0000000000082d04a084185601bb35000aed9a1250004916b10d2aa3e0962d83880005d3010007206d80010a68126a5a000000003022f4380002960003c13a8004bc5e43c0000000014e80000000003000538c8c4027c1a22380030f01800000000000000000003220007b24200004c142f71664d1790e429600162a0f12c000000004a46e8001930007c5a12b5282db5751d0238a54000ce00001c00000000000d42b014600000000000744001c355e0009123b6540017304d1b473000000000000c1800000c98ee9a4000001a82411faa38001164a6d3c00014294b7c799fb46c8797b2865e89600580063a000000d5000000000000000018a90f38a0000000068a42401a921d076cf383802c3294086000000136b3a10496c5e0000000008089337e000000000007dc003075620019f137000000a912f5de000fc0c318a7547d970000c900015b00037cda9841c69288daad558d34001ef0046e5978460008347c89256800000059000000248006d4001672ab0007089a8001ba514a10000000006b800318a9c00000000b68008000f4000002ba00000186000000dc0a70d84a80000023c120001b380000044c59229000000002323d000083800228bf8000000000002b85c000578002dc000000000006142540000000023c359fe61a010003632b4b0c0028b0000015b8210320018e0000000e8801be000dc509800000d84000006589312e000000ad9460003c03fce5a972e45ec40b6e0005c4000005420000000051e0016c800000b84000000000001880063e2d9b224b000000dc00002a6ec000005e0275130240de9a0151dc3e686108834000000b0189000a981e0000d2000280ab000001b7a16696000000004ce000760000000000002b000704002330000000033d000d686e266000000900000000b8328004c4a20f818540e1598a1574460cd80000392838001a30000017232807a001a180058411c00000564001448050000011c05f0d80019e2825fa0005f000000000002ed0009b03706d38053c001df1d4a4dab8005dc41995800000001b5b400000011b800000da4290001dcc69643742c689c2ea304e803ca4ab366
  | 5 => 0xd1c2d27203c000b593c0003b416861000570002f300000000000000000000000faa6cd8264640718bbab90000000008800095c00204000001680000000000000020818c6780000000050842000000c0800424000668003ac9140029a69832542800608001451ea0002d4988ac0004e4003560aa0010307000073c001681deb181cabf5ae2610f8220000b0000003548c40000000000088000000001a21082e80000019b000038000004fa00000000358300d9a1a2f00017fb620000010aad1000001238006be000000000000005bae0264dcc002ca6e4cc9018fa60cd180001c28c001af0000004a0000002da000190000000006a00033a000001ad0009440000049c000000000009e4000000007f11f1e2000d28589486aa9e831309000330699610003dc790000120012f8c22cc000de000000bb13f00000092400112222af4000430f81d40000011800000000000be8c931115acc16a0d60004e800000000000000640ce144000580003c5912196c054d3b1031601e4000352ea378e9271000d2085147472888e3b4e1720011500064a000000000005f916a400000000000000000000000024000000004900000000000091863800
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x520082ac6448020b318d20082e46148020d9545200827b65480209798f54c425d63d53109b98b54c426d62d53109bd8954c426c62553108f99353c423d64d4f109b98b53c426d62d4f108f99253c423d6494f109b98a53c426d6294f108f99352c423d64d4b109798f52c425d63d4b10cb95042c432d5410b10cd95041c43355410710e910841c42e5628c710ad19121c436452487109b98b548426d62d52109bd89548426c62552109bd89538426c6254e108f990538423d6414e109b988538426d6214e108f993528423d64d4a10cb950428432d5410a10cd95341843345410610e910841842b664cc610b998b318436752086109b98b544426d62d5110cb98b544432d62d5110cd587544423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109dd85544427461151108f994544432f6215110cb18854443376115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b18953442776154d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49109b993524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c53149109b990524436561149109b997424426c65d0910cbd53424432c54d0910d3d4f424434c53d09109b994424426c6510910cbd50424432c5410910d3d4c424434c53109109d997414433454d0510d5d4f414435453d0510d9d4b414436452d0510cdd5041443345410510d5d4c41443545310510d9d4841443645210510e91084144276658c510cd1523144354538c510b958a3144364528c5109d1953144334544c510d514d3144364524c5109d99621443345488510d514e214436452885109d19521442b46448510cd15121443545348510d914921443345484110d514e104436452841109b98b540426d62d50109d987540426f62550109b189540427761550109798c540425d63150109b988540426d62150109b98b530426d62d4c108f990530423d6414c109b988530426d6214c109d984530426d65948109b992520423f64548108f19152042ac6454810cbd91520426c6454810cb191520422c6454810d9185520426e62148109d984520426f65d08109b597420426f65108109b594420432f5410810cb150420436652d0410d954b41042756510410cd95041043665210410d954841043a442104109d59731042b664cc410b998b310436552cc4109d5943104365520c4109d597210436552c84109d59421043655208410d954b100427965840109dd9510042b46444010b518d10042e46244010d9549100427b6544010
  | 1 => 0xc2766494430d9d0a510c3644294430cd951510c3355454430d9949510c36552544309d191510c3674254430d9109510c27765d04309d597410c33654d0430cd553410c36652d0430d954b410c27765104309d594410c3365410430cd550410c3974310430d9948410c3655210430e9108410c2ce628c430d5546310c33954d0030e6d0f400c2796510030e610c400c3a84210030ec104400c25f654c030a7191300c2cc624c030b5185300c27b654c030ae191300c25e63d53209758f54c827661d53209d58754c827761553209d18554c823e64d4f208f59353c827661d4f209d58753c823e6494f208f59253c82766194f209d58653c832e5410b20cb55042c82e5618cb20cd95041c83355410720e910841c82ac64487209d987548827561d52209dd85548827461552209dd8553882746154e208f990538823d6414e209d98453882756114e20cb953428832c5410a20ab99332882e661cca20cd95041883355410620e9108418827661d51209d587544832d62d5120cd987544833561d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551209b188544823e6515120cbd8854483376115120cd184544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d20d3588534826e65d0920cb153424834f53d0920d314f424832f5410920cb150424834f5310920d314c424826e658c920cb152324834c538c920b9586324826c654c920cb151324834c534c920cdd53514833454d4520d5d4f514835453d45209d993514836742d4520d910b51483375414520cd15051483575314520d514c51482766414520d9d0851483644214520d98c8514836532145209d997414827465d0520cdd53414833454d0520d5d4f414835453d05209d99441482746510520cdd5041483345410520d5d4c41483545310520e9108414826e65c8520cb153214834c53c8520d914721482ac6448520cb151214834c5348520d9145214832c5488120d314e204836451881209b98b540827661d50209d587540826f62550209dd85540827461550209798c540825d63150209d984540827561150209d987530827561d4c208f990530823d6414c209b98853082766114c209d584530826d6510820cb950420826d65cc820ab99332082e661cc8209b59432082766494420d9d0a510836442944208fd91510823c6454420ad191510833764544209d191510833464544208d19151083674254420d910951083673254420d90c9510827765d04209d597410827765104209d59441083375410420cd15041083a442104209b59621083655188420d9544210836551c80209bd9
  | 2 => 0x5214540cdd0c51503354314540d9d08515036442145409d997415035753d0540d514f415036752d0540d914b41502766510540d5d4c41503545310540d9d4841503645210540e9108415035853d0140c714e405032c5290140cd146405026f6254c409b18953102776154c409d185531023d6590c40ab98a43102b66190c409dd8552102746154840ab98a42102b66190840cb54c42103aa6010840ea580421032c42944409bd89511026c6254440e910b41102ae6290440ad98641103a74210440e910841103355310440cd94841103b26010440ec580411032c4294040cd10650103a84290040ec106401023f6550040a718d40102ac6250040ad185401027b6550040b618d401026e62d53309b58b54cc27661d53309d58754cc26f62553309b18954cc27761553309d18554cc2766194b309d58652cc32e5410b30cb55042cc26e62947309b58a51cc3365410730cd55041cc3a44210730ea10840cc3b041103309b98b548c26d62d52309d987548c27561d52309bd89548c26c62552309dd85548c27461552308fd91528c23c6454a309dd85528c2746154a30cbd50428c32c5410a30e3d0c428c2d6618ca308fd91518c23c64546309bd89518c26c6254630cdd50418c3345410630e5d0c418c3a44210630b398a318c26e62d51309b58b544c27661d51309d587544c32e62d5130cb58b544c33661d5130cd587544c23e64951309b98a544c26d62951309d986544c275619513097d8d544c26f62551309b189544c27761551309d185544c27b60551308f994544c32f6215130cb188544c3376115130cd184544c32f54d4930cb153524c26e64d4930cbd50524c32c54149309b990524c26e65d09309b197424c32f54d0930cb153424c26e65109309b194424c32f5410930cb150424c33754d4530cd153514c36752d4530d914b514c27664d4530d9d0b514c36442d4530cdd50514c3345414530d9d48514c36452145309d990514c3674214530d9108514c27665d05309d197414c33754d0530cd153414c36752d0530d914b414c27665105309d194414c3375410530cd150414c3675210530d9148414c3a44210530ce153304c31c548c130d314a304c354518c1309b98b540c26d62d50309d987540c27561d50308f596540c32f6295030cb18a540c3376195030cd186540c26f62550309b189540c27761550309d185540c31c6355030cbd89540c32c6255030cdd85540c3346155030ce181540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30cb952520c32d54948309b992520c32e5454830cb551520c26c64548309bd97420c26d65d0830cb953420c32d54d08309bd94420c26d6510830cb950420c32d5410830e3d0c420c34d528c830b5986320c3365494430cd552510c3665294430d954a510
  | 3 => 0x1319e181544c72f5410931cb150424c67665d0531cd153414c6d663d0531cd950414c7a44210531ad993314c6e662cc5319b988504c66d62141319b98b540c66d62d50319d987540c66f62550319b189540c63e6494c318f592530c72e5410831cb550420c6756510431cd950410c7355410431b558c410c7a44210431b958a310c65f654c4319dd95310c63f64540318f191500c66f62540319b189500c65e63153219758c54c863e6414f218f59053c872e5410b21cb55042c86ae64ccb21b998732c873654d0721cd15041c87a44210721b958a31c865e63152219758c548863e6414e218f590538872e54d0a21cb15042886e5618ca21cd95041887355410621e910841886b664cc621b998b318872d62d5121cd587544863e64951219bd89544867761551218f994544872f6215121cdd84544863e6494d218f592534866d6294d219d586534863f6454d218f191534867b6054d219e181534866e65d0921cb15342486e661d0921cbd50424872c54109219b99732486ae64cc921cb15332486e661cc9219b994324872c540c9219d997414873454d0521b998b41487375410521cd15041487a442105219d99731486b664cc521cd15331486e662cc5219d9943148734540c521cd153214872c54885219b98b540867661d50219b98b530867661d4c218f992530863d6494c219b594420872e5410821b9584420866d658c821b9586320866f654c8219d59441087365410421b958841087a442104219d59631086e5628c4219dd9531086e562884219bd9521086ac64484219dd9521086b46448421b9d9521087676548421e9d9121086e66448421b919121087a46448421a919121087665448421d915121086e76348421b958d21087665348421d914d21086e460484218fd91500863c645402197d8d500865c6354021d9485500866e6294f409b58a53d02766194f409d58653d02b86050f409d98652d02756194b409b98a51d026d6294740e910841d02ae6290e40ad98643902b66190a40cb54842902ad6510a40cb594429032d5310a40cb10a51903665294640d954a51903a44294640d9d0a51903364294640cd10a51903644294640c910a51903665254640d954951903a44254640d9d0951903644254640d994b419036552d0640e910b41902ae6290640cb94a419032e5210640cd54441903665210640d954841903a74210640e910841902b56510640cd59441903355310640cd94841903a65210640c994841903a552106408f997435031c53d0d40c714d43502b86050d40d3d4f525034c53d4940d3d4c525034c5314940cbd0c525032d43149409b997425034f53d0940d314f425026e6510940d3d4c425034c5310940d5d4f515035453d4540d9d4b515036452d4540d9d0b515036442d4540d5d4c51503545314540d9d485150364
  | 4 => 0xb54c429076652d0641d954b419072c42942419b997425066e6510941d9d4b415076452d0541cb14a415066e6294c419b58a53106ac6250c41add8543106b86050c41ab98a42106b56190841cb54c42107a66110841e9584421072c4294441b998a41106e56290441e910a411063f6550441ab18941106776550441b9d8941106e46250441e9109411072c429404197d8d501065c63540419bd89501066c6254041cd99254106b56395041ad98a54106b66095041b998b53106e562d4c41b998a53106e56294c41d554c531079653d0c41e554f43106b662d0c41ad98343106756590c41ad59243106e66290c41b958a43106776550c41b9d8943106e46250c41bcd8143106f06050c41add9543107376550c41e5d8d43107a76250c41ad18943107a46250c41a918943107b36050c41ad18143107b06050c41ac18143106b66410c41b598f52106d563d4841d9548521076654d0841e995342107a743d0841e950f42106756590841b998a42106b56590841cd59642106b56390841ad98a42106a66290841ad98242106776550841e950842106b56310841ad98842107a66210841e994842107a55210841ad98042106e66410841e999042107665410841e995042107a74310841e990c42107a54310841e910c42107a76510841e999442107a56510841e919442107a76310841e998c42107a56310841e918c42107a75310841e994c42107a55310841e914c42107a76010841e998042107a56010841e9180421067665cc8419d59732106b664cc841ad59332107a442cc8419d9963210675658c841add9232106b4648c841e910a32106b7644c841ad19132107a4424c841ad99032106b5640c841e910832107a442d4041e910a50106d76354041b518d50106e76254041b918950107a44254041b598c50106d56314041b998850106e56214041e9108501066e62d53319b58b54cc72f6295331cb18a54cc73761953319bd8954cc66c6255331cbd8954cc72c6255331cdd8554cc66e62153319b58854cc72e5494b31cb55252cc66e6494b31d958652cc72e5454b31cb55152cc66c6454b319bd9742cc66d65d0b31cb95342cc72d54d0b319bd9442cc66d6510b31cb95042cc72d5410b31cd95341cc76652d0731d954b41cc7365410731cd55041cc7665210731d954841cc7a442107319b98b548c66d62d52319e983548c67960d52319bd89548c66c62552319b988548c66d62152319b992528c63f6454a318f191528c6ac6454a31cbd91528c66c6454a31cb191528c62c6454a31d9185528c66f65d0a319b597428c66f6510a319b594428c72f5410a31cb150428c76652d0631d954b418c7365410631d9948418c7655210631e9108418c6b664cc631b998b318c76552cc6319b98b544c66d62d51319bd89544c66c62551319dd85544c67b6055
  | 5 => 0x53d0ae76154f42b918553d0ae66114f42b958453d0ae66190f42b958643d0ae76150f42b918543d0aeb6050f42ba18143d0b8d4310f42d9d4651d0ace6314742b358c51d0ace63d4342b358f50d0ae661d4342b958750d0ae66194342b958650d0b1e5350e42ad1854390ab86050e42cdd0e5190b354394642d9d0a5190b674254642d9d0b5150b674214542cd9085150a766194c429d5865310aaf6250c42ad1854310ab86050c42b99864210ae561908428fd954210ab461508429bd954210ae76150842b91854210a5f63540429718d5010a7761540429d1855010b2e6495042ab58e5410aae6195042ab9825410ae661d4c42b95875310ae66194c42b95865310b4d5314c42e394f4310b8d53d0c42ab9874310aae60d0c429b5964310aad6490c42b99864310ae56190c429bd954310ae76150c42b91854310aeb6050c42ba1814310aaf6550c42cbd954310b8f6350c42e9d854310aac6150c42e91854310aa46150c42ead814310aac6050c42ea1814310aa86050c42ab9904310ace63d4442b358f5110b655114442b3d8d5010acc6354042b9d855010ae46154042b398c5010acd6314042b99845010ae561140429d98754cca7561d5332cbd8a54ccb376195332cd18654cca7761553329d18554ccb2f6255332cdd8554ccb3461553329d98454cca756115332cb95342ccb2e5410b32cb55042ccb365494732cd55251cca766494732d9d0a51ccb644294732cd95151ccb3554547329d19151ccb674254732d910951cca7661d52329d587548ca7a60d52329e583548ca7761552329d185548ca7661152329d584548cb2e5410a32ab993328cae661cca329d992518cb674294632d910a518ca3f64546328f191518cab46454632cdd91518ca746454632cd191518ca346454632d9d09518cb644254632d9cc9518ca7661d51329d587544ca6f62551329dd85544ca7461551329ed81544ca7860551329b997424cb2c54d0932b398f424cb2e5410932ab993324cae661cc9329d984504ca7561141329b98b540ca7661d50329d587540ca7761550329d185540ca3e6494c328f592530ca6d6510832cb950420cb2d5410832b358c420cae5618c83297d95320ca6f654c8328fd91500ca3c64540329dd85500ca7461540329bd8953d066c6254f419b98a50d066d6294341d5d4e53d06e76254f41b918953d06e66214f41b958853d06e66290f41b958a43d06e76250f41b918943d06f36050f41bc18143d07954310f41d9d4a52d06d66314b41b558c52d07a66410b41e9d0c42d07a54310b419d99732d067565ccb41ad99332d06b564ccb419d99632d0675658cb41b598f50d06d563d4341b998b50d06e562d4341b998a50d06e56294341c794d43906ac6250e41ae181439072f4394a41cb50e529072d5210a41ab594429072d6510a41c
  | 6 => 0xa1512570b017b140a740e2a6e0270330000a3a1e1ad19c0001950278eb02582f0748000000218001190558000d88ec8002070000e50001c783007f16d86e84ea610a50478c792299121188698300e08e12b22402681500006b18916f195841a100ae2390001b70c59cf0ff8be23e0140d92730002509e60b900014b000139a8524525e11100023311a97f00000015796c99d93c8001c400600023580004d0000c8000004a2200001e00006ba0c26280018f1c889328616fa9723e9bca7380000000c0000200100202c0e01700c0000c80f02401c0000900402c008000060240000b0000200000a004018000000000100100201401002800000038008010000080580101e0002380d000004028000060640381c03607806806002034000000100040200e0080000003000002c070030360140080100400c0003000600402801042004098040040040e001002004010000020000001703a000010010020000200f00c0240080100000c0000000001001000000000038140000000100101001806800002008000000000000080000001c000010060000481f00002401005004000000040080500000000000802001002018018010000100000b00003000802000008000010060080680902600c068020280240080000000c0c800002008010000040440000103600000800008000000010180040080400e0180082a01a0040180400c01c008040080041100401e0500081a0180100000700000c0000600000c0380f000000000000040000080801c0340080300201404001002000030070080040580001000c0400e0000000100000c0040000000c0200000000603c018080060080900f0020100000100e0640300000002c000060000980180e000070020000000000000401400c0000100e0380180204a02806012018058010000400100080000400000000002000010030240440100d0020280480503a010000030120000382101e008038000120040000e00401c1a00203a0040680000e0040680d0000300001700400c0000102a004008000000140e0010040340000203800c0300100001801817000088008220060200200700400000004000000068050000080a00900000c028019dd8552d0e746154b439bd8951d0e6c62547439b98a50d0e6d62943439d98650d0e756194343cbd0e5290f665294643d954a5190f374394643d99495190f655254643ab98a4350eb66190d43d9d4b5150f6452d4543d9d485150f645214543dad4b5050f6852d4143dcd475050f7051d4143dad485050f685214143dcd445050f705114143d6d0c5050f3a43141438fd954310eb86050c4397d954310ed86050c439d9865210e7561948439b98a5110e6d62944439bd895010e6c62540439dd855010e7461540439dd8553d0a746154f429d98650d0a756194342d3d4e
  | 7 => 0x9dd1071e486980000000000000028f9e98000001ba000036a178000001b1a4d80000020e0669ce846a5b0c90940c708714f0000178000000fc8002700f48000658510ef29c28a86e10e98200000000025c1138000001ff9b21a08001bc0000540449ce00023a9090da0c2a6400014400d9da9fa13e8001ed22600000028914680000005000018e8d717d0528fa24300003d8001148000001f4800210883a0087680008880018600029a0a481ea8211780027da1ba40257a438d484200001f0791bb8000708d401b0000341fb8e10c60000002651258001b695c8e1a5f80029380026988d8e38df8002348e0000036000000159a0505b80003700000000000000000000000009f8002751c4a9095180020d80000000000000000000000000015900021480021100026d8f1a638e594d80000021f17f80026f8000000000000000a7a8e93c0001529eca2e83b9f89278001cba708c38239cc8738000001ac86600000025691880028c142132a9927c05c10ca2a91185885314a80000280005793fa0907827880015028004a0002250000000001120dc94926b9210d981497ea189761690850978000050000640398752720f99b080016880000023d80009a9629b102b8001b79c008aa4f856a6c8b28000002032120f008d1e824f24091e12d0820d08dc1080aca0e9630111c28e996e89c22189e05b1aa23f0b48860338a9a910d129b1840710d686a80000017d8e480000b82482d80011e80011500000002500000022300000003080002e9359c70000000d62152462201a90b71198000001a31f5a269d0a1304f9f380027a19096a11ba059fb12d8002019ea1bf87aa4599b16093d06a0858000f09d51fd1311ab80000002100000029c9d91a11a9912a1b1f0800a7194f9f2a78276881a170789e210c1051438b8136137a501499322831738cda609a4a180bf2760ee9e7990136a191d22299672489ada7d02ca6f07b1981969480eb86887618e1088afa72a838632928181bb1aa9ee9168ce19a03c08a1c51829928b68d302d295a660548228d200982a8732671e88490230dd17580016b82e00028d0001fe80017ba6e9de09d8dd9898d290600308f9a80728e716584280c02f8498db0328a117405da7f06c9df9e1a5909b98801d1479520f88158db800035a270000f398d29ba3180000000000012011f1fd87d10e000173104a22a0d03180022e17c1a28001989d89098919aea5199d2322372028000af14c11ca1997725d8518170000000000002550b38000001f1a0002a0bb160000029891258a4c8509c5a47a4d22ba631d30741220b417110d93f19323c8831c30f119415e177a7b81a170165299a559f42878e2075a6829801329317a0b782b06380ea1c8000002791c21b58522168000e88bc96e11800019e8001af80012a8320001b296d00
  | 8 => 0x572340001400002081d39a180000014d2678f294280012b800220a3b2258a8a8111a00000015b8001b02848000cd1108470ae8551c119b87e80009b1f5100a5f0fd17208ea1c1038581ef0a68f50981d700423ba7104c18c19f9d28139e10001508628720002068000001040fe94580011c2869b50ab92c2659240220b50cf2829fa98695700000000002c00000019980029200025612a1811451990000000da9d40828000648002949e01548ef8000000902379d600000000000029d83e00027a8431c18ed83f1d183122c9dc28c90781d979a5298a87f9f61f68001d6a601eb0aa86f92f993902a7c9de80013d8000001030000ec09619a92503a8001b90001eba3880007b840a5217c8441e0a0b9c08e90b11a788900023114a00016c00000000000024b84b8001d588b93a1391cc15a9349e40f20000b224c0001460002580001fe00021e8001489bd80595f130000043a6b22f8000f70291ef8650ee239a211d98000a00cf80c828895a141948d000000025310d07d9859331f81919ba80000005906180011619600000009d17684aa8b0000b095f8000260119e6a440b180000027f9d1105a6d0fc25a1cd0001bd0001dc8ce9a400000000005c800298924a0aa420348680ea9af0939c380000014c80005aa7e1dd9f208c1561c81d0206216114000000003a28a5d1b887000012612921a8baa04a9790b9d78b884b0462512099ca2418190000c122c1f91750b30778678ea254a6c00aa8709f2361b3a411d496b0f424711f8e69920002041789db8001f300010f20a0c89c613a80014100000011b07700008810a8000cc80000007e00023286715880005e29d23c14704d8c1a1d0000a90000cc25e91d141a079532619e38898f68000a58001cf80000018080028583a06d0a712186910b01aa758072129e297e0a219f0a2a24a498c30988000000a8087a898000001f78001640560000002490001a385f0a300010688000015d8ed1ff20f0bd80003b0be80007c16680000000012729619793826a9280002968000000000000000c50378169e715c000178048a818000000000000001618000000001298000ad000071a2f00000021f8000000001a515500014b800291a648000000000001100000011850e79a5a44a5b88100000023009717480018180003d27721d964a13a159b800f94e0c9a79a4808492080020b0a61430d380000023093893e15580027789a1ca8d180000000000013710a0002748fb8000000001e516629400028a0001a22669ed8199a886c11300028e1f710f8001a015b0000bf84e08400908c8ba2290fb23d0b580b07c8e428815680020f9268001c9a2a0991ec05d03524a8a08908c021a16a81f9e581619c9be81b93b9170d80000000000fa8000df00010000018da4e8000608000ac0d78620000c41e316381ca2d
  | 9 => 0x28d9a71889b40aa0000001b300004c80017a8120fe0c480019725a8000000000f618c8950000f818ba03a7e92e0e82351db0001c69351318600000000002808e60000bb83800023f8ca8c20bc0539bf1680b60949c920897187a1848f785e9ee22b03f9df1b61792690002901ac1678a408b04583c8d50d580f2688b992880891d800123a3684f1540000fd962133a5423394484100009e8481308bd1fc15380000001000000013b12315e89223a0000000000001a680022d0001fc8001f006f05f88f22800789c89998b19e25c8001838f58018000000001be23814e92c8000020000598f90001018cb0000000000002620002538cb8f30c0970a6a1ae0ca2429e900000028b86d8a198a0000e328f01285a1f100d18f89295a00029501c080a010001011158002888000000108451728000391a61800de2020ab1cda0c86100000000012f0e09b4a4b15d1d81da0240c69340001b98000000de8201699ab27b0ad8ff000038a27987806a238001580001cb00002092e896828187246840000000079818a4a28416100003e8000001ea90200025980000029a80824e0001f98
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x20ca6761095010743b1884a8083a118c4254041d0cc6210a020e856310850106923a2c329663491c95410731a48e8a908398d277510841cc692ba88420e6389dc46454a31c48e2322a518e2464185528c695386a821463491d152d0631a48e8a908318d2775108418c6923a2a598c638999152cc631858e8b10a098d2472550410c712b288420863a158c4210431948e8b146218d157315041c86523a2c518e43435cc5410a21948e8b0c6510d0e73d88544868b39ec22a2438915261d092185eec2a66490e245498732487122a4c5a0a430ddd854cc521c48a93166290ca47458632086523a2c518843299d26448421c4eca3224210e27751912108712324a890843891905448421948e8b1a4210ce07058d21086333b4a690843499d25348421c48c929a4210e246414d21086923a242a8043891912154021c88c690aa010d287050c52502983828628a81499d44210540c4cca21082a07075310841503822988420a81491c55310840b10e6b0084205247254c41102c839ac0208810d1d16194b30a48e2aa0859842c7458a51cc292392a820e61499c75410a30a4ce5aa0831862662987544c312310c22a261499c75410930c4cc8216a29852672d50414c2933a6a420a61499d44210530a48ea210829862665108414c3123288420a61891886195030c48c430aa81861863181540c314310c0aa0618c1846055030a48e2aa0841860d65d0c420c31232084a8861491c95410430c2acba18821852474548410c293ba88420861495d44210430c4eca210821862565108410c314b2884200618c5944110030a48e2aa085904a47458632c821b3a6c2a9c41499c75410920948e8b0c649062454586324832229ac3192418999042d4520c4cca2108290624651084148383a988420a41c114c4210520c18c829a429062464145214821a3a2c3a984189dc86454420c48e4322a21062464d09510831232084a8841499d33254420c48c9992a210624640c95108293396a820841455cc5410420c4eca21082105247454621082923a2a210841491d151c8020a48e8a8a401062464545200832231aa290041491c95410710948e8b1463886246414921c42173a6c4a9c21499d35208610a48e8b08a488524711504244293396a820a21499d35210510a4cea2108288524751084144383a988420a21c114c4210510948e8b1462886245458a314432229ac518a21195d8528c510868ec2a242886146414d2144312320a490a210b1d162d4c10c4ee2322a408624711915204312320c2a9021499c7541081085aec2a0840850d7315042042923a2a5a0821491d15210410a4eea21082084677654b31042923a2a5988218999152cc410a48e8a9062085247454b21042923a2a410821491d152c40108c8eca922008524745491004312322a4880219118d5244010
  | 1 => 0x1ba0000000002a34800267f06344c20000000005501a880000002c0000044a2930cc4a80046632b000000f00300e87c071cc00000000000001d9040000000002e6f05208420150b088eb3000f906c320200940000001b8385e000000848a48008e25848000000000ce003d800a4b52a291569a0023c6aba3c26c0000003881ad9049f4f262002216265242a5b0cb13a9c00b90006c00003a800987a000000000000000000000002ce04680000001a1184a00000d976992b90c00516d02cb2c1212b000004f80000d470af864490e8f4a0005c17c22cf550000e0040a2ccc003016d6ec9001ad681a5280000311e0b520445f8083c6e0000008af0e28d18ce4980050de66968fc9403001be00002a02800268000000001b40000000002a006b0a400851013800a06a991940042319a4000000000002f171b66c02ab85e181225860000035d38000034c00971f8013a000000000001617400bd158013c723407d640038a1c0000003416c0063b1072001b9155a7729b20ec4f001606600000000000430005c3a000640000531c0000062800d4220009800000800001000080401010000a01018040004030080603028200208008040201000000000030000c00000000600000040200000200000008200a010002c000000800120300800000400000000002004060000804020002d2a7290c5050e9938c8628287621c14310f42c34a630287215307050e5190a5238ac72a085299c6609504294ce330686216a061d814310b15b28c0a1885a2d8c6050c42d46c230286216a0611814310a9238aa821665891904254732c4ee4322a31962472191518cb1232684a8c65499d33254632c48c9992a31943474584504ca9238aa821065291d1618c832b20e0a1887a0da07050c42d070d298c0a1c834a1c14394a41948e4b1ca820ca6729825410653394c1a1883a818b6050c41c66ca3028620e93631814310751b10c0a1883a81886050c41b40e0a1e8420ca57690c4210692bac862108368dc14310841b40e0a188420d8673d9442106c2b9eca21083619ce6510841b0ae73288420d2575d8c4210692bacc621083a158c631084194aed2988420f055314c4210693baac02108361dcd6010841b08e6b008420d867318042106c2b98c0210838999442cc841c4aca2166420cb270d9232107133288519083295d8420c841b0ae621064
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xd01c00021664b0401840522800b800a0683dc86454632a0683dc46454a31a0683dd46448421827871925348421c047418d2154021c047414d618c920a0683dc86454420c047418d5148020c047414d628c510824845d8528c510a0683dc464548108248799152cc410824871915244010c047418d5244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
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
  | 5 => packedAt s4K5 (27286+((h/296+packedAt s4K5 (24030+(h % 296)*11) 11) % 1563)*11) 11
  | 4 => packedAt s4K4 (55826+((h/446+packedAt s4K4 (50920+(h % 446)*11) 11) % 1769)*12) 12
  | 3 => packedAt s4K3 (11798+((h/75+packedAt s4K3 (11123+(h % 75)*9) 9) % 363)*9) 9
  | 2 => packedAt s4K2 (860+((h/4+packedAt s4K2 (840+(h % 4)*5) 5) % 20)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffff81ffffffffffffff0fffff
  | 1 => 0xfc07f03ffe03f80ffe0f83f03ff81f80f4c7cc
  | 2 => 0x7ffc0fffc000ffff003ffc0ffe000f8f8f0
  | 3 => 0xfff80000fffffffffffffc0000ffffffff00ff
  | 5 => 0xffffffff0000000fffffffffff000000ffff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1430108202489040805284b14518a2a6015b55
  | 1 => 0x5952a58c643922d79605a155366a9b0a74c5cc
  | 2 => 0x52a4c316a89074ebaab0426d94b6ca14b8e8f0
  | 3 => 0x60c68a28d122468d4d29680820c71c58de00aa
  | 5 => 0x83070c30e1c3870e71ce738e38041060efb600
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeaa8eaa8aa00aa00eaa8eaa8aa00aa00eaa8eaa8aa00aa00eaa8eaa8aa00aa00eaa8eaa8aa00aa00eaa8eaa8aa00aa00eaa8eaa8aa00aa00eaa8eaa8aa00aa00, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37427
namespace PEqualNP.Outside.L_meta_37427
open PEqualNP.Outside.L_meta_37427.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x38024334000f0001c82c500000030608400000004a40000001001ef42ec42ef32ec32f741f441f731f431f721ee21ec21f421e421ef20ed20f710f510
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x8a004945807189821221a002430a79a40000e00030822355394f42b328e852e54ccacca3995594f41b3296833654cc6cca598d994621b32a0436454086cca610d914c21b2a80432c5448298a6905914520b2296213454442a8a6885914910
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x65009198e54086266494c218919150086446354021
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
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
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (297+((h/5+packedAt s5K4 (272+(h % 5)*5) 5) % 31)*6) 6
  | 3 => packedAt s5K3 (602+((h/7+packedAt s5K3 (567+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s5K2 (155+((h/1+packedAt s5K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffffffffffffff03ffffffffffffff87ffff
  | 1 => 0x1fc0fc07f03f01ffc3c1f03f03e07e07acccc
  | 2 => 0x1fff0007ffc001fffc01ffc003ff8007cf0f0
  | 3 => 0xfe0000007fffffffffffe000003fffffff00ff
  | 4 => 0xffffffff8000001fffffffffffc000007fff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc0420820108208100442314518628a3005555
  | 1 => 0x54a9631ab23945af2c1d0d53629aa6c53acccc
  | 2 => 0xa930c5ab5450e9d755c216d9452db28a5cf0f0
  | 3 => 0x31a28a3468a28d1a9aab40820831c71c6f00aa
  | 4 => 0xc1c30c3870c30e1ce33398e38e01041077aa00
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00eaaaaa00, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37427
namespace PEqualNP.Outside.L_meta_37427
open PEqualNP.Outside.L_meta_37427.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x500225cc430050347804a1000030bdc1f00f0903765a101809c03466a4508003802400080070000280740062a0071f9000f5a807c01b4360020a33cad31a58256b2402c0004200e80000000000041020010000061c90102046010a0048300ffd4c03fe5300ff54c03fc5300ff90c03fd4300ff10c01ff51007f94401fd51007f14405ff41017f90405fd41017f10403ff3100ff8c403fd3100ff0c401fe21007f48401fc21007fd4001fe50007f54001fc5000ffcc003fe3000ff4c003fc30007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42003ffc421001fee2108003fb1084001ffb2a2000bfd9510006feca880027f6544001ff32a2007bf99510007faca88002fd6544001fe32a2007bf19510006f8ca880027c6544013ffb222009bfd91100077ec888002bf6444013ff3222002bf9911004ffac888026fd6444013fe3222002bf1911004f78c88800abc6444013ffaa22009ff9511004ffaa888027fc5444011ffb1a2008bfd8d10007bec688002df6344011ff31a2001bf98d10047fac688022fd6344011fe31a2001bf18d10047b8c688006dc6344011ffa9a2008ff94d10047faa688023fc5344011ffa1a2008ff90d10047fa8688023fc4344001ffb122000bfd8910007dec488002ef6244001ff3122000bf98910007fac488002fd6244001fe3122000bf18910007d8c488002ec6244001ffa922000ff94910007faa488003fc5244013ffa122009ff9091004ffa8488027fc4244011ff9922008ff8c910047fa6488023fc3244001ffa8a2000fdd4510007fca288003fd5144001fe28a2000fd1451004ffe8288027fe4144013fb20a2009ff5051004fea8288027fc4144011ff98a2008ff8c510047ec6288023fd3144011fa98a2008ff0c510007fe4288003fe2144001fb10a2000ff48510007ea4288003fc2144001ffa822003ff94110007faa08800ffc5044013ffa022003ff9011004ffa808800ffc4044011ff9822003ff8c110047fa608800ffc3044001ff9022003ff88110007fa4088003ff1044001fd8822003ff8411001fec208800fff65040077fb282003ff9941003dfcca0800ffd65040017eb282003ff1941001df8ca0800fff64040077fb202003ff99010015fcc80800ffd640400b7eb202003ff1901001df8c808017ff540400bff2a02005ff5501002ff8a80800fff63040077fb182003ff98c1000dfcc60800ffd63040097eb182003ff18c1001df8c608013ff5304009ff2982004ff54c10027f8a608013ff4304009ff2182004ff50c10027f8860800fff62040077fb102003ff98810005fcc40800fee6204001773102003ff58810005fac40800fed620400176b102003ff1881001df8c408003ff5204001ff2902000ff54810007f8a408017ff420400bff2102005ff5081002ff88408013ff3204009ff1902004ff4c810027f8640801afe6104001ffa882000ff94410007faa208003fc510400bffa082005ff9041002ffa8208017fc4104009ff9882004ff8c410027fa6208013fc3104001ff9082000fdc8410007fc4208003fd2104001fe1082000fd0841001dfcc00800fff5004007ff2802003ff5401001ff8a00800fff4004007ff2002003ff5001001ff8800800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0xffe531400ffea98a007ff14c5006ffc8628037fd431401bfe218a003ffd845001ffcc228002fe6114007feb08a000bf5845001ff8c22801fff511400fff288a000df9445003ffaa22801ffc511400fbe288a00effd0450077fc822803bfd411401dfe208a00dffcc45006ffc6228037fd311401bfe188a000ff88450007fa4228003fc21140077f300a003ffd405001efea02800ffe5014007fd280a003ff5405001efaa02801ff95014007ff980a003ff8c05001ffa602800ffc3014001ffb2e2000bfd9710007fccb8801efe65c4001feb2e2000bf59710007f8cb8801efc65c4019ffb26200cbfd9310067fcc98800afe64c4019feb26200cbf59310067f8c98800afc64c4019ffaa6200cff95310067faa988033fc54c400dffb1e2006bfd8f10037fcc788006fe63c400dfeb1e2006bf58f10037f8c788006fc63c400dffa9e2006ff94f10037faa78801bfc53c400dffa1e2006ff90f10037fa878801bfc43c4001ffb162000ff98b10005fcc588003fd62c40017eb162000ff18b10005f8c588003ff52c4001ff2962000ff54b10007f8a588033ff42c4019ff216200cff50b10067f8858801bff32c400dff1962006ff4cb10037f86588003ff51c4001fba8e2000ff94710007faa388003fc51c4001fa28e200cffd0710067fc8388033f641c4019fea0e200cfd50710067f8838801bff31c400dff18e2006fd8c710037fa638801bf531c400dfe18e2000ffc8710007fc4388003f621c4001fe90e2000fd48710007f84388003ff50c4007ff2862000ff5431001ff8a188033ff40c4007ff206200cff5031001ff8818801bff30c4007ff1862006ff4c31001ff86188003ff20c4007ffb2c2003bfd961001ffccb0801efe6584007feb2c2000bf5961001ff8cb0800efc6584007ffb242003bfd921001ffcc90800afe6484007feb24200bbf5921001ff8c90800efc6484017ffaa4200bff9521005ffaa90802ffc5484007ffb1c2003bfd8e1001ffcc708006fe6384007feb1c200abf58e1001ff8c70800efc6384015ffa9c200aff94e10057faa70802bfc5384015ffa1c200aff90e10057fa870802bfc4384007ffb142003bfd8a1001ffcc508002fe6284007feb142000bf58a1001ff8c508003ff5284001ff2942000ff54a10007f8a50802fff4284017ff214200bff50a1005ff8850802bff3284015ff194200aff4ca10057f86508022fd6184001ffa8c2000ff94610007faa308003fc5184017ffa0c200bff9061005ffa830802ffc4184015ff98c200aff8c610057fa630802bfc3184001ff90c2000fdc8610007fc4308003fd2184001fe10c2000fd0861001dfcc10800fff5084007ff2842003ff5421001ff8a10800fff4084007ff2042003ff5021001ff8810800fff3084007ff1842003ff4c21001ff8610800fff2084007ff1
  | 2 => 0x210c7fc6290863fd3148431fe18a4200ff88521007dc4290803ff60484017fb024200ff98121007fac090803fc60484077e3024218ffcc1210c7fc6090863fd3048431fe1824200ffd9421005feca10803fe650840f7f3284200ff59421005faca10803fc650840f7e3284215ffd8c210adfec610857fe63084037f3184215ff58c210adfac610857fc63084037e3184215ffd4c210affca610857fd530842bfe2984215ff90c210affa8610857fc430842f7f3084200ffd4421007eea210803fe5108401fea884200ff14421007e8a21085bff410842dff2084216fd904210b7fa821085bf5410842dfe2084215ffcc4210affc6210857f6310842bfe9884215fd4c4210aff86210803fe2108401fb1084200ff48421007ea4210803e52108401ffb004200ff9802101dfcc010803fd60084017eb004200ff180210affe6010857fe300842bfe9804215ff0c02103ffec7a801eff63d400fff31ea001bf98f5003ffac7a804efd63d400ffe31ea001bf18f5003ffea7a801f7f53d400fff29ea007ff54f5009efaa7a801ffc53d4027ff21ea013ff50f5009ff887a801fff61d400fff30ea000bf9875003ffac3a8002fd61d400ffe30ea007ffd475003ffca3a801ffd51d400ffe28ea014ffd07500a7fc83a8053fd41d4029fe20ea013ffcc75009ffc63a804ffd31d4027fe18ea000ff88750007fa43a8003fc21d4027ff986a003ff8c35009ffa61a800ffc30d401f7eb2ca003ffd8e5001dfec72800ffe63940037f31ca003ff58e5008dfac72800ffc63940077e31ca007ffd4e5008ffca728047fd539400ffe29ca011ff90e5008ffa8728047fc4394007ffb0ca003ff98650005fcc32800ff661940017b30ca003ff58650005fac32800ff561940017ab0ca003ff1865003ffea328003fe5194001bf28ca000ff5465003ff8a3280037c5194025ffa0ca012ff90650097fa832804bfc4194023ff98ca011ff8c65008ffa6328047fc3194001ff10ca000ff48650007f8432800efe6094007ffa84a003dfd425003ff6a12800fff3094007ff184a003ff4c25001ff8612803fff635401f7fb1aa00fff98d5000dfcc6a803ffd635401f7eb1aa00fff18d5000df8c6a801fff535401fbfa9aa00fff94d5007ffaa6a803f7d535400ffe29aa00fff90d5007ffa86a803ffc4354001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa000bf1855003ffea2a8003fe5154001fea8aa007ff14550087fe82a8043fe4154021fea0aa010ff1055007ffe62a803ffe315401ffe98aa00fff0c550007fc42a8003fd2154001fe10aa007ffd415003ff6a0a800ffe5054007bf282a00fffcc15001ffc60a803ffd3054007fe182a007bf9945001ffec62800eff6314007ff318a001bf98c5001ffac628036fd6314007fe318a003bf18c5003ffea62801
  | 3 => 0xe18aa200ffd8151005fec0a8803fe6054401feb02a200ff1815101df8c0a887fff405443fff202a21fff501510fff880a887bff305443dff182a21eff4c1510f7f860a881efe651440fffb20a207bfd905103ffcc82880afe641440ffeb20a21cbf5905103ff8c82880afc641440fffaa0a207dfd505103ffca82881ffd5414439beaa0a207ff1505103ffec62881eff631440fff318a201bf98c5103ffac62886efd631440ffe318a201bf18c5103ffea62881f7f531440fff298a207ff54c510defaa62881ffc5314437ffa18a21bff90c510dffa862886ffc431440fffb10a207ff98851005fcc42881ffd62144017eb10a207ff1885103ffea42881ffe5214401bf290a207ff5485103ff8a42881f7c5214439ffa10a21cff908510e7fa8428873fc4214437ff990a21bff8c8510dffa642886ffc321443b7f308a207ffd445103efea22881ffe511440ffb288a207ff54451006faa22881ff55114439ffa08a21cfdd04510e7fc8228873fd4114439fe208a21cfd104510dffe622886ff73114437ff188a21bff4c4510dff8622886ff4311440fffb00a207ff9805101dfcc02881ffd60144017eb00a207ff180510e7fe8028873fe4014439fea00a21cff100510dffe602886ffe3014437fe980a21bff0c051007fecb10802ff6588401ff32c4207bf99621007facb10802fd6588401fe32c4207bf196210d7fec91086aff6488435ff3244202bf992210d7fac91086afd6488435fe3244202bf192210d7fea91086bfe5488435feaa4421aff152210bffec71085eff638842fff31c4201bf98e210bffac71085efd638842ffe31c4201bf18e210bffea71085ffe538842ffea9c4217ff14e210bffe871085ffe438842ffea1c4217ff10e210c5fac510803ff5288401f7a944200ff94a21007faa510803fc5288401f6294421affd0a210d7fc851086bee4288435fea14421afb50a210d7f8851085fff328842fff1944217fb8ca210bffa651085fed328842ffe1944215bf98621007fea310803fe5188401fea8c4200ff146210d7fe831086bfe4188435fea0c421aff106210bffe631085ffe318842ffe98c4217ff0c621007fe4310803f72188401ffb044200ff9822101dfcc110803fd60884017eb044200ff182210d7fe811086bfe4088435fea04421aff102210bffe611085ffe308842ffe9844217ff0c221007feca90802ff6548401bfb2a42009fd9521007fcca9081efe6548401feb2a4200bf59521007f8ca9081efc6548401be32a42009f195210c7fec690862ff6348431ff31a4201bf98d210c7fac690862fd6348431fe31a4201bf18d210c7fea690863fe5348431fea9a4218ff14d210c7fc8690863fd4348431fe21a4200ffd4521007fca290803fd5148401fe28a4219ffd05210cffc8290867fd4148433fe20a4218ffcc5
  | 4 => 0x801001002004010040020080b80d0000180000001c0380480801001c02806000008028000000300100000e008018020100480000900002c0300c00a00000800006004068040280200001fff64d440f7fb26a207ff99351015fcc9a881ffd64d44457eb26a207ff19351015f8c9a881fff54d440fff2a6a207ff5535103ff8a9a881fff63d440f7fb1ea207ff98f5100dfcc7a881ffd63d44437eb1ea207ff18f5100df8c7a881fff53d440fff29ea207ff54f5103ff8a7a8887ff43d4443ff21ea221ff50f5110ff887a881fff62d440fff316a200bf98b5103ffac5a8802fd62d440ffe316a207ffd4b51117fe85a888bfe42d4445fea16a222ff10b5110ffe65a8887fe32d4443fe996a221ff0cb51117fe83a888bf741d4445ff20ea222ff50751117f883a888bf441d4443ff98ea221fdcc75110ffc63a8887fd31d4443fe18ea221fd0c75103ffec1a881ffe60d44077f306a207ff58351005fac1a881ffc60d4445ffa06a222ff90351117fa81a888bfc40d4443ff986a221ff8c35110ffa61a8887fc30d443d7eb2ca220ffd9251105fec928883fe64944057f324a220ff59251105fac928883fc64944057e324a207ffd5251106fea928883fe5494441feaa4a220df5525103ff8a928877ff639443b7fb1ca21dff98e5100dfcc728877fd639443b7eb1ca21dff18e5100df8c72881fff539443bbfa9ca21dff94e510effaa7288777d539440ffe29ca21dffd0e510effc8728877fd439443bfe21ca200ffd8a51007fcc528802fe6294401feb14a200bf58a51007f8c52881fff5294401ff294a200df94a51107fe8528883fe4294441fea14a220ff10a510effe6528877fe329443bfe994a21dff0ca5103dfcc32881fff5194401bfa8ca207fdd4651107fe8328883fe4194441fea0ca220ff106510effe6328877fe319443bfe98ca21dff0c651007fec128803fe60944077f304a200ff58251005fac128803fc6094441ffa04a220ff90251107fa8128883fc409443bff984a21dff8c2510effa6128877fc309443fffb22a21fbfd91510fffcc8a880afe645443ffeb22a21fbf591510fff8c8a880afc645440fffaa2a21fff951510fffaa8a881ffc545443dffb1aa21ebfd8d510f7fcc6a8806fe635443dfeb1aa21ebf58d510f7f8c6a8806fc635440fffa9aa21eff94d510f7faa6a881ffc535443dffa1aa21eff90d510f7fa86a887bfc4354401ffb12a200bfd8951007dec4a8802ef6254401ff312a200ff58951007f8c4a8802fc6254401f6312a200bb1895103ffea4a8803fe5254401fea92a21fffd09510fffc84a887ffd425443ffe212a21effcc9510f7fc64a887bfd325443dfe192a207ffd455103feea2a8803fe5154401bf28aa21fffd05510fffc82a887ffd415443ffe20aa21effcc5510f7fc62a887bfd315443df
  | 5 => 0x7bc17c7466c600017e478bd450441ccf0ed84680000003ac000522c785fc9e40000000000007e000000031c000000000b2861473c8662d417090e300f5af483a66f464d044c980270000443681745a4498b70860fcc1d4d30a2043ccd8e206de1281eea787003040585f8000ac4000000a188ca00000000000000000037a4c8e10c4ce50440554642f74879034c70218bf8000d4894815c060f6c310000798d9c0005c04d4000338b0c9bb080bfc00077a0000010d41a0990000000ba227200000085c068d78ea8cf30180c892aad86b4d350cce34a6a41000097c00000000000000082c278c9c8bc2a000000081a000b40ae05ac71d0e09c2d0c7b26e05bc0000fd0580d20007800b852802c0003bc00076a19000092e74c98800013c8d0000568844884f80000c54ecca400000007ec0007c40cc0007400005d86ae0002900010288ce9da0010dc000b88a5c42b0f40000000006fe76efa0f2c95c506ad0000000000000dc8698df423801c50c0010bc000c0813400000000021c0000000010a4c586e4a70686adc000e18ee87280000009d60000000004d88d479ed3c0000000006543b6ae4beca6e000000000000000644324d5cab06ca3843d49ac4c4424000dbcd90b2ab54000008030030020000100300c01c0000600201c00005000008000010040300500202001c0180201200405009000018050010060040000000201c0280203802c0380200c00c000070020040380f002000050000000580280200000c00000010000008010020040000001000004000018008008020100100000a0040000000200c000008010020a00100700200405802008038010000060000c800010004018020000540000500200c000000020000d0000000580080101c0900080100400c0005000000c00002000020000010140080000300a00002003006000000000040180200300000c0000101001c008050060340600100603c078000120040500b0020000b8060100080000000001c000010000040080300a00001800000004020010000240101400000c0000a0020300280600200000001006004000000100080500001800c0080100a0040280600c0080001b00000c00800010000068020180740700000e01400001000000000030000040080000403c028050180080080500a00c0000000c034000000000040000301000c0180000000800005000000010090040100000500e01c0200200000c010080000080b0020080000080100200c010090060200080500201c038000000000000100200401808006000060010040180000100000c0000000a00c000000200200201200a0000100b002004000020000000000000a0000100b000008008030000180000000000c0000f01201800000006000000010020300200e0180000180500a0000b00500200408804006
  | 6 => 0xf00010ac0000000004a00768c0cb0e406566287180b47929b83528a0d08aaeb7881084ed506ee3c29ae1a50405d002270b0304488189d414072c7d2e2e4acb98a108de000786100d64000000aba596000c60e04ac883e3c48fa6948b44844b80628e4b2054cdd81b2efc00000039c4f070809835cdc08e267488219d050ccc000dac768000be40010b0a2d0700009b60000000000000001380000007d62dc610000e1c000a60000a7ec640000000000010040a8000e807948700ac84a2887e425c99c000fc80000004709d8a54c1c07c77038000091200000097e4f4454d4c6b256476603cee502485094ca82982000e580005d4fd0c841f80c4e3850883aaccabec250b40000006c4000000334000919108b84000000d7cb1090a0008747f00e4806b9e00026e000f10754ca40000000010546ac3aa74279ca9634000014400000042c000cbc3f000000088acd00009dc10c0000000007cc58900c8f0904720000816514000000000000000000000000000000000000000000458a3cd1030ca9281e0206bcd989a46be07400004c4dcae8000da0000e6469af645783ba8f41c09000049464207a0000000f500000009280010100000000000000002700002e8214000a8c05600058c000b610b87c20000008e0000000000000000a88d80000200778bd0e4845c000758704a003dc000922cc8af802a274df89bc03040c00094a92c11800071a000c807b4ba09fab3cb249e0932000000000d94c5064068c3888a800020c0000002e029882485507c9be000b30000894e68a809261e0ce0fc0aecaa050a00016487a9580000002fcba836c1987fe936e246a06f869e18906c00071e8900a03180f4000d70000638f344607a8000ff80007301a8992eb800000097088e0000000002d0000000d180007f428c580000aa200011c000cfe0002f8000bf400061c000000de83e0000516e6c0001b093ae140000000009aa26a9f8916b9a94000000000039000051c6a812ca4eda80d00000da2b05ed10000093e2308a600074e0007383b29b2000f08000000bf091eaa400000104805c7c6000a04000000000f1c3c634508ceb4000000d8c9f008cf2465c00075e066120c3a6963940bc714a9a8c40008eae702acbb8c446888f22047d50ec0003a84646ced24000a3282a038aa6f38000000762f6024464a0000009f2624804a9e00107400068e930000dc4dec8ee0000000000008f6014cac4e43b0e94bb40527f8852e88b68a642ec7babe8db06c059400082e0007725b45380008349344b41241e8000000ec0b5c3b8418000cb8000000ff4000524ac0d449865e000000062c6d400000084301c0000001b4000000000000d040009fe091090000598d280ec408000db508497886a37cdfc682320f30f042e404029c0009506080001da530e74c881dc0008d8
  | 7 => 0x5a875098a0000000242f4000000000000f4c000800a7ce5c8da0002a8000000000b8c0005483c0000000ab8c480003a07ca1140000010940000000006d2e000e8c8c32cec81fd020814fd4a90534cf81ac6b0000f3c0008c81480000001d8000c6c9100000008b6490196bb0c7c812888eb000000068ac74ab6cfaa7a5500001100009760003989989b40008a4d54000000000000cfce4c0000000005b00000a4b2c1fe4948480000d71045747be0010646805921f4ef0000000a681bcc046cc81c2b4776a02000348000000a94a56000abc0003d8000000000000000000000914d687640000009e8ca05dc000000000000064a300000000008cc00099ec68000000000000e90558920724364bbcaf480a00000000000087e8e8028d38354000510a4c7fc79b03cea089e23c9a0d60ebc9fc0000000507c00000010d80007cef4505ca9841e00007016c000db89f6c3056c9247566510988ec1690d0b1452cea42b800084671080200000098c4ecd210686586b6ff0000702fa4000000a6c6900f8b58284de4b9400091c0008a284c954000154d58a2a26c0000000006849a8fb400058400083600070e0006ba3ec00085877ebc00480004b0000c28c3cd1c158748072f88000000bace44c10f5c9a6220bd88567f60006342590f870ccc06d02bc1e2862fb0668130ef8b9cce85b8000886000a2e6e70c008800000000047c8aca9c9f400046c75c1c40005200000008c218c0000000100000009b0400b442c86f21b7060ec4bc4ed000096075a000000d845a04fc784b7d038e30000e8c00096c8d249cf54f0cfe8000b8066cb1d0089ec8987d0afc2c058e0006e20000000007c8000f007b6000eec00000099639f0fcbe07dca630784444388d69840004cd088000f58b9622800000034c5187604e00000000006dc3d05c49ee00000000000094200083035800000005a000bc8a721cc000000000000a2400098ec1800000075309c8280004d0fc44bad6c3e4a76baaa3409c880e082d80000006d83f800088c000b48744c20a44c5c0000004047160000f08768640009ea276618000560d74b046b85f41046a60001d02409c8000000f9406a0000000000001800000000000002c474afbcfec1e4822000000000c944265c89c40dc5e897adcc0000001ea6c88ba6780b07a6f7c8400000000000003e8ddc330964e540000010c84feb0800080ccb4ffc788d00c345910a8178c22b18000bcc7fa868aaaeac0008b0000a1cba4a38000000000df026434a000a481f0e785cc3fca5afac0007d8ef46603cc00073ee0c5441de57c7b09d2974a1502c944cf4f7890c08000016000062000030896e38c0000000001b8000254000832000f28000b904e8cf67ae4346fc0004c0bdca50c144142682cc000c2c51200086c0940000000002926eafe4000000a
  | 8 => 0xf849d050086edd00010a00009380008b8000fe07a4f708920080000008c624c6e84304a40000007da7960000000c0ce47743c80000008726003a2e2a000a7489a000ad463c1080009e600000000062a99a42898093c9cc9c0630e7c0000002242f04f879069cf148080e08be06c4bc6a4a66000604b6ccd43a44a8c4000000064ef68a58f8c000f4048059a00048c32891a4d23140000002108e600053cab4000cec33c9c6000ed4a26da47ac000000000fd800000078c7e88fc59c0000000006c2000c00370e28de000022c0002a4ba6a5e0000000ce00076c000000000474b3827c652d880000008268b2488dd450e6f01e6250000f900000006ec000000374000670000000000e2c0010c4c900000000340000010e4000aa8000b4c000a840007067348380009a24500000000000d4000000084f18001014294b74000000f9c5028200010e889c782d14000000e9ca522341f2edc0000780000009060007b83600006929de67c77c1ec000cdccc43500d904c19494e18444c00000010600000054055c0005e4000000e845f0d400006a20000002480009e20003f487c000968ee0b50648000e98f20208a0c054422a28aace3c6aa15080e6f61c88f8f9860c664c0c7a2fdc994c38a8e0008dc0000000000003b4000000000000280000e60fa8000722260ca8018b6400c0000000000010f0570d2c000000ab27aab34a089086fa00000004efb883c00000000000000014c378000b0000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe505881001eed505881001eec505881001eef405881001eee405881001eed405881001eec405881001eef305881001eee305881001eed305881001eec305881001eef105881001ee7105881001eee105881001eed105881001ee5105881001eec105881003cff76d481001cfe76d4810004fd76d481001cfc76d4810006ee62d4810006ed62d4810005f671d4810005f571d4810004ff769481001cfe7694810004fd769481001cfc76948101967f659481003e7c6594810006ee6294810006ed6294810004ff765481001cfe7654810004fd765481001cfc7654810006ee6254810006ed6254810005f77154810005f4715481003cff761481001cfe7614810004fd761481001cfc761481018e7f651481003e7c6514810006ee6214810006ed6214810004fd76d4410006ee62d4410006ed62d4410186f661d4410004ff769441003cfd769441003e7e65944100067d6594410006ee6294410006ed629441000777519441001dfa7094410005f97094410004ff7654410005ef7254410005ec7254410006ee6254410006ed625441003cff761441001cfe7614410004fd761441001cfc761441003e7e65144100067d6514410006ee6214410006ed6214410186f6611441001dfa7014410005f97014410004fd76c8410006ee62c8410006ed62c841014df576c8410006f576c8410004f576c841017ef665c841014ef465c841014ef764c8410176f564c841014ef763c841016ef563c841014ef762c841014fe662c8410006f562c841014fe562c8410006e562c841014df770c841014df570c841014ef660c841014ff260c841014fe720c841014fe520c8410004ff7688410004fd7688410006ee6288410006ed6288410135f67188410166f6618841001dfa7088410005f97088410004ff76484100057f75484100057c7548410006ee6248410006ed624841015ef66148410004ff760841001cfe7608410004fd760841001cfc7608410006ee6208410006ed6208410007e5210841001dfa7008410005f97008410135f57608410006f57608410004f57608410156f66508410136f46508410136f76408410146f56408410136f7630841013ef5630841014df67208410007e67208410136f76208410137e66208410006f56208410137e56208410006e56208410007e75208410007e45208410147e64208410147e5420841013fe6320841013fe53208410135f77008410137f27008410135f57008410007f17008410136f66008410137f26008410137e62008410137e4200841001dfb7644010006fb7644010004fb76440100077b7544010007787544010007bb744401012fb87444010007db7344010127d87344010007eb7244010007e8724401001fea624401001fe9624401001dfb714401001ff3714401011efa614401001ff26144010
  | 1 => 0x94100067f54594100067d5459410004ff735941000cfe7359410004fd735941000cfc73594100067f53594100067d5359410004ff7259410004fc725941003cff715941003cfd715941001cff705941001cfe705941001cfd705941001cfc705941001e7e505941001e7c505941003cfe7598810004fd7598810004ff7498810014fe7498810004fd7498810014fc7498810004ff739881000cfe7398810004fd739881000cfc739881001eee7298810006ef4298810006ee4298810006ed4298810006ec4298810006ef3298810006ee3298810006ed3298810006ec329881001cfe709881001eee209881001eec2098810006ef7598810006ee7598810006ed7598810006ec7598810006ef7498810006ee7498810006ed7498810006ec7498810006ef5498810006ee5498810006ed5498810006ec5498810006ef7398810006ee7398810006ed7398810006ec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec4398810006ee7198810006ec7198810006ef4198810006ee4198810006ed4198810006ec4198810006ef3198810006ee3198810006ed3198810006ec319881001eef709881001eee709881001eed709881001eec709881001eef509881001eee509881001eed509881001eec509881001eef409881001eee409881001eed409881001eec409881001eef309881001eee309881001eed309881001eec309881001eef109881001eee109881001eed109881001eec1098810004ff75588100067f75588100047f755881003cfc75588100067c755881003c7c7558810004ff7458810014fe7458810004fd7458810014fc7458810004ff735881000cfe7358810004fd735881000cfc735881001eef7258810006ef4258810006ee4258810006ed4258810006ec4258810006ef3258810006ee3258810006ed3258810006ec325881019cff71588100c4fd7158810006f4715881001cff705881001cfe705881001cfd705881001cfc705881001eee205881001eec205881001ef7105881001ef51058810006ef75588100066f7558810006ee7558810006ed7558810006ec75588100066c7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810006ee7158810006ec7158810006e47158810006ef4158810006ee4158810006ed4158810006ec4158810006ef3158810006ee3158810006ed3158810006ec315881001eef705881001eee705881001eed705881001eec705881001eef505881001ee
  | 2 => 0x4fe76885100067f65885100067c6588510006bf64885100d6bc6488510006df63885100bedc6388510006ef6288510006ec6288510007e72188510005f67688510006f67688510004f676885101f5f675885101f5f47588510007776588510007746588510215f77488510215f57488510007b7648851020fb464885101cdf773885101cdf57388510007d76388510207d463885101ddf57288510007e76288510006f66288510006f46288510007e46288510006e46288510007e75288510007e4528851020fe6428851020fe54288510207e63288510207e5328851001df6708851001df470885101ffe6208851001cfc76485100057f75485100057c75485100067f65485100067c6548510006bf64485100cebc6448510006df63485100c6dc6348510006ef6248510006ec6248510005fb704851001df8704851001cf476485100077775485101f5f675485101f5f475485100077475485100057475485100077765485100077465485101edf774485101edf57448510007b764485101e7b464485101ddf773485101ddf57348510007d763485101d7d46348510007e77248510007e76248510006f66248510006f46248510007e46248510006e46248510007f3704851001df6704851001df47048510007f07048510004fe76085100067f65085100067c6508510006bf64085100b6bc6408510006df63085100aedc6308510006ef62085101cdf67108510007e52108510004fe76d41100067f65d411003e7c65d4110006bf64d41100a6bc64d4110006df63d411009edc63d4110006ef62d4110006ec62d4110005f671d4110005f571d411003cff7654110004fd765411003cfc76541100067f655411003e7c6554110006bf6454110086bc6454110006df635411007edc6354110006ef6254110006ec6254110005f77154110005f47154110004fe76c81100067f65c81100067c65c8110006bf64c81101c6bc64c8110006df63c81101bedc63c8110006ef62c8110006ec62c8110005f671c8110005f571c8110007e521c8110004fd7648110004fc76481100067f65481100067c6548110005df7348110045dc7348110006df63481101b6dc6348110005f77148110005f47148110007e521481100067f65c41100067c65c4110006bf64c4110066bc64c4110006df63c4110036dc63c4110006ef62c4110006ec62c411001df671c411001ef761c411001cfa76c41100077b65c41100077865c4110007bb64c41101afb864c4110007db63c41101a7d863c4110007eb62c4110007e862c411001dfa71c411001efb61c411001ff361c4110007f351c4110007f051c41101aff241c41101aff141c41101a7f231c41101a7f131c4110007f221c4110007f121c411001e7f7559410004ff7459410014fe7459410004fd7459410014fc745
  | 3 => 0xc63d4910006ef62d4910006ec62d4910004ff7694910004fe7694910004fd7694910004fc76949100067f659491003e7c6594910006bf6494910296bc6494910006df639491028edc6394910006ef6294910006ec6294910005f67194910005f57194910004ff7654910004fe7654910004fd7654910004fc76549100067f655491003e7c6554910006bf6454910286bc6454910006df635491027edc6354910006ef6254910006ec6254910005f77154910005f4715491003cff7614910004fe7614910004fd761491003cfc76149100067f651491003e7c6514910006bf6414910276bc6414910006df631491026edc6314910006ef6214910006ec6214910005f67114910005f5711491001cfe76d451001cfc76d45100067f65d451003e7c65d4510006bf64d4510116bc64d4510006df63d451010edc63d4510006ef62d4510006ec62d451001dfa70d4510005f970d451001df676d45101f6f676d451001cf676d45101f6f765d45100077765d45100067765d45101f6f565d45101f77465d45101f5f774d4510265f574d4510007b764d4510116f664d4510116f464d451025fb464d4510116b464d45101f5f773d4510255f573d4510007d763d451010ef663d451010ef463d451024fd463d451010ed463d4510005f572d4510007e762d4510006f662d4510006f462d4510007e462d4510006e462d451001df670d45101f7f270d45101f7f170d451001df470d4510004fe76945100067f659451003e7c6594510006bf6494510106bc6494510006df63945100eedc6394510006ef6294510006ec62945101f5f6719451001cfc76545100067f655451003e7c6554510006bf64545100febc6454510006df63545100f6dc6354510005ef7254510005ec7254510006ef6254510006ec6254510005fb705451001df87054510004fe76145100067f651451003e7c6514510006bf64145100e6bc6414510006df63145100dedc6314510006ef6214510006ec6214510005f676145101f6f676145101f5f675145101f77675145101f6f765145100077765145100067765145101f6f565145101f77465145101f5f77414510245f57414510007b764145100e6f664145100e6f4641451023fb464145100e6b464145101f777541451023f7554145101f5f77314510235f57314510007d763145100def663145100def4631451022fd463145100ded463145101f777531451022f755314510005f57214510007e76214510006f66214510006f46214510007e46214510006e462145100077652145101f774521451001df6701451001df4701451022776501451022774501451001cfe76c85100067f65c85100067c65c8510006bf64c851021ebc64c8510006df63c851019edc63c8510006ef62c8510006ec62c851001dfa70c8510005f970c8510
  | 4 => 0x8910006f57198910006f64198910006f54198910006f63198910006f53198910006f9709891014ef610989100057f75589100057c75589100067f65589100067c6558910005bf745891004dbc7458910006bf6458910006bc6458910005df7358910045dc7358910006df6358910006dc6358910004ff75589100067f75589100047f755891003cfc75589100067c755891003c7c7558910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc7358910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc6318910006ed621891003cfe7518910004fd7518910004ff7418910014fe7418910004fd7418910014fc7418910004ff731891000cfe7318910004fd731891000cfc7318910006ee7218910006ef4218910006ee4218910006ed4218910006ec4218910006ef3218910006ee3218910006ed3218910006ec32189100acfc7118910006f64118910006f54118910006f63118910006f5311891001cfe701891001cfc7018910136f61018910136f41018910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e57118910007e64118910007e54118910007e63118910007e53118910137e61018910137e41018910006ef7518910006ee7518910006ed7518910006ec7518910006ef7418910006ee7418910006ed7418910006ec7418910006ef5418910006ee5418910006ed5418910006ec5418910006ef7318910006ee7318910006ed7318910006ec7318910006ef5318910006ee5318910006ed5318910006ec5318910006ef4318910006ee4318910006ed4318910006ec4318910136ef7118910006ef4118910006ee4118910006e64118910006ed4118910006e54118910006ec4118910006ef3118910006ee3118910006e63118910006ed3118910006e53118910006ec3118910006ef7018910136ee7018910006ed7018910136ee5018910136ec5018910006ef4018910136ee4018910006ed4018910136ec4018910006ef3018910136ee3018910006ed3018910136ec3018910136ee1018910136e61018910006ed1018910136ec1018910136e4101891003cff76d4910004fe76d4910004fd76d491003cfc76d49100067f65d491003e7c65d4910006bf64d49102a6bc64d4910006df63d491029ed
  | 5 => 0x6de72d8d10006dd72d8d10006dc72d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d102aedf71d8d10046de71d8d10046dd71d8d10046dc71d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df70d8d102aede70d8d10046dd70d8d102aedc70d8d102aede50d8d102aedc50d8d10006df40d8d102aede40d8d10006dd40d8d102aedc40d8d102aede20d8d102aedc20d8d102aede10d8d10046dd10d8d102aedc10d8d100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d891003cfe75d8910004fd75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d8910006ef42d8910006ee42d8910006ed42d8910006ec42d8910006ef32d8910006ee32d8910006ed32d8910006ec32d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89101ffe771d8910007e641d8910007e541d8910007e631d8910007e531d89101ffe610d89101ffe410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d89101feef71d8910006ed71d8910006ef41d8910006ee41d8910006ed41d8910006ec41d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d89101feee70d8910006ed70d89101feec70d89101feee50d89101feec50d8910006ef40d89101feee40d8910006ed40d89101feec40d8910006ef30d89101feee30d8910006ed30d89101feec30d89101feee10d89101feec10d89100057e75989100057d75989100067f65989100067c659891004dbe7498910005bd7498910006bf6498910006bc6498910045de7398910005dd7398910006df6398910006dc6398910006ef629891003cfe75989100067e759891003c7e7598910004fd75989100067d75989100047d7598910004ff7498910014fe7498910006be7498910014be7498910004fd7498910006bd7498910004bd7498910014fc7498910004ff739891000cfe7398910006de739891000cde7398910004fd7398910006dd7398910004dd739891000cfc7398910004fd719
  | 6 => 0xc64195100073c64195100063c64195100067f63195100067e63195100067d63195100067c63195100075c63195100065c631951022777711951000776411951000775411951000776311951000775311951022776101951022774101951003e7f741951003e7e741951003e7d741951003e7c741951003e7f731951003e7e731951003e7d731951003e7c73195100067f43195100067e43195100067d43195100067c431951003e7f721951003e7e721951003e7d721951003e7c72195100067f42195100067e42195100067d42195100067c42195100067f32195100067e32195100067d32195100067c321951003e7f711951003e7d71195100067f41195100067e41195100067d41195100067c41195100067f31195100067e31195100067d31195100067c311951003e7f701951003e7e701951003e7d701951003e7c70195100067f40195102267e40195100067d40195102267c40195100067f30195102267e30195100067d30195102267c30195102267e20195102267c20195102267e10195100067d10195102267c101951004dbe76d911004ebe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d91102b7b771d911004fb471d9110007b631d9110007b531d91102b7b610d91102b7b410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf32d9110006be32d9110006bd32d9110006bc32d91102b6bf71d911004ebe71d911004ebd71d911004ebc71d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf70d91102b6be70d911004ebd70d91102b6bc70d91102b6be50d91102b6bc50d9110006bf30d91102b6be30d9110006bd30d91102b6bc30d91102b6be20d91102b6bc20d91102b6be10d911004ebd10d91102b6bc10d9110045de76d8d10046de76d8d1000cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d102afd771d8d10047d471d8d10007d641d8d10007d541d8d102afd610d8d102afd410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10
  | 7 => 0x8610007e67208610136f76208610137e76208610136e76208610006f56208610137e46208610007e75208610007e452086102cfe642086102cfe542086102c7e632086102c7e53208610135f77008610135f57008610137e6200861001df976c4210006f976c421001ff271c421003cfe76d9510006bc64d9510006dc63d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100067f54d95100067e54d95100067d54d95100067c54d9510004ff73d951000cfe73d9510004fd73d951000cfc73d95100067f53d95100067e53d95100067d53d95100067c53d9510004fe72d9510004fd72d951003cfe71d9510006f571d951003cfc71d951001cfe70d951001cfc70d951003c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100077571d95100077641d95100077541d95100077631d95100077531d95102bf7610d95102bf7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95102be7f71d95100067d71d95100067571d95100067f41d95100067e41d95100067d41d95100067c41d95100067f31d95100067e31d95100067d31d95100067c31d95100067f70d95102be7e70d95100067d70d95102be7c70d95100067f40d95102be7e40d95100067d40d95102be7c40d95100067f30d95102be7e30d95100067d30d95102be7c30d95102be7e20d95102be7c20d95102be7e10d95102be7c10d95100067f659951004dbe7499510005bd7499510006bc6499510045de7399510005dd7399510006dc6399510005ee7299510005ed7299510005bf745951004dbc7459510006bc6459510005df7359510045dc7359510006dc6359510005ef7259510005ec72595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc7459510004ff7359510006df7359510004df735951000cfe7359510004fd735951000cfc7359510006dc735951000cdc7359510004ff7259510006ef7259510004ef7259510004fc7259510006ec7259510004ec7259510004ff7159510006f77159510004ff7059510006fb7059510004fe761951003e7e65195100067d6519510006bc6419510006dc63195100057e76195100067e76195100047e76195100067f64195100067e64195100067d64195100067
  | 8 => 0x1df470887100057f75487100057c7548710005f77648710006f77648710007777548710185f67548710185f475487100077475487100057475487102edf774487102edf574487102e5f773487102e5f57348710007e77248710007e76248710006f66248710006f46248710007e46248710006e4624871001df6704871001df4704871001cfd7608710006ee6208710006ed6208710007e5210871001dfa7008710005f9700871003e7e65d43100067d65d4310005f671d4310005f571d431003cff765431003e7e65543100067d6554310005f77154310005f47154310005f671c8310005f571c8310007e521c831001e7f7559610004ff7459610014fe7459610004fd7459610014fc74596100067f54596100067d5459610004ff735961000cfe7359610004fd735961000cfc73596100067f53596100067d5359610004ff7259610004fc725961001cfc705961001e7e505961001e7c505961003cfe7598a10004fd7598a10004ff7498a10014fe7498a10004fd7498a10014fc7498a10004ff7398a1000cfe7398a10004fd7398a1000cfc7398a1001eee7298a10006ee4298a10006ed4298a10006ee3298a10006ed3298a1001cfe7098a1001eee2098a1001eec2098a10004ff7558a1003cfc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a1001eef7258a10006ee4258a10006ed4258a10006ee3258a10006ed3258a1001eee2058a1001eec2058a1001ef71058a1001ef51058a1003cff76d4a1001cfe76d4a10004fd76d4a1001cfc76d4a10006ee62d4a10006ed62d4a10005f671d4a10005f571d4a10004ff7694a1001cfe7694a10004fd7694a1003e7e6594a100067d6594a10004ff7654a1001cfe7654a10004fd7654a1001cfc7654a10005f77154a10005f47154a1003cff7614a1001cfe7614a10004fd7614a1003e7e6514a100067d6514a10006ee6214a10006ed6214a1003e7e65d46100067d65d461001dfa70d4610005f970d46102be7f659461003e7c659461000777519461003cff765461003e7e65546100067d6554610005ef7254610005ec7254610005fb705461001df870546102267f651461003e7c6514610006ee62c8610006ed62c861001dfa70c8610005f970c861017ef665c861014ef465c861014ef764c86102def564c861014ef763c86102d6f563c861014fe662c8610006f562c861014fe562c8610006e562c861014ff270c861014df570c8610007f170c861014fe720c86101feef62886100057f75486100057c7548610006ee6248610006ed6248610005fb704861001df87048610007e52108610135f57608610006f57608610156f66508610136f46508610136f764086102cef56408610136f763086102c6f5630
  | 9 => 0xd7459710014fc7459710004ff735971000cfe7359710004fd735971000cfc7359710004ff7259710006ef7259710004ef7259710004fc7259710006ec7259710004ec7259710006f4715971003e7e65197100067d65197100057e75d8b100057d75d8b10065be74d8b10005bd74d8b10035de73d8b10005dd73d8b10006ef6298b1003cfe7598b10004fd7598b10004ff7498b10014fe7498b10004fd7498b10014fc7498b10004ff7398b1000cfe7398b10004fd7398b1000cfc7398b10006f64198b10006f54198b10006f63198b10006f53198b1014ef61098b1014ef41098b10004ff7558b1003cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b10006ed6218b1003cfe7518b10004fd7518b10004ff7318b1000cfe7318b10004fd7318b1000cfc7318b10006f67118b10006f64118b10006f54118b10006f63118b10006f53118b10006f97018b1003cff76d4b10004fe76d4b10004fd76d4b10004ff7694b10004fe7694b10004fd7694b10004fc7694b1003e7e6594b100067d6594b10005f67194b10005f57194b10004ff7654b10004fd7654b10004fc7654b10005f77154b10005f47154b1003cff7614b10004fe7614b10004fd7614b1003cfc7614b1003e7e6514b100067d6514b10005f67114b10005f57114b10005f576d4710186f576d4710186f765d4710186f565d4710185f774d4710335f574d4710116f664d4710116f464d4710185f773d471032df573d471010ef663d471010ef463d4710005f572d4710006f662d4710006f462d471001df670d471001df470d471001cfd769471003e7e65947100067d659471001dfa7094710005f97094710005ef7254710005ec725471001cfd761471003e7e65147100067d651471001dfa7014710005f9701471001df57614710186f5761471001cf57614710187767514710186f76514710187766514710186f56514710007756514710185f77414710325f574147100e6f664147100e6f4641471018777541471031f755414710185f77314710315f573147100def663147100def4631471018777531471030f755314710005f57214710006f66214710006f4621471000776521471018774521471001df67014710187f27014710187f1701471001df4701471022776501471022774501471001cfd7688710006ee6288710006ed6288710007e7218871001dfa7088710005f9708871001cf57688710185f67588710185f47588710305f77488710305f574887102fdf773887102fdf57388710006f66288710007e66288710007e56288710006f46288710007e75288710007e452887102f7e642887102f7e54288710167e63288710167e5328871001df67088710007f27088710007f17088710
  | 10 => 0x8550004fd73d855000cfc73d8550004fe72d8550004fd72d8550006f741d8550006f441d8550006f731d8550006f431d8550006f76198550005bf7458550085bc7458550005df735855007ddc7358550005ef7258550005ec7258550006f56118550004ff7418550014fe7418550004fd7418550014fc74185500067f54185500067d5418550004ff731855000cfe7318550004fd731855000cfc73185500067f53185500067d5318550004fe7218550004fd7218550006f74118550006f44118550006f73118550006f431185502267e50185502267c501855001cfe7694550006f76194550006f4619455001dfa7094550005f9709455001cfc7654550005ef7254550005ec7254550006f76154550006f46154550005fb705455001df87054550004fe7688550004fd7688550004fc7688550006ef6288550006ec6288550004ff7648550004fe7648550004fc76485500057f754855003d7c7548550004fe7608550004fd7608550004fc7608550006f76108550006f46108550007e52108550004ff7498450014fe7498450004fd7498450014fc7498450004ff739845000cfe7398450004fd739845000cfc7398450004fe7298450004fd729845003e7c529845001ef6719845003ef7519845003ef45198450006f64198450006f54198450006f63198450006f5319845001ef6109845001ef41098450004ff7458450014fe7458450004fd7458450014fc7458450004ff735845000cfe7358450004fd735845000cfc7358450004ff7258450006ef7258450004ef7258450004fc7258450006ec7258450004ec725845001ef7715845003ef7515845003e7c515845003ef45158450006f64158450006f54158450006f63158450006f5315845001ef6105845001ef4105845003d7d76944500067d769445003e7f649445034e7d649445003e7f63944503467d63944500057e72944500067e629445003d7e719445003f7671944500067d61944502bd7d70944502be7e609445003f7a6094450004ff768845001cfe7688450004fd768845003d7e75884500057d758845033f6c5288450006f66188450006f56188450004ff7648450004fd764845001cfc76484500057f754845003d7c7548450006f66148450006f56148450004ff760845001cfe7608450004fd76084500057f750845003d7c7508450157745108450007e52108450004ff74d9710014fe74d9710004fd74d9710014fc74d97100067f54d97100067d54d9710004ff73d971000cfe73d9710004fd73d971000cfc73d97100067f53d97100067d53d9710004fe72d9710004fd72d9710006f671d9710006f970d97102be7e50d97102be7c50d9710004fd76997100067f659971003cff7659710005ef7259710005ec72597100067f7559710004ff7459710014fe7459710004f
  | 11 => 0x1ef6309865001ef5309865001ef4309865001ef7209865001ef6209865001ef5209865001ef42098650004ff7458650014fe7458650004fd7458650014fc7458650004ff735865000cfe7358650004fd735865000cfc7358650004ff7258650004fc725865001ef77158650006f74158650006f64158650006f54158650006f44158650006f73158650006f63158650006f53158650006f4315865001cfc705865001ef6105865001ef41058650006f575586501f6f47558650006f77458650006f67458650006f57458650006f474586501f6f75458650006f65458650006f554586501f6f45458650006f77358650006f67358650006f57358650006f473586501f6f75358650006f65358650006f553586501f6f45358650006f74358650006f64358650006f54358650006f44358650006f77258650006f67258650006f57258650006f472586501f6f752586501f6f45258650006f74258650006f64258650006f54258650006f44258650006f73258650006f63258650006f53258650006f4325865001ef7705865001ef6705865001ef4705865001ef7505865001ef6505865001ef5505865001ef4505865001ef7405865001ef6405865001ef5405865001ef4405865001ef7305865001ef6305865001ef5305865001ef4305865001ef7205865001ef6205865001ef5205865001ef42058650006ee6294650006ed6294650006f66194650006f5619465003f77519465001dfa7094650005f970946502be7f649465036e7d64946502be7f63946503667d63946500057e72946500067e62946502bf6e62946500066e62946502bf6d629465003d7e71946502bf7661946500067d61946502bf7561946502bf7a70946502bd7d709465000779709465003e7e6094650005ef7254650005ec7254650006ee6254650006ed6254650006f66154650006f56154650005fb705465001df870546502257d761465003e7d76146502267f641465035e7d64146502267f63146503567d63146500057e72146500067e62146502276e62146500066e62146502276d621465003f7671146502277661146500067d611465022775611465000675611465035f77411465035f74411465035777311465035774311465003d7f70146502257d701465003f7a6014650004ff768865001cfe7688650004fd768865003d7e75886500057d7588650006ee6288650006ed62886500076c5288650006f66188650006f56188650004ff7648650004fd764865001cfc76486500057f754865003d7c7548650006f66148650006f56148650004ff760865001cfe7608650004fd76086500057f750865003d7c7508650006f66108650006f56108650007745108650007e52108650004ff74d8550014fe74d8550004fd74d8550014fc74d8550004ff73d855000cfe73d
  | 12 => 0x46348421377e75348421377e65348421377e55348421377e45348421377e64348421377e54348421377e44348421007e77048421007e67048421007e57048421007e47048421135e47048421377e73048421377e63048421377e53048421377e43048421007e521d8021007e52198021006fb60980210057f75580210057c7558021005df73580210addc7358021007e52158021004ff75580210067f75580210047f755802103cfc75580210067c755802103c7c7558021004ff7358021006df7358021004df735802100cfe7358021004fd735802100cfc7358021006dc735802100cdc7358021006f75158021006f45158021006f64158021006f54158021006f63158021006f53158021006f62158021006f52158021006e52158021007e5211802101efa6018021006f9601802101cfe7598750004ff7498750014fe7498750004fd7498750014fc749875003e7f54987500067d5498750004ff739875000cfe7398750004fd739875000cfc739875003e7f53987500067d5398750004fe7298750004fd729875003ef6719875003ef7519875003ef451987502be7e509875003e7c509875001cfc7558750004ff7458750014fe7458750004fd7458750014fc7458750004ff735875000cfe7358750004fd735875000cfc7358750004ff7258750004fc725875003ef7715875003ef7515875003ef45158750004ff768875003cfe7688750004fd7688750006ee6288750006ed6288750004ff7648750004fd764875003cfc76487500057f754875003d7c7548750004ff760875003cfe7608750004fd7608750006f66108750006f56108750007e52108750004ff7498650014fe7498650004fd7498650014fc7498650004ff739865000cfe7398650004fd739865000cfc7398650004fe7298650004fd729865001ef67198650006f74198650006f64198650006f54198650006f44198650006f73198650006f63198650006f53198650006f4319865001cfe709865001ef6109865001ef41098650006f77598650186f67598650006f77498650006f67498650006f57498650006f47498650186f75498650006f65498650006f55498650186f45498650006f77398650006f67398650006f57398650006f47398650186f75398650006f65398650006f55398650186f45398650006f74398650006f64398650006f54398650006f44398650006f77298650006f67298650006f57298650006f47298650186f75298650186f45298650006f74298650006f64298650006f54298650006f44298650006f73298650006f63298650006f53298650006f4329865001ef6709865001ef5709865001ef4709865001ef7509865001ef6509865001ef5509865001ef4509865001ef7409865001ef6409865001ef5409865001ef4409865001ef73098650
  | 13 => 0x942100cfc73d94210067f53d94210067d53d9421004fe71d9421006f671d942101cfe70d9421004fd70d9421004fd76994210067f659942103cff76594210067f7559421004ff735942100cfe7359421004fd735942100cfc7359421006f47159421004ff705942101cfc705942103e7e65194210067d6519421004fd76d4421005f576d4421156f576d4421156f765d4421156f565d4421155f774d44213fdf574d4421116f664d4421116f464d4421155f773d44213f5f573d442110ef663d442110ef463d4421157e772d4421005f572d4421157e472d442117ef662d4421157e752d44213efe642d44213efe542d44213e7e632d44213e7e532d4421135f670d4421004ff769442103cfd769442103e7e65944210067d6594421005ee7294421005ed7294421155f67194421004ff7654421005ef725442103cff7614421004fe7614421004fd761442103cfc761442103e7e65144210067d6514421005ee7214421005ed7214421007755114421005f57614421156f57614421004f57614421155f67514421157767514421156f76514421157766514421156f56514421007756514421155f774144213ddf574144210e6f664144210e6f464144211577754144213cf755414421155f773144213d5f573144210def663144210def463144211577753144213c7755314421157e67214421005f57214421157e57214421005e5721442117ef66214421157e75214421007765214421157745214421157e452144211576452144213cfe642144213cfe542144213c7e632144213c7e53214421135f67014421155f67588421155f475884213bdf774884213bdf57488421395f77388421395f5738842137df5728842137de572884213b6f66288421007e66288421007e75288421007e452884213afe642884213afe542884213a7e632884213a7e53288421135f67088421004ff76484210057f75484210057c7548421005f77648421006f77648421004f77648421007777548421155f67548421155f4754842100774754842100574754842139df7744842139df5744842137df7734842137df57348421395f7724842138ef66248421007e66248421007e75248421007e65248421007e55248421007e45248421387e74248421387e64248421387e54248421387e44248421377e73248421377e63248421377e53248421377e43248421135f47048421007e77648421005e77648421006e77648421007e77548421007677548421007e67548421155e67548421007e57548421007e47548421155e47548421007647548421005647548421007e76548421007e66548421007e56548421007e4654842137fe7734842137de77348421377e6734842137fe5734842137de57348421377e47348421377e76348421377e66348421377e56348421377e
  | 14 => 0x57d75d82210d5be74d8221005bd74d82210bdde73d8221005dd73d8221006fb6098221004ff755822103cfc7558221004ff7458221014fe7458221004fd7458221014fc7458221004ff735822100cfe7358221004fd735822100cfc7358221006ef5258221006ec5258221006ee4258221006ed4258221006ee3258221006ed3258221006ef215822101efa6018221006f9601822103cfe76d9521004ff73d952100cfe73d9521004fd73d952100cfc73d95210067f53d95210067e53d95210067d53d95210067c53d952101cfe70d9521004fd70d952103c7e76d95210067f63d95210067e63d95210067d63d95210067c63d95210067f73d95210067e73d95210067d73d95210067c73d95210067e43d95210067d43d95210067c43d95210067f71d95210067d71d95210067f41d95210067e41d95210067d41d95210067c41d95210067f31d95210067e31d95210067d31d95210067c31d95210067f70d95210067e70d95210067d70d95210067c70d95210067f30d95210067e30d95210067d30d95210067c30d95210067f65995210067f7559521004ff735952100cfe7359521004fd735952100cfc7359521004ff7159521006f77159521004f77159521004ff705952101cfc7059521004fe761952103e7e65195210067d65195210057e76195210067e76195210047e76195210067f63195210067e63195210067d63195210067c631952103e7f731952103e7e731952103e7d731952103e7c73195210067e43195210067d43195210067c431952103e7f711952103e7d71195210067f41195210067e41195210067d41195210067c41195210067f31195210067e31195210067d31195210067c31195210067d211952103e7f701952103e7e701952103e7d701952103e7c70195210067f30195210067e30195210067d30195210067c3019521004fe76d45210067f65d452103e7c65d4521005ee72d4521005ed72d4521004fe76945210067f659452103e7c659452103cff7654521004fd765452103cfc76545210067f655452103e7c6554521005ef7254521005ec7254521004fe76145210067f651452103e7c65145210067f65885210067c65885210076f658852133eee658852133eec65885210076c65885210066c658852140eef648852140eed6488521406ef6388521406ed6388521007e76188521005ed70885210067f65d81210067c65d812103cfe75d8121004fd75d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210057e75981210057d75981210067f65981210067c6598121006fb60981210057f75581210057c75581210067f65581210067c6558121005df73581210c5dc73581210067f65181210067c651812114ef7611812101efa6018121006f96018121004ff73d942100cfe73d9421004fd73d
  | 15 => 0xf73948514857d739485103e7f639485146e7d639485103d7e729485103f6e72948510067d62948510077771948510057d719485100774719485147e7e619485103f76619485147777419485147774419485146f77319485146f7431948512257e70948511967e609485103d7f76544510067f76544510047f76544514657f74544514657d745445145d7f735445145d7d73544510076f72544510057c72544510076c72544510056c725445103d7f715445103f7771544514567e615445103f7661544512257c7054451004ff7458051014fe7458051004fd7458051014fc745805103e7f54580510067d5458051004ff735805100cfe7358051004fd735805100cfc735805103e7f53580510067d5358051004ff7258051004fc725805103efb705805103efb505805103e7c505805103ef85058051004ff74d9621014fe74d9621004fd74d9621014fc74d9621004ff73d962100cfe73d9621004fd73d962100cfc73d9621006ed72d9621006f671d962101cfe70d9621004fd70d9621004fd76996210067f659962103cff76596210067f7559621004ff7459621014fe7459621004fd7459621014fc74596210067f54596210067d5459621004ff735962100cfe7359621004fd735962100cfc73596210067f53596210067d5359621006ef7259621004ff705962101cfc705962103e7e65196210067d65196210d5be7419621005bd74196210bdde7319621005dd731962103e7e65d4a210067d65d4a21005f671d4a21005f571d4a2133eed76d4a2133eef65d4a2133f6e65d4a2133eed65d4a210076d65d4a2133def74d4a2144ded74d4a212a6ee64d4a212a6ec64d4a2133def73d4a21445ed73d4a2129eee63d4a2129eec63d4a2133fe671d4a21005ed71d4a2133fe571d4a21005e571d4a211fdee70d4a210067f6594a2103e7c6594a2103cff7654a2103e7e6554a210067d6554a21005f77154a21005f47154a210067f6514a2103e7c6514a210076d5214a21005ed7614a2133eed7614a2133f6e7514a2133eef6514a210076f6514a2133eed6514a2133f6c6514a2133def7414a2143ded7414a21276ee6414a21276ec6414a2133f6f5414a214376d5414a2133def7314a2142ded7314a2126eee6314a2126eec6314a2133f6f5314a214276d5314a21005ed7114a211fdee7014a2103cfd769462103e7e65946210067d6594621005ee7294621005ed72946210076c5294621005ef7254621005ec725462103e7e65146210067d6514621005ee7214621005ed721462133f6c5214621005f576c8621006f576c862117ef665c862117ef465c862141ef764c862141ef564c8621416f763c8621416f563c8621007e652c8621007e552c862141fe742c862141fe442c8621417e732c8621417e432c862114ef660c86210057e75d8221
  | 16 => 0x895100cfe7318951004fd731895100cfc7318951006ef4218951006ee4218951006ed4218951006ec4218951006ef3218951006ee3218951006ed3218951006ec3218951156f75118951156f4511895101cfe7018951004fd7018951005ee7618951006ee7618951006ef6418951006ee6418951006ed6418951006ec6418951006ef6318951006ee6318951006ed6318951006ec6318951157e75118951157e45118951006ef7518951156ee7518951006ef7418951006ee7418951006ed7418951006ec7418951156ef5418951006ee5418951006ed5418951156ec5418951006ef7318951006ee7318951006ed7318951006ec7318951156ef5318951006ee5318951006ed5318951156ec5318951006ef4318951006ee4318951006ed4318951006ec4318951156ef7118951156ef5118951156e75118951006ed5118951156ec5118951156e45118951006ef4118951006ee4118951006ed4118951006ec4118951006ef3118951006ee3118951006ed3118951006ec3118951006ef7018951006ee7018951006ed7018951006ec7018951156ef5018951156ec5018951006ef4018951006ee4018951006ed4018951006ec4018951006ef3018951006ee3018951006ed3018951006ec3018951006ef6294951006ec6294951005f67194951005f5719495103f745194951005f77154951005f47154951006ef6294551006ec629455103df6719455103ef7619455149e7f649455149e7d64945514967f63945514967d63945510076f62945510067c62945510076c62945510066c629455103d7e719455103e7f619455103f776194551006ef62d8151006ec62d8151004ff74d8151014fe74d8151004fd74d8151014fc74d8151004ff73d815100cfe73d8151004fd73d815100cfc73d8151004fe72d8151004fd72d8151186f751d8151186f451d8151005ee7298151005ed7298151006ef6298151006ec6298151006fb6098151005bf74581510fdbc7458151005df73581510f5dc7358151005ef7258151005ec7258151006ef6258151006ec62581512be7f6518151006ef6218151006ec621815101efa6018151006f96018151004ff7498851014fe7498851004fd7498851014fc749885103e7f54988510067d5498851004ff739885100cfe7398851004fd739885100cfc739885103e7f53988510067d539885103eee729885103eef529885103eec529885101cfe7098851004fd709885103e7c5098851004ff7458851014fe7458851004fd7458851014fc7458851004ff735885100cfe7358851004fd735885100cfc735885103eef725885103eef525885103e7c525885103eec5258851006f47158851004ff705885101cfc705885103d7d76948510067d769485148d7f749485148d7d749485103e7f64948514767d64948514857
  | 17 => 0x4fd735835100cfc7358351004ff7258351004fc725835103efb705835103efb505835103ef85058351006ef6298a51004ff7498a51014fe7498a51004fd7498a51014fc7498a510067f5498a510067d5498a51004ff7398a5100cfe7398a51004fd7398a5100cfc7398a510067f5398a510067d5398a51006ef4298a51006ec4298a51006ef3298a51006ec3298a5117ef75198a5117ef45198a5101cfe7098a51004fd7098a51004ff7458a51014fe7458a51004fd7458a51014fc7458a51004ff7358a5100cfe7358a51004fd7358a5100cfc7358a51006ef4258a51006ec4258a51006ef3258a51006ec3258a51004ff7058a5101cfc7058a51006ed6218a51005f67194a51005f57194a514c57f7394a514c57d7394a5147e7f6394a5147e7d6394a51007767194a510057d7194a51007757194a5103e7e6194a511967e6094a510057d76d465103e7d76d465103d7f74d46514bd7d74d465103d7f73d46514b57d73d46510057e72d465103f7661d46514af7641d46514af7541d46514a77631d46514a77531d46512bd7e70d4651006fb6098251004ff7458251014fe7458251004fd7458251014fc74582510067f54582510067d5458251004ff735825100cfe7358251004fd735825100cfc73582510067f53582510067d5358251004ff7258251004fc72582511f6f751582511f6f45158251005ee7218251005ed721825101efa6018251006f96018251004ff74d8951014fe74d8951004fd74d8951014fc74d8951004ff73d895100cfe73d8951004fd73d895100cfc73d8951006ef42d8951006ee42d8951006ed42d8951006ec42d8951006ef32d8951006ee32d8951006ed32d8951006ec32d895101cfe70d8951004fd70d8951006ef64d8951006ee64d8951006ed64d8951006ec64d8951006ef63d8951006ee63d8951006ed63d8951006ec63d895133fe751d895133fe451d8951006ef75d895133eee75d8951006ef74d8951006ee74d8951006ed74d8951006ec74d895133eef54d8951006ee54d8951006ed54d895133eec54d8951006ef73d8951006ee73d8951006ed73d8951006ec73d895133eef53d8951006ee53d8951006ed53d895133eec53d8951006ef43d8951006ee43d8951006ed43d8951006ec43d895133eef71d8951006ed71d895133eef51d895133eec51d8951006ef41d8951006ee41d8951006ed41d8951006ec41d8951006ef31d8951006ee31d8951006ed31d8951006ec31d8951006ef70d8951006ee70d8951006ed70d8951006ec70d895133eef50d895133eec50d8951006ef40d8951006ee40d8951006ed40d8951006ec40d8951006ef30d8951006ee30d8951006ed30d8951006ec30d8951006ef6298951006ed6218951004ff7418951014fe7418951004fd7418951014fc7418951004ff731
  | 18 => 0xc004015000001000c002000000c01a003000803c00c000000800400e000002001000a00900180140020000030014006000002801801000000000080000060018000016000004800400000100100100020000008000004001002000400800000000100000070018000004000005001400000b0030034002000002002c00c005000801400800200b805800000100000040000070048014008005001800400000000000200000000018008006000000000000a00300b800400200b002800001000d0000004010002000803800800500000200000000000000000000004802c00600f000000801000600300040000050000004000006000800400000000000000000130020064040004000000400a001000000800000200180000060030000004002000001000000800800000000060090020004000005000000c00c000000000800000300380400020040000004000009002000001000600100200000030018008000002003000800000400200000080070008008016007002800400a0040000034010000002000001000000180040180010008000004002002000000600d0030008000000000000402200000080000100180000008014003001803000a0080010034000000000000000c020000800400000000880080200070008004010000003000c00800c002800000a0000000008000000002800000600200d0000002000001800000000000000000100020000004000006000000c00200b00580140080000128000000000002000001c000000801000000100400000000030000010014004000000400000200100100040020000014000005001000c006002000000c00000c000803001600b00000040000000060010016001009000801200100880000060100058000004003000800000a00000280000040020000028002002008001000c00100080200020030018014006003003802400200e001000001000a000001001600600280000000000048054000003000800400000100000000000010030014018004000001800000d00500200080020000010002015001800800200000180080060030018004000005004ff7498b51014fe7498b51004fd7498b51014fc7498b51004ff7398b5100cfe7398b51004fd7398b5100cfc7398b5103eee7298b5103eef5298b5103eec5298b51006ee4298b51006ed4298b51006ee3298b51006ed3298b5103e7c5198b5101cfe7098b51004fd7098b51004ff7458b51014fe7458b51004fd7458b51014fc7458b51004ff7358b5100cfe7358b51004fd7358b5100cfc7358b5103eef7258b5103eef5258b5103eec5258b51006ee4258b51006ed4258b51006ee3258b51006ed3258b51004ff7058b5101cfc7058b51004ff7458351014fe7458351004fd7458351014fc7458351004ff735835100cfe7358351
  | 19 => 0x1000804800200000100000040040008000002001000000800000a0030008016001002802800801400180380220090000038002002000002800c00700000000000030008004000024001001c00000100000000060070000030000009000000800a0050068004006005005809801c001000800c0000000000014000008000001c00c003001001005201a001800c004001000000000800000780280060000018000000001000804c0040080020000000008003001c00a00000000000020010020034002008001000c008001002802400a00a00100300000030000008006000000001c01400d005001800001e0008004000001000000c00e002001801c00600400100440040080000000004009004800c00e00000180300060070020040006002002000c040000002000000000100480040000010000004000002000001800000c000000000e007001000400a009000002000000000300080000020000064004003001000c002000000000c002000000000800200000180040100070158004002001000000000400d000002c0020050040000002001000002404400500100540100080028000006005009802400000a00280380020000000000000013000001001a004001000000e00000000000200000010000000000000000000e00000000000000090008000002000001802800800000a001800000200180240000000020004008003000004c01a005001001c00c00800200080000000018004004005000000c01e001000001800c00100080000000070000018000005001800c036008006000000400500300000020010000010004000000002c002001002800400c005000001000200c000000c000007000803801c00f0010000004009000000800400200000040120070000060004003002000c00c0060010004012002001000000e00c002802000a0070028000000015008000c00600c0008000000004001800002400000480040000170000004002005005001800000000200180020010000010014009004800400400300100000000100030018006001001001400400200c000c0020000000008004000000000c00200500580000020030008010004001000003c000001003804800e0090008000006005000001800000300400040000010008034000007000800404800600e000400400d00900ac000001004000400800f003800c026000003000000000600000500060000000008000002001000400c00d0030008000002001000000400000000180040050000000036005003000000400000000000000050000024000001000000c002024000000801e000001803c00800100000100020000018004008004000000000000000000240000000020000004005001000400200000b801803801f0020004010006002000401000000000100020040000
  | 20 => 0x4a8ea8a77000005580000009410001bec0000003e5a86101aa1d06827290bab0180000000009ff3888ca80fcad10000eb12910000000001506000000000140d000000265000000034b9b3800025d00012280000004d080dcbf65a81780eac1d678c487000000000001585d06820003c321950a50002ea80000000004fd21181400005e11de800075d3aa000175e08815021585dc1864245c88dda0000000014000afb3cb00011a60005272458ac80003c26c4548e0002081cc000080b1810000878000000000000000000000000000002db0000fde4c7000236271c000081a1faf0500044d1e4d12900033b20390c20703e32998712bf50c490440ee0003659a540008b842100000008d6097a5f80000c7363461761046a5df045334da534ece9fcd7697bcbb428c8365e8d9a24288126353c889fd6781af17ca934c0e6cd54f914088ca765c30b45454245467c3b8aa434f33d03057c458d3a623428d043a0fb8000ba800000a63dcca20000002f1814246b000000138f93d844a768a260000b48000000aff417a2740000004534784536b220000000000b932ad9ea8a08990ba09d64fc09ef00016b538e09f585acc1642adf4542e6520697f80000560b61fa4a3307ce744c400016661143f43f2000000000044daa9565400004f293297052e60b0f7cc9c1ef559df8cd320004a6800000078e10921d81c0b091948001414033c158000000a920000c1ce7a6212f3251a00020100027f40007ac00029c8bb55550eca7a87fe00033845580008cf385aa6565cbc32f700018345440bedd3900863e04884011782590001108000744518ac1918a00028793053c188810e9bb877600026780a433600c441a418a5b6b029ea0d89c60035e7d0816b400046cee68686bc400000011ce2ed3708d900000005a50bf579a0001c7a23411c6ec0e92084000246325821c17caf427122e4e0a00000006a8688000000102928a475000055c000adc00000009c83940000c0150238b40c0000000000000000082c3c400009fe0000004efd5712ef6184f59bfcd560004c7c000000000161220a0009e7452d6458361460000360a360004c8a161794c1139c00000000001c8da90000bbd4c8c0015a4968000177c000bd05240000832b270002f500001f02cc000071a84540d255a0000003caaecc0005603d12a403140dadfd8aa00000003dc00002fa0b9de6c0008a400034080000000002aed5f47d84a8000000041006500002b477c8fa05d3004cae97e8ec0014000001006401a007000800000a002004000800a005000000c0020140010008000003000800c000007000800400200600080040100090008008000000007000800e00c000800000601d000800001a0010000044004006003000000800f001800800a002001000000c0010008000006000001001c008
  | 21 => 0x44b3000000000028255600025d00000000000001752bfd22c0000000ac64db86780000004d22cdc2de00013100001aab814f307080002dc000000000005239388c418a0e5466c83c7a09dd259800135e05e000000129c441458c0000000004f4e4512ce018ca0278d36a5c052c00009fe79c4dd2b9cd346f923a02c563e0000000000bba00058f26a534e73c15c8000b741a15bc80017a700000000011329950001a7512a00015515d546f8b327023280005730a391f00003bc4ea671a00000008b80937f81dd5ec0000a20b4f31695a4c946b70000ba0000848000248eff800000028dc7de5bf0002abcb1f69132d80000007e223b000000000000009d04925c92f240f94e01ea3178ea4e843494ebd67e974b171fc13c4192c0c0372d4d130c190949edc578034180abc578028435493784281b616f8958000202b2494354ce00055680012105354aedfd01987e95431da85b2055cd7220851b24c00000006ca7bc2b3dbf848e32e00009dc000299ce20121544345470166b7442ba3a81fdd4ac3a24939e90fa88a8a19abe04d46285cd923c83412b57327503784012f128caf3a4d00b80000ed883a57490b498c6be000236182e3504e58001494b3200012086140000ca90c4000ac349843200003aa00013b45d49c614e00000005840001a790fc0004c32465337330a27000000000000003d00e6000453e83c6b200000000009ea30a9b92afc62c0002529a49303b67315919c0660001ce9dd02e67990000ce20006a700023fc2a474761294cc99a3984971f343c605d0000762ef029f1b100017ec7870000a6a91c16e44f026528ba1a3905826524bed53441180008f05989ef516a07a2a71cc8cd26d75a4a87b4a8bd934c197e00000009bad6144200041e1348c840d60000000c9a7dd00012447ec54200027ccbea95a0688bbcc2a62002e005403c94780018cc5ac0002d980000000004110000750aac336ab0865e8cd2b100002ca9724a96898918bc10002ab912e05703623a922d22e2e600004da50900002fc0001df0d100ed3045490001a4c0c80001121bf52940a95061018d7e0001b0903d359bc900009a56ae03babba6f4510088962134c5ec65a00c80000006055e42efc000a8f0b400017240000000000f9e00019f1b3140aa16000000000000054aadc4b76a5a2b2855100e325046c270cc78a638aa364a3e0f90b1199400081534190d000060e000000039ca1f32200007cc00059427306d604700002b01369d100005300d217987b82100007295ac8000000a772652bac1000002b71bd00006b13ad112c00012d574000034e3192b0a720420bba000152849a0006012ae84f00000e758301199f50000000a163ce5499d7a66d71e485803ca5a85313198012aa1ae11f9b708cc4b500d05342f81bf4670a6513e3774980cdc00007f
  | 22 => 0x2000270927a6774452f80e0400000000002ce095000084400000000000d82a01ad0002d3800061f000199800000000014683070005539940be08ac380994c000887000000000000000029f515d01ea112e2846a0002b78c6c58a7254a2000000000000006354981c6c89636ea308080f708a5354a9115886e0dea76b05a8ee84a40003c48b2040685239144c51767ed5a921fe694a733c121f00008bd5e9800181c00055d80001600001638000df8afe48e009c476000000025a7f43a309f27b933d00000009ad11e0004bb1ff42f654811811e183c0005bd0cd07b61f8cf155d80c66a05a39ca92f32ff000000076600000000010880000002f38000955800000000000000013ed53600036a9cbcefc37024e800000000047c27d8956380000052d6366bc29080600009c892013e80007a900007f85c24f919eaa90bb0b160001930ef8773509ab8000000041711780000002590000cc6b4820c04c80000002140000000000000000000000000020993e471f0002c0ac76b2d33aa9490b456b40000002da87a000000048800023b90982860000c344780005f788f81608061f4000000053093100010a50404dd00000014763378002f2a000000456400000014025e0000ffc000483b000b6222c1ea17700261884402e2ca7e2ae1a91c645c025832317641a6a3a2f5abcc696322339c0000009d3abf98e00aa4a200005ef76a0000000000be29185b2816e07aa6ad4c049d32591e0002154f570000f6000000000000000000000002f216480005463dd00004a800017a1009336ba06029b90f3e8be53401f722a96452002d80000d24060001676000582404800048428b800068017c8000dfc000b5c4f0c00060c280292a5dc0008e99ed0cc0f90bde2d182c86fa95d05e1b44e1eb8e02797580009ad0000000f46381000109138a236333802c8c600000000003f2925000150444e22200029b8204000543800006daa0000000000000000000014f828333a28211fc90120f9c591129a85b9ac70c20b001b613b8c8a0003cd800021c8a416b82d04b635f00010bc0008c440ea7e43227c04590000cc1b365233028000beb0002b396be11c5c1277d356b253d01b2963035d00000013444850000000000000000000055e00006f0000434a615be0000db0000097c00000000000000000000004dced7511c00054e9320ff6ab915b000068451c36300000000001b1a8c0000194324000159a00000000000009f800000000000000000000a0eb1a531a3c800000031f94f00009e3d9a8a386a6334ca42a5000000000013f8d1c0004d99bcc0005c743ca1f335100043a2c1d550000000220444020708a8f8c0006f70000000f823b13fd1c7536d3510000000000000000000000000032c00000c0b98000208c00087b00000017fc59d40780010fe0000000a4
  | 23 => 0x4834a84000000013260004f10000000c0313f4bac0000e82d33090000b3e00000000000002731ea000014f0000000e342700002b50c6e68f5b80420f340000bb0000000000151000000046500015c023a193207037cfb200000000011967b348dc0000000ed4b72db00000000002fe42660005d42ddcfec3d600000003bc00037c1f4cb3e46043680000004830000000afc40d5a8194859c0005cb80010229d50000000d147b154d000084a2c62fedb3cc604bd335257acdc4cb2c9955d5900000462db90686479668000cb258f1099c5a89825024ba1f6ab3a655d29ef84f6a8d00023fa0a629021c000056400000028b03ed85182006a4f556881f92c0864c0830000000d5c52729c00004d84e90e200014ba3f75f72d554b24480002cb0cd349f336680d2fe656b70defd1d2b3a4e9a8f80477712490f78a644e70651cfcad4a0d3c200011b616b338e57821482a2251e980005de0478000be81631e8800000072b0000c440008e880025ec0000004b480016281a041425f22ee00003698b000099f2ed13bc00054d00000014a20000001e210e000048222a694c46c0de9728aa032d4722b657a5ac02c294145468aac88ef2d1db7ca53d00744d086800000000000004d5499cc3cb720bc0838000ab53518001250b334b513f4fa05a90001db73148ec5088300000000000000000000032780003a200000026ff1206ea305000122b6169e1937c2fe15b5da256a01c7580890bec0860003394d98b5e00042f0a5876e884000209cc4aa014b6a348f5c6e91bd2e752be000494c00090c8a74a9c0008b40004a8492c00000000028d04ec2d000004f000086901508f8c46000000105021548d1bcadac00051953580016528e55199dc8d805942f18e1d27938592e0b3c376000000143000000008a05b12933041650b501ea000361811600000000000000009ec0001eb400000035b00000003f30000001028000164b0700000000c09f555bc5b40000000000000522000000060646e62e838b7682501a10f849260c180012a4c2801113944c257a0f29480d0e00014d0fd459829e558125083a172366400117e85c00000000000000001b6b70800017392782b218c4fa1ae46ab7cc4bc6924ecc03900005e54380003359fc800000000023b8e8a2fe000000137d92314ba07892c000438800100c7434bd40000006435e5cfc43002e5000273c0009c042a00017c619002c8c8d3779c0cdc5fcc00e33b9e42ed80000000c215980005004dd4954f0282d07206cd7780003312544e900002e6800000000020b9cd0000a840a2a02962a1ba3b240000008d50828e0cf5e00030e80000006274c02e0c00049a4934000d18a1e253aad800000000002b60007918001dbc0004800fe9d724646f6330965cabe8c90000c24bed4d44cec0000000001b000000005f
  | 24 => 0x1c3e480000006414888a9400045c07c2c8c000a8200000000001fc0002df800000000028bc000000339a97ca041420000f30000ae200000000000000001d8c0000000aaa130cb84935828168ee99a1a79800010a0cb4e187b4ea20000000510fb60004bc8000000000000219c0006759fd8e6c00036f0260000b709d217e1b200009b2000174089200000015220000004b5c000000000000000131e000018285eab04da00012ecb19bad4688c54ae822603b2adc00000000028e69486b314dc7d8000000000000125e3863a691880000000528d1c0009d71908418000a3580012d00008382aa68e4c5c4150000000f160005f4a0cc50c00029f1364000996023d10d30e597b2b17b540c7da54014e8c729e800001980009812c84000000000000178400098c000000000000036d80011376804912b8cae7886aa01c90e002345f883ed3240282e1114d22e3c50e30b892563714c82f3308ebf703e000097e0001d22e70000b0d4ab8000000219000000134031300000011160002b600000005c333a4e092e09fb2f780b23696c70cba62c00000000000000007c700023cd4468782c118a965e0002f38e7886038c57510100e25060b094e400012503c080200070a26714d869f7f80000000724000000218ccc90002fe9b371f98e14258000000a00090a9e08d291b3578b60734310cb4c3f85bc987df900012d800000000012588942fb173cdd051e156ab4d3399b04279f444be14908d92d8148a2814a02180000000510c3ecb900000019f40009663dc80001f875c11d1c515ca9c9987915c6bc9a61439b78a244e155326d0c780a611400000000005ed0ff40000000000144ad10000000000000000503cacc2fc0fa5b790f84e2847db5226b07230b4768d310325d12c72b84b005a0045b02d4c4a19471aa8cde498ac4e02584b43930002ae0348af23c86408ba660f58606a115b84144e570400006f1692c28260a6da22247a5129733550de0000016d80a69306aaed2982980e6c583266066161c81b1eea5a210481700015da00091200000000009b90000000d127490000000b36000514870400000000029ecb1200000011b456374f1da885340e5630282248000000000185918218500028804426bd31a059096056298a000039a67c1b3a0dc6730004c19578000a5b40480f0000b8026a800074e7bb00ec0013b543f07500f36d288504854a92a91b54aa0460a962950000c48000a025fa16940007ab387021b7a39e4127a4832c627a00000000008da00019f800031a000006c0003950e82a583ea3390001ec03ab00046e12b571a5f71152e8429c93f1a6add400028226d91c0386217000000000000017c2dd225c0f6000000133f000000000000000000000000000000002af000000000000007dc0001ff24d01ccadd17611b87f20003611d
  | 25 => 0x5f353f2d8000000000025f400091a00026ae0008ae2161dd56b64475af00000000000c38eb827600009d00000000004090c7c7a49135b123d552e00000023a0a6e0004e5c73c00091f0760be800055f9e10d6c000202000063a00000000005fe00000000013c92766c14ccd3dc13117500000000009ac0000001103ad6000153a0007d83c2863800000000000013702a127e00000ea57800000000004a92e405800c29990191f7c5e613f0000814e8041329a0000da6957800230042c7202b910f40009d8000000031e8fb8e6621848647f1dc95c603e2be582e7963646d601c400116532452f22ae4380490fc024b08698e9c8000039398e47c800110993c17302031ecba642d84d51f80000738000226a714e6524033447b01285443636f0000097809c50e42acf5d7ae0e9572014315abf800000d55a010c1f420b02b8917d6d224d1170006090000e5a000000000157c3d53aedce4eac000016000123a5d752111f44160001000000b8a1eb33ca330972aa1b469fb17203550f8a1242d40000000854fcaad506d8000000b5100024435188294fb922c1e2a8a0000f1cc7a6683f40000000333800000148a0000001f380007a50002b243320000001c30b584ac084a8e085400031b0000a9e1d722d800000083d0000000000696291800167a09d0002e7824600000518040000000002eed1c43330000000dcc00000007280008f2afd68240000004eb4e4534f09a034273a0002bd3f518a475a4c04e713e14d254346eb08c77abcf2c58ca0000000145835c06b81f0001a6c95e9f10000aec2fd00000000000000002ae80000003c024ca14045e9ed15fa70779887339ba95cf3c50a27a08e12d672e60e9668880b03537951519d0003fa800006257b02349f0000384305a46a4e63e74bec0c60001225902e304fc8b3800224412631e4bc2724dc60001f6af7c02000003525950e46602d200000006d40000fa4f20026000000058600004140012f49e10cea8900004f600025649100005db8000000000487e4140000003bca49655200000000001de4c91b7293adbeab40001498c4812c0001e600007624ab0ac0a5847a38d915440cbd4bf08ec97fe25303d80100003a54ee167170a5db50d98e97700973bf9e35313a3d9a70000bd40001ad000000021f5f4062c00039c0000000000454435831110f0001988000a8e00000000000003cb00016300969d94dac0001300a81719174f880230ea9d9545c9d038bd8c80003360000058000bb04352e9c00060953c800074c0004d04000ea60000000944000000000000038a7e701cc410b6e00011c8000232081364a56c00000006a0000c34000022637912c0000001844000b7b00000005e276d56380000006c54082af5624b102588000d6a5bd30a08ac0000000002bf57ba44d0002fc036e3
  | 26 => 0xb81acbf4a4b6098000aa70001bd94a000090d4d4c0004360002e20000000083cdb252c00066c4e6c0000000003458000eaa5510631cec000932153c00000086210692f8000000000231cde2000412000026893943b9490ebe00034328eae6a64051907701207dc5588000e4379413e901c00000000000000009bb5a60000000c042b24000000b44000000009524a34280010c000013a824e00076fde887311840004b8837e00077619e2a8568c26f19aa2dd33aa6a4b780b7330ac51bf0f0473e000095000145a1b95d580000000000001cf8bb369f0000b740000002d58000000b390001ac800000043211646d20005070e640003e00000cb000037c00028ac0005feb542810000c150000000dba889800200809a2644849f4863a0000d58110a761e9061956800046114280001720000000000000000000000014e90f000000049001400000002e20005218440b3215e00002e0000182000000053a4ae5f98000216783607800146ab64000000098a0b30000000c10b7f1fe1420082a0b49b82b8ae200004900856840000678000bf20000001b640ce3ca0ffa5f11ae61706116a913bad747d86f8ecb0000000000a2866f8cb19e107c445301874c0008b453a8a2e4149cd298a85c3e6000000195000033f58780015380000002284000bc70001898000138181b08000000015c17480002f7000000000000000027c00006195f62c653628a90001158000bb23be9260b0e885d0a109c47a0bb3410adc90e289cec49991cc2b500028da75e7972f416880006d2595984c83877b52aaa2005d396000230c7c21661498cecbf88750390ad10a25294b09a94ec83e44cf253c00000038400000008ef00000010020004a9a1b800049c00026252c0b6832a8f8836800033b4908b5c7ff36200013d29502e5abb10067c30002ee47ca0001db18705878b10a54e152b099a4d1800114649b0f12e916c2000000293e000000000181170e00000000000000001aa16f800000000000008465b5000068c7b00000669ae800026e59200000007a700000018440000000000a5e3d3567a6715ea0000afaf940001d408880000007130000000d4c47e0f4125407e17a9c415317a4a3bdf380000000000000000000000000000110700000311e461000000000000003d9215805e2ba0001e682f421a1160002d0c038000000191c000000000000000000043300000000000000000a22000280800000000000006b00000003b3983466b0000000000000bac51b0b052c4000000000114a000000017c0006fa004908400056080015a18300000000000e2010f44049394c800000000015967ee3f59c8d1fa27910f0f700000024190000a2c98dd9f800000048159300014781b8bf3130d50a622878000147f0001d800007d61c01b426de85c000000000000000028a8
  | 27 => 0x260f4242235369ed46e600000000000000004ae000071474a0000824000b7600014889b899a9a31ab064e58a33f96e4b8c89380008300000000002be8bcd2db0001d8526c00000014ac000000000052800000049c2b0427a0000002fe80009cf8000000000aa3b848000cbd00033d8000000000000147544400000000003cc8b600400000004d7000205877e0000001ddc00002d0ed2bb804b6b82c8213572a000206010816e8aa33911c53085eea3780aa0004eb00000012ea348608284000007409b0001118a271d09308f420000000000e2e00000000015debea2f60001254473219154cce00004ff0b90ace9470d3000000000042b80016a81e480026f800075e54f03731a333858340008720000000dd400056d000293c54894c0000c15229225295c1280006315a00000000565800000142ab9100010dd6f0b134c2ac754e80620001ec981a2c04a4804aedc7b438381511be00022f80000008b0c1d800000000040984980002ac1d00001310b8900880005960000102634f6cc1400010780006a10e3800000028d0002f840000000000000000000348277b84c2041f52e8d8425e00e4a6953b60004e08d585b4b04396000000000021d9e015943b44500000cbc6a200000000004004f0102125a22d06ede298100000d89da580e7464788d7134b2810f2156480a1244df9c0c171a8e50658489d44e81e30da80001b02de2b1089e02e3ab80001ba0005f30a28002aaa43e9ab546940b000000000000039980012840000000000bfc00000000009d872826880000002e941880001e40003110000000a9fcc45621115000055000115e7d600000000002572090b4d5f29bc1880000f1e0000002795060000153272a00085f0000dd955661b09400000000003fc9c340009e49f80e5c0f248936d12dc324094490add005e0003ad8d5cfae000195919046ec0908d000144a000000290405fadb00000000000000000000000260475d6c80005860000000000000337aea861c2f506d023526a79202280e00000003f89cc400000054584e4c0430c2a3c00173e5b02e72f90e96bae412800061aa5c46820fd0de4aa5b30000000000250af1454e00053600001c20000f00a3c000000000274a00000000000000007c500000002a6b380001b4000017a0e41d8086c0000001fc00007262bca65c0002d50001360000000000000171e56380024f80000000001550000000000041ca9b0000000dd1248000390a31800088880000013aca890002ac80006b410c2e5984e3320000000b2a0005a080003b600001200015ee00011e0a97696c06000000133159e0cf80013ab0000000000000000000000000000000000011fb3548c260146da57c0002f6cb420ce26b0370bf05030001c601c465f0ad244116067781d16597ac0005f78000b4e1d6800000168a
  | 28 => 0x1791b9c8a20ff00000002936945c4163b728671000036400000000003f55b08d4071800000033a80000000000004b540345561200808000bd200034e21b0000bd500000016c6000000000062eaf047a128d7a1000000000034fa3f00024e80006e0000195edde6645d8a4a521847200022ad59819c1462778f3fb6d000015851900027828f51909fc4999c702b026507989040001fb21a81f4b0214819d0f24edd859119a4816fa0000001794640000559abd8000b4d13900000000003cec7c97b8aa93ef1b88000afc40e23ac000000000250cee0000457c000000358383000000000000000000000002b340000000002ff80003010000eb000000084a05780012006eb0000000dca7121e7800109c0000000c600007045e762883ceb565281974396000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ec8754d62040015cf02a9ac408002b9205535881000557420a6b102000aad8414d62040015cf02a1ac408002b920543588100053742886b102000a6d8510d6204001d1a8621ac4080029ba16715881000536c2ce2b102000c6c759c5620400155d0938ac408002ab61271588100056741ce2b102000acd839c562040018d8ea38ac40800399dd47158810006733a8e2b102000ce4751c56204001cc8ea38ac408003191d4715881000673ba0e2b102000ce5741c562040019cee638ac408003395cc715881013673380e2b102026ce4701c562040011dd0fa0ac4080023b61f41588100053742e82b102000a6d85d05620400159d07a0ac408002b360f41588100047743e62b1020008ed87cc562040014dd0b98ac4080029b61731588100055742662b102000aad84cc562040071df0eb16a40801e3d61a71d481000672b14e3a9020308f7865c752040019cac4b8ea40800e3b61e629481003d3642ac5290203287f855d9520405f1ef02bb2a40800e3b21d625481000673316e2a902000ce562dc552040011eb0c38aa40800339988715481000672b10e2a90200787c855d852040071db0f310a4080029be1562148100047743cc4a8820008ec8798951040011dd0eb12a2080023b21d625441000673412ed9082029ce5825db21040539ce40bb642080a73948176c841017d3a42ac59082000e678558b2104001cc90ab1642080a739dc162c841014e72b82c5908200787e85dda21040010fb0bbb4420800a2fa1376884100045ec26ed10820018de83dda21040011bb07bb4420809a3da07768841033d3642ac51082000ce9625c221040071d905bb242080c31d984754841000637bacc49082000c6c7598921040018deeab1242080031b1d5624841001c76c12ec10820038ed8798821040554d90ab1042081beb9605620841000673bb2421082000ce57648421040016c90a90842080033a989700841013572c12ec1082026ce5825d821040019cc84bb0420800339509760841000673192ec1082000ce5325d8210404d9cc40bb0420809b39081760841000572c34e41082000ce5769c821040531ef0eb1042080aa9d215620841014e73392c41082000ae78758821040539cf0eb10420800399e1562084101557242ac41082000e648558821040554c90ab104208002b9e11620841000572c22c41082000ae78358821040015cb06b10420809ab9a01620841013572402c41082026ce770588210404d9cae0b1042080aab9e1b520841000672bb6a41082000ae58614821040019caec29042080ab991945208410006f1392e01082000cb874dd910040019b0e7bb220080033ae0b764401000674416ec8802000c7b76dd510040018f6ec3aa20080032eddb74440100066dbb6e68802000ceb76dc910040019d6ec392200809b78dc47244010
  | 1 => 0x904ba2ca0808a3de0574594100047a40ae8b28200387c8755165040011df04b9aca080023b209735941010c7bc0ae6b2820008f4815cd65040070f90ea9aca080023d20575988100053742e853102000a6d85d0a620400159d07a14c408002b360f42988100057340e8531020038ed8790a62040071db0e214c4080029ba17329881000536c2e653102000aae84cca620400155b09994c408002b9a07329881001c76c3c6531020038ed870ca62040015c902bacc4080029ba16749881000536c2ce93102000ace839d2620400159b073a4c408002b9a06749881000572c0ce93102000e2f5495262040011df0eaa4c4080023b21d549881000573c0aa93102000ae481552620400159d062a4c408002b360c54988100053742ce73102000a6d859ce620400155d0939cc408002ab61273988100057340ce73102000ae5819ce6204001c9ea729cc4080023be1d53988100047643aa73102000ae78154e62040015c902a9cc408002aba10539881000556c20a73102000a6e8510e62040014db0a21cc408003a350c43988100047743e8331020008ed87d0662040014dd0ba0cc4080029b61741988100056741e833102000acd83d0662040011dd0f98cc4080023b61f31988100053742e633102000a6d85cc6620400155d0998cc408002ab613319881019636c16eab10200087f855d1620400f0f90aba2c4080023d20574588100043fc2ae6b10200787c855cd62040011e902b9ac40800e3ba1f42588100053742e84b102000a6d85d0962041398d8eba12c408002b3a0f425881000566c1e84b102000ae681d0962040071d90ea12c408002b920542588104de363a884b1020038ee87cc962040014dd0b992c4080029b61732588104d6363ae64b102000aae84cc9620400155b09992c408002b9a07325881001c7643a64b102000ae4814c962041338d8ea192c4080031ddd471588100063a3a8e2b102032e6710dd56204065cca21baac4080c69ba1675588100057340ceab102000ae4815d562040654dd0e3aac4080031ba1c755881018e37b80eab102031c6d701d56204063cce203aac4080c79944075588100053742ce8b102000a6d859d162040018d8eb3a2c408002b3a0e745881000566c1ce8b102000ae6819d162040015cb033a2c4080029be1574588100053642ae8b102000ae7815d162040015c902ba2c4080031b1d4745881000717aa4a8b1020008ef8755162040011d90eaa2c408002b9e0554588100057240aa8b102000ace83151620400159b062a2c4080029ba16735881000536c2ce6b102000c6c759cd620400155d0939ac408002ab61273588100057340ce6b102000ae5819cd62040014df0ab9ac4080029b215735881000573c0ae6b102000ae4815cd62040018d8ea39ac40800393d4e535881000477c3aa6b102000
  | 2 => 0xb5288510006733b6a510a2000ce67614a21440890fd0dbaa42880030f19375485100062e31eea90a205787e861d52144001878c83aa42880031718c75485100043f43eca90a200087e87195214400187eebb2242880030f1d764485100062fbaec690a2000c5c75d8d21440018deebb1242880031b1d762485101fe74386c490a2000c6f7518921440018d8ea31242880fa5da1f75485102bcbb430ea90a2000d34641d52144001aa8c63aa42880025da1f65485102be3a3b6ca90a2044c74761952144001c68c832a42880039518c65485102b65a3b6c890a2000d3475d9121440ab9a8edb1a4288003551d7634851000573436e490a2000d6475dc9214407f9c8edb124288003591d762485100063a3acc490a20008f68718921440018e8ea3124288003591d4624851000733b28c490a2000e64651892144001d4ec83124288003a9190624851000763b18c490a2000ec46318921440015cd0e312428800339a1c624851000733ba8c490a2000ce67518921440019c8ea3124288003991d46248510006323a8c490a2000ce77418921440019cae8312428800339dcc624851000672b98c490a2000d7075dc12144001ae6ea38242880ff78dc87048510004f3c3a4210a2000b64854842144001cceca908428800399195210851000753b224210a2070ea4644842144001d8ec690842881bbb118d210851003e3a32ce3a822000ce4629c750440019c8c4b8ea0880022fe1176541100145e422eca8220008df835d950440031b906bb2a0880023be0976541100063bb2ee2a822000cb464dc550440019a8c7b8aa0880033918b71541100063bb28e2a822000cb4641c550440019a8c638aa0880033918871541101347b434e39022000ce4629c720440019c8c4b8e408800eb921921c8110005b242a43902200087f855d9204400f0f90abb2408800237e0d764811000c6e41aec90220018dc831d920440010fd0fb2a40880021f21f65481100061e3a6ca9022000c5c73d9520440010fd0e32a408801e1f21c65481100061e3a0ca9022000c5c7319520440011bd0db9a408800317d9773481100062e32ee69022000c9f64dcd2044001938c9b9a408800237a1f63481100046e43ec69022000c5f75d8d20440018b8ebb1a408800327dd363481100064e3a6c69022000c7765dc520440018e8cbb8a40880032dd9371481100065a326e29022000cd763dc520440019a8c7b8a40880031dd9471481100063a328e29022000cb7641c52044001968c838a408800335d8c71481100066a318e29022000ce7621c5204404d9c8c438a408800eb92192148110006723b2429022000b648548520440077c10090a408815f1e9db65c411003e3d3b0cb8822056cba76d9310440ab9b4edb1e20880ff3a9db62c4110005b842a4388220008ef825d165040011d
  | 3 => 0xba8a2022ab686d9351440ad96cedb26a2880038dd9764d45100074a31ec9a8a2021ad686d8f51440ab9acedb1ea28800395d9763d45100074a326c7a8a20268f4865cb514407f9ccedb16a28800399d9762d451000752326c5a8a2000ec463d8b51440011eb0f316a2880029d61662d45101155b424c5a8a2021ad68398b51440019cae4316a28809b399d862d451000733b28c5a8a2000e646518b5144001d4ec8316a288003a919062d451000763b18c5a8a2000ec46318b51440019cb0e316a28800339dd062d451000672ba0c5a8a2000ce77318b51440019cae6316a28809b399c062d451013672380c5a8a203ec7671d96514407d8eee3b2aa28815f1e1c3655451013477436e4a8a2000c6f65dc951440cf8d8cbb92a2880032bd93725451000656326e4a8a2000ccf63dc95144001998c7b92a2880fe3ba18725451000637b28e4a8a202ac6c651c9514400195ec8392a2880032b190725451000667b18e4a8a2000ccc631c951440551dd0fb12a2880fe3b21f625451033c77438c4a8a20268ec87189514407d8eea33b0a2880fb1d19676145100071a326ca28a2000e5463d9451440894eb0fb28a28815f1d61f65145100053b416ca28a201cab686d905144001c6ecbb20a288003a518f64145100dd6b436c628a2000e5765d8c5144001d28c9b18a28800399d97621451000752326c428a2000ec463d8851440014eb0b310a288072ada1262145100dd6b41cc428a2000ce5721885144001cc8a4310a288003399d8621451000733b28c428a2000e64651885144001d4ec8310a288003a9190621451000763b18c428a2000ec46318851440019cb0e310a28800399e14621451000732428c428a2000e667518851440019cee8310a288003395d0621451000733aa0c428a2000e655418851440019cee6310a288003395cc621451000733a98c428a2000e6553188514404d9cce0310a28809b391c062145104ef33280c428a209de645018851440014e90d290a28823b8d192521451046f2a31ca428a2000e6462948514404d9d4e031642880feb9a1b2188510006733b64310a2000e6765c862144107d48c990c428820bb118f21885100065a324ed10a2000cd4639da214404d9cf053b442880033990a768851000672a14ed10a2000ce6329da21440019ca653b4428809b39882768851013672104ed10a2000c7676d9621440018ecec32c42880038d19065885100072a318cb10a2000cb676d9221440019acedb1c4288003399db6288510136733b0c510a2000e676518a2144001cc8ca3144288003a9d90628851000752320c510a2000ec76318a2144001d88c63144288003399d46288510006723a8c510a2000ce77418a21440019cae8314428800339dcc628851000672b98c510a2026ce67018a214404d9c8e03144288002b9a1
  | 4 => 0x2440015cb03298c4880023be1d53189100047643aa63122000ae78154c62440015c902a98c488002aba10531891000556c20a63122000ae68114c62440015cb02298c488002b9a07431891000572c0e863122000ae68190c62440015cb03218c4880029ba14431891000536c28863122000e8d4310c62440015cd02218c488002b960443189101347743e8231220008ed87d0462440014dd0ba08c4880029b61741189100056741e823122000acd83d0462440015cb0f208c488002b9a16411891000572c1c823122000ea7439046244001d4a87208c48809ab9a0241189101357240482312209fea640904624413fd4881208c488002b9e1d41189100057242a823122000ea78450462440015cf06a08c48809ab9a014118910135724028231220268ee87cc462440011db0f988c4880029ba17311891000536c2e623122000aae84cc4624400155b09988c488002b961e31189100057342c623122000ae7848c462440015cb09188c488003b190e311891000762a1c623122026ae6808c4624404d5c901188c48827bb18c231189104f762184623122000ae7874c462440015c90a988c488002b9e11311891000572c22623122000ec7834c4624404d5cd00988c48809ab9201311891000537c2ae03122000a6c855c0624400155f08b80c488002ab211701891000567c1ae03122000acc835c062440015cd03a00c488002b9607401891000573c0a803122000ae48150062440015cd03980c488002b9607301891000573c0a603122000ae4814c062440014df0a880c4880029b215101891000557c22203122000aac84440624400159f06880c488002b320d101891001c7ac0ceda9220008bf845db524400517908bb6a48800237e0d76d491000c6e41aeda9220028be84dda524400117b09bb4a48800637a0f76949100046ec1eed29220008bf845da524400517908bb4a48800237e0d769491000c6e41aed2922000c77659c65244001968c938ca4880033518e719491000672314e32922000c77655c65244001968c8b8ca4880033518d719491000672312e329220028be84dd9524400117b09bb2a48800637a0f76549100046ec1eeca9220008df835d952440031b906bb2a4880aa3d204765491003c7743ec4a9220038f686dc552440018eecbb8aa4880bf1d19771549100065bb26e2a922000cb464dc552440019aec7b8aa4880033518f715491000672316e2a922000c77651c552440558e8ca38aa4880032dd9071549100065a320e2a922000cd7631c552440019a8c638aa48800339d88715491000672310e2a92203ec74519d8524400117f08bb0a48800a2f21176149100046fc1aec29220018dc835d8524400f8e8cb388a4880033918a711491000672312e22922000e3464d975144001ca8c7b2ea2880fa9d61f65d45100063ac3ec
  | 5 => 0x8002b960a311891000573c12623122000c6e76d946244001ccb03b28c48828f99843651891051f32086ca31220008ed87994624400155d09328c488002ab61265189100056741cca3122000acd8399462440011df0eb28c488002abe11651891000556422ca3122000acf83594624400159906b28c4880031b9d8651891051733c08ca31220a2e66101946244145cc820328c4880032b9db641891000717b2ec83122000e2c65d90624413fd4f03b20c48827fa984364189104ff52086c831220008ed8799062440014dd0b320c4880029b61664189100056741cc83122000acd8399062440011df0eb20c4880029be1564189100053642ac83122000acf83590624400159906b20c4880032b9d8641891000717b28c83122000e2c651906244001d4b02320c488287a9840641891050f52080c83122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e8c64d8c624413dd8f03b18c48827bb184363189104f762086c631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891000762c08c631220a0ec61018c6244141d8820318c488002d9215711891000733b2ae23122000e64655c46244001d4ec8b88c488003a9191711891000763b1ae23122000ec4635c462440015cd0d208c48800399d9641189100073232c823122000ea7649046244001d48c9208c488003b1d8e41189100076231c823122026ae4865046244001ccecaa08c48800399195411891000753b22823122000ea4645046244001d8ec6a08c488003b118d411891000573434623122000e67658c46244001cc8cb188c488003a9d92311891000752324623122000ec7638c46244001d88c7188c48809ab9219311891000733b2a623122000e64654c46244001d4ec8988c488003a9191311891000763b1a623122000ec4634c4624404d5cb03ba8c488002b9e05751891013572c08ea3122000ae681dd0624404d5cb03ba0c4880029ba16741891000536c2ce83122000ace839d0624400159b073a0c488002b9a06741891000572c0ce83122000ae6811d0624404d5cb023a0c4880038bd5254189100057340ca83122000ae58195062440011df0eaa0c4880023b21d541891000573c0aa83122000ae481550624400159d062a0c488002b360c541891000573408a83122000ae58115062440015cd03b98c48809ab960773189100053742ce63122000a6d859cc624400155d09398c488002ab61273189100057340ce63122000ae5819cc62440015cd02398c48809ab9604731891000727a9ca63122000ae68194c6
  | 6 => 0x61f3a0cb3122000c5e73196624400187ecaba4c4880030f19574989100061f3aec93122000c3d75d92624400193ce7b24c4880030f9d464989100061eba8c93122000c9e7319262440018becab9cc4880031719573989100064fb22e73122000c9c645ce62440018bcebb1cc488003175d763989100064f3a6c73122000c9d74d8e62440018bcea31cc488003175d463989100064f3a0c73122000c9d7418e62440018dcebb14c4880031b5d76298910006573a6c53122000cad74d8a624400199ce7b14c488003335cf62989100063bc0aeb312200787e85dd262440010fb0bba4c48800637a0f74989100046ec1ee93122000c3e759d2624400187aeb3a4c4880030f9d574989100061ebaae9312200787e85dce62440010fb0bb9cc48800a2fa1373989100045ec26e73122000c5e759ce62440018baeb39cc488003279d273989100064eba4e73122000c5e755ce62440018baeab9cc488003279d173989100064eba2e73122002cb67490662440051ef0ea0cc48800b2d9d1419891000e6b39c6331220018f7874c662440039ace698cc4880021fa1f65589100061e3a6cab122000c5c73d9562440010fd0e32ac4880030f1d065589100062e398cab1220028be86dd1624400187ecbba2c4880030f19774589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc645891000c6f436e6b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b1220008de87d8d62440018beebb1ac488003171d763589100064fba6c6b122000c9c74d8d62440011bd0e31ac48800317dd463589100062e3a8c6b122000c9f7418d6244001938e831ac48800317dd773589100062e3aee6b122000c9f74dcd62440010ff0ab9ac48801e1f21573589100045fc22e6b1220028bc845cd62440011df04b9ac4880023de0573589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100063bbaee2b122000c7475dc5624400196ee9b8ac4880032d1d371589100066bb9ee2b122000cd473dc5624414b96ae2320c488293355c4631891000477c3ac43122000a6f8558862440014d90ab10c488002abe11621891000556422c43122000acf83588624400159906b10c4880029ba16721891000536c2ce43122000aae849c8624400155b09390c488002b3a0e721891000566c1ce43122000a6e85d0862440014db0ba10c488002b3a0f421891000566c1e843122000ae581d0862440051db0f210c488002b9606421891000572c08843122000a6e85cc862440014db0b990c488002aba13321891000556c26643122000ae581cc862440031db0f190c488002b9606321891000572c08643122000ae58290462440015cf04a08c48
  | 7 => 0x5d751d763440014bd0b3a6c6880029761674d8d100064fba4e9b1a20a6ad6811d363440ab5ab023a6c68800387d5254d8d1000567c12a9b1a2000acc8255363440015af02aa6c688002b520554d8d100046f438a9b1a20008dd8715363440014bf0ab96c6880029721572d8d100054fc22e5b1a2000a9c845cb63440015af02b96c688022b520572d8d101cd6b408e5b1a2055ad5811cb63440011bd0fa16c6880023761f42d8d100052f42e85b1a2000a5d85d0b63440015ad03a16c688002b560742d8d102ac6f43e83b1a20008dd87d0763440014bd0ba0ec6880029761741d8d100056741683b1a2000acd82d0763440495ad03b86c6880029ba1742d891000536c2e85b122000ace83d0b624400159b07a16c48800a3be1d42d89100053742e65b122000a6d85ccb624400155d09996c488002ab61332d891000c77c3a65b122000e6581d97624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc835976244001c5ecbb26c4880038b19764d89100053742cc9b122000a6d85993624400159d07326c488002b360e64d891000537c2ac9b122000a6c85593624400159f06b26c488002b320d64d891000717b28c9b122000e2c651936244001d4b02326c48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec48800393d9463d891000726328c7b122000e8f6418f6244001d18c831ec488003b160463d89100075232483b12203fae4865076244001d48c8a0ec488003b118e31d89101fd7243263b122000ec4634c7624407f5cb03baec4880029ba1474d891000536c28e9b122000ace831d3624400159b063a6c488002b9a0474d89101fd72c08e9b122000e2f5495362440011df0eaa6c4880023b21d54d891000573c0aa9b122000ae481553624400159d062a6c488002b360c54d891000537428e7b122000a6d851cf624400155d0839ec488002ab61073d891000573408e7b12203fae5811cf6244001c9ea729ec4880023be1d53d89100047643aa7b122000ae78154f62440015c902a9ec488002aba1053d891000556c20a7b122000a6e8510f62440014db0a21ec488003a350c43d89101fc7743e83b1220008ed87d0762440014dd0ba0ec4880029b61741d89100056741e83b122000acd83d07624407f1dd0f98ec4880023b61f31d89100053742e63b122000a6d85cc7624400155d0998ec488002ab61331d89100053742ee1b122000a6d85dc3624400155d09b86c488002ab61370d89100056741ee1b122000acd83dc3624400187ce9b2cc488003179cf65989100
  | 8 => 0x3210ca8801e1fa1f32195100043ec3e6432a2000a3e84cc8654400147b09990ca880029da0732195100053ac0e6432a2000a76818c865440014eb03190ca8801e1fa1f41195100043ec3e8232a2000a5e83d0465440014bb07a08ca880029ba0b411951000536c168232a200787e87cc465440010fb0f988ca880028fa1331195100051ec266232a2000a6e82cc465440014db05988ca880029de0540195100053a40a8032a2000a77814c065440014e902980ca880030f9db65d91100071ac0ecbb2220008bd87997644400147d0b32ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec8880022fe1d65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91100051f430cbb222000c3e76197644400117b0f31ec8880028fa1663d91100051ec2cc7b222000aae8298f644400155b0531ec8880022fe1d63d91100051fc2ac7b222000a3c8558f644400155f04b1ec888002ab20963d91100070fb28c7b222000e1c6518f6444001d2b0231ec888003a518e31d91102b55a43263b222000e94634c7644400155d05baec888002ab60b75d91102455b40eebb222056ab581dd7644400153d073aec888002a760e75d91100061eba8ebb222000a3e859cf644400147b0b39ec88800327dce73d911053d5b408e7b222056ab5811cf6444001c3ea729ec888002abe0953d911000556412a7b222000ab78154f644400156902a9ec8880022fa1c53d91100045ec38a7b222000a3f855cb64440014790ab96c888002a7e0d72d91100054e41ae5b222000ab7815cb644401356902b96c88810aada0472d91102b55ac08e5b2220008be87ccb644400117b0f996c8880028fa1732d91100051ec2e65b222000ab681ccb644400156b03996c88815a2fa1f31d91100045ec3e63b222000a3e85cc7644400147b0b98ec888002aba0b31d911000556c1663b222025ab681dc364440018bcedb2ec6880039560765d8d100046ec3ccbb1a2000a5e85997634400153d0932ec688002a761265d8d1000567414cbb1a2000acd8299763440011bf0eb2ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec68800297a1865d8d100062f3b0cbb1a2000c9e76d936344001c3ecbb26c6880038719764d8d100046ec3cc9b1a2000a5e8599363440014bb0b326c688002a7a1264d8d1000567414c9b1a2000acd8299363440011bf0eb26c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c688002a7a1864d8d100064f3b0c9b1a2000e1f651936344001c38ca326c688003a560464d8d100074a32483b1a2055ad4865076344001d28c8a0ec688002b3a0b75d8d1000566c16ebb1a2046ad681dd763440ab5ab03baec688002a7a1275d8d100054ec24ebb1a2000c
  | 9 => 0x41d95100052ec1e83b2a2000a6e82d0765440014db05a0eca8815e1fa1f31d95100043ec3e63b2a2000a3e84cc7654400147b0998eca880029ba0b31d951000536c1663b2a2000c3e74d9665440018bce7b2cca880030fd95749951003e1e32ae932a2000c9e7319265440018becab9cca8801f1719573995100064e322e732a2000c9e7418e654400193ae831cca880031bd96729951003e3632ce532a2000cac649ca6544001998c7394ca880031bd95729951003e3632ae532a2000cac645ca6544001998c6b94ca88003271cc64595100064e326e6b2a2000c9f7418d6544001938e831aca880032b19372595100066631ee4b2a2000cac641c96544001998c6392ca880030fdd774595100043fc2ae8b2a20008df835d165440031b906ba2ca880023be09745951000476412e8b2a20008f7815d1654400187eea3a2ca8800317dd773595100064fba6e6b2a2000c9c74dcd65440010ff0ab9aca880022fe1173595100145e422e6b2a20008ef825cd65440011d904b9aca880023de0573595100062fba8e6b2a2000c9f741cd6544001938e839aca880031bdd7725951000657ba6e4b2a2000cac74dc9654400199ee7b92ca88003331cf725951000637ba8e4b2a2000caf741c96544001958e8392ca8800333dcc725951000666398e4b2a2000ce7511c965440019c8a2392ca880032d1d371595100066a39ee2b2a2000ce472dc565440071eb033b0ca880021fe1d65195100051fc22ca32a2000a3c8459465440014bf06b28ca880029720d651951000537c12ca32a2000a6c825946544001c6ea2320ca8800395d4463195102253ac0cec32a200087d8799065440014bd07320ca880029760e641951000537414c832a2000a6d8299065440010ff0eb20ca8800297e0d64195100052e41ac832a2000a6f8259065440014d904b20ca880038d604641951054f1bb88c832a2000e34711906544153c6c20320ca882a78d04064195100043ec3cc632a2000a3e8498c654400147b09318ca880029ba0a631951000536c14c632a200087f8758c654400147f08b18ca880028f211631951000537c12c632a2000a6c8258c6544001c38c8318ca880039560463195105472bb88c632a2000e547118c6544151cac20318ca882a39504063195100053b4348232a2000e34649046544001ca8c7208ca881129d21941195100071a3228232a2000e546350465440014ed0d188ca880038d19231195100072a31c6232a2044a74864c46544001c68c8988ca880039518d31195100053b40e8632a2000a7581d0c65440014ed03218ca880029d606431951003c3f4388632a200087d8710c6544001c3a86218ca8801e1fa1f42195100043ec3e8432a2000a5e83d0865440014bb07a10ca880029da0742195100053ac0e8432a2000a768190865440014eb
  | 10 => 0x90e2000ce57318921c4001dc300312438809b399c0624871013672380c490e20009e78748421c40016c90a90843880037848570087102bc3fc3acba862007c76659c750c40531ef0cb8e4188002d921521c831000477c12e8b2c20008ec825d165840070f90eaa2cb0800b0f1d1545961000536412a8b2c20008ef825cd65840011d904b9acb0800e1f21d535961000e2e39aa6b2c2000a6c8254d65840071db0f214c50800e3b61e3298a1001c7643a84b142000ae78150962840071d90e992c508002b9e053258a101f47ac34e3a942000ce5625c752840070ff0eb2ca50800e3b61e6214a102243fc3acba8c202ac6e651c951840018daca392a30809a3de1d62c861000573c3ac590c2026ce78758b218404d1cf0eb1643080031b1d66248610006363aac490c2000b6485484218404d7c100908430809af8a02720861013572436a410c2026ae6861482184055cccca29043082972d5c464d95105266ab88c7b2a20008ee82dd365440011db05ba6ca880723da0774d951001c7ac0ee9b2a2002c3c74d53654400187ae92a6ca880029d60654d95100143fc3aa9b2a2000a6f8255365440014d904aa6ca880029de0554d95100052f418a9b2a2000a5d8315365440011dd05b9eca880023b60b73d95100dc7b40ee7b2a20038f581dcf65440038b8e7a9eca88003175ce53d95100053ac0ca7b2a200187f8754f65440014df04a9eca880029b20953d95100053bc0aa7b2a2000a3e8414f654400147b0829eca8800297a0e64d95100052ec1cc9b2a2000a6e8299365440014db05326ca8800297e0d64d95100052e41ac9b2a2000a6f8259365440014d904b26ca880038d60464d95100051f424c7b2a2000a3d8498f65440014dd0531eca880029b60a63d95100051fc22c7b2a2000a3c8458f65440014df04b1eca880029b20963d95100070e320c7b2a2000e558118f6544001c68c8b8eca880039518d71d95100071a32483b2a2057a74865076544001c68c8a0eca880039518e31d95102bd3a43263b2a2000e54634c765440014dd05ba6ca880029b60b74d95100053b40ee9b2a2057a7581dd365440014bd073a6ca880029760e74d95100061eba0e9b2a2000a76811d365440af4eb023a6ca880029ba0b73d951000536c16e7b2a2000a7681dcf65440af4eb03b9eca880028fa1273d95100051ec24e7b2a2000c5d731cf65440014ed0239eca8815e9d60473d95100043f43887b2a200087d8710f6544001c3a8621eca8815e9d60772d95102bd3ac08e5b2a200087e87d0b65440010fb0fa16ca8800297a0f42d95100052ec1e85b2a2000a7681d0b65440014eb03a16ca880021fa1f32d95100043ec3e65b2a2000a3e84ccb654400147b09996ca880029da0732d95100053ac0e65b2a205787e87d0765440010fb0fa0eca8800297a0f
  | 11 => 0x940018eeeb30a43280c31d1d661486501f63a3aac290ca000ae48258521940015cb0530843280031d5d8510865000733310a210ca000ae78648421940015cb0c908432800339dd9210865000672bb24210ca02ab648548421940014eb0ba0ec2a8002b5a0f41d85500057341683b0aa000a7585cc7615400156d0998ec2a8002b9a0b31d85500047bc3ac230aa000ab48458461540015a906b08c2a8002b920961185500053ac2e8230aa000ad683d0461540015cd05a08c2a80029d61731185500055b4266230aa000ae682cc4615407d1eb0fb0ca2a8003391cb61545501847b438c2a8aa000ce47218551540015cb03b1442a801e1f21476485500046fc1aec10aa0018dc835d821540015cb0430842a8002b9a192108550005724324210aa02ab648548421540071eb0f20cc22800e3d61e319845003c3e42ae8b08a0008ef825d161140011d904ba2c22801e1f215735845000477c12e6b08a0008ec825cd61140cf8d8ebb92c2280ab1b1d4725845013673b88e4b08a026ce5811c961140559cea2392c2280ab1b144725845015672288e4b08a026ce6101c9611404d9c820392c228003391ca415845001c7a43a82b08a000ce47250561140019c8e518ac22800e3d21d31584500067239262b08a000a6c8258651140cfcc8a530c422809a3de1d618845000572412c3108a00087f855d921140531ed0f30a422801f1d1d6614845003e3a3aac2908a000ae482585211404d5c90c908422800339dd9210845000672bb242108a02ab648548421140031bd07ba6cb880023760f74d971000477416e9b2e20008ed82dd365c40050ff0eaa6cb8800b0f9d154d97100145f426e7b2e20008bd84dcf65c40011dd05b9ecb880023b60b73d971000c3fc3aa7b2e2001c5e7354f65c40071e902bb4cb880023be09745971000476412e8b2e20038f4815d165c40011df04b9acb880023b209735971001c7a40ae6b2e2000ce7511c965c40019c8a2392cb8800339dc8715971000672390e2b2e200087f8759465c40015cf04a0cc588002b9e093198b1000477c3ac431620028f58790462c40015cb05208c5880063d61e3118b1000572c146231620038f4815db52c40014df04b28a5880c69d2056514b1003e3b32ce229620009e7825db51c40019cae5316a3880029b209659471000536412ca28e2000b648259451c40531ef0cb90a388003395c8621471000732290c428e2032c757694851c40015cb0da9443880031dddb75487100063bbb0ea90e2000d6475dc921c4001ac8ebb124388002f860362487100063a3acc490e20008f68718921c40018e8ea312438800279a1c6248710006b23a8c490e2000ae68718921c40019cd0e312438800399dd46248710006733a8c490e2000ce47518921c4001cc8ea3124388003191d4624871000673b98c4
  | 12 => 0x29d61673986500055b424e730ca000ab5849ce61940015cd0539cc328002b960a73986500066ab98e730ca030e575394e61940431ef0ea9cc32806e3d21d539865000573c12a730ca000ae48254e61940614ed0a21cc3280029d61443986500074aa188730ca000a7585dca619400156d09b94c328002ad61372986500056b41ee530ca000ad583dca61940014ef0ab94c328003395c872986500047b43e8530ca0008f587d0a61940614ed0ba14c3280029d61742986500056b41e8530ca000ad583d0a61940014ef0aa14c3280c29d21542986500047b43e6530ca0008f587cca61940614ed0b994c3280029d61732986500055b4266530ca000ab584cca61940014ef0a994c3280c29d21532986500053ac2e82b0ca000ad683d0561940015ab07a0ac328002b9a0b415865000572c1682b0ca0038f4875056194005968e8a0ac3280029d61731586500055b42662b0ca000ab584cc561940015cd0598ac328002b960b315865001c7a43a62b0ca001cd4734c5619400156f08baac328002ad21175586500056bc1aeab0ca000ad4835d561940015cf04baac328002b920975586501f53b42ce8b0ca000a75859d161940015ad073a2c328002b560e745865000573414e8b0ca000ae5829d161940014ef0aba2c3280fa9d21574586500065aba0e8b0ca03ee375495161940451ef0eaa2c3280723d21d54586501f71a2a2a8b0ca000ae78255161940015c904aa2c3280fa9da1673586500053ac2ce6b0ca000ab6849cd619400156b0939ac328002b9a0a735865000572c14e6b0ca000a77855cd619407d4e90ab9ac328003355cc73586501f72ba9ca6b0ca0218f78754d61940371e90ea9ac3280fb9514d535865000573c12a6b0ca000ae48254d619407d4ed0a21ac3280029d61443586500074aa1886b0ca000a75859c9619400156d09392c328002ad61272586500056b41ce4b0ca000ad5839c961940014ef0ab92c328003395c872586500047b43e84b0ca0008f587d09619407d4ed0ba12c3280029d61742586500056b41e84b0ca000ad583d0961940011ed0f992c3280023d61f32586501f53b42e64b0ca000a7585cc9619400156d09992c328002ad61332586500067930ae128ca03ed72715c251940011db0db92a3280023b61872546500047743cc4a8ca0008ec8758951940019cee530aa328003391ca615465000673b92c2a8ca000ce47258551940019e2c3b82a32800399e0662146500073240cc428ca0abe66719885194001cce83310a3280039910662146500073398cc428ca000e64319885194089cce21310a3281139944262146500053a412c228ca0028be84dda219400117b09bb4432800637a0f76886500046ec1eed10ca0aac6e7558a21940018deec29443280c31d9d661886500063abacc310ca000e645298621
  | 13 => 0x6b2180ea90842009e687d9521084019ceedb2a42108ab591d76548421154f243cca908422ad647599521084553cf0eb2a42108aa7921d654842100673bb2ca908422ad647559521084013cd0e32a42108ab591d4654842100673bb6e09084200d6475dc121084015cb0d3824210802d9a167048421005b2c2ce09084200d67759c12108401ac8eb3824210802b9e19704842100673bb2e09084200b67855c121084016c90ab824210803591d57048421005e3c1ae0908426ebc4835c12108401aceea3824210803591d47048421136f1380e090842009e78748760084015cf0c90ec010802d921521d8021134f243a433004200b6485486600844d7c10090cc01089a7921d215802100573c3242b004200b64854856008401aceea90ac010803591d52158021006e3b9a42b00426edc473485600844d7c10090ac0108031da0775580210063ac0eeab004200c5f75dcd60084018b8ebb9ac01080327dd373580210043fc2ae6b00420787c855cd600840117f08b9ac01080a2f21173580210062fba8e6b004200c5c751cd600840193ee839ac010803271d073580211347b43ea2b004200c7775d456008445968e9a8ac010887351cf51580210063bba8a2b00421ccb47414560084379a8e628ac010802b9608515802100732290a2b004202cb47490560084015cb0520ac01089a3d21d41580210165a3a282b004201cd4738c560084015cb0518ac01089a3d21d315802100e6a39a62b0042268f687885600844d5e50110ac01089a3d21d21580210053a42a42b004226af08048560084019cf0e90ac01089ab921d21580210067243a42b0042268e4874856008401ccf0a90ac010802b9a1521580210057242a42b004200e648548560084014c90a90ac01080399dd52158021007323aa42b004200ae78348560084015cb0690ac010803b1dcd21580210076239a42b004200ee380485600844d5cd0090ac01089ab920121580210077040242b004226ae08048560084013cf0e908c010802d921521180210047dc3ac030042008ee82dd261d40011db05ba4c3a800b0f9d1549875000477416e730ea0008ed82dce61d40038bce6a9cc3a800e1f215764875000572c14c210ea000ae78648421d40015cb0c90843a80aad921521087500053ac2e8330ca000ad683d0661940015ab07a0cc328002b9a0b419865000572c168330ca0038f587906619400196ae820cc3280029d61731986500055b4266330ca000ab584cc661940015cd0598cc328002b960b319865001c7ac3c6330ca000cd5730c661940614ed0b3a4c3280029d61674986500056b41ce930ca000ad5839d261940015cd053a4c328002b960a74986500065aba0e930ca030e375495261940451ef0eaa4c3280723d21d549865000573c12a930ca000ae48255261940614ed0b39cc328
  | 14 => 0xf824c465484014d904988ca908029ba0a301952100536c146032a4200a76818c065484014eb03180ca9081e1fa1c30195210043ec386032a4200a3e840c0654840147b08180ca908029ba08301952100536c106032a4200a76810c065484014eb02180ca9081f1b19672d452103e3632ae5a8a4267c6c65dc951484018deca392a2908ab1b194725452100733b2ec310a423f8ec865c221484018d8cab8442908ff3a181708852114e3bb0ceb302420087e87d9560484018b8e7b2ac0908021fa1c65581210062e398cab024200c5f65dcd60484018b8cbb9ac0908023ee1d601812100477416e7b2842008f681dcf65084030ff0ea9eca10807179cd53d942100476412e6b2842008f4815cd65084559c8e438aca108021fe1d651942117e73312e5a88422ace7525d851084558e8a4bb0a2108ab391497614421155b2412ca288422f8f7865c85108455ac8a4b90a21080279e19721442117e73c32e428842009e7845c851084013cb08b90a21080279e0d7214421004f2c1ae428842269e4805c851084018eaed290a2108aad9a0a5214421006b2b94a42884200ae586d4a2108455acceba9442108ab591d4528842100673a16ec9084200ce442dd921084019ce65bb24210803390cb7648421154bb43eea9084200c7776dd521084018eeec3aa42108ab59e087548421156b2c10ea908422fc76621d52108401ace843aa4210803599087548421006b2a10ea9084200d64421d52108401ace643aa4210803598c87548421006b2990ea9084200d64321d52108401ac8eb31242108ab591d75248421004f343ca49084200ce7769492108455ac8eb29242108aa7921d524842100673bb2a4908422ad64755492108455ac8ea29242108033961b7648421154f342eec90842009e783dd921084013cb07bb242108033998f76484210067231eec90842269e680dd921084019cd0fbb24210803399cf76484210067239eec9084200ae580dd921084553cd0fbaa421080339ddb7548421154b343eea9084200d6776dd52108401cceedbaa421080319ddb7548421006b3b9eea9084200d6573dd521084015cb0d3aa4210802d9a16754842100573c32ea9084200ce7765d52108455accea3aa4210803595d47548421005b3438ea9084200d66871d52108401aceec3aa421080399dd87548421006b3b98ea9084200d66731d52108401acae63aa4210803591cc7548421156b3c30ea908422ad65861d52108455acf063aa42108ab59a0c7548421156b2c18ea908422ad64831d52108401acec63aa42108035998c7548421006b2b18ea9084200d64631d52108401acc863aa42108035950c7548421006b2218ea908422ad67801d52108455acd003aa42108ab596007548421156b2400ea9084200d67301d52108401acc603aa4210803594c0754842100
  | 15 => 0x2180c4a88aa3da1a719495100672314e3292a200ce7621c552544af8decb394c0a88023ba1f625815100657ba6c4b02a200cac74d89605440199ee7b12c0a8803331cf625815100477438c4b02a200caf741896054401958e8312c0a880333dcc625815100666398c4b02a2008fb87580605440587ce8aa4c428807179cd539885103c3e42ae6b10a200a7586dc652144556cd05b8ca4288bed9a087194851156b3390e3290a200c6f76dc951144018deec392a2288ab59dc47254451156b3c08e4a88a22ad66611c951144011bf06ba2c0288063720d745805100477c12e8b00a2008ec825d160144890f90eaa2c02880b0f1d154580510045fc22e6b00a2028bc845cd60144011df04b9ac0288023b20973580512243e43aa6b00a201c5c7354d60144019cae538ecb1080a1f21d54596210053a40aa8b2c420187c8754d65884014e902a9acb108021fe1d651962103e1f32ae832c4200c3d655d065884cfa58a4ba0cb108ab2d985741962103e2f32ae632c4200c5d655cc65884cfa98a4b98cb108ab35985731962133eb2294e3a94422a8ef865c752884013cf0cb8ea5108ab39e1971d4a2115473c32e3a94422ac76651c552884018eaca38aa5108021f61f6514a21004b6c3eca2944200b6681d94528847f1dd0e292c1108febaa0052582211fc7743c84b04423f8ee878c9608847f1dd0f90ac1108febaa0321582210047dc3ac030442008ed82dcf65484011eb03b9eca90803175ce53d952100c3fc3aa7b2a4201c5e7354f654840147d0829eca908028f61053d95210051f424c7b2a4200a3d8498f65484014dd05b9eca908029b60b73d95210053b40ee7b2a4200a7581dcf654840147d0939eca908028f61273d95210062fb9ce7b2a4200c5d731cf65484010fd0e21eca908021f61c43d95210070ea1887b2a420087e87d0765484010fb0fa0eca9080297a0f41d95210052ec1e83b2a4200a6e82d0765484014db05a0eca908021fa1f31d95210043ec3e63b2a4200a3e84cc7654840147b0998eca908029ba0b31d952100536c1663b2a4200a75811c365484010fd0e186ca908021f61c30d95210051f42061b2a4200a3d840c365484014dd04186ca908029b60830d95210053b40861b2a4200a75810c365484010ff0ab9aca908023be0973595210047bc0ae6b2a420087f8759465484010fb0f318ca908028fa1263195210051ec24c632a420087f8758c65484014ef02a18ca908029d205431952103c3f4388632a420087d8710c6548401c3a86218ca9081e1fa1f41195210043ec3e8232a4200a5e83d0465484014bb07a08ca908029ba0b411952100536c168232a4200a6f8250465484014d904a08ca9081e1fa1f31195210043ec3e6232a4200a3e84cc4654840147b09988ca908029ba0b311952100536c166232a4200a6
  | 16 => 0x3d895100556c20e7b12a200ae6811cf62544cf5cb0239ec4a899f93d4e53d895126c77c3aa7b12a2538ec8754f62544cfc98a6a9ec4a8802b9e0553d89510057240aa7b12a267a6e8510f62544014db0a21ec4a8803a350c43d895133c7743e83b12a2008ed87d0762544cf4dd0ba0ec4a88029b61741d89510056741e83b12a200acd83d0762544cf1dd0f98ec4a88023b61f31d895133d3742e63b12a200a6d85cc7625440155d0998ec4a8802ab61331d895100536c2ee1b12a200aae84dc3625440155b09b86c4a8802b3a0f70d895100566c1ee1b12a267ae581dc362544015cb03386c4a88023ba1c40d895100476c3881b12a267a6e8510362544014db0a206c4a8802b3a0c40d895100566c1881b12a200ae68110362544015cb02206c4a88023ba1c30d895100476c3861b12a267a6e850c362544014db0a186c4a8802aba1030d895100556c2061b12a200ae6810c362544015cb02186c4a88023be1d621895100536c2e84312a200ace83d08625440159b07a10c4a8802b9607421895101476c3c84312a200a6d85cc8625440155d09990c4a8802ab613321895100572c0e64312a2018ed878c8625440117f08b80c4a880a2f21170189510046fc1ae0312a2018dc835c062544011db0f320c4a8802b3a0e641895100566c1cc8312a2008ef8759062544011db0f318c4a8802aba12631895100556c24c6312a2008ef8758c6254455cc8a3ba8c4a88aa9ba16741895100536c2ce8312a200ace839d0625440159b073a0c4a8802b9a06741895100572c0ce8312a22ae2f5495062544015cd032a0c4a8802b960654189512a477c3aa8312a24e8ec8755062544015cf02aa0c4a8802b920554189511553742ce6312a200a6d859cc625440155d09398c4a8802ab61273189510057340ce6312a200ae5819cc6254455c9ea7298c4a8802b9a06531895100572c0ca6312a2538ef8754c625449b1d90ea98c4a8802b9e0553189510057240aa6312a22aa6e8510c62544014db0a218c4a8803a350c43189511547743e82312a2008ed87d0462544554dd0ba08c4a88029b61741189510056741e82312a200acd83d0462544014df0aa08c4a88aa9b21541189511547743e62312a2008ed87cc462544554dd0b988c4a88029b61731189510055742662312a200aad84cc462544014df0a988c4a88aa9b215311895100537c2ae0312a200aaf845c0625440155908b80c4a8802b3e0d70189510056641ae0312a200ae7815c062544555cb02380c4a88023ba1c401895100476c3880312a22aa6e8510062544014db0a200c4a8802b3a0c401895100566c1880312a200ae68110062544015cb02200c4a88023ba1c301895100476c3860312a22aa6e850c062544014db0a180c4a8802aba10301895100556c2060312a200ae6810c062544015cb0
  | 17 => 0x180000000010010000000000000001400000d80e0000001001000c00000000300000020170018008004000005000000001e0078004004004004000000400e0008000004000000800001200600500040000000018000008000001800c018005000001800601400000000000000028000000000001800000e0050060004000000000800400c00200080000000040050018000000000000c000000001800c014000000000000c00200000340000030000010002002000000c00c007001800c000000001000c00000300580000020030038010004000000000000000000280000040020008024010003000000401000100a000800400600000000080020018010010001003803c0060040040008000001000800c0060000000000004001007000800000000900100020010000000000001000800002601600100200060000000034002000001000800c0030000008000000003000000600200180400020000048018002002001801000200000000080020030000014000000000000c00800200000100020000008020026003004000c000000000800802600100100080020030058018006007007000800000100080040000080008008008003000800400200000000000060010000004000000000000400000000280080100030008000004000000004800c007000000000800000580100020010008008000000001001000000000200040020140008004000000000006c000008000000c000000000000800400a0008008000000000800c004001001800c000009000800000a003002000000800a0008010020001000800000400000100280000000010000051db0f214c5a8802b96064298b5100c76c3c65316a200ae5818ca62d440117f08b84c5a880a2f2117098b510046fc1ae1316a2018dc835c262d44051d90ea12c5a8802b9e054258b5100c7643a64b16a200ae7814c962d44014db0ba14c528802b3a0f4298a510057340e85314a200a6d85cca629440155d09994c528802b9a073298a5100536c2e84b14a200ace83d0962944015cd03a12c5288029b6173258a510055742664b14a200ae681cc962944011df0eb10c5288be3de197194a512bc3f43ea8b04a202c3c74d5160944af0fd0fa9ac128807171cf53582510047dc3ac0304a200a6d85d0b625440159d07a16c4a8802b360f42d895101477c3a85b12a200a6d85ccb625440155d09996c4a8802ab61332d895100c77c3a65b12a200ace83993625440159b07326c4a8802aba1263d895100556c24c7b12a267a6e851d362544014db0a3a6c4a8802b3a0c74d895100566c18e9b12a200ae6811d362544cf5cb023a6c4a899f8bd5254d895127477c3aa9b12a2548ec8755362544cfc58a8aa6c4a8802b9e0554d89510057240aa9b12a267a6e851cf62544014db0a39ec4a8802aba107
  | 18 => 0x392199800000037400000000000000098970000000000101a00038a000000042340600010ea1d209f80012e00004961764de63a40000e80000000000000111200000000000007fba898918d0a5f70969e924fa2f000008840000000000aec00014f00016600006750f6000000001a0000f551dc00003798350360000002424490000000030400000000021c08667c71ea12f8c6402f26280011ea70107f96fc9f010c966077c00087d0134000000252000000400d000000c00000c00180080040010000000006001002801003000100080100020060000000010000001001000c005001000000000e0030000004001002000000200b006000401800a000000c0060020000000004002001000400200200380080040000008008000002000002c00e00400400000020030028014004005000000c0380030000004000006003801c01200400180040000010000028002000000000400600000480040040010078000004000003800c00a001001800000000400100080020030068018000001000802400c00100000040100000000008010004000000000c0060000010002000001000800c00000200380080090030008000000002800400c005000801000c00600000340000000000000018000001803000800200200040040000000004002008000800402400200100080000030000014000003001000001200100080000040000008000014001001801400a00100180040020020008050004004000000c000002000800400c00100000280020000008004008005003000800000500000380000020000008002002002802c00400000080040360010020014000000004800400000d007001c0220080000000004000005000001000900000000040060020008002000001000000000000500140080000000024002001000800000000000080140000050008014008000000000000000a0000000006006000001400000700000100000090048018006007006000c00200f001801c00e009000000000200400200200000000000000044000001001c00001000680080000090000000000000003801000200300000000000000050020006002002804000000100080000060010038000000000003803400200000400000000000010014000000000000400800300000000040140040004000000000002000e007001800000000100100100000000000014012000000003c00c002001000000000400380040040000018000000000000801000400000000140040010008000000001001004000000b000002c00200e001800800000300100040020100000004000003004001c00c001000001400200600180040000010000000004003001800000600b0010000002006000001800600100380280000070018004000000000000801c000000000c0000020028
  | 19 => 0x4a51664000000498800052e777015c00026e0e3000091e11a421000046e00042c1c1210c0000003f78d8800000019d1e1481c1b919b8894ef67ad9ab000000000001600ce0001211439fc83f22c94420000c191f8800232415072d2aa23e40002a23c0051287c3fb0b183b921657533a1968522388000094c00044605080008d633b487069c09a2da0000758dce71b4a699bc0000000000000000162800000096035b16b85cc37a934035800000000040d200e0000000000000dc27cc00021368800001560000d34958000000021c0000f58000000000000000000094f2c0a3d80007732be000002600000010a903a00008d800000034941485540000bb48421c47ae0003111a2d14c00029e0b0000080a3d4c0000003190000c9447c7e800013748605b200000002850003b7174cf4640406e9e552c6011a889b6ca96000004214c5da3f508f139d0575ba0e11ed000000008e8000e60288285000000005b000000000800039023b45700000000bf80003c2170a2a52a635d12114ac4de30a3cf94780000000000000fbb1b204017a400083e49380011c600026ba048000703000000079200001f400073a000000000090a20d0e886ad16e00003880f00000000000000000000305460848d8aa800000106200013200012b249045c80002cb0000000000e1049c1f69ff0bac15d00000000004c342b00000008d800015acfb10513b7800000000039c00000b10004968d680ee1438d2036127a5880000000eca6212fa871902a0330000000f44000000243c00000000000003266203fc04ac00042f00004f494e00023ba3a40000002341400e7691700015c00730bd4850788f642f91a700009f20000b70ec40008ef0001e5e00000000024e0728000066502cd3093f00014ec0da00000000000000000001518dc002e00000011104d3000000110000043700000003e62a1a3d000000001c80000000003db800000000000000008560000c90000d6e2b649200003fa06dbd09e0c82c8b541e4a100001450000000000000343400000095008080743ed000000011c0007ac80000000006260001f4ec5c47b3bf21f8000237486058e8347f5000000000008e00016789c24182841daca9e32a0000000e78324000000000000000000001280002278b10c100fb332a0d644e33f03280000006271c180011ce86f0000000000000000000000000000000004920000d297202400000d1a024000090196000114073a00000000002173898f2895e14420100000003e700000006aa733000207848800004980000006f74409fded5c0003e80126d2c58642c1b0093e7914758d94b2223630a491cf6c41946389c453c5480d6a00d176549454035c8ba0460ba181c9dc9070c180001d05bc32f00925ea16a4631fe43c0942022045c96827e00380000000004038000
  | 20 => 0xe000000002b300000000000000891c0077e0da1d50290a4684a3a894d8fb409600f8b70eb669c3ead8ac0004750bc97b009c5f809a223875c895249027d09214b116916cd6c0003080dd23880003d1d958afc3b6000880103e9650001d6e00000000021843dc00032780012e20000000cf83406160b786bc04613b31981e82002ca3d3a568d9e93721a056ccd21b30000c38dcc67f0000000516000000000000062a4108e847a48260000430f346242411bc8cb61783fc5f2a0000000000000d7283214e00005ac00007b19b4900070412850d2747920c3953066c4030bf0000000000415212c2c87434385b186e200018c244c71a8fc00000001a10760ef18a000026b41b05b000000000000000000003ee8000d8e0001c8a4540006bc00000003980000001f129d44ce13b87285e42e30eca1792602c60000f8c0006b43d156ec0008450441364ad47153aa15e4000000000000000065f800000086c4a600000000001f24611d74fb34a004e0000fc684246289980000000000000af05683dd816000041105b000113a0002f514dc0000000000000ec50000001ea400000000000000004c90000f18f6600003023440005a90ea1a652c24893f5a1e0772000000000106e0000001a0a00000000600000000e500016000003131b819c40008553a707d4d4c000000000127c94800017940000000799bfc26a36b8b11a380002600e793e800000040c92444362043d78000be0966000244524a9680001744fc836f000000000018c3bd09da000678000033cfee2120000b7800000004b80010a4000397890479a60f03bdee022956100002bc00096e0940000c2a85d301218c0003dd00018dc0b976d0000000ee419d18188890558bf06f400000054e330dd2c4ac1aa00000000005923550000fcc7ed2559be8e946511c99ac91cc8504a217102800000000610eb476c8264aa88c20b7452800081400000004c7068467000000129617f000000000002abca236c0000c202e0e94ee876aba69728e0e0df065a04ce8a12ca980e38a3e35c34b81fc43b0003c404a800001f800224000030d4909920e9800000000004c219a00000000007221521e64d6695205a000000032e00005352402800002150b48085162879099a248aff00000003784b3a00800082e17280001d63d341d210400093234911911c476b8ed168873245e2d01c9c2167c991a97692de9003a1175ca9435041f8dd0e6e88b128003400070c0000ea00003313f3800000008613413180007c7994800043a00003c01ba8cc78612696500867baa09800000000013a089803203e186044cf8a000000114400000000000000008f127f80000000000e2400123a5053eb80b20900001541aac45674708c0000a501a243b0f7c90200040c000000086600000000000002061d20f08816
  | 21 => 0x200000000004f3296800000068839f136000000000000000000000000000cc000000000010c80000000000a74000124ce2c3683fd00000000000000000000ed27980304000000000000000000047308f8000fa4474000227000043f11c000038a000479800000000011900008d23f901f9790ffc43500000004687591c0908007f27007d1078e790001041e9000000000000000000c04670000ff40000000fc00007171ab800042000002d00000003460000504928000000027400045f1888000aa672c0000dac0007f99d192fce3e000000180a0000000000000f5422027180000000000000cb40007c61d90edc5b600037a00000000000001c792522d025887cc00044e00017fc6d501446f848c45200028a875c00000034f01150cb0003e51e9e2060002e60fe87a250603c8a992b863f426800092a00012a000000000000000000003da000000000000014d14909be000475000000000000000000000000000f106ea0000000000df00001390000724000000000000000011e80002ea13043a0000bc0027013e0bc5c00000000ce00005ab33b800000000033c8da6b3800023b00004ae00036b8d00e9e2ec000161053685a00008507d679d0000b9c0000000000000b8688f00020acfe805541e99480002e22930d04000310000000052600036f8d7c02417b000000000000038d19a04b62d224c1ca014a9693fb0fd8bb61e800000007905623cf072c000000000000063645940200000000001698106d5090339ec00000000036f1ce40000000000000b6a00007f49940004391bb80000003ce0001c2800044800000002f73b50c280011ae0000fa09cd0ce6eb00313ec8124d519322881f800037c8dcc0b30000000af80007062688b3c2da8e51d580000000000000000a886938db000000000007b80000000000e68000540000304970053000000013a00a60003d7400102500000000012980003a912740004d20c4057c29c20c47d8000aba00020300000000000000000baa4dc41d8e18d0219195180011340990e380000005b11088000c3200000001223b800034a9f202840000001ae0ebc3e5000002e1e80001529544c6a4253310944496625381163cc160000001abc0003f3456065510679c34d8bf40a87613e697740000003eb5b880000003a9a21400000022508a8d0e63a0000000ffe25e3d2c0009b43590001beca1e2fb0001c98936885b40000032100024383c031f07d034000000000000000000003220000000d4250440413200000000001fea00092300000000000000395cd000000035d9740fac7a88cf0754a7c8a30ca0d9f0d21194b505290f66918000ebe00005d1160db87302633e09c3c43213311c80003fe7042fb08c47d44c200001c2ed00000001b3495c2162328ba0f2e8f023881cc00029019c9b60d980bc13f800
  | 22 => 0x17a00000009500004830000292000145000000005e1bf195c0000000000000a827a80be8658c7a1a100e0d4513e23a0ff01900002894121d9cc24118a4691c05f85e631499746c72b913be4d8af40fe00010404be2b041dd1b4d12091365a2485d20002d804e44f6000000000000000047900000000000000000dd4000000000000064a222a3580003f1000000000011a4a000012200000000000c8a0000000000b0473f2af14701b21250f3065c44802800015b09660002ad10c80003ba43b8c8cab03000000db21ac87a00000010c00b504d81d4f4342212aa5510be00019800002e22960000000d740000fb203846f933088000000000000000000000003dd1dd8eea0d3000000081e5be34312f00008c437e8f04000887000002400000030f22ad06a44134993b46da3e20df11702ac79b09f00380000003ec225000018600000000000002f940000008bd000041800065e8000000000000000162c0ce6f10791c3400038c41c03b0d849350000000a4a5323d70000000189497800108c67000018f0e4200000000007664441428152bb17ad1a41af84b04270dd0520244168263a29d2044d42ca9a8020b48615b8000a5868185764f000034d42380012549560a451400a36d441007a89fc0de45c01ec7fc56d1c2803cfa21050174b20e0a000290139895a153000000070e0002f09c8c0002bd05f986800075f010c000886577199800064060c2fd8bd831c5e80000000a2c00000000000000002440000cb800000000008c60001de80885e88400000000000000000214400028f00000000000000000000000000411996402c42e000000000000000000000000002c71bc00a0000000000000000000000000000001bf90540000004b6887083e00000000003901fa43c80005248b10000000dda6c40000000fb70000001548000111109800053e18d13d0f2c0000000d400410d656f25b049cb92716099000102e8e000000010ae0003ef40010e628604d0d9b1323171811034c3845a000000062a7ed8000000000478000100091856e000000000000000000009e0000000082c00044d00000000000c80000d4c00020600024100005761c8000078a1d300000000006e3000090c91e0000180c100000004a3081c00000000012c800000048f93bc00000015380010cd0002bea262edf4530979d70c3649a00586b06e70f137b0000f4d0001b2c0003a00003b118b400023b00000010b208300000011b8896346855cace5cd2e7202ea205f7aa398f8b266b11b01bf021268417525783ca560000000038237d2259f7200000000009b800037600000000000003fe800000000000000000df5070ed8344b891690001a8c00000000004b01980002c481c82a07bc01500009fa34f1171f10fc766b1b90b6009e8ba284933000000000000000000e
  | 23 => 0x360000000abe000000000000000013e000000007400000000003cc27a81f80001081bd97f048a3673b000005a80003ab23051578fa36d08fea701ef000000000080f28e80000000002d7800000000004900003ce7460ec08cc0000000d714fc08453900024acfb673221b9e66e3a00015700000000000000e2800000000020f0cbe00000c0000b8a00000000004b26d90000000bfa28c2c50cf475a1dd4084318ffd151000000000000000000011965e323f1158bf27bbb4189d26c900a1cd121000000000000000af46a0001070b4e6ce177927837e08117fa1f07d80ea0dd800025c3f4033e538000000427800000063600000005320323c68000ec300037a80003c61590001e3c14c0000571e28f9e6fe00020052287f68000628a7a10700017711900001250000bbc4bb099df0cdde429474033605a596000257400050b1a18da40dc06c2ad8ff00000003269ebe0000000001ab4000055adc199c000015070000077663800000000003b828700000000002d30000b501241cda0b44eb0000000000000960000000000070e00f191cfaa01b3ea1b740000002da08bc0004fc3a80d3091c00039881300007fb0010be00005258629e406420000450000ba80211bd243457e20134500005ba7ab0e486c0a8034a4b6238471e335395a30c75800034f8000b9e690c7203348fe000000226c92600047b94607ac59d0cf983800000028107c08a423f1aa0de44f00490be1f5e14e0003970b54fb57de3549c60ef256646c82a43f83070000e54c769180e7000084c00000001a800044200000000000ce23015945645aa3474c241b10001cb15648dc0000000000e381c31ec16b855668233e0b44cfa68f0000434c9609827b1e300004bd18d004a0000000bba0cc0000000b80000f1200000000005960001f900012d600000019f2000000278800063e9430000000ca637c3629c650b67641940000d7e640091400000075e972202c1b84833880c7063a1b50568a0800a5ac2f8d66cb8204a00000010dd000465125cfa1000000221800002900000006d086d000000115439e00000000000000000000000000000000000000000000000000000000000f048651a2899c74e00029880005dc00000000000000001f7a458000361209013ee120001cb8000c884e212e800000068f81008f6be60000002244f316d53371faa7ee55c0bd4000bc46582f78fb81fa00018f11508920003b600008f467bbf7000099478b0204000000000000051ca1a00000000000b221e1e7830aee093900010f0ca800032184d861e25a36e251cae44f4000000109000030a0b0800000000011bc0000000878cc86d400001145845f40002040000ec700000000000000000a5400124c44715480000000002a8211a16600025d1b4c00066a00002c00000000000b0c00000010c00
  | 24 => 0x640e6a4de0c78e00fc25c61469514d280e722aa2b8d202692db8db6fd41e90b000002b000000000001720000000000ae684e203975282834213503546a479a88a00002a40000000310fe65df05d1ef498276e8000f4021400000000001a8034acf87852be3b025121a80000001cf98c0f400170159df45e232729a8838498694b00148900b6410721ac01866644910000d82283321092b2c869d000163000090500004e0a5c03b1f0800106000000003e000000043900011260000000000b8e00000022c0c3e00000000000004eb00020a000082c02f80000006c80001ec00007e541a4abc28c00000022cc4d80000000000802000000150800000000000000004c0006e46cef85740000000786000000000047800000024ed16800026b11f42ce59009045c8b6688d1670000cfc0004450c4817c00000000000000001759dfa0000002ab80004b850c218800011800033601848ae6171a58f791fe000000000000013c000080d2926d030e823c22a00007782885b249600008a007173b82d40000003c0000000ce4a0c930c0470cc216b0d880000002cd00004e8ed3763317800002280980023340005c200000011d80350000000fd80001d79fa40826c9018840810800000019d80000004ad8000ae200029500001560e92d296340005a3342c00000000046a0600fc06731568148c0a3a205180000000000aa63000003b43d280005420000000000fa60a013c98e4be44f736914bccf60000001e04c088144b1161c38b4cb0000000051807afd00007388ad251800000026d45f0000b6f06901b80000683e8348949cc9200000000002cc3060000af108808b3050fe0e2420f44dd39400048a05c000089876a0000a0400061300000002b870b00000000004a400000005ee00000000000003e0326246848983d89341f05e60000000000f9c1f82361e383da0003aa9f709422ba3bf800000000000000000000000cd8000f7e3d94a29eb11a675743f80d81b6116372a47816254d2ec1a30c620000000ffcb341fb21405500960618410000000000000051e0007cb0000000a52000000000000000000000000483c70000000b95646403000004b2b505500003e20002f718a643e1bc1471bb89b68fd000000000000046d0000000000014c00000000044b95a4f2c31446800000000d044c16d8caa000000000000000000000000009510001e1cc2200020b8660000000452000053a6ca00000009c80e11028854c584e000000f2aaa00000000000000c70001cf4ef045800015fc0000003560c580003084028000000000029400095200024c80009d25a113a8cac0740000000d1c04a6e90000000c067df1c224b8f6a0001d4a00af8413146918d012a30b10d18040000001d30000000000000000113c00000000001644f21ee00003020000001d0516c7
  | 25 => 0xac83e43b88158b9f43a47c200096e479368972c2ca0004361f00eb05e7000000000000000019e85827441de223000051200014500000000002070112000000000000065000008250980000000d6000000000000f600000000025551040000820c1400018b45787dca6600020e8578000000000101516400005600000006e40000000a42000000080887a000000000000000048c97c20ae0404808000000000262049800000000018069d83641809a9c0008dd00017ac4607c3a81a1db17826207c9b581cc7d928d8000f4c19c3a496e40004d0000000087692830300000007f000000000004aa3ffc00000059725c9b0c668000158a4700000003c980005284cf15a2284dd80003b32044d6a8cc0000000a2e47c016c000000941000000058e00016f800000000000021a000000000016f448000000005d80004a500010b40007c903303d41a448b2d69d00000000000000107264e4ab9ca444672a1f4800000019900000002b41a9105160c00036c0000000000000000000000000048923f813c000000155800000028086dca323663dc9c44000000231000119e4b50001ef904473e80020410c467201e84ca00014c20d80000858de0c88000d7a0002120d782cd7f11df17d00000003f117daa680002e74000af60002e90e2400085c000000104e0000001dfe00012900000000004ac00017c40000000000000d48063000093cbda00019e000000000000000000000003e44000ac60000d300e00000ca21c0d106c662301ac0000c44721731ec4d44000076803e00011c8001a9400027600006e0b0a3db3318a5449c806800146810e8d51978
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x44d0e49760d21580210049925583485600844d2e09060d21580210063121f734856008401a4485dcd2158021006b02037348560084018c4871cd215802100691214734856008401c44751cd2158021007211d0734856008401ac0801cd215802100698217804856008401a638520121580210069821480485600844d264956192108750004992498510e6194001a158550c4398650006856154310d619400162694e06621465000591a4f81988519400126698d06621465000591a4f41988519400126698cc6621465000589a5331988519400186475209614865000619217764842194001864855d921086500043965e8648421540558647520961484501561921776484211404d0e4985d92108450156192157648421140012649560a4118b1000499255828c462c400196075603624871000619a1f7518921c40010e5989d4624871000439e617318921c4001464955cc624871000638a1d8018921c4001c6075600624871000558255215c021c404d0e697e053258a1013439261625c7528400181e8750c43d95100060761d4310c654400181d85dce73d911000607617749d36344001a0d8550c43d891000499255819086244001264956063218910004992558290462440012649560a311891000689217645c46244001a2485191711891000691217635c46244001a448518d7118910006836154310c6244001a8543a044318910004992558790462440012649561e3118910004992615418851440012649854c6214510005296507518a21440014c5931d4628851015619204751892144001c146418c754851054e0d21c6419521441518548718c6548510136381c286dc92144001866861d7724851056d19a5875189214400146697d946248510007091d7641892144001c24751906248510007111d7631892144001c447518c624851000519255741892144001464955cc624851013439a5b8748421440018a464e1d21085100063118f87484214415b26696215210851000689190854842144001a4463215210851000499a6365484214400186787d95210851000689217644842144001a4485d8d21085101343926076485204404d8e0801d92148110006191d8854852044001a0d8550c4398810006131d683d09620400186475a0742588100060b1d684cc9620400186475a073258810006131d6839d1620400186475a0674588100060b1d6849cd620400186475a06735881000439a5f8150d620400106c976144358810006836154310d620400182c75a127158810006131d6839c56204159867801d4715881056619600751c56204001464955d0715881000519255731c562041598678721562c841000619dd8854842104001865762152108410154992558458821040552649560d6208410154992558614821040014e1969c97008410
  | 1 => 0x1485629894004c59b04026c630fd61a70d8006c2200208868405280ba790bb00952100000000000000000000000000018ace3200388f97f001793528002a8016a5f8022a00000000022000024d627f37000a4001c8017400000000000001c0202033a751e122a001527466cc0c8241c04c388e998f00eb000000da460597658422d01532cb1e9c20d4900000000000000f6865add4fc0fd28002800000000600804000600000100200018080600000080201020020f0100410020706c0a00040300e000e83400010401830020380c0c000302802030c800000000024040b018040206028104c0200088121c008080c0006004101715439a5f814c962d4401a0d8550c43d8951006836154310c625440181d84dce73d952100417e61731cf654840181e8750c43d952100499a4b8150c654840181d8750c431952100499245828c0654840126492606301952100499245820c0654840126492604301952100439e59845c851084010e79660d721442115459255835c8510840146595d0b764842100531a4f42dd9210840146595ccb764842100529a5332dd9210845516698d08754842100459663421d5210840154693d0875484210055164f421d5210845516698cc8754842100459663321d5210840152694cc8754842100549653321d521084014659598f764842100529a5263dd921084010e5989cf76484210051965673dd921084014a6949cf764842100519e5973dd521084558647561a754842100619a1f761d52108401165989cc754842100549a52731d52108401525949cc754842100519e59731d521084551669898c754842100459662631d521084015269498c754842100549652631d521084014679650c754842100519259431d521084551669810c754842100459660431d52108401d054310c754842100519a5a301d52108401465968c0754842115459a60301d52108401165980c0754842100519a58301d52108401465960c0754842100549a50301d52108401525940c0754842115439a6376595210844d8e07061a70484210061961b759c12108401865861d670484210063120f765c1210840186776e15704842100459a60755c12108401944831d57048421006511d7835c121084018c473e19215802100459a5c85485600840194473215215802100459a6375485600840186786dd521580211545926075485600840194485dcd21580211343925d82145600855dc447314851580211343925d8290560084012649560a41580211343925d828c560084012649560a31580210061921f85485600844d0e697a152158021134b8a4285485600840186487215215802100499a5c85485600840126698dd521580210061921f754856008401a6080dd5215802100499260754856008401864871d5215802100698200754856008
  | 2 => 0x48648011900418011b5e8023800b78031c00a21a8190d8a071141eaa1b92cf459118d018004f30d5c0000314000001ab4008b50ae697600000034918022000b4802d0c47832984de000027cc1005cb082c00202b112960c187902600000bc1f0024400000000600002b8005684d42ad18a635000a2b8000c800bc0017d34b2000ed7c0016800544a022405c0d00248d00000000007c3653f46005d8019a0039a000000139dc00003180000000020400005f80800004699812950026d5e4420800c57d2d9a5981e23ae2ecbd1d27188284ba60e4ca5b0541085149b6b8b727960d61d0261c004e28
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x82801920240001882cc286218ea9084200a112a0751cd21580210070090a3a0e690ac010803880742007348560084015025130aa188730ca000a0329d8550c4358810
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x1
  | 4 => 0x4c
  | 5 => 0x4d
  | 6 => 0x138c
  | 7 => 0x6
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x124c
  | 11 => 0x124d
  | 12 => 0x138d
  | 13 => 0x14c
  | 14 => 0x14d
  | 15 => 0xa4c
  | 16 => 0xa4d
  | 17 => 0x134c
  | 18 => 0x134d
  | 19 => 0x198c
  | 20 => 0x198d
  | 21 => 0x20c
  | 22 => 0x20d
  | 23 => 0x140c
  | 24 => 0xb0c
  | 25 => 0xb0d
  | 26 => 0x140d
  | 27 => 0x2cc
  | 28 => 0x2cd
  | 29 => 0x14cc
  | 30 => 0xbcc
  | 31 => 0xbcd
  | 32 => 0x14cd
  | 33 => 0x19cc
  | 34 => 0x19cd
  | 35 => 0x95394
  | 36 => 0x94054
  | 37 => 0x94055
  | 38 => 0x209
  | 39 => 0x20054
  | 40 => 0x20055
  | 41 => 0x1549
  | 42 => 0x20e
  | 43 => 0xb1394
  | 44 => 0x141394
  | 45 => 0x154054
  | 46 => 0x154055
  | 47 => 0x154e
  | 48 => 0x138e
  | 49 => 0x449
  | 50 => 0x1649
  | 51 => 0x154c
  | 52 => 0x138954
  | 53 => 0x138955
  | 54 => 0x98c
  | 55 => 0x150c
  | 56 => 0x150d
  | 57 => 0x95414
  | 58 => 0xb0954
  | 59 => 0x94b14
  | 60 => 0xb0955
  | 61 => 0x94b15
  | 62 => 0x94e
  | 63 => 0x1409
  | 64 => 0x140954
  | 65 => 0x140955
  | 66 => 0x95415
  | 67 => 0x154d
  | 68 => 0x2c9
  | 69 => 0x2c954
  | 70 => 0x942d4
  | 71 => 0x2c955
  | 72 => 0x942d5
  | 73 => 0x19c954
  | 74 => 0x959d4
  | 75 => 0x19c955
  | 76 => 0x959d5
  | 77 => 0x44c
  | 78 => 0x44d
  | 79 => 0xd4c
  | 80 => 0xd4d
  | 81 => 0x164c
  | 82 => 0x164d
  | 83 => 0x1a0c
  | 84 => 0x1a0d
  | 85 => 0x1449
  | 86 => 0x1489
  | 87 => 0x14c9
  | 88 => 0x21254
  | 89 => 0x21255
  | 90 => 0x155254
  | 91 => 0x155255
  | 92 => 0x138b14
  | 93 => 0x138b15
  | 94 => 0x141395
  | 95 => 0x139414
  | 96 => 0x139415
  | 97 => 0x2d394
  | 98 => 0x1382d4
  | 99 => 0x2d395
  | 100 => 0x1382d5
  | 101 => 0x1399d4
  | 102 => 0x1399d5
  | 103 => 0x140e
  | 104 => 0x14c154
  | 105 => 0x14c155
  | 106 => 0x2d354
  | 107 => 0x2d355
  | 108 => 0x14d354
  | 109 => 0x14d355
  | 110 => 0xb0214
  | 111 => 0x20b14
  | 112 => 0xb0215
  | 113 => 0xb1554
  | 114 => 0x21414
  | 115 => 0x20b15
  | 116 => 0x140214
  | 117 => 0x140215
  | 118 => 0x141554
  | 119 => 0x21415
  | 120 => 0x2c214
  | 121 => 0x2c215
  | 122 => 0x202d4
  | 123 => 0x202d5
  | 124 => 0x19c214
  | 125 => 0x19c215
  | 126 => 0x219d4
  | 127 => 0x219d5
  | 128 => 0x140b14
  | 129 => 0x140b15
  | 130 => 0x155414
  | 131 => 0x155415
  | 132 => 0x45414
  | 133 => 0x140454
  | 134 => 0x45415
  | 135 => 0x140455
  | 136 => 0x141a14
  | 137 => 0x141a15
  | 138 => 0xbd4d4
  | 139 => 0x2cbd4
  | 140 => 0x2cbd5
  | 141 => 0x1642d4
  | 142 => 0x1642d5
  | 143 => 0x1654d4
  | 144 => 0x2d654
  | 145 => 0x2d655
  | 146 => 0x14cbd4
  | 147 => 0x14cbd5
  | 148 => 0x19d4d4
  | 149 => 0x19d4d5
  | 150 => 0x14d9d4
  | 151 => 0x14d9d5
  | 152 => 0x14d654
  | 153 => 0x3ce
  | 154 => 0x170e
  | 155 => 0x40e
  | 156 => 0x188e
  | 157 => 0x202d1
  | 158 => 0x144211
  | 159 => 0x148211
  | 160 => 0x24211
  | 161 => 0x28211
  | 162 => 0x2c211
  | 163 => 0x14c211
  | 164 => 0x249
  | 165 => 0x289
  | 166 => 0x95494
  | 167 => 0x95455
  | 168 => 0x242d1
  | 169 => 0x282d1
  | 170 => 0x98e
  | 171 => 0x150e
  | 172 => 0x44211
  | 173 => 0x214d1
  | 174 => 0x442d4
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 34
  | 7 => 1091
  | 6 => 3113
  | 5 => 2418
  | 4 => 206
  | 3 => 6
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
  | 8 => packedAt gbK8 (1024+((h/20+packedAt gbK8 (884+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (45493+((h/466+packedAt gbK7 (40367+(h % 466)*11) 11) % 2030)*12) 12
  | 6 => packedAt gbK6 (164790+((h/1182+packedAt gbK6 (149424+(h % 1182)*13) 13) % 5149)*13) 13
  | 5 => packedAt gbK5 (154206+((h/888+packedAt gbK5 (142662+(h % 888)*13) 13) % 4259)*13) 13
  | 4 => packedAt gbK4 (15131+((h/79+packedAt gbK4 (14420+(h % 79)*9) 9) % 345)*9) 9
  | 3 => packedAt gbK3 (494+((h/2+packedAt gbK3 (486+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffc03fffffffffffffffff38787ff87ffff
  | 1 => 0xe03ffffc1f03e03f807c07f00d7a7a63facccc
  | 2 => 0xffc07fffe003ffc0007ff8000e7c7c7c7cf0f0
  | 3 => 0x7ffffffc0000007fffffff807f807f00ff
  | 4 => 0x7fffffffffffff8000000fff80007fff00
  | 5 => 0xffff800000000000000000000fffffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x6142840021046142a30c2854600080ad805555
  | 1 => 0xa53b3d2c1721a53b0534a760a53a3a62bacccc
  | 2 => 0xdd8a5e56e042dd8a0a5bb1414a5c5c745cf0f0
  | 3 => 0x8106b9b5ae808101063c78b8f806f006f00aa
  | 4 => 0x102073e39cf31e3c5c0102020fef000077aa00
  | 5 => 0x1e3c0302108010206002040c0ff7f7db000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37427
namespace PEqualNP.Outside.L_meta_37427
open PEqualNP.Outside.L_meta_37427.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 14 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_128 : Interval s3Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_160 : Interval s3Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_192 : Interval s3Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_224 : Interval s3Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 227 := (concat (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96)) (concat (concat bs3_3_128 bs3_3_160) (concat bs3_3_192 bs3_3_224)))
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
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_608 : Interval s3Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_640 : Interval s3Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_704 : Interval s3Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_736 : Interval s3Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_800 : Interval s3Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_832 : Interval s3Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_896 : Interval s3Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_928 : Interval s3Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_960 : Interval s3Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_992 : Interval s3Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1024 : Interval s3Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1056 : Interval s3Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1088 : Interval s3Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1120 : Interval s3Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1152 : Interval s3Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1184 : Interval s3Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1216 : Interval s3Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1248 : Interval s3Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1280 : Interval s3Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1312 : Interval s3Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 bs3_4_192) (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)))) (concat (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 (concat bs3_4_416 bs3_4_448))) (concat (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)) (concat bs3_4_576 (concat bs3_4_608 bs3_4_640))))) (concat (concat (concat (concat bs3_4_672 bs3_4_704) (concat bs3_4_736 (concat bs3_4_768 bs3_4_800))) (concat (concat bs3_4_832 bs3_4_864) (concat bs3_4_896 (concat bs3_4_928 bs3_4_960)))) (concat (concat (concat bs3_4_992 bs3_4_1024) (concat bs3_4_1056 (concat bs3_4_1088 bs3_4_1120))) (concat (concat bs3_4_1152 (concat bs3_4_1184 bs3_4_1216)) (concat bs3_4_1248 (concat bs3_4_1280 bs3_4_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_704 : Interval s3Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_736 : Interval s3Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_800 : Interval s3Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_832 : Interval s3Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_864 : Interval s3Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 890 := (concat (concat (concat (concat bs3_5_0 (concat bs3_5_32 bs3_5_64)) (concat (concat bs3_5_96 bs3_5_128) (concat bs3_5_160 bs3_5_192))) (concat (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)) (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 bs3_5_416)))) (concat (concat (concat bs3_5_448 (concat bs3_5_480 bs3_5_512)) (concat (concat bs3_5_544 bs3_5_576) (concat bs3_5_608 bs3_5_640))) (concat (concat bs3_5_672 (concat bs3_5_704 bs3_5_736)) (concat (concat bs3_5_768 bs3_5_800) (concat bs3_5_832 bs3_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_3_224 : Interval s4Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 227 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96)) (concat (concat bs4_3_128 bs4_3_160) (concat bs4_3_192 bs4_3_224)))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 17 := bs5_4_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 6 := bgb_3_0
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
theorem bgb_4_192 : Interval gbAtlas 4 192 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 206 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_2400 : Interval gbAtlas 5 2400 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2418 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)))) (concat (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)))))) (concat (concat (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))) (concat (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))))) (concat (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)))) (concat (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)))))))
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
theorem bgb_6_3104 : Interval gbAtlas 6 3104 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3113 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)))))) (concat (concat (concat (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112))) (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))))) (concat (concat (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496))) (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)))) (concat (concat (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)))))))
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
theorem bgb_7_1088 : Interval gbAtlas 7 1088 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1091 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 34 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30),(inputs.getD 5 zero, 14, 46)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 33, 35),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 33, 35),(inputs.getD 2 zero, 33, 37),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 33, 35),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00eaeaeaa8eaaaaa00
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264040 * 2 ^ 32 + 3937053184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37427.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[3,6]⟩,⟨.and,[1,2]⟩,⟨.or,[1,2]⟩,⟨.and,[5,9]⟩,⟨.and,[7,8]⟩,⟨.and,[0,3]⟩,⟨.or,[10,12]⟩,⟨.or,[4,13]⟩,⟨.or,[0,11]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3937053184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3937053184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37427

open PEqualNP.Outside.L_meta_37427 in
theorem PEqualNP.Outside.L_meta_37427 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3937053184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3937053184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
