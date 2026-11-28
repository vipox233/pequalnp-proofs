import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37421.Model
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


end PEqualNP.Outside.L_meta_37421.Model

namespace PEqualNP.Outside.L_meta_37421
open PEqualNP.Outside.L_meta_37421.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 50]

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_37421

namespace PEqualNP.Outside.L_meta_37421
open PEqualNP.Outside.L_meta_37421.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x600039c29fb80000a9d02c89b0337a4a00404c2f08d4b2b750313e620b25483461a64c58800e080041040210223ff42fe42fd42fc42fe32fd32fc32ff41fe41fd41fc41ff21fe21fd21fc21ff40fe40fd40fc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa41fd51483f8a2905f14520ffa0a41fe41483fa82907f10520ff98a41fe31483fa62907f0c520ff90a41ef21483fc42907f48520f690a41fc21483fe80907f90120fea0241fc40483fe60907f8c120fe98241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041be540827ca8107f55020beaa041bd540827aa8107f15020be2a041ff53082fea6107f94c20bf29841de53082bca6107f54c20bea9841dd53082baa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841f651082eca2107f54420bea8841f551082eaa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fc65887f4cb10fe19621ff41c43fc83887d90710fea0e21f541c43f883887fc8710ff10e21f621c43fa43887d48710fe10e21ff40c43fc81887f50310fe20621ff20c43fc41887f48310fe10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff21843fc43087f48610fe10c217e50843fe81087f90210fea0421fc40843fe41087f88210fe90421fc20843fe21087dc4210fd88421ff54442fea8886fd51109faa221fe54442fca8887f55110beaa221fc54442f8a8886f151109e2a221ff52442fea4887bd4910b7a9221fe52442fca4887f54910bea9221fc52442f8a4887b14910b629221ff42443fc84887f50910fe21221fe32443fa64887f0c910ffa0a21fe41443ec82887f50510faa0a21fc41443fe42887f88510fb10a21fd21443ea42887f08510ffa0221fe40443fa80887f10110ff90221fe20443fa40887f08110ff88221fb10443fc20887d84110ffaa0217f54043fca8085f95010df2a0213e54043faa8085f55010deaa0213d54043f8a8085f15010ffa90217f52043fca4085f94810f7290216e52043faa4085f54810f6a90216d52043f8a4085f14810ffa1021fe42043fa84087f10810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681bf42d03fc85a07f50b40dea1681fc42d03fc65a07f4cb40fe19681ff51d03fca3a05f94740fea8e817d51d03f8a3a07fd0740dfa0e81fe41d03fa83a06f50740fe20e81ff21d03fc43a07f48740fe10e817d54903fea5207f94a40bf29481fd52902faa5207f14a40ffa1481fe42903fa85207f10a40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83206f90640fea0c81fc419037883207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4940bfa9281fe52503faa4a07f14940be29281ff425037e84a07f90940fea1281bd42503f884a07f8c940fe99281fc32503fea2a05fd4540ff28a81fd51503f8a2a05f14540ffa0a81bf41503fc82a07f50540dea0a81fc41503fe42a07f88540fe90a81fc21503fe80a07ed0140ff20281be40502fca8207fd4840ff290817e52103dca4205b94840fea90817d52103daa4205b54840fe29081ff42103fc84207f50840fe21081fe32103fa64207f0c840ffa8881fe51102fca2207d94440bb28881fd51102faa2207d54440baa8881fc51103fe82207f90440df20881fd41103f882206f10440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e41fe53c82fca7907f54f20bea9e41fc53c82f8a7907fd0f20ff21e41fd43c83f887907fd0b20ff21641ee42c83fa85907b50b20fe21641ff32c83fc65907b8cb20fe99641ed32c83f865907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83de43907f88720fe90e41ed21c83f843907fd0320ff20641fd40c83f881907fcc320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441fe42883fa85107f10a20ff99441fe32883fa65107f0ca20ffa8c41fe51882fca3107f54620bea8c41fc51883fe83107f90620fea0c41fc41883fe63107f8c620fe98c41fc31883fe43107f88620f710c41fd21883f843107b08620bf28441ff40883fc81107f50220fe20441ff30883fc61107fc8220f790441fb20883fea8905fd5120ff2a2417e54483faa8905f55120fe2a2417c54483fea6905fd4d20ff29a417e53483faa6905f54d20fe29a417c53483fe86907f90d20fea1a41fc43483fe84907f90920f721241fd42483da84907f10920ff99241fe32483dc64907f4c920f699241fc32483fea2905fd4520ff28
  | 2 => 0xcbdc64197f4c832f699065cd320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea5a0ff94b41bf29683ee52d06dca5a0ff54b41bea9683ed52d06daa5a0ff14b41ffa1683fe42d07fa85a0ff10b41ff19683fd32d07f865a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483bf42907fc8520ff50a41dea1483fc42907fc6520ff4ca41fe194837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4941bfa9283fe52507faa4a0ff14941be29283ff42507fc84a0ff50941fe21283fe32507fa64a0ff0c941ffa0a83f741507fc82a0ef90541ffa82837f50507fca0a0ff54141fe282837c50506fca820ffd4841ff290837e52107faa420df54841fe29083ff421077e8420ff90841fea1083bd42107f88420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6437f54c87fca990df95321df2a6433e54c87faa990df55321deaa6433d54c87f8a990df15321ffa9e43fe53c86fca790f794f21af29e43fd53c86faa790f754f21aea9e43fc53c86f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643fd42c87f88590ffccb21ff19643fd32c87f86590ffd0721ff20e43fd41c87f88390ffcc721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c43ff43887fc8710ff50e21fe21c437d52887fe8510ff90a21f721443fd42887da8510ff10a21ff99443fe32887dc6510ff4ca21f699443fc32886fca310ffd0621ff20c43fd41887f88310ffcc621ff18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ff55021beaa043fc54086f8a810ffd4c21bfa9843fe53086fca610ff54c21bea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043fe42087dc8410ff50821f6a1043fc42087fe6410ff8c821f719043fd32087da6410ff0c821bf28843ff41087fc8210ff50421fe20843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843f
  | 3 => 0x400000c00401000400400000000803401001000000400400c01400c00800002400002400800000c00400c00800000000000000001800c00000000400400400000000000000000400001000c02400000000800001c00000c00400802800c00000000400000000000400400000401400806800000402c02000000001c00000000800800800003001400000001400400000400800400000c00000000000000c00000400000000000400000000400800400000000400000400001400002000400000400000c00000000400801001800000000800000000400400800400402001000800000400000000400000000c00c00400400000000800400000000000000000802000400400000000401400c00000400400c00000000001c01400400c00003401c00800001c00c00000400400400800000000800c00800c00000001003400000000000801000001400000000000400001c00001c00000800000000000000400000400c00800000000000c00400800800000402001800800401000c00800801000001800000bfea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85bf43d0bfea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0afaa9217fd4e42ff29c857e5390bfaa7215f54e42fe29c85ff4390bfc87215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190bfaa3215f54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd4d42bfa9a85fe5350bfaa6a17f14d42be29a85ff4350b7e86a17f90d42fea1a85bd4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bbca6215794c42fea98857d5310bbaa6215754c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ad4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32ff21c65fd438cbf887195f94a32ffa1465fe428cbdc85197f50a32f6a1465fc428cbfe65197bcca32ffa8c65fe518cafca3197f54632bea8c65fc518cbfea1197f94232bf28465fd508cafaa1197f14232ffaa2657f544cbfca8995f95132feaa2657d544cbf8a8995f15132ffa1265fe424cbdc84997f50932f6a1265fc424cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032df2a0653e540cbfaa8195f55032deaa0653d540cbf8a8195f15032bf29065ff420cbfc84197f50832fe21065fe320
  | 4 => 0x3ecf25f200016400002f1139328000001fb80000000000000016800010d8000000000001b68f1df00000001a657a51847e85e9cb8000000001a351480010e4a05c783c8ea17ed1b83940000006e52840000000000000001e8001859400000000000001bd0000000000000000000c28000000a98000000000000000811848001d004d1a402a40000000002d40020f215839c6c0924000000000000d9ce7800000000000000000000000125c29d488002078000000000000000000000000000ef0368000000001f315b4000000000000001864271d080001700000013b8450001f503289c80000000014183aca40cbc0000015480018b4000179889e9da284415800013a0000f5dc2800000000000000000073950c000640000000000000000af80000000002480000000000000000000000003780000000000000020580000000000007c108e0ada880000004019f14593405bc0000014ec001094c084347b8001388ac2090361574878720e880000004e9a3c0000000010d4a09e68c685020315340000003220d1af0000000710b9c000000000000000000000000305c300000000000018a8000000001ad9db00000000000010c00015206111a0000000000000000000000000b10001378000000000000000000058fb400000051c6d8000000478000000001f71010000b4c0000019e1afc0000000008f9b39db8000accbcc1f83e1e08f082500000012f00000000018800000000000000012a00001a0000000000000000000000000000001598e700000000000000004180000009e1f400001a8000001800f01f09fc0000000000e7c000000001eb19a0000000011c50000000000000001cd00000000007620a4000000000ec00000000000000000021b0000000000001711bb08f0288b20398000001fac00000001c00400000400400800000802000801401c00000001400800001c00c00000800000000400801800000003000000800001000402c01400400400003400400400c00400400400002800800000800000000800400400000401400400000000400c00000000c00401c00400804400000000000400800400000c00000800400000401000000800000400000c00000800000000400001003002000400000400400000800000000000c00000000000800c00000c01400400400000000801401400000400000c00400c00000000000000400400400000000400400400c00000001c00000c00400c00403000000404c00000000c00000800400000000400c00001400001001c00400800003400400001801400000801000001800c00c02400c01000400801000800c00000001001400000400800000001802000001c00000000000000000400c00c00000800000c00403400400003000003401c00000000400400000000000000c00000
  | 5 => 0x2c1918713b010db98cf48c18d935a201179ef81548292d947888c001f88ab9a11be4308001b88c7dcf8091e80d8ce31e484f800000015c001168199f68000000000618000000f4c00009c0000000c80000003d8eb94cc000730000000a11660f38000001bc80000000000000000000006580000000019f8300001c600010f9b617b5b7cb44e65b05700000001ec9a1a1b8001ca8000001c3800115c000971e8c0000000016500001f1620000000000001f29890000000209df1540b2c0001d80001300005240017ad6e0000000001988001d48121470a295000000000001241380000000000000000000000000000000020600014a800000000012800000000089000170847000012d9800000013080000000000002240000018f000000000000196c2b8000341c406c800000000083d4e92b80014d4000000cc00000010d0a00000f496e80000015100010980000000009b0000e761a000000000082c7d86500000000000005d0000f500000010680000006900000000004d80000000000002e408c000000000001078001051e90e5000000000068c000000000000ed0000000d70840000001198ab40015d8000000001e88958b35aecc240014fc001b248e0e09ac90a8bf0be20da1006e1a909c00005ada548d48190760b8fd8768244001b8d4c49684a800000000000000000000111813545c001bf116dfa1c08e004980000014f4000000001b857f800000000004c00013c0020382181e5f991657b8001f39d880020e95e0000000f31aa8000000000000000000dd8c6c000000b8d1085c1ad20c8000000000000f2000000169928c00109d491a44000000000000000000b241ec000001bf8000a34f7d7a00017c8000001368e205cc48c000b842d8000001c10000000000000bb00017710e1be9ba8c550606f1120e9107c001589d205a05e5288000608000f140000005b9ba0a202b0000001e200000000000001fd98c0000000000002a0898001f49270c419080006a1410ae83a06680000012580011a8001f19d299643b82ed984fb0d98388518c180000013dc000000d081c22380000000021e1d101d1940000d49c00000000000000b60000000000000a48670000261e28000000000000000000350d01b1c29462000127c0014680011e00f5c9884a0803dc000001318000000460001054000000e69920000000000001df99980000d8cf00000000000000007a9851d94000c790f1d30681948d58000ed80000000000000000019900019a8000798001d69cb0000b680000021f96c8000000000000000000000648e5976a16144000000000000000030c0b9c8d671bac0016ccf61de0961d38000dc0000069c700e04c00022196002308d17c47080021d0000000789b70000748000001b00000000000dba0b0001150000001268000001d707cc
  | 6 => 0x9a49f92395a60091d4774000a90000000000001cea0f8a394b1bde24a1a8000115aa06880015789f00f95b89355d0000bf910129c0555e8001c4811d9d1900951480ce09940000e8f74000000000001944d51778aa8001d98000000000000000f34ac4d3c0000000000004ec0015a9ee9c19a69b31ae5d81b496a8000000000000348001c9c522010000000ae0ccc0000000000000000a8000001c91ad49198056900000dcd2c0000000001e0000000a815f1a080000000000005c8001c80d417f40000000000000010a40017f12f99b1420001d6c000000000000000000000000001ec1b161180000000000000016317e80000000000021e94d0000c996780000000000021c0000001a002b5794000001de9798000000000000809085c740005ec0000002d00000000000016b1274000000000000000d21460c480000000000011c4000000000000f28000000a580000880000019180000000011940000000000000000000000010e82e96680000008b000000141c000000000000000940bd94f8562068000000001c68000000000001b2c0010649880003b1868000e605a4000000b9195cf6cd900014a1181018000628000bc00010422100005880000000000007d14f0ad40000004814c80000002a994c000d880400000000001b0a7154c00199c2ce0a80000000ec000eb16d98b8000001910000b48ce80001b953cb700000000009a0100000a30000ff8000ac8570ba138c00000045c509994f99b202201c95500e5049294109928590000908000001eb5d84000001fd8000000000000e980021489394dd788990cb00b1b0c000001ef0001d74e196c12120e00018e8be40000000013560c0000001b113c13ce199c85a790012916ba129ac0a190ccbd4000000002150000000e100007a15b00015705f0000001c7c000000001638098ee8488002070000de9841d8c000001860000001399ab800000035800000000000179cb3db58001dd17b1d60c506380000000021380000015a0de167c390f543186b800047c000000000000001ff80002fe17126c000d196118780000014b80000012d17458b0000000758000001e180297a9dd8000a7524800178078c000000000000d10475da0000000000cd8454a51644f78000000f800000000000013e93e00000010dc0000000016bc000000000000000000000000000000000001ab09bc7b080000086800053120217400224000000071c0a0e800000009810b8001da9b1800005125069c5d4b1c7bc928001cf0000000000000000000000001898000000000000000000001dc1938000d560a0001e78d383d000000095c8621891418380012e80000019780008a82c48e49f4001e60000001628ca0001a71c20001b08000001ea98e144810578ccd1af40004494e59309d9dc9ca1428d291300000d1a
  | 7 => 0x13247c4ff00000004203f53613316352a4000000000468f900008a0000000a0c8d8000001e397480002e0fa00000000004e0000000000001568000000001a60000000f2c000bd12309fc8211e96f000070c85800000105dc6c67976124c00000059c000000f10000000000000000bc8000000000000001b4000202000104c000000000b40594da49200000019c80000006b000094c2f560a088000000000fe8000000ee0d94568000001cc0000000000000000000ea82680000005e00000016f8000000000000000000e414c1ee00002ac000000000f18000000000000000000000000b09a30f68001a4c000000290000000ce4fc8729ea554454134c0012c0000001091009a211c0001eb86ecb78f70c205f8001e940000000020180019d80002bc0000000000000000015f8000c595c00019a400000000000118c000000001320278001cc80000012998d03e533493092d750000298000210002108d30000000315a151f8001715f100000021f0001d7d758001fc90b0002000000000000bdd8c9e580000000000007c88e8000000676228000000000888000000000000001528cc40000000000000007819b80000008512a8000001be13a9264001518000000000b304b163caa00003a4018000b142f8fd0000a648b8c705492545b40004f04a1e40180000000000e140000012e1f58000c000014080006a8000a691f01887185dc0007151b00c14d8000791ea0699659f80000000000001625508048001fd0f45c589e8e28060000000001f61fe88c933c031218cb80000008380000000080000009d0000000000b880000009547500020b51d21d90384946fc000000000000000581b9c000001208000370000000338458b02099fb517c000001fb0000000001560084fc1810110534538000000b81830948b28331fa4239af893e16a2207f10300009b8fcccec578000118545280000000000001374000001ae0000000001a25d50000000001e71439b50000a880002dc000000000000000000001ff000000132c000001a1c0012ac0000017e1d400020400004b8cd562ccca20800136444c0013d97317d00019e80000000009a9ed8000000001d58e38f41acc000431380001190001b900000000000000000000000011d9170c80704dd1f786840000011a4c3000000000000000000000090009400000000202997c001791a59bd4000000000000200f88dca051e440017c1020000001664410ec93513f8741539ce0944e497388cc3c003c0010c8070439bc539142c000000000000000000000000000001531828db18080016184c8000151240000001a48001c5c0000014e000077d5590a0be922197165400106c000550000158b18d80044000da8880cddbc0c60fbc5d91c9a506f452c000000a60001958d6800022c000000000000000a7908
  | 8 => 0xd60000fc40011ad128c3853c144000001ae9bd9a8000000023c2418a00007000004453d1969820ad0661e9831000087000024c67c00069428014e191950fa9029e3051043e1212b13c80004dd36c000000000000000001cd8ad8000001718000409e022317d8465a993480000001412c8000001fe0b500008c4038002110000001b95975d79174da08dc0017204e40018f8148000000001fa9b7a1311bc000001b2846c000910000779311159688001a5c000f3c000001e503f1088000000000000630000bb80000000021c8001adc0000000002c86d0ab10708300000000fc0005a9d64490c74ba80000004f4e6c000f587721400000006f9058000000000598000000c91729a38001110001b81d9c00000000000000000165c000000000000001160001bb44855c80003800000002c0000000b380013e49796d0001818f84fe0000000000000d78b980019600005580013d504458dc940000005c42580011cccf8000000000000000000000000000abd1880002340000013f0000002178001f90000ef860000000119c0000000021805b00000003f8000c880003a933899c0013440f06a4000000000000000000000001bcd9c0000001498000000000000001ed0000000000000000000000000000079d90001648000000000de4000000f64000000000002049bbcc108ed8c0af00015900200800001f4d35229e116a16d4001954fb8000528000000b59740998000228000000001c880017fc0000016c4428df93707e0000160000000000000001bed4506e8001ba5279431d18001bb87d4000000000000c841683e8000001300001ee4000df12607f8ca8000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb41042ed62d0410db94b410436d52d04109fd96410427d6590410cf952410433d5490410db94a410436d5290410dd94641042fa6090410be582410427f6550410cf951410433d5450410db949410436d5250410dd945410427f65104109f594410433e5410410cf550410436e5210410db54841042fa6010410be580410427d65c8410af99321042bd64c8410cf953210433d54c8410b798f21042dd63c8410d794f210435d53c8410db94b210436d52c84109fd96210427d6588410cf952210433d5488410d794e210435d5388410db94a210436d5288410dd94621042fa6088410be582210427f6548410cf951210433d5448410d794d210435d5348410db949210436d5248410dd945210427f65084109f594210433e5408410cf550210435e5308410d754c210436e5208410db54821042fa6008410be580210427e64940109f592500427e62940109f58a500427d61940109f597400433e54d0010cf553400436e52d0010db54b400427f65900109f596400433e5490010cf552400436e5290010db54a40042f66190010bd586400427f6550010cf951400433d5450010db949400436d52500109fd94400427e65100109f594400427c6510010cf950400433d5410010bb98840042ed6210010db948400436d5210010bd98440042f561100109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200427f6548010cf951200433d5448010d794d200435d5348010db949200436d52480109fd94200427e65080109f594200427c6508010af99020042bd6408010cf950200433d5408010b798c20042dd6308010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010db94b100436d52c4010dd597100437754c4010ed953100437554c4010ed553100433554c4010ddd4b10043e652c4010dd54b10043e552c4010d954b100433e5484010cf552100436e5284010db54a10042f56184010dd94610042f96584010de59610042796584010ee95210043b95484010fa94a10043e95284010be586100437a5184010fc946100427f6544010afd9110042bc6444010cf951100433d5444010bbd8910042ec6244010db949100436d5244010bdd95100437765440109dd9510043b76444010ed19110043775444010ed95110043755444010ed55110043355444010f9d8910043e46244010ddd4910043e65244010dd54910043e55244010d954910042f76044010dd94110042fb6544010ded95100427b6544010eed9110043b86444010ee95110043b95444010fad8910043e86244010fa94910043e95244010bed8510043f36144010de94510043f25144010
  | 1 => 0x426d62150109f984540437661150109d984540427e6015010de98054042be64d4810af593520433e54d4810cf55352042de63d4810b758f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810dbd95520436f5454810db95152043ae5454810cb951520436d5454810eb551520432d5454810db151520436f5354810db94d52043ce5354810d394d520436d5354810f354d520434d5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520426e62148109f984520437661148109d984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042f76150810bd185420427f65108109f994420427d65108109f194420433e5410810cf55042042de6310810b758c420435e5310810d754c420436e5210810db54842043ad42108109fd96320427e658c8109f596320427c658c810cf952320433d548c810d794e320435d538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f594320427c650c810af99032042bd640c810cf950320433d540c810db948320436d520c810f34c8320427e64944109f592510427e62944109f58a510427d65d0410cf953410433d54d0410bb98
  | 2 => 0x5288510db14a21442f66588510dd99621442f76488510bd59221443b75488510ed15221442f76388510bd58e21443d75388510f514e21442f56288510f9d4a21443765288510dd14a21443e45288510d914a21443e64288510f950a21443e63288510f94ca21442f660885109f195214433f5448510cf151214435f5348510d714d214436f5248510db14921442fb6048510be181214437465485109d19521442f76448510bd59121443b75448510ed15121442f76348510bd58d21443d75348510f514d21443e76248510f9d4921443765248510dd14921443e45248510fcd8121442f46048510fc181214427e6508510cfd50214433c5408510d7d4c214435c5308510dbd48214436c5208510bd98421443e521085109f997404433f54d0110cf153404436f52d0110db14b40442f661d0110bd58740443b541d01109f996404433f5490110cf152404436f5290110db14a40443b641901109fd95404427d65501109f195404433f5450110cf151404436f5250110db14940442f76150110bd18540443b541501109f994404433f5410110cf15040442ee6210110bb588404436f5210110db14840442f66110110bd58440443b641101109f997204433f54c8110cf153204435f53c8110d714f204436f52c8110db14b20442f661c8110bd58720443e521c81109f996204433f5488110cf152204435f5388110d714e204436f5288110db14a20443e621881109fd95204427d65481109f195204433f5448110cf151204435f5348110d714d204436f5248110db14920442f76148110bd18520443e521481109f99420442be6408110af590204433f5408110cf15020442de6308110b758c204435f5308110d714c204436f5208110db14820442f66108110bd58420443e62108110cfd53104433c54c4110dbd4b104436c52c4110eed5310443b854c4110fad4b10443e852c4110fc90710443f141c4110fc88710443f121c4110cfd52104433c5484110dbd4a104436c5284110bdd9210442f56484110edd5210443b45484110bdd8a10442f56284110f9d4a10443e45284110fcd4210442ee62d5010bb58b540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e62950109f58a540423d6595010cfd8a540433e6295010cf58a540433c6295010cf986540433c6195010cf982540433c6095010cfd91540427f62550109f189540427f61550109f585540427f60550109f581540433f6555010cfd89540433e6255010cf589540433c6255010cf985540433c6155010cf981540433c6055010cf04154042be6415010cf55054042ee6215010bb588540427e6415010cf990540423e64150109f988540436e62150109b988540427d6215010db588540
  | 3 => 0x910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910cfd50524433c5414910d7d4c524436d52149109f990524427d64149109f98c524427d6314910db988524427e6114910dd584524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c52443e56114910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd84524436d6114910d9584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d0910bd98742442f561d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c5290910bd98642442f561909109fd95424427e65509109f595424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910b798c42442dd6310910d7d4c424435c5310910dbd48424436c5210910eb50842442f66110910bd58442442fa6010910be580424427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a32442f6618c910bd586324427f654c9109f995324427d654c9109f195324433f544c910cf151324436f524c910db149324427f650c9109f994324427d650c9109f19432442be640c910af590324433f540c910cf150324436f520c910db14832443cd320c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442ee62d0510bb58b414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510dbd4a414436c5290510bd99641443766590510bd59241443b75490510dd95241443745490510ed15241443345490510bd58a41443e75290510f914a41443b74290510ed50a41442f660905109f195414433f5450510cf151414436f5250510db14941442fb6050510be181414437465505109d19541443b76450510edd5141443765450510dd15141443b45450510bdd8941443e75250510f914941443f36050510bd18141443f060505109f994414433f5410510cf150414436f5210510db14841442f66110510ed504414427e65c8510af99321442bd64c8510cfd53214433c54c8510b798f21442dd63c8510d7d4f214435c53c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214435f5388510d714e214436f
  | 4 => 0xb54932842f7614ca10bd185328427f650ca109f994328427d650ca109f19432842be640ca10af59032843cd320ca10be98032842f9600ca10cf953418433d54d0610bb98b41842ed62d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610af99321842bd64c8610b798f21842dd63c8610db94b218436d52c8610be98321842f960c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610dbd48218436c5208610cfd53408433c54d0210cf952408433d5490210bd98640842f56190210cfd51408433c5450210cf950408433d5410210bb98840842ed6210210bd98440842f56110210dbd4b208436c52c8210db94a208436d5288210bd98620842f56188210dbd49208436c5248210af99020842bd6408210b798c20842dd6308210db948208436d5208210bd98420842f56108210bd597108437565c4210ddd53108437554c4210ddd4b108437552c4210be597108437965c42109f98b544427d62d5110edd87544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110bb98a54442ed62951109f992544423e64951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110bbd8954442ec6255110cfd91544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f988544427d62151109f984544437561151109f184544427e60151109f18054442be6515110cf994544423e6515110ed584544433f6215110cf988544433d6215110cf188544433f6115110cf58454443356115110cfd80544433d6015110cf440544433f54d4910cf153524427e64d49109f593524427e63d49109f58f524436f54d4910ebd53524432f54d4910db953524436d54d4910db15352443ac54d4910cb153524436f53d4910f3d4f524434f53d4910f9d87524436f64d4910db993524436d64d4910db193524436f63d4910db98f524436d63d4910db18f524436f61d4910db587524436f60d4910db58352442be6494910af592524433f5494910cf15252442de6394910b758e524435f5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f53549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354
  | 5 => 0x41c42f96090710dd59641c43765490710ed95241c43b55490710dd15241c42f56290710edd0a41c43b54290710bd98241c43f26090710fc58241c433f5450710cf15141c42f76550710ddd9541c43b76450710edd5141c43765450710dd15141c43b45450710bdd8941c42f46050710cf95041c433d5410710ed50441c42fa6010710be58041c42be64c8710af59321c42de63c8710b758f21c436f52c8710db14b21c436e5288710db54a21c42fa6088710be58221c43756588710bdd9221c42f56488710bdd8e21c42f56388710dd94a21c43e65288710f954a21c43745288710f990a21c43e54288710f98ca21c43e53288710bd98221c43f26088710fc58221c436f5248710db14921c42f76548710ddd9521c42f76448710bd59121c42f76348710bd58d21c43e76248710f9d4921c43765248710dd14921c43e45248710bd18121c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310ed50740c433f5490310cf15240c43b64190310cf95140c433d5450310bdd8540c42f46150310ed50540c433f5410310cf15040c42ee6210310bb58840c42f66110310bd58440c43b64110310db94b20c436d52c8310bd98720c42f561c8310f948720c436f5288310db14a20c43e62188310db94920c436d5248310bdd8520c42f46148310f948520c42be6408310af59020c42de6308310b758c20c436f5208310db14820c42f66108310bd58420c43e621083109f98b548427d62d5210dd587548437a60d5210cfd52548427e62952109f58a548433f64552109fd89548427c6255210cf55054842ee6215210bb588548433e64152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a60152109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10b798c52842dd6314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a109fd96428427e6590a109f596428427c6590a10db94a428436d5290a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a10db949428436d5250a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10b798c42842dd6310a10eb50842842fa6010a10be580428427f658ca109f996328427d658ca109f196328436e528ca10db54a328427f654ca109f995328427d654ca109f195328436e524ca10d
  | 6 => 0x35e534c020d754d3008376514c020dd545300827e650c0209f594300827c650c020cf950300833d540c020bb98830082ed620c020dd9443008375510c020cf953200833d54c8020d794f200835d53c8020dd947200837551c8020dbd5320083ae54c8020db55320083ad54c8020cb553200836f53c8020f394f200836d53c8020f354f200834d53c8020bb98720083e651c8020db54720083e551c8020d9547200833e5488020cf552200835e5388020d754e20082ed6288020db94a20083765188020dd54620083ba5488020ee55220083da5388020f654e20082f96288020de94a20083ea5288020fc94620083f15188020fa88620083e821880209fd95200833e5448020cf551200835e5348020d754d20083765148020dd54520082ef6548020dbd95200826f6548020dbd5120083ae5448020db55120083ad5448020cb551200836f5348020f394d200836d5348020f354d200834d5348020bb18520083e65148020db54520083e55148020d954520082ef6048020db94120082fb6548020ded95200827b6548020ee95120083b95448020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fc94520083f151480209f98b54c427d62d5310dd98754c437960d5310cfd5254c42ee6295310bb58a54c427e6295310db98a54c426e62953109f58a54c436d62953109b58a54c43766195310cfd9154c427f62553109f18954c433d5415310cf99054c427e62153109f58854c43766115310de58054c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c42be6494b10af59252c42de6394b10b758e52c436f5294b109f99252c433e6494b108f99252c427d6494b10cf59252c423d6494b109f98e52c435e6394b109798e52c427d6394b10d758e52c425d6394b10dd98652c427f6454b109f19152c427f6354b109f18d52c436f6254b10db54852c427e6414b109f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cfd5342c433c54d0b10bd98742c42f561d0b109fd9642c427e6590b109f59642c427c6590b10dbd4a42c436c5290b10bd98642c42f56190b109fd9542c427e6550b109f59542c427c6550b10cfd5142c433c5450b10dbd4942c436c5250b109fd9442c427e6510b109f59442c427c6510b10b798c42c42dd6310b10eb50842c42f66110b10bd58442c427f658cb109f99632c427d658cb109f19632c436f528cb10db14a32c42f6618cb10bd58632c427f654cb109f99532c427d654cb109f19532c436f524cb10db14932c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c43cd320cb10bd98432c42f5610cb10cfd5341c433c54d0710bb98b41c42ed62d0710cf95241c433d5490710be982
  | 7 => 0x3d0420d794f410835d53d0420bb98b41082ed62d0420dd947410837551d04209fd96410827e65904209f596410833e5490420cf552410835e5390420d754e41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420d794d410835d5350420bbd8941082ec6250420dd945410837551504209fd94410827e65104209f594410833e5410420cf550410835e5310420d754c41083765110420dd544410827f65cc4209f997310827d65cc420af99331082bd64cc420cf953310833d54cc420d794f310835d53cc420bb98b31082ed62cc420dd947310837551cc4209fd96310827e658c4209f596310833e548c420cf552310835e538c420d754e3108376518c420dd546310827f654c4209f595310827c654c420cf951310833d544c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c4209fd94310827e650c4209f594310833e540c420cf550310835e530c420d754c3108376510c420dd54431082be64c8420af593210833e54c8420cf55321082de63c8420b758f210835e53c8420d754f210836e52c8420dd947210837551c8420be98321082f960c84209f596210833e5488420cf552210835e5388420d754e21083755188420bb596210836d65884209b596210836f5488420eb952210836d5488420eb552210832d5488420dbd4e21083ce5388420db54e21083cd5388420d354e21082ee6188420f9946210836d5188420f954621083655188420bb582210827f6548420cf951210833d5448420d794d210835d5348420db94921083765148420cf950210833d5408420d794c210835d5308420dd94421083755108420be98021082f96008420dbd5021083ae5408420db55021083ad5408420cb550210836f5308420f394c210836d5308420f354c210834d5308420bb98421083e66108420f9944210836d5108420f954421083655108420fa98021082ed6008420fa580210827e64940209f592500827e63940209f58e500836e2194020db086500827d65d0020cf953400833d54d0020d794f400835d53d0020dd947400837551d00209fd96400827d6590020cf952400833d5490020d794e400835d5390020bb98a40082ed6290020dd946400837551900209fd95400833e5450020cf551400835e5350020d754d40083765150020dd545400827f65100209f994400827d65100209f194400833e5410020cf55040082de6310020b758c400835e5310020d754c40082ee6210020bb58840082f66110020bd58440083765110020dd544400827d65cc020cf953300833d54cc020d794f300835d53cc020dd947300837551cc0209fd96300827d658c020cf952300833d548c020d794e300835d538c020bb98a30082ed628c020dd9463008375518c0209fd95300833e544c020cf5513008
  | 8 => 0x209f596430827c6590c20cf952430833d5490c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c209fd94430827e6510c209f594430827c6510c20cf950430833d5410c20d794c430835d5310c20e750c43082ee6210c20bb588430827e64948209f592520827d63948209f597420833e54d0820cf553420835e53d0820d754f420827f65908209f596420833e5490820cf552420835e5390820d754e420836e5290820be98242082f960908209fd95420833e5450820cf551420835e5350820d754d420836e52508209fd94420827d6510820cf950420833d5410820b798c42082dd6310820d794c420835d5310820eb50842082fa6010820be580420827d65cc820cf953320833d54cc820d794f320835d53cc8209fd96320827d658c820cf952320833d548c820d794e320835d538c820db94a32082fa608c820be582320827f654c820cf951320833d544c820d794d320835d534c820db949320827f650c8209f59432082be640c820af590320833e540c820cf550320835e530c820d754c32083cd320c820be98032082f9600c820af99351082bd64d4420cf953510833d54d4420b798f51082dd63d4420d794f510835d53d4420cf952510833d5494420d794e510835d5394420ddd46510827e64944209f592510827e63944209f58e51083775494420dd95251083b65494420cd95251083755494420ed55251083355494420dd15251083775394420dd94e51083d65394420d594e51083755394420f554e51083555394420dd14e51083e46294420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083773294420dd8ca51083753294420dd0ca51083766094420dd182510833e5454420cf551510835e5354420d754d510827f64544209f191510827f63544209f18d51083776554420ddd5151083765454420ed95151083365454420dd55151083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083745354420f918951083776454420dd99151083756454420dd19151083776354420dd98d51083756354420dd18d51083774354420dd90d51083754354420dd10d51083766254420ddd0951083764254420dd50951083744254420ddcc951083763254420dd4c951083743254420dd98151083746054420dd08151082be6414420af590510833e5414420cf55051082de6314420b758c510835e5314420d754c51082f66114420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420b798f41082dd6
  | 9 => 0x18930483cd324c120fa90b20483e942c8120fa8cb20483e932c8120fac8720483e921c8120bbd9220482ed6488120bbd8e20482ed6388120bb586204836c5188120fad4220482de63d5020b758f54082f661d5020bd587540827e63d5020d798f540825e63d50209f58f540835d63d50209758f540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540823d6595020cfd8e540833e6395020cf58e540833c6395020cf98a540833c6295020cfd86540833e6195020cf586540833c6195020cf982540833c6095020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833f6555020cfd8d540833e6355020cf58d540833c6355020cf989540833c6255020cfd85540833e6155020cf585540833c6155020cf981540833c6055020cf08154082be6415020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540823e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209b988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de98054082be64d4c20af593530833e54d4c20cf55353082f661d4c20bd587530827e64d4c20cf993530823e64d4c209f593530833d64d4c208f593530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c20de983530827d6594c20cf952530833d5494c20d7d4e530827e6494c209f592530827e6194c209f586530825d6594c20d7d52530835e5494c20e7952530831e5494c20d7552530839d5494c20c7552530835c5494c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7982530835c6094c20cf951530833d5454c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f185530835f6554c20d7d51530835e5454c20e7951530831e5454c20d7551530839d5454c20c7551530835c5454c20d7d91530835e6454c20d7591530835c6454c20d7989530835c6254c20d7d85530835e6154c20d7585530835c6154c20d7981530835c6054c20d708153082be6414c20af590530833e5414c20cf55053082de6314c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20d794f430835d53d0c209fd96430827e6590c
  | 10 => 0x24836e5450920db15142483ac5450920cb15142482ef6350920dbd4d424836d5350920ebd0d42483ad4350920bbd8542483eb6050920bb18142483e860509209f99442482de6310920b758c42482ee6210920eb508424835f53cc920d714f32482fa60cc920be583324827e658c920bb996324836e658c920bbd9232482ed648c920dbd52324836d548c920bb58e324836e538c920db14e32482ed618c920bb982324835f534c920d714d32482fb604c920be18132482ef644c920bb591324836f544c920db55132483cf634c920f3d4d324836e534c920db14d32483cc534c920d314d32483ce434c920f350d32482ef614c920fad8132482ec604c920fa181324827e650c920af99032482bd640c920bb98832483cd320c9209f993514827d64d45209f98f514827d63d4520ddd4651482bf6454520af19151482df6354520b718d514837551145209f990514827d64145209f98c514827d6314520db908514836d4214520db8c8514836d32145209f997414827d65d05209f19741482de63d0520b758f41482ee62d0520bb58b414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520bb98a41482ed6290520eb50a414827f65505209f995414827c65505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841483ad4210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f19731482be64cc520af59331482ee62cc520bb58b314837751cc520dd147314827e658c5209f596314827c658c520d7d4e314835c538c520bb98a31482ed628c520f34ca314827f654c5209f995314827c654c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb58831483cd320c520ddd443148374510c520be98031482f9600c5209f99721482be64c8520af59321482de63c8520b758f21482ee65c8520db997214826e65c8520bbd9321483ae64c8520bb59321483ad64c8520ab59321482ef63c8520f398f21482ed63c8520f358f21482cd63c8520db14721482ee60c8520bb58a21483775188520dd14621482fa6088520be58221483775148520dd14521482fb6048520be18121482ef6448520bb59121482ef6348520bb58d21483e76148520f9d45214836c5148520f914521483eb6048520bb18121483e860485209f99421482ee6208520f9484214827e65d0120cfd53404833c54d0120bb98b40482ed62d0120eb50b404827e65901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb18940483ad42501209f99440482de6310120b758c40482ee6210120bb58840482f66110120bd584404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc120f34cb304827d654c1209f19530482ef624c120bb
  | 11 => 0xbe64c8620af59321882de63c8620b758f21883765188620dd54621882fa6088620be582218836f5488620db552218836f5388620db54e21883e65188620db54621883e55188620fa98221882ed6088620fa58221883765148620dd54521882fb6048620be18121882ed6508620db594218836f5408620db550218836f5308620db54c21883e66108620db54421882ed6008620cfd53408833c54d0220cf952408833d5490220bb98a40882ed6290220cfd51408833c5450220cf950408833d5410220b798c40882dd6310220bb98840882ed6210220bd98440882f56110220bb98a30882ed628c220bb597208836d65c8220dbd53208836d54c8220dbd4f208836d53c8220bb987208836d51c8220be597208837965c82209f98f544827d63d51209f987544827d61d5120cfd52544827e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf55054482de6315120b758c544833e64151209f98c544835e63151209798c544827d6315120d758c544825d63151209f988544836d62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d20db58a534827e6194d209f58653483796094d20afd9153482bc6454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20af99053482bd6414d20d754c534827e6414d20cf990534823e6414d209f590534833d6414d208f590534835e6314d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434833e54d0d20cf553434835f53d0d20d714f43482ee62d0d20bb58b434827f6590d209f996434827d6590d209f196434833f5490d20cf152434835e5390d20bb98a43482ed6290d209fd95434827e6550d209f595434827c6550d20cf951434833d5450d20d794d434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c434839d4310d20bb98843482ed6210d209f997424833f54d0920cf15342482fa60d0920be583424827e6590920bb996424836e6590920bb592424836e5490920db15242482ed6390920dbd4e424836d5390920bb58642482ee60909209f195424833f5450920cf15142482fb6050920be181424836c65509209b19542483af6450920ebd514
  | 12 => 0x48720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c83ad42d0320cf95140c833d5450320bbd8940c82ec6250320eb50940c82de6310320b758c40c82ee6210320bb58840c82f66110320bd58440c82ee62cc320bb58b30c83cd32cc3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c63552209fd85548827c6155220cf55054882de6315220b758c54882f66115220bd584548833e64152209f98c548835e63152209798c548827d6315220d758c548825d6315220db588548827e6115220dd984548827661152209f584548837561152209d584548837a60152209f993538827d64d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e20d7d8d538827f6154e209f18553882be6414e20af590538835d5314e20bd98453882f56114e209fd97438827e65d0e209f597438827c65d0e20cf953438833d54d0e209fd96438827e6590e209f596438835e5390e20d754e438827f6550e209f995438827d6550e209f195438833e5450e20cf551438835e5350e20d754d43882ef6250e20bb189438827f6510e209f994438827d6510e20e750c43882ee6210e20bb588438833e54d0a20cf55342882fa60d0a20be583428833e5450a20cf55142882fb6050a20be18142882de6310a20b758c42883ad4210a20d794f328835d53cca20be98332882f960cca20d794d328835d534ca20bed8132882f8604ca20af99032882bd640ca20f34c8328837751946209f992518827d64946209f98e518827d6394620afd9151882bc6454620b7d8d51882dc63546209fd91518833f64546208fd91518827c6454620cf191518823c64546209fd8d518835f635462097d8d518827c6354620d718d518825c6354620af99051882bd6414620b798c51882dd6314620dd544518827f65d06209f997418827d65d0620cf953418833d54d0620b798f41882dd63d0620bb98b41882ed62d06209fd96418827e65906209f596418833f5490620cf15241883765190620dd546418827f65506209f595418827c6550620cf951418833d5450620bbd8941882ec6250620dd945418837551506209fd94418827e65106209f594418833f5410620cf15041882fa6010620be580418827f65cc6209f997318827d65cc620af99331882bd64cc620d794f318835d53cc620bb98b31882ed62cc6209fd96318827e658c6209f5963188376518c620dd546318827f654c6209f595318827c654c620d794d318835d534c620bbd8931882ec624c620dd9453188375514c6209fd94318827e650c6209f59431882fa600c620be58031882
  | 13 => 0x9f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f20cf95343c833d54d0f20bb98b43c82ed62d0f209fd9643c827e6590f209f59643c827c6590f20d794e43c835d5390f20bb98a43c82ed6290f209fd9543c827d6550f209f19543c833e5450f20cf55143c835e5350f20d754d43c827f6510f209f99443c827d6510f209f19443c839d4310f20bb98843c82ed6210f20cfd5342c833c54d0b20cf95242c833d5490b20be98242c82f96090b20db59642c836e5490b20eb95242c83ad5490b20db15242c82ed6390b20db54e42c82ed6190b20bb98242c83ea6090b20fa58242c833f5450b20cf15142c82ef6550b20dbd9542c83af6450b20ebd5142c836e5450b20db15142c83ac5450b20cb15142c82ef6350b20db54d42c83af4350b20eb50d42c82ef6150b20bb18142c833e5410b20cf55042c82de6310b20b758c42c83ad4210b20be98042c82f96010b20d794e32c835d538cb20be98232c82f9608cb20bbd9232c82ed648cb20dbd5232c836d548cb20db94e32c83ce538cb20f354e32c836c538cb20bb58632c82ee608cb20fa98232c83e9608cb20bbd9532c836f654cb20bbd9132c82ed644cb20dbd5132c836d544cb20f3d8d32c83cf534cb20db94d32c836c534cb20f314d32c834c534cb20f390d32c83cd434cb20bbd8532c82ec604cb20af99032c82bd640cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c82be64d4720af59351c82de63d4720b758f51c837751947209f99251c827d64947209f98e51c827d6394720db90a51c836d4294720db8ca51c836d32947209fd9151c827c64547209fd8d51c827c6354720dd54451c827f65d07209f99741c827d65d0720b798f41c82dd63d0720bb98b41c82ed62d07209fd9641c827e65907209f59641c833e5490720cf55241c82ee6290720bb58a41c83ad42907209fd9541c827d65507209f19541c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed6210720eb50841c827f65cc7209f99731c827d65cc720af99331c82bd64cc720bb98b31c82ed62cc7209fd9631c827e658c7209f59631c835e538c720d754e31c82ee628c720bb58a31c83cd328c7209fd9531c827d654c7209f19531c827f650c7209f99431c827d650c720d794c31c835d530c720bb98831c82ed620c720f34c831c82be64c8720af59321c82de63c8720b758f21c837651c8720dd54721c82fa60c8720be58321c82ef64c8720eb99321c82ed64c8720eb59321c82ad64c8720bbd8f21c83ce63c8720bb58f21c83cd63c8720b358f21c836e51c8720f994721c83e551c8720bb98321c83ea60c8720fa58321c82ef6548720dbd9521c82ef6448720bb59121c82ef6348720bb58d21c83e76148720f9d4521c836e5148720f914521c82ec60
  | 14 => 0x951103744254440dd8c951103753254440dd0c951103766054440dd18151103744054440bb98851102ed6214440db948511036d5214440bd98451103755114440cf95341102ee62d0440bb58b411036e52d0440db54b411037651d0440dd54741102fa60d0440be583411027d6590440db94a411036d5290440dd54641102bd6590440cf596411023d6590440eb94a411033d5290440eb54a411032d5290440af98641103b65190440cf54641103b55190440cd54641102bd60904409fd95411033e5450440db949411036d5250440dd945411036e5210440db54841103765110440dd54441102fa6010440be58041103ae5210440cf54841103ad5210440cb54841102be6110440ed98441103b65110440cf54441103b55110440cd54441103ba6010440af58041103b960104409fd97211027e65c84409f59721102be64c8440af59321102de63c8440b758f211035e53c8440d754f211036e52c8440db54b211037651c8440dd547211027f65884409f996211027d6588440d794e211035d5388440db94a211036d5288440dd946211037551884409fd95211027d65484409f19521102bf6448440af191211035e5348440d754d211036e5248440db54921103765148440dd545211027f65084409f994211027d6508440d794c211035d5308440db948211036d5208440dd94421103755108440cf906501033c4194040db94b401036d52d0040dd947401037551d0040eb94b401033d52d0040eb54b401032d52d0040af98740103b651d0040cf54740103b551d0040cd54740102bd6490040cf952401036e5290040db54a40103765190040dd54640102f96490040de95240103ba5490040fa94a40103e95290040fc94640103f15190040ee90640103b841900409fd95401036e5250040db54940103765150040dd54540102bf6550040cfd95401023f6550040eb949401033d5250040eb549401032d5250040af18540103b65150040cf54540103b55150040cd54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040fa94940103e95250040fc94540103f151500409f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c836e62953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320b798c54c82dd6315320cf99054c827e6315320d798c54c825e63153209f58c54c835d63153209758c54c836e62153209f98454c827d6115320de58054c835f5394f209f99253c827d6494f209f98653c827d6194f209fd9153c827c6454f209fd8553c827c6154f20af99053c82bd6414f20d754c53c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c836e6214f2
  | 15 => 0x502f96090540ddd4541503745150540bed8141502f86050540afd8941503b76150540edd45415033c5150540ed14541503bb6050540af18141503b860505409f99441502be6410540ed504415027e65c85409f597215027c65c8540af99321502bd64c8540b798f21502dd63c8540ddd47215037451c85409f996215027d65885409f19621502be6488540af592215036f5288540db14a21503ad42885409fd95215027e65485409f19521502be6448540af591215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540eb50821503775108540dd14421502fa6008540be58021503bb42d0140ee50b40503bb41d0140ee50740502bd6290140af586405033c5190140eed4240502de63d4840b758f52102f661d4840bd587521036f52948409f98e521027d63948409f986521027d6194840dbd4e521036e5394840f394e521034e5394840db192521036f6394840db98e521036d6394840db18e521036f6194840db986521036d6194840db186521036e6094840db182521035e53548409fd8d521027c63548409fd85521027c6154840dbd95521036f5354840db94d52103ce5354840d394d521036d5354840f354d521034d5354840db991521036f6354840db98d521036d6354840db18d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840cf953421035e53d0840d754f421036e52d0840db54b42102fa60d0840be583421027d6590840d794e421035d5390840db54a421027f6550840cf951421035e5350840d754d421036e5250840b798c42102dd6310840d794c421035d5310840db948421036d5210840eb50842102fa6010840be580421027f658c8409f996321027d658c840d794e321035d538c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321036e524c840db549321027f650c8409f994321027d650c840af99032102bd640c840db948321036d520c840f34c832102ee62d4440bb58b511036e52d4440db54b511036e5294440db54a511037751944409f98a511027d6294440ed19251103775294440dd94a51103e65294440d994a51103755294440f954a51103655294440dd14a51103746494440ddd8a51103766294440dd58a51103746294440ddd0a51103764294440dd50a51103744294440dd8ca51103753294440dd0ca51103766094440dd182511036e5254440db549511027f62544409f18951103776554440ed19151103775254440dd94951103e65254440d994951103755254440f954951103655254440dd14951103766454440ddd8951103766254440dd58951103746254440ddd0951103764254440dd5
  | 16 => 0xf5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40b798c52902dd6314a40db54852902f66114a40bd584529036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be18142902de6310a40b758c42903ad4210a409fd96329027e658ca409f596329036e528ca40db54a329027f654ca409f595329027c654ca40afd9132902bc644ca40db949329036d524ca409fd94329027e650ca409f59432902be640ca40af59032903cd320ca40ddd46519027e62946409f58a51902ef6254640bb189519027f6254640dbd89519026f62546409f189519036c62546409b18951902ee6214640bb58851903755114640bb98b41902ed62d0640dd94641903755190640be98241902f96090640cf54a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902bd6510640cf594419033d5210640ed984419033d5110640af580419027f65c86409f997219027d65c8640af99321902bd64c8640b798f21902dd63c8640db94b219036d52c86409fd96219027e65886409f59621903765188640dd546219027f65486409f595219027c6548640afd9121902bc6448640db949219036d5248640dd945219037551486409fd94219027e65086409f59421902fa6008640be58021902bd65d0240cf597409033d52d0240af987409033d51d0240be597409037965d02409f98f525027d63d49409f987525027d61d4940dbd4a52502df6354940b718d52502f76154940bd18552502de6314940b758c525036d52149409f98c525035e63149409798c525027d6314940d758c525025d63149409f984525027d61149409f99742502be65d0940cf99742502bd63d0940cfd4f425033c52d0940af58742502be60d0940af592425036f5290940db14a42502fa6090940be582425036f5250940db14942502fb6050940be18142502bf6350940cfd4d42503af6250940ebd49425033c5250940eb149425032c5250940afd8542503bb6050940af18142503b860509409f99442502be6410940b798c42502dd6310940eb508425027e658c9409f596325027c658c940af99232502bd648c940d7d4e325035c538c940eb50a325027f654c9409f995325027c654c940af99132502bd644c940eb509325027e650c9409f594325027c650c940af99032502bd640c940dbd48325036c520c940f34c8325027e62d45409f58b51503775194540bbd8951502ec6254540dd544515027e62145409f588515033f4214540cf508515027e65d0540bb98b41502ed62d0540af997415033e65d05408f99741503ae62d0540af58b41503ad62d0540ab58b415033c51d0540af98341502bd6490540ddd4641503745190540be98241
  | 17 => 0xc421d794e310875d538c421bb98a31086ed628c421f34ca310867f654c4219f994310867d650c4219f19431086ee620c421bb58831087cd320c421af99321086bd64c8421b798f21086dd63c8421bbd9321087ae64c8421bb59321087ad64c8421ab59321086ef63c8421f398f21086ed63c8421f358f21086cd63c8421bb98321086ed6288421db94a21086f56288421dd94a21087e65288421f990a21087e54288421f98ca21087e532884219fd9521086ef6548421dbd95210866f6548421bbd9121086ed6448421bbd8d21086ed6348421bbd85210876e5148421f9d0521087e44148421f9cc521087e43148421bb18121086f76548421ddd9521086776548421bdd8921087e76248421dd94921087e65248421f9d0921087e44248421f9cc921087e43248421ded42500867e64940219f592500867e63940219f58e500867f64540219f191500867f63540219f18d500876e4254021db509500876e3254021db4c9500876f2154021dd885500876d2154021dd48550086be6414021af59050086de6314021b758c50087795014021dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d02de6314b40b758c52d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40af58f42d033d53d0b40cf94b42d03ae52d0b40eb54b42d02bd61d0b40af98342d03ba60d0b40ee58342d02bf6550b40cfd9542d02bf6350b40cf54d42d03af6250b40ebd4942d033e5250b40eb14942d02bf6150b40af18142d02de6310b40b758c42d036e5210b40db54842d03ad4210b40be98042d02f96010b409fd9632d027e658cb409f59632d02be648cb40af59232d036e528cb40db54a32d03ad428cb409fd9532d027d654cb409f19532d02be644cb40af59132d036e524cb40db54932d03ad424cb409fd9432d027e650cb409f59432d02be640cb40af59032d03cd320cb40bb98b51d02ed62d4740ddd4651d027e62947409f58a51d033f4294740cf50a51d027f62547409f18951d03755114740bb98b41d02ed62d0740dd94741d037551d0740be98341d02f960d0740eb98b41d02bd62d0740eb58b41d02ad62d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740afd9541d033f6550740afd8941d03b76150740edd4541d033e5150740ed14541d02bc6050740dd94441d03755110740ed50441d02fa6010740be58041d027f65c87409f99721d027d65c8740af99321d02bd64c8740b798f21d02dd63c87409fd9621d027e65887409f59621d02be6488740af59221d036e5288740db54a21d03ad42887409fd9521d027d65487409f19521d02be6448740af59121d027f65087409f99421d027d6508740af99021d02bd6408740db94821d036d5208740eb50821d036
  | 18 => 0xdb98a530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf55343086ee62d0c21bb58b43086f661d0c21bd587430867f6590c219f996430867d6590c219f196430875e5390c21d754e43086ee6290c21bb58a43086f66190c21bd586430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d430867f6510c219f994430867d6510c219f194430879d4310c21bb98843086ed6210c219f992520873e64948218f992520867d6494821cf592520863d6494821d798e520867d6394821d758e520865d63948219f597420873f54d0821cf153420867f65908219f596420873e5490821cf55242086f66190821bd586420876d65908219b59642086ed6490821db95242087ae5490821eb552420876c5490821bb58e420876f5390821db54e42087e66190821bb58642087e56190821b958642086ee60908219fd95420873f5450821cf15142086ef6550821dbd9542087af6450821ebd51420876e5450821db15142087ac5450821cb15142086ef6350821dbd4d420876d5350821ebd0d42087ad4350821bbd8542086ec60508219fd94420867d6510821cf950420873d5410821b798c42086dd6310821bb98842087ad4210821bd98442086f561108219f597320875f53cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c821db596320866d658c821bbd9232086ed648c821dbd52320876d548c821bb58e320876e538c821f394e32087cd538c821db14e32087e6618c821bb58632087e5618c821b958632086ee608c8219fd95320875f534c821bbd95320876f654c821bbd9132086ed644c821dbd51320876d544c821f3d8d32087cf534c821db94d320876c534c821f314d320874c534c821f390d32087cd434c821bbd8532086ec604c8219fd94320867d650c821af99032086bd640c821d794c320875d530c821bb98832087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d6394421db90a510876d4294421db8ca510876d32944219f59741086de63d0421b758f41086ee62d0421bb58b410867f65904219f596410873e5490421cf55241086ee6290421bb58a41087ad42904219fd95410867f65104219f994410867d65104219f194410873e5410421cf55041086ee6210421bb58841087ad4210421ed504410867d65cc421af99331086bd64cc421bb98b31086ed62cc4219fd96310867d658
  | 19 => 0x3534867e60d4d219f58353486be6494d21af592534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d21db58a53487756194d219f982534867d6094d219fd91534867c6454d21dbd89534867f6154d21ddd85534867f6054d219f181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21cfd53434873c54d0d219fd96434867e6590d219f596434867c6590d21d7d4e434875c5390d219fd95434867e6550d219f595434867c6550d21cfd51434873c5450d21d7d4d434875c5350d21bbd8943486ec6250d21bdd8543486f46150d219fd94434867e6510d219f594434867c6510d21e750c43486ee6210d21bb588434867e65d0921cfd53424873c54d0921bd98742486f561d09219f996424867c6550921cfd51424873c5450921bdd8542486f461509219f99442486de6310921b758c42487ad4210921d7d4f324875c53cc921bd98732486f561cc9219f996324875f534c921d714d32486f7614c921bd185324867e650c921af99032486bd640c921f34c8324867e65d0521cfd53414873c54d0521b798f41486dd63d0521bb98b41486ed62d05219f996414873e5490521cf552414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f994414873e5410521cf550414867e65cc521af99331486bd64cc521d7d4f314875c53cc521bb98b31486ed62cc521d794e314867d654c5219f19531486ef624c521bb18931486be64c8521af59321486de63c8521b758f21487b664c8521ed59321487d663c8521f558f21486f560c8521dbd52214876d5488521dbd4e214876d5388521f9d4621486ed60885219f993504867d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d50486be6414121af59050486de6314121b758c504877950141219f990504873e64141218f990504867d6414121cf590504863d64141219f98c504875e63141219798c504867d6314121d758c504865d6314121db884504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540876e62950219f982540867d6095021cfd91540867f63550219f18d540867f60550219f181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219f984540877661150219f980540877a60150219e980540867d6015021de580540867960150219f993530867d64d4c21db98b530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c21
  | 20 => 0x867d6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875d5314e219fd97438867e65d0e219f597438867c65d0e21cfd53438873c54d0e21d794f438875d53d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438873e5490e21cf55243886ee6290e21bb58a438867f6550e219f995438867d6550e219f195438873f5450e21cf15143886f76150e21bd185438867f6510e219f994438867d6510e21cf950438873d5410e21d794c438875d5310e21e750c43886ee6210e21bb588438873e54d0a21cf55342886f661d0a21bd58742886ed6590a21db596428876e5490a21db15242886ed6390a21dbd4e428876d5390a21bb58642886ee6090a21cf951428873d5450a21bdd8542886f46150a21dbd9542887af6450a21db95142887ae5450a21cb95142887ad5450a21db15142886ef6350a21dbd4d428876d5350a21ebd0d42887ad4350a21bbd8542887e76150a21f918542886ec6050a21b798c42886dd6310a21eb508428875e53cca21d754f32886f661cca21bd58732886ed658ca21db59632886ef648ca21bb592328876f548ca21db552328876e538ca21bb58632886ee608ca21d794d328875d534ca21bdd8532886f4614ca21dbd9532886ef644ca21bb591328876f544ca21db55132887cf634ca21db94d32887ce534ca21d394d32887cd534ca21f390d32887cd434ca21bbd8532887e7614ca21f918532886ec604ca21af99032886bd640ca21f34c832886de63d0621b758f41886ee62d0621bb58b418873e5490621cf55241886ee6290621bb58a41887ad4290621cf950418873d5410621bb98841886ed6210621eb50841886be64cc621af59331886ee62cc621bb58b31886ee628c621bb58a31887cd328c621af99321886bd64c8621b798f21886dd63c8621bb597218876d65c8621bbd9321887ae64c8621bb59321887ad64c8621ab59321887ce63c8621bb58f21887cd63c8621b358f21886ee60c8621bd597218877565c8621ed99321887b564c8621f598f21887d563c8621bd583218877b50942219f992508867d64942219f98e508867d63942219fd91508867c64542219fd8d508867c6354221db909508876d4254221db8c9508876d3254221dbc8550886be6414221af59050886de6314221b758c508877950142219f98f544867d63d51219f983544867d60d5121cfd5254486de6395121b758e544867e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f58a544876d62951219b58a544867d6195121dd586544867e60951219f582544873f64551219fd8d544867c63551219fd89544876f62551219fd85544877761551219fd81544867c60551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f59
  | 21 => 0x5414f21cf55053c875d5314f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c873e54d0f21cf55343c875e53d0f21d754f43c86f661d0f21bd58743c867f6590f219f99643c867d6590f219f19643c873e5490f21cf55243c875e5390f21d754e43c86f66190f21bd58643c867f6550f219f59543c867c6550f21cf95143c873d5450f21d794d43c875d5350f21bbd8943c86ec6250f219fd9443c867e6510f219f59443c867c6510f21cf95043c873d5410f21d794c43c875d5310f21e750c43c86ee6210f21bb58843c873e54d0b21cf55342c875e53d0b21d754f42c873e5490b21cf55242c875e5390b21d754e42c86f66190b21bd58642c873e5450b21cf55142c875e5350b21d754d42c873e5410b21cf55042c86de6310b21b758c42c875e5310b21d754c42c87ad4210b21bd98442c86f56110b21cf95332c873d54ccb21d754f32c873e548cb21cf55232c875e538cb21d754e32c86f6618cb21bd58632c873e544cb21cf55132c875e534cb21af99032c86bd640cb21cf95032c873d540cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86de63d0721b758f41c875e53d0721d754f41c86ee62d0721bb58b41c873e5490721cf55241c875e5390721d754e41c873e5450721cf55141c875e5350721d754d41c86ef6250721bb18941c873e5410721cf55041c875e5310721d754c41c87b54110721cf95331c873d54cc721bb98b31c86ed62cc721af99350c86bd64d4321cf95350c873d54d4321b798f50c86dd63d4321d794f50c875d53d4321cf95250c873d5494321d794e50c875d5394321ded4250c867e64943219f59250c867e63943219f58e50c873e5454321cf55150c875e5354321d754d50c867f64543219f19150c867f63543219f18d50c86be6414321af59050c873e5414321cf55050c86de6314321b758c50c875e5314321d754c50c87795014321b798f54886dd63d52219f98f548875e63d52219798f548867d63d5221d758f548865d63d5221db58b548877661d52219f983548867d60d5221cfd5254886de6395221b758e548867e6395221d798e548865e63952219f58e548875d63952219758e548876d62952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221cf990548867e63152219f58c548876d6215221dd984548867e60152219f58054886be64d4e21af593538867e64d4e21cf993538863e64d4e219f593538873d64d4e218f593538877661d4e219f983538867d60d4e21af99253886bd6494e21d7d4e538867e6494e21cf992538863e6494e219f592538873d6494e218f592538876d6294e219f982538
  | 22 => 0x841af58742107b561d0841ad58742106be60d08419f59642106bd64908419fd9542106bf6550841cfd9542106bf6350841cf54d42107af6250841ebd49421073e5250841eb14942106bf6150841af18142106be6410841b798c42106dd6310841db948421076d5210841eb50842106f66110841bd584421067f658c8419f996321067d658c841af99232106bd648c841db94a321076d528c841eb50a32106f6618c841bd586321067f654c8419f595321067c654c841af99132106bd644c841db949321076d524c841eb509321067f650c8419f994321067d650c841af99032106bd640c841f34c8321073f4294441cf50a51106ee62d0441bb58b41107ae62d0441af58b41107ad62d0441ab58b41106be60d0441af592411073e5490441bd59241107765490441ed95241107b74290441ed50a411067f6550441afd95411073f65504418fd9541106bf6250441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441ed90941107b44250441ded42501067e62940419f58a501067f62540419f189501073f4254041cf509501073f4154041dd905501073d4154041dd50550106ee6214041bb58850107795014041b798f54c86dd63d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f6395321cf98e54c873d6395321cf18e54c873e6295321cf18a54c873f6195321cf58654c873f6095321cf98254c873d6095321cf18254c873f64553219fd8d54c867c63553219fd8154c867c6055321cfd9554c873f6355321cf98d54c873d6355321cf18d54c873e6255321cf18954c873f6155321cf58554c873f6055321cf98154c873d6055321cf18154c873d5415321b798c54c86dd6315321cf99054c867e6315321d798c54c865e63153219f58c54c875d63153219758c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c873e54d4f21cf55353c873e5494f21cf55253c875f5394f219f99253c867d6494f219f98253c867d6094f21d7d5253c875e5494f21e795253c871e5494f21d755253c879d5494f21c755253c875c5494f21d7d9253c875e6494f21d759253c875c6494f21d718a53c875f6194f21d758653c875f6094f21d798253c875d6094f21d718253c873e5454f21cf55153c867f6454f219f19153c867f6054f219f18153c875f6554f21d7d5153c875e5454f21e795153c871e5454f21d755153c879d5454f21c755153c875c5454f21d7d9153c875e6454f21d759153c875c6454f21d798953c875f6154f21d758553c875f6054f21d798153c875d6054f21d718153c86be6414f21af59053c873e
  | 23 => 0xfd9432d067e650cb419f59432d06be640cb41af59032d076e520cb41db54832d07cd320cb41bb98b50d06ed62d4341db94b50d076d52d4341db94a50d076d5294341ded4250d067e62943419f58a50d076e5254341db54950d067f62543419f18950d06ee6214341bb58850d076e5214341db54850d07795014341b798f52906dd63d4a41b798e52906dd6394a41dbd4a529067e6394a41d798e529065e6394a419f58e529075d6394a419758e529067e6094a419f582529067f6354a419f18d529067f6054a419f181529076d5214a41af597429073d65d0a41af58f429073d53d0a41cf94b42906bd61d0a41af983429076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd18542906bf6350a41cf54d42907af6250a41cf94942907ae5250a41cb94942907ad5250a41afd8542907b76150a41ed18542906bc6050a41b798c42906dd6310a41eb508429067f658ca419f996329067d658ca41af99232906bd648ca41d794e329075d538ca41eb50a329067f654ca419f595329067c654ca41af99132906bd644ca41eb50932906f7614ca41bd185329067f650ca419f994329067d650ca41af99032906bd640ca41db948329076d520ca41f34c832906ee62d0641bb58b41906bd65d0641cf59741907ae62d0641af58b41907ad62d0641ab58b41906be60d0641bd597419077565d0641f998b41907e562d0641bd583419077b50942419f98a509067d62942419fd89509067c6254241cfd09509073d4254241cfd0550906ee6214241bb588509077950142419f98f525067d63d49419f983525067d60d4941b798e52506dd6394941dbd4a525076d52149419f98c525067d63149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e6510941b798c42506dd6310941eb508425067e658c9419f596325067c658c941dbd4a325076c528c9419fd95325067e654c9419f19532506bf644c941af191325076f524c941db14932506f7614c941bd185325067e650c9419f594325067c650c941af99032506bd640c941f34c832506ee62d0541bb58b41507e662d0541f958b41506f560d0541cfd4a41507b75190541af582415067e62d41419f58b505077b5094141bbd8950506ec6254141bb98850506ed6214141de540505067e6214141db988505066e62141419f588505076d62141419b588505073e4114141db98a541076d6295041dbd4a521067e63948419f58e521067e60948419f582521067f63548419f18d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841db94b421076d52d0841bd98742106f561d0841af58f421073d53d0841cf94b42107ae52d0841eb54b42107b661d0
  | 24 => 0x420cb3e5450832cf551420cb6e52508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832eb508420cb3e548c832cf552320cb6f548c832eb952320cb6d548c832eb552320cb2d548c832bb58e320cacd638c832db94e320cbce538c8329fd95320cb3e544c832cf551320caef654c832dbd95320ca6f654c832dbd51320cbae544c832db551320cbad544c832cb551320caef634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832f3d95320cacf654c832d3d95320cbcf644c832f3991320cbcd644c832f3191320cbcf544c832d3d51320cbce544c832e3951320cbcd544c832d3551320cb8d544c832c3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832af993510cabd64d4432cf953510cb3d54d4432f34cb510cb3e5494432cf552510cbcd3294432ddd46510ca7e64944329f592510cb6e3294432db4ca510cb4d32944329f982510ca7d6094432cf951510cb3d5454432f34c9510ca7f64544329f191510ca7f60544329f181510cabe6414432af590510cb3e5414432cf550510cbcd3214432dd544510cafa6014432be580510cabe64d4032af593500cb3e54d4032cf553500cbcd32d4032cf952500cb3d5494032f34ca500cb7b50940329f992500ca7d64940329f986500ca7d6194032cf951500cb3d5454032f34c9500ca7f64540329f191500cb6e3254032db4c9500cb4d32540329fd85500ca7c6154032af990500cabd6414032cf950500cb3d5414032f34c8500caf66114032bd584500cb795014032b798f52d06dd63d4b41dbd4a52d067e6394b419f58e52d067e6094b419f58252d076f5394b41db94e52d07ce5394b41d394e52d076c6494b41dbd8e52d076e6394b41db58e52d076c6394b41dbd8652d076d6194b41dbd8252d076e6094b41db58252d076c6094b41d794d52d067f6354b419f18d52d067f6054b419f18152d076f6554b41dbd4d52d076e5354b41f394d52d074e5354b41db54d52d07cd5354b41d354d52d076e6454b41dbd8d52d076e6354b41db58d52d076c6354b41dbd8552d076d6154b41dbd8152d076e6054b41db58152d076c6054b41b798c52d06dd6314b41d794c52d075d5314b41db54852d075e53d0b41d754f42d076e52d0b41db54b42d06f661d0b41bd58742d075e5390b41d754e42d076d5290b41d794d42d075d5350b41db94942d06de6310b41b758c42d075e5310b41d754c42d076e5210b41db54842d07ad4210b41bd98442d06f56110b419fd9632d067e658cb419f59632d075e538cb41d754e32d076e528cb41db54a32d06f6618cb41bd58632d067f654cb419f59532d067c654cb41afd9132d06bc644cb41db94932d076d524cb419
  | 25 => 0xa7d64942329f986508ca7d61942329fd91508ca7c6454232db909508cb6d4254232d7cc9508ca7f61542329f185508cabe6414232af590508caf66114232bd584508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544caf66195132bd586544ca7e64951329f58a544cb6d62951329f986544cb7661951329d986544ca7d6195132dd586544ca7561951329f982544ca7d6095132cfd91544ca7f6255132dbd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e6415132db588544ca7e61151329f584544ca7e60151329f580544ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f996424caee6590932db996424caed6490932db952424cb6c5490932f3d8e424caee6390932f318e424cbce4390932bb986424caed60909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424cb6c65509329b195424cbaf6450932ebd51424cb6e5450932db151424cbac5450932cb151424cbcf6350932bb18d424cbcc6350932b318d424cbaf4350932f390d424cbad4350932f350d424cb8d4350932bb185424caef60509329f994424cade6310932b758c424caee6210932eb508424cadf648c932b7592324cbcf528c932f390a324cbcd428c932b7986324cadd608c932af993514cabd64d45329f993514cb3e64d45328f993514ca7d64d4532cf593514ca3d64d45329f983514ca7d60d4532af992514cabd6494532ddd46514cb7551145329f990514ca7d6414532db908514cb6d42145329f980514ca7d60145329f993504ca7d64d4132db90b504cb6d42d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cabe6414132af590504caf66114132bd584504cb7950141329f990504cb3e64141328f990504ca7d6414132cf590504ca3d64141329f984504cb7661141329d984504ca7d6114132dd584504ca7561141329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d60950328f596540cb3e6295032cf18a540cb3f6195032cf986540cb3d6195032cf186540cb3f6095032cf982540cb3d6095032cf182540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cfd95540cb3e6255032cf189540cb3c3255032cfd85540cb3e6155032cf585540cb3c6155032cfd81540cb3e6055032cf581540cb3c6055032af990540cb3d54150329f990540cb3e64150328f990540ca7e6215032db988540ca6e62150329f984540ca7d61150329f980540ca7d60150329f992520ca7d64948329f597420cb3e54d0832cf553420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420cb6e52908329fd95
  | 26 => 0x3908429fd954210b5e5350842d754d4210abf6550842cfd954210a3f6550842e794d4210b3d5350842e754d4210b1d5350842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bce5350842db54d4210bcd5350842d354d4210baf4350842eb90d4210bad4350842eb10d4210baf6550842abd954210b2f6550842ebd8d4210bae6350842eb58d4210bac6350842ebd4d4210bae5350842e394d4210bad5350842cb54d4210b8d5350842c354d4210bac5350842ebd854210bae6150842eb5854210bac6150842ebd814210bae6050842eb5814210bac6050842b798f5110add63d4442d794f5110b5d53d4442eb50b5110b5e5394442d754e5110bad4294442ddd465110a7e63944429f58e5110b3f4294442db90a5110b3d4294442db50a5110b2d42944429f9825110a7d6094442d794d5110b5d5354442eb5095110a7f63544429f18d5110a7f60544429f1815110ade6314442b758c5110b5e5314442d754c5110bad4214442dd5445110afa6014442be5805110ade63d4042b758f5010b5e53d4042d754f5010bad42d4042d794e5010b5d5394042eb50a5010b7b50940429f98e5010a7d63940429f9865010a7d6194042d794d5010b5d5354042eb5095010a7f63540429f18d5010b3f4254042db9095010b3d4254042db5095010b2d42540429fd855010a7c6154042b798c5010add6314042d794c5010b5d5314042eb5085010af66114042bd5845010b795014042bd987548caf561d5232d758f548cb6e62d52329f987548cb7661d52329d987548ca7d61d5232dd587548ca7561d52329f983548ca7d60d5232cfd52548cb6e62952329f986548ca7d61952329f982548ca7d6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5450e32cf551438caef6250e32bb189438cb9d4310e32bb588438cb3f54d0a32cf153428cb3e5490a32cf552428cade6390a32b758e428caed6590a32db596428cb6e5490a32eb952428cbad5490a32db152428caee6390a32f398e428cbcd6390a32bb986428caed6090a32cfd51428cb3c5450a32bbd95428cb6f6550a32ebd91428cbaf5450a32db951428cb6c5450a32eb151428cb2c5450a32bb18d428cbaf4350a32eb50d428caec6150a32bbd81428cb3e5410a32cf550428cade6310a32b758c428cbad4210a32bb597328cb6d65cca32bbd93328caed64cca32af993518cabd64d4632ddd46518ca7e64946329f592518cb6e4294632db50a518cb5f32946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632dd544518cb7b50942329f992508c
  | 27 => 0x429f58e50d0a7e61943429f58650d0a7f63543429f18d50d0b3f43543429fd8550d0a7c6154342b798c50d0add6314342bd98450d0af56114342de54050d0af661d4e42bd5875390b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390aee6290e42bb58a4390abd65d0a42cf5974290b3d53d0a42bb5974290b6d65d0a42bb58f4290aee61d0a42bb5834290ade63d4642b758f5190b7751946429f98e5190a7d6394642cfd0a5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642ded425090a7e63942429f58e5090a7e61942429f5865090a7f63542429f18d5090b3f42542429fd855090a7c6154242b798c5090add6314242bd9845090af56114242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bd9865350af56194d42d754c5350a7e6114d429f5845350a7e6014d429f5805350abe65d0d42cf9974350b3c53d0d42ebd8b4350abe62d0d42eb18b4350abe61d0d42af5834350abd6490d42d7d4e4350b5c5390d42bb98a4350aed6290d42bbd894350aec6250d42ebd894350abc6250d42eb1894350aac6250d42bb58f4250baf43d0942eb50f4250aee61d0942bb5834250abd6390942ebd4a4250abe6190942af5824250ade63d4542b758f5150a7e63d4542d798f5150a5e63d45429f58f5150b5d63d45429758f5150a7e60d45429f5835150ade6394542b758e5150b775194542dd5445150a7e63145429f58c5150b3f4314542cf50c5150a7e60145429f5805150a7e63d41429f58f5050b3f43d4142cf50f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142b798c5050add6314142bd9845050af56114142de5405050a7e6314142d798c5050a5e63141429f58c5050b5d63141429758c5050a7e6114142dd9845050a7661141429f5845050b7561141429d5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c42d71925310b5e6294c42d718a5310b5f6194c42d79865310b5d6194c42d71865310b5f6094c42d79825310b5d6094c42d71825310a7f6154c429f1855310a7f6054c429f1815310b5f6554c42d79915310b5e6254c42d71895310b5c4254c42d7d855310b5e6154c42d75855310b5c6154c42d7d815310b5e6054c42d75815310b5c6054c42b798c5310b5d5314c42cf9534310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c42d754e4310a7f6550c42cf9514310b5e5350c42bb9884310aed6210c42d794f4210b5d53d0842e794f4210b3d53d0842e754f4210b1d53d0842af5924210b3e5490842d794e4210b5d5390842bb5924210aad6490842db9524210bae5490842f394e4210b6d5390842f354e4210b4d5
  | 28 => 0x20004001000800200000030000001000c0010000001001c0030004002000000000080010004000000000200000010008001000c0050018000000800200080070000004000400300000020000003000800100040000004000000c002000000000000020000000000c00a00000030000000000400400040000000000001c00000080000000003000c0050008000000000900240000000000001000000100020010006001800000080020000002000000100080010004005000c00000080020000000001000000000000004002000000000000010004000000c000001000000080000000002000800c0000000000400000000010004000000000200000000004001000400000080020000002000000a0004004000000700040000000000000c0000024002000c0000008004000400300080000000000000400400040010000003000000000080040000006000400100000000008000000000200080000008000000c0040000002001c00200080010000000000000100000040004001000400000000000000001000000700040010004000000000100000040000002000000100080000000000000000000000010008003006c00100140000010000000800000000080004001000000100000040000007000000000100010000003000000000000010008002000400100040020018000000400800000020000002001000400080000004003000c000000400200080040000001000c0010018001000800000040030014000000000c0014004001000000040010000001000000100000080008001000c000000800c0018001000000000080000000005000c00000000020000003000c0010000001000000100040020000000000000000040000000000000000100000010000001000c0020000002000c0000000000000000300000000010000000000300000000000000000c000000000200140000014001000c00200000060004002000000200000000000004000400000000000000002000000000140050004000000c0000008007000800000100020034000000c00b000400100040010008000002800000000000004001000c000001000100000010000000001c0010010000000000700000050000001000000200000040004000000000400100020004002002c000000400000000020000006000c0000008000000000000080000000000000000000080000014000bd98753d0af561d4f42d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42bb98b43d0aed62d0f42af98b43d0bae62d0f42eb58b43d0ade63d4742b758f51d0b7751947429f98e51d0a7d6394742cfd0e51d0a7e60947429f58251d0a7f63547429f18d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943
  | 29 => 0x20000004000000000000020000000000000000000060000000000c002001c001000000000000030004002000000000000040000000000400100080000008001000400100000000004005000000000100020014000000800100000000000002000000000080000000000002c0000000002000000300100000004000000400400100000004001000400000000000004000000800100040020000000000000f00000000010000000000000000000004001001000200100000000001000000000040000014000000000400040020000001000000000040000004000000800200080010008002000000100080000000009000000100000000000005000400200000000008000000800000000020018000000000000000000000000001000000000050008000000800000080000014008000000500040000000000000c00000040010000003000000100000010000001000c0020008000000800000000030000000001800100000000000000000c002000000000000000018002000000b0004006000000600040010000001001c00000000080000005000400200000000004000001400500040050010000000000300000030000002001000600000000000000000c0030010001000c00300000050000000002c002000c00000080020004000000000000040000000002000800300000030000001000c0000000000000400100040030000000000c0020004000000c008000000000080010004001000c00000040000000000001c000000c00100000020014002000000000000000000011002000000000040018001000800100080040000001002c002000000000040020000000000000200000010000001000c00800040000000002000000100040010024000000000000040000000000000000100000020004000000000000080040000002000c00000000000008000000000100000000008001000400600000060004000000000700000000000001000c0020000000000000100000010000000000c0010000000000400000000000008003000000200000040000000000c0010000000000c004001c00000000040000000000400000000050000000002400000040020010001000c001000000100000050000000000800200000000010002000000200040050004001000400000040000000002000000000000030008000000800000000000000001000000000100010004001000000100080040010000001400200180000008001000800000080000000005000000000000020004001002400200080000018001001800000000010004001000c003000000100000020000000000000300000040010001000000c00000000004000001c000000400100000000004001001000000040000000001000000200000010024000000000000000000000
  | 30 => 0x400a0000000001c0060000005000800000000050004001000000400000000004000000000200000050004006000c001003000000080020000000000000200000110008006000000000000000018000000000100080030000000000400a0000001000c00100000030008007000000000080000000004000c001001000000000000008001000c0010000005001400000080080004005000800100000030008001000000100080010008001000000100000000000000000000b000000000040010008001000c0000000003000400100040010000001001000100040030008003000000100140000004000000000000000060000004000400000000020008000000c0030004001000c001000c0030000004001c000002c0010014000002800c000000000040000004003001400000080010000000002800200000000000000000000000040000010006000c003004400000000000004001001c0030000002000000100000000004000000c000002c000000400c00000030000002000000100000000004000000000000340040014001000c000000c001000000000000000004001000400000080030004004000000000000000024001000000000000010004001001000100040000008000000000500040000000007000000500000020000001000400200040010018000001000000000000004005000000000040010000003000c000000c000000c000000c001001c006000000000080000000004000000200040010004000000000000080000004000000800200040000008000000400200000020008000000c00000140000000001000800000040000004000000c00000000040008005000000000080010004003000000200080010000002001400400040010000000001400100000010014003000000000040020004000000000000040020004000000000700080040000001000000100140030010003000000200040020004000000000200180020000002000800000000000000002000000000080000004000000000300000000000002000000100000000008002000000000040000008001000000000000010000000000c004000000a0000002000000500080060004000000000300000000018007001400100000000004003000000200000010004000000c001000400000040000008001000000100040020028001000c0000000000000400100000030000000000c00100040010000000000000100000000030006000800000000120000000000400300180000000001000000000100010014000000000000000000014004000000000000050004001000400600000000000005000800000040010004008000000300000030008003000000000300050000000000000a000000000000000014000000c00000040010000004000400100000010000000
  | 31 => 0x14001000000a000c0000000002001000000040020000000001800100000000004001000400000040000004005000400000080010008001000000000000010000006000c00000040000004003000000500080040008000000000900000050000000000000000000020004002001000000000000004004000000200000000004001000c0000008007000c003000800000040000010000000c0000000000000800a000c006000800000000010000000000000200100000004001000000100000030000000000000000040020000006000400000040010000000000c0000028001003c001000000000000020000000001000300140000004001000800000340010000000000000300000020004000000c00400040060010001000c000000400100040090008001000c00100000010000000000400000140000008000002c001000000000000060000001001400000000000004002000000400000030000003000c0010000006000000b00000000000005000400200100010008002000800200100000000001000000100000020004000000000200000020028002001800300000040018006000000400040010014000000000000040000000004001c00300000000000002000000000000020004002000400b000000100140000008002000000000040000000001001400100140020000000000c00000000030004004000400400000010000005000000000000020000001001c000000c000000000100040010000000000400100000020014007001c000000000400040000004007000000100000080004000001800000000010000000000000200040010000001001800300080000000000000000b002c0000004000000000200100000008000000000100000000004007000400100040010000000000c0000000000000400000000070000003000400000000010000002000c00700000000000000001c003000000000080010008001000000000040040000000000400000000050004001000000100040010010004000000000000060000000000c00500000010000000000400000000020004006000400100040000008002000000000000000000001000000000000010000000001800000100070008000000c000000c000000000000000000010007000000200040020040001001400200000000000000000c0000030000000000000280020004000000000300000010000001000000e000000000140000008000000000000000050004001000c000000000200000010014000000000200000050004000000c00000140020000001000000300040000004012000c00100000020000004001000000040020000000000800100080000020000000000000280010000000001800000000000000000000801100000020000000000800200040000040004000
  | 32 => 0x30f0000b1340000002e3a661000000000006df8000a421b10000000054014cc36e800b21faddc00022e20608ffc89628ea03b542c00a0cc2000000000000000002b610000000000000019580000000000a85c0002e80000844175400005db000296a27b800000000000001c06b018000000000019c253216a8000000000000000000000000187a32caa2a834000000063000000000000000156c0000b867f580006a4a83a0000bf224f96a6743a64e741800034c16ce0002b1665ead6a7dc400000000000b715160002d1645283931f049fa26400000048b586c5c000934895265400000000b18517800051340000db80000000000a4780007d00000000000000000003a19d350000000a1122d00000000a52000000000001942c430000000a0000000000000000289e0001aec61c0000a170b021770dc8a6b0ef6000000007980003e98000000000000000000001cb17e88f8c8870000000000000003a10000000000000000000001ac8000000000033002bb0000d0c533800000000001f1668a7b44000a84d23e9e19288000159e00000000001ad00002f2a00000008baa630046000078f9a4e5d4800000000000000000000197f1560740000000000000007aa1e769c11c5ca5d806800000000000000000000068f400021b000000000000000000000000000000000000000a8b000000011660000000370a1a80000000427945d04b0000000239c4f3168448700000000f2000003bf8ac1a3882c0000000000000022c12e10e364700000184027e0000000a2d5f4e000070400000005e9800000040000008000000c000000000100080020000000001c001000000100080050000003000c00000040020004001000400300100020000000000c0010000001000c003000000000000000018000000c0000008000000c00100000000044000001c00000080020000005000000000040020000004000c00000000000004001000800900000000000000000000700000000000001000000000040020000007000c00000000010000006000000100000010000001000400200080000004001000000700000040008000002c00100040000000003000000100000000014000000c00200100010000003000c00200040000000000000000000000020000002000c00000140020004000000c00300000010000007000000400000000004005000000000040000008000000000100140000000000000800300080000010000000800000000030010003000800000000080000000000800100000120000000000400300140040014003000800400300060004000000000400000020008000000c0000000003000400000000000004000000400000000030000000000000000040000000003000400000080020004000000000400080000000006000c002000000
  | 33 => 0x618800058b80000001c370000bd00000000000000000000000000000000000000000009e6c00037e000054b1ea900000000000000000000000005f26c0dd56388ab9abc7400000000000000c320000810000000068087a198822780c3cc8a0000dbc47d8000328a2a40001cf00000f0caffaabe00017880000cc8000000000000000000f68464000000000000001ec800000000000000a60265700000000000e640002e20000150477780004ff274200000006b0d7260000bf413e00000000000000000079b00000000000a6f808e92b1dd6000046f8d6ab9b000000000006c2000000000000000000000a068000027000000003c8b0d183100000000ee1f1d5c682ce5960c2ca0fa60a1e1d338528af5e10bc0000c4c000000000000000000000000a1464b4b4321cb000196400000000000542000121a240a7d20002d4600015dc00000005100000a604000000000000018238a94de80000000000191a135c57c549c0004e300000000000398800079f20ba93e000000011840000000790c000000059e226000002e800000000000000000a608e7800000c40002d7444480000000000000000080d0000a1f8000721091367ec00054e81549cc80000002c3dbbcdc44000278100008a086783ae0001a4c00016a404900006558000000079831f0000000092600021670002efea18800000003e60000000772000000000000000000b190c9891b0efc0000000000000000023049836f0c17f800000000008a25e25000000024a80000000000000000000000000000000000000000000be0001df42a468c82be4b1e0d00c03000000000000000001d440d60a2a97e151357a000000000000000000000000035317fab1d8000b5f800000000c642b80000000000adda3de56e0000bb0a196000000098b299a2bc54c69709842284075611a2dd69cfadb0b6886f0043000031b2458000255e00000003e6800069a0000000000000000004f8e364849113e733101a0000dea6d1a47c0000d1202a815f000034d5520000000000065dc0000000d840210000a71800061000000000000000000000006540001ec60862e5c2f180004679808000000000000000002a9000026062a1d40ea8d00000000000000231e00004d200008a2148a79c87200000e1c000000000050e1cdc62c23d416d220600000000001a7620905d49f023faa2140729e59c640000000ab6dea100009500000a40000000000000000000a81382a5922ef0db0000000000000000000000000000093200000000b7495600000be9a28000000053c40002a9000008140004b90000000000012d10d00002a9640b80009c399434c7000000000000000000000000005da574ac180009bb656e5efa1687c556029eca02a000122800000000000000000000053200000000000000260000
  | 34 => 0x912400098fa86e0000e8900000000002a2b6d9000086105e00002ebe8ea0000b8ac0002f4800000007c962e000000000003d34000a081c70803ce5a5ec00000002dda2102c5a000112600000000000000000119f0220ce20000702000000012a00000000000740c0000000000017a9d095f04d00000c8000000000000d410001102a0a9b2a9c929350b7aab87962ece3328000000163c120604e1a82ed4088400052b8fa100000006130000629887b771a77bad881b70002a9e0002d4e76b8000000050200021b88b49150b6708c4962a9385948b144e58000933218630d11af06f2e67a280000186400000000005e614580002c8c5f08d500000000000000000005290001d52722000005185c270f5ae875ca8e4000000000000009ab2de047088c0000000000000000f75f2e0000000b5080000001cfc00026f90b8923a6bf8000139a0e600000007dd00000000000200c000000000000000007a5664fa1c26f2054c00001fc0004af0e4a00000000000000000233e0000000000045c0002eeaa0302f800029c2629000071e994b00000000000f0676380002f28000000000000000000000000000014c679c00000018f65c5800000000000528000117800000001af92f489400000000002b3a000000021780002fe000000000000001db00e700004ba4000514113800000000002356000120c00019a714dd99227690522038880657800043a400016300000000bae16e8d7404c15f663a4000b7780002b006bc5df42aa000002f3740000000257200000001c30000000264400029cb000162f00000008d30d722ed01c3000000000000009eb591000000000000000000000098ec00087412c9ba89efe000000031216aeaba800063749e40cc800023c00003e61b542032e2e33eaa50a2489f64c30000bd6818e08da0c80000000000000000012ee00026e00002b83b0590c64b981d90001902037c000000000082d0000000000000000000000000000000000000004861f8a0000000000063400023570000000b6f80000000e4c9200db6ae90000243c000000000000000001df0000071800000006e60001b2479b80006a4cae958a164844a00000002eda000000000000000000000000029200000000001d580000000000094200000bb000000000000000b0400000000000000000000040e6460000a73800000000001190000000277e6cc87330000000000000000015c20000000000000000000000e9c00000019b800000003df057020700003d0000000020d100004917a7800069e00fa779987149f80004b1000061a80006900000000000000012fd9fb000000000000000f7e14ca052185eb3fb5b90fc000074aa6aac316fd000000000000002d2c7b689c6b9582da81a0000000000000000000de8e73ba62c3e23a0342000000041d80
  | 35 => 0x2c8128a7063a4016364a0ed23f940307d8893637c97ac61d8000000000000000000000000000274600017f823c8000000104c20528460000a8600000003cb00000000000000000004f800059e80009462ad909a83a00000000158665900025fa21aaa7f92a400018904aa29298947bca16f4b6c000a7567800000000ac42964192c135b06800067e89a6886000000012320000000000000000018ee90b193f00020d70002c9835f01ca0b246a7000000000024df0002ec40000000378050000000000000000000000086b92bd14d000000000000000000bd98000000000000002614fd8000000043962a6542b4d800084e8c3618100000002f544a6088dadd0000827168a0000fe00000bd70000b940000000000000043000b874700001b72283000000000000001150000286a7cda8d869cb1a854ca7fc0000000000b7610f500000000a900003f3000000012dd31a00000000000b00851e000000000003c50000000000000077b80000002d2420f1d867ef80000000000000000000000000e91ace723935e000278356003680000000000000000000000000000000000018ac00000000000000000000000000000008af613e3a78aec12f80000002236703000073bc00000003ed7e20000602a4c00000000000000095a27c200000000000000a470c20b308ff088f8cb28e4800000000002a08eae0000000bcec000a5fc00048e5e9fb00d25ba9f800000500000001bc04b583a30000000000000000027380000308000000000000008200d04000165cb6004c034b000000000000000000000000038c800006a80000002b12000089d7f402540000000000163a9d780000000000000194299280d6296adb200015581b5ab2cb4b9f6d0000000ab3800000006ab00015b700021c4884800000000000000000b9e10cc712800000010940cf800000000008e307e041f0000311800091c00002e285a40000000000000000000003aeaeaa0fdc43d0000000000000000000000002eb859b89684cf1be02220a8e0000c8636ca86801f400000000000001d900001c2648480009b0895459c00003860f109feaa16266240a00019d021c80000001a16000000024b80000000000000000000000000000000000000000000008aec00014a800000029404899e3089f80009ef800000000008bb1e4c5af8000b892a6a00000000001c5b8dc800086c8000660000000005a22c297d2000225300000006a9dde4000000000000000002b4c000194700000000000000315965a9e6000062b57a00d7408600019740002e860000000387112e95391529a51ebe0000000002400040e8822b7b2707463242e302c0001c580000000000000167c000203264880000000000a4d1d368b6000000018c400023d0052cfa2b9deb7c000000000027bc539800000007f82aa80000
  | 36 => 0x1ac8744000000000002650000000000000019a49a880000ac400000000007e589381388e7e00000001b480001656b541b5c00016b8000782800084440000000000000000000b9920a9480000000000000000000023450000000000000073380000000249000000000001220001f7e000000071600009e487c21ec130000027e45c7000000000000001f540001472000000044100001210000a028144a21000000000002452ea8000000000000000000000a7126720000000000000000000000000000247400000000000000e4262f2bce3e28000a36c0000000000000000000000007fd00005b9a0fc0000f820000000000000000000000000c0e7a340007040000000075b000000014c00000000000000210e00026be914e63a50329880000000000000000000006874000000000000000000001eec000293300000007d314b86c5036309040000002f600000bd531e00003a900002322ef5000000000000009d48000000000000000000000000460400026180000000fd65c62da80000000b4f073278500000000000858196e00000000001e5517fc0000000f4410b9d17000000000000006270000a97ca7594e91ca7118000124000000018c300000000000000000000011b800000028ef000000035100006bc01c172c80000000000b8711977c0134c929913064c12066dc000000000000000000308800085d800043b000024b000007a0d788dc263d95984babc10000a29d9ab00000005e0ad8888f0000b9c258c00f1e6427c80008ce9d8069cad44000000000027a144323dc835575537b80006b30000345800000000004fe292600000000002ce20000000000000000003fc4539b5cacf93dc9350bc704fd1e00000bc24261995b9bd0064aa000000000000001dac3af8000000064e28d8303aca1514862a5a42c5981d626e59c8be000000019f10000946000000000000000002e794d14c24000000000000000000000000076a8c0800000017ba6a70000000000000010a80000000b8304f20000ce6000000000006d400000000002bbca2e4ab20000e140001cf426d8000000000000000008050000000000089e5e9ab60ae30a46000000006da000000000000000000000000000000003783b180000000000000000000000008ed14a1000000000000000d300008a100000000000995a29c0000df400000000000300268e3c2b1793e839d1d39a9e9ea4000067f5ada442000042600006780000000ab4accc21b65e686fab657429f369220000517da3aa0f449408f80000000000000000000023a23168c600001f0890f9e7260f1fd91cee3e69db00008cfc00000000006c74c334f2c62701ea9d4000000000000004c480000000000000151c00000004eb80000000000000189000019e421412fe0b140002bbc0000a140009f405137dca
  | 37 => 0xa42c4a60000000000240c000000034e000000004f700020f7000227b231800000023e803a049a554c000000000000027120000000519c0000000000000000000004440002cd63dbacf887c0000040800000000004fdee360000834a4e8000000000079bc0000001cae4322b1f00000000c5400000000001ca12b600000009228000000000015900000000687000000000000000002c54000171296a000077500000001f7c000000000000000000000000000000008d607580002941ac1b838000303c24a000000000000000002c4500000000000000000000000000000000000000222200003f66ffa4b851a26f593b9e4a4461ee878703110c11b6f00018b22271363000000070b000084fc00000000000002c0400000000000000136c64510a64262f8a9f3000082800000000000000000000076a00000000000000000054286000000000000000062ac000000000064f2e5800000000000000b081bf66c208ad5bc0c7a00022ce00000000000000000000000000000000d6ca2618840f1c000000000007bde06000000080724e60000000653000000000000000000000000066200000000000000000033b80000000eca8cd2c4c00000000000fea0000000000000001f85ec7509ee271fa98a0000000000245d5de17e48524720048e6f737629e67c5cd4600013a000020f21ba6154000000096500000000000000199a000000058ac9ce1fc108ea25d0237e148b5000000000000006d7800000000000f700000000000000000000000001a4cc6a4c8af140000724000000000000000ac80000000000000000000000001f1230c0000000000000000012cf000000092b960a8e9143900000000001ffc000000000000000000079000000000000000f60d02000187b00000002f116149845fa300000008082a4c00002d200000000000000000000080c29a42748000000117e00000a5ac7537000004800000000844d97217180000fe8f306920ac66d9800000000000000000000000099a00007710000aeb01fe49a00000001cc014d8c1800002c220684da4d6000022d800083b800000000000001510489400000000001bb08a4000075200026a803b000000014dc1e6a05e00019ca0000000000000000028600000000000000000000000001528803000000000007b2c0004a6800000022a20001d4e462821c00000002d2800000000000000000000000042f85cc000000000006fc0791034b2100000001b927ffa30db1d4000ac880000748000000000000017a2aea0bf6af782d849680000000000ab10000000000000024121f3000000000000aa06060002c0e17dd95ab3918d763e80000000000a1b400000000000000c080000000a2400001c72e7d36d000000000005b08eec445acd00001f2c0001e6600000000001d9c00000000000000
  | 38 => 0xc5ae00000000000a51272a30f80000000000248c9d00001c090000000000000025d0000879a854b3780006574fac1671054acaa7916f30d98000215c000208a00000009cb8931473121400000007adc0000002b3007818990002a0a19fa9687a480000001182000000007d80000001402000000000021fe0269e8200000005a880000000000adf80008d2199884e40000000000000000000000000002ae80002e9ca572bf008a80740001d9a6aa03540000000183c000000000000000000604000000000000000000002c7a000000000000000001e320002c3b00000009c692df0901a0c89f59a600000008f896da8d858da3f1119424401b80a880001f0d35f734a9d844156e0ba90000593a70a0000e2a00029960001ca20002acf000293c6f78742000000000000009e3068152c00000000000ab911b6000000000019f48879f26183800000000000d5a86a58e232a000000018824303e499ec88300005115869112d43a1e280000000000b062af0299c184000131819dab68721800001d800000004860000000000000035b800001b24fe00022ca68808dc46c8000478dc472a880000002ebc8c58c9c3738000000276e4a1800000022d10002e87617d446b8c80003f56a7c7d5800000013ac0000000723073a1b8a5c09ee000031480000000000000000084d00000002d48000000046852ca87d0000000000038e80004d08d20b3e800000000003a200005fa000000023253c882b900012780002d64000004cb18049e8e6800000011e200000000000000000000000000000000000b79900478e80000000000aa897242080000416800000015be14fa90021c1f5e275a11c906a87411f000068240003cf000000000009de80000001f8b00000003520000000000029300000000000184edac000000000009006b61ed00d4a294000000022e1c3a0001fa419dc5602cea24200024720fb000000000000001612068192573987ac5fb0000197000000000000e0800000001fb00000000000000831a1280000000000000095302df0000000000000000000006a14000000038c0000000000159a0001158000000000000000000000936000000000000001489000000000000000000000000000000011fa00000000000000000269a2f78a0a1094a209e79a8c5cf1dce1f990bc00000005b7575000012943769810000000000008de00000000002a9497a000000000008d7800000025ff0002056415800017a800000010c2a8011080f4ef48484000057e89dc0000505000137a000188503fec92a8180002c0eb43a139cc40002ee8336153500007b44950000a5f118933780000000000000000000000000001820000000000006b4000000079e00000002e4600000000001aae3aa000053fa95e000000000000003858000000000000000009df56de000
  | 39 => 0x8400083500000000000000238a0000000000000081e0461000000000001b9b8e000000007a500000000000000000000000002a02780dde000000056380000001f144c987754d6800000000000002d9800017b200000000000000000011615ac9800000000b5b1d762d580000002b180000000000000064e8000562000052fae4a00000000000d240b1c5851e104a300002cd3a30967000000000000009bb00000000000000178a9a700000000000644c00000000002a72b4400000000001b8b36980000000000000116f7fc14780000000000078b98600000000000000000000000000000000000000087e2bdd000054b00000000000d9e3b81a1591120e29eb04ee641cc2ea9700003ab1bc4342a15e0000000000000077080000000000000000098067f612ed99d00000000000000a10ea0c83fe7c82d100004e390fe0002a46b4809e8000000000000000000afe000000000000006259d940001c2a8db000000015fc00026fe000000000000000000000000165b92fc000acf0000245c000000000000000000000000000000000000004b34000000000000000000000cd266d800000000008479010000209883d0000aff000000000000001d1f38c061800000008f9000000000000ab000065b000083610e800000000d1a82898c9c281dd1dbc559800000000007c493ee000000000009f067300000000000000000031a40006fe800000004b8000231a00017143bf92fc000000000000000000000000000000000000768aff266808a000016b7840000511c00004a8ef3a8f63880000000000000000000000002e7b00000001339bd80000554165000000000005c802330000000612c762000098a00004a705e000000000001bd000000000003b628d695d80000a2a19a16d8000955000052b0daa2bb8afa912000000029fa18f00002fa80000000ae400000005f800000000000000000009a0c708df144468200007e00000000030a19a0000000161e000000000017320000000410800000000009b400000002da500000000000000a17cd2800029305d580003d80000a28482a12c07a764ba0fe0000c5492c800000000005ff800081a945ab10400000008bf3658000a1245ca00000000000000461ac2600000004090000000000048b0000b1440007730000000000000000000000000257000000029fb000094e930a7af7b98000000000000000007808e3cb64ac44000000000026690000000bce000000029021d1a49a674c0000001b62032c00000015d46ac80000000000000000059a800036e16aa59540000002451000292eafb00000e500003f710ea0000000000198d000000000000003ebc000000003e0000ce066b2e6c0002d7800012dc000000000007ca0000000000000000000000000000000000001c470e0002f5000001645f9876
  | 40 => 0xc63d469dd0000000757182c000236668700001e266fb00000007c700000c488ec4b405c162d400000000000000000000055a0000e009bd19c0572220805fc000aac267800000005c40e4056e40000000000b1b80000002aa65a39c3600023aa0000000000000000000001f2d81800000003209a5818fc9d894f1d536c39b3eb3a00000000000abe800000026c00000000000184e963894800000b67fd800000027411ec800000000002c1800062480000000000000000083e83c90001cf60000000000000000017c63c600004c2800000000000000e0866eaee62989c410000b0c000000000000006640000a5280009e6ae22b0880000f3400020e8d9035494e73980e82131a6fd3b5000096c982400027fc0000000b72800000000000000000000000092e800000000000c0a75039d80000002c880000000056ca141848ea2ab2a3b84e180006f89f381e71c4000013360000000000000000029e2620c0000428a559179b8000000000002b73000000078d95da000000000000001a18000000047260721db00000000000000000000000000000000000000000000000000000bcc0000000000172a17e10e49e2000099090580001a2400000009b700000000006a41800000000000001b6c160a676b858b1c61e0000541800000008aa000000000008f60000000000000000000000000000840506390d28500000000000164c0002cf40000eb200000000000d580000fae4008000a3c015c000000000000000000000bd480008891fa500000005020383000026400000000000000b2f0a8c00027dc000000063b40000000000000064300013aa00000000000d2e080d1ba72512441600408a339dca78f194f000000000000000001e510000bfcb368c92000000000000000000000224800000000008699088b0c000000000004696a320002bd60000000383205a9250000000131a000000000000003f600008738000000000000007b800000000002b5580d80ce00019e00c7225c42d000055729f000000000001e871cc6f585591f2000000240001d130002a844f487120001fe00001c7800000007e300000000000000000048da2d400015a88548eb011e8000962013d293939c01a874b08d00fd7521e5770d0ea35b2400a3a489447f318824f5800078016d6bd700000000000000161827000000000000000000090640000ed229f00000000000000660800000000001a500000002dcc75bc00000000000000000000000000000000000000000000000014660002d3400000000000000a7594880002a1a000000094080000000000000000000000008c48e1a000000000000000000000000129e0000000840000000000000000000000000000000002029c3b08e00000000000000163b000178c00000000e38000000279f000011e1934000000000003
  | 41 => 0x18a20000000000000000029c00000000000112b6869a2a050800071b856d0000000000000000000000001c546ca40000000000000000040884520b580007bcc00000005492bd80002fac000000000000000000000000000261b00007fe72b162d2c8000000000000000000000070800000000002bfa00018f08ba000000000000000000590ecaa00000000002a1c00006a2000000000021e800028de10d800000005b8ad6000035f800009940000001be84f8a3a600000000000de600000005c380000000000000012e0002aaa000213519bc84e0002f470000000000000000000000000000044800000000006d5a0d9000000000000004370000000000000000000000000a68000000000000000fe231609929a7adc40001ca0003c0000002dd2adc232685302e43bc00006390000000000000000006f98000740ace60000000000000002b5e1874e818c000000000000000002f4a070a876a7a878000024be0000d18101cbc0a0b8da29b680000000000655400072c28f20fa00001b400002810000000000017640006340000000000000000000000000000000091326545b6000000000005b4a6c4a532b5f00000008b9800000000000000000488400045880000000000668dd0c00000001c61b251a55d2c00003e00000054942800000027720000000724000002e6420000000000000000000000000191f0ba00000000000000183fab34b300000000000248c2aea0dc1a0000033e0000181c0000001c480000a23ad20a90b4c0d150002e7300009040000000a459e6b46b800099a9960000000000000000001d9e00000000000000000000000000000000818895c95828d2198000000023b800000000000000000bc09a360000000716400000000000e040000000000000000000000000000000000000000000000000000593400085b853a635a754000000011000002ad890c000000000000000bf800000000003d3a5b000028b3000000000016dbb322ca847ba7c4b2780000000000ab78000000000000000000001fd79a90000a0fd40a000000000000002d6a28a85e80000000f12000000048a8000000055684a91a20000000000000000000001e1800000024e80000d6a83aec0823825d20f196960000000000000079580000000000698a7cf463c0000000000000000042e000000000000dc0361000030e7f200000001790182835a435ad9eaf18000000155600005dd00000000000000000037601bc00000000000000f84000008c0002d0e00000003c0ad1a34380000e40000aa080000000000000000092ad0740a18d9a3ee0df66aa5abb57907d6b7d08f8ac2947e9ad800000000000000f3634fa54f0002d263d6800000000008108a8a0000000a8957a4b9eacc0af5000000000003221c2f33a800000016727f71a5200024
  | 42 => 0x269d6000000015827d600000002a44000151a0000000000052b00000000001b1817100000000000000168b0f4262a649800000000006c34000000000000011700000000000000061a00000002619000000097400000000000000096e000000000017f0b17141200001a4000000034196b2b078000000000000003b27cd1c52a791fb8101088200024a80001e4b000000000000000000000000072c3ea00008ae000033f11b86178ee4000106218700000001b860000000a34800000000000000000b1c84e3000185a000000000000003e40000392000000017830afa44e0000000000064c87b8000000120e0002cec00000000002360000000006a2bb2000000000019858a6000028c14bc1b211be18a00000d9c0000000000000000000000000000000000077700000000001c010000000113c00000007350002a88af629fc5e560b69ffa5b4222804959bef3ea2b176a2230000b97a2ee0000000a8c00000000000523800000020a4000000000000ef9fcc00071a05843810d1a00000000002d5800000000000000000214b000000000000000001b2600022c40000000000000000000004724eee9fd0ea1000000000000002c340008ad0f544194fee98d9cd6928ae440000000000000084980000001908000000000000000002c8e000261608598f2000000034000008298000000000001f29fd0002cf200000008538000476800000026964c40000000000000000000001b840001d019dd91144f081088b58b34498998a2ce146e06987b15a08000000000000000000001b7c0000000051cdfa0000a7a809a1158f59cde000190100014faa3e99f9000000096080005f72e1810400000001821b0903f050f66a775e00001cf537e750159c32310080001e7a000245400019f3109000025b000000020d000000002edc00059a10f0041800068fc000b840000000000000000000000000000000008ca040b0500de00017d800004ea000230f00000000000000a748000a2e0acc0001c50aa4a16a1f6874c1e5400033a13d000000000000000000237a708000000000000000000000000000000000001b98a15ddf0b9b5ada3a0c6ce15aa28669980002950000000149200000000170000000000015380000001d4c18500007616b4600018a30002d0600000000002df08cbe2161320000000000000000000000000087c0000001a3e0001caa00015347a2000000000000000c64000000000000005959c1c4f84000000063800000002461c9a0000e6800000000000000000000000000000b280000000000578000000000000000d291e4000000000005c880000002cf039e93a80002d8e36218953960fd4000121f0002a0ba480b4000004ff76e0000000065e86e98ae796d4f2a20e71d192850e248a84a8a14ace0000000000229d6ebab3894800000
  | 43 => 0x1a20000000000000000008f400000008810f2400000004ed80000001f498110000000000000000008e800005d7c00089780230c94ca400000008e1000000000000000000623400015480000001d660000000000000006d000000000000000000b8f08c2000000022a00008d08a680000000000000000000000002d8a368000050d8d0821350de3baaca4911c44a0000186a1b00002a20258000062e0000000000175767228400001b5800015c41510b42000000064b400000021e00000000788000008f11465ff659e52d80000002a1900000000000000bc180000002c94130e476a14e41b0002460000181a0001e2a00000000002166000000000000008a2c000284a8f40001e80000000000000000001f6c1e35e9700585660000ef20000fbe00000000000000b7c800000000000000000000184a74d00004c10b10000179a0001068000000000000000000000249c00000000000000248a1366537fe9df9a43000000000003998000265800000000001fb835e000000000000000001cf827980001b62730000000000000004ba80000000000000000000023180c7829c0f44000000000000021180000000000000000023ba00029b2b1b0ecc000000057600006f4182a0001b1c9f82cd4801aa7000000009ae89305bb2c52000000053a83cc00000007be8000b2e08582242e500001e9400028e34820000000000000000000002602000040c136024c00002b600002f008ae03c5a30000622000082818148f30e8780200000002888afb8000738800000000000002beab2405230ad66260ca05c09c09eaa42119e50000000000000003d1b2c51e81f03971cfa3d18000611000000000000000f16000235c0000000000000000000000002eec00000000000000000118b00000005bb4000000000000000004349ab609c80000938d60000195866300000002dcb00002f4000028392424f600004c299680006b88000000000000014f79c880003cc8000000000000000000000fa035c000005eaad000000007c92ce00000000a808000000000000009ec0000f04000267066192a60819d377acec9a67b80008219c3c00022fc00000006ac0000035000000025ae14b00000000d83000000000007be33500000002b66000000004ce6b400000000001584000000000005ad000000000000000002b2600000000002e12000000066c800000000000000000485ea1e8fb20c9000251d00000009e3800000000000000e2c7d72bc200000000000000636dfb53b4000000000009bbc000000197c000000000000005b29852000000000000000001250000000090e88b222b027800015bd609ab2f93b000000025c835280000002ac8b930b520000000b53000000015087c7a3f27ea800014612f63a9c00094780000980000bc9904a029c000667a4da0001
  | 44 => 0xc400000000000000278900003b000000006da80002df000000004e8741c00000005d65dae0cd0000c020001044a9901ed000000078300000000000000000000019d20001932000000000000006af9a3b00014ca00020ecbc90000291000000000000000a28000000009b1c8203c0296395800000029f800000000001c6a0002b334e08c4a000000000000001cf0c4400021de00000008508000a2880003808420000000000000007aaeb8e4f1800000018747f7942a8ab9176000000000000000000bd43710000000000014280002ece2ac0001f65000000094b90a5000000000000001efd3e4000000000000000000000000000081e80000000fca97b0000000000000015300000000000000000014730002dea78a00000001a74a7355604b7a3780001baaa7e400000000000000000a0358ec67c8e127c8800022945115aec00013c00002c480000001a5600019d600000004caae3e9f5878c00000000000000000000072e28425ab00000000dd233c03507360000b6123981e0a1ca000000010c8fe88b000000000000747800015c80000000000389800000000000739f4a8058000000000090100000000000000000000000001469ba67ebc91a6ed10a26b906909a6113a487400000000000001fa1000000043cc68b69ea762b5a000000000008ae9d4a407a7940002a660000c76000000000000000000000000000008692700002114000000000013c057b800000000001ff0000b579a0e00017000002c4800000009b153d78e413a200000005c295d6a89c0000002af20000000b9006ac04a109c0001a0b000000047392c07b280009518d8c5be9f94801c000000000000005484758000a190000bd3000070000000000c16505a2301a249c810a00000001c2357c00000001f6a0c1c66a50dcb040000000bbc00007aea9df3c98000000085a20187260000000329c04700000003d70ffa7978000760a8d00000000aa680000000000000000063880000000000545eb0f81b03a2000000000000000002e1432b14e0000075000000000000000000000026e000000000000001f18000000022cc00086b000000029e0091c0000000000000057494c12f914550660000000000000000000005db000008280000000000000000000399a90001fac42c98cc067c4cc0000f050000000a83ec89ac500000000000856c0000000000013800000000000000b0545200000000966463a65c29ceb82641297e000000065ac0000000000000000000000001070000000000000010b60000000000133479c40001ada8ec000000070cc0006e92a6e47d222689916c6000000000000000000000000000074f00000000000000213b0000000b7000004b500002d5173a22b800023280003aaa28800020644fa4000000000000000008aa0000
  | 45 => 0x9f5000000000002baa4569dd00d0a9e00002dc0e6c000093400000000002b1c35ec4d4b9084dd1d80000413ad8c5f7a256379000096000007ecc000b93800000014c2000017011b000015bc00088a8770000000065500000000000af4941c0001bca858df1a3d09bef00000003b3817486a800000000000000f4ab1d0000016800000000005b2000034993503e22a2d3a3800000000003d580005ba0f2a0000000000000000000006688000000000000019620000000000176800000000000000000000000000000000000b0a80000000000597a2b62e59b2b6bd991e850c246000000010b0edf474000051700009e41570820a41f000121bb448d2f0494c1a4e485f40854ea00001e5200016b00000000000252c00000001be0000103c8ba6799e5f000000000000000002b5c00000007610b4888b800000012b8000071000000000000000000000054b800065100007e080000000000000000000000001b4400016b000000000005548000bbcaed856ec000000000000000009078b2e0000e34000093a97806469190cf20000000347aa2e0ac00009a2463291e21822b9c000000282c2639e9c615a00e6c100000000000a22c0000002cb426ba9b87cc8aae00000000e94080000077a0002a2100000000002bf666fc6fa436556ea00aa2218ccf09492a234729a0000000cbc54da5c60002a412d896c16f09b37984e8aa13728fe000000000000000000c4e000000000000000000000000000000000c2000000000000000000000000004800002520001d505b9000000000000000000000214600001967b70000784800000000000002528a36800000000000000000000000058800000000000000000000000000000d144f54000000108a00000000000000066800000014ed000062c4a1000000018023b0800000000fe00000008a862e400000000002bef00019382e0000000000000000000a4c8000bbf1c766f490ac95414c41eac000000272c00007e400017174102b4200023310002116000096000018000e1678a98700004312ab2000102847793724ac977ea5180006c19d2400000009c3428489322de00008ea21227ae0000000a091c16a8faef800004ca000228000010df00000000000dec000000000027e65b445b04b46d3a1b66f3c67bc00000000000000000620000067647344590000000137c5ed800000000002f380003211bf2267adab0000f800000000000000000000007f519fe0b4e0da6fb19913e78000000000000000000000000b6e910a89dc0000000d36b5f00000000000ba28000000000000002ba000000000015463b0c0005719e475fa8f7a0a3143225f28a60000ff26308a1c0000cdc0001ed80000000000195200000007b81fff00025dc26823b287a800091ea259000160f00000000000000000
  | 46 => 0x28000000000000000000a04000000000000000000001e9dbb59b1e000253e63f000000016bf8eb97f220c20a20000e709ea1b5200000001f52504ba017600000000000020f9d680005d0120a1808e460002f3643c8f390000000a6d862d428000000000000000000000290458a8a96b1a00000000aa00000000000000099ea04a00000006e6961a8f180000002ad8000225da3b954e11c4000bd10ef51d38000000000000020f50001830270811a00000000000000983c0000000000000000000021360dd0000000250000000000000000000075e000000000000000000e2429801690001ab400011780760dfe0002c466cc24220000000000116d39ba0cb000000000017ca000182200019999ab80000001f2300028103d3c000000000060d0000000067300024e500017667412b5e0e4953216221e264000007270b7a58dc000b94800000014ab00000009325576877c00000000000000000b8780003171eff1fa0000000000000000000000000000000000000000b004464b300009fc00f80001394841800419c9a42a428000000000000000000000000a4b00007b0a2fe9a20000513000000018be00000000001e2ea804000b1600000000a6f000000035ea0650000000000000000018c865fad960002bbe0000000000076400009b4a76c00000000000b3000046680000002c500001ce80000000000000000000008630000000000074800001fd80003b59d8cbca00008220000905000055d08ce73b82bd7ef000000000000000d3a6a000002fa2bb4000023b000000017422a6a2c000000000457ea213c000045b3ed800000004d900000000000000a5424de000000000000000001a130002e000000000000000083c00000002dc6000000000000b10000000a8cea6c311dfd829a869900025ea000000000009880000000000000000000004400000056a0cca7c800000000009f609150d800000000237b72210a0dbc000436800000600000002156000000000026500676d0a82e00000002ca2000000000000000000000000000074c9c390000000000194800000003c540004bbc070a880000000000000000000001aac000000000000000001f9b7ac456861e40000000000b2b95fe0000098999c0002948000000000000000005cc025a19023be000000000000000000000000000028e800000000009612d146d0800005780cc0000000028a5e46e227e24388000837800015e80000000000000000000028669af2a180002aac4500000bcb8000211907e2e7800000025d60000000b1095b60000000000000000000008c9d15e41e000015f8bf932d00002800000000285e000000017885ce6c7d7bc0601c4900017420001ac45b5000044f0000033c000000295800000008f600000000000000000000000006e280001d200006010000000000
  | 47 => 0xe000000000000000000000000005fa0000000000000000012ed7a3916e0f9c9787909b136744714000000069f8000000000000029900000000000169e7edc00000000009e90488a0c80000002e020002c565eaa70b000000057e000000000000000000000000000000002c88000000000000000000dc400000000005e1a3e0000000000000000001b5a15ce0e7aad8886af2a178acd8eda65a632400000000000e8000027de000000000000000f08000000000000025649168bec00020a800000007c1a23a8ef0000493a03eb488000000000000007b3bbba25200007ecb3716500000000233000000000004a403240f7d6cc00000000000000a6c00000000802000250e00000003ceab9e0000000198849866c45d2aa0657a000000000000000000000000000000000008e5000000012e10000a5624917e2137a2556564e751f4c0000000000b7d80002b589cb00000009d900009a3800000000000e18000a060874000000070c800000000006c042d00000000000000000000000ce944e9d9a6b21ca80000001a00000000000001880000000000000073f800022103d401000000000000000000000025367a9c000043950c2ab000096b053946828166c280000000000000000000000006fb98e80000000856800000020c7ba0a3540000c1276f81522af800864d9a4481ca11225a80000000000000128c0000000000095a548000029980000000000000000000000000001dea000221a0001ae0000260c0160520000259a63713f00000000000000000000005aa02300000000000000062d00000000000000000072e8000876800000013644cbc00000000dd00000000001454000000000000000000000af824e200000000000000000179c000000002c8000000166b5dd00008c3800049d00000001608abe155ab0b000010b5a980e10baa0a080000002c622da13060001ef1b66820b0000000000299e2bdc3c46b78000000261400000007d48e285fd0000000000087f00000000000000000000000006f39db20000000000000000000000001c3500000006bc80002d7022c0000000a048000000000097c9a0700000009f6400000014e80001e08b8a0000a54800040f87a2446800009544580001d6a000000045f1ccb000000000025262990000bb200325449f9c000013c0001728660400000011fc00000002db1efc9c62b08289800082c97d00001f0a59f86880002a61b9d8000a6380006d020ce1804000000286f83b4a580000000774800000000008430000000000000005983fb0d10b4a80000000000394af22000000000016267620000776a10700014d00000a1600011bc8cf00008db80002a789b050923215b118de3c52674000000000000000002130000228c5f690362049aaa00026400001a54000000070fd168746c00067a00001a
  | 48 => 0x85255c0002a5607009f8736a96c0002f5600000000002a2a000248654880000001a86bd346260000000123157896800009ae1d5e49817468839bb08510bd9701149e0000000af11bb6000204c000126a000000000025d457140008c1987e1ac1780a0217711cc0b6a000035cb96a9ba4f38adc29b8c100002e044ec000050180000000000000000007d66a0144847471bcf0a0002eae000090d69b89163ea8cfe71580007ce8000a898000000000016a2c4e000000000000000000000000000000000000000000000087a7a2800000008d4000000000015ec851c32600000000000000000000000000000000000471288e6ba929cae521b0664d784000212900008b00000000765a6cc7fa80006970000000000000b56df60e8336350013600000000000bb15d11fe6202000000020ca0eb000026a8000000000015b8000000000010e941001900009ea8000000025e76a800000000000000000000000000000000001ede869000028f00000ad00002fdc000000000000000004418000ae28a8f1aa03ef00000005729b1a0000000119a4bc8688000b1f25ee000000006426ea196a0d30002b9958f80001bc800000000003ca40000000000000000000000007fb00000eac616a019afc000089fba240000001e5a000117966b69140000000000000074153ea00011e400000000000c142cf05f039fda2cb9a68b2000000000000000000000000000000000000d100007b7e0a500022f04209484641400000000001e202c4000000000000003a6941e00029a20562dc202f47dc5165b3cbcd2da637f074d547867bb2c2538977ac9656580000000000587245fa6300008f280000000000a7a0000000000065a8000b899b8c7c100000002562a302457123cc8e000000000000000000000000264d000000000000000e6000000000005a6186b000000075f8000000000084880000000000000000000000000000000425a6f06b9d02000000008b70000000000000000000000000000000070280000b21b9c0000000b9c40000002c123558a84032800000000000002e0600018637c40000000000034c800000000000000000af200004bd000000027f282580000001a8277880004298000adb9196000033c57880003ef29720000000000146f603000000000000000000000002017980dc02d0000000246ea73c0000000000543eeba403a49600000000000000000000000000002a48000ba2d65182f00000000000000033400020104d7000000000000000e6a000143e3f900000b464d1b0a0b32000000064b1ece24f2858000000000004f69b997fc000203a000000000000008a1c00039f1d1452a084200016fe41415ea450988a735248200000000001ec4a6980000240000000000000000000566ac04cba5a60ae157200010000000000ac8155000000
  | 49 => 0xc4a984274e0002ed038f80000000000000000000000000000000000175e0000d9c00000009338000000266056500000000000000000000000003b88000000000070500000000000000000090412da0000000000046a000000030026588d1800000000008bc80000002c00a088000000000032c03c0000020c00011e6000225087900e6000141a000000000000e24d480007d9aa580000000000000068b87f476900780000000000000000000000000000000000000014fc8fe0000000000039c8e967049dba4858000141000039518b39458000000000066fae087dc2ef6a97845621287916bd0d0100022990f8879406b800000012567780145000000000000007f0eb04bac9b0c55527700001ef08d41f78219000000006de00000000001cb300000000000000a5e00000f940000000000000000071c80000000000000000000000000001f0106c0000b12c0000e9800053c016220fac5b0000dac6a8527c5689ac685ca27f57ca0f658428e616c98ba0000000643800000000000001642a770000000000046a106c00000009e08be40000000b0f000021e0000b42293e000000000000000000000000053c00008da00003f513e871a00000000002e5476294a40000ff85ed1d186de800012f000025a526c1f396b463e0000000000000000000000000ab1a6fc2b10000bcca4e3000000024c80000140000000000000000004385eb600029869ec04e00000000000069a000000000000000000a0900000002ed4000b99000066500006a2c0000002d9da115122b9880004cc800000000000000000000226eb2f80001f7a8dc4cfab3d000083840c00009b780000000e5e49d800000000000000000000000000000000000000000000000009760000000000000000000000000000000160e3b0400000002f6145800049600000000000a231e5c0002e94903a86174689ef95806ea0410000000000011c000000000000000000000196189a000008ea0bf42e91f0050266b90840003dc43d26a9ab006904000000000007b8d42740000053aee2a00000b0000000000020aa3140000ba80000ae143e4000000051d12f00000000a22a7cc34d0bfaa50a7176268eb69f18000749800084b800000000001cdc0000001758ad5a6d411680000000000a981f90000000000000006a880009a12aa47de9cbebb785973cfa22000000004a08000000000000000000c6000000000005108000018223811fc0000000000214800000000005a4994689d00000002e8400000006d426c60000000a6b800007c8293000000061368b6000128b000022300000000002d10000086e00000000001d1d000099c0000000bad2d560000000000000000013da81b958644d800000020589b8acce5d6400000026310000d660c827a79e4cceca5d228e000000037700008b6ada30
  | 50 => 0x12b70001ef80000000000000000000000002240000000018aa728000078f58309f409c1a4d000000000012a05a18648af98cd00001a906f4d90a61740001144000000000084080001cfc24461402d4b7513beabb0000000043000000003b86d40000000000000002558000000086672a19d46ef80002361df80000000bc5800000014980002bc0000000000000002278000000142013b0000000000000025967c3227a6ae2f3000000004fb0bb80001d254231eee0000000000000000000000000000000000010aa5986af109a97c0000000000051940004d21296000000048e2daa49000000000fbb00000001ab9dfa0000000000000000002ae9cbc000000224613e400003ac0003f413f400000000000000a7bc000000000000000005f02dee0002748000000000000000000000000044e000000000000000001f571c2c00000000007dda34d0000000152ad380000000000036c4fac00053880005f38000213020800000000002174000000000000000fc86250001c7c00000009c400001ef0e0e0002a4a49b80002fc40000002f4b360840a224c0003c2c00000011ad22de8ca0000be61ab40000002508198000003caf180000000865483285c12b97d1a44faeee18ebd1ab6900000000000000000000000000004b80a97000000016391f80002cd28c8c0009c2221400022f40001c92000000000000000000000000000000000006d15d380000000aeda17c00000000000000785800000000007ac800038816cb000000098f2eca9949604357800000000000002d509fb80000000000000000000000000002da4ae1000022f809f000000000000000c8400019b800000000000002db40000210000000000000000000000000000000000000002b7800011ea8588000909000000000003f48000000252296eaa317c5868310dd39e0c500000002e8c000207000000000000000000000000000000001ebd4d2d7367ba8000268832ab7e21dcb10000000000004f20dc09249b12036a16cb3119c421f000000014f6140400000000000002544128000000014d200000420000000a37c0000a2c3de5f580003ec987a14700000000000945000000025b678f400040f1bb80000c0c25e9cca3c6400000000000000000000000000009e200000007ec80000000000000114c00010c300000000002cee66700008fd80000002de80000000000270129700006ef0000157de400001156000176200000000001f44000000000000000002dfa04dc000ad918ef3fd00000000000234a0c1000000027a800000000000000000524d7c80000000000000000000000000ef40001931703800000000000000000081200200000006a21fc200000000001b760c34538000000000000006c54000000170200019c6000000041c2ecc8b18000009c00083580000002
  | 51 => 0xc239000037200007c0000000000000008840000a9080007688000000000000000001048000aea8000a950000843614a0e5494c00011d7a7b0000b0423687364000000000097f800000015180000000301400001980000000000000000007e12b400000000000a741e38000000251a11f800044389d42b080000001c2410f800000000000000000000000030e81f100014010000000871a8a43e38000000170c000000000000008078000000000006b4000000000000000005a24d6200000000000000000000062623c41768a0800004fc000289a000000000000000001a8a05a972e0002b2d1ce40003e900000000000b6a64988cb94f3000290e000000000000004e2800026900005ce0c1c000000000000006e4165300000002e892c6000076e5900a6d03440004f100000ef41ba0000000bd08000000000000000003e700000000000b572ba01cd80000002ee00000000000123d76480000bbacfc89f00006c8e26a3c6a7a064cedfc0001c4317d4000000000000022a3a900000ab718fe00013d8000079e9d7000045d4000000249e05c92fa00000001b30000000000000015de0c193287340000000000000000004c0800000011ec00027bf00020e84200046000000000000001312266000000081501b6000000000017d40000a0b000000000029608ca00006a34000000000044d00000002b603628000000000000b1b197f881be6b2800000008b43b780000000000000251c000000000014e46a5a3b6000000000000000001a5a000000028e00000000c74000000000000007f3800000000000000622000273100000000002a9c24499a00000000898019e08894d860bccf600000001136103000072e906110752301ec07d00000001475490400000000006a90000000000000000000000000000000042c00004dd0f1e00000000002b4e0000000000000000000000000000656c000b8b00000000000a0f0000607eef40002b8c8d38ee600000000a6800081198389a19502000000074b800087c80000000000000000000000008ff8000000000000000000000000177c0004ee8000b9c80000000ab400019a500000000000000000000077b400027f8000164c67a000076653d0000a2fa73a6d32b399991060ba99a6ca4da27654f90ee95a99213ec1a3948b85a600007a8000000026b000000011aa58c000000013660000000404800000000000000000092c48e0001674000222c0000000000281e3474000000000000025a20000000000000000000000001d70000000097d0000a8e800035a6c800fb91540002d4357d0000a5e800068f24d6000000000019490000bdaac855bc95587580000ca07d4000000000008a04ad89da8b9979418a100d00000df800054e194e0000000000000000028d4a662804238838a5748b002cdaae25280000
  | 52 => 0x21c0000000000000000000000b2d9c5e00012309d587f247614e9b3629de26f88763940000860460c8a68000456997834a80000000000afe0587000000051f0000000177667c124c000191284202e6716855e5201a704ba0fc817a12004dd866c5158b92b739b4e68526ceae0166c7ae13af756aa99a490d920000036000000000000000001202000000000000e96f14000a81c00000000006e780001ae8000a250000000128e00000008e1800000000006418212000000092a96160002ac209d0f701e8c00000009de000000000010d80000000000188b000000004500000008000667c0007e7800023f233d15d869e108c0000000000b59800079f85e5bab12d28bd80002ed8000000000000000004e980000000000000230072d80000002be240e00000000000000000004640000000bc1000000000e00004f280005ae8fc000000000000000000000000013980002ae603f2b50000000000007eabac00000000000000000061800000000000000000000000000000000000000032e9e1a2ec0000aa19b2230a8aa6b7f889600024d00000000b22800000000000000000000000017f11c169a8ad2b40000004e80000002e9656900000000000a74c00000000000002b574d280000001f64000000000000000002785b920c6ea3882e109e87d000002f25d2811c0001384b54800000000000000000000000000000000000000000000086f1a84302800012f40007f2900a3db0000000026200000000000d3ca53ae345a421fa00000000002accbd240000390000000037c2df8000000000000013b4126d1d2b6e0caa00ac63e433a70520da570000000000000000000a786810000711400000006fe4c74000662c00029cac3a00009b500000006b7000000000000000c262b2a8ba5cf80003be83f44810000000296200000006fe000076d0000286000000000000000000ba482c62005886333000000000000000a240000000072000000000000000c90000000048dc000000000079c000081d079700000000000524000000049c9eb45699b740000658000000000000000001ed4000000072e67ca7e04000000000000000000001f868d1d07a00024280000000000032c0000000b640000688a066abd070000000004ec80000000c667982b1e000000000000000000000738020200000000000c400001976000000000006c0aa602c30001ee49500cf4000000051b0000000000090d80000000000aa02b0c639c0008e594621b194ee20b929d0000af400000009891d469be000000000008fb94ba246c00092c000060d800000000009e2c00000029227588000000285a00025cc0000000a20000084b00004ae83640001704000000069a51926570ef700018d9000000000004b600019b080a04c54d58000000019400000005dc
  | 53 => 0x2a8143da85929cd1d3e0000000242ac3f51c000032faabc8f69c660001ec9372800000000000000000a84225a0000000000000000000000000000000041100000000001de80000fb40000000131c84f00000000000000aa80c1e00010a40002a4e91a14999d3000000001680001fa6000008f0001fd200000000000000000000095e2910000000000000000000000000238e0000edc0000000000111e00024c400000000000f6209400000f3c00000988d0000000000000002fb80005b40000000196d00000000000b820002b900002b869d10000000000083a400000014641e48a8dadb29d1000000000012e2179000037c03bb7879a3400023580ff80007ca9c6c31f895e0000b0e2d82f20ac24000827800000010fa9956db600000009e740928f0000028f59667591eac000017113d00000002b5a00000000770000000000000000000001fbf00008601df80002528000976a8590000000000000000000000002a9b000000000000004058000172000000015ba000192a00024000000d4e00021c2000000000000000000000000249c6038d5a00000005dc0bb200000004af800047f80000001f3000020762bf0156a43406e595e1b44c7800026100007c08000000157a00008bc1c2a01208382eaa5c00000000000000000000000004da9634b5c979e0f292646490a0e01de46667e20ac64bc00000000000000000000118859d80005ffc0005b001d0000000000000000002c9c78d00008251dd8000136800000000000bc80000000000000000000007ac0000000000002b8000000000004340000000000000000000000000001cb40002f10000000000000003550000000060d9c524b63e1873e032255a000000000000006b09efd2bf6109000017ea0ed59000014da2bec0009c0c7ae00000004a28000000000090c80000000000000202423900000000000000000000028410000000b5ea70000000000000ec0000000068c9e389ed25f64b3890600000000002d5400026ca00000000000000000000000000008e08000b6b800011898a802823620000110000000000016600001d1900000003ff8000ada8000000000000000000002bb8000000000015620001032000000000000000000000000079600000007020000000000000011a34e3400070e00000000000000000000000009aa800017b8000000000084e07d1000000000000000002b4a0001f92000000090580000002f408aa8000000000002900000000000000068246c06e44d8800000000002d400001e90000000000031080000000dae00025247d6800000002cf3638b6e661c68f0000000000000000000000001ecc0000940118000000000005180000448002956b94ec7262f0a1271bea97891c83cd00000000bd66c3e7da5a2000000027ea000020d00000000000000000000
  | 54 => 0xcc000005f4e20000000000000000000002dbc5ba9b4d000055c55040f67d200000002d760000000162892140528a96d29953ac68000000000000000000575c960d2c000000016c00010caa9684fe00000000000000000000000004386a791a400000000000911a25800000014144f783c30000000687863a0001e590c04000000000000000008c41279000000000028780000000000001a1a98000000116a0001a6000000000001bac0002abab1c000035e400000000006e50062000017c3a100000000000665c000ade811700012f8000000000000005b713db00016c70000ca6ae9ad044b08844000022e0ef8225000134e56c1f9700000000000000000000051ae8bb93800db00028383130d1f1000664a8a593e0d9800000000000000000b028ac85b8a08e00000006a8032235d90d718a400000000000000000000000037580001d84000000040662b0000000000082694a300000000000d86000239e000091c4f984761c88b5e1d68000301000000007b600000006ec881600000a86be00008ce00000002956000000000000000000000699149400019da00000000000d5ca7f8000000000098e0c4904d000043d8000000183e000000000000000a38000a72644000018c600028bc19e400000000006ca000000009ba000000058d800000000000000000000000000006ca8730000b9f0000000000000000000000000000000000028c200000007e7c0000002b41830000000000001aa40000000000000280e00000008f380000000ba8000018f00000002dc80105e500006c00000000000000004a191280000001b38a120642000000067a843b102504804e16457da0000000000000000007eb80000001d3000000009c4c000000000000000000000000000000000000004bb000000000000002f12000000040a971e000267c00000000000000000026e692800000000000000000000186c0000854000000000000000002e0a000052800012236cb8f507078000000000000000000000000892000044402900000192000000000010aa000000058000000000b9c00000000000000850000000007380000000550800000000000000000546e35200002800a600002f8000000000000000c96000134087b0000a8f000051a80000000000000000079524fb0ce1a186e5ad7000000000000a7c984800013d40004976b52971000000025fc0000a0c55100000002060000000000000001f20000000000000000000001b340002f1e239a88202fd88eb9d0f0e0000418000142e00000000000000449000000000002bc000000000004cb0000000090e0000e10000154c2a60000000000033b4a6c7b480000000000000000000000000000f740000000000000000004e4663c000000000082400000000000000000000028f80002b2e9f3a09276980008d
  | 55 => 0x273c0000000000164600340000000e447ad6eb6000118d00000000001e905e5856ca264596120953c87580000000000000106ea098fe6992c00070696a07ab40007fc8a32000028d00004789fa0000000000000000000000000000158a07124ea0000000000295a0000000a9c80000000671a3f00000000000000052600000005ee122400000000001c8a000130e000000076800000002c2f00001fc00000000002768604800000000000f5a7a69ac6b0e929eae05bd80002eb00000002b323c229f600000000002dad59501398eb18328b822b2281ad620000000983994a00000000000cb80000000000000078900000000bf069191e800011721ae000000000000001d980002966012c000b6bd3200000000000243800024dc182000003b933a0000000439400017f40000001ad4bc21828000000000017645ea07a000000008fc0000000182e0000000000000053500009a080000cb800038e00007cf800000000005e4800006299fc000025c00000004a91cb500029f766f000079a00002919ec7a448000000000000000000001f84000000000000000000000727992300000002dd981e0001dd0856000061980000000000000003a87d800000021d80c262625444000b3d80003a60000424810b1a380005d700007ab81ab000000000006960000000000000039e6edc00019400001c3e0000000000000000000000000000000169a000097200000006162d325adc4b20000000a380000000000020b24f47448000ac3400018f4a1e000000000024840000000000000000000006f680000002bba000000000000006c5a1d4000000000005082b500d80002be80000000000000000000007e8058622e486200000000000000000000000000000000000b1e06eea82000048ec0000000af883a977c06c80000002cea0002b2b078800000012ae000000099191c600a8b0800000008cdad28000278700000004772b31a31a4ca7f90b28a2b80007eda0842c3c0005010000000000053583bc00000000e014c000000000002efa0002e88a38400000009bc0000000000292a21acfde4582b923ae19ae0000000000000016fc00030c20be6bfc0006f8e192000085c7838a9a9282b13124985c0001fba6704f660e593900001ddc00015ef73180003278c9a46a66a68b0800000000000001ad23d2000000000000001ba80000000009664c00029da9418000000000075b0ce4387a66c9a4000098a1297000000000000000000000a2a0000000000000000006e0c00000000000000000000029416400bc144144a4752f008a580000000000a1c87681af8aa862780000000000000000065f6292000000000000002d3a6d6793919880e0416438e07c000000000000004c206c4b2b00000c689a8000265e6a68000000000000000000000de200014f80002b
  | 56 => 0x29e6350000618400037302b7b9829f5000000000005625e2c00000000000001a0619f40000002bd0b3f80005eb96bc000000064580000f04000000000000000000000a80000000011300003a7043c000000000015c0207a27055f000000000004bc577a00000007189526000075d3a98000000000000000000001e5d0001aba000000000000000000f4c0000000000223200006aa56322548312d9fba14000000122000000004062e8300000002ee9ce40934000497000000004270000000000125f6f72b4000028366d11b3a0000000000000000000000002c4700004960000964a8a2928865c00000000000000000000000000000005c1ae9e00000820002d3e2730c1100000007d8d495000000000000000000000860000058c800000000007cf16fc4ab000000000000001ef600001320002c7e50853fe63d29cc36f87c600025bebcb00006ff014900000000000000000000028880002b680007e380001a162cca6720040000a7e6ee800000000001088000000000000024460000000000000091d00000001957ba680008068b9843d00008308ff65fd93163d6164193e88000000000000272600012497910d2b00000002de000041928e800000000634000ad9c00032a0000632888100003b675500000000000000000000000000000000000000000000000000000000000007a9acd0000000000000000014960000000000000000000000002847000075c177ade2000000000000000000000000000048cc0000000000adc994d16f1bf08670000000000000015686cda4f000021883b209200000000000000000016940001c30025262e0fe05500000000000000000000008c22a24008800063994e3000000000000008c8800045eac8200000000001afa4cc000000016c30000000000000020980000001d60000091e00002260b8231f0000eb4000205c80b8000191000085918480000a7000000000001ef457380000000000000000000018d800000000f380006f919aa4d500009149be984c80000000a6100000000002bdcb03000000000000000000000000049200000000000000033000000000000000000000000000002d9000022980000002380000014800000007a89c2e8c700000000000151e0aeae21934939000000000008912dd001580000000000175da9435a00b30002ba23cb8000000248e000000000000004031d276f9c000aa380000000000066000023f97cc0000000000000000000000000000588a6620000000557a6c824a4000000000000000000002d4a0c8ca9400000000a225101a462f72909e980000000000000000019790000000000000077f2bb07a5a5ca66d1e269ee9aee44ca0d22e200000002cca000000000000005121e480e6a50c9c5800000014760000000000000045ddea60234a48000000000010460
  | 57 => 0x2c32000227250888fa4350000007a68003a8000000000038b80000002d1e000041495223ea4aeda7c0000000000000000000000001a26713000073080000002e8e00000000000000000257e05380006a39d6828ec00000026150001664000000000013806f566990000cda892871e0000000000000056c8000000000000000001c193240000000000000000000008f203050002e6a3e510f80000ade000034a0000000a374000000197b00012b083812d300000003591cbcb28000077025b81bd800000029843b1149ca8fc0000002c6667da374000000000000000001c800000000b8680005b14af29fe141800004d6000000000015c300000000000000000009d0000052000000000000006232b9614ba9940000000afc8000a28c0006c15b78000143042180000002a7478eef0e3af00000000000a72048ab31800086d8cc431780000da800000002bf000000047a400000000000001e49000287c2e380006f1800006a40003c000003555945393a6220000000117d6f800000000000000223a1202e900000000000592800064500007ec00000002ec0000089a00000000001a9544700000000000492c000000000090f00000001bd65208000143000050f0000297800079d131424cd8d207cde4daabad5a000000074463f455a9681000000000025ce000000099ba84b007190c814000000000000000000000097e16ac000a88ddfe75d1f28000000065c278464440005529ba061c80001844f968ec29d90000000000237600000003f693a40bf00006e0a7b61008741000285600023306f5050619d00008cc800066cdd7c283515c000000000012f200000960001ca40000000b9996620000000640c0000000000000000010d195f0001ac00002a0e2b9800078880000ea80000001e840002b98000000000013d996a800056493f263a800000003ba000031648780008dfa1d20000f5e1a300003ba00000002cba6dc9b8e000000026303620002b9c2ae02009d00cf5987a61a00000000002e752c98000aad030c088136ca1e9b4866a2afc52283a846b000044a80007f1aa8c7008630a07000062a800000025bc00024029c7000004814e52d315cc91aa2825e392662d9ad186b58266000000000019c274a0000620424f00012524600868000077800010ed0d7c00021587766d64000000000000000001f61a10a7d26660e7800000000000000f780002ada150226c000112c00000003718000000000000012aa19d527a0000000000157e01740000001360129022471d245c1451fda000142699200000002d1c00000001dc8000929000000011e575e8000b0e07aa08a00008c2e52a537a10400000000000000000000000000005c206e02e319838c826e82e40fc65999e6a0000bfe000000000000007d800000000000000208c0000
  | 58 => 0x285b7fa1fb4a21914478105710278000000285200016780001a6b9020c38000054600023d20000000944a71e00000000000000000000077c8000000000000000007af000000004500000000000070db2980000af2a1400012f7228e0f8b8def3a8521ba28121d08809cabc611af1c3f39ed62d1800001100000001db600010e00000d9400022d761f2c8607518733a5129286800001f4952a5490d80000218b00000000d3ac1b80883da41a972c9b900003cd699200005f637526f37e629d780600a61ee800000006e7484659018da13700019e28a6c0000bb0000000000000000000000000407c00000003655f10000469a22800329bc0001c4e982de89000000000010e600000006018000000019c2884000000270c3488cb6000291a3a29df6000000000000000a9800012b8da40001606000000003016440faa34062d80006d80000880000000000000000000abb800000016f40000000000000045b06a4049800000016f20002bda0001222650645000029a80002c2e0eb69b410681ac0000000000124257980000000ab00002b24b6813f500000009618000000168034700002e980007ee5428034800000000009548000a2d000071098e0000080446d0b3e708976e0002b34afb5fc000000000000000293e5d8000016e0002ec6000000000000000000982b07196700013b869400000002a0990a94b228f8000a3104a5000000099f800039c5b20000000000000000000000424000065a00000000eed0000000550000090700000001aad3c70000918a344000000041c8000745a3149d8000000015b4994591c3dc9fc40001a0a5d3800032ba30a48b400000002762e6800028b00000002aa80001bc80000c06000000000026fa00000000000000000000000000008c6ebe400000000000000521800000000000000ae20000ae000016b90000c9484680000000000000000048f18160000000ab58000000000085400009bb9cc8000198e0001246b5140000002830000000000000000001c2d9df00000000000000000073a80000000000000000098100000002d94000000000000002809e8c1999f0e685c000000000000000005438000ad64000bc682425a700008a800002f840000002e6e012800000002e31fea634ba400001d5000007e8000880800000000000000000000000000000007fe0bd800000000001b4700000003d926b00000a767d0902c61900acb2c8000000000049781cc1ea4f5209f0c720001490a3da74aafd1e4600013fa4d100000002afe194a339aeb8000a550000718000000000000000f760000cf7095923485140000000000000202c933c00024a0000333800016692d8615000085fa4f20000000000000081f800000000000000000b40aa04176000000000006f5c000000052191f94b416f99ce74aa20a0000000
  | 59 => 0x9c8000000014aa00000000000000000000000010eb00000002ba1b68bb900000000000000067c89396240002ee27db80000000c285a3dec0000147100000002c68000000000000000000000000000225b4ef000000000004d18ff5381ad8661b8000000105e802875f000000045d000000015d02ee63fc9b49e620000bbb000284c7e0d8a000000008640f281e9800000017481680000bd3c0000001b6e69780000001215000000000015ac0000000000000000017ee0001d21b9f8ad06778000040000000000000002290a8e136e47c807b1d100000002b020acc00000001db00014340002d604b22a68a84939a27f00002f700001904000000000000000000000b2c5cd000000000000002855000273612b27781174000000000000000000000da80000000818aaf625c1a120000000ab500005e040000000b2a4f80ef800000006c09cf2b9a0000a72aa483df40000000fc23ce26f6a9894a64a882355bbaed21a10cd62c91e860000bbe2c041500c2e0e492e441e8af80d549d641d7a06a76112147977b01731c15c189a300003a06b37087a96e077ac369b6162c2728000000000000000000000000000000000029ee000096246700009820fba000000000003480000000000000040719dc0000000000236a242256c1f8951d4f51d6e318af4e5d31d2293c671b9c6549a000000000000008bea5349e880009a4945215e1772000000086512806659ee700000000000000143c00000000000000000bd886980000cc60e200001664000000000000000006b99598000016008a5e2c4170000000000028b80000000000a2700000002f64000000000000000000000000044200000000002ded0000000000000000000000000000b79229e0000000000000073b000060f400027100000000000000000000022bc03368d80000000454400000000000000000000000000015a0000140000000000000000000000000000009ea5ea000024fc00024064de00000000000000175a00000001a4800026c80007fb80000000000000000000000007e680006338000000061a000000000028cc95295aa0000166000000000019d868c0000000000000006e8000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x846f769484004236bb4a4200219398e5210010c9ac7290800846f765484004236bb2a4200219398d5210010c9ac6a908008635549844004333294c2200219954a6110010c6ca8b088008635545844004333292c220021995496110010c6aa930c4008655539862004332a94c3100211ddd56188010c6aa8b0c4008655535862004332a92c3100210f9d3650801087ae9b28400845e73d94200422eb9eca100210f9d2650801087ae9328400845e73994200422eb9cca100211d5c5650801087ce8328400843d74194200422f398ca10021175cc650801087aeb320400843f75590200421fbb4a8100210f5da540801087eecaa0400843d76550200422ebacc610021879526308010c3aa9318400845f7558c200430f2a2c6100218755163080108beed298400845d7694c200430f324a6100218759253080108beeca98400845d7654c200430f322a610021875915308010c5cc9290400862d64948200432731ca4100219358e5208010c5cc8a90400862d64548200432731aa4100219358d5208010c6ca9308400863554984200432b29cc2100219554e6108010ccaa5308400863654584200431aaa2c2100219594d6108010caaa6b084008666525842004332a92c2100211d5db54c4010acae5aa6200847576d4b100429aba6a588021555cf52c4010e4aa929620087265454b1004392aa2a588021d194d52c4010e8aa6a96200847576946100431cb2ca9080218e5955484010cd2cb29420086696554a1004394aa2a508021d254d52840108f2ed28c200843e76951100421e3b4a8880210f9d95444010878ecaa2200862e54d891004316aa6c4880218b9506244010c5aa8312200846e7694910042363b4a4880218bd925244010c58c9292200864f63949100432631ca4880211b9d952440108d8eca92200862f645491004316322a48802193d8d5244010c98c6a92200863774d95100431a3a6ca8802199dcb6544010cc8e5b2a200863765d91100431bb28c8880211d9db5444010acae5aa2200853575951100431bb2ca8880218dd955444010a6cecaa22008534765511004333b2ec488021c95536244010cceca31220086a4641891004392aa0c488021b118c62440108eceda92200853574d4910042aab9ea488021595d65244010ccecb2922008725549491004333b2aa488021c99515244010e4aa8a9220087465354910043a2a9aa488021599d95244010ac8eca922008727645491004392322a488021d1d8d5244010e88c6a92200863554d811004332a96c0880218edd36544010c70e9b2a200866b72d951004334396ca880218ed976444010c76ca322200863b65951100431db2aa8880219ad976244010cd6ca312200866b659491004335b2aa488021ca5515244010e92a6a92200847a769451004398aa4a288021d854a5144010
  | 1 => 0x420422eb9ccb21021179cc65908108bae632c840847671196420422f39ccaa1021175ce65508108bce632a840845d73195420423b388caa10214b1c95450810a58e8a92840847575d85420431aaa6c2a10219554f6150810ccaa5b0a840847575185420431aaa0c2a10219554c6150810ccaa430a840845e73d94420422eb9eca21021179ce65108108bae7328840845e73194420422eb98ca210211d9c465108108f4e0328840852d72950420422ebacc621021879526310810c3aa9318840845f7558c420430f2a2c6210218755163108108beed298840845d7694c420422fbb2a621021175d95310810a5ae9290840864e639484204326b1ca4210219398d5210810c9ac6a90840852f755084204296baa84210218bd954210810c5acaa10840868d63508420438729a8421021c354d421081087ce932c640843d74996320421f3a0cb190210f5d0658c8108ece232c640843e74995320421eba4ca990210f9d0654c81087ae832a64084767119532042a639aa4990211d5d7614c810c6aa9b0a640866552d85320423aba8c2990218d550614c810ccaa430a640843e74d94320421eba6ca190210f9d2650c81087ae9328640843e74194320421eba0ca190211d9c4650c8108f4e0328640843d75990320421fbaac8190210fdda540c81087aed2a0640843f76550320421ebb2a8190218b992520c810c5ac9290640854d739483204317322a4190218b591520c810a9eea990640854d754c83204327b2a641902193595320c810d1ac8990640870e544c83204386aa264190211b9ca64944108dae5324a20843e7498a510421eba4c528821179ce62944108bae7314a20862e5498b4104316aa4c5a08218b95162d0410c5aa8b16820846f7694b4104236bb4a5a08219398e52d0410c9ac7296820846f7654b4104236bb2a5a08219398d52d0410c9ac6a968208639545824104334a94c0208218e9516010410cd2a4b00820843f76953210421ebb4a9908210fdd954c841087aecaa6420861e5498f210430eaa4c7908218795163c8410c3aa8b1e420845f7694f210422ebb4a7908218799253c8410c3ac929e420845f7654f210422ebb2a7908218799153c8410c3ac8a9e420862e6494b2104316b24a5908219398e52c8410c9ac7296420862e6454b2104316b22a5908219398d52c8410c9ac6a96420866952582210431caa4c0108219654e6008410c72a8b004208659535802104335292c0108210fdd16194010878e8b0ca00846f725865004236392c3280218d5526190010ccaa530c800847775586400431aaa2c3200219954961900108dce5b28800846d72d944004237394ca200211b5ca65100108eae2b28800846e721944004236b90ca200211b5d66210010c5ca9310800862d549884004237baac4200218b9516210010c5aa8b1080
  | 2 => 0xa4102218b5905208110c9cc6290408864d63148204431baa4c2102218d1526108110caea73084088654539842044333a94c2102219914a6108110c6ea8b08408863454584204432ba9ac2102219514d6108110ccea4b084088664525842044272bb44210221999962108110d4ac910840886c56388420443922a0a508221d114c5284110c9cc7316a80864e6358b5404326b1ac5aa0219958a61d5010a5ce5aa4a80852d72d52540428f398c52a021475cc6295010c5ac4314a80852e721825404296b90c12a0214b9cb6455010a5ae5b22a80845e73189540422eb98c4aa0211b9cb61550108dae5b0aa80853471589540428f398c4aa021475cc6255010c5ac4312a80852e721815404296b90c0aa0210fdd95415010c5aa9310a80862d545885404317324c42a0219398e6215010c5cc8b10a80864e635885404326b1ac42a0219998a6115010ccac5308a80866962980540430f2a4c7a90218755263d4810c3ca8b1ea40861d5458f520430f324c7a90218759263d4810c3cc8b1ea40861d6458f520431ab24c3a90219558e61d4810a5ce9a94a40852d74d4a52042a739ea529021535cf5294810a9ce7aa4a40854d73d5252042a7398a929021535cc5494810a5ce9a9ca40852d74d4e52043872a4a729021c35525394810c5ac8324a40854e7319252042a6b98c9290214b9d06394810a5ae831ca40864d6318e52042973a0c1290214b5d06094810a9ce6304a40854d73182520422f398c8a9021175cc645481087ce831aa40843d7418d52042973a6c4a90214b5d36254810a9ce7b12a40854d73d89520421f3a6c2a90210f5d361548108bce7b0aa40845d73d8552042373b6a8a9021539cf5454810a9ae7aa2a40846e7615152042a7398a8a9021535cc5454810a5ce9a9aa40852d74d4d52043872a4a6a9021c35525354810e1ca8a9aa40870d5454d52042b238ac8a90218b5906454810a9ce6322a40854d7319152042b238ac6a90214b9d06354810a5ae831aa40864d6318d52042973a0c0a90214b5d06054810a9ce6302a40854d7318152042973a020a90214b5d01054810a9ae6082a40843d76950520421fbb2a829021879526314810c3aa9318a40861e5458c520430eaa2c629021175da5314810c3cc9298a40861d6494c520422fbb2a629021879915314810c3ac8a98a40862e549885204316aa4c4290219394e6214810c9aa7310a40846f765485204317322a4290218b5915214810c9cc6a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204317324c4290218b5926214810c9cc7310a40864d63988520431b324c2290218d5926114810cacc7308a40865563984520431cb24c0290219658e60148108bce732e840845d73997420422f398cba1021175cc65d08108ece232e840845e73996
  | 3 => 0xca610c9108e8eab08648866852980324423c3aac019221b24c9600c9108dceb316828862f5498b41443162a4c5a0a211b1d562d0510c5ea8b16828862c5458b4144237bb6a5a0a211b5db52d0510c9cc7a96828864d63d4b4144237bb0a5a0a211b5d852d0510c9cc6296828864d6314b414431c2a4c1a0a218d9975490510e48a9a9482886666514a41443922a0a520a21d114c5290510a68eaa14828863b54181414431a32ec8a0a211d9d85450510e48a82928288744531494144272b90c0a0a21acd906050510c68a930882885347550441443922928220a210f9d664c8510878eab26428843f76d53214421ebb6a990a210fdd854c851087aec2a6428845e7598f214430faa4c790a218715263c85108b8eab1e428861f5458f214430e2a2c790a2117ddb53c85108baeda9e428861e64d4f214430eb26a790a2117dd853c85108baec29e428861e6414f214430eb20a790a218b99352c8510c5ac9a96428864e63d4b2144326b1ea590a218b99052c8510c5ac8296428864e6314b2144326b18a590a219a14a60c85108ecebb2442884d573d92214431b328a910a211d9d7638851096ae9b1c42886566514e214438a2a0a710a21999975288510e4ea829442887245414a21443a3a98a510a21d114c5288510ac8eaa144288564754ca2144335a90c090a211d1d564485108e8eab1a42887145414d214433232ec490a211d9d85248510e48a8292428874453149214425aba0c090a21355cc6048510dc6c430242886645298421442b23aa4210a21c91512108510e88a6908428863454987404429a3aa83a02218d99641901108dce5b2a808846d72d954044237b92caa02211b1c96550110cc8a5b0a8088637541854044332290c2a02214d1d54150110b60e0a0a808862f5498840443162a4c4202218bd516210110c58a8b10808846f76d484044236bb6a4202219398f5210110c9ac7a90808846f761484044236bb0a4202219398c5210110c9ac6290808863754984404431a2a4c22022199d4a6110110cc8a5308808863754584404431a2a2c22022199d496110110cc8a4b0880884b576904404431b32c8220221a958a4110110cc8a530e408856475487204433332c43102210f9d3654811087ae9b2a408845e73d95204422eb9eca902210fdd16548110878e8b2a408845f73595204422e39aca902218d1536148110ca8a7b0a408863454185204432a298c29022199d486148110ac8ea90a40885e070485204421fbb6a8102210f5db540811087eec2a0408843d76150204430faa4c610221871526308110c3ea8b18408861c5458c204422fbb6a610221175db5308110c3cc9a98408861d64d4c204422fbb0a610221175d85308110c3cc8298408861d6414c2044317326a4102218b5935208110c9cc7a90408864d63d482044317320
  | 4 => 0x98c7b12a48863464d85524432a31ec2a92211bdd95214910a5ee8a90a48852c7454852442a7b9aa429221531cd5214910a5ce9310a48852d7498852442a739cc429221535ce621491087ce8300a48843d74180524422f398c029221175cc6014910c5ccbaa0a48846d7695052442a739ca829221535ce54149108deecaa0a48854f7355052442a639aa8292218b9945414910e4ae22a0a48864e65d4c5244387aa6a629221c315353149108daed298a48852e7494c5244296ba4a6292211bdd95314910a5ee8a98a48852c7454c5244387aa0a629221c31505314910e4ea8b08a4887245458452443a3a9ac229221d114d6114910acae3b20a48862d6419052442a7398c829221535cc6414910acae2320a4885697019052442b2b8ec6292214b9d06314910a5ae8318a48864d6318c52442b2b88c6292215a5c06314910a5ce9b08a48852d74d8452442a739ec229221535cf6114910ccac3b00a488665615805244297ba220292214b1d11014910a9ee6880a48854c73440524422f39ecba1221175cf65d09108bee6b2e848845c73597424431a2a4c3a12219514e61d0910ccea530e848847475587424431a2a2c3a12219514d61d09108bce7b2c848845d73d96424422fb9acb21221171cd6590910c6ea930c8488654539864244332294c3212211d1d56190910ca8a6b0c848866452586424422f39ecaa1221175cf65509108bee6b2a848845c73595424423bb8acaa12214b9cb5450910a5ce9a92848845e73d94424422eb9eca2122117dcd65109108b8e6b28848845e73194424422eb98ca212214b5c854109108bceb318848861f5498c424430e2a4c621221171d56310910c3ea8b18848861c5458c424422fbb6a621221175db53109108beec298848845d7614c424432731ea4212219358f5210910a5ae8290848864e631484244326b18a4212214b9d54210910a58eaa10848862e65508424431632a8421221a358d4210910e1ea6a10848870c53508424431a2a4c2212219914a6110910d4a85308848847475584424431c2a4c0212219a14a60109108f0eab0084886a942580424421f3a6cb192210f5d3658c91087ee8b2c648843c74596324431a2a4c31922195d4e618c910cc8a530c648847475586324431a2a2c31922199149618c91087ce9b2a648843d74d95324421fba2ca992210f1d1654c9108eee2b2a648854e73d49324421f3a6ca192210f5d3650c91087ee8b28648843c74594324421f3a0ca192210f5d0650c91087ceb320648843c75590324421fbb6a8192210f5db540c91087eec2a0648843d761503244317326a4192218b593520c910c5cc8290648862d6414832442a6b98a419221539d5320c910a98ea990648864e654c8324432632a6419221a3591320c910e1ea8990648870c544c83244332294c219221b14
  | 5 => 0x861e6458c528430eb22c6294218b5926214a10c9ac7310a50863664584528431ab22c2294219598d6114a10caac6b08a50845e73197428422eb98cba1421179cc6590a108bae632c850845f73595428422e39acaa1421179cc6550a108bae632a850852c7255142842963a2a4a1421179cf6510a108bae7b28850845e73194428422eb98ca214218bd954210a10c5acaa10850868d635084284354a12c0214210f9d0658ca1087ae832c650843f74595328421e3a2ca994210f9d0654ca1087ae832a650854c73549328421f3a6ca194210f5d3650ca1087ce8328650843d741943284327b2a641942193595320ca10d1ac899065086c93258032843172a2c5a0c218b55162d0610a5ae42a4830843e76951418421ebb6a820c214b5c85410610c5ac9296430864d6394b2184316b22a590c219358d52c8610a5ae8294430854d7314a21842373b4a490c211b5db5208610a5ae8290430854d731482184296b90a9a04210f9d85450210a5ae42a2810843f7655040843172a2c4204218b5516210210c6ca8b088108635545844084296ba0a590421535cc52c82108dcec292410852d7414920842a6b98a4904218b5925208210c9ac7290410846f765482084316b22a4104219358d5208210ccca4b08410866552584208429bba2cb8842159dc965c42108bce7316a88845d7398b544428f39cc5aa221475ce62d5110c5ec5316a8885357118b5444297b92c3aa2214b1c961d5110c5ea9314a88862f5458a544432731cc52a2219398d6295110c9ac6b14a88862f64d895444327b1ec4aa2218bd906255110c9ec6312a88864c631895444332316c2aa2210fdd95415110a5ee4aa0a88852c725505444297394c82a2214b5ca64151108dce4300a88846d72180544429ab8ec42a221479cc6215110a3ae6310a88862d62188544429ab88c42a2214e5c06215110a5ce5b08a88852d72d84544431ab0ec02a2218d58560151108bce7326a48845d73993524421f3a4c7a92210f5d263d4910a9ce72a6a48854d7395352442a7b9aa9a9221531cd54d4910e4ae22a6a48870f54d4f52443862a6a7a92218bd9264d4910a9ce7326a48854d7399352442b2b88c9a92214b9d263d4910a5ae931ea48864f6398f52442b2b88c7a92214bdd161d4910a58e8b0ea48854f7358752442a639ac3a922187d526394910c38a931ca48861f5458e524430e2a2c729221879935394910c3ac9a9ca48862e64d4a5244316b26a5292219398f5294910c9ac7a94a48861e6498e524430eb24c729221879916394910c3ac8b1ca48843e76d51524421f3b0a8a922187d536354910c38a9b1aa48861f5418d524430e2a0c6a922187d935354910c38c9a9aa48861f64d8d524430e326c6a922187d906354910c38c831aa48862f64d895244316326c4a922193d8f6254910c
  | 6 => 0x83872a2a690041c35515348020c5aa830a401064d531852008333b2ca290041c95525148020e8aa728a4010664615452008333b2aa290041c99515148020e4aa8a8a40107465354520083a2a9aa290041991d95148020c5aa9b02401064d53d81200831db2ca8900418ed955448020cb6cb29a401065b6554d2008394aa4a490041d254e5248020ce6cb28a4010673655452008398aa2a290041d454d5148020ec4a4a8a401045e7398b54c422eb9cc5aa6218bd516295310c9cc7314a98864e6358a54c4326b1ac52a6219998a6195310ccac530ca98843f7655054c4296b94c82a621179ce64d4b108bae7326a58843e7498f52c421eba4c7a96218b5935294b10c9ac7a94a58861e6498e52c430eb24c729621879916394b10c3ac8b1ca5886366498652c431ab24c3296219598e6194b10caac730ca58846f7654852c4296ba4c429621535ce6214b108bce7b2e858845d73d9742c431a2a2c3a1621179cf6590b108bae7b2c85886645258642c422f39ecaa1621175cf6550b108bce732a858845d7399542c4297396a8a16214b9d35250b108bce7b28858845d73d9442c422f398ca21621175cc6510b10c5ccaa10858862c6550842c4346b1a8421621a950a6110b1087ce9b2c658843d74d9632c4332292c3196210f9d3654cb1087ae9b2a658843e7499532c421eba4ca99621539cf524cb1087ce9b28658843d74d9432c421f3a0ca196210f5d0650cb10c9cca990658864c654c832c4346b226419621b14ca610cb10c5ea8b16838862c5458b41c4296b94a920e21695ca549071087cec2a283884e572d9541c42d8b86a8a0e211d9d8545071096cec2a283884e57218141c4296b94a820e210fdd95410710d6282b00838862d64d4b21c4326b1ea590e218b59052c8710c9ac6296438852d7494a21c42a6b9ca510e21355cf648871096ae9b1c43885a57494a21c42e2b9ca510e211b9d8524871096ae9b2a43884d573d9521c42f0b86a490e211d9d852487109ccec29243884b57418121c426ab98c090e214b5d25208710a9ae7290438846f7654821c437090ac010e214b5ca54d031087ced2a2818852d7295140c421ebb6a8206218bd516210310c58a8b1081886375458440c425abb48220621a958a4110310a5ae9296418854d7394b20c42373b4a4906214b5d25248310a9ae7292418846d76d4820c4316b26a4106219358f5208310c5ac8290418864d6314820c4333a92c210621395da2108310d4ac910841886c56388420c422f398c4aa421175cc625521087eecaa0a90862d54588548432731cc42a4218b9916215210c9cc6b10a90864d635885484333312c22a4219958961152108bce6322a50845d73191528421f3a0c6a94210f5d06354a108deeca90a50862d645485284326b1aa429421879926314a10c3ac9318a50
  | 7 => 0x710841595c75388420c9acb29c421070d5494e2108326b2aa710841c39515388420e1aa8a9c4210665659462108392aa4a310841d154e5188420e4ca8a8c42107255454621083a329aa310841d154d5188420c5aa8b04421064d535822108332a8ac1108418e5526008420cb2a7300421063954580210832ca9ac0108419c9456008420a9ae7aa0421056571d502108296baca8108414b5d35308420acae3a98421054d7594c2108386aa4a610841c39515308420e1aa8a98421062d549842108326a9cc210841595d66108420e4aa93084210745539842108392aa4a210841d154e5108420e4ca8a8842107255454421083a329aa210841d154d5108420aceeca884210667765442108394aa4c010841d254e6008420c5aa8b00421064d535802108394aa2c010841d254d6008420dc4c2b00421046d760865008316aa4c5200419354e62900208deeab14801062d5458a4008326a9ac520041999895190020ccac4a8c801045e73d94400822eb9eca20041179ce65100208bae7328801045e73194400822eb98ca20041175d66310020c3ca9318801061d5498c400822fbaac620041879516310020c3aa8b18801045f7694c400822ebb4a62004117dd953100208baeca98801062d54988400832729cc4200419354e6210020c5ca8b10801062d54588400832729ac4200419354d62100208eaeb308801063654984400831aaa4c2200419594e6110020caaa7308801047775584400831b2a2c2200418d5516110020caca6b08801065553584400823abb4a2200419598e5110020caac72888010666629444008332b14a2200411ddd95110020cacc6a888010655635444008333312a220041995895110020c5aa9314601064d5398a3008237baac5180418b551628c020c9aa6b146010666625463008332b12a3180410f9d2650c02087ae9328601043e74194300821eba0ca180410fdda540c02087aed2a0601043f76550300821ebb2a8180418b952620c020c5aa9310601062e545883008316aa2c4180419394d620c020c9aa6b10601047576944300831b324a2180418d592510c020cccc5288601066562944300823bbb2a2180418d991510c020c6ac8a886010666625443008332b12a218041535cf54c8020acae3aa6401052d74d4f20082b2b8ea790041c355253c8020e1ca8a9e401070d5454f2008316aa4c3900419354e61c8020e4aa928e4010745539472008237bb2a3900419998551c8020e4ca8a8e40107255454720083a329aa390041d154d51c8020cceeca8e401046d7694a200823cbb4a510041cc5515188020ea2a6a8c401046e76d5120082a6b9ea890041595c75448020a5aeb2a2401062f659512008317b2aa8900411b9db5348020a5ae9a9a401056571d4d20082a6baca69004193d965348020e1aa929a401064f6554d2
  | 8 => 0x96354420acee4a1aa2105647250d510838aa1886a8841599c84354420acae421aa21053674989510829aba4c4a8841559ce6254420aaae7312a2105567310951082aab9884a8841c95084254420ae4e0212a21057170109510829b3a064a88414d5d03254420e8a64192a210572700c951082b8b8064a88414d9d06054420a6ae8302a2105567318151082aab98c0a88414d9d02054420a6ae8102a2105567308151082aab9840a88410f5da541442087eecaa0a21061e5498c510830eaa4c628841879516314420c3aa8b18a21045d7694c510830f324a6288418759253144208beeca98a21061e6454c510830eb22a6288418d9526114420c6aa9308a21065653984510832aa9cc2288411ddd95114420c6cc8a88a21063564544510832b31aa2288419558d51144208bce7b2e821045d73d97410822f39ccba0841175ce65d04208baeb31e821061e5498f410830eaa4c7a084117dd563d0420c3ca8b1e821061d5458f410822fbb4a7a0841175da53d04208beeca9e821045d7654f4108316aa4c5a08419394e62d0420c9aa7316821062e5458b4108316aa2c5a08419394d62d0420c9aa6b16821065663947410832ab1ca3a08419998a51d0420ccac528e821065663547410832ab1aa3a08419998951d0420ccac4a8e821045e73996410822eb9ccb20841179cc65504208bae632a821046d75d894108316aa6c4a08419354f6250420c5aa8312821064d531894108333b12a2a08419918951504208bce7328821045d73994410821f3a6cb988410f5d365cc42087ce932e621043d74997310821ebacc9988410fdd564cc42087eed2a6621043d76953310821fbb2a9988410f5d954cc420c3cc929e621061d6494f310830f322a7988418759153cc420c5ca9316621062d5498b3108326a9cc5988418b95162cc420c5aa8b16621064e5358b3108326a9ac5988418d99251cc420c6ac928e6210666629473108332b14a3988418d99151cc420c6ac8a8e6210666625473108332b12a3988410f9d2658c42087ae932c621043e74195310821eba0ca988411b5d7624c420c5aa9b12621064d53d893108316aa0c4988419354c624c420ccec4a8a621066462545310821f3a4ca188410f5d2650c42087aeb326421043f75593210821ebb4a9908410fdd954c84208baeb31e421061e5498f210830eaa4c79084117dd563c8420c3ca8b1e421061d5458f210822ebb4a7908418799253c8420c3ac929e421045f7654f210830f322a7908418759153c8420c5ac9296421064d6394b210831b324a3908418d59251c8420cacc728e421065563947210831b322a3908418d59151c8420cacc6a8e4210655635472108338a8ac190841999c565884208daedaa4421054d73d5221082b2b8ea9108418b5965488420c5acaaa4421046d76d4e2108296ba6a
  | 9 => 0xaa8b08a610655535845308317324c4298418b5926214c20c6cc9308a610635649845308333314c2298418d9916114c20c6ac8b08a610666625845308338b0cc0298411d9c665d0c208eae332e861047671197430823ab88cba18411d9c66590c208eae332c861047671196430823ab88cb218411d9c66550c208eae332a861047671195430823ab88caa1841471cd5450c20a38e8a9a861046d75d894308316aa6c4a18419354f6250c208daea312861062d541894308326a98c4a18411d9c66510c208eae3328861046d72594430823b388ca218411d5c46510c20a3ae72a0861051d7494c430828fbaa8621841475d54310c20c3ecaa18861061d6550c43083172a4c4218418b5526210c20c9ca7310861064d5398843083172a2c4218418b5516210c20c9ca6b10861064d535884308346a1ac4218418e55160908208bce7b28841045d73d944208296b92a821041175d66310820c3ca9318841061d5498c420822fbaac621041879516310820c3aa8b18841045f7694c420822ebb4a62104117dd953108208baeca98841062f655084208316b2a8421041a358d4210820e1ca6a10841070d53508420831d2a2c0210419654d608c82087ce9b28641043d74d94320821ebacc8190410fdd5640c82087eed2a0641043d76950320821fbb2a8190410f5d9540c820c3cc9298641061d6494c320830f322a61904187591530c820a9ae4a98641064f654c83208326b2a6419041a3591320c820e1ca8990641070d544c8320832d29ac0190418795263d4420c3aa931ea21061e5458f510830eaa2c7a88418799253d4420c3ac929ea21061e6454f510830eb22a7a88414d9d35194420a6ae9a8ca21055673d4651082aab9ea328841179ce64944208bae7324a21043e7498e510821eba4c728841559cf5494420aaae7aa4a2105567315251082aab98a9288414d9d35394420a6ae9a9ca2107165494e510838aaa4a728841c59515394420e2aa8a9ca2105367414e510829aba0a728841c95506294420e8aa6314a2105567399251082aab9cc928841599ca6494420a6ce931ca2105357498e51082b3394c728841c550c4394420acce421ca2105657210e51082ab3988528841555cc4294420e4a84214a210536740ca510829aba06528841d14c83294420a6ce8304a2105357418251082ab398c128841555cc60944208ecedaa2a21055673d5151082aab9ea8a88411d9d85454420aace62a2a21055573151510823b3b6a6a88414d9d35354420a6ae9a9aa2107165494d510838aaa4a6a8841c59515354420e2aa8a9aa2104767614d510829b3a0a6a88414d5d05354420e4ca8312a2107255418951083a3298c4a8841d154c6254420aace7322a2105557399151082b3394c8a8841591c96454420a6ce931aa2105357498d51082b3394c6a8841591c
  | 10 => 0x64c654c831483a2990a218a41b24c9600c5208dcebb2642904cd73d93214831732cc990a418b99564c85208dcebb1e42904ad74d8f214832732cc790a41a359263c8520c9ccab1e429068e6458f2148346b22c790a418b59051c8520c9ac628e42904ad741812148266b98c090a412b5d2620852099ae7310429051d7315340483162a2c5a02414b1d542d01208bee6b2a809051d731514048266b98c4a02414b1d54250120c58caa12809051d7414f304832629ac5982410fdd1654c120878e8b2a60904ad74189304832632a64982416a5d321c8120b92e790e40904af745862048267b9ac310241995845188120c9ac7316a81065663987540832ab1cc3aa0419598d61d5020caac6b0ea810666625875408332392c3aa041479cf5495020a3ae7aa4a81053671d52540829ab8ea92a0418758c6395020a5ce431ca81051e7318a540828eb98c52a041479cf6195020a3ae7b0ca81052e72d86540828f398c12a041475cc6095020a6ce2304a81053571182540828f39ec8aa041475cf6455020a6ce3b22a81053571d91540822f39ec2aa041175cf6155020a58e4b1aa81061d6318d5408297390c6aa041479cc6255020a3ae6312a81051e73d85540828eb9ec2aa0414b9cb6155020a58e4b0aa81051e73181540828eb98c0aa0414d9c46055020a6ae2302a81043f76550540830eaa4c62a041875516315020c6aa9308a81063554584540830f324c62a041879916315020c9cc7310a81064d63988540831b324c22a0419598e6115020caac7308a81066662984540831b322c22a0419598d6115020caac6b08a810666625845408338b0cc02a0418d95261d4c20c6aa930ea61063654587530831aaa2c3a98418b59262d4c20c6cc930ea61063564987530831b322c3a98418d59161d4c20cccc4b0ea61066472587530828f3a6a729841475d35394c20aace3a9ca61055571d4e53082ab38ea929841555c75494c20aace22a4a61055571152530830eb20c929841539c86494c20a3ce8314a61051d7418a530828f3a6c329841475d36194c20a9ce5b0ca61051e74182530828eba0c129841559c46094c20aaae2304a61046e72191530828f3a6c6a9841475d36354c20aace3b1aa61055571d8d530821f3a6c2a98410f5d36154c208bcedaa2a61055671d5153082aab8ea8a9841179d85454c20aace22a2a6105557115153082a6392c8a9841875906454c20a9ce4322a61051e74189530828eba0c4a9841479d36154c20a3ae9b0aa61054e72d8553082a6392c2a9841479d06054c20a3ae8302a6105567118153082aab88c0a9841479d02054c20a3ae8102a61043d76950530821fbb2a829841879526314c20c3aa9318a61045f7654c530830f322a629841875915314c20c6ca9308a61063554984530832aa9cc2298418d9516114c20c6
  | 11 => 0x88297ba2a39044153dcd51c8220cccc2a8e411045f73587544822e39ac3aa24187d906355120c9ae431aa89064c63d89544832bb1ec2aa2419518f6155120c6ec830aa89065763185544832a318c2aa24199d88615512087eecaa0a89051c73550544829a38aa82a241875516315120c3cc8b18a89064e635885448326b1ac42a2410fdd161d4d20878e8b0ea69062d721915348316326c4a9a418dd936154d20c68c9b0aa69063764185534831a320c2a9a4199d886154d208beeca98a69051c7454c534830eb22a629a41551c55314d20c38e6b20a69061d6498c534821f3a0c429a410f5d06214d208ece3b2e869047571d97434828e39aa9a1a414d1c554d0d20a3ae829e869047671d96434823ab8ecb21a41475cc5490d208eee2b2a869047471595434821f3b4a8a1a41471cd5450d20a68e2aa2869045e7694d434823bb8aca21a411d1c56510d208dce4328869043d76d50434828eb98a821a41475d05310d20a3ceaa18869051c7550c434830fb2a8621a41875954310d20c5ea8b10869062c545884348327a9ac421a419314d6210d20d1a86b10869051d7315342482a6b98a9212411bdd95390920a58e8a9c84905647154e424828eb98a8a12414b9d76450920a5ce92a2849046e7615142482a6b98a8a1241635cc5450920a5cec2a2849062e761514248387398a8a12414b5cc5450920e1ae62a2849050d731514248297388a8a12411b1d95350920a58e8a9a84905647154d42482963ae86a1241c3d4f4350920a58eaa1a849070d5350d42482373aec2a1241335cf615092099ae630284904e5711814248346b1a8421241475d053cc9208dcebb2464904e571d923248237bb2a919241531cd548c920ac8e2aa4649052d7414e324828eba0a699241531cd544c920ac8e2aa2649054e75d8d32482373b0a6992414b5d0534c920b1ae829a649054e7614d32483273b0a699241c39d0534c920a9ae829a649070d7414d3248286ba0a699241539c4534c920a98eb21a649070f5490d32482a63aa8699241c3551434c9208dcebb0a64904ad74d853248256ba0c099241395c4604c920d1ac8990649047776544514829a3a2a228a41551cd5114520acae3210a2905677150851482b2b8c6428a4159dc532145208bce632e829045d73197414832b31ea3a0a419598c51d0520ccac428e829051d731524148266b9cc520a414b1d54290520c5ccaa14829045f73594414822e39aca20a41179cc65105208bae6328829051d7315041483162a2c420a414b1d54210520c58caa108290725421444148354a12c020a410f9d065cc52087ae832e629063664d47314831b320a398a419958851cc520a3ae829c62904ad7498a314832732a6518a410fdd1650c520878e8b28629043e74194314821eba0ca18a41475d0530c520c98a6b106290
  | 12 => 0x21641875516310b20d1ac6a1085906a94258042c8272b8ec9196414b5d0538cb208deeab0c659046e76d5132c82a639aa899641725c3534cb208dcec29a659052d7414d32c82673b0a699641635d0534cb20a9cec29a659064e7614d32c83873a0a699641535d0534cb20e1ae829a659050d7414d32c82a7388a699641d25c0534cb20a98eb21a659054c7550d32c8386aa286996412b5d3614cb2095ae830265904e57118132c830eb24a61964187591530cb20d1ac899065906c93258032c822f39cc928e41175ce649472087ce931ca39043d7498e51c83173228528e419398d32947208eeeca88a39045e73d9741c822eb9ecba0e41179cf65907208bae7b2c839045e7399641c822eb9ccb20e418b552629072099ae7314839062e6550a41c829ab8ca820e410f9d365cc72087ae9b2e639043e74d9631c821eba6cb18e410f9d2658c72087ae932c63904ad7498a31c8326a9cc518e4193995328c720aaae329863904cd73d9321c8256ba6c790e41a359263c8720d1cc8b1e439068d6458f21c8316b24a390e419358e51c8720d52c8b0643906c96358321c82f0b86a290e41399d8514872095ae830243904cd7318121c837090ac010e418b550625032099ae6312819045f73587548822e39ac3aa4410fdd95415220c3aa8b18a91063554584548830f322c62a4419398d6215220c9ac6b10a91065663984548832ab1cc22a4419958a6115220c6cc8b08a91065663584548832ab1ac22a44199589611522087ee8b0ea71043c74587538822fbb2a629c41875915314e20caaa6b08a71047671197438823ab88cba1c411ddc56550e208e8e2b2a871047671195438823ab88caa1c41471cd5450e20a38e8a9a871061f6550c438830eb2a8621c41a350d6210e20d1ac6a10851068d644c8328822f39cc928c41175ce649462087ce931ca31043d7498e518831ab88c8a8c4187d936354620c38c9b1aa31061f6418d518830e320c6a8c411ddd95114620c6ac8a88a31065563544518822f39ecba0c41175cf65d0620c3ca8b1e831061d5458f41883172a2c5a0c418b55162d0620a3ae62a4831053571152418829a3a2a320c4117dcd65506208b8e6b2a831045e73195418822eb98caa0c410f9da545062087aedaa0831051d73150418829ab88a820c410f9d365cc62087ae9b2e631061d6494f318830eb22a798c419394d62cc620c9aa6b16631055473546318821fba2ca98c410f1d1654c62087ce832a631043d741953188297ba2a310c4153dcd51886208daedaa04310567715502188236bb6a610c4159dc55308620a5ee8a88431054f73544218828eb98a9a04414d5c454d022087cec2a2811051d73151408829ab88a8a04410fdd95410220c3ca8b18811061d5458c40883172a2c4204418b5516210220c6ca8b0881106355458440
  | 13 => 0x5214440ccca5308a22066552984511023bbb2a228881999895114440ccac4a88a22046d7598b4110237baac5a08818b95162d04408daed296822064e6394b4110326b1ca5a08811bdd952d0440c9cc6a96822064d6354b4110333314a3a08819958a51d0440cccc4a8e8220665625474110338a8ac1a08818d9c56590440c5acb294822062d6554a411038729aa520881c354d5290440c6acb28c8220725529464110393292a320881c95495190440c5aa4b048220635515824110334a94c0208819a5496010440ce4a2b00822070e535484110386a9aa4208814d5d66110440e4aa53088220725529444110393292a220881c95495110440a6eeca888220637765444110394a94c0208818b5496010440e52a4b0082206b261580411022f39ecb90881175cf65c84408bce732e422045d73997211022ebacc79088117dd563c84408beed29e422045d7694f211030f324a7908818759253c84408beeca9e422045d7654f211030f322a7908818759153c8440c5ac9296422064e6394b2110326b1ca5908818b99152c8440c5ac8a96422064e6354b2110326b1aa5908818d99251c8440c6ac928e422065663947211032ab1ca3908818d99151c8440c6ac8a8e422065663547211032ab1aa390881179ce65884408bae732c422045e73195211022eb98ca908810f5d76448440c3ec8a9a422061c6454d2110317b22a4908818b1915248440c6ec8a8a422063464545211022f39cca10881175ce650844087aec20ca02070e5354b4010386a9aa5a00818b54a61d0040e4aa528e802043f76547401031b30aa3a0081c994951d0040e4aa4a8e802063776547401021ebb4a9200811e5da5490040ec2a4a8c802062f659494010317b2aa4a0081c394d5250040e1aa6a92802062d52185401031bb2ca2a0081c954a5150040c68c2a8a8020637655454010393292a2a0081c95495150040c68eca8a802066b659494010335b2aa4a0081ca9515250040ce6cb28a80206736554540103992a2a2a0081d85495150040a9ae7316a99045e73d8554c822eb9ec2aa6410fdd95415320c3aa8b18a99061e6458c54c8326b1cc42a6410f9d36154f2087ae9b0aa79045f7654c53c830eb22a629e418b5926214f208ece3b2e879047571d9743c823b38ecb21e411d5c76590f20a38e6aa2879051c7454d43c830fb2a8621e41875954310f20d1a86b10879051d7315342c82a6b98a9216411bdd56190b2087cec2a2859051d7315142c82d4b86a8a16411b9d85450b20a9ae62a285904ae7615142c82c6b98a8a16414b9d85450b20c5cec2a2859070e7315142c8296b98a8a1641c35cc5450b20a1ae62a2859052e7115142c8394b80a8a16414b1d15350b20a58eaa1a859070d5350d42c8266b9ec2a1641335cc6050b209cae2302859043f7655042c830f2a2c6
  | 14 => 0xc428e82a04ad72181415022f398cb90a81175cc65c8540cacc7a8e42a063564147215032b318a390a81275ce6488540a9ae629442a062e6550a215021f3acc890a81275ce644854095ae532242a045f73594215022e39aca10a81179cc65085408bae632842a062d6414821502a6b98a410a818b1954208540e4a8428842a06a94258021502d4b9683a02812bdc96190140c6ac228c80a054e73d4a52102a6b9ea529081599c75294840acae3a94a42056671d4e52102b2b8ea729081539cc6494840a9ae6324a42052e7418e5210326b18c7290814b9d36194840a9ce7b0ca42054d73d8652102a7398c129081535cc6094840acce2304a42056571182521022f39ec2a9081175cf6154840acce3a9aa42056571d4d52102963a2c6a90814b9d06354840c9ac631aa42052e74d8552102a739ec2a9081535cf6154840a58e8b0aa42054e7318152102a6b98c0a9081599c46054840acae2302a42054d73101521022ebb4a62908117dd95314840c9ca7310a42064d539885210237bb2a4290819398d5214840c9ac6a90a42065653984521032aa9cc2290819954a6114840caca6b08a420655535845210332a92c2290819a54960d08408baeb318842045f7558c421022ebb4a62108117dd95310840c9cc7290842064d63948421032731aa4210819358d5210840d1ac6a10842070e535084210386a9a84210819a94960108408ece332c642047571996321023b388ca990811d5c4654c84087aebb22642062f645493210316322a499081531cd524c8408ece33286420475719943210317324a4190818b592520c840a9ae7290642062e645483210316b22a41908153dd5320c840a9aea990642064f654c83210326b2a6419081a3591320c840c9cc7296a22064d6394b511032731aa5a88819358d52d4440acce5a8ca22056572d46511022f39cc528881175ce6294440aace7a94a22055573d4a51103a329ca528881d194d5294440e8aa6a94a2207246454a51102ab398a528881555cc5294440a6ce9314a2205567398a51102aab9cc528881559cc4294440aaae6214a2207254210a511029b3a065288814d5d03294440e8a64194a2205667218251102b2b90c1288811d9db5254440aace7a92a22055573d4951103a329ca4a8881c91925254440e8ca6a92a220745535495110392322a4a88811d9d85254440aace6292a2205557314951102b3394c8a8881595ca6454440a6ce9312a2205567398951102aab9cc4a88814d1d16254440aace6212a220555731095110392a1084a88815c9c04254440ae2e0212a220537744c9511029a3a264a88814d9d03254440a6ae8192a220745320c951102b3390c0a8881595c86054440acce4202a220565721015110236bb4a4288819398e5214440c9ac7290a22046f76548511032731aa4288819358d
  | 15 => 0x4d7394a210863abb4a510843695d25288421b8ae72944210c6f755912108637baac6908432b5d3614842199ae7b0a4210ce676d0521086e339e8290843a959041484219cced98a4210da674cc52108762b1862908432b5d0604842199ae63024210da67494921086e339ca490843399d84248421b8ce62124210ce6760c921086d33a06490843179cc64540218bae6322a010c3e7418d500861eba0c6a8043595c64254021c58c8a12a010d65718c9500872631a64a80434b5d32154021a9ae790aa010d6a70c8550086b438242a80431edd95014021c72c8a80a010e5963540500862f39ec2a9681175cf6154b408deeca90a5a064d6354852d021fbaac3a16814b1c95350b40b52e1a9285a04ae7614942d02c6b98a4a1681275cf6150b4093ae630285a04b57118142d0326b1ca4216819358d5210b40d1ac6a1085a06a94258042d023b38ecb196811d5c7658cb4096ae332265a054c7354932d031632a8499681c354d424cb40c9eca99065a064d654c832d0346b226419681179ce62947408bae7314a3a062e6250a51d023bbb2a228e81a398d62d0740d1ac6b1683a062d6294741d0354b12c1a0e816c5c3515074096cec28a83a04ad7218141d0358a0ac020e81179cf65c87408bae7b2e43a045e73d9621d022eb9ecb10e81179ce65887408bae732c43a049d7399221d0317322a510e818b995428874093ae732243a05657194821d0237bb2a4294819358d5214a40ccaa4b08a52068d63508429023bb8aca994811d1c5654ca408ece232a65204757119532902a639aa49948193d95320ca40c9aca990652068d644c8329022f39cc528c81175ce6294640c9ec7b12a32064f631895190326318c4a8c811ddd95114640ccac4a88a32052f72546419029bb8aa420c814bdc951106408bce7b2e432045d73d972190316b24a590c819358e52c8640c5ac8a96432064d6354b21902b2392a310c8117dcd65486408b8e6b2a432045e73195219022eb98ca90c814bdc951d0240c6cc2a8e812045f73587525022e39ac3a92811bdd95214940a98e6a90a4a064d6354852502b238aa429281475cc52d0940a9ae629484a054d7314942502973aec4a1281475cc5250940b1ae629284a052e7614942503173b0a4a1281c39cc5250940a5ae629284a070d731494250286b98a4a12814b9c4525094087cebb0a84a049d73d85425024eb98c0a12812d5c46050940d1ac6a1084a054d7214e325031632a8519281c3d4d428c94087ceb32264a04b571991325031632a84992811ddc5650c9408e8e2b2864a062d64d483250316b20a419281535cc520c940a9cea99064a054c754c83250326b2a6419281a3591320c9408eeeca88a2a056472544515029ab8e8428a814ddc54214540c5ccb31682a062e6558b415034731ac5a0a81a358d62d0540c5a
  | 16 => 0x8726b1cc42a0439698e6015021cb2c7300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e72615805408696ba4c5a98430f9d06054c2187ae8302a610c5f7654c530870eb22a6298439654d6014c21c5ac9310a610e3a64980530871cb24c0298438e9916014c21c72c8b00a610e6a62580530873930ac0298431e9c065d0c218f2e032e8610c6d7598b430863abacc3a18431e9c06590c218f2e032c8610c7671995430863d380caa18431e5c06550c21a38e6aa28610d1c7454d430863d380ca218431e5c06510c21c3ecaa188610e1d6550c4308672b8cc421843a350d6210c21c3cc931ca410e1d6498e520870f322c729043875916394821a3ae62a68410d3970153420862f39ecb21043175cf6590821a9ae62a48410d69701524208637baac32104339dd56190821cceeab0c8410c6d759824208697396a8a10430f9d85450821a3ae62a28410d397015142086d338ea8a10431b9d85450821a9ae62a28410d697015142086573b0a8a1043635cc5450821b52e02a28410d2e7615142087173b0a8a1043c39cc5450821a5ae62a28410f0d731514208686b98a8a10434b9c45450821e4ce22a28410f2a701514208696b80a8a1043ca5c05450821a52e02a28410ce571d8d42086373b6a6a10434b1d15350821a58eba1a8410da671d0d42086963aa86a1043c354d435082199ae7b0a8410ccd731814208672b88c0a1043179cf65108218bae7b288410c3f76550420870f2a2c621043875516310821d1ac6a108410ea542984420861f3a6cb190430f5d3658c8218daebb246410ce571d923208636bb6a9190434b5d0538c821ad2e029c6410c6f755863208673baac31904399dd5618c8218daeb3046410ce571d913208637baac8990431b9db544c821a98e6aa26410dc671d4d32086373b0a6990434b5d0534c821ad2e029a6410cce7614d32086c6ba0a699043725c0534c821a9cec29a6410e4e7614d32087873a0a699043535d0534c821e1ae829a6410d0d7414d32086a7388a699043d19c4534c821e94e029a6410d4d7014d32087a4b80a699043525c0534c821a98eb21a6410dc67190d32086a63aa8699043c3551434c82195ae9b0a6410cad741813208672b88c0990430f9d3650c82187ae9b286410e1d6494c320862fbb2a61904387591530c821d1ac89906410ec532984320862f39cc928843175ce649442187ce931ca210c3d7498e510871732285288439398d32944218bce7b2c8210c5d73d964108716aa4c520843335ce62904218bce63288210c5d73194410871632a84208430f9d3658c42187ae9b2c6210cad7498a3108726a9cc5188430f9d0650c42187ae83286210e4c654c83108666b9ec9908432b5d363c8421d1ac931e4210e8e6458f2108746b22c7908431b5da5288421a5ae92944210d
  | 17 => 0x9c43479cf54d0e21a3ae929e8710d1d73952438868f39ea8a1c430f9d85450e219cce5b0a8710d1d73950438861fbb2a821c43475d25310e21a3eeaa188710d1d7550c438870f32a8621c438b9516210e21c5aa8b108710e4e535884388726a9ac421c43a350d6210e21a3ae72a68510d4d739524288636bb6a7214434b9d35390a21a3ae72a28510e355418542886373b4a8a1443535ce5450a21b1ae72a28510d2e7695142887173b4a8a1443c39ce5450a21a5ae72a28510f0d739514288686b9ca8a14434b5c25450a21a5ce9a9a8510d2f75d0d4288786a9e86a14434bdd54350a21e1ea6a1a8510da47150d4288666b9ec2a14431b5d46050a2199ae63028510ce5711814288746b1a8421443475d253cca219cae3b246510c6d76d5232886a739ea9194434b5d2538ca21a3ae929a6510e555318532886a739ea8994434b5d2534ca21b1ae929a6510d4e7694d32887273b4a699443c39d2534ca21a9ae929a6510f0d7494d3288686ba4a699443535c2534ca21a9eeb21a6510f0d5490d32886a7baa8699443c3d51434ca21b88e2a1a6510cad74d853288636ba8c0994432b5d0604ca219cae23026510e8d644c8328868eb9ca920c43335ce6290621a3ae72a08310e2e545884188656ba4c518c43335cf64c8621c5acb3264310e2d655932188726b2cc790c43a359263c8621c9acab1e4310e8e6458f2188746b22c790c438d59664c8621c6acab264310e556598f218874b324c790c439559563c8621a5ae990aa110d4d73c8550886b538642a84431edd95014221c3ea8b1ca890e4e6358a5448726b1ac52a2439598d61951218bce6302a890c5d73181544861fbb2a82a243475ce6415121c3ac9a9ca690e2e6458a5348716b22c529a438d9916194d2187ce9b0aa690c3d74d85534861f3a0c0a9a430f5d06054d218beeca98a690d1d7498c534863ab8ecba1a431b5cb6550d218f6e0b2a8690c7870595434868f39ea8a1a43479d35350d218dcea3128690c7675d85434870f32a8621a43871954310d21d1a86b108690ce471588434871a2a2c3a12438b9954210921d1ac6a108490e5453587324872732a6419243a3591320c921c3ea8b1e8290e1c5458f4148717aa2c5a0a438b15162d0521a3ae72a48290d2d72952414862eb9ecaa0a430f9d85450521a3ae72a08290d2d72950414869ab8ca820a430fdd95410521c3ac9a9e6290e1d6414f3148727a9ac598a439314d62cc521a3ae929c6290e966498f214862f39cc9a8243175ce64d412187ce931ea090c3d7498f504863dbb2a028243879926314121c3ac9318a090e1e6458c504870eb22c6282438b5922114121c9ac7108a090d6970884504862eb9cc5aa043535ce62d50218bce6302a810c5d73181540861fbb2a82a043875516315021c72a8b00a810e1e6458c540
  | 18 => 0x494f21a3ce8314a790d1d7418a53c86ad380c529e43565c06294f21a3ce9b0ca790d1d74d8653c868f3a0c129e43475d06094f21a9ce4304a790d557118253c861f3a0c0a9e430f5d06054f218bcedaa2a790c5e7615153c86aab8cc8a9e43531c96454f21c3ac8322a790d4e7219153c868f3a6c2a9e43475d36154f21a9ce5302a790d577158153c868f3a0c0a9e43475d06054f21a9ce4302a790d557118153c861ebb4a829e430fdd95414f218beeca98a790e1e6454c53c870eb22a629e438b9926214f21c5ac9310a790e365498743c872aa9cc3a1e438d95161d0f21c6aa930c8790e565398643c872b29ac321e43471cd5450f21a38e8a9a8790e2d54d8943c8726a9ec4a1e438b5506250f21c9aa63128790d1d7395043c868eba4a621e4347dd54310f21a3aeaa188790e1f6550c43c870eb2a8621e438b9526210f21c5aa93108790e4e5398843c8726a9cc421e438b9516210f21c5aa8b108790e4e5358843c8726a9ac421e43a350d6210f21c6aa930c8590e565398642c872b29ac321643175d66310b21c3ca93188590e1d5498c42c862fbaac621643879516310b21c3aa8b188590c5d7694c42c862fbb2a621643a358d4210b21e1ca6a108590f0d5350842c871b2a4c2216438d952618cb21caaa730c6590e365458632c861ebacc8196430fdd5640cb2187aed2a06590c3f7655032c870f324a61964387592530cb21c3cc8a986590e1d6454c32c8746b226419643c3951320cb21e1aa89906590e565398432c862ebacc7a0e438795263d0721c3aa931e8390c5f7558f41c870f2a2c7a0e438755163d07218baed29e8390c5f7654f41c8716aa4c5a0e439394e62d0721c9aa73168390e2e5458b41c8716aa2c5a0e439394d62d0721c9aa6b168390e2d54d8941c8726a9ec4a0e438b5506250721c9aa63128390f165350441c861ebb4a998e430fdd954cc721c5ca93166390e2d5498b31c87172a2c598e438b55162cc721c9ca6b166390e4d5358b31c870f2a4c7a86438755263d4321c3ca8b1ea190e1d5458f50c870f324a7a86438759253d4321c3cc8a9ea190e1d6454f50c862f398c8a8643175cc645432187ce831aa190c3d7418d50c861ebb4a8286430fdd95414321c3ca9318a190e1d5498c50c870f2a2c6286438755163143218baed298a190e1e6494c50c870eb24a62864317dd95314321c3cc8a98a190e1d6454c50c863dbb2a028643935ca63d5221c9cc6b16a910e55639875488732b14c3aa443479cf5495221c3ea8b1ca910e4e6358a5488726b1ac52a443479cf64552218bce6302a910c5d73181548861fbb2a82a443475ce6415221c5ae5326a710e3564987538868f3a6a729c43875935394e21c38e6b24a710e2e6458a5388716b22c529c43479d36354e2187ce8302a710c3d74181538862fbb2a62
  | 19 => 0xca80a1a0d4e73d4a5290726b1ea529483179cc6054a418bae6302a520c6f76548529068eb9ca5a1483535ce5290a41a9ae72928520d1d7394942906c6b9ca4a14834b9da5250a41c5ced2928520f0e739494290696b9ca4a1483c35ce5250a41a1ae72928520d2d70949429064eb9ec2a14830f5d46050a4193ae63028520cb5711814290746b1a8421483535ca538ca41c5ecaa146520f0d5350a329065ab8cc8994838bd95424ca4196ce9b0a6520ea5421853290716b24a419483535ce520ca41c5ac8a906520d4f754c832906a6baa641948393995320ca41d1ac89906520e2d6598b4190716b2ac5a0c83a398d62d0641d1ac6b168320e656598b419076331cc5a0c839959562d0641a5ae5a0aa120d3a70d05509063dbb2a0284839358f52949418deeca90a4a0e2e655084250746b1a84212830f9d4644c941a9ce7a9264a0cb471590325072732a641928393195320c941d1ac899064a0ec66398b415062f39cc5a8283175ce62d41418f6eca80a0a0e4e63988505072731ac4282839358d6214141c5ac5208a0a0d3970904505072731cc52a0839398d6295041c9ac6b14a820c5e73181521062eb98c0a90831bdd95214841c9ac6a90a420e6952580521065bbaac3a10838ddd561d084187aeb3068420cb571d8d4210696392a6a1083699c7525084195cec2928420d8d7314942106d4b80a4a1083275cf615084193ae63028420cb5711814210726b1ca4210839358d5210841d1ac6a108420ea5429844210752a14c3190831e9c0654c8418f2e032a6420cb571991321061fbaac899083531cd524c841c58caa126420f0d53509321065ab8cc81908393d95320c841c9aca9906420e8d644c8321074731ac5a0883a358d62d044187aed2a48220c757695241106d2b94a9208832b5c86050441b4ce52a28220cb67610941106cb39884a0883179cc62540418bae6312a020d3571d09501071631284a80834b5cb4154041a74e1a0aa020d3870505501063dbb2a0280839a5895014041c9ac7316a990e566358754c8733312c3aa643479cf5495321a3ae7aa4a990d3571d8e54c870eb18c72a6434b9c86395321a3ce6314a990d1d7318a54c869d380c52a6434e5c06295321a3ce7b0ca990d1d73d8654c868f398c12a643475cc6095321a5ce4304a990d357118254c868f39ec8aa643475cf64553218bce6302a990c5d7318154c869ab8cc6aa6434b1c96355321c3ac631aa990d2e7218d54c868f398c4aa643475cc6255321a3ce7b0aa990d1d73d8554c8697394c0aa6434ddc56055321a3ce6302a990d1d7318154c8697390c0aa6434d5c4605532187eecaa0a990e1d5498c54c870eaa2c62a643879926315321c3cc8b18a990e4e6398854c8726b1cc42a643479d35394f21a3ae9a9ca790d5571d9253c870eb20c929e43539c86
  | 20 => 0xd54151320cac73a6c299065635d3614c832e1aa9b0a641954d75985320cac73a4c299065635d2614c832e1aa930a641954f75585320cb86aa2c299065c3550614c832d8ac230a641970d54d81320caa6bacc099065c3552604c832a9eeab02641958f74581320cac63a2c099065c3551604c832b8ee2b0264195c471581320cac73a0c099065635d0604c832e1aa830264195c671181320cae2b88c09906533dd932d4432d1cc8996a21968d644cb510cb86aa265a8865c39513294432e1aa8994a21964f764ca510cb263b26528865935913294432e8ee2994a219744714ca510ca1fba2c1288650f1d16094432c9a64b04a21970d544c9510ca1f3a0c0a88650f5d0605443287aed2a0a21943f76550510ca67bb26428865a39913214432d1ac8990a21970e544c8510cb86aa264288651ddd95114432c74a9300a21963954980510cb64994c0288658e9516014432c72a8b00a2196c932580510cb38a8ac02886533dd932d4032d1cc8996a01968d644cb500cb872a265a8065c355132d4032e1aa8994a01943f74586500ca1e3a2c328065c39513254032e1aa8992a01964f764c9500cb263b264a806593d913254032e96e0992a019748704c9500ca1f3a0c2a80650f5d06154032c9a6430aa01943d76950500ca1fbb2a82806533dd93214032d1cc8990a01968d644c8500cb86aa264280658d9526114032c6aa9308a0196c532984500cb1b2a2c2280658d5516114032d8a64b08a01947b76540500cb38b0aa028065539cf5294b41a9ae7a94a5a0d4e7319252d06a6b98c9296835a9c06494b41ad2e0324a5a0d6571d8e52d06973a0c7296839358c6394b41a9ce7b0ca5a0d4d73d8652d06973a0c129683539cc6094b41a9ae6304a5a0d657118252d062f398c0a9683175cc6054b41acae331aa5a0d2c7458d52d06973a0c6a96839358c6354b41a9ce7b0aa5a0d4d73d8552d06973a4c0a968359dc56054b41a5ce8302a5a0d4e7318152d06a6b98c0a9683595c46054b418baed298a5a0c5f7654c52d0637bb2a4296839398d5214b41c9ac6a90a5a0e565398742d0732a94c3a16839594d61d0b418baeb31885a0c5f7558c42d062ebb4a62168317dd95310b41c9cc729085a0e4d6394842d072731aa4216839358d5210b41d1ac6a1085a0f0e5350842d0786a9a84216839994a6110b41caaa730c65a0e665298632d0733292c3196838bd91524cb41c58c8a9265a0d4c7354932d0717324a4196838b592520cb41a9ae729065a0e2e6454832d0716b22a41968353dd5320cb41a9aea99065a0e4f654c832d0726b2a6419683a3591320cb41c9cc7296a1a0e4d6394b50d072731aa5a86839358d52d43418bce6312a1a0c5d7318950d0636bb4a4286839398e5214341c9ac7290a1a0c6f7654850d072731aa4286839358d52143418f6e
  | 21 => 0xb86b98a8a14654b9c45450a32a5ae02a2851968c6350d428ca1fbb2a821465879516310a32c3aa8b18851968d63508428ca7338ec9994654d9d35194632c5cc8a14a31943e74181518ca1eba0c0a8c651ddd9511463287ee8b0ca11943c74586508cb1632284a84651edd95014232c6ea8b0ca89966562986544ca3b388c0aa2651d5c4605513287eecaa0a89953571990544cb26b1ac42a2658715163d0932acce32a484995c671d8e424caa73a8c721265339ce6190932998e6b04849952e75d91424ca973a4a8a1265599c654509328dcec2a2849952e76151424cb173b0a8a1265c35cc5450932a5ce22a2849952d70151424ca673a8c6a1265939d4635093299ce231a84994cd7018d424cb1632e86a1265a318f4350932c98cb21a849958d7490d424cb862a486a12654b1d54350932c58caa1a849964c6550d424cb87b2a86a1265c31954350932c18caa1a849968d43185424cb46a1ec0a1265a358d42109329ace3b24649968d6490a324cb47b2285192658d5c664d4532c6ac9a8ca29947776544514cb86a1a8428a650fdd16014532878e8b00a29947671993504ca3ab8cc9a8265c350d42d413287ce930ea09943d74987504ca3dbb2a0282658d9926114132c6ac9308a09963664584504cb1ab22c22826599dc96114132cc8e4b08a09952e72d86540cb1ab08c32a0654b9c86095032a6ce2304a81953571182540ca3b388c0aa0651d5c46055032a6ce3312a81953571989540ca97396c2aa0654b9ca6155032c6ac230aa81952c72581540ca9bb8ac0aa0654d1c56055032a5ce4302a81953671181540ca9ab88c0aa0650fdd95415032c3aa931c841945f7558e420cb0eaa2c721065875526310832c3ca8b18841961d5458c420cb17b2a84210658b5954210832d1ac6a10841946d7694e320ca373b6a8990654b5d6544c832c5ecb2a2641962f65551320cb8739aa899065c31cd544c832c5aa9b1a641970d5494d320caa6bae8699065c3553434c832e1aa921a641970d5450d320caa6ba88699065c3550434c832c9aebb2a641964e76d95320caa6ba6ca99065539c7654c832a9ae1b2a641954d75991320cae338cc899065715c6644c832a9eeab22641968d64191320ca673b6a899065539db544c832c9cedaa2641954e71d51320caa6b86a899065535d6544c832b1aeb2a2641950d75951320cb47b2ca899065c3d96544c832a9cecaa2641954c76551320cb87ba2a899065c3d91544c832e18c8aa2641954c71551320caa7b82a899065c3dd5544c832d1ecaaa2641970f65551320cb87bb2a899065c39d9544c832e1aecaa2641970c76551320cb87b8aa899065c39c5544c832e1ae2aa2641970c71551320cb87b82a899065c39c1544c832e1ae0aa2641970c70551320ca673b0a899065539d4544c832b1ce82a2641970
  | 22 => 0x885555c46054c428beeca98a62164d5358b4310b2729ac4218850f5da54908428daed2a4842161f6594d4210b0fb2aa6a1085c39c95350842e18e4a9a842164f6594d4210b27b2aa6a1085c39515350842e1ce8a9a842170f6454d4210b86a9e86a10854b5d64350842e1aa721a842170d5310d4210b16baecaa10858b9db6550842a5ae7b2a842152e71d954210a96b86caa10854b5d66350842b4ce331a84215a57198d4210a97baac6a1085a358c635084295ceda9a842158d7594d4210b47b2ca6a1085c3d965350842a5ceca9a842152c7654d4210b87b1aa6a1085c318d5350842a58e2a9a842152f7054d4210b87baaa6a1085a3d955350842e1ecaa9a842170f7654d4210b873b2a6a1085c35d95350842e18eca9a842170f7154d4210b8738aa6a1085c35c55350842e18e2a9a842170f7054d4210b87382a6a1085c35c15350842e18e0a9a84214ae7614d4210ac7398a6a1085c354c5350842b1ce7b0a842158d73d854210b86a9ec2a10854b5d66150842b1ce730a842158d739854210b86a9cc2a10854bdd56150842e1aa6b0a842170d531854210b52b08c2a1085c354f6050842a5aeb302842170d539814210a97baac0a108563dcd6050842b18e6b02842170d535814210ad3b8ac0a1085691c56050842b1ce6302842158d731814210b86a98c0a1085699c46050842b4ae230284214af7650b5110b4731a85a8885a358d42d4442e1aa6a16a22170e5350a5110b86a9a85288858bdd94294442c58eca14a22162d6350a5110b93b8a8528885c91c542944428bee6b04a22145c735825110b16a12c128885c354d42544428bce6302a22145d731815110a2ebb4a62888517dd9531444295eeca10a22168e635085110b46b1a8428885c394d4214442e1aa6a10a221477765445110b2d29cc0288859654e6014442d5285300a22165a535805110b2ca9ac028885aa5096014442ce2a2b00a2214af7650b5010b4731a85a8085a358d42d4042e1ca6a16a02170d5350b5010b86a9a852808517dcd61940428b8e6b0ca02170e535095010b86a9a84a80858bdd94254042c58eca12a02162f635095010b95b8284a8085ca1c142540428bce630aa02145d731855010b16a10c2a8085175da53140428beeca98a0214af765085010b4731a8428085a358d4214042e1aa6a10a021656539845010b2aa9cc228085a950a6114042caca6b08a021655535845010b52a12c2280851edd95014042ce2c2a80a02164d6398b548cb2ab1cc3aa4659998961d5232cc8e4b0ea91953671d52548ca9b38ec8aa4651d9c460552328eae2302a91943f76550548cb26b1cc42a4658b5506250e32d1a86b10871953671d53428ca9b38ea8a14650f9d85450a32b1ae7aa285195a671d51428ca373b0a8a14652b9d85450a32a5cec2a2851962e76151428c
  | 23 => 0x600000000140060010000004002013006000400e0020068004018006001000802400d000000000a00d00800440020010080014000000006000801e00e00a800c0000020150008002001001000002400700b803401e0020000008002000003001c004001001800c00000300580000240130000000064020000800401a000003800000000f000001c0bc000001000400600000380080060000038028000002000001c05e000001801c00a0050150008002020000000c020008004802800c00f0190004032000004004c00200300180180260010000018062007000800802e02500a000800000e003003801a0000038044016006000800401000200580000480150020018002003012802801601d000005403a004003000802e00b0120054000002004800000e0000000018004008006801000400400f009c010000000000400001d000000c000014006806400e000011800800c000006000402400200000200000170000000000051001000800000a00880000100000048020008006000001000200000600100080050010054022001005823001c00600200180020070060000002002000800007200a000008800a025000000000e01e001001000201001500e400200400c000402a003000800800e0120040070106000000024401600a0020114000008003000c004000019005000c0010008010014028002801002200500f001006a00000c0008012033000800401c000001000000c0000018008002000000801c04c01802780000060070020038001559c75394f428ece2302a7a14757118153d0a2fbb2a629e85559cf51947428bce6302a3a145d7318151d0a3bbb2a228e8517dcd61943428b8e6b0ca1a147b7654050d0aab38ea729c851d9c46054e428eae2302a72145f7654c5390aab39ea328c85179cc60546428bae6302a321477765445190a2fb9ac328485171cd61942428f6eca80a121657535865350a2fbb2a629a85699c762d0d42a5cea31686a14ae729874350a56392c1a1a85a34c86250d4295cea31286a162e751894350a57388c4a1a852b5c06250d42d1ac7a1e84a165563d465150a3bbb2a228a8517dcd60145428b8e6b00a2a14767198f5050a3ab8cc7a8285179ce61d41428bae730ea0a147b765405050b2b31cc2282859558e6114142cacc6b08a0a1655635845050b1bba2c2282858d1d16114142ccee4b08a0a1664725845050a8f3a6c329885539cb6194c42caac230ca62151e741825310aa7390c129885559c46094c42aaae2304a621476711815310a3ab88c0a9885559c66454c42aaae3322a621556719895310aaab8cc4a9885479d36154c42a9ce5b0aa62151e749855310aa7394c2a9885955846154c42a38e8b02a62154c725815310aabb8ac0a9885551c56054c42a3ce8302a62154e721815310aab388c0a9
  | 24 => 0x5000c0ae00b009805000e004004002c00400e002801001200200380040000140078024000000000000400000900500a006e005001807c00a00100200040020120018008000000000800001e006003001000201c00380b00000030018024000002003000002400200100240000020020004000006000001c004000003800400800600b804001c001006800400200f00380180160030018000018005003004c002003001000004400000980140ac002006805805000d0090000014042009800400200e000803c01003000f003004000d001006003c00100280040000080018008004000001000400400300000100100030058014004000008800000e001019800400400100b801c00a0160038000064005016000000c009000001002801b0068020008000000006400a0050000004036012002800000004b00a00000100010000000000001000002c08c00603d0000014005009001000c00b0060000018003000808c000003003004002c03c00f80ac00200000000180000020000004000001013001406400801000d4000016000803c002003000802000a0080028004000000000000c00800f002000c0320160018004008003000000800a003005801401e001007803800600e02100f80000760038140000000001800400c004013000000200300c8004044001000009c018000011800c00600b0338008002000000005000e011013003806a02f00980200000010038000012001006800c01200001680600700000010008012000001802c00a0030000000000000000002000001a0000028064015000000c00000000080ac0b400a0000024006011003800000400b009800001e00100000b402e002007000800800001a801001c00100100100000030028010006003000000001000500f00000020110018008000005000800005c003000802801400201b000801a00001a004001a00000c801c000006007003000200b001008c00c009000800001e0000008018032001002801c00000900e8008030006001804402c001000802400401f005801400a00100080240260160000010000001000002409401d000800000200200701e404a00000080740020000028064002004012802401c000000000401e000004000c0160000000094002000000001803800c00100080620010030018004008004801801200d0010000000000000000401600000d800000202600a000c008004000001400c002003000000801d0030008000006004801c000001000800400600600c8058000002000001003c07800200100080040048040034064004003c00400900400080060140030000002008000800c000001000000000c00000a802001403c0028024036000000807002200b00a801000c0000040110002000001003000000e00f0000026000001003008c00700000240
  | 25 => 0x3150e51944efada99100001c129898243175cb8000000055800160400000000000000000000002ebc8e51e90a0ba088520001faf82d5840000002a6c000000055800084e0006a700000009066a10df1a2795f0371e5e814e400b4b524012d6f4b40002002012000000200100e80000160010008000004000002800000000200000280000050030000002026000000000000102f002c004001006001400404b00380000120000000000000004008003800e0220010054004003006006c01200a00080b0006008013801400000c000000c00c00201e800801e0010018024018001004800000000c0000000016017000004c00c0000000018002003002001400600000300400020020000004004001000002408e00e000802401a0080030008018000000800802200000c800001400d0018000006004008801800203800400180060040000014000008000000c000000001800c00e0020000000004016000000000a00f000001802c0020078000026000000000400600300d805c01000502380040080010018030000008003800000c000002804000605400300000000070060028004003004000004a0010010000036002004000c00000401d0004018000003001400000d009803401600400e00580040060048098000002000000000000f0000000020000008800400002e003000400001c00080a4004003001804c000001002803000400700000080120310000014006000002803400200000080c4010003001000407c009000806409e0010028008002004002001400000000080040080140038008000000000000800a000000000805c00200180280000400008040002013005805002c004000000401a00c005017400000e00a0010006000001004800000002200040000130020020034034004000000800a002802c00c00000680000000000030058012001000000800000300b816000c00300900000040070040064036000007003c00001500100fc00000200a005c002011001001400c0010000000012008001016c0040010040000018004000000003a00000a0000018002025805800000000000340060000030000024006001001800000e002804c0160120000018008001000800001200401a002c0280230020008004003001812000000000b0000014000000002c0280070018080006011004022001a00000000040000010030064000004005000c00e00e000008801001700980400000010028020000001000800c000055000800400400100000240720180020000000000006000000000c000801c0020280008000000005005800401c01500c8018002001002000000000100d800001e00800000480620010028018000002007002000a021004000400000101e8004006000010007c028000000003c03e00d002801000e00d002000c01a0000
  | 26 => 0x904c9d2d6a000000000230fe44000703b99e0000000888001a62a1667d00000000000ba800000000000021a00004bdeaa3994000b3d51d80000000001398000000b8a00000000000abe91915c25600000011d8e7a9cd21f000046cb75731b4bde96370117c0cfa74af4261374519279880000010e667c31daa56bb20000003cc2000000294259c6c02ab60f80003b579a4e55aadcb8e318a63052264914f50383c58e16e759b700f58cd30000e3a000079054a6dcb62b2f0a51854e54d890b0a504d4e1b40c6ebd805c01b06f0fc9c98de7dbe800064d48b3162bd45179b95ca93bf024bfb3b529237c63ed616de9877c9f012d073f0faaa836731f14c20fd5388ac5306b3006fb6bc1824a0711b46b767898108ccce9202741c85485bf763819c3bb0000f0a00008e4ad46010eaaeb7a0483420a94fc06874b5dd90bdc0ba91dc89f84ac0696c461014000db034524bc490000000083f95cbe6408000000080664383830bc40373f818557b5926393421352bd94fe09b80002fe45869b103ab4e0001334c86e4557f9c896400895586e7091e01e24329105969690ea4659986c0c2e396ecb5449d07a22e04807cf671c001d240004a40564c90b076621eb48540e6bdd038dc22bace4288d11e09f52fa192b43047a2f081d4850388000000070d0d036c9fb80008c24c8b01c0000000001efc0000004a1e2d8a884be27932ac2a400076217d88d80003263b685eaf301a10001c4b8fdd3724249a81aceb43594e286c400012b183800061200000000000000000e4000000000019986c000025bc1430000f44000000de888d988dae000009122f492856f0402f3de5eb116b8885c5549ac00010da36000000000018ab9026bf9970000afe0001ab921c0005e3038ec40000660ebe40002ce3039fc078800000033920003473bb00005e4a8d1d1bcdb3360006fd058cb1c085000025dbeaa266faf8400000302e50deba60a8cf0c0f5ddf64d35d18dbe61e0165c0b6c800058811f92fd3ee4e515e02f4d04c331762c9dc5939d224b48a412b64382a9fbd48b4574800a188e9be3ea1ef09e83cb67608051d2a4a4d888b889e0000002f08000b11d41c84c382f1a0c9ee4d40214e08e1aed0508ea04f3c64834c0e4500b90cec36315097b051c00072ac525692928492606d57736e75aa4a30b0ddc323a550028000725b954e4d0930003d21083000000056d1f100020e000080c00024b00019b40000bc0ed000016600001411f67c874580011200005dc237c000dc5555c0000d433600007ad76800000024897062a8c8b40019ee00004c12bc0c605a2441761c6a0af10b4da56740000001330000000554b3d2fd44a100014c4000f388000000e34cfc5433b7d4a040d0000000000c8d78313e5d7400058b0a949fb00048d69ad57ad1665d2b3600013109a8
  | 27 => 0xadd8f5e99f8000a4ee48c3d33344d8246c921e9084b3a86bf3b72c1b34aa9c01473d9c606746f2757071c9908fa9a7a8886302f9b3cc9e0b1a0723cfce202602b70e346ce2121ee2a38f1f0e20dfe76c000d074cf1b9cfe493814834500f82cd24480000000f60003be8c4ca4100002b60000004e71d252451cb32a3c5c04f41251872bea6ae520b413740b03b25fb1dc16624932f4001ac3c4d00000cc6df4000455265ddb60000001b7000069149313808b0371adb8198418000007463013400043500012cc86d63d8000900bb200004950a20001b2a9bc52e1aec0a200c13e382b0c1520c5bc54a3dada1110d52757bd2400045e29a0001a3e3c03d29d817564ef0fe739ae3256e800000014e4ea1274f8cc32edc49f1364f08b380000ebe000000000000125494e42410b188c987577a36cfd671e3d01bd003b2e1596000088c00002240013e689b000311000000000028a8000aa42baf4974ea82700009fd9cc8f7700b8b4d904b3471800036e0004262359316b3400033c8d4485376706b0000d3f21740002202002412e7920fb573288d5441600035c000151640b50fb53400621900036b1354f2d4e8828c51e0001f480013880fce2f1bd9646dc30e1376084a00000005e7aee0001fc1e4f369d2527f75d400000000000012adae400004e12e61330003a0000018701f7890e04dd4237ad0d1e40006fb8d6d432ebe67f8fd4b160a680000015fd1dcf84977ce2e45531e141195035a44bea79c4cd460000000450000070c001213dd736608e29969b81d30838000d6e16c216c5f07d6533f84cc2240fe869a380006e63c90000e524c02512fa8faa0005be00015c42bb0002c2d21a000736aada000c31d46c00115c0ef5fe0d100fa0125cc94347b280c75184f00aacd918db238fb0e1e6f135280001d26630001814661690c00163a0004af47c44fcdda000062642b389e021ba83e41c30001abc00034b11102ca8480000001c4c6408ee3c5acac64ad0f60eadf812d39b36165aa6a23df0109f5d7e04752ca8e9d162d8877cafb5525b0bd5102995939c6565c235be20e8177240b438d9d6f6dce17e72f1022f5ec4602981fd01e825ca0978088ad1564c700007f937f134659800052b51243780000aea2e00007bc8125e0716000000000033c1f48441f297110ba17caeb96d4140dc79c6f338066dcc034a4c6aba17a6e565c69e57bba8620c023e795d26906997fc89484301fe4cc5728173d4a104aa4bb1bf7e83841a22bf1f8f6852a54608f118d52433035c84a8fbaacc54637ff1b2c5d3278b79ba4448560a95d84e291bbfcb707aa2c118180003227fd6539f64ce6dc833a9bed5e09dc79ac67950646d13eda5d272e0c64c7315472bca69db885e50a5d6d2b4e1bf661d2d01f35a36bb647090529a242b0690d3dd4ecce6a08001396
  | 28 => 0x6866a3e1ee48201176d686b525a80d310bbca451962c4694dc5ec8d0619ed596a897172b9a9419c91c0003a35ace39f1fa5b6d3e46555570a78a0c5e90000001364bef00002880007620001c555024b50002e3170017900026460000510000001bc8000000000000072e000000000001f00001de000f050000000000be04d580000002850001084000a53475a5809366ae8001b4c24e22ee5480005a47cc179800000010b800542581d70418226215040a0993f86850c7db5444000000669000000167300070faacd6f61d81f42a986fa0005012d4c3440004ba9a62000056ab1163c3ad9d51f22b4492b6cd652404f78a4b109d98b45ae25e5bfec896a0b0200d0be8e38bb7000274a8c860a47f8001a083cd70436042d431c21974923216ba1678377cd6950232a5ac0310000001eec94e00a5489f4d5cef1e2414e32284ac3702400151566d0002e1000000007dc3e80000000000fad86cba900035307ef000000000067ea2b6f4c000000c6e000000186ec8a02d400182ec55000349183c000000000004600040d000000012455d2eb8f3f00000039a5abee062cb399145a000329e011aa6df66f8e9794ca0e11582c0c2009e92a712e2566c3e0301bbd283e2b962b545dc6a341ccb2c5720a8bafb8a11a7a3086cc80a42dee6f7002740efd5c46b49769e1ecfe00000011fc5943aa1e02a2e65596430684f4e2a5dd2e2db441be6ae9dac1cf37465c2060baa4312d30c551f425b0002d854b6000133b39c6491f30000499dc800000000003b459928a8cc5225be710d94f0d2a0001d8800000000051380000001970450000bd6334ec603ae00000062b0a08000a700000000e8099f0003b44000a0d582b320e9a5ad00000000000005b5a5a7810f456603b9522c046563229d87261018500000000005753c1d171000146dd14000d0a0b90000000df96080afac5e0000dd000000000000005fced019a617e5645d2233000000072b0002fe00000000000a4000000008e0e000016649fb70700000000000001ba400096500000000000000c23c069fe4d60000000e299e55a42890ed8e1700e68fcdc410541221ce0000000d8b94000030600027b922beb14c7b90817e5265d878420000006d1a1b00000003c0a8f117b5243688c44e4aa880570000000d2800000011680005e2643628aa52583200800038548740c5a23c204aa827616f41606b11c8ede65f0002c863a192938d837000080e48a800132c7df1a9268839394f71f31454aa2d30703678ba8d9b2522b74c1cc4c749867c9d8a87713800168fc0d2bc8f04b82f371c8a6cc00052000000de2e6c60445a4b25b218aef34001deadb9041859e9f404f8002b5c2ae00000000003bdef480033e0eae0000000741694dc70561b22000e4710c2b6d3ac03cc3b55d90d27e8608e0b9c8753aa3c
  | 29 => 0xf1ff811359e1e331516fddb66010788000a900000000000000000378c952e0a3918001cbc00000022d3afaa6333f2a28000000000105cdc01e672ea848570daa5a37c719548225f103500000003ce871c0003849571ad528a357592a668000d792338b817888bb6cd269000032300000019389202b8a920c665b95d42cfa8b80945df33554840e9826380ae422e251c4935e765a91c32bd78ce5ac2193a94f7c790acd068556a00078a9ac9014773000244e4b8c6b674172400030e36e9868000ac703a000000018866c2a593280001c5c5a64526863508d25473099cf610b4f2000029639c55f40e966516840ca91349fae5136c58c3ada5b46d4c0b75bbd3999f7c51b41df4b30e5148bae80ff6bf909624ec06c9d7152192c8dfa3359f24d9a4f36b1651fe058870e92c90de4d803557011c09886043ef3c200008ef1758a8c1470cf1de6631c9276d36f2b2c000df24f3995980a6a40da9ad0000328397b35d1da4f77698000000a973890001368918493eed5df0ca38002798678eb203940015bc00000020f19e281c4be308c000394c6586a000001c1563cc9ca832dec900001e050b4852ddcf7a000053d82c00091fb7e888d6965e5077eb959b813e34a00009e61850e37728a9aca335b82dcdc2dd545417e1255d14820a20cbf65021aeac5569a759c8cd6918b83321e709ad458b516e8373cadbe3b1e112e1c5f74e4abb3a6a740001908ee89b6807431c66194b1b95045c380003186d9a951742073615146708400047302e4502f2b414bab53dede61c7ac28ae324f00000012480004c02a9d8ea08b00023a11efcefc4f8a5940e52a7171ccddeee4d3e30a5b666ae3765b6ed406e035a92648e000626db95984deec2006ae3be4c59b2b38959188b2631c6654ca6748722338526a3e1075800095c78ecb805e90e87f3358121d777e70839256998ee0fe148ff49540540edd80ceb5e2f29ebca8000c0612188a800969600000014fc0000000000462040efeb3b8abc0cef630000e8c5193328e721cc0074472f780004a5552933f9121ca80019afcf8cd18e05eb85c60000002c390cc86480037e17011b241f8d585beebf5d308dc00046dabdab3c0004fd000000045a4ed589bc7c000000496c4519be4b442e109878a0000a680012c30000000000ee800000000012c80000c69315944def1a802bac2eabf1b1352c932d18148a04a000b36da840006047da383800051f7c02c8800091a35c000000000000034e207cc8c0000001fdc000eaa00015fdc621ab8ee38cc0a42bd3f4975955a2c00e6a4c4f1a01d00008ec95000000038a0000000467130200000000000000004113dbaabd51f00018f0000fce8b1e019e4cc50beb0000001565000456103950000042f4000fea000000051c66f0000001d0d0fe2308e50000e2c629153a8a583
  | 30 => 0x7027908985c2000b3f75b03f9af00a422132b57968bf3af2ac014a5725badd6348e5070eb9ed8ecc4fc7224f30e229c80d714395e667e9eda9e29ea5d75aeb8497f08d73a103b1d12a4c5dae518e78ec810327756dc58513e881d7d052d2ab2bb26206d403f94f87081535a20f50df8cd678e80e6f04ee24e6c5d0000ceb00000000d8000415811dcf2276677a8dd2412fc1fb87f0dc8862f6c10e91e600071baa1f695c984e508eb3b2ec55352efd15273177080b0999d6c46c38aba6a7cb42b26ed159e6149e80f1e78b0c047595c01bc9b4b8fb790be8d225b93f27209256755355e82c7a4788c00c8ae9740b152953e32e6a008e1800a216ad0b684557b525e90d521e77260c9fe4c6f1e51233350b083272084c1446a6cb739816512c3ef627a285dd6ced12bbaf0ad8de531e8c25b0896d8021b29e7c6c767538558fec4885b1a4866172b19c800000055000000011481dd01300000000673480001b8c0004532e593808be64b2811b0e0001162801b4e7796a43a0db9c40c3b4a99c8ac8ff887612d08009b1dfc0000009892460000524f3853e000083200046295f001c0000b5911505e3076c88e80c7e24b61aafd4e5010731a80015784fac27b40ce068d42b20ff8eeebac2b088743bec570540000fa000000031418b23891f30000000811735282e3ec13d3a992c16b6647e8cadcd7a0ed02ce355d1900000001ce8f32000297af58ef401e9944975b9600064f374d602000000128d55bb794f12850000e782113400ea27c33ab3a54ae82663e126c042a96e29c18e5415b32ce497d4316c226b1000079e73740f04543f6a890002b2919e395678eae771ecccb44107516e982000000000046608bdfd159c9521da98c93b4cd24251bd46328c48bb0465d0c64e3878a688e625230fb89fa565cf45d32e425eaeb4da92b5da802432000c906e47469c9814e6d3930eb24dda2e9233311be52ba3643f1000055ef251ba904d8e2cf00001a146ecefc6797a79bdc231e22b79ccb28fe9b9386c19807100016ad86028af800cda6eeada04260f505a94a2d18f80cbc8ca05095706568844be97351a24bccfca02184c9f823506ac216846f54086832bbe93d580002a2a3d1c19d5474818c800368563045124b8000000373814e440000b7cf0b3a7dc1a0c27a10000e8100065daae423e05625d0001cb61bc000130567268d0001d72000dbe13fc000bfae3a28e3c9d10a7c1000080961ac6a000037fc7a9e8650bc0c04400012a0001b8800059d76551f80b16d70790a000001ddb9047900888001f9875200035e3641d5c84e4b18375d28000355110c9ce37a000347800000077b087054c00000000009f3734000104a0008130ec8000000c735de8910c560900001e450c0046d3f97c133dd2d0000c99e2494b12834815b83a531103d557c0004e
  | 31 => 0x218590b2606d62d220f23638b25e28d933aa4b01b821990419288609b294c944a772014ff40000e48004ae00aa63e9e5982a65d05cf7f186800000039a09b429b18b000139df404960000eb2eb036b19ac000cb221d8001532ecd12489889fc09cb799de0e94b9b0000b19e9802500023f20005ee3c79e21663a0f0d6e9e96ca370d0eba1dbd93400493a158562dd194a1843a8ec13290a2868c000490a39c0002c318a087209de5979a12de30210d6ffa405bfc8595cf9f94882000017c68c872bd80a18f022ee636e3f19983ab23a5d2977599a15c4b64a018b0ae933d0956930e144702294000e993409398f640002d2af2ef0aa5f01e91641c90001960edc000007b120481735a82e3c800000000069fe0ec0005273ad000046f00000000016aa10229d948893c00031b86fc00044d48280000003bd78da1ac96c35e1ee94c8bd463424f9478d12d5637b88f032a4f803583183143370c7135c36c8976991e1c28024aed5b2f000047700007dc9f70006950dcc385b588b3adeefec04de27001680440456fa4503fa8beac3bc09e2290fc92c3c4c5cf44056b8d9cdc361451ab616b34186701801916000497159402b0000150000000a08072800000093269f60cde48e8a3e380000005ba000000107046845917144e09720000adce6c3f00f092380003a26c19b0e8badf468cf03dabc1cf5882f63342f202171e8cec2a5c64a920c03033a1448bdd04a2a7bd406a9b3ee38bf181bd5280ca56c8ebd712e8102508c84a16da1d5b83220c2ff3c1bad1cf411215a1c3535db6231d3b75ac25de773245f710c9f05a5bb05def4d22826815c2420367978cfcb15e0a23618bf43079c2f444a0a6602bc278d9c6ad034c3938c4a3ad1164f9d3c2b71621152d0e069b682b24dafc2858c7f96b62827c697235448d949f2fb64dc089854ec115150ddec2af9830cb47ed763a8bc8a678943d0b2450d6be328cf281f340055a2f508609ed0840cf9422775354b8a5cfa11d5de2c48d0bde5cbb02e01d1e090c1a48f2f04233dee21839cc6510234f8bc8038b188df945d19d269035d215a6930a09091caee73b2a8145403fb6bd1e182e04f2f883561b84bf3695d911b16d660f00bf5d86c915202698f481f42718cd75aaa6d821aea872e43654aa9e03d800018f8001b7838398902816323d03939c0443ee7b407a2500005fe0000c8e602748d8791adb1ec2ceba1789d305f21d52dd134e00037f86ecd3444b67db39031e0b093207e5d3483a0000000000eef4a1000000000014f800000078a5c700005e895e2e0097c0000578003510644e965474001210a10664a2255543344656eb40d02474e5ef6c75831d22f8000000000000000185c0002e18c233c0f50020f44c1b700069114cc38f20829802c81da68058db1852f239a69ba510b7864d4b6208cf
  | 32 => 0x9e9fe0002fc809adcc0002400096005337afc40761c40d380000000000dea0c402a000000000000000073a994a98612152d00000009490002a6800000077827901550d1ee693d99ba4781eb1d70a86dbf25d8dcb5585751f525615d80002c000017fa00000038f741892beb913700a91a50c5df8039080052cb3d400047d2590000000000561c89cd06908800074fbbcb4f14d685c00000000fcb0943c25821eb46e6da94d1d674e2ddc67d58faf75a12b0928f80184aac2d13532a60f016ae5330590ec5b5476328131d1ff1a19a4c99e90c31b37c1c3a7ef3a78cbccc86319768a4cd03eb87a5144cbda22426f1c30760f3d71447a8d5ae8e74422ffc40bc8000329112647e01a4cafa4c63bf1934300000b05180becf711c5685b439d44c322e98a89bd565aae303e4f62c834a9ada400066a1fa1e549d000023080015e27802a6154d76264135891688360f300996f45a20000000000de29a300003aa174f0e27d9ffc653460516c00000096380018707500000001f2954628ed155b09c1d8391fc49ec1081620c480002aae916c10000000c3c4d703b816891955c0a9aac67c4712b37902a8b34f51a11cdfa3a07fa6f01d44715b3107d206d4559b9545b1493cc00aa85141f4674db92a42034846f0cb5bd400016a28298a4bff6b0380800012d23a55e99fa0fc0000000c4eb8700032d1c726f800c9b8dd76c4a4ed59a04a665b0107564ceec8177fb4b1c8c8b2bcc27d8b067092b4a6bc6a6d1c623e9c87e22f90f416c8e5a0cd6c29628ea03c74bd8300fb8c4d449064cd180c4004036cf6824c4e99d9cf28eac0ad08cb842814c5a8d343520ece403cc4d8640c973ad7948c0f88001859d94e8441f37ac00084967c416e4280000000894000f2fc63870e58100009b8944b12f390000000000000186000000000011eabd2000c6d7298000000b7a1cb36e021400046440000000005b80001bac0a8c1813287f591d00014309c800000d480d58976405d84690aa37f068a61092216c02f976c000c701fe0a30072000699b12ce300006b58000000000107a275748e5a57c0e619c40003f60000190000000000000068b33d8001b2c8441f9b4a39a0c945e6ac001b000000000019602be4e39da765264a4c08000000eab00015140005360348cd4477bc36612de00000820003c31db20007792b0123ccf40000aa4000b2d2e426b4a200003859ff1aec4c6000282c0000001bdf2fc000000564a0a878374c13b89a1a7889e2038000f548d35693484000ce508c0001704f31ef480fc000a4538e89d512200057d86911755be61dae14d8c60d5f70e4bd3a9ff1ce202c01629d6cc000050e223ef68001aa0e191d70000000d735f22c20cad55700014a53a4cbd58b9d8d4e8b240e8a56c12c55d08710d071810368ead8113242dcdf8425256014f
  | 33 => 0x25d118605b4371bc84141f05eb9b24442f3500000012682b648d00001e181900024f7ceecaf6ed8fb1a865dc590a9ec2c0dc91179ba1939bcc00027f50f631cd1c38faab46c134781ecdaeb361921b1590cbb916602f80005b605271909beae64a60cccd46c6200028a099cefd64c9962040ccb16dad317926b31c5377d4a247f7460dc58300001fb27d06b0d1206d00003c600079621349380483a0b0e800017e0000001cd897e1b30000000000274a934a9e049154d0e1ab60004ac6b1092a31a5e0843dd7ada90d7c9c81f0ab171c0a20a107b00b6cc8b2167470e62deabccce891f28d46547cf927005bbb259078145f115a10461c288dc5607e608aae3576aed5c332747707a209416a1bd7b40ca8b04d654df320422e52b894ab9d99b8ae65cc143d079ccec2876b1f6e5ac9c51bd87e838b56d021c561d9270834382218b601702e8c4c4e2bc7694859410eafc49387b84c26eb6f4105043f52e6fa56341ee194ae1132e786b72555a77601e66c00806703049474c700b538219063b34551828713850000682ea113442c72eef470002fd00000fb0bc733c13173f45829a00c808df1bf70444f8c66218994d3c5a25fb91a470f8a22c32ced63c73e52c3bcc494000790947bc908455ef86fa0e018632c1a993b3684b5b15dd92082c1d8e1d4990129047b5b4c0ca795ff05746beb4149e29f4370a563bdaf38ea434c0002f49a9e79f42d09e7c9e000000017920b00062fbc10000a2200000010e45b40001210a2c00000000007bc0001ec0001dda36f4f1481565ca253cd9c18a36c2f0a7832d35b6a804fdf4405eb591c9f5f012a1af34eda756b06d06d31a64778c48710d4500005595031d7cf1c30d0002370a9232cadc2b590ba4e1569862208487945ae7f35fabb06884ae94cce7644a8001d1e679240b345564294620084438c0000001c983407580003590bde00048f800142a000000183cdb0844a95a9d98829cfc3e148c000a20136822a0b809c275a390000de0288aa751f08bc7660de0b5ce3c43b99fcb3aeee11ae5ca8788543ae965c89c0e72ac0001198091000055051a2a80408001a8e29c5b3b5a956ea931591a5e2faef44e7a449386000000211c0005d11728a2c09c7a71c028689563099cf3199c38c3f72c0009c4dea665b8000dca00001ec09aa34a8565ab004a4ad01000257e000e9c000219c00077f6f08eb62600000000779b2e1e750757e56b8f130000000eaf1460000001b6a8800d56618676a99cb12664d40cdb04ea1e1c68b0280016c0000000175057de3014b00033040a679709c8b551380b3b248afc000b4034f80002da0000000046f3313f36900000003ee00000ea000a731c92473de20005628cf4000b6f60a00010bf0000002e895300000000001330435b282c711349fa76780014e56080000000
  | 34 => 0x934a4e631abdc401a8f2cfbcb906c7e45d392e5b1cc2c5a1026400000000000000000000000000a840000000000f9cee92e925854ee0006d000000000001ac8000000bd50002e68000000000241ce3e1db56a0a4a0005547395a5670e672447a84c192ab635eaaf37b4f3373a15f853272ca201df8f7db9faf382cce6a78c141a334b9c3796d88db0a3af4f5940ad49e2cac760255915e2f06fd543dce0a845c90d3982b07755031a4a02b3c1f1218d320f23536bb55a68dbd0bd8e057c262a14ed3252228321131bb4a14ee057700ada0c2d0440bb5d66ac314a19973908613576e86d4c0efe7549b54c7c45b29c90fda34394693a3008a47300a80d1486e3f9429202481edb40e99dc44f09c227120854c83ff4bfbce97d83a143200450400bc2312ecc48aee851f0892ab697a01d28c808a7c93a21e851ec60255bedfd68ce0549808e6de05f176911b96c62160793cd936bd100b8999d2c14d80fc1e7804b8354a031e1c5b3d34dd02d5608e624e6186cb7e3bf4ce0881e1a1ed6b1b23c7727f1338a5a949215639c7268b0400042ba3f4000c770002a6af38e7271b4000274642629a3750a000073f000152dc97430c0e000000005d4ed865d000242898c4820000002ab2000878e3400000005cb000174003721e6aab12559a9f1080a1f994a00000000ccf664335ad00017a2a31000010033208c0000000e72401042c00000000067c80300000005e00c2c18688700006481b29eb000000000000038bd0d20000002a3b4d87a2d18a451cc80000276c69554000ce906aa3d152f86536f9bf9b7477c1d996cd96c6ac6d220991b43c95642d7ca308c7e4604591041a65ceb60137a609000399917972c47a8b9800007600015f51f203e2492229be1d9c1aa0000ad0f437253c50011f16156ae6149e0002262db1326000775111c0005402386389bf1b6d63a38935e49a84232d1d7b8c6c00000003669046049c62000000000198cc615a700016bc3c30002a0800197c0c7000309464b0004c5290db28bfa00015ade160000220f94000612
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x5320c940c0e75591320c940c0d645cc5208540a0d831954208540a0f8558d4210840a0d8694d4210840c0d645ce520c840c0f75591320c840c0d75591320c840d05735084294440d05744c83294440d05735084254440d05744c83254440a31859856010440e21529856010440a0d839914294720a0d8498d3294720c0d545ce6290720a0d839954290720c0d7454e628c720a0d84995328c720c0d545cc6250320a14815516315120c0d735c86454d20c15641c55314d20a0d821cd6414d2081c875954310d20a14815954310d20a0d831516210d20a0d8414d6210d20a0e8550d6210d20a0c8550d6210d20a0c8654d4350920b048154d4350920b0481551434c920a0d831516210520a0d831954210520a0d8414d620c520a0d84195320c520a0d8315162d0120a0d8414d62cc120a0d839516210c20a0d8494d6210c20a0f8550d6210c20a0d8550d6210c20a0d825516310820a0d83d954210820a0f8558d4210820a0d8694d4210820a0d8654d4210820c0d645c9530c820a0d84d95320c820a0f85591320c820a0d86951320c820a0d86551320c820d05435c84394420d05735084294420d05744c83294420d05435c84354420d05735084254420d05744c83254420a61859856008420e21549856008420e4153985600842090d839cb5450b1090d839d35250b10a0d831954210b1090d849cf524cb10a0d84195320cb1090d831c95450a1090d831d15250a10a0d83d954210a1090d841cd524ca10a0d84d95320ca10c0d73d8a62d5110c0d735886215110c29625c06215110c0f645ce64d4910c0d74d8e63d4910c0d645cc6414910c29645c06414910c0d7458c6314910c49635c0631491090d839cb545091090d839d35250910a0d821516310910c0d7458c5210910a0d831954210910a0c8558d4210910c0e7558d4210910c0c7558d4210910a0f86d4d4210910a0d8614d4210910a248550a6110910c2875509601091090d849cf524c910c0d645cc520c910a0d84195320c910a0c85591320c910c0e75591320c910c0c75591320c910a0f86d51320c910a0d86151320c910a44854ca610c910c48754c9600c9109a1821c141501109a1841c121481109c1831c12148110c0d735886295010c0d735886255010c0d645cc6494810c0d7458c6394810c0d645cc6454810c0d7458c635481090d831c9545081090d831d15250810a0d829516310810c0d7458e5210810a0d83d954210810a0f8558d4210810c0f7558d4210810c0d7558d4210810a0d8694d4210810a0d8654d421081090d841cd524c810c0d645ce520c810a0d84d95320c810a0f85591320c810c0f75591320c810c0d75591320c810a0d86951320c810a0d86551320c810a24865506244010e055418c6244010c24761915244010c447618d5244010e046418d5244010
  | 1 => 0x2b05811c1535084290d859cf615084290f8754f615084290f8754e615084290d8754e6150842e0553584615084290e8754d605084290c8754d6050842d0553dc56050842d05531c5605084290d859cc605084290f8754c6050842d05539c46050842d05535c46050842c0f7654d42d4442a0d83dd94294442c0f735096094442a0d8694d4214442e095350a6014442e0a535096014442e09535096014442a0d831d94254042b21811c14254042c0d735086154042a0f8654d4214042c0f7654d4214042e055350a6114042e05535096114042b0681d954350932a8681d91428c932b06819cd544c832b05819cd544c83290d849c7654c83290f845c3654c832946819d9544c832b0681dd9544c832b0581dd9544c832b06819d9544c832b05819d9544c832c0d761d9544c832a0e86dc5544c832a0e869c5544c832d05711c5544c832a0c865c1544c832b07815c1544c832b04815c1544c832a0e861c1544c832b06811c1544c832b05811c1544c83290d859d3614c83290f87553614c83290f87552614c83290d87552614c832e0554584614c83290e87551604c83290c87551604c832d0554dc5604c832d05541c5604c83290d859d0604c83290f87550604c832d05549c4604c832d05545c4604c832c0f7655132d4432a0d84dd93294432c0f744c96094432a0d869513214432e09544ca6014432e0a544c96014432e09544c96014432a0d841d93254032b41811c13254032c0d744c86154032a0f865513214032c0f765513214032e05544ca6114032e05544c96114032a0f8558d4210b41a0d8694d4210b41c0d645ce520cb41c0f75591320cb41c0d75591320cb41c0d645ce520ca4184e87995320ca41c0d75591320ca41a8481591320c941a2980195424c841a0d831894254041929821c14154041a0d839516210f21a0d8494d6210f21a0f8550d6210f21a0d8550d6210f21a0f8558d4210b21a0d8694d4210b21a0f85591320cb21a0d86951320cb21c0d735ca64d4e21a0d821cd6494e2181e879954310e21a0d839516210e21a0d8494d6210e21a0f8550d6210e21a0d8550d6210e21a0d839516210621c85431c56210d2190d839cb5450821d09739c05450821c2a765c05450821d0a735c05450821d09735c05450821d22715c05450821929801d74350821929801d54350821d09749c0534c821c4a765c0534c821d0a745c0534c821d09745c0534c821d42715c0534c821949801d6434c821949801d5434c821a0d839914294421a0d8498d3294421c0d545ce6290421a0d831954210421c0d7454e628c421a0d84195320c421a0d831914254021a0d8418d3254021929841c12154021949831c12154021a0d839894294740a0d839915288740a0d839954288740c45631c55214940c0d645cc520c94084c87595320c940a448159
  | 2 => 0x48809000003e0001f8ea2e71c2aa0016eae000001ae8600038354d828c5f8cd1304858000d008c003e8f617400000080122a078d9000ac130820fc71258003ecd6074741ed091a2c824c041186109c34440f18bcf40d8473c8003f0850009d194480004e4842d2900039918000000007d000b580060018cd000a200000000a825c0f2d0da0008c000b50001a178018b8734145ec1d161e0e5269030909890c000011e1e8adc2c032806a060b637cde0c000000143b47c000b7800003305c1dcb8800c90f01b4007a8ac003385a2946c32d0e000d4000000002522c00000891105a8002919ce12f50d088004308d1bc9847c721730f200003fc0a370f714c00188794200020cdd05c5708000000002a4190003b318a61a40e002053cc504806e33c8412ca8800000009c474a70007638c353e4b1204d7390bb8001f0009f3a104468000b01c150c20a0494504a444eb4042101c004484f380e72dcaa328fe17c660e52329e00284e9254d326488000311ac97a6cb22b46c87e873b00034800000001d4ef100db2bc3200011245022e8261a06d2f10646c450008a3b857944002f85b0080c2ccfd428c545c3745459034e2000000000030cac800f280000154000007f14a92000ab23800464002fc958540024000000003040100000000f1108c40008f000002ecc02e4161c0d11aa3a13463278002e0520f8f00005625000104000003d0000b000003d410190b031c000000000013054020001808300208800080c06024020f05000060502000780009008120503008080d0200c020a02810040b02010000105004120500820040400800000000000000200004240000178040000800060401804040c020000e060080056000481c360100808160000000000e00000020005010040000034000cb06819c95350842b05819c95350842b06819d15350842b05819d1535084290d839c7655084290f835c36550842926819d95350842b0681dd95350842b0581dd95350842b06819d95350842b05819d95350842a0e86dc55350842a0e869c55350842d05711c55350842a0c865c15350842b07815c15350842b04815c15350842a0e861c15350842b06811c1535084
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 27
  | 6 => 1098
  | 5 => 6068
  | 4 => 3921
  | 3 => 292
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (510+((h/13+packedAt gbK7 (432+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (35646+((h/500+packedAt gbK6 (29646+(h % 500)*12) 12) % 2898)*12) 12
  | 5 => packedAt gbK5 (265696+((h/2508+packedAt gbK5 (230584+(h % 2508)*14) 14) % 15998)*14) 14
  | 4 => packedAt gbK4 (212214+((h/1545+packedAt gbK4 (192129+(h % 1545)*13) 13) % 5563)*13) 13
  | 3 => packedAt gbK3 (18483+((h/107+packedAt gbK3 (17520+(h % 107)*9) 9) % 426)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc3ffff87ffffff03f0fe1fff87ffffe88f1ff
  | 1 => 0x7fc1f0ff83e1f0ffc7f0fe1c3f870e1f774e93
  | 2 => 0x7ffe00fffc01ff1ff800ffe03ff80fe1878f1c
  | 3 => 0x800000fffffe001fffff00003ffff001f80fe0
  | 4 => 0xffffff000000001fffffffffc0000001fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4000008000000000001002400090200001025
  | 1 => 0x89461111942a102c31062089882245c334692
  | 2 => 0x510caaa228d548355888b5412d5049c5858b18
  | 3 => 0x43a94cc452906a59adaa11023664e089d80dc0
  | 4 => 0x6231888763198c9e36ccd99384408111eee000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_37421
namespace PEqualNP.Outside.L_meta_37421
open PEqualNP.Outside.L_meta_37421.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 292 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3776 : Interval gbAtlas 4 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3808 : Interval gbAtlas 4 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3840 : Interval gbAtlas 4 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3872 : Interval gbAtlas 4 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3904 : Interval gbAtlas 4 3904 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3921 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448)))) (concat (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672))) (concat (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 bgb_4_800)) (concat (concat bgb_4_832 bgb_4_864) (concat bgb_4_896 bgb_4_928))))) (concat (concat (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152))) (concat (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280)) (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 bgb_4_1664))) (concat (concat (concat bgb_4_1696 bgb_4_1728) (concat bgb_4_1760 bgb_4_1792)) (concat (concat bgb_4_1824 bgb_4_1856) (concat bgb_4_1888 bgb_4_1920)))))) (concat (concat (concat (concat (concat bgb_4_1952 (concat bgb_4_1984 bgb_4_2016)) (concat (concat bgb_4_2048 bgb_4_2080) (concat bgb_4_2112 bgb_4_2144))) (concat (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 bgb_4_2272)) (concat (concat bgb_4_2304 bgb_4_2336) (concat bgb_4_2368 bgb_4_2400)))) (concat (concat (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528)) (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656))) (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))))) (concat (concat (concat (concat bgb_4_2944 (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136))) (concat (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)) (concat (concat bgb_4_3296 bgb_4_3328) (concat bgb_4_3360 bgb_4_3392)))) (concat (concat (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520)) (concat (concat bgb_4_3552 bgb_4_3584) (concat bgb_4_3616 bgb_4_3648))) (concat (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 bgb_4_3776)) (concat (concat bgb_4_3808 bgb_4_3840) (concat bgb_4_3872 bgb_4_3904)))))))
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
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6068 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)))) (concat (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))))) (concat (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))) (concat (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))))) (concat (concat (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)))) (concat (concat (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456)) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))) (concat (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))))) (concat (concat (concat (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936))) (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416)) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))) (concat (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)) (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)))) (concat (concat (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992)) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))) (concat (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)) (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280))))) (concat (concat (concat (concat bgb_5_5312 (concat bgb_5_5344 bgb_5_5376)) (concat bgb_5_5408 (concat bgb_5_5440 bgb_5_5472))) (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856))) (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))))))))
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
theorem bgb_6_1088 : Interval gbAtlas 6 1088 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1098 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 27 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeeeaeaa8aaa0aaa0eeeaeaa8aaa0aaa0eeeaeaa8aaa0aaa0eeeaeaa8aaa0aaa0eeeaeaa8aaa0aaa0eeeaeaa8aaa0aaa0eeeaeaa8aaa0aaa0eeeaeaa8aaa0aaa0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,3,35)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,3,35)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264008 * 2 ^ 32 + 3937053312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37421.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[3,4]⟩,⟨.and,[6,7]⟩,⟨.or,[6,7]⟩,⟨.and,[3,4]⟩,⟨.and,[1,5]⟩,⟨.or,[10,11]⟩,⟨.or,[0,8]⟩,⟨.and,[0,9]⟩,⟨.and,[12,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264008 * 2 ^ 32 + 3937053312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264008 * 2 ^ 32 + 3937053312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37421

open PEqualNP.Outside.L_meta_37421 in
theorem PEqualNP.Outside.L_meta_37421 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264008 * 2 ^ 32 + 3937053312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264008 * 2 ^ 32 + 3937053312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
