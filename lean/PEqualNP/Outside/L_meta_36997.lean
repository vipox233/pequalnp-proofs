import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36997.Model
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


end PEqualNP.Outside.L_meta_36997.Model

namespace PEqualNP.Outside.L_meta_36997
open PEqualNP.Outside.L_meta_36997.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 5, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36997

namespace PEqualNP.Outside.L_meta_36997
open PEqualNP.Outside.L_meta_36997.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x400025a809184a031c800c7be42bc42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1180c400940418c420ca58a4a0ce14141a7294632e5290298a4985514530
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (208+((h/4+packedAt s0K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s0K3 (197+((h/2+packedAt s0K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 2 => 0xffc0fffffffffffff81ff80fffffffffe38fff
  | 3 => 0x3fff01fff80fe03fffe0fff03ffc0f80fcf3cc
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4a4414423122490a01652a544a2194aa0d3615
  | 2 => 0x909228a442449414580a510a94c629546288ea
  | 3 => 0x230a4d2890e90566aaa09d6227688e06b4d34c
  | 4 => 0x3a2cb1d12481d9bb34d3064c39b3c418df03b0
  | 5 => 0x3c30c1e1c70e1e3dc71ce78f01c30860fbec00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36997
namespace PEqualNP.Outside.L_meta_36997
open PEqualNP.Outside.L_meta_36997.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x340088028007804800a8038000004c00b8a181800000491253aa00003e084000001580000000108010800064d80200000352011800001380160068500a8000001c00000600003c00000004c00e0058020000000012000000102002000608000000c001ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x50d09801125018028060e9f000f801e9a0b02001a802b16a285a395a580002a0f27a926891ca204198b9421ad0c9012a8ac981711ada4ab961d1c0700000e29811080260a9480000323191380079e211520a4200c131d88868a120017ac00802a801f8027048288001b1880039b8d80011a2000c52480000040d00000400628000030824c020400101bba8a87745150e7ca1a14f55242afa9a855c5350aeea2a15d14542bda8285785050b3ea6a16714d42d7a9285b75150b68a2a16ed41429e28285b85050a70a0a14f95042bb28e657551cca7ca9194f55232bb28c6575518ca7ca8194f55032afa9a835c535067ea898cf15131ea988633e54c867aa990d794f21aea9e435e53886baa710cf950219eaa0435e53902baa7205d94640baa8c819e539033aa7204f54a40db28c81b5519027ca1204f548409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2eca2185d544309f2a6413d54c837081904fd52209e2a4413f5448278a89057d4d20ae29a417751482e8a2904f950209eaa0415e53082baa6105d94420baa8841b8400827ca9884f553109faa2213c54442bea6885714d10b7a92216c52442bca6085754c10
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x20406aec809c514c5150b1b5314142c614c5050b335114142cc1445050a94644c431c594e51902396510020
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
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (802+((h/14+packedAt s1K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s1K4 (2694+((h/30+packedAt s1K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s1K3 (312+((h/2+packedAt s1K3 (304+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0x3f80ffffe03f81ff83f03e0ffffc1f01d89fcc
  | 3 => 0x3fff03fffffffffffc003ff03fffffffe0e3ff
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x848a1008c489082014b14a114a2129540b2e15
  | 2 => 0x9526299143922ae58155168d96e51a0cd896cc
  | 3 => 0x22144aa20924614aa80825a4254a54a960c16a
  | 4 => 0x3458b34492074db34e6d810939b38831bd03b0
  | 5 => 0x3860c3871c3871dc738e39ce01c210c1f6f800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00faaaaaa0fa00aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36997
namespace PEqualNP.Outside.L_meta_36997
open PEqualNP.Outside.L_meta_36997.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4801e560111742a0d01046000d00000000a9470b22291991e00a000000380000000300006150000f8010000003a01200004c0044ea8000005901b12a531c0018802800c0430000001820604180ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa40e465e9e000a164800244c002e00000032a23c9a5c00000044a05a1a7e000000962870b69c64b25800001c004e545098001e007400a6663800608e00009492b0006a04363006782a3a007600080014407c828c000000000000b48800008602800000000000524290a82c008aac00000c12007a56226eae20846c0026004a18000000aa0010003e000000620000006834720001030004000001000b030305000000010016030408020600060302000301bba8a87745150eeca3a15d54742af29c855d5390aeca3215d54642af298855d5310abca1995754e329faa2653c544caeea2995d14532bda826578504cb3ea8996715132e7a9265d7514cba8a29976d4132ae28265d8504cab0a0995794c32afa9a835c535076a8220cfd51319e2a2633e54c867aa990d794f21aea9e433e548867aa910d794c21aea98435e53d02baa7a057d4d40ae29a816f52502d8a4a05dd4540ba28a817651102eaa2204f952309eaa46176518c2eaa3186795230ceaa4615d528c3aca3187554630af284615d520c2bca0187694030af29e415d53c83b0619057d4e20ae29c413f5448278a89057d4d20ae29a417751482e8a2904f950209eaa0415e53082baa6105d94420baa8841d830082bca7885754f109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x32090029800003800001c5150514cb1b5414132c6150504cb535114132d4144504ca946350441c5952518c259650c020
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 5 => packedAt s2K5 (802+((h/14+packedAt s2K5 (704+(h % 14)*7) 7) % 75)*7) 7
  | 4 => packedAt s2K4 (2724+((h/30+packedAt s2K4 (2484+(h % 30)*8) 8) % 147)*8) 8
  | 3 => packedAt s2K3 (314+((h/2+packedAt s2K3 (304+(h % 2)*5) 5) % 17)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xff81ffffffffffe07ffffe03fffffffe3f8fff
  | 1 => 0x3ffe03f80fff81ff83f03ffc1f07ff01d8f27c
  | 3 => 0x3ffffffff03ffffffc003ffffff81fffe0ff8f
  | 4 => 0xc00003ffffc001ffffffc0001fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80a428892209204014b24a41250a31540b84b5
  | 1 => 0x950c9990e4922ae5815616d50b475a0cd8b25c
  | 3 => 0x2610522241a4492aa808251a52d10ca9605b0a
  | 4 => 0x3459634489074db34e6c81921ce58831f503e0
  | 5 => 0x386183870e3871dc738f39e3808610c1beec00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaee00aa88aa00eeaaee00aa88aa00eeaaee00aa88aa00eeaaee00aa88aa00eeaaee00aa88aa00eeaaee00aa88aa00eeaaee00aa88aa00eeaaee00aa88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36997
namespace PEqualNP.Outside.L_meta_36997
open PEqualNP.Outside.L_meta_36997.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfc07ffc07ffc0783fffffc0ffe07ff007f9e7c
  | 1 => 0xfff81ffffffffffc0fc07ff03fffffff98e3ff
  | 2 => 0xffffffff81fffffff0007ffffff81fffe0ff8f
  | 4 => 0x1ffffe0007ffffff80003fffe001ff03f0
  | 5 => 0xffffe000000007ffffffffffc0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2530c4471448a980b2ca9c854e43390c2b8e3c
  | 1 => 0x88524c892091831405582594128e525498a0d5
  | 2 => 0x30a111120d2224a950224a29a5510ca960570a
  | 4 => 0xa2c59a24483b36ce69b3030939e58831f503e0
  | 5 => 0xc3061c3871c3c7738e3c73ce018610c1def800
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0c8c8c0c0eaeae0e0c8c8c0c0eaeae0e0c8c8c0c0eaeae0e0c8c8c0c0eaeae0e0c8c8c0c0eaeae0e0c8c8c0c0eaeae0e0c8c8c0c0eaeae0e0c8c8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36997
namespace PEqualNP.Outside.L_meta_36997
open PEqualNP.Outside.L_meta_36997.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2126119001801d2000b95102a3cb06127071b020129e16895a72815c2d480de35001d63330f8fb76035fb65ee5a1722a40190420000000130000c519d00f5d8a5068012000a08203000000128082010aa804400c0105bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (731+((h/13+packedAt s4K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 2 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 2 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 3 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0eee0eee0eac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36997
namespace PEqualNP.Outside.L_meta_36997
open PEqualNP.Outside.L_meta_36997.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1c813be00140825a4dfa622e5b190034aba0600000700003560b0c3434480007801dab0050b176eb928a467d4a13a40209626c00b00cc01e001800c00000225e0151c50c83a41e2003d05040818f003808100042802c000040c08400bda8287785050eeca221dd54443bba8a85745150af4a0215e540429f2a6653d54ccaeca3995d547329f2a4653d548caf4a1195e54232b7a92836c52506bca620d754c419faa2633c544c6dea498db14931bda826378504c67ca818cf550319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502dca4205b548409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309faa2413c54482bea6905714d20bba8a4174514827ca8104f550209f2a6213d54c42bca7885754f109f2a4213d54842dca5085b54a10
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (718+((h/13+packedAt s5K5 (640+(h % 13)*6) 6) % 49)*7) 7
  | 4 => packedAt s5K4 (1875+((h/21+packedAt s5K4 (1728+(h % 21)*7) 7) % 84)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307c1fffc1ff0ffffe011e73fc
  | 1 => 0xfffffc0fc1ffff801f07fffff0f01ffe13fccf
  | 2 => 0xf83ffff001ffffffe007fe0fff001fffe38f0f
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 4 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x309118a2904250150549d0930914d21906315c
  | 1 => 0x51222864229422820b82632590a144aa10d4c5
  | 2 => 0xa29451019522152d2044948a2a029951630b0a
  | 3 => 0xc52882492034a9ca5290210cc4cb0062b80ea0
  | 4 => 0x630e38e39c73e739ce739c0888c1183dfe000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36997
namespace PEqualNP.Outside.L_meta_36997
open PEqualNP.Outside.L_meta_36997.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001027fd5007fe54007f55007fc54027fd4c01fe53007f54c09fc5301ffd0c01fe43007f50c07fc43027fd4805fe52007f54805fc5201ffd0805fe42007f50805fc42007fcc805fe32007f4c805fc32027fd4403fe51007f54403fc5101ffd0403fe41007f50403fc41007fcc403fe31007f4c403fc31017fc8403fe21007f48403fc21027fd4001fe50007f54009fc5001ffd0001fe40007f50007fc40007fcc001fe30007f4c001fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x82400dffd012002ffc8090003fd404800bfe2024000ffcc12002ffc6090003fd304800bfe1824002ffc8120017f64090017fe204800bf71024005ff0812002fd8409000bf82048019ff8824005ff0412002ffecb08016ff658400bff32c2004bf9961002ffacb08002fd658400bfe32c2005bf1961002ffec908016ff648400bff3242003bf9921002ffac908002fd648400bfe3242005bf1921005ffea90802bfe5484001feaa4200aff1521002ffec708016ff638400bff31c2000bf98e1002ffac708002fd638400bfe31c2005bf18e1005ffea708003fe5384001fea9c200bff14e10057fe8708003fe4384001fea1c200aff10e1002ffec508016ff628400bff3142002bf98a1002ffac508002fd628400bfe3142005bf18a1005ffea508027fe5284001fea942009ff14a10057fe8508027fe4284001fea142009ff10a10007fe6508027fe3284001fe9942009ff0ca1000dfac308007ff5184003ff28c2001ff5461000ff8a308007ff4184003ff20c2001ff5061000ff88308007ff3184003ff18c2001ff4c61000ff86308007ff2184003ff10c2001ff4861000ff84308016fe608400bffa842005ff9421002ffaa108017fc508400bffa042005ff9021002ffa8108017fc408400bff9842005ff8c21002ffa6108017fc308400bff9042005ff8821002ff44108017fd2084001fc9042005ff0821002ffe2108017f71084003fd8842005ff0421002ff02108003ff65440017fb2a2000dfd9510004feca88023fe65440097f32a2000ff59510005faca88023fc65440097e32a2000df19510024f8ca88003ff64440017fb222007ff9911001dfcc888003fd64440017eb222007ff1911001df8c888023ff544400fff2a22000ff5511003ff8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c688023ff5344001ff29a2000ff54d10047f8a68801fff4344001ff21a2000ff50d1003ff88688003ff62440017fb122006ff98910015fcc488003fd62440017eb122006ff18910015f8c488023ff524400dff2922000ff54910037f8a48801fff424400dff2122000ff50910037f88488003ff324400dff1922000ff4c910037f86488016ff6144003ffa8a2001ff9451000feca288007fd5144001faa8a2001ff1451000ffe8288007fe4144003fea0a2001ff1051000ffe6288007fe3144003fb18a2001ff4c510007ea6288007fc3144003ff90a2001ff8851000ffa4288007fc21440037fb022008ffd411002ffca088003fd504400bfe2822007ffd011002ffc8088003fd404400bfe2022000ffcc11002ffc6088003fd304400bfe1822006ffc811002ffc4088003fa2044001fe9022000fe4811002ff84088007ff1044003fd8822005ff8411002fec2088017fc104400bfa0822001fe04110
  | 1 => 0x6fe610c00bfb3086001bd9843002ffac218002fd610c00bfab086000bd5843002ff8c218016fc610c02dffa886012ff94430007faa21804bfc510c02bffa086012ff90430007fa821804bfc410c029ff9886012ff8c430007fa6218053fc310c027ff9086012ff88430007fa421804bfc210c00b7f3006005ffd403002ffca018017fd500c00bfe2806005ffd003002ffc8018017fd400c00bfe2006005ffcc03002fbe6018017fe300c00bfd1806005ff4c03002fba6018003f9300c00bff9006005ff0803002ffe2018017fc100c00bffb2c4005bfd962002ffccb10012fe658800bfeb2c4000bf5962002ff8cb10016fc658800bffb244005bfd922002ffcc91000efe648800bfeb244000bf5922002ff8c910016fc6488023ffaa44010ff95220007faa910043fc548800bffb1c4005bfd8e2002ffcc710002fe638800bfeb1c4000bf58e2002ff8c710016fc6388023ffa9c4000ff94e20007faa710047fc5388021ffa1c4000ff90e20007fa8710043fc43880057eb144002ffd4a20017fca51000bfd5288005fe2944002ffd0a20017fc851000bfd4288005fe2144002ffcca20017fc651000bfd3288005fe1944005ffd862002ffcc310006fe618800bfeb0c4000bf5862002ff8c310016fc6188023ffa8c400fff94620007faa31003ffc5188021ffa0c400fff90620007fa831003ffc4188001ff98c400fff8c620007fa631003ffc3188005ff90c4002ff88620017fa431000bfc218800b7f3044005ffd422002ffca110017fd508800bfe2844005ffd022002ffc8110017fd408800bfe2044005ffcc22002ffc6110017fd308800bfe1844005ffc822002fde411000bfb208800bfe1044005fe0822002ffe2110017fc1088001ffb2a4000bfd9520077fcca90012fe6548001feb2a4000bf59520077f8ca90012fc6548001ffb224000bfd91200077ec890002bf644801bff3224003bf99120007fac890002fd644801bfe3224003bf1912000778c89000ebc644801dffaa2400dff95120007faa890037fc5448001ffb1a4000bfd8d20007fcc690002fe6348001feb1a4000bf58d20007f8c690002fc634801dffa9a4000ff94d20007faa69003bfc534801bffa1a4000ff90d20007fa8690037fc434800b7fb124002ffd4920017fca49000bfd5248005fe2924002ffd0920017fc849000bee4248005fea124000fb50920017f8849000bff3248005ff1924002fb8c920017fa6490003ed3248005fe1924000ffd8520005fec290033fe61480037f30a4000ff58520067f8c290006fc614801dffa8a400cff94520007faa290033fc514801bffa0a400cff90520007fa8290033fc4148001ff98a400cff8c520007fa6290033fc3148005ff90a4002ff88520017fa429000bfc21480057fb02400effd412002ffca090003fd504800bfe2
  | 2 => 0x30007fca718003fd538c03dfe29c601dffd0e30007fc8718003fd438c03bfe21c6005ffd8a3002ffcc51800afe628c00bfeb146000bf58a3002ff8c518016fc628c03dffa94601cff94a30007faa518073fc528c03bffa14601cff90a30007fa8518073fc428c001ff994601cff8ca30007fa6518073fc328c00bffb0c6005ff9863000dfcc318017fd618c0017eb0c6005ff1863002df8c31807bff518c037ff28c6000ff546300dff8a318077ff418c037ff20c6000ff506300dff88318003ff318c037ff18c6000ff4c6300dff86318073ff218c037ff10c6000ff486300dff84318016fe608c00bffa846005ff9423002ffaa118017fc508c00bffa046005ff9023002ffa8118017fc408c00bff9846005f7cc230007f66118017ff208c00bfe1046005ffc423002ff82118003ff654c0017fb2a6000dfd9530004feca9806bfe654c0097f32a6000ff59530005faca9806bfc654c0097e32a6000df19530024f8ca98003ff644c0017fb226000efd91300057ec898067fe644c0077f3226000ff59130005fac898067fc644c0077e3226000ef1913001d78c89806bff544c033ff2a26000ff551300cff8a89806bff534c001ff29a6000ff54d300d7f8a698067ff434c001ff21a6000ff50d300cff88698003ff624c0017fb126018ff98930015fcc498003fd624c031fe3126002bf189300d7fea498063fe524c001fea926018ff149300cffe8498063fe424c001fea126018ff10930007fe6498063fe324c001fe9926018ff0c930007fec298002ff614c02fff30a6001bf98530007fac29805ffc614c0037e30a601affd45300bffca298003fd514c02ffe28a6019ffd05300bffc8298003fd414c02ffe20a6000ffcc5300bffc6298003fd314c02ffe18a6018ffc85300bffc4298003fd214c02ffe10a601affd413002ffca098003fd504c00bfe2826019ffd013002ffc8098003fd404c00bfe2026000ffcc130007f66098017fe304c00bef1826018ffc813002ff8409805fff104c00bfe0826005ffd943002dfeca18017fe650c0097f3286005df99430024fcca18017fd650c0017eb286005df59430004faca18017fc650c00b7e3286005ffd903002dfec818017fe640c0077f3206005ef9903001d7cc818017fd640c0017eb206005ef590300057ac818017fc640c00b7e3206016ffd50300affca818003fd540c02bfe2a06000bf98c300b7fea618053fe530c001fea986014ff14c300affe8618053fe430c001fea186014ff10c3002ffec418017fe620c0057f3106005fb98830015dcc418017fd620c0017eb106005fb58830005dac418017fc620c00b7e3106016ffd483009ffca418003fd520c027fe2906015ffd083009ffc8418003fd420c027fe2106014ffcc83009ffc6418003fd320c029fe1906005ffd843002ffcc21800
  | 3 => 0xe28c8003ffd064001f7e832000ffe4190007fea0c8000ef5064001ff88320003ff319004dff18c8000ff4c640137f8632009fff219004dff10c8000ff48640137f84320016fe609000bffa848005ff9424002ffaa120017fc509000bffa048005efd024001ff68120017fc409000bfc2048005ffc824002ff84120017ff109000bfe0848000ffd9540005fecaa0097fe65500097f32a8000ff59540005facaa0097fc65500097e32a8005bfd914001ffea8a000ffe5450007feaa28003ff15140007fec6a0002ff6350001ff31a8000ff58d40007f8c6a0002fc635004bffa9a8000ff94d40007faa6a0097fc5350007ffa1a8003efd0d4001ffc86a000ffd4350001dea1a8003ff10d40007fec4a0002ff6250049ff3128002bf98940007fac4a0093fc62500057e3128025ffd4940127fca4a0003fd5250049fe2928003ffd094001f7e84a000ffe4250007fea128000ef5094001ff884a0003ff3250049ff1928000ff4c940127f864a0003ff61500017fb0a8023ff9854000dfcc2a0003fd6150047fe30a8001bf1854012ffea2a008ffe5150001fea8a8023ff1454001ffe82a000ffe4150007fea0a8003ff10540007fe62a008ffe3150001fe98a8023ff0c540127fe42a008ffe2150001fe90a8023ff0854001dfec0a0097ff505000bff2828000ff5414002ff8a0a000fff4050007fda028005ff9014002f7c80a0017fc405000bde2028003fe10140127fe40a0017fc2050047ff8828005ff041400a7fecb98002ff65cc045ff32e6004bf99730007facb98002fd65cc029fe32e6004bf197300a7fec998002ff64cc043ff3266003bf99330007fac998002fd64cc029fe3266003bf19330117fea998087fe54cc001feaa66021ff15330117fea798053fe53cc001fea9e6014ff14f3010ffe8798053fe43cc001fea1e6014ff10f300a7fec598083fe62cc0057f3166000ff58b30005fac598053fc62cc0057e3166022ffd4b30107fca598003fd52cc041fe2966021ffd0b30107fc8598003fd42cc041fe2166014ffccb30107fc6598003fd32cc029fe1966014ffd87300fffcc398006fe61cc001feb0e6000bf587300a7f8c398006fc61cc045ffa8e601fff94730007faa39807ffc51cc043ffa0e601fff90730007fa839807ffc41cc029ff98e601fff8c730007fa6398053fc31cc041ff90e601fff88730007fa439807ffc21cc045ffa866005ff94330007faa198017fc50cc043ffa066005ff90330007fa8198017fc40cc041ff9066005ff083300fffe2198017fc10cc00bffb2c6005bfd963002ffccb18012fe658c00bfeb2c6000bf5963002ff8cb18016fc658c00bffb246005bfd923002ffcc91800efe648c00bfeb246000bf5923002ff8c918016fc648c03dffaa4601dff95230007faa918077fc548c0017eb1c601effd4e
  | 4 => 0x13fc549400bffb1ca005ff98e50005fcc728017fd63940017eb1ca005ff18e50027fea728013fe5394001bf29ca004ff54e50027f8a7280137c539405dffa1ca000ff90e50007fa87280bbfc439400bffb14a005ff98a50015fcc528017fd62940017eb14a005ff18a5002df8c528013ff5294009bfa94a004ff94a50027faa5280037d5294009fe294a02effd0a5016ffc8528003fd429405bfe214a000ffcca5016ffc6528003fd329405bfe194a005ffd865002ffcc328006fe619400bfeb0ca000bf5865002ff8c328016fc6194009ffa8ca004ff94650166fca328013fd5194009fe28ca004df14650177fe83280b3fe4194001fea0ca02cff10650007fe63280b3fe3194001fe98ca02cff0c65016ffe43280b3fe2194001fe90ca02cff0865002dfcc128017ff509400bbfa84a004fed425002ff8a128017f8509400bffa04a005ff1025002ffe4128017fc209400bff884a005ff0425002dfecaa8003ff64540017fb22a02bff9915001dfcc8a8003fd6454057fe322a003bf19150027fea8a8013fe5454009feaa2a004ff15150007fec6a8002ff6354001ff31aa000ff58d50007f8c6a8002fc6354009ffa9aa004dfd4d50027fca6a8013fd5354001bea9aa004ff14d5015ffe86a8003fe4354001fea1aa02bff10d50007fec4a8002ff6254055ff312a002bf98950007fac4a80abfc62540057e312a004ffd4950027fca4a8013fd5254009fe292a02bffd0950157fc84a8003fd4254055fe212a000ffcc950157fc64a8003fd3254055fe192a000ffd8550005fec2a80a7fe61540037f30aa000ff5855014ff8c2a8006fc6154009ffa8aa004dfd4550027fca2a8013fd5154001bea8aa004ff1455015ffe82a80a7fe4154001fea0aa029ff10550007fe62a80a7fe3154001fe98aa029ff0c550157fe42a80a7fe2154001fe90aa029ff08550025fec0a8013ff5054009fda82a005ff9415002efca0a8017fc505400bbe282a004fe1415015ffe80a8017fc4054055ff902a005ff0815014ffe20a8017fc105400bffb2c8005bfd964002ffccb20012fe659000bfeb2c8000bf5964002ff8cb20016fc65900077eb248003ffd524001ffca92000ffd5490007fe2a48005ffd8e4002ffcc720002fe639000bfeb1c8000bf58e4002ff8c7200a3ff5390001ff29c8000ff54e40147f8a72000fff4390007ff21c8000ef90e4001ffa872000ffc4390007de21c8005ffd8a4002ffcc52000afe629000bfeb148000bf58a4002ff8c520016fc6290051ffa948027ff94a40007faa52009ffc5290007ffa148003ff90a4013f7c852000ffd4290007fe2148003ef10a40007fe652009ffe3290001fe9948027ff0ca4002ffec320017fe61900037f30c8005ff58640005fac320017fc619000b7e30c8028ffd4640137fca320003fd519004df
  | 5 => 0x4b31007faa5988d3fc52cc46bffa166234ff90b31007fa85988d3fc42cc429ff9966200f7ccb311a7fc6598803fd32cc401ee9966214ff0cb3100dfac398807ff51cc403ff28e6201ff5473100ff8a398807ff41cc403ff20e6201ff5073100ff88398807fe31cc403ef18e6201fd8c73100ff86398807dc31cc403ff90e6201ff8873100ff84398853ff60cc401ff3066205bf98331007fac198802fd60cc429fe3066236ffd43311b7f8a1988d7ff40cc46bfe2066234ffc83311a7f84198807ff10cc403fe0866200ffd9531005feca988cffe654c4097f32a6200ff59531005faca988cffc654c4097e32a6200ffd9131005fec8988cbfe644c4077f3226200ff59131005fac8988cbfc644c4077e3226233ffd5131197fca898803fd544c465fe2a26201bfd8d3119ffea698803fe534c401fea9a6233ff14d31197fe8698803fe434c401fea1a6232ff10d31007fec498802ff624c463ff3126202bf98931007fac4988c7fc624c4057e3126233ffd493118ffca498803fd524c463fe2926232ffd093118ffc8498803fd424c463fe2126200ffcc931007be64988c7fe324c401fe9926200f74c93118ff86498806ff614c403ffa8a6201ff9453100ffaa298807fc514c403ffa0a6201ff9053100ffa8298807fc414c403ff98a6200fdcc53100ffc6298807de314c403fe18a6201f70c53100fe86298807ff214c403ff10a6201ff08531007fec098802ff604c401ff3026200ff58131007f8c098816fc604c467ffa826233ff14131197fe80988cbfc404c463ff9026231ff0813100ffe2098807f7104c403fe0826200ffd9521005feca908c3fe65484097f32a4200ff59521005faca908c3fc65484097e32a4200ffd9121005fec8908bffe64484077f3224200ff59121005fac8908bffc64484077e3224230ffd512117ffca890803fd544845ffe2a24200ffd8d21005fec690803fe63484017f31a4200ff58d21005fac690803fc63484017e31a4230ffd4d21007fca690803fd5348461fe29a422fffd0d21007fc8690803fd434845ffe21a4201bfd8921017fea49080bfe5248405fea924202ff14921017fe849080bfe4248405fea124202ff10921017fe649080bfe3248405fe9924202ff0c92100dfec290807ff5148403ff28a4201ff5452100ff8a290807ff4148403ff20a4201ff5052100ff88290807ff3148403ff18a4201ff4c52100ff86290807ff2148405fb90a4201ff8852100fdc4290807fc2148403f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090816fc6048461ffa824230ff1412117ffe80908bffc4048405ff9024202ff0812100ffe2090807fc10484097eb2ca005ffd925002ffcc92800efe649400bfeb24a000bf5925002ff8c928016fc6494009ffaa4a004ff95250027faa928
  | 6 => 0x5ff10a6402ff08532007fec099002ff604c801ff3026400ff58132007f8c099016fc604c87bffa82643dff141321e7fe80990f3fc404c805ff9026402fbc8132017f840990efff104c877fe0826401bfd9551007fec8a8802ff6454475ff322a203bf99151007fac8a88ebfc64544077e322a204ffd5151027fca8a8813fd5454409fe2a2a200ffd8d51005fec6a8803fe6354401feb1aa200ff18d51005f8c6a8813ff5354409ff29aa200df94d51027faa6a8813fc5354409be29aa23affd0d51007fc86a8803fd4354475fe21aa200ffd8951005fec4a88e7fe62544057f312a200ff589511cff8c4a880afc6254409ffa92a204dfd4951027fca4a8813fd5254401bea92a204ff149511d7fe84a88e7fe4254401fea12a239ff10951007fe64a88e7fe3254401fe992a239ff0c95100dfec2a8807ff5154409fba8aa201ff9455100efca2a8807fc5154403be28aa201fd1455100ffe82a8807fe4154403fe20aa201ff8c55100ff862a8807ff2154403ff10aa201ff08551007fec0a8802ff6054401ff302a200ff58151007f8c0a8816fc6054409ffa82a204dfd4151027f8a0a88ebff4054475fe202a239ffc81511cff840a8807ff1054403fb882a201ff04151007fecaa0802ff6550471ff32a8204bf99541007facaa0802fd6550471fe32a8204bf1954100dfec8a080fff5450407ff2a28203ff5514101ff8a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc63504017e31a8238ffd4d41007fca6a0803fd5350471fe29a8203ffd0d4101f7e86a080ffe4350407fea1a8200ef50d4101ff886a0803ff62504017fb128237ff98941015fcc4a0803fd625046ffe3128202bf189411c7fea4a08dffe5250401fea928237ff1494101ffe84a080fbf4250407ff2128203ff509410077a84a080ffc4250401ff9928237ff8c941007fa64a08dffc32504037fb0a8201ffd454100ffca2a0807fd5150403fe28a8201ffd054101fee82a0807fe4150403df20a8201ff1054100f7882a0807f44150403ff18a8201ff0c54100ffe42a0807fe2150403fe10a8200ffd8141005fec0a0803fe6050401feb028200ff1814102df8c0a08e3ff5050471fe2828203ffd014101ff880a080fbc405046fff9028237ff0814100ffe20a0807fc1050429ffb2e6200bfd97311b7fccb98812fe65cc401bf32e62049f99731007facb98802fd65cc401beb2e62009f597310a7f8cb98812fc65cc429ffb266200bfd93311affcc99880efe64cc401feb266200bf593310a7f8c99880efc64cc46dffaa66235ff95331007faa9988d7fc54cc4037f31e6236ffd4f310a7fca798803fd53cc429fe29e6235ffd0f310a7fc8798803fd43cc429fe21e6214ffd8b311a7fcc59880afe62cc401feb166200bf58b310a7f8c59880afc62cc46dffa966234ff9
  | 7 => 0xa900bfc2054887ff882a443ff04152007fecaa1002ff6550885ff32a8404bf99542007facaa1002fd6550885fe32a8404bf19542015fec8a100fff5450807ff2a28403ff5514201ff8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc63508017e31a8442ffd4d42007fca6a1003fd5350885fe29a8403ffd0d4201ffc86a1003be4350807fea1a8403ff10d4201f7886a100aff6250805ffa928402ff94942017faa4a100bfc5250805ffa128403fbd0942017fc84a100bbe4250805fe2128402ef10942017d884a100bfe3250805fe1928400ffd8542005fec2a1107fe61508037f30a8400ff5854220ff8c2a1006fc6150885ffa8a8441ff9454220ff8a2a100fff4150807dfa0a8403ff9054201ff882a1107fe3150883fe18a8402ffc8542017fc42a100bfc2150801ffb028400bfd8142007fcc0a1003fd6050801fe3028405bf18142217fea0a110bfc5050807ffa028403efd014201ff880a100bff2050805f79028402ff0814220ffe20a1107fc1050829ffb2e6400bfd9732207fccb99012fe65cc801feb2e6400bf597320a7f8cb99012fc65cc829ffb266400bfd93321fffcc99900efe64cc801df3266403af99332007fac999002fd64cc801deb266400af593320a7f8c99900efc64cc881ffaa6643fff95332007faa9990fffc54cc8057f31e6440ffd4f320a7fca799003fd53cc829fe29e643fffd0f320a7fc8799003fd43cc829fe21e6402bf58b32017fea59900bfe52cc805fea966402ff14b32017fe859900bfe42cc805fea166402ff10b32017fc659900bde32cc805f71966402ff0cb32017b86599053ff61cc87dff30e6401bf98732007fac399002fd61cc829fe30e6401bf18732207fea3990fbfe51cc87dfe28e643fffd07321f7fc83990fbfc41cc87dff18e6414ff0c732017fe439900bfe21cc805fe10e6414ffd8332007fcc199016fe60cc801feb066400bf583320a7f8c199103ff50cc881fe286643fffd03321fff8819900bff20cc805fe106643effc43321f7f82199003ff654c8017fb2a643dff99532025fcca99003fd654c8017eb2a643dff19532025f8ca99003ff644c8017fb22643cff9913201dfcc899003fd644c8017eb22643cff1913201df8c8990f7ff544c879ff2a26400ff551321e7f8a89900aff634c87bffa9a6400ff94d32007faa6990f7fc534c879ffa1a6400ff90d32007fa86990f3fc434c8057fb126402ffd4932017fca49900bfd524c805fe2926402ffd0932017fc849900bfd424c805fe2126402ffcc932007de649900bfe324c805ef1926402ff0c932017b8649900bec324c801ffb0a6400bfd85321dffcc299006fe614c801feb0a643bff1853200df8c2990f7ff514c877ff28a643bff145321e7fe82990effe414c877fe20a643bff8c5321dff8629900bff214c80
  | 8 => 0xfc415325ff820a9853ff6590c017fb2c864aff99643025fccb21803fd6590c017eb2c8614ff19643025f8cb2180efd6490c07ffaa48603ff9524301ffaa92180ffc5490c077f31c864affd4e430a7fca721803fd5390c29fe29c8603ffd0e4301f7e872180fdf4390c29fe21c8603f710e430a7fec521927fe6290c057f3148600ff58a43005fac521853fc6290c057e314864affd4a4324ffca521927fc5290c07ffa148603efd0a4301ffc852180ffc4290c93ff1948614ff0ca430a7fec321923fe6190c037f30c8600ff58643005fac321853fc6190c037e30c864affd4643247fca321923fc5190c07ffa0c8603ff9064301ff88321923fe3190c29fe18c8649ffc8643247fc4321923fc2190c29ffb048600ff9824302dfcc121803fd6090c017eb048614ff18243257fea12192bfc5090c07ffa048603ff1024301f788121927ff2090c93fe1048648ffc4243247f82121803ff6550c017fb2a8647ff99543025fccaa1803fd6550c017eb2a8647ff19543025f8caa180eff6450c07ffaa28603ff9514301ffaa8a180ffc5450c077fb1a8647ffd4d43007fca6a1803fd5350c8ffe29a8603ffd0d4301fbe86a180ffe4350c01df21a8603ff10d4301f7886a180fdc4350c01ffb128600bfd8943237fcc4a180afe6250c01feb128646ff18943015f8c4a191fff5250c8dff2928646ff1494301ffe84a180ffe4250c8ddf2128603ff1094301f7884a191bfe3250c8dfe1928600ffd8543005fec2a1917fe6150c037f30a8600ff5854322ff8c2a1806fc6150c8fffa8a8645ff9454322ff8a2a180fff4150c07dfa0a8603ff9054301ff882a1917fe3150c8bfe18a8646ffc854322ffc42a1917fc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028605bf1814323ffea0a191ffc5050c07ffa028603efd014301ff880a191bff2050c8dfe1028645ffc414322ff820a180aff6554801ffb22a400bfd9152227fcc8a900efe6454801feb22a444ff1915201df8c8a9013ff5454809ff2a2a404ff55152027f8a8a9003ff63548017fb1aa400ff98d52007fac6a9003fc63548017e31aa404ffd4d52026fea6a9013fe5354809fea9aa400df54d52027f8a6a9113ff4354801ff21aa400ff50d52227f886a900aff6254805ffa92a404fbd4952017fca4a900b7e5254805fe292a402df14952017d8a4a900bff4254805ff212a402ff10952017fc64a900bfc3254801ffb0aa400bfd855221ffcc2a9006fe6154801feb0aa443ff1855200df8c2a9013ff5154809bfa8aa404ff94552027f8a2a9113ff4154887ff20aa443ff1055221ffc62a910ffc3154805ff90aa402ff88552017f842a9003ff60548017fb02a400ff98152007fac0a9003fc605480b7e302a404ffd4152027f8a0a90137c5054889ffa02a444ff10152017fe40
  | 9 => 0xa00201000800400200300000500400000100100500200300300000e00600200000101200000c00100400700b00600401d00600003300000000300000000000700001dfecaaa00eff6455007ffaa2a804efd515401ffca8aa00f7e5455007fe2a2a803df1515401f78a8aa003ff63550017fb1aa800ff98d54007fac6aa003fc63550017e31aa804ffd4d54027f8a6aa00fff4355007fe21aa800ffd8954005fec4aa14bfe62550057f312a800ff58954297f8c4aa00afc6255009ffa92a804ff94954027f8a4aa00fff4255007ff212a803ff10954297fc64aa14bfc3255001ffb0aa800bfd855428ffcc2aa006fe6155001feb0aa851ff1855400df8c2aa013ff5155009ff28aa804ff1455401ffe82aa00ffe4155007fe20aa851ff8c55428ff862aa14bff21550a3ff10aa851ff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa016fc6055009ffa82a804ff1415401ffe80aa00ffc40550a5ff902a852ff0815428ffe20aa147fc10550097eb2ca614ffd9253287fcc92980efe6494c01feb24a600bf592530a7f8c92980efc6494c09ffaa4a604ff95253027faa929813fc5494c097f31ca604ffd4e53026fea729813df5394c09afa9ca614ff14e53027b8a729943ff4394c29fe21ca614ffd8a5327ffcc52980afe6294c01feb14a600bf58a530a7f8c52980afc6294c09ffa94a604ff94a53027f8a529943ff4294c9fff214a64fff10a5327ffc6529853fc3294c29ffb0ca64eff9865300dfcc329803fd6194c017eb0ca614ff1865300df8c329813ff5194c09bfa8ca604ff94653027f8a329943ff4194c9dff20ca64eff10653277fc6329853fc3194c9fff90ca64eff88653277f84329853ff6094c01ff304a605bf98253007fac129802fd6094c29fe304a604ffd4253027f8a1298137c5094ca1ffa04a650ff1025327ffe412993ffc2094c9dff884a64eff04253025fecaa9803ff6454c017fb22a64dff9915301dfcc8a9803fd6454c9bfe322a603bf19153027fea8a9813fe5454c09feaa2a604ff15153025fec6a9813ff5354c09efa9aa604ff94d53006fca6a9813fc5354c09be29aa604f714d5326ffe86a9937fc4354c01ffb12a600bfd8953267fcc4a980afe6254c01feb12a64cff18953015f8c4a9813ff5254c09bfa92a604ff94953027f8a4a9937ff4254c99ff212a64cff10953267fc64a9933fc3254c01ffb0aa600bfd855325ffcc2a9806fe6154c01feb0aa64bff1855300df8c2a9813ff5154c09ff28aa64bdf94553027f8a2a98137c5154c9bffa0aa64bff9055325ff882a992ffe3154c97fe18aa64cffc855325ffc42a992ffc2154c01ffb02a600bfd8153007fcc0a9803fd6054c01fe302a605bf18153027fea0a98137f5054c09fe282a64dffd015326ff880a9933ff2054c99fe102a64bf
  | 10 => 0x200000000300e00b00200002e00501200400100a01300600600000600500400400701d00900200700000000100000100100101100a00000000000000200000c00100100800700100001900500400401500d01100400300e00300300302703000000000000a00d00c00600001100000100000a00200100b00000500000d00002000d00300000200000c00000700a00200200000000300300000c00000300700400301800900000801601603800000201500000003300000300300400000200b00200100400500b01d00900200700001a00b00200100601002100501400200100f01e00000500401300300000800000000300400100500300000100101b00000000200000000700000600200500000100500900200000200400000000d00101b00000000800100201301700000200300200300200500000500000900200100300200500100400100200100000102502501900200d00000000000100300100400100101300000400000300800000200300000c00100d00300800000000900000000000600000200100100000100601200000301100300701e00000200000100000801100001600000a00100100000200e00000600400000000200000000400000400000300d00c00100500a01300501d00400200000200e01700000100100201501c00400a00a00a00500800300100200000200300000300000f00000101200000000000401300600600e00000200400900000900000500000900b01200000101900700500000e00200000000500e00001500001700201800000000200c00000100d00a00600601200400000100b00900000400a00600d00900b01200400101300300000e00200c00000f00300201100500000700300000100000900000800000200200100000000100200c01400201500600000000700200100000901000000300700000200100000500300300200000200000200000603b00000101e00500000000200400000101500200000200300000d00000200200a00000000300100000000500200800300b00000100201900000100600100000000000000400000a00501900200300000500200200201301200a00201100000000000801f00200801500b00001200000501600100e00100200e05900700600100500100102100100000100e00f00200100000200500000000000100901f00000800000700600801300100000900100100000800200001602100001900600900300100000301f00000000000902900100000000000100600301200000200000000000700003602500200100d00100e00000600801201801700300b00600000000200000700001200400000100200501a00b00600701300900001901400700100900700000000000200100e00001002100d00300d00100300300700001300400100d00600400100000d00
  | 11 => 0x27f01a400006f09a00004c26d128b8328c6200032380000000003f480000000000001e0cdde0000001d480002ae000195476e21c228800000085900015e4ce8602309000044452e00022545f60002ba0000f9015f2d700000024d4000000000000017190340002dd0001a100003822518000b1415639020cca8871f1058d0002a33500005200ca00018506740003fa32f0b386d270c12811e000066d0c217d8cb22232898840c3c51a0b011f860a63700005348ae0a800004190400aa000000107e0002a40e389f04ff03c12f46e665d23f9cd0a7e8872b5946ccfe5471188e0c9140000251af800036e23d80cc0fe4e2415995884e4401f88f48bc24b74170f34f6c0b513c07e0ff45e313a1aac3b81db14b070454a78d1619ce030c11e1bd0200a6a0000048b240000001f919c4d6200036c85703dc102000176cc843ce00000000a207b2f5a148a560d536200000005fd01f82680000002a611ac25e2db2112078b3879e2fd12008902c61490d2025805e2819994ee25941a19420ed40a33528a14f4a1133b4074c19e7ed0e58c74b4605b35b0d981ee00037817483de79711807acabe0701a494dcae464e0938fb411020443b9a145fa3e00a00000bee545000000000000013a821c0001f123600000000003739b5c87c0000001f2426c01840a910c51c86521a0b44b5e7151e790908460001b093b4d1a000000133cc8c00034180003401214008cf81383300c4950c0000000001440eb40002cfa1c00001771d783207cc8313d51f640005bf01e1df400000000000e80000000001a5cbb800005d0c78cfa0000000720a7a0002bd9fbcd420682ea03440006780000000000000000000000016f30b1cd40ee5f343f020c0007c406681d06fa00003520189d24dc1dc80000000003711bf8c16786131022468e4d012209088a02ab12381f077462b3208bc811674510f02b911412210b0000c2828a11c1f58b780000000000d7e5c13ff854c5304892ce97a0d2875c19d040095c0272cf15401047ab2ad1f6ce063764000be8fb44062e01dd05a03f43b1903cf707a237c97a473830b0d68e900cc0001411880c9406d378826403652708b0868aa416b42d8000d7285000005909f45683378fd42183921ee88d0a6410a000068c44e742000035cace43116d000000000000e99680003ea41b223800044b3228000da400028a17448982170aa037901a80b3a3060834a6210001d1cede54e1a28e5c0ea38900000006564b81848000a520bb00000000200000000f5c00037706f800111e6f316680010505de38d00000000000000000000000000000017a1982011b140a40da3e5178100e1f300013640801030000000b60501117172cbe86cd1d59bb01720000001bf4af000000014e0cd42a10fa9a2c08c787000094401001901400200100300e00b
  | 12 => 0x5a8a5032f19e9a6c23e5ca21308d4f1c3143ac90d4e662332328f007fc1fe42aa0384ce399049182027626f2629fd4f2619719892d02ea02e22a050908208c086a184d247921659c2c40c6a03db84dc4da5121218e584c03e930207a8916297120a17825a0ec36b0d38d527f6123220836424a20a081c78c6f80a195d879009e07c0a906c63f32cb00c48927e2120036462008f33a86e8f182f61010ae483852f113112883413e13b9b309ba1bf2e2858cfbc6cf1b200706301c90000000a9488414186d800000042b975cfe043d18b02c09300001a20864ff87df3128c203485c60191a749e68351ef000004674d1c41e090e80002c18700d947be0fd84680984c02c884d45b879d31a802909e09400006a441c84523d10c84b414b14e8d480003b530b80010246e42879ef49487312bb8648bf87e300008347fe32d1ad83ec29472b2639730d8675d26500007544ee05f00006d80003f50000e960003dd90040008461140f942ca0000000000000000052a2140000004110000c0e0001b58000000000000102c5367a91a300006724550000c0c24623d41b93e400069c00005f000011400011c87144da1628a40dda3fd370913c00034f3da84e852a0000000330e440001ea000041214600010a47e00003aa80008a684c356958c5bc3a7363159103e60515d9a24bf00001078000f862cf22300510f2239209958422e2110a605c040614e0000d3455436734c8fdc00013f41200000002bd0ce000088e4b5000097000000000000009e800000010150e24901a1208c1426dd0000db4c980001b7800018c39d0001418000000000000000000003598b000000033495f800022542c0000fcc0004019aa88f209d00005884f81f70001660f644622790000000000405000000071c24e8000d5e0002ea892cf421ed4339ab8c327f400000000006d300214ec5000c50b49a1870c0c100013b01d65d638e9634c904bf2c70e101e22e70000000f1e32611f0f6c49a87b2728f1c3f8076134a24820e67909c0a0400081b13d18184dc17d16219ed1260481e114e4d1c2b20b9184c00002a21783b887800000007640003f838c0b2800005d3bd204c7b80000d78d706a635542686cc2f63291d41cf50c823c190105890260e3be094ce1c00000006ec00018b360000000000021816d800031243403c8e000c212a80d85d82a01d3106c39417938a06dc46e5620b70efd0d284b19500000880001c886f0d3c67239600001f26de3b28c5c0005660000000000000296000000000000000009ac00000000003aa1c40000e6c000000000000108800016911780580000001c580760000000fe50760002608000b0e3a205906c00000000000000db8000000019cc9a000000000000050713e80000000004399324f0a4d832e0ab4f666ee431125c89c00017980000000
  | 13 => 0x5b40000000a682871a8919c00000038c856507000029e18f000067c0780e300003752319534f9e82717f96d494a5802ec027c5e265f32793f094451d1f102cc0b400035a8aa48b64363c580010e47f142a0000a120450218000dec7f230e0e8401e66426b888086e5dd40d05742b61e50cb0cc89761d40eb00f4d900160001764000536065a258e12115359977c0000000001688a2c70600000001c273b419157480070d23880007003383110678000000000000000035d000005cd04012000000000054200014440002b500000000000002dc82380001d1000067c17860d21400000000000000f5806a68c0001498ebc0dd0001af433418a3751d38c485a00000df0808000171074010886e26f00000c61c336c170cfba0000bc000072000000000000000003828000b2a00022c9a58e208490001be8000000000021800e00025f21f000083a00021b000049201000008f83f608883fc23051938880003200003bb8a340004e40000000c760000d38788e5e000000007911864b3f288b4d2a04203c80009ec5050001ca4bda45c3ce1f60cb074a00016f8c7c0002a8800034c4a90000c9006e7800000000000000000000000600019280000002290f480004b00002a99bdc75a2e90e2859891c87624399000002c70001d004f60550001bec1560001d994cd0102f707a8be0df8000000000000038b38f10240002df01480683be54f3b311f401600e2f6126ce886360c0980c6020002be1f5011a07a00001c400000024600003444bc2fd86508760002f21fec27202244a06a83724af0000090b627b12b50124250013172a1bc5b027907020f83505c20799f2cfa024f1489348d8e7dc0ed066cc5a2930da8000afa51c000000000066300013f4f5c0002910fb859000002582e0000000000139ce541241bc8000b503ec00003240560952539af04c610801a16a400a5893b61f0105a4b335219d85461c207d14c00004442211984a3e737383999c7764993d18990dd68042f89a28b10322232000000021b0001d2050833f000097d11233c00000f80004c839802985e03bc3730a9cc7a2fe3199fe00000002e6a22c6183580f311340dc0001d880310603df000015856c00000000000000000001ca0d2252407680008cc77224a18fc61a191336078045e5552cd9da49080003c093dc00006c00002d8b742ac2d68964b164a121993a89d0573187955c3f477e38d89b00a81334200cb81c65932c61e447687a42b01d9c00088d40e98bc9c21953e3819000055e135874878a1de3141c8400061f2d61028cdc8112b88eb86b47a6175811c5aa28600000000002e12ac0f100003020728000f1441930c0000bde4560c420f4c2a0000001d4c3b00000000000a300001b000002ec3153de0f848300000bf800000000026d8a701b043f4060000ebe0000b60
  | 14 => 0x8000a1c29a2dd88509ea21d1479f4c0007ba1580d0425c00001c84380001f600010305ea2bf36484482a20280000000f9849f00016c87aa76100000008b01c708c800035c3064300c688061570e70af803e70a30d800000012602b8b6430a20a2370ff104c6300a3800000037419197b800000000018b87b44eb42e89fc8de75100000002401fd2291d4000047524997c000050b28208308ee1490178e5009a6001b40ec105e00017708c86980ce3289ce400000025b000077a000440933000000000000000000003591a2037a42e1460e3c1ec0604108000d7028b00008005744101b5061c2786a703102b50fa82c3bf8240c4e69807e9398650257253131090a7e81612070f361e434000000002c0000156cce07ac3aa0ba8a5454000000005683b200000001c84f14318064fee000000000046c8833560084ec00fe2f3994c2da1290589c941d26682340cdcd0e000321a0f0bfe4d520400000000004298000000213100800000013d230925415209b0a80cec94073e2fa8c005ac00042100000000001cd000024a00040a0000daa86b3b7183c73e68f1f5971c0006da00013181226a8000014000017e2f1209496435e1b90000fdc7e02e98000e7e62905f868400000024f01640005653cc0000f720003d6963ceec45d00016487b061a11d9b4096200000005e8fc82b11381f8400017431c97205de4911e800004ec50c0001ac00705da4330884ca40b40001efc6ae69f35b8f2400084a1ca8e940007960e30a887a27a730600002bc0003e309140002881249d6c73025b37a800080e00020e98444e62ed1f188fcc200002129f080001e80000370e103a92989d3095467731a0f304901cf18c8e045d04200069b7cc4658103f0c7c43e0d32d3169cdb6438000000054c0001bf09f8d9c421000000109c00044302880007a0000000088200036587e4000000000078426400019997e400070f000031cf5e00000000006381453131f349380002ae16cc70e85a2410bd0a4686a3700c1c9960af02c204069650204c0f640003590001344c7400025800002546e330e9608b20541255800112000033015b08e004136114785f239334d1f9c85a6a632a00000008510391cb809c7ec26f8c9cba08022f51338e485843008cb0906762000000030689100011d800073a3c480006080000000a7c5a600000000000000000000000b426e944b8000000000000043c1de00035d00005c054932d92a101e000000145400000000000004244c30001c98ad229908498e0ee05c915e10ad0fe6570dc053c0000001f4086093400000311a4eb0155278134c5a80004148000c1288031909485825462b696dc00037100015c036818f115165c6a05c400000006f084304084c10541670ff8854216104000000000015242b030cf34000000000031a7ce38b8000000
  | 15 => 0x9de525000099400057530510446e07fe02e0d58d685ab2f91b94e640ac2c31d5c3ae12b013034100a1cd00896a83183be0e6039c28235442f8000ffa56f23690483e05e51028c84f827a82dc1cd83d81990d61f14e4e0001448398eea0001d0205800000000000008be0002f30d285f86660000f903e4000000192400043900011a861c0000ac205caa81051b100002b457f00019400000003b990e80a662a28508900006810001d3caf400043d1258d20000000000047472d0b880010ea11c0b087740000002ab211c6be05f1c280001f82af000093000033435121b4ab21e301812e4eda5a41390358b4a795069038906884840c8dec73c00000000000c200004b00008580e800006f9012000000000091e0001271de01480ea0001ba091a085215036c796193000000000011000000004d00000000000b9c4e00000000da87040989facadc1733791f5453c6c127d907c12e0003d80fec78200000000001140000010000f2000025d00000000000001d044d469312a0000fae31b2de938c00010100000000e618e00010540007d10000000fa40000000cd87860002e799f85cc72312b0b90a7c2083b5948009e000188897490c0000a2217000000011600000007560000eb082e0000000f4c1400003cc94b477045a0000adc1e80003bc800099a000053903903077b2a59c046263e71b283508c050d3a1879cf6873c2c28ae04567f308e85a06fe74935180010f029438112b4f3e67a4441e10f2867323994e871a47438900005508390d580005662d71f799acf100b7062097874602d2ff1bfc4e27f9012824c18018038980000006bb3311484a002cc08d92b09844452cc9d90de82662cd01f43e80001db0f280000002441078c880000d8
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7654910004fd7654910004fc76549100067f65549100267c6554910004ff7650910004fe7650910004fd7650910004fc76509100067f65509102167c655091001ebe6450910006bd6450910005f7715091000df471509100a4ff76cc910004fe76cc910004fd76cc9100a4fc76cc9100067f65cc9102067c65cc91003dbe74cc910005bd74cc910006ef62cc910016ec62cc91000df671cc910005f571cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101ee7c654c91002df47654510026f4765451002cf4765451000df7755451000f777554510007776554510026f66554510026f46554510047746554510005f77354510007765354510047745354510047775254510007755254510007f3705451002df6705451002df47054510007f0705451000ef7605451000ff3605451004777505451002df4764c510006f4764c51002cf4764c510005f7754c510005f5754c51000777654c51000774654c51000df7734c51000fd7734c510007d7634c5100a6f6634c5100a6f4634c510007d4634c510007d7324c510007d5324c510007f3704c51002df6704c51002df4704c510007f0704c51000ef7604c51000ff3604c510024ff765411000cfe765411014cfd765411000cfc76541100067f65541100267c6554110005f7715411000df4715411000775515411002ff0105411001cff765011000cfe765011011cfd765011000cfc76501100067f655011012e7c6550110006bf645011001ebc6450110005f7715011000df4715011000cfe76cc11000cfc76cc1100067f65cc1101167c65cc110006df63cc1100a6dc63cc11000df671cc110005f571cc1100a4ff764c11000cfe764c1100bcfd764c11000cfc764c1100057f754c1100457c754c1100067f654c1100d67c654c110005bf744c11003dbc744c110006df634c110006dc634c110005f7714c11000df4714c11029dfa768811002efa76881100077b6588110007786588110065f97288110016fa6288110016f8628811000dfa718811002df8718811002efb618811002ff3618811007ff25188110007f1518811007ff23188110007f13188110014ff764811000cfe7648110064fd764811000cfc76481100067f65481100767c6548110005bf744811003dbc7448110006ef6248110016ec6248110005f7714811000df4714811000df87648110016f8764811000cf876481100077b6548110007786548110007bb7448110007b8744811002dfb724811002feb7248110007eb6248110016fa6248110016f86248110037e86248110037ea4248110007e94248110037ea3248110007e93248110007f3714811000dfa714811000df87148110067f0714811002efb614811002ff36148110067f25148110007f15148110067f23148110007f13148110
  | 1 => 0x8d100bcfd7098d100a6f97098d100057f7558d100457c7558d100067f6558d100067c6558d10005bf7458d1003dbc7458d10005ef7258d10035ec7258d100fdfb7058d10004ff7558d100067f7558d100047f7558d10024fe7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d100bcff7158d10006f77158d100fcff7058d10006fb7058d100dcfe7618d100067f6518d100067c6518d1003dbe7418d10005bd7418d10006dd6318d10024fe7518d10004fd7518d100a4fc7518d1001cfe7418d100a6be7418d1001cbe7418d10004fd7418d100a6bd7418d10004bd7418d100a4fc7418d100a6de7318d10006df4318d100a6dc4318d10014fe7218d10004fd7218d10014fc7218d10006de3218d100a6dc3218d1002cff7118d1000cfe7118d1002cfd7118d100a6f57118d1000cfc7118d100a6df3118d100a6f63118d10096dd3118d1002cfe7018d1002cfc7018d100a4ff7694d10004fe7694d10004fd7694d100a4fc7694d100067f6594d100267c6594d100475f5394d1000df67194d10005f57194d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100267c6554d1000df67154d1025f765154d100a4ff7690d10004fe7690d10004fd7690d100a4fc7690d100067f6590d102567c6590d10006bf6490d1001ebc6490d1000df67190d10005f57190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1023e7c6550d1001ebe6450d10006bd6450d10005fb7050d1002df87050d10014fe76d89100067f65d89100067c65d8910036ee62d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d89100a4fe73d8910004fd73d8910006ef42d8910036ec42d8910036ec32d891002cff71d891000cfe71d891002cfd71d891000cfc71d891007eef21d891007eed21d891002cfe70d891000cfd70d891002cfc70d8910036ef20d89100057f75589100457c75589100067f65589100067c6558910005bf745891003dbc7458910005df7358910005dc7358910036ec62589102a5fb7058910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df73589100a4fc7358910006dc7358910004dc735891007cff7258910006ef7258910064ff7158910006f771589102a4ff7058910006fb7058910004ff7654910004f
  | 2 => 0x1667e41d95101667d41d95101667c41d95101667f31d95101667e31d95101667d31d95101667c31d95101667f21d95101667e21d95101667d21d95101667c21d95101667f70d95102d67e70d95101667d70d95102d67c70d95100067f40d95102d67e40d95102d67c40d95102d67e30d95102d67c30d95100067f20d95102d67e20d95102d67c20d95101667f10d95102d67e10d95102d67c10d95100467c65595102cdfb7059510164ff75595100067f7559510004ff745951001cfe745951001cfc7459510004ff73595100a4fc7359510004ff7259510014fe7259510014fc725951014cff7159510006f771595102ccff7059510006fb70595101657e76195100467e76195101647e76195100067e64195100067c64195100067e62195100067c62195102bf7671195100477571195102c67f61195102bf7631195102be7f60195102bf7b10195102c77610195102c77410195102bf78101951001cfe76d91100067f65d91100067c65d911003ebe64d9110024fe75d9110004fd75d9110024fc75d91100a4fe73d9110004fd73d911003ebc43d9110014fe72d9110004fd72d9110014fc72d9110006be42d911003ebc42d911002cff71d911000cfe71d911002cfd71d911000cfc71d9110136bf41d9110136bd41d911002cfe70d911000cfd70d911002cfc70d911003ebf40d91100057f75591100457c75591100067f65591100067c655911003ebc6459110005df7359110005dc7359110005ef7259110035ec72591102b5fb7059110004ff75591100067f75591100047f7559110024fe7559110024fc75591100067c75591100247c7559110134ff7459110006bf7459110004ff7359110006df7359110004df73591100a4fc7359110006dc7359110004dc735911003ebf4359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec725911003ebf425911011cff7159110006f771591102b4ff7059110006fb70591102aebe40591102aebc4059110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100267c65551100067f65d8d100067c65d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df43d8d10006dc43d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10006dc32d8d1002cff71d8d1002cfd71d8d100dedf31d8d100dedd31d8d100457e7598d100057d7598d100067f6598d100067c6598d10006df6398d100bdf97098d10024fe7598d100a67e7598d100247e7598d10004fd7598d100a67d7598d100047d7598d100a4fc7598d1001cfe7498d10004fd7498d100a4fc7498d100a4fe7398d10014fe7298d10004fd7298d10014fc7298d100fcfd7198d100a6f57198d100a6f6319
  | 3 => 0xf7458e1001cfe7458e1001cfc7458e1002edf7358e10004ff7258e10014fe7258e10014fc7258e100bedf3158e100bedd3158e1002cff7058e1002cfe7058e1002cfd7058e1002cfc7058e1002ede3058e1002edc3058e1002ef71058e1002ef51058e100a4ff7694e1002cfe7694e10004fd7694e1002cfc7694e102ee7f6594e100267c6594e1005f5f5394e10004ff7654e1002cfe7654e10004fd7654e1002cfc7654e100267e6554e100067d6554e100a4ff7690e1002cfe7690e10004fd7690e1002cfc7690e10004ff7650e1002cfe7650e10004fd7650e1002cfc7650e1001ebe6450e10006bd6450e10005fb7050e1002df87050e10004ff7558a10024fe7558a10024fc7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a100a4fc7358a1002eef7258a10006ef5258a1004eec5258a1004eee4258a1004eee3258a10066ef2158a10066ed2158a1002cff7058a1002cfe7058a1002cfd7058a1002cfc7058a1002eee2058a1002eec2058a10004ff7654a1002cfe7654a10004fd7654a1002cfc7654a102e67f6554a100267c6554a10005f77154a1000df47154a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a1001ebe6450a10006bd6450a10016ee6250a10006ed6250a100a4ff76cca1002cfe76cca10004fd76cca1002cfc76cca10055be74cca10005bd74cca10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca10016ee624ca10006ed624ca10005f7714ca1000df4714ca1002dfb76482102defb7648210007bb7448210007b8744821002feb7248210016fa624821002ef8624821004fea4248210007e9424821004fea3248210007e9324821000dfa714821000df87148210024fe76d95100467e65d951001cfe74d9510004fd74d951001cfc74d95100467f54d95100067e54d95100467c54d95100a4fe73d9510004fd73d95100467f53d95100467c53d9510014fe72d9510004fd72d9510014fc72d95100467f52d95100067e52d95100467c52d951002cff71d951000cfe71d951002cfd71d951000cfc71d95101667f51d95101667d51d951002cfe70d951000cfd70d951002cfc70d95100467f50d95102bd7e76d95100247e76d95100067e64d95100067c64d95100067e62d95100067c62d95102d77771d95101677471d95101677631d95101677b10d95102d77610d95102d77410d95101677810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067e32d95100067c32d95102d67f71d95101667e71d95101667d71d95101667c71d95101667f41d9510
  | 4 => 0x8520004fd74d852001cfc74d85200a4fe73d8520004fd73d852002cfd72d852000cfc72d8520006f751d8520066f451d8520066f431d8520066f621d852004ef521d852002cfe70d8520014fd70d852002cfc70d8520066f710d85200057f75585200757c7558520005bf745852006dbc7458520006bf6458520006bc6458520005df7358520005dc7358520066f461585202f5fb7058520004ff7654520004fe7654520004fc76545200267e65545200067d6554520006bf64545201d6bc6454520005ef7254520015ec7254520004ff7650520004fe7650520004fc7650520006bf645052001ebc6450520007ad4250520004fe76cc520004fd76cc5200a4fc76cc5200757e75cc5200057d75cc520006bf64cc5201aebc64cc520015ee72cc520005ed72cc520007cd32cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c520006bf644c520196bc644c520007cd324c520024ff7654120014fe7654120154fd7654120014fc76541200067f65541200267c6554120006bf645412015ebc6454120005ef7254120015ec725412002fe8205412001cff7650120014fe7650120124fd7650120014fc7650120006bf645012001ebc6450120005ef7250120015ec7250120007ad425012002fb8405012002fe82050120014fe76cc120014fc76cc120006bf64cc12010ebc64cc120006df63cc1200a6dc63cc120015ee72cc120005ed72cc1200a4ff764c120014fe764c1200c4fd764c120014fc764c1200057f754c1200757c754c120005bf744c12006dbc744c120006bf644c1200cebc644c120006df634c120006dc634c120005ef724c120015ec724c12002e7f7559610004ff745961001cfe745961001cfc7459610004ff73596100a4fc735961005e7f5359610004ff7259610014fe7259610014fc725961014e7f515961014e7d515961002cff705961002cfe705961002cfd705961002cfc705961002e7e505961002e7c505961002ef7105961002ef51059610004ff7559210024fe7559210024fc755921002ebf7459210006bf5459210056bc5459210004ff73592100a4fc7359210056bf4359210004ff7259210014fe7259210014fc7259210056bf425921011ebf415921011ebd415921002cff705921002cfe705921002cfd705921002cfc705921002ebe405921002ebc4059210004ff765521002cfe7655210004fd765521002cfc7655210024fe7598e10004fd7598e100a4fc7598e1001cfe7498e10004fd7498e100a4fc7498e1002ede7398e10014fe7298e10004fd7298e10014fc7298e100a6df3198e100fedd3198e1002cfe7098e1002cfc7098e1002ede3098e1002edc3098e10004ff7558e100067f7558e100047f7558e10024fe7558e10024fc7558e100067c7558e100247c7558e10004f
  | 5 => 0xc5f97098d20024fe7598d20004fd7598d200a4fc7598d2001cfe7498d200a6be7498d2001cbe7498d20004fd7498d200a6bd7498d20004bd7498d200a4fc7498d200a4fe7398d20104fd7298d200a6ed7298d200a6ee3298d2000cfe7198d20004fd7198d2000cfc7198d200c4fd7098d200a6f97098d200057f7558d200757c7558d20005bf7458d2006dbc7458d20006bf6458d20006bc6458d20005f77158d20065f47158d20105fb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20024fc7558d200067c7558d200247c7558d20004ff7458d20006bf7458d20004bf7458d2001cfe7458d2001cfc7458d20006bc7458d2001cbc7458d20006df7358d200c4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d20104ff7058d20006fb7058d200e4fe7618d200757e7518d200057d7518d20006bf6418d20006bc6418d20006dd6318d20024fe7518d200a67e7518d200247e7518d20004fd7518d200a67d7518d200047d7518d200a4fc7518d2001cfe7418d20004fd7418d200a4fc7418d200a6de7318d20006df5318d200a6dc5318d2002cff7218d20014fe7218d2002cfd7218d200a6ed7218d20014fc7218d200a6df3218d200a6ee3218d2009edd3218d2000cfe7118d20004fd7118d2000cfc7118d20006de3118d200a6dc3118d200a4ff7694d20004fe7694d20004fd7694d200a4fc7694d200067f6594d200267c6594d20006bf6494d20286bc6494d200775f5394d20015ee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200267e6554d200067d6554d20006bf6454d2026ebc6454d20005fb7054d2002df87054d200a4ff7690d20004fe7690d20004fd7690d200a4fc7690d20006bf6490d2001ebc6490d20015ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d2001ebc6450d20015ee7250d20237ae4250d2002dec765092001eec765092002cec7650920015ef7450920017af7450920007af645092001eee645092001eec645092006fac6450920005ef7350920007ae435092006fac435092006faf4150920007eb705092002dee705092002dec7050920007e87050920016ef6050920017eb605092006faf405092002dec764c920006ec764c92002cec764c920005ef744c920005ed744c920007af644c920007ac644c920015ef734c920017cf734c920007cf634c9200a6ee634c9200a6ec634c920007cc634c920007eb704c92002dee704c92002dec704c920007e8704c920016ef604c920017eb604c92000cfe76d8520006bf64d8520006bc64d8520066f661d8520024fe75d8520004fd75d8520024fc75d852001cfe74d
  | 6 => 0xc73595200767f5359520154ff7259520006ef7259520004ff7159520006f77159520004f7715952000cfe715952000cfc7159520006f4715952000cf471595200767f515952031cff7059520006fb70595202e67e50595202e67c505952001cfe76d912006ebe64d9120024fe75d9120004fd75d9120024fc75d9120006bf54d912006ebe54d912006ebc54d91200a4fe73d9120004fd73d912006ebf43d912006ebc43d912002cff72d9120014fe72d912002cfd72d9120014fc72d912013ebf42d912013ebd42d912000cfe71d9120004fd71d912000cfc71d912006ebf41d9120006be41d912006ebc41d9120014fd70d912006ebf40d91202fdbe76d912001cbe76d9120006bf65d9120006be65d9120006bd65d9120006bc65d9120317af72d912013fac72d912013fae32d9120006be61d9120006bc61d912013fbb20d9120317ae20d9120317ac20d912013fb820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006bc53d9120316bf72d912013ebe72d912013ebd72d912013ebc72d912013ebf52d912013ebe52d912013ebd52d912013ebc52d912013ebf32d912013ebe32d912013ebd32d912013ebc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bc51d9120006be31d9120006bc31d912013ebf21d912013ebe21d912013ebd21d912013ebc21d912013ebf70d9120316be70d912013ebd70d9120316bc70d9120006bf50d9120316be50d9120316bc50d9120316be30d9120316bc30d912013ebf20d9120316be20d9120316bc20d9120006bf10d9120316be10d9120316bc10d912006ebc645912030dfb7059120004ff7559120024fe7559120024fc755912013cff7459120006bf7459120004ff73591200a4fc7359120124ff7259120006ef7259120004ff715912000cfe715912000cfc715912030cff7059120006fb705912013dbe761912006ebe761912013cbe7619120006bf6519120006be6519120006bd6519120006bc65191202ffae721912006fad7219120306bf62191202ffae3219120006be6119120006bc61191202febf60191202ffbb2019120307ae2019120307ac20191202ffb82019120004ff7655120004fe7655120004fd7655120004fc7655120006bf645512001ebc6455120006bf64d8d20006bc64d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006df53d8d20006dc53d8d2002cff72d8d2002cfd72d8d200e6df32d8d200e6dd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006de31d8d20006dc31d8d2006dbe7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d20
  | 7 => 0x92200a4fc7359220086bf4359220126bf4259220126bd4259220004ff715922000cfe715922000cfc715922002cfe705922002cfc705922002ebe405922002ebc405922002eef205922002eed2059220004ff765522002cfe7655220004fd765522002cfc7655220024fe7598e20004fd7598e200a4fc7598e2001cfe7498e20004fd7498e200a4fc7498e2002ede7398e200a6df3298e20106dd3298e2000cfe7198e20004fd7198e2000cfc7198e2002cfe7098e2002cfc7098e2002ede3098e2002edc3098e20004ff7558e20024fe7558e20024fc7558e20004ff7458e20006bf7458e20004bf7458e2001cfe7458e2001cfc7458e20006bc7458e2001cbc7458e2002edf7358e200c6df3258e200c6dd3258e20004ff7158e2000cfe7158e2000cfc7158e2002cfe7058e2002cfc7058e2002ede3058e2002edc3058e2002eef2058e2002eed2058e200a4ff7694e2002cfe7694e20004fd7694e2002cfc7694e2008f5f5394e20004ff7654e2002cfe7654e20004fd7654e2002cfc7654e200267e6554e200067d6554e20005fb7054e2002df87054e200a4ff7690e2002cfe7690e20004fd7690e2002cfc7690e20326bf6490e2001ebc6490e20004ff7650e2002cfe7650e20004fd7650e2002cfc7650e2001ebe6450e20006bd6450e20004ff7558620024fe7558620024fc7558620004ff745862001cfe745862001cfc7458620004ff73586200a4fc735862002ef7715862007ef65158620006f7415862007ef4415862007ef6315862007ef62158620036f5215862002cff705862002cfe705862002cfd705862002cfc705862002ef6105862002ef41058620004ff7654620004fd765462002cfc76546200267e65546200067d655462000ef66154620006f56154620004ff7650620004fd765062002cfc76506202aebf645062001ebc6450620005ef7250620015ec72506200a4ff76cc62002cfe76cc620004fd76cc62008d7e75cc6200057d75cc620004ff764c620004fd764c62002cfc764c620005ef724c620015ec724c62000ef6614c620006f5614c620024fe76d95200767e65d952001cfe74d9520004fd74d952001cfc74d95200a4fe73d9520004fd73d95200767c53d952002cff72d9520014fe72d952002cfd72d9520014fc72d952016e7f52d952016e7d52d952000cfe71d9520004fd71d952000cfc71d95200067e51d95200767c51d9520014fd70d95200767f50d95200767c6559520005bf745952006dbc7459520005df7359520005dc7359520005f77159520065f4715952031dfb705952016cff75595200067f7559520004ff7459520006bf7459520004bf745952001cfe745952001cfc7459520006bc745952001cbc7459520004ff7359520006df7359520004df73595200a4fc7359520006dc7359520004d
  | 8 => 0x1cfc745843000cfd7358430004ff7258430014fe7258430014fc725843002ef77158430006f75158430096f65158430096f45158430006f74158430096f64158430096f441584300a6f731584300a6f43158430006f72158430096f62158430096f4215843002cfc705843002ef6105843002ef41058430006f77558430006f67558430006f57558430006f47558430006f77458430006f67458430006f57458430006f47458430006f75458430006f65458430006f55458430006f45458430096f773584300a6f67358430006f753584300a6f65358430006f553584300a6f45358430006f743584300a6f64358430006f543584300a6f44358430006f77258430006f67258430006f57258430006f47258430006f75258430006f65258430006f55258430006f45258430006f74258430006f64258430006f54258430006f442584300a6f73258430006f63258430006f532584300a6f4325843002ef7705843002ef6705843002ef4705843002ef7505843002ef6505843002ef5505843002ef4505843002ef7405843002ef6405843002ef5405843002ef4405843002ef7305843002ef6305843002ef5305843002ef4305843002ef7205843002ef6205843002ef5205843002ef42058430004ff7654430004fd765443002cfc76544300267e65544300067d65544301d6be6454430006bd64544301ceee6254430006ed625443000ef66154430006f56154430005fb705443002df87054430004ff7650430004fd765043002cfc76504301c67e65504300067d655043001ebe6450430006bd6450430005df73504300a5dc73504301beee6250430006ed625043000ef66150430006f561504300fcff764c43019e7e654c4300067d654c430196be644c430006bd644c43018eee624c430006ed624c43000ef6614c430004ff7648430004fd764843002cfc76484301867e65484300067d654843017ebe6448430006bd6448430005df73484300a5dc7348430016ee6248430006ed624843000ef66148430006f5614843002dfb764c030006fb764c030004fb764c0300077b754c03000778754c03002f7a654c03002f79654c030007bb744c030007b8744c03002fba644c03002fb9644c03002dfb734c03002fdb734c0300a6fa634c03002fda634c0300a7da534c030007d9534c03032fdb434c0300a7d8434c03002fea624c03002fe9624c03002ff2614c03002ff1614c03002e7f7559620004ff745962001cfe745962001cfc74596200067e545962008e7c5459620004ff73596200a4fc735962008e7f53596201567f52596201567d5259620004ff715962000cfe715962000cfc715962008e7f515962002cfe705962002cfc705962002e7e505962002e7c5059620004ff7559220024fe7559220024fc755922002ebf7459220004ff735
  | 9 => 0xd505903002ebc505903002ebf305903002ebe305903002ebd305903002ebc305903002ebf205903002ebe205903002ebd205903002ebc205903002ebf105903002ebe105903002ebd105903002ebc1059030004ff765503002cfe7655030004fd765503002cfc76550300267e65550300067d655503001ebe6455030006bd6455030005df73550300a5dc7355030296ee625503028ef66155030005fb705503002df870550300a4ff7598c30024fe7598c30114fd7598c300a4fc7598c300a4ff7498c3001cfe7498c3010cfd7498c300a4fc7498c30014fe7298c3000cfe7198c3002ede3098c3002efa3098c3002edc3098c30114ff7654c300267e6554c300067d6554c3026ebe6454c30006bd6454c30266ee6254c3025ef66154c3010cff7650c3023e7e6550c300067d6550c3001ebe6450c30006bd6450c300a79c4350c30236ee6250c3022ef66150c30004ff7558830024fe7558830024fc7558830004ff745883001cfe745883001cfc7458830014fd735883002eef7258830006ef525883009eee525883009eec5258830006ef425883009eee425883009eec42588300a6ef32588300a6ec3258830004ff715883000cfe715883000cfc715883009eef2158830006ee215883009eec215883002cfc705883002eee205883002eec2058830006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef5458830006ee5458830006ed5458830006ec545883009eef73588300a6ee7358830006ef53588300a6ee5358830006ed53588300a6ec5358830006ef43588300a6ee4358830006ed43588300a6ec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef5158830006ee5158830006ec5158830006ef4158830006ee4158830006ec41588300a6ef3158830006ee31588300a6ec315883002eef705883002eee705883002eec705883002eef505883002eee505883002eed505883002eec505883002eef405883002eee405883002eed405883002eec405883002eef305883002eee305883002eed305883002eec305883002eef105883002eee105883002eed105883002eec1058830004ff7654830004fd765483002cfc76548300267e65548300067d6554830226be6454830006bd6454830005df73548300a5dc7354830016ee6254830006ed625483021ef66154830004ff7650830004fd765083002cfc76508302167e65508300067d655083001ebe6450830006bd6450830016ee6250830006ed625083020ef66150830005fb705083002df87050830104ff764c8301ee7e654c8300067d654c8301e6be644c830006bd644c830016ee624c8301def6614c830004ff7558430024fe7558430024fc7558430004ff745843001cfe7458430
  | 10 => 0x1300ccfd765013001cfc76501300067f655013012e7c6550130006bf645013001ebc6450130005df7350130005dc73501300067f65cc1301167c65cc130006bf64cc13010ebc64cc13002dde73cc13002cfa76cc1300077b65cc1300077865cc130007bb64cc130007b864cc13002dfa73cc13002fdb63cc13002cff755943002e7f7559430004ff745943001cfe745943001cfc74594300b67f54594300067e54594300b67c5459430024ff7359430024fd73594300a4fc73594300a67e53594300a67c5359430004ff7259430014fe7259430014fc72594300b67f52594300067e52594300b67c5259430004ff715943000cfe715943000cfc71594300b67f51594300067e51594300b67c515943002cfe705943002cfc705943002e7e505943002e7c50594300067f74594300067e74594300067d74594300067c74594300b67f73594300a67e73594300a67c73594300067f43594300a67e43594300a67c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067c42594300a67f32594300067e32594300a67c32594300067f71594300067e71594300067d71594300067c71594300067f41594300067e41594300067c41594300a67f31594300067e31594300a67c31594300067f21594300067e21594300067c215943002e7f705943002e7e705943002e7d705943002e7c705943002e7f405943002e7e405943002e7d405943002e7c405943002e7f305943002e7e305943002e7d305943002e7c305943002e7f205943002e7e205943002e7d205943002e7c205943002e7f105943002e7e105943002e7d105943002e7c1059430004ff7559030024fe7559030024fc755903002cff745903002ebf7459030006bf54590300aebe54590300aebc545903001cff735903001cfd73590300a4fc73590300a6be43590300a6bc4359030004ff7259030014fe7259030014fc72590300aebf4259030006be42590300aebc4259030004ff715903000cfe715903000cfc71590300aebf4159030006be41590300aebc415903002cfe705903002cfc705903002ebe405903002ebc4059030006bf7559030006be7559030006bd7559030006bc75590300aebf73590300a6be73590300a6bc7359030006bf53590300a6be53590300a6bc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006be5259030006bc52590300a6bf3259030006be32590300a6bc3259030006bf7159030006be7159030006bd7159030006bc7159030006bf5159030006be5159030006bc51590300a6bf3159030006be31590300a6bc3159030006bf2159030006be2159030006bc215903002ebf705903002ebe705903002ebd705903002ebc705903002ebf505903002ebe505903002eb
  | 11 => 0x67f65551300267c6555130006bf645513001ebc64551300f4fe7694d300067f6594d300267c6594d30006bf6494d30286bc6494d300d75f5394d3002cfc7654d300067f6554d300267c6554d30006bf6454d3026ebc6454d30005fb7054d3002df87054d300ecfe7690d300067f6590d302567c6590d30006bf6490d3001ebc6490d3002cfc7650d300067f6550d3023e7c6550d30006bf6450d3001ebc6450d30005fb7050d3002df87050d30014fe76d89300067f65d89300067c65d8930006bf64d8930006bc64d89300c6ee62d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893002cfd73d8930014fc73d89300c6ee32d893000cfe71d8930004fd71d893000cfc71d8930006ee21d89300c6ec21d89300c6ef20d89300057f75589300d57c75589300067f65589300067c6558930005bf74589300cdbc7458930006bf6458930006bc64589300c6ec6258930005f771589300bdf47158930004ff7654930004fe7654930004fc76549300067f65549300267c6554930006bf6454930226bc6454930004ff7650930004fe7650930004fc76509300067f65509302167c6550930006bf645093001ebc64509300e4fe76cc9300067f65cc9302067c65cc9300cdbe74cc930005bd74cc930006bf64cc9301febc64cc93002cfc764c9300067f654c9301ee7c654c930006bf644c9301e6bc644c930006ef624c930016ec624c930005fb704c93002df8704c93000cfe76d85300067f65d85300067c65d8530006bf64d8530006bc64d85300bef661d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853002cfd73d853000cfc73d8530014fe72d8530004fd72d8530014fc72d85300bef631d8530006f721d85300bef421d85300bef710d85300057f75585300d57c75585300067f65585300067c6558530005bf74585300cdbc7458530006bf6458530006bc6458530005ef72585300c5ec72585300bef46158530004ff7654530004fe7654530004fc76545300067f65545300267c6554530006bf64545301d6bc6454530004ff7650530004fe7650530004fc76505300067f65505301c67c6550530006bf645053001ebc64505300dcfe76cc5300d57e75cc5300057d75cc5300067f65cc5301b67c65cc530006bf64cc5301aebc64cc53002cfc764c5300067f654c53019e7c654c530006bf644c530196bc644c530006f7614c53000ef4614c530005fb704c53002df8704c530004ff7648530004fe7648530004fc76485300067f65485301867c6548530006bf644853017ebc6448530024ff76541300d4fd7654130024fc76541300067f65541300267c6554130006bf645413015ebc6454130005df7354130005dc735413002fd8305413001cff765
  | 12 => 0xe10d95302ee7c10d95300d67c6559530005bf74595300cdbc74595300d4ff75595300067f7559530004ff7459530006bf7459530004bf745953001cfe745953001cfc7459530006bc745953001cbc74595300f4ff7359530006df7359530004ff7259530014fe7259530014fc7259530004ff715953000cfe715953000cfc7159530114ff7059530006fb70595300057e76195300d67e76195300047e76195300067e64195300067c641953033e7f63195300067e62195300067c62195300067e61195300067c611953033f5e301953033f5c301953001cfe76d91300067f65d91300067c65d91300cebe64d9130024fe75d9130004fd75d9130024fc75d9130006bf54d91300cebe54d91300cebc54d91300a4fe73d913002cfd73d91300a4fc73d91300cebf43d9130014fe72d9130004fd72d9130014fc72d91300cebf42d9130006be42d91300cebc42d913000cfe71d9130004fd71d913000cfc71d91300cebf41d9130006be41d91300cebc41d91300ccfd70d91300cebf40d91300cdbe76d913001cbe76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130006be62d9130006bc62d9130006be61d9130006bc61d91303279e30d91303279c30d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130326bf73d91300cebe73d9130006bd73d9130006bf53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bc52d9130006be32d9130006bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bc51d9130006be31d9130006bc31d9130006bf21d9130006be21d9130006bc21d9130006bf70d9130326be70d9130006bd70d9130326bc70d9130006bf50d9130326be50d9130326bc50d9130326be30d9130326bc30d9130006bf20d9130326be20d9130326bc20d9130006bf10d9130326be10d9130326bc10d91300057f75591300d57c75591300067f65591300067c65591300cebc6459130004ff75591300067f75591300047f7559130024fe7559130024fc75591300067c75591300247c75591300ccff7459130006bf74591300ecff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff715913000cfe715913000cfc715913010cff7059130006fb7059130005be76191300cebe7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c6519130336bf6319130006be6219130006bc6219130006be6119130006bc61191303379e30191303379c3019130004ff7655130004fe7655130004fd7655130004fc7655130
  | 13 => 0x8a30024fe7558a30024fc7558a30004ff7458a30006bf7458a30004bf7458a3001cfe7458a3001cfc7458a30006bc7458a3001cbc7458a3002eef7258a300e6ee4258a300e6ee3258a30004ff7158a3000cfe7158a3000cfc7158a3002cfc7058a3002eee2058a3002eec2058a30004ff7654a30004fd7654a3002cfc7654a302e67f6554a300267c6554a30005df7354a30005dc7354a30004ff7650a30004fd7650a3002cfc7650a3001ebe6450a30006bd6450a30016ee6250a30006ed6250a300c4fd76cca300edbe74cca30005bd74cca30014ff764ca30016ee624ca30006ed624ca30005fb704ca3002df8704ca30004ff75586300067f75586300047f7558630024fe7558630024fc75586300067c75586300247c7558630004ff745863001cfe745863001cfc7458630004ff7258630014fe7258630014fc725863002ef771586300def651586300def6315863002cfc705863002ef6105863002ef41058630004ff7654630004fd765463002cfc76546300267e65546300067d655463000ef66154630006f56154630004ff7650630004fd765063002cfc76506302aebf645063001ebc6450630005df7350630005dc73506300bcfd76cc6300f57e75cc6300057d75cc63000cff764c63000ef6614c630006f5614c630005fb704c63002df8704c630004ff7648630004fd764863002cfc7648630005df7348630005dc734863002df976cc2300a6f976cc23002fda73cc2300a7da53cc230007d953cc230024fe76d95300d67e65d953001cfe74d9530004fd74d953001cfc74d95300d67f54d95300067e54d95300d67c54d95300a4fe73d953002cfd73d95300a4fc73d95300d67f53d9530014fe72d9530004fd72d9530014fc72d95300d67f52d95300067e52d95300d67c52d953000cfe71d9530004fd71d953000cfc71d95300d67f51d95300067e51d95300d67c51d95300d4fd70d95300d67f50d95300d57e76d95300247e76d95300067e64d95300067c64d95300067e62d95300067c62d95300067e61d95300067c61d95302ef5e30d95302ef5c30d95300067f74d95300067e74d95300067d74d95300067c74d95302ee7f73d95300d67e73d95300067d73d95300067f43d95300067c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067c42d95300067e32d95300067c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067c41d95300067e31d95300067c31d95300067f21d95300067e21d95300067c21d95300067f70d95302ee7e70d95300067d70d95302ee7c70d95300067f40d95302ee7e40d95302ee7c40d95302ee7e30d95302ee7c30d95300067f20d95302ee7e20d95302ee7c20d95300067f10d95302ee7
  | 14 => 0xa6de73d93300a6bf43d9330014fe72d9330004fd72d9330014fc72d933010ebf42d933000cfe71d9330004fd71d933000cfc71d93300a6f970d9330326be40d9330326bc40d93300a6bc6459330004ff7559330024fe7559330024fc75593300a6bf745933002cfc73593300a6be43593300a6bc4359330004ff7259330014fe7259330014fc7259330006be425933010ebc4259330004ff715933000cfe715933000cfc715933010ebf415933010ebf4059330004ff76553300a4fe7655330004fd76553300a4fc7655330005fb705533002df870553300b4ff7654f300a67f6554f300a67c6554f300acff7650f300a6bf6450f300a6bc6450f300a6ec6258b30004ff7558b30024fe7558b30024fc7558b30004ff7458b3001cfe7458b3001cfc7458b3002cfc7358b300a6ef3258b300a6ec3258b30004ff7158b3000cfe7158b3000cfc7158b30106ef2058b30004ff7654b30004fd7654b300a4fc7654b300267e6554b300067d6554b30004ff7650b30004fd7650b300a4fc7650b30006bf6450b3001ebc6450b30005fb7050b3002df87050b3009cff764cb30016ec624cb300a6f46158730004ff7558730024fe7558730024fc7558730004ff745873001cfe745873001cfc745873002cfc7358730004ff7258730014fe7258730014fc72587300a6f731587300a6f431587300fef71058730004ff7654730004fd76547300a4fc76547300067f65547300267c6554730005fb705473002df87054730004ff7650730004fd76507300a4fc765073001ebe6450730006bd6450730094ff764c73000ef4614c730004ff7648730004fd76487300a4fc7648730024ff76543300267e65543300067d6554330005df73543300a5dc735433002fda305433001cff765033001ebe6450330006bd6450330005df73503300a5dc735033002fb8405033002e7f7559630004ff745963001cfe745963001cfc74596300f67f5359630004ff7259630014fe7259630014fc7259630004ff715963000cfe715963000cfc71596300f67f515963002cfc705963002e7e505963002e7c5059630004ff7559230024fe7559230024fc755923002ebf74592300eebf4359230004ff7259230014fe7259230014fc72592300eebf4259230004ff715923000cfe715923000cfc715923002cfc705923002ebe405923002ebc4059230004ff765523002cfe7655230004fd765523002cfc7655230005df7355230005dc735523002ede3058e300d4fd7694e302ee7f6594e300267c6594e300f75f5394e30024ff7654e3002cfc7654e300267e6554e300067d6554e30005fb7054e3002df87054e300ccfd7690e30326bf6490e3001ebc6490e3001cff7650e3002cfc7650e3001ebe6450e30006bd6450e300ef9c4350e30005fb7050e3002df87050e30004ff755
  | 15 => 0xf5394d40004ff7654d40004fe7654d40004fc7654d4002cbc7650d4001dbf7350d4001f9f7350d400079f6350d400a6bc6350d400079c6350d400069c6350d40005bf7250d40236be6250d40236bc6250d40007bb7050d4002dbe7050d4002dbc7050d40007b87050d4002db87050d4001ebf6050d4001fbb6050d40014fe76d8940126ee62d8940024fe75d8940004fd75d8940024fc75d894002cfd74d8940014fc74d89400a4fe73d8940004fd73d8940126ee42d8940086ed42d894000cfe71d8940004fd71d894000cfc71d8940006ee21d8940126ec21d894001cfd70d8940126ef20d8940126ec6258940355fb7058940004ff7654940004fe7654940004fc76549400067f65549400267c655494002dbc7650940016bc765094002cbc7650940005bf7350940006bc635094001dbf725094001faf7250940007af6250940016be6250940016bc6250940127ac6250940007bb705094002dbe705094002dbc7050940007b8705094001ebf605094001fbb6050940127af2050940004fe76cc940004fd76cc9400a4fc76cc94001dbe74cc940005bd74cc940006df63cc9400a6dc63cc940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940006df634c940006dc634c94000cfe76d854011ef661d8540024fe75d8540004fd75d8540024fc75d854002cfd74d854000cfc74d85400a4fe73d8540004fd73d8540056bf43d8540006bd43d8540014fe72d8540004fd72d8540014fc72d8540056bf42d8540006bd42d854011ef641d8540056f541d854001cfd70d854034ebe40d854034ebc40d854011ef710d85400057f755854012d7c7558540005df7358540005dc7358540005ef7258540125ec725854011ef46158540345fb7058540004ff7654540004fe7654540004fc7654540005bf745454001dbc7454540004fe76cc540004fd76cc5400a4fc76cc54012d7e75cc5400057d75cc54001dbe74cc540005bd74cc540004ff764c540004fe764c540004fc764c540004ff7648540004fe7648540004fc7648540024ff765414001cfe765414015cfd765414001cfc76541400067f65541400267c6554140005bf745414001dbc745414002fb8405414001cfe74d9730004fd74d97300a4fc74d97300a6de73d97300a67f53d9730014fe72d9730004fd72d9730014fc72d973000cfe71d9730004fd71d973000cfc71d97301167f51d97300a6f970d97302ee7e50d97302ee7c50d97300a67c65597300a67f7559730004ff745973001cfe745973001cfc745973002cfc73597300a67e53597300a67c5359730004ff7259730014fe7259730014fc72597301167f5259730004ff715973000cfe715973000cfc71597300067e51597301167c51597301167f5059730024fe75d9330004fd75d93300a4fc75d9330
  | 16 => 0x4a4001dbc7454a400a4ff76cca4002cfe76cca40004fd76cca4001dbe74cca40005bd74cca40004ff764ca40004fd764ca4002cfc764ca40005bf744ca4001dbc744ca40016ee624ca40006ed624ca40004ff7558640024fe7558640024fc7558640004ff73586400a4fc7358640004ff7258640014fe7258640014fc725864002ef77158640136f65158640136f6415864003ef54158640136f63158640006f72158640136f4215864002cfe705864002cfc705864002ef6105864002ef41058640004ff7654640004fd765464002cfc76546400267e65546400067d655464000ef66154640006f561546402adbf765064000ebf765064000cbf7650640005bc7350640006bd635064013dbe725064013dbc7250640006bd625064001dbf715064001fb7715064000ebe61506402afb661506402afb5615064000ebc61506402adbf7050640007bb70506402afb8705064001ebe605064001fba60506400a4ff76cc64002cfe76cc640004fd76cc6401457e75cc6400057d75cc640005bf74cc64001dbc74cc640004ff764c640004fd764c64002cfc764c640005bf744c64001dbc744c64000ef6614c640006f5614c640004ff7648640004fd764864002cfc7648640005bf744864001dbc7448640024fe76d954012e7e65d954002cff74d954001cfe74d954002cfd74d954001cfc74d95401767f54d95401767d54d95400a4fe73d9540004fd73d954012e7c53d9540014fe72d9540004fd72d9540014fc72d954012e7f52d954000cfe71d9540004fd71d954000cfc71d95400067e51d954012e7c51d954001cfd70d954012e7f50d954012e7c6559540005df7359540005dc735954035dfb7059540174ff75595400067f755954015cff7459540006bf7459540004ff7359540006df7359540004df73595400a4fc7359540006dc7359540004dc7359540004ff7259540014fe7259540014fc7259540004ff715954000cfe715954000cfc715954035cff7059540006fb7059540024fe75d8d40004fd75d8d40024fc75d8d4002cfd74d8d40006df53d8d40006dc53d8d400eede43d8d400eedd43d8d40014fe72d8d40004fd72d8d40014fc72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d40006de31d8d40006dc31d8d40006df6398d400cdf97098d400057f7558d4012d7c7558d4010dfb7058d40006dd6318d40024fe7518d40004fd7518d400a4fc7518d4002cfd7418d40006df5318d400a6dc5318d400a6bf4318d400a6de4318d400aedd4318d40014fe7218d40004fd7218d40014fc7218d400aebf4218d4000cfe7118d40004fd7118d4000cfc7118d40006de3118d400a6dc3118d40336be4018d40336bc4018d40004fe7694d40004fd7694d400a4fc7694d400067f6594d400267c6594d4001dbe7494d40005bd7494d4012f5
  | 17 => 0x4ff764c950004fe764c950004fc764c95000cfe76d855014ef661d855002cfd75d855000cfc75d855001cfe74d8550004fd74d855001cfc74d85500a4fe73d8550004fd73d8550014fe72d8550004fd72d8550014fc72d855014ef651d855005ef551d8550006f721d855014ef421d8550024fd70d855014ef710d855014ef46158550365fb705855002d7c765455000e7c765455002c7c76545500057f73545500067c63545500067f62545500257f715455002777715455000777615455000e7e615455000e7c615455014f7461545500077b705455002d7e705455002d7c70545500077870545500267f60545500277b605455014f771054550004ff7650550004fe7650550004fc7650550006bf645055001ebc6450550004fe76cc550004fd76cc5500a4fc76cc5500257e75cc5500057d75cc550006df63cc5500a6dc63cc550004ff764c550004fe764c550004fc764c5500257e754c5500057d754c550006df634c550006dc634c550004ff7648550004fe7648550004fc764855002e7f755964015e7f545964015e7d5459640004ff73596400a4fc73596401467f5359640004ff7259640014fe7259640014fc72596400067e52596401467c5259640004ff715964000cfe715964000cfc71596401467f515964002cfe705964002cfc705964002e7e505964002e7c5059640024fe7598e40004fd7598e400a4fc7598e4002ede7398e400a6de4398e4010edd4398e40014fe7298e40004fd7298e40014fc7298e4000cfe7198e40004fd7198e4000cfc7198e4002cfe7098e4002cfc7098e4002ede3098e4002edc3098e40004ff7558e40024fe7558e40024fc7558e4002edf7358e400cede4358e400cedd4358e400cebc4358e40004ff7258e40014fe7258e40014fc7258e40006be4258e400cebc4258e40004ff7158e4000cfe7158e4000cfc7158e400cebf4158e4002cfc7058e4002ebf4058e4002ebd4058e4002ede3058e4002edc3058e400a4ff7694e4002cfe7694e40004fd7694e401475f5394e40004ff7654e40004fd7654e4002cfc7654e400267e6554e400067d6554e40005bf7454e4001dbc7454e4001dbe7390e4001f9e7390e403279e6390e40006bd6390e403279d6390e4013dbe7290e4013dbc7290e40005bd7190e40327ba7090e40325bd7090e40007b97090e4001ebe6090e4001fba6090e40004ff7558a40024fe7558a40024fc7558a40004ff7358a400a4fc7358a40006be4358a4006ebc4358a4002eef7258a4013ebe4258a4013eee4258a4006eed4258a4013ebc4258a4013eee3258a40004ff7158a4000cfe7158a4000cfc7158a4006ebf4158a4002cfe7058a4002cfc7058a4002ebf4058a4002ebd4058a4002eee2058a4002eec2058a40004ff7654a40004fd7654a4002cfc7654a40005bf745
  | 18 => 0xe7258650014fc72586500467f52586500067d525865002ef771586501667e5158650166f65158650166765158650046f551586501667c5158650166f6315865002cfe705865002cfc705865002e7f505865002e7d505865002ef6105865002ef41058650004ff7650650004fd765065002cfc76506500057f75506500257c75506500a4ff76cc65002cfe76cc650004fd76cc6500257e75cc6500057d75cc650004ff764c650004fd764c65002cfc764c6500057f754c6500257c754c65000ef6614c650006f5614c650004ff7648650004fd764865002cfc76486500057f75486500257c754865001cfe76d915015ebe64d915002cfd75d915001cfc75d915015ebe54d9150146bd54d91500a4fe73d9150004fd73d915015ebc43d9150014fe72d9150004fd72d9150014fc72d9150006be42d915015ebc42d915000cfe71d9150004fd71d915000cfc71d915015ebf41d9150024fd70d915015ebf40d915015ebc6459150005df7359150005dc735915037dfb705915002cfd75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d500f6de53d8d500f6dd53d8d50006df43d8d50006dc43d8d50014fe72d8d50004fd72d8d50014fc72d8d50006de32d8d50006dc32d8d5000cfe71d8d50004fd71d8d5000cfc71d8d50006df6398d500d5f97098d50005bf7458d5015dbc7458d50115fb7058d50006dd6318d5002cfd7518d5001cfe7418d50004fd7418d500a4fc7418d500a67f5318d500a6de5318d500b6dd5318d50006df4318d500a6dc4318d50014fe7218d50004fd7218d50014fc7218d50006de3218d500a6dc3218d5000cfe7118d50004fd7118d5000cfc7118d500b67f5118d5033e7e5018d5033e7c5018d5002c7c7654d500257f7354d500275f7354d500075f6354d500a67c6354d500075c6354d500057f7154d5025e7e6154d5025e7c6154d500077b7054d5002d7e7054d5002d7c7054d50007787054d500267f6054d500277b6054d50004fe7690d50004fd7690d500a4fc7690d500257e7590d500057d7590d50006bf6490d5001ebc6490d50004ff7650d50004fe7650d50004fc7650d50014fe76d8950156ee62d895002cfd75d8950014fc75d895001cfe74d8950004fd74d895001cfc74d89500a4fe73d8950004fd73d895008e7f53d89500067d53d8950156ee52d895008eed52d895000cfe71d8950004fd71d895000cfc71d895008e7f51d8950024fd70d89503767e50d89503767c50d8950156ef20d8950005bf745895015dbc7458950005df7358950005dc7358950156ec6258950005f7715895014df4715895036dfb7058950004ff7650950004fe7650950004fc76509500057f75509500257c7550950004fe76cc950004fd76cc9500a4fc76cc9500257e75cc9500057d75cc95015dbe74cc950005bd74cc950
  | 19 => 0xd2102cfe76d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d81210a4fe73d8121004fd73d812100cfd72d8121014fd71d81212f6fa20d81212a6fa10d8121006fb60981210057f75581211857c7558121005bf745812117dbc7458121005df7358121005dc735812102efa6018121006f9601812102ebf7459250176be545925012ebd5459250004ff73592500a4fc7359250176bf4359250004ff7259250014fe7259250014fc7259250176bf4259250004ff715925000cfe715925000cfc7159250006be4159250176bc415925002cfe705925002cfc705925002ebe405925002ebc405925001cfe7498e50004fd7498e500a4fc7498e5002ede7398e500a6de5398e50116dd5398e50014fe7298e50004fd7298e50014fc7298e5000cfe7198e50004fd7198e5000cfc7198e5002cfe7098e5002cfc7098e5002ede3098e5002edc3098e50004ff7458e5001cfe7458e5001cfc7458e5002edf7358e500d6de5358e500d6dd5358e500d67c5358e50004ff7258e50014fe7258e50014fc7258e500d67f5258e50004ff7158e5000cfe7158e5000cfc7158e500067e5158e500d67c5158e5002cfc7058e5002e7f5058e5002e7d5058e5002ede3058e5002edc3058e500257e7394e500275e7394e502ef5e6394e500067d6394e502ef5d6394e500065d6394e500057d7294e501657e7194e501657c7194e502ef7a7094e502ed7d7094e50007797094e50005797094e500267e6094e500277a6094e500a4ff7690e5002cfe7690e50004fd7690e50004ff7650e50004fd7650e5002cfc7650e500057f7550e500257c7550e5001ebe6450e50006bd6450e50004ff7458a5001cfe7458a5001cfc7458a50004ff7358a500a4fc7358a5002eef7258a5016eee5258a50076ed5258a5016eee4258a5016eee3258a50004ff7158a5000cfe7158a5000cfc7158a50006ee2158a5016eec2158a5002cfe7058a5002cfc7058a5002eee2058a5002eec2058a502e57f7654a500167f7654a500147f7654a500057c7354a500067d6354a500257f7254a500276f7254a500167e6254a502e76e6254a502e76d6254a500167c6254a501657e7154a501657c7154a502e57f7054a500077b7054a500057b7054a502e7787054a500267e6054a500277a6054a50004ff7650a50004fd7650a5002cfc7650a5001ebe6450a50006bd6450a50016ee6250a50006ed6250a500a4ff76cca5002cfe76cca50004fd76cca500057f75cca500257c75cca50175be74cca50005bd74cca50004ff764ca50004fd764ca5002cfc764ca500057f754ca500257c754ca50016ee624ca50006ed624ca50004ff745865001cfe745865001cfc7458650004ff73586500a4fc73586500067e53586500467c5358650004ff7258650014f
  | 20 => 0x5bf745952117dbc74595213c5ef72595213d5f771595213ccff75595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc7459521004ff73595210a4fc73595213c4ff7259521006ef725952121cff7159521006f77159521004ff705952102cfc705952101cfe76d912117ebe64d9121024fe75d9121004fd75d9121024fc75d912120cfd74d9121006bf54d912117ebc54d91210a4fe73d9121004fd73d912117ebf43d912100cff72d912100cfd72d91213bebf42d91213bebd42d9121014ff71d9121014fd71d91213aebf41d91213aebd41d912102cfe70d9121004fd70d912117ebc40d912101cff76591210057f75591211857c755912117ebc64591213a5ef72591213b5f77159121004ff75591210067f75591210047f7559121024fe7559121024fc75591210067c75591210247c75591213acff7459121006bf7459121004ff73591210a4fc73591213a4ff7259121006ef725912120cff7159121006f77159121004ff705912102cfc7059121004ff7655121004fe7655121004fd7655121004fc7655121024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2100cff72d8d2100cfd72d8d2139edf32d8d2139edd32d8d21014ff71d8d21014fd71d8d21396df31d8d21396dd31d8d2102cfe70d8d21004fd70d8d211dcfd7698d211857e7598d210057d7598d2117dbe7498d21005bd7498d21006df6398d211dded7298d2118df57198d21024fe7598d210a67e7598d210247e7598d21004fd7598d210a67d7598d210047d7598d210a4fc7598d2101cfe7498d210a6be7498d2101cbe7498d21004fd7498d210a6bd7498d21004bd7498d210a4fc7498d210a4fe7398d211dcfd7298d210a6ed7298d211f4fd7198d210a6f57198d2102cfe7098d21004fd7098d211f5ef7258d211a5f77158d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21006df7358d211f4ff7258d21006ef7258d211dcff7158d21006f77158d21004ff7058d2102cfc7058d21394fe7618d21006dd6318d21024fe7518d21004fd7518d210a4fc7518d2101cfe7418d21004fd7418d210a4fc7418d210a4fe7318d210a6de7318d2100cff7218d2100cfd7218d210a6df3218d2138edd3218d21014ff7118d21014fd7118d210a6df3118d21386dd3118d2102cfe7018d21004fd7018d210a4ff7694d21004fe7694d21004fd7694d210a4fc7694d211875f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210267c6554d210a4ff7690d21004fe7690d21004fd7690d210a4fc7690d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2101ebc645
  | 21 => 0xd70d9131196bc40d9131196bc64591313f5df7359131004ff7559131024fe7559131024fc7559131244ff7459131006bf74591313f4ff7359131006df7359131004ff7259131014fe7259131014fc725913122cff7159131006f77159131004ff705913102cfc7059131004ff7655131004fe7655131004fd7655131004fc76551313ecfe7694d310267e6594d310067d6594d3119f5f5394d310a7d43194d31024ff7654d3100cfe7654d3125cfd7654d3100cfc7654d310067f6554d310267c6554d31005f77154d3100df47154d3125fd43154d313e4fe7690d310a7d43190d3101cff7650d3100cfe7650d3122cfd7650d3100cfc7650d31006bf6450d3101ebc6450d311979c4350d31005f77150d3100df47150d3122fd43150d31014fe76d893118eee62d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d893100cfd73d8931006ef52d893118eec52d893118eee42d893118eee32d89311f6ef21d893102cfe70d8931004fd70d893118eec20d893118eec6258931004ff7654931004fe7654931004fc76549310267e65549310067d6554931005f7715493100df47154931004ff7650931004fe7650931004fc7650931006bf645093101ebc6450931006ef6250931016ec6250931384fe76cc931195be74cc931005bd74cc931385de76cc93139ede76cc9310079e74cc9310079d74cc9311dddd72cc931016de62cc931016dc62cc93100dde71cc93100ddc71cc9310a6df61cc9311f7d710cc93100cfc764c931006ef624c931016ec624c931005f7714c93100df4714c93100ddc764c931016dc764c93100cdc764c9311f5df724c931007cf724c931007cf624c931016de624c931016dc624c93118fcc624c931007d7714c93100dde714c93100ddc714c9311dfd4714c9311dedf614c93118fcf204c9311dfd7104c9310a77675cc5310a77575cc53100df673cc53100fd673cc53100ef763cc53100fd763cc5310a7d732cc531007d532cc531005f570cc531024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d8131014fe72d8131004fd72d8131014fc72d8131006fb50d8131006f850d81310fefa10d8131006fb60981310057f755813119d7c7558131005bf7458131195bc7458131005ef725813118dec725813119d7e75181310057d751813102efa6018131006f96018131024fe76d95211867e65d952121cfd75d952101cfe74d9521004fd74d952101cfc74d95210067e54d95211867c54d95210a4fe73d9521004fd73d95211867f53d952100cff72d952100cfd72d95213de7f52d95213de7d52d9521014ff71d9521014fd71d95213ce7f51d95213ce7d51d952102cfe70d9521004fd70d95211867c50d9521024ff76595211867c6559521
  | 22 => 0x4f313f4ff7650f3123e7e6550f310067d6550f310a6bf6450f310a6bc6450f310a79c4350f31014ff7658b310067e6558b310067d6558b310a6ec6258b31004ff7558b31024fe7558b31024fc7558b31004ff7458b3101cfe7458b3101cfc7458b3100cfc7358b31006ef4258b311a6ec4258b310a6ef3258b310a6ec3258b311deef2158b31004ff7058b3102cfc7058b311a6ef2058b31004ff7654b31004fd7654b310a4fc7654b310267e6554b310067d6554b31004ff7650b31004fd7650b310a4fc7650b312167e6550b310067d6550b31006bf6450b3101ebc6450b31005f77150b3100df47150b3100ddd76ccb31016dd76ccb3100cdd76ccb310a75e65ccb310a75d65ccb310a79e74ccb310a79d74ccb31016de62ccb310a7ce62ccb310a7cd62ccb31016dc62ccb3100dde71ccb310a7d671ccb310a7d571ccb3100ddc71ccb31394ff764cb311ee7e654cb310067d654cb31395df764cb3138edf764cb310075e654cb310075d654cb310a7cf724cb31016de624cb31016dc624cb3100dde714cb3100ddc714cb311a7cf204cb310067e65983310067d65983310a6fb609833102ef860983310067e65583310067d6558331005bf74583311adbc74583310a6f86058331004ff7558331024fe7558331024fc7558331004ff7458331006bf7458331004bf745833101cfe745833101cfc7458331006bc745833101cbc745833100cfc7358331004ff7258331014fe7258331014fc72583310bef631583310a6fb30583310a6f830583310befa1058331024fe76d953119e7e65d953101cfe74d9531004fd74d953101cfc74d953100cfd73d953119e7f53d9531014fe72d9531004fd72d9531014fc72d95310a4ff71d9531274fd71d95312767f51d95312767d51d953102cfe70d9531004fd70d953119e7c50d9531276f710d953119e7c6559531005bf7459531195bc74595313fddf7359531005ef725953118dec7259531005fb7059531005f87059531274ff75595310067f7559531004ff7459531006bf7459531004bf745953101cfe745953101cfc7459531006bc745953101cbc74595313fcff7359531006df735953119e7c5359531004ff7259531006ef7259531004ef7259531014fe7259531014fc7259531006ec7259531014ec725953119e7f525953125cff7159531006f7715953125e7e515953125e7c5159531004ff7059531006fb7059531004fb705953102cfc7059531006f8705953102cf8705953119e7f505953125ef7105953101cfe76d9131196be64d9131024fe75d9131004fd75d9131024fc75d9131006bf54d9131196bc54d913100cfd73d9131196bf43d9131014fe72d9131004fd72d9131014fc72d9131196bf42d91310a4ff71d9131244fd71d9131246bf41d9131246bd41d913102cfe70d9131004f
  | 23 => 0x6f9601814125cfd75d973101cfe74d9731004fd74d97310a4fc74d97310a4fe73d97310a6de73d9731014fe72d9731004fd72d9731014fc72d97310a6f571d973102cfe70d9731004fd70d973125c7d76997310a67f64997310067e64997310a67c64997310a67e63997310a67f62997310067e62997310a67c62997313fe7d61997313ff5e31997310a77631997310a75c31997310a67f60997310a67c6099731024ff76597310a67c65597310a67f7559731004ff745973101cfe745973101cfc74597311b67f54597310067e54597311b67c545973100cfe735973100cfc73597310a67e53597310a67c5359731004ff7259731014fe7259731014fc72597311b67f52597310067e52597311b67c525973125e7f515973125e7d5159731004ff705973102cfc70597311b67f50597311b67c50597310a57f76597311b67f76597310247f76597310a67f64597310067e64597310a67c64597310a67f62597310067e62597310a67c625973125f5e31597310a77631597310a75c31597310a67f60597310a67c60597310067f74597310067e74597310067d74597310067c74597311b67f73597310a67e73597310a67c73597310067f43597310a67e43597310a67c43597310067f72597310067e72597310067d72597310067c72597310067f42597310067e42597310067c42597310a67f32597310067e32597310a67c325973125e7f715973125e7e715973125e7d715973125e7c715973125e7f415973125e7e415973125e7d415973125e7c41597310a67f315973125e7e315973125e7d31597310a67c315973125e7f215973125e7e215973125e7d215973125e7c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067c40597310a67f30597310a67c30597310067f20597310067c205973125e7f105973125e7e105973125e7d105973125e7c1059731024fe75d93310a67e75d93310247e75d9331004fd75d93310a67d75d93310047d75d93310a4fc75d933122cfd74d93310a4fe73d93310a6de73d93310a6bf43d9331014fe72d93310a6ee72d9331014ee72d9331004fd72d93310a6ed72d9331004ed72d9331014fc72d93311aebf42d93310a6f571d933102cfe70d9331004fd70d93311aebc40d933101cff76593310067e65593310067d65593310a6bc6459331004ff7559331024fe7559331024fc75593310a6bf745933100cfe735933100cfc73593310a6be43593310a6bc4359331004ff7259331014fe7259331014fc7259331006be42593311aebc425933122ebf415933122ebd4159331004ff705933102cfc70593311aebf4059331004ff76553310a4fe7655331004fd76553310a4fc76553310267e65553310067d65553313fcff7654f310267e6554f3125e7d6554f3125fd6315
  | 24 => 0xf7459541006bf7459541004ff73595410a4fc7359541004ff7259541006ef7259541004ef7259541014fe7259541014fc7259541006ec7259541014ec725954128cff7159541006f77159541004ff705954102cfc7059541024fe75d8d41004fd75d8d41024fc75d8d4100cfd74d8d4141ede43d8d4141edd43d8d41014fe72d8d41004fd72d8d41014fc72d8d4101cfd71d8d413f6df31d8d4102cfe70d8d41004fd70d8d411c57e7598d410057d7598d41006df6398d411bdee7298d41005ed7298d41195f57198d411adf77158d41006dd6318d41024fe7518d41004fd7518d410a4fc7518d4100cfd7418d410a6bd7418d410a6bf4318d410a6de4318d41416dd4318d41014fe7218d41004fd7218d41014fc7218d41416bf4218d410a4ff7118d4101cfd7118d410a6df3118d413e6dd3118d4102cfe7018d41004fd7018d41416bc4018d41004fe7694d41004fd7694d410a4fc7694d4101dbe7494d41005bd7494d411c75f5394d4100df67194d41005f57194d41004ff7654d41004fe7654d41004fc7654d410067f6554d410267c6554d4100dbc7650d4122ebc7650d4100cbc7650d4101dbf7350d4101f9f7350d410079f6350d410a6bc6350d410079c6350d41005bf7250d41236be6250d41236bc6250d41007b77150d4100dbe7150d4100dbc7150d4122fb47150d4101ebf6150d4101fb76150d412adbc7050d41014fe76d89411beee62d8941024fe75d8941004fd75d8941024fc75d894100cfd74d89410a4fe73d8941004fd73d8941006ef52d89411beec52d89411beee42d894140eed42d89411beee32d894101cfd71d89413a6ef21d894102cfe70d8941004fd70d89411beec20d89410057f75589411c57c75589411beec6258941405f77158941004ff7654941004fe7654941004fc765494100dbc7650941016bc765094100cbc7650941005bf7350941006bc635094101dbf725094101faf7250941007af6250941016be6250941016bc62509411bfac6250941016ac6250941007b7715094100dbe715094100dbc715094120fb4715094100db4715094101ebf615094101fb761509412adbc70509411bfaf2050941004fe76cc941004fd76cc9410a4fc76cc94101dbe74cc941005bd74cc941004ff764c941004fe764c941004fc764c94101dbe744c941005bd744c941006ef624c941016ec624c94102cfe76d8141024fe75d8141004fd75d8141024fc75d814100cfd74d81412b6bd74d81410a4fe73d8141004fd73d8141346bf43d8141006bd43d8141014fe72d8141004fd72d8141014fc72d8141346bf42d8141006bd42d814101cfd71d8141346fa40d81412aebc40d81412b6fa10d8141006fb60981410057f75581411c57c7558141005df7358141005dc7358141005ef72581411bdec725814102efa6018141
  | 25 => 0x8d5145e7f50d8d513fef710d8d51006df6398d5119df57198d51005bf7458d511d5bc7458d51005ef7258d511cdec7258d511b5f77158d51005fb7058d51005f87058d51006dd6318d5100cfd7518d5101cfe7418d51004fd7418d510a4fc7418d510a6de5318d51456dd5318d51014fe7218d51004fd7218d51014fc7218d510a4ff7118d51024fd7118d510a6df3118d513eedd3118d5102cfe7018d51004fd7018d5100d7e7694d512767e7694d5100c7e7694d510257e7394d510275e7394d510067f6394d510075f6394d510065f6394d510075c6394d510057d7294d5100d7e7194d51277767194d51007757194d5100d7c7194d510267f6194d51027776194d510057d7094d512ee7c6094d51277771094d51004fe7690d51004fd7690d510a4fc7690d51006bf6490d5101ebc6490d51004ff7650d51004fe7650d51004fc7650d510057f7550d510257c7550d51014fe76d89511ceee62d895100cfd75d895101cfe74d8951004fd74d895101cfc74d89510a4fe73d8951004fd73d89511ceee52d895144eed52d8951006ef42d89511ceec42d89511ceec32d8951024fd71d89513c6ef21d895102cfe70d8951004fd70d89511ceef20d8951005bf74589511d5bc74589511ceec6258951445f7715895100d7c76549510167c765495100c7c76549510057c73549510067f63549510257f72549510276f72549510076f62549510167e62549510167c62549511cf6c625495100777715495100d7e715495100d7c715495121f74715495100d7471549510267f61549510277761549510057f70549512e67c605495121f771054951004ff7650951004fe7650951004fc7650951004fe76cc951004fd76cc9510a4fc76cc9510057f75cc9510257c75cc9511d5be74cc951005bd74cc951006ef62cc951016ec62cc951004ff764c951004fe764c951004fc764c9510057f754c9510257c754c951005f7714c95100df4714c95102cfe76d815100cfd75d815101cfe74d8151004fd74d815101cfc74d81510a4fe73d8151004fd73d8151014fe72d8151004fd72d8151014fc72d8151024fd71d8151366fa50d81512cefa10d81512d67f65981511d5be7498151005bd74981511cdee7298151005ed7298151006fb60981512d67f651815102efa6018151006f96018151024fe76d95411c67e65d954128cfd75d954100cff74d954100cfd74d954143e7f54d954143e7d54d95410a4fe73d9541004fd73d95411c67f53d9541014fe72d9541004fd72d9541014fc72d95410067e52d95411c67c52d954101cff71d954101cfd71d954142e7f51d954142e7d51d954102cfe70d9541004fd70d95411c67c50d9541024ff76595411c67c6559541425bf7459541005ef72595411bdec7259541435f7715954142cff75595410067f7559541424f
  | 26 => 0x24fe75d9132004fd75d9132024fc75d9132014fd73d91321e6bf43d91320a4ff72d913224cfd72d913224ebf42d913224ebd42d913200cfe71d9132004fd71d913200cfc71d913202cfe70d9132004fd70d91321e6bc40d913224eef20d91320057f75591321ed7c75591321e6bc6459132485df7359132005f771591321ddf47159132005fb7059132005f87059132004ff75591320067f75591320047f7559132024fe7559132024fc75591320067c75591320247c755913224cff7459132006bf7459132484ff7359132006df73591321e6bc4359132234ff7259132006ef7259132236be4259132236bc4259132004ff7159132006f77159132004f7715913200cfe715913200cfc7159132006f4715913200cf471591321e6bf4159132004ff7059132006fb7059132004fb705913202cfc7059132006f8705913202cf870591321e6bf4059132236ef2059132004ff7655132004fe7655132004fd7655132004fc765513247cfe7694d321ef5f5394d320a7cc3294d32024ff7654d32014fe7654d32264fd7654d32014fc7654d320067f6554d320267c6554d32005ef7254d32015ec7254d32267cc3254d32474fe7690d3201ebe6490d32006bd6490d3201cff7650d32014fe7650d32234fd7650d32014fc7650d32006bf6450d3201ebc6450d32005ef7250d32015ec7250d320a7ae74cc9320a7ad74cc932015ee73cc932017ce73cc932016ef63cc932017cf63cc932005ed70cc93200cfe76d85321def661d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d8532014fd73d85321def651d8532006f741d85321def441d85321def631d85321def621d853202cfe70d8532004fd70d85321def410d85321def46158532024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813200cfe71d8132004fd71d813200cfc71d8132006fb40d8132006f840d8132106fa20d8132006fb60981320057f75581321ed7c7558132005bf74581321e5bc7458132005f771581321ddf471581321e5be7418132005bd741813202efa6018132006f9601813201cfe76d91511d6be64d915100cfd75d91511d6be54d915146ebd54d91510a4fe73d9151004fd73d91511d6bc43d9151014fe72d9151004fd72d9151014fc72d9151006be42d91511d6bc42d9151024fd71d9151426bf41d915102cfe70d9151004fd70d91511d6bf40d91511d6bc6459151005ef72591511cdec7259151465f7715915100cfd75d8d513fe7d75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d5145ede53d8d5145edd53d8d5145e7c53d8d51014fe72d8d51004fd72d8d51014fc72d8d5145e7f52d8d51024fd71d8d513fe7e51d8d513fe7c51d8d513fedf31d8d5102cfe70d8d51004fd70d
  | 27 => 0xf4159332006be41593321febc4159332004ff705933202cfc70593321febf40593321febc40593320a5bf76593321febf765933201cbf76593320a6bf6559332006be6559332006bd65593320a6bc65593322379e32593320a7ae32593320a79c32593320a6bf6159332006be61593320a6bc61593320a6bf60593320a6bc6059332006bf7559332006be7559332006bd7559332006bc75593321febf73593320a6be73593320a6bc7359332006bf53593320a6be53593320a6bc5359332236bf7259332236be7259332236bd7259332236bc7259332236bf5259332236be5259332236bd5259332236bc52593320a6bf3259332236be3259332236bd32593320a6bc3259332006bf7159332006be7159332006bd7159332006bc7159332006bf5159332006be5159332006bc51593320a6bf3159332006be31593320a6bc3159332236bf2159332236be2159332236bd2159332236bc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006bc50593320a6bf30593320a6bc3059332236bf2059332236be2059332236bd2059332236bc2059332006bf1059332006bc1059332004ff76553320a4fe7655332004fd76553320a4fc765533201ebe6455332006bd645533248cff7654f320a67f6554f320a67c6554f3226ebe6454f32006bd6454f32267ce3254f32484ff7650f3201ebe6450f32236bd6450f3200cff7658732006be6458732006bd64587320a6f46158732004ff7558732024fe7558732024fc7558732004ff745873201cfe745873201cfc7458732014fc7358732006f751587321f6f451587320a6f731587320a6f431587321f6f62158732004ff705873202cfc70587321f6f71058732006be6498332006bd64983320a6fb609833202ef860983320057f75583322057c7558332006be6458332006bd64583320a6f86058332004ff75583320067f75583320047f7558332024fe7558332024fc75583320067c75583320247c7558332004ff745833201cfe745833201cfc7458332014fc73583320c6ee3258332004ff715833200cfe715833200cfc71583320a6fb30583320a6f830583320c6fa2058332024fe76d95321ee7e65d953201cfe74d9532004fd74d953201cfc74d95320067e54d95321ee7c54d9532014fd73d95321ee7f53d95320a4ff72d953227cfd72d953227e7f52d953227e7d52d953200cfe71d9532004fd71d953200cfc71d95321ee7f51d953202cfe70d9532004fd70d95321ee7c50d95321ee7c655953248ddf735953227cff75595320067f7559532004ff745953201cfe745953201cfc745953248cff7359532006df7359532264ff7259532006ef7259532004ff715953200cfe715953200cfc7159532004ff705953202cfc705953201cfe76d91321e6be64d9132
  | 28 => 0x8d420a6de4318d42496dd4318d420a4ff7218d4201cfd7218d420a6df3218d42476dd3218d4200cfe7118d42004fd7118d4200cfc7118d4202cfe7018d42004fd7018d42004fe7694d42004fd7694d420a4fc7694d420067f6594d420267c6594d422175f5394d42004ff7654d42004fe7654d42004fc7654d42005bf7454d4201dbc7454d42015be7690d4224ebe7690d42014be7690d4201dbe7390d4201f9e7390d42006bf6390d420079f6390d420079c6390d42015be7290d4224fae7290d42007ad7290d42015bc7290d4201ebf6290d4201faf6290d42005bd7190d42005bd7090d42326bc6090d4224faf2090d4200cfe76d854220ef661d8542024fe75d8542004fd75d8542024fc75d8542014fd74d85420a4fe73d8542004fd73d854201cfd72d8542006f751d854220ef451d854220ef641d854220ef431d854220ef621d854202cfe70d8542004fd70d854220ef710d85420057f75585422157c755854220ef4615854202cfe76d8142024fe75d8142004fd75d8142024fc75d8142014fd74d81420a4fe73d8142004fd73d814201cfd72d814200cfe71d8142004fd71d814200cfc71d8142356fa40d814230efa20d81422157e75981420057d7598142316bf649814220df67198142005f57198142006fb6098142316bf641814202efa6018142006f96018142264fd75d973201cfe74d97320a6be74d973201cbe74d9732004fd74d97320a6bd74d9732004bd74d97320a4fc74d97320a4fe73d97320a6de73d97320a67f53d97320a6ed72d973200cfe71d97320a6f671d973200cf671d9732004fd71d97320a6f571d9732004f571d973200cfc71d97322067f51d973202cfe70d9732004fd70d97322067c50d9732024ff76597320a67c65597320a67f7559732004ff745973201cfe745973201cfc7459732014fe7359732014fc73597320a67e53597320a67c53597322667f52597322667d5259732004ff715973200cfe715973200cfc71597320067e51597322067c5159732004ff705973202cfc70597322067f5059732024fe75d9332004fd75d93320a4fc75d9332234fd74d93320a4fe73d93320a6de73d93320a6ed72d933200cfe71d9332004fd71d933200cfc71d933202cfe70d9332004fd70d9332234bd76993320a6bf6599332006be6599332006bd65993320a6bc65993320a6be6399332486bd62993324879e32993320a7ae32993320a79c32993320a6bf6199332006be61993320a6bc61993320a6bf60993320a6bc609933201cff76593320a6bc6459332004ff7559332024fe7559332024fc75593320a6bf7459332006bf54593321febe54593321febc5459332014fe7359332014fc73593320a6be43593320a6bc4359332236bf4259332236bd4259332004ff715933200cfe715933200cfc71593321feb
  | 29 => 0xa4fc7418d520a67f5318d520a6de5318d524c6dd5318d520a4ff7218d52024fd7218d520a6df3218d5247edd3218d5200cfe7118d52004fd7118d5200cfc7118d524c67f5118d5202cfe7018d52004fd7018d524c67c5018d520157c7654d522667c7654d520147c7654d520257f7354d520275f7354d520075f6354d520a67c6354d520075c6354d520076f7254d520157e7254d520157c7254d522676c7254d520267f6254d520276f6254d520057f7154d5225e7e6154d5225e7c6154d522e57c7054d52004fe7690d52004fd7690d520a4fc7690d520257e7590d520057d7590d52015ee7290d52005ed7290d52004ff7650d52004fe7650d52004fc7650d52006bf6450d5201ebc6450d5200cfe76d855221ef661d8552014fd75d855201cfe74d8552004fd74d855201cfc74d85520a4fe73d8552004fd73d8552024fd72d855221ef651d8552006f741d855221ef441d855221ef631d855221ef621d855202cfe70d8552004fd70d855221ef410d8552005bf7458552225bc745855221ef4615855202cfe76d8152014fd75d815231e7d75d815201cfe74d8152004fd74d815201cfc74d81520a4fe73d8152004fd73d815236e7f53d81520067d53d8152024fd72d815200cfe71d8152004fd71d815200cfc71d815236e7f51d815236efa50d81522e67c50d815231efa20d8152006fb6098152005bf7458152225bc7458152005df7358152005dc7358152005f7715815221df4715815202efa6018152006f96018152024fe76d95422167e65d9542294fd75d9542014ff74d9542014fd74d95424be7f54d95424be7d54d95420a4fe73d9542004fd73d95422167c53d954201cff72d954201cfd72d95424ae7f52d95424ae7d52d954200cfe71d9542004fd71d954200cfc71d95420067e51d95422167c51d954202cfe70d9542004fd70d95422167f50d9542024ff76595422167c65595424a5bf74595424b5ef7259542005f7715954220df471595424acff75595420067f75595424a4ff7459542006bf7459542004ff73595420a4fc7359542294ff7259542006ef7259542004ff7159542006f77159542004f7715954200cfe715954200cfc7159542006f4715954200cf47159542004ff705954202cfc7059542024fe75d8d42004fd75d8d42024fc75d8d42014fd74d8d42486bd74d8d4249ede43d8d4249edd43d8d4249ebc43d8d4201cfd72d8d42486be42d8d42486bc42d8d42486df32d8d4200cfe71d8d42004fd71d8d4200cfc71d8d4249ebf41d8d4202cfe70d8d42004fd70d8d4249ebf40d8d42486ef20d8d42006df6398d421e5ed7298d420057f7558d422157c7558d421fdef7258d42005f77158d4220df47158d42005fb7058d42005f87058d42006dd6318d42024fe7518d42004fd7518d420a4fc7518d42014fd741
  | 30 => 0xf54d95432867d54d954301cfd73d954323e7f53d9543014fe72d9543004fd72d9543014fc72d95430067e52d954323e7c52d954300cfe71d9543004fd71d954300cfc71d954323e7f51d954302cfe70d9543004fd70d954323e7c50d954323e7c65595434eddf7359543005fb7059543005f87059543284ff75595430067f755954326cff7459543006bf74595434ecff7359543006df7359543004ff7259543014fe7259543014fc7259543004ff715954300cfe715954300cfc7159543004ff7059543006fb7059543004fb705954302cfc7059543006f8705954302cf870595434e4fe7694d4323f5f5394d430a79c4394d43024ff7654d4301cfe7654d4326cfd7654d4301cfc7654d430067f6554d430267c6554d43005bf7454d4301dbc7454d4326f9c4354d430a5be7390d430a79e7390d430a6bf6390d4301f9f6390d43235be7290d430a5bc7290d43005bd7190d43005bd7090d43014fe76d894301dbe74d8943236ee62d8943237ae42d8943024fe75d8943004fd75d8943024fc75d894301cfd73d8943006be43d89431febc43d8943236be42d8943236ee42d8943236bc42d8943236ee32d894300cfe71d8943004fd71d894300cfc71d89431febf41d894302cfe70d8943004fd70d89431febf40d89430057f755894323d7c7558943236ec6258943005f7715894322df47158943005fb7058943005f8705894300cfe76d854322ef661d8543024fe75d8543004fd75d8543024fc75d854301cfd73d8543014fe72d8543004fd72d8543014fc72d854322ef641d854322ef631d8543006f721d854322ef421d854302cfe70d8543004fd70d854322ef46158543024fe75d8143004fd75d8143024fc75d8143014fe72d8143004fd72d8143014fc72d814300cfe71d8143004fd71d814300cfc71d8143006fb50d8143006f850d814310efa40d8143006fb20d8143006f820d8143006fb60981430057f755814323d7c7558143326bf6418143235ee7218143005ed721814302efa6018143006f9601814301cfe76d9152226be64d9152014fd75d9152226be54d91524debd54d91520a4fe73d9152004fd73d9152226bf43d9152024fd72d91524a6bf42d915200cfe71d9152004fd71d915200cfc71d9152006be41d9152226bc41d915202cfe70d9152004fd70d9152226bc40d9152226bc64591524d5ef7259152005f7715915221df47159152014fd75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d524cede53d8d524cedd53d8d52024fd72d8d5248edf32d8d5200cfe71d8d52004fd71d8d5200cfc71d8d5202cfe70d8d52004fd70d8d52225be7498d52005bd7498d52006df6398d521eded7298d5221df67198d52005f57198d52205ef7258d52006dd6318d52014fd7518d520a67d7518d5201cfe7418d52004fd7418d52
  | 31 => 0x91530a57e7394d530a75e7394d530a67f6394d530275f6394d530265f6394d530057d7294d5325d7e7194d530a57c7194d530057d7094d53014fe76d8953266ee62d895301cfe74d8953004fd74d895301cfc74d8953024fd73d8953266ee52d8953266ee32d895300cfe71d8953004fd71d895300cfc71d8953006ee21d8953266ec21d895302cfe70d8953004fd70d8953266ec625895300cfe76d85530257e75d855325ef661d855325f7651d855301cfe74d8553004fd74d855301cfc74d8553024fd73d85530067e53d85531b67c53d8553014fe72d8553004fd72d8553014fc72d85531b67f52d855325e7e51d855325ef651d855325e7651d855325e7c51d855325ef631d855302cfe70d8553004fd70d85531b67f50d8553005bf745855326dbc7458553005ef7258553265ec725855325ef46158553005fb7058553005f8705855301cfe74d8153004fd74d815301cfc74d8153014fe72d8153004fd72d8153014fc72d815300cfe71d8153004fd71d815300cfc71d8153116fa50d8153006fb40d8153006f840d8153006fb10d8153006f810d8153006fb6098153005bf745815326dbc74581532ee7f651815325df67118153005f5711815302efa6018153006f9601815326cfd75d96430a6bd74d96430a4fe73d96430a6de73d9643014fe72d9643004fd72d9643014fc72d964300cfe71d9643004fd71d964300cfc71d964302cfe70d9643004fd70d9643024ff76596430a67c65596430a67f755964326e7f545964326e7d54596430a4fe73596430a4fc73596430a67e53596430a67c5359643004ff7259643014fe7259643014fc72596432567f5259643004ff715964300cfe715964300cfc71596430067e51596432567c5159643004ff705964302cfc70596432567f50596434ecff7654e4326f9f4354e43014ff7658a430a6ec6258a43004ff7558a43024fe7558a43024fc7558a430a4fc7358a4324eee5258a4324eee4258a430a6ef3258a430a6ec3258a43004ff7158a4300cfe7158a4300cfc7158a43006ee2158a4324eec2158a43004ff7058a4302cfc7058a4324eef2058a4300cff76586430a6f46158643004ff7558643024fe7558643024fc75586430a4fc7358643196bf4358643004ff7258643014fe7258643014fc7258643196bf4258643246f641586430a6f731586430a6f43158643004ff705864302cfc7058643196bc4058643246f710586430a6fb609824302ef860982430a6f86058243004ff7558243024fe7558243024fc75582430a4fc73582430cebf4358243004ff7258243014fe7258243014fc72582430cebf4258243004ff715824300cfe715824300cfc71582430cefa4058243326bc40582430a6fb30582430a6f83058243024fe76d954323e7e65d95430a4ff74d9543284fd74d95432867
  | 32 => 0x6dd6318d5401cfd7518d54024fd7418d540a6de5318d544fedd5318d540a6de4318d544e6dd4318d54014fe7218d54004fd7218d54014fc7218d5400cfe7118d54004fd7118d5400cfc7118d5402cfe7018d54004fd7018d54014fe76d8954296ee62d895401cfd75d8954024fd74d89540a4fe73d8954004fd73d8954296ee52d8954296ee42d895400cfe71d8954004fd71d895400cfc71d8954006ee21d8954296ec21d895402cfe70d8954004fd70d8954296ec6258954005f7715895428df4715895400cfe76d855428ef661d855401cfd75d8554024fd74d85540a4fe73d8554004fd73d8554014fe72d8554004fd72d8554014fc72d855428ef651d855428ef641d8554006f721d855428ef421d855402cfe70d8554004fd70d8554005ef7258554295ec725855428ef4615855402cfe76d815401cfd75d8154024fd74d81540a4fe73d8154004fd73d8154014fe72d8154004fd72d8154014fc72d815400cfe71d8154004fd71d815400cfc71d815437efa50d815435efa40d8154006fb6098154005df7358154005dc735815402efa6018154006f9601815401cff76592530a6bc645925323f5f5359253286be545925323ebd54592530a4fe73592530a4fc73592530a6be43592530a6bc4359253004ff7259253014fe7259253014fc7259253006be4259253286bc4259253004ff715925300cfe715925300cfc7159253286bf4159253004ff705925302cfc7059253286bf4059253014ff7658a531ef5f5358a530a6ec6258a53004ff7458a5301cfe7458a5301cfc7458a530a4fc7358a531ee7f5358a5327eee5258a530a6ef3258a530a6ec3258a53004ff7158a5300cfe7158a5300cfc7158a531ee7f5158a53004ff7058a5302cfc7058a531ee7c5058a5327eef2058a5300cff765865319f5f53586530a6f46158653004ff745865301cfe745865301cfc74586530a4fc7358653004ff7258653014fe7258653014fc7258653276f65158653276f641586530a6f731586530a6f43158653006f72158653276f42158653004ff705865302cfc7058653276f710586530f75f53982530a6fb609825302ef860982530d75f53582530a6f86058253004ff745825301cfe745825301cfc74582530a4fc73582530d67f5358253004ff7258253014fe7258253014fc7258253004ff715825300cfe715825300cfc71582530d67f51582530d6fa50582532ee7c50582530a6fb30582530a6f8305825301cfe76d915326ebe64d915326ebe54d9153256bd54d9153024fd73d915326ebf43d9153014fe72d9153004fd72d9153014fc72d915326ebf42d915300cfe71d9153004fd71d915300cfc71d9153006be41d915326ebc41d915302cfe70d9153004fd70d915326ebc40d915326ebc64591534f5df7359153005fb7059153005f8705
  | 33 => 0x4000006800f00040110000015001c001000000a0008000000000000200020048000001800300080000000002000c00a001401000080000038000002400d000801b000000a000000e0034001000000b0008000000c0010004004004800000000000004009000400000000020004003002800e0000005001400a00000080008001000c0000000016000800d001000200040030010000000000500080020008003001400300040010018003000c004000000200000090040006000400c00000000004000002000000080090028002000401a00140010014000000c0010010008004400d000400200040090018004000400000040000008001001c00100140020000001000000000040030010002000000100380000020002000800500280000000003000c00200000030008000000400400000010004008000001100000010030001000800100080000038000000000c0000000000000100000000000001000400200180170008003000400000000010000004001800300080000000008000c003000000c0004000001c0000004005003c0010008002001400c000000000080010018002005c005005000b000800a00100010004002001c0000008000000401400140080008000000000600100040014003002c00e0010000000400000100010000009000800000100030034000001c00e001000500000070004002000001400000030018007000000000140040000000005400a0010004000000900140000008022000c00000000020008000000401c000000300380010014005000c00000040000000003002000d00140100018000004400000080000004005001000a00000000008002000000400000090024002000000200b40000008000000400000840080000000001c0020000002000c0010000001000400000000000060004002c00100640000004001001c0070040000000c005000000100100010000001000c0020000005002000200400000008002001400c00040140004002000401700280010004003001800500300010010001000000a00040000000007000c0000000006000400300240010010017000800400040040004001001c00000040030010003000000300000050000000001800100040040028004000c01c000000000000010014008000800a000c0000004007000000000400010004012000c00600040000010001000c004000000200040010000000005c0030008001000c0030010001000400300780450000000001400100000000000001003400000040030000008000c0020000007000800101cfd75d8d54024fd74d8d544f6de53d8d544eede43d8d54014fe72d8d54004fd72d8d54014fc72d8d5400cfe71d8d54004fd71d8d5400cfc71d8d5402cfe70d8d54004fd70d8d54006df6398d54005fb7058d54005f87058d54
  | 34 => 0x4000001c0040070007000400300080010010003001000100000010008002000000300340110000000003800100340050000004000c00000140000000000000c003000000700000060000003004800100000020008000001c00c002c003000000d001400000000000020001003800100100040000000000000200000000014000000000800040000004001001000000100010034003006c0020008001001c008000000300080060030000001400000000090014001002000000040010068003000000000000000014002000800800000170018007000c000002800100140030028000003801000100000010001004000000100000000001000c00000040010008000002000d000001c00140000018003005c0020024000000c00000000050014008000c00100000050004004005000200140090000012006c0050060000000400000380020010003000c001000000700000000000007003400a00100010000000000400000000020000001001c0050014006004800800140000000008000400000000070014003000800b0034000003801a00100030020001006000600000000024002000c0010040000001000600980000008005000400000280030008000000000000000040024000000c003003400100240040010000005800000280000000004000c01100000000070001000000b000c0000024000001400b000800200080000008005002400400000000000004001c00200000000054003000000000640040000003000000300140010008000004401000000070000002005c0060000001000000c00380080000003005000d002001c0010014000400900000040014000004800900080000000002000000000100040004001000000200040070000000000400100000090000006000000100680050008005000800f000001d0008006000c0000004001000c00000000020000006002000400000000034003003000a002c00200100000060000000800b0040007000c000003800100000080000001000c0010000000000800100100050004006000c00000180000000000000000d000000c0018005002c000000000000080000048005000c00d002c0000024004002c000001002f001c000001c0000008000000000100000020010000000400300200010004002001c001000c000003800000200060000004002c002003c00400000000000000005c01100000000000000002c002005c0020004002000000200040040014009000c000000c0010008007000000800040000000009001000a00000000000001000c00300240010058005003000000000000004005000400000040050008006000c0030018001002c00e00000020008006000800300b4000003000c000c0000000001000400100240040000004003000300000000004005002800f0
  | 35 => 0x300100010000004000400600040100000006000000000080030008004000c000000c00500000050024004000c0000010005000000000280070000000000c00700300000000004002c000000c001002c005004000d0000002001c00000000020000001000400b0010006001400000000000004000000000b0000003000800b00000000000001000c001000c000001400e001400200080000008013001c00000000030014004000400800200020004003000800100080070004000000000200000000014002000c00000080000000002000000000040040004003002c0010000007000c00a000000700040010018000000800b000000000000000000007000400100180030004001000c00200040000018004000000300400030014012000c001000c004000c002000000000040100010000002000000080050000008000000c0040003000000800040020008001000400c00280030020000000000000000000028000000000a00000010000001000c0080014009000800c00000050000006001800900080020030005000800600040050000000000400300000040004000002c004003c00800000010000014000000200000000004006000800200180000024001008c0080000003000000d0008001000800600000010004001000000000040000014003000400600080030024000000000000240180008004000800d000000300000080060000001c0000018000000000200000010028013000400a0010000000c0010004002000800300200060004009003000100040000008005000000c00140020024001002400100000020008000002000000000020000006001000900180050000000001000100000000008009003c0020004002003800000000030004009007c0000014000001c0030004001001c00d00040010000000000c00b002c00000000040014003001400000100000068010000c000000400100040050000000000000000500030004000000c000000800000000000014001002400400000010024001000000200140040068003001400000000020004005001000c00180070010008004000200000000000009000000800000000004003000000100180000010000000400400180020004003000000000080130000000000c0030008002003c004000000300040020008000003000b000400000100020014000000000200280000004001001c002000400000000040014017000c00a00000010060001007c00400240010000003000c0000024000000000000040030000002000c0030050002000000100300030004000005000900040020000000003c000001400d0000003000c00100080000004000000801900140000008001000400700800000004000000400a00000080014000000000300000030024004004c00100240060018
  | 36 => 0x800014a00008ab00008fc800095480006bf00003c800006e9877e83721b64a216d63b3800000005b41fc9c0c2762602a9100fa099035427f227c877000049a81ee000118a30d00008428000000073e306800000004fa0000dea0001852329a1626c800000000134aac89740f4a0a60001d84000232e0000000000000096d000007101f47cb00005450c4030984caac523aa1840eb892006006440af846ba266258935a3868cb62cf1d14252142ca2b1bba82705a242485f63079c8482686807c1000079724f86aa0000603000000027d6000105e926280a00008d800022c64491e9e03b0998476276646e1d9884014e64391bd480a90a01a21eda54b80001cb800000000000000000864998044c900c340919266ea6782a08ce61a121d6af117f4af217ca6478a54ab4a21c8ce23349c9888c7b5109a7af043a95a1c4a4071a103e1210e0d6175857904521d100001cd0430770aa7600002fc00029c84d7975a9da2412aa410dc472884a25c9c02000000016a183c6160a505200e7847800000001a309cf84fc0000000a4a0996181811e130000021a8000afe800057295eaab30148000204ead82bd41b0a744578978633813980df89ec00000004ab80d488f869001101ec79100006018000004840e00027aa00000000000000252800000023a63208000000218e92b17aa0000000000000000000000001a36000033c9f500e6000000042f02380000d825c493d41f00e3a00000002fc8000912800000020a8000290e1f900000001644154000000010f60000ec6a0b0000226800000000000000bc20000000a9b0d32661881c47c867e00000003d6235261a222800000000000000000029825c000000007d83be12da6380dcc000281a000124600020900001686049294294c0000afb2b8600029e4733225007a80009b10000b071c440001a4c1c9054a0000198000000043e8000215893c0000000000000083a00000000b3263b8000966a8b80000003002400100200040028009004800100380010008005000c004000000f0010003000001900180010008002003c01f00080000008001000c014000800000040010010009000000500240010004005005000700040000008007003400e003000000240000008000000000000380000000004000400500500010000000000c002006000200100000018000002400000000030038006000000200100000000000002c0010028000001c000007800100140190004000001c00900000030000000001800d0008012000c00000000090010009000800000040000010002001000100040020000006000400100600000000000001c000004400100000000000003000000700180010014001000000300000010008017000000b0004005001c00300000010004004000c00000040010004005000c0010018000
  | 37 => 0xd42a40800007302c246d9b103d2a65aa3c906089ba8282f783de0001e1a0002ab800000000b7091a1c30fc030e11d013780004650f122c81518015047e794000001b000073a00a2000000000000000002620000282a6e7000000000000000000ae404bea41000091880000e0000044f80004f080000000cea1c11eba00000003c280008c1000049f22d4a521cdc723993863700000001a6666781c814729944708966aed26b01318ba00000000000000000000000001180000000098a052076a9ff6aec9c34467800004692003b58000032188a00000000000000aa39ab671a03720002bd600000002d6000077892860001afa00000000000000000000000000000000ee2000000052c1ec04810000000000069a00002ec12cc00000000ad28e4b0287a67af8f6e040a3ec6a5173e7c5150e1ae0ff85cba70caa922bc9b8a9cc000231a8db149817792d02938de659a25360000000000103a00000000000d4472ca4006ca8000256a39a2e68db832d1bfca17944810017e0aa211227b29de077ea60e596000000000007548a6a3bb80000ca800000017927550000037835a81c80006f91c9200000004cd939c0000e460000000000241a46720240340c2c00024bc99980003e4999222504ba5b117f0238a46c04e8ad40778958936a96287c067c8cb000000009060b60000000282e0001aac4b9245e6b48370000291a0000000ace23640001c1a0689474976157e6f308ac076800000014e8000204683d01d80a9040601a0b620001af07c6a63800d0b5c733a1320000000515800000003e657c2a8c51f270450d29dcaa6800064997d21c72bd22d500000002be40001dba000112a0000000a1987320e4951058014ec8259ea800000004100290370904a675a40243b8000000000066500000001b18000000045299bc00028fe7259d4600009dc257000037a11ea4668e265b0993c061877878ba9ea000272e7c780001e227788a6098c1b784aaad690466d909ca53d1e423328f08362a0fe9d214a02830000000278007f00006cb246a0000b0e00010d8000000002e000079796648eb8c0c8761b58253150ca8d0ea66f680007e112c41981c522c68000b008a3467600e2000000000012e8a8a000093f82aa769921e7aa8c14b050d462ef9b7c57d994caef8b1ea9709608658774af2a3081b80c227f49d229de854c1be84ac89582741351dca5cc26248d597825de141a6b3a4869dc8000ad1085259c0000000000095c00000000d8e422a3746af813869c0a567d08aae853213839b09fe4d382186539dd4b03a28a7f1a52c72e80003e8a99200000004ad0aa62dc86fe4fd800094325d65a91d2c6d30268140806e44600000091f9600025840000c4667f8420000087e00000007a2800044c0018535243200025c48ef08162ee873600004047a3
  | 38 => 0x5aac825a101e77c92242f5113c91d8f0478d052a7c497e49d729643e680005dca7be7019c3a000000058780002238000000159400017cc000275400000007a200005a61d2000029060001b0a6dd80006f400006ab80000001746000000000029f0000000000000003fc08d203080007a5017a82192be3f0a8c641a1ce011c8000000000000000000000a3000000002ad00003040b16321000011680000001e28ae608f001383324c18000947a07a0000d1c0000450000000000000000001c649730000000000000000000000000000261eae7800087eaa4a60f8f8a0a107ae23f869c000000020d80008502944000000096a00001428dfa2df297050a0000ab3878c98980000ee21ce92f800000018600002ae0aa780000000db0000000000000000000000302075e85794a600024fa37e0a18317096a34423006dd25a261c8f42000155600003c2556800000010765e00b9831680004568f706d11b3a9fd07140ce856a000110882003a4ad200009ff0000a9080000ec264a000201800000009d38ae60000000286800000012bc52180008c3037a70899aa9bfaa2a0c29840000000000000f09158000ab519340001dbe1718000000000074203205a01d4e53c25d0841863e000000035ba62e2ba0000000244e6ad1f0a1f98d529bb813268e84e442f92fa4db8000000100012808fa9768000000214e56d80000000c3c000000050791a42a680001d60000047000000000002cc00008c60854a87000062f16520001a500a70000000000059b1ec25cd0000000028604a00000002210000152c208912ea658be012113861790000085000000003d60000698865092200020c6385800057d1042001800082880000002b520000000210063a00000006b2139272600001160c78000000091e08ae1c186ac00006f68d7101493208f402980000aea1c20001eac0a0849a146219c981a84e000000024b80007f103863c01a5a00006d49b825c0000000090781d20002abc0000fa61118000069883259e9eae0000d20a7d00000e11fbe04980000d20bae5ab9fb2000000060c0438a131fb459325d28f5192c9870f8839414aa3921f249be850c8ccaa4e0fa0a909661718499a1ca87a190c3f78e3c76d080687f28464c9a1be19785ee31e85da96b874c60d09300000000a04000039f0000a740c60a4b24640b4939600000f248d06c8762959e0002a22000000000000000000aa297b9bf0000023e8020be28491f86274052e7de07465f603a22f105d809224ee88baaa600027e88bd000000009d6a7600000a309c6482810c00005bea05000076b80005998000000000000000008a385986c9000000020922050000a602826a2680000af9fd60000a6e01d825e00000007ca000078600008c38000488a5fa86188a600029982fe96884eb28a495f80007a5800
  | 39 => 0x612980005c28cb8000015aa0d2b2c235296a0ea295a75f8000042800000020283350dce00024f64c116c00000e14afe00000002b942f187107e8800206ea4a65090000ab098d0a9a97003499d920001cca183271a8a4800081f8c769b28a1475d1fd4000000000019be1f4a9108d30000a4880009609eb27c095c45bc800000000003ed800065799d4706089e740a8969bcaa7c8ac000000000005b6a1183fd9a9200006e86c20000000000082b000055b9588000000000028ec84b9bfa138a9a60001eb48fd82c64cf1cc02f30000a36a78ea95a326868949a9e51f46a3f00009e48000a071bbc398a81e6141b4a8f490709788000000288662119ce63d89b80000000aa82252995986c75021ba4ae0bd800010da14900009900d180001eb800008c428e0a80000108638719e4609060200014ea671a18c000255a7e200009148b0a000158c00428ce73d00000cf8a2e7bd0c0a000000057b86e6522944473421b0831261254c8e7273c000000016d43b52bce6638dfe58700daa5a0000198a7dc623878632728361c79c5e21e88b02551cfc26c80bcae69fd82ed0000000000072e0000000260400000002d291da6309f3c6a00a7a44292ec4730f0c56f28e83a880003f290ba00000000001a9802187c40001344000082c00027c69a307306da1fdc63e93fc1e29a627fb0a1c8cc037c88b0d4808a8cc20001c10871a9c080ea93a36d90c830808606d209144e300000141a8c06f800000000004fc0000000000061091044560130000222600028aa1928000000253a68a0000918000042b93a80000c2800016ec00024aa9d4815c86d21e07280000000000000000009c5800010f0000a99800074a800060700000eb9e6827480009a1000004b000000000000001bf20001d584c520e6102a0f64c7035c47d000092c0a9c16705b006a08766e8a92a30c05ba0f39c6608c000031a000077380be310859223d80000001f2e000000082f800000017b86860000000095600006a43a1969ca1a8f94144926800002b247da66e76180000001d6a00000009460000000231200000000000000000000047e24d20000f029c784f6000000000000000000000118924c024000000000000000872000000035e80007138000000000000028bc000133037b22da0000f3a4cba8f820fa6360000c6c00024040ff800003f80004b200000001bc838b00008c8800000000000000000000247a189000000018362ea000074c00007e685f0000121a00000000000000463000003600000001a528239642000009a72b00007d10000750a930039000000024ae8ba800089398047d909867d400000000da688c80000000000ac90000803143c4d585f450ba3e622a120e13a286252b1d0e952031c35702086e220703f90fd49e99558a08116a5f20bdca70948e6ce06828f
  | 40 => 0xa000070f9f94668115c00007b488d1cb03e795ec9f003787a1a742919958a1b629bc74f800058619c4000000079d95747988f1c93d0000897800090900000000000580a36a7c000000000f768fa98c0a82800086b17160001b624a1079a1fb98f400000000cb8b605f8a3be00b92ca00015cc603a3ee0000000ab18b9e000000092e9766acf00000001ece8b800b41270000000256e00000000000000000000005e0424000217426492968208000a3b972495d800067a2936a64265467986ec2bbaab49ab10b44b8989610c99a20671caa01e1d2e9d580f4a78a32a69b14940002044862224880d0e84136855635d9918000048272fa7583ac1454676876200011824659cee12e00005bf9aaa1a59dda0001abc33d0a7804429b01a393404dd8c6a4d41d444e000006bca2ce1d69dfe79e8000065000043c1c5400029d4ad891145e320200000ac60000000731800000028ba00016b8000268e99208f875805f802595a234d80d2000299ea9420029f98000240a2a20ea9aa2a1b1f4098426e4405990a40223b461291ec01609de4d216ce4220ed88f90000a5c99ca8330b061f2a8f69af24ea052937e6589732adc9b02a5b0728237000023a15fa0bc800000005524aa036668f800000008c8000000026986fc000070a000000000000006bd06f045912120a8000000000000000ea458fa4680000ffa91d1ada00000008be0ed235f23a40f40796ab6800000015b09ae20ec00012a42bc9f7200015620001b8000002544852a8244195667fa000000000009162ad082e2212064a38a99c806654c1c8a000242c0000d3e0450084a3818143bc1dc65c380b09c700008b901b24bc0000000018a00000000b519a4000165673507b000012f40002168812a6ea8a790d20e4287800009f49f4800000000c4ac799c016ca46ea8b12a20001faa0002b2e9c928640002a46aaa000094d0d867dea12c00000000000e580000812228800000000000000000000000019e1e52000053cade80002b3a6f60fe00000000224000160800020ba77d0000a6ba39436b8098a9300000000f267fb80000000e4c0000000000000049e80008562808000254200000007fc02ae3e5800002b10800000000608929e00000008710000a96a414000000045f9e54175000000011407219b0067b96cc91faaee000000095e800000012b02e497dc1c3975e9798afa94a29f676800000001e480000e206c50b8200028f09b5a0ce7dc00009362b88a6f803a9540ade00017682b5a6460000de23cc934a8cf8cc641318ae28880002d5814c81a04a84cb167e2a497ea0ee887893c80000000c4c0001ce656d2238054223c4d804ec48180000001e1200016a68300b5e0001b7871080002a58fe003a91c498c80000002bf632609ae229287e45b8e6045b0b747cf97da84da6d224a05
  | 41 => 0x9ad8000000000051e0df65a1000068829b42b600008b7000026689e60002b760002594770053428e8000acfa0740001b6075e0b00316239201a800042613b21c014da4620000000279828928de8d880003b9000060b1ddea639a6e31115700000c1c7ce172a4550000504229632c1aca181090e000000027a80008e10082000000000000008ec85361ea000074294fc4e3800061500005f99c62570a442217264e65f0fd62a3a77e00023ca60580001ee299a0099f320d013de24a9892557a4dc0f0163220211a6000000028a015e00010ca29c11d400000006120000000000000027b2000000066b9c7c0000000a260000497000029da422000218a87d2b0497f9682aaa851e5af117c2e407fa788145e7a909f89a690ea20b80008950000000000098580000000d8cad28dd871ea27e00009764e78bd07889462a5587a034f283c6778cb23cb80000001ea652489522d685ac0001df8a001542a0c8eae53d86769fe00000c580002e000000000898ae3800054a903c0000b100001da48ae00008ada42800000009f624ec0000000537800098e800000011b200000009e680007ce80007ee9bc03500a882200b706f3902066304e006f18269019a5813624b62d190548d027fa0ef280c6329b7006402700000c364991a3463b0000143800000000003418820a691e3e0ec82000a297d02ff97be8df237241e140c63e160c108a1485259a9c79fa51a09f00000000000979245c578142a00000003d70a867ffa8c800004c823412ac5ce0fa07a813129b21f345ceac0c51082120001f9c47927fe5bd000053700000001d885db9c249f8000084203d80001c263672746000000000000002fd800022d22fa148a7500000000570000035b057c70480000000000000167c12000009b68000239881a74e8de000000000001b928d780000002848500a1fe189928c6d71e300000000000252e29d0c4a9e325461f59d0065d96065aa9afe63200007b60e927e98222a5d8ea83ee00006ea189470212760000000a8105e65080fb000016300002af20000de479380000000000000034c42080001cf00003139f90000077078c8f2438ba350a3880002c20d12000000000029ee1611de80000b8e0f700008eb209800000004fe000032ba9ce7daa6ba7479fe20000000000106a0000000000000000023d80001210000055829c80006d39c6a8b62afc5059d94000273a21b800024f800000000000000000000000000006c40a6800000000000000000429a978000000000000009530824195a16a1919c2aa2d8000000267c8b31ed20000f2271301747d780000000c24ae89a2238428ea2d213be2fd00003f22b025dd80006508a2c000000064100000000000438000a4f3000009e80004948c720238000000000067d8afe212000000000004de000021699786
  | 42 => 0x82b8f8676c0c7c75b800000020360000000000000000000000000000000000000003fc00005fc3ed2a620e095c8000000089c89247631e2400000000000eb22898350000194459b80000000000998144c402a7085740e6e59d90d40002a8693990d69cc27b6afd0000776177411b9c6085991fc45182caa8baaf07b211de00000000002a58000000000000005ab00003b98f443ca124417304b2747153e58a80006f5a51c00000003cd80001a880008f82be80000000728ac0848c800081025a4087195091c00002b800006008000673000000000000000000000000000010e86c300005b40000528969676e02e202508c20001a3c6a383f20db8b9c92a00000000afc65a000000006f80000f6290d000000000000000000738969028f25f610bab1800000005459a6407c911670d9fc036802e6000280667f2b227b900009721ade0001bb80ed113a0000000000000000000000000000000265863c81400000000000000000000006fda74053ba40c9d914500000000af8a30269818e47b9828e2d90ed01e08cfa8549b6e00c036004f807241682a89e28266a8c24e83770000538a56a6b3041800000001fc0000000233c72300009c4a2aa00016de3b00ce2a3d1bb400020ca8821fe485c28be41f00008678a4449d211636492fc00013a2a528000aad80003528aa8880a222ab1156883a8b524c086684f292263d48426a108000145897a000015600021200001f9275c00005a3000000021a441592423bd93ea000017600029ba3f124e20001a56000000074ca900000189c00021e6a7c9dfc000061e28da95e0001354000000000007c200013660001cf65b900009a0a64c81aa5667b8a3d000000003f3000000022de61f9a1e90f872a64214080000bb20001d4c000182e949aa7a760258a000036c509800000020c25d8a8a20000000a312694000000096f8ce4000000084f0a100000000000061c6c592500000f34a1a03561128da49429d6600001d633f9df6135a51400018ba5468062000213a9560aba5de8da20fe8000283961a00014763fb0000324800096d825c0001270100a48e0000672982030800012d60000e6a41f862e6d99f2a43f0000000007c11c0000000081862694463eb81e637b9f8a00014fe958a39e7d480009e8296e0001ffa9c50c948542146a8318201a280003de0000000236e4de923000027e40000c500000000000277c69700007f69f5c0001d248a400ce85b00002eb13da0000f18a622b5400012e690ba984a50180a1d98980645a130000000041e9b22000167807e252495780003a21b126cf29e876d91287c5a7ea21613346a78000a47a2ca00008be0002a720000000add09e2000055c224803c0001c9a98f856e5611272000184665b81b68bb97a6000138a8e719f0000000e00001c00000dc025f0
  | 43 => 0x1efe0002c1a4a9a812000115e00011442ea929a62d848e11a00004da8180000230a4d49ec68f7a5ac000000000002f603f000000006362e500e00001d0c1c891ce2da0c861dc8eec2cb2244027122c25411fe26097ce692aae213b81a05ea28a08b980000001b263950000a0f9edc59d010600001722c902065e789c20000aa0892a78461ea91c2620d680000c7e8f09c806079aa475e897e2c70000adb1522af6171c89a000073e855a34b83646df800049e13c0000121691c80005cf00008bfa66226283f641713fe29492eea560000a201b960c899963279c56804a45097d189800009a24588f460001d12000019a9f689c82ba9e5a0bc173649fa1563d69e1c0000000000286e59c866a8bf22d04068b424f705c413c10a444483c8267ab404a28b3614421bc837a57418383da5db25f0559083898a8f06a309c3c80785d61ab8000000185e00000006f889e845400006722c104b7031e2b3036a5ae89009a5846c6f72280866800084402b664b8456ae097b25519f5846d08bc05b2006907000000006b24baa79e5eb94d86cf936c6481aa600000007e3800000000001ce800000000004a022c8000000000000007eb2b7e8e387aa0a0000000000006e41e820002b8c0000000000156a648a5967658000634a69000006945d31fe09558e0c05ba8160000628000000010f80000d4800000014f86fa13ba758abda00027d00000c6e4f5800094a831055e0f480000000110000069e07e07c988000001b1ca861efa2daaa1e98005e800023144920000000000000000009698b9630080005dc23ba42d8dc8aaf90c22f48ebc1469dc8a272bf2560a60c0c619720000d580001fbc8221a0a83f146000000001bb8000440000000002ec0001cf89038a0436b00009ed188c000000030a80006b602de00000009772692211a180832282235c00000000000ac700000000000505000000000000001b860000000000000029800000000000000231c000000075280006890000000000000021a068180000000a94000039c00024c200000000001b40b00000000000000002a3c9ce00000e3000056183c45b19c303b3288887b000000002fa4d080c03caa54a84a000000000007a300000002b96000000094c800023b97b400006120002a0eaea137c82290260fd02ea9ec0a2a8dd800041401a497780cc67a9f184f107ea98f0d969c1884c9dc0ba6159007e3f999fa73a8334576804294480006a419660001018a11137449288ce1151044124022029300000000000228000015c000070b000038108baac3902eac980006e080009d89c7082817d4a1f20f84f40ff200004cc3e000001d203004558000a2d0f1a9da80000001fb0319800038489be00006a8000000075f000000007be000000039485ca0000dda00027f6ab58000548000031d00004ad9a88
  | 44 => 0x2fb1d36afaa0524fe86d00000eea3de876466109f23ef16b42e1995254d1c1c00016ca18a8000000000027d9de6000040800022947f080005d38000000000051b8000000000000000000001f4e0000cf852423ce000000000021d407704b02c087bc07428fa0001bca6b9834400009a883907dc35a85740131440470056c2ac8d008aea10c0002a3a7828000145168a305800000028a600011860001b06095a9083f701b40e59b9e45e9bec589a6de9ab9c9c10d8bee1c6800034d01faa1c91c60000d4e24e239800000000000b7e9278000000000052d8000000148466a0eda5ba8000000000056380000fc243011d005e00000003ea00000000000a80000099b0d940b40cc0a76806002014fa0000f6a059900420a93b0a74875200007cc0000000a82000070ca6a6ab280006faa2a87ed8ffc516a5ba7cd9ad68ff8000000168e2f58000816a73c18d1c9078e200a13faa84000157a9d811b00001202a841dd28aca9c60c503be8e5826202ea50405a111e76b08c004496469ad03ea98c1024000000058e00001d019740001e3aabd057e69aa0fa90411480001b360000e303bc9b46000000033100005c105608448a3e00000000002a9862000003838000ad089e4a22abf08348b4e65596120280abc61b8bfca0e820a76722188130c707029f7c6acaaf800018d60a99d82367800000017f200007f400010b058e86ea00000000000000a4e19e037c95986ae8000000289411800009350000000150a00000007f292b200014d040d001c0002ae60000c54685a914000000038f89787fe008a3258000000000038080008fd2b00783aa5253113e639f800000000004e5256c90820265d40572a6d8a64aee8eaa9bb25e070b80001050000000298c0000af407c00000001c9e0000000000032c88590cc69795d4882909c9a921aa000193e2af9e6e00005d200000005850f980001a7e06300004fba7340000000000000000000000001e1000000001619506000130800029fa000287420f172c0000000789856879c205608687b63d7a70a20a00002d9825055d92de10488fc00000007a71466248106e2ca000000000005e380000000000ac312fea35800035c80006eca7103d40e42000144a7859d4800018566872bd00000000000058aa7e1ab0964a6a80000000a99030e15780dc93180004e100006fba8500001346a448a326cd277405480000899a966850d2a6ef9412617157c9a728180000546027800081200006f10000000210277b29b272a0e9400000000c1929c9a200000002a1668680001690c803fa000050100006da8658734901285c8780493800083815fe2cf891e3c392f2232a23651c16d2929251640890fe2d41624acda966046139a000084e0000000846a728000000000025c20000d1e5f100003fd10328c7a93e27698ea680
  | 45 => 0x12916000000003281468f715808c90000000285200000d6628981200017ee9cd80005fe1af800000005550fc69e097ac00026e6000177e000224ca42a72029602e4000000057593a604110c405fa57219b00000e607082651cfe00002962aa98be000000046a8000938193a6c6a264a8e0184951005a3740ae20001e4632a80000000d667bb89ac6c39de471d19248ed80004f48e08000194a190a3a86b40fd205c16c832f109447e8a9e71217b67db1bac5c7abb66d4026a1d417c652e1d5e57a2918000177c2179c724b388cc15395a41190d0418c8fba21080005658b6c000297a12d16b22432a9c9a010f421880002508eb41e707544aa9fe6071a59c0000e320e200008f000009b08000000059000010b8ada83a6af98ebe0000a120000d626e900003b724c44fa1d0400023069c0000000024e47d99dee472068640a0cf040a82920000000000000094000008819c7e000000000000000000000a4980004161bde32298de040151e689a4c0000000000007e800000000001ffc1dba72c98b19368191b549860ffe00000000001ae8683284054e956c00000007da299c5ec0000ad7816a6661d3c0af057a3612a74af095008a991ba7f20a06adb85d05f0280291100004ed0e745358620110a346382874e00002c00000000873000098508ec8901d063bd159a2ef286000025fc24e98da0000cbe3280000a160a8400000005139f0e59a80006e100008001bc600008447b419f200027c426aa9504ed800000000008198dc6a2480001fe00007732aae15982b80000d14a27994685e800000018880739bae78da8827fa9328657234e75a00000000000ae113a485095ae00003e040f9364381992a3ab00006fe1ae476c8f2c66e126253481200001a02660ac18000061a4e20cba15021de44680009420000a240b7834a088836f0efc2de8ec21f20912a5d21ae65914c200023b845d9438a7785a68d9841099d93bc8880f5400000000001efc00019f4754000000028700000a0200000003979c0400000009501cc4000248200000000000a623ce19dc4a810ac14e2154000036863a00f80000a4000018b02710000530000000020140002af60dd2a4833485ea0000e647d8800000792401c58adc7d582466ca21d21aa8020554000081ba76c5ff800008b112c51f84f251a114c28584bc87018d88fea6d09a6000000021e448d80480000000495292e16d800038d8d980000a1e96a81086e280000001e088d100009bc2b6600000008dc1a7a4610f1e00017985190c8c6bb0ac0000021eaccaae80000000000211498880005698a080fb97fa5ca0ac85c1800069d248c90600004fb04ce9ef0ee800005b800015080000e2a5e6800039c06c68e085c8393a3868de0e808c81290638995aa6b121caf70000185000012300000000cce000186a000000
  | 46 => 0xa28bd9970730800000005440960a5a000184e0000a0a000000000020d032421e2000080a7e30000000000000000009fc800000029fc00000003f685e00b3235a8f180000e289ba000059e87d8000000000076780000000000000000079916be47c1a5400000001f3aa1a430270e000000017720d824290ce5921dc43eca5ca9481e2a9d7800026f1b2e61900006621f3042390960001fde8389e662b480004018004a30189065ea6704c4179661c154c00025e818c1d381af91900589a9a876812e0000000806800017c80007c314b2000000016580006baabc60f88000703800000000000000000000000000025a09168000000000000023420001d9082300002b6800040b20d4000086855c80002e3050891f000024b059a5ff00000002590708227682904941b588aa245aa400002aec4f904c42f69e6c05900000001b420002b0a000089000013c81f520f000000000000000000000009b000000000000000a4a024800034695a800000006e500001ae808c596a12a814242a00016ee0001e605e4000000026cc0001b9a6d580009b624b80000000abfa560adf27c210b0e9e2e8a25848a26a000004760000000000182a804000000000005321a46781000019c0cde2ac10a82c980002fa9ef80001eec3f3a3da0b3800000013d80002b30a80800026d988200000001ff293c2368b2e0000cfc0000244000000043189f035821646629cbc000000000001e20001bd255801ac5a8295c42409444ae86da56f90f2000120867480000000d24239000069214ce0030000a54a2d21e6000003b9d9a1df00009f8a74a00013aa00000009751cd68478dba707a5644c8265e34c0cd648a9a04292288e00003260ca0ec80eb055479a9f9ea15181000000523998000a39a8a873b002200009642ce2b34000141c45e0000b01000000003cc160045c56480002a918f0000163661d0000000080279286bc54f06740d780003e30b44a89202e0001bfe00000003729238000000000021045798f4c4e80a7c0001c280002baa45814e086a1ee091182788ce88d6000001a10a8e8a61d82ac66702c897198c455493165d48bc0902800042a800000010a2000046a00011dc1c606f47e911a2849908c40080008f3000066d90489408ad072527189b0019e00007f637f12940001536ac405042378000ad40d64ab7800000022421a7a05cad30efa000160400000000000c5e4f8a6f800d8720221ac064cc800008d0000000180000000000001d720cc09b48a68ae44ca89a489e80000001526000000056a97223c5a17838a087c9f39eea8cdabae3e4143a6f610305f7ab5c716044425016a882126fc2380ab85318f60333000000000003a09ef05b880005c2243c6d7a588a8480004c3ac1233b0810000243606c0aec02ba3e21a8160e5d70000000227499d0fd8a7
  | 47 => 0x9344598e9a6401a869e1a28411f152436a1d346b0886c23a800044d27f052722a000005aa48b800056b0b409338028000000003a00005e9249a00005ce69000000002510000000098d1bc200000005448000000255c1de80007558000360226092427ca152000000000005bd80000002946a9f8790355918e963272a00024080fb20bc000081e0000f725ef0e1e9d30b8a000112604584ae7499ef6000000049823582670000000138200022ae300000081f034600000002ce800000000000000000000161087a800012783e448f9baa10d09ee7390fbe241000077aaa78ac5a57ca0c28d499a937017e9df01ee9a3299f80001f795d87571a8435416e034306549eb02e0643aa8a27026861a4a6f485f1c465e51f206bda9609f30dd29258000000000000027ec7dd143e9b392c089c14a81ff8d5a4ce100e1f89d107db89ce00011727220000a0e00a800017542229142000206c8d2abb011e9b6c00011ee00016fc2f9800036c8000a4d2a1400f92d8478800000000007ac29aa9a793f282daab020d1d765fd910ea49287a96f14ba1400000000000000000002140000a12a9a2375800038920782750000000000057c9bf497c9064000000054a00003928910121a522000053a000187c33220b43db00000000a429228000000000031924166e38702a23020c4c6814e3cc220c5938ca47e8000094f800005624de0001e983eb0000000191c0000bc8000000022da61a04f17143f4002c00000001ad154e03180aa808a5b24340000541109eaca925a9c0800034eaa9200c83380d2abbc0001e9a0000df400001d4000000080717480000000081000000000005278c562c1038e4f82190551154a00006508df91bc1f68d380930ba47d69e7caf794e4793133a000052619307ec3a422f041d0d7439daafa4be27c8928965033d805c194a2860001174000000000011e606380003cf29d63288d90af81ff28ca00009dd80000a8800000000000000000825209e8ff179c4b48dd41921be01b3226a7a127b800000000000000000235485802405ba22880001f0889680001588000000000000000000002b20913206297b00000000870641800058f250600014065ad930a574a0300a20000000297e225aa6e5a884280c106caa7fa2825be16dc45c0e8c4c002b05c80616597aa0690e94302fe140a8ad10383b7a0b011209462a6027e585971a00007843779dd000000000cd9c7863180006d48000011800000000001a6800096c000026394880000e8e56e80a457e000000023b00000000000000058d000000000009600c480e51aa05471654705029e69f11d27a4983a9e704d24da058e967876a25b8000000000000025b800000002f28342a53800000000000001ddc301aa266b8a28c00000000000000019000085680009cc800039a00000001d
  | 48 => 0x18200000000000b1498280005e28b220be000008f02940000f4e4832a6089e22c28fa17023148000072989e86e000000019a630380003b8000000027ae3958ac4219000042100008ba1fcc0000000000078e7831b3035791526dea85a6e61436106906c4a6000029f9ac471d8eba12581c251e98a034882602ed8b4c28815b2a8d86e21dd995409d81ae36fa6aa3b28aca4882aba90e000000016d865fa93200020766a080003910000ae011a800029e609695dc0001cde000000000000000001862ae983c658b0bb80000f9c88a80142db80004681ad400000000001e3c2cd07609949f821070f144c612c60000000000000051a800051c800008e93f400000009329538000000081080003e080007b7800058b8000763865a0001ca6ae4925e00000000001fd00000000670ab0819b800051b0000000000000002d669da246973a20016f00880000000000000000000000b680005d100003370000aca00000000b185da824a8af831aae90000000205830494a42c31548a0381446dc87c6083981a17f88b8000000030e82c400000000001358aba94000000000000000000000001b700000dd80006cc8b7644d888211e072c8e4216e4148d880002b0651612f600025ea5f086e40000000716800000014ca46b00000ba000000000000000000a8c80000000000000000000000009e580001d0a1d0201000058a00008611948000000000006180001a2c52f800000006081608a5e2319036aff930c70e28d89941f4a396986600000007b580000001e9061e00003d9000026c28dc69080004c88000736000065aa644705910272d9a2e00007d078b0532242169400000006d6a50e000000085101224d724cc5fb1a0e82caadc10318189150000000162000000000001062000026e000000000000004d8a586000223a0002a8008c8000000000086c898464c0e188b11dbcadc1914000199a4f380000000000ad3800033a00007b3079430f96e6b0580003a59a087d320d63fa904e44800b60ed80f600010ec928000018f0cf291001e87e61cda30c80009e90000000080e00000000000000000236800027a80002ad88f1007a00000007ba096c000000073226be0000000803a20e7879e400002a685c40faa1058ab649600001db00700c923a000000009ba16f00000000000044c000000000020548e000000000000000000000023100000cda00023883bf9cf213715fc71b0b2a00021f8000083aae8160a1a98000000000000000000000926000248483c9c6e79c800000019b000001fe000285686629a82970fa400019906a2a6c6342145c2198488000123c8529ae068a8000633000000018a60002a5e99705427568d2c343a68aa6180002bd98fc5230594571800017b07a40841902000000000010e6a21000032a18ce000094e000000053c880c0
  | 49 => 0x13a8d0a273000000004d00000242000125602c800000000000001d18646a9542ab000000009fa3a71cb4191000009380002b09960881174a000000046611be32b21a6780a176503975633b8eb600020daa60864059828240c080009e219b20bb862c44419ec00000004198f4086097d6080800062d000051484c29ac9c403711f1067e1ba008d8530291a488000052c094800000019d0000111c0e680001d728ca000203800003ca59700400000000000000080101e000000005e82bac0001958124848a00000000d3969e557000079d23f84d31ea238e08f2a8fa6d4306000071400007d82032043876863fa8d253300005c988b274a24b429b0c8e1e7970c268058887b8000221082606e22d62998c041e4901000000001c4a1c8629236084881960001fb85e21324aab0000000000050c800000000000000000000000000000001700000000126e0000b840000000000000000000004b5000000000000001e06000000000006b60002426a729928ac68be852082fe00022e24e40bf014fa03e5be84f848e800080b0228000021600000000002a7052f00004430000119a4920000000927095e5d08756000000012618aaa628000000000038d11d69c8a29c000000000022ec0002aa26ec00004b090b250620ee19392e01d2ab64508abc02c48c8819900001eb0f567fd0f3e89b00005889d1a3b102f49ee80086f99d16000169aaff000000000006b18000000000062b26a29b70d7e170937295509369538000a880e7a0c4a57855000000001cae00000000002ac013995026ae05769f79072a5f00000002a540001784000000076a000062a0bce4eb9932129267aa4800004f18ea01179adc0001912000000000015a0355221e3d98188616ab560000f6800000006b01a7200019ac45a030c000004a8058000000000094e000036d15900001c5c29a2316128800035304b600000162e2067a0000000a2b800000000001999d6c0001c00a342b7852d18e61ac000093c1ec4000000000023482471e1400024d6000000057380000000000000000000000000001b0400000007c8800001d129262e0cd80582a945e893b83a600002a300000000000000000034592821b0072600000000000000113800000000001829e5647a000036a9aee898ab3a72900000000000a2c8f7c1b380000002668000294c9e400007dd99b457783625fa0e223e3a87679e09903c40000000000000000007bc80000002230602000000000008850c9a000000000000007590000437988685f812a598822e00000000000000a7800008bc80000000000000000015e266400024940000e0081796928fc000000009e01eca2c000000000000d78000000000000000000056000285c000000031880008e322a4a6e05a05ac0000afb800000018321078622aa59f7e37c0
  | 50 => 0x2720001bb665b000000023c816325f800028049120154ad600000000000796221a693800024c8000280203c0002b8a00e159c9340af0000000006aa25c68e1fae6910000000000000001e4ada000000018b256e0000a3300008470000611184ca431c82000000044e09187e0213418e0000780128eaee05e28891f548de8874453a75aab92b463f880002a284f4678889c43e0e5c3dd1f1c84f87a20001b1e04d868c5d921f27f38000000000096390e2334002a1b4abcc93f1a12990a3a21bc800000000006350be40e7800020c2b9c00003d40000fee366983800000006e31e8000012183df8000050800000000001ce126c77580000000000000017c30b83a016b933e5929fa85d000007c1800000000000001eb69db9940ac4865c92c8e4052b81f694f28b09fb80005d829ec9e8a15c00029a000000005eea0605901f4882a931e
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8f4865c653440018eecab8ca6880021fe157654d100045fc22eca9a20038bc845d953440011df04bb2a68800a3b2097654d100047dc02eca9a2000c76511d953440290fd0fb2aa6880021fe157690d100243e42aed21a20058f4865c643440090fd0bbb286880021f6177650d100043fc2aeca1a200487c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a20028ec825d943440291790eb228688052a720d6450d1023556412c8a1a2055cb87059143440031f50db8286880031e1977050d100045fc22e7b1220038bc845cf62440b50f90dbaac4880021fa1f65589100061e3a6cab12200087e871956244001878e832ac4880030fd9774589100061e32ee8b122000c5f65dcd62440018b8cbb9ac48800317d9473589100062e328e6b122000ccc621cd62440090fd0fbaac48800e2fa1f74589100061fbaee8b122000c3c75dd1624400187eea3a2c4880030f1d474589100a46f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000cac74dc96244001998e7b92c4880031d1d771589100066a39ee2b12200087f855d9524400117f08bb2a48800e2f21176549100046fc1aeca9220148dc835d952440011ef02bb2a4880121f21476549100143f43ecaa92200487e85dd942440010fb0bbb284880021fe1576509100243e42aeca1220008bf845d942440011bf06bb284880523720d765091000477c12eca1220028bc87591424400153906b22848800aab209645091002c7b436e2a122000c7465dc542440010ff0abb664880121f21576cc9100061f3a6cb9922000c3f655d33244001878caba664880032b9d362cc91002c7a432e39922000c74655c732440090fd0bbb264880021f617764c9100043fc2aec992200487c855d9324400117f08bb2648800e2f211764c9100046fc1aec99220008ef825d932440011ef02bb2648800e2fa10764c9100045ec20ec992205ac7476d9551440032ed0f29aa2880131d1da5354510006abb9ca6a8a2000a748654951440098e8eca92a28816b5cdd4705451002c7a432ea98a205ac7476d9531440b18e8ec32a628800395d94634c5100056a4326498a202cc7471d9550440018eecbb8aa0880165d21d515411002d3a432a2a822005b708054550440af0fd0dbaa60880021fa1f654c1101643e43eca9822000c3c74d95304400187ecbba260880030f197744c1100064e3a6c69822000c9c7418d3044001878e9b2a40880030fd9774481100061e32ee89022000cac74d89204400b1ed0db8a40880031d19771481101663c3b6ca9022000e6862d9520440af8f0ec32a408809f2e1db74481102fe5c3b0e89022000ae8864c920440013e10e98a4088003f04c93148110
  | 1 => 0x8e5b2280900166b21d425012002d5643284a024005ba8805094048001878c9baa609017e2fa1b744c1200045f43ec898240278bc87d91304800187eebb2260900030f1d7644c1200062e3aec69824000c5c7518d304800b17d0faa2c9080030fdd7545921002d5d406a8b24200487e87dd563840bb8ee21baac7081771d4437558e102ec3fc2aeca9c200587c8759553840010ff0abb287080121f2157650e1002c7c402eca1c20058bc87591438402953906b2287080172e1c16450e1002c7743ea4b142000c6f75d4962840050fb0bbb2a5080162f21d6450a1002c7643ac4a14200087f855db32840090f90abb665080021fe15764ca100243e42aec99420058ec87589328400187ae92a6ca880028fa1062d95100051ec20c5b2a2000c3d741d3654400147d0839eca880028f61073d95100062eb98e7b2a205aa75811cf654400147d08396ca880028f61072d95102d53d400e5b2a202ca79801cb654400147d09196ca880028f61232d95100043f43865b2a200087d870cb65440590fd0f906ca880021f61f20d95100051f420c432a2000a3d8418865440010fd0fb2ac8880031b1cb65591100043f438cab222000c6c7219564440018becbb9ac8880031719773591100062fb28e6b222000c5c651cd6444001938c839ac8880031bd9772591100063632ee4b22200487e87dd564440018beebb9ac888003171d773591100062fba8e6b222000c5c751cd644400193ee839ac88805327a1073591100064fa10e6b222000c9e401cd64440019388039ac88800a3ba1f725911000637baee4b222000c6c75dc9644400199ee7b92c888003331cf725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b22200087f855d954440011bf06bb2a8880523720d765511000477c12ecaa220028ec825d954440070fd0fb2aa8880022fe1172d8d1001c5e422e5b1a2000a9e848cb63440010fd0fb2ac6880030f1d36558d1000636396cab1a200087e871956344001878e832ac6880031b1c86558d105063db80cab1a2000c3f65dd16344001878cbba2c6880031bd977258d100063632ee4b1a200487e87dd5634400717d0fba2c6880030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c688003271d37358d100147743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440019c8e5b8ac6880031e1d77058d100061f3a6ca31a2000c3e74194634400187ecaba0c6880030f1957418d100046fc3ac631a2000a9c8458c634400159904b18c6880523720d7418d100a64e41ae831a2000c9d74d0c634400153d09190c6880029760f6594d101663b38ecb29a2005
  | 2 => 0x631d91200051ec2c63b2240008be870c7644800117b0e18ec89009e2fa1f10d91200045ec3e21b2240008bd87994644800117f0eb28c890002a7e0d65191200054e41aca3224000ab781594644800156902b28c8900028fa1461191200051ec28c232240008bf845d954480011bf06bb2a8900523720d76551200047bc0aecaa240018f4815d9544800917d0fb22a890003175d753d8d200043fc2ae3b1a400487c855c763480014bd0b18ec6900022fa1f6458d200061fbaec8b1a4000c3c75d916348001968e3b22c6900022fa1c6458d200061fba8c8b1a4000c3c751916348001968e2322c6902872edc06458d200065bb26e2b1a4000cb464dc563480090fd0fbaac69000e2fa1f7458d200061fbaee8b1a4000c3c75dd1634800187eea3a2c6900030f1d47458d200062e3aee6b1a40018f687dc563480018eeebb8ac6900031d1d77158d200065bba6e2b1a4000cb474dc563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200065c3a6e0b1a4000c3e75d90634800187aebb20c6900030f9d46418d200061eba8c831a40008df8758c63480014b90ab18c690002b52056318d200a46e41aea31a4014c5c835d463480018baeba98c69000297a163118d200045fc22ed29a40038bc845da53480014bb07b2ca69000387d4f6494d2002c76432e529a4000c6f655ca534800717d09bb2a6900022f6137654d200043fc2aeca9a40008bf845d9534800717908bb2a69000237e0d7654d200047bc0aeca9a40018f4815d953480290f90eb2aa6900529720d6554d2025d3a40acaa9a40028fa86dc15348001970c9b82a69009f2b9cb6490d2002c76432e521a400087f855d943480090f90abb286900022fe117650d200047bc0aeca1a40018f4815d943480011f700bb286900032b9087650d200a45f43ec8a1a4062cac76d91424800535d0f21a849000f2b1da4350920316d5ba0e0a1240058ec865d132480c5958edb2264901832b1d8644c9200043fc2ae7b0a400487c855cf61480018eaeba8ec29018a2f21b74585200045f43ec8b0a4000c3f75d916148001878ebb22c2900022fa1c64585200061fba8c8b0a4000c3c75191614800193ec9b9ac2900032719373585200064fb20e6b0a4000c9c641cd61480019a8c239ac29000e2fa1376545200045ec26eca8a400187c8759551480014b906b2aa2900069d205655452000656326e4a8a40038bc841d9414800317d0fb22829000eab2194250520006563b284a0a40008bf845db314800717908bb662900030f19175cc5200061f3aec998a4000c3d75d933148001958c8b9662900031d9d761cc52001c5f426ec98a40008bd84dd931480090fd0a3b262900021f614764c520006663b26498a4000c6f65dc9504804f95
  | 3 => 0xaa186014a9c83591430c02959906baac418016ba201745883000717aa4a8b106014e4e53d4d620c02959906b8ac4180029ba14715883000536c28e2b106000aae841c5620c00155b0838ac418052b3a0c715883009d66c18e2b106005aea801c5620c0275d30038ac418052b3a0e515883000566c1ca2b106000e6751945620c00b5d50120ac418002ba60241588300053742c62b106000a6d858c5620c00b0f90eb2aa41800317597735483002c7643ac4a906000ccf73589520c00b1f100bb284180162f21d645083002c7643ac4a106000cb964dc1420c0019d2c5b8284180031ddd751584300063bbaceab086005af0805d5610c0295a906ba2c2180038dd5254584300a72b29ea6b086014e944350d610c0295a906b92c2180029da1472584300053ac28e4b086000ab6841c9610c00156b08392c218052b5a0c72584300956ac18e4b086005af2801c9610c0255e300392c218016bca02525843000578c04a4b086014ad683909610c0015ab07212c218002ada1232584300055ac2464b08600587c85dd9510c00b1f100bb2a2180161f21d655443002c7a43ac2a886000c7965dc1510c0019e2c3b82a2180162f213765043002c5e43ac8a086000c9d64dcd410c00b1e90eb0a821800335dcd615043002c76416ec90860058f481dd9210c00b1d90eb12421800333dcd624843002c7a43ac29086000cd773585210c0018f70bbb260180031e217764c0300065dc26ec9806000cb884dd9300c0299b4a7bb260180031eddb754c0300063dbb0ea9806000cbb76dd1300c001976ec3a260180034e1d4744c0300066dbb2a6980600587e87951658800187ee92a2cb1000e2fa1f7458e2032657906e8b1c4064cad20dd1638800117f08bb2a71000e2f2117654e2002c7c402eca9c400587c8759553880c917f08bb287100162f21d6450e2002c3e43acaa8c40058f487585518800317b09bb283100022fe1176cc62001c5e422ed98c40008bf845d9318800717908bb263100031d5c651d95200053cc04a3b2a4000c5c651cd654800717d0fba2ca9000327dd373595200064e3a6e6b2a4000c5f751cd654800193ee839aca90003271d073595200a62f428e6b2a4000c5f511cd65480018bca039aca9000317140735952000c7b43ee2b2a4000cb774dc56548001968e9b8aca9000335dcf71595200066a39ee2b2a4000c77751c5654800196ee838aca900032d1d071595200066bb98e2b2a4000cd4731c565481458f6ebb82ca900030f5d754d91200054fc1acbb224000a9c83597644800156f02b2ec890002ad20565d91200051f428c3b224000a3d85187644800187aea3aec8900028fa1473d91200051ec28e7b224062aad821cf644800147d0a38ec8900028f61471d91203155d400e3b224027ab9801c76448001c6ea328ec8900028fa1
  | 4 => 0x24c001968e3b22c4980022fa1c64589300061fba8c8b126000c3c75191624c001968e2322c4980031dd9771589300063a32ee2b126000cb764dc5624c001968c9b8ac49800e2fa1376549300045ec26eca92600287e87d95524c0090fd0bbb284980021f61776509300145f43ec8a126000c3e74d97324c07f1790cba664980030fd9574cc9300061e32ae999260008bf87d93324c03317b0fb2664980032e193704c9300043f43ecab0a6000c3c74d95614c0018d8e5b2ac2980021fa1c65585300061e3a0cab0a6000c6c72195614c00187ecbba2c2980030f19774585300045f43ec8b0a6000c3f75d91614c001878ebb22c2980032b1cb64585300045f438c8b0a6000c3f75191614c001878ea322c2980032b1c8645853000637b2ee4b0a6000c6c65dc9614c00195ec9b92c2980032b193725853001c5f426eca8a60008bd84dd9514c0030fd0fb2aa2980121fa1776505300043ec2eeca0a60018be87d91414c06d0f90cbae62980030f19175cc5300043fc3ecb98a601a87d87d97314c00187cebb2662980030f5d764cc5300063c32ee098a600487e85dd9214c0010fb0bbb2429800e2fa1376485300045ec26ec90a6000c5f65dcd504c001938c9b9aa09800317d9473541300064e320e6a826000c5c65dcd404c0018b8ca39a809800327d9073501302ee3d3b6cb982605de5b63d97304c0098f4ec32e60981932e9db64cc13001e5d3b0c99826000e3865193304c00b0fd0f2a2ca180030fdd254594300063bb8ca2b286000c3f749d1650c0294b906ba2ca180169e201745943002d3d404e4b286000a79809c9650c0294b906b92ca1805297a0e42594300052ec1c84b286000a3e848c9650c00147b09192ca1805297a0e71594300052ec1ce2b286000c77719c5650c00b4f100b8aca180169ea0241594300053cc0482b28601687e878c5650c0010fb0f18aca180021fa1c21594300043ec3842b286000a3e84085650c00147b0810aca1805297a0c21594300052ec1842b286005a7a80085650c0014f30010aca180162fa1f54590300061fbaea8b206000c3f759d5640c02953906baac818016ae20175590300a70f29ea6b206014a9e839c9640c00153b07392c818016ae201725903002d5d404a4b206000ab980949640c02b17d0f192c8180022f61e325903002d5d404e2b206000ab9809c5640c02953906b8ac818052a7a0e51590300054ec1ca2b206000e3751945640c00147d0b18ac8180028f61631590300045f43842b2060008bd87085640c00147d0a10ac8180028f61421590300a54f41842b206000a9d83085640c00b5750010ac818002ae60021590300a46e41aecaa060058f8805d9540c00b0f90eb2aa8180162f21d64550300062eb2ee6aa06000c9d64dcd540c0018f2cbb82a8180032e59370550300a70e21ac
  | 5 => 0x800a3b209765473000c3f43ecaa8e60018bc8759141cc029938e6b2281980172e1c16450e3001c5f43ee8b14600287d85dd9528c00117f08bb2a51800e2f2117654a300047bc0aeca9460018f4815d9528c0c517f08bb285180162f21d6450a3002c7643ac4a14600487e87dd5618c0b50ff0abb2a3180161f21d655463002c7a43ac2a8c60018bd84dd9418c0010ff0abb283180121f215765063000477c12eca0c60028ec825d9418c0010ff0abb243180121f21576486300045fc22ec90c60038bc845d9218c00187ae92a6ca980031d5c651d95300051f424c5b2a6000a3d8498b654c00147d0930eca980028f61261d95300061eba0e9b2a6000a3e848cb654c00147b09196ca980021fa1c32d95300d43ec3865b2a6000c75711c7654c0010fb0f18eca980028fa1031d95300051ec2063b2a600087e87087654c0010fb0e10eca980028fa1021d95300051ec2043b2a6000a5e83087654c0014bb0610eca981769ea0021d95300053cc0043b2a605dc78705c3654c0010fd0f906ca980021f61f20d95300051f42621b2a6000a3d84c43654c001878cbba2ca9800e2fa1f74595300061fbaee8b2a6000c3f751d1654c001938e9b9aca980032e1d370595300051f424c432a6000a3d84988654c0014f301310ca980028fa1261195300051ec24c232a6000a5d83984654c00187aebaa6c8980028fa1662d91300051ec2cc5b226000a3e85987644c00147b0b30ec8980030f5d475d91300045ec3c65b226000a3e850cb644c00147b0a196c8980038dd4651d91300051f42c63b226000a3d858c7644c00117d0e18ec8980662f61c31d91300045f43843b2260008bd87087644c00147d0a10ec8980028f61421d91300054f41843b226000a9d83087644c0c95750010ec898002ae60021d91303271d286a1b226000a3e85c83644c00147b0b906c8980022fa1f10d91300045ec3e21b226000c3c64dd5644c0010fd0fb2ac8980021fa1c65591300243f43eeab226000c3f75dd1644c001878ebba2c898003171d773591300063c3aee0b226000c3e76d94644c00117b0f328c8980028fa1665191300045fc3aca3226000a3e86194644c00187cec328c89828f878c0651913051f0e180ca3226000a3e85988644c00147b0b310c898002a760e62191300051f42cc23226000a3d85984644c00157301308c8980021fe1576551300045fc22ecaa260008df835d9544c0011f700bb2a89800e1fa1f65551300245f43ec8aa2605da5d83d96534c001c3ea7b24a6981771e1c36554d300065c326e0a9a6064cb870d91434c0018f0cbb8286980021fa1f65589300061e3a6cab126000c7471d95624c0010fd0e32ac4980030f1d065589300063a388cab126000c3f65dd1624c001878cbba2c4980022fa1f64589300061fbaec8b126000c3c75d916
  | 6 => 0x6563a6e4b2a42a4c7775dc56548401968e9b8aca908030f5d754d91210243f43eeab224200c3c75dd164484018d8ebb92c8908031d1d771591210043fc2aecaa242008bf845d954484011df04bb2a8908023de0576551210046fc3ac631a420087f855c063484090f90ab80c6908022fe117018d2101c5e422e031a42008bf845d9534840717908bb2a6908023be097654d210047dc02eca9a42058f8805d953484290fd0fb2aa6908021fe157650d210243e42aeca1a42008f7815d943484011f700bb286908163e2017650d210a45f43ec8a1a42008fb8758060484010fd0f28ac72819e1fe1d6394e500f52fc3ac729ca067c5f8758e53940bb2f70cb84a7280031ee197094e50004bcc06eaa1ca000c3f75591439402953906b2287280021f6187354a502e4bcc36e0a94a000c7986dc1529400b1790eb2285280163b21d6250a50164bb40eeb994a00097980dd732940011ef02bb265280063d205764ca500043f43ca6b0ca02ca768194d61940012f301baa83280025e603754c6500063bbaac298ca000c9c641cd645400117f08b96c6a800e2f21172d8d500054f42465b1aa000a5d850cb63540011bf0eb18c6a8002a72116318d500054f4246431aa05887e86dc5535400187aebb2486a80022fe1173d895001c5e422e7b12a00187c855cf61540cf0fd0db9aa2a81fe1fa1c635455000c5f43ec8a0aa01487c859db315400117f08bb662a800e2f21176cc55000c6e41aed98aa000c5d75d8f315400b0f90cbaa62a80165e201754c55000c6f43ec698aa000c6f72949659000117d0f212c7200030f5977454e403345fc3ac721c80008be8790d629004f55d0521ac5200161f21d655464002c7a43ac2a8c80008bd861cd419004f35d05ba663200023be09764c64001476412ec98c8000c757194765500018b8ca39acaa000317dd473595400064fba0e6b2a8000cd873dc165500018baeba9ec6a00021fe1571d8d400243e42ae3b1a8000a5e858c7635000153b0818ec6a000237e1d6318d400052e42ac631a8000a5e858c463500014bb07b2ca6a00030fd957494d4002cdc402e929a8021a9e8718d435002993d0e31a86a01822fa1b7250d400064e31ee4a1a80059ba87dc1435000517908b9ec4a000a1fa1f65549403345f436e6a1280908be8718d4250029179093b664a00021fe1576cc9400243e42aed99280028dc835db3250029938c6ba664a00166e20174cc9400064eba6c799280058bc865d1325000b37100ba264a000a37a1f634c9400064eba0c6992800087f855cf61500090f90ab9ec2a01a6ae20143d85400061fb2ee8a828000c777194565cc0050f90eb2aa5980021fe157650b300243e42aeca1660008f7815d942cc0031e902bb2859800a2fa1f6450b300045fc22eca8e60038bc845d951cc0011df04bb2a39
  | 7 => 0xbf845cf625440717908b9ec4a880a1f21570d89513fc3f430e6a92a27fc7471d8d52544032ed0fb8aa4a895e1fa1b705495100cba40ee0a92a20187e86dd732544032ed03bae64a88032b9d362cc95100c3f436ea992a2048f686dc532544011f70eb00c0a896a9ee1560181510051ec24a5b2a8200c6d7294b655054f87eebba2caa080a3ba1f725954100637ba8e4b2a8200caf741c9655054d8eeebb8acaa0803391cb71595410046fc3ac631a820087f855c063504090f90ab80c6a08062f2197494d410a47a432e329a8200c6d75d4b62504010ff0ab86c4a08121f21570d894148656316e6a1282908be8718d425040555d0db1284a08066da1f715094100c5e432e999282018bc865d1325048d958c4ba264a08066d205744c9412acdc402e899282008bf8750f60504bf17f0ea16c0a080b2b1c942d81410047dc3ac03028200a3e8498a65cc40147b09314cb9885297a0e62997310a43f43ca8b2e6200c3f7495165cc40147d09312cb988028f61262597310a52f41cc4b2e6214e4f3298965cc40187ee93a2cb9885297a0e74597310052ec1ce8b2e6200a3e849c965cc40147b09392cb9885297a0e72597310052ec1ce4b2e6200a7a809c965cc4014f301392cb9885297a0e42597310052ec1c84b2e6200a3e848c965cc40147b09192cb988028fe1170597310051e422e0b2e6214a5c835c165cc4974ed02382cb988029d60470597310a52f41880b2e6200a5d8310165cc4014dd04202cb988029b60840597310043f43e40b2e620087d87c8165cc40147d08102cb988028f61020597310a52f41840b2e6200a5d8308165cc4290f90eb2aa9988538710d6550f310a47743e84b16620487e85dc162cc4010fb0bb82c59880a1f21d6554b310145f43ec8a166202aae82d9142cc4018eccbb8a85988030f1d265583310061e3a2cab066200c3e65dd160cc40187acbba2c19880e2fa1f74583310063c328e0b2a62038be87dd1654c54b8beebb9aca9880a3ba1f725953100657ba6e4b2a6200cac74dc9654c40195ee8392ca988032b1d072595310065dba6e0b2a6200cb874dc1654c4019d6e5b82ca988033a1cb70595310063dba8e0b2a6200cbb741c1654c401970e8382ca988033adc8705953100674390e0b2a6200c3d75d53644c40117f08bb2a8988023be09765513101476412ecaa262008fb805d9544c40b1f100bb2a8988061fe1d6594d3145d2fc1acb29a625da7880596534c4018eecbb8aa6988031b5d752d89310043fc2ae1b12620487c855c3624c4050f90eb2aa49880a9b209655493125e3a38acaa92625ca7880595524c4291ed0db8aa49880a2fa1f645093101c7743ec4a126200c7975d43604c4015e302286c0988023ee1d60181310053c42ac03026200c3d74953654840717d0fba2ca908030fdd474595210
  | 8 => 0xcbba2a6a180e2f2197090d433265c302e121a86038bd8790f6250c8d55d0521ec4a18021fe1570d89430243e42ae1b128600c7975d436050c015e302286c0a18029ea1720d81430055cc2041b028664caf645c86050c011f70eb00c0a18029e21560181430051ec2c83b22a4008df8758c635480117f08b80c6a900e2f2117018d520143e432eb21aa4148ec865ca435480117f08b86c2a900e2f21170d85520043fc3aa7b02a4008fb87580605480147b0928ecaa10031d5c651d954255e1fbaee8b2a84018f687dc565508018eeea38acaa10032ddd0715954200673b90e2b2a840087f855c763508090f90ab8ec6a12ab275d36398d423165db20e0b1a84008df8758c63508014bb07b2ca6a100a2fa1b7454d421e45ec3ec721a845f8bc865c243508010ff0ab9ec2a10121f21573d85420063abaea3b0a84018bc845c361508011f70eb00c0a118aaee1160181420063bb8ca2b2e6400a3e8598664cc80147b0b30cc999052a7a0e61993320a45f43ea8b266400c3f75d5164cc82953d07aa2c999052a7a0e41593320051f42cc2b266400a3d8598564cc82953d0730ac9990030fdd675593320a54f41ceab266400a9d839d564cc829c3ca7a9ac9990028fa1671593320051ec2ce2b266414a9e839c564cc80153b0738ac999002aea0271593320055cc04e2b266414a9e8394564cc80153b0728ac9990038dd4651593320051f42c62b266400a3d858c564cc80147f0ab82c9990028f21570593320a54e41ae0b266446aae821c164cc80155b04382c9990032e5c070593320a54f418a0b266400a9d8314164cc80156d02282c999002ad60450593320045f43e20b2664008bd87c4164cc80147d0a082c9990028f61410593320a54f41820b266400a9d8304164cc8291790eb22a9990031ddd7515873201c5f426e0b0e64008bd84dc161cc80187eeb322c1990030f1d664583320061fbaac8b066400c3c7559160cc8090fd0fbaac1990030f5d254d953254e2fbaee6b2a6400cb8641c1644c8090fd0fbaac8990063da1f71591320063bbaee2b226400c7475dc5644c8018eeea38ac8990031d1d471591320063dbaee0b226400c7875dc1644c8019e6e3b82c8990033c1c770591320063dba8e0b226400c78751c1644c801976e8382c8990033cdc4705913200678388e0b22640087f855d9544c8011ef02bb2a8990063d20576551320047dc02ecaa264058f8805d9544c80517f0eb248699192ae2016490d320045fc22e1b0a64038bc845c3614c8015d304206c0990023ee1d60181320055c422c03026400a3d8590b645440117f08b96c6a880e2f21172d8d515462ebaec731aa25ac7b651c163544011bf0eb18c6a88ce1f61f6394d5119d2ec3ec729aa200c5d87d8e535454bcae21b1ca6a895e1f2197094d5100c3f436eaa1aa2008
  | 9 => 0xea1d20d600013c00000019a05100000000005700000504c8001128680000fea732579d600000004ba3f8000279540000000001212678f000000010a00000016189410180011d0000000000e100025300008a92980021200021815a037a221e780005500000000002616a8daa3a8011d500000006f8788001918220160001550001d580000000000003708e800000222a6a15f0891601380a08000f79a219b126a12a468000000000968000850000ff14c0000000000000000001990000000001cc8000f29040110d4847a3901a8cb86c800000002400000000000002800800400400001000402400800401c00000400801400800000000c00800403c00002400000800400000000400000400400402000000001001001000002c00400800003000000c08002000003002000002c00000800800401400400000401000400800000000000000000001400800c00000400400800c00800800000401c00000c00000401000400001400800800c02c00000000402400c00000c00c00002c00400000400c01400000800401402400001400000000400400800002800400c00002001400000000401800400400800000c00001000000400000401400000000001000401002c00400000800000800002000c01400400000400800000803000403c01c00400000000400001000400401000401805800c00400402800000400000000000000000800801000800000400400000000000c00801400401401802000c00400000800c00400000401c00801401000400000800400005400800000800c01802006800800000800001000401c01001000004000400000400c01400000400001c00c00400000400000003400800000000400000000001000001c00801800000000000000400800000801400402c00402003800000400000000800400000000000400000400c00400000c00000003403800003400000800000000000400800002800001400000400000000000000c00001800003401400000000400000000002000000c01000000002c00000001c00000c00800c00000002400801800000800400000000001800c00000802c00000001c00000401000801400801000800001000400000000000000000000000002000001000c00000001000401400800402400400800400002000000000000400c008011bf0eb18c6aa002b62016318d540047dc3ac0302a800ad8835806055001970c8382c8a98121f2197094d532ee3c302e129aa60487d8794f6154c974ed0329ec2a98022fe1170d855301c5e422e1b0aa600ae9821036054c0157509886c0a98029e61410d81532ee3bb2ae2302a6008fb875806054c0157108b00c0a98031ddc6515964300636b94a5b2a8600c78651c16550d598beebb9acaa18031edd470595430065dba0e0b2a8600cdb731c16550c0187e
  | 10 => 0x19760000fe00021da1b9aa00012a0000000000001ba0000001ab9a40b280000000021d0e59988c921181c9d39840920000000000000959c080000021f0000001ad08185880000018d9828000001ec80000000004809100007b1b580023a0001f613980000000019595fa198d926b00000017a21789080000000000000013d0000000e90a292d09b80000000000008c00022500000001a0f38a704d8000001330001119e3898a2800004494880003693b0c3a42a1a8b40db1f00000a311202d03200018508e0cc168a1f82f15d0000002450000250000001fc00000001421e8b800011780000000000000026080010923005083e96484904700020300000000000000000022784680027380e93110f8002601678208001080000000001221dc0c081200000021394681d87a00005320b0001df0ca9b70002381930b48000bb938933a40a3e140a7a9c000000015e0000000000000e1a1600000000013b8a788a0000000b08000001c20048d69c38000a0050268a6e8be02d9e29359f900c8a60001f7840879a4d98ea470000001a90ee8000330aaa7087d0000000000000001750708000d011e80000015c9d10000de0000001670f900297ea340000000000139fb000252882a4c9f41c68a40000000dd0da251072000263125a29173a438000770ae0000000898001588669e48002700000c897b0ec0ad8000001570e89e20000000000001b027c80024913280024ba660000000000000fa94526e00022b01e80000000000024625896b9a8a720000001fd00021307e0001b79168000000000000000000000000fd80012509e9cf0158000731a180012c87e8000ab8001a294e1f480002e84d208868a518000000001288bc8000d400000017f2200001db800000020233a348000c99e600000003d8a980000000000000000000000000017e22a8001858ec8000238002188a18001949f20000000000000000000000001b50000fc00c0000168000228000000bd8001970000002368000000001cd17680000000023d8000a89c725e00024a0f600025f8000000000000ce1548e48900000000000000002169920000001021978000f199c876024a060000000000000832249e08e688786f1dd80005580016d80000007b80003580000000000000003a14800021e0001071b98000001770001c50000e300010c8000000d215600018e00010b1610f880000022983907900012480000000000020d80000019d09c8001a60b500010780015e8a68071a38000d796d0000000000000001229ac00000008b27700000015c00000010a80003e00025b14394200025e8ac10d80005207c8992218000001e88001281490001a485b14c9c80000001b900017900017100880000022c0002109ab1e710f1238628460300e20748eb0618c280b0382140299718000001369
  | 11 => 0x18f9e12288ee1d29cc1d00000000000000f598380026900000025a0000000000000001fa00025c8000b19ee804000201a1a00015083600000000000001917f80000680000000000004980000005c8000000002008001de94b8000000d990111580000019280000007d9430000000000000000000a508fa650000002640000000000000002020001f80000000000001051de00000000000000000025380025f00806380003b8002670001b30bea7180016b00000b8000960000030de8000bc26b80013901300000011b04e8002171848000000000000001f38000000000001059e980000000000006505680000014a0fa04b0398091361479a5a270931f996c8000000d88000fba768000000971b20000001e81658c40b68000bd0ae8000c7800000174a3780000016399e0000bf8678000a38000001f28000000001110001d687a80007784e0561b180020c8000000000000000000001758001088001f180027627b93f0000000000179888000000000000000001da14b1411400000880000000000001bc04c0d31fe00000016c0648e280000000002e1ea8000000e706c0000b119516f0000001b280019800021c1151260cf20d1378ed8ad1279c480005402810095126f9581320000000db8429860a2131a7293c94700013709820c22e0000df80000000000000000000004a02920f93a0001cea0b8c1a501f526581f00010381500000000008c91c80000005d8000000001031daa3b8529c300019400023600000000000000000000010e0001a100000000000006009b0cd000000000083a2da0800e00005f0230001bc8000c800024c27b0630001ff8ed1100ab0000af0001a50c594f9b89fc8000808000b380000000018b81c0000b32028000000000000001a79d08000000000000000001898780751908000000000cb15220e9609701ff1599208df15783106200012d9e42620000810000000000868001960e6000230a591cb19e9149ed23c9d82331cda0a1c78939429caa740350001b48840148928670b901b2209a6a388e806a207826a1b0421fba4d00a910a3721585806e8cf8188d19730ac80611e134a1101808200022d0b58001a998c2628001708000001b380018300006d05e1ca0338a590e9eb8dc8218002541be24480001703f8cda4e8000c700020e0002580000b980a0450000000000001640000000001190000000ea00009a0001ed80000011f8001ee0259801519fe8fd14404009d9eb0f3038812800000000274a410000001098fc8099d700016512b06b88600000009e1d417280000004890000023d0000000000000000001622498000579740000002598001bb0d109c00009781f8000001e00000ba8590000001138fb00015b0001291c182700004f00025090d02b0411d30439140000c500000000006900024b1bd8001d
  | 12 => 0x1f88d380004a80016e20f0000001340aa0001188000018000001cba240000000000000001630000000000d517c1dd1d90001f68c10e0181a0400f89f8001448001788ca19380000011aa7c15d80000025499c24400000006b00000000000012a9721ae18c99999d80022f03c15315b9c900011b80002f8c20bb0001db08485c04185d0f088d0b70e78dd977800045a6117b8611ef0000f988f00018a03b00d12c0af93017816f8001b12259a726d00d88585b94e80000000020901b80000000003aa61a0500000000000010b9c28000001b80768000000000430001d49f71e68ffa710b78001881aaa0380000000000000000005f8001590000000000000000000000000001131af9230000598002680000001890000000001ef800000000000145800000119a560001c880000780000000000000000026c00000000000027a00000000003400012b93e91700000000006e1798001f5a520002420001f103f15589a99f8000000001498b88000241ba8a900012e1ac8000000001271bb8d8031a5b9ec1a81820199218701968f100016296a0000000918000b014187c11800013514d0000f70000000000000000002048000001fda418dc08b80000024f27880008da698d286a8718518000000001fa89512012f9e51c60000000e421c8000002778000000000000000000000000000000000f680009d0000000ce8000001e30000211cf80000013d86407f22ba6a94f02a0002568000000f48001d88ba0eb98f0000000000000000001ce00023599f0000000001e1a4a80006d9c58000001b6a098000002011460bf2352401c412f032980a6d99b84413e26f13fa4583d05a18b1069c100000000014a8000729669f08f40001660000d71698000000e511d9871b627917da5d80022c80000000080000000013a8c00001bd1ad916206a488759bf800000000000000053a002329680948000001a30000001e580018a8000c480010480019a80012e81d0002058c697d219275010a3b1910e091a00000226c80023982c0000000001d98000ea80014d80024f800000000214a649a0a798c30b62210000000000d58309bf06600000000025c00005a82a85481000f1d780025500006591c1568002571ae8000000000000000000f80002239a007fa478000001500002150740001c98ef2260000000001529308e980019000000007110c0998000002310a120a80000000000026380000017c82880024e0001e9187a2f98680000000000000000000000018d11f23180023c25d0d080000006080000000000017a8001241df95a8800000001f30c624318125aa4816900000000000023e8000000000000870000000000039060000f216e8f522a22301e275a070000001b4153a2e9b0a780000b200010288882c80000003489f000266a3f
  | 13 => 0x2b84f87380000000000021003c8000001dc8000000002558058000698000000000a48000e38000a80000000000001be80005e8001af0000118002320000cc8000000000000efa268000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2058000515644501cd654800148d9210073591100067021d324c520440016c0964c93148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94b
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x124b
  | 10 => 0x124d
  | 11 => 0x124e
  | 12 => 0x98a
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x128a
  | 16 => 0x128d
  | 17 => 0x128e
  | 18 => 0xca
  | 19 => 0xcb
  | 20 => 0x4
  | 21 => 0xcd
  | 22 => 0xce
  | 23 => 0x9ca
  | 24 => 0x9cb
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12ca
  | 28 => 0x12cb
  | 29 => 0x12cd
  | 30 => 0x12ce
  | 31 => 0x168a
  | 32 => 0x168b
  | 33 => 0x168d
  | 34 => 0x168e
  | 35 => 0xa0a
  | 36 => 0xa0b
  | 37 => 0xa0e
  | 38 => 0x130a
  | 39 => 0x130b
  | 40 => 0x130e
  | 41 => 0xa4a
  | 42 => 0xa4b
  | 43 => 0xa4d
  | 44 => 0x134a
  | 45 => 0x134b
  | 46 => 0x134d
  | 47 => 0xb0d
  | 48 => 0xb0e
  | 49 => 0xb4b
  | 50 => 0xb4d
  | 51 => 0xb4e
  | 52 => 0x16cb
  | 53 => 0x16cd
  | 54 => 0x16ce
  | 55 => 0xb8b
  | 56 => 0xb8e
  | 57 => 0xbcb
  | 58 => 0xbcd
  | 59 => 0xcca
  | 60 => 0xccd
  | 61 => 0xcce
  | 62 => 0x170a
  | 63 => 0x170d
  | 64 => 0x170e
  | 65 => 0xd0a
  | 66 => 0xd0e
  | 67 => 0xd4a
  | 68 => 0xd4d
  | 69 => 0xe8a
  | 70 => 0xe8b
  | 71 => 0xe8e
  | 72 => 0x178a
  | 73 => 0x178b
  | 74 => 0x178e
  | 75 => 0xeca
  | 76 => 0xecb
  | 77 => 0xecd
  | 78 => 0x17ca
  | 79 => 0x17cb
  | 80 => 0x17cd
  | 81 => 0x104a
  | 82 => 0x104b
  | 83 => 0x8a
  | 84 => 0x150a
  | 85 => 0xb89
  | 86 => 0x180a
  | 87 => 0x14a
  | 88 => 0x2c9
  | 89 => 0x198a
  | 90 => 0x14c9
  | 91 => 0x4b
  | 92 => 0xd49
  | 93 => 0x17c9
  | 94 => 0x138b
  | 95 => 0x10b
  | 96 => 0x409
  | 97 => 0x180b
  | 98 => 0x1609
  | 99 => 0x198b
  | 100 => 0x1789
  | 101 => 0x9c0d5
  | 102 => 0x589
  | 103 => 0x5c9
  | 104 => 0x138d
  | 105 => 0x1849
  | 106 => 0x150d
  | 107 => 0x198d
  | 108 => 0x138e
  | 109 => 0x150e
  | 110 => 0x1a09
  | 111 => 0x180e
  | 112 => 0x3ca
  | 113 => 0x24b
  | 114 => 0x15ca
  | 115 => 0x144b
  | 116 => 0x188a
  | 117 => 0x160a
  | 118 => 0x184b
  | 119 => 0x148b
  | 120 => 0x1a0a
  | 121 => 0x164a
  | 122 => 0x19cb
  | 123 => 0x14cb
  | 124 => 0x58a
  | 125 => 0x5ca
  | 126 => 0x18ca
  | 127 => 0x1a4a
  | 128 => 0x154d
  | 129 => 0x140d
  | 130 => 0x24d
  | 131 => 0x144d
  | 132 => 0x1a8a
  | 133 => 0x194a
  | 134 => 0x19cd
  | 135 => 0x14cd
  | 136 => 0x154e
  | 137 => 0x140e
  | 138 => 0x24e
  | 139 => 0x144e
  | 140 => 0x184e
  | 141 => 0x148e
  | 142 => 0x58b
  | 143 => 0x5cb
  | 144 => 0x18cb
  | 145 => 0x1a4b
  | 146 => 0x3cd
  | 147 => 0x15cd
  | 148 => 0x1a8b
  | 149 => 0x194b
  | 150 => 0x1a0d
  | 151 => 0x164d
  | 152 => 0x3ce
  | 153 => 0x15ce
  | 154 => 0x188e
  | 155 => 0x160e
  | 156 => 0x5cd
  | 157 => 0x1a4d
  | 158 => 0x18ce
  | 159 => 0x58e
  | 160 => 0x15692
  | 161 => 0x11693
  | 162 => 0x199353
  | 163 => 0x5c591
  | 164 => 0x19d4d3
  | 165 => 0x1a57d2
  | 166 => 0x19d4d5
  | 167 => 0x1a9952
  | 168 => 0x1a4ed2
  | 169 => 0x1a57d3
  | 170 => 0x18ce93
  | 171 => 0x1a9953
  | 172 => 0x1a57d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2200
  | 6 => 5647
  | 5 => 1274
  | 4 => 4
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (90196+((h/733+packedAt gbK7 (81400+(h % 733)*12) 12) % 2905)*13) 13
  | 6 => packedAt gbK6 (297404+((h/1882+packedAt gbK6 (271056+(h % 1882)*14) 14) % 8199)*14) 14
  | 5 => packedAt gbK5 (80254+((h/424+packedAt gbK5 (75166+(h % 424)*12) 12) % 2236)*12) 12
  | 4 => packedAt gbK4 (283+((h/1+packedAt gbK4 (280+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc1f00ffff01ffc1fffffe00027f639d1e73fc
  | 1 => 0xfe000f81ffffffe0f803fff1d98bce213fccf
  | 2 => 0xffffff001ffe03fff0003fffe1e0c0ffe38f0f
  | 3 => 0xfffffffe00003ffffffc000fe00ff03fc0ff0
  | 4 => 0xffffffffffffc0000000000ffff0003fff000
  | 5 => 0xf00000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x540508292710a4c098a9b206002b218d06315c
  | 1 => 0x8a0105a0963c9520d02a4aa0c982ca210d4c5
  | 2 => 0x654b6901129422a5a00519546160c055630b0a
  | 3 => 0xa72b2964020433946560018b600d602b80ea0
  | 4 => 0x4f9cdce79cf9701084181060dff50003dfe000
  | 5 => 0x8000e00400c1802108602180fbdefbf8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36997
namespace PEqualNP.Outside.L_meta_36997
open PEqualNP.Outside.L_meta_36997.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 7 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 92 := (concat bs1_4_0 (concat bs1_4_32 bs1_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 44 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 64 := (concat bs4_4_0 bs4_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 40 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 64 := (concat bs5_4_0 bs5_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 40 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4 := bgb_4_0
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
theorem bgb_5_1248 : Interval gbAtlas 5 1248 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1274 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))))))
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
theorem bgb_6_3872 : Interval gbAtlas 6 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3904 : Interval gbAtlas 6 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3968 : Interval gbAtlas 6 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4000 : Interval gbAtlas 6 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4064 : Interval gbAtlas 6 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4096 : Interval gbAtlas 6 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4160 : Interval gbAtlas 6 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4192 : Interval gbAtlas 6 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4256 : Interval gbAtlas 6 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4288 : Interval gbAtlas 6 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4352 : Interval gbAtlas 6 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4384 : Interval gbAtlas 6 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4448 : Interval gbAtlas 6 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4480 : Interval gbAtlas 6 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4544 : Interval gbAtlas 6 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4576 : Interval gbAtlas 6 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4640 : Interval gbAtlas 6 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4672 : Interval gbAtlas 6 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5647 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))) (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))))) (concat (concat (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))) (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784))))))) (concat (concat (concat (concat (concat (concat bgb_6_2816 bgb_6_2848) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)))) (concat (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488))))) (concat (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))) (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)))) (concat (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000))) (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)))))) (concat (concat (concat (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352))) (concat (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)))) (concat (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704))) (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896))))) (concat (concat (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056))) (concat (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)))) (concat (concat (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344)) (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440))) (concat (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536)) (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632))))))))
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2200 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888)))) (concat (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 bgb_7_2016)) (concat (concat bgb_7_2048 bgb_7_2080) (concat bgb_7_2112 (concat bgb_7_2144 bgb_7_2176)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0feeaeee0fac8eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809440 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36997.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.and,[0,4]⟩,⟨.or,[1,6]⟩,⟨.or,[2,7]⟩,⟨.and,[0,5]⟩,⟨.or,[8,10]⟩,⟨.and,[1,5]⟩,⟨.or,[0,12]⟩,⟨.and,[9,11]⟩,⟨.and,[3,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36997

open PEqualNP.Outside.L_meta_36997 in
theorem PEqualNP.Outside.L_meta_36997 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
