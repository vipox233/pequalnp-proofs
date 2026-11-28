import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37115.Model
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


end PEqualNP.Outside.L_meta_37115.Model

namespace PEqualNP.Outside.L_meta_37115
open PEqualNP.Outside.L_meta_37115.Model
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

def SBf (j : Nat) : Nat := [7, 6, 7, 5, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37115

namespace PEqualNP.Outside.L_meta_37115
open PEqualNP.Outside.L_meta_37115.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x110008b0f8c4e4c003362831e4c0189140208175e70a15484800f2c018000000000008400200000005a1c4a80ab8e9a322c00030946aa56a51811c1e1c101060428114003042a24200ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4a0c800008d00000d80010001060000000ae000380128433500000491d800cc5a1f2604496000000006000b42852311801e1b00000aa0051010e8364b80132794a9fcbc7348054003a188d48e4b00070009b1a058422316000002a0000000002d800007d3400000420700000512c9bd0c000f8744e0d422144c9f000011c0020800782f120011800001311232048c010002e8e45013240000018280008017001d4f44f051ecec12000152601478fc8c9238270209d3ba2d027c3915822a0521e0c287270f418a1228a4340332a780491269b8b8820599cc65451990d6331717d3437400acda53129107088001a4b07e451c43c000000010002890e00000006800001000f038c028b810506010080010004029608008886000101000a80000000800002850609828c8380804f94b439ea8e873e50d0e7aa921dbd4943b6292879f5350f5ea4a1cf14943d6292872c5250e7ea2a1cf141439f2a0875e53d0abaa7a14f54e429f294853d5190a7ca12157d4d42ae29a853d5310a7ca4216b948429ea88853e5010a7ca9994f55332d6216653f548ca78a91967d0e32cea1c659f548cb38a9195794a32cf214659c428ca7ea8994f151329f2a0653d540cb3e86196750c32d6210659e540cb3aa8195794832e729065cf420cb3c84196710832e6210658c420cabca7a0d754f41cf29e833d53d073aa7a0c754f419f296839e32d073865a0cf943419eaa4833f5350678a4a0e78c941ce19283b75150678a0a0cf950419f2a6633d54cc67ca918cf55231cea1c636e528c6daa518cf951319eaa2633e540c67aa818e750c319faa6433c54c87986590cf952219eaa4435e53886baa710cfd51219e2a2435f53486b8a690f30c921bda824378504867ca810cf550219ea9c813e529033c6520670ca409ea8c813e50902bca6205754c40cf298813d531033aa6204754c409f290819e321033864204f544409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c827ca9104f55220af29c415d538839865104fd51209e2a2415f53482b8a6905dd4520ba28a413f5408278a810730c8209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x76440222abd5363e2800f0c000ac00d002d2c9c025407149800d4b8270411b12478693166930e48e590308dd5801201d004274407666540536018000031700281e000080c20584060010d0c0408f0004000c3d4c5250f0f631494387d8d5190a1d63942428d584548ca8e62d5232a3988548ca9561152328b594420ca8e6290832a3d94420ca8d6510832a3584420ca8e60108329318953d062c6254f41a318953d070f6254f418718953d070c6254f418318953d061f658cb418759432d070c520c9418758c505068c6250e31c350e528c61d63951318b189544c6386055131a3189430c61d6315321c315032c870c540c921d20c8504861d6395021c3948329021f635464093189531022c6254c40a3189531030f6254c4087189531030c6254c4083189531021f658c84087594321028c6250f308b98b548c21c6550d30a3189434c30d4314930c550c514c21d6395320c3950328821d63150208d584540830c540c8208758e54c421d6315210
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x4004800820cc0000a2380428338ec629287215c76510832818e4b18a0a0c0c7258e5408607396c6a8c81411c9431453081aec2a06410505711503208206392c72a621031c96315210
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
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (912+((h/16+packedAt s0K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s0K4 (4895+((h/55+packedAt s0K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 73)*7) 7
  | 2 => packedAt s0K2 (502+((h/3+packedAt s0K2 (490+(h % 3)*4) 4) % 16)*5) 5
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
end PEqualNP.Outside.L_meta_37115
namespace PEqualNP.Outside.L_meta_37115
open PEqualNP.Outside.L_meta_37115.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xc82000748c0b28020508000080bf42bd42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x70000112009200a3300f26aa3a15594632c6a10652d52d069ca518e55043196a9081355110298a4985514530
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (212+((h/4+packedAt s1K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s1K3 (282+((h/3+packedAt s1K3 (270+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 2 => 0x3f03ffc1ffc1fff878383e0ffc3fc1fe94e73
  | 3 => 0xfc003fffe0ffe0fff803fc00fffc3fe0f18f9c
  | 4 => 0x3fffff0000fffffc0000ffffc000fe0fe0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x104000880008000008840422200444840210a5
  | 2 => 0x48a65910ca5138658321a3445642a85a694652
  | 3 => 0x292aaa2146a309aab042e9089aa83342b18b18
  | 4 => 0xb2cd344a943a52d35de84212ed33018cde0de0
  | 5 => 0xc30e387318c39cfc6673739c0e222210fde000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0faaaaaaafaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37115
namespace PEqualNP.Outside.L_meta_37115
open PEqualNP.Outside.L_meta_37115.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x700b40060890d0044596004e0c02a385100e00653055c00618525c828126c021027c90000086915e8c40f144caab1678e804a546000040087001465003180ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x4314000000a1d8009e760000000000319cc80000060b0000785800000000000720000034771f92c48693407874752d1985a211a09ce21c000dcf0143a02c8e000e85c00461a9ac0000002144451000945c0e350000040048a8e03c1b00000332e000a40d20800ca7f00030c04e091bcc4450012000001e9e4a8840001100390d898ac6c30864264c16000dc2f04040001f1820cbc57028a40000118040000088080000251e8007c18a08006d2116c0e20399f80000000000000191ecaa003e801025f1c000885d26800564900000c6530000c0059000f800152804c2820000004144000000008101404180c0c0004000808086014000008000410102c0c4c2014040010400002baa921d794a43af28c875d5090f3ea8a1d714943ae28a875f5050ebca621d794f42aea9e859d43d0aeca3a15d54742afa9a855c5350b3a86a15794c42aea98855f548cabaa9195794a32af28c655d508ca7ca8194f55032afaa0659e540cabaa81967550328eaa0655e520cb9ca4195794432aea80655e53d06baa7a0e750f41b7296836d52d06bea6a0d714d41cea1a835e53106baa620d7d5231aeaa4635e528c6bca318d7542319f2a0633d540c6bea818e795031aeaa0639d540c63aa818d794831af28863d6510c6baa018cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710d7d4d21ae29a435f53086b8a610f948421af29e815d53d02bca7205754e40cea1c815e53102baa6206750c40b7290816d52102eca2205d544409f2a6613d54cc2bea9986795330aeaa6619d54cc23aa9985794b30af28e615d538c2bea8985755130ae292615c514c3b6a0985794c30afa9e415c53c82bca7105754e209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d54420afa9e215c53c42bca7085754e109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x38070002290000060098000401632cc00200a1078a0144b208002e180000680aa00821c0008003c550d51d0a8c6250d4295987548ca1d649463287d91508ca1d6595032c350d52d06946150d419398b548c61d6494a3187d91508c61d659503187590534861d6414c2196580530870d4354840c550d511024c625513095185544c21d641493087590514c21d6494c308759053c821d6494e208759053c421d6494e10
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s2K5 (864+((h/16+packedAt s2K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s2K4 (3970+((h/44+packedAt s2K4 (3618+(h % 44)*8) 8) % 194)*9) 9
  | 3 => packedAt s2K3 (1036+((h/8+packedAt s2K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffc1ffffff81fffe0ffff83ffffe78f1ff
  | 1 => 0xe07e0ffe0ffe1ffe1e0ff0f07fc3f83fa74e73
  | 3 => 0xff800ffff07fe1ffe00fff007ffc3fc1c78f9c
  | 4 => 0xfffff8001fffff000007fffc001f80fe0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x20800440004000022100111100449080810a5
  | 1 => 0x49149488652830960c8690a22a4290b4a34652
  | 3 => 0x85252910a351032ac10b2a044ca82685458b18
  | 4 => 0xd659ce254a1d55cd77a1888977330319f80de0
  | 5 => 0x18618c398c6199f199cdccce06220421f6e000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaee88aa88eeaaeeaaee88aa88eeaaeeaaee88aa88eeaaeeaaee88aa88eeaaeeaaee88aa88eeaaeeaaee88aa88eeaaeeaaee88aa88eeaaeeaaee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37115
namespace PEqualNP.Outside.L_meta_37115
open PEqualNP.Outside.L_meta_37115.Model
def s3K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8a4200682f995d32be6374c6f185c30
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x4c109541cca350b318d420c2550430
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*4) 4
  | 3 => packedAt s3K3 (i*15) 15
  | 2 => packedAt s3K2 (i*26) 26
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (5+((h/1+packedAt s3K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (96+((h/2+packedAt s3K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt s3K2 (107+((h/1+packedAt s3K2 (104+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 39 s3Pos s3Neg, 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8eaeaeaeae8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37115
namespace PEqualNP.Outside.L_meta_37115
open PEqualNP.Outside.L_meta_37115.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x9500010000c74012166d1004e0000046ac01a043000a3239404009000f002001826015142ea438500940160070189008401f3c988111a484280000044001380003ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461bf428c37a851877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea1061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641ee42c837a85907b50b20d6a1641df32c83dc6590774cb20f699641cd32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e84907b90920dea1241ed424835a849077cc920f719241dd32483da6490734c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10ef99421dd32842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa1221bd42443be6488774c910fb20a21f541443ec62887d4c510fb10a21f521443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810ef99021dd32042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083bf421077a8420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31dfa1663bd42cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f790e31eea1c637e528c6faa518efd0a31dea1463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063bf420c77a8418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21f721443bd42887da8510eb50a21ef99443ee32887ba6510fb4ca21e6994437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8490ef50921ef99243dd32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410efd0821f721043bd42087da8410eb50821ef99043ee32087ba6410fb4c821e6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40ef99681dd32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a852077cca40ee994817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea1081df32103ba64205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28
  | 2 => 0xc0040080a000058088000020240700800000c0080c002000018090000040200100c00001000000000000050180100300603c00400800000004008000000000000100402efca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7c87a16f50f42de21e857e51d0afaa3a15f94342bea8685bf53d0b7ca7a16f54f42de29e85bf51d0b7ca3a16f54742de28e85bf50d0b7ca1a16f54342de286857d5490a7aa9215f94e42ef29c855e5390afaa7217754e42aea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f90d42dea1a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142dfa9a85be5350b7aa6a16f14d42dfa9285af5250b7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050afca8214f95042bf29885de5310abca6215f54c42eea98855d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ef21e65dd43ccbb887996fd0b32dea16657e51ccafaa3995f94332bea8665df54ccbbca9997755332ee2a665df42ccb3e85997790b32eea16659d42ccbb8859977d4732ef28e65dd51ccbb8a39977d4332ef28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85197b90a32dea1465ed428cb5a851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbbc86997750d32ee21a65bf424cbdc84996f50932f6a1265ad424cbde6499778c932bfa8a657c514cafea0995f14132efaa265de544cbbaa8997715132efa9265cf524cbbe849967d0932ef21265ce424cbba84996750932e6a12658d424cbb8849977d4532ef28a65dd514cbb8a29977d4132ef28265dd504cbb8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf29683ee52d06dca5a0df54b41f6a96836d52d077e85a0ef50b41ef99683dd32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52906faa520efd0a41dea1483df32907ba6520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837
  | 3 => 0xd500059c0000000000017000000000a0c0c0005140000010a504758000001fc37c00278292000370401ae130d3800000794002ac00021400245000bf80e000000cbc000000000006ea42048d15ae095378360001f9000ad800000440000000001c40dd74800000001341300000015789e44200149a3f00066c000000000000027b0000d90c29246211cff8c461c000b981b3ae0000000000065ca1000000001b90dc000a597ea5e4d44fc50b38000a6db00000002a9501870002dd12aa73420b4000e600000000000040000beb2d1c8dac00000000000060000005f80000053a150002f3000290b6a8b000804001523b4411b78fd2980017725621e430001b20002c4003310006681e000000000812be5b8449aa80048e001a3000000000002fa6ac000698006d85547e0002662943e00000000005800206de13002646e0010e0943b60e1609e0000001291f813a0000022b000574000c600000000000000124001e8000cd0000004c287c000002c43054c0003da0f93ab5f00023000000000c3c00000000000718c259650cc29c25501c8002c26e200000000000000bb000000000001345c808d70800000330a3109000000000000000000000000000000099000000af9706760000006462e24c37b040b2d6cc236e3e2001b6800000b58bb9010c4869200411dac84ddb1f03e3ad9184e15ed91990d547a0000000000052c602154c678d01b1e33a00175a552ce000350d42b61159f00f0d0845693440f681c4403f340714a700a4489299205d146d09528b42d84c96516525e72d0b20917e4193b04d362415ba20a2e82d81481e53c63cd71583d86e0408002385c4b4000000000000ad382810019f25446b00025a0b000000000000d24f38001f668c3380e62274422000000bb495000352000880005b48d12a31858c001b9ac0360ac8bd357000000000000000000000681e01c000010070020000080b00801c000000020000000300a0100300601e008018000000280380100e008030000000140000000e0180400000200000000030000020020100400180300000800800000020000000000100000000002800000000000000260000080180d0240000480000000806000000000050030000040300500202002000012034048010020000080400001400001000024000000020a40000200200800000006024000080000200102c008008048050080000380000c00002000018018038030000000281300800401002018000000030020040000000201403801008054008040000000801f0020100000001a0000300300200c018020040080980100400800802000034028000020000000000c0500100200a0100000d0240040300600000c0080701e000010040000040080000000801006002054048000020000000401200400001000010068050
  | 4 => 0x1890000d8a101d0000000240037621a1582800019e0007c1794c44c4d12e31223bd472ec50a1d9320003d47345000018e1e10804635e9956a28d0e05d44f8000000000032e178d44a89dc3e00000024e0000000000064a000003470007ed88000614741288004a6000003670000011a810000000000001766fcc827e46c20da5a7110c001a1ad54460009e31322a000002b369a0000025c41ed7462800000ccce980018600000000570000001220000000030200036c003682c0000968001200003c8ae0c600194800000001a80000000000026d000cfc00000000000000003f40007b800000000f20003a897c0000000000000286000000000000004f811000000000001e13987d0042a9064c0c7aa303fc490bdaab522359aa0cd2b43c8000000005fc000003e6000000004f44f4000550000000a00009458c18800000d60df1130000000b9c34b29a4000000000015baf830cd649b24d454a30000000000005302c6560011e0000004508f2bd0000019c9f62e40a8728006c472400352372c0032b07024b4d932f441c0003b81309e1d13381a5923405c8f92226ddb82d956284cc1816650c24a6acd2f0bc49308f2c23b92b80058841c90a06538a54001290000000019f0d6064000000000013e800000224cf000616c68ee945610000000da3a48b552001466ad0970e82d6de5481d948865180948452000be000000ad53faa3500b7c2f26c444238293300b60016c000104000000002ac6241788b0006d9040004de7f5242720000000025b0007980018c1b2b9c4b8000007600000032c0000020b6440018a33617cd0147908000000ca8005f8ba17ba124f20000000024a1f47a0d26bc000000000fe000000001e200000000288a049c2870000002d34c000694c7000374a24141470001e9730006ea328002e50902b0802f069e00155000000108039c40000000013955a000001ab000000f58001a2000000000006040035a000324a0918000001860251fed4c1aabb0868bd1931962a09c002ae528270000002b8c1838a4c3503e9398000002d51d9f74f800000000000cd5029532160004c01d404a5c0018a0c20157780023622935a14000c35680a25f2599902b02a85b8c419305c000000de41a15c021400000017d91a5fe458a780000014c0000054ca68ac9ca000000de9200000000000038e000738003d20003f29f5c4cf4a80005100000015e000ae84b31b5421a4000001c27b8da000000cb113b272563b16e89a6ee73cb4abf6d2000001a6000000000000000010e8b00007380018b35a00000000156001b52de366001700a74ee0005c002474c71a503d3f800000266000000000000005a800000000d858e800380000000000004a13a000678000002cf0003d8000001520003683b00085c1a0005ec7bc000f30560017a81500
  | 5 => 0x8badb0009b8288000003c0000923907d4069b50008e09d0e00002c8d200058ed8c3a800654d951cab94b00cd643160002f487000322670000003040180000026a000000600009c008a1e23a320000004000e5b30000000000008445c000001e24861cc961df10e4dcc68a8000cdc00000000000cc8000000c00011943249c5d0004ba00065a4b00000091b4111a3a4750005ae648000000005912798027617c4000048c000000b300000000000000d391316f096b0da40ce4a000120800578000ea80047c8b00009b60a0014ca28492b1506198598000000003bc7180000004286c8f800674ba8ab94a00019800000000b44002f2
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2528423d6494a109798e528425d6394a108f990528423d6414a109798c528425d6314a10cb949428432d5250a10d3949328434d524ca10e350932843a94248210f24c9208423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58854443356115110c7d53534431c54d4d109758b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425d6214d10d5584534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524434e6314910d358c52443656114910da580524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb149424425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d3149324438d424c910cd15241442d563905109d19541442b5648c510d514e3144274654c510d914a21443a54288510f14ca21442746548510da14a20443e221881109e19520443a94248110f24c920443e121481109798f540425d63d50109b98b540426d62d50108f596540423d62950108fd89540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109758a530431e5454c10c7551530425f6254c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48108f992520423d64948109798e520425d63948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520434e6394810d358e520432e5454810cb551520434e5354810d354d520432e6454810cb591520434e6354810d358d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d525081097d97320425d65cc810c7953320431d54cc810d394b320434d52cc81097d95320425d654c810c7951320431d544c810d3949320434d524c810e3509320433554c4010d554f100436552c40109e596100436952840109dd9510043355444010d554d100436552440109ed9510043695244010
  | 1 => 0x82af6550b20cbd9542c832f5350b20e394d42c832d5350b20e354d42c830d5350b20c795332c831d54ccb20e350b32c82ad648cb20cb55232c831e544cb20c755132c838f424cb20e350932c832d544cb20d394d32c82cf654cb20d3d9532c834f544cb20e395132c834d544cb20e355132c830d544cb20cb50a51c834d3294720ab59321c82cd63c872097d8d548825c63552209798c548825d63152209d984548827561152208fd91538823c6454e208f990538823d6414e209d98453882756114e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d20ab59242482cd63909209b195424832f6550920cb195424832f5350920cb54d42483ab6050920ea181424838d42cc920ab59232482cd638c920e3d09324838d424c9209b195324834f654c920d3195324834f544c920d355132483cb604c920f2181324823e64145208f590514825e63145209758c514832d4214520d34c8514826e65c8520ab59321482cd63c8520ea50b20483c932c81209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c2097d89530825d6254c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420825d65cc820c7953320831d54cc82097d95320831e544c820c7551320834e524c820e350932083365494420cd55251083565394420d554e51083374294420cd50a51083573294420d54ca51083365454420cd55151083565354420d554d51083374254420cd50951083573254420d54c9510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020d9545200827b6548020dc545200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c432f5250b10cb14942c434f524cb10d314932c438d424cb10b558e41c42b5648c710e950a21c43c5328871097d8d548425c63552109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108f99
  | 2 => 0x5350840c754d421032e525084097d97321025d65cc840d394b321034d52cc84097d95321025d654c840d3949321034d524c840e350932103565394440d554e51103665294440d954a51103374294440cd50a51103573294440d54ca51103565354440d554d51103665254440d954951103364354440cd10d51103374254440cd50951103573254440d54c9511023d6590440a798e411031d5390440cb54a41103355190440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401029c6350040c754d401032d5250040cd545401027b65500409b98854cc26d6215330c715143cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb30e350932cc23e64947308f59251cc29d64cc730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b3588438c23e6494a308f592528c32e5250a30cb549428c34e524ca30d3549328c38d424ca308fd91518c23c64546309bd89518c26c6254630a7992318c23d62d51308f992544c25f63551309b988544c26d62151308f994544c2ad6215130c758c544c32e62151308f588544c32d62151308b588544c25e6590d30c7152434c25c6550d30c7151434c23e64149308f590524c23e65d09308f197424c23e65509308f195424c31f54cc930c7153324c31f544c930c7151324c34f524c930e3509324c25e65cc530a7593314c31c54cc530b358b314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c31c63550308fd89540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c25d6510c30c7550430c2cd6210c308f992520c23d6494830cb952520c32d5494830cb992520c32d6494830cb951520c32d5454830cb991520c32d6454830d398d520c34f4354830d310d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c31e54cc830c7553320c34d52cc830c7951320c31d544c830d3949320c38d424c830cd952510c3355494430d994a510c3655294430cdd0a510c3354294430d5cca510c3553294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430cdd09510c3354254430d5cc9510c355325443097596310c29e648c430c7552310c34d528c430d5546310c31d540c430d3548310c355510c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030d3549300c355514c0309ed95300c25e63d53209758f54c832e62953209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20d398a53c831e5454f20c755153c823e6414f208f59053c831e53d0b20c754f42c82cd6390b20d354e42c831e5350b20c754d42c832e5450b20d354d42c
  | 3 => 0xa21d355132887c7614ca21f118532886ad64c8621b358f218863f64542218f191508865f63542219718d508872d4254221d34c9508865e63d51219758f544865e63951219758e544866d62951218f993534863d64d4d218f992534863d6494d219b58a534878d424c9218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540872e62950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992520863d64948219798e520865d63948218f597420871e53d0821c754f420866d6590821ab59242086cd6390821d354e42086e561908218fd95420871e5350821c754d420872e5450821d354d42086af6550821cbd95420872f5350821e394d420872d5350821e354d420870d535082197597320871e54cc821c7553320878d42cc8219b59632086ad648c821cb55232086cd638c821b9586320865f654c821c7951320871d544c821e3d09320878d424c821cb551320874e534c821b3d95320874f654c821d3d51320878e544c821d3551320878d544c821c3551320872d4294421d34ca51086ad64c8421b358f21087a54288421f14ca210866f65484219dd9521087a74248421f1cc9210873a5494021ce552500875a5394021d654e50087a94294021f24ca500873b4294021ce50a500875b3294021d64ca500872d4254021d34c9500873a5454021ce551500875a5354021d654d50087a94254021f24c9500873b4254021da90950087394254021da50950087294254021d6cc9500876a3254021d64c950087693254021d24c9500876b2154021dc88550087692154021dc485500865e6394b409758e52d032d52d0b40d394932d034d524cb40e350932d025e63947409758e51d029d63d0740ab58b41d02ad6210e409798e529025d6394a40cb949429032d5250a40d3949329034d524ca40e3509329025f63546409718d519026f62546409b189519029e63906409758b535026e6214d409b58853502cd6214d40d3988535025d6214d40d3588535024d6214d408f997435031c53d0d40c714d435025e63149409758c525031f53d0940c714f425031f5350940c714d425032f525094097997325025c65cc94097995325025c654c940e3509325023e65d0540a758f415031c53d0540ab58b415031c5350540c714e405025d6294c4097d89531023d6590c40c754e431031d5310c40ab588431025e63948409758e521034e5394840d354e521034e6394840d358e521034e5354840d354d521032e6454840d398d521034d6354840cb90d521032c4354840c794f421031d53d0840cb54b421031e
  | 4 => 0xb94942d065f65ccb419759732d074e52ccb41d354b32d065f654cb419759532d074e524cb41d354932d078d424cb419b98a539066d6294e41b358a539074e6294e419758a539074d6294e419358a539065f6254e41c794f439071e5350e419798e529065d6394a41c794f429071d53d0a41c794d429071d5350a41cb549429065f65cca4197597329065f654ca4197595329078d424ca41a758f419071e53d0641ab58b419063e6510d41ab588435065e63149419758c525072f5250941cb14942506b46150941d3d49325074c524c941e3509325069e63905419798c505065d63141419b988505066d62141418fd95431065e63948419758e521072d52d0841ad587421074e524c841d3549321078d424c841a758f41106ad62d04418fd954110677655044197d8d501065c63540419b98b54cc66d62d53318f58a54cc71c63553318fd8954cc66e62153319b58854cc71d54d0f31c755043cc6cd6210f318f99252cc63d6494b31cb95252cc72d5494b31cb99252cc72d6494b31cb95152cc72d5454b31cb99152cc72d6454b31d398d52cc74f4354b31d310d52cc63f65d0b318f59742cc72e52d0b31cb54b42cc63f6550b318f59542cc72e5250b31cb54942cc71e54ccb31c755332cc74d52ccb31c795132cc71d544cb31d394932cc78d424cb319b98a548c66d6295231ab58a548c71d6395231cb98a548c63d6295231cb58a548c62d62952318fd89548c71e5490e31c7951438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c71e54cca31c7553328c71e544ca31c7551328c74d524ca31e3509328c69d64cc631c7953318c6cd62cc6319758e544c66e62951319b58a544c65e65d0d3197994434c71d5410d31b3588434c63e64149318f590524c72f5250931cb149424c74f524c931d3149324c78d424c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c3197d95430c71c5450c318f992520c63d6494831cb949420c72d5250831d354b320c6d561cc831e3509320c63e64944318f592510c69d64cc431b358b310c65f654c4319dd95310c63f64540318f191500c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e53d0b21c754f42c871e5350b21c754d42c871e54ccb21c755332c871e544cb21c755132c878d424cb219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e21b358e428872f6550a21cb195428872f5350a21cb54d42887a76150a21e9185428878d42cca21ab592328878f424ca21e3509328874f654ca21d3195328874f544c
  | 5 => 0x50d0b4e6294e42c794f4290b1d53d0a42ab98a4350b1c5350d42ab9884350a9e6390942a758e4250a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050aad6294d42ad9865350ab56194d42abd895350b1d5314d42ab58f5250aae61d4942ab5835250a9e63d4542a758f5150a9e6394542a758e5150b355114542a7d8d5050a9c6354142add855050ab46154142a798c5050a9d6314142ad9845050ab56114142c794f4210b1d53d0842d354e4210a3f6550842c794d4210b1d53508429bd954210b2e5450842d354d4210a7661d53329d58754ccb1c5450f32c755043cca3e64947328f59251cca3f64543328f19150ccacd62d5332b598754ccad561d5332c755054ccacd6215332e3d8942cca9e64d4732a759351cca9e6494732a759251ccb555114732a7d9150cca9c6454332a799050cca9d6414332b598450ccad56114332cb98a548cb2e5450a32abd95428cb2f6550a32c7953328cb1d54cca32cb50a518cb2d42542329d986544ca75619513297997434cace62d0d3297195434cb1c5450d32c7550434cace6210d32ab592424cace63909329b195424cb8f4350932e390d424cb8d4350932e310d424cb2f6550932cb195424cb8f6350932e318d424ca9e648c932a7592324cb8d428c9328f993514ca3d64d4532cb508514cb2d42d41328f990504ca3d64141329d984504ca756114132b358a544cad66195132b5586544cacf6255132c7550544cacd64d4932b3987524cacd60d4932e3d4b424ca5e6590932a7592424cace6590932d3996424cacd6490932a3592424cace6190932b3582424cb8f6250932e3d49424cace6550932b3195424cb8f6450932e3d51424cb8c5450932b3185424cacf6050932e3d95424cb8e6550932e3595424cb8c6550932e3d85424cb8e6150932e3585424cb8c6150932e3d81424cb8e6050932e3581424cb8c605093297994424ca9e6410932b3988424cb8d4210932a7993514ca9d64d4532e350b514ca9e6494532a7592514cb8d4294532e3509514cb8d4214532d5544514cb8d42d4132e350a504ca9f6454132a7191504cb8d4254132b5d85504cad46154132a7990504ca9d6414132e3508504cad66114132b5584504ca5e63d50328f596540ca3e64150329798c540ca6e62150328f992520ca3d64948328f597420cb1e53d08328fd95420cb1e5350832cb949420cb1e54cc832c7553320cb2d548c83297d95320cb1e544c832c7551320cb8d424c8329bd95320cb2d544c832d394d320ca5d6294f4197d8953d071d5390f41c754c43d06ad6210f419798e52d065d6394b41d394e52d074d5394b41d398e52d074d6394b41d394d52d074d5354b41cb99152d074e6354b41d358d52d072e4354b41cb10d52d071e53d0b41c754f42d072d52d0b41c794d42d071d5350b41c
  | 6 => 0x2a0001239b98001231d40d982080006100022000027a8b48f724c2360a19091d1a34a2d8c30ac19b8e21591389a9a1ca9b0319c0900a1503400014782300028528106d1749498170a40000c90dc14fa7d9868fb23583d12988916d0fe8302238479322552370001e0134800244109a91a1029400000025e1f100003324093ea6397b13e1d82989870370b20ea25ba20a7000010824917d23a85e9111e7097a571c598a9730000aa9fe9f4a1d21d9ee853052102029a8c0c39341b915000100203401c000290160080200e0b80000001c0180041200300c04001000000044008000020b00401e004000010080160001400101c05401811004014000060040040000100c0000c03000209c00004004000070120060040000208600c0000000602c000060000000080a002028030060200101500900a000000670120100d80404402c0980500201c0600202201c0e80500008800002004014008000201000a80c000004220150060000f8000000001100000200000007000058010000400000280000207c0180100c0c4008000020100486d01a2840400400a034000000020180682103e0340b003022018010000000340000a00a03808804000004030000180e00900202a0180480101a02c0b00703a00415800008008008000080040b000040020000000000000b005000050000000000100d8020040400380000a010000170000081080401e0240000000e014018030000340880300003c0301100006000014008004050000040040180100000403802000014000120040080080c0160000400701c0000480003603802802000000008020000000000203c0440180205a0140280f0040080180400001c030040100040b818000020218000060540080f008000038100140b001000018014040050100000081c00200c030000160481280203e0000d00600000c008290020240206400000010000004014010030000481280b0000180000301400400815000004178160080340081504201c1404f01a0340700c00a01c0000206e00400004028020000000020040500700001801004008004000050040280500502c0000c80200402c010020100280381b0060780100100e010030039b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a7d854310e9c6050c43e350e5210f1d4354843e350d5210f2e6454843d398d5210f2f4354843d390d5210f2d4354843d350d5210f0d4354843c750e5110f1d4354043c754c43d0a5e63947429758e51d0a5f63543429718d50d0aad62d4f42ad98753d0ab561d4f42c754c53d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9f6354342a718d50d0a9e6314342a758c50d0ab66114342ad584
  | 7 => 0x80003a8b11308d225c0271c18f4295036a2822e80005694015aa1a94413523d871a538119c50001f221400000018b96a29396da8f00b2169408000f00ed00014d0000001d913100011a983043a110000e915123d21b0000000000000000af00020108f22b075000209a160e02488509618001572410701cea801e693b19e874a3ca2a12188ca8b11488d26f8811118f3a1599c85803b06205724e8c215609e89b148a2c8bfa9d8cb8670399ad0ef08520da55a680818489d8a090781e58ae02820794e8dda1ba3e2710002829b389c069a0b80001e02e8ca98c9eb0cc1700961861651cb12f1960ba1491131d98548b28ba9a39da1dd9b5a0d24583c12ea67076a3a18095f000000257a2a86f13812f9188000159af9200880740000420981f32321a69251d480a8d3a8d1b0214a2180000000020c14a9339b8957a7090b84318487f0261ae81f0bc937a4487894b00e00010f8931bc00020812827484b809a68a17a0e24702c0bb89101ca2b82c85114c91d21f0351b128d97405781b8002868198970da055092a7e0558b40239898872758c9a0b084a6797803e890a072530e500f2928bf2900eb2009a41e2a791cf03781e8bc11a0bd8b817729c88b80e99722c14122622424616f2171529cc0d4971a602398a49d09c90b8a1988000d1709ae0c70f804d0739ef19e0fca78a9a80001a8f922680000020498e06280015e8338a09be0f782790d8001621e48001691290500608000d78000001609ea80011c8002389811670fba9812e23016e8dc84587d8d00e40998b617c26e01c12d8002391ce14d8140fa8efa1c0f184c8e1003a468150a020aa8a0f681a2451c72339ba97e80486624007991d9931041901928050ca2129de00014c16f997a6284984119192297907b9e18000000000320869f72431e50a29aa0de8b329a1000e808a08f80026400da3080000007a80000010380000004ea5610e8b01ac13580009a82d07c87e0000fe00004280027800000016280000323818fa738001032369f880028ba742540001468791422499948fd82ba510131268228b78001a520e90f04a0002508121b224799884b1c01ed97e18280024d0e280000000000026493900000000026b9c8800000000131925a81a6c00000b834a08a63205a5a290a3786e1faa6d94a1dc105a97a480d91f814800019c2881419e79d61838e48001a60000000000000a680110b05a81d25224187b0001089078000e98000f48b682488e1bc8ce8b19a28a800011380702000000028e9f91060001128000000000000000000138808000710000001ac8000310e58da8d2800098a1e058906a420000ec87d00023113a00000000000018d00000021300006e8d180003b953a0a1ff29900006f8001300000001e80002271f98000d31dc9548001cd8000001c4000128a5c80c80
  | 8 => 0x6811209a0168d1007a92276a661f093a9788b906505fa31829120998030a3b0fa179a580101ec0d71519d6a2509f9fb04d8f21bb1c20e6213a221921990ad83e00681800095e1191070590df1508f989f190a7984490a1460aba668d808209ca7ea6111411682b142a5f27f03c835a2125895b83921e89180884a85c9c99180a22548111739ed1e097a88e85d06787f90ca0296a95f92c22f9050bd08424f29712223317f1b4840a4b87086c8ea9639de968299a5f8000000002229e39530001f780014f0001e606c05e0000aa1f407297c844119a1a2350c60c18858000d41728b38109ea1b602d8081958bea1180013628a81491095404726593f0e32968b09c680000001d85d98ea278328949241602591f00000df9598951fe14380017d8000cf1d000000000006a9d700020fa2480004915500028780024c8001e900003813d0941ff8000001938f50561649a019f8a30eda2f2328eba8c9fc19a06191e98f10186398a2000190d6896a690e70fd0b58a709219f06b0ee89d0898002192808862650db02215b1a71d204e06d9b80000400000001d10ee12a800271a8f9c28a51760000000000001a30000000000000000001bd91fa022728a980000000000180011f0c2a6c8830000000020001b086b9e89fda019db0cc9659632621caa949c106480005f10d1cba6d0000210d615818b2821170aca7d00019d0000be01615a1f384f03f12a06893d84811c1bb9b7a5da3e80c0001f181fa2e11616e27780000021f8e19b29470c80c00001559df06699b1331fc8001c788c2931a096b10c0000e88cd8001c49a8000185059a3418408d80fa6a0000b500000025d1bd13ca838000000000ae8720000000001372518001e2077a030000000ff1a480005a261a2980002e1779b50cf8c79f28c49398d51679459642761750f8a068040f10000a600011ba25800176800291000024210a4a00000012b8001b6883825196800046a500002889ab0a7a8601b27f8d098d991075a4380000024e1ec87614491580026a981a7700012b1f50ab1d79d2a0c8991fa1880f58ce23f06a0361b300000003f97a26b00595d9db9248e39ca028a7204505c1fba7b24fa8580019a9a11b728489005383a175a3c27c23ba062698c416892c9f61d30dd1c39260cd00a11e04c19994b9a59a886424a92d19d98216695ca9d0f62428258e69100f30269af1d59da9b18691951e40fc06029595215c10e0e7a231369ab9c609d84f9c310a92107e83880007717f80015688b1b42899800658001eb9888001a20001179a92568000001271450000000c593f80014e16b87c0001bea5e8060c080015d1ef80018c0001c800029612782f0000002529941ba0000730001cca750a102fa1800029b8000000461bf9ee1660528c51e30b99cd25aa052870ec1011ad8888000028d8
  | 9 => 0x143018a291720c691510496c132a6e85b89388280007a0000e0a831d51699bf00925989e00013c16c9a198900027b96113b9dd2038000178a38001e12730218001aa85b28e0db91b25b0a90cb0540bb20f0001710d581286300027a0af80017b8000001e98001cfa7c9f69d38b72042840001a785184180003d9df80009b9f580024da3f8f0a60895a18a9c0c115880008a80022d26f185a4b0c882aa289fd2121028ff8a5a890a88de0878ad1878f28
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x98e0d6358a548c70739ac52a463835cd6295231a1ae52a48718d0d72951438c686b94a999463435ca544ca31a1aeaa126518c1d76953318c686b94a998c638395162cc631c1aa8b108698d0d74149324c742a10c299263235ca648c531a1ae42a28618d1970151430c616b90c8a8063435cf6550a21a1ae9b2a6510e0f635095088707b2264a8443135ca63d512185ae5326a690d2970d4d4208686baca6a10438359542cc821a1aeba126410d4970d513208686baca899043c254d4294021e12a8994a010f09424ca5008695baa84a8043c294d4254021e12a6a12a010d4b754c950087852a264a8043c25513254021a92e7212a010d61719095008784a1664a80434a5d23254021ac2e3192a010f0b424c95008784a1264a80434a5d32154021a92e790aa010f214288550087a099442a8043c8d092154021e866490aa010c4d7298e51d0286b9ca4a1481235ca6390640c1ce8b10a6a060d745885350286b90a7a1a81435c85350d40a1ae429e84a050d7214d425030732a8499281435c853d0540c18a6b1682a050d7214d4150286b90a7202818354d6210c40a1ae529a842050d739494210307b2a8499081c15093294440a4ae421aa220705424c95110246b94c7208818398d5290440c2cc6a8c822048d7218d401030631aa4a00818518d5150040a1ae42a2879842d7299251cc307aa2c421c61435d2524ca3091ae5324631860d63588544c30739ac42a261835cd6215130a1ae42a4869850d72151434c286b90a999261435c8544c930a1ceaa12649841d76153314c286b90a998a618315162cc530a1ae42a2629850d72152304c286b90c6aa061835516210c30a1ae52a2641850d74949320c287baa8499061c15093294430a8ae421aa218705424c9510c246b94c91886107dd9548c430c1cc8a94621861664546310c246b90c898061071d9544c030c18c8a92601861464545300c286b98caa12410b1d95350920a48e2a9a84905a1711814248286ba0ca99241131d9544c920a88e2aa264905c1711813248306b1a8428a41835913214520a1ae7292841050d725513208286ba4a49904143dd5424c820c1ecaa126410705424ca5108382a1264a88418a5516008420c92a6b00421044d7298f54c4216b94c9a9e21435cc5250b10a1ae8292658844d7218d5484216b90c8a9c21435ce5250a10a1ae9292650860f64d8f5244306b22c6292218a5916014910c92c6b00a488661615805244286b90a6a1221435cc5250910a1ae42a2648850d7414932442873aa8499221431d5424c910c1ccaa12648860c6550932442923aa8510a21511d53288510c50caa124088648654c92044306b22c729021835916354810a1ae529a840850d739494204286b94a899021435d2524c810a1eeaa12640850d755093204307b2a849902183595424c810
  | 1 => 0xd7000000019541e00000001d40012000000000000000c910000000006e800006c67000006e1f8dc1e7c24800a0000000000000036822ae1cb814200239900000000d0ceb200000000040b513cac5c320005a0034d84212b001348e3111820000b8000000001654e4c46894e04f001ac740a2f0000000002b47883630c400000000000bf2280120a567b5800000000000000032d04002100000b52d801a2006d80006c154b54fe00001d800000000000440031d2800002f89a8568001780000000482e4ab6034004980000004e2219200000c800842e800006a30225b2000001d607a00001c46d5a0016e35000000020000b02a96621a0000000291000000000e4221994400002e28816054c801a463490595e41020d8003e0f0000097662a9142300000563b07000fc00458505a28002e838c015000000000000000000000fa004f9e400006e000009d00000e23d4398480e3099d086b339aad308f34800b0bb13034f600180a410482b9ddbc6f0029936b1139296ce14314cbe2f0fb28aa525e8609ca000824186525b1546c3668e03a1b0123172546f800cc00008060300014040200804000102000043e0b82806000403800000d0200c0d078000a020080400031c8001200008000a0304844000002800020102800120800008040000814060002000000000004000101030000191ae5b0a8621c8d721814310e4ab88c0a188743dc94354843a1eeaa1aa421d25719915210ea2b8cc6a908743dd94354843a1ee2a1aa421d0c7050d5210e8bb8a87288878354d6214f4291ae730ea4a148f735835250b06aa2c42a665831954350932a4ce3b2a849948d74987524ca47ba2c1a9265319c66550932b0ce3b2a849958571d95424cac338ccaa1265615c66550932c1aca32a849950e75d85424cb42b08c2a126561dc56050932b08e2b02849950e75181424cac3388c0a1265615c4605093291eeca16a29970542544514cb42a16c2a8265a1508615413291eeca10a09968542984504cb42a12c2282658354d6210f41a1ae529a85a0d0d7394942d0707b2a8499683839d16294e41c1ae8b14a720d0d7294f4390686b94a6a1c83435ca53d0a41a1ae529a8520e0d655093290686b94a7a0c838394d62d0641a1ae629284a0d84715093250646b94c720a83135c86354041a1ae431aa998e0d5458843cc686b94a899663435d2524cb31a1eeaa1265
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2b0000638c854304968142804190581dd94354843905811c14354843a05819d16294e41a05819cd629523180d8795162cc631a05819d16214d40a058298d5190440a058218d5150040a05819cd621513080d8715162cc53080d87991528c430a0582991518c43080d87191524c030a0582191514c030
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
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
  | 5 => packedAt s4K5 (27286+((h/296+packedAt s4K5 (24030+(h % 296)*11) 11) % 1421)*11) 11
  | 4 => packedAt s4K4 (55826+((h/446+packedAt s4K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s4K3 (11856+((h/76+packedAt s4K3 (11172+(h % 76)*9) 9) % 364)*9) 9
  | 2 => packedAt s4K2 (860+((h/4+packedAt s4K2 (840+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f83f0fc3ffe1fff83f44f3cf
  | 1 => 0x3fe1e1ff0f0ff87fc7f0fc387e1c3fc7bb4d33
  | 2 => 0x3ffe01fff00fff8ff800ffc07fe03ff8c38e3c
  | 3 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2000010000008000001004800240800001045
  | 1 => 0x84484222241500814310441122089286194512
  | 2 => 0x2884954442aa441a9888aa8255412530c28a28
  | 3 => 0xa1d55988aa83552cedaa220479938192ec0f80
  | 5 => 0x3119910ecccc664f36ccf32711020624f7e000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8eeeaeeeaeae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37115
namespace PEqualNP.Outside.L_meta_37115
open PEqualNP.Outside.L_meta_37115.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x36785031e9cc23004008e0058ba9267d30d34001064a009280010a2a4800e1522010800a21580122d1004074c8c0e04000609d00c04d140080ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x8817e52102faa4205f94440bea88817e501037e80207e90040dea0081f940102fea9986fd53309faa6617e54cc2faa9985f15330de2a6613c54cc37c87986f10f30bf296617d52cc3be6598774cb30bf28e617d51cc3be6398774c730dfa0661bd40cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa71877d0e30df21c61bc438c3b887186710e30bf294617d528c2fca3185f54630bf28461bf408c37a811877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261be434c37886985fd4930be29261df324c3ba64985fd4530be28a61df314c3ba62986fd0130dea0261fb304c3bc60985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30efa1861be430c37886187710c30ce218617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa88617e500c37e80186f50030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20df21e41bc43c83dc65907b4cb20bf28e417d51c83de43907b48720dfa0641bd40c82fea9105f95220df2a4413e54882faa9106f552209eaa4417c54882fea7105f94e20bea9c417c538837c87106f10e20bea94417e51882faa3105f94220dfa0441bd40883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20df21a41bc43483dc64907b4c920bfa8a417c51483de42907b48520dfa0241bd40483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20df21841bc43082fca4105f94420fb288417651082faa2107d54420baa88417e500837e80106f50020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10df21e21bc43c42fea5885f94b10bea96217c52c43ec63887d4c710fb10e21f521c437e81886f50310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53842faa7085f14e10df21c21bc43842fea5085f94a10bea94217c52842faa3085f94210dfa0421bd40843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c534437c86886f10d10bfa92217e52442faa4885f14910fb18a21f531443ec42887d48510dfa0221bd40443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437c86086f10c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e500437e80086f50010fb88021fa10043ea20087e44010
  | 1 => 0xd53906baa720ef90e41de21c837e52906faa520ef90a41de214837e519077e8320fdd0641bf284837d50906fea6a0df14d41df21a83bc43506fea4a0df14941dfa1283bd42507ee82a0ef90541bfa82837c50506fca820df94c41bea9883be43107788620df94841bea9083be42107788420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798ef90f31de21e63dc43cc7388798df94b31bea9663df32cc7ba6598df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77c8718ef10e31bf294637d528c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898f7d0d31df21a63bc434c7b88698e710d31bfa92637c524c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863be430c7788618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21df21e43bc43c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21df21c43bc43886faa510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21df21a43bc43487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c530877c8610ef10c21bf290437e51087de4210fd88421f690843f521087ca4210df94021fd280437a50086faa010fe54021bca80437e53d02faa7a06fd0f40df21e81bd43d037887a05f94b40bea9681bf42d037c85a06f50b40de216817e51d02faa3a06fd0740df20e81bd41d037883a06fd4f40df29e813e53d037aa7a06f14f40dfa9681be52d037aa5a06f14b40df99681be32d037a65a06f0cb40dfa8e81be51d037aa3a06f14740df98e81be31d037a63a06f0c740df90e81be21d037a43a06f08740beaa4813d54902fca7205f54e40df21c81bc43902fca5205f54a40bf28c817d51902fca1206fd0240fda04817f53503bea6a057d4d40be29a81dc53502b8a6a06fd0d40df21a81bd435037886a05fd4940be29281bf425037c84a06f50940de212817f51502f8a2a06fd0540df20a81bd415037882a07ed0140df20281bf535033ea6a06f94d40dea9a81bc5350278a6a06714d408e29a81bf525037ca4a06f54940de29281bf325037c64a06f4c940de19281bf515037ca2a06f54540de28a81bf315037c62a06f4c540de18a81bf215037c42a06f48540de10a81bf5050376a0a05f950409f2a0817e53102faa6206f90c40de21
  | 2 => 0x20000180100000000800004000018000040000000000e00c0000a004000008050080000500400a0000100601c014000000020000000100e018000020140040300000a008010010080040180700c01000801000000000000020000200200000400000000004000040000100100100c008008010020040280000e004008060020380080c002000008040200080000700a014000010000040000300c01400000000000000040040080200000400c02803006004008020060000080000400c000020040000000100c004000040000000180000202000804004008060090060000180300a01800000008000000090020040080000c03c0000500601c0080000000001003004000000070020100100001000001002004010028000000000080e00600400804006000000000000000000300a0800080000201400002000000000000000000000300000c00002000000020160000040000300800403801000000018010000000180000400400000002002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090e7ca721efd4a43df29487bd5290f78a521efd4643df28c87bd5190f78a321efd4243df28487bd5090e7aa121ef14243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043df298873e5310f3ca621efd4843df29087bd5210f78a421efd4443df28887bd5110f78a221efd4043df28087bd5010e7aa021ef14043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7c86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65be43ccb7887997710f32ce21e657e51ccafaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cb7c87196f10e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a89977d0d32df21a65bc434cbb886996710d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6196f90c32de218657e520cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cafca7a0df54f41df21e83bc43d06fca5a0df54b41dfa1683bd42d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83d
  | 3 => 0xe0000003013c878e48c528237c5c000000000d4000000c700000047a0011524e1680013b0e40000013eb13008001879e20000000000025c000001bc000099778470006ac000000f243c0002b000a1c000003c271c479560001540000030e0016c832402ad0cc22700082573800000001311095281ac0022b110000b19654083580000000000000000078000000000000243e8006323756392a5048bce60003d40cd068005e227c0000046e000001a62be000000004be000000004185a8000000ee8e0000005987b4ff8ab00026d2880510c4f827a97000565082db0004900021700012c0000004ea04a514f000208491fa3c80000012357c3b40019200000176265154508858001cc2c0000000001a0000004e4ae4cf9d60463f0f983b000a8800249618264001bd62c22888800000058000000008a000000000000ca87b0000000000005e158d70c73e29cc000740004318815b4f4000b483700000000000000000f300004a8f0000002de820000004981c400167000000e52eb0005fcd114b0002d800000000000000005240010b000000000000000c27f508a4a000000e200057a4e8621e800000000000044000000dc0be12145aaa1826fd6289d00002c00000000a9895800000000459e9262a5568a07050210fb04d000778000003a0000512050000000019700070cf6206026070990001c607c001b755ca58f00a51ee6b0ff0000005b881000000000250ae0ba87c68966088c740008d0000000007a0227345d2d2000061348ca376ae0001f7000000002563dcb293f91800010c189280005ec00000000340dd000000000d8000000000d0a4f60c3fd3702d000148a88001dc3340020a000000000b2000b68618005000018d800000000a68005300009b87f31c0000000017c000691052a045c00024010000002b500091400000000000e000049a4f00000057e000001a4000000000004ea3ed2c0000000006c0000005140000000000144800560000000005a603000244460bd86028c2da3c4840365fe6a5340000000000a8000000018f80059ab8d700001e838430222000b04e0afd2e4000000030000018d000166c780000048036c000eb566530001c509800073a7712673d8b9b44005e000255606308760000581380300007224469ade2a6b2cbe8002063187aa9a5e451c002ba5869905a800000000a90004da0001c1d9000000c3050000000002670c850c07800000000bb9ad0000007116b0004fc75000000000000000002704d2fb000000000002088f94800154a000781e700000000000564a148c99b37cbd0000193b4ba4000bd0007ac000850002805b800000000000e829035c000000000012db0b0000000000a00000000321000000000002d80000000044c2b0002192720000000036c00039000000000a011634a9b11daa00000
  | 4 => 0x5b803944196000000001574420009a22029c610ba9aa0de000002710008d40000000091c0011c0b62fc000000000000019c000000af000438000000006228c89028a3a6000002250000000900055e000000bb0003cc00000000000000000000000029d000448000000000012d0000008e8910a81724f4000172ec4b00000000000167a15000c20d89062f48d8000000006058500051c000001a30008cd208003a8001058005aeb50c9aa1608a100000000ea6c44a790a27f06c9f2532c354898f0004547c9ef60e0007ea542ba86c001cb5eec044c2183ae0d4aa80000000000000370669098780003bc00000000a0c670000000004a2d50dc000000c84d4bc03380000044cf1800196000000002920000017e2c4aa0931b353c4cc000f21f425c20000000000000002e2104000af10e9ec1011f03a050ac1733e064097800000000000e90007440011e00000000263446b6112000624468000000000000000061200000000000ad87f1995f49e15580019eac40000037200000127322000e40000b09d000000000000660004a4000c69c200000000000000324230965e61256b00000020c00000000c0121ae650c0010a2df0000014f99e000000000000009c0e330e2c29bc00000000000329d50e67ed7c0000a60f80001a1ec650002ad000000000003b692000000288000001885f200038160000568000e000018c001380000010d28f4b8b8490ac22e0ba8151b500000125800252a9c3b00d546a7000000146001903181f00000000059259117000558b200025021406d232dd03c7e57e229000b381a02e5800003e000000000001545261b0801a7548c14f289023a18907234000000000000000000008c0000000021d33abb88083f0008c4402663b84500000030a4ec881f4364000000000000000000000080cd7a610005e5012e85c8000c18000b400000000300204002f50744d8470004720010900057841d8a8a9000908ee8575a0b18e912d316680000000d2000002ed000000000004bc95c000d43ea298000003129f000000000000000660000006d0003f00f4368000000000017400000000000000980000000bcc084aa2c56eaa5299ce588b946f000000009358000000012c8002f80011fa0f000000000000000000004545a000000590001f82a00030477c000000002f010a5d0522b4b414626a570520005fc2c43aae20000006a800000284000e50001088da7e0004c0c50000001a82e000000000c61d800049408000000c5146abb21c0008680014
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1530831c6454c208f990530823d6414c209798c530826e6214c209d98453082756114c208fd96430823d6590c20c794e430831d5390c208fd94430823d6510c20c794c430831d5310c20cd95251083355494420d594e51083555394420cd90e51083344394420cd95151083355454420d594d51083555354420cd90d510833443544208f992500823d64940208f597400831e53d0020c754f400833651d0020cd547400823f6550020a718d400831e5350020c754d40083365150020cd545400834d53c8020d9547200837151880209bd95200834d5348020d954520083a940480209ed95200837151480209798f54c425d63d53108f99353c423d64d4f108fd9153c423c6454f10c794c43c431d5310f108fd9152c423c6454b108f99052c423d6414b109798c52c425d6314b10e510d31c43645248710a718d40c423e639521097d8d548425c6355210a718d548431f63552108f18d548431c63552108718d548423e64d4e108f593538423f6454e108f191538423e6414e108f590538426e6214e109b588538423f6590e108f596438423f6510e108f594438431f5310e10c714c43842b96010e108f993528423d64d4a108f990528423d6414a109798c528425d6314a10a718d408425f63551109718d544426f62551109b189544423e64d4d108f593534423f6454d108f191534426f6254d109b189534431f5310d10c714c43442b96010d108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109d1953144394434c510bc18131442746548510d9149214429c63501109e19520443e121481109798f540425d63d50109b98b540426d62d50108f596540423e63950108f18d540423f60550108f581540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431f6494c10c7192530423f6454c108f191530431e5454c10c7551530431f6454c10c7191530423e6414c108f590530425e6314c109b988530426d6214c109d984530423f6590c108f596430431e5390c10c754e430423f6510c108f594430431e5310c10c754c430423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb90e520432c4394810cb951520432d5454810d394d520434d5354810cb90d520432c43548108f990520423d64148109798c520425d63148109b988520427661148109e980520423e64940108f592500423d65d0010c794f400431d53d0010cb94b400432d52d00108fd95400429c6350010c794d400431d5350010cb949400432d5250010d554f100436552c40109e596100436952840109dd9510043555344010d954910043b140440109ed9510043695244010
  | 1 => 0x27b6550040ce951401031e63d5330ce58354cc31e6315330ce58054cc2b96090f30ae58043cc23e6494b308f59252cc23f6454b308f19152cc31c54ccb30c715132cc23e64947308f59251cc23f64547308f19151cc31c54cc730c715131cc29e63d0330a718d40cc31f6355230c7550438c29d6510e30c7594438c29d6010e30c710d528c31c4354630a718d408c29c64cc2308f992544c25f63551308f994544c23e63151308f18c544c23e6590d308f994434c31c54cc930c7151324c31c54cc530c7151314c23e65d0130a798f404c23c6550130a718d404c31c548c1309b98b540c26d62d50309d987540c27561d50308f596540c31c63550308f990540c26e62150309b588540c27661150309d584540c31d54d0c308fd96430c23d6590c30a798e430c2b96090c308fd94430c23d6510c30ae580430c25d6510c30b6580430c31e6510c30c7594430c21d6510c30e6980430c29d6010c30e6580430c2996010c30cb952520c32d5494830e310e520c32e4394830cb10e520c31c4354830cb951520c32d5454830e310d520c34f4354830cb90d520c32c4354830d310d520c30c4354830cd952510c3355494430e510e510c3665294430d954a510c3364394430cd10e510c31c4354430cd951510c3355454430e510d510c3665254430d9549510c3574354430cd90d510c3344354430d510d510c31443544308f992500c23d6494030c710e500c23d65d0030cb94b400c32d52d0030cd947400c33551d00308fd95400c29c6350030cb949400c32d5250030cd945400c3355150030a7193300c34d52cc030d5547300c398438c03097d95300c29c644c030d3549300c355514c030e6501300c27b654c030e690d300c25e63d53209758f54c823e64d4f208f59353c823f6454f208f19153c831e5310f20c754c43c838c434cb208fd9151c823c6454720a718d40c823e639522097d8d548825c6355220a718d548831f63552208f18d548831c63552208718d548823e64d4e208f593538823f6454e208f191538823e6414e208f59053882766114e209d584538823f6590e208f596438823f6510e208f594438831f5310e20c714c43882b96010e20a718d408825f63551209718d544827761551209d185544823e64d4d208f593534823f6454d208f19153482776154d209d185534831f5310d20c714c43482b96010d209b195324838c434c920ba181324823e64145208f590514825e63145209758c51483645148520a718d404825e63d50209758f540827661d50209d587540823d65950208f98e540823c63550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7d92530831c6494c208fd91530823c6454c20c7951530831d5454c20c7d9
  | 2 => 0x65950218f98e540863d60950218f18d540863f60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7d92530871c6494c218fd91530863c6454c21c7951530871d5454c21c7d91530871c6454c218f990530863d6414c219798c530867a6014c219e580530863f6590c218f596430871e5390c21c754e430863f6510c218f594430871e5310c21c754c43086e562884219bd9521086776548421b9d9521087676548421e9d9121087a46448421e995121087a55448421f194d21087c55348421e990d21087a443484218f992500863d6494021ce95250087395494021d694e50087595394021f8486500873a6494021ce592500873a4394021ce10e50087652154021ce95150087395454021d694d50087595354021f8485500873a6454021ce591500873a4354021ce10d500876b2154021dc88550087692154021dc48550087612154021c794c43d031d5310f409798e52d025d6394b40a798e42d029d6390b409798e51d025d6394740a798e41d029d6390740ae58353d031d5314f40ae58053d02b960d4b40a798e52d029d6394b40ae58052d023e658cb408f59632d023f654cb408f19532d02b960d4740a798e51d029d6394740ae58051d023e658c7408f59631d023f654c7408f19531d023f65487408f19521d023e65087408f59421d029e6308740a758c21d03a52108740ae98021d02b96008740c794e439031f6414d408f997435031c53d0d40c714e435031c5350d40c7d4c435031c53d0940a798e425029d6390940c714e425031c5350940c714c425031c53d0540a798e415029d6390540c714e415031c5350540c714c415031c5390140a798e53502b96094d40aed81535031d5314d40a7994535031e6514d40c7d88535031e6214d40c7588535031c6214d40c7d84535031e6114d40c7584535031c6114d40c7d80535031d6014d40c714f525029e6394940a758e525031c5394940ae582525029f6354940a718d525031c5354940add8552502b46154940aed81525031c5314940c714f325023e658c9408f596325031c538c9408fd95325023c654c940c714d325031c530c940ae98032502b9600c940c714f515029e6394540a758e515031c5394540ae582515029f6354540a718d515031c5354540abd8951502ac6254540aed81515031c5314540c714f315023e658c5408f596315031c538c5408fd95315023c654c540c714d315031c530c540ae98031502b9600c540c714f215031c53885408fd95215023c6548540c714d215023e65085408f594215029e6308540a758c215031c5308540e948421502ba6008540ae580215031f53d4140c714f505039b53d4140e614f505023d6590c40c794c431023f6550040a718d401
  | 3 => 0x843ab9885110ead6214443cd5445110eba6014443ae5805110eae6214043ab5885010eb66114043ad5845010f1e5310f429798e51d0a5d6394742c7d925390b1e5390e42c754c4390b1e53d0a42c714e4350aae6290d42a798e4250b1e5310c42c754c4310aad6210c428fd954210a6f65508429d98754cca7561d5332c799443ccb1d6510f32e398843ccb8d6210f32a758043cca3e64947328f59251ccb1c43547328f99250cca3d6494332c710e50cca3d60952328fd81548cb1e54cca328f992508ca3d6494232c758f544ca3d60d51328f992544ca3e65151328f580544ca5e65d0d32b398b434ca3e6590d32a798e434ca3e6510d32c7d50434ca9e6510d32c7994434ca9d6010d32e310f324ca9e648c932c710f514ca3e64141328f590504cb1c43141329d984504ca7561141329798f540ca7661150329d584540ca7a60150329e580540cb1e5310c328f992520ca3d649483297d95320ca6f654c832e390d320ca3f64544328f191510ca3e64940328f592500cb1e5310f419798e52d065d6394b41c7d92539071e5390e41c754c439069e6390a41c794e429071e5310a41c794f419071c5390d41ad986435063e65d0941a798e415071e5310c41c754c43106b56110c418f596421069e63908418fd95411067765504419b98b54cc66d62d5331c799443cc71d6510f31e598443cc7956110f31a758043cc63e6494b318f59252cc71c4354b31a719132cc63e64943318f59250cc71c43943318f582548c63f6055231c7953318c63e64942318f592508c71d63d51318f583544c63e64951318f994544c63d601513197997434c6d661d0d318f996434c69e6390d318f994434c71f5410d31a7994434c71e6510d31a7580434c71c43d4931c7153324c69c644c931c7151324c74c524c931b5185324c79443cc531a7992314c63e64141318f590504c71c43141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c71e5310c318fd91520c63c64548318f992510c63d649443197d95310c677654c431e590d310c63e64940318f592500c65e63d53219758f54c863e64d4f218f59353c863f6454f218f19153c871e5310f21c754c43c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863f6454e218f191538871e5310e21c754c438863e64942218f592508865e63d51219758f544869e63d51218f98f544871e63d51218798f544871d63d51218f583544863e64951218f994544863e63151218f580544863e64d4d218f593534863e6494d218f592534863f6454d218f191534867b6054d219e181534863e6590d218f196434863e6510d218f194434871e5310d21c754c434863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d
  | 4 => 0x86eb694f80013830b2700010802068c8540033c2a449c0000027a00101800000128611c845e7099b8000c2000002c60ee9240022051c000161620004acb809d0002cc2c0006ced618512a64e3800020152800000000012000000001f0b80e826b2ee4607633132c0017c22a0006c47a0001a44b0290d914c0b5a9000000c3d1916f534914fd033508c191bb531b60118114f1d4c7d0a21749a179020a10006349203d45c89d75b700005ace01865820d85d9ff3567042a800000269af06a3ce781950c13f04304200004a0013680000092ca6a9f4c8000001be000d709d97458e62d9604b66a239a02ea6c49e46a1a711ad4473b505b86819208f2f82d10eafa4c00e1401f7116ab4668955a2ac49116357c5a8da23f622845891ec3068e111b6a6440540686d38e984f0915292b6c002432624bd658000ea1d0001dd000170231a93a89580e8c552ec70e7125114cfcd81135fec585515e140bf99b008162b8d6c88931e6412880022c4d80012827c9a16005d2806647930757478d2936d08ed38c49ee64c4855434c0fa1c88301f31c7784185445a3d821800006001538003780000033b000000001001b40009ca3e000000000000007580000000032d500000000708d8002820000000064200000000032001408a9696001390af00077c000004f4219b6158000558358640009fd1632e00043c778000003996a1c946091c0026c4fa001388cf1460000400000c0060140280700400407001034030038040260140001f008000020010060000480201c0000080500a004008150000140000000203c10800000014000030161180b8020121040000000c004020000020000180b02e00c02803012068020010000280380000a0ac0100200800c008020140480400200406c0a80003c0040d0000100000200a03e000128000080000f0010000040402700003400005028004000030080e00300201e0380000c00001000004002000048060020000100001a00c0000200201c0180e03800000002000004010010000000100100400400800002010010050041380180000200c050010000140100e000010018020020000981a000000000020120000000202a0000100900e004040010020040001a00001c0000001c000028020000000a00602800004802008004040060120000080000002c000010081280301200e00c010000000000400102800805009012014028000100000000301a000020000020800080100e028018030120000180600200c0c800004024000000000000000700200000000008046b661d4a43ad5875290f2f5294a43ab98b5190ead62d4643cdd465190eae6214243ab5885090eb66114243ad5845090e3f6550c4397d954310f1e6394c43a758a5310e9d6194c43a79825310f2d5214843ad9845210eb56114843ae9805210eb96014
  | 5 => 0x54c889b91becc97631b39abdd6bb094ec29d098ba364bc9968795ead0c84a7e2ecc68de8004be1ed012c81fc76d0f09e3fcccd5b9d13a63907fa8329c0b9b31bf4821b09681340abc056af362a29415103000000002c55b48680000021a3cc3300034a5c55724a5140007580025c264a8000278114808012641101a87f59468d2f29d4840515a8a40187a8fda5c000c20a504051e498070a8334d05899cb4ce42c8d2f43ea068b412310aa418b8d716eb99aa0000009cc412fc586960b717f0600010c0880b4b954898c02c98c6c00b082b750713f000000cc34717c9bd8a13057a769112981f48ac00029414a49458d04806a0d70b2000001092960002d4a30186d6728001825609940014423cab007b00598000010000de988600005780000026a4164d13a00018e690a40c81ead9000094118001b7a290006b4bc0002a83dc740966ae00000000000894af9733d0000000004ae000000b9000859262e72b63f4000000002ac000003c805c788001248180029306e0005e3635fa00000000000ce00010e1c6594fa0003b0bb4051e66b24a57d99f000414bda8944cb9013b6843600000000322939ada9b046000002314ea000001aa0c6000aca8800eb391b2534b6c39b2aa93aec100000012e59d8c8d1000771648e26520012a0000b60008a1d9000000000000006506b299000048db19e000131509f61d25f80033d000a351e16d2c8801678050009e000060398d8592a392aa7bd7b2b91007553b91f0cec8d8087c3f8000000391220019799d0000fc08a8c00091000000476be458000000000001570760003d000544001980000008d09011d548000000215040002102f000a980000041a0000031041e001741512f24cc000000508d54f2d61700007e0000000017713a57e0013d9b82103ec002246905715930c3367e46f2cd2e415d57a596e4a1c5fb3a3e0dc58f0244b481c9b800000000408933429a4a5ab6224000728004185983882b1f2d3c0023a0007b40033e32e7a4001f30000d1788654663850e1a2000a8d4a9cf5886b152800204019a4810192000d9800570001a13281386556f00035e6e8b0800000000288005a450d4e09b0000003990713e5d476800656000342080a051c2f9c40001b8db97a6c0615558226ac7f4000006be16582b39000330c0b5a5be74813056376610000a20a657443800630999708000005088c84e4a05b0240315680018696003c45c002851e00006225d00013c001040000001900031400169a0900061c00000000001240003c42f5ae9920e00016114543e000000b6000001b72bb000bbc3f345000c0d108001b88a1a22e250c1344c0c6000cd00019c38c1e1901e55b000000188000864002550000e8002d0000d34e2b4a34c06c67246000000a60ca386000000000000008500000064d278003d61d
  | 6 => 0x3c000000ad0000000008e0000006d40026e1aa34c772d50000f8f8a3d63a5f434800000124562aa2d2001aa8902202b9599f23001889a8c35d2
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xc08000000000000000011850007d00000b4510000000003e1c02200068010666000f4f4612b000e200000007e8c00160401b001750e0247000b80000000e6001f12c24630d0000000000009000000907200000a0680c2122c00001b800580301000101000e00040000000306010303010e0000010000000905000004010c01020402020002000100040100050001a4ce3a94a521d2672d465190f12a92c2290878a5496014843c4ac4a88a221e31515805110e8b38ec929c85455c66510f32a32e0218a09961443584504ca87396c929c83435ca6510f31a32e0218a098e0c43588504c60e39ac928643071cd6494221838e6b00a890c3970194434860ebb4a621a43461c15310d21838e6b04a810d8673d912108782aa2a690843299da4348421a4aea21a4210c1c73592500868c39ac928043c89512154021e42a890aa010f425348550087a0a9a42a8043461cd6454021e46e890aa010f2074485500879132242a8043c85912154021e448690aa010f2043485500860f39eca90e81a84856008740a1ce5b20a6a050d72d90535028b38ec829a81455c76414d40838eab1c84a041c7558e4150306b10c429a81459c46214d40a2ae2310a6a0519701885350287390c229a81435c86114d40c2ac2308a6a051970184535030a29ec2a92818514c6154940c30a730064a060c53d895150306298c4a8a818614e600c54083ce7b2a42a041c73594215020e3aac610a8107dd8530854083aec29842a052475484215038229a4210a818614e6008540c30a6b0042a06a121580215030d31ac02a661435ca6510c30a2ae3328861841f75580430c24dbaac02186186dd56010c30b12e021ca4185197010d520c2c4b8086a90614a5c04354830a92e021aa41870a7010d520c286b8086a9061c25c04354830a12e021aa4185917010e510c38221aa528861465c04354430b22e021aa21870443949510c38221aa4a88614c5c04354430aa2e021aa2187127010d510c28ab8086a8861c45c04354430a22e021aa21860c63949400c30631aa4a00618518e5150030c28c6a8a801860c6454b300c30a322a39806183191524c030c28c8a8a601849876501300c384a928098061c4545404c030934ed21a601841e73d9151c828ab88a621c418614d6010e20c30a6b00869060c6510d32482c4b808699241a210c604c9209c2e2302649041c73592500820e3b4a6a0041071d95350020c28c728a80106146354540082c439a8090041c254d4048020e42a2a02401041e73d9152c4286b90a621c218614d6010e10838e6b26a50861853580434430a3288698a21645c0434c510d208630262884e172181314433032a4290221071cd6055010838e6b24a00841c7694d400420e3b2a6a00218318e5250010c18c6a928008590735011004388a9a8088021c85494044010
  | 1 => 0x1700000442a0009800001240816478b4a400299a01c000000000000002d1a6e1780c0000328000069001a90289000183c30001c80067000009e1d041788a013a000000014a14007500000fe0000000004d0000000000000000000007c86001d2004a0a20800001709864807b1881cfc212f954da05001280018378cca00900000ec8800000c00000000ee002d8000000190ecc80f3580000823c0d8f227110f114861300000003615c2a35230007084001880047150ac004e2c800001
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2e68000602c48002450c0009806282a241c58ec1e802ab220000430d0000400c9a118010d6114132a098010d6214131905859cf6448421b0283dd12154021920875912154021b008359121540219228790d2154021c05625c46214d40c09625c06214d40c05725846114d40c11615c06114d40a058614d2108540e00534856008540b018010d5294430b018010e5254430b018010d5254430a118114d6010e20c08655c0434c920c80435c4604c9209088754d4048020d00735454048020a098214d6010e10c10655c0434c510c80435c8604c5109108754d4044010d00735494044010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 26
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s5K5 (24591+((h/267+packedAt s5K5 (21654+(h % 267)*11) 11) % 1408)*11) 11
  | 4 => packedAt s5K4 (36788+((h/294+packedAt s5K4 (33554+(h % 294)*11) 11) % 1166)*11) 11
  | 3 => packedAt s5K3 (7440+((h/48+packedAt s5K3 (7056+(h % 48)*8) 8) % 251)*9) 9
  | 2 => packedAt s5K2 (1608+((h/8+packedAt s5K2 (1560+(h % 8)*6) 6) % 35)*6) 6
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fe0fff0ffffe3f078f1f8ff1fff83fc0cf3cf
  | 1 => 0xc1ff0fff07c7fc7f80fe3f1fe383fc3c733d33
  | 2 => 0x1fff0fff807ff8fff003fe3fc03ffc383ce3c
  | 3 => 0xfe0000fffff8000fffffc003fffc0003fc0fc0
  | 4 => 0xffffff000000000ffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x280010210104001020482404a08110045045
  | 1 => 0x14424222120a40828052110921092828312512
  | 2 => 0xa8842444409480152900224248125281828a28
  | 3 => 0x8c16aa889480c929ca9480039258188ad80f80
  | 4 => 0x3118cc0ee727124e74e93c90006063336ff000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8fee8eae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37115
namespace PEqualNP.Outside.L_meta_37115
open PEqualNP.Outside.L_meta_37115.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1980e11000007958a1686810b198f95089b1e0e9c829e8a930997138204841280031d008508190005801c00000c001f83901f1da08d11949a8b8ca00f141b960609108012178700188000001a0d80000802025090808382020808b029c786000800201ffd5007fe5401ff55007fc54027fd4c09fe53027f54c09fc5301ffd0c07fe43006f90c07fd4301ff10c07bc43027fd48097f52017f94809fd52005f54805fc5201ffd0805fe4201ff50805fc42007fcc805fe32007f4c805fc32027fd4409fe51027f54409fc5101ffd0407fe4101ff50407fc41007fcc401fe31007f4c401fc31017fc8401fe21007f48405fc21027fd4003fe50027f54003fc5001ffd0007bf4000ff90007fd40006f50003fc40007fcc003fe30007f4c003fc30017fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2e2005bfd971002ffccb88012fe65c400bfeb2e2009bf5971002ff8cb88016fc65c400bffb262005bfd931002ffcc98800efe64c400bfeb26200bbf5931002ff8c988016fc64c4017ffaa6200bff9531005ffaa98802ffc54c400bffb1e2005bfd8f1002ffcc788002fe63c400bfeb1e2000bf58f1002ff8c788016fc63c4013ffa9e2009ff94f1004ffaa788027fc53c4017ffa1e200bff90f100077c878802ffd43c4017fe21e200bef10f1002ffec588016ff62c400bff3162002bf98b1002ffac588002fd62c400bfe3162005bf18b1004ffea5880277f52c4015ff2962009ff54b10006faa58802bfc52c4017ffa16200aff90b1005ffa858802bfc42c4001ff996200aff8cb10007fa658802bfc32c40037f30e2005ffd471002ffca388017f651c400bfea8e2009fd5471002ff8a388017ff41c400bff20e2005ff5071002ff88388017ff31c400bff18e2005fd8c71002ffa6388003f531c400bfe18e2005ffc871002ffc4388017f621c400bfe90e2000fd4871002ff84388006fd60c4003ffa862001ff9431000ffaa188007fc50c4003ffa062001efd031000ffc8188007fd40c4003dea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe82188023ff65440117fb2a2000dfd9510004feca88023fe65440097f32a2008ff59510045faca88023fc65440097e32a2008df19510024f8ca8801fff644400f7fb222007ff9911001dfcc88801ffd644400f7eb222007ff1911001df8c88801fff544400fff2a22007ff5511003ff8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c688023ff5344011ff29a2008ff54d10047f8a68801fff434400fff21a2000ef90d1003ffa868801ffc434400fde21a2000ffd8910005fec48801bfe62440057f3122000ff58910005fac48801bfc62440057e3122008ffd4910046fea48801bfe5244011fea922000df54910037f8a48801fff424400dff2122007ff50910037f88488003ff324400dff1922000ff4c910037f86488006ff6144011ffa8a2005ff94510047eca288023fd5144011faa8a2005ff1451003ffe8288017fe414400ffea0a2005ff10510007fe6288017fe3144001fb18a2000ff4c510007ea6288017fc314400dff90a2005ff88510007ec4288003fd2144001fa90a2005ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003dfa022001ff9011000ffa8088007bd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff104400bfd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7fc20cc003ff0866001ff04330087feca98042ff654c001bfb2a60009fd9530087fcca98012fe654c021feb2a6010bf59530087f8ca98012fc654c021be32a60049f1953007ffec89803eff644c001dfb226000afd913007ffcc89800efe644c01ffeb22600fbf5913007ff8c89800efc644c01fde3226003af1913007ffea89803ffe544c01ffeaa2600fff1513000dfec698043ff534c021ff29a6010f794d30087faa698043dd534c021fe29a600fffd0d3007ffc8698003be434c01ffea1a600fff10d3007f788698003ff624c0017fb12600eff98930015fcc498003fd624c01dfe3126002bf18930087fea4980437f524c01dff2926010ff54930006faa49803bfc524c01fffa12600eff9093007ffa849803bfc424c001ff9926000f7cc930077fc6498003fd324c001ee992600eff0c930007fec298002ff614c001ff30a6000ff58530007f8c298016fc614c021ffa8a6010ff94530087faa298043fc514c01fffa0a600fff9053007ffa829803ffc414c001ff98a6000f7cc530007fc6298003fd314c001ee98a6000ff0c530077fe4298003fe214c001fe90a600eff0853000dfec098007ff504c003ff2826001ff5413000ff8a098007ff404c003dfa026001ff9013000ffa8098007bd404c003fe2026001ffcc130007f66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff9026001ff8813000ff84098007fe104c003fe082600dffd952006dfeca90037fe65480097f32a400dff5952006dfaca90037fc65480097e32a400cffd9120065fec890033fe64480077f322400cff59120065fac890033fc64480077e322400cffd5120067fca890033fd5448019fe2a24000ffd8d20005fec690003fe63480017f31a4000ff58d20005fac690003fc63480017e31a400dffd4d2006ffca690037fd534801bfe29a400cffd0d20067fc8690003be4348019fea1a400cff10d20067788690006ff6248005ffa924002dfd4920017fca49000bee5248005fea924002df5492006fdaa4900036d5248005fe2924002ffd0920017fc849000bfd4248005fe2124002ffcc920017fc649000bee3248005fe9924000fb4c920017f86490003ff61480017fb0a4000ff98520007fac290003fc614800b7e30a400dffd452006ffca290037fd514801bfe28a400cffd0520067fc8290033fd4148019fe20a4000ffcc520007fc6290003fd3148001fe18a4002ffc8520017de429000bfe2148005fe90a4000fb48520017f84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001efd012000ffc8090007fd4048003dea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe409000bfb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ff8412000ff42090007fc104800bffb
  | 2 => 0x210c7f88690863bc434840b7fb124202ffd4921016fea49080bfe5248405fea924202df54921017f8a49080bff4248405ff2124202ff50921017f8849080bff3248405ff1924202ff4c921017f8649080aff6148433ffa8a4205ff945210cffaa290817fc5148431ffa0a4205ff905210c7fa8290817fc4148401ff98a4205ff8c521007fa6290817fc3148405ff90a4202fdc852102ffc4290817ee214840bfe10a4205fb08521017e8429080be42148401ffb024200bfd81210bffcc090806fe6048401feb024217ff1812100df8c090867ff504842fff2824219ff541210bff8a090863ff4048431dfa024217ff901210c7fa809085ffc404842fff1824217ff0c121017fe409080bef2048405ff1024202ff081210bffc2090817fc104842ddfb2a8016ef995400b77acaa005bbc6550001dfb1a8000ef98d400077ac6a0003bc63500015e31a8016efd4d400b77ca6a005bbd535002dde29a8000efd89400af7cc4a0003bd625002bde3128016efd49400b67ea4a0057be525002ddea928000cf549400af78a4a0003bf325002bdf1928000ef4c9400af7864a0003bf6150001df30a8000ef5854000778c2a005bbf515002ddf28a8016ef545400b778a2a0003bf3150001df18a8000ef4c5400077862a0057bf2150001df10a8000ef485400af7842a0007bf60500035fb028003eed814000f7ea0a0007be5050003dea828001ef1414000f7c60a0007bc3050003df9028001ef8814000f7840a0007be1050003de0828012ffd97300a5fecb98053fe65cc0097f32e6014ff597300a5facb9804bfc65cc0097e32e6012ffd933009dfec99804bbf64cc0015fb266013ff9933001dfcc99804ffd64cc0277eb266012ff1933001df8c99804bbc64cc0075e3266013ffd533009ffca99804ffd54cc027fe2a66001bf98f300a7fea79804bfe53cc029ef29e6014ff54f300a7baa79804bfc53cc027ffa1e6012ff90f300977c879804ffd43cc025fe21e6012ef10f30097fec598047fe62cc0057f3166000ff58b30005fac59804bfc62cc0057e3166014ffd4b300a6fea598047fe52cc029fea966000df54b3008ff8a59804fff42cc023ff2166013ff50b3008ff8859804bff32cc001ef9966011ff8cb30007fa6598003dd32cc025fe1966012ffd8730007fcc398016fe61cc001feb0e6000bf58730097f8c398053ff51cc029ff28e6014ff547300a7f8a39804fff41cc027ff20e6013ff5073009ff8839804bff31cc001ef98e6000ff8c730007fa6398003dd31cc025fe18e6011ffc8730007fc4398003fd21cc023fe10e6001bf5833000ffea198007fe50cc003fea866001ff1433000ffe8198007bf40cc003ff2066001ff5033000f7a8198007fc40cc003ff1866001f78c33000ff46198007fc30cc003ee1866001ffc833000ffc419800
  | 3 => 0xeb286205ff1943102df8ca18817ff640c40b7fb206205ff9903101dfcc818817fd640c43f7eb206205ff1903102df8c81887fff540c43fff2a0621fff550310fff8a818886fe630c441ffa986212ff94c31107faa61884bfc530c43fffa186212ff90c310977c861887ffd430c425fe2186212ef10c3102ffec418817fe620c4057f3106205ff58831005fac418817fc620c40b7e3106220ffd4831106fea41887bfe520c441fea906200df548310f7f8a41887fff420c43dff210621fff508310f7f8841884bff320c43dff1906200ff4c831097f86418816fe610c40bffa886205ff9443102ffaa218817fc510c40bffa086205ff9043102ffa8218817fc410c40bff9886205f7cc43102ffc6218817f6310c40bfe9886205f74c431007ea6218817ff210c40bfe1086205ffd803102ffcc018806fe600c40bfeb006200bf5803102ff8c018806fc600c441ffa80621dff94031107faa018877fc500c43fffa00621fefd00310effc801887ffd400c43bfe200621dff8c031097f8601887bff200c43bff100621dff0803102ffc2018817fc100c40bffb2c4205bfd962102ffccb10812fe658840bfeb2c421cbf5962102ff8cb10816fc658840bffb244205bfd922102ffcc91080efe648840bfeb24421bbf5922102ff8c910816fc6488437ffaa4421bff952210dffaa91086ffc548840bffb1c4205bfd8e2102ffcc710802fe638840bfeb1c4200bf58e2102ff8c710816fc6388439ffa9c421cff94e210e7faa710873fc5388437ffa1c421bff90e210077c871086ffd4388437fe21c421bef10e21015fac51080bff5288405bfa944202ff94a21017faa51080b7d5288405fe2944202ffd0a21017fc851080bfd4288405fe2144202ffcca21017fc651080bfd3288405fe1944205bf9862102ffea310817fe518840bfea8c4205ff1462102ffe8310817fe418840bfea0c4205ff1062102ffe6310817fe318840bfe98c4205ff0c62102ffe4310817ef2188405fb90c4205ff0862102fe84310817ff608840bff3044201bf9822102ffac110802fd608840bfe3044201bf182210e7fea11086bfe5088439fea84421aff142210dffe811086fbf4088435ff204421bff502210d7f8811086bfe3088435fe1844202ffc8221017fc411080bfc208840bff0844205ff042210cffeca90866ff6548433ff32a4204bf995210cffaca90866fd6548433fe32a4204bf195210c7fec890862ff6448401dfb224200afd91210c7fcc89080efe6448431feb224218bf591210c7f8c89080efc6448431de3224203af191210c7fea890863fe5448431feaa24218ff15121007fec690802ff6348401ff31a4200bf98d21007fac690802fd6348401fe31a4200bf18d210cffea690867fe5348433fea9a4219ff14d210c7fe8690863fe4348401df21a4218ff50d
  | 4 => 0x8afff21cc40bfe10e6212ffd8331157fcc198806fe60cc401feb066200bf58331097f8c198806fc60cc459ffa86622aff94331167faa1988abfc50cc443ffa066221efd0331157fc8198887fd40cc455fe206622aff8c331097f861988afff20cc455ff106622aff08331157fc2198817fc10cc40bffb2c6205bfd963102ffccb18812fe658c40bbf32c62049f9963102ffacb188a6fd658c40bbeb2c62009f5963102ff8cb18816fc658c40bffb246205bfd923102ffcc91880efe648c40bdf3246203af9923102ffac9188a2fd648c40bdeb246200af5923102ff8c918816fc648c451ffaa46228ff95231147faa9188a3fc548c4497eb1c6229ffd4e3114ffca7188a7fd538c453fe29c6228ffd0e31147fc8718803be438c451fea1c6228ff10e31147788718817ff628c40bff3146202bf98a3102ffac518802fd628c40bfe3146205bf18a3114ffea5188a77f528c44fff2946229ff54a31006faa51889ffc528c451ffa146227ff90a31147fa851889ffc428c401ff9946227ff8ca31007fa651889ffc328c40b7f30c6205ffd463102ffca318817fd518c40bfe28c6205ffd063102ffc8318817fd418c40bfe20c6205ffcc63102fbe6318803f7318c40bff90c6205ff0863102ffec118817fe608c4037f3046205ff58231005fac118817fc608c4037e3046229ffd4231137fca1188a7fd508c44dfe2846228ffd02311477e811889bfe408c451fea046226ff10231137fc611889bfc308c44fff9046226ff88231137f84118817fe108c40bfe0846225ffd953112dfeca98897fe654c4097f32a6225ff5953112dfaca98897fc654c4097e32a6224ffd9131125fec898803bf644c4015fb226224ff9913101dfcc898893fd644c4497eb226224ff1913101df8c898893bc644c4075e3226224ffd5131127fca898893fd544c449fe2a26225ffd4d3112ffca698897fd534c44bfe29a6224ffd0d31127fc8698803be434c449fea1a6224ff10d31127788698803ff624c4017fb126223ff98931015fcc498803fd624c447fe3126202bf1893112ffea4988977f524c447ff2926225ff54931006faa49888ffc524c449ffa126223ff90931127fa849888ffc424c401ff9926200f7cc93111ffc6498803fd324c401ee9926223ff0c93112ffea298817fe514c44bfea8a6205ff14531127fe8298817fe414c449fea0a6205ff10531007fe6298803f7314c40bff18a6205f78c53111ffe4298817fc214c401ffb026200bfd8131117fcc098806fe604c401feb026222ff1813100df8c098897ff504c445ff2826225ff54131117f8a098893ff404c449dfa026222ff90131127fa809888bfc404c445ff1826222ff0c13111ffe409888bfe204c445fe1026222ff8413102ff82098817ff650c40b7fb286205ff99431025fcca18817fd650c4417
  | 5 => 0xf3218ffa879904bfc43cc825de21e6431f710f3218f38879900afd62cc805ffa966402dfd4b32017fca59900bfd52cc805bea966402ff14b32017fe859900bfe42cc805fea166402ff10b32017fc659900bde32cc805f71966402ff0cb32017b8659904bff61cc801ff30e6405bf98732007fac399002fd61cc825fe30e6432ffd4732197fca3990cbfd51cc865fe28e6431ffd073218ffc83990c7fd41cc863fe20e6402ffc8732017f8439904bff60cc861ff3066401bf98332007fac199002fd60cc825fe3066401bf18332197fea1990c3fe50cc865fea866430ff1433218ffe81990c7bf40cc861ff2066431ff50332187f881990c3fe30cc825fe1866402ffc8332017fc419900bfc20cc861ff0866430ff0433217ffeca990beff654c85fff32a6404bf9953217ffaca990befd654c85ffe32a6404bf19532177fec8990baff644c801dfb226400afd9132177fcc89900efe644c85dfeb22642ebf59132177f8c89900efc644c85dde3226403af19132177fea8990bbfe544c85dfeaa2642eff15132015fec6990bfff534c85fff29a642fff54d3217ff8a6990bbff434c85defa1a642eff90d320077c86990bbfd434c85dfe21a642eef10d32177b886990bb9c434c8057fb126402ffd4932016fea49900bfe524c805fea926402df54932017f8a49900bff424c805ff2126402ff50932017f8849900bff324c801f79926402ff8c932017bc649900bfc324c805ee1926402fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299016fc614c85fffa8a642fff9453217ffaa2990bffc514c85dffa0a642eff90532177fa82990bbfc414c805ff90a6402ff08532007fec099002ff604c85bff3026401bf98132007fac0990b7fc604c8037e302642fffd413216ffca0990bffd504c85bfe282642effd01321777e80990b7fe404c85dfea02642dff1013216ffc60990b7fc304c805ff9026402fbc8132017fc409900bfc204c85bff082642dff04132097fecb988b2ff65cc459ff32e6204bf99731166fccb988127e65cc459feb2e622cbf59731006facb988027d65cc425fe32e6204bf19731097fec998886ff64cc443ff3266203bf9933110ffac998886fd64cc425fe3266203bf1933110ffea998887fe54cc443feaa66221ff15331167fea79884bfe53cc459fea9e6212ff14f3110ffe879884bfe43cc425df21e6221ff50f31097f8879884bbc43cc425ffb16622bff98b31015fcc598803fd62cc4017eb166212ff18b31015f8c5988b3ff52cc459bfa96622bff94b31167faa5988037d52cc457fe2966221ffd0b3115ffc8598887fd42cc457fe2166212ffccb31007be65988affe32cc401fe9966200f74cb31097f865988b3ff51cc40bff28e622cff5473102ff8a398887ff41cc40bff20e6221ff5073102ff88398
  | 6 => 0x600000000000000080100000000000500000080300600080000280080200100000000700400000000000000480480100100000100000100100300000380080180100200000080180000080200100000300000000200100100680000080200000100200080080400080080200180100080180080080080000400080000280000680080100100000180000000100080000480000200400000000000080000000000000080080280080080500200000180000680000200000000280000080280300100000000000000280000000200200000400000100000000000100300180300000000000080000000000080180180400000080000180000600000300080000000180000080100200100700000000000000000000280000000080200680180180400080300100500000180000280000180000100000080100000080000080000500080300000000180080100300000000080100100000000380080000100000000300200400000180080480180100000000200000000080100100000280180080000100080100000900000080380000200180180000280000480380180000380a00180000300000000500080000000100000200400500084bbf6590c6fdf32c8637ef5964309778cb2184bbe6390c075f31c8603e798e431bf7ea72184bbe5390c6fdea9c8612ef14e430977ec5218dbbe6290c01deb148612ef18a431bf7ea5218df3f5290c6ddf2948637ef54a431b778a5218dbbe3290c25de1948612efd86430077cc321803bd6190c25de30c8637efd46431bf7ca3218dfbd5190c6fde28c8636efc86431b778432184bbf6090c6bdf3048600ef582430057ac12184bbc6090c6fdfa848635ef942431bf7aa1218d7bc5090c6bdf1848612ef0c2431b77e41218d7be2090c6bde1048635ef842431af7821218d37f6454869bf322a434df591521a6f8c8a90037f6354801bf31aa400df58d52006f8c6a90d37f4354869bf21aa400cf90d521a6fa86a90d37c43548699e21aa402dfd8952014fec4a90136f6254805bfa12a402df90952016fa84a900b7c4254805bf192a402df0c952006fec2a90037e6154801beb0aa400df185521a6fe82a90d37e4154869bea0aa434df10552016fe42a900b7c2154801bfb02a433df98152006fac0a90cf7c6054869bfa02a434cfd015219efc80a90d37d4054867be202a433df8c15219ef860a900b7f2054805b7902a402df88152016f840a90cf7e1054867be082a412ffd9732195fecb990cbfe65cc8097f32e6432ff59732195facb9904bfc65cc8097e32e6412ffd933218dfec9990c7fe64cc8077f3266431ff5933218dfac99904bfc64cc8077e3266431ffd533218ffca9990c7fd54cc863fe2a66402bf98f32197fea79904bfe53cc865fea9e6412ff14f3218ffe87990c7df43cc825ff21e6412ef9
  | 7 => 0x13f5ae00000032709900023b5414d137133c0000000000000000004a40dd2105222f64420001be0f80004722644a300000000000000000022717b2b209031c1a236b23115a3c00001f312c00000026c42800033208a3d54fa56845013053a2ec00000007203d00048f0002d50000000bc00000034800018b57436e0d20002593f921225828800003141116805915859633e55100043f4f141a4e737d0000000000002ba0004e00e300037a00c0004bc0004c64061aa27e08405159f46923f39500005558b00000b0441a405e5790ff2381460002200001ed1b000000000051c0000000002bc38203e02f0ec4af51200034400000000000000053000017a0000000000000000002840014c31c13c910a5671cf20a00000600031e0002fd00016a0000002720000000531443c73620004100000002a33e100000000000041325a0d300055e00000046300000054c00031f0034ee29c00027800000000000000000053b0170000fb41d0d600000000000042f58a47d5732df25621757d25b0384401700680003ac4a20610002d200000004100011d0000003d31e539f0004b00000000001dc14910800000000002b00022f35d1ff3de00000000008e00000019537f32d4ad00000040a3bf37e4bf0e732c50b2973042190df0e512b00010b14a13809b4f25a90633c43ad1f800052f26953917203526a0002760000000000000004d401600011f0bf00045b00010c00000000000005720b4583010000000000000aa42748e4751f60c20000000000930d727a42e01d3a400020f19007900000000054800000001409c0000000004e400000034e00000049f20800015e15d40451d00000000000000000000000000000000000000056f0003872c20000000000000000000d40f228e00047e3a71cd00033f2de3df57000000026f1643cd41f1160820000b82090342a100034b1fe24421127f00000043700052b5a71980005255050002c700042616139b00020300000002828b5a010400000000000000000000000200180400000500300000200000080000100080000080280180100000000000000000580200000000080200200000080200080000080000180080080500080080080280000280000000100000000000080480000080080180380000000300000000280080000000000000100180000180000000000100080080000180000000000080400580000000080100000100000280100380000000300000080000080000500180100600100280000080680000000180080280000100280200000000100200200080080080000180500000000000100000600300080000d80000180480000600480080700000000600300000100180000000180300300280180080280100200000080000000100680000080000180180000280100080180080100000
  | 8 => 0x2052c83050a729b3a03904485a555f0661ce48d54405b4492f842a00004b00059b11b00039d22910f0000001063ba5a80001ee26b00000000009a4385750001b312600000000050158e0000000000003fb00000000050f0000002b500033d0003d90000001d800000013e15413b4e20000a41940e452a36d23227d2c50d81eb0001510004c900000000008551e41900050c00000055811e3795a23c30002d70000000001374b54642f50000000000000000000003da4ab00000000008c00008300000000000000053149900004637442d0000000004544d90001690000000000000005660001774974df07050a1c903c4613654ca3b60005ac38e0000001e20000000000000000f740d00039241400056e2a229f4fe0001d90a11750000004861413c15843e80000005423e73b95ab0405454e95652ef1352ad0a300012532050859e3b40000001d00000970d900000000001257c00000003213300000000002539633b0000000000000362c600044725c20030b00042c00000000000000019a4a10000003cc00045518a0003250000000001390004a627c0000000004c40000001fb0000000001120000000000000002140000003c626209f00040c4050004520000000002531c60e100000000048c00010d4b11f900014b0000003f600000a0740000000000005780000000004761b70000be0001e62e93ab0005ad1670000002e54d55854020003560003090002fb11c0003fd0000004c00000002374a007715500000000004e0101bf0000000000052f70003514f024e06b0000004e64440000000002915110003450003af00000000000000023400024300012153500000011035b49e0b93cf32245c25f30c28526e5710ed3645245561af0002540003e63a52a052c23c36a3210880000005993b13101140892525920000270003f700029e0001cc00000000035200000025d0003582d04e326d0000000002ab18400012d00000000000030e0000000000692920000003f100017100009100000054900000000024c2d81475530e614d4ae0000000000000004fc54300000052d0001db08d41700030a0001990002fa00000000000000014c2040002bf00000000000019f32a0000000a90000000001ef4350000521850000000000000000001d334c00036f3bc0000000eb0002670dc4b43e31282180002a509822600000000000000000000000028c00049407d3410004b84572470a617c4f90000002860004790003314d723d58f00000000700000000028100000052800000000000000056c00046500000000000000021a42939717f1c402615b4953493142711001fc0000000003190003290000000000000000002891310000000115540000003162130000002f20000002664340921e40000003d100008700000000000000022d1df06d16d
  | 9 => 0xb4242ce0c60001271861f10000000004305630004ac55c0000000000000000001de0002b157a2285802b700049213228d0005000002b44dc4d244d41c3d251601f32451a1bc21e3683852dc0000005692061760000002610f01bb32f0005213665590002a900014005420c27702c0000000000000000000001f24670000005aa3a100051005000000000000000000018045a2f048b00003b0c84b658800058911a0000c75570003db5970000240003d63730bd07f43e3472410090001e947a0002e131153222e00000006215200043d02d19d34316251f0424a900047f00035f2ed4ff0000002d10000000003e00002874684ce0004bb30f12f2831c81e04eb2af0000000002995060000000004c80002ac0004230001ec38d1a748800000025e0130000964fd00000004906400000045f5600000000000000005a10000000b20000000003690000000000001da2cd00000000000000017800005824a4cc1b600016f0b40c91450004463ca0002aa34619253f2402e23c847100000000000000039c1050004620000000001c70004081e84c20000001533be00000000000d00012a0005180003fc2db0000003353aa03f10950d00011954d0000c144a4564220d000055d0000fe0001433dd5a30001c500000000019e36741b00035e0002fc2750003dc0001d50000000003153d41ae54e42123921b5870003ec45e2982a800044c0000004090004451a13170000000000783555130b300000031a2213380000000000003760000b50000002ca09524d0000713830000003b74f40ee48a5340000390000001605904d61e71234435720805460000000000004aa2223020000000000000b019c1d70001915090f61b52b900021d4f53e50000001a925500000f00031d0000d105c1960201220430000000000000000000000000004030000000003eb00000000035738000000053d5641650b635000000000000045d0000e800000000022a00052e22b0003ae1dd0004534bd3f81e340f4e829012001b5950004330000002be0003785030003ce0005021b800056d0004b70001ad0ac0003540000330000000000002022a700000002e0000a00002334000000000000003e40000b104c2945610003ea00000033a07b4591b90482a434a0600e24a51832300750000000c006700018956a00007a00000000043a4da3a82e40000cd28a4a70003e211757e0004870003123f30002ff0ad00042b47800009e0b700052300000005d00033040e1870001fd0002f10001562703814320003c22dd1cb43907300014f0ea43b0001361ca0000fa49600000050e0000000000001fa00017d0004db2d300000000030638b35a0003e95200003ff0000000000000763d800056200018e0000000000860000000003f53611d100000000049c59100000047354a00001c0000
  | 10 => 0x2b60000000000004e13a34c100016b3860000003fe52958138c47c11347400000000007c3370000f125700000032b3fa24200041619b2da03041200017e0ae00031b0000003402950000000d537000000026800000038400032e0000020000000002f33910000ef27443628000000000000000004f0000000002e70003360004810000004831f05762164b20003d70000001a600044f3030003600044d82c44200002790000c40000000003000000000004ef00048500015c2c34c70000000004cf53800000000030d3a21f40a800013c29a16c0002f41114660000002d62ae1bd3080000da1c339800000000000000049104704a3281011ea00000005f00059c0cb07e14e1634ec01a13d53308f3723f001959424b0000000000000002650000001f700000000000000000000000041e00000000000041558319354b00049d46a4f336c5a64d000000039e0221f53332cc58223638f20e1075170000000000000000c52b33b200000037b00006c2ee3f239400059d4601a00de00001e1420001590a20000003bd00000000000000000000000000012931300051b09d0000003b52e303a0bb0004e500000037c49a0db0000000000004701791342e80e000000000020157b0001c00000652bb46e0000080291a30000004cb0000000001b422c0000001a800e54f0000002eb58603725030700013a2cb0000003b346c0000000000ce0000003b80004075372bd0cc06a00000012400000000038a18c0005070003893753cb5470000001d610e3425554770f40f50002c91ab0000000003630004800004820002b800022300000044e00017428200040b00034f1a555b29d0001b10233c54c53394f61ac0180004932350004840000000fd00059a4a800000028f08b00002a00000000040158d54027b31804549b0000004ea4dd4ba0ca0f90ba0002ea00000000050400006f4900003a94fb21516e3d01880000000215190000002e00001180002070000cf2511e100019723e00000000000000000000000032639900037700018235c04d0002a60001020000000000001660003a60000000000000000000e926355200000029600011500000000000000000012e0001ba2e65500000004be0000000003344cd0000002454b33b047b0000152d40000004b94d31d406e14800023a4182c03ee00052618d0000000004982fe4253235144890002d958c4ed1c200000043122515700046f35338818f0ab00024f0002240004f826020d5775151730f346d2c153600000043c00000000039a0002734f72930004de0001030000002460000000000000001b253c2493f446b0005930003930005270000af00035921c00000000000000005a00000053e56b4410fc08157f0000002f900000000059809415015f0003ed5a40000a53ef2cf0003bb05634d44
  | 11 => 0x1810000c31d20000000002b021f55a248451
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7658c51022774658c51002fb6748c51002fb5748c510115f5738c510096f6638c510096f4638c510007b6438c51022fb4438c510005f5728c51022777528c51000775528c51000df6708c51000df4708c51002ef7608c51002ff3608c510137b7408c510137b5408c510137f2208c510094ff764c51000cfe764c510114fd764c51000cfc764c5100067f654c51012e7c654c510005bf744c51003dbc744c510006df634c510006dc634c51002fd4314c510005fb704c51000df8704c51000df4764c510116f4764c51000cf4764c51021df7754c51021df5754c51000777654c51020f74654c510007b7744c510217b4744c51002df7734c51002fd7734c510007d7634c510096f6634c510096f4634c510007d4634c510007b6434c510217b4434c510005f7724c51020f77524c51000775524c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c510117f0704c51002ef7604c51002ff3604c510117b7404c510117b5404c510117d7304c510117d5304c510117f2204c510205f6768851002ef6768851002df775885101fdf575885100077765885101f774658851002df77388510005f57388510007b643885101efb443885100bdf57288510016f66288510016f4628851003777528851003775528851002ff3708851000df6708851000df4708851002ff0708851002ef7608851002ff360885100d7b740885100d7b540885100d7f22088510014ff764851000cfe76485100bcfd764851000cfc76485100067f65485100ce7c6548510005bf744851003dbc7448510006ef6248510016ec624851002fe42148510005fb704851000df8704851002ff0104851000df47648510016f4764851000cf476485101e5f775485101e5f575485100077765485101df746548510007b774485101d7b47448510005f77348510005f57348510007b643485101d7b4434851002df7724851002fe77248510007e76248510016f66248510016f46248510037e46248510016e46248510037775248510037755248510007f3704851000df6704851000df470485100bff0704851002ef7604851002ff360485100bfb740485100bfb540485100bfe720485100bff220485100bfe5204851002df87648110016f8764811002cf876481100077b65481101c7786548110007ba43481101cfb8434811000dfb724811000feb7248110007eb6248110016fa6248110016f86248110037e862481100377b5248110037ea52481100377952481101c7e95248110007695248110037ea3248110007e93248110007f3714811002dfa714811002df87148110007f0714811000efb614811000ff361481101c7f251481101c7f15148110007f23148110007f13148110037eb2148110037f22148110007e92148110037f12148110007e12148110
  | 1 => 0xd10007b67190d10007b57190d101aebf6190d10277b65190d10277b55190d101adbf7090d101adbd7090d101aebf6090d101afba2090d1026fbb1090d101afb61090d101afb41090d101afb81090d10014fe76d89100457c75d89100067f65d89100067c65d8910036ee62d8910004ff75d89100067f75d8910024fe75d8910004fd75d8910024fc75d89100067c75d89100247c75d8910004ff74d891001cfe74d8910004fd74d891001cfc74d8910094fe73d8910004fd73d8910006be43d8910006bc43d89100367f52d8910006ef42d8910036ec42d8910036ec32d891002cfe71d891000cfd71d891002cfc71d8910036ef21d891002cff70d891000cfe70d891002cfd70d891000cfc70d89100d6bf40d89100d6bd40d89100d6ef20d89100d6ed20d89100057f75589100457c75589100067f65589100067c6558910005bf745891003dbc7458910005df7358910005dc7358910036ec6258910265f77158910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe7458910004fd745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910094fc7358910006dc7358910004dc7358910006be4358910006bc43589100d4ff7258910006ef72589100367f5258910264ff7158910006f771589100bcff7058910006fb70589100bebf40589100bebd40589100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c765491025e7f64549101a67e645491025e7d64549101a67c64549100067f63549100067e63549100067d63549100067c63549100073e435491025f3c43549102557f72549100476f72549100367f62549100167e62549100367d62549100167c625491000776715491000775715491019e7f615491019e7f605491019f3f405491019f3d405491019f6f205491019f7a205491019f6d205491024f7b105491019f76105491019f74105491019f781054910094ff76cc910004fe76cc910004fd76cc910094fc76cc9100067f65cc9101967c65cc910096de63cc910006dd63cc9102479c43cc910006ef62cc910016ec62cc91002df671cc910005f571cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91017e7c654c910005bf744c91003dbc744c910006de634c910006dd634c91023f9c434c91000cfe76cc51000cfc76cc5100457e75cc5100057d75cc5100067f65cc5101667c65cc510006df63cc510096dc63cc51000dfa70cc510005f970cc5100edf6768c51002ef6768c51002df7758c51002f76758c510235f5758c51002f75758c51000575758c5100077
  | 2 => 0x2867e30d95102867d30d95102867c30d95102867f20d95102867e20d95102867d20d95102867c20d95102867f10d95102867e10d95102867d10d95102867c10d95100067f65d8d100067c65d8d1003dbe74d8d10005bd74d8d100079c43d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d10004ff74d8d1001cfe74d8d10006be74d8d1001cbe74d8d10004fd74d8d10006bd74d8d10004bd74d8d1001cfc74d8d10006df43d8d10006bc43d8d10006dc43d8d100069c43d8d10014fe72d8d10004fd72d8d10014fc72d8d100067f52d8d10006de32d8d10006dc32d8d1002cff70d8d1002cfd70d8d10136bf40d8d10136bd40d8d10136df30d8d10136dd30d8d100457e7598d100057d7598d100067f6598d100067c6598d10006df6398d10115f57198d10094ff7598d10024fe7598d100967e7598d100247e7598d10004fd7598d100967d7598d100047d7598d10094fc7598d10094ff7498d1001cfe7498d10004fd7498d10094fc7498d10094fe7398d10096bc4398d10014fe7298d10004fd7298d10014fc7298d100067f5298d10114fd7198d10096f57198d10154fd7098d10096f97098d10156bf4098d10156bd4098d100057f7558d100457c7558d100067f6558d100067c6558d10005bf7458d1003dbc7458d10005ef7258d10035ec7258d10155f77158d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d10006df7358d10006bc4358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d100067f5258d10154ff7158d10006f77158d10114ff7058d10006fb7058d10116bf4058d10116bd4058d10134fe7618d100067f6518d100067c6518d10006dd6318d100079c4318d10094ff7518d10024fe7518d10004fd7518d10094fc7518d10094ff7418d1001cfe7418d10004fd7418d10094fc7418d10096de7318d10006df4318d10096bc4318d10096dc4318d100969c4318d10014fe7218d10004fd7218d10014fc7218d100067f5218d10006de3218d10096dc3218d1002cfe7118d10096f57118d1002cfc7118d1002cff7018d1000cfe7018d1002cfd7018d1000cfc7018d100eebf4018d100eebd4018d10096df3018d100eedd3018d10096bf7690d10006be7690d10006bd7690d10096bc7690d10276bf6590d100073f6590d100063f6590d101bebe6590d10276bd6590d101bebc6590d102773c6590d101be3c6590d1027dbe7390d1003f9e7390d10006bf6390d10096be6390d10006bd6390d10096bc6390d101b6be6290d101b6bc6290d102773f529
  | 3 => 0xd2058b1002efa1058b1002ef91058b100067f7654b1024e7e7654b100067d7654b1024e7c7654b1024e7f6454b101a67e6454b102de7d6454b1024e7c6454b1024e7f6354b100067e6354b100067d6354b1024e7c6354b100073e4354b102df3c4354b102557f7254b1004f6f7254b1024e7f6254b100167e6254b100567d6254b100167c6254b1024f767154b10007757154b1019e7e6154b1024f763154b1024f762154b1019e7d6054b1019f3f4054b1019f3d4054b1019f6f2054b1019f6d2054b1019f761054b1019f7a1054b1019f741054b10094ff76ccb1002cfe76ccb10004fd76ccb1002cfc76ccb10096de63ccb10006dd63ccb102d79c43ccb1002df671ccb10005f571ccb10004ff764cb1002cfe764cb10004fd764cb1002cfc764cb10005bf744cb1005dbc744cb10006de634cb10006dd634cb102cf9c434cb1002df6714cb1002df7764c710006f7764c7102c5f7754c7102c5f5754c710007b7744c7102bfb4744c71002fd7734c71002fd7634c710096f6634c71002ef4634c71002fd4634c710007b6434c7102bfb4434c710005f7724c7102b777524c71000775524c710007d7324c710007d5324c71000df6704c71000df4704c710117b7404c710117b5404c710117d7304c710117d5304c71002df776487102aef776487102a5f775487102a5f57548710007b7744871029fb47448710005f77348710005f57348710007b6434871029fb4434871002fe7724871002fe76248710016f6624871002ef4624871002fe4624871002ee4624871005777524871005775524871000df6704871000df470487100bfb740487100bfb540487100bfe720487100bfe520487102957e76d95100467e76d95100247e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c43d95100057d72d95100067e62d95100067c62d95102877771d95102877471d95102873f40d95102873d40d95102877a20d951028f7b10d95102877610d95102877410d95102877810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100063c43d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067e32d95100067c32d95102867f71d951028e7e71d95102867d71d95102867c71d95100067f41d951028e7e41d95100067d41d951028e7c41d951028e7e31d951028e7c31d95100067f21d951028e7e21d951028e7c21d95102867f70d95102867e70d95102867d70d95102867c70d95102867f40d95102863f40d95102867e40d95102867d40d95102863d40d95102867c40d95102867f30d9510
  | 4 => 0xc520006dc638c520015ee728c520005ed728c5200076d528c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520005bf744c520065bc744c520006de634c520006dd634c520015ee724c5200076d524c520007cd324c520004fe760c520004fd760c52002cfc760c520006df630c520096dc630c520015ee720c520005ed720c5200076d520c520006f7610c52002ef4610c52000dfa700c520005f9700c52000dec764852002eec764852000cec76485202f5ef75485202f5ed7548520007af74485202efac7448520005ef7348520005ed7348520007ae43485202efac4348520015ef7148520017e77148520007e7614852002eee614852002eec6148520007e4614852002ee46148520007eb704852000dee704852000dec70485200bfe87048520016ef6048520017eb60485200bfaf40485200bfad40485200bfea1048520094ff7598f10024fe7598f100967e7598f100247e7598f10004fd7598f100967d7598f100047d7598f10094fc7598f10094ff7498f1001cfe7498f10004fd7498f10094fc7498f1002ede7398f10096bc4398f10014fe7298f10004fd7298f10014fc7298f100067f5298f1000cfe7198f1002ef67198f1000cf67198f1000cfc7198f1002ede3198f1002ef63198f1002edc3198f10156bf4098f10156bd4098f10096df3098f10156dd3098f10004ff7558f10024fe7558f10004fd7558f10024fc7558f10004ff7458f10006bf7458f10004bf7458f1001cfe7458f10004fd7458f1001cfc7458f10006bc7458f1001cbc7458f1002edf7358f10006bc4358f10004ff7258f10014fe7258f10014fc7258f100067f5258f1002cff7158f1000cfe7158f1002cfd7158f1000cfc7158f1002ede3158f1002edc3158f10116bf4058f10116bd4058f10116df3058f10116dd3058f10096bf7690f1026ebe7690f10006bd7690f10096bc7690f1026ebf6590f101bebe6590f102e6bd6590f1026ebc6590f1027dbe7390f1005f9e7390f1026ebf6390f10096be6390f10006bd6390f10096bc6390f1026ebf6290f101b6be6290f1026ebc6290f102e73f5290f1026fb67190f10007b57190f101aebe6190f1026fb65190f102e7b55190f1026fb63190f1026fb62190f101adbf7090f101adbd7090f101aebd6090f101afb61090f101afba1090f101afb41090f10004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b10006bf7458b10004bf7458b1001cfe7458b10004fd7458b1001cfc7458b10006bc7458b1001cbc7458b10004ff7358b10094fc7358b10006be4358b10006bc4358b1002eef7258b100567f5258b1002cff7158b1000cfe7158b1002cfd7158b1000cfc7158b1002eee2158b1002eec2158b100bebf4058b100bebd4058b100beef2058b100bee
  | 5 => 0x96bc6390d201b7ae7290d20007ad7290d201aebf6290d201b73f5290d201b7ae5290d201b73d5290d20327ad5290d201b7ae3290d2026ebc6190d201b7af2190d201adbf7090d201adbd7090d201aebf6090d201b7bb2090d201afae2090d201afac2090d201afb82090d201afba1090d2006f6f76549200266f765492019f6c76549200266c765492031f6f74549203176e745492031f6d74549203176c74549203176f64549203176e64549203176d64549203176c64549200076f73549200076e73549200076d73549200076c73549200076f63549200076e63549200076d63549200076c63549203176f43549203176e43549200072e43549203176d43549203176c43549203172c43549200076f71549200076e71549200076d71549200076c71549203176f41549203176e41549203176d41549203176c415492019f6f70549200076b705492019f6e705492019f6d705492019f6c705492019f6870549200176f60549200166f60549200176b605492019f6f405492019f2f405492019f6e405492019f6d405492019f2d405492019f6c405492019f6f305492019f6e305492019f6d305492019f6c305492019f6e105492019f6a105492019f6c105492000dec764c92016eec764c92000cec764c92030def754c92030ded754c920007af744c920307ac744c920015ef734c920017cf734c920007cf634c920096ee634c920096ec634c920007cc634c920307cf434c920007ae434c920307ac434c920307cc434c9203078c434c920005ef714c920007eb704c92000dee704c92000dec704c92016fe8704c920016ef604c920017eb604c92016faf404c92016fad404c92016fcf304c92016fcd304c92016fea104c92002cfe76d85200076d52d8520004ff75d8520024fe75d8520004fd75d8520024fc75d8520004ff74d852001cfe74d8520004fd74d852001cfc74d8520094fe73d8520004fd73d8520006be43d8520006bc43d852000cfd72d85202fe7f52d85202fe7d52d85202fef621d85202fef521d852000cfe70d8520014fd70d852000cfc70d8520266bf40d8520266bd40d8520266f710d85200076d5298520006f76198520035f970985200057f755852006d7c7558520005bf7458520065bc7458520005df7358520005dc73585200076d5258520055fb705852006d7e75185200057d7518520065be7418520005bd7418520005de7318520005dd73185200076d521852002ef66118520006f56118520004fe76cc520004fd76cc520094fc76cc52006d7e75cc5200057d75cc520096de63cc520006dd63cc520015ee72cc520005ed72cc5200076d52cc520007cd32cc520006f761cc52002ef461cc520004fe768c520004fd768c52002cfc768c52006d7e758c5200057d758c520065be748c520005bd748c520006df638
  | 6 => 0xc6448530005de7348530005dd7348530077e4214853000dfa76cc13000efa76cc13000cfa76cc1300077b65cc13034f7865cc130097bb74cc130097b874cc130007bb64cc130357b864cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc130097da53cc13034fd953cc130097ba43cc130097b843cc13034f7b52cc1300077952cc130097db32cc130007d932cc130097db31cc130007d931cc130065be74d8d20005bd74d8d20004ff75d8d20024fe75d8d20004fd75d8d20024fc75d8d20004ff74d8d2001cfe74d8d20006be74d8d2001cbe74d8d20004fd74d8d20006bd74d8d20004bd74d8d2001cfc74d8d20006bc43d8d2000cff72d8d2000cfd72d8d203467f52d8d203467d52d8d20346df32d8d20346dd32d8d2002cfe71d8d20004fd71d8d20014ff70d8d20014fd70d8d2033ebf40d8d2033ebd40d8d2033edf30d8d2033edd30d8d2016cfd7698d20006df6398d2016ded7298d20075f97098d20094ff7598d20024fe7598d20004fd7598d20094fc7598d20094ff7498d2001cfe7498d20004fd7498d20094fc7498d20094fe7398d20096bc4398d2016cfd7298d20096ed7298d2008e7f5298d2008e7d5298d20096ee3298d2002cfe7198d20004fd7198d20184fd7098d20096f97098d20186bf4098d20186bd4098d200057f7558d2006d7c7558d20005bf7458d20065bc7458d20185ef7258d20005f77158d20005f47158d2008dfb7058d20004ff7558d200067f7558d200047f7558d20024fe7558d20004fd7558d20024fc7558d200067c7558d200247c7558d20004ff7458d20006bf7458d20004bf7458d2001cfe7458d20004fd7458d2001cfc7458d20006bc7458d2001cbc7458d20006df7358d20006bc4358d20184ff7258d20006ef7258d200767f5258d200767d5258d20004ff7158d20006f77158d20004f77158d2002cfc7158d20006f47158d2002cf47158d2016cff7058d20006fb7058d2016ebf4058d2016ebd4058d2033cfe7618d2006d7e7518d200057d7518d20006dd6318d20094ff7518d20024fe7518d200967e7518d200247e7518d20004fd7518d200967d7518d200047d7518d20094fc7518d20094ff7418d2001cfe7418d20004fd7418d20094fc7418d20094fe7318d20096de7318d20096bc4318d2000cff7218d20014fe7218d2000cfd7218d20096ed7218d20014fc7218d203367f5218d203367d5218d20096df3218d20096ee3218d20336dd3218d2002cfe7118d20004fd7118d20014ff7018d20014fd7018d2032ebf4018d2032ebd4018d20096df3018d2032edd3018d20096bf7690d20006be7690d20006bd7690d20096bc7690d20326bf6590d201bebe6590d20326bd6590d201bebc6590d2027dbe7390d200679e7390d20006bf6390d20096be6390d20006bd6390d20
  | 7 => 0xc93000dde704c93000ddc704c93016fd8704c93016edf604c93016f9f404c93016f9d404c93016fcf204c93002cfe76d85300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d8530024fe75d8530004fd75d8530024fc75d8530004ff74d853001cfe74d8530004fd74d853001cfc74d8530006be43d8530006bc43d8530014fe72d8530004fd72d8530014fc72d85300067f52d85300067d52d8530006df32d8530006dd32d8530006f721d8530006f421d8530156bf40d8530156bd40d8530156f710d85300857e75985300057d75985300067f65985300067c659853007dbe7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300857c75585300067f65585300067c6558530005bf745853007dbc7458530006bf6458530006bc6458530005ef7258530075ec72585300067f65185300067c6518530006bf6418530006bc641853002ef66118530006f561185300ecfe76cc5300857e75cc5300057d75cc5300067f65cc5301667c65cc530006bf64cc53010ebc64cc5300979e43cc5300979c43cc5300edde76cc530006de76cc530385df75cc5303775e75cc530385dd75cc5300075d75cc5300055d75cc5300075f65cc5303775c65cc5300079f64cc53037f9c64cc530005dd72cc530006df62cc5303775f52cc5300075d52cc53002ede61cc53002edc61cc53000dde70cc53000ddc70cc530096df60cc5301579f40cc5301579d40cc53000cfe768c5300857e758c5300057d758c5300067f658c53014e7c658c53007dbe748c530005bd748c530006bf648c530146bc648c530115dd738c530006f7618c53002ef4618c53000dfa708c530005f9708c53000cfc764c5300067f654c53012e7c654c530005bf744c53007dbc744c530006bf644c530126bc644c5300079e434c5303679c434c530006f7614c53002ef4614c530005fb704c53000df8704c53000ddc764c53002edc764c53000cdc764c53036ddf754c53036ddd754c5300075f654c53035f5c654c5300079f744c5303679c744c5300079f644c5303679c644c530005df724c530006df624c53035f5f524c5300075d524c530007d7714c530007d7614c53002ede614c53002edc614c530007d4614c530007db704c53000dde704c53000ddc704c530117d8704c530116df604c5301179f404c5301179d404c530154fe760c5300067f650c5301067c650c530006bf640c5300febc640c530155de730c530007d5310c530004fe7688530004fd768853002cfc76885300067f65885300e67c6588530006bf64885300debc6488530005de7388530005dd7388530006ef6288530016ec6288530004ff7648530004fe7648530004fc76485300067f65485300ce7c6548530005bf744853007dbc7448530006bf64485300c6b
  | 8 => 0x1aebd10d91301aebc10d913027dbe7690d30096be7690d3027cbe7690d303c6bf6590d300073f6590d300063f6590d301bebe6590d303c6bd6590d301bebc6590d303c73c6590d301be3c6590d30095be7390d300979e7390d30096bf6390d300979e5390d303c79d5390d301b6be6290d301b6bc6290d303c73f5290d3026ebc6190d30095bf7090d301adbd7090d30096bf6090d301af9e3090d300979c3090d30097b83090d30097983090d30014fe76d89300857c75d89300067f65d89300067c65d8930006bf64d8930006bc64d8930076ee62d8930004ff75d89300067f75d8930024fe75d8930004fd75d8930024fc75d89300067c75d89300247c75d8930004ff74d893001cfe74d8930004fd74d893001cfc74d893000cfd73d8930014fc73d8930006be43d8930006bc43d89300767f52d8930076ee32d893002cfe71d8930004fd71d8930076ec21d8930186bf40d8930186bd40d8930186ef20d89300057f75589300857c75589300067f65589300067c6558930005bf745893007dbc7458930006bf6458930006bc6458930076ec6258930005f77158930005f471589300067f76549300057e76549300067e76549300047e76549300067d76549300057c76549300067c76549300047c76549303be7f64549300073f64549300063f64549301a67e64549303be7d64549301a67c64549303bf3c64549301a63c64549300075e73549300075d735493019e7f63549300073e43549303bf3c43549302557f72549300876f72549300767f62549300167e62549300167c625493024e7c615493019e7f605493019f3f405493019f3d405493019f5e305493019f5c305493019f78305493019f6f205493032cfe76cc9300067f65cc9301967c65cc930006bf64cc93018ebc64cc9300979e43cc9300979c43cc93032dde76cc930346de76cc9303b5df75cc9303b5dd75cc9300075f65cc9303af5c65cc9300079f64cc93018ede64cc93018edc64cc9303a79c64cc93018e9c64cc93016ddd72cc930016de62cc930016dc62cc9300775f52cc9300775d52cc930005dd71cc93000dde70cc93000ddc70cc930096df60cc9301879f40cc9301879d40cc93000cfc764c9300067f654c93017e7c654c930005bf744c93007dbc744c930006bf644c930176bc644c9300079e434c93038f9c434c930006ef624c930016ec624c930077cc324c930005fb704c93000df8704c93000ddc764c930016dc764c93000cdc764c93039ddf754c93039ddd754c9300075f654c9303975c654c9300079f744c93038f9c744c9300079f644c930176de644c930176dc644c93038f9c644c9301769c644c930185df724c930007cf724c930007cf624c930016de624c930016dc624c930077cc624c9300775f524c9300775d524c930005df714c930007db704
  | 9 => 0xc704c7301179f404c7301179d404c73002cff7688730094fe7688730004fd7688730006bf64887300debc6488730095de7388730005dd7388730004ff7648730004fd7648730094fc7648730005bf744873009dbc7448730006bf64487300c6bc6448730095de7348730005dd734873008fe421487303d57e76d95300867e76d95300247e76d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95303cf5f73d95303cf5c73d95300073c43d95300057d72d95300067e62d95300067c62d95303cf3f40d95303cf3d40d95303cf5e30d95303cf5c30d95303cf7830d95300067f74d95300067e74d95300067d74d95300067c74d95303ce7f73d95300867e73d95303ce7d73d95303ce7c73d95300067f43d95300067e43d95300067d43d95300067c43d95300063c43d95300067f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300067e32d95300067c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95300067f21d95300067c21d95303ce7f70d95303ce7e70d95303ce7d70d95303ce7c70d95303ce7f40d95303ce3f40d95303ce7e40d95303ce7d40d95303ce3d40d95303ce7c40d95303ce7f30d95303ce7e30d95303ce7d30d95303ce7c30d95303ce7f20d95303ce7e20d95303ce7d20d95303ce7c20d95303ce7f10d95303ce7e10d95303ce7d10d95303ce7c10d953027dbe76d913007ebe76d913001cbe76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130095bc73d91300079e53d91300079d53d9130006be62d9130006bc62d91300073f52d91301af9e30d91301af9c30d91301afb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d91301aebf73d913007ebe73d9130094be73d91301aebd73d91301aebc73d9130094bc73d9130006bf53d9130006be53d9130006bd53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d9130006bc52d9130006be32d9130006bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d9130006bf21d9130006bc21d91301aebf70d9130094bf70d91301aebe70d91301aebd70d91301acbd70d91301aebc70d91301aebf50d91301aebe50d91301aebd50d91301aebc50d91301aebf30d91301aebe30d91301aebd30d91301aebc30d91301aebf20d91301aebe20d91301aebd20d91301aebc20d91301aebf10d91301aebe10d9130
  | 10 => 0x4b3041f3e4354b3041f3c4354b302557f7254b300a76f7254b300167e6254b3008e7d6254b300167c6254b3024e7e6154b3019e7d6054b3019f3f4054b3019f3d4054b3019f5e3054b3019f7a3054b3019f5c3054b3019f6f2054b3000ddd76ccb30016dd76ccb3000cdd76ccb30095df75ccb30415dd75ccb300979f64ccb3018ede64ccb30096dc64ccb300979c64ccb300969c64ccb30016de62ccb30097ce62ccb30097cd62ccb30016dc62ccb3008f5f52ccb3008f5d52ccb30005dd71ccb3000dde70ccb30097da70ccb30097d970ccb3000ddc70ccb301879f40ccb301879d40ccb3033cff764cb30005bf744cb3009dbc744cb30096bf644cb30096bc644cb300979e434cb300979c434cb30016ec624cb30097cc324cb3033ddf764cb30336df764cb3040ddf754cb3040ddd754cb300079f744cb304079c744cb300979f644cb30176de644cb30176dc644cb300979c644cb301769c644cb30097cf724cb30097cf624cb30016de624cb30016dc624cb30097cc624cb3008f5f524cb3008f5d524cb30005df714cb3000dde704cb3000ddc704cb3016f9f404cb3016f9d404cb3016fcf204cb300a57e75987300057d759873009dbe7498730005bd7498730096bf6498730096bc6498730096f7619873002ef4619873002cff7658730005bf745873009dbc7458730096bf6458730096bc6458730096f46158730004ff7558730024fe7558730004fd7558730024fc7558730004ff7458730006bf7458730004bf745873001cfe7458730004fd745873001cfc7458730006bc745873001cbc745873000cfc7358730096be4358730096bc4358730004ff7258730014fe7258730014fc72587300067f52587300067d5258730006df3258730006dd3258730096f73158730096f43158730116bf4058730116bd4058730116f7105873000ddd76cc73002edd76cc73000cdd76cc730095df75cc7300975e75cc7303fddd75cc7300975d75cc7300055d75cc7300979f64cc7300979c64cc730005dd72cc730006dd62cc7303f75f52cc7300075d52cc73002ede61cc730097d661cc730097d561cc73002edc61cc73000dde70cc730097da70cc730097d970cc73000ddc70cc7301579f40cc7301579d40cc730114fd768c7300a57e758c7300057d758c73009dbe748c730005bd748c730096bf648c730096bc648c73002ef4618c730134ff764c730005bf744c73009dbc744c730096bf644c730096bc644c7300979e434c7300979c434c730097d4314c730135df764c730006df764c7303eddf754c7303eddd754c7300079f744c7303e79c744c7300979f644c7300979c644c730005df724c730006dd624c7303df5f524c7300075d524c730097d7714c730097d7614c73002ede614c73002edc614c730097d4614c73000dde704c73000dd
  | 11 => 0x73d520c540135be710c54042f9f310c54042fb6310c54042f9d310c540007b5310c5400edbf700c54000dbe700c5400efba700c54000dba700c5400edbd700c54042fb9700c540005b9700c54000dbc700c5400eebf600c5400ffbb600c54042dbf7688540005be7688540005bd768854042dbc768854042dbf75885400b5be758854043dbd758854042dbc758854042dbf7388540005be7388540005bd738854042dbc7388540006bc63885400bdbd7288540007af62885400afac62885400af3f52885400af3d5288540205be718854042faf21885400afb7218854042fb421885400d5bf708854000dbe70885400d5bd708854000dbc70885400d6bf60885400dfbb60885400d7b71088540005bf7648540006bf7648540004bf7648540005be7648540005bd7648540005bc7648540006bc7648540004bc7648540435bf75485400b5be7548540435bd75485400b5bc7548540005bf7348540005be7348540005bd7348540005bc7348540006bc63485400d5bf72485400af3f52485400af3d5248540265bf71485400afb7214854042fae214854042fac21485400afb421485400afa421485400bdbf704854000dbe704854000dbc70485400bebf60485400c7bb60485400bfaf2048540096bf75d9330096be75d9330096bd75d9330096bc75d9330096be73d9330094be73d93300969e73d9330096bf53d9330096be53d9330096bd53d9330096bc53d9330096bf72d9330096be72d9330096bd72d9330096bc72d9330006bf52d93300063f52d9330006be52d9330006bd52d9330006bc52d9330096bf32d9330096be32d9330096bc32d9330096bf71d9330096be71d9330096bd71d9330096bc71d9330006bf51d9330006be51d9330006bd51d9330006bc51d9330096bf31d9330096bc31d9330006bf21d9330006bc21d9330096bd70d9330096b970d93301aebf50d93301aebe50d93301aebd50d93301aebc50d9330096bf30d9330096be30d9330096bc30d93301aebf20d93301aebe20d93301aebc20d93301aebe10d93301aebc10d9330014ff7658b30005bf7458b3009dbc7458b30096bf6458b30096bc6458b30096ec6258b30004ff7558b30024fe7558b30004fd7558b30024fc7558b30004ff7458b30006bf7458b30004bf7458b3001cfe7458b30004fd7458b3001cfc7458b30006bc7458b3001cbc7458b30014fd7358b3000cfc7358b30096be4358b30096bc4358b3008e7f5258b30096ef3258b30096ec3258b30004ff7158b3002cfc7158b3016ebf4058b3016ebd4058b3016eef2058b300067f7654b300067e7654b300067d7654b300067c7654b304267f6454b3041f3f6454b300063f6454b301a67e6454b304267d6454b301a67c6454b3041f3c6454b301a63c6454b300075e7354b300075d7354b3019e7e635
  | 12 => 0xe7558540005bd75585400b5bc75585400073c75585400b53c7558540006bf6558540006bd6558540005bf73585400079f73585400059f7358540005bc73585400079c73585400059c7358540006be6358540006bc6358540005bf7258540007af7258540005af72585400adbe72585400adbc7258540007ac72585400adac7258540006bf6258540006bd62585400073f52585400073d5258540007b7615854042ebe61585404a5bf7058540007bb705854005dbb70585404a6bf605854003fbb605854049dbe761854042dbf75185400b5be751854042f3e75185400b53e7518540005bd751854042f3d75185400053d751854042dbc7518540005be7318540005bd7318540006be6318540006bc63185400adbe7218540005bd721854042dbc7218540006be6218540006bc62185400073f52185400073d5218540495be711854042ebf611854042fb6611854042ebd6118540007b5611854001dbf701854000dbe701854001dbd701854000dbc7018540486bf601854048fbb6018540487b71018540487b51018540005bf76cc540005be76cc540005bd76cc540005bc76cc54047dbf75cc5400b5be75cc5404773e75cc5400b53e75cc54047dbd75cc5400073d75cc5400053d75cc5400b5bc75cc540096bc63cc5400adbe72cc540005bd72cc5400adbc72cc5404773f52cc5400073d52cc5400079f32cc5400079d32cc54000dbe70cc540155bd70cc54000dbc70cc540156bf60cc54010fbb60cc54042dbf768c540005be768c54042ebe768c540004be768c540005bd768c54042ebd768c540004bd768c54042dbc768c54042dbf758c5400b5be758c54042f3e758c5400b53e758c54046dbd758c54042f3d758c5400053d758c54042dbc758c540115bd738c5400079f638c540096bc638c5400079c638c5400069c638c5400adbe728c540005bd728c54042dbc728c5404673f528c5400073d528c5400edbe718c54042f9f318c540007b7318c540135bf708c54000dbe708c540135bd708c54000dbc708c540136bf608c540147bb608c540137b7108c540005bf764c540006bf764c540004bf764c540005be764c540005bd764c540005bc764c540006bc764c540004bc764c54045dbf754c5400b5be754c54045dbd754c5400b5bc754c540096bc634c540005bf724c5400adbe724c5400adbc724c5404573f524c5400073d524c5400079f324c5400079d324c540007b7314c54042f9e314c540115bf704c54000dbe704c54000dbc704c540116bf604c540127bb604c54042dbf760c540005be760c540005bd760c54042dbc760c54042dbf750c5400b5be750c54044dbd750c54042dbc750c540155be730c5400079f630c540096bc630c5400079c630c5400969c630c5400adbe720c540005bd720c54042dbc720c5404473f520c540
  | 13 => 0x89400b5bc7558940005bf7358940005bc7358940006be6358940006bc63589404d5bf7258940007af62589400aebe62589400aebc62589400afac62589400af3f5258940005bf715894042dbc71589404c5bf7058940007bb70589404cdbb70589404c6bf6058940067bb60589400073f76549400073e76549400073d76549400073c76549400073f73549400073e73549400073d73549400073c73549400073f63549400073e63549400073d63549400073c63549400063c63549400af3f72549402553f72549400b72f72549400af3f62549400af3e62549400af3d62549400af3c62549400af3e32549400af3c32549400073f71549400073e71549400073d71549400073c71549400af3f21549400af3c215494019f3f705494019f3e705494019f3d705494019f3c705494019f3f605494019e3f60549401a73b605494019f3e305494019f3c305494019f3f205494019f2f205494019f3e205494019f3d205494019f3c205494019f3e105494019f3c1054940005bf76cc940005be76cc940005bd76cc940005bc76cc9404bdbf75cc9400b5be75cc9404bdbd75cc9400b5bc75cc94032dbe73cc9400079f63cc940096bc63cc9400079c63cc9400969c63cc94016dbd72cc9400af3f52cc9400af3d52cc9400af9e32cc9400afae32cc9400af9c32cc94042dbe71cc940005bd71cc94000dbe70cc940185bd70cc94000dbc70cc940186bf60cc94018fbb60cc940005bf764c940006bf764c940004bf764c940005be764c940005bd764c940005bc764c940006bc764c940004bc764c9404b5bf754c9400b5be754c9404b5bd754c9400b5bc754c94033dbf734c9400079f634c940096bc634c9400079c634c9400069c634c940185bf724c9400af3f524c9400af3d524c940007af324c9400af9e324c9400af9c324c9400afac324c940005bf714c94042dbc714c94016dbf704c94000dbe704c94000dbc704c94016ebf604c940177bb604c94016faf204c940005bf75d85400b5be75d8540005bd75d85400b5bc75d8540006bf65d8540006bd65d8540005be73d8540005bd73d8540006be63d8540006bc63d85400adbe72d8540005bd72d85400adbc72d8540006bf62d8540006bd62d85400073f52d85400073d52d854001dbf70d854001dbd70d854049ebf60d85404afbb60d854049fb710d854049fb510d85404a5bd769854042dbf75985400b5be7598540005bd759854042dbc7598540005be7398540005bd7398540006be6398540006bc63985400adbe7298540005bd729854042dbc7298540006be6298540006bc62985400073f52985400073d5298540485be719854042ebf6198540007b76198540495bd709854042fb9709854003db97098540496bf609854005fbb6098540005bf75585400073f75585400053f75585400b5b
  | 14 => 0x4febf60d8d4050fbb60d8d404ff9f30d8d404ff9d30d8d40505bd7698d40005bf7598d400b5be7598d40005bd7598d400b5bc7598d40006bf6598d40006be6598d40006bd6598d40006bc6598d4027dbe7398d40006bf6398d400079f6398d400adbe7298d40005bd7298d400adbc7298d40006be6298d40006bc6298d400073f5298d4042dbe7198d40005bd7198d401adbd7098d40007b97098d4007db97098d401aebf6098d4009fbb6098d40005bf7558d400073f7558d400053f7558d400b5be7558d40005bd7558d400b5bc7558d400073c7558d400b53c7558d400079f6358d40006be6358d40005bf7258d400adbe7258d400adbc7258d400073f5258d40005bf7158d4042dbc7158d40505bf7058d40007bb7058d4009dbb7058d40506bf6058d4007fbb6058d404fdbe7618d40005bf7518d400b5be7518d400073e7518d400b53e7518d40005bd7518d400073d7518d400053d7518d400b5bc7518d40006bf6518d40006be6518d40006bd6518d40006bc6518d401adbe7318d40006bf6318d400079e6318d40006bd6318d400079d6318d400069d6318d400079f5318d400079c5318d400adbe7218d40005bd7218d400adbc7218d40006be6218d40006bc6218d400073f5218d4042dbe7118d40005bd7118d4001dbf7018d4000dbe7018d4001dbd7018d4000dbc7018d4027ebf6018d404f7bb6018d4027f9f3018d4027f9d3018d40096bf7518d40096be7518d400963e7518d40096bd7518d400963d7518d40096bc7518d40096bf5318d400069f5318d40096be5318d40096bd5318d40096bc5318d400969c5318d40096bf7218d40096be7218d40096bd7218d40096bc7218d40006bf5218d400063f5218d40006be5218d40006bd5218d40006bc5218d40096be3218d40096bc3218d40096bf7118d40096be7118d40096bd7118d40096bc7118d40006bf5118d40006be5118d40006bd5118d40006bc5118d40006bf2118d40006bc2118d40096bf7018d40094bf7018d40096bd7018d4001cbd7018d4027ebf5018d4027ebe5018d4027ebd5018d4027ebc5018d40096bf3018d400969f3018d40096be3018d40096bd3018d4027e9d3018d40096bc3018d4027ebf2018d4027ebe2018d4027ebd2018d4027ebc2018d4027ebf1018d4027ebe1018d4027ebd1018d4027ebc1018d404edbe76d8940005bf75d89400b5be75d8940005bd75d89400b5bc75d8940005be73d8940005bd73d8940006be63d8940006bc63d89404c5bd72d89400aebe62d89400afae62d89400aebc62d89400af3f52d894042dbe71d8940005bd71d89400afac21d894001dbf70d894000dbe70d894001dbd70d894000dbc70d89404d6bf60d89404e7bb60d89404d7af20d89404d7ad20d89404ddbf7658940005bf75589400b5be7558940005bd755
  | 15 => 0xf6458d21006bc6458d2115df77158d2111fe42158d21004ff7558d21024fe7558d21004fd7558d21024fc7558d21004ff7458d21006bf7458d21004bf7458d2101cfe7458d21004fd7458d2101cfc7458d21006bc7458d2101cbc7458d21006df7358d21006bc4358d2111cff7258d21006ef7258d2111e7f5258d2111e7d5258d2115cff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21006bf4058d2111eef2058d2113cfe7618d210c5bc7418d21006bf6418d21006bc6418d21006dd6318d210f7e42118d21094ff7518d21024fe7518d21004fd7518d21094fc7518d21094ff7418d21096bf7418d2101cfe7418d21004fd7418d21094fc7418d21096bc7418d21094bc7418d21096de7318d21096de5318d21006dd5318d21096bc4318d2102cff7218d2102cfd7218d210f67f5218d210f67d5218d21096df3218d210f6dd3218d2100cfe7018d21004fd7018d2100cfc7018d21006bf4018d21006de3018d21096dc3018d21096bf7690d21005be7690d21006be7690d21004be7690d21006bd7690d21005bc7690d21096bc7690d21094bc7690d2151ebf6590d211bebe6590d2151ebd6590d211bebc6590d21515be7390d210c79e7390d21006bf6390d21096be6390d21006bd6390d21096bc6390d2126ebf6290d211b73f5290d211b73d5290d211b6bf6190d211b7b72190d2126fae2190d2126fac2190d211b7b42190d211b7a42190d21005bd7090d211aebe6090d211aebc6090d211b7af2090d21014fe76cc521014fc76cc5210cd7e75cc5210057d75cc521006bf64cc52110ebc64cc521006df63cc521096dc63cc521015ee72cc521005ed72cc52102fe421cc521094ff764c521014fe764c52111cfd764c521014fc764c521005bf744c5210c5bc744c521006bf644c521126bc644c521006df634c521006dc634c521005ef724c521015ec724c52102fe4214c52100cfe76d81210c5bc74d8121006bf64d8121006bc64d8121057e421d81210befa60d8121004ff75d8121024fe75d8121004fd75d8121024fc75d8121004ff74d8121006bf74d812101cfe74d8121004fd74d812101cfc74d8121006bc74d812101cbc74d8121094fe73d8121004fd73d8121006be43d8121006bc43d812102cfd72d812100cfc72d81210567f52d81210567d52d8121014fd71d812100cfc71d81210bebf40d81210befa20d81210befa10d81210057f75581210cd7c7558121005bf74581210c5bc7458121006bf6458121006bc6458121005df7358121005dc7358121037e421581210bef86058121005bf75d8d400b5be75d8d40005bd75d8d400b5bc75d8d400079f53d8d400079c53d8d400adbe72d8d40005bd72d8d400adbc72d8d400073f52d8d4042dbe71d8d40005bd71d8d4001dbf70d8d4001dbd70d8d40
  | 16 => 0x8221006be4358221006bc43582210367f52582210367d525822102cfe715822100cfd715822102cfc715822102eef215822102eed215822102efb70582210d6bf40582210d6fa205822102efb105822102ef81058221535be76d91210c6be76d912101cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121005be73d912152f3f52d912152f3d52d912152fb721d9121527ae21d9121527ac21d912152fb421d912152fa421d9121005bd70d9121006be60d9121006bc60d912152faf20d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121094be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d9121526bf72d912152ebe72d912152ebd72d912152ebc72d912152ebf52d912152e3f52d912152ebe52d912152ebd52d912152e3d52d912152ebc52d912152ebf32d912152ebe32d912152ebd32d912152ebc32d912152ebf71d9121526be71d912152ebd71d9121526bc71d9121006bf51d9121526be51d9121006bd51d9121526bc51d9121526be31d9121526bc31d912152ebf21d9121526be21d912152ebd21d9121526bc21d9121006bf70d9121006be70d9121006bd70d9121004bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006be30d9121006bc30d912152ebf20d912152ebe20d912152ebd20d912152ebc20d9121526bf10d9121006be10d9121526bc10d91210cd7e75d8d210057d75d8d210c5be74d8d21005bd74d8d21006bf64d8d21006bc64d8d2113fe421d8d21004ff75d8d21024fe75d8d210067e75d8d210247e75d8d21004fd75d8d210067d75d8d210047d75d8d21024fc75d8d21004ff74d8d2101cfe74d8d21006be74d8d2101cbe74d8d21004fd74d8d21006bd74d8d21004bd74d8d2101cfc74d8d21006de53d8d21006dd53d8d21006bc43d8d2102cff72d8d2102cfd72d8d2113e7f52d8d2113e7d52d8d2113edf32d8d2113edd32d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006bf40d8d21006de30d8d21006dc30d8d2113eef20d8d210cd7e7598d210057d7598d210c5be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d2111df57198d2115fe42198d21094ff7598d21024fe7598d210967e7598d210247e7598d21004fd7598d210967d7598d210047d7598d21094fc7598d21094ff7498d2101cfe7498d21096be7498d2101cbe7498d21004fd7498d21096bd7498d21004bd7498d21094fc7498d21094fe7398d21096bc4398d2115cfd7298d21096ed7298d2115e7f5298d2115e7d5298d2111cfd7198d21096f57198d2100cfe7098d21004fd7098d2100cfc7098d21006bf4098d21005bf7458d210c5bc7458d21006b
  | 17 => 0x41f3c435483156d7f72548311076f725483124e7f62548310167e625483124f6e62548310166e62548310f67d625483124f6d62548310066d62548310167c625483124e7e615483124f5f315483124f76315483124f5d315483119e7e605483119e7c60548315673f40548310f76f205483115cff764c831005bf744c8310fdbc744c83115ede634c8310979c434c831097cc324c83102df7764c431006f7764c431004f7764c431007b7744c43154fb4744c43102df7734c43102fd7734c431096f6634c43102fd6634c431097b6434c431097d6434c43109796434c43154fd5434c431097b4434c43155f77524c43100775524c431557d6324c431097d4324c43154fb7404c431004ff75580310067f75580310047f7558031024fe7558031004fd7558031024fc75580310067c75580310247c7558031004ff745803101cfe7458031004fd745803101cfc7458031096be4358031096bc4358031004ff7258031014fe7258031014fc72580310067f52580310067d525803102edf315803102ef6315803102edd3158031006f5315803102efb70580310eefa5058031006f950580310eebf40580310eefa4058031006f94058031096fb3058031096f830580310eefa205803102efb105803102ef81058031094ff7598e21024fe7598e210967e7598e210247e7598e21004fd7598e210967d7598e210047d7598e21094fc7598e21094ff7498e2101cfe7498e21004fd7498e21094fc7498e2102ede7398e21096bc4398e2115e7f5298e2115e7d5298e21096df3298e2115edd3298e2102cfe7198e2102cfc7198e2102ede3198e2102edc3198e2100cfe7098e21004fd7098e2100cfc7098e21006bf4098e21004ff7558e21024fe7558e21004fd7558e21024fc7558e21004ff7458e21006bf7458e21004bf7458e2101cfe7458e21004fd7458e2101cfc7458e21006bc7458e2101cbc7458e2102edf7358e21006bc4358e2111e7f5258e2111e7d5258e2111edf3258e2111edd3258e2102cfe7158e2102cfc7158e2102ede3158e2102edc3158e21004ff7058e2100cfe7058e2100cfc7058e21006bf4058e2102ef71058e21096bf7690e2126ebe7690e21006bd7690e21096bc7690e2126ebf6590e211bebe6590e21546bd6590e2126ebc6590e2153dbe7390e210df9e7390e2126ebf6390e21096be6390e21006bd6390e21096bc6390e211b7ae7290e21007ad7290e211b6bd6290e211b73f5290e211b73d5290e2126ebe6190e2126faf2190e211b7b72190e2126fb42190e21005bd7090e211aebe6090e211aebc6090e21004ff75582210067f75582210047f7558221024fe7558221004fd7558221024fc75582210067c75582210247c7558221004ff745822101cfe7458221004fd745822101cfc7458221004ff7358221094fc735
  | 18 => 0xf62549310167e62549310167c625493111f6c62549310166c625493124f5e315493119e7e605493119e7c60549315973f405493111f6f205493113cfe76cc931006bf64cc93118ebc64cc9310979e43cc9310979c43cc931005de76cc93113ede76cc9310079f64cc93118ede64cc93118edc64cc93158f9c64cc93118e9c64cc93111ddd72cc931016de62cc931016dc62cc93111f5f52cc93111f5d52cc93102dde71cc93102ddc71cc931096df61cc931005dd70cc93158f9f40cc93102cfc764c931005bf744c931125bc744c931006bf644c931176bc644c9310079e434c9315879c434c931006ef624c931016ec624c931005f7714c93102df4714c93102ddc764c931016dc764c93102cdc764c9310079f744c9315879c744c9310079f644c931176de644c931176dc644c9315879c644c9311769c644c93111ddf724c931007cf724c931007cf624c931016de624c931016dc624c93111fcc624c931016cc624c93111f5f524c93111f5d524c931007d7714c93102dde714c93102ddc714c931007d4714c93102dd4714c931005df704c9315879f404c93111fcf204c93112d7e75cc5310057d75cc531006bf64cc53110ebc64cc53102dde73cc53102edf63cc5310977675cc5310977575cc531007b764cc531577b464cc53102df673cc53102ef763cc53102fd763cc531097b643cc531097b443cc53157f7752cc5310077552cc531097d732cc531007d532cc531005f570cc531577b740cc53100cfe76d8131125bc74d8131006bf64d8131006bc64d8131116fa60d8131004ff75d8131024fe75d8131004fd75d8131024fc75d8131004ff74d8131006bf74d813101cfe74d8131004fd74d813101cfc74d8131006bc74d813101cbc74d813102cfd73d8131006be43d8131006bc43d8131014fe72d8131004fd72d8131014fc72d81310067f52d81310067d52d8131006df32d8131006dd32d8131116bf40d8131116fa30d8131116fa10d81310057f755813112d7c7558131005bf7458131125bc7458131006bf6458131006bc6458131005ef725813111dec7258131116f86058131004ff7558831024fe7558831004fd7558831024fc7558831004ff7458831006bf7458831004bf745883101cfe7458831004fd745883101cfc7458831006bc745883101cbc7458831096be4358831096bc435883102eef72588310f67f52588310f6ee5258831006ed52588310f6ee4258831006ed4258831096ef3258831096ec325883102cfc715883102edf315883102edd315883102eee215883102eec2158831004ff705883100cfe705883100cfc7058831006bf40588310f6ef20588310067f765483124e7e76548310067d765483124e7c765483124e7f64548311a67e64548315667d645483124e7c645483115e7e635483141f3e4354831
  | 19 => 0xc631097b643cc631097b443cc6315af7752cc6310077552cc631005f570cc6315a7b740cc631004ff7558231024fe7558231004fd7558231024fc7558231004ff745823101cfe7458231006be745823101cbe7458231004fd7458231006bd745823101cfc7458231006be4358231006bc4358231004ff7258231014fe7258231014fc72582310067f52582310067d525823102edf315823102edd315823102efb7058231136bf4058231136fa3058231136fa205823102efb105823102ef81058231125be76d9131126be76d913101cbe76d9131006bf65d9131006be65d9131006bd65d9131006bc65d9131095bc73d9131006be62d9131006bc62d91310073f52d913126f9e31d913126f9c31d9131005bd70d9131006be60d9131006bc60d9131006bf75d9131006be75d9131006bd75d9131006bc75d913126ebf73d9131126be73d9131126bd73d9131126bc73d9131006bf53d9131006be53d9131006bd53d9131006bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d91310063f52d9131006be52d9131006bd52d9131006bc52d9131006be32d9131006bc32d9131006bf71d913126ebe71d9131126bd71d913126ebc71d9131006bf51d913126ebe51d9131006bd51d913126ebc51d913126ebe31d9131126bd31d913126ebc31d9131006bf21d913126ebe21d913126ebc21d9131006bf70d9131006be70d9131006bd70d9131004bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d9131006be30d9131006bc30d9131006bf20d9131006be20d9131006bc20d913126ebf10d9131006be10d913126ebc10d9131005be7690d31096be7690d31144be7690d3159ebf6590d311bebe6590d3159ebd6590d311bebc6590d31095be7390d310979e7390d31096bf6390d311b6be6290d311b6bc6290d3159f3f5290d31096bf6190d3126f9e3190d310979c3190d31005bd7090d311aebe6090d311aebc6090d31014fe76d8931006bf64d8931006bc64d893111eee62d8931004ff75d8931024fe75d8931004fd75d8931024fc75d8931004ff74d893101cfe74d8931004fd74d893101cfc74d893102cfd73d8931006be43d8931006bc43d893111e7f52d893111eee52d8931006ed52d893111eee32d893111eef21d893100cfe70d8931004fd70d893100cfc70d8931006bf40d8931006ee20d893111eec20d8931005bf7458931125bc7458931006bf6458931006bc645893111eec62589310067f76549310067e76549310067d76549310067c76549315967f64549310073f64549310063f64549311a67e64549315967d64549311a67c64549315973c64549311a63c64549310073e43549315973c435493111d7f725493112f6f725493111e7f62549310076f62549310066
  | 20 => 0x2e77105963102e7e105963102e7d105963102e7c1059631006bf7559231006be7559231006bd7559231006bc7559231146bf7359231146be7359231006bd7359231146bc7359231006bf5359231006be5359231006bd5359231006bc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf52592310063f5259231006be5259231006bd5259231006bc5259231006be3259231006bc325923102ebf715923102ebe715923102ebd715923102ebc715923102ebf515923102ebe515923102ebd515923102ebc515923102ebf315923102ebe315923102ebd315923102ebc315923102ebf215923102ebe215923102ebd215923102ebc2159231006bf7059231004bf7059231006be7059231006bd7059231006bc7059231006bf5059231006be5059231006bd5059231006bc5059231006be3059231006bc3059231006bf2059231006be2059231006bc205923102ebf105923102ebe105923102ebd105923102ebc105923126dbd7690e31096bd7690e31124bd7690e3126ebf6590e311bebe6590e3126f3e6590e311be3e6590e315c6bd6590e3126f3d6590e310063d6590e3126ebc6590e31095be7390e310979e7390e311b6be6290e3126ebc6290e315c73f5290e31096be6190e310979f3190e31097b43190e31005bd7090e311aebe6090e311aebc6090e31004ff7558a31024fe7558a310067e7558a310247e7558a31004fd7558a310067d7558a31024fc7558a31004ff7458a3101cfe7458a31004fd7458a3101cfc7458a31006be4358a31006bc4358a3102eef7258a3113e7f5258a3113eee3258a3102cfc7158a3102edf3158a3102edd3158a3102eee2158a3102eec2158a31004ff7058a3100cfe7058a3100cfc7058a31006bf4058a3113eef2058a3102ef71058a3124d7f7654a310067f7654a310047f7654a3124e7e7654a3124d7d7654a310067d7654a310047d7654a3124e7c7654a3124e7f6454a311a67e6454a3124f3e6454a311a63e6454a315be7d6454a3124f3d6454a310063d6454a3124e7c6454a3111e7d6354a310073e4354a315bf3c4354a3156d7f7254a3114f6f7254a3124e7f6254a310167e6254a3113e7d6254a310167c6254a3124e7e6154a3124f5f3154a3119e7e6054a3119e7c6054a315bf3f4054a3113f6f2054a3111cfd76cca311967e65cca310067d65cca3118ebe64cca31006bd64cca310979c43cca31014ff764ca3117e7e654ca310067d654ca31005bf744ca31145bc744ca31176be644ca31006bd644ca315b79c434ca31016ee624ca31006ed624ca3113fcc324ca31005f7714ca3102df4714ca3102df576cc631096f576cc6310977675cc6310977575cc63102f7665cc63102f7565cc63102fb664cc63102fb564cc63102fd673cc631097d653cc6315afd553c
  | 21 => 0xe7558b310247e7558b31004fd7558b310067d7558b31024fc7558b31004ff7458b3101cfe7458b31004fd7458b3101cfc7458b3102cfc7358b31096be4358b31096bc4358b3115e7f5258b31006ef4258b3115eec4258b31096ef3258b31096ec3258b3115eef2158b31004ff7058b3100cfe7058b3100cfc7058b31006bf4058b3115eef2058b310057f7654b310067f7654b310047f7654b310067e7654b310057d7654b310067d7654b310047d7654b310067c7654b315e67f6454b311a67e6454b315e67d6454b311a67c6454b3141f3e4354b3141f3c4354b3115d7f7254b311676f7254b310167e6254b3115e7d6254b310167c6254b3119e7e6054b3119e7c6054b315e73f4054b3115f6f2054b3102ddd76ccb31016dd76ccb3102cdd76ccb310975e65ccb310975d65ccb3118ede64ccb31096dc64ccb31016de62ccb31097ce62ccb31097cd62ccb31016dc62ccb3115f5f52ccb3115f5d52ccb3102dde71ccb31097d671ccb31097d571ccb3102ddc71ccb31005dd70ccb315df9f40ccb310f4ff764cb3117e7e654cb310067d654cb31005bf744cb3110dbc744cb310979e434cb310979c434cb31005df764cb310f6df764cb315d75e654cb310075d654cb310079f744cb315cf9c744cb31176de644cb31176dc644cb31097cf724cb31016de624cb31016dc624cb3115f5f524cb3115f5d524cb3102dde714cb3102ddc714cb31005df704cb315cf9f404cb3115fcf204cb3100cff76583310067e65583310067d6558331096f86058331004ff7558331024fe7558331004fd7558331024fc7558331004ff745833101cfe7458331004fd745833101cfc745833102cfc7358331096be4358331096bc4358331004ff7258331014fe7258331014fc72583310067f52583310067d5258331006df3258331006dd3258331156bf4058331096fb3058331096f83058331156fa10583310067f74596310067e74596310067d74596310067c745963114e7f735963114e7e73596310067d735963114e7c73596310067f43596310067e43596310067d43596310067c43596310063c43596310067f72596310047f72596310067e72596310067d72596310067c72596310067f42596310067e42596310067d42596310067c42596310067e32596310067c325963102e7f715963102e7e715963102e7d715963102e7c715963102e7f415963102e7e415963102e7d415963102e7c415963102e7f315963102e7e315963102e7d315963102e7c315963102e7f215963102e7e215963102e7d215963102e7c21596310067f70596310067e70596310067d70596310067c70596310067f40596310063f40596310067e40596310067d40596310067c40596310067e30596310067c30596310067f20596310067e20596310067c205963102e7f1059631
  | 22 => 0xc93217d7e75d85320057d75d8532006bf64d8532006bc64d85320079c43d8532004ff75d8532024fe75d85320067e75d85320247e75d8532004fd75d85320067d75d85320047d75d8532024fc75d8532004ff74d853201cfe74d8532004fd74d853201cfc74d8532006be43d8532006bc43d853215e7f52d853215e7d52d8532006f651d8532006f551d853215ef621d853200cfe70d8532004fd70d853200cfc70d8532006bf40d853215eef20d8532006f610d8532006f410d853217d7e75985320057d7598532175be7498532005bd7498532006bf6498532006bc64985320079c4398532006f76198532005bf7458532175bc7458532006bf6458532006bc64585320079c4358532006bf6418532006bc64185320079c431853202ef66118532006f5611853200cfe76d8132175bc74d8132006bf64d8132006bc64d81320079c43d813216efa60d8132004ff75d8132024fe75d8132004fd75d8132024fc75d8132004ff74d8132006bf74d813201cfe74d8132004fd74d813201cfc74d8132006bc74d813201cbc74d8132014fd73d8132006be43d8132006bc43d813208e7f52d813208e7d52d813202cfe71d8132004fd71d813216ebf40d813216efa30d813216efa20d81320057f755813217d7c7558132005bf7458132175bc7458132006bf6458132006bc64581320079c4358132005f77158132005f4715813216ef860581320957f76597311667f76597310247f76597310967f64597310067e64597310067d64597310967c64597310973e43597310973c43597310057f72597310967f62597310067e62597310967c62597315ef5e31597310975c31597310967f60597310067e60597310967c60597310073f40597310067f74597310067e74597310067d74597310067c74597311667f73597310967e73597311667d73597310967c73597310067f43597310967e43597310963e43597310067d43597310967c43597310963c43597310067f72597310047f72597310067e72597310067d72597310067c72597310067f42597310067e42597310067d42597310067c42597310967f32597310067e32597310967c32597311667f71597315ee7e71597310067d71597315ee7c71597310067f41597315ee7e41597310067d41597315ee7c41597310967f31597315ee7e31597310967c31597310067f21597315ee7e21597315ee7c21597310067f70597310067e70597310067d70597310067c70597310067f40597310063f40597310067e40597310067d40597310067c40597310967f30597310067e30597310967c30597310067f20597310067e20597310067c20597315ee7f10597310067e10597315ee7c1059731014ff7658b311657e7558b310067e6558b310067d6558b31096ec6258b31004ff7558b31024fe7558b310067
  | 23 => 0x19f6f20581521957e75987320057d759873218dbe7498732005bd74987320979c4398732096f7619873202ef461987320979c4358732096f46158732004ff7558732024fe7558732004fd7558732024fc7558732004ff745873201cfe7458732004fd745873201cfc7458732014fc7358732096be4358732096bc435873211e7f525873211e7d5258732096f73158732096f4315873211ef62158732004ff705873200cfe705873200cfc7058732006bf405873200cff76583320057f75583321957c75583320979c4358332096f86058332004ff75583320067f75583320047f7558332024fe7558332004fd7558332024fc75583320067c75583320247c7558332004ff745833201cfe7458332004fd745833201cfc7458332014fc7358332096be4358332096bc43583320767f52583320767d5258332076ee3258332004ff715833202cfc7158332186bf4058332096fb3058332096f83058332186fa2058332515be76d9132176be76d913201cbe76d9132006bf65d9132006be65d9132006bd65d9132006bc65d91321779e73d91321b79d73d9132095bc73d91321b73f52d91321b73d52d91321b79e32d91321b79c32d91321b7ac32d9132005bd70d9132006be60d9132006bc60d91321b7af20d9132006bf75d9132006be75d9132006bd75d9132006bc75d91321b6bf73d9132176be73d91321769e73d91321b6bd73d91321b69d73d91321b6bc73d9132006bf53d9132006be53d9132006bd53d9132006bc53d91321b6bf72d91321b6be72d91321b6bd72d91321b6bc72d91321b6bf52d91321b63f52d91321b6be52d91321b6bd52d91321b63d52d91321b6bc52d91321b6bf32d91321b6be32d91321b6bd32d91321b6bc32d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bd51d9132006bc51d91321b6bf21d91321b6be21d91321b6bd21d91321b6bc21d9132006bf70d9132006be70d9132006bd70d9132004bd70d9132006bc70d9132006bf50d9132006be50d9132006bd50d9132006bc50d9132006be30d9132006bc30d91321b6bf20d91321b6be20d91321b6bd20d91321b6bc20d9132006be10d9132006bc10d9132515be7690d32096be7690d32514be7690d325febf6590d321bebe6590d325febd6590d321bebc6590d32095be7390d320979e7390d325159e7390d32096bf6390d32096bf6290d321b73f5290d321b73d5290d321b79e3290d320979c3290d32097ac3290d320978c3290d3226ebc6190d32005bd7090d321aebe6090d321aebc6090d321b7af2090d32007af64cc9325f7ac64cc932015ee73cc932017ce73cc932016ef63cc932017cf63cc9325f7cf43cc932097ae43cc932097ac43cc932097cc43cc9320978c43cc932005ed70cc9325f7af40c
  | 24 => 0xc2090d526573e1090d526573c1090d520057f74d85521a57e74d85520057d74d85521a57c74d85520067f64d85520067d64d85520057e73d85520057d73d85520067e63d85520067c63d85520073e43d85520073c43d85520257f72d85520257d72d85526367f62d855264f6f62d85526377621d85526377521d855219d7e70d85520057d70d855219d7c70d85520073f40d85526376f20d855263d7d769855224d7f74985521a57e74985520057d749855224d7c74985520057e73985520057d73985520067f63985520067d63985520073e43985520073c43985526457d729855224f6d72985520cd6d729855256e7f62985520e76f629855224d7e719855224e7f619855200777619855219d7e70985520057d709855219d7c70985520067e60985520067c60985520073f40985526476f20985520057f74585520073f74585520053f74585521a57e74585520057d74585521a57c74585520073c74585521a53c74585520067f64585520067d64585520057f73585520057c73585520067e63585520067c63585520073e43585520073c435855263d7f72585520076f72585520e56f725855263e7f62585520cf6f625855200777615855224e7e61585520057f705855219d7e705855219d7c70585520073f405855263f6f20585526357e761855224d7f74185521a57e741855224f3e74185521a53e74185520057d741855224f3d74185520053d741855224d7c74185520057e73185520057d73185520067f63185520067d63185520073e43185520073c43185520257f72185520157e72185520257d72185520157c721855256e7f621855262f6f621855224d7e711855224e7f611855224f76611855224e7d611855200775611855224f76211855262775211855219d7e70185520057d701855219d7c70185520067e60185520067c60185520073f40185526276f201855219d7e76d81520057f74d81521a57e74d81520057d74d81521a57c74d81520057e73d81520057d73d81520067f63d81520067d63d81520073e43d81520073c43d81520257f72d815261f6f72d81520157e72d81520257d72d81520157c72d81526167f62d815261f6f62d815224d7e71d81520057d71d81520067f61d81520067d61d815219d7d70d815219e7e60d815219f7a60d815219e7c60d815219f3f40d815219f6f20d815219f7a20d81526177920d815219d7f76581520057f74581521a57e74581520057d74581521a57c74581520057f73581520057c73581520067f63581520067d63581520073e43581520073c43581526057f72581520076f725815260d6f72581526067f625815206f6f62581520057f715815224d7c71581520067f61581520067d615815219d7f70581520077b605815219e7e605815219e7c605815219f78605815219f3f4058152
  | 25 => 0x8243006be3258243096bc3258243006bf7158243006be7158243006bd7158243006bc7158243006bf5158243006be5158243006bd5158243006bc5158243096bf3158243096bc3158243006bf2158243006bc21582431aebf50582431aebe50582431aebd50582431aebc5058243096bf3058243096bb30582431aebe3058243096bc3058243096b830582431aebf20582431aebe20582431aebc20582431aebe10582431aebc10582430057f74d8d521a57e74d8d520073e74d8d521a53e74d8d520057d74d8d520073d74d8d520053d74d8d521a57c74d8d520067f64d8d520067d64d8d520073c43d8d520257f72d8d520257d72d8d526767f62d8d526876f62d8d526775f32d8d526775d32d8d5224d7e71d8d520057d71d8d5219d7e70d8d520057d70d8d5219d7c70d8d520073f40d8d526776f20d8d5267d7d7698d520057f7498d521a57e7498d520057d7498d521a57c7498d5265d7e7398d520067f6398d520075f6398d520065f6398d5241f3c4398d5266d7d7298d520076d7298d5217d6d7298d5266e7f6298d521976f6298d5224d7e7198d520057d7198d5219d7e7098d520057d7098d5219d7c7098d520067e6098d520067c6098d520073f4098d5266f6f2098d520057f7458d520073f7458d520053f7458d521a57e7458d520057d7458d521a57c7458d520073c7458d521a53c7458d520067f6458d520067d6458d520075f6358d520067e6358d520073c4358d5267d7f7258d520076f7258d521956f7258d5267e7f6258d5217f6f6258d520057f7158d5224d7c7158d520057f7058d5219d7e7058d5219d7c7058d520073f4058d5267f6f2058d526757e7618d520057f7418d521a57e7418d520057d7418d521a57c7418d5266d7e7318d520067f6318d520075e6318d520067d6318d520075d6318d5241f3c4318d520257f7218d520157e7218d520257d7218d520157c7218d5265e7f6218d526676f6218d5265f5f3218d5265f5d3218d5224d7e7118d520057d7118d5219d7e7018d520057d7018d5219d7c7018d520067e6018d520067c6018d520073f4018d5265f6f2018d5241f3f7690d520073e7690d520073d7690d5241f3c7690d5241f3e7390d525153e7390d521a71e7390d520073f6390d5241f3e6390d520073d6390d5241f3c6390d521b73f7290d521b73e7290d521b72e7290d521b73d7290d520072d7290d521b73c7290d521b73f6290d521b63f6290d521bf2f6290d521b73f3290d521b73e3290d521b73c3290d5241f3f7190d520073e7190d520073d7190d5241f3c7190d521b73f2190d521b73c2190d5241f3f7090d526573e7090d520073d7090d520053d7090d5241f3c7090d526573e6090d526573c6090d526573e3090d5241f3c3090d521b73f2090d521b72f2090d521b73e2090d521b73
  | 26 => 0xc0018010002001000001c014017000006800a0210010000006000007009400a0010018010002001001800000c0000050018036011000807000200600280000b2024000004c006021000000000e00000b800c044000004801c004002001800000000200280000000020018008004010001000000000d00c000000200700100040140000008014000004095bf7658a43005bf7558a431bdbe7558a43005bd7558a431bdbc7558a43095be7358a43095bc7358a43096be6358a430979e6358a431769e6358a43095bf7258a43097af6258a431b6be6258a43096bc6258a43097ac6258a431b73f5258a431b7ae5258a43007ad5258a43097af3258a43097ac3258a43005bf7158a4326dbc7158a43096bf6158a431b7ac2158a43005bf7058a431adbe7058a431adbc7058a43096bf6058a431b7af2058a43095bd769864326dbf75986431bdbe759864326f3e75986431bd3e7598643005bd759864326f3d75986430053d759864326dbc7598643095be7398643095bc7398643096be63986430979e63986431b5be7298643005bd729864326dbc7298643006be6298643096bc62986430073f5298643095be7198643096bf6198643097b76198643096b76198643097b46198643097b73198643097b431986431adbe7098643005bd70986431adbc7098643096bf6098643095bf7658643005bf75586431bdbe7558643005bd75586431bdbc7558643096bf6558643006bd6558643095be7358643095bc7358643096be63586430979e6358643005bf72586431b5be72586431b5bc7258643096bf6258643006bd62586430073f5258643095bf7158643097b7615864326ebe6158643096bc6158643097b46158643097b73158643097b43158643005bf70586431adbe70586431adbc7058643096bf6058643095bf7658243005bf75582430073f75582430053f75582431bdbe7558243005bd75582431bdbc75582430073c75582431bd3c7558243096bf6558243006be6558243006bd6558243096bc6558243095be7358243095bc7358243096be63582430979e6358243005bf72582431b5be72582431b5bc7258243096bf6258243006be6258243006bd6258243096bc62582430073f5258243005bf715824326dbc7158243096bf6158243006be6158243006bd6158243096bc6158243095bf7058243097bb60582431aebe6058243096bc6058243097b86058243097bb3058243097b83058243006bf75582430063f7558243006be7558243006bd7558243006bc75582430063c7558243096be7358243096bc7358243094bc7358243006bf5358243096be5358243006bd5358243096bc5358243006bf7258243006be7258243006bd7258243006bc7258243006bf52582430063f5258243006be5258243006bd5258243006bc5258243096bf325
  | 27 => 0x6000e000000000000000f001000c004001002000000400300a8024010000000000c00e004003000000c001004806c01a00000000000240070008000000000006800002200100f8008000002002802000000400d000802a00300300640000080008008000002001800800600301d006400001c0010000016000000002000200d005000400202e0028004014000000000000600000080000000060000098016001000001c000018000800000c0000058004018000000000000e002000000000600001b800400000f00000080140000020000006000002801c0140040000010004005000000400a0010038024004001000800400601f0008000082000000000c022004000000003a001004001001400000080240000030018000006001000800000400b000000c0020040088000000006002009c0020000000004042000000000400801a00b000402400300c003801000b0018000000019000001000000400000000240040050004004000008001800000100400000000010000014004001002000400000c0010010012000000800003400400000100020010010038000006002002400600700900000060040018000000001000000c000003005002401c004002000003c003000000c00a002000000000200a000000c0440010000034004000000000002800700180380000030008020016015004800000200500100000000030008068000008015803c0020010000000010002000800000e003000000000000000000080040040000008006013006000c012008000001c006005000800c01800f0038000000002000005c00000900b800003e003005803800401600280000000150008000004001001001400c0040048040006000004002c000000001001800c0110050000000003000000800a0060010000004006000800c0020000028014012018000001000001900000100000070010000000000001001000c001003001801200100c000000800102580140000020000000014000009002802c000000800000c007002001400600300080640000090000008004003000000000400000080000120000008004006000000004c000001000800000001d000007800000001e000c006012000800c01000000580640060110078004008018000007801000200080280000050000004002001004800400400b00000180020070000004044001002802c00c0040030000000001004004000e00b004800003201100480000000000000074008017001802c00202a002002400000e002000000a001001000400000100300040020080010008004001000806c01201e00080040040000000048004002000800400600e00100700040000020010002000004000401a0010038014002004000800400c001000005000000300c001400c0000000018014010000000800a
  | 28 => 0x8038000005014800402800a0000014000000000000c00400300300140000040058070002011006801c02e0010010008000021001800800000d0000004008005000001c00000e000000800000a0020068002000003800802c00400c002c00602100800000000040008028004000007800000400200880080080000010000000002003000401e000006004401604000000c400000d000801400a0000048008002004000003c000008000000c00000900000600000000008018002004001001802e004001800000800b000002c008005000800c002006000801000c002000000000c0080078008002006001800800c0040008008000003001002c01600200c8038006001000807000600000000100120070018000014000000001c03200300180100000000018008002002001001800400b00780000020000010000020001000800c000010000800002000000a0024004000001800c0020080038000000004004002000000500000040000000050000000000006802c00e00000000040020000008000002001000006400a008000003400e0040030008006002005000400800000000000120000060004004001001800001a0190000000022001007000400400100000140000060040008008000002802005c0010028014014011000000001c00f00600200000000008014000027000000c0140070000024004001001000c000008004000c00200600100000060040038030006006000000400a000002800c016000000001800200400e8020000006001000000c0030028000000001001001800600a000000000e006002808401000500380280020040000000004008002001000000a00080140000010028000002000001800000800c0000000006001002000c00e003000000c00e000001806c000002000801c00600f0010004036002001801c004000000800800800100000100080000000000000017000000400000000100200020040000024050001002800800800000f80000000000098008006001001002c00000300280000080160008000002001000000002600100000080120040030000000001000001401200200000100000020048000028004000000001600200c802c006008011000c02000100180180020020008004002007000800c000000000001400a024001800400e015002800000c0040000034006009000000c00000c001000c00600a000800c00000000c00000040060068008000000000807800000001400000020000020014008004004000400000000380140000040048000002002002000801c00b002001c00a00a002001c0000000000008000003004000400a008000800400a00100000200320000008010004004000000800000100d80000000010028008000000003009400400100000040080080020004002000001
  | 29 => 0x493d045980d24658f8e5629ef44dd97340e58f3879606a200000001b3800085601763031bfa4f8004c859a3221ed07906c0800000000002ed80006ae8b50000171615200000a0991e836162c04e8a301df0072000190a79b97a6485236032100002e911ce4f117d058697ac65993c24d48208851808a6c88c3c48119c872007b60291cea48c968c1ab87d00000b025e192fe00007b034495cc0000cc6000057e8631a60000000034980000000e0836c80000000b4a00000000000000171210643c0000883020a69c800012d80006bb07520001ab06e49df07dc00a63b700004b7947c46c1d30016000027a0000023800000000005d921b6000000015380000001fb6000022a047185c00000001e205b81619ad6070089e7ff232067084cc1d0002e7f907c21dc997c55200001b1111a48e18a87f217ea7e7816e36c034c4f283a66808a52789933a0000b1200000000000e7674519f80000aa4000000023d1b74000000000004287b896947918ffa58b8f46041800030d09fa000000035b00002349de2861800040e800040c000064187d8312197a56c81ea00000006c10008000000000007d400013b2148845a4f621a87a082128d021887b39be473a23000001fe0000000000003ae78ca29c00000007500ac057715d66f322f483780000979e0e53a146200000006619c263cf1f8a54a05e21cb90b000018f856307fe054803c0001dea33985607b9198253c92840ce81c236d0b28000151e79310dc3e680000de091e00017a0000000082d893c1839c100b1937e3a590100e68bac48018d81859cb45940000341a130207181600018c800000003b38e8409185125740000000012e0000000000000042100002da10cc160800006723802d3969c00011a0615070e0000000008a36a7fc9f0c3c51a1864804b028587804c48000884000000000000001fc66a58e661c9000073310ee0000476000000000001282770c14063995e0388e404c701fc66722da6b983d271b00000000000000000400600000200000000020010008004001005803c0000000008038024006000802800a000003800400800100080200000040000048012015000000c004002000801c00403b0010004002010004800000200d00080280000000000000000000001804c00000e003801c002000008000000e00100300140060160018010002003000000400000100100000040030008050004000002000000000a0010000006007000000000000000300080040060050034008003000000c0000000008010000003011000801800000080540120000010014008006000000000e000003000c04e00000080200200010000000020004004001405c0020028004000001001001401000f0030010006000007802c0100000008030000000000000800a009000000c00600300b002c02
  | 30 => 0xfe00000000001d0c0001a8a556913a00005266e100000001d5e0cf00000001028000000000005e43ca0706433800039183a000001947f71bb84fa163221f000000016a85a4000076b00005841992000000030b12c029b13b469b8000222055c6ef93cc57086c0000069a0001a7400004de3db1d80894075a7f680006b6976e6d48b1073d212000014e42291738418028e887030400007ea00001005710bcc4868d5a3d20bc60ada3c200000000000d22000000082a80000fa0264725238655f8000000000024500000001f2a54416923351cc2022157c0a799220f00f3067a80000f5000014b222e2cb14b80ea9d166d68b440000bfe00000000b8026c0000ea81f793041a60f5e75d91e85d1958600017e8224000000018ea82199a60001ea015c88782e281a460e9ffe40200004ef000034c0000000000014e800000019ce7509a1c88fa03200018e2824a2843eb80000000af082c213e59107b2121992e1ef9e4e7871c6a71d80000000b225298ce080c07ac52a0dd837f14a07e08d1e23086d25fd14945041f2236d86cc0bc970232f80006f4800051d00004cb90c27aa9e0217e8000000128613f17b800009aa33703ac45500d68438000000177a29796382d50ed25ad9a8e52f98a60d100001e280000000d7633e800070c180c1c411904ab0d145b780006908b8071c968a2a48f5a377105e89b1f6033f9cf23e21fac873035a37ca0505b990e036a9aa253380003a5090000000005b317c00cba2563a611268e210041ab1e9c0000b9600000000001f627589d8a57a1d003341cee02485323fc18ac1e4800032b8b7847c88680000b344ffa1bc45402fc0001a2807b0d7066a18980f30f742b99e564d88f3e46b89887078cf85d6160426b950a872877a000143681600a20000f6e31002a43b10f7687987dc4fb0f4c0d3914200019620fb800064f83c200013326cd0a3e05e00003c9000078e95262300306000164e00012561e692c4882005632296f4131092e8678ede0cd00e66fb0000530898200007643c0899a1ee9ca446386d459b895e5be1458383953c579981e0b52304000213c08e800019b194c85c0c1c11f8b40813a1c6139a0ce014225e3f20070398007c87c9d943ed21426e88588094011873e83b2123a05e2b7109e5c314ec13613a282380003438b2029387ae23380008bf22d261aa2907b50498021080c3b522d084917e241e027e0001fd88c29aaa55c1c9046023b64908000263209c8550a9e67ba34800000001e800000000000000000000018422d6097c4379afe4a38348154167c7de0974000193844421b40001e9e000055a49d0e6a313a25856f22cc5d080c229a9a327e922767541bb637d80486a49bf04db80aa7ab17480d715a858600ca47d05c877282ec53686a00000aca16a0f0e691800000012500000fde88
  | 31 => 0x7b884250114e683680003f196220001098680015e88b02d202d9f6c70d07222801f403959ce61ac82f047e8410000021413d908823c80005bc22ba02185286659d8e32419f42ba99dc0001d38000075c0001aa4202179a0000000804821e2d21ea200008a20001d201948bee75e9eb400000000000f0a7198000000000000012600f39c14085943e0000278000069c62c92802531ef024c178c08804b800000008b28c0800015ce19b81825f99eae23798687280a580258c4c00000003f089f86d30e34000195209398da6fe000000000005120e740000a6645f00007ee800046600000a109ba4538f1600023ae88e000000008b031e8a863b09fbc374800037b80000001a0c632856425a95da39688dc0000bde30582d03d71a640c295e078b800028d03080000000776000083b10d0275235c000000000019a46701d6059e000000000003f58000000000066a80e40000eee3bb02ca5830000025010c6cc934869a900e1121d701171fe273795ca000037e67e9c5260080004741f980000bc48c680008c6083a37194ae0d00b166ea21407029d226e292d6261917810680006c40afe010146613a95a2000165e12400002048000295000005f8a1c00003688a2812287b800073204c2000046c00000000000000000002432d06087861d541db9da48d5212863015de0002312576140c2201ec25a394084e6933e0b080002e6800063e866818900000fc94203da045055804a6078821842ca22a7410f002fc9a3c1409b6e00015ec44d1a70088987c86c8000214201e0000000000213a000016836e08aa6da102c179963a07d13a820c195c272a1d400000005f29d2862180ae37594648ac886c881000077515727880ed07449e6686c057a221116438580000001eb0551800015b8000000112e378867200008ca5df8f7c587a0522c302600000a808038fa886880006d605d8406878e30788967f286d63f98ad046a800021105987e5932a20590aa7d6000022e00002c120a600000000001ab600017bc236a34a0001a5655e80004af8ca600009f20000e54000000000000000f4017c656113c7978e5e4a801167c68abc0000000000000081e158440a9c006f7048c33f0f20343211e6a98d2a000000060480002f9098a217868845a226613906f212a1b8272f238244301f616f925822b8c2833586504c290708b88000469866a0001a2057c149e82f0fa43c6806263500006b519ba20b15ee62a91f076a165659620ac7bd9a6c4a7178264a861e306800000000003a416b0195055803380005bd96aa77f00005cf1a065ef9e9623b1a8629a00000f7a3cc0c300002e19c0435580324f199fe2c18d84000000000015023e9800012480005800ecc5f517b673800006fb80008b2000000000007cd92924c3a2365c9198011600000001db000015807ba9c
  | 32 => 0xdee1a0031c58d02a8103800014201ee73d88ba820101238080007658000249949a1959c2a7d689ce4828000730149c0ce0f9c0001c8c7c9a22000000006fa073067680dc36f18a4130092c2ab18d6528800013813f03eaa33e74f15fc270800000000000001c0e31a00000001cb886e9fb46ec15a0567846601b8cea71700fe049156c3ca8b1419d19ac5b516a216c971820c9c8e0b22226545824c0a583601ea1ca827d92d41bd0c2e86088a810a8fec7621ea83f91b7e678800000000007f587f000021fa000000023300005819bf20000000000000000000002cd8000000101c00000000558c5a13c000001190c6076190e3f80a40072800045f96ca364800000000001810e9a4cc10be3df9b8e5c7914a0001d9c5ae80000000000777800027c1ab400000c02719e941d60206701a31e6ba82984f217c48f2952a81800000909f8845c8e20150137a42495143d98000258237c6a6199888799e68ee846800000005fc0000000179e00016dc000136a6c1951c7c1a09e00000003928f044d097e000002da4860cc885b155c00000003a31b54000153000000000001cda2ff238c5e1192688c020c4a58ab85cf980e605090e49a046a00590f44238f623ef060680f22d817e0f1e244000076e0000000214867c000000019082769740000000000019d00000848369a2b886e134c00519b82ef92cc55d19d264697a881d0c2025398e666c001a0b7800020f0936718800027b23648c19ce2710018a323800033080000000b8217a9f3c000130083b80003552324393928a07c94dc35c83be870000045480007980f100000e821a3868a05c00000000a1400017f85bb9d24000196e000000000021f446c88748738c10000000000008544cf000000000005b681745c7000024480020001c120001438000000047600000ae12727e7000000007c672c8004201136c19022c00f280006689c7e000214e10e00006b620c62ab8d8061d11003b69018878922a000000018500005fe88d452381bc18680000001ed052e81e45a100004240a0c41021e4000119e17488e861580002a71026410800018480003d58000585800000000004881bc0550800600000008b38e4c4a21d3e6de08fe0000d2c2e60d323161fee6a3082e61300000001abe24a1ba0000027a000000000001de3ba800070a160a0001b0a3e79afc726153e563a0e862480007ec083e177887a01701f045d8b762b10000111887e0441e8a1e121d88ab919238c1c9c3f5044a6c68eca3e10b6038502e81368bce32f15c60129c161b0840081088e453493e619310ba61f80000000000787800000008ea0001fd26aba1e80000dda231034600011ea70e00007a68c9816581fa0000f8a000199a6c300002fd800055e00008800aaa472837655d939c21a946c8528c026cd8ab25c19612888a20e1
  | 33 => 0x4ef80008d187a48b900004501a50725a38e2701d8620502f432e0f4e6340bda7fb00da3408e52317226289f86288d48944613842035b94e20ed0f820d890e83a385fe028155013b217a1db03545529c2c00000747da875000002b000005544bd962481200000bd91444b986e84a40c962dc031687b0aa87bb8000000208a77380000001476000000000000006c78000375120600023680a48c8253ea2a60001a54000000000002d664f04627c604705ca80004d285e8813000000017d8469027400000004a60000000000071c1a08000154436393d4618a08c2590abe53c0bbc000116000005ac00015380000000000000048f12ce79e80005ee80002ac09e66a11de65e420c20001fa60680b7c51711060001380000191004d224a38115ea1c200000000d52699800069f800000014d638795f232a8a321921ae42c297b40000d7a0001f5c37800000001d688c59d021c094861bb11fc000125a4e79faa0a9938c2230c66000000068382d8197814200020e68610000000092a3cd1b72652a3940002194000000000000000630000000000016d8a385a98b6400000005d49cce017800039080000000236000071863b0de67e4942a000141221d8fb28d322b47fe070a6a0a3420f69bf43fd189c825076250a0c742550f962f20f0c02f98b88059d6c4c893287b81c182f48eac7f5217e0f200001ee104a0f109e00000c0a72b01b80001cc4698a022000234456a9ea60a198de303800024e00004e2160255320548ea8ab45591fe88d7935429122aa6c515ae0000dde8bf9ca239b000052906b00a4100c54c80b81108d00114987054b82721251fa20be046067791b64450a5a5620ea67d28000268843c88ca12228a94fe49a800078d80006d88a8e5ba983800000004208c7001b096e6bc9832455863e122a2480000d9000016a01c715342ea80004eb000076d00002b0927849c147a53d80006b2862a0000c9c4a50f541981e046d100001e991de8431c3214a95041ea801845223085640f3a1dd926277422862470a745950c561e180000b9867c08e0000000237e4b40c7648386763f00c3e637051e0640af26168000155869e7109e3e000000000012aa0000d24000119a51b9a167f419ec00022be00019322089f386ca0000000128c599a32c5208f7264a239a1ae010400013ae68c0df04d70be61929c5a6520000000207e1f5911200000000001f7a328a1903bc8f4a00000007ea07d200018f067f0a603f40c9283f87a241a18044bd14720cc057c1be1abc28900001bd828a09a800057d8f6a2e4874e2e50d8c26710061b9000069122827428000000000081b000045180008eb1b560001a7a00000007e68ae40000bec2a9800000000008be8d5800000004c900004d817dc1771a3824300002b514b017d0000360a0f80001
  | 34 => 0x803a000000032c8d7e00012f000f81547af195a75386961a4004448080001831ee655b8ed8000024a7689b8022f224c4321682506815a74b0000493800000012a81be9fc03c71cae7940cf4000000000000000000e44159800016880000001f2c00004806339b240001da603200006850692874a29645e9eda000019e0000370212930239b97d22d481e6347000000013f80000000565800012588e036581300000766260148a0000e70000000000000008d600000000a8461c80002be962000002546f4049a88a0000000000000022440001ac632901d044f89a475f005254200660c38000000000006b9d5232a21ac213998e52f051a68e8a0282d032014f00008e8813210e98b008913aa8d58ff235418665c28ce415a000055392da278888e0000d3c479064e4841f8e0a7000029d948c1048d080000dc48e2888a00023c03c994404d387c428d93f64489d5a41502266631b204ce145610d8d400000f2c63180bc28a055264d150e20a83244ac000047581a202301c45a180007cf8e8a72aa11635e00000f90d1a00000ac50d000047d8cf606c80000000c3000000000000a186d083320001f7e059000068680008cc000071d08585751ee800007ec461203a57f99cc6828cd8512a26005b1c4e7ac80c46d80d10256894060d96bc6cf80004e495003e3119484a81b661220445991bfc7cc9a7c43f17a400000006b404fe81c800000009d87390ee62869d4478184024ed9d321b780000001e8e26823bc000000051a80000000000598208413ea2a418d80002f5000065194b2357812c67509b84428000137000000012080001e400001d9a3480cb6000000046f000062e800018d000000000000000fe22d988d08f383b000016d800012dc7a200002561b7c000000000000000000000000152200000001c5800002680007c0800000700007e1800000016520001df4000173a8101636000000060008c68ab000075f82bc4c40a503a799e8000000000016a43d082b23b18000784005400009d279e00000d991e65db1f4827593d63fe16d6000207623e954089c16763111306224825275900000001b9c17c910279122926640fe85598aec41c915c41300f67318c060000810037832c3f119144d584be1fa010a29703b812914b400004d64b09a360000bb416910441c7841841d8f803b20ef40f80b1881988263829df861b9f80000065a000000000000d844a800000000000c61e8c6e9800054b0d16211987a0001480423000066111b844720f60e2111e3a70e6476093205bf21381af959c7721f468c095c800002a021689c829910500001bd444e183486705da513931433a0acc3331a1e25b00d489513840001d723ff8a720a00b262cf04886ff827c3d90cc051e1b30000000015b031a00015e214c0fbe6551f1653b975c0000a7e372215c
  | 35 => 0x26a13724e90dba397000039f0e3265900360001316000000000020243cb859478a000003e1e00000165a81f1b980001f1c4f680000000a2c00000008db00004b480000001e0a0000c320000000000000000000005c01b4a3af8c64000000083100004081eca5111ec42d094de8bc05845a68afc6f80e284b619c619f991885589342d88b88000002c259a1440a895361f316ce45783dc8011f52817073c4fb818011b994e1a09c865560e1c000127c07496d08c386ca7159390000189e00000000000000271000089e10bc4d616fa3849b7626589fc78697568268c725f38e7a14621143de8b6a06a800000015627091fae28881925259512201826809c1afa14b8fee51680000001d9887105d400017ae50c92e423f0eb81b6149289b9db20000ebc65103e271a1fea00021722fc1fbe73c21764749246000228800000000001b643ac0af482a03e665d841c8b98ed616e962680d95687769daa1de1dec00000000001c02000000000008620540f7046e80000000248188800069618f48ba8408438a11c000000048d8000514000040e1bac2321dc400000000001f723ed800000000000001ebe0000000000148449318f642980000000a480000fb800000000000000000233452400004569f0e00000006f69ade7d920ae000202642192fa14100008cc925200000004328478000000004518960000000835916c0000bae0000234000100044d8b4649b979820a04d000020ba18814cc00000003a905ca0000b320988ca043498c44f780008780000744000000010225578cb054618105fb08246eb8c6041a835600000005c69df643c800000004ba0001a10249094a80b000036714147329d9000010568de8cca0001b2a00016e00001e4a5df1f34000000075e00007b3000037e8204000050a00003fa06a21d000000000e3859c000134400000003c180006db21a00001e524df19f608f16402b18bea37a9b2c30017d6350a09688d08948411aee007953a00000005cb023e3369dc65bc838a1cd8bb04ad80003a180005b080fa79c80645fd8000844043000018186500cf20000f320a31f24000000000009420240000693800083295fa0d400345e2800005884bc000000000009fe0000eb4000216e17800000001e7481a893e4e0800000000000001d6e885800000000000000000000000055a84aa000179658a91286c48e680db9ab8000000000012ea70f1d1e1100000000000037080000000fca28ba28e7749ddc5dd8796163135a3e8107c31798762ea000026c81200e7800038400008a300ba3e61a243ad880a368050601e864287580002f0000000011dc79a8ec066d164a2f8800061793ea6ab17501c0000027b8000471949823e0678072000063900004458a040000b8426980006f8921c4d18a9600017de04d8eb216b81462409fb87bf
  | 36 => 0x196058a20a04ae8af86f386da51c10d60661882000000000000005ff9064000000075983bc44100007cb800000012c68cf00000cd8000724a2183cd800066f000004f916e7559bb200994e014e0d6203b12b850280000000f860001bea08a18220002240000213472c063c45608528db9a4c4d9907a0001b1803d000000000007be90ea4f911cc2d680005ea89762641b705ba18a05ac867a8991ac807800008690b001b400001c1093a00000004391894386890632200008e10fce8d980001df80005ad000048a00000000000000000000000007ec80008a6000000000005070000284000037d000055506fc86a80000001f0400010d47db893231412226070000000045e684800062f837a00000b440d00001d5a0fc000000000000008349c3a64b15b60000fa22820c621089e620000000742197031f06c648993967b19c604ee13e24bc8b568cd86ea6760b08640229e87a8728507a150647211a2b381b429282760e522dc59c93ba24692f801a0ee442023143b89e5c394000061b126459b15a482e167400814c638880006e50c9a000155200000004438000622000047b0f22000183e7298efa277874c18e21745b4841639f9e868040ce212786c80be98460a5058a1530c2a812a27285a00001dc1a481d19b6a1191bca8f121ae73700002c788b25001ae8446021a65f81a6258a3a6711984428192b41cc96ac7ae9de02518e8029c23762ba0f081f802c00001bd83899916000000088906b40998a788969e5412106a830117e439e00000d782b46068d28248085c439a2d44910efe85797b268b03a247017303aea3c6602121e0001af4323218036680004d013368ba097e0808a5649f8968000196a24215f44c9822e35395c02cf9e90184000a21ca2681350e928a0182e6c98f92000122e26b084024288d647e071483700007461a9c7d980004d4142c2d7889c000227c0001792000000018280003ee87345060230000042c11f1d920e10a6e78c1c544de043e472190c000072600011a200010742a520cc197000000000000000000716059a36500788c31da000004f487e06446f5968000392160000a0a053a2c65648000031826e73b105a0001f1243f80005cd8b3a0aa80000752132624000018700007c51f081d79904665214c20697da186036c2c7201a7a91760543202e8b1226a81e800031b000048f8000164a34e5f205c24999ff403b9ffa6181468000030065c9d5c0fb00001ef23927221adc11e800000000006fd96fe2ee19e0449103e26788a06c580006ce984a6149364027219883906fe0d60ac818000000000000000201c8a8094807fa3a834b807677098fc1d20188000014877ca0e04628000241000046f853600000000000000000000000014ac00000007b5800086f8000000174a0b12160000009e00010580c4800
  | 37 => 0xfa84ee64485a029ea0346a80d883ec0f186b39f8c50b96be430042e34e22f2000138e293175a6f10d180000c1841880004a795a689080008668288000000048d00b000000008ee19024670be000015b01f200007fc000000020d0000051633b905c11c95940ab07ee00007982e380cc8c70fda5d389be00009722fd17c2431000025e1d4c800233a08715821cb1f1e361902e20e100203f0e4833123b06cf08664a09e682651c9a0d085d050e98843d10590274200c31290466ea8dce6d390f68d8a0be396239656ea1f685e195079f120c49da3264aba23a42e1b9e00008860ff9b00000193a0001e161fe8c460001c7a21ba11222d806a1f897702a20ef84c60c243528a9a0571d3643682be327a2ec0448dd0127000004680008698000858800080e0000000000000016e26d780000001fcc83e83c62b48000405000044b13f2000000000000000000646000056200009b4000144c78e01445e700380000d7c000125481c00000c993ce000232a7bb20f25a5a00635100286b885fc6d19ef203c1af058710fa1ae91741209d3a6a785d646d17080001968000205600018300598000000000004a9ec02a600007c289f40001d4800000001c680006ee947e8cb83a859f800000000000901cd679b0d4c05c8ad60e496624d7800080fa15a0b389cc1ad814c7b2000041b17320618b7440c872a0000b4c57e025a59200001d81f5e5da800013a0fdc12b8b7e23d8898000000040785a64bf00003410000000000000015b4254227a000124a6b000002f4000038900003f301ce69488d82c38000000035256f80000ab80007c0136845c1a3e0a693a68639b88132050c73f03f058f132c11d0684462058e7b600b20000e886ce0000298800026f02cc0000000000000058c00000001a04000013c555a10a585000020d80007dd8000000000018c00000000000000000006c22f869a000000004ac5c40e2a000018400003b600000003aa92ee00000000da8000000066218b8e2e00000000000c363bf1ede00014f869d857685f11c22a882ee000000023c123a000000072e80007d399e42ce07f8000000072792bc0439488334831016d03f642da2c25e500008aa00000000382000097a08398a2870989a00012b20000000000000059a80000001f9400013080001b408a88000000000039c94b688509b06140c6a2f71fde000054200011d47da196c000000c0000d8a0000000084218a2cb9930835089a7b4a372428000078b121216780003b8000000017b05b0177800020140000000000237000018fe3c496e48e60d0a5e0235a36610241da130c12d18b68bd800006f9b4809580006f79402000000062d00002880e0030484f24e2850e497000040294c019c00000479a9a0001f7462386a40000000000000066b80000ca101684982ea08b0d5c00
  | 38 => 0x1289f5076d90960b91a40000212e2b780002548000000032200000001dd14c80001a7838f188c2b8106e6a2000085a937400016682f59dae5d79c5038f88706331f560000dec2db8c268020b8c0fe0df80000082000182a1fd1c4831e1aa81f900007498e365c10cce0000ffc8409e1231f80000001de80001248157886465080000ff00008b80ba000021fc00000005d884ca1739e6400000004e500006f9964271100001f3800000000000e60000490000000000000ae863a508800047100f271796c611105ec796800017c23d08060dcc2038da416000e022d22527e41ad267c950675d0bca5c49dbc42896ae53d1e080e197228c41dc00e90f520c5225c4c79eb650993d22e406ee3e516ec36a001243e0e0673420ea1bc01e815295e405a82dc460982c3151ac215d053436b0000790999e72d891800005704a9800000019744769d0e00018585351c0c1b7000000022d60001b8c0c78bd860f1edc8d41c1c00021dc34d106656b19b28a5168818987ca10c9c362fe05c65a60ba21f020a27a61c781b89824872083451498260528dae74a90a800000e82a3237852a9a266de85144360aba3378000453192466fa3b26b306585109f54128229a2ca8820509023284d800000011863d0000000000007f098d20000000000034a0001c203eb1efc31086940000a8254818060ca9a2e102a0902bba05a1e30d661389c840dd01ac86592ca4a89b900001e8035180007e1174c3f60fd26bd940631b944681a0000751856a6c7000000023be0000000000000082612e801f92a46710e3a000045479c1e240f610ae6c39b9a000000000013fa426940e30e1e34413a3a066298808e91dfe0340eae01091a881191e066213701e522bc81916460759f284cd1a5a7088cec050175400a91ee33c0d640b881267ae159a32b13a0736098e4e60bba5fb908a77900006f1a0881491d4a1e7a1f03de239c000000004089e44270ff66f080002c91f4c5c984d20000ef04120b7a5dc86860001f3000000001c30000697172044c8ba66978000692800076fa3907229b5000000000000e3853f1d1a4f710ec51501dc00016c87069b5c00022b01b8074215e0a1e60801602a401967630000000062c59708a61fc927a0e70000000038c148141613198402e7a24666800000000000000000022b1f4240d82fe4e18dbe3d81cd40002328000000073e042672f892274d04ce2b680002fea24e09111ac64d87e6458808034e95b82db159862ba2ee0001c2e3688a3c41fa1186229d6a675970e1472164115972e00017a279d98e8000000032000003700000864895c103208200017144f0151a1b981da0180d6000017f200014d8245873865e000028380003250000000000035d02580001ff68b788ee87f8af61ff1dba3219524004125e00012c800000
  | 39 => 0x17447c807f642d0f5083c1f1077e972800006666558a7c000116a6ed0000000000063c8030756000000020a400020c00000c524bb0000719163e2079d84478922435a1ba478a813879f800088080000df00000fd07da44800000001c0868d00006ac868c5e3a3b4101202807313b05d998bc5e2060227a97c661900003bd80000c080002b880000000000000000000000000000000000000000000000000000000126c00005006ef0856109000018c8dca7df1c3e398969e00000001990c222a820e288f14602f096700001e1405e800000000001701052000220a4a69d066cb88be5931e480971bc840f1c8238b043437a06bc877800083d0dfe4b89dd6105000012c8a3a30ea02a8f20b3003a80000001d2e34d81c6000176826108183d605f6367844c0cf918c1d501ba16f21da284879c82ca1522dc80000000510886a06e0001a2284214c460a000000011fe1aa895600000000001c4a00000006b11cd27ce9e0c2208d6a5b11fa001380003a80fea000239e00003ba61e0be850f1e92000227400000005dd073e2d7000000009b60000cba1e094ca2919b861d28d4802600007be08e200009926d99e842ec873a4b80a2634f91307f10b1a07e15d271f099816a9a9042b212c6a50a422e71fce50c0e0c21819b61daa33863b87206a004f8056200a14f9e3c06690a477319ca0dc910838609702001fe610793f40d905b000020202ad93fc000084c71b80000000000080000053405441d11c4c0e000a853a8000767922c8819e2200004064c697fc00021001a992302b60de42a2a0c88ad97cc04216b863800001519a2a01685cc0000ea258210948dd00000f58ee880088026e59ae07d1145e23980000000f900e41d1c000160e000044e6c20000602a0626be071259e98c20
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6c8258d5244107c388631aa48800a9ba08635491000536c10c6a922000c3e7690d5244001878ed21aa4880031d1da71549101e5b2c14e2a922033a74865c5524407f6cf04b8aa48800e2fa1276cc9100045ec24ed99220028de839db3244001938873b664880021fe1576cc9100243e42aed9922000e1c43d9732440011bf0eb1e64880c6a721163cc91001566412c79922000e8c43d8b32440031e90cb8e64880121fa17764c9100043ec2eec99220038be849d9324400117b093b264880032710e764c9100043fc2aec992200487c855d9324400117f08bb2648800e2f211764c9100046fc1aec99220008ef825d932440011ef02bb264880032710c764c9100061e3a6ca9922000e1c43d95324400187ecbba264880030f197744c9100046f43cc699220028dc8758d324405d53908b1a648800ab3209634c9102943e432eb98a205087f87d9731440010fb0fb2e628811a5d219758c5100069a21aeb18a2000977825d6314400b8eec0bac62880175cd81758c5100069ba02eb18a2000d35405d63144001ae440bac62880025de1f658c5106bcdac3c8718a2000d357590e31440012eb0ea9462880030f1d3654c5100061fb2ee898a2000c3c65dd13144001938e9b1a6288003271d0634c5102863a3b6ca98a2000cb476dd13144001b60e1ba2628835a6da1e434c5100965a3b48698a2012e946390d3144001bc441b9262880cf1d1d9524c510006b3b92a498a2000ad4864c93144001878e9b2a42881479908765485100061fb2ee890a2000c3c65dd12144149b6021ba242880032b1d3624851002d7340ec490a20018fa86dc121440a18e8edb2a42880039918b654851052e5a3b6e890a20a5ea462dd12144001b60e1ba242880025d617734851000c7a432e690a20009b68790d214406b968ed21a42880dba918a434851001573436c490a2051c7876d95204409b970ed21a40880039ae195248110005b5432a49022000b68865492044001cd10ca92408800b9add95248110017343b2a49022000f2a4354920441abe5086a924088003d8a055248110007b0c0aa49022033e6b615492044067ec6c2a924088353e210d3248110007b0a96e29022000b71851c520440017a30638a4088003d85487148110005b8c2c629022000be1828c52044001ec2a518a4088003d85493148110007e09926290220019e887485204400b9d0ec90a4088017781c5214811000df043a429022005de08748520440037c50c90a4088006f8219214811001770432429022002ee376485204400bbc4ec90a4088017781d92148110017703b2429022005ce07648520441a77c70a90a408834ef86152148110007b1b2a4290220d2f60654852044001f470890a4088347e82112148110005f1c1a429022000be1834852044001f448690a4088347e810d2148110
  | 1 => 0xf0eb1c86880028fe156390d101bd1e42ac721a2000aaf8258e434406d55904b1c868804b2ddda7190d100059ac2ce321a2012ab4865c643440014db05baec4880029b60875d89100043fc2ae9b12200487c855d362440011bf06ba6c48804a3720d74d89100043fc2ae7b12200487c855cf624400117f08b9ec48800e2f21173d89101be1e3ac87b1220d8c3c7510f6244025938e621ec488002ae60043d89100243f436eab12205087c86dd562440010fd0fb2ac4880030f1d365589100043f438cab122000c3c74195624400187ecbba2c4880030f19774589100062fb2ee6b122000c5c65dcd62440018beca39ac48800317194735891000666310e6b12200487e87dd5624400187e81baac4880030f50375589100045fc22eab1220038bc845d562440011bf06baac48804a3720d75589100043f438eab1220038be87dd1624400187eebba2c4880030f1d774589100945f41ee8b122000c3f52dd1624400187aa5ba2c4880022fe0374589100045ec06e8b12200087f855d162440090f90aba2c48800237e0d74589100946e41ae8b1220008ef825d1624400117d0e3a2c4880030fdd474589100061e3a8e8b1220038be84dcd624400117b09b9ac48804a37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100064f426e6b122000c9d84dcd62440018bea5b9ac4880031754b73589100064fa06e6b122000c9d40dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd624402593f0839ac48804b2721073589100062fa90e6b122000c5d521cd624400193e8039ac4880032750073589100045f43c86b1220128bc8790d624400187eeb21ac4880df0f1d643589100064fb9c86b122012c9c7390d624400117d0e21ac48804a2f21c43589100061fba886b1220d8c3c7510d624400193ee621ac48804b271cc43589100055cc0086b122000cac74dc96244001998e7b92c488003351cf71589100043f434eca922000a6d829d95244001878873b2a4880021f60a765491000636c14eca922000c3f409d9524400187a813b2a4880031bc82765491000636904eca922000a3f845d9524406947908bb2a48800297e0d76549100052e41aeca922000a6f825d952440010fd0c3b2a4880d28fa1076549100051ec20eca922000c3e841d9524400187b083b2a4880030f10c76549100243fc10eca92200487d821d952440018eb023b2a4880031d88476549100063a908eca922000c3f401d9524400187a803b2a4880031bc8076549100063d100eca922000c6d201d952440018f2403b2a4880d28fa1363549100051ec26c6a922000e1c43d8d52440010fd0f31aa4880021f61e63549100043fc3ac6a92200087c8758d524400147f08b1aa4880d28f211635491000537c12c6a922002
  | 2 => 0xc72d95100052ec18e5b2a2051a76811cb65440a14eb02396ca881429ea0072d951028d3cc00e5b2a200087e8790b65440010fb0f216ca8800297a0e42d95100052ec1c85b2a200087e8710b65440010fb0e216ca880021fa1e32d95100043ec3c65b2a2000a3e848cb654400147b09196ca880021fa1c32d95100043ec3865b2a205087e87c8765440010fb0f90eca880030f9d365d8d100061f3a0cbb1a2000c3f655d36344001878caba6c68800387d9443d8d100070e32887b1a2000b998010f634400717d09baec6880022f61375d8d100045ec3ce9b1a20038bf875d3634400193f06ba6c68837a2fe0174d8d1042c5ec02e9b1a2000c9d7410f634400153b0e21ec6880032761c43d8d100070f42887b1a2000e1d8510f63441b353f0021ec688366a760043d8d100064e21ae5b1a20ddc3e74d4b634400187ae9a96c6880038710f52d8d100054f42465b1a2012c3e435d6634402587886bacc6880021fe097598d100061fa02eb31a2000c3d405d663440090ff0fa94c6880021f61f5298d100043f43ecab1a2000c3c74d9563440018d8e5b2ac6880021fa1c6558d100061e3a0cab1a2000c6c72195634400187ecbba2c6880030f1977458d1000637b2ee4b1a2000c6c65dc963440090fd0fbaac6880021f60b7558d100061fa06eab1a2000c3d40dd5634400117f08baac68800e2f2117558d1000477c12eab1a20028ec825d563440010fd0e3aac68800e2fa1f7458d100061fbaee8b1a2000c3c75dd1634402517d07ba2c68804a2f20f7458d100045fc06e8b1a20008bd80dd163440010ff0aba2c6880121f2157458d100046fc1ae8b1a20008ef825d163440051d904ba2c6880022fa1c7458d100061fba8e8b1a2000c3c751d16344001938e9b9ac6880030fdd44358d106c61e3a886b1a20a2cac7210d63440051dd0fb92c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880031be177258d100063642ee4b1a2000cac43dc9634400195e81b92c6880032b5037258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a200087e87d4963440090f90fa92c6880030fdd35258d106ee1e3a6a4b1a2000c6f72d4963440058d8e5a92c688003391cb7158d102963ab88ca31a20008df8758c634400153908b18c688002b32096318d100070fb288631a2000e1c6510c634400173300218c68804a3720d7418d100954f4268631a20008bf845c8634400717908b90c68804b2710d7218d106e70e21ea431a204ac7571d48634400153d09190c688003279ce7690d100051fc2aed21a2037a3c855da434406f47d0db2c868836f0f9cf6590d100070f39ecb21a2000a3d82d9643441b587ee1b2c868836b0f5c36590d100045ec3ec721a20d9c9e73d8e434400117
  | 3 => 0x118a4000d69525c2314800717d093b262900022f612764c5200243f428ec98a400087d851d931480011bd0f31a62900163721d634c52002d6a40ac698a4000c6f7654931480018d8eca9262900034bdd1524c520316963a2a498a4000ccc764c931480c1b18e899262900021fe15760c5200243e42aec18a40008bf845d8314800717908bb062900163d205760c5200046ec3ec618a40018ec865c8314800b9c8c2b9062900031b9d9520c52000636bb2a418a4033d6a70548314800b1f10cb8062900035a549700c520526563b6e890a40a4ea461dd12148001b50e1ba242900025b617734852000c76432e690a40009ae8790d214806b958ed21a4290137a9186434852002d73436c290a4012c3e435d663c402587886bacc7880021fe097598f100061fa02eb31e2000c3d405d663c40258be60bacc788003174c17598f100243fc3ea531e200087d87d4a63c40958ece3a94c7880022fe117558f1001c5e422eab1e20038be87dd163c409b17d0e3a2c7881362fa1c4358f100061fba6a4b1e20ddc3c74d4963c414f17f0eb1c87880022fe117558b1001c5e422eab1620038be87dd162c402517d07ba2c5880030fd4b7458b100061ea96e8b1620a48be871d162c40090fd0bb9ac5880021f6177358b1001c5f426e6b1620008bd84dcd62c400117d0f21ac58804a2f21e4358b100045f43886b1620128bc8710d62c40674ed03bb2a5881271d9c77654b100051fc22eca962034a3c845d952c40014df04bb2a5880021fa1e6354b100043ec3cc6a962033a768198d52c400147f08b1aa5880d28f2116354b1000537c12c6a962002a6c8258d52c41bf6cf04b8aa5880c6a721163ccb100243f42eec996200087d85dd932c40031ed03bb265880022fe11764cb1001c5e422ec99620058dc8758d32c405d53908b1a658800ab3209634cb1053cdb43c8698e2012e946390d31c4001acee4a926388016b5219324c71052752316e890e200097585dcd21c40011ef0cb9a43880026da1e434871026f523148690e200087d8799365440010ff0eb26ca8800297e0d64d95100052e41ac9b2a2000a6f8259365440014d904b26ca883630f9d843d95100059cc0087b2a200887d8718b654400147d08316ca880028f61062d95100052f418c5b2a2000a5d8318b65440018dae4316ca880030f5d074d95100051f426e7b2a2000a3d84dcf654400147f08b9eca880028f21173d95100062eb98e7b2a2051a76811cf65440a14eb0239eca880021fa1c43d95100043ec3887b2a2000c3e8710f654400187b0e21eca8836a8fa0c43d95106dd1fc0087b2a20dba3d8010f654400147f08b96ca880028f21172d95100061fc22e5b2a2000c3c845cb654400187886b96ca880030fd0172d95100061ea02e5b2a2000a3e841cb654400147b08396ca8800297a0
  | 4 => 0x3480011bf0eb18c690002b52056318d200961f21aea31a4012c3c435d463480950ff04ba8c6900ce1f6097518d200061fa02ea31a4000c3d405d463480258be60ba8c690003174c17518d200045fc22e231a40038bc845c4634800147f0abb486900de8f2157690d200045ec3ec721a40008bf8758e434800147f0ab1c86900de8f2156390d200055bc0ac721a404dab48158e43480255590cb948690183639cd7290d2031597426e6a924000b2d84dcd52480674dd0d39aa4900029b61a7354920196363b4e6a924033b6a809cd52480016d30139aa4900035a1c2735492000537c32e6a924033a6c865cd524800165f08b9aa49018acb2117354920005b5c02e6a924033b68805cd52481998d8ec39aa4900035a1c0735492031597426c6a924000b2d84d8d5248001c9ec731aa49003ada6026354920004b7c3ac6a92400d96c8758d524800165f08b1aa49018acb2116354920005b3c0ac6a924000b648158d52480236d700b1aa49038a5ba1c635492019cb6c38c6a924000e4d6318d5248001c5d0d21aa4900038b61a43549201bf17bb486a924037e2c7690d524814565d0721aa49018bc3a0e435492070d97c0486a9240e1b2d8090d5248195e50e121aa4900db8bd8243549201b795b0486a9240caf2a1090d52480676d101b8aa4900ce9ba1a715492000536c34e2a92401cc6c769c552480676d50138aa490002da602715492000537c32e2a924033a6c865c5524800165f08b8aa49018acb2117154920005b5c02e2a924033b68805c5524818b8d8ec38aa49018acba10715492000596c20e2a924033b6a801c552480016d30038aa4900cedaa1f705492019eb543ee0a924002b6a86dc152480056d10db82a4900cf5a9db705492019eb43b6e0a924000d6b73dc15248001ad2e7b82a490003ca90f70549200079421ee0a924000b6981dc15248001ad6e3b82a4900035a5c77054920006563b6e89924000da870dd132480c171d09b1a649028a6ba1e434c920096563b48699240a2b8e8390d3248025d18c721a64900025b617714c920006f1086e29924000f8843dc132480010ff0ab9ec2900121f21573d85200045fc22e7b0a40038bc845cf61480015730021ec29001b5a5c1529852006cb643aa4b0a4000d2f7454961480c5a58e8a92c29000353dcd5258520006a639aa4b0a400ad6b7054961481c12df0ea90c2900ce5b61d5218520316973a2a430a4000d2d745486148001a9ce6a90c290003535cd52185200047bc3ac230a4000ad4835846148001ccaa4b08c29000e2fa1276cc5200045ec24ed98a40058de839db314800b5a902b1e62900063b21972cc520004b7c3aa598a400096d8754b31480031d90cb9462900025be1d528c520004b6c3aa518a4062d2e7454a3148001a5ae8a9462900cf5a9c1528c52002c7c432e
  | 5 => 0x80032b1c8645853000637b2ee4b0a6000c6c65dc9614c00195ec9b92c2980032b19372585303d62eb98ca30a604fc9d73190614c0011ef0eb08c298002b920961185301643e432eb98a6000c3c645d7314c025a3c86bae629804b4710d75cc5300043fc3ecb98a601087d87d97314c00187cebb2662980030f5d764cc530384ae432eb98a6000d1c645d7314c0012bf04bae629804b17d8175cc530096adb02eb98a6000d1f405d7314c001a3a80bae629800257e1f65cc5300068ebaec998a600095d8754b314c0f50f90cbac62980030f191758c5303cc3fc3ecb18a600087d87d96314c00187ce9b2c629813e2f219748c5300061fb2ae918a6000c3c655d2314c06b17f0fb2462980022f61f648c5300061f3aec918a6000c3d75d92314c001878e9b2a629813e2fa1b744c5300061fb2ee898a6000c3c65dd1314c14f17d0fb2262980d62f21f644c5301ae4e3b48698a604de946190d314c06bb30e121a62981e7171db654c53026e4e3b6e898a6000d9870dd1314c06b938edb2262980cf171d9524c530006a7b92a498a6000e9764185314c001d2ec898862980021fe1576885300243e42aed10a60008bf845da214c00717908bb4429800257616738853000c6e432e710a600487e85dd9214c0010fb0bbb2429800e2fa1376485300045ec26ec90a60038be849d9214c00117b093b2429800339086764853001c5e420ec90a6000ce4211d9214c001878e9b2a42980039908765485300045f436e890a6000c3f65dd1214c001878cbba2429804a67a0f74485300045f43ec890a60008bc87d91214c001d4843b22429800237a1a7348530004aec2ce690a60018dc865cd214c0f38f4edb2e60981e796d8f65cc1301ae5d3b6c99826002c7a7654b304c00717d09baec6900022f61375d8d200045ec3ce9b1a40038bf875d3634800187ea4ba6c6900030f54974d8d2071c5fc02e9b1a40158bd805d363480010ff0ab8ec6900121f21571d8d200243f43eeab1a400087f82dd563480010fb05baac6900030fd037558d200061ea06eab1a40008bf845d5634800717908baac6900023de057558d2002c7a40aeab1a400087e871d5634800717d0fba2c6900030fdd77458d200061e3aee8b1a4000c3f52dd1634800187aa5ba2c6900022fe037458d200045ec06e8b1a400087f855d163480090f90aba2c6900023de057458d2002c7a40ae8b1a40008be871d1634800187eea3a2c6900030f1d47458d200061fba886b1a40d8c3c7510d634814f968e221ac6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900032d10f7158d200063ba96e2b1a4000c7552dc5634800196e81b8ac6900032d5037158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c56
  | 6 => 0x4e1eb86cb21a6000c3c75d93624c001878ea326c4980029b60b75d893000536c10ebb12600087f855d3624c0090f90aba6c49800a3720d74d89301be1e3ac87b1260d8c3c7510f624c0010ff0ab8ec4980121f21571d89300043f43ecab126000c3c74d95624c0010fd0e32ac4980030f1d065589300061fb2ee8b126000c3c65dd1624c00117d0fb22c4980030fdd764589300061e3aec8b1260008be87191624c00187eea322c4980030f1d464589300063bb2ee2b126000c7465dc5624c00196ec9b8ac4980032d19371589300063bb28e2b126000c74651c5624c00196ec838ac4980032d190715893000672310e2b126034a3e84dd9524c00147b09bb2a4980021fa1a76549300061e324eca926000a6d829d9524c001878873b2a4980031b60a76549300061fa04eca926000c3d409d9524c0018de413b2a4980028fe1176549301a51e422eca926000a6f825d9524c0014ef02bb2a4981269d20576549300061e320eca926000c5d831d9524c001878863b2a4980121fe0876549300243ec10eca926000c5f321d9524c0018ba643b2a4980030fd0076549300061ea00eca926000c6f201d9524c0018da403b2a4980d28fa1b64549300061f3b6c8a926000c3c76d91524c14547d07b22a4980da8f20f645493000717416c8a926000e2d82d91524c1d187ee5b22a4980038bdcb645493041d1fc06c8a9260e1a3d80d91524c195c5e41b22a49832b8b48364549300062e3b4e6a926073b4d829cd524c0674b90cb9aa4981dad3e09735493073d1f43486a926000c3e7690d524c001878ed21aa49820fc60c243549307370e21ecb9926012a9e83d93324c001c38c9b2e64980c6a7a1b64cc9300061e3a6ca9926000e1c43d95324c001c9865b2a649813e2fa1b744c9300061fb2ee89926000c3c65dd1324c14517d0fb2264980d62f21f644c9300954f41ec89926000e8c32d91324c1cb53d0d21a64980d7271da434c9301b746314869926035d987090d324c001d1887b1264981e7171db654c9300070e326ca9926000e4c62d95324c1cb53d0dba264980db271db744c930006cc386e8992602ea9e86d91324c06b938edb226498003a318b644c9305f746326e49926000e8c64d89324c0012bb0bb8a6498002b560c21d853000578c0043b0a6000c3e74d96614c00187ce832cc2980030fd9574985300061e32ae930a6000c3e75d92614c00187aebb24c2980030f9d464985300061eba8c930a600487e86dd5614c0010fd0fb2ac2980030f1d3655853000636396cab0a600087e87195614c001878e832ac2980031b1c8655853001c5f436e8b0a6000c3f65dd1614c001878cbba2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614c001958e5b22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c1c993ee6322c29
  | 7 => 0x7d85dd921cc00717d09bb243980022f613764873000c6f41eec90e60008bf845d921cc00717908bb2439804a2fa1b7448730094cf41ee890e60008be87d9121cc0251790fb224398003a908764487300046fc32e690e600087d87993654c0010ff0eb26ca983a68fa1843d95300061e322e5b2a6000a3e8498b654c00147b09316ca980421f61c62d953000636b90c5b2a6000c3d741d3654c0010fd0e21eca980421f61c43d95307361f43887b2a60e6c3d8710f654c1cd47f0021eca983aa8f60043d95300051fc22e5b2a6000a3c845cb654c00187f08b96ca980030f21172d95300061e21ae5b2a6000c3f405cb654c00187a80b96ca981da97a0c72d95303cd2ec18e5b2a600087e8790b654c0010fb0f216ca9800297a0e42d95300052ec1c85b2a600087e8710b654c0010fb0e216ca981e61fa1e32d95300043ec3c65b2a6000a3e848cb654c00147b09196ca980021fa1c32d95300843ec3865b2a6000a3e849c7654c00147b0938eca981c297a0c71d95303cd2ec18e3b2a600087e87107654c0010fb0e20eca980021fa1f21d95300043ec3e43b2a600087e87087654c0010fb0e10eca980028fa1021d95300051ec2043b2a6000a5e83087654c0014bb0610eca981e69ea0021d95300053cc0043b2a60eac3e76d97644c1cd878e7b2ec8980028f60b65d91300045ec3ccbb2260f3a3e85997644c00117f0eb2ec8983ca8fa1865d913078e1f3b0cbb2260f0e1d83197644c1d787ce632ec8980028f60865d913075e1fb80cbb2260f0c3d70197644c001c38cb29ec8980d6a721953d91300051f42cc5b226000a3d8598b644c00147d0a316c8980028f61462d91300051f436a5b2260ddc3e76d4b644c00187aea3aec8983bea7a0c75d91301ad4ec18ebb226000aae821d7644c00155b043aec8980d62fa1f53d91300045ec3ea7b226000e1f5394f644c1b117f0ea9ec8980d62f21d53d91300051f42ce5b226000a3d859cb644c00147d0a396c8980028f61472d91307754f418e5b226035a9d831cb644c00117d0fa96c8980022f61f52d91300061f43ea5b226000c3d87d4b644c14587ce7a96c8980db0f1cf52d91306e61fb86a5b2260edc3d70d4b644c19547b0b296c8980d62fa1e32d91300045ec3c65b226000a3e858cb644c00147b0b196c8980028fa1432d91300051ec2865b226000a3e859c7644c00147b0b38ec8983b2a7a0c71d91301ad4ec18e3b2260008be87147644c00117b0e28ec8980028fa1721d91300051ec2e43b2260008be87087644c00117b0e10ec8980028fa1421d91300051ec2843b226000a9e83087644c00153b0610ec8980d6aea0021d91300055cc0043b2260eba3e86d96434c1d587cedb2c869839bc60c36590d307361f39ecb21a60e6e1e73d96434c00147b05b2c869839b0fdc36590d307
  | 8 => 0xcb9c42a00022f21973885400064fb98c710a8012c9c7318e215000137301bb242a0003a908776485400945f41eec90a8000c3f52dd9215000187aa5bb242a00032e60376485400045f434ec90a800093f855d9215002d2790abb242a000267e0d7648540004ce41aec90a80009af825d9215000137700bb242a005a4fa1476485400049ec28ec90a8000ea4211d9215000187d0a3b242a00030f61476485400945f418ec90a8000c3f521d9215000187aa43b242a00032b884764854000656108ec90a80038bf801d9215000717b003b242a00032bc80764854000656900ec90a8000cb7101d9215000196a203b242a00022fa1b73485400045ec36e690a801693e85dcd215000127b0bb9a42a00022fa1a73485400045ec34e690a801693e859cd215000127b0b39a42a00022fe1973485400045e432e690a80019ba801cd21500013730039a42a00022fa1c63485400945e438c690a8000c9f7318d2150025938e631a42a0003a908463485400945f43ea5b2660008bd87d4b64cc1b987d0fa96c9980030f61f52d93306e61f39ea5b2660dce1e73d4b64cc1b9c72e1a96c99804a2fa1c51d93300045ec38a3b266000a3e85c8764cc00147b0b90ec99804a2fa1c21d93300045ec3843b266000a3e8508764cc00147b0a10ec99804aa7a0c21d93300054ec1843b266035aba8008764cc0015730010ec99804a67a0f7458b300045fc22eab1660038bc845d562cc0051bb07ba2c59800e2fa1f7458b300954f41ee8b1660128be83dd162cc00193d07ba2c5980032760f7458b300945e41ee8b166000c3f52dd162cc00187aa5ba2c5980022fa1c7458b300243f42ee2b16600087d85dc562cc06947d09bb2a5980028f6137654b3000536c14eca966000a3f845d952cc06947908bb2a5980029be097654b3041d1f41ec8a966083e1e83d9152cc107c5d05b22a59820f8b60b6454b3000717b96c8a966083e3980d9152cc195c5e41b22a5980ce9761a7354b300062fbb4e6a966081b4d829cd52cc10569f04b9aa59804aa7a1b744cb30004aec2ee299660f4c3f645d661cc1e9878c8bacc39804a67a0f74587300045fc22eab0e60038bc845d561cc00717d0fba2c39804a2fa0f74587300945e41ee8b0e60008be871d161cc00187ee9a92c3983770f1d352587300061fba2a4b0e6034c3c7454961cc0018dee4a92c39800b1b1c9525873018e4e3a664b0e602ec9c744c961cc005998e4992c39804b47d9175cc7300968e322eb98e600095f825d731cc0dd8bac0bae639800347d0175cc7300068ea02eb98e600095d8754b31cc0678baeca9663983d30fd91758c7307a61e322eb18e60128be86dd131cc0251790dba26398003271d3764c73002d6a40ac498e6000d4f7254931cc00117f08bb4439800e2f21176887300243f42eec90e60008
  | 9 => 0x62185400b49fc3ea430a800093d87d48615000127f0ea90c2a00024f61d5218540004dbc3ac230a80f6bb380584615002d27d0bbb662a00024f61776cc5400acd7416ed98a80009ad82ddb315000137301bb662a00026ee0176cc5400b49f428ed98a800093d851db315002d27f0ebae62a004b0f98d75cc5400961e31aeb98a800093f825d731501eb87ec0bae62a00034ed8175cc5400b49f42ae598a800093f8754b315000127b0ea9662a02166761f32cc5400061fa94ed18a80038bf809da315000717b013b462a02172dc42768c5400065a884ed18a80009bb805da315000193f06bb462a00030fd49768c5400065dc02ed18a80f4c3c635d6315000127f04bac62a037b0fd81758c5400069db02eb18a8085d37105d6315002553d0db1c62a0003479d7638c5400064fbb0c718a8000c9d7618e3150001a3cea31c62a0002a761c638c5400964ec38c718a8012e1e8518e3150025c3b0a31c62a0003279d4638c5400070f3a8c718a8000c1e7518e3150001c3aea31c62a0003271d4638c5400070fa90c718a8012e967118e31501c993ee031c62a0393275c0638c5407274b880c718a80e4e951018e315002d27d0ab9462a00032718d728c5400049fc3aa518a800093d8754a315000187ceca9462a00030f5d9528c5400070e31aa518a80009b980dd9315000187ea5bb262a00032e603764c5400045f434ec98a800093f855d9315002d2790abb262a000267e0d764c540004d7c12ec98a80159ac825d9315000137700bb262a005a4fa14764c5400049ec28ec98a8000c3e851d9315000187b0a3b262a004a2f20c764c5400061fa90ec98a8000c9e311d93150001938623b262a000e2fe00764c54001c5ec00ec98a8000c9f301d9315000193a603b262a00032dc40764c5400065a880ec98a8000c3f765493150001878eca9262a00034bdc9524c5400ae96392a498a8000c9c76cc9315010b3390e99262a0003271d9324c5400aec63926498a8085b94814c9315000336d0f98a62a00066e202760c5400049fc2aec18a801693c855d8315000137700bb062a004aa7a1b630c540004cec38c618a8012c9f7618c315000193aec31862a0002e5604630c5400045fc32e418a80008bc865c83150025938c6b9062a020f8718d520c5400ae97392a418a8000d2d725483150067a74e0a9062a00026de1d310c5400974b31a6218a80039ba865c031500073710cb8062a00034ee15700c5400069c42ae018a8000d9b635c03150025974c6b8062a004b2e18d700c540006cc31ae018a8000d3b525c03150001a72a4b8062a021766cc5700c54042ed918ae018a8085d99315c03150001b6262b8062a00024fe1576885400b49e42aed10a800099f835da215000133906bb442a00026ee0176885400b49f42ce710a800093d859ce215000117f
  | 10 => 0x9928000c9f7618d325000193aec31a64a0002a7a1c634c9400964f438c69928012e1e8518d3250025c3b0a31a64a0003279d4634c9400064e3a8c69928012c9f7218d3250001c3ea431a64a000387548634c9400064e388c6992802ea9d8018d32501f793ee031a64a03ef275c0634c9407df47900c699280fbe8d2018d3250025d18c799264a005a4fa17714c9400049ec2ee299280858bd87d97615002d87cebb2ec2a0002a720d65d854007cdcc04e7b0a800093f855cf615002d2790ab9ec2a02162f61c63d85400051ec28c7b0a8012c9e7318f615000193ae631ec2a02162f61f62d85400b49f42ce730a800093d859ce615002593ce731cc2a0002a7a0e62985407d69cb86a530a804bd397054a61501f3b62e1b0cc2a005a4fa1f75585400049ec16eab0a8000c3f60dd56150001a76c1baac2a000267e0d7558540004ce41aeab0a80009af825d5615002b35904baac2a00026ee0175585400049f438eab0a8016c3c75d956150001958e5b2ac2a02162f21d65585400054e41acab0a8000cac725956150001a3eebb9ac2a0003471d773585400064fb06e6b0a8000d9b60dcd6150001a3eea39ac2a0003471d473585400964fc30e6b0a8000c9f651cd615000193aca39ac2a00032798473585400064e308e6b0a8000c9f601cd6150001b36c039ac2a00030fdd663585400061e3acc6b0a8012c9c7398d6150001958e531ac2a0216ada0663585400051ec28c6b0a8000c3f7518d6150001878ea31ac2a000327dcc63585400964e398c6b0a8000cac7218d615002b35d0fb92c2a00034bdd77258540006963aee4b0a8000d8f73dc96150001b18e7b92c2a00034be1772585400069642ee4b0a8000cae63dc96150001958c7b92c2a00032bd837258540006d5b06e4b0a8000caf761c96150001a5eea392c2a00034b1d47258540006c7b98e4b0a8000d8c731c9615000117d0fb12c2a0003271cf62585400ae56396c4b0a80858bc875896150001938e6b12c2a00572b1c9625854042d5a40ac4b0a800093e87d49615002d2790fa92c2a000347dcf52585400068e39ea4b0a8000d2f72d49615002ba58e5a92c2a03e34edc352585400049f43aa4b0a800093c875496150001a3ee6a92c2a0003471cd525854000697b92a4b0a8015d2c7254961500b7a76e0a92c2a00034edd770585400069c3aee0b0a8000d9b73dc16150001b30e7b82c2a00036adcb7058540006d4396e0b0a80f7db371dc1615000127f04ba8c2a02170fd85751854042e1eb0aea30a80dec3f605d46150001a76c0ba8c2a02174dc4175185400069a882ea30a8000c3e7598c615000187aeb318c2a00030f9d463185400061eba8c630a8012c9e7318c615000193ae6318c2a0002ad60463185400045ec3cc430a8000c3d75988615000153d07310c2a00030f5d4
  | 11 => 0x50001c3f07a90c6a03738720f5218d406e70f996a431a80dce1c31d4863501b987ee1a90c6a03770f5c35218d406e70f986a431a80ffe1d30d48635002553d07290c6a0002a760e5218d400054fc1aa431a8012a9c835486350001c3ea6a90c6a020f8714d5218d400954f418a431a8000a9d83148635002553d07a88c6a0002a760f5118d407f70e29ea231a8012a9e83944635000153b07288c6a000387d4e5118d400054fc1aa231a8012a9c8354463501e9c38a6a88c6a004a2fa1c5118d400045ec38a231a8012a9c831446350001c3ea6288c6a00028fa172118d400051ec2e4231a8012a9e83c84635000153b07908c6a004a2fa1c2118d400045ec384231a8000a3e85084635000147b0a108c6a004aa7a0c2118d400054ec184231a804faba80084635000157300108c6a00066ea0273d894007cdcc04e7b12800093f855cf625002d2790ab9ec4a00562f61c63d89400964f398c7b128000c9d7318f625000127f0ab8ec4a005a4f21571d8940004cfc1aeab12800099c835d5625000136f02baac4a02166d2057558940004ddc02eab12801693e851cd625000127b0a39ac4a004b271ce63589400ad57414c6b1280fddab72dc1625000167301bb2a4a00030fdda765494000596c14eca928000b1f835d9525000163906bb2a4a0002cbe0976549400059bc0aeca928000b34815d9525000167700bb2a4a00030f5d876549400051f436e6a928000a3d86dcd5250001a3ee739aa4a025acb60a73549400051fc32e6a928000a3c865cd525012f65f04b9aa4a0056cba0a635494000596c14c6a928077b398098d525000127f0eb1aa4a00024f21d63549404259dc02c6a92800093e8718d525000127b0e31aa4a00038758c635494041e1f438c6a928083c3d8718d5250001c3ee631aa4a020f871cc635494000717b90c6a928083e1f3218d525010747f0031aa4a00d28f600635494041f0f980c6a9280fce1d3018d52501f9c5e4031aa4a03f38b480635494043596c14e2a928000a3f865c552500014790cb8aa4a021ecbe0971549400051f430e2a928000a3d861c5525000137301bb664a00024fe1576cc9400b49e42aed99280009bb805db325002d27d0a3b664a00024f61476cc9400accec38c79928012c9f7618f325000193aec31e64a00026e603764c9400064ec1eec9928000c3f52dd9325000187aa5bb264a00032e603764c9400045f434ec992800093f855d9325002d2790abb264a00026de05764c94042cda40aec99280009bb805d9325002d27d0a3b264a00024f614764c9400061f428ec9928000c3d851d9325000187ea43b264a00030f548764c94001c5fc00ec99280038bd801d9325000193e603b264a0003274c0764c94000657900ec9928000cad201d9325002b33d0fb1a64a004aa7a1b634c9400adc7416c6
  | 12 => 0x8030f1d764581210045f438c8b024200c3f751916048401878ea322c09080327d9373581210064e326e6b024200dc421dcd604840193ec839ac090803271907358121006e2108e6b024200a9d86d4f635002593ceda9ec6a0003475d753d8d400049fc2ae3b1a801693c855c7635000137301bacc6a005b0f1d76598d400061ebaccb31a8012a9e83996635000153b0732cc6a005a2fe1d6598d400954e41acb31a8108d9970d8e6350025938c6b94c6a00028fa166298d400051ec2cc531a8012a9e8398a635000147d0a314c6a00028f6146298d4083e9cb86a531a8012e98635c2635002d27d0fbaac6a00024f60b7558d400061fb06eab1a8000d3b60dd5635000117f0cbaac6a000267e0d7558d40004ddc02eab1a800093e871d56350001a38ebb1ac6a00030fdd66358d400061e3acc6b1a800093e87d49635002d2790fa92c6a041b4edc35258d400069dbaee0b1a8000d3875dc1635020bb36e7b82c6a00024f61e7518d400970f31cea31a801693f875d46350025c3cc6ba8c6a00030f2197518d400068e41aea31a8012c3e635d46350025878c6ba8c6a00024fe097518d400061fb02ea31a8000d3b605d46350001a3e60ba8c6a0003474c17518d400b45ec3eca31a8016c3e75d94635002553d07b28c6a0002a760f6518d400061ebacca31a8016c3e75594635000153f06b28c6a004aa720d6518d400045ec38ca31a8012a9e83194635000153b06328c6a040aa761a6318d40825ccc04c631a80008bf8758c635000147f0ab18c6a00028f2156318d40004cfc3ac631a8012a9f8658c63500016390ab18c6a040ee6e016318d400054fc3ac631a8000c9f8758c6350001c3f0ab18c6a0002a72156318d400070e42ac631a8000a1c8558c6350001c3ceab18c6a0003875d56318d400054fc12c631a8000a9c8158c635020553f00b18c6a0003a6e016318d400054fc36a631a8000a9d86d4c6350001a3aeba98c6a0003879975318d400070eb2ea631a800099d8714c635002553f0c298c6a0002a76185318d400070fb28a631a8000e1c6514c635000147d0b310c6a00028f6166218d400061ebacc431a8012a9e83988635000153b07310c6a00028fa146218d400051ec28c431a8000c3d75188635002553d06310c6a0002a760c6218d4000656b90c431a801693f87d48635000127b0fa90c6a00038758f5218d400954ec3ea631a8000c9d87d4c635002553d0ba98c6a004b87a175318d400970f3aea631a8012e1d75d4c635000153b05a98c6a0002a7a075318d4080d4fc06a631a8101a9d80d4c6350201c3ea1a98c6a0403875435318d400945f43ea431a80008bd87d48635002553907a90c6a000387d4f5218d406e70e29ea431a80dca3f87d4863501b987d0fa90c6a03728f61f5218d400061ec3ea431a800083d87d4863
  | 13 => 0x55b40861b224200ab5810c3644854b17d0f086c8908022f61e10d9121006b210aebb1a4200da4215d3634843117b0fb26c6908030f9d764d8d210061ebaec9b1a4200a9e83d93634840187cea326c6908030f5d464d8d210054f418c9b1a42038be84dd7634840117b09baec6908021f61e75d8d210243fc3aebb1a42ad87f825d763484930fb04baec6908031bc8175d8d210243f42ee9b1a420087d85dd3634840117b0f3a6c6908030f9d674d8d210061ebace9b1a42038bf875d3634840187ceaba6c6908030f5d574d8d210061fa92e9b1a4200c3d525d3634840117f00ba6c690813179d653d8d210246fc3aa7b1a42d8c3e7510f634840187aea21ec69080e2fe1f40d8d210045ec3e81b1a4309c3e75d03634840187aeba06c690802a7a0f40d8d210052ec2861b1a4200acd820c363484015ab02186c69084b1718d7598d21006b210aeb31a4200da4215d2634840187cebb24c6908030f5d76498d210061f3a8c931a4200c3d7519263484018baebb1cc69084b0f90d7598d210961e21aeb31a420087f825d663484010fb04bacc69084b17cc17598d210945e41ae931a4200c3f525d2634840187aa4ba4c6908022fe017498d2101c5fc3e8131a42008bd87d02634861387ceba04c6908030f5d74098d21006d210ee8b1a42008be87d91634840117d0e322c6908022fe117558d2101c5e422eab1a42008fb805d563484031f100baac69080e2fa1f7458d210061fa96e8b1a4200c3d52dd1634840117b01ba2c6908022fa1c7458d210045f43e80b1a42038bc87d01634842553d07b20c69084aa7a0c6418d210046fc3ac631a42aaec42158c634840117f08ba8c69080e2f2117518d210043fc2ae031a420487c855c0634840117f08b80c69080e2f2117018d210945f43e8031a4212a9e83d00634842517d0d3b48690803690867690d211bd1f42ced21a4200a3d859da434840187d0b3b486908030f6167690d210945f41ced21a42128bc839da434840187ea53b486908030f54a7690d210065710ced21a4200cac219da434840117b013b486908032bc827690d210045f430ed21a4200da4211da434840117b0fb1c86908de8fa176390d210051ec2ec721a42008bf8758e43484011790cb848690803690857090d210061e322eb98a4212c5c635d7314857bac842bae62908030f9d764cc5210061ebaec998a4200c5d75d8f3148401958c8b96629084b3318d72cc5215345f436e898a424dda421dd1314840117d0fb226290a962f21f644c5210045fc22ebb0242038bc845d7604840157301ba6c090802ae60074d81210045fc22e7b0242038bc845cf604840117d0f21ec0908022fa1c43d81210945e43887b024200d6421dd5604840717d0dba2c090a922f21b7458121006d210ee8b0242008be87d91604840187eebb22c090
  | 14 => 0xf825d9520c4094dd0eb12a4188129b21d625483100717c22c4a906200e2c84589520c507c5c86b12a418a0f8b10d625483124f2798ac4a906249e4d31589520c4014df00b12a4188038bd0162548310065a3a6ec9886212e9643dd9310c4018ed0bbb262188031d617764c4310965b21eec9886212cb443dd9310c4018eea5bb262188032dd03764c4310065bbb6e89886212b9483dd1310c4018eeeca926218a0fc590d524c4310243f43eeab0062e6c3e43dd5600c5cd87887baac0188021f60b75580310061fa06eab006200c3d40dd5600c4a30fd0e3aac0188029b60875580310043fc2ae8b00620487c855d1600c4010fd0fa92c0188121f21f52580310043f43aa4b00620087c87549600c4058dce4a92c01884ba590d31580310976998262b0062058f887541600c40b1f10ea02c01884b0f90d7598e210961e21aeb31c4212c5f305d6638861387ceba04c7108030f5d74098e210045fc22eab1c42038bc845d5638840717d0fba2c7108030fd4b7458e210061ea96e8b1c42008bd80dd1638849b17d0e3a2c7109362fa1c4358e210045f43e80b1c42038bc87d01638854f17f0eb1c871084aabe197290e21856c739ae521c420487e87dd5608840187e81baac1108030f503755822128c3f438eab044200a6d821d560884010ff0aba2c1108121f21574582210046fc1ae8b0442128dc835d1608840717d09b9ac1108022f61373582210061fbac86b044237c3c7590d608840187eea21ac110b630f1d443582210064fb9886b044212c9c7310d60884015730021ac1108022f61e65d91210054f41ccbb224200a9d83997644840117f0eb2ec8908036908673d9121006d210ae1b2242188bd87183644840147d0a306c8908028f61460d91210054f418c1b224200a9d831836448401972e0306c890802a7a0f75d91210054ec1eebb224200c3d751d7644840147d0bb9ec8908028f61773d91210051f42ce7b224200a3d859cf644840193ee739ec89084b279cc73d91210045f43ea7b2242008bd87d4f644842593ce7a9ec89080387d4e53d91210045fc3aa7b2242008bc8754f644842593ce629ec8908028fe1570d91210051e42ae1b224200c3f855c364484018790ab86c89084a2f20d70d91210061fa92e1b224200c3d525c3644840147d0a386c8908028f61470d91210054f418e1b224200a9d831c3644854b55d04386c890a92ab60870d91215255b408e1b2242a5ab5811c3644840117d0f286c8908022f61e50d91210045f438a1b2242008bd87143644840153d06286c890802a760c50d912152d57410a1b224200aad82143644854956d02286c890802ad60450d91210045f43c61b2242008bd878c3644840117d0e186c8908022f61c30d91210051f42861b224200a3d850c3644854b55d04186c890802ab60830d912152
  | 15 => 0xf286c8988022fa1c50d91310045ec38a1b226200a9e83143644c40153b06286c898802aba0850d913100556c10a1b22624dab681143644c40156b02286c8988022f61e30d91310045f43861b2262248bd870c3644c40147d0a186c8988028f61430d91310055741061b226200aad820c3644c49b56d02186c8988028fa1720d91310051ec2e41b2262008be87883644c40117b0f106c8988022fa1c20d91310045ec3841b226200a3e85083644c40147b0a106c898802a7a0c20d91310054ec1841b22624dab681083644c40156b02106c8988022f61e10d91310965bb0ced21a6212d94319da434c46b1790cb84869884b650c57090d311ae5c302e121a6212d9b305c2434c4091df0ea96c4988021fe1570d89310243e42ae1b1262008be87d91624c40117d0e322c4988d28fa1376549310051ec26eca926200a6d829d9524c40147f08bb2a4988d28f211765493100537c12eca926200a7b805d9524c4674f100bb2a4988d28fa1b645493100716316c8a92630bc3f72d91524c401c5ee5b22a4988028f603645493100717906c8a9262b7a3e8690d524c46dc58c521aa49880a9ba1b625493100717b26c4a926200e2c64d89524c4094dd0fb12a4988129b21f62549310071721ec4a926200e2c43d89524c4014db01b12a4988038bd03625493118d4f436c999262a78be86dd1324c54517d0fb2264989362f21f644c9315b54f43486992624dc9c7690d324c46dd18c521a6498937651c6434c9310074621ec49926200a9e86dd1324c46d938edba264988dba318b744c9311754f436c8992624dc9c76d91324c401d18c5b226498937651c7644c93113d67436e499262bee8c64dc9324c40559d0db126498803a3193624c93102ceb43ee29926200d97741c5324c401b28e838a64988030f19175cc5310061f3aec998a6200c3d75d93314c5553af0e996629884b74cc170cc5310045fc22ebb0262038bc845d7604c40157301ba6c098802ae60074d81310045f43c87b026200ab98090f604c40117d0e21ec098802ae60043d81310045fc22e5b0262038bc845cb604c5bb878e9a96c0988d30f1d152d813101636392a5b026231c9c74ccb604c45d938e8996c09880b331c932d813101c5f436e8b02624d8bc86dd1604c40117d0fb22c0988030fdd764581310061e3aec8b026200cac72d91604c40117d0e322c0988030fdd464581310061e3a8c8b026200cac72191604c40195ec9b92c0988032b19372581310045fc22eab1062038bc845d5620c40717d0fba2c41884aa7a0f74588310064f41ee8b106200c9d83dd1620c40187ea5ba2c4188030f54b74588310045ec06e8b1062a48be871d1620c40b1d90ea92c4188163b21d42588310045f43e80b1062038bc87d01620c4054d905bb2a4188028fe1176548311a51e422eca906200a6
  | 16 => 0x592310055ac0860b246200a3e85c81648c40147b0b902c9188022fa1e20592310045ec3c40b2462008be87081648c40117b0e102c9188028fa1420592310051ec2840b246200a9e83081648c40153b06102c918816ada0420592310055ac0840b2462a7c3e73596438c5e9c3ce6b2c87188028fe096590e3126f1b882cb21c62358bf865c2438c40187ccab8487188030f5957090e311ae5d302e121c6249a6d829d5628c55b4df04baac5188121fa177458a310043ec2ee8b146237c3e7590d628c5b187cea21ac5188121fa177058a310043ec2ee0b146309c3e75d01628c40187887bb2a5188121fe0b7654a310243ec16eca946200c3f40dd9528c4018de41bb2a5188029be097654a310061e21aeca946200c6f825d9528c40187e80bb2a5188031bc817654a3124e3b882eca946200e2f82591528c401c5904b22a518ab70fdc96454a3100717b92c8a946200a3f80591528c401c5e40b22a518aca8f61a4354a310061fbb486a946200c3d7690d528c5e9c3886b2e65188030f1d1654ca310070e21aca9946200e4c32595328c40b8e8e2b2a65188022f61b744ca310061f32ee89946200c3d65dd1328c46d17d0eb226518a8a2f21d644ca3100746192c89946200e8c43589328c40b9c8e2b1265188031d597714ca3101c5f426eab0462008bd84dd5608c50b573013a2c118b7aaee0174582310045ec3c86b046200ab98090d608c40117b0e21ac118802ae600435823101c5f426e4b0462008bd84dc9608c5bb87ce9a92c1188d30f9d152582310045ec3ccbb226200aae82997644c40155b0532ec8988022fe1d65d91310051f42cc5b226200a3d8598b644c40147d0a316c8988028f61462d91316ee1f3b6a5b2262248bd87183644c40147d0a306c8988028f61460d913100557410c1b226200aad82183644c401972e0306c898c3aa7a0f75d913126d4ec1eebb226200c3d751d7644c49b17d0fa9ec8988022f61f53d91310070fa9ca7b2262d88bf8754f644c49b1790ea9ec8988028fa1672d91310051ec2ce5b226200a3e851cb644c40147b0a396c898c36a7a0c72d913126d4ec18e5b2262008be87d4b644c40117b0fa96c8988030fa1f52d91310061ec3ea5b22630ca3d8594b644c40117b0f196c8988028fa1632d91310051ec2c65b226200a3e850cb644c40147b0a196c8988028fa1771d91310051ec2ee3b2262a9a9e83dc7644c40155d05b8ec898802ab60b71d913126f1b28ea3b226200a3e85c87644c40147b0b90ec8988028fe1570d91310051e42ae1b226200c3f855c3644c4018790ab86c89884a2f20d70d91310061fa92e1b226200a3e851c3644c40147b0a386c8989f2a7a0c70d913126d4ec18e1b226200aae821c3644c40155b04386c898936ada0470d91310055ac08e1b2262008be87943644c40117b0
  | 17 => 0x966212e1c4359532cc40187ccbba265988030f597744cb310062fbb2ca9966212e5b3059560cc40717d09b92c1988022f61372583310061fba4e8b2c6200a3f845cd658c40147908b9acb18c4e9de05735963114c3f43886b2c620087d8710d658c5e987d0e21acb18bd30f61c435963126d1f41886b2c6200a3d8010d658c54fc6e2021acb188028fa1372596310051ec26e4b2c6200c3e84dc9658c40187b09b92cb188030f10f725963156e3b886e4b2c620087e87909658c4010fb0f212cb1880297a0e42596310052ec1c84b2c620087e87109658c4010fb0e212cb188021fa1e32596310051f42464b2c6200a3d848c9658c4530fd0e192cb188021f61c32596310051f424e0b2c6200a3d849c1658c40b4ed03382cb189129d60670596310051f420e0b2c6200a3d841c1658c4534bd06382cb188029760c705963100537410e0b2c6200a6d821c1658c40b4ed02382cb188a69d60470596310043f43e80b2c620087d87d01658c40187d0fa02cb188030f61f40596317a51f41e80b2c6200c3f72d01658c5bdc6e21a02cb18a168f612405963102d3b40c80b2c6200a7581901658c40b4ed02202cb188029d60440596310051f42460b2c6200a3d848c1658c40b4ed03182cb188029d606305963114c3f43860b2c620087d870c1658c40147d08182cb188028f61030596310053741060b2c6200a6d820c1658c40b4ed02182cb188029d60430596310043f43e40b2c620087d87c81658c40147d09102cb188028f612205963102d3b40c40b2c6200a7581881658c4010fd0e102cb188021f61c20596310051f42040b2c6200a3d84081658c4014bd06102cb188029760c205963102d3b40840b2c6200a7581081658c40187eeb3aac918c4aa7a0e75592310054ec1ceab246200aae829d5648c40155b053aac918c46ade0573592310045f43ea6b2462008bd87d4d648c401c3ea729ac9188de2fe1d53592316c45e43aa6b246200a3e859c9648c40147b0b392c918c42a7a0e72592310054ec1ce4b246200a3e851c9648c40147b0a392c9188022fa1f52592310045ec3ea4b246200c3e87d49648c40187b0fa92c9189268f61652592310045f43c64b246200a3e858c9648c40147b0b192c9188028fa1432592310051ec2864b246200a3e85dc1648c40147b0bb82c9188030fa1770592310061ec2ee0b246200c3f52dc1648c40b56d03382c918916ad60670592310054fc1ae0b24630fa9c835c1648c40117d0f282c9188022f61e50592310045f438a0b2462008bd87141648c40153d06282c918802a760c505923100557410a0b246200aad82141648c40b56d02282c918802ad60450592310045f43c60b2462288be870c1648c40117b0e182c9188028fa1430592310051ec2860b246200aae820c1648c40155b04182c918816ada043
  | 18 => 0xc8015730021ec0990022fe1171d813201c5e422e3b0264038be86dd1604c86d1790dba2c0990022fa1f64581320061fbaec8b026400c3c75d91604c80117d0e322c0990030fdd464581320061e3a8c8b02640099e8710d604c801a3eea21ac09945b471d443581320065bb26e2b026400cb464dc5604c801b2887b8ac0990032dd9071581320065a320e2b026400d94431c5604c8590fd0f312cb988028fa1262597310051ec24c4b2e6212a5e8398965cc4018dee5312cb9884b93cca62597310051f424c0b2e6200a3d8498165cc4254bd07302cb9884b96cc2605973184e1fbb680b2e6200c3f749d165cc62b4bf06ba2cb9884a9720d74597310951f42686b2e6212a3f8450d65cc425c3886a1acb988028fa1372597310051ec26e4b2e6200c3e84dc965cc40187b09b92cb98b730f90f72597316e61e21ee4b2e6200a3e849c965cc40147b09392cb9884a97a0e72597318a52ec1ce4b2e620087e8790965cc4010fb0f212cb9884a97a0e42597310052ec1c84b2e620087e8710965cc4010fb0e212cb988b21fa1e32597310043ec3c64b2e6200a3e848c965cc40147b09192cb988028fe1171597310051e422e2b2e62b5a5f835c565cc4014bf06a0acb9884a9720d41597310043f43e42b2e620087d87c8565cc40147d09382cb988028f61270597310952f41ce0b2e626ea5d839c165cc40147d08382cb988028f61070597310952f418e0b2e622ca5d831c165cc4014dd04382cb988029b60870597315ed3b408e0b2e6200a75811c165cc4010fd0fa02cb988021f61f40597310061f43e80b2e6200c3d87d0165cc42547d07a02cb9884a8f20f40597310061fb9680b2e628ea3d8490165cc4254bd07202cb988029760e40597310952f41880b2e6200a5d8310165cc40147d09182cb988028f61230597310043f43e40b2e620087d87c8165cc40147d09102cb988028f61220597310952f41c40b2e6200a5d8388165cc4010fd0e102cb988021f61c20597310051f42040b2e6200a3d8408165cc4254bd06102cb988029760c20597315ed3b40840b2e6200a758108165cc40147d09082cb988028f61210597310952f41c20b2e6200a5d8384165cc4014db053aac5988029be097558b310243f42ee8b16620087d85dd162cc4251dd0fa12c5988121fa177058b310043ec2ee0b166309c3e75d0162cc46947d09bb2a5988028f6137654b310061f426eca966200c3d84dd952cc50787c87bb2a598a0f0f10f7654b310243fc16eca96620487d82dd952cc4018be65bb2a598803174cb7654b310061fa06eca966200c6f20dd952cc46947d093b2a5988028f6127654b3100536c14eca966200a6f825d952cc50787c86bb2a598a0f0f10d7654b3100637c12eca966200c3f405d952cc4018de40bb2a5988021fa1c7654b310061e3a2ca9
  | 19 => 0x22f61e65d91320055b40ccbb226400ab581997644c80117f0eb2ec8990ba2f61c60d91320051f428c1b226400a3d85183644c80156d02306c899002ad60460d91320065cb80c1b22651aa9e83dd7644c86d53b07baec8990030f5d475d91328cd4f418ebb226436a9d831d7644c86d55d043aec899002ab60875d91321b45f43ea7b2264008bd87d4f644c801c3ea729ec8993622fe1d53d91321b45e43aa7b226400a3e85dc7644c80147b0bb8ec899462a7a0f71d91321b54ec1ee3b226436aae82dc7644c80155b05b8ec8990028fa1671d91320051ec2ce3b2264b9a9e831c7644c86d53b0638ec8990022fa1c51d91320045ec38a3b226517a9e83dc3644c86d53b07b86c899003275cf70d91320051fc2ae1b226400a3c855c3644c80193ae6b86c8990030fe1570d91320061e42ae1b226400c3f525c3644c80187aa4b86c8990028fa1470d91320051ec28e1b226480a9e831c3644c86d53b06386c8990daaba0870d913200556c10e1b226400ab6811c3644c80156b02386c8990022fa1e50d91320045ec3ca1b2264008be87143644c80117b0e286c899002a7a0c50d91320054ec18a1b226436aae82143644c80155b04286c899002ada0450d91320055ac08a1b2264368be878c3644c80117b0f186c8990022fa1c30d91321745ec3861b226400a3e850c3644c80147b0a186c8990daaba0830d91320055b40861b226400ab5810c3644c80117d0f086c8990022f61e10d91320045f43821b2264008bd87043644c80147d0a086c8990028f61410d91320054f41821b226400a9d83043644c86d55d04086c899002ab60810d91321ac5e432e121a6412d8c325c2434c86b970c0b84869904b66cc17090d32095c741ec99926412d8c435c3324c825b9660b8664990030f9d764d85320061ebaec9b0a6400c3e75193614c80187aea326c29945b479d443d85320068eba887b0a640487f875d7614c8018de40baec2990121fa1774d85320043ec2ee9b0a64028dd83dd3614c86f87ceb21ec2990030f5d643d85326c61f3a887b0a6400c3d7510f614c94593ae621ec2990131d9d651d85320247bc3aa3b0a6509c3e75d03614c80187aeba06c2990029d61410d85320056ac1821b0a6400ae582043614c80b8e8c2bacc2990030f9d764985320061ebaec930a6400c3e75192614c80187aea324c2990026761c43985328b68f3a88730a6400d1d7510e614c8018eaebb0cc2990022fa1f64585320045f438c8b0a640099e8710d614c94593ae6320c2990023de1d61185320074a21ac230a640099e8710f604c825b1ee421ec09928b631c843d8132005ccc0087b0264008bf845d7604c80717908baec09900a3760f74d81320055cc06e9b026400ab9801d3604c80117d0f21ec099002ae60243d81320045f43887b0264a2c9d7310f604
  | 20 => 0x96c12e121aa400d2f625c24354907a7660b8486a920f4e0c17090d5265697902e121aa40095e83dd361548012bb07ba6c2a90125b60b74d855224c3ec3ec9b0aa434c3e74d93615485f2db0539ec2a90024fe1173d85521a49e422e7b0aa44987d8718f61548018bae631ec2a91269da0463d855241e8f39887b0aa400d1d7310f615480127f08b9cc2a90d24f211739855251e96b948730aa483d1e7310e6154801a3ae621cc2a949b4b5c8439855292eb2b96c330aa400a5d8318261548014eb02304c2a94934b5cb40985521a49f43ee8b0aa48393e83dd1615480187ec5ba2c2a90034bd8b74585520049ec06e8b0aa400d2f20dd161548012df04ba2c2a90024fa1c74585521a61e3a6c8b0aa44987c8759161548934e902b22c2a90d24fa1373585520049ec26e6b0aa400c5f7398d61548010fd0e31ac2a90024fa1e435855241c9e43c86b0aa4a8d2f7290d615480127d0e21ac2a920e4f21c435855291e97b9086b0aa400d2f74dc96154801a58e9b92c2a948b59dcb6158552014b6416e0b0aa40093e87d0161548692790fa02c2a94874bdcb40585528f4b7c12e830aa40296c825d0615490727906ba0c2a90034be09741855200696412e830aa4adc3f625d06154801a5ec4ba0c2a91270fd85741855224e1eb0ae830aa40093f805d06154801a5e40ba0c2a90024fe1173185521a49e422e630aa43296f825cc615480187ae9b18c2a9003179cf63185520053ac0ec630aa40087f8758c615480187ae8b18c2a920e4fe1e43185520049ec3c8630aa48393f8710c615480127b0e218c2a90025de1d6118552905b3c12c230aa51fe6762584615480187ae9300c2a90030f5d060185520052ec18c030aa400a7581180615486927f0fa00c2a90024f61f40185528f4b7c12e9b02a40296c825d360548052dd0539ec0a90be5b60a73d81520049fc22e7b02a43493c845cf60548652df04b9ec0a900a5b20973d815219c3ec3ec7b02a400c5e73d8f60548010ff0eb1ec0a93634bdc843d81525169639087b02a40093f845c7605486927908b8ec0a90725be0971d8152014b6412e3b02a43387d87d8760548938ece3b0ec0a90021fe1d61d8152004afc1ae8b02a40095c835d160548012df04ba2c0a90025de05745815224cba40ae8b02a43493e84dcd605480127b09b9ac0a90021fa1f63581528ee97b9486b02a400d1f7310d6054907a38e621ac0a94734bdc843581520043f43ec2b02a43387c875856054a37ad6e5b02c0a93d34710d7598732094ce41ae930e64028dc835d161cc9cda3887baac1990121fa1f75583327361f21eeab0664e6c3c43dd560cc80187e81baac1990030f50375583320043f438eab066400a6d821d560cc8010ff0aba2c1990121f21574583320146e41ae8b0664038be84dc560cc80117b09b8ac1990
  | 21 => 0x831c96090c6b53b06392c1218022fa1f52582430045ec3ea4b048600a3e87d496090c0187d0fa92c1218020fa1f52582430061ec3ea4b048600a3c87d496090db9878e7a92c121b738ecc352582436e71c186a4b0486358be878c96090c0117b0f192c1218028fa1632582430051ec2c64b048635aba808c96090c0157301192c1218030fdd771582430051f42ce2b048600a3d859c56090c0196ee338ac121802ae60271582430051fc2ae2b048600a3c855c56090c0187eeab8ac121802aee0171582430954f418e2b048635a9d831c56090c0117d0e28ac1218022f61c51582431ad5d400a2b048600ab9801456090c0147d0b90ac1218028f61721582430045f43842b0486008bd870856090c0147d0a10ac1218028f61421582430954f41842b048600a9d830856090c6b5750010ac121802ae60021582430049ec3ce9b1aa51e96f825d3635486927f0eba6c6a90034be0974d8d5200696412e9b1aa400c3f625d36354801a5ec4ba6c6a90024fe0174d8d5200697902e9b1aa43487d87d93635486987ce9b26c6a900297a0f64d8d521a61f3a2c9b1aa43493f87d03635480127b0fa06c6a90025b60b7498d5224cbb40ee931aa40097581dd26354907c3887b1cc6a94c7535cb6398d520052ec3ec731aa400c5d87d8e6354801c3d09b1cc6a9003876136398d529862eb96c731aa400e4f635ca63548014bb07304c6a90031e5c26098d520052ec18c131aa400a75811826354801c3ec7a04c6a94bf4b5cb4098d521a49f43ee8b1aa400c3f62dd16354801a5ec5ba2c6a90024f6037458d5200697906e8b1aa40096f825d1635480127d0e3a2c6a90d30f1d36458d521a43e43ac8b1aa400a5c835916354a5da5ee421ac6a90034bdd37258d52006963a6e4b1aa52dd4f73dc9635480127d0fa02c6a90d24f21f4058d5296697b9680b1aa40296e82dd063548092db05ba0c6a94af179da6318d52955a6c14c631aa40087f8758c6354907c3886b18c6a900257e1d6318d5294da7c12c631aa40093f845c4635486927908b88c6a90725be097118d520052ec18c031aa400a7581180635490787eed3b486a920f0f1d97690d5200597c12ed21aa400d2e725da435480127b0fb1c86a920f8798f6390d520049fc3ac721aa528b2f8258e435486d65f0eb9486a90db4be1d7290d521bd97432e521aa483b2c865ca4354801a5cecb9486a920f4b1d97290d5241e9739ae521aa483f0e735ca4354a4fa1ce6b9486a920f4bdc57290d5200597c02e521aa483d2f705ca435480147d0d38c86a90028f61a7190d5200697394e321aa483d37719c64354801a5ae4b8c86a90028fe197090d520051e432e121aa436b2e825c24354801a5ce4b8486a90034b5c97090d520061fc32e121aa400c3c865c2435490727906b8486a90034ba097090d52006
  | 22 => 0x2008000808404800a005000400000100000100020020000000002003005000c00200200800000160000000000012002000801000e00c007802800000c0020000008001003800000c00600180000040040000000000000000001c000014008000c0040000038094004003000001000c001000000c0080040000004002001000000001200a0000018034002007800000400c0000000000005002000400000300200040180030028000000001001000800a0040000004008003000000000400100a8008008008007801402600d0000004002001000000000000100000000100000008004000002000800000200000200100060000058018000001000000c00601400000000000030018030004000004800001c00200c002400a00300080000020080020004253590ea92c521ccba398d5258a431bc9f42ee2b14860093d85dc56290d4f87cc6bacc321bd34798d75986430049fc12eb30c86f4c3c625d66190c9b87ec2bacc3219370f58575986437a61fb02eb30c864dd37105d66190c0187aeb314c3218032b5ca62986430055ac0cc530c863793f87d4a6190c0127b0fa94c321b738dd87529864326c5e43acab0c8637c3c755956190c9b1790eb12c321bae4fa1f75582437361f436eab048600c3d86dd56090dcd87cc7baac121b9b4798f75582430049ec16eab0486e6c3c62dd56090dcd87ec3baac121b9a4fa1c755824300596c10eab0486358be879956090c6b5750132ac1218d62f21d65582431be1e3aacab0486358be879896090c0147d0b312c1218028f61662582430061fbacc4b048600caf729896090c6b1790eb12c1218024fa1f52582431bc9e43ea4b0486358be879856090c0147d0b30ac1218028f61661582430065bb8cc2b0486358bc875856090c0187eeab0ac121b9b0f9cf75582437361e39eeab048600a3d82dd56090dcd87ee1baac121b9b8edc375582437371d986eab0486e6e3830dd56090c0147d0b3aac121802ae60275582430055dc02eab048600c3d751d56090c2553d063aac1218d6a760c755824300557410eab048600aad821d56090c0147d0e3aac1218030fa1c75582430070f418eab048600e1d831d56090dd787ce63aac121baf0f1cc755824300717410eab048600a3d821d56090c01c5b043aac1218028b608755824375e1fb80eab0486ebe3b701d56090dd7c76603aac121baf8e0c075582431ac5f43ea6b0486008bd87d4d6090c25c3ca7a9ac1218d6aea0353582430055cc06a6b0486008bf8754d6090c6b1790ea9ac121802aee0153582431ad5c402a6b048612e9b3054d6090c0147d0b392c1218028f61672582430061fbace4b048600caf729c96090c0157301392c1218028fe1572582430051e42ae4b048600abb805c96090c0147d0a392c1218028f61472582430061fba8e4b048612a9e
  | 23 => 0x802a00200080080000030000004008000002002000200200080080000030010000002001000806400e001000000000400000000000020170000010000000000001c00a005001801401e01c000000000a002003000c000005000000c006001001002c02a002000001803e006000002000000100000000060010060000002005010000800000100000080040010058010010000004800800800d0000008000002002800c0000020098008022007000000c000008001000001200e0000070008000003800002e0000000014000007000001c00000c000000000600000280000380030098024000000006802000a008000803400a00000000080000040008010000010001800400a00b000000000e0170040000002003005801c000000000800400000700080000040020008000004000000802400001100f80080020090000000004002000000000e00300000000040150000000000003002001000200a001000000000000000040000070010014002000001800800400600180140080000000014008004005800c010001001000400a0020000000004000001000c002000003000800a00000100000200030000058000007001000800e000006000400e000000004c01200000080000020000018008004000000000400000c004002c0000000008008000000000000001c000001000800200b0050020000012000002000000500100080040100120014002009000001000800000100080000020000000016006000000000400800c802000000000000000020000040000012000001002400200a000802000a0010028000000003004000400000100080200020000000000000000008801c0140010010000000005002002000401400080100080160028000000000001800401a005000801400000300f802400000c009000000000500100100d800300180000000010088048002008003800000a0000000008016006000004c002001000800002400000000000020020000000000001000801001000000000100060010000000006002002802c0000000008038024006000800800000002a802800e0060008010000004001800000a00100180040060030018014000001000004c00000100400100000080060004000000003801c004001002801c004000000000402000c000002400400300500080080000038014000002000000c000002000801c008008003003c004001000802c00000400600040000030008044000001000000400000d001801400000100000040020040008000004007000000003601f003003000200000080080000050000010000000000001c002000000000400c00000180000220030030008000002001000c000003000000c01800100180180060030060004010000000800c008000001800401200100d0008000002002800400
  | 24 => 0x6d4023565b0932d6d21891cf1958c9ea7a000000000000061c04502b09e4063a5341e6b700000000000141000176d7509a80fd8ef000066c107a720730ad300010985be4314d1181800000056180000006a7535096133a12259d1d28f74bdc5f710c80000000000000000960311800007a0572a300000d664b35092f449000000000000009ca17015c400000000000fd6346af0000e58d02adb3648000eaa0005e9000000008231e2c98b12000253809800000034e8000000c2842ba46d082b0d402825000063118a26d57c00001d19310210000295000000092f58c9d34f62aac4f420d118ebf04ea21f440000010200016d6b3317a24f166a0002cc1d24afe83c00020fc370c1f37998940000001a32e282e42da00010bc91600000015652ec28527d03fc2f27bb0001a7882627720c800078e1624bc0c556ee000000097c000000000071c00076420aa340000000004800179237618f8000bc00000d680018627e61b21b980000000000000db0000293abd48f2685000177d0860002650d547c499900000000009c500000005043543b4800079a000000202c000000000000000000038d2514000742000151568c0002f89f04b9e15e5ef2254b367ff257a650e387962640ccc87e70527a23909f851d408ad01142b1e0fe0b786cc0000000000eb635e0f921d1280bd51742ea426a00445b15351ba00061eafdc0001c22692f5827e52239027a43300000c88bf41480000000000000000000000027000000a00000000000000000e6484c5c98000902317582a6611d800000000005d80000000000000000000245937c8e532ba73910c7400002c040009e117c1b70ed6bfa0001fec0000003cea938d745a517baee0c0e7650a723b80000000028012006002800800000b008800c002000000002800a00100080000080050008000000001005004c00000000c0030000001001000000000100000740060050008004000000002801400200300100a0000004001800400a002000800401600700800280000010030000000002000007000a006000801000600000080b802600c000001000800200380240120050008004006002007000001600100080100020040078000008007001001000c00100a800000a0030030008012005006001400000100480000000080008000000003000000004800a00c000000200d0010018004006000001800201c000800001c0030000008000004000800c004007000000c00e000001800000400800300180020080000004000000003000000e000001802000800800000580120010008000000003001005c0040040030008010000001800801a000002802800600000280040060100038028024008000800000400100080680020000018010000004000800800a007000000000c0030000034004006000801000a00100
  | 25 => 0x2232df8bd4000343000189e8eb33f196c000000000000168aaab0d20af8000000483a24000017e00017e875400000015280009c30000210000a1302a8000000ba61d10c70f6050f153000000000059c0e40e4400007c2e2ccdea5624323c15ee00021800001468ed3948d048520004371e1cfa821652a8f9000022259ea5bc6f0000193003c00055038c8000b0c9fa000000048441f4df99d94485915440000000bc32918aa92580005b90cb800052c5f5903800022d32c0000000a0d00029600000f432f800000000000000000000001eaa5486346450de1378ba8a33000000131c23000019e8dc25d0000000000012f0000000f3000000f8000748654126819402e8f61f8800029406e0002ff40000004310000ee60000001b3400011c00000004620002c000001602254aca58ceac0000a600014200003dc9ac8000000000000000014261e30d80000002e5949800000000000007d800025816f164a90c000128504a4cd15100014a0536141800000000000007680003c639c265c6c000018318dd12424551d1c1d3b05a4180286559473745a1408440008000800132c5ff0fd2984b0863508512c9374000000100527a52f5e09f08d32000560109cf9e9ad2f3ad9cc2e0005f0873c0009800fb9e180009da2f48000b4caee5a61b2c9e453a3d48000f028372378000ea800000025212f428e3750000000000178a6456040000000000ff0000000000000001010380015ae000551082c4fe0004c3add0c36c454b6b1203000e100024191660002ea82e08ba55a61995d0aea2a300014210f426423680000006902f6a05cfda0005058001320a3d00000000002881922a480006f60000000b8207011e00000000005a680002202fc00000000000000378000b3e5e137a9efc7a400000000012340005ec0c780004b7172864c0000005b208040000002d9000000044f00028ec000b680001d18c30000000000000000000007840003f5446800124e9a030a222400000003b1838da4c0a395a7400007775bf80011583694e98000924000117800005042e0000001046a355f6a43cce800047c30e8b9a8ea00021214dc9934ff89185704bb083278cd6ea034bc919c00000061809800004ef12626986d443d0be80003fe56e00004e4dfc24155b8320e4e9f63fa800000009f0000fb800e0001159f2cc7ebc82ec1e5182a11709826488182700d72d24b5858f146833c6a24ec0ae056862c87f1fb187554a003121928947c00055aa74903a2630002a70f9200039f000082e8780a380000009180001468d8617b30d2a9c4180003a980015f45b927118b8dbc8075f307281cc05e0001f4c0000ef000000000005c59400000006c0297000000049837a000155c00015e000024a9553c18001024585160974800000060f1e4cb88000366099d11e67c2b0af
  | 26 => 0x53c7e60003fe830c362b793582e24898583081800032a000238800000085935f8438e1448d000000000002f000236c88662d3181e240000002cb89d00002f5000225c000273150000000050e00000000000000001524a560000002fd8000000000000123c75f0002fa57960002fb00000000000002c80000bd1000000174a00035680011d2000000260476c00000000009aa00000000000001450002afcb0e78f00000013063d108c8000000000000000000000000000007323320002f188c22e100022f00fc43a2e01c2509ab30000110113a2dc531ac380009fc5a20ac96f621a53aa4900004103e610b4d9030b2bb2594c8c02a53e2e300000000001cf45480000cf80000f20151e1956115e03c00025ccd9c000333ac5000043849d9ea94800e400000000000000001a1c0009f80000000828b941a1a4851160484b72ce561660005f81c871ab0452ba4acaae00000000c4000acf0d9895c000bf2000000025a0005608000000000499045816e3af0000000c5821761a0de8000000000000141e80a5c80f68c7652d3c6ac295f82fa2fb91d97d064854680010c80000000000c6c49b5dd1c0400006c19a2b780007020ca0adc00078029a8000472c2a00000003ea7d945ba8c00004a42c52920e2e501263a35c77600055200000000005338b5816411d14c29bcd7050003411d4a62ad862203c4db2bce2bda280000bc203a0000d2c3180ae98bce5090b0a98000000c051c92a64b18a6606a26d0fb45d324a921cb8ca7e00c90ec2ac8bb53fa2f471cbd74678000000be45392244162af80000ecc0000000002d04b3a1d3000290cbdc04c38301486460001108000134ab025a94e40000003d90000ede83d00000008c400000010583e65e41400a44dc637f42e00001c08a4000014400000016405a80004394c319640000003392450cf60003cd846119237e0c700007d2b2f32480010ea8f527190147ee6ae2c821c82d644700012cd0ec92012c83e8d120af626259d3ba0ce268286cbea855000037c00007d0f3013800066428a2d751960f7515239ced0176309809d73887901c89a039663a17b10d01d63d337612d95c40004a1a70879000007eab9cbe4b8833e800000080617f8c9d70ac0d3e2000047c2d81cf9550a1499a53021840006fc38f80d00005332d524340007ec47f0000000b1b0001e940000000002438ee492a2272b3800028b415000145e8df059a5d00a000010696598a0b87136800000000000000000004e0000000031a98900000007b80493d029e50f60ac0000ff00000000790978000bae06aa96800048424700005a20001cd80005080000002a8c0000005d2000000030200000000000000000000c8000000027b00004dd441adc40006da00721480000000001cbc00005617980000008a80939a7c0000002411c940000
  | 27 => 0x1d4608000ed879e00008496623ab00011085ae00041700009ec0005f11d8400033640200006ca0001672bf80000853fbac015f600037012b14687524de22e88a26a0000008d4bcad01c20b6d47e00025580010ee1dc1648d6c000000489a8a43240000000000ef40001602fa9284b81550ab9000047b00006110340c01542a0589c1d837f928c000000525800000089902a000110270e5d78001070b7600000580003725b30370e461e95478000f4659c2069ecc0008c00000850d3600058a9d6936e00051ca7109a890a3d3ae6d62c5f31c3806850c42235e8f7d3709f13891ea01d879555300009f2c321a80a70fdeb43562000012c3cb1c49a0800000053826c40009510000eb40000003f519c08069ef3ba930000049d2f118ac00012450498117f849757880000001010002cd0e5835f28b8c6cf3e57d144aedd33c9de29f8d8c8f47be269ac201b600047300008a400045386bc0000000d094e00000005ca82d80000003d680005587c008603c10e21965c108292b48d20000000000183000000075257a5c88000ea01c803884e933e9b000023500007e209ead2c8343ff253000046c0004280a1c00095e45ca070c249121808001220000000158155e44152f877800073c0000000000c0904c80006326b118416c400080e0000b885a49842140ec4cf22b95aa0000fbcb8f29e84b974011a00000012ba9440f68924000b061ae0000b6c0000000000000a1c00028540000970001ae580c4a914f000000054e00022b5746ae800010490a6a8400002440000e91c180000009660a430f928c00033300009685920000afc000000339ad4d092c4b266306d17e5ef4400000000000577869cb5078400002a82560000002e48dfa000000002880400000000000000003fc80000005bb000148495472145913a4a263ac00000e819a39500024a000030537801a875c45a0001b7c00048c46d2d8177c35d30a963572c293299127c9fe8a959099081182c228c28088c02b61c30cac97c02536083a0aba74c0000000a981493c518442d88b800001e04100000002b4529479c0f727c0b8467742705b5198c0854b199406a6b424289e4e723ba09419a4f9c3c006829b00000ed44518f4a3c000000067800095311c2e740004b83ae00008f86385e20000c941712fa03310109020002a449c26b314faa08ff4c20002880cb42b591332b086e6c0e1d830ecac68fb1e787f80007ca00000007640004d5800000076340b0000bbc00005a80000000001dc80000001a3609a0a400018b000000179a0000000f9400000043e000000078b628a10068e8de596859481e44855022687400003c9000086e04d36a8000dae7dc46a93ed05e97d000173103ca220001f74000b5800021ad8940002d70001270bd35be002c8f00005b68000000a9b4628000ce25110001
  | 28 => 0xd5800052110912ac0005e821292eeb9836387d0124064000000000009e000303c0001c000000000000000f59f0c00000044a0000ba257e0750000816411000221ccc66a23be19d4bb24c53a5922951c0d227295a507c74100015453e85f841a89e87bcbb025e07c400000020f075cc888332a11f6000000001d88780003fa031016c000a370df846d0b499547128c52fe26e35a80016a45a3237292800065c49d083837a85b46209107942e71db8a553ae1732890db40003590001d5c00046b187ac8c7f0304564969d690157000000074ac0400000000002242b3a9710b00fe1682f8c5aa3db4329424c4c1c560c9d649208c801807495161330191de4e743111391bed0ce3ea313a3458209c009e00014a464e56680002c6b9e27a886d4567701152a783c40c500000000003d615d08180000005ec8fd043e000346249567e00000000000003795ff047800010b06103451f2a9a0000000b7e00028fa5b17447d240d860500001e08880000000001f800000008695171654a068fc39b1a3cada45c1fd870c47ead23722c5d654af2169a68443289f0000000f2e00000011d067000004e800097e2cc1f40000ec05eb0110e2149e96a000000000039d0002c0d76a00012e00012ae00055400001ba85d1fc80000000000000aa472e34e04e00011c66f909600015ca00018700000000005a5000000055b0be07a80000000000d280002c33fe0000000000416063c0004210000000b4455e0000000fa03c91678e8460e0001a68000036b4e2440360ed4b99482aa0c76840a5a1251c71e9ed48ca81c34c9e7479801983851b00016b50742231252e008a80000002ae000099b00000000007c54588000000000423800000050b36b0000000000000300000000029b8d8829e0004fc8000e6878e19100000707bc4d18cc0b689301cd0a9495a0890d1218c0005f00002ba426c0003ba2904000000236109400053b071260805879a51180000008d910116397e2c23000018d63e0004082db80003bf13e8000e5cbb200024f800000000000000004680000000000aaa2fd9c209b87d6000000079865129800012f60372f28ff8d0800002d29900000000b480017fe0004350ab41440004e30000000000000000000000038a86ed5d47e04b10c482421261c08001104000314116c000000000191c6ea00047b800078a0000b08000360000351aa3143000061600014285b813c1be12d67e130080007da0d336daef4d1601334709748469091ad28f03ca9155ad935c58a14330280014a8000372800089289637b8a657561d007d9a604debdf47f80f939856400021b4c404180a59c456a01c94fa800166e5533f41a0c0000c1526133c74e5fe504000051e000596273c7141880468e2c000a4400000000000003bf000165263956c81e800000017793f4000
  | 29 => 0x6104000000064a0000001464d6c4a854f982012ab1d2281f7c00022c00006940940000001cc00002cd049800000082d40193f92684ba528b06052c8f109d80001f261f00000000000000000d200000000001201042000089957c3a824b0000000000bc0000000000000022a800166447d1509d14000b470e6300d1d09410d50000000000000000000000036e8ca8e540005761db400081300030040000c461a8f40fae58b2c080014ec3a807a957176629d4061f94000000000000048016039a8000a480000000000000b5530f0108bac1230002eeca50186000012c39c0004d614540000c9198b1003885725129de0e66bcc000016119abad0c101853925b32332db0d94c1a0102ad971a4f00000a680000000000000000000608930d4da0000000000ea24d600002b80001df0000000000000261115c0002ea00000000007131940001076bc7203a29910a9bd57b117811600053487580006ed4790000bb4000000014c196000000000869e4ce5090ad54ee210050ac8908880f5ba80016ca9f32b2a58436a62a386a118e9c6bb57315e4688be73549020000167054000049e88e39311950843583f187bc6122e9119262d64e30c4eaacd80004e717f18a40000005b102f4568c02559ab210444e829a1c5988c3ef35e1b416d47fe4381e996a260f14d8c850be7c734900000006a600000015c20f60002b1ca865b5374ad68bf2a931351f34f441b9621a0e57425af37426d880850409a152cca04592fe10182d05d74b81fc46d8a0e5b19864e18041052803011066d000040904000024e24b4a186972a413e0000b09276b0986f6c3f128a3609be0005bd000115623a1f0800000000000018cc4f621340fa098f5e9501e087d95002332a900000007f62d8000020037c3de99812384c60ec982800091d0000000faa0002aa80015a80000000000000000413a4053d608e45109acfe40001c015f07c60002151968b7477b14099ad0049293192814cd08b029e066d48a0000001930000ba761102994a6a0a4b4b059210000258aef184ea683f806d96ae6f13c81c913b836e5cbb01d3cc2543aeab140ba09b4a72b7c20ea731f5800036895b321a4b8ece34961ba24d1a6a460002c4d35e3394b8aa5442a868436056c7849f22ab08d458ca2c2cc8791572b7d51b0228b867ae196a788d9e17724c9c108acb5e30e08a5262a4d0aa288425241d1ea000026e9003e314f80000b93da04494b20000002b680ee00019780000008541b793440000003a227dd6221850000001012c39575800000000000000003200000001e90000000282a63c00049a0000a5046800042b03b80000003772cf8b92000000079c9b24532b6000091e972189800000000000000000000003f3800000000000007e400000057e862910800000000016208510fe8000000000000
  | 30 => 0x81a94000582000269d27e496532980c6528d65088000cc48660ed80013660004a491cc0000005b9962005c9d60002fcc00000053e8048000000481a13c56200017800007040000001e140000000000000066c0b0002ed141800000024cc7b054400001a4000000000285984a21c1d3248c00000061483580000e50000000000bb15c213b800000047ea8985f29a53b3000124c5e30828d2d50ea7140c0cf015a00035f00000000000001b146a45e84630fc800033e2608000c4800050e95c1434bbf5569650052ad65238dad0bc0000001a70b520e70bc0b1cdd6c420631fb838298a2b400000005660001c608d2073377a0c147000000010000b217f0000ce92989855fd924d3b20000d91e2068a000022094886674800023386768dc00000015647103f480000000000af9d78a0c07c00000010de00000000000be000000000000000000005e8b346a400008b80000000ce800000010f48200014baae00f60a4093c5be37d168025484b08fa6e426220950f2e68e8ebdd0df1984000000000089c000000000000157600034d000000044b4f00114c0473f0002ad0a820003292621828aff44600001b4000123a9ac85696800009d49286c628680000000184c60000000ad5000000032e000000000157c0000001b4c000000222a2615301ac00018d00005e60332af50504eb50b8aacb9c109586136d3ca4da05da5d4c1847f0db87341029df52d984151200012a80003d0000000000000022800021cc00093600000000000000000dd000000055d1c6c8e471e00005bc9921591ec8da077000038e80002887b823205d0000a850d49cb400000030b0280000c4d2269a3538e7993ac00000000000002fb00000000000f10000621134837800068859e09d97060000e88000af0a9d17180008ee80d000000029a34039d800000000028b2b300005935a780001740000000d3086c036000106c1f81641ce1678caa00000026c800000000011c011e529288013c79c2bb0a02c1d56200000015a80000004ff23e9794357185000171c00000027b800000002021f859600025280003741d557682f8cdc00044e00002a0c2f543000000037113f2bcc000bf51c29bc9464c1d4be19a80ce00000000000002970000000ac470b57819fc52404716a0000d2ab2449b8000000a2d1768000f903fd513a45c22a2612502704eeca78196252c4e270019020c91e89db1450bed61e41c5e28000000000000177400033f05380000008c20002810000abc0002a4012000036899340000001ca0090f0473140a9a000000005030b10e1e8ef04380000000000000bc85ba23700006687c0000015800013000000027446205fd157920d70c0005d6228d7f20ca0a90ed47cec2d000000135200000000014005400000000dc4b5c5e795ad85c0002162ea90288e00000000e0
  | 31 => 0x5c7086a87c9d40000000ddca4a8aa4fe800038c6911be8180c7ca494af800068460b5dcafd000004300013cc2aa6ab4f51facf6a0000000000cba13e0000000c440000000acc0009fb0b7000114a0006209b100005ca0001b9c51800023188980000001b800000000004b2247c0004b958917700003610a896f4d1423d000000077c35362380344d89a4000000106c6d459daa2800000021022d400000023f117c0da0003611eb12fc3dd2e2a2b854e38c000000000078c0b32560000435129a734f4225a0cc8e447ae30300024e4aee00000000003500000000000a8e27c58e2d584ac0000002b718564e4000093982e0003bf92b82ea99c00012240000a9000147163000061080000007db19a8000ae60d935500009cc02d56328817f000057c8000c120000ee80005cc00009000001780805958000000000000000000077d204a488a0e000415800000000035400000005200001d8800094f0f1aa50b9000000011a8cf00e3000206400026201081d400000026c24d545079153110f0b5607b53da9d030e2b00001f4466e000043007000031d5ed020d19400046180010c00004d717b000023b1758000000393554a27867a000000209000000000000000000005af9a500000003fa0670000b6f5f7acb800000056e800055c00000000012229bb05a2384000000108a00457a3670000b900002054d50000000000624800002200056595bc43a69338a22200007f30000b64264c0c000063061a0005cf87812b876e00000004304440000000c1a1460001eac00044a1f30000000000000124408c84554b80003f00005bc1d3c35645832f20c415625027ba26c9e264145f00012a800021f035c0006535db2bd15c6be50000000e862ee0f82f500fe000612272d31a7b60d016dc4b62ca3dbb0484ca7e40001dc477a0000b
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1b981f3061f5218d40006074c187d48635000181d87e0f5218d400058364b83d48635000161691e0f5218d407a48766353944635000181d87d4c5118d400040f65e85c84635000141c955cc63d89400040fe61761d9525000141c935d876549400050d245761d95250107a0c6360a63549400050725d6318d525010721c936187154940005072557618f325000103d98d48764c940007224c1201d9325000141c955d8634c940005252457618d3250001496919d4634c940004876635218d325000141c955cc63d85400062320c72595615002509c98594735854000507654611cd615000141d95d807358540096071cd8518d615000103d981d463585400060b6147218d6150001894811cd6258540006075d683988615000141e95dd8638c540096259c58718e31501fd41f989d4638c5407f5076627518e315000141d929d4638c5407f507a547518e315000121d98d48638c54000607a14635ca315000181f8718d528c5400040f663521d93150001499900c4764c540007244c1101d93150001894811d9324c540005072557618c3150107c0c635c9520c5400054a648855c031500015919118d700c5400972498d315c0315000141e95dcc6388540005a864021dd921500016a19008476485400040f663521d921500014a990084764854000728481101d9215000141e95dcc6348540004a96602118d21500016a19008463485400048b66372d9152cc0016a19008764487300040fa60435cb654c00103e98d0172d95300050724d401d9524c001c294048076549300048b66372d91524c00181c8619175cc53000538640219d9214c0014e19008476485300059864021d95214c1d781e831977448530005a864021d91214c001561911c2735492000558644701cd524800124f9858c6354920005912456318d524806f42c9761a43549200060b1d9841c5524800116b985cf70549200056864470dd1324800138a9810f704c9200069120d52584614800906c985d9520c5200040fa60435cb654400103e98d0172d95100040f66274197634400121d9819443d8d10096269d98010f634400121d9810f52d8d10004876606510c6344001a1b656004318d10006861958010c63440258987360043d89100942e25d8010d62440258987360043589100040f660431d952440018358460476549100040f663401d95244001c2940480765491000718485201d95244107a0c43608635491000619608769c552440016899010f62cc91000526640431d932440015319010d758c5100056864870dd1314406766096605524811019cd8661521c52044001b41835487148110004d8661528c520440a3c6076d9521481105266821f84485204414baa086e112148110527281db84485204400136195e0d2148110004e8a6243485204409bca07690d2148110
  | 1 => 0x4e71219dc00b91c84cc2b3371608ab23c0014e8c6400094503da94001b200009e0025844007a000c80000000008cb60023d622c0000000000000134005496c56342a8cc44370aa9042825fad584862903d0e621283508790c938705d3587c74490011c7e003f0013c9d0227c40764099c00ae00178c6424800816a358270186511a0d327050b10c88e001986a6f5e0a91a4d35180768963000b4122c9f156aa2e26c0000000000008242e8280a00158003e000d8a6002faf40e6c12299302d49931680614b24001e0b00050030080208030140800000000c010981800000002800020602004040283c00020300c060e018081a00000000c050100c000b0602808000181406020b8100c030101c00000980012010000002080060ba1e821d56090c01a0e8360875582430068360d821d56090c0182e7360875582430060b1cd821d56090c0182f7060875582430068adc1821d56090c01a2b3060875582430068a0c1821d56090dcd81e83dd472582430040fa5c87d496090c0103e97a1721582439a44ba63625d3635480181d87a136398d5241e0710f8758c635486f12e989c97690d520060b61a729c6435480182f869c97090d520060be1a825c2435480152990a097090d520050b259825c2435480152b906097090d520044b663625c24354a6912e98d89741855241d0724d7458c615480181d7460c60185520060d5d181180615480122d9221570d91320050b648855c3644c80103d989d464d853209662dc98010f604c82521c9361372597316e50724d84dc965cc40103d98dcb40597310040f66340dd952cc40103d9810f72596310040f66372d01658c40122d92a1770592310050b64a85dc1648c40103d98d4b70592310048ba6372591528c40103e98d4970d913141d83a4f84589520c40146592a17764c431096261cd8010d60884011a59808673d912100568640219cf64484015a19008570d912100507a57739cf64484015619008575d8d2100568640215d3634840181e75a0f64d8d2199d0b64a751936348401561900857598d2100568640215d263484015a1900877458d2100568640219da434840142d92a167690d210040f663529da43484014a9900867690d2100568640211da43484015a1900857090d210055864021dd560484015a19008774581210057064021dcd60484015c190084735812100607218835d4635000111c984c17518d4000607e1f8558c635000121d922156318d40004872627558c635000121c985d56318d4000607e1d7558c635000109d97e1b5318d40004876636514c635000121d981945318d400040fe6175988635002581e835d66218d400048726163d48635002509c9361f5218d400060761f53d4863501b941c9361f5218d406e60724d87d4863501b981f3261f5218d406e6070c587d486350
  | 2 => 0x14570722a0004cc761aa10a6904a81809700001243c000040000000000010003050075002dc007f0d2b482304a9a0620000001160000000881c028b8007d628f41c8a000000018002f922004b05ce69400074da00440015ea22baec5eac001d
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa0840062000140751ee0c10eab0486008072a53061f5218d4000601b0ec9707a90c6a000301587a4783d48635000100ed4d0a31ae518a8000a24680811d9324c540
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x94b
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x138e
  | 10 => 0x138b
  | 11 => 0x138d
  | 12 => 0x98d
  | 13 => 0x98e
  | 14 => 0x9cb
  | 15 => 0x9cd
  | 16 => 0x9ce
  | 17 => 0x168b
  | 18 => 0x4
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0b
  | 22 => 0xa0e
  | 23 => 0xb09
  | 24 => 0xb0d
  | 25 => 0xb0e
  | 26 => 0x1409
  | 27 => 0x140d
  | 28 => 0x140e
  | 29 => 0x249
  | 30 => 0x24b
  | 31 => 0x24d
  | 32 => 0x24e
  | 33 => 0x16cd
  | 34 => 0xb49
  | 35 => 0xb4b
  | 36 => 0xb4d
  | 37 => 0xb4e
  | 38 => 0x1449
  | 39 => 0x144b
  | 40 => 0x144d
  | 41 => 0x144e
  | 42 => 0x16c9
  | 43 => 0x16cb
  | 44 => 0x16ce
  | 45 => 0xcc9
  | 46 => 0xccd
  | 47 => 0xcce
  | 48 => 0x1709
  | 49 => 0x170d
  | 50 => 0x170e
  | 51 => 0xd49
  | 52 => 0xd4d
  | 53 => 0x1789
  | 54 => 0x178b
  | 55 => 0x178e
  | 56 => 0x98956
  | 57 => 0x98955
  | 58 => 0xb0955
  | 59 => 0xb0956
  | 60 => 0x94b16
  | 61 => 0x140955
  | 62 => 0x140956
  | 63 => 0x95416
  | 64 => 0x209
  | 65 => 0xb4956
  | 66 => 0xb4955
  | 67 => 0x94b56
  | 68 => 0x144956
  | 69 => 0x144955
  | 70 => 0x95456
  | 71 => 0xcc955
  | 72 => 0x170955
  | 73 => 0xd4a
  | 74 => 0x1a09
  | 75 => 0xd4955
  | 76 => 0x1549
  | 77 => 0x178a
  | 78 => 0x178956
  | 79 => 0x589
  | 80 => 0x14c9
  | 81 => 0x134a
  | 82 => 0x2c9
  | 83 => 0xb1395
  | 84 => 0x138b16
  | 85 => 0x4b
  | 86 => 0xb5396
  | 87 => 0xb5395
  | 88 => 0x138b56
  | 89 => 0xcd395
  | 90 => 0x171395
  | 91 => 0xd5395
  | 92 => 0x179396
  | 93 => 0xb0995
  | 94 => 0x98b16
  | 95 => 0x124b
  | 96 => 0xcc995
  | 97 => 0x98cd6
  | 98 => 0xd4995
  | 99 => 0x98d55
  | 100 => 0x178996
  | 101 => 0x3c9
  | 102 => 0xcb
  | 103 => 0x15c9
  | 104 => 0x12cb
  | 105 => 0x1689d6
  | 106 => 0x1689d5
  | 107 => 0xb49d6
  | 108 => 0xb49d5
  | 109 => 0x9cb56
  | 110 => 0x16c9d6
  | 111 => 0x16c9d5
  | 112 => 0x9d6d6
  | 113 => 0xcc9d5
  | 114 => 0xcc9d6
  | 115 => 0x9ccd6
  | 116 => 0x1709d5
  | 117 => 0x1709d6
  | 118 => 0x9d716
  | 119 => 0xd49d5
  | 120 => 0x1789d6
  | 121 => 0x17c9
  | 122 => 0x5c9
  | 123 => 0xb5696
  | 124 => 0xb5695
  | 125 => 0x168b56
  | 126 => 0x16d696
  | 127 => 0x1696d6
  | 128 => 0xcd695
  | 129 => 0x168cd6
  | 130 => 0x169716
  | 131 => 0xd4c
  | 132 => 0xd5695
  | 133 => 0xa0a
  | 134 => 0xa0b16
  | 135 => 0xa1416
  | 136 => 0x24a16
  | 137 => 0xa0256
  | 138 => 0xb4a16
  | 139 => 0xa0b56
  | 140 => 0x144a16
  | 141 => 0xa1456
  | 142 => 0x16ca16
  | 143 => 0xa16d6
  | 144 => 0x289
  | 145 => 0x4d
  | 146 => 0x1489
  | 147 => 0x1849
  | 148 => 0xb89
  | 149 => 0x124d
  | 150 => 0xa0cd6
  | 151 => 0xa1716
  | 152 => 0xd09
  | 153 => 0x150d
  | 154 => 0x1889
  | 155 => 0x1609
  | 156 => 0x128d
  | 157 => 0x409
  | 158 => 0xcd
  | 159 => 0x18c9
  | 160 => 0xe89
  | 161 => 0x12cd
  | 162 => 0x58b
  | 163 => 0x178b16
  | 164 => 0x160a
  | 165 => 0x148b
  | 166 => 0x28b
  | 167 => 0x58a
  | 168 => 0x179416
  | 169 => 0xb4255
  | 170 => 0xb4253
  | 171 => 0xb4256
  | 172 => 0xd4255
  | 173 => 0x1a0a
  | 174 => 0x16cb55
  | 175 => 0x16cb56
  | 176 => 0xccb55
  | 177 => 0x170b55
  | 178 => 0xd4b55
  | 179 => 0x178b56
  | 180 => 0x16d455
  | 181 => 0x16d456
  | 182 => 0xcd455
  | 183 => 0xd5455
  | 184 => 0x179456
  | 185 => 0xcd6d5
  | 186 => 0xcd6d6
  | 187 => 0x1716d5
  | 188 => 0xd56d5
  | 189 => 0xeca
  | 190 => 0x170cd5
  | 191 => 0x178cd6
  | 192 => 0xa4b
  | 193 => 0x128e
  | 194 => 0x198b
  | 195 => 0x150e
  | 196 => 0x2cb
  | 197 => 0x20e
  | 198 => 0x19cb
  | 199 => 0xbcb
  | 200 => 0x14cb
  | 201 => 0x154e
  | 202 => 0x178d51
  | 203 => 0x5cb
  | 204 => 0x3ce
  | 205 => 0x17cb
  | 206 => 0x1a4b
  | 207 => 0xecb
  | 208 => 0x15ce
  | 209 => 0xb09895d
  | 210 => 0xb09895e
  | 211 => 0x9894b1e
  | 212 => 0xcc9895d
  | 213 => 0xd49895d
  | 214 => 0x95455
  | 215 => 0x94b55
  | 216 => 0x58e
  | 217 => 0x144591
  | 218 => 0x14d791
  | 219 => 0x14c591
  | 220 => 0x1a0c
  | 221 => 0x1a0d
  | 222 => 0x180a
  | 223 => 0x139416
  | 224 => 0x99556
  | 225 => 0xd5791
  | 226 => 0x995d6
  | 227 => 0x180b
  | 228 => 0x59451
  | 229 => 0xcc591
  | 230 => 0x134c
  | 231 => 0xd4591
  | 232 => 0x179a11
  | 233 => 0x17d791
  | 234 => 0x17c591
  | 235 => 0x14c
  | 236 => 0x9d6d5
  | 237 => 0x1a1791
  | 238 => 0x9d715
  | 239 => 0x9d7d5
  | 240 => 0x5d791
  | 241 => 0x5c591
  | 242 => 0x1797d1
  | 243 => 0x1785d1
  | 244 => 0xbcc
  | 245 => 0x16d816
  | 246 => 0x5395
  | 247 => 0x139255
  | 248 => 0x1a1395
  | 249 => 0x124955
  | 250 => 0x1a0955
  | 251 => 0x58cd1
  | 252 => 0x58d51
  | 253 => 0x151295
  | 254 => 0x19cc
  | 255 => 0x1a0591
  | 256 => 0x1a4591
  | 257 => 0x59a51
  | 258 => 0x58e91
  | 259 => 0xd695
  | 260 => 0xc9d5
  | 261 => 0x1692d5
  | 262 => 0x1a1695
  | 263 => 0x1a09d5
  | 264 => 0x12c9d5
  | 265 => 0x180e
  | 266 => 0xcd415
  | 267 => 0xb5a15
  | 268 => 0xb4d55
  | 269 => 0xb5715
  | 270 => 0xb45d5
  | 271 => 0x1440d5
  | 272 => 0x145715
  | 273 => 0x1456d5
  | 274 => 0x1457d5
  | 275 => 0x1456d6
  | 276 => 0x16ccd6
  | 277 => 0x16d8d6
  | 278 => 0x58cd6
  | 279 => 0xcc0d5
  | 280 => 0xcc255
  | 281 => 0xcd7d5
  | 282 => 0xcc5d5
  | 283 => 0x151296
  | 284 => 0x59296
  | 285 => 0x179296
  | 286 => 0x188e
  | 287 => 0xb0216
  | 288 => 0x21416
  | 289 => 0x181416
  | 290 => 0x155416
  | 291 => 0x59416
  | 292 => 0x180b16
  | 293 => 0x154b16
  | 294 => 0x58b16
  | 295 => 0xccd55
  | 296 => 0x179716
  | 297 => 0x3d716
  | 298 => 0x3ccd6
  | 299 => 0x17da53
  | 300 => 0x181716
  | 301 => 0x1715d6
  | 302 => 0x59716
  | 303 => 0x180cd6
  | 304 => 0x1a57d3
  | 305 => 0x15ccd6
  | 306 => 0xd4cd5
  | 307 => 0x40d52
  | 308 => 0x194b
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 1455
  | 6 => 4585
  | 5 => 3154
  | 4 => 202
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
  | 8 => packedAt gbK8 (1870+((h/22+packedAt gbK8 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 7 => packedAt gbK7 (59655+((h/485+packedAt gbK7 (53835+(h % 485)*12) 12) % 2556)*12) 12
  | 6 => packedAt gbK6 (239944+((h/1528+packedAt gbK6 (220080+(h % 1528)*13) 13) % 6053)*14) 14
  | 5 => packedAt gbK5 (199749+((h/1051+packedAt gbK5 (186086+(h % 1051)*13) 13) % 4579)*13) 13
  | 4 => packedAt gbK4 (14743+((h/67+packedAt gbK4 (14140+(h % 67)*9) 9) % 267)*9) 9
  | 3 => packedAt gbK3 (492+((h/2+packedAt gbK3 (486+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe0f03c1fc1ff87fff80ffc13d13c0cf3cf
  | 1 => 0xf0781f003fe1fe1ff8703ff07c6d2ed0733d33
  | 2 => 0xff801fffc001ffe1ff803fff838e30e383ce3c
  | 3 => 0x1ffffffe0001ffffc00003f03f03fc0fc0
  | 4 => 0x1ffffffffffe0000000003ffc003fff000
  | 5 => 0xffffe000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x884020080240220092080210004004045045
  | 1 => 0x1050850015209214882092a068250650312512
  | 2 => 0xad010a56400125415501254d018a30a1828a28
  | 3 => 0x8402139aa6540001e64d80610ad03b02d80f80
  | 4 => 0x8445ced3b99f99800060186337fc0036ff000
  | 5 => 0xce67800e031031104408060843ffbdf8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37115
namespace PEqualNP.Outside.L_meta_37115
open PEqualNP.Outside.L_meta_37115.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := (concat bs0_3_0 bs0_3_32)
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
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat (concat bs0_4_0 (concat bs0_4_32 bs0_4_64)) (concat bs0_4_96 (concat bs0_4_128 bs0_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
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
theorem bs2_4_128 : Interval s2Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 6 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
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
theorem bs4_3_224 : Interval s4Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 228 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96)) (concat (concat bs4_3_128 bs4_3_160) (concat bs4_3_192 bs4_3_224)))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 26 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_128 : Interval s5Atlas 3 128 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 144 := (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 (concat bs5_3_96 bs5_3_128)))
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
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 883 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)) (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 bs5_4_416)))) (concat (concat (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)) (concat (concat bs5_4_544 bs5_4_576) (concat bs5_4_608 bs5_4_640))) (concat (concat bs5_4_672 (concat bs5_4_704 bs5_4_736)) (concat (concat bs5_4_768 bs5_4_800) (concat bs5_4_832 bs5_4_864)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 802 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 bs5_5_384)))) (concat (concat (concat bs5_5_416 (concat bs5_5_448 bs5_5_480)) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576))) (concat (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)) (concat (concat bs5_5_704 bs5_5_736) (concat bs5_5_768 bs5_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_192 : Interval gbAtlas 4 192 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 202 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_3136 : Interval gbAtlas 5 3136 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3154 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336))))) (concat (concat (concat (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528))) (concat (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)))) (concat (concat (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)) (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912))) (concat (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008)) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 bgb_5_3136)))))))
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
theorem bgb_6_4576 : Interval gbAtlas 6 4576 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4585 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))))) (concat (concat (concat (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)) (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))))) (concat (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)))) (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272))))))) (concat (concat (concat (concat (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)))) (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))))) (concat (concat (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)))) (concat (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)))))) (concat (concat (concat (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552)) (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)))) (concat (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000))))) (concat (concat (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 bgb_6_4128)) (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)))) (concat (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416)) (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))))))))
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
theorem bgb_7_1440 : Interval gbAtlas 7 1440 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1455 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 (concat bgb_7_384 bgb_7_416)) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))) (concat (concat bgb_7_544 (concat bgb_7_576 bgb_7_608)) (concat bgb_7_640 (concat bgb_7_672 bgb_7_704))))) (concat (concat (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864))) (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))) (concat (concat (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)) (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248))) (concat (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344)) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8feeaeeeafee8eae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37115.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.or,[2,5]⟩,⟨.and,[1,3]⟩,⟨.or,[0,4]⟩,⟨.and,[6,9]⟩,⟨.or,[0,8]⟩,⟨.or,[2,11]⟩,⟨.or,[1,11]⟩,⟨.and,[7,13]⟩,⟨.or,[10,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37115

open PEqualNP.Outside.L_meta_37115 in
theorem PEqualNP.Outside.L_meta_37115 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
