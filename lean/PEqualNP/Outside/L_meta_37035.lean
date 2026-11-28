import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37035.Model
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


end PEqualNP.Outside.L_meta_37035.Model

namespace PEqualNP.Outside.L_meta_37035
open PEqualNP.Outside.L_meta_37035.Model
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

def SBf (j : Nat) : Nat := [6, 7, 6, 6, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37035

namespace PEqualNP.Outside.L_meta_37035
open PEqualNP.Outside.L_meta_37035.Model
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
end PEqualNP.Outside.L_meta_37035
namespace PEqualNP.Outside.L_meta_37035
open PEqualNP.Outside.L_meta_37035.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x10000801924bd01b1cac8a5002cb082830009002918026003a2300c2000c6800f3a8542c029951c4800fa91a5569e00157174e0c03401c108144304904504aff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x16070d27d000d800371e830000436800640000000000042800800000118002811800be003a800ba470d000c01b091084a55001b8745310800a2440002c007c001cc0c1f001a8824f1c9601a6100134de293ba0ce200098f81e082a10cac2b001ec322600138ce812d18c2a00000c0cc1819800d6353a0d08a00170b4925c0019462202515c005b0000000000b000905200000003b3604108053f0bc064b000442e50049c0987a0f178c4781f81cd00012074702a1e0044e722c9e42882071d8440a32200fe0001010000c042c0c0400001808000828240864180414301028180008180c0c0c08140418140c20001838001c0c027aa5a1cf947439f286873d5490eeea2a1dd14543cfa9a873f5250f6ea2a1cf14543da28a87345150e78a0a1cf950439ea9e853e51d0a7ca1a14f55242bba8a85745150a7ea6a16bd4942dba8a853c5150b68a2a14d145429e282853e5410a7ca9994f55332bb28e657551cca7ca9194f55232bb28c6575518ca7ca8994f551329f2a0653d540cb9a64194f54e419ea94833e519067ca120cf54c419ea90833e511076ca220cf940419f2a6633d54cc6dca598db54b31da20e633f548c678a918cfd51319e2a2633e540c67aa818ed104319f2a6433d54c86bca790d754f21da20e433f5488678a910cfd51219e2a2433e540867aa810ed10421bb28c8175519027aa7204f54a409f28c81b6519026ca3206d546409f284813d531027aa4204f944409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f553209faa4413c548827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310da20e213e548427aa9084fd51109e2a2215f53442b8a6885bd4910b629221b4414427ea8084f15010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1a000412028314020030988b800007800020007000000008a4000000006c8aa96018004380b000c70081800418d18552d0e3661943438d18553d0a3661943428d185544ca3860551328d185540cb2652107318b588548c6356510431a558c410c71653107218758c54886356510421a958841086346154c408d185521023461553308d987548c23461553208d98754883145310510c9148414423661d50108758c540422d6215010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s1K4 (3970+((h/44+packedAt s1K4 (3618+(h % 44)*8) 8) % 177)*9) 9
  | 3 => packedAt s1K3 (1036+((h/8+packedAt s1K3 (988+(h % 8)*6) 6) % 53)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xe07fffc07e0fc1ff0f83e0fffe1e0781d27ecc
  | 3 => 0xff83ffff800ffffff003ff07ffe007ffe38f0f
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x21000889100200002284a108802290a404b055
  | 2 => 0x4b199187249492cb05a168d3b214350cd256cc
  | 3 => 0x862aa2120d29315550425a4555404659630b0a
  | 4 => 0x145344244981a5a69968108669996011b80da0
  | 5 => 0x1863873871ce39f8ee739ce071118461ffe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00faaaaaa0faaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37035
namespace PEqualNP.Outside.L_meta_37035
open PEqualNP.Outside.L_meta_37035.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x380600102a4a04532c01000be42bc42df32dd32be41bc41df31dd31bf40bd40de30dc30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1402081063800900c00200c26ca3215554732c6212652e529069aa598e510531962928134515029aa4185554430
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (282+((h/3+packedAt s2K3 (270+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x83ffffffffffffe07fffc0ffffffffff1e3fff
  | 1 => 0xfc1ffc0fc0fc1fff8783ff0fe0f83c1fe9ce93
  | 3 => 0xffe0fff000ffe0fff803fff0ff003fe0f1f31c
  | 4 => 0xffffff0000fffffc0000ffffc000fe03e0
  | 5 => 0xffff0000000000ffffffffff00000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xa00004820020000011048011010a0508021425
  | 1 => 0x94648649548b46582a1550a68d0a85668ca92
  | 3 => 0x10ca9121a69285aaa84266a0ba4132c2b16318
  | 4 => 0x5a94e249341ad6f34ce83488dce5a084fc03c0
  | 5 => 0x6318c38e38e318dc7773b8cc10860318dfbc00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaee88aaaaaa88eeaaee88aaaaaa88eeaaee88aaaaaa88eeaaee88aaaaaa88eeaaee88aaaaaa88eeaaee88aaaaaa88eeaaee88aaaaaa88eeaaee88aaaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37035
namespace PEqualNP.Outside.L_meta_37035
open PEqualNP.Outside.L_meta_37035.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa006288e30000a5a480600bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x403040008ea98852c525065ca5205554430
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
  | 3 => packedAt s3K3 (112+((h/1+packedAt s3K3 (108+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 2 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 1 => 0x10891048252442502a11214921422528a22486
  | 2 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37035
namespace PEqualNP.Outside.L_meta_37035
open PEqualNP.Outside.L_meta_37035.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x2587511f35a1890584f20e0008a83437c000f516d468000000cc2620007a82837a6d546a302960293d1234822b8001c0000738001043969ec3922f0884b8d80c23ee5106b8320d876c5f0640000c0268c61fa77000000000a4d388941c424cc61881f43440c01248044034169440504328002026d0e20fc41c4fc0000048c54887a010340880007416a8d8079b634c3bc6680010484cdc0563585913c16822455c3b98b43c7e4000001ec000002611e4000a1276156815089c922c94d3997f298478fb2681f06792a1c300045c0008e0002fc000aa114500ff8000007600012f37e0011f0b200025c0026c50e058000751da4754b27d0009bc05800000000c082906e00028a2a31e2140006a0b4a10a184a12209000000498254980ba264908000000005c03b1d2438001350003347ac6f0130965350906e1d63ec0002c0460005088f00074077249000000dd8331b80000d88900a0414513a4342b49625703a969392561b2311019e049c001460e10cc2cc0028538a5711a96700099400038506970e985f1ca248bf1a73ca54c8193633e5886984008a5390d9864da2812c24d0006e42a95d20ca2d170d81e64ec1c9b300018cd424821c0bcdb8bd0000011d0000000000017121a0d42b800000644002903ea514000092b4001129ef30a2d0000040007c12208c522998ba2470f21311c99d1709b8000001381bc6b000240000000000008b00007c04e000000004420013a05819e840998481e8000e400621097cb605c194001190000000403003004040300000004004090100000008000000280200007000130000a00c03030010180200402004010340000400048050000502c080080d02c0301011020010501f000020080203804004000081500002068060200000006004030000001002004000000300006034030100104c04064140040001c1403c04000070001500405000010140201002008030080000401040020b80000013010000080402004018000100702001004030040b0000200c1a00c0001408040010380201c1900801008020080904002018160001200002024040000500400000000081e01c05028020440201404000000080003000000010140a08406004000040100000008020540402802004020040900003010060a400bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x1da0000000000026a5c8001d4000000d2019000184aa1980f427c00243000000001504d296518a0618679c7f0421aa49c38000000000001874e081d288870780000a8003260009c00000066d3e173000000de1af42c210908000002a40012d35c104639cf504200001ab3be7a40000045a4293211b1bea540027f32c1fd2280201a8303e9d93bc8a4738b61fe555000360bc0a8a886b41e3dc860a4362338c00000006080028604a2a0002235124a8238a700019cbe1c1470000000f9312000ff00032e000d90002ec000000000000b5312084566a53c81f38e180eb1ec0002ec0000343e9d400000000a043f17d2ac1b4348710007189c9614ce38c0016b344400000a33c6071111a1000234189d5028730fa007000260441ee52496cb30001ba2dcc7000000000931e8000000fea26022001471844bc26c0020a07a3980013733800000000000148d285d0002f00000c2688340003e3e20012ea092560e9479922263a08e1f81205e08c17b000000af24b00093c0000024a00000000000264248d0000790001463e6000072192f256cd021500032c00000180278001ca32a0002196a32858c82911252560b70e900042c000000b6928d500039a0000000042826845909478164b29c2102808000f127851c0004e0406e80000029e000588d41b6020fe23f0000b88a0532940fc9f08613a000001751820003d800250488920001902b0780543e4000000735008ed1995900294000000000380002774080000b9dd000000b79833ae8903c0003148dcf0a7e0a0001140a23c40ac9e9992903490ea882c0368af8462043901d8ec3f62e41325242e7e92a80044e4688c80003c298581ed528640bd1774d600062a184c65254b8003a2324000003cc2bd3018d47a00052821106000d180
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2310c355518c430d5544310c35551cc03097d95300c29c644c030d5545300c27b654c0309798f54c825d63d5320cb18954c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c834e6294f20c795153c831d5454f208f99053c823d6414f20cb55342c82cd6310b20cb55232c82ac644cb20cb55132c834e534cb20ab19121c823e64d4e208f593538823e6414e208f59053882766114e209d584538832e5488620cb95021882e96008620cb953208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65d0920b358c424826c654c920ab19132482e8604c9208f990514823d64145209798c514825d63145209b99721482ac6448520ab992204826e62d50209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209b98853082766114c209d584530823e64948208f592520825e63948209758e520823f64544208f191510826d6588420ba580210823e64940208f592500826f65480209ed95200825e63d53109758f54c426f62553109b18954c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c426e62d52109b58b548425f63552109718d548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da5805244354538c5109d195314436852881109e195204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520435553c40109e596100436952840109dd95100435553440109ed9510043695244010
  | 1 => 0xc66f62551319b189544c67b60551319e181544c65e65d0d31b3588434c63e64149318f590524c69c644c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f59253886cd6310a21ab191328863f64542218f191508865f63542219718d508863e64951219bd89544863e65151218f992534863d6494d219b58a534863f6454d218f191534867b6054d219e181534872c54885219798f540865d63d50219e983540867960d50218f596540872c62550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c21cb553420866d6510821b358c420866d658c821cb55232086ac644c821cb551320874e534c8219bd9521086ac64484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b4254021da109500876a3254021da4c9500876b2154021da485500869d6310b409798e51d025d6394740ab18941d02ad6210e409798e529025d6394a40d398e529034d6394a40cb90e529032c4394a40cb94b429032e5250a40a798e419032e5290640cb948419032e52d02409b988535026d6214d40d3988535034d6214d408f997435031c53d0d40c714d435031c53909408f994425029d6310940c714c425023e65d0540c714f415031c5350540ab189415031c5390140ab98a405023d6590c40ab588431023f65508409bd89511026c62544408f596411029e63904408fd95401029c63500409ed95401026e62153309b58854cc23f6454b308f19152cc23e64947308f59251cc26e62d52309b58b548c2cd6210e308f992528c23d6494a30a7191328c23f64546308f191518c26f62546309b189518c29e648c6308f992544c25f63551308f994544c25e65cc530c7153314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30b3588430c32e5494830cb552520c32e5454830cb551520c31d54cc830a7191320c31d544c830d3949320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3574354430d510d510c3573254430d54c9510c25d658c430a799
  | 2 => 0x410c354362011b2664f081900054400000000490001de0461f10819b40424482a0011a000ea18d3d8578ae0511de000000a22b46a81b96305c38c399c50000289b9a40002a425018228000001d11023a41c0792ba470071231f81d49d9590002940003f1000000605a0fe5a48581e23a460ce1390007c8d68f2000001069960000007f80000000000000000820508000000000000000c814809740004442f1be00071c7b12712e5e00000015c40c228002e28507c94c0ae448989b721e0002f976012000e68da00000000000000688a90bd2a83ac24122296698a010831c53885000076000931500005e8b100000070000000268228569a32e06d80e86621253c5b0621dc6088c9253ec2dc000000005f0e30003fc7d04d99723457cb400012800802010070000000401010050380004c0200c000940a0000000403028000440000003000030000d0000404406004060000004000008010000000001018010040b01001024030040300c0400002004010080000c0000400018050200001c01014010440101c0000801004270040100006000010100100400000000040200007028050040000c0100c000040b0040102808014040000a0100000400000060000402400000020200100c0000000000090400000c0a01c03024000000700c0001c030040f00c0204408014100301000000010000280601c010080300405058050226f62547439b18951d0e6e62943439b58a50d0e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5e63947429758e51d0a5f63543429718d50d0aad6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7661d53329d58754cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548ca3f64546328f191518ca3e64942328f592508ca3e64951328f994544cb1d6315132cb588544cb1c5490d3297195434cb2c5490932e390e424ca6c6550932e350d424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320caad6210f419b98a50d066d62943419b98a539066d6294e41d398a539074d6294e41c794f439071e5350e41c794e429069d6310a41c794c429071e53d06418f99443506ad6210d419798c525065d6314941d398c525074d6314941cb90c525072c43149418f997425072c52d0941cb149425069e6390541cb14a415063f6550c418f596421069d63108418fd9541106ac62504419dd95411065f63540419718d501066e62d53319b58b54cc71c63553319b98854cc66d6215331c755343cc6cd6210f31cb95252cc72d5494b31cb95152cc72d5454b31c755332cc69c644cb31c755132cc74e524cb31c7953318
  | 3 => 0xe7000392000001bf0006ac000560005ec00000190000dc00037a5b0961980c0214001020443f8b294d0004a43b0963e20a8280dc068704ed8fb00671000195000000d7000000000000000001d03d8070002e46e80026c00050000000000299790001c8000003f6000701842506bcd41900000e4c894231216cff910098560130a80007210319d1fa2d0000820003284c138000648671480004bcf18001ea528000421324b4a388806a5587890e3c00000007d0000006004127a0000018b000000001070000f8000000001bc1b000000000998003f4768001f522c10ce98de2261a89f064000510001d50002746d80012a0000000027e0005a8aa3fa7f0dd8a7146430d907822a050001860001c000000000000e789c0000010b8c23e60010986d2540010a8003ac0441280000020c0000041e5fcec13a3407b9048af000000c9a1808c4b9070653c43c0a482113c5b81987a2b6230001212de1b8340103be27cb501b1da37cc51e83624c0628b10b80bd0d0280a847ca99e63ae45ce58e53da7e0001e5000000001e70000000000001a3186b00018e67c00071000000de000058774f59044065183180026a0005d00004e7dcc0800000000001a10005c8470d70b06e80017d000000958490000001d204422330690b011e00053000000000000000000000000021a30c0001f000000560002ae000040b83988580000009e350168001cc164a08000000008f0172aa50cf813217834c000000005f8000f70c2070ec80000032ce90000000589e000366770b5800360400000243d2008830bf00059cc01d0026148da8f30007a80a8e10005dc001450000c0f79752da0ac73a191566143b8b20d2390688ea33c000d380b4143e8d28f8000324000002362f800000096240149662e66d023a070405845d80031000000000088000000000002480780037206852001080000000002c02247a1ac06433c0004d4160006c08b134210001c31827e4e103c4242cc000e8328000000000ce000000001c41f80203d30e668000c4000630c7800000000029a92c8340270551d83340005d3060004380000048000031418000000930d6728091e
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x24030550f1804530cd00e0000006070010121000085d540a0160022c0001000861818358d6215132a1ae529a8720d0d731494250707318a520a83435c86355331838ecaa26598d0d7318954086163b2a899043525cc4254021a50e8992a010d28744855008686b9ca4a14818398e5290640a1ae429a86a060c53189415030629cc520281435c86355030838ecaa264185457210d510c28a3a264a886185991518c430c28c8a8a601850d7318954c82163b2a8996418a9516008620
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x688080d8798c529054180d8798e529064080d8714c625054080d8714e6290140
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
  | 4 => packedAt s4K4 (22272+((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0ff87f87fe1fffe07d19f3f3
  | 1 => 0xfe1fffc1f87ffff07f87f87fe1c0fffee63c9f
  | 2 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa402088850102002900980920252212808d131
  | 1 => 0x884110480a400502882082420844a50622486
  | 2 => 0x144aa290354906a58444d50b540a950b054b18
  | 3 => 0x5954c425240d4b394d50440d992c0613b00ec0
  | 5 => 0x61988739c67193ce7667664110301863dfb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37035
namespace PEqualNP.Outside.L_meta_37035
open PEqualNP.Outside.L_meta_37035.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x40b0b8952082160000c800014018009912a1a1d2060094a832038fa700700945aacf1214007884244d0c2674da8008c5890882820122001c20c11ccff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x38157011145a00191b21561f0000496955000064672f003400004a04006f006e304c4f3e396c71455f545b121d104d5e230048003f00006a520000070a40240c0d5808005c4702662b0000000000510000010e32002d18311e3d3a00000028722a6300570f330000001c0900615d0543170050730b3b006d3c6813224e602e4400362520163700410026354603594262744b296500272c531a066b008500800003000002850581808080010480010780118385808304000101830681808004010403e750c43bb28887755110ebca7a15754f42bb28e857551d0a7ca9994f55332bb28e657551cca7aa920d794e41aea9c836f52506d8a4a0ebd4941d629283b7515067ca820d794c41aea98839f41cc73a8398cf952319eaa4635d538c76a8318dbd4931b629263b5414c79ea498f314931eba8a639f414c7ac8298e750531eaa0a6395414c67ca818cf55031af29863b541c87aa6390cf952219eaa4435e53886baa710cf950219eaa0435e53086baa610ed50421ea988437a50086f2a010db94a40b6a94815f53502b8a6a05794c40aea98816e52102daa4205d94440baa88816e528c2daa5184fd51309e2a2613e540c27aa8185b94830b6a906176510c2eaa2186bd0720d6a0e41cf31c839a63905b54a209faa2413c54482bea6905714d20bba8a4174514835ea8906b15120e7a9a41cc53483cea2907914520d7a0a41ad414839e6290734c520f5a82416e520827ca9884f55310af29e215d53c436a8388754c710b7294216d52843d241086d50510ea98a21e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x60068e88252c710812b80a9ea2629602410020600000c00068198a1c550d5110f245250531a5592414c6c46250531e1d89414c7846250531e1d49414c7845250531c554d4108715544c421cc505500875131540219558453502356115130e150531c83245414520d114c514822c6550520931953148385414c520c554d41c4315544c710e850520443c13148110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xa0c00a0cebb128298c8676d49414c6823aa8298a4181195414c520
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 4 => packedAt s5K4 (3471+((h/39+packedAt s5K4 (3159+(h % 39)*8) 8) % 155)*8) 8
  | 3 => packedAt s5K3 (952+((h/8+packedAt s5K3 (912+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83ffff07fffe1f0787fe1fffc3fff81e19f3f3
  | 1 => 0xfc3e1ff87c3ffff8070fe3c1fc783fff164c9f
  | 2 => 0xffc01fff803fe1fff80ffc01ff803fe1e78f1c
  | 3 => 0x1fffffc001fffff00001ffffc001f80fe0
  | 4 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x88040110080020008012044440888844009131
  | 1 => 0x110932212255112843852288a4511299124486
  | 2 => 0x2894445218a80253880a48154902a544658b18
  | 3 => 0x72a99885520d559d55a10221b2670189b80ec0
  | 4 => 0x433110e6633199e666cd933820440611df6000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfaeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37035
namespace PEqualNP.Outside.L_meta_37035
open PEqualNP.Outside.L_meta_37035.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d223179e0001c0000d4d1f00018a2128d6001e045395c0002840183b06e21a3636915994c845bb0601d322a0022d289c91d6640b004a60e172639e8052181810106040000e0c4800c087002640180017fd5005fe54017f55005fc5401ffd4c01fe53007f54c07fc53017fd0c05fe43017f50c05fc4301ffd4801fe52007f54807fc52017fd0805fe42017f50805fc42007fcc801fe32007f4c801fc3201ffd4403fe51007f54403fc51017fd0405bf4100ff90405fd41006f50403fc41007fcc403fe31007f4c403fc31007fc8403fe21007f48403fc2101ffd4001fe50007f54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x804004ff8c020027fa6010013fc3008009ff9004004fbc8020027fc4010013fa2008009fe9004004fb4802003ff24010013ff1008009fe0804004ffd9610025fecb08013fe65840077f32c2004ff59610005facb08013fc65840097e32c2004ffd9210025fec908013fe64840057f3242004ff5921004dfac908013fc64840097e3242009ffd521004ffca908027fd5484013fe2a42004ffd8e10025fec708013fe63840117f31c2004ff58e10005fac708013fc63840097e31c200affd4e10007fca708003fd5384015fe29c2009ffd0e1004ffc8708027fd4384013fe21c2004ffd8a10025fec508013fe628400f7f3142004ff58a10005fac508013fc62840097e314200affd4a10007fca508003fd5284015fe2942009ffd0a1004ffc8508027fd4284013fe2142000ffcca10007fc6508003fd3284001fe1942001bf5861000ffea308007fe5184003fea8c2001ff1461000ffe8308007bf4184003ff20c2001ff5061000f7a8308007fc4184003ff98c2001ff8c61000ffa6308007fc3184003ff90c2001ff8861000ffa4308007fc21840097f3042004ffd4210027fca108013fd5084009fe2842004ffd0210027fc8108013fd4084009fe2042004ffcc210027fc6108013fd3084009fe1842004ffc8210027fc4108013fa2084009fe9042000fe48210027f84108013ff1084009fb8842001fec4210027f82108013f81084001ffb2a2000bfd9510006feca880027f654400dff32a2003bf99510007faca88002fd654400dfe32a2003bf19510006f8ca8800e7c654400bffb222005bfd911002ffcc88800afe644400bfeb222005bf5911002ff8c88800afc644400bffaa22005ff9511002ffaa888017fc5444001ffb1a2000bfd8d10007fcc688022fe6344001feb1a2000bf58d10007f8c688022fc634400dffa9a2000ff94d10007faa68801bfc534400bffa1a2005ff90d1002ffa8688017fc4344001ffb122000bfd8910007fcc48801efe6244001feb122000bf58910007f8c48801efc624400dffa922000ff94910007faa48801bfc524400bffa122005ff9091002ffa8488017fc4244001ff9922000ff8c910007fa6488003fc32440097fb0a2001ffd451000ffca288007fd5144003fe28a2001ffd051000f7e8288007fe4144003fb20a2001ff5051000f7a8288017f54144001daa0a2001ff1051000ffe6288007fe3144003fb18a2001ff4c510007ea6288007fc3144003ff90a2001ff8851000ffa4288007fc21440037fb022006ffd4110027fca088003fd5044009fe2822005ffd0110027fc8088017fd4044009fe2022000ffcc110027fc6088003fd3044009fe1822000ffc8110027fc4088003fa2044001fe9022000fe48110027f84088007ff1044003fd8822004ff84110027ec2088013fc1044009fa0822001fe04110
  | 1 => 0x7fe5188001fea8c4011ff14620097fe831004bbf4188023ff20c4012ff506200077a8310047fc4188001ff98c4011ff8c620007fa6310047fc318800fff90c4011ff88620007fa431001ffc21880097f3044004ffd4220027fca110013fd5088009fe2844004ffd0220027fc8110013fd4088009fe2044004ffcc220027fc6110013fd3088009fe1844004ffc8220027de411001ffb2088009ff8844004ff04220007feca90002ff6548021ff32a4003bf99520007faca90002fd6548021fe32a4003bf1952007ffec89003eff6448001dfb224000afd912007ffcc89000afe644801ffeb22400fbf5912007ff8c89000afc644801fde3224002af1912007ffea89003ffe544801ffeaa2400fff15120007fec690002ff6348001ff31a4008bf98d20007fac690002fd6348001fe31a4008bf18d20087fea690003fe5348001fea9a4010ff14d2007ffe869003ffe434801ffea1a400fff10d20087fea490043ef524800fff2924000ff5492003ff8a490043ec524801fffa124007ff9092007fdc849003ffd424801ff6a124007ff10920007fe649001ffe3248001f71924000ff4c920007da649001ffc3248001ffb0a4000bfd8520077fcc290006fe6148001feb0a400eff1852000df8c290043ff514801dff28a4000ff54520077f8a29003fff414801fdfa0a400eff9052007ffa8290003bd414801dfe20a4000ffcc520077fc6290003fd314801dfe18a4007ffc8520007de429003bfe2148001fe90a4000fb4852003ff84290043ff5048009ff2824000ff54120027f8a09003fff4048009ff202400fff50120027f88090003ff3048009ff1824000ff4c120027f8609001fff204800ffd9024004ff88120027dc409003bff1048009fe0824004ffd9420025feca10013fe65080077f3284004ff59420005faca10013fc65080097e3284004ffd9020025fec810013fe64080057f3204004ff59020065fac810013fc64080097e320400cffd5020067fca810033fd5408019fe2a04004ffd8c20025fec610013fe63080117f3184004ff58c20005fac610013fc63080097e318400dffd4c20007fca610003fd530801bfe298400cffd0c20067fc8610033fd4308019fe2184007bf9882003ffea41001ffe520800ffea904007ff1482003ffe841001ffe420800ffea104007ff1082003ffe641001ffe320800ffe9904007ff0c820027fec210013fe61080037f3084004ff58420005fac210013fc61080097e308400dffd442005ffca210003fd5108017fe288400cffd04200677e821002ffe4108019fea084000ef5042005ff88210003ff3108017ff1884000ff4c42005ff8621001fff210800fff1084007ff4842003ff84210012fe6008009ffa804004ff94020027faa010013fc5008009ffa004004ff90020027fa8010013fc4008009ff9
  | 2 => 0x30005dac418013fc620c033ffa906000ff94830007faa418067fc520c031ffa106018ff908300c7fa8418063fc420c011ff9906008ff8c830047fa6418023fc320c009ffb086004ff9843000dfcc218013f6610c0037b3086004ff58430005fac218013f5610c0017ab086004ff18430025f8c218067ff510c02fff2886000ff544300bff8a218063ff410c031dfa086017ff904300c7fa8218003bd410c02ffe2086008ffcc430047fc6218023fd310c011fe1886000ffc84300bffc4218003fd210c02ffe1086004bf98030027fea018013fe500c009fea806004ff14030027fe8018013fe400c009fea006004ff10030027fe6018013df300c009ff1806004fe8c030027fa6018013dd300c011fc9806004ffc4030027f8201801fff65c800f7fb2e4007ff9972001dfccb9001f7e65c80073f32e4007ff59720005facb9001f7d65c80013eb2e4007ff1972003df8cb9001fff64c800f7fb264007ff99320015fcc99001ffd64c802b7eb264007ff1932003df8c990057ff54c802bff2a64015ff553200aff8a99001fff63c800f7fb1e4007ff98f20045fcc79001ffd63c80017eb1e4007ff18f2003df8c79005bff53c8001ff29e4000ff54f200b7f8a790057ff43c802bff21e4015ff50f200aff8879001fff52c802df7a964007ff94b2003ffaa59001ffc52c800ff62964007ffd0b2003ffc859001fee42c800ffea164015fb50b2003ff8859001fff32c800fff1964007fb8cb2003ffa6590003ed32c800ffe1964007ffd872003ffcc390006fe61c800ffeb0e4000bf5872003ff8c390006fc61c802dffa8e4014ff94720007faa390053fc51c802bffa0e4015efd07200a7fc8390057fd41c8001dea0e4014ff10720007fe6390053fe31c8001fe98e4014ff0c72003ffe439001fef21c800fff10e4007ff48720007da439001ffc21c802dffa864004ff94320007faa190013fc50c802bffa064004ff903200affa8190013fc40c8001ff9864004ff8c320007fa6190013fc30c8029ff8864004ff04320027fecb10012ff6588009ff32c4003bf99620026fccb1000e7e6588009feb2c4000bf59620026facb100027d6588009fe32c4004bf19620027fec910012ff6488009ff3244002bf99220027fac91004afd6488009fe3244004bf19220097fea91004bfe5488025feaa44012ff15220027fec710012ff6388009ff31c4008bf98e20027fac710002fd6388009fe31c4004bf18e2009ffea710003fe5388001fea9c4013ff14e20097fe871004bfe4388025fea1c4012ff10e2007dfac51004fff528800fff2944000ff54a2003ff8a51004bff428800fff2144012ff50a2003ff88510003ff328800fff1944000ff4ca2003ff86510013ff6188009ff30c4001bf98620027fac310002fd6188009fe30c4004bf1862009ffea31004
  | 3 => 0xe32c6004bf19630027fec918012ff648c009ff3246002bf99230027fac91807afd648c009fe3246004bf192300f7fea91807bfe548c03dfeaa4601eff152300ddfac71807fff538c011ff29c6000ff54e30047f8a71807bff438c011ff21c601eff50e30047f88718013ff628c009ff3146007bf98a30027fac518002fd628c009fe314601fffd4a30007fca518003fd528c03ffe294601effd0a300f7fc851807bfd428c03dfe2146008ffcca30007fc6518003fd328c011fe1946004ffd8630027fcc318006fe618c009feb0c6000bf58630027f8c318012fc618c03fffa8c601dff94630007faa318077fc518c03dffa0c601eefd06300effc831807bfd418c001dea0c601dff10630047fe6318077fe318c001fe98c6008ff0c630007fe4318077fe218c001fe90c601dff08630025fcc118013ff508c009ff2846004ff54230027f8a118013ff408c009ff2046004ff50230027f88118013ff308c009ef9846008fecc230027fe2118013fc108c001ffb2a6000bfd9530006feca980027f654c039ff32a6003bf99530007faca98002fd654c039fe32a6003bf19530006f8ca9800e7c654c037ffb22601bbfd91300077ec898002bf644c037ff3226002bf991300dffac89806efd644c037fe3226002bf191300df78c89800abc644c037ffaa2601bff951300dffaa89806ffc544c039ffa9a6008ff94d30007faa698023fc534c037ffa1a6008ff90d300dfbc869806ffd434c037eea1a6008ff10d30007fec498002ff624c001ff3126000ff58930007f8c49801efc624c039ffa926000ff94930007faa498073fc524c037ffa12601bff909300dffa849806ffc424c011ff9926000ff8c930007fa6498023fc324c001ffb0a6000bfd85300d7fcc298006fe614c001feb0a601aff1853000df8c298073ff514c035ff28a6000ff545300d7f8a29806fff414c037dfa0a601aff905300dffa8298003bd414c035fe20a6008ffcc530007be629806bfe314c001fe98a6000f74c530047f86298003ff214c035ff10a6000ff485300d7f84298073ff504c009ff2826000ff54130027f8a09806fff404c009ff202601bff50130027f88098023ff304c011fd9826004ff8c130027bc609806bff104c009fe0826004ffd9430025feca18013fe650c0077f3286004df9943001cfcca18013fd650c0017eb286004df59430004faca18013fc650c0097e3286004ffd9030025fec818013fe640c0057f3206004ef990300157cc818013fd640c0317eb206004ef590300057ac818013fc640c0097e3206018ffd50300c7fca818063fd540c031fe2a06008bf98c30047fea618023fe530c011fea986008ff14c30047fe8618023fe430c011fea186008ff10c30027fec418013fe620c00f7f3106004fb98830005dcc418013fd620c0017eb106004fb588
  | 4 => 0x13fe61940037f30ca004ff58650005fac328013fc61940097e30ca003ffd465001ffca3280977e5194007fea8ca003ff1465001ef8a32809bff419404ddfa0ca025ff90650137fa8328003bd419404bfe20ca000ffcc65012ffc6328003fd319404bfe18ca000ffc865012ffc4328003fd219404bfe10ca004bf98250027fea1280137f5094007fda84a004ff14250027f0a128013ff4094009ff204a004ff50250027f88128013ff1094009fe084a004bfd9550127fec8a8092ff6454049ff322a002bf99150127fac8a8092fd6454049fe322a002bf1915001ffea8a800f7f5454007ff2a2a003ff55150126faa8a800ffc5454001ffb1aa000bfd8d50007fcc6a8003fd6354001fe31aa008bf18d5001ffea6a800f7f5354007ff29aa003ff54d50006faa6a800ffc5354049ffa1aa024ff90d50127fa86a8093fc4354001ffb12a000bfd8950007fcc4a8003fd6254001fe312a007bf1895001ffea4a800ffe5254001bf292a003ff5495001ff8a4a800f7c5254049ffa12a024ff90950127fa84a8093fc4254001ff992a000ff8c950007fa64a8003fc3254001ffb0aa000bfd855011ffcc2a8006fe6154001feb0aa023ff1855000df8c2a800fff5154007bfa8aa003ff9455001ffaa2a80037d5154007fe28aa024ffd05501277e82a808ffe4154049fea0aa000ef5055011ff882a8003ff3154047ff18aa000ff4c55011ff862a8003ff2154047ff10aa000ff4855011ff842a800eff6054007ffa82a003fed4150027fca0a80137e5054009fe282a004df1415001ff0a0a8093ff4054009ff202a024ff50150027f880a808fff1054009fe082a008ffd9730045fecb98023fe65cc0077f32e6008ff59730005facb98023fc65cc0117e32e6008ffd9330045fec998023fe64cc0057f3266008ff5933010dfac998023fc64cc0117e3266021ffd533010ffca998087fd54cc043fe2a66008ffd4f30047fca798023fd53cc011fe29e6008ffd0f30047fc8798023de43cc011fea1e6021f750f30047f88798023ff62cc011ff3166007bf98b30047fac598002fd62cc011fe3166022ffd4b30007fca598003fd52cc045fe2966021ffd0b3010ffc8598087fd42cc043fe2166008ffccb30047fc6598023fd32cc011fe1966008ffd8730047fcc398006fe61cc011feb0e6000bf58730047f8c398006fc61cc045ffa8e6020ff94730007faa398083fc51cc043ffa0e6021efd0730107fc8398087fd41cc001dea0e6020ff10730047fe6398023df31cc011ff18e6008ff4c730007ba6398023fc31cc001ff90e6020ff88730007fa4398083fc21cc045ffa866004ff94330007faa198013fc50cc043ffa066004ff9033010ffa8198013fc40cc041ff8866004ff04330027fecb18012ff658c009ff32c6003bf99630027facb18002fd658c009f
  | 5 => 0x9721005facb9081ffc65c840f7e32e4207ffd932103dfec99081ffe64c84057f3264207ff5932114dfac99081ffc64c840f7e3264229ffd532114ffca9908a7fd54c8453fe2a64207ffd8f2103dfec79081ffe63c84117f31e4207ff58f21005fac79081ffc63c840f7e31e422affd4f21007fca790803fd53c8455fe29e4229ffd0f2114ffc87908a7fd43c8453fe21e4201bf98b2103ffea59081ffe52c840ffea964207ff14b2103ffe859081ffe42c840ffea164207ff10b2103ffe659081ffe32c840ffe9964207ff0cb2100dfac390807ff51c8403ff28e4201ff5472100ff8a390807ff41c8403dfa0e4201ff9072100ffa8390807bd41c8403fe20e4201ffcc72100ffc6390807fd31c8403fe18e4201ff8872100fdc4390807f621c8403fe10e4201fb0872103ffec19081ffe60c84097f3064207ff58321005fac19081ffc60c8455ffa86422aff1432114ffe81908a7fe40c8453fea064229ff1032100ffe2190807fc10c8401ffb2a4200bfd9521006feca908027f6548451ff32a4203bf99521007faca90802fd6548451fe32a4203bf19521006f8ca9080e7c654844fffb224227bfd912113ffcc89080afe644844ffeb224227bf5912113ff8c89080afc644844fffaa24227ff9512113ffaa89089ffc5448401ffb1a4200bfd8d21007fcc690822fe6348401feb1a4200bf58d21007f8c690822fc6348451ffa9a4200ff94d21007faa6908a3fc534844fffa1a4227ff90d2113ffa869089ffc43484037fb124228ffd492103ffca490803fd524840ffe2924227ffd092103ffc849089ffd424840ffe2124200ffcc92103ffc6490803fd324840ffe1924201bfd852100ffea290807fe5148403fea8a4201ff1452100ffe8290807bf4148403ff20a4201ff5052100f7a8290807fc4148403ff98a4201ff8c52100ffa6290807fc3148403ff90a4207fdc852100ffc4290807ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484097e3024228ffd4121147f8a09089fff404844fff2024227ff5012113ff88090807ff1048403fe0824203bf59650027fec928012ff6494009ff324a002bf99250027fac92809afd6494009fe324a004bf1925001ffea92800ffe5494007feaa4a003ff15250027fec728013fe63940117f31ca004ff58e50005fac728013fc6394007ffa9ca003ff94e50006fca72800ffd5394007fe29ca003df14e50137fe872809bfe439404dfea1ca026ff10e50027fec528013fe629400f7f314a004fb98a50005dcc528013fd62940017eb14a004fb58a50005dac528013fc6294007ffa94a003dfd4a5001ffca52800ffd5294001bea94a003ff14a50137fe852809bfe429404dfea14a026ff10a50007fe6528003fe3294001fe994a000ff0ca50027fec328
  | 6 => 0x1dfb2a822fef995410077acaa08bfbc6550401dfb1a8200ef98d410077ac6a0803bc635045fdfa9a8200ef94d410077aa6a08bfbc5350401dfb128200ef989410077ac4a0803bc625045fdfa928200ef949410077aa4a08bfbc5250401df9928200ef8c9410077a64a0803bc3250403dfb0a8201afd85410176ec2a0807bf5150403df28a8201ef5454100f78a2a0807be3150403de18a8201ef8854100f7842a0803bf6050401df3028200ef5814100778c0a08bfbf505045fde2828201efc414100f6e20a0807bc1050411ffb2e6208bfd9731047fccb9880efe65cc411bf32e62039f99731047facb98802fd65cc411beb2e62009f59731047f8cb98822fc65cc411ffb266208bfd9331047fcc99880afe64cc411feb26622dbf59331047f8c998822fc64cc45bffaa6622dff9533116ffaa9988b7fc54cc4037f31e6208ffd4f31177bea798823fe53cc411fea9e6208ff14f31047b8a798823ff43cc411ff21e6208ff50f31047f88798823ff62cc411ff3166207bf98b31047fac598802fd62cc411fe316622effd4b31007fca598803fd52cc45dfe296622dffd0b3116ffc85988b7fd42cc45bfe2166208ffccb31047be6598823fe32cc411fe9966200f74cb31047f86598806fd61cc403ffa8e6201ff9473100ffaa398807fc51cc403ffa0e6201efd073100ffc8398807fd41cc403dea0e6201ff1073100ffc6398807de31cc403fb18e6201ff0c73100fb86398807fe21cc403fe10e6208ffd8331047fcc198812fe60cc411feb066200bf58331047f8c1988bbff50cc45dfe286622dffd033116ffc81988b7fd40cc45bfe2066201ffc433100ff82198803ff654c4017fb2a622cff9953101dfcca98803fd654c4017eb2a622cff1953101df8ca988afff644c4577fb22622bff99131015fcc8988affd644c4577eb22622bff19131015f8c8988afff544c457ff2a2622bff5513115ff8a898806ff634c459ffa9a622cf7d4d31047fca698803fd534c411fe29a622cf714d3115ffe8698823fe434c457fea1a6208ff10d31007fec498802ff624c401ff3126200ff58931007f8c49881efc624c459ffa926200ff94931007faa4988b3fc524c457ffa12622bff9093115ffa84988affc424c411ff9926200f7cc931007fc6498803fd324c401ee9926208ff0c93100dfec298807ff514c403ff28a6201ff5453100ff8a298807ff414c403dfa0a6201ff9053100ffa8298807bd414c403fe20a6201ffcc531047ee6298807fe314c403ef18a6201ff0c53100fb86298807f4314c403ff10a6201ff08531007fec098802ff604c401ff3026200ff58131007f8c098812fc604c459ffa82622cff1413115ffe80988affe404c457fea02622bff1013100ffe2098807f7104c403fe0826207ffd972103dfecb9081ffe65c84077f32e4207ff5
  | 7 => 0x9900afc644c86bffaa26435ff951321affaa8990d7fc544c86dffa9a6408ff94d32007faa699023fc534c86bffa1a6408ff90d321affa8699023fc434c86dffa926407ff94932007faa49901ffc524c86bffa126407ff909321affa849901ffc424c811ff9926408fbcc93203ffc649901fde324c801ffb0a6400bfd85321a7fcc299006fe614c801feb0a6434ff1853200df8c2990dbff514c869ff28a6434ff145321affe82990d7bf414c869ff20a6435ff505321a7f882990d3fe314c811fe18a6434ff8853203ff84299003ff604c8017fb026400ff98132007fac099003fc604c8097e3026436ffd41321b7f8a0990d7ff404c86bff2026435ff501321aff880990d3ff104c869fe0826407ffd943203dfeca1901ffe650c8077f3286407df9943201cfcca1901ffd650c8017eb286407df59432004faca1901ffc650c80f7e3286407ffd903203dfec81901ffe640c8057f3206407ff59032195fac81901ffc640c80f7e3206432ffd5032197fca8190cbfd540c865fe2a06408bf98c32047fea619023fe530c811fea986408ff14c32047fe8619023fe430c811fea186408ff10c3203dfcc41901fff520c80fff2906407ff5483203ff8a41901fff420c80fff2106407ff5083203ff8841901fff320c80fef9906407ff8c83203fdc641901ffd320c80fee9906408fb4c83203ffec21901ffe610c8037f3086407ff58432005fac21901ffc610c8037e3086433ffd443218ffca2190c7fc510c865ffa086432efd043218ffc82190cbfd410c863fe2086408ff8c432047f8621901ffe210c80ffe1086407ffd803203ffcc019012fe600c80ffeb006400bf5803203ff8c0190cfff500c867fe2806432ffd0032197fc80190cbfd400c865fe2006431ffc403218ff82019006ff6554461ffb22a230bfd9151187fcc8a880afe6454461feb22a230bf59151187f8c8a880afc6454407ffaa2a203ff9515101ffaa8a880ffc5454401ffb1aa200bfd8d51007fcc6a8803fd6354401fe31aa208bf18d5101ffea6a880ffe5354401bf29aa203ff54d5101ff8a6a880f7c5354461ffa1aa230ff90d51187fa86a88c3fc4354401ffb12a200bfd8951007fcc4a8803fd6254401fe312a207bf1895101ffea4a880f7f5254407ff292a203ff54951006faa4a880ffc5254461ffa12a230ff90951187fa84a88c3fc4254401ff992a200ff8c951007fa64a8803fc32544037fb0aa201ffd455101feea2a8807fe5154403bf28aa201ff1455100ef8a2a8807f45154403ffa0aa201efd055100ffc82a8807fd4154403fe20aa201ff8c55100ff862a8807fe2154403fe10aa200ffd8151005fec0a8803fe6054401feb02a200ff18151025f8c0a880fff5054407bfa82a203ff14151187fe80a88c3fe4054461fea02a230ff1015100ffe20a8807fc105440
  | 8 => 0xfd4d5201ffca6a900ffd5354801bea9aa403ff14d521f7fe86a90fbfe435487dfea1aa43eff10d5201dfec4a900fff5254807f7a92a407ff9495203efca4a901ffc525480fbe292a403fb149521f7fe84a901ffe425487dfea12a407ff10952007fec2a9002ff615487bff30aa401bf98552007fac2a90f7fc61548037e30aa403ffd455201efea2a900ffe5154807fe28aa43effd05521f77e82a90f7fe415487dfea0aa43dff105521effc62a90f7fc315487bff10aa407ff08552007fec0a9002ff6054801ff302a400ff58152007f8c0a9012fc6054807ffa82a403ff1415201ef8a0a90fbff405487dff202a43eff501521f7f880a90f7ff105487bfe082a408ffd9732045fecb99023fe65cc8077f32e6408ff59732005facb99023fc65cc8117e32e6408ffd9332045fec999023fe64cc8057f3266408ef993320157cc999023fd64cc8777eb266408ef593320057ac999023fc64cc8117e326643bffd53321dffca9990effd54cc877fe2a66408ffd4f32047fca799023fd53cc811fe29e6408ffd0f32047fc8799023fd43cc811fe21e643cffd4b3203ffca599003fd52cc80ffe296643bffd0b3203ffc85990effd42cc80ffe2166408ffd8732047fcc399006fe61cc811feb0e6400bf58732047f8c399006fc61cc879ffa8e643aff947321d7f8a3990efff41cc877dfa0e643aff907321dffa83990ebfc41cc811ff18e6408ff0c7321d7fc439901ffc21cc811ffb066408ff98332025fcc199023fd60cc8017eb066408ff183321e7fea1990f3fc50cc877ffa06643bff903321dffa81990effc40cc875ff886643aff0433203ffecb1901eff658c80fff32c6403bf9963203ffacb19002fd658c80ffe32c6407bf1963203ffec91901eff648c80fff3246402bf9923203ffac9190e2fd648c80ffe3246407bf192321c7fea9190e3fe548c871feaa46438ff152321adfac7190e7ff538c811ff29c6400ff54e32047f8a7190e3ff438c811ff21c6438ff50e32047f8871901efe628c80fffa946407ff94a3203ffaa51901ffc528c80fffa146407ff90a3203ffa851901ffc428c80fff9946407f7cca32047de651901fff618c80fff30c6401bf9863203ffac319002fd618c80ffe30c6401bf186321cffea3190dffe518c86ffe28c6438ffd06321c77e83190dffe418c871fea0c6437ff106321bffc6319023fc318c80fff10c6407ff0863203ffec11901ffe608c8097f3046407ff58232005fac11901ffc608c873ffa846439ff142321c7fe81190e3fe408c871fea046438ff102321bffe21190dffc108c801ffb2a6400bfd9532006feca990027f654c86dff32a6403bf99532007faca99002fd654c86dfe32a6403bf19532006f8ca9900e7c654c86bffb226435bfd91321affcc89900afe644c86bfeb226435bf591321aff8c8
  | 9 => 0xc11fea1ca608ff10e53047fec529823fe6294c0f7f314a608ff58a53005fac529823fc6294c07ffa94a603ff14a5301ef8a529913ff4294c89ff214a644ff50a53227f88529823ff6194c11ff30ca601bf98653047fac329802fd6194c11fe30ca601bf1865301ffea32980f7f5194c07ff28ca603ff14653227fe8329913bf4194c87ff20ca644ff5065321ff88329823fe3194c11fe18ca643ff8865321ff84329823ff6094c11ff304a604bf98253047fac129802fd6094c11fe304a603ffd425301ff8a12980f7c5094c89ffa04a644ff90253227fa8129913fc4094c87ff884a643ff04253045fecaa990bff6454c857fb22a642ff99153015fcc8a990bfd6454c857eb22a642ff19153015f8c8a980fff5454c07ff2a2a603ff5515301ff8a8a980eff6354c07ffa9aa603f7d4d53047fca6a98237e5354c11fe29aa608df14d5301fb8a6a990bff4354c11ff21aa642ff50d53047f886a9803ff6254c017fb12a600ff98953007fac4a9803fc6254c0f7e312a603ffd495301efea4a980ffc5254c85ffa12a642ff90953217fa84a990bfc4254c01ffb0aa600bfd855320ffcc2a9806fe6154c01feb0aa641ff1855300df8c2a980fff5154c07ff28aa641df9455301ff8a2a980f7c5154c85ffa0aa642efd055320ffc82a990bfd4154c83fe20aa641ff8c553047f862a9907fe2154c83fe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff18153025f8c0a980fff5054c07bfa82a603ff14153217fe80a990bfe4054c85fea02a642ff1015320ffe20a9907fc1054c077eb2ca407ffd925203dfec92901ffe64948057f324a407ff59252205fac92901ffc649480f7e324a403ffd525201ffca92900ffd5494807fe2a4a407ffd8e5203ffcc729022fe639480ffeb1ca400bf58e5203ff8c72900fff5394807ff29ca400df94e5201ffaa72900ffc5394807be29ca440ffd0e52207fc8729103fd4394881fe21ca407bf98a5203ffea52901f7f5294807f7a94a407ff14a5203fd8a52901fff429480fff214a407ff50a5203ff8852901fff619480fff30ca401bf9865203ffac329002fd619480ffe30ca401bf1865201ffea32900ffe519487fbf28ca403ff1465201ef8a329103ff4194881dfa0ca43fff90652207fa83290fffc419487fff18ca43fff0c65203ffc432901ffc219480fffb04a407ff98252025fcc12901ffd60948017eb04a407ff1825201ffea12900f7f5094807fe284a440ffd0252207fc8129103fd4094881fe204a43fffc42521fff8212901eff655487dffb22a43ebfd91521f7fcc8a900afe645487dfeb22a43ebf591521f7f8c8a900afc6454807ffaa2a403dfd515201ffca8a900ffd545487dbeaa2a403ff15152007fec6a9002ff6354801ff31aa400ff58d52007f8c6a9022fc6354807ffa9aa403d
  | 10 => 0x28000000000000000c004001005800000000000080000020000000008000000002800401600000000000000000000008000000000000000200000080000080000020004002000000000400000500180000080010018000004001001003c0000030008004000004000000001000200000080120000000010000000000800400000000580080000000000000000000000800400400300180000020040000000002006000000c00e0000008008004000000801000000100280000000000008004000000000001000200200100040000080010000000005000800001800100280000000050000008000000002003000400700200300040010000000008004001000000000300000000040010020008000004000000000000200080140020000020008014001000800000600000080000020010000000012000000000400c0020010008000003000801400400700000080000020000010000001000000400c0000000004000006000000800000300000000000010018020000000000802400600900000000000000028004000003002801c000000000000000a0000000000010001000001c0020020000000000009002800000c0030000000000008007000000400200080040000000038000002001000000800000200080000040000018004004004001001c00000000000000060070008008002000000000800200000080140020050000000002004001000400000100180000000020008008000000002000c0020000018000006000000000000000100000140000000030014014000000800c0040000030008008000000001c0000010000010002007000000000000400180040000010000004000000000000c00000100300140000010038000000001000800401800000000000040060018004002000004800800000700000040060020000020002003002000400a000001000400000000000000000010018008000001004800000c000002000400400400080040020020000000004000006000000000000380000080010018000004005000800c000000002000c0000010000004004000000000400000500300000000000010000000000001800c006001003800c00000200080000160000000004008001000800c002002000000000c00000000000080000008000000000000000800000100180000000030010004000001000800800000000180000040010020000000000001800400000000000040060010008000004002002800000200300000100000010010018077eb2ca608ffd9253045fec929823fe6494c057f324a608ff59253225fac929823fc6494c117e324a603ffd525301efea92980ffe5494c07feaa4a644df5525301ff8a929822fe6394c11ffa9ca608dfd4e5301fbea72980f5f5394c11fe29ca608f714e53047fe8729823fe4394
  | 11 => 0x1e3c3e61c500000002200000001c48ae232b21da1d40ce0000000000f3a64311c1e10f3c00000001c400000034d8ad50e60000000000000000000000000062b27d800115c0491a68000c2e0000000000000000000000000000000000009066dc0000000eda6c840d881c24e00000000000006921d21500486244000178c2f26d70b6000000035100000000000001a300008940000000eb0f1c3e2000014000080a10c21785ea000000171c3d82db0c616d8d66089000000000000000000000000002ae9c4000000000000004ce00000009b89664d50001fa40000001589af800074914d80006486822b28000a3a00000009bc1f24da1869a6031e25d000000024a2b31f7161800000000009089f40000001fc40000000001380f7e1ad1061c506b20000000000dac00000013f06ee2002768cd0da051c3692038b0a1e40000000000000000000018431c19913202ec452000000000000000000000000000000920ba800000005d00000000000b9800200000000000003d800017180000000000000000000194000020400000000006d436f2e20000ce000000000007a2782000000019400000000009080001c91a780002af22f1c740de00000000d0d2248641200000000000000000b780000c6800000000000010cc00036126e9afc0004f911b00000006b831a9870000000000000000071300022d880624f00000000000002a7800000000000000007066590cc12301425e2000000080a58a0b19ba000039b398150c0f80000000b3800031f260807c00000027f0b5000065500005bc00034e000000000029f2d80fd8b1254200012e800000016a84c0cd015f0000f9000000000000000000000000a60b707802fd1cd0e6a3d2045872cdc000000000008e8391000000000048800006805f40720000a4cf6c24012f11c47260ea38b000000000045d00000000000188000c580000000e68baa000000000000000000000000000c40000778000000383892ca9c7b300000002480000000000008000000800000000100000020030000008002001003001000200000000080000010000004000004000001c00600000080100020020000000000000002001000200000000000000020000000002000000801c002005003000c000000000000400000600180140000000008008000000000000c0000000068000000000003800c00800100000040080000010000006000000000000600000000080000000008000000007000000800000300080000000000008000014005000000400c009000800800e001003000800a006003000000a000000001000200000080040000030008000000002000800800e000000001000000100080040000000010000000002001800000200000080080000020028008002001000000000a0000000000004001000800c00a005
  | 12 => 0x869700009846a60042be8bb8c360001d7000000000000000004641671f580000006900001850af418932c03c06ea0000000a881ae68304900000002ae1111d44e8400000003c85e442a14f0e64828000000000000072700000000000002f48000000027059000000000000000000167743e710fc0a400000000003de00000000a800000000011b4ece0002951f20f0e0000000454aac00020f0af800000021006d8f941971459b600004890001d00000000000000017a00005f079823400000018a00806031f800000006390ea8000000257316a05c00083f0000de80007bd20d800012c6330000000000000000000000000012803bc0000000000f386222d3249000096a0001c080000002d200000000000000000000c2038739887840000000f0000000000000005a400000010919e40485f1296000071039f3f29cbc00032c0000f8c0001ba1648bb461862e07a21bc2523d52da09ccea66b045602280000000000d98a7650d24f9f6c59007f00000004c40001e680005423781ed107030648a00000b06be00045018c8a8a20345e20f463c00000015f04b230433f940c0001be0000000492078000173400000000001900000003770000bda4b91cf19940000000d716600000002bd893000000011f068c61e6a900018dc0003f52120000ff08410ac9aa0e426b400000000000070ab000015000000000010082520001b9490421105b00005de4110ce000000000039480000002132321aac64677d40396a41e60b000019705f834936f1f84000000000000000000028b80009e082500018740000003cb80002fc0000890000a2a6160000000000000000116c0560001f99a3506867600000000000003c8800058400041080000000000000000d103f92948c6cd480000e98150096000000000000021d00019500000000001eb423a66108f200ca7e64903599ec28a0001a191fcf186a000007a027c6464200b6800000000008400007ba00003dc9b00001d5000000000000014f860400002b8158c88146000000000059000000000007bb25080000000000000000a3c03f228800000000000000bd122507000166800000000000000000000ec21e8000687269913065e5740de94ac42a50f388800000047b2b18b610e800000000010d08670001bd452e29127703acf240e00000000f0c00031780001567ee000000000000000005e10528453f385fc000000000000000000000000000000d0000000000000000f00000000000000ff00b800017f03ec5580d900998e8000000000227000000004d80000bc1da00000000003bb40f80000000000000000000416000000099e8141dc9adc6ae34238400000182960000000fb80004088adccda8a81a9000031c83b00000002ca6f7000199886400021d000105c7ec000203c4280003101d20bf057313f
  | 13 => 0x30000d9800039f196c0000000b68f302a600000000000000000000ff40000003d4000000000044d85988923bf27b9510b4c09c3ec80006aa0003c48000b6e40729e800000049e00007b423632a16205a8b64512246829000037600004ec0000000000000a20000000000000031000000000003de00000000003b71e58000d6200000004240005790000820bf258d0af00004020003b1096910e4340e30ce4000195298800000024a000193c00036e3ae0bb0fac32707e17f400020900016ac39c03b0001c6c00000000000002c856e1ee09b000085536d0000000000000079473a00000000000ba0001d1222c1720000000000f4e7250000f0800060802f9facb620000000ab4c6800016616744f800000000000004bd4320a740000000001f180000000000c240000000130000000000000000061c7ff0001d0c08855a22f912093800000014a000000000000006004593aa844ce6e3e935917cc9e40000000af47380003ad0444de23f70000240fa47d0399800112481a1340db47821430a10c8800000000004a00000000bd013085e0000000000f544c60019d0471a000000000000004a0000000000000000137800000000016651140003af00000005921da88a08a80000000648e2e082000000000000000006d0000182000000000000000000000000000000c68a9486327580000001390000000000000000009400086100011601960513061730f4456d000000071650b0b903e900a02919da1f8aec1030930a504f60003ca8fa0000000000000034c00002d22bc0000000858a3d16284a1f5023cd3a00003b86408ba611000170443400000000d4000091000000045e0003259898cae88d0ef94900000000000b904c8000000000000003d00000010d68820ee1d740000000001908e06409201058095e000000000000000000000006e468900005ec51429a0d9a20400000000000009a077621c9c340001b500010dcb5a000411800000083700000000000000000138000000167a150f86000000140910a5be14700000000000c9800000000000000010f08491f380006260000000000ef400000006201fa00023f1de411c85900004ac00000000000008e60000000000000000198800000023900000000004700001d800002c129380000000000a584b446e00000000000000001f6000000000000011b80000f10000000000000000024cfc40000b8959c0000000000644b3e000000130c3644260000ebd02c35d0cb1ba87502f817180000005ea00000000500001c70000b8026d4142034df45662738bcc93a26b451229c00075835c80001c6000000000000000000017d40000003a613d08c6455000000036e71a0398b2c0000002bf0f00ac200000000000000000000000740662155800002c00041f00000000000000898000000064118017
  | 14 => 0x7785ce425800012e00016522500000000000d2c00079f4559784f8e0c500004b0d820000000000d6a3b307f013ce0051a26e1f1000000043614e40000001b1000000013700005a09d01f40f39a98aea00000000010120002f914c05b24a409711a0d08000000113c00022300000003760000f50b18ad800013a16cd07065600000010cc0000ac00000000001b3800000000000000000000000ae90740007503910334000000000209c0000003f400008340001eb102c0000000000f8000000000000000008a342d16501000000000000000000000021c0000000000f84c1c0002099b84f5e0000000000edc00021280009fe50e39f800000008800000000008a900000000000000001ef80002c30001424000000000000000020e000000000000000013bc00041f083928c34800026280007622bc11a0000c6c1ab383000037e135272151c000000252886cb9e3971a40000bd870c00000000000000d60000c4e00001c9c140000000000000000000000141000025500011680003f409009a800000000004f0dda00000000000000000001e4000000000000000000000001cd8aa800000005dca103c61d80000000138000183c22c0593bb96389d434f1c11bd10a232100000000000530001dd42e000045b8000b9089d00005840006af16e00000000000000000000000300800000072d07c1f7c45400000000000000002df928800000000000000000000000000bb453c00010610d459500000000820000001e94a32000000000000003030480000000001e2800000000000000008cc00021c00000c40000000000a5e00040400000000000f4800094e6d340e0c480003ab1480e58dec00000013c4d4e000000000000065f0001fdc74c12a27480000004040000000000000000000108c0ac00020d8000000000048414400000000007ae000000000000077029900000000001bf11403b20e12b2154c1d087130010c0a46000000000000059b36a00000007e0000157c22e68b00011d466e0e900000005a23a130a80000007de44400000281540a3a1b43845fb29c006c3980653d321c045846c1601a8c000513000000000001c2f401a0e1e00000001080000003d880000005a71d280000004a633600000000000000000ab00000001cb000069f00000003b60000001b3c00000041aa0bc82a4bf3300000d7a246000176c8ec7b9000135827e412000000016655e3950a6400000000016e400083a282865108e0b10000000000000000000000000000000000000002c88000000000000000000000000000004ca0002659328f3449600000000000a50001a1400000024d1d6c54e0003d2097c5e8604000000043200037987589540001930e144b03863011be400088902a8a803a80000000000000000000000000084427600000000003f
  | 15 => 0x1aa18297988c407b315042850c0f506180003500002080000ab800039202e8b2e13142b8a306bc10533a8000000000000000000000036200000000af0000000d0228300000000781850168000faa58b00001c08787cf0f1000000000006f00004fe037000200467a00000000000002560cf81a50980003fa810d0e416b000000000033f00004ccc3e00000004e87f65df0801f2c0226120001e043a40001b60001026000000000108600004d00010dc5b50fb0c6400031500000003800000000e3d09e7ac35e22683e0032000082820821700000000000ff00000005d000000000000000000a5000016e40a000170c9b200000020b103c00040e800026467400000000001cf37e97dca980360001b345041c40000084c3200000000011680003fd1b1400000034a96306400000000cf00d80002850f944e0000000000109000010100000000cc2ab80000000a9322800000000000010b5032000046000109c40f0000000e02000000047000077f00000009a400021402b8d5c0e734d1a64e6460a24a00006827961780c5c96c074000039511e76c00000000000003f819dc0000002d7800000072b1e400000000003f19e848b80003e297b800000045a80683600001c21d480000000000000000018000000000011f361911c00000000000000000000e888c042c77c000000000000006e0000000000000000000000015d80000002290001f444400d410f0160e884673b2133887c788337843c00000041c99680000000ee8d3001e22d363a0c885c00033187f80003c712d800000000000000000000000001ff88585ff35118fc00004824c00000008790000000ec24c01a000010200000a6000000022100012f8510005434a2e4000000272800000088400000010c4000000000000036442b04050c05183d701145240000000b5884e61a000098c74e0001ae000044e000000000000085d0000000000511000000000000000000000000000000000c6003300000000005e045816200003680000da40005840001d50d2600000000000000000000000000000000000000056013900000006c600011ac00034400000000005870000970b060000000000000000000000000074d26d9b8c000000258100466600000013500000000000000000000382000000000007682809c275725c00000000000000dd0000000000000040c4360000000000802102855c21c8532158504f64060142108c0000d32649b9c00002219c1b9800015c0000000000000000000000000002d8cb45000c022000000002c5303811c0000003648020efc5e70e51944000000000091400000000000000000001ad9f74c160000000dc43f883c15f8000000000000000000000000000000007280001400e2a0001bf80007e4465000000000085c2061c8c46a7cd0f18bd80
  | 16 => 0xec0000000000000472000163c0001bc00000003446ec00004d88441eb00015ac630314302800047e000000075cbae2de0000000d2c19e00000000000000000000f4018a10796005c06941739c981b456a08312800001d03f511f400047c00015a40000000001e647863a30000000a66747000225c00076f25d8000afe75f0000000000000000112c00000d01c00007e251f00005cc00076a235202c00000031100000005930000000fae7d34550000ba00000001d28000000126833c0000002ad89e458e5c21ab000000000003080000000000001bfc000000000000050a6a5000134454a7c223d07c90a068f0ad8c58e740001818fbc00043d16e8000d0c000000000000000000000000004e2000087c00009521880000005d30000000b0468e00000000000004418000000000000000000041900021f00000001551da40002a9340193400000029b1c804085810000b88000000000000000000044fa2ec0000000001b6c7b218b13e9430be0000000000000000000000011641b900000001020001c48000c7a0000000000c4600000000006ca0df0000000000000000000000000000000000000000000d8c0001143c58000fe600000000001b6000000000025e79c237a29800078a00900009ec0000001b38ca04c208680000000002f28a044e24e3000000009a1a50000d1c0000000001d5801c2662e89f685d674f000000080c0000000000958478000000008c3ed0b100000007a300008ac14600000000000000001708000ec60941ff87e905a0003391204dc88931809f04968000310848cb5c77b04f00010ca0003711e1400000018380000003d33848618de46691a8000000000000000000006f8000000000085b000000000000003e80000000001be0d605126cb2fe17bc99a0000000734ee61b81fd189418216e00000000000000001fd061630a00000005461c804c976000054b0000000000000000000000000000000000000000000000b2c3fe172a24000000029a80000001a10000000752000000000110c00000021fc13a000000094c14c0c924980000000f600000000006d5255a294bec0853a2800000000000000000001c300000008a600000019cc00078336e80000001480001da00001842b1000050e3ad0170bf40006d100000000005de1c611585ae0000e3800000049116680009f07f200000006fa00000000000006244061ff4bfc0000ff83880005700000f7c5507460c399ac00006e000000000000000008e8c8200000000000003dd3c687ecc900000000cf8000000000000010c00000a88ccfec06329b82100007590000000000000000000047622409100000000000001238b54000000000000000000019c4ee40002108000000000000006400000032999480003302f5800000083024d82fcde067e08c1edc0005d90
  | 17 => 0x184ccd437300012a45485a20001a280ec000291151800052100000000003c930f13cc23221c361034417054d24b80000000001ca80000000002808000280000000000000000000000000006df00000000007fb00001d43ee17c0001a7000079400000000041c11188000e5c1f11f30000c0c7fc306800000048f0468000cfa7c90000420aa40aa17b9c6490a435000121c00065d3e0199cab20dd39c80005644290000a7000000000018a400000017f800029c76b00000000004f500004d051a2b901d20a85680000001f609cc0000a81134cf001000000000002950002254b4200000000000007d4076000036252e0000e5000000000000000000002d183480000001058000000000000000000000022180009507e42a09fb47681a925ba148000000010000000000025917750663ba42c19e90ee00000016ec0000000030000fde00038e21080008ad2a48000aa20c705d80005d4000184026000000042f8000f5600000007b80003062458d50ae43db0bea0011482b029300000000000a69450e3c3be1de8000be808300000000006eb000135ccc86fb25680010560000000000c8000000000000000000000e6117a6ba2d00001166000000000104c7f90000daccdc0000000f405d2638000098000015203515e0aee6aa43e800096200000000000000002211cec000000000208834e25400000004ee0d60fc000000074b2aa9110000000000169464a4953569b6400000000000000007781789ab0b5800000000000000001c500f80000004470e0068a65e00511a40002f93cc0dec1aa0003b8800109a000000000079e71f00009a480000000000000006e93e6000000022e000066c00000040c03b813e07900007f400031d44015200120000000000a68000000000000000000014e800049900000011704790000904c9406d2481480cf800044f00000465c9000054400064730c000000000022088f0000000000000000020d00020c40001c913b16780006a10fc8674e781753651690a5a5d62661ea4f7837913c0d6800000000000007702470000cb86e010c0000cd4a0c7b5000000000087b2e29118000000000000000000000000000000000a210340000003dc000000044e19b00003021800000000978793000000000000000000000000001a515bc14e00000001980000000000000e140c60aa82d40005cb16f972800000031f0000d18631000000000052545083900000000000000000000000000000000000016a000063b0000000ecc00000000007a800038c19380002750001ad80000003da12b8f3607e39c000000001720ba05511800017d91dc5a000000002d0dde5d200020482926c044c131c00000000010380f419a0ad1d3800000009e911419c00026f83600003c424000004f400000002b47f000015d07d400000037f1671
  | 18 => 0x2b40074c9823d00006bc000000000000000000000017900000002a800000001990000ce800000040322584a26bb37e13f4e162b807313107940000000000eca00038718f06525bd1b000000000000000000000702000000000051b000000049c51600000000007b0000000000073d4100ec80003b61c8115c0005dc0a7800000000000000000000000000894b7489915b0a9800000020400008c2000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x45350510007b77250510007b67250510007b57250510007b47250510007b76250510007b66250510007b56250510007b4625051025fb75250510007b65250510007b5525051025fb45250510007b73250510007b63250510007b53250510007b43250510007b77050510007b37050510257b6705051002fb57050510257b47050510007b0705051000fb7605051000eb7605051000fb3605051025fb75050510257b65050510257b45050510257b63050510257b43050510257b62050510257b42050510025f4764c510046f4764c510024f4764c51000777654c51000774654c51024df7744c51024df5744c51000df7734c51000fd7734c510007d7634c510046f6634c510046f4634c510007d4634c510247d7534c510247d4534c510007d7324c510007d5324c510007f3704c510025f6704c510025f4704c510007f0704c51000ef7604c51000ff3604c51001cff765411000cfe765411011cfd765411000cfc76541100067f655411001e7c6554110005f7715411000df47154110007b54154110027f0105411000cfe76cc11000cfc76cc1100067f65cc1101167c65cc110006df63cc110046dc63cc11000df671cc110005f571cc110007b541cc110007d531cc110044ff764c11000cfe764c1100d4fd764c11000cfc764c1100057f754c1100357c754c1100067f654c1100e67c654c110005bf744c11002dbc744c110006df634c110046dc634c110005f7714c11000df4714c110007b5414c110007d5314c11000cfe76c811000cfc76c81100357e75c81100057d75c81100067f65c81100b67c65c8110006ef62c811003eec62c811000df671c8110005f571c8110007b541c811005dfa7688110026fa76881100277a75881100277975881100077b6588110007786588110075f9728811003efa628811003ef8628811000dfa7188110025f87188110026fb6188110027f3618811008fbb418811008ff2418811008fb9418811023ff14188110007b1418811008ff23188110007f1318811003cff764811000cfe7648110074fd764811000cfc76481100067f65481100867c6548110005bf744811002dbc7448110006ef624811003eec6248110005f7714811000df47148110007b54148110027e8204811000df8764811003ef8764811000cf876481100077b6548110007786548110007bb744811022fb87448110025fb7248110027eb7248110007eb624811003efa624811003ef86248110007e86248110237eb5248110237e8524811022fea424811022fe94248110007ea3248110007e93248110007f3714811000dfa714811000df87148110077f07148110026fb6148110027f36148110077bb4148110077f24148110077b9414811022ff14148110007b14148110077f23148110007f13148110077eb2148110077e92148110
  | 1 => 0x4d10004fd7694d10044fc7694d100067f6594d1001e7c6594d100375f5394d1000df67194d10005f57194d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d1003cfe76d89100067f65d89100067c65d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d8910044fe73d8910004fd73d8910006ef42d8910006ec42d8910024ff71d891000cfe71d8910024fd71d891000cfc71d891008ebf41d891008ebd41d891008eef21d891008eed21d8910024fe70d8910024fc70d89100357e75989100057d75989100067f65989100067c6598910006ef6298910075f970989100057f75589100357c75589100067f65589100067c6558910005bf745891002dbc7458910005df7358910005dc73589100a5fb7058910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df7358910044fc7358910006dc7358910044dc7358910006ef7258910074ff7158910006f77158910076bf4158910076bd41589100a4ff7058910006fb705891008cfe76189100067f65189100067c651891003eee6218910006ed621891003cff7694910004fe7694910004fd769491003cfc76949100067f659491001e7c6594910025fa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc76549100067f655491001e7c6554910044ff76cc910004fe76cc910004fd76cc910044fc76cc9100067f65cc9101e67c65cc91002dbe74cc910005bd74cc910006ef62cc91003eec62cc91000df671cc910005f571cc91003cff768c910004fe768c910004fd768c91003cfc768c9100067f658c9101ce7c658c910006df638c910046dc638c910025fa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100357c754c9100067f654c9101b67c654c91003cff760c910004fe760c910004fd760c91003cfc760c9100357e750c9100057d750c9100067f650c91019e7c650c910006df630c910046dc630c910006ef620c91003eec620c91000df6710c910005f5710c910025fa700c910005f9700c91002fb77650510016b7765051002fb47650510016b47650510007b7755051025fb67550510007b5755051025fb47550510007b7655051000737655051025fb66550510007b5655051025fb46550510007346550510007b77350510007b67350510007b57350510007b47350510007b76350510007b66350510007b56350510007b4635051025fb75350510007b65350510007b5535051025fb
  | 2 => 0x77541d951012f7631d951012f7b10d951027f7610d951027f7410d951012f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d951027e7f71d951012e7e71d951012e7d71d951012e7c71d951012e7f41d951012e3f41d951012e7e41d951012e7d41d951012e3d41d951012e7c41d951012e7f31d951012e7e31d951012e7d31d951012e7c31d951012e7f21d951012e7e21d951012e7d21d951012e7c21d951012e7f70d951027e7e70d951012e7d70d951027e7c70d95100067f40d951027e7e40d95100067d40d951027e7c40d951027e7e30d951027e7c30d951027e7e20d951027e7c20d951012e7f10d951027e7e10d951027e7c10d95100367c6559510275fb705951012cff75595100067f7559510004ff7459510014fe7459510004fd7459510014fc7459510004ff7359510044fc7359510004ff725951003cfc725951011cff7159510006f7715951011ebf415951011ebd4159510274ff7059510006fb705951012d7e76195100367e761951012c7e76195100067f64195100067e64195100067d64195100067c641951026e7f61195102673f41195102677641195102673d41195100077541195102677631195102667f60195102677b101951026f76101951026f741019510267781019510044fe76d8d100067f65d8d100067c65d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df43d8d10006dc43d8d1003cfe72d8d10004fd72d8d10024ff71d8d1000cfe71d8d10024fd71d8d1000cfc71d8d100eebf41d8d100eebd41d8d100eedf31d8d100eedd31d8d10024fe70d8d10024fc70d8d100357e7598d100057d7598d100067f6598d100067c6598d10006df6398d100d5f97098d100057f7558d100357c7558d100067f6558d100067c6558d10005bf7458d1002dbc7458d10005ef7258d10005ec7258d10105fb7058d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d100d4ff7158d10006f77158d100d6bf4158d100d6bd4158d10104ff7058d10006fb7058d100ecfe7618d100067f6518d100067c6518d1002dbe7418d10005bd7418d10046de6318d10006dd6318d10044ff7694d10004fe769
  | 3 => 0xe7458e10004fd7458e10014fc7458e10006bc7458e10014bc7458e10026df7358e10006de4358e10006dd4358e10004ff7258e1003cfc7258e100d6bf4158e100d6bd4158e100d6df3158e100d6dd3158e10024ff7058e10024fe7058e10024fd7058e10024fc7058e10026de3058e10026dc3058e10026f71058e10026f51058e10044ff7694e10024fe7694e10004fd7694e10024fc7694e1029e7f6594e1001e7c6594e100575f5394e10004ff7654e10024fe7654e10004fd7654e10024fc7654e1001e7e6554e100067d6554e10004ff7558a1001cfe7558a1001cfc7558a10004ff7458a10006bf7458a10004bf7458a10014fe7458a10004fd7458a10014fc7458a10006bc7458a10014bc7458a10004ff7358a10044fc7358a10026ef7258a10006ef5258a10006ec5258a10006ee4258a10006ed4258a10076bf4158a10076bd4158a10076ef2158a10076ed2158a10024ff7058a10024fe7058a10024fd7058a10024fc7058a10026ee2058a10026ec2058a1003cff7694a10024fe7694a10004fd7694a10024fc7694a1001e7e6594a100067d6594a10025fa7094a10005f97094a10004ff7654a10024fe7654a10004fd7654a10024fc7654a102967f6554a1001e7c6554a10005f77154a1000df47154a10044ff76cca10024fe76cca10004fd76cca10024fc76cca1004dbe74cca10005bd74cca1003cff768ca10024fe768ca10004fd768ca10024fc768ca1003eee628ca10006ed628ca10025fa708ca10005f9708ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca100057f754ca100557c754ca1003eee624ca10006ed624ca10005f7714ca1000df4714ca1003cff760ca10024fe760ca10004fd760ca10024fc760ca100557e750ca100057d750ca10025fa700ca10005f9700ca10025fb7648210006fb7648210007bb7448210287b87448210027eb7248210027eb624821003efa6248210026f86248210027e8624821028feb524821028fe85248210287ea4248210287e94248210007ea3248210007e9324821000dfa714821000df87148210077bb4148210077b94148210077eb2148210077e9214821001cfe76d95100367e65d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100367f54d95100067e54d95100067d54d95100367c54d9510044fe73d9510004fd73d95100367f53d95100367c53d951003cfe72d9510004fd72d95100367f52d95100367c52d9510024ff71d951000cfe71d9510024fd71d951000cfc71d951012e7f51d951012e7d51d951012ebf41d951012ebd41d9510024fe70d951000cfd70d9510024fc70d95100367f50d95102657e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d951012f3f41d951012f7641d951012f3d41d9510
  | 4 => 0x9420024fc70594200267e50594200267c5059420004ff7558c200067f7558c200047f7558c2001cfe7558c2001cfc7558c200067c7558c2001c7c7558c20004ff7458c20014fe7458c20004fd7458c20014fc7458c20024ff7358c20026df7358c20006de4358c20006dd4358c2003cff7258c2003cfe7258c2003cfd7258c2003cfc7258c2003ede3258c2003edc3258c20004ff7158c2000cfe7158c2000cfc7158c20006bf4158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20026ef2058c20026ed2058c20044ff7694c20024fe7694c20004fd7694c20024fc7694c2029e7f6594c2001e7c6594c20046de6394c20006dd6394c2006f5f5394c20004ff7654c20024fe7654c20004fd7654c20024fc7654c2001e7e6554c200067d6554c20046de6354c20006dd6354c20004ff75584200067f75584200047f755842001cfe755842001cfc75584200067c755842001c7c7558420004ff7458420014fe7458420004fd7458420014fc7458420004ff7358420044fc735842000cfd7258420024ff7158420026f7715842005ef6515842005ebf415842005ef64158420006f5415842005ef6315842003ef7215842003ef42158420024ff7058420024fd7058420024fc7058420026ef2058420026fa2058420026ed205842003ef92058420026f61058420026f41058420004ff7654420004fd7654420024fc765442001e7e65544200067d655442000ef66154420006f56154420006bf7650420256be7650420006bd7650420256bc7650420256bf655042017ebe6550420006bd6550420256bc6550420256bf63504202b6be6350420006bd6350420256bc6350420007af72504202a7ac72504200a6be62504202adbf7150420067b77150420256bf615042000ebe6150420257b6615042000eb6615042005ebd6150420257b56150420006b5615042000ebc6150420256be6050420257af2050420257ba2050420257ad20504202a7b92050420257b71050420044ff76cc420024fe76cc420004fd76cc42006d7e75cc4200057d75cc420046de63cc420006dd63cc420004ff764c420004fd764c420024fc764c420046de634c420006dd634c420005ef724c42003dec724c42000ef6614c420006f5614c4200267f7559610004ff7459610014fe7459610004fd7459610014fc74596100567f54596100067d5459610004ff7359610044fc73596100567f5359610004ff725961003cfc72596100567c525961011e7f515961011e7d515961011ebf415961011ebd4159610024ff7059610024fe7059610024fd7059610024fc70596100267e50596100267c5059610004ff7558e100067f7558e100047f7558e1001cfe7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e10006bf7458e10004bf7458e10014f
  | 5 => 0x6bf6454520186bc6454520005ef725452003dec72545200876f5254520006bf7650520005be7650520006be7650520004be7650520006bd7650520005bc7650520006bc7650520004bc7650520006bf655052017ebe6550520006bd655052017ebc6550520006bf63505202b6be6350520006bd63505202b6bc6350520007ae7250520007ad72505202dfaf52505202dfac5250520007ae3250520007ad3250520075bf715052007fb77150520076bf615052000ebe615052000ebc61505202a7bb2050520257ae2050520077b71050520004fe76cc520004fd76cc520044fc76cc5200857e75cc5200057d75cc520006bf64cc52016ebc64cc520046de63cc520006dd63cc52003dee72cc520005ed72cc520007cd32cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c520006bf644c52015ebc644c520046de634c520006dd634c520007cd324c520005ee76c852003eee76c8520085ee75c852003dec75c852003def74c85202d5ed74c8520007af64c85202cfac64c852003def73c8520005ed73c8520075ed71c852000eee61c852000eec61c8520077af41c8520077ad41c852003feb70c8520025ee70c8520025ec70c852003fe870c852003eef60c852003feb60c8520024fc76485200057f75485200857c7548520006bf644852013ebc6448520006f7614852000ef46148520005fb7048520025f8704852003fe82048520025ec764852000eec7648520024ec76485200076f7548520085ee7548520085ec75485200076c75485200856c75485202c5ef74485202c5ed7448520007af64485202bfac6448520005ef7348520005ed734852003def714852003fe77148520007e7614852000eee614852000eec6148520077e46148520077af4148520077ad4148520007eb7048520025ee7048520025ec7048520007e8704852003eef604852003feb604852001cff7654120084fd765412003cfc76541200067f655412001e7c6554120006bf6454120126bc6454120005ef725412003dec72541200876c5254120027e8205412003cfe76cc12003cfc76cc120006bf64cc12010ebc64cc120006df63cc120046dc63cc12003dee72cc120005ed72cc120044ff764c120004fd764c12003cfc764c1200057f754c1200857c754c120005bf744c12007dbc744c120006bf644c1200debc644c120006df634c120046dc634c120005ef724c12003dec724c120024ff75594200267f7559420004ff7459420014fe7459420004fd7459420014fc745942006e7f54594200067d5459420004ff7359420044fc735942006e7f535942003cff725942003cfe725942003cfd725942003cfc725942003e7e525942003e7c5259420004ff715942000cfe715942000cfc715942006e7f5159420006bf4159420024fe705
  | 6 => 0xf7558d200047f7558d2001cfe7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d20006df7358d20004ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d20006bf4158d20004ff7058d20006fb7058d20004fe7618d200857e7518d200057d7518d20006bf6418d20006bc6418d20046de6318d20006dd6318d20044ff7694d20004fe7694d20004fd7694d20044fc7694d200067f6594d2001e7c6594d20006bf6494d20226bc6494d200875f5394d2003dee7294d20005ed7294d200876c5294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2001e7e6554d200067d6554d20006bf6454d20216bc6454d20005ef7254d2003dec7254d200876f5254d20024fc76549200067f655492001e7c6554920006bf64549201f6bc6454920085ef725492003f6c5254920005fb7054920025f8705492003fe82054920024fe76cc920024fc76cc92007dbe74cc920005bd74cc920006bf64cc9201debc64cc920006df63cc920046dc63cc920025fa70cc920005f970cc920005ee768c92003eee768c920085ee758c92003dec758c92003def748c9202fded748c920007af648c9202f7ac648c9202eded738c920046ee638c920046ec638c920005ed718c9202f7af418c920025ee708c920025ec708c92003eef608c92003feb608c920024fc764c9200057f754c9200857c754c920006bf644c9201aebc644c920006df634c920046dc634c920005fb704c920025f8704c920025ec764c920046ec764c920024ec764c9200076f754c920085ee754c920085ec754c9200076c754c9200856c754c9202edef744c9202eded744c920007af644c9202e7ac644c92003def734c92003fcf734c920007cf634c920046ee634c920046ec634c920007cc634c920005ef714c9202e7af414c920007eb704c920025ee704c920025ec704c920007e8704c92003eef604c92003feb604c92000cfe76d852007dbc74d8520006bf64d8520006bc64d8520076f661d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520006bf74d8520014fe74d8520004fd74d8520014fc74d8520006bc74d8520014bc74d8520044fe73d8520004fd73d8520024fd72d852000cfc72d8520006f751d8520076f451d8520076bf41d8520076f431d8520076f621d8520024fe70d852003cfd70d8520024fc70d8520076f710d85200057f75585200857c7558520005bf745852007dbc7458520006bf6458520006bc6458520005df7358520005dc7358520076f46158520004ff7654520004fe7654520004fc765452001e7e65545200067d6554520
  | 7 => 0x9520004ff74d9520014fe74d9520004fd74d9520014fc74d9520044fe73d9520004fd73d95200867c53d952003cfe72d9520024fd72d9520086ed72d9520024ed72d952003cfc72d95200867f52d9520086ef52d9520086ec52d952000cfe71d9520004fd71d952000cfc71d95200067e51d95200867c51d9520006bf41d952003cfd70d95200867f50d95200867c6559520005bf745952007dbc7459520006bc6459520005df7359520005dc73595200876c5259520005f77159520075f47159520084ff75595200067f7559520004ff7459520006bf7459520004bf7459520014fe7459520004fd7459520014fc7459520006bc7459520014bc74595200867f54595200067d5459520004ff7359520006df7359520004df7359520044fc7359520006dc7359520044dc73595200867f535952009cff7259520006ef7259520086ef52595203167e52595203167c5259520086ec5259520004ff7159520006f77159520004f7715952000cfe715952000cfc7159520006f4715952000cf471595200867f5159520006bf41595200b4ff7059520006fb70595202967e50595202967c505952007dbe76d912007ebe76d9120014be76d9120006bf65d9120006be65d9120006bd65d9120006bc65d9120307af72d912007fac72d9120007af52d9120007ac52d9120005bd71d9120006be61d9120006bc61d912030fbb20d9120307ae20d9120307ac20d912030fb820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006bc53d9120306bf72d912030ebe72d912007ebd72d912030ebc72d9120006bf52d912030ebe52d912030ebc52d912030ebe32d912030ebc32d9120006bf71d9120006be71d9120006bd71d9120004bd71d9120006bc71d9120006bf51d9120006be51d9120006bc51d9120006be31d9120006bc31d912030ebf21d9120006be21d912030ebc21d912030ebf70d9120306be70d912007ebd70d9120306bc70d9120006bf50d9120306be50d9120306bc50d9120306be30d9120306bc30d912030ebf20d9120306be20d912007ebd20d9120306bc20d9120006bf10d9120306be10d9120306bc10d9120044fe76d8d20006bf64d8d20006bc64d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df53d8d20006dc53d8d2003cfe72d8d2003cfc72d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006bf41d8d20006de31d8d20006dc31d8d2007dbe7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d200057f7558d200857c7558d20005bf7458d2007dbc7458d20006bf6458d20006bc6458d20005f77158d20075f47158d20004ff7558d200067
  | 8 => 0x67e21596203167c21596200267f70596200267e70596200267d70596200267c70596200267f40596200267e40596200267d40596200267c40596200267f30596200267e30596200267d30596200267c30596200267f20596200267e20596200267d20596200267c20596200267f10596200267e10596200267d10596200267c1059620004ff7558e2001cfe7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e20026df7358e20006de4358e20006dd4358e20004ff7158e2000cfe7158e2000cfc7158e20006bf4158e20024fc7058e20026de3058e20026dc3058e20026ef2058e20026ed2058e20044ff7694e20024fe7694e20004fd7694e20024fc7694e2001e7e6594e200067d6594e2009f5f5394e20004ff7654e20024fe7654e20004fd7654e20024fc7654e2001e7e6554e200067d6554e2001cff7654a20024fc7654a2001e7e6554a200067d6554a20005fb7054a20025f87054a201e67e65cca200067d65cca20095be74cca20005bd74cca20046de63cca20006dd63cca20025fa70cca20005f970cca20044ff764ca200057f754ca2009d7c754ca201b67e654ca200067d654ca20046de634ca20006dd634ca20005fb704ca20025f8704ca20004ff755862001cfe755862001cfc7558620004ff7458620014fe7458620004fd7458620014fc7458620004ff7358620044fc7358620026f7715862008ebf415862008ef64158620006f5415862008ef6315862008ef62158620024fc7058620026ef2058620026ed2058620026f61058620026f41058620004ff7654620004fd7654620024fc765462001e7e65546200067d6554620006bf7650620256be7650620006bd7650620256bc7650620256bf655062017ebe65506202573e655062017e3e6550620006bd65506202573d65506200063d6550620256bc6550620256bf63506202b6be6350620006bd6350620256bc6350620007af7250620007ac7250620076bd62506202adbf7150620097b77150620256bf615062000ebe6150620257b6615062000eb6615062008ebd6150620257b56150620006b5615062000ebc6150620256be6050620257af20506202a7bb2050620257b71050620257ba1050620044ff76cc620024fe76cc620004fd76cc62009d7e75cc6200057d75cc6201767e65cc6200067d65cc620046de63cc620006dd63cc620004ff764c620004fd764c620024fc764c6201667e654c6200067d654c620046de634c620006dd634c620005ef724c62003dec724c62000ef6614c620006f5614c62000cff76486200057f754862009d7c75486201467e65486200067d654862000ef66148620006f56148620005fb7048620025f8704862001cfe76d95200867e65d9520006bc64d952003dee72d9520025ed72d95200876f52d
  | 9 => 0xf7358720044fc7358720024fc725872003ef771587200a6bf415872003ef7215872003ef4215872003efa205872003ef920587200a6f71058720004ff7654720004fd765472003cfc765472001e7e65547200067d6554720005ef725472003dec72547200b76f5254720006bf76507202a6be7650720006bd76507202a6bc76507202a6bf655072017ebe65507202a73e655072017e3e6550720006bd65507202a73d65507200063d65507202a6bc65507202a6bf63507202b6be6350720006bd63507202a6bc63507202a7ae7250720007ad7250720327af52507202a7ac52507202a7ae3250720007ad32507200a5bf71507200afb771507200a6bf615072000ebe61507200a6bd615072000ebc61507200a7af21507200a7b71050720044ff76cc72003cfe76cc720004fd76cc7200b57e75cc7200057d75cc7201767e65cc7200067d65cc720046de63cc720006dd63cc72003dee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c72003cfc764c7201667e654c7200067d654c720046de634c720006dd634c72003dee724c720007cd324c72003def764872005eef76487200076f75487200b5ee75487200b5ec75487200076c75487200b56c754872003f6e654872003f6d654872031def744872031ded7448720005ef7348720005ed734872003fe7714872000eee614872000eec61487200a7af41487200a7ad4148720025ee7048720025ec704872001cff765432003cfc765432001e7e65543200067d6554320005ef725432003dec72543203176c52543201167e65cc3200067d65cc320046de63cc320006dd63cc32003dee72cc320005ed72cc320044ff764c3200057f754c3200b57c754c3200e67e654c3200067d654c320005bf744c3200adbc744c320046de634c320006dd634c320005ef724c32003dec724c3200267f7559620004ff7459620014fe7459620004fd7459620014fc745962009e7f54596200067e54596200067d545962009e7c5459620004ff7359620044fc735962009e7f535962009e7c535962009e7f5259620004ff715962000cfe715962000cfc715962009e7f51596200067e515962009e7c5159620006bf4159620024fc70596200267e50596200267c50596200067f74596200067e74596200067d74596200067c74596200067f73596200067e73596200067d73596200067c73596200067f43596200067e43596200067d43596200067c43596200067f72596203167e72596200067d72596203167c72596200067f42596203167e42596200067d42596203167c42596203167e32596203167c32596200067f71596200067e71596200067d71596200067c71596200067f41596200063f41596200067e41596200067d41596200067c41596200067e31596200067c31596203167f2159620
  | 10 => 0x84301567e65c84300067d65c843014ebe64c8430006bd64c843003eee62c8430006ed62c843000ef661c8430006f561c8430004ff7648430004fd7648430024fc76484300057f75484300cd7c75484301467e65484300067d654843013ebe6448430006bd6448430005df7348430045dc734843003eee6248430006ed624843000ef66148430006f5614843003e7f7559720004ff7459720014fe7459720004fd7459720014fc74597200b67f54597200067e54597200067d54597200b67c5459720004ff7359720044fc73597200b67f53597200b67c5359720024fc725972003eec7259720024ec72597200b6ef525972003e7e525972003e7c525972003eec5259720004ff715972000cfe715972000cfc71597200b67f51597200067e51597200b67c5159720006bf41597200b67f50597200067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067e43597200067d43597200067c435972003e7f72597200b66f725972003e7e725972003e7d725972003e7c725972003e6c725972003e7f425972003e7e425972003e7d425972003e7c425972003e7f325972003e7e325972003e7d325972003e7c32597200067f71597200067e71597200067d71597200067c71597200067f41597200063f41597200067e41597200067d41597200067c41597200067e31597200067c315972003e7f215972003e7e215972003e7d215972003e7c21597200067f70597202967e70597200067d70597202967c70597200067f40597202967e40597200067d40597202967c40597202967e30597202967c305972003e7f205972003e7e205972003e7d205972003e7c20597200067f10597202967e10597202967c1059720004ff7558f2001cfe7558f2001cfc7558f20004ff7458f20014fe7458f20004fd7458f20014fc7458f2003edf7358f20006df4358f20006dc4358f20024fc7258f2003ede3258f2003edc3258f20004ff7158f2000cfe7158f2000cfc7158f20006bf4158f20044ff7694f2003cfe7694f20004fd7694f2003cfc7694f2001e7e6594f200067d6594f200b75f5394f2003dee7294f20005ed7294f2033f6c5294f20004ff7654f2003cfe7654f20004fd7654f2003cfc7654f2001e7e6554f200067d6554f20005ef7254f2003dec7254f200b76f5254f2003def764cb20006ef764cb200076f754cb200b5ee754cb200b5ec754cb200076c754cb200b56c754cb2003f6e654cb2003f6d654cb20335ef744cb20335ed744cb2003fcf734cb20046ee634cb2003eec634cb20005ef714cb2032faf414cb20025ee704cb20025ec704cb20004ff755872001cfe755872001cfc7558720004ff7458720014fe7458720004fd7458720014fc7458720004f
  | 11 => 0x24fe7694830004fd769483001e7e65948300067d6594830206be6494830006bd649483003eee6294830006ed62948301fef66194830004ff7654830004fd7654830024fc765483001e7e65548300067d65548301f6be6454830006bd6454830005df7354830045dc735483003eee6254830006ed62548301eef66154830004ff755843001cfe755843001cfc7558430004ff7458430014fe7458430006be7458430014be7458430004fd7458430006bd7458430014fc745843000cfd7358430004ff725843003cfc7258430024ff7158430026f77158430006f751584300bef651584300bef451584300bebf4158430006f74158430006b741584300bef64158430006f541584300bef44158430046f73158430046f431584300bef621584300bef42158430024fc7058430026df3058430026dd3058430026f61058430026f41058430006f77558430006f67558430006f57558430006f47558430006f77458430006f67458430006b67458430006f57458430006b57458430006f47458430006f75458430006f65458430006f55458430006f45458430046f77358430046f67358430046f47358430046f75358430046f65358430046f55358430046f45358430046f74358430046f64358430046f54358430046f44358430006f77258430006f67258430006f57258430006f47258430006f75258430006f65258430006f55258430006f45258430006f74258430006f64258430006f54258430006f44258430046f73258430046f63258430046f53258430046f43258430026f77058430026f67058430026f47058430026f75058430026f65058430026f55058430026f45058430026f74058430026f64058430026f54058430026f44058430026f73058430026d73058430026f63058430026f53058430026d53058430026f43058430026f72058430026f62058430026f52058430026f42058430004ff7654430004fd7654430024fc765443001e7e65544300067d6554430186be6454430006bd6454430006ee6254430006ed625443000ef66154430006f56154430255bf7650430006bf7650430004bf7650430256be7650430255bd7650430006bd7650430004bd7650430256bc7650430256bf655043017ebe65504302573e655043017e3e6550430006bd65504302573d65504300063d6550430256bc65504300079f73504302b79c7350430106be63504302a6be6250430257ae6250430006ae6250430006bd6250430257ad6250430006ad62504302adbf71504300c7b77150430256bf615043000ebe6150430257b6615043000eb661504300bebd6150430257b56150430006b5615043000ebc6150430256be60504302579f3050430257ba30504302579d30504302b7b93050430257b7105043003cff76c8430024fe76c8430004fd76c
  | 12 => 0xf3159030046be3159030046bd3159030046bc3159030006be2159030006bc2159030026bf7059030026be7059030026bd7059030026bc7059030026bf5059030026be5059030026bd5059030026bc5059030026bf30590300269f3059030026be3059030026bd30590300269d3059030026bc3059030026bf2059030026be2059030026bd2059030026bc2059030026bf1059030026be1059030026bd1059030026bc105903003eef759883003eee759883003eed759883003eec759883003eef749883003eee749883003eed749883003eec7498830006ef5498830006ee5498830006ed5498830006ec549883003eef739883003eee739883003eed739883003eec7398830046ef5398830046ee5398830046ed5398830046ec5398830046ef4398830046ee4398830046ed4398830046ec439883003eef719883003eee719883003eed719883003eec7198830006ef5198830006ee5198830006ec5198830006ef4198830006af4198830006ee4198830006ed4198830006ec4198830046ef3198830046ee3198830046ed3198830046ec3198830026ef7098830026ee7098830026ed7098830026ec7098830026ef5098830026ee5098830026ed5098830026ec5098830026ef4098830026ee4098830026ed4098830026ec4098830026ef3098830026ee3098830026ed3098830026ec3098830026ef1098830026ee1098830026ed1098830026ec1098830004ff755883001cfe755883001cfc7558830004ff7458830014fe7458830004fd7458830014fc7458830026ef7258830006ef5258830006ec5258830006ef4258830006ee4258830006ed4258830006ec4258830046ef3258830046ec3258830004ff715883000cfe715883000cfc7158830006bf4158830006ee2158830006ec2158830026ee2058830026ec2058830006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef5458830006ee5458830006ed5458830006ec5458830046ef7358830046ee7358830046ec7358830046ef5358830046ee5358830046ed5358830046ec5358830046ef4358830046ee4358830046ed4358830046ec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef5158830006ee5158830006ec5158830006ef4158830006af4158830006ee4158830006ed4158830006ec4158830046ef3158830046ee3158830046ed3158830046ec3158830026ef7058830026ee7058830026ec7058830026ef5058830026ee5058830026ed5058830026ec5058830026ef4058830026ee4058830026ed4058830026ec4058830026ef3058830026ee3058830026ed3058830026ec3058830026ef1058830026ee1058830026ed1058830026ec105883003cff7694830
  | 13 => 0xc530166dc654c5300075c654c5301665c654c53034ddf744c53034ddd744c5300079f644c5303479c644c530006df624c530045df714c530047d7714c530007d7614c53000ede614c53000edc614c5300d7d4614c5300d79f414c5300d79d414c530007db704c530025de704c530025dc704c530007d8704c530046df604c530047db604c5300d7d7104c530004fe76c8530004fd76c853003cfc76c85300067f65c85301567c65c8530006bf64c853014ebc64c8530006f761c853000ef461c8530004ff7648530004fe7648530004fc76485300057f75485300e57c75485300067f65485301467c6548530006bf644853013ebc644853001cff76541300e4fd7654130044fc76541300067f655413001e7c6554130006bf6454130126bc6454130005df7354130045dc7354130024ff75594300267f7559430004ff7459430014fe7459430004fd7459430014fc74594300ce7f54594300067e54594300067d54594300ce7c5459430044ff7359430044fe7359430044fd7359430044fc73594300467e53594300467c5359430004ff725943003cfc72594300ce7f52594300ce7c5259430004ff715943000cfe715943000cfc71594300ce7f51594300067e51594300ce7c5159430006bf4159430024fe7059430024fc70594300267e50594300267c50594300067f74594300067e74594300067d74594300067c74594300467f73594300467e73594300467d73594300467c73594300467f43594300467e43594300467d43594300467c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067d42594300067c42594300467f32594300467e32594300467d32594300467c32594300067f71594300067e71594300067d71594300067c71594300067f41594300063f41594300067e41594300067d41594300067c41594300467f31594300467e31594300467d31594300467c31594300067e21594300067c21594300267f70594300267e70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300267e30594300267d30594300267c30594300267f20594300267e20594300267d20594300267c20594300267f10594300267e10594300267d10594300267c1059430006bf7559030006be7559030006bd7559030006bc7559030046bf7359030046be7359030046bd7359030046bc7359030046bf5359030046be5359030046bd5359030046bc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006bc5259030046bf3259030046be3259030046bd3259030046bc3259030006bf7159030004bf7159030006be7159030006bd7159030006bc7159030006bf5159030006be5159030006bc5159030046b
  | 14 => 0x6ee21d8930006ec21d89300e57e75989300057d75989300067f65989300067c65989300ddbe7498930005bd7498930006bf6498930006bc6498930006ef62989300057f75589300e57c75589300067f65589300067c6558930005bf74589300ddbc7458930006bf6458930006bc6458930005f771589300d5f471589300067f65189300067c6518930006bf6418930006bc641893003eee6218930006ed6218930004fe7694930004fd769493003cfc76949300067f659493001e7c6594930006bf6494930206bc6494930004ff7654930004fe7654930004fc76549300067f655493001e7c6554930006bf64549301f6bc6454930024fe768c9300067f658c9301ce7c658c930006bf648c9301c6bc648c930006ef628c93003eec628c930025fa708c930005f9708c930024fc764c9300057f754c9300e57c754c9300067f654c9301b67c654c930006bf644c9301aebc644c930006ef624c93003eec624c930005fb704c930025f8704c93000cfe76d85300067f65d85300067c65d85300ddbc74d8530006bf64d8530006bc64d85300d6f661d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530006bf74d8530014fe74d8530004fd74d8530014fc74d8530006bc74d8530014bc74d8530024fd73d853000cfc73d853003cfe72d8530004fd72d85300d6bf41d85300d6f631d85300d6f421d8530044fd70d85300d6f710d85300057f75585300e57c75585300067f65585300067c6558530005bf74585300ddbc7458530006bf6458530006bc6458530005ef7258530005ec72585300d6f46158530004ff7654530004fe7654530004fc76545300067f655453001e7c6554530006bf6454530186bc6454530006bf7650530005be7650530006be7650530004be7650530006bd7650530005bc7650530006bc7650530004bc7650530006bf65505300073f65505300063f655053017ebe6550530006bd655053017ebc65505300073c655053017e3c65505300079e73505300079d7350530006bf62505302a6bc62505300d5bf71505300dfb771505300d6bf615053000ebe615053000ebc61505302b7bb30505302579e30505300d7b71050530005de76cc530046de76cc5300475e75cc5300475d75cc5300075f65cc530176de65cc530176dc65cc5300075c65cc5301765c65cc530045df74cc53035ddd74cc5300079f64cc5303579c64cc530006df62cc5300d5dd71cc53000ede61cc53000edc61cc5300d79f41cc5300d79d41cc530025de70cc530025dc70cc530046df60cc530047db60cc530024fc764c5300067f654c5301667c654c530006bf644c53015ebc644c530006f7614c53000ef4614c530047d4314c530005fb704c530025f8704c530025dc764c53000edc764c530024dc764c5300075f654c530166de654
  | 15 => 0xc72d95300067f42d95300067e42d95300067d42d95300067c42d95303867f32d95303867c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300063f41d95300067e41d95300067d41d95300067c41d95303867f31d95300067e31d95303867c31d95300067e21d95300067c21d95303867f70d953029e7e70d95300067d70d953029e7c70d95300067f40d953029e7e40d95300067d40d953029e7c40d95303867f30d953029e7e30d953029e7c30d953029e7e20d953029e7c20d95300067f10d953029e7e10d953029e7c10d95300e67c6559530005bf74595300ddbc7459530006bc64595300e4ff75595300067f7559530004ff7459530006bf7459530004bf7459530014fe7459530004fd7459530014fc7459530006bc7459530014bc74595300fcff7359530006df7359530004ff725953003cfc7259530004ff715953000cfe715953000cfc7159530006bf4159530114ff7059530006fb70595300057e76195300e67e76195300047e76195300067f64195300067e64195300067d64195300067c64195300073c64195300063c641953037e7f63195300075e43195300075d43195300067e61195300067c61195300073f41195303767f60195303777b301953037f5e301953037f5c30195303777830195300ddbe76d91300debe76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91303679f73d91300df9c73d9130005bd71d9130006be61d9130006bc61d913036fbb30d91303679e30d91303679c30d913036fb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130366bf73d913036ebe73d91300debd73d913036ebc73d9130006bf53d913036ebe53d913036ebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006bc52d913036ebf32d913036ebc32d9130006bf71d9130006be71d9130006bd71d9130004bd71d9130006bc71d9130006bf51d9130006be51d9130006bc51d913036ebf31d9130006be31d913036ebc31d9130006be21d9130006bc21d913036ebf70d9130366be70d91300debd70d9130366bc70d9130006bf50d9130366be50d9130366bc50d913036ebf30d9130366be30d91300debd30d9130366bc30d9130366be20d9130366bc20d9130006bf10d9130366be10d9130366bc10d9130024fc7654d300067f6554d3001e7c6554d30006bf6454d30216bc6454d30005fb7054d30025f87054d300067f65d89300067c65d8930006bf64d8930006bc64d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d893000cfe71d8930004fd71d893000cfc71d8930006bf41d8930
  | 16 => 0x8a30014bc7458a30026ef7258a30006ef5258a30006ec5258a30006ee4258a30006ed4258a30004ff7158a3000cfe7158a3000cfc7158a30006bf4158a30024fc7058a30026ee2058a30026ec2058a3003cff7694a30024fe7694a30004fd7694a3001e7e6594a300067d6594a30004ff7654a30004fd7654a30024fc7654a302967f6554a3001e7c6554a30005df7354a30045dc7354a3003eee628ca30006ed628ca30025fa708ca30005f9708ca3003cff764ca300057f754ca300fd7c754ca3003eee624ca30006ed624ca30005fb704ca30025f8704ca30004ff75586300067f75586300047f755863001cfe755863001cfc75586300067c755863001c7c7558630004ff7458630014fe7458630004fd7458630014fc7458630004ff725863003cfc7258630026f771586300eebf41586300eef64158630006f541586300eef63158630024fc7058630026df3058630026dd3058630026f61058630026f41058630004ff7654630004fd7654630024fc765463001e7e65546300067d6554630006bf7650630256be7650630006bd7650630256bc7650630256bf655063017ebe6550630006bd6550630256bc65506300079f73506300079c73506300d6bd63506302a6be6250630006bd62506302adbf71506300f7b77150630256bf615063000ebe6150630257b6615063000eb661506300eebd6150630257b56150630006b5615063000ebc6150630256be60506302579f30506302b7bb3050630257b7105063000cff764c63000ef6614c630006f5614c630005fb704c630025f8704c63003cff76c8630024fe76c8630004fd76c863003eee62c8630006ed62c8630004ff7648630004fd7648630024fc76486300057f75486300fd7c7548630005df7348630045dc734863003eee6248630006ed624863001cfe76d95300e67e65d9530006bc64d9530004ff74d9530014fe74d9530004fd74d9530014fc74d95300e67f54d95300067e54d95300067d54d95300e67c54d9530044fe73d9530024fd73d9530044fc73d95300e67f53d953003cfe72d9530004fd72d95300e67f52d95300e67c52d953000cfe71d9530004fd71d953000cfc71d95300e67f51d95300067e51d95300e67c51d9530006bf41d9530044fd70d95300e67f50d95300e57e76d953001c7e76d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300075e43d95300075d43d95300067e61d95300067c61d95300073f41d95303877b30d953029f5e30d953029f5c30d95303877830d95300067f74d95300067e74d95300067d74d95300067c74d953029e7f73d95303867e73d95300067d73d95303867c73d95300067f43d95303867e43d95300067d43d95303867c43d95300067f72d95300067e72d95300067d72d95300067
  | 17 => 0x6df634c550046dc634c5501675f534c550004fe76c8550004fd76c855003cfc76c85503157f75c855001d7c75c8550006f761c855000ef461c8550004ff7648550004fe7648550004fc76485500057f754855001d7c75485500467f7559730004ff7459730014fe7459730004fd7459730014fc7459730024fc73597300467e53597300467c5359730004ff725973003cfc72597301167f5259730004ff715973000cfe715973000cfc71597300067e51597301167c5159730006bf41597301167f5059730004ff7558b300067f7558b300047f7558b3001cfe7558b3001cfc7558b300067c7558b3001c7c7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b30024fc7358b30046ef7258b30046ef3258b30046ec3258b30004ff7158b3000cfe7158b3000cfc7158b30006bf4158b30046df3158b3003cff7694b30044fe7694b30004fd7694b3039e7f6594b3001e7c6594b30004ff7654b30004fd7654b30044fc7654b3001e7e6554b300067d6554b30004ff755873001cfe755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc7458730024fc7358730004ff725873003cfc7258730046f77158730106bf4158730046f73158730046f43158730106f71058730004ff7654730004fd7654730044fc76547303967f655473001e7c6554730006bf76507302b6be7650730006bd76507302b6bc76507302b6bf655073017ebe6550730006bd65507302b6bc65507302b79e73507300079d73507302a6be6250730006bd6250730105bf715073010fb77150730106bf615073000ebe6150730106bd615073000ebc61507301079f3150730107b71050730045df764c7300bedf764c730166de654c730046dc654c73038ddf744c73038ddd744c730006dd624c730047d7714c730047d7614c73000ede614c73000edc614c730047d4614c7301079f414c7301079d414c730025de704c730025dc704c730107d7104c73003cff76c8730044fe76c8730004fd76c8730004ff7648730004fd7648730044fc76487300057f75487301157c754873001cff7654330044fc765433001e7e65543300067d6554330005df7354330045dc7354330027da30543300267f7559630004ff7459630014fe7459630004fd7459630014fc74596300fe7f54596300067d54596300fe7f5359630004ff725963003cfc72596300fe7c5259630004ff715963000cfe715963000cfc71596300fe7f5159630006bf4159630024fc70596300267e50596300267c505963001cff7654e30024fc7654e3001e7e6554e300067d6554e30005fb7054e30025f87054e30047db3054e30004ff7558a3001cfe7558a3001cfc7558a30004ff7458a30006bf7458a30004bf7458a30014fe7458a30004fd7458a30014fc7458a30006bc745
  | 18 => 0xc6154d503cf3f4154d500077b7054d500257e7054d500257c7054d50007787054d5001e7f6054d5001f7b6054d50024fd75d8950004ff74d8950014fe74d8950004fd74d8950014fc74d895009e7f54d89500067d54d8950044fe73d8950004fd73d895009e7f53d89500067d53d895009eee52d895009eed52d89503167c52d895000cfe71d8950004fd71d895000cfc71d895009e7f51d8950006bf41d89503c67e50d89503c67c50d8950006ef62989503176c5298950085f97098950005bf7458950125bc7458950005df7358950005dc73589500876c5258950005f7715895011df471589500b5fb705895003eee6218950006ed62189500247e76949503157f74949503bd7d74949500057d739495039e7c639495001d7e729495001f6e72949503167f62949500076f62949503176c62949500057d71949501fe7e61949501fe7c61949503b73f41949500257e70949503177a70949503177970949500257c709495001e7f609495001f7b6094950004fe76cc950004fd76cc950044fc76cc95001d7e75cc9500057d75cc950125be74cc950005bd74cc950004fe768c950004fd768c95003cfc768c9503157f758c95001d7c758c950006df638c950046dc638c950004ff764c950004fe764c950004fc764c9500057f754c95001d7c754c950004fe760c950004fd760c95003cfc760c95001d7e750c9500057d750c950006df630c950046dc630c95000cfe76d855011ef661d8550024fd75d855000cfc75d8550004ff74d8550014fe74d8550004fd74d8550014fc74d8550044fe73d8550004fd73d855003cfe72d8550004fd72d855011ef651d8550056f551d855011ebf41d855011ef421d855001cfd70d855011ef710d855011ef461585503adfb70585500257c765455000e7c76545500247c76545503a57f74545503a57d74545500057f73545503967c63545503157c72545500067f625455001d7f715455001f77715455000777615455000e7e615455000e7c615455011f74615455011f3f41545500077b70545500257e70545500257c705455000778705455001e7f605455001f7b6054550006bf7650550006be7650550006bd7650550006bc765055017f3e75505500073d7550550256bf6550550006bf63505502b6bc635055017f3f53505500073d5350550006bf62505502a6bc62505500073e525055017f3c525055011dbf7150550127b7715055011ebf615055000ebe615055000ebc615055011f3f515055011f3d5150550276bf605055017fbb50505502573e50505502573c505055017fb8505055011fb71050550004fe76cc550004fd76cc550044fc76cc55001d7e75cc5500057d75cc550006df63cc550046dc63cc5501775f53cc550004ff764c550004fe764c550004fc764c55001d7e754c5500057d754c550
  | 19 => 0x4a502957f7054a500077b7054a50297787054a5001e7e6054a5001f7a6054a50044ff76cca50024fe76cca50004fd76cca503857f75cca5001d7c75cca50135be74cca50005bd74cca5003eee62cca50006ed62cca5003cff768ca50024fe768ca50004fd768ca5001d7e758ca500057d758ca5003eee628ca50006ed628ca50004ff764ca50004fd764ca50024fc764ca500057f754ca5001d7c754ca5003eee624ca50006ed624ca5003cff760ca50024fe760ca50004fd760ca5001d7e750ca500057d750ca5003eee620ca50006ed620ca50004ff7458650014fe7458650004fd7458650014fc7458650004ff7358650044fc73586500067e53586500367c5358650004ff725865003cfc72586500367f52586500067d5258650026f7715865012e7e515865012ef65158650036f5515865012e7c515865012ebf415865012ef64158650006f5415865012ef63158650024fe7058650024fc70586500267f50586500267d5058650026f61058650026f41058650006bf7650650256be7650650006bd7650650256bc76506500073f755065017f3c755065011ebd65506502b6be6350650006bd63506500073e535065017f3c53506502a6be6250650257ae6250650006ae6250650006bd6250650257ad6250650006ad625065017f3f52506500073d52506502adbf7150650137b77150650256bf615065000ebe6150650257b6615065000eb6615065012ebd6150650257b56150650006b5615065000ebc615065012f3e515065012f3c5150650256be60506502573f505065017fbb5050650257b85050650257b71050650044ff76cc650024fe76cc650004fd76cc65001d7e75cc6500057d75cc650046de63cc650006dd63cc6503875c53cc650006ee62cc650006ed62cc650004ff764c650004fd764c650024fc764c6500057f754c65001d7c754c650046de634c650006dd634c6501675c534c650006ee624c650006ed624c65000ef6614c650006f5614c65003cff76c8650024fe76c8650004fd76c865001d7e75c86500057d75c865003eee62c8650006ed62c8650004ff7648650004fd7648650024fc76486500057f754865001d7c754865003eee6248650006ed6248650024fd75d8d50004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500fede53d8d500fedd53d8d50006df43d8d50006dc43d8d5003cfe72d8d50004fd72d8d5000cfe71d8d50004fd71d8d5000cfc71d8d50006bf41d8d5029e7f6598d50006df6398d500e5f97098d50005bf7458d50125bc7458d50115fb7058d5037e7f6518d50046de6318d50006dd6318d500247c7654d503d57f7454d503d57d7454d5001d7f7354d5001f5f7354d500075f6354d500467e6354d500467c6354d500075c6354d503157c7254d500057f7154d5020e7e6154d5020e7
  | 20 => 0x33e7e6294e5029f6e6294e5029f6d6294e5012d7e7194e5012d7c7194e503e73f4194e5029f7a7094e5029d7d7094e50387797094e50005797094e5001e7e6094e5001f7a6094e5003eef7598a5003eee7598a5003e6e7598a5003eec7598a5003eef7498a5003eee7498a5003eed7498a5003eec7498a500b6ef5498a500b6ee5498a500b6ed5498a500b6ec5498a5003eef7398a5003eee7398a5003eed7398a5003eec7398a500b6ef5398a500b6ee5398a500066e5398a500b6ed5398a500b6ec5398a500b66c5398a50006ef4398a50006ee4398a50006ed4398a50006ec4398a5003eef7198a5003eee7198a5003eed7198a5003eec7198a500b6ef5198a500b6ee5198a500066e5198a500b6ed5198a500b6ec5198a500b66c5198a50006ef4198a50006af4198a50006ee4198a50006ed4198a50006ec4198a50006ee3198a50006ec3198a50026ef7098a50026ee7098a50026ed7098a50026ec7098a50026ef5098a500266f5098a50026ee5098a50026ed5098a500266d5098a50026ec5098a50026ef4098a50026ee4098a50026ed4098a50026ec4098a50026ef3098a50026ee3098a50026ed3098a50026ec3098a50026ef1098a50026ee1098a50026ed1098a50026ec1098a50004ff7458a50014fe7458a50004fd7458a50014fc7458a50004ff7358a50044fc7358a50026ef7258a50086ee5258a50086ed5258a50006ef4258a50006ee4258a50006ed4258a50006ec4258a50004ff7158a5000cfe7158a5000cfc7158a50006bf4158a50006ee2158a50006ec2158a50024fc7058a50026ee2058a50026ec2058a50086ee7558a50086ed7558a50086ec7558a50006ef7458a50006ee7458a50006ed7458a50006ec7458a50086ef5458a50086ee5458a50086ed5458a50086ec5458a50006ef7358a50006ee7358a50006ed7358a50006ec7358a50086ef5358a50086ee5358a50086ed5358a50086ec5358a50006ef4358a50006ee4358a50006ed4358a50006ec4358a50006ef7158a50006ee7158a50006ed7158a50006ec7158a50086ef5158a50086ee5158a50086ed5158a50086ec5158a50006ef4158a50006af4158a50006ee4158a50006ed4158a50006ec4158a50006ee3158a50006ec3158a50026ef7058a50026ee7058a50026ec7058a50026ef5058a50026ee5058a50026ed5058a50026ec5058a50026ef4058a50026ee4058a50026ed4058a50026ec4058a50026ef3058a50026ee3058a50026ed3058a50026ec3058a50026ef1058a50026ee1058a50026ed1058a50026ec1058a5003c7f7654a502967f6454a503de7d6454a503857c7354a500067d6354a5001d7f7254a5001f6f7254a5003e7e6254a502976e6254a5003e6e6254a502976d6254a5003e7c6254a5012d7e7154a5012d7c7154a503df3f415
  | 21 => 0xe21195213ef6c21195213ef742119521044fe76d8d210067f65d8d210067c65d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d21006de43d8d21006dd43d8d2103cff71d8d2103cfd71d8d211bebf41d8d211bebd41d8d211bedf31d8d211bedd31d8d21024fe70d8d21004fd70d8d211457e7598d210057d7598d210067f6598d210067c6598d2113dbe7498d21005bd7498d21006df6398d211a5ed7298d210057f7558d211457c7558d210067f6558d210067c6558d211d5ef7258d21004ff7558d210067f7558d210047f7558d2101cfe7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d21006df7358d211d4ff7258d21006ef7258d211a4ff7158d21006f77158d211a6bf4158d211a6bd4158d21004ff7058d21024fc7058d211bcfe7618d210067f6518d210067c6518d21046de6318d21006dd6318d21044ff7694d21004fe7694d21004fd7694d21044fc7694d210067f6594d2101e7c6594d211475f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2101e7c6554d2101cff765492100cfe76549211ecfd765492100cfc76549210067f655492101e7c6554921005f7715492100df4715492103fe4215492100cfe76cc92100cfc76cc9210067f65cc9211e67c65cc92113dbe74cc921005bd74cc921006df63cc921046dc63cc92100df671cc921005f571cc921044ff764c92100cfe764c9211a4fd764c92100cfc764c9210057f754c9211457c754c9210067f654c9211b67c654c921006df634c921046dc634c921005f7714c92100df4714c9210067f65d81210067c65d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d8121044fe73d8121004fd73d812103cfd71d81210a6bf41d81210a6bd41d81210a6fa10d81211457e75981210057d75981210067f65981210067c6598121006fb60981210057f75581211457c75581210067f65581210067c6558121005bf745812113dbc7458121005df7358121005dc73581210067f65181210067c6518121026fa6018121006f96018121004ff7458e50014fe7458e50004fd7458e50014fc7458e50026df7358e500e6de5358e500e6dd5358e503867c5358e50006de4358e50006dd4358e50004ff7258e5003cfc7258e500e67f5258e50004ff7158e5000cfe7158e5000cfc7158e500067e5158e500e67c5158e50006bf4158e50024fc7058e500267f5058e500267d5058e50026de3058e50026dc3058e5029e7f6494e503e67d6494e5001d7e7394e5001f5e7394e5029e7f6394e5029f5e6394e503867d6394e5029f5d6394e500065d6394e500057d7294e50
  | 22 => 0x8f21004fd7458f21014fc7458f2103edf7358f2100cfe7258f2100cfc7258f2103ede3258f2103edc3258f211a6bf4158f211a6bd4158f211a6df3158f211a6dd3158f21004ff7058f21024fc7058f2103eef2058f21044ff7694f2103cfe7694f21004fd7694f2103cfc7694f2133e7f6594f2101e7c6594f211575f5394f2100df67194f21005f57194f21004ff7654f2103cfe7654f21004fd7654f2103cfc7654f2101e7e6554f210067d6554f21004ff755832101cfe755832101cfc7558321004ff7458321006bf7458321004bf7458321014fe7458321004fd7458321014fc7458321006bc7458321014bc7458321004ff7358321044fc735832100cfc7258321076bf4158321076bd415832103efb705832103efb205832103ef82058321076fa105832101cfe76d95211467e65d9521004ff74d9521014fe74d9521004fd74d9521014fc74d95211467f54d95210067e54d95210067d54d95211467c54d9521044fe73d9521004fd73d95211467f53d95211467c53d952100cfd72d95211467f52d952103cff71d952103cfd71d95211fe7f51d95211fe7d51d95211febf41d95211febd41d9521024fe70d9521004fd70d95211467f50d95211467c50d95213ed7e76d952101c7e76d95210067f64d95210067e64d95210067d64d95210067c64d95211ff3f41d95211ff3d41d95214077721d95211ff6e21d95211ff6c21d95211ff7421d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95211fe7f72d95214067e72d95211fe7d72d95211fe7c72d95210067f42d95214067e42d95210067d42d95214067c42d95214067e32d95214067c32d95211fe7f71d95211fe7e71d95211fe7d71d95211fe7c71d95211fe7f41d95211fe3f41d95211fe7e41d95211fe7d41d95211fe3d41d95211fe7c41d95211fe7f31d95211fe7e31d95211fe7d31d95211fe7c31d95211fe7f21d95211fe7e21d95211fe7c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95214067f20d95214067c20d95211fe7f10d95211fe7e10d95211fe7d10d95211fe7c10d95211467c65595213fdef72595211fcff75595210067f7559521004ff7459521014fe7459521004fd7459521014fc7459521004ff7359521044fc73595213fcff7259521006ef72595211ecff7159521006f771595211eebf41595211eebd4159521004ff7059521024fc70595211fd7e76195211467e76195211fc7e76195210067f64195210067e64195210067d64195210067c64195213ee7f62195213ee7f61195213ef3f41195213ef3d41195213f77721195213ef6
  | 23 => 0x20cfd7654d3100cfc7654d310067f6554d3101e7c6554d3140ddf7354d310475c5354d31005f77154d3100df47154d31047d43154d3103cfe76d893115dbe74d8931005bd74d893101cfe75d8931004fd75d893101cfc75d8931004ff74d8931014fe74d8931006be74d8931014be74d8931004fd74d8931006bd74d8931004bd74d8931014fc74d8931006ef52d8931006ec52d8931006ee42d8931006ed42d8931044fd71d89311d6bf41d89311d6bd41d89311d6ef21d8931024fe70d8931004fd70d8931006ef62989310057f75589311657c75589311657e75189310057d751893103eee6218931006ed6218931004fe7694931004fd769493103cfc76949310067f659493101e7c6594931045de7394931005dd73949311675c5394931004ff7654931004fe7654931004fc765493101e7e65549310067d6554931005df7354931045dc73549311675f5354931005f7715493100df4715493118dde76cc931046de76cc931165de75cc931045dc75cc9310479e74cc9310479d74cc93103ede62cc93103edc62cc93100dde71cc93100ddc71cc931046df61cc931047d761cc9311d79f41cc9311d79d41cc931005dd70cc9311d7d710cc93100cfe768c9311a5dd738c931006ef628c93103eec628c93100df6718c931005f5718c931047d4318c93100cfc764c9310057f754c9311657c754c931006ef624c93103eec624c931005f7714c93100df4714c93100ddc764c93103edc764c93100cdc764c9310075f754c931165de754c931165dc754c9310075c754c9311655c754c931045df724c931047cf724c931007cf624c93103ede624c93103edc624c931007cc624c931007d7714c93100dde714c93100ddc714c9311a7d4714c93100dd4714c931046df614c931047d7614c9311a79f414c9311a79d414c931005df704c9311a7d7104c93101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d813103cfe72d8131004fd72d8131044fd71d8131106bf41d8131106bd41d8131106fa10d8131006fb60981310057f75581311657c7558131005bf745813115dbc7458131005ef7258131005ec72581311657e75181310057d751813115dbe7418131005bd7418131005ee7218131005ed7218131026fa6018131006f9601813103e7f7559721004ff7459721014fe7459721004fd7459721014fc74597211567f54597210067d5459721004ff7359721044fc73597211567f535972100cfe725972100cfc725972103e7e525972103e7c52597211ee7f51597211ee7d51597211eebf41597211eebd4159721004ff7059721024fc70597211567c5059721004ff7558f210067f7558f210047f7558f2101cfe7558f2101cfc7558f210067c7558f2101c7c7558f21004ff7458f21014fe745
  | 24 => 0xe715973120e7d715973120e7c715973120e7f415973120e3f415973120e7e415973120e7d415973120e3d415973120e7c41597310467f31597310467e31597310467d31597310467c315973120e7f215973120e7e215973120e7d215973120e7c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067d40597310067c40597310467f30597310467e30597310467d30597310467c305973120e7f105973120e7e105973120e7d105973120e7c1059731004ff7558b3101cfe7558b3101cfc7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b3100cfc7358b31046ef7258b31006ef4258b31006ec4258b31046ef3258b31046ec3258b311a6bf4158b311a6bd4158b311a6ef2158b31004ff7058b31024fc7058b3103cff7694b31044fe7694b31004fd7694b3101e7e6594b310067d6594b31045de7394b31005dd7394b3139f5c5394b31004ff7654b31004fd7654b31044fc7654b3101e7e6554b310067d6554b31005df7354b31045dc7354b311775f5354b31045df764cb31006df764cb310075f754cb31175de754cb31175dc754cb310075c754cb311755c754cb310475e654cb310475d654cb31047cf724cb3103ede624cb3103edc624cb3100dde714cb3100ddc714cb311a79f414cb311a79d414cb31005df704cb31004ff755833101cfe755833101cfc7558331004ff7458331006bf7458331004bf7458331014fe7458331004fd7458331014fc7458331006bc7458331014bc745833100cfc7358331004ff725833103cfc72583310d6bf41583310d6bd4158331046f63158331046f53158331046fb7058331046fb3058331046f830583310d6fa105833101cfe76d95311667e65d9531045de73d953100ddd73d95311675f53d9531004ff74d9531014fe74d9531004fd74d9531014fc74d95311667f54d95310067d54d953100cfd73d953121edd73d953100cdd73d95311667f53d9531166df53d95311665f53d9531166dc53d953103cfe72d9531004fd72d95311667c52d9531044ff71d9531044fd71d953121e7f51d953121e7d51d953121ebf41d953121ebd41d9531024fe70d9531004fd70d95311667c50d95311667c655953140ddf73595311675c5359531005ef7259531005ec725953121cff75595310067f7559531004ff7459531014fe7459531004fd7459531014fc745953140cff7359531006df7359531166df53595313967e53595313967c5359531166dc5359531004ff7259531006ef7259531004ef725953103cfc7259531006ec725953103cec72595311667f525953120cff7159531006f7715953120e7e515953120e7c515953120ebf415953120ebd4159531004ff7059531024fc70595311667f505953101cff7654d3100cfe7654d31
  | 25 => 0xc9412a7b5710c941005b5710c94100dbc710c94118ebf610c941197b7610c941255be700c941005bd700c94118fb7100c94117dbe75d8141005bd75d814117dbc75d81412b5be73d8141005bd73d8141006bf63d8141006bd63d81412a5be72d8141005bd72d8141015bf71d814143fb771d8141015bd71d8141426bf61d814143fb761d8141427b710d8141427ba10d8141427b910d814142dbd769814117dbe7598141005bd7598141255bc75981412b5be7398141005bd7398141006be6398141006bc63981412a5be7298141005bd7298141006be6298141006bc6298141435bd7198141257b5719814102db571981412aebf619814104fb76198141255be7098141256bf6098141007bb6098141257b71098141005bf75581410073f75581410053f755814117dbe755814117dbc75581410073c755814117d3c7558141005bf73581410079f73581410059f73581412b5bc73581410079c73581410059c7358141006bf6358141006bd6358141005bf7258141007af7258141005af72581412a5bc7258141007ac7258141005ac725814142dbf7158141007b7715814104db7715814142ebf615814102fb76158141007bb6058141256be605814142fb71058141425be761814117dbe75181412573e751814117d3e7518141005bd75181412573d75181410053d7518141255bc75181412b5be73181412579e73181410059e7318141005bd73181412579d73181410059d7318141006be6318141006bc63181412a5be7218141257ae7218141005ae7218141005bd7218141257ad7218141005ad7218141006be6218141006bc6218141015bf711814100dbe7118141015bd7118141257b5711814100dbc71181412aebf611814141fb76118141255be7018141256bf6018141257ba6018141256bd6018141007b96018141257b71018141257ba1018141417b910181410467f7559731004ff7459731014fe7459731004fd7459731014fc74597311767f54597310067e54597310067d54597311767c545973100cfe735973100cfc7359731046dc735973100cdc7359731176df53597310467e53597310467c5359731046dc5359731004ff725973103cfc72597311767f52597311767c525973120e7f515973120e7d515973120ebf415973120ebd4159731004ff7059731024fc70597311767f50597311767c50597310067f74597310067e74597310067d74597310067c74597310467f73597311765f73597310467e73597310467d73597310467c73597310465c73597310467f43597310467e43597310467d43597310467c43597310067f72597310067e72597310067d72597310067c72597310067f42597310067e42597310067d42597310067c42597310467f32597310467e32597310467d32597310467c325973120e7f715973120e7
  | 26 => 0x2a6bf62189412a7ae62189412a6bd6218941007ad6218941007af52189412a7ac5218941015bf711894100dbe7118941015bd711894100dbc7118941446bf611894144fb76118941447af2118941447ad2118941255be7018941005bd7018941447b710189412a5bf7694941005be7694941005bd76949412a5bc76949411edbd75949410073f659494117f3c65949412b5be7394941005bd73949410073e539494117f3c53949413edbe72949412a73f529494117faf52949412a7ac52949411fdbf719494100dbe71949411fdbd719494100dbc71949411febf6194941207b761949411ff3e51949411ff3c5194941255be7094941005bd709494117f3f50949411ffb71094941005bf7654941005be7654941005bd7654941005bc76549411fdbf755494117f3e65549410073d6554941005bf73549412b5bc735494117f3f53549410073d53549413fdbf725494117faf52549412a73e52549412a73c525494117fac52549411edbf7154941007b77154941005b7715494100dbe715494100dbc71549411efb4715494100db471549411eebf61549411f7b761549411ef3f51549411ef3d5154941005bf7054941255bc705494117f3c50549411efb710549412b5bf76cc941005be76cc9412b6be76cc941004be76cc941005bd76cc9412b6bd76cc941004bd76cc9412b5bc76cc9412b5bf75cc94117dbe75cc941005bd75cc9412b5bc75cc9411d5bf71cc94100dbe71cc9411d5bd71cc94100dbc71cc9411d6bf61cc9411dfb761cc9411d79f31cc941255be70cc941005bd70cc9411d7b710cc9412a5bf768c941005be768c941005bd768c9412a5bc768c9412a5bf758c94117dbe758c941005bd758c9412a5bc758c9411a5bd738c94118dbe728c941007af628c9412a7ac628c9412a79f328c9412b7af328c9411bdbf718c94100dbe718c9411bdbd718c94100dbc718c9411bebf618c9411c7b7618c941255be708c941005bd708c9411bfb7108c941005bf764c941005be764c941005bd764c941005bc764c941005bf754c9410073f754c9410053f754c94117dbe754c941005bd754c94117dbc754c9410073c754c94117d3c754c941007af624c941007ac624c9412b7af324c9412a79e324c9411a5bf714c941007b7714c941005b7714c94100dbe714c94100dbc714c9411a7b4714c94100db4714c9411a6bf614c9411afb7614c941005bf704c941255bc704c9411a7b7104c9412a5bf760c941005be760c941005bd760c9412a5bc760c9412a5bf750c94117dbe750c9412a73e750c94117d3e750c941005bd750c9412a73d750c9410053d750c9412a5bc750c9411d5be730c9411bdbe720c9412a79f320c9412a7ae320c9412a79d320c9412b7ad320c94118dbf710c94100dbe710c94118fb6710c94100db6710c94118dbd710
  | 27 => 0xd7298d4148dbd7198d412b7b57198d4115db57198d4148ebf6198d4116fb76198d41255be7098d41005bd7098d4148fb71098d41005bf7558d4117dbe7558d4117dbc7558d410079f6358d412b6be6358d41005bf7258d412a5bc7258d4149dbf7158d41007b77158d4116db77158d4149ebf6158d4115fb76158d41005bf7058d41255bc7058d4149fb71058d41495be7618d4117dbe7518d41005bd7518d412b5bc7518d4148dbe7318d412b6bf6318d412b79e6318d412b6bd6318d410079d6318d410069d6318d412a5be7218d41005bd7218d41015bf7118d4100dbe7118d41015bd7118d4100dbc7118d4147ebf6118d41487b76118d4147f9f3118d4147f9d3118d41255be7018d41005bd7018d4147fb71018d412b5bf7694d41005be7694d41005bd7694d412b5bc7694d4120dbd7594d4117f3e6594d410073d6594d41475be7394d412b73f5394d4117f9f5394d4117f1f5394d412b79c5394d412a5be7294d41005bd7294d4117f3c5294d4121dbf7194d4100dbe7194d4121fb67194d4100db67194d4121dbd7194d412b7b57194d41005b57194d4100dbc7194d4121ebf6194d41227b76194d4121f3f5194d4121f3d5194d41255be7094d41005bd7094d4117f3c5094d4121fb71094d41005bf7654d41005be7654d41005bd7654d41005bc7654d4121dbf7554d410073f6554d4117f3c6554d4140dbf7354d4117f9f5354d412b73e5354d412b73c5354d4117f9c5354d41005bf7254d412a5bc7254d4117f3f5254d4120dbf7154d4100dbe7154d4100dbc7154d4120ebf6154d41217b76154d4120f3e5154d4120f3c5154d41005bf7054d41255bc7054d4117f3f5054d4120fb71054d4117dbe75d8941005bd75d894117dbc75d89412b5be73d8941005bd73d8941007af52d8941007ac52d8941015bf71d8941015bd71d894145ebf61d894146fb761d894145faf21d894145fad21d8941255be70d8941005bd70d894145fb710d8941465bd769894117dbe7598941005bd75989412a5bc75989412b5be7398941005bd7398941006bf6398941006bd6398941445be72989412a6bf6298941007af6298941455bd71989412a7b5719894113db57198941456bf619894114fb76198941255be7098941005bd7098941457b71098941005bf75589410073f75589410053f755894117dbe755894117dbc75589410073c755894117d3c7558941005bf73589412b5bc7358941007af62589412a6be6258941465bf7158941007b7715894114db77158941466bf615894113fb76158941005bf7058941255bc7058941467b7105894145dbe761894117dbe75189412a73e751894117d3e7518941005bd75189412a73d75189410053d75189412a5bc75189412b5be7318941005bd7318941006bf6318941006bd6318941455be7218941
  | 28 => 0x8951006ef42d8951006ec42d895101cfd71d89513febf41d89513febd41d89513feef21d8951024fe70d8951004fd70d89511fe7f6598951006ef6298951145f57198951155f771589513ee7f651895103eee6218951006ed621895100d7c765495103e7c765495100c7c76549514de7f64549514de7d64549513957c73549510067f635495101d7f725495101f6f72549510076f625495103e7e625495103e7c62549510076c625495100777715495100d7e715495100d7c71549511ef74715495101e7f615495101f7761549511ef3f41549510057f70549512967c6054951004fe76cc951004fd76cc951044fc76cc9513957f75cc95101d7c75cc951185be74cc951005bd74cc951006ef62cc95103eec62cc951004fe768c951004fd768c95103cfc768c95101d7e758c9510057d758c951004ff764c951004fe764c951004fc764c9510057f754c95101d7c754c951004fe760c951004fd760c95103cfc760c95101d7e750c9510057d750c951006ef620c95103eec620c951024fe76d815100cfd75d8151004ff74d8151014fe74d8151004fd74d8151014fc74d8151044fe73d8151004fd73d815103cfe72d8151004fd72d815101cfd71d8151276bf41d8151276bd41d81513aefa50d8151276fa10d815127e7f6598151005ee7298151005ed7298151006fb609815127e7f6518151026fa6018151006f960181514d5be76d95414adbd75d954117ebe65d954117f3e65d954117e3e65d954117ebc65d95412b5be73d9541005bd73d954117f3f53d95412a5be72d9541005bd72d954117f3c52d9541015bf71d954100dbe71d9541015bd71d954100dbc71d95414bebf61d95414cfb761d95414bf3f51d95414bf3d51d9541255be70d9541005bd70d954117f3c50d95414bfb710d95414c5bf76595414bdbf75595410073f655954117ebe655954117ebc655954117f3c6559541005bf73595412b5bc735954117f3c5359541005bf7259541007af7259541005af72595412a5bc7259541007ac7259541005ac725954117f3f52595414adbf7159541007b771595414b5b771595414aebf6159541187b761595414af3e51595414af3c5159541005bf7059541255bc705954117f3f50595414afb7105954117dbe75d8d410073e75d8d4117d3e75d8d41005bd75d8d410073d75d8d410053d75d8d4117dbc75d8d412a5be72d8d41005bd72d8d41015bf71d8d41015bd71d8d41496bf61d8d414a7b761d8d414979f31d8d414979d31d8d41255be70d8d41005bd70d8d41497b710d8d4149dbd7698d4117dbe7598d412b73e7598d4117d3e7598d41005bd7598d412b73d7598d410053d7598d412b5bc7598d4147dbe7398d412b6bf6398d410079f6398d412a5be7298d412b7ae7298d41005ae7298d41005bd7298d412b7ad7298d41005a
  | 29 => 0x4ff7059432024fc705943219e7f505943219e7c50594320067f74594320067e74594320067d74594320067c74594320467f73594320467e73594320467d73594320467c73594320467f43594320467e43594320467d43594320467c435943203e7f725943203e7e725943203e7d725943203e7c725943203e7f425943203e7e425943203e7d425943203e7c425943203e7f325943203e7e325943203e7d325943203e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320063f41594320067e41594320067d41594320067c41594320467f31594320467e31594320467d31594320467c315943203e7f215943203e7e215943203e7d215943203e7c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067d40594320067c40594320467f30594320467e30594320467d30594320467c305943203e7f205943203e7e205943203e7d205943203e7c20594320067f10594320067c1059432004ff755843201cfe755843201cfc7558432004ff7458432014fe7458432004fd7458432014fc745843203edf325843203edd325843203cff715843203ef7715843218ebf415843218ef64158432006f54158432046f73158432046f4315843203ef7215843203ef42158432004ff7058432024fc705843218ef71058432004ff755803201cfe755803201cfc7558032004ff7458032006bf7458032004bf7458032014fe7458032004fd7458032014fc7458032006bc7458032014bc745803203eee3258032046ed3258032004ff715803200cfe715803200cfc7158032006bf415803203efb7058032006fa4058032006f94058032046fb3058032046f8305803203efb205803203ef82058032044fe76d8d5100cfd75d8d5140e7d75d8d51004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d514f6de53d8d514f6dd53d8d513967c53d8d5103cfe72d8d51004fd72d8d514f67f52d8d5101cfd71d8d5140e7e51d8d5140e7c51d8d5140ebf41d8d5140ebd41d8d5140edf31d8d51024fe70d8d51004fd70d8d514f67f50d8d51006df6398d513975c5398d51165f57198d511675c5358d51005ef7258d51005ec7258d51175f77158d51046de6318d51006dd6318d5100d7e7694d5121e7e7694d5100c7e7694d514ee7f6494d514ee7d6494d5101d7e7394d5101f5e7394d513967f6394d510075f6394d510065f6394d513975c6394d510057d7294d5133e7c6294d5100d7e7194d5121f767194d51397757194d5100d7c7194d5101e7f6194d5101f776194d5121f3f4194d510057d7094d5129e7c6094d5103cfe76d895100cfd75d8951004ff74d8951014fe74d8951004fd74d8951014fc74d8951044fe73d8951004fd73d89514e6ee52d89514e6ed52d
  | 30 => 0xe43d95320067d43d953239e7c43d953239e7f72d953233e7e72d95320067d72d953233e7c72d95320067f42d953233e7e42d95320067d42d953233e7c42d953239e7f32d953233e7e32d953233e7c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320063f41d95320067e41d95320067d41d95320067c41d953239e7f31d95320067e31d953239e7c31d953233e7f21d95320067e21d953233e7c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d953239e7f30d953239e7c30d953233e7f20d953233e7c20d95320067f10d95320067c10d95321b67c65595321b4ff75595320067f7559532004ff7459532014fe7459532004fd7459532014fc74595321ccff7359532006df73595321e4ff7259532006ef7259532004ff715953200cfe715953200cfc7159532006bf4159532004ff7059532024fc70595320057e76195321b67e76195320047e76195320067f64195320067e64195320067d64195320067c64195325067f63195324fe7f62195324ff6f32195325075e32195325075c32195324ff6c32195320067e61195320067c61195320073f411953203cfc7654d320067f6554d3201e7c6554d32005ef7254d3203dec7254d32047cc3254d3201cff76549321b4fd7654932044fc76549320067f655493201e7c6554932005df7354932045dc735493203fcc325493200cfe76d85320067f65d85320067c65d85321a6f661d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d853203cfd73d8532044fd72d85321a6bf41d85321a6f641d8532006f541d85321a6f631d85321a6f621d8532024fe70d8532004fd70d85321a6f410d85320057f75585321b57c75585320067f65585320067c65585321a6f461585320067f65d81320067c65d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d813200cfe71d8132004fd71d813200cfc71d8132006bf41d81321b57e75981320057d75981320067f65981320067c6598132006fb60981320057f75581321b57c75581320067f65581320067c6558132005bf74581321adbc7458132005f771581321a5f471581320067f65181320067c6518132026fa6018132006f9601813203cff755943203e7f7559432004ff7459432014fe7459432004fd7459432014fc745943219e7f54594320067e54594320067d545943219e7c5459432044fe7359432044fc73594320467e53594320467c535943203cfe725943203cfc725943203e7e525943203e7c5259432004ff715943200cfe715943200cfc715943219e7f51594320067e515943219e7c5159432006bf4159432
  | 31 => 0x9332046bf3059332046be3059332046bd3059332046bc305933250ebf205933250ebc2059332006bf1059332006bc105933201cff7654b32044fc7654b3201e7e6554b320067d6554b321f6be6454b32006bd6454b32005df7354b32045dc7354b3203fce3254b32004ff755873201cfe755873201cfc7558732004ff7458732014fe7458732006be7458732014be7458732004fd7458732006bd7458732014fc745873203cfc7358732046f77158732006f751587321d6f451587321d6bf4158732046f73158732046f431587321d6f62158732004ff7058732024fc70587321d6f71058732004ff75583320067f75583320047f755833201cfe755833201cfc75583320067c755833201c7c7558332004ff7458332014fe7458332004fd7458332014fc745833203cfc7358332046ee3258332046ed3258332004ff715833200cfe715833200cfc7158332006bf4158332046df3158332046fb7058332046fb3058332046f8305833203e7f7559632004ff7459632014fe7459632004fd7459632014fc74596321ce7f54596320067d54596321ce7f535963203cfc725963203e7e525963203e7c5259632004ff715963200cfe715963200cfc71596321ce7f5159632006bf4159632004ff7059632024fc70596321ce7c505963201cff7654e3203cfc7654e3201e7e6554e320067d6554e32005ef7254e3203dec7254e32047cf3254e32004ff75586320067f75586320047f755863201cfe755863201cfc75586320067c755863201c7c7558632004ff7458632014fe7458632004fd7458632014fc745863203cfc725863203edf325863203edd325863203ef771586321bebf41586321bef6315863203ef7215863203ef42158632004ff7058632024fc705863203eef2058632004ff755823201cfe755823201cfc7558232004ff7458232014fe7458232004fd7458232014fc745823203cfc7258232004ff715823200cfe715823200cfc7158232006bf415823203efb705823203efb205823203ef8205823201cfe76d95321b67e65d9532004ff74d9532014fe74d9532004fd74d9532014fc74d95321b67f54d95320067e54d95320067d54d95321b67c54d953203cfd73d95321b67f53d9532044fd72d95321b67f52d953200cfe71d9532004fd71d953200cfc71d95321b67f51d95320067e51d95321b67c51d9532006bf41d9532024fe70d9532004fd70d95321b67f50d95321b67c50d95321b57e76d953201c7e76d95320067f64d95320067e64d95320067d64d95320067c64d953239f6f32d953233f5e32d953233f5c32d953239f6c32d95320067e61d95320067c61d95320073f41d95320067f74d95320067e74d95320067d74d95320067c74d953233e7f73d953239e7e73d95320067d73d953239e7c73d95320067f43d953239e7
  | 32 => 0x44fc735825203cfc7258252086ef525825203eec5258252004ff715825200cfe715825200cfc7158252006bf415825203efb7058252086fa505825203efb205825203ef8205825203cfd75d8d52004ff74d8d52014fe74d8d52004fd74d8d52014fc74d8d521cede53d8d521cedd53d8d52006de43d8d52006dd43d8d5200cfe71d8d52004fd71d8d5200cfc71d8d52006bf41d8d52024fe70d8d52004fd70d8d5233e7f6598d521f5be7498d52005bd7498d52006df6398d521b5ed7298d521edf67198d52005f57198d521e5ef7258d525067f6518d52046de6318d52006dd6318d5203c7c7654d525257f7454d525257d7454d5201d7f7354d5201f5f7354d520075f6354d520467e6354d520467c6354d520075c6354d520076f7254d5203d7e7254d5203d7c7254d520076c7254d5201e7f6254d5201f6f6254d520057f7154d5220e7e6154d5220e7c6154d5251f3f4154d522957c7054d5200cfe76d85521eef661d855203cfd75d8552004ff74d8552014fe74d8552004fd74d8552014fc74d8552044fe73d8552004fd73d855201cfd72d85521eef651d85521eebf41d85521eef641d8552006f541d85521eef631d85521eef621d8552024fe70d8552004fd70d85521eef410d85521eef4615855203cfd75d8152004ff74d8152014fe74d8152004fd74d8152014fc74d81520b67f54d81520067d54d8152044fe73d8152004fd73d81520b67f53d81520067d53d81520b6ef52d81525167e52d81525167c52d81520b6ec52d815200cfe71d8152004fd71d815200cfc71d81520b67f51d8152006bf41d81520b6fa50d81522967c50d8152006fb6098152005bf74581521f5bc7458152005df7358152005dc7358152005f771581521edf47158152026fa6018152006f960181520467f7559732004ff7459732014fe7459732004fd7459732014fc745973203cfc73597320467e53597320467c53597321e67f5259732004ff715973200cfe715973200cfc71597320067e51597321e67c5159732006bf4159732004ff7059732024fc70597321e67f5059732006bf7559332006be7559332006bd7559332006bc7559332046bf7359332046be7359332046bd7359332046bc7359332046bf5359332046be5359332046bd5359332046bc53593321debf725933250ebe7259332006bd725933250ebc7259332006bf525933250ebe525933250ebc5259332046bf3259332046be3259332046bd3259332046bc3259332006bf7159332004bf7159332006be7159332006bd7159332006bc7159332006bf5159332006be5159332006bc5159332046bf3159332046be3159332046bd3159332046bc315933250ebf2159332006be215933250ebc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006bc505
  | 33 => 0xc7258653046f7715865321ef6515865321ebf415865321ef64158653006f54158653046f73158653046f4315865321ef42158653004ff7058653024fc705865321ef71058653004ff7458253014fe7458253004fd7458253014fc74582530e67f54582530067d5458253044fc73582530467f53582530467d5358253004ff725825303cfc72582530e67c5258253004ff715825300cfe715825300cfc71582530e67f5158253006bf4158253046fb70582530e6fa505825329e7c5058253046fb3058253046f83058253044fd75d8953004ff74d8953014fe74d8953004fd74d8953014fc74d89531e6ee52d895300cfe71d8953004fd71d895300cfc71d8953006bf41d8953006ee21d8953006ec21d8953024fe70d8953004fd70d8953006ef629895333e7f651895303eee6218953006ed621895300cfe76d855301d7e75d855320ef661d855320f7651d8553044fd75d85530447d75d8553004ff74d8553014fe74d8553004fd74d8553014fc74d855301cfd73d8553176df53d85535367e53d85535367c53d8553176dc53d855303cfe72d8553004fd72d85531767f52d855320e7e51d855320ef651d855320e7c51d855320ebf41d855320ef631d8553024fe70d8553004fd70d85531767f50d8553005ef7258553005ec725855320ef46158553044fd75d8153004ff74d8153014fe74d8153004fd74d8153014fc74d815303cfe72d8153004fd72d815300cfe71d8153004fd71d815300cfc71d8153006bf41d8153116fa50d8153005ee7298153005ed7298153006fb6098153005bf7458153215bc745815329e7f6518153026fa6018153006f96018153004ff7458e52014fe7458e52004fd7458e52014fc7458e5203edf7358e521b6de5358e521b6dd5358e5239e7c5358e5203cfc7258e5203e7f5258e5203e7d5258e5203ede3258e5203edc3258e52004ff7158e5200cfe7158e5200cfc7158e520067e5158e521b67c5158e52006bf4158e52004ff7058e52024fc7058e521b67f5058e5233e7f6494e5252e7d6494e5201d7e7394e5201f5e7394e5233e7f6394e5233f5e6394e5239e7d6394e5233f5d6394e520065d6394e5233f6e7294e5233d7d7294e5239f6d7294e520056d7294e5201e7e6294e5201f6e6294e521fd7e7194e521fd7c7194e5252f3f4194e520057d7094e5229e7e6094e52004ff7458652014fe7458652004fd7458652014fc7458652004ff7358652044fc73586520067e53586521467c535865203cfe725865203cfc725865203e7f525865203e7d525865203ef771586521fe7e51586521fef651586521fe7651586521fe7c51586521febf415865203ef7215865203ef42158652004ff7058652024fc70586521467f5058652004ff7458252014fe7458252004fd7458252014fc7458252004ff7358252
  | 34 => 0x180090000001000c003000c0030004001000c008001000b0000000000400000000020004000000c00f0010009000400000000000000001000000500140000014000000000000100040020005000400400080000000002002400200000070024000000800200040030004003000800000000030000001000000c00040050018000000000100380000004004000c0000000015000000000000060024007000c0000004005000400100100010048002000800000040000008001003400000080000008003000000400040000000001002c00300000020000001001400900180050000000000c0000010000000000700200000018001000c00100180050000000002c00700000000044000000400500000020000000000800000040000000001000c002000000000080020008003000000000000010018000000000400040010000001001400600300000018004000000000040020010000000000000080020014008000000b0004003002000000180010004000000000a0008005000400700100000000005000000900080000020004000000000000000008001000400300040040000000000000000000000008002000000100040010004001000000500000050000000000800200000030000000000000000040000004004001800100000000000000000800200000010010001000000b00000000000000001c011000000500000010004000002c001001400300080010004003000000c0000000000400100000000004001000c004000000300040000000002000800000000010000000000000000480000000001000000000280000000004001c000000800400300010010000000000200000010018000000400000140010008002000400a000000a0000004000c0000000003000c0000000003000000b001c00000000020014003001800000000020028007001000900000010000000000400000040090000002000c000000c001000400200000020000003000400200000030000000000800c000c00300000030000003002000b00040000010002000c0000004001000c00000080000000002000400000000000008000000c0010004003000000100300060004007000000300240000014002000c00100080000004001000c00d0030007000c00000080010000000004ff7458a53014fe7458a53004fd7458a53014fc7458a531b67f5458a530067d5458a53044fc7358a530467f5358a530467d5358a53046ef7258a531b6ee5258a5333e7c5258a53046ef3258a53046ec3258a53004ff7158a5300cfe7158a5300cfc7158a531b67f5158a53006bf4158a53004ff7058a53024fc7058a531b67c5058a53004ff7458653014fe7458653004fd7458653014fc7458653044fe7358653044fc7358653166df5358653046dc5358653004ff725865303cf
  | 35 => 0x2800000040020014000000400000240010000002000000100040030018006000800000140000008004000c00300000030004009000000200040050000005000000200000000000001000000200080010018004000800400080020004005000000200080020000002000000100040020000000000c000000c008000800700000010004015001c0010000000001c006000800100080060000000001400100000000000000000400300040000000000002400400040000004007000c00000000090004001000c000000000c0004006001000000080010010003000000000440060000001001000000040020008007000000300000000000012002000000040000000002000000200100030000000000c002001800200180030000002000000400040000010002000800000080040004000000c00b000001b0010001000800000100010014000000c000000000000000100004000000000100000030020000001800100100000008008000000000200010000006001c0000000000000c00500080040014006000800000000000024000000801000040000000000000400000000010008000001c001000800100000010000003000000600000020000003000c001000c00a001400500300000000005000400000000000004000006400200000010004000000c0010000001000800400040000014001003400000000080008000000400000480020000001000000000200000000000000c004000c00000080040004004000c000000000200000040000000000000100000000004000003000200040030018006001000600080000034001000c001000000300080060000009000800000040030034000001c0020008002001400000180000004000000400700040000000004000c0000010002000400100100010000008000800000080030004000000000000000020008000001000100000020010000002c002000000000140000000001001400000040000010010001400600000010000000004000000100010010000000c001000000400080090008001000400100040070008001000000100000000020000000000400080090000004000000000000000004000000400200000000000000000c002002c005000000a000400100040000004005000c0030008000000c0000000000001000000000060000002000c0010000003000000300040010008001000000a00000020038001000000300000030004002001c00000000020014001001c005000c00000000000004002000000400040090000000002c0020004000000800400000050004000003c00a002c0010000012000c0000000008001c0010008004000c00000200000008005000000200040030004000000000200180010004000000c00000040000000009000c0000000003000000000000020
  | 36 => 0x400000040000010001000800100280010000006000c00b0004000000000000000010008007000800300000000000009000000800240060034011001000700000000040001000c005000c00100000020008005002400500180050008000000000300240000010000000000100100010000001000000b0000001000c0090014014000001300180010000004000000300000010010000001400200140010018003000000100040060004000000c00000000020000006000c006001000000040000000004000000100000010004001000800300040010000000001000200080010000000000400d003c00200000090014000000c0000004000000000200040030000005000000100000000034001000c00600080030004001000400000000000004007002c00000140060008003000800200140000008000001c000000c00100100000008000000000c0000000001000000000020004004004800100000000004001000400100200030000001005c005002c004000000200280070004005000000100000000000000000000f0000001000800000000000010002000000000040000000000000400600100020008001000c00300000000008003000000400040050018001000400200000000008001000800a000000100300050034001000800000000010010005000c00300040010070001000400200080030000000001c00500000020000000001400100080030000000001c001000c000002c00000000000028001000000700000030000000000c00000080010008000006400a0000005000000500000020000000000400000000030000000000000000000010020005001000100080000024004000000300000000004000001c00000240000000003000400000040000004002000800c000800100080060000000000000a00000070028003000800200180030024002001000000000010000000001c001000400600100000018000000c0000000004001c00000000010004003001800300100010008008001c0000008000000c001002400500000140000008000000000140000004000000000500080020004000000400000200040000004000400300000010030001000000300000000004001000000100080010010000002400100040000000000000800000100010014000000000000040010000001001000100000000004005001c001000400600580000028007000800e00080000000002000000000100000000002000400000000000000007000c001000000100000010000000000000000100020008002000000200040090004003002000100100000024005001c000000c001000000000100010024004000800100040020000002000000c000400600080030000002000c003000c00000000010004000000000000540040010003003c0010000
  | 37 => 0x154c290000000000009a7800000000000000000a5282f41258000a3a8f50000000000000005ee0000a4600003a19a5000006b28d5985030682bc8bf855c9bd800000029a63218b36000000000000006e9a648115105c0000000000060a000000052e80000000000000183c8f99d740001f1200011dcac500007550000000199c00000004b000000ef8704000153ead814d86ec00000002bee7df00000001ef6000000000017cc5cf8694000113691329c6000000000000000000000409000000000006df0c3a000000000000000000c2e6d89fda78c83f26451fca0001ef40c5800000012d8000000094d0000568904a834800011b2b320000e906110b604f1897eb2a26bc92ea8264dc20840ab0b20b5a157ab1b0244ad891f26999b4a7a7203e19d8590a1d208ea9d23a400028283ca07c66d49ce6b5881ec00008e20000000b15800068d256a00005ec000298c000000037c00000000a2c000000000000000000000000087e00005f623c07a200000003d68000000042000000003aca22619c0000a7b124c65925be00004a062c000000002e00000000000224c3c4968a3181a9681ba41400005585c300000ab800000022e40000000000000000000003b80504261890aa5e93f400000001a9000000009404e4230e00007aa000242a000000000000000000000000000000000004b300000002b78aee1b2c001400000000000004001000000000040010010005000000900000010020002000000200000050018003001400000000080000001001c000000800000040010000000001400200040000008001000800000080050008008000000100100020000002000000000000020004001000c00100000180014003000800100040000004000000000400200010004001000400d000000000040000028005000c001002400000180000000001001000000180010010001000000600000010004000000400400080010000006000800600000000014008000c0010004000000400500000040000001000c00a00000070004001001000c00040010000003000c00200040000000002001400200140020000000000000300000000044001001000000040010000001000000b00100030008002000000c000400400140050000000001400800140000000008000c00000100010010001000c0000000002000c001000c000000000000000010000000001c00100300000018002000c00100000080008000000000000300140014004000000500080000000000000400000040000000002003c0010004004000800400000000008000000000100080030008000000000100000010000003000000500080000008005001c0020000000000c00700000020000000002c0010000002000c00300000030004000000000000000000028000002800100000000020001
  | 38 => 0x432503884c681f868f2d00000000076080002f59a0800006aa00005d00000b82873886699d000073180000001004000000000000003b1815638925b65e291948aa1c100f7800000b8ee200000001b780004208000000000000025f64ac0000000000070c00002fe800053d170200005002a496b200000005451a9a4080000638000093e0000628a7aa000147800020ec07400000000000538202c000000018591b800000005980c0c12ca940093800000000000000000ad2942c000000040d9e9a3e21aac79a00000001ca83b000001e780000000000000000000027924730000b23a0c88119522333076000000007ef0612a4180000000000b1417f26deabc60000000000281400007f27e5000000000b8000000000000004c2800000000000000000116917c5520000781800033494ea950118c58180a6add293000000000a3000000005740000000000211a8c280004b90000205800000021c0000035e00000000000000b1d142a00010ac000000000000008ba801095e866c374894a00017948721c0064a80000002092a81064c7bf80003db0c7c9429f521fe2854096086e0002aec00000002e31dce0001c6c3a60cb45ce955806d208c53a0dc46921fdc2098c8a3f607c272580001942a342a204d23bd25d4a769bb865d8724171000087b29bc6858000000142093f255864300003f900000000000000038416c8000b2d15b40160000000085c00001c800000001d88d780000000000000000000000000000000000030503ea00017220000290960000054c2bbc2678000b04800000004061a980007a280000001a1e00021b8000268e00008bc0000f4ca298000000110a0000b384ce00003e4acbc18d27b08b0930800000489cb1b3200009ea000294e3fa110e000229c7ef86bc1c487bc6960acc08b06d4914a4c00c80000000144ea9415c87622b200000cc23e41b167b0000023e000071e0000759000036780000000000000143a385000000017fe00000000000000a4d00000d5000000000007b688b8a5a000000000002f60000000251200015280000000000097a000248a00016a24018c54b1100f634eaa2e0000000977800016828bc5031556000000063c800025c00005588000013800000005a40de9196000000000017e80001ae800000001bf800000025d80000000000000000002dc00000000002a4800003f86e100000000e2e0001ff28809b4e29918aa0001e20928000079b0baa000243600000008f3a7687ce80000df800032100009c5072c6d8299e0000000000266679780e295e00008db0a807ca80000001d9a000179c25880000001fb866800001dfa7cab0a00005a08000000000020780be0000000000271a4fb00000000000000000000027a46158000000000000000000000efa00000000002ce600000000000000000
  | 39 => 0x46900008da800054c800041196dc25b0ad80001a78000000000003c063f00000000000000000050680008cf2b9e000075a0c980006730000000000026a80000000000000186c75700000000000957a6cc0001bbc00001e8000000000000000002218a4e034a00000005938bc68870ca611a9c9293788e418700002f0a8908a280000000e560002d1e00000000002b7e0aeaa327df9dd89918534000000000000002da256253898ea00000000000000000000000023e800000009ee80001e280000002340a748f7c5e79142b36159a343108400015d0aa08000313800050700006b3a146000213e0002d5c042816c33a26126d1188071b8000234903c446a0ac3b58000434235a000152000000000001d2800000000002bdcaf41258a861abe31d0b7407992140000000000000000000000000000000000000026a6000150800000006d680004df80003ec2d42000000000025b0b20800067280000000d3600000003262be00001d16b18000000000000000000000000000000000000852000000000013b60002b0a9d28000000000000029120002d8868000000000fc428026f804b80001d919e45a195e6ae49630255037c5f08cc4108a52ea01a5a6279000088d02340000a461e5800065b9290a1e293a5bc972a0361b28000007c00000006040000558000000000000000f60173969000022983090000000021e8601068a968000000000043017ae05c0000424a07c000000000015dc20d9ebc88c27563961b0600000005de8000000016885680000002c0caf4921e0e980005278ca20001d860000cce7d080000079100000073435486c80001dec000000000000000001fc6000038c000128e0000ae293601a4000000000000005d99d9000028186ad80005e8000040b878400023100000000000068a000000000000001d380000258a7a000244e000278247121c60001dae00000007322c7600008ce0000000000000000000004268dbc2930a9a000070c000000000007724a019ec0000000000282aa48a8b88ee19920002d6e000000052a00007c000003910000000000000000001f10000000000000000009a02412903925c6a516800002b482248000000000011980000000656000000000000009dc009a00000000000e0431c80004d8000099c94b4000000000004f078a875800000000001ff8000000000013100000000610152400000006f493cc0000000b511790729a4a60a78a3203f83fa59ea088000000000020980000000000104430a00000000ecc23e8000000000081c1e2c00029826248e8e49786ac00018663fc014800001c2a1f800000000008760a1082da956ae6a3544ad8dce9fa05f0516aa6c0f6800000018ba3fe000000000000000000000000000000005d300000000000ae600006e39a9855d000034500007289b9
  | 40 => 0x3830000000000000000008c80cf89fc8b144b186640000e5a1d0000000029a2000000000025661e60000000027e000219a55480008de8000000116800010e47e300000000000000149090a000012080007b59ea897083c43cd80007089890630225e0000000735866e39d8dbe5a20cb09e818cc6830fb866fa40c0000000a4500004318000000064894f00009f8a9d0000000000000006538000215ac8c000067c00022a26fa24503d102822ef1bcaa3c2236af28b348750738a492ad650b8a380000000000106e00018740000f060000000000216e00000007dd2764a918000000037028a800000000002f7052e000000000021a83c390fa94600da00000006560000b3a9e0c7638fe25b81076000000000000000da89c8000000084515987ff01de00020daa3c8344a0ead2494722c871d8000265919a79a8686429a1c200000000002b6c6eb000006a000000002ec0baa5caa98247cab301d283aa04a07b9ee881b014e72ea3e410a9708000000000000002d7800013380006b8a98a61f286629d89820002a6600010a0ae00000000000000000008b10000000000005e197a6f00000639000000000000000000000274ea4400000000000000000069c80002bc289a69500000000898000090400002624a79e4c00000007f62662ac1000000003b68fb800000023a80000000b1a800000009ecafea12e0000000000000000019d8266ac0000014644e9800000000004fc0000aff00002c400000000b442c1800096326d692d0000000000000018ac505800000008be0000804000000000000007fa1bce1360a0e32006f8000000063700000000e5000017725f6ab26000000098b800006f8000844000004980a2000000000028302af1dc00000000126000003d000066c14ee352018c00024444cf02aaa550cb600007f0ad3242e58b800023d1f2262321b20f5000000004c8000000000014e40000d00ac901829f0a04e00000000000000000000078000004e680006c8000024418da00000006f600000001c6a00000000000000000000035e80005b580000000000000213882e80008280830a708000794a9e400001f600016125d180000000000000000000000000001bf4b2b000070200008a080c64c020000000000882935e7d5a730203175493b9f8e0000e92b52a38200aa120a9897fa4b80bb867c8946a3ea70e0000aae449227c8d19e7a000000039284e0828ac309a41a2a42c8000000000000015ba7eb24400001d305d080000020364784000000125ba5ce2c2282f20e2000087292000000000000000000096183007411d9e0dc88b000026888ca28b42f98dc01ac00000000f40000280c33b8d04000084a00019426ec841240300000002a9c626872e0cc18007069650597a88426f000062600000000000000000000015727a1000000
  | 41 => 0x259e0a8a748b35093e41e9da06f8a9f8000003038d000000000000002a3c00027fa0000000000000010780000000c9200000006f20aba2e6a52246e800051509f09bf9df80ad88a000000000000144204800000000001e908a69ef11fc8758d740002708500071462f00008018390a30011a6c600009191a02000000000000000002736000000000000000000000735000000012988be00000c600007ec80002511f065f9ac1697fa3421860000b0e1ac87d600003bb2ce4000212c00012aa000000000000003761d8a55680007d1027000000006f52c960000000000294622e80004e00266316802c77e8000720000095b085a48b800050980000000000414000000000002ef96aeb3700004530000b5600009ff000082680000000000000248800000000000bca7101de2b5912269ad000049a1e62a73000007280006baac060000000000022800025b4000000000000000000000000000000013be11700000001134b3f80009f6800000000002470fa09a300007d2a1e060a24783af2b5200000004e11f3e00000005bf2ab800000000000b30000000002380009430000000000059c938250a1bccadc8e0a62d0bea4998000000000000000000002bbe21621de404283e56d8000619048a15d800062980003c980002132b4000000ac0002aa60000ab8000000011a0000003a980361134446a000000000007c502f656900000001d024cb00000002ce000000000b2800087ca21e4bd800082a8000390160000000000000000a3881529680bdeae98b0867a8d5c2b49442000000082faba09de0d76000020400000000001f0e00008860000000000000000016620b524e2654a5a28e48db6b2d80003998d7000000005a11780622954e85e800046708d6a02231c5f205387a900005fc2c8816a0000b5d00006d0800000021ae000000000000009c1047c00000000001ed889800008cb8000000000000000000000000000000058aa34c16102f20000ec400002d60000000acd00004c196a0923070201a23ba681964c2960ff66b520286779150000000088b85fc000000000000007360790ae4000003500000000952a7118388d9a0901378fdc03e14cc7e8176e7271caa6b080000002c5c00026ecaf5833e7cd0000000000002c177885280005900d389a81114a0f03f40000000332a80a0d48136a8b00000000666000000000001107380ebe000236e436aabe000000078a0000000000000000004ec22b2aea800000006b4375ab662db000000000001bd00000001dbc55129f0b330000000000000000002d72caa408a5dc00000000000000000000091d2b360001e2600000002eda4ce993ac18b60aa727f481a207c0000042135856228884bf80000000000000000000027f00000a28000163834f96c8000000044f0b869f300007b10ae82c300
  | 42 => 0xd303f691c8b42a5460000000000000000003580000f0ca158000000243c80885645ee80005ab22f0000000000003fe8e8000000000000000000000053e9882caeae08c6a000056e00022ca34b0000000030470d05d2000000010cab5e2452afa5b2800000002f00000000340a9ac1771f206e08e1c3121dcc000121c2d280000ac0000000000006c8000b4987ba140a4c42f919b25eaaca60000bc843f8d80a010cde4f4a1040002462000100a59180000002be800000009172ace69d2c0200020d4a28a4fe237000000000008b9800027d91721c00000468848000000001ef800079c15bc00000000000ce600025302fb00000000828000000000019a223087d20000000829000088800008a4101200000000000000846221a000000000000007210000000034630e00cc45da418000208a000000042a938c46a80001158000000000000000008d40000000220452f80000000000000273e08a9e1281713d4000000077929e6000285e00000000c52a8000009b89aa00008a20000000000000000000000000924000050e00001529e827d7962c693acc60000000530940600014d200027204cf8000000280e000000062180560002b085d487229700faa7d216a400000009fd28d60002bf40000fc80001f84326800025f17c014c9d6858ea62871c8c207bb80a8000000000000000002c7caac0dae97b108e1fb80002eb157c5552d5e2670ac200000000001a200561aaa000000000008ea000000078d00003b2a7b47fda33a4790decb0e80000000000000115a00000000002c0ea2d8000000000008ba91600000000000000000000000000008cb015c349958ea2e958094b000000000000000000a1f0000000215c000000027823fa00009380000190000000037c94c6008000021ea0ee00011044ca80006038000000000000020760002a149a28718982058c7ff8fb60001db2000000051600008cd9bf2ab21e1c0002a840000db000000000aa00000000cc80001af616aa67600000000000000000210a27d236062e2a8a0108000000117e0000000000000000000000c0937aad08000508a1721f7a82c000196600000000002a8859f02e81c5a94281eac5813e8000b5829dc59a90f0000000044780000000000000000013b80005610ef000000000000000b0128100000000000272a70705b800009d61c4000030d9a180000000000000000000007598f6e22300005209854000000000000003989e7c0002aee8680000000195cb101c5897b800001880009070b2800000000000c263e500000001ffa00025c60002a9a0001c0a00000003ab8f72b0f9e2e8d9000065500000001c4e6c080008422aae51a80e4a3226e073b819c6db000000007265a700002c004440000000000000000000009f7000000000002ff000065c800000025b86148dcc0
  | 43 => 0xaf5030e0e50000000000000000009cc8a2270517642b69cf286705cc76718ce1669eba0000218000241e00000000d58026000203c0001d84000022600000000000000310a6dc000229201ca99600000000000000000000000026302e100005cb20301f71dc60e61cde6cb829a495916a59504b849410880001928a7aa9b205185e485094dc000193280129025bc04d000000007c900000000b0a76b000000026ce47780008ae9acc316278695b9c4800010940000000000000000010d492580000000c0634d13949b216ba000089c000253ab4da8c267e80000000f460000000000000000000000000000ab610300000000488000057829620002080000000092c08b20001f1800009d8461000032a014a00000004718000000135a00000009d5000094c800000010729252a286e81bec31c0d667c08000000068400021da0001f90336834800022a000000005ec282e5be800000003d00002c260002510af026ee11f92b274c80005e6000072201642540d5407000007bc0a3c3d91be61eba1eaabd25764b50838a6925f41b01d4026100006780fca00000005da80000000cae00000002ad800000020f000023d096c80008f61b308398000b0225ae7388af66500000000000000013ba2c728347e580005e39b725e695061d0856a68380003fc97a61e98d6000000007be10a20001a800001fe04ff9b0a1029cf013ca0c40000000000000000000004de0000ade8000000000009d00004daa6980001eb2000000094e00000000000000000000006a20000c7a9c880005ac0000000211600000000000000000000038000007b722405c7194ab090908000009000624b611290a88e58a8c9d780000000000000087400003ee3ff2362000024c000000000000004cc195a1db930c35280005e300004b2a18e6c380000000000000000074ea7c600009da4f39daa4d38000862000023510c425e2a3a1bb80005c8000046d800050c800059c184e87d80009d4ac5a0000000000000085300007d5060800007ca985000000000000000000000000086f8000000000000010dcb3d80002e980000002ce8b3f00ee0a28000000000000014040000000000046200000003778d289bca3f053dabe60149608000118a8ff80007af85367aa80000001616000273c000000087a0000000207e1f6ab5c67d000000000000000000b0d000095503a830f00009d0800068480006701f6648389b0000081c9e400003ae874a00004d43789e9412eac48183800045e00006a8235e78e8bf4b4802cc178ac7a0001eb4000000000000000000000000000000000000000000000224616f8c083258000000000000000000049936000044c8052a520000000160903200008ae835800047592480002a005440000211800021900000000000000000000000005cc8
  | 44 => 0xb220001376000000000025203a79c528f7800000011ee000000061823029340268674892210b0ea67d68c904a89c2a0000e9451c0f563ba2a1e0000b6265f00000000000808000000023882b10652ab783b844800000000000ae38000000000004c800000023ac000000064e800029b817600029de05400002b022d200000005d2256400023f80000000b1380002ed0000000000000000009c180000000000000281606e969a450000027c80004d91224a9a94faa32882e08f8000298949c0000d44044aa7a0001da40000000a8c01f407512beb0508d098400000000490a93006c1c2ad70b2780005c6890c000000000000000000c5c000000004f9b58804105800000000ad0000774259a010087c76010560000f3a0001fba8dc000000012b8aab08240419fce8ba18b65f714c81a48890147a6a247f8000b5680000000000000000035784e600022420001b56172800000000003eb0bee0000410841a7c0810245a40516b8a3781c49e50cb2000000060d19340bfa8dc20f0016add9a3a190abb61c72a96000000000000004b7a3080001876a78152e46b0a08b3c8d5692906ae00000003e0800000019bc44599fcb2ea62c78386628da0000b1e0b7851324a200000003f580006e6a55aa8289985bd8000492a30c59a1aca48c0264021000086b0786a6b8fe0612210e000151884780000002788190244263880000001160635800098702400002b1c00000000c91db442c138e69717922b408d8a970c34ad41c3a0000a680001ae677ba8ce754195e9f100009d9aca43588000000000000000000001a2c8d2800000000000000000142800000000008c00f5415b235c82c0000a1d9e406be2a8e0d8800000000000000a560000000525000081c8b3c8180862000000006780008d3a0fc000000059f80000001f1c14722500000000000284c98615d26908000ae12258912800000025d26ea947604a1e4e00000009a092c200022964c3a552366800078500000052d4681aa5921b88cf00001cbc0001c9e4aa00007a880005128eb00002b9400000000790e160000000000000031780000000000790890e77a836c0000000885980a8550000000132200018367c78000682800000027745baa54c44890e200017ac7208000aba22d00ef019200000000002d86b5f8e2a81d000072f80009b00000000000000021120000000000000029e0eea0000b6a37f927e000000000000006d5000000000004b11bc4127931850f00000000000681000004e2a4260e867400024d4000000000000003e580008331d520001b6612b054c1b4935200000008f7000000000002808000000226c10e00001dd0000000000049380000000000000000077500008cc80c888f98ae00000bc33f8000b3c0a3a00000000000000000000094680004e486e63ab09c617b9350
  | 45 => 0x68f5181229f0000000000000000000000e360000b645808000000000090c80001da21fe000059e481000091ea994a5619f013287480001c2600000000001826a119fa4000139e078092a2bb22e0698a78e0000d2a9090e48000225a5f2a90000022ec26d0b881ec222a0000f2400016bc000043400012ea0002aa483180001a0800000000000a9a43e9368d4012710c80000dc6000000027f000066d8000000194c00026e200027966e2ab8a9b99e1e000062e00020520000d124c9000000006fc48f80009be800000012f80e680007868c683049a1400013d6a3e23d64461808000066a4e1906473d055e7e19da20270e5e6a0a4ec0cf04b00001a38ac02bac000000002b800000000002d480008bca3cc7a780000d09158000182c000000048e000038b0328502996800010ca0001bea000000055b800097c8000000297c200a692238013c0001f7600009a2710800000000001d300001cca1e2b2c000000000005df28120000000000299a8fc80004e8800000029880000000a18800021789ce6b48000000000000000003ed27406ed9446000000000000005fb80000002ac69f5000000000000000b3a4e28000123817cb1c000058a1ac6000087000000000001de85c3800031300000000000000153a2d4000000011463bc8ca0634851640e9f8a0000ae07f794020a127f61868e6a0000000000000000000009582b58000088000000004849fa60339664717000000001ac18e800058720f400000000000dc825aa3ca2b2acc845d0b026c723c00000000000116e000224800000000001814a47a89817a920600005e60358000000082c0001fea0fa000000011024a28d9450d8000000058a8bd24227cb2a0258c8000000000000020120c30202000000037e0000000063800000000001f9c8af0d204ca218a59b00000002a1c20024f21099f080b90f526c00c2c00011540000000ab7000000000000000000000233e1ea000041214485f615a00000000142000000000000000000838228e00015e879c8140a1c12403c22458000219847c18de9508b1a000000000000007008000000000000029600000000000000000000007bf08065b8800000000000920fa45d71254640000068905ae1722ac2a7200005e92a5e220a9721269164a2280444af1cc218b000079f8fc2669051a040800000000000001c7c0000000952000000000000000c6200000000000000000196c6eb80003658000000000028fa374417815e0000000752800039915640000000000020e0000000000058000000009e9800070f28a848c80007b81d6c3fb8d8801e175a5432d3c048057875e02a06cd267a9d40000000000000000000002d2a00000001ff8ff4000000053f198800001da00000001e5000090c0000379296a9e795700000c0000026de000000001ea17e268
  | 46 => 0xba4825640000a7587d48548bc426d8000776a1640000c4400012a612f106a6478e069f38d645ff000069780006438c32009101aa1e961057783225ba0dc22f02a10045265e000171600021bc4ea1e308f180dea5b044000000000000000ac8993c48200000000000413a72475880009f78a846a1800099c000077f0000145199865a800000000009400000ae70000798209c00011f65dc27b658f9df4000065400005100000000000072a33e800014b0aa687300000002aca973ab1e70fa1680000cd0000000000000003c10fd04ab1b68218000000000005502a4000000000000000587909c00022c02778000a9900000001d0c0000f0a000041800013aa0000000000000000000002110000000133a80980000000aee0001b4607a912656b00006e200000000c1c0000000150a0240c2224a9a18f020001c2043b2b3880e83c842299100000e740002034285165c00000006e72644083249c62901f296b000039c800052998d047800002f88000210160e0002652a6c20ca40996b603a27264f781249660820b54800000003345be02122ca99e2303a7168a50b7a55786a00001df23c60000000000046800000002a9e4fe939600017d006e00004eb0000000000087c2d060000000000000040e01808c78000000249200000000000000000177e83c828619715ce77f990a8e791ce23988fc71300004bb9ec8b21000000000009a900000000000000000000000000002a3e00000000f7000093d0000631800015017280001f3600021340000000717879a000000051a24f0000000000000006540000000000049a84e2a391c2e000274409dabb400000000000000b3d0932880000032b06d0affa76036a0000532869a00000005c7998a0001df66bf987a000292c11da33451b02c019a1f6000000000000000000003c573000088427100d8000000028821b300005a4800000000000000a122d51b3a323000000019040001824000000000017eab4e8000000000000016d8b1a00000000000b27043a00000003f1800000000003f78000000000000000645b980000181ac00001c4a4f6000026e97560588460671a5d00282a7000000007d9000000000001f31460869a47e0000000000000091c80004a68000000263233f0000000000000021a473a90f65408000561800060880000000cbe55b00006f684d62650000000000078d800000000007a48e700eb85488848000000000000029902a6041a90027b80001a1c0000000000000096221ee00000005888000000000009480000000000000049400000000002d920001b6a000191c00000004f700000000000000000000000000000000000077a000000006529320000000000000000000000002bbaa070000000212200000000001d4e76e000087f23da8ac09020000972000113260c90b49df09e
  | 47 => 0x6093280006108000000121a000000093d800064e0000529297400000006a8a95a9458b3e05500b22a880001fd8d0e376914a5860fce861889400000005c90ffa1781a4a4d29d2c1fa80009019d0001d8a6000020c082cab70124a70c4f0a71c975873e0002b18701288e000004a83e80008851d1a00000006dc148082984e85d1033600001d6796800015880004a50f9e37a0c4600017d4795000000291d20f300004fe0b040000000926101ea2b80000002ab6000000000000009fb99820001a8a00000000000000000120a7d407ce8b8ad7c0ca80002fe0e109710afa02d00000000094af20e522af80000000000a3d80000300366000095e000134c962800000000008e320d01000e805d798e600000000b2279800000000001fcc000215645e800000000003640a8e56583c23c5000000000003a300000000000000000000008140000000000000074813726d7000092b800052c23bc01a9b36b190000000139c4618000000266a00000007e00000105153c000000025680005ef266e7dba01e1580a0c648004600028361020f6ab339cc4722a84a1ad80004d50be06ea2aea0001074000000035f293c000000094993b20001b406aa127041e000099080001b5988e00000ea000046418a1c4625d0000753257c92a0000467acf8000000037e800024016241b1800044e1b4855980002fca1485f8800000000004c9834e59d80002d226b8b46847a0c69f0c00008685852ad2436284e305aa6eaa4177487d129c00021924062cd2372800075596cc00000000a2027a00000000000000139000003b2952a249cfe5518c18747acd000011b07758bae4e90fe6723050e3ca8b962041cdc4291da64219128aaa13b400009760001aa4b12800000002600002b861a72ab2000000000014b80000000476000000029f200000000001bfe0001d3e72c000000018ee37a80000001b140e01be0abd800098e80000001d6aaa30000847000000015f8000000051e8000abc80002e71a403040e3200000005c290ae34f2a5600000003c6800013685560328c562320e3e0000db241087c000000000000e3c91a00004638caa0412c4c932000000006dc0001eac67f9320000000003100000f9098084919d420e800061318b297800001ae0000000000009580007a5a0fe55e14d428190b693087565e122567418ea40000c02000000088b04ae00009580be1e564a187b600000000000888000246e40a1ad600008f2000000001502d000000000000000000000000000000000000338000000000000000000b45000046f9bdc2150c52b2425c826a0000297950e5cb8e1887280005aa800056ba67c3a580000002a4417789885b69fb09528000000000000000000000000000216c000000000000002b20afc000111200000002d680000000ddca3f0aac877148682
  | 48 => 0x9400000000edcb5e83a02460e08524800003cac3c00009e80000e229ce00000001d2400000009f600000000000000000000000008ecad1018c204400000007d32c3652b0af49928000987987200005fa4db1efa4a318c2282a606905800028583aa00000000002cb253c88e80000fa8000166e0bf0000391969ea788a9c63b14da71818022c3a318000000000002e26741e6e7fb2d3ea0900d000000a478f8c64000000060c12928a6aa4e0ac800012a20584589060143000037982c438a00000001e3800000000001ff000000005d6000044b80004ab8000000000000000008058d4e6ac000048d000066e99f6000000000022de0000000a5205f40b782d21510000874a60a00000009558cc0000045011c8f981bd80007340392338800087980c20002bea1840000000000074980000001dca0000c040002314b2faba400023223c800508b597b28ef94f0aa8902c3e720f60001c2400000000002c54212171400000005b000fc71e961a3360000b4a00006e9280247093eeadf02100e7800035680006bd000006b800082e000000000004a80000000000038c0f2c00000000ff0484a578f865678d724ef250e97ead7679900009d88000206a5e6a7d9cfa000019a94aab5689a80000002ae479117f82b7a5aaa12018669e8000a610596000000000022da00004a24e800000000000000000022b0c4a0000000000003e57190e600000000002d4e09a800000022080c7a0ce0208d067ea82e60000000a4b80007ce125200000007a9a398000000002a80002fc0000000005c48401720000b4e7c5a6b6a8698467ea19863459016000134200014ec1de1ad0afc0000a1c982e000000063a27e0393a8e83980000000000046ba504164ab5a9238000000000005a8000b44a9b400000000000000000000092f8f4e3838646857a8c44ba0000ab9a3265b3800000000000789e860000000575000000000006b60000000000056a17d61e80bcc12980008a1198c253a2700001a880ec000000011b22368000000000076a0936aec800086780000000000000271200000009080000000000069680285b406eca7e9340518800030c214400000000002b3c7579d180000deea07a8aa4b2000057c104c000018a4358000149ad8e00000002be15345811a7c47a0a8a0001ccc3b5062000000000000000000000000011f4742800000000000000000000000000019080000000000120c00011d4389a38a0000000b1c95d637d08c60000000000000000014567ed00000e926849dca4e00002d2e7e680003d794984f00000000000000000006d4000000000009eb0000995800052380000002b6a8b1800033d83e200000004eb89dc8ea87280d70000488a26400000008e7220680d8000a3b0000ac68000a950000000000075800008b380000000000935800000009
  | 49 => 0x142000000000000009f9800000000006708000000043c43813482d01466000000013f800000024cc7c2a00a07300002b58b2400000006a3185835f8e8a996830a6cf9cfc5899366afb1a9c89e00005bb8000000062a000000000017e48fd00000002c94000000000000000000000ae8a46c6638000000019600000000b09e02000183e00000006699e881800fd41f88000000000000006241ee00000000000000116c73a1c8e0ed2a0e1c3938800000000000000000000000000000000000000133200000003f48000000000000000000001e46000000000009c485c04c28a1a7d0a8800008f080001b804ec000000000011700000000000000098890ee00000000000000000014c2289526ace9a2e3d22ada24c1918353278c7198cdc5140b12995000033d13fc9e01818000139873b1ef28258c8800000000000000792000033ca02a0000000af0800000024ea504945c3c42ce21718c2216622803bf8f580da1f404240000707aae0912041c9ef80000000000000000097a93349491f102dc1a5295a0fa656980006ae0000000000000021b482526ac25211e69898daa6ef8aa4000039c0761e8c62f871e0000a1a000110635a800000024b2544800000002360000b580000000000069811d07e80dd80002ac800052c943e49d8000000000066e000067a07e079e20d861f9eca000022000000008de2cca000000057d80005911ece05ea658797160c00000000002d90000000000012d02e2985a000000084e8f0061785f86a3a372b3ea1943a8000005b8038531000000000020000000183000036e26f08fb0782000000000025700001b74a63860269800000000afe64c032c00000007c9800000017500000000000115c0001b3847b16fe00000004c7800000003e00000000000000000004421ed0000ae300006bc800009f17b69970000000000070c800075d800000000005b91706a81a7ec3aa80000000000000000078f02967828000000147e5f1a54e000000049f000099b00000000000000000081580008e38a4a679a2382911f4e5609b8c4bf174a8ad1b5eae2228c689a8d2b199f7088a092826fa9be8aa82784000238a0c999a0002d080002456088991aaeba27a85e0aa89ae8e6c43f218201b968c0000a6647e24e831f8690000201c57a8b920002634000000000021aa000000064f800000000007b4294c000000000002ee5022042a102d3408286da0000214000000000017688be94a200000009aba3fc49ea6d292e0fbc7b32126964000000000001eb24601980000afd800058f1fae00000000000000000000000010b89aa80000000000000000037f00007329594a499d98000000091c000016700000002a9416f1924000122a00000000b68118000000000000000001fd0000042e00000005b480000000af29b500002
  | 50 => 0x2d831c05f9cb65cd00004c10e9c1e48f7873e0000000000091515fe6588000000000057b80007030d4610580003a8800000000006a989cc1f609e23908e382e9121800000000568926255a3c80001a681b92d0e2a400000000000000000000000ba00005a200e8000103ab060001b0c15527460000736a291b9833912ec1d98aa01bca5362699bf874d88cc00000000000000000240a094000000000002f400003a680008cc27a891daaba1549eec7b19bf600015fc000000000014c0000152c00000008f8800000017108b50000159800000000000f48246000000089d147c54a8eb65b118f8b260a9458829f414e800061e00000000000a7280000000000a0e000070b1e180000000122078800000006e02c1a97f00005ad000019280000001f8200005206c9000050380000fb00000000d8200026c2000000000011800000000000000024480006db8000926800000000000000000000208200000009e28744000000036380000000000000000000005fe55f88fe000000076c000000000000000000000000000000e09de9f2ea9d98ca6610604000000045100007e7aa2200000f0abc0f70000243800000006dd9f1a55a0000000057c66b0000000000000014bc00000009e72410000000000015d894f8000000000000000003ff8000803800000007fc3cf8000000154200000008eb8000000000082a0000ac08000000263e00000003cb8000b22a7c80002d8c38680007450000000000000000000000000000263c3b4964a5a58000000044600013c801c17ce0002b2e000000078200005ef97181ba02428c48ee6000000022a0000058000000000000002cd600000e6a3314400489d386010000a410254aec000062a0000990000054680008b3000000000008121c74a9a0e780f58dac00026e800000000000000000203200000000000000000000098008ca3b7800000005066c6867ab45800000000000001fd4000125a67680004ee1a6e18c8a541fb1d582e5132e000033200000000000da60000fcc00000004b6905200015fa000000052304a40000d2233595f2a8d800000020dc1ba800000000002a58f9a210800086e9f6803e91fa63c27ae00000006b68000000289c01780004809fc20001e66000110c0000000000141400000000000000acc000000000000001a3e0000000000000008002329b6aa926659db676f800000026f400000000000000715255c814271850d000000017266d9037884009d09010d6c36e978261880000002c2a00000000ce80001e00000a61ab647488c1e0001d460b1893c350a4c600024085dd813a3dd122c423000000000000000000000000048f00000002616197800000015e47a40000a1927f8a1090ea83a089a00023b647880000000b7e8542b2c38780000000000ad39ce43278b7691a8d928390
  | 51 => 0xa078a169eb8000075c0000d68000000000002160000000a2000001c19bc28e9800000000000e0800000000000002bce14880008e6a8d484a896e521000000007fa0000000a08000058d00006220000114800009b8000000054e000231a000000042f00000000000000000075c80000000658000000000000001d19894000135685600000000000499232454e000080e2d1c88e8e6e00004309a7000000000000000000097800000000008df012a000064e00020080fc226626905500001488000000052805123bf0a748e01eb60000000000000000000000000aaa000000009700000000000644800024ea6ea10a269400027b24b3a696b1898060001ede2f6a91a0000990000000000000001df2d0c000000000023163628000a5fa64c5a51a900af800068c0d9c40200001e70000491a4860000000000000041f8d241f9aa3816c05d6000286a00000003c591980000000aca95165cf16c20001e74a7f0a36a7a0000af60000a4709d4000000036d1be40002a2600014aa00000000000000000000000001b084f040c3df8000a34257e6e5a25c65200005b7967800000000000000861000000004b614a951c00010ce770a80000000008e880000002484000000000000000968c7800000005ea0000000000000000007d880004b7000000000000000000b300000a31a79a1851316673800000000008ce186a2e799801161eb08bf000000011560000c66287a6023a10b325f7844ea5b800000019460000000418800000000004a0a8ee96580005fb022486303380002734000000019c800069c18a00000000a6a97f49ac12363420292a57000067e0000000000013a80002b718fe70d800024b8000b55036e00009c042f80003eca5da68cacde73d830612d2176ab100800002d4c0000000223ab0c1310000000000000000000001b2a43d1f5c4a102720001e22000000000015500000000b601eae000000000000008af97c411e168e11b8b9800000009f90000000000000000001a78000000000000006fa000000000021d07b9000000000009ce89fa522840474d213032f1e8e599800000000005148da40000000a1babde8e404f4b3109340f38f80940a02eab40d989892a080000000a429f926fc19a8222a51e711000026b00000001fc8000000000000007440000000000085826be000003473485da2871e243d8a01a3318d509a6867e537a0022c600001698000b0b053025086ce1a2000000000008bb80007ed9d7000000007f8800026480006bf24e600000001ae9d920000cec000275a7f59e8000000001e3a4e4000000047408960000000241800075f0000187a384000205e433109600008c00000000000000004386a868d92e672185f250600000000000603000065d276e000214e73010de655a8524f993c40002c7ea9f22ac3ef9444
  | 52 => 0x2507a4d261700004bc2b68342a71e29712d269904be5342abcb4098206f40bce9790000743800000026648658000b04000061b800032700000000eb40000000202000000000007f000004b5800000009c283780000000000000113aa6a000057280000000000000212800000001d50a6c625941000000001dd8e1214610ba28128968ed00000e391880000000000137c000073a2b51df0abf17123e300001b080004c50b1e0001362509000000019ae000000040a937400000887a60ed0a830d5866a800000000000000f3400000002b3ab12189958c246aaaa2d09d480000ee47748000000135c4701fe4000276a0000f680000000000243400026fc7dca96400000009b1aaf831016a8000010c1b1000089a01743681aee00027d600000000001e0435ba60eaad0000000292a552a3860001760b02a4260001c2885d0000a2801fc27f8000b2e008c00009b200000000000000000000000000000000000abf800000010f22a0812c0001de600028be15a0000b17873c00300002ee95aa3f00eda640843e72d1a56000276c2ec0000000000013186060000000000136e8b7000000015362fd80000be912c000000021e1bc6000000013d80004071c9a53f800000000004da0000000000000000000b62a7e3d2970400026789c0192eab89ae07281c56000000046d000000013e20000b6e00000007cc0c6e01f80006c1174089fa9080001066b5e18706de08840000f1e0001b129119260000000006980000000000263800018faaa00000000000000000013364768000000000000022b608c267e7fd115e51b80000000bd27ba9ee6000000000000000000000000000000000000000fae0000000000290c00000000000fecb0800005908000000057025907c828829781ec94f87e6000000000000001bfa0000fba0000000893a3766650000b1b8000000023c4f901662c99a220000f8402489ca00000006fba8ac00000000002a580e899dc00000001a000004262b440001882000035000000000000000000000000019b49ff90c26d3285c0c40000000259c8c10000000000000000008d4997e00000000001f780001f469730000000086a1a39242000000098a95ec1c80000951188484d801ab07800065e22b86bb1d8ca3980d23441c7eb4c80000001e4a12300003a0a0f81f59f7a00000000000000000000092a8000a51000055a80000d69a7e0000000a9e0000000000000009689868ba86bead307daa1322ad0a5a71892a4229258e24b00000000000000160a61a20661f41aba0001c1237507e4000181e0000000000124400009ae22d0000000000000000005b1800000000000000000000229e000000000000000001c0e000184a2b988f60001a9e7a8000000000000000000b1186d80620032000083e00001b60000000000192c74b8bb25e5
  | 53 => 0xf9272019aa4a4100f8ab55a2624c48000000176c00023d28218b460ee83b21d418c80869b1e2921d426310c6c11215b800000004858000b2829fe8711ddc6710000a3d29ba000000000022d80dd0000562800058d93d0013009800000003bd80000001d440000000000000008eab54000227675b8000480000000012f41b2a22400000000000000000111c733800000000001d78ea84be800000021f80002ca200000002e8858e0002068000130249d0eee3b2201889b9bde62791301179d940001ee24150000756a728420131cb411b1044fa9360000bd40000b564fa8ece000250800010020000000045ad6cb249a1024792281e30000000000000000001a3123a00000000000f8e39f8000acf8000785ab100a52992a3680dc7cc8e884649c18293824aafe0f2221b243a3be20c2af680006a10000a702cec5a600003ce29b852580000fd8ec21650ba037d8e7a6a49dc48d6042484313461da821c0000000000000000000005fd89f806a80000002d2c00021a2000270a9450000000029c00015da4fa0000231071a65c000056c9d1200007f43881bd6000000004d0e7c5d3a6d83780000b0721e49e8a574729082215f884e43a1190000000000000000000000000165800015b0adb80000d01fa27cf29ce44aa77e4ad293e6498a340001786ad18000000000000000000000000000000000015c45f800000000ac60000d1895c800000000000000000b598000000000000180000000000000000051d237e000200c5479c6472bac32a6600000000000000149a0001b220000000998000000000860000f1c2e400004520386a4a000072e00009069ae400000002e000007f1000010d800000000000000000000000020d00008e502ce0001cb20002d1800000006e8800000027ea6058000459800029480005cc2cdaa27ab169b100005ed08de0000000000000000024bc00017a218d98fa6c2199e2ff8000a160f325f4a34474708182480a70000000028b8000000107c1dc21b6927a81a0000b667f9800000024dc0002d38000165a0000000000000000024fa4422ad420399903d092e2416800000011bc8409a6a5178aea2570be82e39a460000cd42a1854621422ae00027025bd12f20001648000073040383d8347000000000000000000191189c9d70000000284400004cc000000034680009f4800094a11a622a800036180006cf00000471bb485025a414a0000000000089c834c88f10d27db2cee34ca5826488000a75275832e17360f2826c765a3e03d701981af914e00016520000000000000017a224400000004608000000000000000009ac81c689500000000c8e000000000000001bc0b7c15c8a720a3a9d863d04aa6b78000000000000022320000000b610e5c0000a2600000000000a9e07393f20c4800000000008f100004f68fa
  | 54 => 0x38e8c82016ad6a13f000025980000001d7a00000006e48000000000016b2950000000026297620a9209e701800000000000000752aa1800000000007fb800000000000000000000003670e038aaea0000635000085a8000286013000000000000ed84989504000000015e82b84fd9944716a5bc0001a4c9540000000000049b000000000000000000000000000007080002054082245e000000000028d802280009d30000000232a00000000000000b26a348000076c000053ca1b00009e1000023ba63800029ee000000041c00000002bc47b50d2e6dfa9a074a8ca40000a7e97888b67c1000000012780610b4c9dda4ac59596be7b4abe40001a6c0f98000a5da17c00000000001bba000000097c18d89b92d2200000008ec00003cf0000000000047a9d7e00010f800000004440000000000082d0000130286000000000002a24137196052b89d2000000000021903de80006ab800057d018e000297064580005700b2e2cb29208838298454a30698128868bd8d1e5e208326aca72e0000000202889e6ff1dc8121a5840000000380800074200000000a2400022a400000000001a2856f80000001c980001cda9418fea00000006e185240002c525398a30a0880000000000a3f95e200009ee98d8000858a8940000000ae5ac803dd8022b5005d4a858a6aa2c800000008ec0001472ab018f6a1a14b6afc800000000005b512880000000000126e8fa80000000000000000000001fe000094c4a5a59420a89166419b9000000000000924000000000000003ae0000b2183ac0000000000000000000000000000000058816e8000b0b9c9439a00000a02d50542800000000009b280006c98206161a6506e7a99c000296667b81a00000ab00000e4c97a00000001ac4000063c0001a760e58000000159cb5c800000000000002a120001de031d800000000000000000705a04c33a957600000000000000000000072b0000000000000000000000000a439c68a14182aa2c00007ca000050c1a443cc00000002c42000000097e1e5087e800072428e00001dba7779af0607065a5bb1ab47960c0a96a21b04aea2a617019c879d9034a6d950041b069630aab0e8fd800021d93e09199a1a000047059d00009b415c20002cc216d8cbaa2315928830000368a60c000000047285b439500002c580000000c3e00000000000000000000000000000000000000001c0000dd013e0678af884025570000000007400000000000000af300000000000859a42c188800000013ca7e214ce0cb96a600000002dc9abc36301bc0000000000000000000000000000aa624028191d3c3d9ad8a0000000000000017601000000000027a05a81881dc000000000019d642781fab520c50000011e000000071c0ae4000000000022225359c50894aa2a6b70a425c0181a40
  | 55 => 0x2b2800005c20f1a668000098c000055a0001ec200000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb37855c941440976690ab928288002ece017250510255d8402e4a0a2089cb4761c9414409766d0a3928288002cd6147250510255d9400e4a0a2000bb1801c9414409766d0b3128288002cd61662505100071a32cc4a0a200ebb180989414400b3690eb128288002cde15625051025d9a42ac4a0a2000b9783589414400172906b128288052ece0162505100071a328c4a0a204abb2809494144001763012928288002ade1952505100055a432a4a0a20009b687cc9414400136b0f992828812aeca023250510005d8c0464a0a2000ab7864c941440015690c9928288002cde15325051025d9a42a64a0a2000ab6860c9414400156b0c192828812ecda1432505100059ac2864a0a204abb2800c9414400176300192828800aade1b705051000d5a436e0a0a204acb476dc141440957650fb828288006eca1b705051000dd8436e0a0a204adb276dc14144151b60edb828288003ccd9770505100079832ee0a0a2000db373dc14144001b62e7b828288002ec60b7050510425d9438e0a0a204adb2871c1414410d7650c382828812baca18705051025799428e0a0a204af31851c14144001e66ca3828288003cc1947050510257c9418e0a0a204af91831c14144095f45043828288002ec6087050510257d0c10e0a0a2000ba1821c1414409f8e8edb2a62881371d1d8654c5100072bb28c698a2000ad4864c931440916a90a9926288002f8608704c51012e3a38ecaa822000c7765dc550440095a90c98e60881321fa1b754c1103743f43eca982202587c87d953044001878e9b2a60880030fd97744c1100061e32ee89822000c9c74d8d304400136d0ea0a60880026d21d414c1100069bbaa82982204bd347550530440093a90e98a6088012b5219314c110246aa3aa629822004bd0804c530440990f90cbae40880961fe1f65c81100043ec3ecb902204bd36755072044001a6aeaa0e40880036ce1d4188110256d843a83102200bdb2765062044095d64eca0c408812bcc9d5418811025798baa831022000f33655062044001e60caa0c4088003e8e094188110007d041283102200edb1725062044001878e9b2a408813f9a08365481100061fb2ee89022000c3c65dd12044001958e9b1240880123da1b71481100063a32ee290220009b68750520440013690ea0a408812be8081414811012e3c3b6ca902204cc787619520440c3970edba240880039ad946248110235b442a649022000db38750520440017650ea0a4088002ec21d4148110006d843a829022001db2765052044003b60eca0a4088003ccd9541481100079832a829022000fa2825052044001f4304a0a408812b6cdc94148110257d1b92829022000fa3625052044001f40c4a0a408829fe8d49414811053fd0292829022000fa2325052044001f4264a0a4088003f04c93148110
  | 1 => 0xa83baac48800a2fa1f74589100061fbaee8b122000c3c75dd1624400117f03ba2c4880022f60774589100043fc2ae8b12200387c855d162440011bf06ba2c4880223720d745891000477c12e8b1220008be871d1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100064fa0ee6b122000c9d41dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001958e9b92c488003331cf72589100063a3aee2b122000cd473dc562440011df0eb10c488002ab21162189100056641ac4312204fc7a70d9652440031f10cb84a4880021fe1576549100045fc22eca9220028bc845d952440011bf06bb2a4880223720d76549100047bc0aeca92200387c851d9524400f0fd0fb2aa4880021fe1576cc91001c3e42aed9922000c3e74d97324400187ecaba664880030f19574cc910006573a6c599220048f4865c732440018e8cab8e64880021fe15768c91001c3e42aed19220018f8865c232440070fd0bbb264880021f617764c91001c3f42cec992200087d859d932440010ff0abb2648800e1f215764c9100045fc22ec99220028bc845d932440011bf06bb264880023be09764c9100047bc0aec992200387c851d932440010fd0dbaa64880021fa1f654c9100043e43eca992200387c859d832440010ff0abb0648800e1f215760c9100045fc22ec19220028bc845d832440111b906bb0648801e3b209760c9100043e432ea192200087f87d9432440010fb0fb2864880123d219710c91000c7c432e01922000ab7865d541440955690cbaa8288002e9e097550510005d2412eaa0a2000bb3805d5414409576100baa82882ab8d99765505102659b436caa0a2000e3776d954144001c68edb2a82880978dd83655051012f99b06caa0a204ebb380595414404b66d0c32a828812f8da1865505100071bbb0caa0a2000e34761954144099c6ec032a8288133ccd80655051025d9b42ee6a0a2000b3585dcd414409556d0d39a8288002ad61a735051016e5a3b4e6a0a204bb36859cd414400166b0b39a8288002e9a0a7350510005d2c14e6a0a204abb2809cd41440017630139a8288002ade1973505102555a432e6a0a2000bb3805cd414409576100b9a82882432d1d87350510006cab98e6a0a2000e3465d8d414409766d0b31a8288002cd61663505100d5d8c04c6a0a20059b48758d414400166f0ab1a828812ecd21563505100071a32ac6a0a2000ba78258d414400174904b1a8288082ece01635051054cdb438c6a0a204a9b58718d4144001d2ac631a8288002ada1a53505100055ac34a6a0a204bf175394d414409556d0d3928288002ad61a725051014e5a3b4e4a0a204abb2809c94144001763013928288002ade1972505102555a432e4a0a2000
  | 2 => 0x47458e100164e3a486b1c20048dc8750d6384005938e8a1ac70814e1fe157654e100045fc22eca9c20028bc845d953840090f90eb2aa70800a2fa1f7458a103045f438e8b1420048ee87d496284005958e9212c5080123b21d4258a100243fc3acb294200787d85dd9528400117f08bb2a50800a2f2117654a100046fc1aeca9420088dc835d952840010ff0abb6650800e1f21576cca100043fc2aec994200387c855d9328400117f08bb2650800a2f211764ca100247643ac49942000c6c75589328400117f08bb0650800a2f211760ca1028db442a649042000be3814c9208400187ae92a6ca880029d60654d95100143fc3aa9b2a2000a5f8359365440014b906b26ca880029be0964d951000536412c9b2a204fa74865076544001c68c8a0eca880030f5d074d95100052f418e9b2a2000a5d831d3654404b4ed023a6ca8813e9d60474d95100051f420e7b2a2000a3d841cf65440018bae639eca8813e9d60473d95100043f43e87b2a200087d87d0f6544001c3a8621eca880969e60072d95100043f43885b2a200087d8710b65440010ff0aba2ca8800237e0d74595100446e41ae8b2a20008ef825d1654400f1d904ba2ca880021f61e64195100043fc3ac832a2000a5f8359065440014b906b20ca880029be09641951000536412c832a204da7486504654400193ee821ec6880022fe1172d8d100145e422e5b1a200087e87d956344001878e9b2ac6880021fa1c6558d100061e3a0cab1a2000c3f65dd16344001878cbba2c6880031bd977258d100063632ee4b1a2000c6f651c963440018d8ca392c68800e1fa1f7558d100061fa0eeab1a2000c3d41dd5634400517d0fba2c6880030fdd77458d100061e3aee8b1a20008bf81dd1634400117b03ba2c6880021fe157458d1001c3e42ae8b1a20008df835d163440011df04ba2c68801e3b2097458d100045f438e8b1a2000c3f751d16344001878ea3a2c688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000657a0ee4b1a2000cad41dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c688003391cb7158d100061f3a6ca31a2000c3e74194634400187ecaba0c6880030f1957418d100046fc3ac631a2000a9c8458c634400159904b18c6880029760f6594d1012e3b38ecb29a20048f4865c653440018eecab8ca6880021fe157654d100045fc22eca9a20028bc845d953440011df04bb2a68801e3b2097654d100443f43ecaa9a204f87c86dd562440010fd0fb2ac4880030f1d365589100043f438cab122000c3c74195624400187ecbba2c4880030f19774589100062fb2ee6b122000c5c65dcd62440018beca39ac48800317194735891001c3f43eeab122000c3f41dd5624400187
  | 3 => 0xaa0a40008bc87595414800153f06b2a829015aa720d65505200055bc0acaa0a4001ab481595414800117f0eb1a82900022f21d63505200051fc2ac6a0a402fa3c8558d414800156f02b1a8290006ad205635052000557434e4a0a4000cac769c941480b174b03392829012aab2197250520006563b2e4a0a405bb2c855c941480b574f02b9282900032b1da32505202555643264a0a4000cac764c941480b76590a9928290002e9e05325052000c6f41ced98a40008bf845db314800517908bb662900030f19175cc5200061f3aec998a4000c3d75d9331480011bf0eb1e62900ba9721563cc52000d6a40ac798a4000cac645cb314815f6990a99662900031d9d761cc5200145f426ec98a40008bd84dd931480070fd0a3b262900021f614764c52000c6e43ac698a402ca5c8558d31480035a902b1a6290003331d9324c520575a642a6498a401096e859db2148001958c93b642900425b21573c85200061e326ea90a4080d6820dd5214800187eebb2242900030f1d764485200063a3aec290a401096e87dd5214807f8d8edbaa42901f71b1d87548520306563b6c890a4000d2c75d9121480091d90cb9a42900425b2157348520006b23aec290a4000d6875dc12148001ad6ea38242900425b21572cc1200043fc2aec982400387c855d9304800117f08bb2609000a2f211764c12000c7a40aec9824000c3c64dd5304815b17d0dba260902b22fa1f644c12030c5e43ec89824000c3f75d913048001878ebb226090003171d7634c1200243e43aa8b28400387e87dd563080010ff0aba2c61000e1f2157458c200246e43a86b184002c9c7450d630800187eeba0ac6102af0f1d74158c2001d2e42ac7298405387f855d953080090f90eb2aa6100123721d6354c2001c3f43eeab084000c3f41dd5610800187a83baac2100021fe15745842001c3e42ae8b0840078ec825d161080091e90ea0ac21013e1fe1576544200243e43acaa8840048f487585510800356903bb282100028fe15765042017d1e42aeca084054aac825d9410800156f02bb282100028fe15635042017d1e42ac6a084000aad86dc9410800556d0eb0a821000aad21d61504200071bc2ac2a084000e34855854108001d4ee4b0a8210153a91c9615042025753902c2a08404aeb2205854108095d4a40b0a8210153ac48161504200462f31aeb988402ea5c8558f31080018baeab1e62100021fe15764c42001c3e42aec98840048dc8758d31080594b90ab1a62100023b61b724c4200046fc1ae8b2c20088dc835d165840090f90eaa2cb0800e1fa1f7558e100061fa0eeab1c2000c3d41dd5638400517d0fba2c7080030fdd77458e100061e3aee8b1c206ccb710dd163840d996a21ba2c7080021fe157458e1001c3e42ae8b1c206c8be871d1638400187eea3a2c7080030f1d
  | 4 => 0x34800187eebb22c6900030f1d76458d200065a38ec8b1a40008be87191634800187eea322c6900030f1d46458d200065a388c8b1a4000cb764dc56348001968c9b8ac6900030fdd77458d200061e3aee8b1a40008bd81dd163480010ff0aba2c69000e1f2157458d200047bc0ae8b1a40018f4815d1634800187eea3a2c6900030f1d47458d200062e3aee6b1a4000c7775dc563480018e8ebb8ac6900032ddd37158d200065a3a6e2b1a4000cb784dc5634800196909b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a40008be87d0563480051790fa0ac6900030fdd74158d2055e1e3ae82b1a4000cb771d056348003968e3a0ac6900030f9d76418d200061ebaec831a4000c3e75190634800187aea320c6902c32b5c86418d200046fc3ac631a4000a5c8558c63480015a902b18c6900022fe117694d200145e422ed29a4000a5d83d965348001c3ea7b24a6900123b2197294d2000637b2ae529a40028be84dd9534800117b09bb2a6900022fe117654d200145e422eca9a40008df835d953480011ef02bb2a6900063d2057654d200443e43acaa9a4008a5c8359553480834e902b2aa6900123ba1b7254d20516b4296e0a9240b08bc865d332480c117f0fb2664900022f61f64cc920084b742ced192401096c855c63248001878c9baa64900030fdd7644c9200061e3aec89924000c5c75d8d32480212dd0fbaa64901cf1b1db754c9204fe363b0ea9924060cac76d913248001a58ebb226490003531d7634c920006a63a8c69924000d6875dc13248001ad6ea38264900022fe1175d85200145e422ebb0a40008df835d761480111b906baec290002ad60774d85200055ac08e9b0a400087f855cf61480070f90ab9ec2900022fe1173d85200145e422e7b0a40028be86dd161480c11790dba2c2900022fa1f64585200061fbaec8b0a4000c3c75d91614800117d0e322c2900030fdd464585200061e3a8c8b0a4000c9f64dcd6148001938c9b9ac29000327d9073585200064e320e6b0a4000cd4611cd614800517d09bb2a2900022f613765452000c3e43acaa8a4072a5c8359551480034e902b2aa2900032b1937254520024f5406e4a8a40008be869d9414800156b033b282900032d60676505200065b884eca0a4000a3f855d9414805f4790abb28290002a7e0d76505202b54e41aeca0a4000aaf825d9414800156f02bb282900be8fa1476505200051ec28eca0a4000c3e851d9414800187b0a3b282900032b608765052000657a90eca0a4000cac521d9414800517f023b2829000a2f604765052000657908eca0a4000cad211d9414800195c403b282900032b08076505200065b880eca0a4000cba101d94148001972203b2829012aab60b65505200045fc3ac
  | 5 => 0x31e5977054a200061f3a2cb9944000c3e655d3328800187acaba665100232798d74cca200064eba2c7994400087d86dd532880e70fd0eb2a651027e1f21d654ca2001c3f42ee6b0c400087d85dcd61880091e90ea0ac3100121f21776546200243e43acaa8c4001ab481dd9418800156f02bb283101570fdc565506200071bb8acaa0c404ae37105954188095c6a20b2a83100038b997725062000717328e4a0c4002ab68758541880055690eb0a8310003a9dc9615062000752392c2a0c404aea7205854188095d4a40b0a831000e1fa1576cc6200043fc32eb98c400087f8759731880010fb0eb2e63100123721d634c6200063732ee498c400087d86dd5218807f0fd0eb2a43101f61f21d654862058656b90c9b2a40048ed82dd365480014bd0728eca901572b5cb41d95200065a388c8b2a4000c9c64dcd65480018b8ca39aca90003271907359520006a6290e6b2a4000cb464dc5654800517d0fba2ca900022f60774595200046fc1ae8b2a40088dc835d165480011ef02ba2ca900063d20574595200045f438e8b2a400287c875516548005878e8aa2ca902cb171cd54595204ae3a38aa8b2a40088de87dcd654800193ee9b9aca90003271d373595200062fba8e6b2a4000c9f741cd6548001938e839aca900063da1f71595200065bba6e2b2a4000cb474dc565480019aee7b8aca90003351cf71595200065bc26e2b2a4000cb484dc565480018eeea38aca900032ddd071595200065a3a0e2b2a4000cd7731c565480019a8e638aca900022fa1f41595200145e43e82b2a4000c9f73d056548163938e7a0aca900032ddc7415952000e5a38e82b2a40008bd87997644800117f0eb2ec890002a7e0d65d91200054e41acbb224000ab781597644800156902b2ec890182aba1b52d912000717b2ea5b224060baa80d4b644801f17b0e30ec8900028fa1461d91200051ec28c3b224000a9e83187644800153b0630ec8900032d5c461d912030d57416ebb224060aad82dd7644800187aea3aec89000327dce73d91200051fc2ae7b224000a3c855cf644800147d0a39ec8900028f61473d912030d57410e7b224060aad821cf644800147f0ab8ec8900028f21571d91200061fc2ae3b224000c3c855c7644800147d0a38ec8900028f61471d91200054f418e3b224000a9d831c764480c355d0438ec890182ab60871d91203055d400e3b224061ab9801c7644800117d0f28ec8900022f61e51d91200054f41ca3b224000a9d83947644800117d0e28ec8900022f61c51d91200045f43c63b2240008bd878c7644800147d0b18ec8900028f61631d91200045f43863b2240008bd870c7644800117b0f10ec8901862fa1f10d91200045ec3e21b224000c5d75d4f63480010ff0ab8ec69000e1f21571d8d200052f42c63b1a40008be87d916
  | 6 => 0x51f420e2b2e4000a3d841c565c80fd8d8e438acb900021fa1f41597200043ec3e82b2e4000c3e87d0565c800187b0fa0acb902e38bdcb41597205b71639682b2e4054a3d8490565c80010fd0f18acb900021f61e31597200051f42462b2e4000a3d848c565c800147d0818acb900028f610315972003d3741062b2e4000a6d820c565c80a58d8e5b82cb900028fe1170597200051e422e0b2e4000a5f835c165c80014b906b82cb9014b1b1c970597200053bc0ae0b2e4000a74815c165c800147d09882cb900028f613105972003c6f43e86b1e4000c9d7410d63c80070fd0bb8ac7900021f6177158f2003c3fc3acb29e4000a5f8359653c80a74d904b2ca7900031b5957294f2002476412eca9e400787c8759553c80018dacbb92a7902825ba1f754cb2001c3f42ee6b0e400087d85dcd61c800517d09b9ac3900022f613735872003c3e42eeca8e40048ec825d951c80030f90eb2aa3900031b597725472025557416eca0e4000ab7815d941c809555904b2a8390002ade05655072000d5a40acaa0e40b7e2f8259541c80a9c5904b2a83900038de0565507200071a40acaa0e40b6c3f7159541c8001c6ee2b2a83900038dc4165507200055bc0ac6a0e4001ab48158d41c80c96590ab9283902d6e9e0572507203259642a64a0e4000ba7814c941c80070fd0abb663900021fe1975cc7200043fc3acb98e400087d8759731c81696990a996639000a2fa13764c7200045ec26ec98e40048ee82dd931c80031b90eb1a6390006b5205634c72059da642a6498e407e96e87dd521c802d2d90ab9a43900129b209655432000636b2ee4a86401696c855cb30c80010fb0dbaa61901c21fa1d654c3203743e43aca9864000c3c7459530c800187ccbba261900030f597744c3200064e3a2c6986400487e87951658800187ee92a2cb100121f21d54596200051f424a2b2c4000a3d8494565880014bd0728acb100029760e51596200063bb8ca2b2c4000c3f749d165880018bee739acb100021fa1f43596200043ec3e86b2c4000e1d4310d658800147f08b92cb100028f21172596200052fc1ae4b2c4000a5c835c965880014ef02b92cb100029d20572596200051f424e2b2c4000a3d849c565880014bd0738acb100029760e71596200063bb8ce2b2c4004a7a809c565880014f30138acb100028fa1071596200051ec20e2b2c400087e87d0565880010fb0fa0acb100030fa1f41596200061ec3e82b2c404aa3d8490565880010fd0f18acb100021f61e31596200051f42462b2c4000a3d848c5658800147d0818acb100028f61031596200253d40062b2c4000a79800c5658800147d0910acb100028f61221596200246e43a86b1c4002c9c7450d63880070fd0bb8ac7100021f6177158e200243fc3acb29c4000a5f8359653880090f90eb2aa71
  | 7 => 0x97309d1610c0abd2a613a2c218002b5e0d74584300456a41ae8b086000cb7875d1610c001d2f06ba2c21815ba520d74584302574b982e8b08604ae95305d1610c001c6ea92a2c218002b5e0d54584300456a41aa8b086000ab684dc9610c00156b09b92c2180029de1572584300053a42ae4b086008ad4835c9610c0014ed0a392c2180029d61472584300055b420e4b086000ab5841c9610c0115ad06392c21805eb560c725843002579400e4b086017af1801c9610c0015af06a92c218022b520d52584300456b41c84b086000ad583909610c0014ed0a212c2180029d61442584300243e42eeca88600487c87595510c0091e90eb0aa218006ad20776504300065bb8eeca0860028bf81dd9410c00196f03bb2821800a2f60776504302565a40eeca08604acb710dd9410c09596a21bb2821815aa720d76504302b64e39aeca086000ab7815d9410c00196ee2bb2821815b2720d76504302ac5fc0aeca086000cb7815d9410c09593e60bb2821812b274c176504302565b882eca086055c3f71595410c001c6ee2b2a821812b8dc4165504302571a882caa086000a9d86dcd410c00193aedb9a82181572bdc6625043000753b8cc4a08604aea710989410c095d4a2131282181572bdc5625043000753b8ac4a08604aea710589410c095d4a20b12821800aada1d61504302ae5b43ac2a08604acb587585410c0055690eb0a8218003a5dcd61504302b74a39ac2a08604ae9730585410c095d2a60b0a82180123b60976c843001c3e42eec90860048ec82dd9210c0091e903bb242180021fe15764843001c3e42aec908600087d86dd5210c00187cc9baa42182031b98b75484301fe3b30eea908600087e87595210c0010f90eb2a42180030fdd564484300061e3aac89086008c9c73591210c00193ac9b9a42180123b21d624843000637baac49086000c6c75589210c00199ee6b1242180031ddd561484300063a3aac29086000cd773585210c0119a8e6b0a42180123b209745972003c3f43ca8b2e4000c3f7495165c800f0f90eaa2cb900028fa1251597200051ec24a2b2e4000a5e8394565c80014bb0728acb9013f1b1ca51597202ae5639682b2e4000c3f749d165c80014bd073a2cb900029760e745972003d37414e8b2e4000a6d829d165c80014ed033a2cb900029d606745972000537c12e8b2e4007a6c825d165c800147d0939acb900028f61273597200062fb9ce6b2e4007a6e829cd65c80cf8d8e539acb900029da0673597200053ac0ce6b2e4007a6c825cd65c81418d8e439acb900021fa1f43597200043ec3e86b2e4007a6e8290d65c80014db0521acb900038750c43597200051f424e2b2e4000a3d849c565c80014bd0738acb900029760e715972003d37414e2b2e4000a6d829c565c81018d8e538acb9001e9b20971597200
  | 8 => 0xe212ca180021f61c42594300051f424e2b286000a3d849c5650c0114bd0738aca180029760e71594300051f420e2b286000a3d841c5650c0010fd0fa0aca180021f61f41594300061f43e82b286000c3d87d05650c09547b0920aca180028fa1221594300051ec2442b28600087e87085650c0010fb0e10aca180028fa1021594300051ec2042b286008a5e83085650c0014bb0610aca180129ea0021594300053cc0042b286000c3f759d5640c17753f06baac818022a720d75590300454f41ce4b2060baa9d839c9640c00147d0a392c8180028f61472590300051f42ee2b206000a3d85dc5640c00187d0bb8ac8180030f61771590302ae4f986e2b206055c9d30dc5640c17353f06b8ac818022a720d71590300045f43ca2b2060008bd87945640c01153d0728ac818002a760e51590300045f438a2b2060008bd87145640c00117d0f10ac8180022f61e21590300045f43842b2060008bd87085640c00147d0a10ac8180028f61421590300454f41842b206000a9d83085640c0095750010ac818002ae600215903000717aa4a93106000aae84946620c00155b0928cc418022b3a0e519883000566c1ca33106000aae84146620c00155b0828cc4180029ba17419883000536c2e833106000e2e85d06620c001c5b0ba0cc41812aab61241988300247743e84b1060048ec87509620c0014dd0a212c4180029b61442588300055742442b106000aad84885620c0014dd0a10ac4180029b61421588300055742042b106000aad84085620c01159d0610ac418012baa0021588300456641aeab106000a6e851d1620c0014db0a3a2c4180038bd52545883000557424e2b106000aad849c5620c0014df0ab8ac4180029b21571588300456641ae2b106000a6e851c5620c0014db0a38ac418002aba10715883000556c20e2b106008ace831c5620c00159b0638ac418012baa00715883000574c00e2b106000aae84945620c00155b0928ac418022b3a0e515883000566c1ca2b106000aae84145620c00155b0828ac4180029ba17415883000536c2e82b106000e2e85d05620c001c5b0ba0ac418023271cd64548300062eb2ee6a906000c9d64dcd520c0091d90eb12a41800333dcd62548300145f426eab0860008bd84dd5610c0031bb07baac21812a2f61e74584302555ac0ce8b0860088dc835d1610c0ab56f02ba2c21800a2fa1372584300045ec26e4b0860048f687d05610c0014ed0ba0ac2180029d61741584302ae5b43e82b086000e3685d05610c001c6b0ba0ac218157a5cc341584302af4a98682b0860048f487505610c0115a906a0ac218002ada1375584300055ac26eab086008ad683dd5610c02f5ab07baac218002ada1075584300055ac20eab086000a76859d1610c0014eb0b3a2c2180038da1674584300071ac2ce8b086055e
  | 9 => 0x71589300065a326e2b1260008ef87588624c0015c902b10c4980022fe1176949300145e422ed29260028be84dd9524c00117b09bb2a4981be1fa1b754c9300061e326ea99260a087e87d95324c00187eebb2264980030f1d7644c9300061e3a6cbb0a6000c3c74197614c00117f08baec29800a2f21175d853000c6e41aebb0a6000ab581dd3614c00156b023a6c2980022fe1172d85300145e422e5b0a605387c86dd5614c0010fd0fb2ac2980030f1d365585300043f438cab0a6000c3c74195614c00517d0dba2c2981b22f21b74585300061fb2ee8b0a6000c3c65dd1614c00117d0fb22c2980030fdd764585300061e3aec8b0a60008be87191614c00187eea322c2980030f1d4645853000637b2ee4b0a6000c6c65dc9614c00195ec9b92c2980032b193725853000637b28e4b0a6000c6c651c9614c00195ec8392c2980032b190725853000672308e4b0a60028be84dd9514c00117b09bb2a29800e1f214765453000c3f43ecaa8a602fa3e85dd9414c00147b0bbb282980022fa1a76505300055ac0ceca0a6000cb5819d9414c00196e213b282980028fe15765053017d1e42aeca0a6000a9f835d9414c00155f04bb28298152ab20976505300055bc0aeca0a6000c9d831d9414c00517f023b2829800a2f60476505300064f988eca0a6000c9d311d9414c00193c603b28298003270c076505300065b880eca0a6001ab681d95414c00156b03b2a82980be8fa1b65505300061f3b6caa0a6000c3c76d95414c001c6d03b2a82980038d60765505300061fb8ecaa0a6000e3771d95414c001c6e21b2a82980022fe1d65505300045e43acaa0a6000a3e86195414c00187cec32a82980030f1d865505300054f434e6a0a6000c9c769cd414c0d372b0339a829812aa721973505300064e3b2e6a0a606bb97815cd414c001938c93b662981ba97a1b65cc5300070e320cb98a6000e1c65d93314c0e1ca863b2a62981b7a50c7644c5301652f436ca98a6053c5c76d95314c001ca8c3b2a62981bf171d8654c5300070e320ca98a606cc9c76d91314c001c38cbb226298003a5187644c5300072a32ec298a600087f855db214c0070f90abb642980022fe1176c85300145e422ed90a600387e85dd9214c0010fb0bbb2429800a2fa1376485300045ec26ec90a600387e859d9214c0010fb0b3b2429800e1f21476485300043f436ea90a6000c3c64dd5214c0010fd0fb2a42980021f21f65485300061fbaec890a6000c3c75d91214c0e18b8e7b2aa09800317d9773541300064e326e6a8260088dc835d1650c0090fd0f2a2ca180030fdd254594300243e43aa8b286000a3e84945650c00147b0928aca1802297a0e51594300061fba4e8b286000a5f835d1650c0114b906ba2ca180229720d72594300452f41c84b286000a5d83909650c0010fd
  | 10 => 0xb2a6070a5e831d3654c0a74bb063a6ca980029da0474d95300053ac08e9b2a6053c5c735cf654c0a70fd0fa1eca980021f61f43d95303870e21a87b2a600087e8710b654c0010fb0e216ca980028fa1271d95300051ec24e3b2a6000a3e841c7654c00147b0838eca981c297a0c71d953029d2ec18e3b2a600087e87d07654c0010fb0fa0eca980030fa1f41d95300061ec3e83b2a600087d878c7654c00147d0918eca980028f61231d95300051f42443b2a6000a3d84887654c0010fd0e10eca980021f61c21d95300051f42043b2a6000a3d84087654c0e14bd0610eca980029760c21d953029d3d40043b2a6000a7980087654c0a78f0e0b86ca980028fa1310d95300051ec2621b2a6000c3c65dd1654c00517d0fba2ca980030fdd774595300045ec0ee8b2a600087f855d1654c0011bf06ba2ca980022fa1c74595300061fba8e8b2a6000c9c74dcd654c00117d0fa0aca9800a2f21f41595300043ec3cc832a600087f87590654c0014bf06b20ca980038760c64195300051ec08c832a60bce1e30190654c179c3860320ca9800297a1a43195300070e3248632a606fa5c8650c654c001c38c8a18ca980028fa1261195300051ec24c232a6000a5d83984654c00147d08308ca980028f61061195300051f4368232a6000c3e76d97644c00117b0f32ec8980028fa1665d91300045fc3acbb226000a3e86197644c00187cec32ec8980030fd9571d91300061e32ae3b226000a3e85987644c00147b0b30ec89806e2f61c61d91300065ab88c3b226000c3d751d7644c0dbc3ca7a9ec8980028fa1672d91300051ec2ce5b226000cb7719c7644c00147f0ab8ec8980028f21571d91300061fc2ae3b226000c3c855c7644c0db53d0638ec8981b2a760c71d91300045f43ca3b2260008bd87947644c0db53d0728ec898002a760e51d91300045f438a3b2260008bd87147644c00117b0f18ec8980028fa1631d91300051ec2c63b2260008be87887644c00117b0f10ec8980022fa1c21d91300045ec3843b226000a3e85087644c00147b0a10ec8981b6a7a0c21d91300054ec1843b22606caba80087644c0015730010ec8981b38e94350d913036c5f43e21b2260008bd87c43644c0a78f0e1b2aa698002b360c21d893000574c0043b126000c3e74d96624c00187ce832cc4980030fd9574989300061e32ae93126000c3e75d92624c00187aebb24c4980030f9d464989300061eba8c9312600087e87d95624c001878e9b2ac4980031d1c765589300043f438cab126000c3c74195624c0018e8e232ac4980030fd9774589300061e32ee8b1260008be87d91624c00187eebb22c4980030f1d764589300065a38ec8b1260008be87191624c00187eea322c4980030f1d464589300065a388c8b126000c7765dc5624c0018e8cbb8ac4980032dd93
  | 11 => 0x540e18beca39ac4a80023be1d621895037c3e432e7292a01096d87d8a525409b0f90cb8ca4a80121f616768c95001c3e428ec992a00787c859d8325400117f08bb064a800a2f211760c9500062ebaec6192a00187c855cf615400117f08b9ec2a800a2f21173d85500045fc22e5b0aa0028bc845cb61540df0fd0db9aa2a81f61fa1f62545500055ac0ceca0aa000a3f855d9415400153f06bb282a815aa720d765055000557c12eca0aa054aac825d9415400156f02bb282a812a8f219755055000596412eaa0aa0beb37815d541540110f90b3b662a80022fe1176cc5500145e422ed98aa0018dc835db31540018baebb1e62a80121f219754c550314b6412ea98aa0018de87d8d31540035ad03b1a62a80121f61676c85500045fc22ed90aa0028bc845db21540011bf06bb642a80223720d76c855001c3e428ec90aa008a5e8394565cc0070fd0fbaac5980021fe157458b3001c3e42ae8b166000c3f75d0562cc157878eba0ac59800a2fa1372587300045ec26e4b0e600187d85dd951cc0011df04bb2a39801e3b209765473017d1f42eeca0e6000a3d85dd941cc09553d07bb28398002ade0576507302b64e3b2e6a0e60bdb97815cd41cc00147f0ab1283980be8f21562507300055bc0ac4a0e6001ab48158941cc0594b90ab126398006b5205624c7300043fc2aed90e600387c855db21cc0010ff0abb2439800e1f21576487300243e43aa8b2c6000a5f83551658c00517d0fba2c5180022f6077458a30016563a484b1460048ec87509628c00117d0fa0ac51800a2f21f4158a3003c3ec2eeca9460008bf845d9528c00517908bb2a5180023de057654a3000c7a40aeca946000c6c75589328c0070fd0fbaac31800317a0f75586300062ec1eeab0c6000c3f41dd5618c00187a83baac3180021fe15745863001c3e42ae8b0c60008ef825d1618c00f1d904ba2c3180123d21d415863027c3fc2aeca8c600487c87595518c00356903bb283180028fe15765063017d1e42aeca0c6000aaf825d9418c0a955904bb28318002ade0576506300064f3b0e6a0c60008bf87589418c0011790eb12831800aada1d61506300155a43ac2a0c6000e3785585418c001c690ab0a8318003a5dcd61506300074a39ac2a0c604ae9730585418c095d2a60b0a83180022fe1176c86300145e422ed90c600087f855d9218c0070f90abb243180022fe1176486300145e422ec90c60048ec87589218c0018d8eab1243180030f5d254d95300052ec1ca9b2a600287f87553654c00147d0928eca980028f61251d95300052ec1ca3b2a6000e1d83193654c00147b02326ca980038719243d953029d2e43287b2a6000e1c6450f654c00147d0930eca980028f61261d95300051f420c3b2a6000a3d84187654c00147d0da0eca982af0f9db41d95300061eba0e9
  | 12 => 0x29b6174198a505c71742e83314a000e2d85d06629416dc5ceba0cc5280038b94f4198a505c71629e83314a000e2e51d066294171c58a3a0cc5281578bd434198a502af16a8683314a000a6f85506629402d4d90aa0cc52805a9ba163198a5000536c2c63314a000aae848c6629400155b0918cc5280029be143198a500b53642863314a000aae840c6629400155b0818cc5280123b21d4258a5000536c2884b14a000aae84885629400155b0910ac5280029b6142158a500055742042b14a000aad84085629400159d0610ac528002b360c2158a500257540042b14a010a6e851d162940014db0a3a2c528002aba127358a5000556c24e6b14a000a6f855cd62940014db0a39ac5280429ba174358a5000536c2e86b14a000e8d4310d629400155d0938ac528002ab6127158a5000537c2ae2b14a010a6e851c562940014db0a38ac528002aba107158a5000556c20e2b14a000ace831c5629400159b0638ac528012baa007158a5000574c00e2b14a010a6e85d0562940014db0ba0ac52830b8ba174158a5000716c2e82b14a010a6e858c562940014db0b18ac528002aba123158a5000556c2462b14a000aae840c5629400155b0818ac528012baa003158a5000574c0062b14a0a087c8758d529402dad6e5b82a5282872b98974cca50006573a2c5994a000cad7458b329400f8dcc4bac652819f1b98b754ca50086363aac4994a007c6e625d432940218dceab1065280031b5d5620ca500043f43ca6b0ca025a768194d61940fd0f90ea92c3280123d21d415865000d5a40eeca0ca000ab7815d9419400187aedbaa83280038758e535065012d9b40ca6a0ca000b398094d41940a9c5d0b31283280038bdd662506505bf163acc4a0ca000e2e53989419416fc58a73128328003a9dc662506500071728cc4a0ca0b7e2c519894194095c5ea1312832812b8b542625065025753884c4a0ca04aea5109894194001d4ee2b12832812ba9c41625065025752882c4a0ca054e2e62549419404b66902a92832800aada1d61506500155a43ac2a0ca025e3785585419404bc690ab0a83280038ddd561506505571a3aac2a0ca000e36535854194155c68a6b0a83282ab8dd4961506500071aa92c2a0ca04ae37505854194095c6aa0b0a83280965720d75cc6500062ebaac798ca016c6e7598b31940018daeb31663283079314e62cc650086373aac598ca000c6d7558b31940091b90eb1a632800317dd5634c65000637bacc498ca016c6c759893194181c98a731263282ff9514d614c65002476c12ed90ca007c6e625d721940091d905bb243282031b98b75486500247643ac490ca010c6c7558921940014bb0ba1ec6a800327dd043d8d500045fc22e5b1aa0028bc845cb63540011bf0eb18c6a8002a72116318d5026c3f436e2a9aa09f87f8754f62
  | 13 => 0x6363aec4992622c95e87dd5324c4cf8b8edbaa6498803551c7754c9315062e3b0ea9926200d54711d5324c401a98ebb126498803531d4624c93100ceb43ee29926200d5475dc5324c4033a903b8264988023be0975d813103c76412ebb02620087f855cb604c4070f90ab96c0988023ee1d601813103c3e43aa8b2e420387e87dd563c840187e83baac7908030f5077558f210043fc2ae8b1e420387c855d163c84111ef0cb8ca79099e1fe157654f2103c3e43acaa9e42028be87dd160c840156b023a2c1908030f5d254d95210143fc3aa9b2a4200a5e8399365484014bb07326ca908030f5d074d95210062eb98e7b2a420087e87d0f65484010fb0fa1eca908038750c43d95211fd36c10e1b2a420087e8710365484010fb0e206ca9080297a0c40d95210052ec1881b2a4280a6e8210365484014db04206ca908fe9da0440d95210053ac0881b2a420087f855d165484011df04ba2ca908021f61e64195210052f41cc832a4200a5d8399065484014eb03320ca908021fe1d641952162d37c12c832a42028df8750f634840593ce8a1ec6908030f9d36598d210061f3a0cb31a4200c3f655d26348401878caba4c6908232718d7498d210064eba6c731a420087e87d9563484010fd0e32ac690b131bdc86558d2101c3f43eeab1a4200c3f41dd5634840187a83baac6908021fe157458d2101c3e42ae8b1a42008fb805d163484091f100ba2c6908031b1d77258d210046fc3ac631a4200a5d83d9653484010ff0abb2a6908023be097654d210443f43ecaa9a423fc7471d95524840187ce9b2e64908030fd9574cc9210061e32ae99924208c9c635d3324840193ae9b1e64908031d19571cc9210466a31ae3992427d87e86dd5324853f0fd0fb2a64908fe1f21f654c92161e36b90cb302423f87c86dd560484010fd0fb2ac0908030f1d365581210043f438cab024200c3c74195604840187ecbba2c0908030f19774581210062fb2ee6b024200c5c65dcd60484018beca39ac0908031719473581210047dc3ac030242048dc8750d63940014bf0aa1ac72800b271d14358e500043f43ca2b1ca070a5e8394563940e14bf0eb1ca7281bf17e1d6394e500070fa0ac729ca00087f865ca53940cf8dcc4b94a72814e5ee197094e503763dc32e129ca053d6a625c253940a7ad2c4b84a7280034ed057094e5033d36c3ca7314a06fa6e8394e629402dc9d0729cc5280029ba065398a5029d37c04a7314a053a6d8094e629402d4dd0ba1cc5280029b6174398a5000537c2a87314a016a6c8550e6294001d1a8621cc5282029b61e5198a5000717424a3314a000e2d8494662940014dd0728cc52800393a0e5198a500052741ca3314a000e4d83946629409b4dd0328cc52805b99a065198a5027d37c04a3314a04fa6d80946629402d4dd0ba0cc528
  | 14 => 0x761dc96050401b4e21b92c0a080369443725814100697ba8e4b028200d2c751c96050401b1ee6392c0a0803631cc725814100657b18e4b028200cad631c9605056d95ec2392c0a080369d84725814100657300e4b028200cac601c96050401b4e20392c0a08036944072581410069bbaee2b028200d3475dc56050401b2ee7b8ac0a0803651cf7158141006d3b96e2b028200da472dc560504033750fb02c0a0b276cdc760581412ae1fb0aea3028200d37615d46050495a6e20ba8c0a092b4d44175181412ae4fb0ce63028200d97619cc6050495b2e21398c0a092b6544273181412ae4fb0ae63028200d97615cc605049593ec0b98c0a092b275817318141256cb882e6302824ad95105cc605040117b0f318c0a0803275ce631814100557414c63028200c9d7318c60504ab95ec3390c0a080369d867218141256d3884e4302824ada5109c860504ab95ec2b90c0a080369d857218141256d3882e4302824adaa105c86050495b4a20b90c0a08036a44172181410064eb9cc43028200cad72988605040193ae6310c0a08026ee1d6018141645d9c0ac030282018dc835d165cc4110fd0f2a2cb988030fdd254597310443e43aa8b2e6295c5c7355165cc58f8b8e7ba2cb988030fdd274597310452f41ce8b2e6200a5d839d165cc4014bf06ba2cb988229720d74597315962e39ae8b2e6208a5e839c965cc4e78b8e7392cb988229720d72597314fe2e398e4b2e6208a5e8390965cc4014bb07212cb988021fa1c42597310043ec3884b2e6208a5e839c165cc4e18b8e7382cb988029ba0a705973100536c14e0b2e6200a3f845c165cc40147908b82cb988229720d70597313762e398e0b2e620087e8710165cc4010fb0e202cb9882297a0c40597310052ec1880b2e6200a6e8210165cc4014db04202cb989069da0440597310053ac0880b2e62088ee87d0962cc4070fd0bb82c5988021f6177058b311fd2e41acb2966200c5d655ce52cc4031b906bb2a598803175977354b314fcaf43eea99662028be87dd160cc40156b023a2c19880e1fa1772583310043ec2ee4b0662018dd83dd3654c4050ff0eaa6ca9880297e0d54d953100636328e4b2a6200d4c531c9654c4011df04ba2ca9881e3b20974595310047dc02e8b2a62048f8805d1654c58d8beebb9aca9881e3ba1f725953100657a0ee4b2a6200cad41dc9654c4018deea392ca988b317dcf6554d31536aa29ee2a9a62008bd879d3624c40517f0eba6c498ac62fe0574d89312b45ec0ae9b126202cae7490b624c4051df0ea16c4988021fe1570d893101c3e42ae1b1262008ef87588624c4014d90ab10c4988063721973949310062fb2ae729262019d4815ce524c40517d093b2a4988022f612765493103c3e43acaa926207a6c82595524c4031bd0db9aa4988b25721570cc93100
  | 15 => 0x4ba8c4a0a5a6de0575189412a696412ea3128200d37815d46250401a6902ba8c4a0adb0fd8575189410069bb0aea3128200d37105d4625045b36f02b98c4a095a2f61f6318941004d7c3ac43128200b2c85588625059774f02b10c4a08034b5d75218941004dbc0aed2928200c3d76d965250401a3ae729ca4a0802cb60a53949411fd9b40ca729282009b581dd952504ad33d073b2a4a08026760e76549410049fc2aeca9282009af825d9525040136f02bb2a4a09524f21d65549412a596412caa9282cab3781595525052ba68e2b2aa4a09524f21d535494120e9a38aa6a9282019b687dc5525040536d0db8aa4a080a6d21b7154941004dac06e2a9282019b481dc1525045f27d0b3b664a08024f61676cc9410061f42ced9928200c3d859db32504ad95c653b664a095b2b4ca76cc9410145fc0ced99282028bd819db32504ad93e633b664a0803274c676cc9410065b884ed99282009b7815db325040196f02bb664a08032dc4176cc9410049fc2ae1992822f93c855c3325040127f0abb464a08be4f215768c9412a4d6412ed19282009b7815da325040136f02bac64a08066d205758c941004dac0eec992822f93e859d9325040127b0b3b264a08024fe15764c94117c9e42aec99282009b7815d9325040137700bb264a092a6e201764c94117c9f43eea9928200d3471dd5325040187ec3baa64a08034dd87754c9410069b886ea99282009b7815d5325040336902baa64a08024fa1c754c9410069a388ea99282569ae87d893250401a58ebb1264a08034b1d4624c94100cdb43ee29928200d3775dc53250401a68ebb8a64a080a6da1b714c941014da436e29928200da762dc53250401b48c5b8a64a08026d603714c94100cda40ee099282019b4819d8325040136f02bb064a0adb0fd85750c9410069bb0aea1928200d37105d4325040536d0cb8864a080a6d219710c9412a6cb992e21928254d95325c4325040136f00b8864a08022fe19700c9410045e432e019282019b6815c0325040135f04baec0a09526b20975d81414b4dbc0aebb02822d9b7815cf605049517b0fb1ec0a08024fe1572d814117c9e42ae5b0282299b7815cb605040127f0ab9cc0a08be4f215739814100557414c730282a8db171d82605045f27d0fbaac0a08030fd8775581410069bb0eeab028200d3710dd56050401a6a21baac0a080347dd773581410068e3aee6b028200c9f61dcd6050401b2ec3b9ac0a080365c437358141006ca886e6b028200d1f751cd6050401a38ea39ac0a0ac727d847358141006cbb08e6b028200c9e601cd6050401938c039ac0a080365c407358141006ca880e6b0282008be87d8d60504ad938e7b1ac0a095b271cd635814100697baee4b028200d2c75dc96050401b1ee7b92c0a0803631cf725814100657b0ee4b028200da
  | 16 => 0x594320452f41880b286400a5d83101650c80f4dd04202ca190029b60840594320053b40880b286400a7581101650c80147d09882ca190028f61310594320043f43820b28640087d87041650c80147d08082ca190028f61010594320452f41820b286400a5d83041650c80f4dd04082ca190029b608105943203c7a43a82b0864028be87dd1600c80117b03ba2c019002ad60474580320045f43e82b0064028bc87d05600c805970e9202c01901e3e21d405803200c3ec2ee9b1aa2d5c5d75d8e63545018deca392c6a880237e1d6318d51164aec3ec729aa272a5d87d8e53544018bb0fb1ca6a8b1b87d076394d516370ea0ec729aa27d87c865ca53544990f90cb84a6a88029b61442d895100477c3ac4312a280a6f8558862545410fd0fb1aa4a89321fa1b705495100c3ec2ced992a200cae74d8b32545010ff0abb464a88061f219758c95100c3f436ea992a20187c865d432544018daebb1064a893f1bd9672981510047dc3ac0302a24fa7b85580605445f87eedb2acaa08032bd877259541006d3b0ee4b2a8200da710dc965504a9a5d0a392caa08034bd94725954100696328e4b2a8200d2c531c9655056d95ec2392caa080369d84725954100697288e4b2a8200d2c511c96550401a5ea0392caa080369c4072595416a69bbaee2b2a8200da772dc56550401b48e5b8acaa0a5a6de0575d8d4117c9fc3aebb1a8200d37815d76350401a6902baec6a08030fd8575d8d410069bb0aebb1a8200d37105d7635056387ec2bacc6a08034dd857598d410069b882eb31a82d3d9571d8e63504ad95ec7394c6a095b2b58e7298d415b657b0ce531a8200da7619ca6350401b4e21394c6a0ac72bd857298d41006d3b0ae531a8200da7105ca63504ad53d0db1ac6a0b4b65dcf7158d41004cfc3ac631a82d1b978158c63504ad53f0eb18c6a080327e1d6318d4158d4fc0ac631a8200e978158c635040153900b18c6a0b43a5c416318d410049fc2ae431a822f93c855c8635045336f02b90c6a08024fe157018d4117c9e42ae031a8200c9d635c06350403369033b4a6a08026de057694d410058fc1acb29a8200b2c82596535059f66f02b2ca6a0a574d9c56594d41014db432e329a82029b4865c6535059db2ea6b8ca6a095b6514d7194d41004dbc02e329a82019b6815c2535040136b03bb2a6a08024f6167654d41004d7c12eca9a82549ac825d9535040136f02bb2a6a08026ee017654d41254dc402eca9a825693e87d95535040187eedb2aa6a0802ab61b52d89410049fc2ae1b12822f93c855c3625040127f0ab9cc4a08be4f21573989412b64f39ac731282cdda571d8a625045f27d0fbaac4a08030fd8775589410069bb0eeab128200d3710dd56250401a58ebb12c4a08034ddd771589410069a3aee2b1282ccda772dc562504a93590
  | 17 => 0x266400aad8204164cc811938e6b22a599003275937354b320145f426eab0e64008bd84dd561cc8ad56b033a2c3992c6ade0574587320145f426e0b0e64008bd84dc161cc8070fd0fbaac1990031ba0b755833200636c16eab06640087f855d160cc8070f90aba2c19901e3720d74583320061fbae82b0664abc3c75d0560cc80f0f90eaa2cb1900e1fa1f75586320062f41eeab0c6400c5d83dd5618c80187e83baac3190030f50775586320043fc2ae8b0c640387c855d1618c80f1d904ba2c31900a2fa1370586320045ec26e0b0c6400c3d74953654c8050ff0eaa6ca990028fa1251d95320051ec24a3b2a6400a5d83947654c8018eae328eca990029da0664d95320053ac0cc9b2a6400a3e84987654c80147b0930eca990028fa1061d95320051ec20c3b2a64abc3e76d07654c80187ae83a6ca9919f171cd73d953233c3f43e87b2a640087d87d0f654c8e7c3886a1eca9919f1b1c972d95320051f424e3b2a6400a3d849c7654c80147d0838eca990028f61071d953239d2f418e3b2a6467a5d831c7654c8018eae238eca990021fa1f41d95320043ec3e83b2a6400c3e87d07654c80187b0fa0eca990021f61e31d95320051f42463b2a6400a3d848c7654c80147d0910eca990028f61221d953239d36c10e1b2a640087e87103654c8010fb0e206ca991ce97a0c40d95320052ec1881b2a6467a6e82103654c8014db04206ca990029da0440d95320053ac0881b2a6400a3e84c43654c80147b09886ca990021fa1c10d95320043ec3821b2a6400a3e84043654c80147b08086ca991ce97a0c10d95320052ec1821b2a6467a6e82043654c8014db04086ca990021fe1574595320043ec3cc832a6400a5d83990654c8014ed03320ca990029d60664195320043fc3ac832a6400a3e84984654c80147b09308ca990029760e61195320051f420c232a6400a3d84184654c8cf8d8e5b2aa6991cf171cf65549320062fb2ee6a9264028f787507614c80117f08b86c29900a2f21170d85320043f43ecab0a640087e87195614c8cf0f90dbaac0990021fa1f65581320061e3a6cab026400c7471d95604c8010fd0e32ac0990030f1d065581320063a388cab026400c3f65dd1604c801878cbba2c0990031dd9771581320063a32ee2b0264008fb87580604c80f0fd0f2a2ca190030fdd2545943203c3e43aa8b286400a3e84945650c80147b0928aca1902297a0e51594320061fba4e8b286408a5e839d1650c8014bb073a2ca190028fa1271594320051ec24e2b286408a5e839c5650c8014bb0738aca1901e9b20971594320051f420e2b286400a3d841c5650c8010fd0fa0aca190021f61f41594320061f43e82b286400c3d87d05650c80f4dd05382ca190028fe1170594320051e422e0b286408a5c835c1650c8010fd0e202ca190021f61c4
  | 18 => 0x8002000000800c004000001000000a0040040000004000001800400c00300100140020000018004000004000001400000200000140060030008004000001002000000200500100200000000018004000000000001c01800100100000040000000024000002001801400400700080040020020018004002001000800000000100080040040000000018000005000000000200000b00000000040008030002001000000801c008000001c006000001000800a00000500140000040000000000005002000000000300000180020000010000010001001001400c001000800c0000050010020008000002000000000200080500060000040018000000002000c0060020000000002001001800000200000000080060000018020006001000000000a0020010000002000000000000000000080140080000038010004004001000000e0000000000002002002000401a00100280000080030018000002000001801c006000001000000400300000180000010008010002002001000000000000400000020000018004002000001806c00000000000000000000000000004008002000800e00100000a2fa1372586530045ec26e4b0ca6088f4875056194c014db0a10ec4a9802b360c21d895300574c0043b12a6008ef875886254c0117f08b86c2a980a2f21170d855333e37b28e4b0aa653c6f659ca6054c011f70eb00c0a98021fa1e5158e5239d2f41ca2b1ca473a5f8758e53949418bf0eb1ca72900387d056394e5233cb7c32e529ca49fc6f865ca5394801a5e82b94a7290021fe197094e520043f43ca6b0ca4028df8750f635480593ce8a1ec6a90232718d7498d520064eba6c731aa400cd7635c663548119a8c6b8cc6a900237e1d6318d523f43f436e2a9aa4028f787507615480117f08b86c2a900a2f21170d85523743fc3aa7b02a4dace972d8260548e78beca39ac0a90023ee1d60181520452f41ca2b2e6400c3f759d564cc81153d073aac999366a760e75593320051fc2ae4b266400a3c855c964cc9b153f06b92c9990028fa1771593320051ec2ee2b266400c3e85dc564cc80187b0bb8ac9990028fa1671593320051ec2ce2b266408a9e839c564cc9af53b0738ac9990022fa1e51593320045ec3ca2b266408a9e8394564cc80153b0728ac9990022fa1c51593320045ec38a2b2664008be8788564cc80147f0ab82c9990028f21570593326b54fc1ae0b266408a9c835c164cc80147d0a382c9990028f61470593320454f418e0b26643ba9d831c164cc94355d04382c999002ab60870593320055b408e0b266400ab5811c164cc81153d06282c999002a760c50593320045f43e20b2664008bd87c4164cc80117d0e082c9990022f61c10593320051f42820b266400a3d8504164cc81153d06082c999002a760c105933250d5741020b
  | 19 => 0xe00000000005fa000000000000000034100008620004e511ec11c3363130000dec3eb0000b309b877100000000006e70000000000000802003e002002800800600200000140020070000000002000001800801a00400080000040040050004000000002000400000100000000060020000018000003006800000800100100040080000000008000001000003400000a0018004008002000000000000000000080020000040008000000000003800000c000800000200000300000220000000000004000000000800000500200000040000018000000001000801800e001001002c000000000001c002006000802c000001006000000200c0000004004000000801c004000000001000000300000000020000010004002002000000800a00100100100100010018014004007000802800c001000000000800300080040040000000008004005000000c00600b000000800800000080040060000000008000000006800001c000000800000a00700000000140000018008004001000803c000000001002000c0000018004000004000801c00c00100180080080000030010032000000000000800000180080020000008000000004001802c000003000000000a001002800c008000001001400c0000000000006003000000400a001000000800c006000000000400000b8000000005000000000400a00300000080030000008004001001000c004001000000400c000000000000c00100000180020040000000006005000800c0000000000000002000004800000000f00400000080010020004002001000800000600400300000000140008054000002005800000000000000040200010040004000000001800400200300480200080000078018010002000001801600000000280100000008004006000000000404200a0000008000001003800c0000000000000006001001000c0060050008008000000001000c0020020050000000000000000800800100100040080060048000000007000000400000100400000000010000000002002001000400400a0008004008006001001c00200000080040000030008004006003003001800800100080100000010008008004007000000800e00100000040000000000004004001000000000000000300040000090018004000000000000c01400400180000000020000000000003000800400000100000000000020030000006003000000c000000002800002a003004000c00000000300000060000010004002001007800000000100000000000000030004000002004800400000100000040040020010000000000000000800e00300000040020050000034004007000000c00000000000000320060008014000002000000400800300080000000010010008000000005800800a0020000000000001000800
  | 20 => 0xc000056a2b70000d88ad40e23338000420000299853891484d00000009f89380000000da400044e20c891c00035416982cea0f459a1940007530002850ce022b4dd000093084a2d695dcfdc7d700000000000000001fec00000027a8000aac1b3000000000028e342874c5b6000000000069636000021a860c0002e3171c0000000001efc8186fe000269d10800000000000000ea4c200000000001cb12340000003f980000008e02178b1c47245100004f4cea00003e8ac8b32000000023d2ae52c501a3a42bc0000002498faa4b239e26683984f400000000000000b28000000000000000000088618000000000002a880000004af00003900000000000000000000000244c00000000000007ce0000001a1838a00036d8fbc444578000000043a0000000000cde00042e00009fe82a50380000206894f89f14c7e84e01180000000000c000011e800000000007ba000000282d3f84bf1208b8077800016f126433800036c100000041e1790b3800003a000202000000040f9d9400012e165a53800000000014a800099f46494448fa96000014ec0000fd00017b00000000001adc0000090000f4c000188265000000070f2549b242860000db0dd000000000005e0000000000245c0000000000d58a5200000000000002e2000000071079a00000011167292c08e0d32c9b20000000dd000000d00007340000001d146de5012c1a4943b009a0dba5184165bc16c04c0a480001fa1ea002649d481019ccb2268000086cbb200000011c00e63ed00020fc0008600bb13510ce0003b611a854438400000011c26914051254f0606d427a42c1b826100021ec0002910000000c38663000000000000010380000009c945000000002e828914c40009cd00000002948e700018c810400030d113865a49002b0ac41961832ac0bf899073a15e8000ce60000001c58000442000000135e43000010182b25693bea7187f63d2336000000086f00000000003f100000000004a700016100005fd1c026440000e8000112c0000000ec9990a3497c05514f805245d3e0a14cfcc59743f97d08da05a47581f0cee86e3f808a00c08d110b81ec0002080000000d7a00000013a4d4a00000002cd0480002baa53c0d04f6000243800000000001e93680001d580000000001ff9e18000000000000033c803000121c95c0b638c00000000000000744cd40000000cf0f9c6870001fb04e400000001d865e22618709b0000000000268015c0002a6a57cdbe2754cc8890000958332800032800000011040000004f08000fe4715000091000000026600000006552f69f1c81450d395a2d40007124bd0000d3a000013226d2225bf49a8d38b3a0004388664cbc00021705200661f32c498bc0003fe2b186a801e00000211140000000000000000359000000000000000011213e
  | 21 => 0x96e4920bac00000000009a807e62a028800111e9920000d188c07db2d590d0000000000000000087a0001ab40000992a620f449080e000000077a361000070c0000000dc9cfd38200000000007440000000a845a4000203800000000009600000007cd00000000002840d28ba538e00000014b50447fc0c280000008bf04420ac27e00019100000000000558000d4200001508806500001811c0000000039980004120003c99b4caca2b00001b5400000000003bcf00000428a1dc7b6000000000019c00000021b0966000000000000000000007a141034502285c4a307c000000000006ea07197981a49df4820001084000000000000000000000012b4940000000000035317c00010d2000000000000000000000000000001d2000078e84305923c521279c0068000c40000000000000000000005e869000000015d00000000e4a2203881a82b68a7816867e000050505e91e00000008a60004718000b8a0000a30000cb4000497a3a000063100006740004f82dd2684bbe80c28a1f4c41c0001901d990be128000051c000000000028424c00000000000009940001bec00000002180009360000000000a442761f50000f620000000c8c95a00001d9c990128ed3238000000814000000018291b0000a4120c00001c0001162000164800000000035e1a880003a600027300f268400a23bc000000000036835e0000000d9c49643e0a981340000000001ae0d1000002382900009492d7128800056e00000000008ca346000000000000000003c677400016d0df0000000098c00025c13e000048600024480009702f430211987908c04b5832541c00000000000000002789a7c61000000000010a47a33c50218e6204a3500e640001e6000000054c75b09895189029210000c9421211400d87a80007bd00027f821031400002e12c481814600011b28b900000000003cc00000001a656b239000000097338280000001040870000000000223000000000024f0c1cc6843d0001694e3e00036419fc0000003168cb8bae53900006180007c92582654000974000000000031709207686087e800000000ae53f2d922a4bec912077083c75438f499925000096945b00000887a52358604000000380800099611a3210ee0000993113a7ac00089e00018dc0000001559e101d200000001900005472c3a09c0c608a0fe19200007030000000000000000130c00000000015551f400000000000000000cc180d3063151d61050e18951112a4e876853c000182c6f20000000000000000079a5a800047f000014013e70e0000e2c6e00590000dc53880000001a540ca00000016080006cc05e9dd43d800000000012b62c00001eb46f0000078000138a00027f24c44344d734711b074018c23227a83f45442e8a2bca6c09b2990e6c28a88133300008ee4b126
  | 22 => 0x8de00033100000002ba00000004ba0004ac800000000044c80000005d23e502e8000000157906400070743c1a48000151000222400000000000005d44864f8000000000000022f0000000000000132e84c29700013ca0000000e1d27a5bd1c89e891180000000000c760000001c5c0002111b90000000000103202ca7a57b0b0a094cf6000000000000091a14e80000000000000aec0000001af10d45aa4bc41c8f411ea5420000d8c000000000000078657306f09fc34c3be442a5980000001a383ac5fe88a28d961888882c1a08e7c000000471248c39076f2bf1e54cda8fe0da031c000845275106ca2a1cb2e8000100800031c85ac0006b22f58534c1c947000000079c2000861974db40004bb000027618e38e14a000074900009f8000000094a15002c00039906900005fe0e0224480a00000000000000001d792b00000004aa8000da028232087b4f4e3a70f28000000987000000000008400000000000003ac800001609715523b8000762000155c0000fe0001a6c0001b249d950d0761402621c205c641f00010240009d000000012fe0212a50000d609b91f7009c9a000019800000000003ab1d1c1e21de10180000000003d0a348176000000000000000016782342be9a8403262000072a00000000006ec0000000d2800000013140000700738000a1e00000004600006300000000f640000000000000000000123d01e0000f3a0541da47608b093471291615a150131c000004103800022d384949c0785254669934df25042611d44000972467229c0000004fc040c0004a84d4800037a00045180012ce89a0001d1800007400000000009bb4bc8e8cd2c0002108c3000000000000000000003968550bac2601bf2748cf04634861c4d3dc6c33900000a0c11c00000000000003e6120cc1a00000f0e9453e02c31408b80000000eb90a800000000020749be000000224800000000000003ac000000224c0001ca14d0f00dca2952cda404000312420000000000000000000001370000000000000000182925447a000137902000046d800000052108800000006c600024ac4946f7000000000000000000010d61e10000e180000ec000270c5e62873a1000000000036083e0be609538a08f49f4000000281400000000000000008ab021000000000000000006d0000000010137a8f24ce9fd4d000002e680646260001620b0851448b4b817c800096412491d0d560000000000000281000000024400000000000006f34d70d9800000038113a0ef200022b08fd42442811496b009c820000046c86c0001f0a2c93b09ed2818e5c0000004f4000000024c000247c00007546b07880007b30c8a21c1184033fe80000006744cf01fc41400012d83d8b82000000000097c72436e8000d1a77e04880000000004df8000d2e0004c6a8000
  | 23 => 0xb3403646e85f0e7c3ad137a20c00077a34f000080200004b116d0fa0000c9000048e000269800000073738d89e440402447818145942d105186580501155069df000033142c148cfce6aa0001d7840a00035c800101a00031b000000000000016900904820001b9940c00011e23cc8c2039000000102e449000106857230d000040800000030f80009e437d4239270b160c84ee1d0000023336f09b4ed258f48785480003553ea0bb12bc7874ed865cfb206e19a81a88bc40d4ee86d52ba00116c81540008262a580000000004de193800060c40c962806e00000000009766bf0181d7c5cc00000000000004292ed8ed42fa000000000133641500020e815e0003d60000000723000062d22000028984f87184ec37d189092e000000157000086100000000000002858cf460a66b000000125a216170848cb527cf17693b93020003c4800100a44a0000ec40005ca00000000007b90000000f8800033887dc08c3b21a880006b60000001fa80003760000eb86ba7e905385cd2389563720d10d4c00000019707ca0003db0c25354093159a0e13f62a900b95fc01421c195915c1a81252d7a1750622d73d7a7e4a3c8a60b602244b000000024d89723103b59f440fc4f000010c894800000019488400002cb0000f2e4170060a1884a60832b80007ae0000000000c700003b3800001c0001628d3c0005c90000c7800000000000005ce46918c8000e6c5e00001dfcdea00048408790b26d70a8000000056230e915517a75d0001ae8be20000000000b3c000000001c2f60002d518b92d00000000f440000004639c2d2a66291c0992c2d098a0e813800005a33ee24a400011900013bc2c80000001f48dc28b43888cfd07c97b199800000000000024c0000000000000133818200000000001392d800012903ca2cf80000006120e10f880000000000d400000000e6800087400000000000002310001f605100000000000eb85c40000000aba00000000007300c2000110c0000000619c751700002b880000000000000000000289000000103c5e80000fc00004e406a847435200002e800081e0001be283003e0000000000000000240000000081315fa34112c6be0ba18894088ea00014ac0002153d00000ac00004ff9e780001ba0000c590c83640000ca4e9e777000000000000000000000000000001e48000872054800000000000018e8f4c000330800000019b00000000000000002124000000000000090800020900000009ec000047c9540001ba80b49b21f10208000c0400030b80002c022f00022845be2e400026b43dc0000000c440008fc0000d083600001ce8000000790000000000000035600000000000000000cac8572711bf00000003a4000136a292000000128479b34c136927e91d42b10e10420002c2a290ad000000022f82780000
  | 24 => 0x2e70908162000403991400000302fa34c4802510000000dc09d521d9d5d12a49f28b9c1872626900000000003f9465947000000010900000000002c88000f3a00000007800002700000000540000208a0447c60003938aa115000022a20091f20002118000d5c0a619b8000a0009021213980000001b615400000001ea17b869400000027000008d800008d91820000000a348443323c780008a4000000000000078200000013ea8970a6068052e4920000000b1800000014d40000000000360e6800000000000a40000001fac0000490001c8400000047d800084e7e5140181c56c4712b800008a069a0000000d8e965400800000014400007040000000000f80eda95c397274d3c8000396000000000000000009820003d480000000000000000a3a00049e0eec0008660001660c220000000ecd0da3a92b30000d680000000000000000000000000000000010581f64e339c013113a5924168000e9a4881d400006064d200007e00007ab00000001c00000f7a5e03fa95209a099cbce00012f80000000002d4000000000000006b40000000000000dfa0004c1000088e6ff22c80000008c80000f640005930000000b8635c00013ec00097d4f483941e85cb41494dc00064a00e0be41ba00008b9aa400085e0fb22dc0001e43fb19e80009ac419a6148101072d89318e5e00000000000000d908308d0c4e000000000013a9d4000000037c0000000f900003ba11085c121428533c80000002c300000000009140fd800026c00007305d400000001a05545ba00000c2234ac800032000000000002c80000000000000000000000000000000005cf000000000000019c124c0c20001908000ba863d4c48000d6a1bf000186c00027b1ef8000e203183f113cccec95400000003d260104c14bc85635a248a4c86805761ce1840f7c81623e27cc65400025a86102cc000118208ca9c09e152a0d50900001bf99a0b405b64560000ff09a3328159c00027117a80000004a100000006d6000000000000000000000000000000000000346000208007418a9f40000e54000000000000000038e00024648ca16e3b0000103600000012dc0000002e40000000000000000000019000015c80000001270f251f00003ac20b80000830000000000000000044400000000000007aa7e439e9f8cb2813a00000000000003a7000000051630aa240000580000184c0a856100004b4f9040228c80000003e90001e200000004b78000000000298153d0604f905fa330f2838a06b0fd8c4a00000000000008e44eb8e84baa609000000000000013c012c1b600000000000000000000c2800055319d188cbc60000ae9ad80002e5000116000050c263a31800000028281a534439000000006a427a00000000007550001b3400000000000000000000000fc80001272f5117c
  | 25 => 0xc0000f52d10bc4000000000211883019f04a000000000000000011866ed00025d400000035d80880003b70001c693bc0fa4fe80003e05b53ee82f800062b3bc000000000005e0000000000000000000000000005c83a472800007500009d90001d2c9fa2c636714980ee0002b7996099a2ef4a80000c0c0000000c3c00015b4d300000003dc0000738ee084b31a962102494a43827384320cd2db9d051b89ab0c4840448c000000139c0000000000400d5e000000000000000000008e8000000116000000000000000000000004582488000508152014c000000000032864e9052fb96ec52c26211f06acf8463c0000000000000000000000000000000000d60000e380080006542f480004bc0003ad0000000977000000120e0000000f2c00008b00000000009b800000000008a5000000000040b000095c0001db0898000f3e8d5400260021411250480f89da00012c94240002563f080b85b85f90959d306a81f21cf1d4020a8bb310957830e6c0321a8400000001b297c067210f10c094800088000000000000000000000cb60001538fa000000000000ac21a0001db0000000000000000055a50a1668000b801a20cd1ea8f705fc00010b0e765ef21e11885064671ed1b6406a1f50000000af400000000002d486249a000000003d07c800000016200023f44ee30b000037c4700003298000000000000000051e67200000013186ca0001c340002c1000133c00000002c00000001fe0000ceced400045114e8000796000000000000013320d00007f700000000007da34e15b09ee0002af80007720000001230d140000000000000944000000000000037800011ae26517d80000000001a1800105000046200000000000ad000000000000000006929713de137410055a00000000000000000000000000000000141441d1c90bf02ee57d00005580000003a90f580000000000b500009e32530810000000056000000000000000000000000000000da899800003000003fd063000129a0000000000bb8000000000000031d39a800000000000000000000000d7000000000000000000000000001e048380000ac16e000058e08f1a8c38c00000000010fc00000005bc000538000000000087900000183b800000000000000000000000ca279809c14080000002261ec00006cb0000a8cd3200000024343620000000db80000000002708c2800000000000000000000000a8a4b400019a40005de39c80012820002ce00000b67fe25d00000003fc00005e43f20d73b900011cc00023c8f986981f424d0804d2000000000012c600040d1e90d2670407e27d800000000020f000033e000000000000000003c918a00005b82d44fa18f00000004a88ba3d717e88b48443911baca924b61298968de40003b182a0ec829c4a289cc1722743539f58000294
  | 26 => 0xf00000006e60000000000000000000000000061600000000000ff00021d41608ad00007540000000000000bc200000000002c600000009400000001ab8bc000092c3c280000007b414ca6dc09e0000000af8636385000000041a7f43dd156c254000000000000000000000000000000001790bfe2ac0002350a9000042d80000006d100020712d80004db0cb046496149f1d111b400000000000009a40001a0cb7200000000012960000428f14000000000000000000000021d800a43900000011300000001e3825e0000001bbc00000015c00000007fa1e10000fc0000000000000000000005b40cc83600000000000000c680000001950001fe40000001e69c7805e000255800000000000000010b44780a79f0d4220c418d00011549e20001fb48080005008000ba6000067a80913e44d3a180000d831f00009b80002fa0a580c40000f736200000001b8000000000000048a8000cfa5da38c8fe02427bb1e79b3c000000000000139e0000000000940644287084cbf69372a08b4c0c4157000125800000033e18ccc7c0000001a04f6a0d13c580000005a11808f10e6053400000003140003ef00000000000500000000000000000000000000000000000000001e300001a1000000000020c1ec00001443c611a800000061e0000000000000039000000000000002b52066b100027e80004ce3371bd0aa44eb000186000047317b800000029b0001f2c00086800000000007544df0a4c00062c000262d2727733b080000000003718b680001ff0001a3cedc00000000000000004eb088c5166490000c980009cb4d285f80000000001b140003c100000008b80000001acc216776135973000065f4c3128d0e60001a680000001cf0000ded2da43f42815640000000000000bba000264a2b8ef61bc0000270b1a02500000000000324d824a0000000000008112800000000007e600000000008d000000000000004e148c093d1d892e1b4944053000000015511844d500000013de42d0000000dd23bf47b183c00078d00025f80006d6000000019800000017d43be70a00000000005791c1021c1248e52fc20dc0240110000850dc40000000ab8c8c132000104c00026400000004aa874000113d42600000000000000001fb8774000000038a6c4f8c46e00011001a000000010dc7288414c780000009da00026cccc0000168000000000000023fd2860004f31f40bca2f63522640f221354f90de80001203f780003582bc0000d7c00047e0379edd2400004e40e349ac74a00011d44762c81bb800000000000000005ac4bd0000000000000219800000042600000009ca36a000274400000000000013c07ff00022080000a537715f07ea22a000279c00000000005700004c0000147c76033437881e111c5203cc81711be0002f119300007252d3887
  | 27 => 0x1a70b4a5300004d100aa18d0aa17f0c9800000032400004cc000000000141c0000000001fc4b2a87c0409b700002ee00000001c25be000000000000000008dc0bc8cf0000f780000000001da03d64db47b9760000000000000000000000024000000003000000c9e3fa1f6170800000024280006386c230ca37800036d34580006b000000000002925b3122850894a0000dd800124e7d
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2912000a00431d16080721000000000038370018223e0336312a2c00173d11351e003a090040422f143023100533190d2b13200c013b241c0000413c0f3f1a25153428062d260e2e271f4402320b00041b00390700380030e4c00012282132e04499020000410140142e96944725954100543a4e511c9655040142e9614472595414c44da63615d763504014989058d7018d41006499c48259653505b99248220575189414c44da63615d462504014949644073581410052364c601c960504014a4964407258141006235ce8298c605045d05c9760e4259731006131ce829c165cc401a0e84a0e5198a500068361283946629416f22d989474198a5000583a4e51d0662940016269194e62506506f50ba5e51989419400160e9394662506500048da625358541941bb23498549615065000525646301d9414c00109d980c0765053000525644301d9414c00123598dc7655053000525644649db314c0016159119065cc5305a6131ca8394565c800186472a067359720006131ca839c565c802d06c976083159720006131c8835c165c80018647220570597206e6892088159541c800123698dc565507200050b255211d9414800142e95880765052000529646201d941480014a591080765052000728485101d941480018a5811da72505200060b214765c9414800182c851d93250520006291db814c9414800184c851d9324c520174172617558f3108001234966177350510006291da829cd4144001494965cc73505100060d21c6558d4144001a246520963505100052525d6318d41440016849258c63505100048d259851c941440050b4976183250510006c8d95821c14144001b206560870505102650da5b755053044099434965d541c811000668dc8875052044099c3076195414811000568a5e8250520440955a09760941481100066821d82505204414f72095609414811053dc82553250520441b7740954c93148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x3
  | 8 => 0x4
  | 9 => 0x124d
  | 10 => 0x124e
  | 11 => 0x8a
  | 12 => 0x8d
  | 13 => 0x8e
  | 14 => 0x98a
  | 15 => 0x98d
  | 16 => 0x98e
  | 17 => 0x128a
  | 18 => 0x128d
  | 19 => 0x128e
  | 20 => 0x150a
  | 21 => 0x150d
  | 22 => 0x150e
  | 23 => 0xca
  | 24 => 0xcd
  | 25 => 0xce
  | 26 => 0x9ca
  | 27 => 0x9cd
  | 28 => 0x9ce
  | 29 => 0x12ca
  | 30 => 0x12cd
  | 31 => 0x12ce
  | 32 => 0x168a
  | 33 => 0x168d
  | 34 => 0x168e
  | 35 => 0xa4a
  | 36 => 0xa4d
  | 37 => 0x134a
  | 38 => 0x134d
  | 39 => 0xb0d
  | 40 => 0xb0e
  | 41 => 0x154d
  | 42 => 0x154e
  | 43 => 0xb4d
  | 44 => 0xb4e
  | 45 => 0x16cd
  | 46 => 0x16ce
  | 47 => 0xb8e
  | 48 => 0xbcd
  | 49 => 0x3ca
  | 50 => 0x3cd
  | 51 => 0x3ce
  | 52 => 0xcca
  | 53 => 0xccd
  | 54 => 0xcce
  | 55 => 0x15ca
  | 56 => 0x15cd
  | 57 => 0x15ce
  | 58 => 0x170a
  | 59 => 0x170d
  | 60 => 0x170e
  | 61 => 0xd4a
  | 62 => 0xd4d
  | 63 => 0x164a
  | 64 => 0x164d
  | 65 => 0xeca
  | 66 => 0xecd
  | 67 => 0x17ca
  | 68 => 0x17cd
  | 69 => 0x98955
  | 70 => 0x98956
  | 71 => 0x128955
  | 72 => 0xb4956
  | 73 => 0x94b55
  | 74 => 0xb89
  | 75 => 0xb8956
  | 76 => 0x14a
  | 77 => 0x2c9
  | 78 => 0x198a
  | 79 => 0x14c9
  | 80 => 0x99255
  | 81 => 0x99256
  | 82 => 0xd49
  | 83 => 0x17c9
  | 84 => 0xb8b
  | 85 => 0x1849
  | 86 => 0xb8c
  | 87 => 0xb0995
  | 88 => 0x98b15
  | 89 => 0x154995
  | 90 => 0x99555
  | 91 => 0xb8996
  | 92 => 0xcc995
  | 93 => 0x98cd5
  | 94 => 0x15c995
  | 95 => 0x995d5
  | 96 => 0x1609
  | 97 => 0x130b
  | 98 => 0xa4b
  | 99 => 0x150b15
  | 100 => 0xb9516
  | 101 => 0xcd515
  | 102 => 0x150cd5
  | 103 => 0x17cb
  | 104 => 0xb49d5
  | 105 => 0x9cb55
  | 106 => 0x16c9d5
  | 107 => 0x9d6d5
  | 108 => 0x1789
  | 109 => 0x130c
  | 110 => 0x14c
  | 111 => 0x5c9
  | 112 => 0x134c
  | 113 => 0x168b55
  | 114 => 0xbcc
  | 115 => 0x164c
  | 116 => 0xa4bd5
  | 117 => 0x138e
  | 118 => 0x164a55
  | 119 => 0xa5655
  | 120 => 0x1a09
  | 121 => 0xeca55
  | 122 => 0xa4ed5
  | 123 => 0xd5355
  | 124 => 0x17d355
  | 125 => 0x44a
  | 126 => 0x2cb
  | 127 => 0x1a0a
  | 128 => 0x14cb
  | 129 => 0x1a4a
  | 130 => 0x10a
  | 131 => 0x4d
  | 132 => 0x180a
  | 133 => 0xa0a
  | 134 => 0x130a
  | 135 => 0x138d
  | 136 => 0x40a
  | 137 => 0x20d
  | 138 => 0x160a
  | 139 => 0x188a
  | 140 => 0xd0a
  | 141 => 0x140d
  | 142 => 0x5ca
  | 143 => 0x58a
  | 144 => 0x24d
  | 145 => 0x178a
  | 146 => 0x18ca
  | 147 => 0xe8a
  | 148 => 0x144d
  | 149 => 0x104a
  | 150 => 0x19cd
  | 151 => 0x194a
  | 152 => 0x1a8a
  | 153 => 0x14cd
  | 154 => 0x74a
  | 155 => 0xd4bd5
  | 156 => 0x140e
  | 157 => 0x17cbd5
  | 158 => 0x144e
  | 159 => 0x44c
  | 160 => 0x5cb
  | 161 => 0xe8b
  | 162 => 0x198b
  | 163 => 0xecd55
  | 164 => 0xd4ed5
  | 165 => 0x17d655
  | 166 => 0x19cc
  | 167 => 0xb89895e
  | 168 => 0x138955
  | 169 => 0x95455
  | 170 => 0x94b96
  | 171 => 0x184e
  | 172 => 0x10c
  | 173 => 0x10b
  | 174 => 0xb4996
  | 175 => 0x16c996
  | 176 => 0x409
  | 177 => 0x184c
  | 178 => 0x104c
  | 179 => 0xb5516
  | 180 => 0x16d516
  | 181 => 0x151555
  | 182 => 0x184b
  | 183 => 0x150b96
  | 184 => 0x185516
  | 185 => 0xd455
  | 186 => 0xccd5
  | 187 => 0xda55
  | 188 => 0x585d1
  | 189 => 0x1696d5
  | 190 => 0xa59d5
  | 191 => 0x94b56
  | 192 => 0x150b56
  | 193 => 0x1516d6
  | 194 => 0x184996
  | 195 => 0x44992
  | 196 => 0x45712
  | 197 => 0x45892
  | 198 => 0x1a57d2
  | 199 => 0x1a8c
  | 200 => 0x5255
  | 201 => 0x139255
  | 202 => 0xd59d5
  | 203 => 0x21555
  | 204 => 0x155415
  | 205 => 0x140b15
  | 206 => 0xb4b96
  | 207 => 0x17d9d5
  | 208 => 0xe8592
  | 209 => 0x256d5
  | 210 => 0x16d455
  | 211 => 0x144b55
  | 212 => 0x19d4d5
  | 213 => 0x1a4ed2
  | 214 => 0x1712d5
  | 215 => 0x170b55
  | 216 => 0x1715d5
  | 217 => 0x170ed5
  | 218 => 0x150996
  | 219 => 0xb49895e
  | 220 => 0x2cb93
  | 221 => 0xb82d3
  | 222 => 0x151856
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2238
  | 6 => 5834
  | 5 => 2581
  | 4 => 69
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (92504+((h/746+packedAt gbK7 (82806+(h % 746)*13) 13) % 4323)*13) 13
  | 6 => packedAt gbK6 (307248+((h/1944+packedAt gbK6 (280032+(h % 1944)*14) 14) % 10249)*14) 14
  | 5 => packedAt gbK5 (163459+((h/860+packedAt gbK5 (152279+(h % 860)*13) 13) % 4533)*13) 13
  | 4 => packedAt gbK4 (4991+((h/23+packedAt gbK4 (4830+(h % 23)*7) 7) % 83)*8) 8
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fe0f01ffc0ffffe0ffffc03f027a33e19f3f3
  | 1 => 0x83ff001c1ff0f80ff0f01ffff1da5cc7164c9f
  | 2 => 0xfc3fffe01fff000fff001ffc0e1c60f9e78f1c
  | 3 => 0x3fffffe000000fffffe0000fe07f01f80fe0
  | 4 => 0x3ffffffffffff0000000000fff8001fff000
  | 5 => 0xffc0000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x440100024010a22011444092000811a009131
  | 1 => 0x82a5010d0990d04490a08952c0ca0c45124486
  | 2 => 0x680a7620162a00ab2a0152a8261460a8658b18
  | 3 => 0x2033ab574080410dcccb80304b607601b80ec0
  | 4 => 0x423ccd9b9bcce5c0808200c08dff0001df6000
  | 5 => 0x73000e0203088601080c03030fbffbf6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37035
namespace PEqualNP.Outside.L_meta_37035
open PEqualNP.Outside.L_meta_37035.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 10 := bs2_3_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 24 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 117 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 69 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_2560 : Interval gbAtlas 5 2560 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2581 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))))))
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
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5834 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216))) (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)))))) (concat (concat (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568))) (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)))) (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952))) (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))))) (concat (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)))) (concat (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))) (concat (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))))))) (concat (concat (concat (concat (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040))) (concat (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424))) (concat (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))))) (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)))) (concat (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)))))) (concat (concat (concat (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512))) (concat (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)))) (concat (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896))) (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))))) (concat (concat (concat (concat bgb_6_5120 bgb_6_5152) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))) (concat (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344)) (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)))) (concat (concat (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536)) (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632))) (concat (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)) (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824))))))))
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
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2238 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 bgb_7_1344))) (concat (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632))))) (concat (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920)))) (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 bgb_7_2048)) (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8feeaeee8faeaeac8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37035.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.or,[1,4]⟩,⟨.and,[2,6]⟩,⟨.or,[0,8]⟩,⟨.and,[7,9]⟩,⟨.and,[1,5]⟩,⟨.or,[0,11]⟩,⟨.and,[2,5]⟩,⟨.or,[3,13]⟩,⟨.and,[12,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37035

open PEqualNP.Outside.L_meta_37035 in
theorem PEqualNP.Outside.L_meta_37035 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
