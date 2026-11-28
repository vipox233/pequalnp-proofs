import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37365.Model
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


end PEqualNP.Outside.L_meta_37365.Model

namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
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

def SBf (j : Nat) : Nat := [4, 6, 6, 4, 4, 4].getD j 0

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

end PEqualNP.Outside.L_meta_37365

namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
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
  | 3 => 2*((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffff822596ef
  | 2 => 0xffffffffffffffffffffffffffffff844aab77
  | 3 => 0xffffffffffffffffffffffffffffff88934dbb
  | 4 => 0xffffffffffffffffffffffffffffff911c71dd
  | 5 => 0x21e07e1e
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc000000000000000c000000000000000c000000000000000c000000000000000c000000000000000c000000000000000c000000000000000c000000000000000, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x210020c1016ed21ef21ec20f610bf41df31dd31be40f410de30bd41bc40dc30ee20
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x195414c74a8290f14c521
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s1K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/1+packedAt s1K3 (81+(h % 1)*2) 2) % 3)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f80fffe03ffffff01f83f07ff07fffe88e3f
  | 3 => 0x3fff00fffc03fc0ffe003ff83ff83e030f3cc
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80840a022048480016284508450842a8334d5
  | 2 => 0x5155294651a92934781522a46aa46b55288a2a
  | 3 => 0xaa64aa6a94a3b215bab0433d233d2381b0d34c
  | 4 => 0x3346cd8d193223a6dcd9ea0843ce71063d03b0
  | 5 => 0xc3870e0e1e3c3c38ef1e73ce720842183eec00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0aaaaaaa0aaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2010c0020df31f610ed21bf41de30be40dd31f410bc40dc30ef21ee20bd41ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1a5414872a8298f14c521
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
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
  | 4 => 2*((h/11+packedAt s2K4 (224+(h % 11)*4) 4) % 14)
  | 3 => 2*((h/1+packedAt s2K3 (81+(h % 1)*2) 2) % 3)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x3f80fffe03ffffff01f83f07ff07fffe88e3f
  | 3 => 0x3fff00fffc03fc0ffe003ff83ff83e030f3cc
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80840a022048480016284508450842a8334d5
  | 1 => 0x5155294651a92934781522a46aa46b55288a2a
  | 3 => 0xaa64aa6a94a3b215bab0433d233d2381b0d34c
  | 4 => 0x3346cd8d193223a6dcd9ea0843ce71063d03b0
  | 5 => 0xc3870e0e1e3c3c38ef1e73ce720842183eec00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xaaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888aaaaaa88aa888888, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
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
  | 3 => 2*((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x7f01fff80fffe07fe07e0f83ff07fe07f44e73
  | 2 => 0x7ffe03fff01fff81ff800ffc1ff83ff818739c
  | 4 => 0x800003ffffe00001fffff0001fffc0001f83e0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x108100881024000028a1104220842a28194a5
  | 1 => 0x2aa529946a548ae8f0548aa35546b415544a52
  | 2 => 0x4c954aa528d91a2b75410ce919d23950586318
  | 4 => 0x68d9b3464c91d34db9e7a8421ee710619e83e0
  | 5 => 0x70e1c3878f1e1c71de79cf73908421861f7c00
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xaaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8aaaaa8a8a8a8a8a8, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def s4K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt s4K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x7f01fff80fffe07fe07e0f83ff07fe07f44e73
  | 2 => 0x7ffe03fff01fff81ff800ffc1ff83ff818739c
  | 3 => 0x800003ffffe00001fffff0001fffc0001f83e0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x108100881024000028a1104220842a28194a5
  | 1 => 0x2aa529946a548ae8f0548aa35546b415544a52
  | 2 => 0x4c954aa528d91a2b75410ce919d23950586318
  | 3 => 0x68d9b3464c91d34db9e7a8421ee710619e83e0
  | 5 => 0x70e1c3878f1e1c71de79cf73908421861f7c00
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xaaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def s5K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 3 => 2*((h/1+packedAt s5K3 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x7f01fff80fffe07fe07e0f83ff07fe07f44e73
  | 2 => 0x7ffe03fff01fff81ff800ffc1ff83ff818739c
  | 3 => 0x800003ffffe00001fffff0001fffc0001f83e0
  | 4 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x108100881024000028a1104220842a28194a5
  | 1 => 0x2aa529946a548ae8f0548aa35546b415544a52
  | 2 => 0x4c954aa528d91a2b75410ce919d23950586318
  | 3 => 0x68d9b3464c91d34db9e7a8421ee710619e83e0
  | 4 => 0x70e1c3878f1e1c71de79cf73908421861f7c00
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xaaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8aaa8a8a8, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def q2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q2K6 : Nat → Nat
  | 0 => 0x14000801491c01c0240080000055000780444141fe41fe10fc21fd41fc20fe30ff10fc30ff21fc31fe20fe40fc32fd43fe43ff43fc43ff31fe42fd31fd40ff32ff41fc41fe32ff42fd30fd21fe31fc10ff30fd20fd32ff40ff20fd10fc42fd42fe21fc40
  | _ => 0
def q2K5 : Nat → Nat
  | 0 => 0xc83be4350f7aa998ef50c43f7a14655d53042fca7a17d90431bf28e85fa401037e87216f15130bf28c857e53086f8a918fe50040bf28c617d538c6faa788778ca30bf284417e544c3f460186fd0641bfa9e41bf4310fee6290eb50842be2a443ee52d0f7e86215fd5020bf2a061bc42102f8a710efd0a42f6a9487df534437886207b10820bfa9841bf4210afca990df94720be29a85de324c7ee21084f55010f6a96837e54c83ec43885f14930b6292217e50107bca6206f50841be2a0617e500c3baa6105714d10df212857e5310ae8a2907ec8220deaa4437c54082dea4885f94843fb98821ed4210bbe87995f94732fc980617f544cafea2997e84010f699241f7414867aa990f714d40f7a12437f540cbbc86195f94031de21e85dd320cafca8105f54b41bf29465fb10443ec8210ef55010b729683bf411077ca810774c930bea9843fa20082f8a6885b94b43faa0e21be4350afaa2105f94830be292877d52842f8a89977d0f31b7a9261f551d0efca7905f94c40be2a6617d52cc3e86290df55020f7296637e500cbbe639877d0c30bea9687df300c3eaa2206f10f41bfa8a61bf43106fca110df944419f2a6657d544437aa8107710f31deaa6437e50cc7ea4210fd10631bea9a417e528c6fca9087bd0b21dea1e817d538c2dca518df94321f710841ec52442fea710df55021f6a1065be548cafca4215f54e21faa8c657e508c37ca918df94c31fa18821be40503ec6390fd145209eaa0613e548cabaa710d794c40f7a9221bd415037aa918d794e21fa18c437c53502fca598df54840be292837f54c82f8a690db94a43daa0883bd4390bd88490dd14530bea9e81f421042fea9986f90f41f799265f741042fca520df14520faa8841ed32c83da8410df14b10f7210857d54c86fea9185f14e10ef19061f641c43baa720fb50a21ef19663ee420cb7ca8185f94810ee99463f631442faa720dd54743bfa9e217f52502faa9216fd0d40be2a6633f544c2fca8206f50040f619441be41902fea918d714d40baa8881dd320c7bc8618fb48520f7192417d529037a86a05f15310bf29a437d5110bea43885f94431bfa8265f651d0f7c82a0df54032bf29621bd4310beaa2187b90821aea9c83de434c2f8a990f714d10bfaa443f7314c6faa6885f55010f7a10417c544c6faa118dfd4121f6a9463ec21883baa7215f148109eaa4437e518c7de4210df94910dfa128176510c37c87205f94021bea86857e541073a8621df94f10f6a9061ef32487de65195fd4b10f6a96877f548cafea6a06f95221dfa1c837e518867aa9995d94732fb880217d51103da43907bc8520df21881ee32c83dc8510fb94a43bf28685dd434c2fca6087710d32bfaa063be41102eaa3995f94020bf294217f53883eea2985f54321baa8c857d5110efaa9985f95121
  | 1 => 0xc328c3bc6318774c030b7290217d53903d884995bd4940f6192437f5150bf681207bd0a20be28a657d5210efca221df94c30be29a837d5088678a8905d94440fb90a43dc318c37ea8985f94a30bf28481be42d077a842177cc530bf280877d538caf8a4885fd4d20fc900417f53486faa9186fd5120f7290217f53507f680a05f54e42beaa261de324cbe882085fd4a10be2a4656e52cc6f8a8195f94b40fb18843f7418c6eaa321dfd4910bea9621dc434c67ca990df54e10be2a2217d51d03da85907794e41ef29841ed21086fca2207d48510bf2a085ee32086faa9195f54c20bf29683bc42d06fca3a05f94e21bea96817c544c2fea9105f54243afa9a41bf54442fca7105f54f20ee188617d50106f8a9085f94442bfa90217f544c6baa7217ec4210bfa9261ec32c87bc62185fd4141fb28861f510043dc4290df94e41bfaa043df4390fb887185f15220beaa6637d50087be86a1df15121bea9e437d52886fca41977cc631faa8e856e52102fea498fb10a32f6a96637f53086fca5a1f70cb31bfaa421bd41d02faa5187d94742efa9a416d520c3da8490770c830bfa8a817d54842f8a9995f95331b6a94637e54886fca2106f15120bf28c657d51883ee63087b4ca21baa8e857e51906fca89077cc431bf29063de43cc2eaa2185f95110af29c833e540c2baa6107d0c610efa9a817e50842f8a8085f14c20f6292817751482baa790fd8c710faa8c87dd53102daa520cf95020bea8c617f54482faa8195f54043eea1e617d510cafca521df94821f7212413d540837c84a0fb88120dfa0a817f53442fea7087b50b32be28a817d5190fd88590df54042bf2a0217e508cbd8a4985fd5110f6108417d54c83d864105754f42dea12817d53d07dca518df54730bf2a6217f5050afca4107d50731bf2a4637c5050afca898ef95321bea90837651d0b7e81205f14c21bb28c85dd53c87be65985f94e42bea94417d51843b886185f54c40eea9e857e5090feca2107d10531bea9e857e5310efaa921df14542bf2a4417c54c83dc85997750e32fba0c21ee32886f8a2a1df14143beaa263f421842bca7215f15120fba8a417e5090afaa018ef90a40b6a94877e50d07dc85907bcca20beaa463f621087bc87195fd4143beaa621f531c87daa520d7d4d10f790441f741886fca7a0efd0f40bea8e857e510cafca5987b94830faa8c857c53882faa6085f55121bf298656d52042baa6206fd0040f790c43bc42903ea8218df54430bf286657e540cbbe8698ef10e40ee98e615d53d06fca1a1d7d4d40de212837d534877a8520db14940baa88417f51482faa818df54232de21a837d52cc77ca998fd90731fa98a21df438c3baa6086fd0b40f7a1265ed520437c84205794f41bba8a61f741507ea8210df94231ef98461df328cafaa1a1f754e21fba0
  | 2 => 0x202c0f4001bc000684c1589b008000dc001a402000000002601822020730400000001178010000507c0400000000433040109068a606803803024242585100c00000000ac3b004121b0000d461008000045f000020042b0b80f0142101412018000205704d3a0540200000000004640012858101c9054000000001005038c8090b1a400102c16008130025e25c133a41d000280243d00c4d009e00040a0040304e8c01dcd0140000408334010000000c0a0040261000188050111b20d8a248060001c0005c194000740003c40006a4048000500076c13c7c090740c080000002604403044080000003803004020000000402090c000c030003d3980002c10220190cc1000002049dd0003903c82002fca9184f55231be28a617e53c87bca7a15f55030bf29081ec42883e88310ef50441de20c817e53082daa598df55120bfaa0217e53d02fca818d794c10bea9463765190efca721fd10610de2a2217f5150fde43905f14141bfa9e437d51d0efca5217bccb21de20881f5310c6faa620fdc8621dfa1483df324c2fca9197794e42ef990637c540c6eca3a1df55220bf2a0433d548cafca2086f95332f729081f721842faa9205fd4941f729483f641c87ea6210df14f10fba0a637f544c2f8a7905f95132bea84857c504cb7a8620df54241bea8e65ef4290af8a6905b54b43ef298217f54486fea6a1774c530af29841ee52d06fca3105f94c41fc880217c504c6f8a090ef552329e2a2217d544cbaa6218f790e31faa08835e53c86fca2187750c32dea1c83fb308c2fca9997750e31fba8a81f610442eaa3196f90d41bb288417f540c3ec42887b4c821faa8e65dd430c7daa4207b88620f7a9281f541443ba8621fecc130ef99463f541c877e8721d714d20bf29c817d520c6daa5a0df54830deaa665bf42106faa1995f54a43be298217e50906faa3215fd5321fb28c87dd53d06fca70877cc832ef29e437e50042fca210df14931b6292613f54442dca4185f94640ef182613e54cc7bca710df94730f7a92617d52043eca2207794f41f6900417d50cc6fea098df15021fa28a817e5190fdc64197d94732fb28c85f531c42faa910df94042bfaa6657d52907b86498dfd5310f2908437e5410e7aa998cf95231fb98c437e54cc39a64197dcc631dea16817e51d0e78a8986fd0740efa1a65bc4350afaa9997d90441f699065bd540c2e8a2a04f95221be292817f5250efaa920df94040ef21887f721042fca6884fd5120be29e437d51903de64104f95010f7900417f53042faa7105b54840ef18a637e52903e8a2986f90f42bf290837d5310beca319774cb30f7a1285dc43ccafaa4887ec8120ee29a416e52906faa3905f15230bea8683dd310c6fca6905794f42fb18863f641442eca3195fd5331bba8a817d518caf8a5086f95010fa20a43d
  | 3 => 0x1801010022240a00c1001c0101401020100004b000060540a028110540c4201500050000106e80175449034010f49808e4a01483000021bcee000321dc0042c010640001c06000ae00003030050e0000a00a000063c4051241704c0f0000c0300a130a30944c004030000400084044000300001d740
  | _ => 0
def q2K4 : Nat → Nat
  | 0 => 0x75250f1d63952319758f525069d6490c439b997214831c544c9309b58a54c423e64d4810ab58b419072c6255020d554e51d0ab661908409b58a544c63e6515120abd954210a5f6354a40cb549401032e5350842c7151434c3545314540c758e548ca7561141329b98a544425d63141429bd95420cb354154041cd95151ccacd63c8720a758f41d032d5488420d314e204825e6590d309798e524426d62d53319d984548cba74210521d558453442ae6290d43b9987328ca3f6454032cd553418c69f6150c439b988540425e63d5321d394b318c63d6414e20a798e411034e53c86218f596421035453d45209798f540cb5753d4520ab58b4310f1d5454e21b5587324c31c54d4d209798f54c432f4314940b398b434ca766194f40d314d21482ce62d0d43d5146304c27561951329d586534871e5454f21d354e52d069e648c531a7992310c2ad648cb20d9146204827661d50318f99251cc23d6494831d918552907546154c109d1855010a6d6215230c7150534826f6548421d314a304c2b561d0841d354e210832f4394a41d554d51082ae6290440b9987428826e62d5231ab189401032d54c80208f19153883555308410f10c931c874c43548309798e52c433554544209d987540876451485209b988538426d6215210d914a314425d63951329b99742486cd63c842197d8d52443655254430ad59231c8736545442097d8d54442ad64c8621cd5503104356524c431d310d52cc71d53104409d98753c835553d0641cd150514c35453d4540b598f419063c6454021cb1505244355518c430cb951428863d64d4b10ab993328826e62d5030cb18954c86776154d109ed9520082d561cc832a7593314c3374314540d354f200825c6354a108f99053c87656114910cd553100426f6550821d9d095190b4f654c8329d997414863e65d0d409d19541442b46150040d954b41043345490510d354f4290b66525474397d8d54882d6618cb31d9148514c2ad648c8219798f540c66e6214131b358a4310e3d64944318f592530c78c43d09329b98b54086ae64cc9218f990540c23d64d4d21c7d954310f646154810c7552320c31e53d0e419d59731042e56448421b5586434c2ae6290f42c755343cca5f654c831b518d100434d5394840d358a53d0b1c548c1308f992544426d65108209b988505065f6354a109dd8553902e56290510b3d91320ca3d6414e21d394e328867761549109798c5304274654851097994434ca5d658c4309b99452442e662cc621ad592314432c5450821b558e41c872d52104409d997414c6d5644c431cd95241c867661152309718d544426e6215230d9d4b514c27661141329b58b53c42ad62d0740d9d09510832d54084208f59353c42776550441ab59321c83556194f21d994941cc7546154e41cd55321886766194d20
  | 1 => 0x831d5310f428f590504c6b66190e409b98a54c42ae64cc820b55864310e5d6314810d3d4c32882d6618c932ad986435072c5450b209d596410c71e5454c20c7153324c25d63150109798e544423d6494821cb15242482e56190b328f59353086776154a309d996414434e5354840b358a438c677654c421d554c318866f62552309758c504863e6414a10d954520082ce63d0921ad98642903355454632d990a51cca5d6594c209d185528c31c5350940ad986425067561948439758c54c86766588510d554c31487665348421cb90d52d066d65d08208f997425029d63d0641d514d214435543946329e596100426d6214c10d914921c427661d5132e3d0c424cb563254430e5d0c414c73554944309b58a54cc32d54d0b219758f548866d6295110ad58742d033554d04109b189548c31e5454c10d3949328c6ce62d0f328fd954310a7561152308f99353886756195032d354a310c35553cc4109798c505065d63d53218f592534865f6354021cdd50418434e5350a21c754c42d074d4394a31ab98a415071d5390b418f593530826e6214143e590d410c63d6494b30b9987424863e64d4f209d99731486e662cc631c754f401025e6394442f18c9310874c5314940d594e41c872c54c85209b58b5150e5e63d4941cb588544834c544c832d34ca510cae5628c4218f9944350a5f6355130e9909410876752d4540ad191100432c5250540d594e51102d663d0410ab98a419032c5290140d5d4c51502b561d0940b9d91210866c6254031c7953318c66f6254d20a758f415025e6394740b59874390e6f6254041b998732c87553214530d954b419063d64d4c10cb54842d066f62546309798c540c23e64d4c2097596430c6d4614c030cd550418c74d53948109b58a53106766195330b358f218873554c8410b5d91310c75543145309d185538825c6354620c754d401023c6454a30c7952438ca5e6315210cd95241cc66d62d5330cdd95411074c524c9309718d500863e6414c20c714f41502b56490441b5986328c23e65d0540cb54b401023f6550c41cb54a42d06ce628c6309bd89548434e5354b41cd146405023e6494c31d350c524c32f65508428f99353c43553154031cd151410866c6254e408f191500cab561d0c418f59352043345150540cdd0e5190e5d63d50219b588540434e5390a21cd951518cae662cc6109b98b54cc23d65950109d984530431e53d0e42c755343cc7555310621a798e4210355510c4309798f520426e6294740b998b410429e6390640ad993210425e65d0d329798e540873754d4530d9d09518cab66190c40c7553300c23f6454910cd551100423d6414810c755253c873554d0621c7d5053442af61508429b189501063f6550040ab58b415025e639482197994434c65e6314142cb152324823d64d49319d58
  | 2 => 0x6294443cb90d52103345448510b358e4210b34544c510ab58b435027561141439d98654c825c63549109b59732082cd6290e32d314d324834d528cb318f19152842e5618c920c794d43906b561d0a428f59353c866e6510932c7951438c65d6394421c754c42103545314520d5d4c51482e56190842b998b418876452d4530d554c41042e562904219758c50506b76550441d9949511032e54c86219758e520867b65500409b98a534425d6395121d910951082b561d0d408f59053c876552cc6319d9865310ab5648c4219d58654cc31d5390840d94c85148357329463297594430c3c5328c4219d58754c832e52d0a41b558e214426d6295121cb14b425032d5410921cd95131c866f62546409d58754082e662d05419b98a53c42e661d0932b958a210878f4390b3297d95430ca3e6494432cb548421031d5454f219b98853043656194b31ad993214865d63d5320d394e52102766115332e350e420caae64cc932d354d520436732546329b98a540c63e6494c219798f54886b561d0a41cb95252cc73454d45309758e54086cc604c832d5cc8514c31d544c030d510d51cca5d63d53109d994414866c6254d1097d95430c6cd62cc6318f191518834d53d0b219b98854843954390431cdd08515023d65950209b58854cc66e62d4d41a798e429035551cc030c7550434c72c5450920cd58654c87655254743b558e410863c6454e10d3d4f524431d53904408f994544c25e63d4b10d9549511034d6294e219d98652d02b664cc4108f992530ca5e6394d20ab992218834c6254e429bd8954443645290510d514e214423e641412197994534834d520c430ad58743d025c6355220cb952520c32d5290840d948550086ad648ca21b358a430c6ae6488521c794f42906d663c8410d950a51ccb2d54d0a328f99353486e662d0531b998b414866c6255130d914d21087655208410d514d31c42cc63480209d9845050e7661d5020c7551530832f54d4930cd95251ccae46148020d314b324c2766195120b958d210874d53d08208f596540c25d6394b10b358b310c72e5494a31a7d894310e6f6548020cd10d51102756508410b5d95310c65d6315210cbd53524426e6294730b558e310c6d56388710d514d41443365454430a7992318c31d5410f319798c540432d52904409d59641087574354643ad592210863e6415020b5d89310c63e64d4532cb9525204357530c610b358e42482cd638c832c754e43d066f6254e10a798e42507675214540ab58b431066e6215331b958642483673254420b9987420832d5494b31cb553420827661141429bd954210a7761551309d586544c23e64948329b588540c23d64947209b98a52442746154a40c715353442756194b409d18553483944350731b358e42ccb1d540c8309dd855348354534c510b398f428
  | 3 => 0x4219d994314874d5354b419bd89544833551500409dd95410c63e6495130a7593328ca5c63551209d986544c2d661d0f31cb553328ca766194f20c7953328c63e6515110a71814310f56534c7218f99252c43355494732c7952530433554cc631b5587328c6766195132d314e32482e56290731ad5874310a9d63d0842d954a5190ed661d0c30cb153524c29e648cb319b195424823e6494720b998b418434e544c832d9548418c66d6214141d9109518cb55514c0309d185500cb5553c4010d354b300c2756195120ad9864350f1c5414d10d554f218863e6414e21d390c524c34c534cb20cb50a5110ae763484219798e52d034f5314910b358a43cc25d63152219d185539032d54cc820d98c8514834c53d49109d987540c32e5454810d514e314425d63953109d195314423d6494c21cb5095010b355408410a7593318c63f6550c439b588504c6e661d0a32c755043ccb543254430d594d510826e6215030d354d200825e6315220b398e218825f6550c43f1cc8314871c53d0d40b358e420cb55530c4108f191534825c6354042b358b31cc3665448421d994a41cc757435473297d8d501074d3254032c7953328ca5e6514d109758c52842e561908329b189518c36765484219d984540425d6315020ab593214825e6315321ad5874390b2e5454830cb151420cb2d4394a41b598f418866d62d5231cb55152cc69d64cc831b558e41cc6ae64cca329b596320865f654c030c7152434c3364354742d394e52042ce6388521cd15141443345488510b398f420834d53cc8209798f544872d4314940b598f415063d64d4532f10cb314876552cc410cd552510823e6414e208fd91518c31d5390c409b98b54cc7665294430ab5924210b545384110a758f421066f654c832d9d4821842756115030d90c9510825f6354620b5586438c72d54ccb21b918910042d661d0d329798e54c42b561d0e41d994a5190e7565d0410b398b4390f6552546439718d548423f6454e20c794f4290b5553544409798f540863d6494832b5987434c66d62951308fd91500c63e6494d209758e5110aae6290f41ad5874210ae662d064197d8d5010a3d6414e10c718d540c26d62d4d41d554d51d0aad62d0f40ab98a435069e6390541cb951528c63d6494910c7553430c32d5494a31cd553318869c63500409d584548833654507219758e52106e76548421a7593328c735511044097994324c737429464297d95310c63e64948319bd89500c65d6395131b958a41c87365494420f14c8318869e648c931b598f414869e648c830d554e510831d5494e21ad99321886e46048421d9185528c66d62950319d98454882cf654c832cd50c515034e52cca318f59253c425e63d50109b98b5150f1e5494e21c7951328c66d6588420d354a320c2766114810d314d320866d
  | 4 => 0xdd85538823f6454a30cbd50524c2e661d0a429b997424ca756194b309758f54487645214540d9547200831c63553319b99432486ac6050842cb153524432c62552329ed95300c31c6355332d354e52906d661d0e30d9149214426e62d4f10b598f214874c5390920d9149314432e544ca21d594d511026d6294d21b358e420867661d49438fd954210b365494632d394e52907656194b41cd55151cca3f64546209d9875350b5553c8410b9586420867661d4c219dd95310c6cf614c8329d58653c833554cc410ad5874390e3d6414c10b558e411073654507319d9865210eb66190f429bd95320871c5450f308f99252443565394742d594d51d0a766115030c7d50438c26e658c9209b189544434e5354810d9908514832f4394a439d185544829d64ccb30cb550420825d63d4b10a7992328c365510842097597430c34d520c830b358a430ca6e62d4c21b998b31042ce63d0a429d987540caae6290c40b5586438cb37439464297596530426d62d5030cd95231c867561153328f99253c82d561cc831d9548410427761551208fd95411071e5350e42cb95242ccb574354430b358f214826e6590920b958a310c756544c431d354832cc67561d4d42b998732486d663d0610cb55042c867661d4c20d9147214834c53c85209d98754ccb4f53d4940b598f414c6ad62d0c42c754c43d075553d06219718d50106e5618c832cb552520435553440109d58453083974390731cd550418869d63d0b40cd152104423c64549109d594310423e6510941cb152204825d6590c329b98854082ad62d0e428f993530426e6295130e950841887655294430d354c420825e65cc5309d58454082b664cc6219798f54c83564314530cb552520c2756195121d394e52d073454d4520b998742c865f6355120b598f218866e62d50329798e521074c6254c208f994435071c5450c329b58b54c42b664cc5219798e54487564394632cd58654cc7565350721b998732882ae64ccb219758e54c834e4394a31cdd53514833551d00409b594320829d64cc4318f99352c432c5448520b998b418c6766194b3097195434c3365350441e310d42cca5d658c830cb55120082766114c209bd895010f3554544309b98a53107345450710ab98a4350a9d63d0940cbd50524423d6494f209b988530826f6254e40cb10d52d06ad648c920cb95152cc74d53ccb21c714e405031d5454c10c7550430c2b664c8610d9d48514c23d64d4f20ab58b439066f62551309b98a53d02ce63d0932d914b515025e65cc9308f596431023e64d4c21cb551528c63e6494b30b5586430c6756114e209798c528426e62d50318f590504863d6414132ab992210825c63546409798f5150a6d65908329b58a53c431c5350540d915121086776155230cd50e5190ab664cc5319dd855010e3e6494
  | 5 => 0x51d026e6295131c7153314c2b56488510b398a314c6ac6448020b558732cc23d6494c32a758f411066e65cc9219798c54082e5618cb20ad592310c6e661cc820abd8d4210b4c524c5308f990538426d6295132cb949429065e6395120d594d5190a6d6214e10d594e31c87346155010cb149425031c5350d40d354c32c871d4354043a798e42d07344354742d554d5190a756195131e590f418c74f4354830d3d0d5290ee5628c721cd185548c6756115232ad98643d067561d5330d510d510c3a44250721d3d0d52cc6d561cca32d554e5190b4d524c030d394d328872d5454810e910b41486d563907109b189548427561d4c209d58754ccace62d0f31a758f4290b1d5310c40a7593320caad648c832b358e42c833454504318f593538875453905109dd855010a7561d5132d5145314c2b66190b41c7d535344276658c510d314c52442cd6390a219dd85544431d5494c20b9586428867661d5320cd909511036552c40108f191518c3354214540a759331cc36552944408f59052842e5618c8219798c54886cc624c0309d987548cab762504419dd85548823e64150109758e54443a542904218f990504c71e5494f21cb14b415023d65904409d986540cb4c6254f21ab98a439031c5450c31c7952438c66d62d51319798e54c832d54548309718d52903344254440a7992324cb355494632ad993318425f6354640b59874350e5d63d4810c7552310c3355410531c794d429063e64141329d58653482d663c86109b58a53442e5628c510b558e410c65e6394d10b558643cc26c6254640d5d4f51502d56388421d314d424823f6454021c794f419063e6414c10e350c428cb1e5494c20cb550424cb665294743a758f429072d540c8209798e51c832f5410a20d954831043645250510b598f418c7665254643d914a214431e5450e329d5845050ab56488710a7d954310f2e52d0641d5151310c72c4354840c750e5110f1c53d09408f59251cc2776548421cb58a548869c644c030d514d310867661d5330c7151314c34e5354a41d9508514825e6394421b958642c827561953209798c53082746155230ab58b4390ed4604c431c7550434ca6e62d5310cd584544426e62152318f993524c63d6494b10b99874250b365250441cd546411035553d0410c7951538863e6494f10b358b314c34d5310b218fd9153482776154a40cd1474150335540c6219b988520426d6294730e510f414c72d540cb21cb95142cca3d6494d20b958a41107556194f419b58b54042cd6290d30cdd50514c2ce6388420b398b430c26c654c9209b98b544c6b76350441d354c320825d63d4542cd15231442ce63d0a32cd550414865d63949108f191500c63d6494d109d587540ca3e64d4f21d354d52906ce62d0d31b958a31c425f6355210cd185548872d5410a329
  | 6 => 0xb00c2300800a0000100005a054050260000045f03905600800000008010100180960040000403008c550030500100683b01003008001000048410060400000001b008050090040242080c01107e0200100802a000a890c1520700280b2940300300e19200800808024f800d80806e1940000003c00818819240000100051c8004001890da0180801100c00819003000004008070100d00600002a11c6800100002001007000000010510020200100300604011801000104230000180000500204a018b605602a18c0106d02c04c0784500a0000082600801000013098000038290760480c0004da2800a8b70120002a80504404c0880000e980660000320380000021c02400005004000000031f6098068040001000000a0000340481f01e00c110230020005501e0c600401013012004000bb000570121a701228c1b8000000507204c0000001880b006a40030240000701d00100e010510240000704080000608c05803012010f80000005201802401e2b02f92c0ae824021c802806c000030140080480005c05800bb30aa0100284c00e0000100448e0123f6454d10b398f4250a6e6295330d314b314c36552c841097997434c65e63141219b189538431d540cb31d3d4c525032c544c920b398b438c2756510410d554f31887565394420b3591320cb345414520e390f428cad661d0f32c7d53534825d63951209d98454082756194f408f99253487645284110cb952428871f5414d20c758c544c2746154043cb150524c2ce63d0b219d587540c23f6454e10ad5874310f1d5390f42cb952328866e629444397d95320cb5451cc530e550c418c6e5618ca21a798e4250a7761540328f99052042e661cc932d3588534838e4350832b5586430ca6f6254d109b596520434d5354840d354c210834c53d49408f992534427665105319b58a51d023e6494821ad9864350a3c6454d109758e52d031d548cb31b558e414433754145209758f540426e62d4c10b998b314867565c84109dd9510042b661909429b99442486ad64c84219798f54083365494430b998b314c67561d4f209b98b540425d6315220d954b418c6746155220c7550310c25d63947209b588548c76552440108fd95421063d6494421ab58b411066d62d4c108f59053082b46050441b5986320c36652544309d185544c2756194c42c750e5210f655188420d354c324866d6214143a7593324c2b664cc6318f592510ca7b6544010cb58a54cca5e6314810b5986324c7565394642d954a51d0f1d5494c109d596310863e64944319b1895010f355410410d554e511025d63d5020b398a310c36652944409b58a53d03364354440b958a41c42b5648c710d5d95310c66d62d5031d518553886e562904319b596420863e64951209dd95410867561d52328fd9152842766114e209758e
  | 7 => 0x780600102a0140a00201a0f0358040e20900783c002038048070020000080107a0000001b000000008010020080700866c008078120020f00080100a0200000801600e2e0050600205200b008760000040024fc000000000084881108e030010002280041a00d0d40144880000a0000081800c5c00b80002e004060100040180008d00c01c00024050000078110005a00486c00e0001480301200c0002d0051940e80b2021940000b000c64078170000c4000410c80000d02b08c0040901914604c2881701a0004c00f00003d6580003e0101180f01c678010000001340380b004014be39b00605d4e01147895c0000000813c088140080141701800a0582800000600409b0216c0203100500e0300283522c014221ce0000200200302400809805000010110030000081a00a0280404a8b6022000178000020183487412
  | _ => 0
def q2K3 : Nat → Nat
  | 0 => 0x85267494d210870bb24a89886319dd952d0631c4a8430aa02144d7614f2148322a9cc3a1643315cf6448421c4cc8a96420860e6454f320830b29ac3a1c83315cb644c431c1cc6a14a22161665d0c414c722b18a690843139da544c832a2ce92926218e1664546310c30b322a7988210ddd954c862192eeca188318d4671d0d520c322a9cc5a0c83495cb4394642a4ae5a1ca321e4452587324c32229ac518a218955261d0b21c4aa930e851964662546310c306b18a5a12818555261d0f31c2ac829c428864652587328c60ebb0a999261835506348020c8ca6b148390e0d5398a411030bb2c86a0863075d854cc530c8ca6b0c6510c4f7654e21082333b4a6908439158c528851092cec21a8398e266454b318c692b8e862928115dd953d0621c8cc6a8c421060c6454d20083132a2c321665239d84350b32a2ce72928220c8f7650c428ca8b3a6ca98863295d06048421c1ac92966318e1454587324c30ab20a718a21519cb4354430a8ce5a1aa3994557614e21443062a2c521a61235cf6150842c1ecb21a841962454586424830aaa0c2980619154e61d082091ae7b2a84214a5711814210b0631a84a80858355263d0820a4ce521aa22062554987320822abb4a720e43155d85390510c2aa831a200861464545300c3072a2c521c63519c74354b31c1aa731487a160e6354a42d0617bb2a999041075da54cc631c2aa730c862060e6454a310c31232242a804385552618c830c2ac628e82a061654587328c7072a2c72144383191524c030c4aa830a401049574181310c7132a2c520e438315162cc530a8ce5b2a6218e45531891004306b24a71944391189514c030c4ac829462885457390a51cca52b90c0a08830b1d95448020c1ac829662984657694a41cc61a3b2a8880218554e61908408aeeca9e4310e145358742502a2b9c8428a419118d514802098ae43026218e256414a214430a32262a8063199da5448421c4aa8312200843776553210430a2a2c720a218354e6290f4185aec2a4649060e6354a411030aa1cc329087519cf6548421c1ca8b166318c9574d89310c706a18c4a808789951618ca21c2aa730c87a161654586438cb07b24a899065899915188420c4ac428e82a054673d09518cb2331aa5a0c83315c7654c832c48c8a92200848d731814210a9338c86a9081839974310932c4aa530c842060e5458e42ccaa339e84a88418314d62d0d40c1ca8b1487196165458e41cc713312a3208818354c6250040a1eeaa1c8419616535874290a27bb2a7a1643519c7654c832c1ca8b1e4310e155398643d0706aa4c7a16438359252cca31c8ca6b0c8510e0e5358b4390a4ab98c0a0883499cb6550441c2aa931e4310e266454b3104306b20a790a41495cb4314540c1ac829c649048d74181320cb0b322a790c438955261cca32
  | 1 => 0x2148262b8ec89906589189415404185eecaa66590e465358a31c872231aa488021295d36548421c18c6a92802050e73d954210b22a90c298061495d2321452098ae230264196245458a4144312b20a89084383991538842085aec2a642904c5731812108722a9cc5a0c438350e6294443c1ac8296649860e644ca510caa2b948628a618994961d0a41c8aa730e85216455398b310421bbb2a998c439158c5290510c4aa93166310c2d769523288712aa4c59882189951628c721a1ce5b2a8621e255498b318c652b96c6a088385d8e535044186aec2a442886455298632cc69339486a8e85235d3654c832c2ac828e629860d5498b430c322a9cc3990418599153c8410a8ce32a264195457290e518cb0632264a8065515c64394a31c1aa93146218644535864248322a98c2900418554e6190b4192ae23028621c9571d894310f0aaa4c3a18619154a618c830c1ac82a2641954672d0d5190f22b10a398a618550c6154043c48c4a8a80206155498632cc68bb8a8728887899516190a21a2cea21e8298e1564151310c70731aa5210819154e62d041083eecaa4641850e74d95320cb12aa4c5a0c43071d9544c030c4aa93168208516748c9510c30729ac5a0c838955262d0631c1aa8312601854673d095190b12aa4c3a1041135da53c8621c88a6b14828852674cc9518cb0a2a2c321a619118d2154021c2ca8b0c8718c4f7654f42082933a664a88418358c52d0540c1ac72968520e0c5458e424829338ecaa10858555263d063192ae3b2a8621d2571d0e5290e32bb0a518a21191d9524401092ae9b2a6218c8d74d85320ca1abb0a918a21515c64314930c2aa931e8310c4c7654d2008312a94c3216839154e61ccb21a4ae3a1ca520ca571d8d4210a46b96caa18878595161cca32c2aa931e8208615531854010307322a799643499c64354b41c28a8b1c428860d5498b43cc707322a5190619198d52d0631c1ac929e4310e0d5398a4310312a90c2a008119dd952d0410c2cc8a9e6310e0f6394d4210a1bbb2a998c63519c74354a438a8eca9a20086466354b210420ebb4a999463235c86050c43a1ee4a1ca421c5676951310c60fbb2a91886189151618c92089aed29c8510e2452587425030a31aa2a00818518d4154041a1cea21e849962464545200829338ca6a1085295c76550842c8a6430aa019644624c5500c693394a6a088383991528cb31c1aa931c42105177550e410c662b96ca98863459ce4254440c8ac72948398e16535874390a4ab9ec4a0883851915344010a2ae7a14a32154673951210870729ac5a1c83135d85390920c18a8b1e429054672951310c616bb4a990c4389151628c5108caec294828851574cc8514c30629ac5a0a819114d618c9208aeeca9e820851574cca518cb0b2a2c720e4315dd953c8410c8cc6a9682
  | 2 => 0x3000260c00154401bb0a600e0a008302000048002a05000a48600008044a000e8780e011d2dc02006c0e42c000480c0000023740e060d04414562a00004fe07000080128024cc09018604600000000a18878245a2e00000fa1a038801000000003c00088384a00008000017068006e0375814261a00002b6060202808031400004005082c0ce606000020202248069902804127977028e6010d9a004060a0041c00008047e0400a1002631f074020e94ae9b1a4210ca572d95411070aaa4c790821459cf6550441c8aa73166310e0d6394b4190633bb2a5988218594d61d0a41c2cc6a8c822060d5498f428ca1bbb2a998821075da54cca32c2aa930e87996265458a41cc68ab9e8428a818514d61d0d40c8ac628e429051671d954310e17bb2a9994658355262d0f32a4ce9b2a4210e255498732c8646b96c2a18870bdd9548842098ae7b2a4210c9573d95411060fbb2a91966385592538c72186aed2a46390e2564147
  | _ => 0
def q2K2 : Nat → Nat
  | 0 => 0x80f87590544c83281787590544c431
  | _ => 0
def q2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 830
  | 4 => 1423
  | 3 => 364
  | 2 => 2
  | _ => 0
def q2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt q2K7 (i*5) 5
  | 6 => packedAt q2K6 (i*16) 16
  | 5 => packedAt q2K5 (i*27) 27
  | 4 => packedAt q2K4 (i*38) 38
  | 3 => packedAt q2K3 (i*49) 49
  | 2 => packedAt q2K2 (i*60) 60
  | _ => 0
def q2I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt q2K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt q2K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/311+packedAt q2K5 (22410+(h % 311)*10) 10) % 830)
  | 4 => 2*((h/530+packedAt q2K4 (54074+(h % 530)*11) 11) % 1423)
  | 3 => 2*((h/156+packedAt q2K3 (17836+(h % 156)*9) 9) % 364)
  | 2 => 2*((h/1+packedAt q2K2 (120+(h % 1)*1) 1) % 2)
  | _ => 0
def q2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffc0ffffffffffffffc3ffff
  | 1 => 0xfc1f03f83e07c0ffff1c1c1f0e0f87c3fd5293
  | 2 => 0xffe003ffc007ff03ffe01fe00ff007fc3e631c
  | 4 => 0x3fffff80003ffffe0000ffff8003f83e0
  | 5 => 0xfffffc0000000003fffffffff00000003ffc00
  | _ => 0
def q2Neg : Nat → Bits
  | 0 => 0x4000008000000000000202100108040000425
  | 1 => 0xa946659194aa95d1cb0d0d1a268d168b9d5292
  | 2 => 0x30caaaa28d353456d56217484ba42738ae6318
  | 4 => 0xa294d34529a1a69b66b742108dce72113783c0
  | 5 => 0xc318e38631c638e3b8db9b9ce10844223bf800
  | _ => 0
def q2Atlas : Atlas := ⟨7,rawDecor 55 q2Pos q2Neg, 0xeaeaaaaaaaaaa8a8eaeaaaaaaaaaa8a8eaeaaaaaaaaaa8a8eaeaaaaaaaaaa8a8eaeaaaaaaaaaa8a8eaeaaaaaaaaaa8a8eaeaaaaaaaaaa8a8eaeaaaaaaaaaa8a8, q2N, q2R, (fun _ _ => 0), q2I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def q3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q3K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def q3K5 : Nat → Nat
  | 0 => 0x41f721842fca118f754c20f6a96637c525076a8220fd10631bf29a41f731486fca4885f94230be29a437f54843d88490ef10d41bf2a661ed5290eeaa321df54d10beaa065bf4310fec8390df94010bf298217e5190efca0195f94a42bf2a465f621443ea6218ef50940aea9e83f721886faa8995f94642bfa8263de53d0aeca3216f90f42b629261bd429067ca8087b14940bfa82435e53d0aeca321efd0c41be282857f540c6fca9995f55320fb98c637c54042faa9207bd0b21b729021bd54ccbbe87185794e21bf29661be54cc6fca310f750e32efa1a63fa40103ec6210df95110de2a2217c504c6faa598df94b31bfaa2613d54082fca2185f15132df20a83bf54482fea91977cc631bf28883bd41502fca710fed0240bfa90216e52907ba86985f54021deaa6635e53042fea610df94e10bf298657e5010efaa398774c431bfaa0436d5290efaa7a17d4c510bf28665de324c6fca421df94b10be29e41d5310c6eca2185fd4d41be294217d548cadaa518f70c630df21a87bd41d02faa2105f55120bf28465dd53887bc62186f90f41bf28e657e510cbbc6598df94f42fd884217f53c82fca9884fd5110bf2a241de43cc37884207b50821bea96837c53507bc64185f14810bf28843bd4310fdea4a05fd4943f6a1665dd430cbde84995f54f41be28a617e52d06fca2085d54420ef98a61dd32cc2f8a9907bd0a20fba0a43f631c43f240105fd4e20bea80637e50d0af8a898fb50a21bf28481be43902fca7905754f42f6a94637f53482fca5a1fb14930bf29861ed32c82f8a818efd0a42beaa4617c51483ea6390fed0140dfa1c836d520c37e86a07d50431fba0c21ec32c87ba60187d14530f6992417e5290fe88290fb08420fca0081ef32083ba8621fe8c030bb28e65ee20482f8a4a07714d10be2a441dc32cc6faa718f7d4d10afa9a41bd4210bbaa6205fd5030ef99463ef208837e80205d14520beaa243f541443e862087d54732b6a90817e5090fee8310df94e42bf2a0637c54083b88798cf15110f790e41dd53d0afaa39977cca32be28265f441842faa918fdd0641bf280617f53487da84217bc8520be2a443de314c6f8a6a16f90b41fb98c21f510043dc42105f15210ee190617d50c8678a89877cc930f699065bd42d03de85215fd4c20bea98417d5490b7883205f15330bf2a061df53502faa9996f50e42baa8e657e54486faa6215b94830bf29881bc425077aa990fb90b20ee218617e50c867ca910df54810be29a217d50cc6faa1995f55220bfa9e21ec32882f8a5887d50721ba28a613e54083baa7a0dfd5010df21481ee32c82fca1087d90441bfa9a857d54cc3eca2205f14e10bea9c81de328c2fca6215fd4d10be2a4637f5250278a8905f95040bea8e876e528c7daa520f34c832ee98a61de53907d884105f54d20
  | 1 => 0xe52d0eeea2a05714d40df21081bf41906faa3195f54231be2a0617d5090efca520df54e21bf290435c53483d884995f94740bf28863be40502fca0105fd5321faa0e63f5310867aa918fd88710bf28063be43507d86490df54a31bea8861fb20483baa7217b90a21fba0c63bd54043be65987b10b21f7190437f54c83f620886f90942bfa8283be41903dea4886fd0842deaa061de5390bbc64995f14542beaa2217f53503eca3197bcca32be2a643f731043dca598fb94a43aea9c856d52d06fca2205f94221b7296837d53103ba8618dd54430d6a10857d520c2faa898ef55231efa1e637d500ca7aa9995754c40fba8a615e5390bec6390df54720b629281ed52d0ebaa710df94743bf28e617f544c7ea63887948421ef21c657c548c2faa790df15021ef21c63be540437aa8105f14121bea9e815e53083dc6510fb14910ee99463ee52d06faa810df54c41bf29481bf544c3dca4084f55331bf29a217e54882fea7085f54c10bfaa2217e5010afaa5085d94743dfa1c876d52cc77882205f14943ef988637f54883dc84217790c32bfa8265ee520c2faa120df14c20faa0843de53042fca8217754f21b7a9281de434c3daa4206f90941faa8c657f544877886207790c43ee29a416d52042dca521f74c730be2a6635e53d06faa4205fd4542bf288877d53c43f260185f95041fa10821ee21486fca8197dd4520dfa16817f528437885a0df54843bf290657f5050efaa818f7d0c30faa88417d538c2fca5186f95221bea8485f431487ba64986fd0240dea1885df308c2faa610df54640de21a857e54086baa6085bd4910df2a665ed21087da85905f55243f7a12857e520837a80207b10a32faa8e87bc42903de6490cf95331ee29a817f54c43bca7a0df55310fa90a216d52906eca3a16f50f409eaa4437d52883bca790fd0c610faa0e21dc310c2fea9995f54443bea94817e53c86fca9185f94420bf28885f610442fca910df54831be2a2217e528c77a8420f794c40bf290817e50102f8a610f74c832dfa1c85ee52102faa5185f14543be2a2617f54887f220086fd0740b629221f710042f8a790df15120b6a96877f52c42fca5195f54841f7a10417e53907eea2a07b50920bf28c837d51102fea4985fd4f21df2a643bf54443ee4290df94d21fb28e857e5090aeca2107d90431afa9a813f54483e86310df54341bf2a0417d50106fea8195f54620bf290837e51902faa71077d0f32bea96217e50cc7f660987710d32eea1c63f641443be64195f54740aea9e437551102fca918df94c31bf29c81bd41107f440107bc8020bf2a421f65190fda84195f14e20bf28687f5510c2fca898d794f21eea9c837d5110be8a2a05f55030bea94433d540437ca8106f90440bf29085df320c6faa990fb0c820fb28c85be540c2fca4185794e41f690
  | 2 => 0x400070000a0030102b14c2f0281e1ec1a000190541a0080019a760ec0b00c005d000030820000314c1b18c011843d00000000020181b0744d0100200000014270f0610600b068020005d000070083400c41000de0a00205c0000411004590c000034000100618571014074e002018023182e0f42b0780400000014005195b00406004c6004610381018402000011380502c200404804c4d090002b807014030141c148050000201c210000c0b83f04c0101409054770047a2c405000000300c0000100c010a0380082c00014004002840003c0c014000100002c0100c070600904c030041e0f40e134090081c050570706008c6d58c0100c2700057004000000d000000e8600040b0980b0100106afca1105754c20bfa92217c548cbe8a2905f55241f7a1465f721043dc84196fd0841bf28e857c53887dc84907d90731fd080213d54c87eaa321dfd4e21be2a6215e53102dca4207794c20bfaa463de318c37c86205f54d21faa8c857c53042dea4987d10621ae29a217e518c2faa8984f55030fd98461df53482faa4887d48421de21e857d5190efca5085fd4532fb28861bf4310afea99857d4d10f7992657c505077aa910cf95232ee21e65ee528c7da6410fd94743bf28083f421842f8a4886fd0940f7296877d53c82faa3a1778c130fba0a63df4390efea498fd48710bea8c617e51883ee6310fd544409f2a4633e54ccbbe86995f15121bf29e21dd43cc378a8987b8c920fa20a637d5190bf641106fd0441bf29843755190afaa0217d90421bf2a6637e5410efaa998dd54743beaa4433e54c877e87a05fd4142bfa98217f548c3ee82a0df94831dea18837e53106f8a7885f54a41f6a90217d52d0f7887a0df54e41bea9661ef328837ca918df95320ef21863ee320cbba6418fb94a41baa8e85ef21086f8a8195f54221bfa8a877e51c82faa1a1f70c931f610c41f7314c6fca8995f94631f7996437451503be63984f55232bf29e817c515037ca9197bd0921bf29c87f551d0afea8107dc4210f6a9061dd530437887205fd5120f621441df4350efaa1197d90710f7a9261bf42907da6510f70ca30bea80877e544c2eea2905f54a43ee21a63bc54482faa3085f95010bf28043df300c2fca4086f55232b7296637f514c2f8a2996f90d429faa2617c53482f8a6a07bc8621bea96817f54cc6fca7105f54342bea8865ee21882fca3195f94f41aea9c837f51482fca621fd884219f2a0617c524c2faa8105f14143bfaa2657c524c7da43905f55210beaa021f741043b887185f94341be2a66577514c2fea4a0fd94420bf28483ee42086eca3195d94440bf298417e52d02fca990efd0540bea9c65f6310c73a8621fb90b32faa0883f441043bca710fb54b41bfa8a81ed21482faa7215f54e10dea1c83bd43503eca3995d54632fb18a216
  | 3 => 0x100a004d501000034500b40003002018405d40b00003008021b03b00024000000a80f04c04014176d0fc0900c01006018000000035ca203012068040001807025054f8018021700302c6400438084040c98215c580dc1600054074910e80803c290280e0
  | _ => 0
def q3K4 : Nat → Nat
  | 0 => 0x220483a44250721d5d0d510c32f4394a439d9865210f656114910c7551530429e63906409b588504c66c6254e10d994a41cc65f654c431b598f214874d528c830cd55251ccb2d54d0a329b98854083374394643cd145415026c62551109dd85539023e64d49318f59251c829d63d0841cbd0c525035553cc6219b988520433554cc631d914931442ae64cc820cd550414871d548c8309758f54486b76550441b5587324c277654c4319d994414c66f6255120cd95241cc66e62947309d98654cc25f6354a40c7951530433551500409758e54482b561d09409798e51c8275611414397596310c2766194f409b588540c2cd63c8421cbd5042882b561d0c429b98a54cc36552d06418f596411031d5494c20cb95142ccb2c52d0540cb14b425026d62152318f191528c25c6355220b398f42083365494732ad185401026d6214143cd18554887655188420b398f4250aad62d0c42ad98643d06766114c20d594d41c86ce62d0f329d584548c32e5490a21c755153082756114132cd109511023d64948319b58b540c26e658c9208f993530872e4354840cb50e529069e648c531d314d32482b561d0d40b598f414c72e5490b32d354f32c872d540c8208f990540431c548c1309d58453882e56288421b998b31486d56190e328fd95401025d63d5010b518d1004275658c421cd552518cad56388710d954520082d561cc83297997434c69d64cc930cd551518cab5648c710b9987424cb6552cc410c7152434c2d661d0f31b358a430c74d5394840e5d0e41cc65e63d48108fd91500c72d5290b419758e544431c5450d309b9885050f2e5494b31c755043cc63e6494f10cb58a548863e64d4532cdd50418426e62d5021b998b418c74c538c9209d19521443645284110c754c4210355518c4309758e51d029e648c4308f99742502d56388421cd55251082b561d0842a71814310f345414530d310d52cc66d62947409b189544c34d32540329b58a53c432c5414910c714d42502b66190941d354f420823d6494b30b558e214426e62d4f108f59053886e661d0a32cb553200823d6414810d394e52d06cf644c832ad993314872d5290840cd553310432c54c8520d514d314425d6315321b998b418866e65d09219b98b53042ad648c9209758e54c431e5490e32ad592314426c62552109b596420872c5450b208f592520cbc5328c4219d58653d026e62150308f990504cad663c8410b318d200826c6254031d314b314c36652507318f590504c7575314540b598f418427561d5032cd152214425f63551108f992510cab664c8610b958a310c72d5454b31a759331cc32f6550842d9549100436552c4010a7593320caad62d0740b358e420ca756508410ad986421029e648ca30cb95152cc7a442d0521c7951438ca5e6315220cd95141cc74c5350920
  | 1 => 0xc65c6354a10d354f200826f6254041b998b318869e648c932d390e528c6ce63d0921a759332cc2e662cc6319799453482ce628c630e9909410874c43548309758e520863d6414e209758c505066f6550832b358b318c6d561cca32d9147214831d5494f21ad993214875553d0621e310d42ccb54534c421d9149414429d6490c43d9185528c63f64549108f59053c87546154e219b59632086ad62d044197997314c27461540439d18553883345414520cb95132886e562907219d987548ca6f6255210d914b514c29c644c030cd553418c66d62953309758c52042ad648ca218f992530c7355410531add89411066d6590832d514f514826e65149109798c52842d563907219798e544825e63150308f592510c78e43d0a32d994a5190e3e64d4f20cb152424832d52104408fd91528c23f65504419798f548863e65109419798f540ca7665905109758c5050ae56190832c7953328c6d56190f309758c52842d663d0541c754e42d063d64d4c109758c548826d6214c10b5986324ca756114c20b398e218833454504318f59352c42d56190c439d9845050e6f62546409758f54c42d7644c431cd95141c872e54948309758f5150a3d6494c31d594d511032e548ca219b58853842766194c42d9485500871d5410d31d954a51103355454420c754c43d0a9d64cca32c794d4390a6e6295130cdd5051482766115230d99495190f3754d4530d954b410434f53149109d185534826d6294d21d594e41c865f6355120b5591310c63c64540329798e52442e462440109758f525069e648c931c794d43907954310631d354b300c31c53505408f596431032e5250a418f997435034c5348520b358a434c32d6215120c7552538872e5450a218f593538871c5450c32b958d21087665254743c750e5110e9e648c8309d58753c827661d5032ab993324ca5d6394421d554c410431d5454f21cb150524c25e6510d32d314f52443545348510d5951310c66f62540319b988504c63f6454a108f59253c425d6395131d9d4b51502ae64884208f992534429d63d0740cd553410434d53548109dd85548831d54cc0309d984504cae56190b20c7951328c6d6618c830cb55332c878d4310a32b598f41042746154e409d98652d027661951329d58653c82ad62d0d40cb55252cc676650c521d514d414425e6514d108f59252c426e6295131b398f424ca6e62d53308f59251cc3674254420d354e520429c63500409d58652cc336544c721d9949511023d6494c21d34ca510cb5753d4520b398f428ca6c62546408f99741503644254420cd553218867561d5030a798e429023e64d48109b98a534425f6354042ab993328cab664c8410c754d401026d62d53309bd89548c35453145408f590530429f6250c439b98a53c423d65950109b59652042cd6290c32cb15
  | 2 => 0x6550842d554f310431d53d0040a798e4250a5e63d50219d98454ccb565394642cb55332082b5648c7219d98753c82ad62d0641d3189530823e6494730d994a511026d62d4543cb151324825d6394b409758e5110aad64c8621d914d21086d5638c4319d98654483364354440c755343cc76452d4540cb55042c876551c8020b358a43cc38d4390832cd58654c875653547428f99253086756195131cd505501066d62152309d987540c71e5350a41d50c9510c3346155010d9951210866e62d5010d514e314426d6510820cb551520c2ad648cb20f1cc8314872d5410921d9d4851502766114142d558653d071e54cc6319798e534434d43149308fd954210b645290510c795253082d661d0d4397195434c27561951219d5875350a5e6394d208f990504c65d63d502097d8d524431c544c930ad9864350ecd63908219798e5110a5d6315221d954951d0e3e6494831c7550430c2d661d0e43cb551528c72c548c920c795153082776550431ab59321482d661d0e30d314d32c823e6415030cdd0a5190b1f6550c43d954b21042b66190b41c754e4310355510c430cb50c525023d6494821d3588534835553d06419b58b548c7a54210621ab992214875553c40108f592534866d62d4d41cb151420ca6e6214e10ab98a41507555354440d9548418c66e6214c10ab98a43902756114142cb951520c356538c721b598f218871e5494f219b189501075653947429798e52d031d548cb318f59050486b763504419d98454082756195132ab19120082cd6390b329ed95401025e6314121b358a438cb6765484219d59641087375414530d31895390a7661d5030b558732cc3365490721d554d100427661d5020cd553210435732946328fd91534425e6394821cd550318865d6394b10e950a41086e661ccb21cb151424826d62d5310d354c32082b664cc6319d58754ccb4e5390a21cd95251082cf654c8328fd91518c32c4354b418f590538423e6510d419b98853083345450710c7151314c2776154910b958a410c73454504219d58654cc3565394420ad986439031e5454e21ab98a411026c6254630d958652d074f530ca209d586544823e64d4f21cd94d411066d62d4c109758f548863d6494d10b9586320872d5410a32b358f218866f6254630d914921442d563904319798f5150aae6290d43d514e414431e5454f219798f52c427565cc41097d95320c6b66190f42d958652cc6ae64cc9219b98b540c25d63948418f99053882ad64c84219798f540431c6355332cb10d521029f6150c43a758f42907555308410d554e510823c6454021d5146304c29d64cc631b9d8d210865e63152219d98754cca3e64d4f109b98b540cb56431453097d954310f56524c4319b99721483554314530d9cc9518ca7561d4c20b358f214832d5494830d350e528
  | 3 => 0x530ab58b4390f654214520d594e511032d5250040b998b414c6d661d0c30f14c8318871f5414d20c714f43502cd62cc4318f593524c6b664c8621d3d95320cb574354643a798e41507944350731d3949328c72f54d4910b958642cca3d64d4c218f992520cb4d6294e21b958632887664294732d594d5190a5e6395121cb552528c6756194c42d314c524432c6255020b998742486cd6390920e510f414c6756115030e590d410c66f6254d10cd550310429e63908409b58a544c26d6215010c755043ccacd6290c439d986540ca3e6494421d5545300c23e64d4d21c758c544c32d5210840c7d50438c26e6294910a799232cc6ae6290d42b9591210871c53d0940d9109518cb1e5494c109dd95210865c63549108f590504ca5e63d5121c715353482ad62d0e429b9885050734544c510b958a31c426e6294f40d914a214431c53d0540c7551538872c54485209798f54c874d5394a41cd909511029e6390440b598f4148764528c5108f993530434d5354a418f592530ca6c62552309d586540cb65520c4108f596421034f53d4940e3d0e42cca3e6494b10e390d420cb645448421cdd53514831d5390f419b597320827661d4c20d554d51083355410621cd951510826e6215231d5145314c34d528c4308f990520426d6295310c754c43d06766195130b958a314434e534ca21e5d0c414c754544c431d554c318867661d4c219bd895010e5d63d5021b998b41842e5618c920ad592411065e63947408f990530827665cc52197596530423c64546208f992530cab561d0e429ed95100429f6550c439dd8554443345484110b598f418c6d663d0621cdd0c51503664214520ad5874290ad6618cb31b398a314c7546154e419b98a544431d53908409d9875250e7661d5330cb55342c86b5648c431d594d51082d4614c030cd147415026f6254d20ab58b43d026d62d53318f992520874d53d0b21b398a310c2756115220cd547401025d6590c319d59721042ad648c832b5d89310c71f54d4d109d997414c63e6494b30cb58a54ccb4c53d4940cdd08515027b654c030b9d95210867661d51329d19541443556194f219758c54843643254420a758f411071f54d4d2097596430ca9d63d0842cbd50524c32e4354b419d597410436752086108f992534867965840109b58a544ca77654c4219bd89538426c654c9209798e540863e6414e109dd85544c2b561d0e439758c540423f6454032cb550210825d63d48108f99353082d7654c431b9987328823e6494d20c7153324c35443547329758e54c82756195320abd8d4210ace63884209d58652d023c6454d10b5586438c63c645403197d8d50106b561d0f40d54c5500c7545388510d554f218872c5290140cb54a411034c528c1308f992510c74e4314930ad58742d03645214530c715143cc2af
  | 4 => 0x7593314c2d6618c931b358a438c66e62950319798f54c427665105218fd91518823e6495120cb552520433551104409b997424cacd644c832d914851502766114e209dd85534431d4394843d5d4f51502776154a309758f54c866d62950319b98b5150ed4604c431d354c32c8736548c721ad986431026e65109329798c54842cd62cc530d354c210832e52d0a419b98a54c426e65cc9219b98a53106b561d08419798f525065d658c830d5d95310c63f6454d20c755343cca3d64d4c209d586544c23f6454e108f993538874c524c930cb94b41907555394440c7550434cb345450510d394d52102e661cca32b5987434cb2e5454810cb952520423e6414e218f19153842ad6490842ad587431074d53cc820c754c411034d5394b41ab189401035551cc030d5cc8514c2b460504418fd954310a3d6494910b3181320ca77615512097d8d544c32d54108209798e54c834e538ca21d3951320ca766115030cb552210834d6294f42cb94d4210ad56390441e550e410c74d53d0a428f590530826e62d4d41ad59221c423f6550c43b958a41106766115220cd14640503653214520b9987320827561d5330d394f218872c5250940ad99331886ce62d0e4397996434c33554547329dd855010e6e650c921b398b438c23e6414121b958a31087c6324c4219b58a53d034c6254f21d314f21482b564885109d987540874c534c8219758e51c826c62540438f99454482d561cca319d58754083663214520b998b410434f4354b319d587548cacd63c8720a758f425026f6255130c7150534823d6595030b358e42887a74210521d918552042ae6290d41cd50e5190a3d6595020c750d5010ed661d0d318f990528431d548c43097d8d519025f6550c32b998742c871c54d4d10cb551200832d42944429b988548c2ae6290c40ad191100425f654c030d954b318c67561d4943d3149314c26f65508219758e544865e63d53209b596210832e5454a319798e54c433654547329d984548ca5c6355120b398e214872c54d49308f992544c25c6354620d58c9510c34f5314940d394d428863e6414c109d18554882776154d20d9d09518cb1c54cc530cd952518cab56488421a7593310c74e53548109dd95411074f4354830c755253042776154a40ab58b41502b66190a40d994d210874d5354b41b358e320ca7661d53209758f54c82e460484219dd95100423e64d4b10a758f419066d62d5031c7553430c34e5394810a798e42506e46148020b358e4210b1d63952319d185548c2cc624c030b9586420863d6494f209bd9521087655254643d9146204825d63d4b10cd153514833654546329798c540426e62947409d586534874d5310b219d584540832d5210b418f99053c866c6254d108f99251c835553d0410d954a5190eb66190d429d584548cb553214
  | 5 => 0x419065f654c8329b58a53442e562907109b98b54cc65c6355110b398b434c65e6314810ad58743907556114d1097d8d548834d528cb318f59353c87555354642b598f41906ce63d0a20ad58742907654294732b958632c8275650c4109758e54087355408410b998b318435453d4540c754e4110354534c7109d587544cad663c861097997434ca5f6354a10d554c418863c6454630d354c324865d6315020d9d48514c32e54c86218fd9153882d56390710d5147314c2746154032cb5095010ab661909429bd95320ca9d63d0b409b98b530873654544309b189539025c6354a40b99874290ae661cc921cd550418c72f5414910c754e43d0a766114810d9544210833654944309b988540423d64d45329b58a5110eae6290f418fd95431074d5354840d394b318c74f4354a43c7953328ca5e650c9319d98652cc23c6454a10e310f424cb1e5450e31c714d435025d6510c30b958a41442e662cc531ab58b4310e9e648c630d554c310431e5490e31b5586430ca7561d5320cd94941107c4324c721cb189548ca5e6315321cd15241443673254420b558e4144276658c5108f59353c825f63540219798e51086e5619084297597430c2ad648c821cd58654cc6e56190a218fd95421065d6395132ad993314c6776154e209ed95200834c5388120d3548310c33443544408f592510865e63d50319b994424876552104108f99253c82746154a40d5d4c514826e65909209b98854cc72d540cb219b58b540423f64540218f593534865c63540219b588548432e5494a31d354832cc7665254430d314b324c23d64944329b58b544c66e62d5031b398b43cc73461552319718d501066f6550842c755032cc71d540c4309b98b548c74c5314940c718d540c3665294430a758f415026d6295110a7593328c74e52cca319dd855010b2c5250540b958a410863e6515110d9145214839643d06318f59353c42b561d0c439bd9532086e561909209798c505067665d0521ab58b43107344354742ad98643506ae64ccb219d5865210ed56390421b9987428834e5394a419d986534827761540329d984540432f4394a419758c504865f6354620c754c431025e6394841b998b414865c63552108f59352043544354430d5d0d51ccaaf61508429d9875350b6552d06319d594410433554104109b988548431d5310b41d554e51d0ab664cc610d554e5190b57530c610d554f210426d62947309d1855010b1f5414d108f19153882776550421b998b415072d54d0820b5586430c74e5354a41ab59321c833554cc621b398f42c865e6510d31d554d51d0b1c539014097d95430c66f62551109798e5444355530c521d994a51d0f2d5454810cb153524436752d4530b9987324cb354314540f10cb314865e6315020cd151214427461551209798f540826e62d5131a
  | 6 => 0x40f806800016008000d20700040300004802c0280d22e0040101b0022b9a580200c00c0480d0280000003c0060000802a058000000060044a003003002000080070080dc088060080100000f002018108050062f0000002280c00000b02a014098030164800000e05a1180d00001c088000cd292c980288f000208040060202100a80b05400c04825110010340020980aea080125a0000f98c248090734c35f401404008012018d480a00c0640403a02000c0680e08600c020020660000980301803c080050bc0240689639c004110020041d0008190020000480001211c1800000802000922012141538000029400000903000010a8f1c21180d8060f20002f1570040002480001a2081d81c00c000008030000100380302c010098120100000980e020000d180101a0600303c000d5c0302c0000442e8190a0004000000080041982700c01401806038005e9801020001fa801004008000460000400f0790000140b04f0f0000038930340188a00008419400b3a0000340081a00e0140300d0260640001209a0090e803076050010f40000140780b36a00f376550441b398f4290aac6050842c718d54cc66d650c8209d185528c27561153328f99252442d6618ca308f99254442ae6488620d954a51d0ed561cc831cd152314425e65cc930a798e42d06b5648c421d3549300c2e661d0820d394d52d06ce62d0d32c7551300c23d6494d20c794f4390a6d62153319d58653482ce62d0d439798c53042756590431e3d0c424ca6e62944438f99054082e76448421cb54b401026f6548020cd50851502cd6390b209bd8953902766588510c794f42906746155130b358b31cc31e53d0e41cd553100434d53108209d195314434d53884209b58a544866d6295131b99874250a6d62d4f10ab98a43d0a5c6354042cd546411023e6515130cbd53524c3674254642cd90d51d0b2c54508219b588505066d6294c41c794f4290b356115110b3d85320ca766114c109758e52442e5628c721ab58b43906766194f209b59742083564394632b958a41cc7554394632ab98a41903655254430cd551100431e5494e21d954a510c29d63d0a42d3d4f524423c64549109b19542482e5618c8329d98654c829d64cc831b558e41cc71d6395232d594d31c86e662cc4109798c530832c6255321c794f419065d6594c20cb550424cb655254440d518553043545384110d9548210431d540c830cd153514c25e6314142c7151430c63d6414a10cd551510c3545314520ad993310434d5348020c715053442d661d0f329dd85548c34e53948409b98b54c433554d06218f9944350b4d520c8309798e52c423c6454d209718d51902d56190d3097d8d54843374394642cd552510c2ae64cca20d3151320cace62d0c30d914921c434c5390920d9185529072d54cca32b998b
  | 7 => 0x89982900200003876000018508000000000017b004068a600e0000080507f0020bc0001603601c240070d609801022000038011ba020288100240ba92c6b00e01c3080380a00001c008000740080000a00000c278000000180781d0020c80fb9004c46c000020060300381506a0340789808200d9380e1c400c0300412a0d800000000010000120003d007802000b1007036000038a2808022038050040000004e80409600c028010040382b82501205833135018080050220000640602f0020348300d008094170002c400001800000004700000ac0181c804862088010570060501d0000000200000b01c0080100f13805c0804301000002000194c88010240006341b800046000018270000100182301cbb414007004058010000041000127100
  | _ => 0
def q3K3 : Nat → Nat
  | 0 => 0x861654586438ca4ab88c0a188783191524c03098ae7b2a4210e26645462108322a94c319061515ce4214520c4aa8312200864553987420832331aa5a0c63235cf6550842c1ac82966298624625454010312aa4c3a1041899516290721a8ce5a1aa2186266454b2104312b20a390a41495cb4394642c2aa730c85a0e156494e31c8706b18a5a0a81499ca5350441c2cc8a8c621860e5458a438c70b29ac3a1483075da54cca32c4ac829462886466354b210430aaa4c790c4383d964350832c8aa7316620854672d0d5190f06a9cc52088115dd953c841092ae9b126218d2571d0e5290652ba6ca90843519ce544842191cec21a85994357695231c8713322a59882183550624c030c1cc8a9e6590d0e7510f424cb22292c399261459ce425444085eecaa4421060d5398a43d0706b24a7194439158e5290731c1ccba18849941f76552310c322a9cc598c438555263d0410c4ca8b148398c1d76953318c72229ac518a21459ce5250441c8a6430aa0194a571d8d4210b12292c3a1281499c64354b41c2cc8a9e420846676951210869339486a88818514d61d0d40a4ce929a4210c677654b31043073226528865439cb6550c43a8ae7214a39961653587439070aaa4c3190610ddd954cc41083aec2a664986166454f318870b322a790c438958851d0540c4ac829442884c571d91320cb06b20a7192418599153cc410c8ca6b148390ca571d954210b0aaa4c319663295cb6550441c8aa430a601861454587324c262b96ca988638395163c862189eeca9e84106165458e41cc70aaa0c6880218358e52d0a41c8aa530c6598e0c5458b314c30b29ac3a14858955261ccb218aaec29c828862564151210870aaa4c7a0c639154e61d0a42c88c498aa018e0c63549401032231a42a8043199da5348421a4ae5a18a2a0615631474150262b8eca990659198d52d064192ae7b2a8220e45631472148246ba0c099065859516390721c1aa631280206255498b410430aa18c2a80878355263d08208caed2948398e2464549100429339486a8e85831915348020c2ca8b0c8718c9571d954310e1a3b2a8880210ddd954cc631a8ae521ca3196155498f4188692b968728c8785590538c510a4ae3a1ca521c1c76551300c30731aa52088183d8e5350842a8ce3a1aa41851674949310c64aba6ca98863831516290d3091ae9b0a641960e6454a320c322a98c4880219198d52d041083eecaa464186155398642102263b2a690041495c74314940a8ce7a12a31964462545300c292ba46428a4189151618c920c1a86312a021cc572181310c71232242a8043315cc6048421c8ac629a4210e245458a4144322b18a510a218398d4294442c2aa830a601842d769532188712aa4c5a0c63159da544c43198ae7b224210e156414e214430ab20a398a6185191514c030
  | 1 => 0x414430aaa4c3a1861515c6431493092ae63028220e445358a4144306a9cc521881235c86050c43c8ca4b0e6518e0c635095010a26bb0a7212419194d618ca21c8aa730e8590d2674cc9518ca62b88c099065515ca4314530c1cc6a94842060c5458e424830aaa4c3a1e63899516190b32a8ce3a1aa521e2554987328ca1bbb2a9908218359052cc930c8aa730e6590e176590d410c68b39ecaa0883195d85290510a8ce3a1aa598d4672d95310c70a2a2c720a21155da539072186eecaa64310e0e6454e2108246b9ec2a1085851913154031c88a6b0c649060f64951320cb12aa4c3a146519dd952d06318aaec29c428860d5398a43d0b0aa98c2a008125dd9431063186eecaa66310c2c76551200828b38ecaa1887851516190d30c8ca6b0c8510c64765491004322a9cc5a0821455d33294632a8ce5a1aa39954671d95320cb0aa9cc321881235cc6050842a8ce7a12a21051573d085150246b96c2a1887839516290e3289aec29e42906266454b318c7132a2c518e43459d3654c431c88a6b0c84906246454520083132a2c31944383991528c430a8ce52a26218e0e5458e42cca27bb2a71084185d92544c431c8aa73168310e255498b31042933a6ca90843895486150040c1aa9316861864553185200830a31a82a80838314d62d05408caec29462885177150e5110f06b20a89906589189415404183aec2a662986465358a31c8712aa0c2900418554e6190f42c18c8992a01960d5498b43cca9338c86a9081139da544c832c4ca8b0c8510e0d5498b43cc687b9287290878359253c8621a4ce3b2a84216155398643d070729ac5a1c8391989518c43085eecaa6651948d72d954310f13312a320881255cf6250441c1cc8a946598e14635454010252ba0c090843459d2325443094ae43028220d457190e528c60ebb4a9994639154e62d0641c1ac72968320e0c5358b4350306b24a599463295d36348421a4ce5b2a8220e0d6414f214830729ac5a0c830b5d8548c920a2ae9990a29861654587328c70a29ac3a128145dd54390431c4aa93166318e0e5458e428864ab8ec4a18870bdd954ccb21a8ce7b2a4210e4663546210830729ac5a1c858555263c8410a4ce9992a21042f7655332082873a6ca990658398d5290b418a8eca9a200860e5458b318c70b31aa320881235d3654c832c2ccba188298d167510f414c70bb1ca6a088385590544c431c4aa930e8590e155498743cca16bb0a990a418955262cc62189aed29c8510c4d7694f21886a338ca89906515dd953c8621c4aa530c85a0e0c5458f2148216bb4a9194439118d514802083eecaa46598c967610d41cc713292c3a1483255d0604c431c8aa730e64104a572d8d4110706aa4c7a14658550e6194843c4aa930e641060d4398a5110f122a2c518a210d5d8548c5108aeeca9e82
  | 2 => 0xd800072d0405c001181402151900c320f0400044070200800000000000010000c4c06120380006060080001010000000000002002028200002110080816020441a04000181006068000000040180216000280a07468342c007b8380c040a0180607000080047000181020028b402071482824250007c004749000000000018144d000ac04000480cbe05000dd92050009c041b0500040060029c26015380c0c0a938003a160006804060002ce6120087c007300838003ec1ac629684a048f7650c428caa339e84a8c85851915344010c1cc8a9e64104677654b4104252b88c0a108543dd54390832c1aa9314621864562147314c312a94c32108189151619092086aec2a4428861654587328cb06aa4c7108418594d61d0e42a2ae7a14a32160d6494b318c72231aa488021851516388510a4ce329a842160d5418d2008312a10c2a8085439cf6550842c4aa93168310cc572d91310c627bb2a7a164315dd953d0621c1aa931e8590e456314a
  | _ => 0
def q3K2 : Nat → Nat
  | 0 => 0x81787590544c43180f87590544c832
  | _ => 0
def q3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 830
  | 4 => 1423
  | 3 => 364
  | 2 => 2
  | _ => 0
def q3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt q3K7 (i*5) 5
  | 6 => packedAt q3K6 (i*16) 16
  | 5 => packedAt q3K5 (i*27) 27
  | 4 => packedAt q3K4 (i*38) 38
  | 3 => packedAt q3K3 (i*49) 49
  | 2 => packedAt q3K2 (i*60) 60
  | _ => 0
def q3I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt q3K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt q3K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/297+packedAt q3K5 (22410+(h % 297)*10) 10) % 830)
  | 4 => 2*((h/509+packedAt q3K4 (54074+(h % 509)*11) 11) % 1423)
  | 3 => 2*((h/163+packedAt q3K3 (17836+(h % 163)*9) 9) % 364)
  | 2 => 2*((h/1+packedAt q3K2 (120+(h % 1)*1) 1) % 2)
  | _ => 0
def q3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffc0ffffffffffffffc3ffff
  | 1 => 0xfc1f03f83e07c0ffff1c1c1f0e0f87c3fd5293
  | 2 => 0xffe003ffc007ff03ffe01fe00ff007fc3e631c
  | 3 => 0x3fffff80003ffffe0000ffff8003f83e0
  | 5 => 0xfffffc0000000003fffffffff00000003ffc00
  | _ => 0
def q3Neg : Nat → Bits
  | 0 => 0x4000008000000000000202100108040000425
  | 1 => 0xa946659194aa95d1cb0d0d1a268d168b9d5292
  | 2 => 0x30caaaa28d353456d56217484ba42738ae6318
  | 3 => 0xa294d34529a1a69b66b742108dce72113783c0
  | 5 => 0xc318e38631c638e3b8db9b9ce10844223bf800
  | _ => 0
def q3Atlas : Atlas := ⟨7,rawDecor 47 q3Pos q3Neg, 0xeaaaeaaaaaa8aaa8eaaaeaaaaaa8aaa8eaaaeaaaaaa8aaa8eaaaeaaaaaa8aaa8eaaaeaaaaaa8aaa8eaaaeaaaaaa8aaa8eaaaeaaaaaa8aaa8eaaaeaaaaaa8aaa8, q3N, q3R, (fun _ _ => 0), q3I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def q4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def q4K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def q4K5 : Nat → Nat
  | 0 => 0xa83f631086fca1a1dfd4d40bea9e437651083ec42885f54232fa20a437d538437c84a0dfd5310bf28485bd54cc6baa6107d14530ba28a617d53d02fca3105f54740bf29681dd310c77886205f95020f7a1041ec32487ee42085f94841beaa6657c54887dc65905794c40bea94837d54907f641105f94442bea8087de53042fca721df55240bb28861fa40102fca520fd8c710bf29863de53082f8a7885f54a40bf29063dd4310ff220086f95331bea8683d5310c7d842105f15131be29a41df328cbb886995f14a10faa0e43bd43502f8a090db54a43fb90c21fa300c2bca720df952329f2a6437e51107be6518db54810bf29887bd54082eea2905f94c42ef29e83ee32887daa520f7d4d40bf28e873c544437a8720df15121bf28c63be4350efca7905f54031ee21e637d53c42faa420fdc8621beaa263f531c86eca2207790c43dea1083bc54442fea5885f54b40baa8c87bf43106fea098dfd4532ee194617c54cc2faa321df14e20be2a4637f53043de85107b54810f7a1285f741487de85215d94642bf288657c544c3f681207dd0631be282857d548cafaa610d714d40dfa1085ec52443bc6498fb94b41b629221bd40102faa3205f95040bfa9e417d54882f8a998fd14540bfa9281de314c77c82205f14931bea8483be43102fca5207d94742bfaa021df310c6dea4887b90821f690e417651d0fda8410fbcc921fd080217d53486fca918ef50f40fba8a81f641442fca021f790c31f7a92215e53083eaa2207d94743d6a1085ec524c3d843106fd0040bf2a2657e52cc3bc60985f54442bf29821f651cca7aa8104f95332faa8c656e5290efca218fd50510df2a6435d530427aa918fbd4940f7294837e520cb7885207d48710bea9081f65190afaa3987750e31efa1c617e508c27ea8885f94331bb28e657e54883ee62087794f21f6a9081ed20082fca6207bd0b21df2a061bd41502fca190df15332be29281dd328c7e862085f94241de21a83ec52502bca710df54e40bfaa463bf54443be6318db54b31df2a6657d510c37c82a0f754c10f619041be43506fea9987b10820be28265ee21486faa3a15b14930bea94637c54883b862186f10b41bea98417e51907bca7a15714d10be2a4657f53842fca990fdcc621aea9c857e548c3be65987dcc610b7290617c54442f8a9086f50441bf28c81ef21086faa5185f54243bea80657c5050efca720df54f20dfa1485dc430c2fca3a17d0c610ee29a21f7314c6eaa2185fd5321bfa8a615d53906f8a098fd54420bf2a641de53103bc8719778cb31dea18837551d0bd865107d0c621dea0e817d52043ea6218db94b41bf29c81f7318c6faa7a0dfd5331b6a90617e53c86faa418f790e31fb18a21dd5390afea898ef952329eaa4437c530437c85205f54242bea84637f53886f8a6a06f55221
  | 1 => 0xf54842fca8986f90e40aea9e857f540877e85a05f94443f710c417d53102fea9905f54a20fa10c21dd320cafea090fdc4010bfa9e21dd430cbdc6410dfd4d21eea9c836e52d0efca5195f15020bfaa2437e5010a7aa8085f94a42f729687ef32c86fea790df94232ee98a61ee52042faa4887bc87209eaa6637e51c837aa8086f10f41dfa0a817c548c2fca4205fd5230bf2a0217e53c42faa4187d90441fb108437e544c7bc65186f50c42bf29a21dd434c2faa1a15fd4930f7214437d52d0f7e8320f7cc030fda0281be43d077e8120778c630f6a94873e548877ca8106fd0740fb884217e5410f7aa918f70cb31fba08217e54486faa3215f94a10fb10e217d50887dca4205fd49419f2a663f541106fca8195d54632fa98e217f53883b8a6907bcca32be29a837e50082faa921774c930fba0c43f731487e86290df14540ef98a617c540ca7ca8187b48421deaa643755190bde4310fec4110efa1a876d52907be86995fd5221fc90041de430caf8a8905f54a43dfa10837f54482f8a2995f54610af29c85dd531037884207d94643fba0c21dd53886bea6a05f94642f7992657d51882baa790dfd4142fa90843ed32887ee8298fb94830f6996417f53482fea8186f95221be28a857c540c2f8a818df54630f7a12437d5010afca598df94a31cea18877f540c6faa190df54732bfa9a21ee320cafca020fd544309f2a0417e530cb7a87215f94210ae29a417d51d0efea8985f94740bea9c417d54c86f8a810df94842f719241f641c86faa2205f94820bf28c61ec428cafaa5985f54443deaa0617d540437e86a05d14540fd88421df4390efaa6906f10640ef21a61bc425077a8520df94f42bf29043be4350af8a9885fd4542bf28e61bf41106f8a4a1ef509409eaa6657d53887be8798df94810fb208437d50086faa8907b94b31bf294616e52906fca0085f54041de21a85f4418c6faa5887754f41bfa8a81bf4310feca2105f55331bea9c637e5210fdaa4185f55330bea9e857f53506faa5a0fe88020b7a92817551d0f7e8720f70c830bf28843bf4390efca1997948421bf29a437551103b887997d90710faa8c857d54443bc64995fd4a10faa0843dd320c6fca910f7cc230faa8e87dd438cafca2107d44010bf2a6637e52d0feca3195fd5220deaa665df320c7ba8618f754c20af29e837c52506f8a2986f15130bf29843ee528c6daa4206fd0f40dea1681be42102eea2a05f14b10bf288617e5348278a898734c832bf2a063f551d0adaa518ef50c43bf2a061f541c42baa7a0fd4c510bfa90217d54087f640904f55232beaa4877d54c82bca6085b149409f2a4637e51ccbb88698df95120bfa8a417d50d0fee8320df94021bea9c657f5350beea2907d84110bfa82657e50902bca790fb10921efa1861dd300c3da42905f94440fba0
  | 2 => 0x54040001611817040000040e0000203c3b0084200421000050602e0b57f000040a0503b41000000000175a8000401005001008003e01f0401207c0d0601d28404000040900001c9f008000080400000004040dc080080305c0917422030600000404c3d00087000000780106804000382e0070241200442028270840e06c16030070000606848000e000400000050200600006004000f10a020170140b0381e008230d400094210380904c00134011181209c7d01c020642800800098101300a0000000c04029ac0640f0000400008000010001900000040000941c034004c000030040605f0e81c4340004800008030f0000040a020020000013802048050141003405098000900a038260d404002faa2105f94221bea8665de5390afaa2195f54a10fa28a41ed42482f8a2907b88120be29e41dd31cc3da6410dfd4141bf29c21ed420cafea498f754f42bf28c87ed4210bf661185f95042f7a12657d528867ca9195f15010f7a92617f53082faa8107dd4530bf29e81ef320827aa8185b94840bf2a6657d54486eaa3995f55130ef29c83ec42882faa918df54720f790a417c52442eea2987794e21bf298417f5250fba87987b54b43f6a96836d52d0fba65985bd4930bfaa221f6511037882207714d40f79004175510837c85a0fd8c721bea98217e518cafca0187b90920bfa8a877f52442f8a690fb88420be29e437e53882fca310ef55232bf298615d53102faa620fb90832fa20821bd4210afca810dfd5032fc980617d54c42fea9995d94643f7210857e54842fca020778c830dfa1885f551ccbbaa790df54e30fb20e637451482fca4884f95010df2a46376518caf8a6105f14e21efa9a417651d0b78a8905f94410ef18861bc439037ea8907b54a31fa90a21df320cbe88310df95310f6a16657e5290efaa720df54d10f621643ec32c86f8a9905f55030bf29e837c50507ec8218df15132be2a6437e53887be63985f94342fa20c217d5390af8a6885f55132faa8c87bc43d0b7e84a07d94430b7294637c524c2faa198f710e30f6212656e52cc6faa8196f95010bfaa4657d52cc6fea8105f54c42fb188637f53087ea8398fd10531bea90877e5390afca1a0f790f30beaa0637d54887b863185f95330f6a16417e54106f8a2a1fd50431dfa14833d54c87de65106f90f42beaa4217d518cbde41106fd0e42afa9a21b541106fca88877cc930fa988437e500cabea690770c931f6a96635e53d0be842085f94243beaa4617e53106fca4185fd5132f7a1465df53443dc85905b948109faa2417c53087ee4290dfd4143be29c21df43ccafca018df942209e2a241ed32483f280205f94231f7216653f544c3be8698fb94a43df20281ed320cadaa5a0df94b41dfaa2617c5350bf660985f94b10be29021be4250bda8510d754e21df20c817
  | 3 => 0x6c00805114080291805806002580001301807008130040b0294a031c800c0a034700000206c050000a06c170ec1c0d4061343c050001544c01401028331c29d21c09108020082607c05008001d8ec000060040002805234000400d0
  | _ => 0
def q4K4 : Nat → Nat
  | 0 => 0x321887554394632d954b418c71c5414d208f59252443553214530cd151414423f6454a10d9109518ca6c6254d109798c5050a5e6395021a758f419072c4354b419d98754c826e6215230cd146405034e53948409bd95210871d54d0f329dd8552902ae6290640ad181411074e524ca31b358b310c63e6414e21ab992210834d5394840d914a214431d4354043c7153534431d540c830f14c8318863f6550c419758f540872f54d49108f99353c87364354440ad993210432d5410820e510f414c67561d5320cb18954082e564484219bd8953442e561908219b594420823f65500409798e544823f6454630b958a41106ad648c821ad191100434d528c430add89411066d6590832d5d0d510c26c6255110b9987424ca6e6295310cd55041042e56290431a758f4210b2c52d0540c794f42907654294732b958a31c425e63d5020ad5874310f1d5494f21abd8d4210a3d64947309dd95210874d53d0b21ab189401032e5494830cd153514826d6295110cb553328ca5e63d5320d914a414423e6494831b9586328867761540439718d52442e56190b32f18c931086e562907219d99641442cd6290c43b5987438c364528c5109b98b54042ad64c84219b58a53d0354514c5308f592530c66d62d4d419b98a524426f6550842d994a511025c63546409b99442486d4604c431cbd53524c32d6295221a758f41d027661d4c209b588540c26d62d501097596530426d65cc8209d5865310a6d6295031b958632482e661d0a32c794f4390a6d6295330c754e42d072d4254042ab1814210ae5628c510cb153524c23e6515130d510d510c25d6394841d554c318867b65440109d987530873454507109798e52d031d5410f32cd95131c871c5450d30cb55221083555310621b598632cc63e6510d41c715353482ce628c531a7593324c27665cc521c7550310c25d6395131add9541106e5628c421b358e420cb374314540a758f429072f4394a419798f525073554c84109b588505065d63d5020d594d510823d6494d20b5185300c2e661d0820cb94b42906cd6290d309ed95300c3565394642a71814310f365454420d554d51083654214520b398a310c27565c8410c755153c874e538ca21cd15131442cd6390b20b398e210832c5448520d558653c872f4394a439bd8953842ce63d0942b5d89310c7675208610cb55332c871d5310840c7d535344355514c030d594e51d0a766114142d314c524425d63d48109dd855010a5f63552209b195324826d6295131d90c9510827965840109bd89534823e6494832d9548310429d64cc8329d58653d025d63d4b108f59353c863e6495130c714f425027561d50208f59654082e661cca20b9d91210863c6454a30cb551200832e5450a21cdd0a5190b4d6294f42b5d95310c76552104109d984548827561d4943
  | 1 => 0x427665d0521b398e214863e64d48109d185544823d6494832c7553430c34d5394a418f990540c23e64d4e21cd55041886e661cc932c7951328c69f6250c43f10cb314871d5494c10cd95151cca766115232c754c41102e46048421ab98a43903375414520d554e5190a3e6414e10d310d52cc6766114e209d9845050e776154d109d987540c2756195130c7d50534434e534ca21a7992314c76752d4530b5987434c72d5410932a798e429025f6355130a759332cc33554947328f992510cb2e5454a319758c50486cd62cc530c795153c86d56190e319798c50506b5648c7218f59253442ad64c8621d314f525025d658c830cb55342083374394642cd153514c31c5350940d354d521032e5454830b598f418431d544c0309b98b540c2ce62d0f318f99253c83944350731d5d95310c66e62152109d586544832d5250040b9987328caad62d0d40d994d210871d5494e219b98b54cc34c524c9309758e51c835551cc0309b988540829d64cc4319b597420826c6255230d354f32083656194b41d394d52103573214530cb15352442cc604c832d394e52906b664c85219d98653d027561d50308f59253487655294440d394b328c6776154a30cb151420cab561d0841b3d91320cae661d0921d94c851482cd6290f309dd8553902ad64c8520d5951310c65e6394740c7951538871c5450f308f592520866e65cc9218f992544833454485109bd895010f665294643b998732082d56390441cd58654c86d56390431d5d4f51502ce63d09329dd85548834c6254f21d314f214826f6255230b5587328c6756114143abd954210a7661d53329d98652d02b66190942ad99331886cd63c8720ad993318c66d62d5131c7550430c32d5454a31cb50c525029d64cca32cb95132887365490731a798e425071e5454c10cd550318872c5490920cd54540102ae6290d41d918552043646154a419718d548833451505408f992534863f6454e10cb50a5110b5553544408f992530c75643145309d994414876632145209758e51d025e63951108f191534434e5354810cd185540425f654c030ab98a415075453145409b596210831d5310b41cd55031042ce63d0a328fd91528c35653544409d1855010ace63d0820d3d95320cb2e4354840d390e528c69e648c4308f992530ca5d6395121d58c9510c27661953209758e54c82756194d219798c54c866d62d4543d954b318c65e63d5221d394e52042cc624c030d3149314c23e64d4f109718d51882776154d209b98a51d02cd638c8329b98a544c23e64150108f993524c6ce62d0d439dd9510043365450721b918520082ad62d0e439b988540c2756194843cd551510c2d56390721cb952328863f65508429718d5010ba442507218f19152842b66190f428f593524c7355494430d3d0d5290e3d64d4f10cd55
  | 2 => 0x63d0541a758f411065e6394b108f997415032e5490b329798c54042cd6290c32e3d0c424cb6452487109758f54c86d663c86108f59252c425f6354a109d59431042756590421b998b418425f654c832d9d48514c26d62951329b58a534431d5454c20cb14b425023f6454e20cb55032083556114d10cb552520434d528cb319798c520438f4390b328f191538431d5310c40cd546411026f6255210d314d424825d6395110ad58743502746154a409bd89539023e6494f10c7553300c26e62d5231d354c324869e6390b419bd89519026e62d50218f191538825f63551209d185500ca6e62d4c21ab98a43d0754534c710c7152304c31e53d0e419d594410432d52d0040b59874390f2d52908409bd95320cab5648c431cbd50524434e52cc631ad98642507376550441b598f410427661148109798e54c42e661cc921d5147314c31c5390140cd147415032e52d06419b58b540c25e6510d32d9949510c25c6354021ad9864350a776155230ab58b43d023f6550841e950a410866e62d50329798e510873551d0040ab58b4390a9d64cc530ad18540102ae64ccb21ab98a41102e662cc531d554c310431e54cca31cd552510834c544c832d3951320cae661d0a42cb550428cb1c5414d10d554c410432d54c80209d185548c2e56190842cb90d52d066e6295330d9cc9510825f63540219d996314436752d45409ed95200823f6454021ad59241106ae6290c409dd85538834d520c430a758f421067461540439758f548874c53881209b58b54c434e43149309b994424cb364254440d994a510c27661950329b98a544c65d63953108f593530865d63d5310c7552320c25e63d4542b5987434cb4f4354b31d5d4c51482e56190a219758f525063e6515110d5151310c63e65d0d409758f54042b66190a40a7992328c34c52cc930a7d954310ed7644c431ab592328863d6494831b358a438ca5f6550c328f99352c427661d51328f993514ca5e63152219b58a53106b561d0e43cd552518ca746550510d394e42887355454632c718d540c36451485209b98b535063d64d4f20c795253c863e64141328f59252cc27661152308f191500c71e5350a41d3d4c525023d6494720c755032cc7c4324c7219718d529026d62d5231b998b31842766194d209b98b544c7344354742b598f414c677615403297d8d518831e5350e419b189539033754d4530ad587429066f6254041d394d52d074d520cb31b398b434c74d530cb218fd9152443355410631d358a538874d53084209798c540825e6510d318f59253c831c53d0d409bd95320863d6414c10cb55042c875553c8410d9d09518ca5f6354042c718d54ccad661d0c30b958642482ae6488521d594d51d0a7665d05319798f54c866d62947309d987548caad648c920d554c314863d6414131d5d4c318
  | 3 => 0x421ab59321c823f6454d20cb588544827761551309b58b540c73654907218f99353042d56388710b598f414872f5414930c754c43d069d64cca318f59050486cd644c8329798f520423d64148109b58a54486746548510c758e548c6e662d0410d350c524c35653507219d584504cb6452841109798f540874d3254032b998b314866c62551309b58a53c42d56190c318f596421026d6215010d314e32482b561d0f40c7d53534836552d04109758c54042b664c8621cd55021042e562904219d58453882d56388510cb553428cacd6290e31cd55151082b561d0e429b98b53c43664294732a7992324c63e6494431cd18554887364354742d5546310c2d663c8410d554e51d0a3e6494821e9909410865c63551109b98b530427561950328f191500863d6414e10ad986439036652544409d98652cc23e6510941a798e41507c5328c4219bd89544c31d548cb319d586544c73454145309b189500c6cc6348020a7992320c38c43d0932b358e420866f6255120d550c514c34e5354a41cb150524426d6215231d9548418c734548c510b958a310c76552c4010d354c420823e6414e20c7953318c65e650c931d514d314432c5450b209d594210434c52cc530cd95231c871e5490e31cd151410c6d56388421d9549100432d5494a319d5875350aae6290d43cb54842103546154e419d986544c26d650c8208f592530cb2d54d0b21d310d520c32d54948308f59353082746154a30d514f515038d43908328f59643102ce62d0e30d9549510c2d561cc8319798c548827565d0410b958632c82e662d0531b398f4290b645214540abd854210a7665885109d586534826f6548020cb153214834d524c030cb150524c25e6314c10cd550414c63e6414c10ab99332883655108420d994941cc6ad62d0c42d990851482d6618ca308f9925108674654c51097997324c23d6414132cd50c51503345490510b358b31cc2766195120a798e41903546154c108f191518826e6215010d354e210826d62d4f109d587544cb2d4394a418f59053c866e65d09329b58b54cc71d5410f319d98653c827561d5032b958a31c865d63949109b19542482766114c10e550e410c79543106319798f540ca9e63908409758e544836552084109b18954842d5644c431b3d85320cba74210521b398f424871d54d0f31b9586320cb56534c721cb54a411034f53d4910cb15142087545314520cd1095110277655042197596530826e6214143b998b310432e5490a21cd152214436552944309798c53082d661d0f32cdd0e5190e7561953309b58854cc75453841108f990540823f6454032c714d415025e63953208f99053c873754145309bd95420874d520c830cb58a54ccb4d5348020ab58b415023d6494f108f992544431d5494c20cb551520432d5410921ab58b43906d6
  | 4 => 0xd150514834f5314910d354f420826e6215231c7550434c6e46244010ad59221c432f4314940d5d0d51cca5e6394910c754e43d0ad563905109bd95420ca776155120c794f4290a6e650c9219d58652d034d52cc03097597430c2746154e40d554d51d0ae563484219b98854cc65e63d5121cdd08515027561d4f20d314d214827661141329b988504c7365454430b9586420cb4c53d4910cd55041486756115232cb54842d066f6254031c7151324c33561953319b58854842ae64cc820ad59221442cd63c8421ab592320cb365494430d514d21442e662d05218fd9541106ae6290f429b98850507565354642b5586434c2b66190840cd55331042e56290731cd50e5190b4d5354810cdd5041843555394440d354a320c31d5410d32ad99331842756194f20b59874350e76650c521d31895390b6552d0641d554f31886cd639084297994534432c625523297d8d548434d5394810d34ca510cad6618c931d954951102e661d0b219758e5110a3d6414c20d9151210865d63150209d58652cc2d56390421add8d411071e5490e32a718d401026d629531097594430c33554d04109dd95410c6746155220d354d52906ad648cb20ad5874310a6e62d5310d9951210865e631521097d95310c66e6294d10b958642c825d658c430d910951082766115030b5986320c2cd6390a219d58754cca7661d5330ab58b419071c53d0540cb55252cc71f5414d209b596520426d6214131d95495190e3f64540319d986544cb4e53c8621d594e511031d5390c40d510d51cca3d6595030b398b4390f3454504219d596410c72c5250940d394e52d076552946439b98852042d663c8521c795253043656114910cbd954210a3e65d0940b5586430ca6c62546408f59052843355454732b5587324c2ad6490842b958a41c426e6294730cb551520c29e648c9329758c5050b64524c510d554f41886e56290510c750e5210f3554c40108f590538872d540cb21d514d414431c544c530c794d4390b3754d4520d9d095190ab561d0e419b189538426e6294f10b598743cc65e6394841e5d0e41cc67661d5021cd505501065e63947209b98a5110e6d62d5330cb95142cca766114c20c718d54cc69c644c0309dd95310c7575314540d99495190e9d6490c439b98a53106cd6390920cb1522048277655044197997434cb6551884208f593514cb974310531b998b415066f6255110b358e42ccb3554440109d9865310ab66190b41d354f32c874c534c920cb55152cc74f4354830ad986435072c62553219b996324827661948438f99353082ad62d0740a759331cc34d5354b419d584548c31e5450e31d9545200825d6590c32cb54a42d074d4394a31cbd50428826d629513097d95430c6d463440108f191500cb1d5454e21d954b31042d561cc8329d59631086e56288
  | 5 => 0x52042756195320cd10d5110356538c721ab992218825e65d0d31d554d5190b6765484218f990504871e5454c20cb149415031d63952329b588548c35653944208f99253483655254743d354c320826d62141438f593538863d64944218f993530863d64d4b108f99251cc38c4350b329758e52c43573294632b998732c871d4394443b358f218874d53d0a4297d95320c71d6315130c7d954310e5c6550d309b9885308354518c130cb15232482d56190e32d3d4c328834e5350a21cb953218867561d5232cd952510826e6294f409b189518c25d6395021d5544310c31e5494e219bd89518c2cf654c832c754d401027565cc410c7151430c6756115030cb14a405025e6394442d914b514c26c62540439b58b530425d63948219d587530838d4310a32d554e510823f6550c42e910b41486cd6290c31ad59231c431c54cc930d9149214425f6354640c794f41907674254420d9185528c74c53149409798f52c42b66190f41ad993310435743546439758c54887665290731b358b318c7656194b319d984540426e6295110d554c210432d54084209798c50486e763484219d987540c63e6494c21ab191200825c6354041ad592210867661d4d429718d528431d5390f419dd8554443673254632d354f200826e65c85209798c540c356524c431ad592314427661d5020b558e41cc71d5454c1097d8d501075643946329d18553882ce62d0d328fd954310ece628c630b358f21482e662cc621cb951520425e6514d209758e51086d561cca32a7d854310f6451c8520d514d310873461552318f592530865e65cc5309d58454cca9d63d09409718d544827661953309d58454882ce63d0b21ad986431023e6414c20b598f419063f6454d10cb151424826d658c821c754c43d0b4f53d4940cb95252043365494732cd94d411065d6314810d554f419065d63d53208f59053882b561d0b409d185534823d6494432cd544411027661d4943ad5874290a6c6254041b398e218835453d4520a798e41102756195121d5d4f51482ae64cc9329b994524425e6314a109dd95310866e629503197d954310e6e65d0921cb553320833554d06219718d548427661150209b588530426e62d45438f99353c823d6595010cb548411031c5450c32ad592310866e65909208f994544839643d0631d5185538873652504419d58453082d6618c932c7d50438c27661d50329b588538431c5350d409798f540c65d6314a108f990504c6b664cc531b598f418876521540218f99052842ae64cca32d9149414425e63d5310c7152434c26d6294443cd5845444366529474397596430c6d5639071097d8d544438e43d0a32ad58742502ad62d0c41c7552310c27561d5330b598f418c78e43508328f99252c431e54cca32b398b430c27665105319b58a53486d56190c43c
  | 6 => 0x2014030000140280000305e0000700706a05c0000104c040170052320047502a0c0000058180000106e0090000f00182f0020301f04e2620000b018026000008460000280880700e0180080600e0340a80001009c05817012198008080723554a8050223bc0b045016c4c780630000dc000010040081900312800003800004144028000040800d02a00024806049006034038042ee0003502312c024060250100006680b030004150010040081b0000000400001700000c06809002cec0901a0000040300505e0140000e01c0880481703608404acf0720541183800c000008432640340684200004c0301c01200c0883303c0f8018008e402009005012188010250040244f00200e924000071f800001816024000200230860080001e05e008018b0064004018830760783c844002098000040000641b0000180042580a018004058cc0000200f00016e04402870000000000000be140120b400219c078080120181480d00e000000130280000a8000ee0fc01820016078080a8004000110342040100a8050000540100101604c0001f01003c3900000005a3d65904408f191534823d6494431b398b43ccb5553c86219758c54842e662d0621cb95252cc65d6315321d54c5500c74c6254c20ab58b411063f6454620c7951438cb655294743c7153314c35553cc410cd952518cae5618c8218f99252442d5638c4319798e544873554cc621b998b419072c544c9209d185544c3645348421a758f42d023e6510d429d98454cca9e648c6309798f540429d63d0a42d9547200831d53904409758c50506b664c8610a798e4250a3e64d4d219758f544863d64d4d21cd50851502b664cc521cd152104425f6354a409d5845050b54538c510d354e52d075453885109758c54883365454632d554f410432e5250a41d558653d075453905108f99253443543254430cb10d52102b561d0c41d9d4851503c7320c5218f19152442d56190f30d914b515029e648cb31d314a304c2e662d06319798e534432e5494a319758e544caae6290d42d994951d0e3e64947209d586544ca9d64cc6319b98b54cc65f63549109d584540832e5454b31b998b318c71d53d0040d914620483645214530d3588534826e62d50318f191518c2b561d08429b58a51d025e6394d209b59642086ce63d0a209ed95401034c534cb209d98753c8356539072197996434c2e76548421e9508418876552c8410cd95141cc73554cc6319758e52d025d63d4542ad9864350ed561ccb30c7952530823d64d4c10a758f415035553440109b988538435553c4010d314e424826e6214c109dd8552442e661d0942d354c42c863e6494b30d314d32086d663c8621a7593320c6e661d0a20ab58b4310f9643504319798e520872e53508428f99052042ae64cc921c754e421033554d06318f593
  | 7 => 0x30040011040041302a0180000000a01617c040102180c4000840040280a00c0021f4018670526740000103a0080b800000008488270241941a06500c4b40380c02c1880500505e028080270100f80000300a010100000022600401501c1240580c0004702180000400c000da0040140003601402c0f0030560044081c000000028021000003d819004038058080040040580401422c350ad00001c5180100a0140000242c0381900f0080640680500c008190000100000a80201e5b420800004080030240100004d88502a0f8088440fe00c4480a014028008000180140b0020003dc0e80d042a240600301a0000d0000ae8180000318c004848020380003f004072000dc80d01604c578260340240503401e038058020ce3e4048050001f4d602a02
  | _ => 0
def q4K3 : Nat → Nat
  | 0 => 0x1051573d085150246b96c2a1887515ca431453089aec29c8490625541852008307b1ca6a1085499c643548408ceeca9662084577654f418872231262a8063255cc60504418aeeca9e82084a5741812108652b88c0a108591548614c030c2ec92a26218e26525874290706aa4c51886189951629073194ae9b2a4210e2554987328cb06a98c4a00810ddd954cc621a1eeaa1c84196455298632cc6a339686a8c8789151618c920c1ccba18849961665d0c414c626bb4a790c4385552618cb31c4ca8b0c8510e0e5458f218870729ac5a1c839118d2154021c1aa731487a1615539864310312aa4c3996438999152c8410c1cc6a14a22151574cc8514c24b3b086a0e630d5da548c72198ae3b2a641960e6354a4110307322a799643519cb4354732a2ce72928220c2d769523288712aa4c5a0c438955262cc621c1aa93168798e246250550106273b4a899065255cf6550441a4ae5a18a2a060e644ca510ca4ab8ecaa1887839516290e32c4aa930e85196265458642ccb06b24a599463255c76250c43c8aa63122008516739095110312b10a3a0a81315cb654c43192ae9b2a6218e45631472148216bb4a990c43895486150040c1aa731482204a572d8d4110712aa4c59882185d8e5350441a1ce9b2a641960e6454a320c287396caa18878599153c8410a2ce7b2a8220e255498742c8662b9eca9084391189514c030c2cc8a8c62186255498732082263b2a690041495cb439464392ae23028621e456314a2144322b18a69084345dd54390431838ecaa260186245458a314430b322a790c438955262cc631c8cc6a968208614535874350246b9ecaa1085831913254032a4ce521aa3a14c572d91310c633bb2a5a0821295c76550842c2aa931e4310e1564147314c312aa4c5a0821295c76350842c8ac428e62986465358a41c8712a10c2a80850b5d8548c92091eeca188519615431855010e62b98c090843515ca439463286eecaa6620860f6590d420cb13322a598c638955261d082098ae3b226419644635491004312aa4c5a0c63455cf4294642c1ac629682a06255298642d070aa9cc321e83515c64394a31a4ae3a18a4a049574181310c706322a498061315c8604c431c8ca4b0e6518e1553185401030b29ac3a1483831516290d30c28a8b1c828852672d954110616bb0a990a418518d5150040a4ce529a8220ca572181411068b38ecaa1887859516190e32c1ca8b148718c3576152314430b2a2c399463315c4604c832c1cc8a9c42104977650c418c712b20a510a219154e61ccb21a8ce5a1aa2186155498f210432329ac31944389951629072191ae5b2a8621d4672d95310c70b2a2c39946543dc94394843c28c898aa018e0d6494b318c706aa4c7a1643135da5390a218aaec29c42886165458e41cc706a9cc521881891915148020
  | 1 => 0x3208312aa0c488021315cf6448421c8aa630a401060d6414e3248246ba6c29906589951618ca21a8ce52a26218c657614a314430aaa4c3a18610bdd954ccb21c8aa73168320e2454586424830aaa4c7a0c43519c74354a43c4ac8294628854673d09518cb0a2a2c3992619198d52d0641c28a8b0c869861563147415030bb2c86a086383550624c030c8ca6b146390d1574cca518cb12322a4880218359253c8621c4aa530c8420616535874290aa2b9c8428a418355263d0a32c4cc4a8c822060c635095010b1232242a80438554e6190840c8cc4a8c62185167510f414c69338ca6a1085499d33254632a4ae5a1ca32160c5458f214830a31a82a8083855905388510c8aa530c641841d76953318c72229ac520a219158c5290510c1aa731487a0c1f76552320c292b8e87294878315162cc5308ceeca968318e0d4398a5110f0aaa4c3190618359053c852094ae5b2a8220c547654d1004246b9ec2a1085235d0604c832a8ce3a1aa41860f64951320cb22a9cc3990418555263d0410a4ce521aa220516748c9510c2a339eca9084385590544c43192ae9b126218e146454d1004307322a5188618514d61d0940c8cc6a8c42104a574d8d21087132a2c518e430d1d95444010c1ac629684a060d5498e210830731aa5210818999152cc410858ecaa240106155498f418c70aaa4c3a1e659118d514802089eeca9e8590e155398643d0b0aaa0c68802185590538c510c1ca6b16872141d76953328ca8b3a6ca98863195d852905108aaed29c8390e145458e2144306aa4c5a1861515c64314930c1ac8296649850e73d954210b06aa0c69004115dd953c862191ae63028421525748c85148322a9cc598c430bdd954cc820c2ca8b1c8390d457390a51cca27bb2a7a104145dc543944438aced2a26218e4553987420830b29ac3a1c850ddd954c8410c28c8a8a601862564147214828b3a4a4988638358e52d0a41a1cea21e849960c5358b4150306a18c4a80878314d62d0d40c2cc8a9e6310e2664546210830b322a798821195da5290731a8ce7a12a3216455398b310430631aa4a0081519cf4254420c8aa730e852162452587425032331aa5a0c63235c86050c4386aec2a4428848d74d95320ca9338ecaa108515dd953c841083aed2a66518e1554185300c22abb0a720a21499d2534842191cec21a859961654586438c7122a2c520a218555261d0f31c1aa931e84104667694d210870aa9cc3216839114961cc93083aec2a6629854671d0d52cc722a9cc5a08219194d6190a21a4ce321aa5a0e445358a314430729ac5a0c83831516390920c8a6430aa01949573d89411072331aa59082183590544c832c1ca8b166318e455398b418861bbb2a998c638359052cc53085eecaa6651960c6454d2008306aa4c5a1e659114d6190920a4ce9992a2
  | 2 => 0x3384a00008504e000d01c0020020001c0e11c001212150040c00558204264008080001989b436023fc042a058c008003a0b0100c60368041e0002050e600020001a000c008160601800240008848180102000420f0c00004000001c060b068140684a52c4080020830060c7b528584702b9c08002e04816000c9c00c0105020001e1a00822030300018010005402000d00000ba4701400ff00012b6000e39038e8000000800050d400370800080040000412050a0083c00c48c4a8a802060e6454a32cc617bb2a91084185592538c721c2ca6b0e8720c377655321886a338eca990659114d618c920c2a8730ca421e0d6494e3288722a9cc3a1643191d95244010a4ce9b2a4210c667695121087072a2c721443519c6544c83283aec2a66498546739512108712b20a8908438598d519044089aec29e429060d6394b419060fbb2a9188618398d5290b41c1ca8b1c85996456394a41cc692b8e872948313dd9538842083eecaa46598e0e6454f
  | _ => 0
def q4K2 : Nat → Nat
  | 0 => 0x81787590544c43180f87590544c832
  | _ => 0
def q4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 830
  | 4 => 1423
  | 3 => 364
  | 2 => 2
  | _ => 0
def q4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt q4K7 (i*5) 5
  | 6 => packedAt q4K6 (i*16) 16
  | 5 => packedAt q4K5 (i*27) 27
  | 4 => packedAt q4K4 (i*38) 38
  | 3 => packedAt q4K3 (i*49) 49
  | 2 => packedAt q4K2 (i*60) 60
  | _ => 0
def q4I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt q4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt q4K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/290+packedAt q4K5 (22410+(h % 290)*10) 10) % 830)
  | 4 => 2*((h/509+packedAt q4K4 (54074+(h % 509)*11) 11) % 1423)
  | 3 => 2*((h/163+packedAt q4K3 (17836+(h % 163)*9) 9) % 364)
  | 2 => 2*((h/1+packedAt q4K2 (120+(h % 1)*1) 1) % 2)
  | _ => 0
def q4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffc0ffffffffffffffc3ffff
  | 1 => 0xfc1f03f83e07c0ffff1c1c1f0e0f87c3fd5293
  | 2 => 0xffe003ffc007ff03ffe01fe00ff007fc3e631c
  | 3 => 0x3fffff80003ffffe0000ffff8003f83e0
  | 4 => 0xfffffc0000000003fffffffff00000003ffc00
  | _ => 0
def q4Neg : Nat → Bits
  | 0 => 0x4000008000000000000202100108040000425
  | 1 => 0xa946659194aa95d1cb0d0d1a268d168b9d5292
  | 2 => 0x30caaaa28d353456d56217484ba42738ae6318
  | 3 => 0xa294d34529a1a69b66b742108dce72113783c0
  | 4 => 0xc318e38631c638e3b8db9b9ce10844223bf800
  | _ => 0
def q4Atlas : Atlas := ⟨7,rawDecor 31 q4Pos q4Neg, 0xeaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8eaaaaaa8, q4N, q4R, (fun _ _ => 0), q4I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def q5K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q5K3 : Nat → Nat
  | 0 => 0x8010037905d30ea21b482f987710
  | _ => 0
def q5K2 : Nat → Nat
  | 0 => 0x324c120d130443848110
  | _ => 0
def q5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q5K4 (i*4) 4
  | 3 => packedAt q5K3 (i*15) 15
  | 2 => packedAt q5K2 (i*26) 26
  | _ => 0
def q5I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt q5K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt q5K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q5K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q5Pos : Nat → Bits
  | 2 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 3 => 0xbf333e3ba0da
  | 4 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q5Neg : Nat → Bits
  | 2 => 0x0
  | 3 => 0x42444211044a
  | 4 => 0x241814820914
  | 5 => 0x1801a92012a0
  | _ => 0
def q5Atlas : Atlas := ⟨4,rawDecor 60 q5Pos q5Neg, 0xfffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0fffffff0fff0f0f0, q5N, q5R, (fun _ _ => 0), q5I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def q6K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x400028036907710be61d442e986f20
  | _ => 0
def q6K2 : Nat → Nat
  | 0 => 0x344c110c930483848110
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 3 => 2*((h/16+packedAt q6K3 (90+(h % 16)*3) 3) % 6)
  | 2 => 2*((h/1+packedAt q6K2 (78+(h % 1)*2) 2) % 3)
  | _ => 0
def q6Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 3 => 0xbf333e3ba0da
  | 4 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q6Neg : Nat → Bits
  | 1 => 0x0
  | 3 => 0x42444211044a
  | 4 => 0x241814820914
  | 5 => 0x1801a92012a0
  | _ => 0
def q6Atlas : Atlas := ⟨4,rawDecor 58 q6Pos q6Neg, 0xffffffccffccccccffffffccffccccccffffffccffccccccffffffccffccccccffffffccffccccccffffffccffccccccffffffccffccccccffffffccffcccccc, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def q7K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x400177105e30d84170c3b087410
  | _ => 0
def q7K2 : Nat → Nat
  | 0 => 0x320c020e02004340c010
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 3 => 2*((h/9+packedAt q7K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt q7K2 (78+(h % 8)*2) 2) % 3)
  | _ => 0
def q7Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 4 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q7Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 3 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 4 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q7Atlas : Atlas := ⟨4,rawDecor 57 q7Pos q7Neg, 0xaaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000aaaaaa00aa000000, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x700000002010103007f08001fc10007f44001fd21007fc4001ff20007fc8401fd20007f08401fe10007f88401fe20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x182000ff14d20007ee6290803ff43080017f3282000ff55220007fca9108027e6588401ffa1c2000bf98f20007de8590803fe54c8001fea1a4000ff4ca10007fea310003fd4308001ff2982000fbd4b21007fea990802bc6444001f79924200ff90d10007faa790802de6388401ffa9c4000ff10121005ecc210002fe65c8001ff29c2000bf98d21007fea790003fc53084016e31a4000bbd8910007fa8710802fe65c4001ff2984000ff10f21005fcc988003fd5188001feaa64000ff15321005fcc990003ff43884015f3244200b718d10007faa690802fc6348001ff98c4000bfd8a10005f8cb08003fc5344001ff2a64200f948421007faa790003fe4304001ff2024200ffd4f10007fea990003f75148401f7a904000ff55310007f8a610003fe5388401ffa9a4000ff90f21005f8c688003fc4388001ff21c2000bf98c20005f8c888002f46148001feaa24000bf99621007fea988003ff4284001fe2a44000ff14121007fc8610003fc43c8001ffaa44000bb98810007f8a990002de63c8401ffa9a4200ffd4c21005f8c710003ff43c8401fea1e4200ff14e100057cc9908027e6508001feaa22000ff14c10005bcc610003fe43884017bb0a40009f19510007fea890003ef4288001feaa04200ff95220005fcc788003fe3048401f79904000ff54e20005fcc910803ff5344001ff29e4200ff15310005fcca10003fc43c4001ff29e2000ffd0f10005fcc610803fe54c4001fe2a24000ffd5121007faa788002fe6408401fe29c4200ff10d20007fea810803fd5348001fba082000bb58810007fca890003fd3188001ff21a4000ff50f10004fccb90803fd43c8001fba0c2000ff54e10005bcc608003ef4248401fe2a24200ff15021007f88610803ff4388001fe21a4200ffd5110007fa8710003f751040015f3202000ff90f20007fea608003fe54484015f3204000ff54c21007eea308003fe53c8001fe1824200bb18910007ee6308003fd5404001fea1a4200bf98c10007fea708003fc54440017f31c4200ffd4c20007fe8690002fc6544001fe21a20009f19520007fca710003f74188401fea9a2000ff95110007faa908003fe5048401ffaa02000fdcc410007f8a790803ff4348401ff2a02000bf19220005fcc990803fd5408001ff29a4000bf19620007de6590803fd4188001fea184200bf99721007eea310803ff43084013f3282000ff50a10007ee6310802fe6448401ffaa42000ffd5020007fea710802fe6408001ffa1a2000ff90e20007f8a808003fc4304001ff29a4200ff55221007fea508003fd5304001fe2184000bf99521007fca610803fd4344001f7a104000bf99010007f8a908002fe63c8401ff2a42000ff15020007faa890803f741484017e31c2000fbd4a20007f88708002fe6508401ff21e2000ff94d10
  | 1 => 0xb02830146cb809a65c30006cd42c2424003ab400c00020001805703400000070000c104408008000001d0404000020024820001c1c00981c02ac240420158a5c140c30060c2c0008100c040c000c00992458c46c000d59500c0c0000000028041e480c000400000020000004180008d8003c0c447c01ff9942000ff14d21007fca810003fd5308001fe29e4000bf19520007fea910803fe5408401ffa1e4000ff54a10005f8c908003fc5388001fea182000bd58420007fe8310002bc6448001f79944000ffd4f21007fc8610803fd4384001fea9c4200ff90d21005f8c890003ef5248401fe2a44200ff55321007f8a788003fc4388401ffa
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x674d4621004fd7695320006be6414e210067c7419510005f77154d210073f5495310004fe76d0e10007d453cc610004fc7614e20005bf7454f10005f57194d21006bc7519110005ed7214f20006dc5498c100067e6550f21006bf7519110006f75318520006bd6414c20006dc63d0d10005f771552210067d6590c10004ff7654f100067c6514d10005ed7295020004fd7615321005ee74cc820004ff7654c20006be64d0620005ee73d4b21006de6314f20006fa7018e10006be6410f210067c7399621006de63d0f200073f5495010006dd5418d200067c6550d100079d4310c210067e65953200067c6594d20006be6410d21005f674cc610005f57110f10006ee54189100067e6514f210067e6515310004ff76553210076c54d4820006bc6450d10004fe7518d20004fe7499710006de63d0c20006ee5398810005ed72d4620005f571cca10006be6454c10005ee73d4a20006be6415021006bc6414d10006de6314f10006dd63953210067e65d4c10006dd7598e21007e752d4521006fa7019610006bc6494d20005f474cc410004fe7419510005bf7454c10004fd76d4d21006dc6314d10006bf6494d20005ed7210e21007cc53cc820006ee43588100067c6594e20004fe76d0a10006de6310c10004fc7655220005f673d46210067f65d0d10004fe7419620006df5418d20004fe7498f10006ec54d8910004ff7610f210057c7550e10006f454d8520004fe7419520004fc7654620005f571d0a10006be6410c20006be6495020004fd76d0c21004fc7654a100067e6555020006dc63d4d20006f762d4610006dc3218e10006f55398420006dc6350d10006bd7599321005ef7250620006de7598f21007f270cc610006f64318520007e571cc921007cf53cca20005f57190c100067e74994200073d5415221005ed7294c20004fd7695221005f571d5210005ed7214c21004fc7610e10006bf7519120005f5718c121004fe7498c21007cf53ccb21004fd76d4f21004fd7690c20006be6495321004fe7418e10007ac54d0a200067e6590c10005f57190121007b454d0610006be6410c21006ed76d4820006de6314c20005f673d0410007e752cc521004fe7599020007ac54d0b21004fd7690f21005f571d4e210073f5495110006f571192100067f6550d100067e65952210067d7499410006dd7498f21006be6455010006ec43d8910005f571d4a10005f571d0e21006de3218e100067e65d5020006bc6490121007e65348421005f77150e21006be7599221004fc76cca10004fe7399721006de5498c10006dc7498e21006dc5498f21004fe73990210067e7399621006df7518d10004ff7650c21005f675cc4100077453d45210067d6590c20004fd7610e210067e6515021004fe7399421005f77155210006dd7498c10006df7598e21
  | 1 => 0x8e21006bf6414d10005f571d5221004fd76950210067e6595321005ed72d0f21006bd7599010006ed5458810006ef53d89100057f7550f10005bf7454d20006de634ca10005f571d4c10005ed7294121006be7319120006dc63d0e10004ff7614c21004fe7399121006f45358420005f77150c10004fd7610f10005f571d0c10006bc6495110005ed7215120006be7399321005bc7454e21005ed72d0e200077453d4610004ff7655221004fd7614e21006e562d4410006ed7218e20006dd6315321006bc6415220004ff7610e210076e53d4a20004fd76d5321006be6494c10006be6415121004ff7650c20004fe7614e200067e6515320006de63d4c21006be6490c200067d65d0e210067e65d4a10007b754d0521006f55418520006ed7299521006ec54189100067d7499721005ef7250d210067e6514c21006ef5458810006df63551100073f5495321004fd7690d210067c6594e10004fd76d0f21004fe7319110006de63d0e21004fc7655110004fe76d5110005ed72d5321005ed72d52200067d7399410004fc7650a10006de6390c100057c7550e210067e6555010004fe7498c10006de5418d100057f7550c10006de6314d21004ff7655310004fc76551200073f5495220006e562cc410005dc7355121004fe76d46200079d4310e10005f475d0610006de5498c20004fc7654d20006be6415020004fe7690d20006bd7599221006dd63d50200067e6515221006be6490c21004fe7694e100067e6554c20005ee74d4b21006bc7319110005df7355121006dc6314e100067e7499410004fd7614f100073d5415110006f75418520005ee73d09210067c65d0d10004fd76d0f20004fe7399010007d743cc610005f57114c21007d443cc521006df63d5110006f643d8520006dd63550100075d5314d21006de6390f21006dc6354d20006be64d0e21007cc43cc921006ee43d89100077654d45210067d6550e210077653d4621006bd7399020006bf7399221006dd7518d20004fe7399720006ec4318910004fe7599310005f57115021004fe76d5120006de6350e21006be64153210067e65d5010006be6450a10005f475cc521006fa7019210006de6314e21004ff7615221007ae43d0a20006bc7599321006be6450e21007cf43cc8200079d4310c20005f673d44100067e65d0f21005ef7254d21004ff7610d21005f57110f21006de6350c20004fd76d5121005bf7454e20006dc7418d10006de63d0f10007ae43d0b21004ff7615021005bf7454f210067d7319520005ee74d4a200067e6510e21004fe7399320006de63d0f21004fd7218e10007b643d0610006f653984200079d4310f20006bf7319110006dd63d5010006bf7599221006ef5358810006bc64d0d10004ff7614f200076e53d4b210057f7550d10004fe7319510005f
  | 2 => 0x6ef53189100067e6594d21007ac54d0921006bd7319110006bc6410e10004fe7399410005f475d0621007d753cc521007b754d0610007d743cc621004fd7690121006f576d4621007d443cc610006fa7018e20006dd5498c100057f7550d20005bc7454d10005ef7250c20006dc7598e21006dd6395221004fe7498f21004fe76d0620004fe76d4e10007e54348421004fd7694f10006be6410e21004fd7118e200067c6550d200067d7419520006bc6414d20005dc7355320006dd7418d10006bc6450d20006dc7598c200067c6514d20005f475cc610006bc6410d10006be64d5020004fd7610c21007cc43cc820005ed7214e210067c6510d10006bf7599321005dc7355020006de6354f210073d5415310005df7355320004fe7598f10004fe7399521006dc5418d10006ec5398810005df73550200067f74195100067e6510f21004fd7694e21006ed4398810005f57194e10005f771550100057c7550d10005ed7290e20006ee4318910006dc5498c20006ed54d89100067c6514e20006bc6490e20006df5498c10006dc7518d100073d54153210073d5415220006de5498e21005f674d4410007e74348421006de6310f20006be64d50210076c53d4b21004fc7650d20006be64153200076c53d4a20004fd7615021006be64d4f21005f77154e10004fd7614121005ec74cc921006de7498c200067d7499621006f576d0410007d453cc621006de6310c20006de63d4f210075d5314f20004fe7598f20004fd7690c21005ed7214121004ff7654f21006f55318520006de7518d10006be7599321006bd7519120006be6490d21007af54d0a20004fe7319120006be6495221005dc7355021006f762d06100067e6590e21004fd76d4c21005ee73d0820006f74358420006e66448421006ed5358810005ee75cc921005df7355021004fd76d0e21007e742d4521004fe7599221006ef54d8910006bf4099121006dc6310d10005ed72cc6200067f6510d10004fe7499621004fc76d0a10004fe7598c210067c7499721006f54358420004fe76d5220004ff7654c21006df7598c10004ff7610c10004ff76150200067e6594c20006dd5498f21004fe7418d10004fe75d8a10006de63d0d21004fd7694c100073d5415010005ec74ccb21005ef7255321006be6490f21005ef7255220007b443d0621006be64d4c20004fe7498e210057f7550f210073f5495120006de7518d20004fd768c121005f675d0521004fe7519110006be6410f200057f7550e200075d5314c21004fc7614e10006be7399010006f753d85200067c5219610005ee75d0b21004fc7650e20007af54d0b21005ee75d0a20007e45348421006de63d4c10004fe7518e10006df5498f21004fc76d4a100067c6595110005f57195121007b454d06210067e6554c10006dd549
  | 3 => 0x57190d21006bc6490e10006bc6495120004ff7650f20006be75990200067f74996210067c6590d10004ff7614c10006dd6355321005f673d0521006de6394f210057c7550f21005ee74d4921005f474cc5210067e7399721004fe7599021006ee5498810006bd6454f21006be6454f210067c6595220006f44358420007ea70d4a20006ed5418910006de7598c200057c7550e20006dd7518d10005ec75d0b21004ff7610f10005bf7454d21006be7399221006be6414c10005bc7454f210067e65d4e21004fe73990200076e54d4b21006bc6490d100076e54d4a20007ae43d0921005f675d0610007ac43d0820005f571d5010004fd7695010005bc7454e20006dd3098d210057c7550f100073d5415120006de6390c200067d6550f21007e742cc5210067c6514e10005ec75ccb21005f57195210006f571196100079d4310e21006df6395120006dd63d5321006be6454c200077454d4521006bc6410e20006bf6414d20006bc64d5220005ef7254c20007e572d0521007e65448421006dc5498e21005ee75cc820007b454d0410004fe76d4a10005f57194121006f74398420004fd7610f21006ef5418910004fd76d4f10004fd7610121006dc6314e20004fc76151200067e65552210067c6514121006dc6390d10005f674cc621004fc7650e10006bd6494f21006ee53588100067c7419520004fd7614c20006dd7418d20006be6415221006ed7219220006f576cc6210067d5099521006e75258420006de6354c100067d65d0f210076e53d4921004fe76d4e20005dc73552100067c6515110005ef7254620006f45398420005ee73d4921005f675cc521006be6455321006df7498c20006bc73990200075d5314c200067c65d0d20005ec74cc820006bd64d4c10006be6490f20006f65318520004fc7615110004fe76d4d20006de6310e210057c7550c10006dc7498f21006f543984200067e65950210067f7399420006dc6310e100067e6594c100067e65153210077453d4621007e732d4521006ed53d89100067e65d52210067c7499420006dc6394d200077654d4610006e66348421007b643d06210067d6510e21005ed7290f21005f5710c121005bc7454c10006f65458420004fc7610e20006dc630c121005ed7210d200067f73195100067d73996210067f6590d10007ac43d0921004fe7418e20006bc7519120007b443d0410006df7418d20006f554d8520006bc64d0d20005df7355210006ef4398810006be64d5321006bd64d4e21004ff7654f20006bc7399010006bc6415210006dd7598c20004ff7615121006bc6415110006bd7519110007e752d0521006be64d51210067c7319510006dc7598f21007cf53cc9210067e5219610006f553d8520006f754d85200075d5314e10006de6310f100077653d4410004fc7615210
  | 4 => 0xc610004fe76cc6200076c54d4a20007ae43d0820004ff7610c21004fe7498c20004fd7615121006dc63d0d200067d6510f21006ec4398810006bc64d5210005ee75d0921005ed72101210079d4310c10004fe7518d10005ef7255121006ed76ccb21004fe7690d10006dd5418d10007e742d0521006dc638c121007e572cc521007cc53cca200067e65d0c20004fe76d4d10006de63d4e21004fe7499521006df6315120004fd7614f21004fe7099521004ff7614e210057f7550d21006bc64d51100073f5495021005dc7355221004fe7399621006dd5498c20007af54d09210067c6510d20004fe7499421005f57114d10006f57198d21005ed7215320006be6494c20004fd7615020007d743cc410007d443cc621005ee73d4820006bd6454c10005bf7454c21004fd760c1210057c7550d20005df7355221005f475d0410004fe7098d21006f57199521005ed720c121006bc6410d20005f57115110006f57199121005ed7294e20005ed7294f21006be64d4e210067f7399721004fe7499721005f57115321007d753cc610006de3118e200067e65d4620004ff7615321006df7518d20006df5418d100067d7319510005ed72d0d21006bd64d4c20004fc7610d200077654d4621004fd76d0d210067f7319520006de63d4f10006bc7399321006de6394c10005f57110c21006e562d0410004fe75991210067c6595120007e454484210067d6590e21006df5498c20006f65498420006dc6314d20007b643d04100073f5495121004fe7615220004fd76d50200067c65d4d100075d5314e21006bc6410121006dd6355020005f673d4521006de6390e210067e73994100067f7499721006be64d5320006de63cca10006de63d4c200067e65d4f21004ff7615010004ff7654d21005ed72d5121006ed53189100067e6594f10007e44348421005f475cc621006be64d0c100067e6554a100067f6550d20006f45458420004fe75990100067f5099521006bd64d4f21006bd7399321006ee53d89100067e7319520006bc4119220006de6310d21007cf53cc820006bc64d4d10004fe7499720004fd7694f21005ed72d4e20004fc7610d10005ed72d4f21004fe7694d20006bc7319120004fd7694c20005f57194e21007d453cc410006be64550200067e6590f21007ac54d08200079d4310d10005ec75cca20006df3098d210067e6550c20006be6490e21007b754d06210077454d4610004ff7655320006bd6454e21006df7498c100067e6514c20004fd7690f20005ed72150210067d7399721005f77154e21006ed76cc820006fa7019620006be6450c100067e6554e21004fd7614c21004fd7694c21005ec75d0a20007ea70cca20006bf7599020004fd7694f20006dc63d0e20006dc63d4d10004fe7598c10005f674cc410006f653d8520005f
  | 5 => 0x6de6350f210057f7550c21004ff7654e21007e64348421005f57114f21006bf73990100067d6550c10005f77154c100077454d4621004fd7615320006bd6454c20005f57194c10006de6314f210067e7499721005f77150a10006dc7418d20006bd6494c10006ee43988100073f5495020004fe76d0d20006bc7599020005f77155121006f74318520005dc7355110004fd76d53100067c7319520006de63d0c21004fe7598f21005df73551100073f5495320004fc764ca10006be6410c10005ed7214d200067c6554d100067c7399721004fd7695121005f57114f10007cf43ccb21005ed7210c21006dc7498c20006be6455221004fc7615220006dc7498c10005ee74d4820007e75348421006de5418d20004fc7614d100067e65d0c10004fe7614d20005ed72d0c20005f474cc610005f571d4d21004fe7418d20004fd7690c10005f57115310006be6410f10004ff76153200073f5495210005ed72d5020007ea70d0a20004ff7614c20005ed7295321005bc7454f10005ed72901210067e6594f20004fe7319220006ec5358810006ed4358810006bc6454d10006be4119220006ef62d4a10006f75358420004fc7654e20006bd6414f21004fe7519220006be64d0a10006de63d4f200067c6515120006ee5318910005bf7454c20005bf7454e10006dc6310e20004fd76d0c10004fe7399221006df7418d10006de6354c200075d5314d100067e6595020004fd76d5221006f454984200067f74994200067f7499410004ff7610f20006df5498e21006be7599010006f54318520007e572d4521004fe7614d10005ee74cca200067c6555110006f45318520007b754d04100067e65d5321006de7498e21007cc53ccb21007cf43cca20005ed72d0620005f57190e100079d4310e20005f675d0621006de6314c21006bf64d4d10006dc6354d10006bc7599010004fd7610c200067d7499420006f643584200067d65d0c20004fe7610d200067e6514c10004ff7650f21004fe7399710006be6495010004ff76550200067e6555321005f571952210067e6550c10004fe76d0e200076c53d49210076e53d48200067c7499621006de63d4d210067c65d5110004fd7690e21006bd6494e21006bd73992210067e6514d21005ed72952200079d4310f10006bc6455110006e74258420004fe73195200067c6595210004fd7119220006de7598e21005ee74ccb21005bf7454f20005f673d0610005f571d0d21006be64d52210076c54d4b210067e6554620006dc6350d20006de7498c10004fe76d5210004fe76d0d100067e6594e21006be6494f21004fe73d8a10005f77150d210067f65d0d20006ec5498810006f443984200067d6550c20004fd76950200077453d4410007e571d49210067c6515220004fe7690e20006dc63d4e10005f675c
  | 6 => 0xd72d4d210067d7419510005df7355310006de634c620006bc64d5120006f576d0621006e66548421004fe75192100067c6594121007b454d0521005f57190e210067c6594d10006df7598c20004fc7655210006be6490f10006ef54988100067e6514f10006dc5418d20005f571d5121005f571d4e100067e7319510004fd76d0c20005dc7355310006df6355120006dd6315221007cc43ccb21006de63cc6200067c5119620006be6450c20006ed43d8910006de6394c200067d6510c20004fe7498f20004ff7650e21005f571d0e10005ed7290c20006be6414c20006ef43d8910005f77150e10004fe7695220004ff7614d21006bc6494d100075d5314f10004fd7614f20005f77154a10004fe75993210067d7399420006bf6454d10006f654185200073d5415320004fe7598c20006bd75990200067f73996210075d5314f21006df63d5120005dc7355010004fd7615310005ec75cc9210073d5415020007f270d4610004fc7654d10004fd72196100067e6554f21005ef7254f21005ef7254e20006df6395110006de6350c10006de6314c10007e554484210067d65d0c100057f7550e10005ec75d0921006bf73191200076e54d4921005f675cc6210067e74195100067e6510c20006f743d85200067c6590d200067e6515020006dc6394d10004fe7518e20004fd76d50100067c65d4d200067e6595010004fd76d5021004fd76d4c20005df73550100076c53d4820007e571d0921005ed7215221006dc6310d20006dd7598f21006ed76d0b21006bc64d4d20007f270d0610007b443d0521004fc7614d20006bf7399020006f57118e10004fe7099121004fd76d0f10004fd7614d21006f576d4410006df7598f21006be6415010005ee75d08200067c7499410006bc6490d20004fe7610e10006ec53d89100077654d4410006ef53988100067e65951210067e7419520006dd6395010006be4219210004fd76d4c10004fe7695210004fd7695321006e73258420007e75448421006ed7219620006f64398420006f75458420006be6415310006dd63d52210067f6510d200077653d4521006bf64d4d20006de6354e21004fe73993100067e74996210067d6590f21006ed76d0820004fe73196200073d54150210079d4310d20007e732cc521004ff7655121007d443cc4100075d5314c10006be6454e21004ff7655010005ed7290d210067c7399410004fd7695310006f543d8520005f673d46100067c6515210006f453d8520005f475cc410004fe7399321007e732d0521006ef4358810005f674d4521005ef7255020004fe76cca10004fd7615010006dd6355221004fd7610f20004ff7650f10006dd7498e21005ed7210f20006bd73990100057f7550c20005ed728c121004fe73196100057f7550f20007af54d0820004ff7615310
  | 7 => 0x88100067e51196200067f73994100077653d4610006ef62cca10006bc6454d20007d743cc521006bf7399321006be64d5310006de6310f21005dc73551200057c7550c20006bd6414c10004fd7694121004fe7598d21004fd7610c10006bf6494d10004fc7650d100067d6510c100073f5495221007d753cc410006bc7399221005ee75cca20005ee75ccb21005ec75d08200067c6554d20006dc6390d20006be75191100067c6555120005bc7454c20006f454185200067e65d4c20005ed72951210057c7550f20005df7355120004fe7499420004fd7615221006dd7498c20004fd7610d21007d753cc621005f674d4610006f762cc610006bc42192100076e54d4820006df6315110006be64d0c20007b643d0521006de7498f21006ed76d4b21006bf7599010004fc764c620006df7498f210057c7550c21006dd7598c10006ed5398810004fe74d8a10006be64d0f210079d4310f21004fd76d5320006ee54d8910005bc7454f20006be6450620006bf6454d20005f673d06210067e6515010006f55498420006be64d4c100067e6514f200067e7399420005ec75cc820007cc53cc921006ed4318910006be7399020005bf7454e21006f44318520006ed7299121004fe7499410006ec4358810006ec53189100067e65953100075d5314d200067e6594c21007d453cc521006dd6315010005f674cc5210067f6590d20006de7598c10004fe7614e10005ee73d0a20004fd7690f10006dc7518d20004fe7694e20004fe73192100075d5314e200077454d44100067e65151210067e6594f21005ec74cca20004fd7219210006bc6455120006dc7598c100057c7550d210067f74195200067e6510c10006de7418d10004fe7610d10006de6394e21005ed7294d21004fe7519120005bc7454c210067e6590c20005f474cc621004fd7694d21006de5498f21006de6310c21006ef62d0a10004ff7650d210073d5415121005f57114121006f75498420006be6494e21004fe7498d210073d5415210006bd6494c20006f75398420006f654d8520006dc63d4e20006f55358420007e55348421005ef724c620006bd6414e21005ef7250e20004fd76d4f20006ed7298d21004fd76d4e21005bc7454d20006ed5498810006fa7019220006bc7599221006be7519120005f57195010005ef7250f210067e6514e21006be6490c100067c73994200067e6550e21005f675d0410006bc6415120005ee73d0b21006be7319110006be6450f21004ff7614f10006f55458420004fe7598e210067c65d5120004fe7615210004fe7615120006be6414f21006de7418d20006de63d0c10005dc7355220004fd7614c10004fc7654e10004fe7695120005dc7355321004fe7399420005bc7454d21006ee5458810007cc43cca20004fd7119620005df7355220005e
  | 8 => 0x3ee0358600b026004000050003389a8060001a03f0241c00040001e04646000805010214008200000200980903c0a80a8010120000000105604c0182e0de0dc45006010084000080021c0178011b0000008050660004300402216c150000000e4000030180e40a8060cc0040102400c0004901400000c180000002240208604e418e002b00a014008000100b80000100200c0f0870b8004040520020083b00304a0606c0020000004700652802c01800020020038540320c0018010b002c008020060540488400a01804816006004010030340583c8020408cc000170b40000580b0440fc148000040a41480201a00839062000000108000000000000a0068980000708003003807016000008510cc008000210700000080700e09c018060bc00c2581003a0dc0000d0080281500405801c460410000501986e0940800000b014028000150000180505e0000101180095e048018010001381480802c000060ad0100bc0c8a50280040100007c0001d0060001d00100b008014018002b012c021890d0008258000200100284e014144068000280d0010320142f40001f0b60bc0080000806017812000078058850cc18c051700a407c000a10080002501c00c0a00180a01806c3a16046404416804038000138010b209d831864003a83b008600000610190000241b0010260880680001a0202080a0240f4010e002a0042b153024024150050565740183005600c2f80602408c048230008500002f0600502607500c0202880003a06c2900000a0002800c0020202380900025c0782000608c0480000010400801062060100290ec0e80f8010f00640802d01e074060070260001a8000040501010b0000000080801a0e00000307a00013843018068640350f430c0a832006dc3118e20004fc7650620006bd4099121004fe7695110004ff7614f21006f576cc410004fe7599320004ff7654c10006dd6315020005ee74cc921005ed72d4c20005bf7454d10007cf43cc921005bc7454e100067e65d0e21005f475d0521005f57110121004fe7610e20006ef4318910004fe7419610004ff7610c20006f65358420004fe76151100076c54d4921006be64d50100079d4310d21006f443d8520007b443d0610005df7355321004ff7650c10004fe7694d10006dd6395020004ff76550210057f7550e21007ac43d0b21005f57110d10005f7714ca10007ac43d0a20006bd7319120006df7498e21004fe7690e10006ec545
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa9f8650c43084011eb03bb0a6908030f5d954153210052e432a629c40008be86dd1534800147d0b210c908002a720d40991210045ec36e8a9840009ae841d732484014bf0aba4c710802b561853cc62100572c34a69084200c3c651d1534400127f0eaa0a9108021fa1f6550d100066631ae429a4000e2f5495262040015cb032a2c40800387d5363951100064ebb28621e4200cd4635c4534400165f04aa0a8100024fe1d541501000717aa4a9b122000a3c855ce648840195cc8b9686100031d99571153210043f43ccaa8c4000c9e641cd54080012dd0a3a66490803175d95314e21005c7c128621c40008dd861cd54c8401b8862b9060908021fa1b7550d200065b322e3a1c4200a3e8499754884014db0c29ea410002a7e194310c200045f420ec29c2000a3c85502644840193aeca1887108036910572901210046f418ec2a42000dc4325c630484015cb04298c290003391d162cc4100043e438caa1a4000b978150c438400147d0b324a8100030fdd274994200051fc22e632a4000cad645ca530800196cc8b88a7908033398d7290f210054e422eb3184000c3e65dd153040010f90eb2a86100028f211739941000556422a7b122000ae58690d210840187cca3a2a710803171d66350e210043e43acaa182000a5c855d2630400147d0b324a99080317dd66350c2000566c10a831a4000ae586d5121084015c90b992c210002b9a0f52584200073329ac5a882000ab78454e61080015cb02218c488003171d95314d100061eba8eb3244200a3e8499754c840187eeb3a8c888002ab21153988100062eba8ea31a2000ae582d4d610800127f0eaa0a9080023b60876152100052fc32a629e4200c9d731cc644800156f08a98c29000237a18735512000567c1aa8b102000b1c83550548840147f08b98ca88002b960643588100062fbb2a62984000ae5821506148001968c8b88a8880032799373550200056641aa8b1020008be87991538840153f06bacc9108028fe1573990100062e3a8c6a1a20008be861d153440014b90aba4c6100030f9947454f210053a42a86b084000b1c83550540400187ee93a0ca900038d55054584200070fb22a629a4000b648550d21084010fb0dbaa87908030fdd46450d200064eba0e931840008de86dcd54440010fd0dbaa86880028fa1464951100065b322e3a182000ae78614d21084018bae639ccb90803a350c43588100054fc328621c4200e1d6454c53040011790eb22a710802c720d54152200046f41eec2a042009d6831d7414840139d063ae84100021fa1c6550d200051fc2ae63224000cd5635c654884010f90f32a8608003599d752cc5210046f436e6aa24000cce635c853884014bf0ca98a6080030f1d66450f2100537c2a863122000da674d0b3148401c3ac8a98a7908022fa107614e20
  | 1 => 0xd063ae8208003a910f42584200046f41eec2a64000aaf8454f6244001c3cc8a98a7908022f21e6454c10007c221e8598a4200a9f8650c43c80018eccab8ea9108028f2117319520004f2c38a89084200cce635ca5308001c3aa82a4c608002b36087518d20005b342e85a8a42009d6831d7418840193aeca1886100021fa177610f100051fc2ae63222000a3c8655054480014bd07288cb10003a9d5342584200058e42a8621a4000ae58194d620400163906aa0a990002b520d54584200074aa1886b08400093f875505408001acceba9682908033598d7190e210067339ac5a082000c5c7518d43480013ad063ae83080027961c53484210070faa2c72a44200a3f855ce64884010fb0dbaa8710802b36087498e210045e438c8a9a40008be861d1534800153f0ca188790802cbe095415220005e3c1aa89084200c9f7418d53480015cb022a0c488002a7e194310f100070eb2a862184000a9e839086484001c3ea8b1ca9908029d21543185200046ec36e6aa04000c6d655cb430800163908a98a6908028fe1954150200073229ac5a882000c5d731cc6548001938e931aa610003e150c43484210061eba0e932c4200cd6635c443c840193cc839aa9908028f61b54950200053a42a8730840008bd861d1530400187ccbba2a6100028fe1954153100061fbacea3224000b378155054484011b90eaa0c690002f120d54484210066ab1ae32a02000c3f759d6640400195ac8b94a790803275cc7399321006d33a685a8a4200e2f5495062440018e8cab88a8880023be197215021006723aac5a082000c3d751d664040016390aa188790803275cc73990100054fc22ea31a2000ae78255161080011bd0f31a631000237e1d5498e2100572c0ea6b102000e3554152610800153906bacc810002ad60473191100072aa98a6b084000a9c844c26348401e48a9a9682908028f21573191100045f436e8a9a2000e1d54d8c54480018eacab8c86080039994f52584200058e41aa82a04000cce635c84388401c6aa82a6c290002b9a1265484210070eb2a86218200087d86dd54304001f088799682908024fe1d54153200046e43aa831a2000c6d655ca430800147d0832ea88800369105721012100537c2a86b102000c3f749d06544001e8aa629a42108022f21e6454e210054e422ea31a4000b978150c43884014b90aba4c790803275cc73191100061fbacc8a184000ae78150d620400153f0ca188608002b9a1263484210057341e84b0840008de8798d32840014bd0b188c7100021fa1e6550f210064fba4c6a982000b978150c430400196ac8b8ca7108027961f32d452100556422a63122000a3f845ce6508001d8cc7a9a4210802ab61843d0b210071aaa0a830a4000a748550f61480014790caa0a9080028f61b54953210053ac08e732e4200
  | 2 => 0x543584200052e432a629a4000c9f7650c430400178d07a966290802c72115314e100055ac30a9a0c42008bc8759153040014b90aba0c6900039995162d44100051e42ae73204000a9c8650c4388001cc8a8b16a2080039554c53984200046ec36e6aa02000e2d5415362440018beeb31a8710802c72115314e2000573c1286b084000c3c65dd15344001c3ea92a4c7908029720d7499410006e2192e21824200c5f7518d4344001878cbba2a690002c720d54153100063632ae42a240008de83dd854c400135d083ae6510002a7e117598f210059bc0aa82a42000c3e76d525448001ac8a4b8ca0908032d9917110f2100566c30879964200ad78355361480011db0c3ae64100033398d7294f210051e42ae73264200c9f7650c43080016af02a98a708003a550c43d85200054fc22ea31a4000c6e655c8538840159b043a0c69000387d525498c200072aa98a630a4000e2f5495162040014eb0c29ea31080297e195314e210045ec36e8a9e4200ad5811d46344001d8cc629a4210803171d66350c100055ac3087a082000c3f7599143c840187aea3acc990802b520d54d85200073229ea4b084000c3c75991430400187cecaa0a890002d9e1543484210061fbb2a82a6420093f87550548800147908b9cca10002b960a43584200053ac30a9a882000a9f835d664c840159b043acc7108023de197110c2100763a9e64b0840008dc87552630800193ae83a0c6880025ba1474cca200064fbb28621e4200a3f8655054040011bf0eaa4c610003271d26354f2100557c22a73102000c3d76d52540800147b0daa4a9108030f9977454e210043e43ccaa1e42008de861cd54440015cb05a1ac2100031d5957190e210046f41eec2a242008f7865c4530840155908a9ac4080027961f42d45210046fc3aa831a2000ce47558b3104001d8cc7a1a4210803d114f52cc5210063732ae42a442008dc8758d54040013cb0e21a42108030f1d954151100051fc32a82a4420087e87d95434800196ac8b8ca608003875954310e210061e328e8a9a4000ec66310d210840187ae83a4ca10002b361853cc8200062fbacc6a1e4200aad86153420800117d09bb0a7880028fa1464951200061f32ee8a9e42008df8755263c84010fd0bbb08790002b9e0553588100043f430eaa1a2000b1c8454c530840195cc8b968790802ab61843d08200058e42a8621e20008be8799153080011db05bb0a988002a7e117598c100061ebb2a82a44200b1c8550c434400171f04a188610003875505418d200072aa98a7b0a4000a3e86d5254480018bae639ccb108023d2197110d100054fc22eb31c4200c6e655cb540800147d09290cb080030f5d475990200051f42cc92a442009ce831d742c8401c3aa82a4c7108021fa1c6550d100065ab22e3a982000ad78355161080013a
  | 3 => 0x998a4200c6e655cb53c840187cedaa4a888002e3e094310f21007322a6a4b0840008dc8755263c84014bd0b190c708002c720d541511000477c32e421842008be8799141880011eb03bb0a790002b520d54185200062eb98e73282000ba48454d21084011eb0c3ae62080023721d635532100572c36869084200ea454d0961080011bb0db9aa9908038b55054189100046fc3aa831a4000ec743cc961080011eb0c3ae82080023d607761532000572c0ea8b102000a5f835d2650800127f0eaa0a9908026ba1075cc8200074aa188630a4000a3e8599254040011d90cb90a690002b361843cc8200064e3a4c6a9c4200ae68598d21084015cd0b32242108021f6187550e210061eba8ea32240008be8799142840014d90aa1cc408003b110f32584200052fc2ae931e4200c9c7650c4348001c3cc8a98a608003175d95314f210045f438c8a9a2000a5c835d265080018bceca98a6900032b1917214d200051e422a132a4200ccc635c843480011bb0c39aa9108032b9917214e210058e42a8621a4200c9f7498d53080012dd0a3a664100021fa1e6550c200053bc2a87b0a40008de87d8d5444001c3aa9b18a888003a999043484210046e43ac6aa44200c3d76d52540400147f0caa0a990802c720d54153210053ac08e932e42008be87191534800195ac8b96a610002cbe0954153210065a322e229a2000e1d5458c54c840169f04a98a7100024fe1d54153100045ec36e8a982000e1e6550c43040014b906ba0ca90002c72115314f200045f43ec8a9a4000a5f835d06548001ccca9a92c2100029b21543d8910005abc0aa62982000e1f5458e540800193ae639cc910803a99935448421006e339e65a8a42008f581dd843c80018bccbb9aa8080028f21573990100046ec36e6aa44200aaf8454c62440014bf06ba4ca08003a550c43984200070fb22a629a2000e1f5458e5404001d4c87a12c2100033598d7194e210051fc2ae73204000ad5811d663c84011eb03bb0a890802b9608431852000716aa0a93102000ad7835526108001958c8b90a890002e9a1352d05210056bc1aa830a4000a9f835d66404001878eb3228710802cde0554152210063732ae5a984000c3d751d464440016af02a98a710802c72115314e210063632ae429a4000c5e651cd54040015cb03a1ac4080023b61875d08200059bc0aa82a02000ad48355261080014b90aba4c7108033358d72d53210051fc32a82a04200ae78650d21084010fd0f32a8710802a72117598c100045f43ec8a9a2000cd4635c443440019cceab1662080033358d72953210054e4328621a2000b1c8454c53040015ab022a4c790802b9e0554588100047ac08ec2a44000a9c8650c434800187ee93a4cb108030f1d46450d100051ec36a92a02000ae78615121084014db0c2a6a4100029de1
  | 4 => 0x44800139d063ae8490802c72154310e1000556c30a9a164200c9e64dcd548840159f06aa6c4880038dd52545842000536c30a9a9642008dd861cd540800193ceca188688003275d07418d200062fbacc6a182000a6d821d0654800147908b9ccb908030f5d954150100066ab1ae3aa44200ae58114c62440011bf0eaa4c6080023d6047610e200051e422e632a2000a9e848c863840015cd0b992c2100027961f42cc5210046ec38c71824200ad58610f3104001c9aa629cc408002b320d54d891000746a1887b122000cb6645c654040015cf0c21a42108021fa177610d210056ac30a79882000c9e641cd54884018dccab9087108032b99172950200045e438c8a9a2000c5f7654c530400156908a9ec290002d3e095314c200063a32ae229a2000c9c64dcd54440014bf0aba0c6900023d21971151100054fc1aea32220008ec865c854480015ab022a0c68800327dd94310e210062eba8ea31a4000c3d76d5254c84018baeca98a608002a7a123118e200051f424cbaa02000c3c7519143480011790eb22a61000297e195314f200055ac3087a0c4200cd5635c754040018bccbb9aa8100030fdd954152210054f41c823244000ae68399121084015cb0529ac210002c72154310c2100573c12a6b08400087c879954308001938c839aa888003875505498c2000476432e421a4000cae645c8438840193cc9b9aa808002b56047498f2100536c10e632a4000cad645cb53c84014b90ca98a6880023b6087614e100054e41aea3224000a6d8614f52c840117b0e32480908024fe1d54151100051fc32a82a640008ed82dd853c40018eccab8ea6080035914572941210061fbaceb3264200a5f855d263040015cb0d2a24210803399d162cc4100062f328e6aa04000b1c835505448001c9aa629ec488003879915314e210070f32a862184000a6c8550c6244001c3ea92a0c6880022f21d6454f210076229e64b084000aaf8454d620400153908bacc790802e9a1332d05210052fc32a629842008f5811d8538800147d0b208c910002b961b53484210065b322e22a64200a9f8650c434840117b0c3a2a7908032799073550100064e3a0c6a9a2000a9c835d464440018baea3acc7908026da1075cc5210070eaa2c62a44200ae485d0961080011b90eb1aa8100029de1543984200070faa4a931c4200ea44358b41040014b906ba4cb908030f5d074997210043f430eaa1a4000ea75458b41040014b90aba0c688002a720d75993210058e422a62984000cae645c854884014ef0aa18c2900031b99572d53210073332ca69084200b4f8254c53484010fd0f32a8608002ad60475191100063b32ae229e4200c75655c74304001ac8a2b90a0908033598d7190c100070e322a629a20008be8799153c840193cc9b9aa990803c9d525448421004bb428e
  | 5 => 0x8003175cc739942000657322e52a64200ab78454d61080011db05bb0a6908026da1075cc6210054e422eb31c420093f87550544840153908ba8c688002a7e117598c200062e32ee6aa220008bc8799153080014b90ca98a70800273a0c75d0a20004b7428e99964200c3d76d525488401c3aa8b18a810002c72154310f2000477c32e429842009e587d4b31484018dacab9687908021f6187550f21004db420eb9882000e1f54950634800187eeb32287108038755163150100062e32ee6aa24000976851d331884011eb03bb0869080327dd26354e2100537c2a87b122000acd821526388401d48a8b16820800387d954310d200051fc2ae73264200c5d751d663080010fb0c3aa8608002b56047418d10006e339e65a0a4200a5f8654c53c40018b8eb31a87908032b1917210d20004d7420eb9964200aad821cc64480012ed0a3a66208003871915314d200047a432e229a2000ae78654d2108401c38caa188690002c72115314f100043ec38cb2824200a5c854c2634840193ee931aa7908038dd5254984200053642a86b102000c5c651cd54480011b90eaa4c6080030fdd46450d10005d3c22a69084200da4425c64048401c3acaa188790803d114f32d45210071baa4a830a4000ce67558b41040018dacab9487908022f61b7454e210066b31ae32982000e1d6454c53884010fd0a3b087080026da1075cc61000556c10eb3244200c9d7650c430400156b0c2a6820800237a0c7615220006b2292e22824200ccd635ca540800187cca3a2a608002c72154310c100065b322e32a442009e587d4b4148401938e831aa690002a7e0d759902000597c12a82a24200e4d5314c6244001cccca29a4210803a990d62d04100054e41aeb3202000ec75358b31040010f90f32a87108025da1474cc6100062f32ee6aa44200c5f7654c53c840193ae639cc810002b9e1954484210061ebb2a82a04000ab48454d610800187ae83a0ca900030fdd274997210052e41ae832a20008ed82dd8434840193ae83a4c608002b320d549881000746a18873102000ea66490d21084018bccbb9aa990803879954310f210046f43ec6aa24000c5e651cd54884014eb023a0ca8800317dd46350d200064f3b28621a40008bc8799153c840147d0932ea8100031b1957210d200070f32a8621c4200c3f7599143040018eacab8e87108028fe1173997210055a422a630a4000ab48454e61080016390aa188710002ab60875191200062f328e6aa642008dc87552638840193ae83a4c7908029720d50995210043e438caa1a2000aad821ce648840117b0c3a2a7108021f61b7550c200051e432a82a44000e1f6550c434400147d09288cb1000297e0d7499721007922a685a8a4200b578154c534840187eecaa0a810003275d07498e210062e3acc6a18400093f875505
  | 6 => 0x71d07e0942000004020150000a05c144f8010bc6600006020000c04700c053641205c28050030f8030245a0100c1b0000b4000240302c070a805001270040b0101d31c101bc0a00435000011580002c0206c0d00400028060051fc32a82a242008f7865c4540840196ac8b8ea7108030f5d074195100063a32ae221a2000c3f759d664080011db043b087080024fe1d54150210063b32ae3aa02000ae582d5161080015cd09992c210002b561843cc6210058e41aa82a4200087c8759543c84014eb0c2a6a3108028f21573191200062eb98e632a2000a5c835d265884014bf06ba4cb108038dd5254d85200076229ac59882000b1c8454c53440018b8eca98a6900021fa1e6554a100055bc22a7b0a40008ed861d3320800117d09bb0a790003875505418d100045f426ec2984200cce635ca43080015c909992c210002a72194310e1000476c16ec2a24200b4f8254c53c840153906bacc910802f1a0f42cc52100733328a89084200e4d5314d62040014bf0ca98a6908031719473551100051fc22e732c4200c5f7654c538840193ee831aa688002c72154310e2100666b1ae5aa04000a3e841975448001c3cc8a98a610002b9a0e65484210055ac08eb32642008dd861cd54040016390aa18861000387d53639512000753320a89084200a758614f51040010f90eb2a8710802d9a1732d452100763a1ac59882000c5d7654c53080014db0439ccb10802c72115314d20006e218ae51824200acf835526204001e4aa82a242108022f6187454c200061f328e8a984000a3e86d525444001938c9b9aa890003b110d62cc4100061eba0e932820008ed82dd843c400187eeb3acc91080387d525498c1000716aa0a8b102000c3f749d265040018eccab8ea71080297e157498c200070eb22a62984000ce67358b5104001878eb32286100036910971101210051fc22e73282000a5f8654c530800159906aa0c4880033598d7114f210052fc1ae832a2000a5e8394865840013cb0f9968290802c720d541512100572c14a8b084000b1c8355054084014df0aa1cc408003175d47598e210055ac08e73264200c76655c443c8401c38caa1886880022fa137614d2100536c10e932c4200c5d751d66304001938eca188688002b9a1742584200051e422e732c4200e8d4310c62440014bf0aba0c688002a7e0d7519120005cbc0a8621a4200b8f8250c4348401878ecaa0a890003179d95314d10006733a2c5a882000e666595121084014eb02398ca880030f9d954151100064e320e6aa2400087d861d5430800187eecaa0a8080021fa147610e200058e422a629e42008be87991530400159f06aa0c4880021fa177610c210070eaa0a931e4200a3c86550544400159b0c29e6590802b9a1352584200064e3a4c6a982000cb4645c443440011eb0c3a6620
  | 7 => 0x400c00004000040c01c0d00462008023140b0782702031018080012e0b0090b433000000040146c010140601400004171900006c01004190844f004d400c000741a0083f05c7208002d40080302c008000647101408170000a40003c9a01079018034380200001040900040210c0708c0b44c6a00001128061dc0f0940001835000930200e008010340c3200103ca01207c2940402c02004b95285d04c195b00a00002014000000000000000132e403010000081303c031306002c0775c010082f34c030bc183a0010803e0680b0100b0ec230000810c010117f03c000e0083ba8c4f4790009301002000a400003070080005b018072800000809000000180000c030001309400090301805002c2002c0220c63510570b1162d40001c0e0000501c0a1d85303c0c078190100004c03008120b40a06846174070003802c048400
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x181e7620d54151100050724d741d265040019858710f32d052100487a5883550544800192675a1352d05210040fe61751d664c840122f9855054d89100050725d54152630400123798550545842000507251751d4634400160c9550c43189100040fa5b87550544800141f9755163150200058524d54150614800141c955d07498f2100507251731ce658840185576e055314e21006075d88550c430400181d762115314e210040fe61741d2650800121c981915314d10006079d883550544800160c935505498810006079d88454c534400181f762115314c200040fa6076550544400121c989915314e2100507255741d2638840141c945cc73997210040fa5b8755054440016879150c43588100048de6154153614800121c989915314c1000487a636550c434800181d7620d54150100065161c53ccb514840103d96e1d5415020004b1a4c85d09610800160c935505458810006075d88550c43c840121e962154310d10005852515314d610800121c98551631522100507251731ce650800121c989915314c20006079d88550c43480016479654c5348421005852515314e610800189576e054310e2100607dd88454c538840181c762115314d10006135db8254c530800103f985d4759901000531a4c7558b410400141c935d074195200040fa6376550548840141c975505418d100064961c54d0b514840188d76e094310c2000487a588454c534800121c985915314c10004872616550c430400103d96e1d54152210050725d5415263c840103e98dd95415321005852515314c614800181d762115314c10005832515314d620400181c7620d5415110006075d883550548840121c989915314f21004872615458c540400162792550545842000507251731cc654400160c9454c53988100048be615415262040017049550c434842100487a636454c53440016879650c434842100507255731ce64040012a694217325842000507255741d0634800141c945d47518d2000591e455314d620400160c9550c43d8910004b1a4f86151210840185576e055314c100058524d54152610800181e762115314d200058324d54150624400103d96e1d541532100507255731cc644400181f7620d5415321006255db8150c430400181f7620d54150100048be6154151620400103e985d954152210050724d741d265884016879250c43584200040fa6176550540800103e98dd954150200040f26276550544800121c989954310c10004876588355054c840121e98d954310d1000607dd883550548840103f985d07499410004872615458c54c840103f985d074996210050724d751d6640800141c955d07498c20004876588550c43c840103d96e1d5415010004876588550c438840121d962154310c2000589e455415162040019458714f52cc521
  | 1 => 0x100607dd88550c430400121c985954310e21005c124d54151210840121f9855363151100050725d54152638840141c945d47598e2100507e5d54d8c544400103f985d0741952000487a636454c534800103f985d475191200048de6154152610800121c989954310e210050724d751d664c840141c935d4751912000507e5d5458c54c84016149550c435842000487e6154152630400160c9454c5318910006075d88550c430800122f98550541891000507255741d2630400103f985d475990200048765883550548840181c7620d5415120006075d88355054080016149550c43d852000507e5d5458c540400141c945cc7399410004876588454c530400121d962115314f2100519a547458b310400141c975505418d2000607dd883550540800181f762115314c1000607dd88550c430800121f985505418d1000507255731cc64480016149550c4318520004a9a538614d21084019258715352d0521006135db8254c53c840103f985d4759922100487e6154d8c544800121e9620d54151100048765883550540400121e962115314d100050724d741d2650800183576e0554152210050724d751d6640400103e985d9541501000487e615415263c840181f762154310e2100499a5484cc9610800121c985915314f21004872606550c434400121f985505418d200066161c43d0b314840121c981915314d20005832554310e620400141c945d47598c10006075d88454c53c840121d962115314c200048765883550540800141c935d47599221005852515314f614800141c955d07418d10004872606550c434800121c985915314c200040fa617655054c840121c989954310f2100607dd88550c43c840141f975536315120006079d88550c43440017049454c53484210040fe61751d4644400181c762115314d20005832554310d620400141c935d475191100060b5db8255054c840141f97551631522100499a578610d210840160c9355054d89100048de6154150614800161493550545842000529a507558b310400141c945cc7319520004c9e6154151210840121e962154310d2000649a1674d0b514840121c985915314e2100591e495314d610800141c955cc73993210040fe61741d0654400181d762154310e2100607dd88454c53c840141c935d074195100040fe61741d265c840103c989d954151100040fa6076550544800181c762154310d10004876588550c430400121c985954310f2100487e6154152630800181c762154310d2000487e6154152638840182d76e095415020006075d88454c53080016149355054d8520005832515314f624400121c985954310c20006235db8250c43c840141c945d47598c20005852554310e610800141c955cc73990200050725d54152630800141c935d07499721004872626550c4308
  | 2 => 0x6180004191c03010428026000070d0a0e0000000004020005020109330073000c7da2192000100304202710070300050b01000001010123000d001b1d180e660505015b110172011800011e001b00020c0001000701045c0503000c0b150939010000062121000002795f002b010028171a030040fa6376550540400121c9855163150200060d5db81550540400162796550544842100507251751d663c840181d7620d541532100507255731ce648840121d962115314e2
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 12
  | 7 => 250
  | 6 => 1407
  | 5 => 960
  | 4 => 242
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/18+packedAt gbK8 (312+(h % 18)*4) 4) % 12)
  | 7 => 2*((h/118+packedAt gbK7 (9250+(h % 118)*8) 8) % 250)
  | 6 => 2*((h/469+packedAt gbK6 (67536+(h % 469)*11) 11) % 1407)
  | 5 => 2*((h/327+packedAt gbK5 (56640+(h % 327)*10) 10) % 960)
  | 4 => 2*((h/115+packedAt gbK4 (16940+(h % 115)*8) 8) % 242)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffc1ffffffffff
  | 1 => 0x3f03ff01fc0fc0fff03ffc03ffea8a2744e73
  | 2 => 0x3ffc0ffe000fff03ffc0fffc03f30c398739c
  | 3 => 0xfc0000ffffff00003ffff000003fc0fc1f83e0
  | 4 => 0xffffffffffc0000000003fff001ffc00
  | 5 => 0xffffff000000000000000000003fffffe00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4204100a1410810420410551500030ca194a5
  | 1 => 0x23523a741a88d48eb523ae80aa9ea8a2544a52
  | 2 => 0x439e88bd4810e7a239e88f2a80af30c3186318
  | 3 => 0xe90410de7cfa41043ef3c2030337c0f41e83e0
  | 4 => 0x820820ef9f3cfbcf1041040c0c3bfd001f7c00
  | 5 => 0xf3ef3c081020820820820830303dfefbe00000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 6, 0, gbRaw),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 6, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8, 0, gbRaw),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 8, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 8, 0, gbRaw),(0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222, 5, 0, gbRaw),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 5, 0, gbRaw),(0x3030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303, 5, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_37365
namespace PEqualNP.Outside.L_meta_37365
open PEqualNP.Outside.L_meta_37365.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 3 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 14 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 3 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 14 := bs2_4_0
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
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
theorem alls4 : ∀ k ≤ 3, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
theorem alls5 : ∀ k ≤ 3, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_2_0 : Interval q2Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allq2_2 : Interval q2Atlas 2 0 2 := bq2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_0 : Interval q2Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_96 : Interval q2Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_192 : Interval q2Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_288 : Interval q2Atlas 3 288 76 := block_range (n:=76) (by decide +kernel)
theorem allq2_3 : Interval q2Atlas 3 0 364 := (concat (concat bq2_3_0 bq2_3_96) (concat bq2_3_192 bq2_3_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_0 : Interval q2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_96 : Interval q2Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_192 : Interval q2Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_288 : Interval q2Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_384 : Interval q2Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_480 : Interval q2Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_576 : Interval q2Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_672 : Interval q2Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_768 : Interval q2Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_864 : Interval q2Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_960 : Interval q2Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1056 : Interval q2Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1152 : Interval q2Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1248 : Interval q2Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_1344 : Interval q2Atlas 4 1344 79 := block_range (n:=79) (by decide +kernel)
theorem allq2_4 : Interval q2Atlas 4 0 1423 := (concat (concat (concat bq2_4_0 (concat bq2_4_96 bq2_4_192)) (concat (concat bq2_4_288 bq2_4_384) (concat bq2_4_480 bq2_4_576))) (concat (concat (concat bq2_4_672 bq2_4_768) (concat bq2_4_864 bq2_4_960)) (concat (concat bq2_4_1056 bq2_4_1152) (concat bq2_4_1248 bq2_4_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_0 : Interval q2Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_96 : Interval q2Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_192 : Interval q2Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_288 : Interval q2Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_384 : Interval q2Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_480 : Interval q2Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_576 : Interval q2Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_672 : Interval q2Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_768 : Interval q2Atlas 5 768 62 := block_range (n:=62) (by decide +kernel)
theorem allq2_5 : Interval q2Atlas 5 0 830 := (concat (concat (concat bq2_5_0 bq2_5_96) (concat bq2_5_192 bq2_5_288)) (concat (concat bq2_5_384 bq2_5_480) (concat bq2_5_576 (concat bq2_5_672 bq2_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_6_0 : Interval q2Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem allq2_6 : Interval q2Atlas 6 0 40 := bq2_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_7_0 : Interval q2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq2_7 : Interval q2Atlas 7 0 1 := bq2_7_0
theorem allq2 : ∀ k ≤ 7, ∀ i < count q2Atlas k, checkRow q2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq2_2 i (by omega) hi
  · exact allq2_3 i (by omega) hi
  · exact allq2_4 i (by omega) hi
  · exact allq2_5 i (by omega) hi
  · exact allq2_6 i (by omega) hi
  · exact allq2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_2_0 : Interval q3Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allq3_2 : Interval q3Atlas 2 0 2 := bq3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_3_0 : Interval q3Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_3_96 : Interval q3Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_3_192 : Interval q3Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_3_288 : Interval q3Atlas 3 288 76 := block_range (n:=76) (by decide +kernel)
theorem allq3_3 : Interval q3Atlas 3 0 364 := (concat (concat bq3_3_0 bq3_3_96) (concat bq3_3_192 bq3_3_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_0 : Interval q3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_96 : Interval q3Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_192 : Interval q3Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_288 : Interval q3Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_384 : Interval q3Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_480 : Interval q3Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_576 : Interval q3Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_672 : Interval q3Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_768 : Interval q3Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_864 : Interval q3Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_960 : Interval q3Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_1056 : Interval q3Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_1152 : Interval q3Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_1248 : Interval q3Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_1344 : Interval q3Atlas 4 1344 79 := block_range (n:=79) (by decide +kernel)
theorem allq3_4 : Interval q3Atlas 4 0 1423 := (concat (concat (concat bq3_4_0 (concat bq3_4_96 bq3_4_192)) (concat (concat bq3_4_288 bq3_4_384) (concat bq3_4_480 bq3_4_576))) (concat (concat (concat bq3_4_672 bq3_4_768) (concat bq3_4_864 bq3_4_960)) (concat (concat bq3_4_1056 bq3_4_1152) (concat bq3_4_1248 bq3_4_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_0 : Interval q3Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_96 : Interval q3Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_192 : Interval q3Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_288 : Interval q3Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_384 : Interval q3Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_480 : Interval q3Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_576 : Interval q3Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_672 : Interval q3Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_5_768 : Interval q3Atlas 5 768 62 := block_range (n:=62) (by decide +kernel)
theorem allq3_5 : Interval q3Atlas 5 0 830 := (concat (concat (concat bq3_5_0 bq3_5_96) (concat bq3_5_192 bq3_5_288)) (concat (concat bq3_5_384 bq3_5_480) (concat bq3_5_576 (concat bq3_5_672 bq3_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_6_0 : Interval q3Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem allq3_6 : Interval q3Atlas 6 0 40 := bq3_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_7_0 : Interval q3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq3_7 : Interval q3Atlas 7 0 1 := bq3_7_0
theorem allq3 : ∀ k ≤ 7, ∀ i < count q3Atlas k, checkRow q3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq3_2 i (by omega) hi
  · exact allq3_3 i (by omega) hi
  · exact allq3_4 i (by omega) hi
  · exact allq3_5 i (by omega) hi
  · exact allq3_6 i (by omega) hi
  · exact allq3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_2_0 : Interval q4Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allq4_2 : Interval q4Atlas 2 0 2 := bq4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_0 : Interval q4Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_96 : Interval q4Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_192 : Interval q4Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_288 : Interval q4Atlas 3 288 76 := block_range (n:=76) (by decide +kernel)
theorem allq4_3 : Interval q4Atlas 3 0 364 := (concat (concat bq4_3_0 bq4_3_96) (concat bq4_3_192 bq4_3_288))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_0 : Interval q4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_96 : Interval q4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_192 : Interval q4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_288 : Interval q4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_384 : Interval q4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_480 : Interval q4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_576 : Interval q4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_672 : Interval q4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_768 : Interval q4Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_864 : Interval q4Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_960 : Interval q4Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_1056 : Interval q4Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_1152 : Interval q4Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_1248 : Interval q4Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_1344 : Interval q4Atlas 4 1344 79 := block_range (n:=79) (by decide +kernel)
theorem allq4_4 : Interval q4Atlas 4 0 1423 := (concat (concat (concat bq4_4_0 (concat bq4_4_96 bq4_4_192)) (concat (concat bq4_4_288 bq4_4_384) (concat bq4_4_480 bq4_4_576))) (concat (concat (concat bq4_4_672 bq4_4_768) (concat bq4_4_864 bq4_4_960)) (concat (concat bq4_4_1056 bq4_4_1152) (concat bq4_4_1248 bq4_4_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_0 : Interval q4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_96 : Interval q4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_192 : Interval q4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_288 : Interval q4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_384 : Interval q4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_480 : Interval q4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_576 : Interval q4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_672 : Interval q4Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_768 : Interval q4Atlas 5 768 62 := block_range (n:=62) (by decide +kernel)
theorem allq4_5 : Interval q4Atlas 5 0 830 := (concat (concat (concat bq4_5_0 bq4_5_96) (concat bq4_5_192 bq4_5_288)) (concat (concat bq4_5_384 bq4_5_480) (concat bq4_5_576 (concat bq4_5_672 bq4_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_6_0 : Interval q4Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem allq4_6 : Interval q4Atlas 6 0 40 := bq4_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_7_0 : Interval q4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq4_7 : Interval q4Atlas 7 0 1 := bq4_7_0
theorem allq4 : ∀ k ≤ 7, ∀ i < count q4Atlas k, checkRow q4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq4_2 i (by omega) hi
  · exact allq4_3 i (by omega) hi
  · exact allq4_4 i (by omega) hi
  · exact allq4_5 i (by omega) hi
  · exact allq4_6 i (by omega) hi
  · exact allq4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_2_0 : Interval q5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq5_2 : Interval q5Atlas 2 0 3 := bq5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_3_0 : Interval q5Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq5_3 : Interval q5Atlas 3 0 6 := bq5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_4_0 : Interval q5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq5_4 : Interval q5Atlas 4 0 1 := bq5_4_0
theorem allq5 : ∀ k ≤ 4, ∀ i < count q5Atlas k, checkRow q5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq5_2 i (by omega) hi
  · exact allq5_3 i (by omega) hi
  · exact allq5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_2_0 : Interval q6Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq6_2 : Interval q6Atlas 2 0 3 := bq6_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_3_0 : Interval q6Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq6_3 : Interval q6Atlas 3 0 6 := bq6_3_0
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
theorem bq7_2_0 : Interval q7Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq7_2 : Interval q7Atlas 2 0 3 := bq7_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 6 := bq7_3_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 50 := block_range (n:=50) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 242 := (concat bgb_4_0 (concat bgb_4_96 bgb_4_192))
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
theorem bgb_5_672 : Interval gbAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 960 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864))))
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
theorem bgb_6_960 : Interval gbAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 63 := block_range (n:=63) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1407 := (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat (concat bgb_6_672 bgb_6_768) (concat bgb_6_864 bgb_6_960)) (concat (concat bgb_6_1056 bgb_6_1152) (concat bgb_6_1248 bgb_6_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 58 := block_range (n:=58) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 250 := (concat bgb_7_0 (concat bgb_7_96 bgb_7_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 12 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 60, 62),(inputs.getD 2 zero, 58, 62),(inputs.getD 3 zero, 54, 62),(inputs.getD 4 zero, 46, 62),(inputs.getD 5 zero, 30, 62)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq2 (cert : Complete q2Atlas) : Lower true (roots q2Atlas) (target q2Atlas) 8 := by
  have ready : Ready q2Atlas (asRow q2Pos) (asRow q2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq3 (cert : Complete q3Atlas) : Lower true (roots q3Atlas) (target q3Atlas) 8 := by
  have ready : Ready q3Atlas (asRow q3Pos) (asRow q3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq4 (cert : Complete q4Atlas) : Lower true (roots q4Atlas) (target q4Atlas) 8 := by
  have ready : Ready q4Atlas (asRow q4Pos) (asRow q4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq5 (cert : Complete q5Atlas) : Lower true (roots q5Atlas) (target q5Atlas) 5 := by
  have ready : Ready q5Atlas (asRow q5Pos) (asRow q5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 0, 4),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 5 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 0, 2),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 5 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8eaaaaaa8aaa8a8a8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq2 : Complete q2Atlas) (certq3 : Complete q3Atlas) (certq4 : Complete q4Atlas) (certq5 : Complete q5Atlas) (certq6 : Complete q6Atlas) (certq7 : Complete q7Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 : Sig) 6 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 6 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : Sig) 8 :=
    slice_correct (ms:=fixRows 0 8) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq2 certq2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : Sig) 8 :=
    slice_correct (ms:=fixRows 0 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq3 certq3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000 : Sig) 8 :=
    slice_correct (ms:=fixRows 0 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq4 certq4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222 : Sig) 5 :=
    slice_correct (ms:=fixRows 2 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq5 certq5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a : Sig) 5 :=
    slice_correct (ms:=fixRows 4 1) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0x3030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303030303 : Sig) 5 :=
    slice_correct (ms:=fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3937053352 * 2 ^ 32 + 2863179944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37365.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[4,5]⟩,⟨.and,[1,6]⟩,⟨.and,[2,3]⟩,⟨.and,[8,9]⟩,⟨.or,[1,2]⟩,⟨.or,[0,10]⟩,⟨.or,[3,6]⟩,⟨.and,[7,13]⟩,⟨.or,[11,14]⟩,⟨.and,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937053352 * 2 ^ 32 + 2863179944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937053352 * 2 ^ 32 + 2863179944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37365

open PEqualNP.Outside.L_meta_37365 in
theorem PEqualNP.Outside.L_meta_37365 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937053352 * 2 ^ 32 + 2863179944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937053352 * 2 ^ 32 + 2863179944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq2 allq3 allq4 allq5 allq6 allq7 allgb)
