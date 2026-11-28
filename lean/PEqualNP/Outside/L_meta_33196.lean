import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_33196.Model
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

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
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
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


end PEqualNP.Outside.L_meta_33196.Model

namespace PEqualNP.Outside.L_meta_33196
open PEqualNP.Outside.L_meta_33196.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 7, 7, 7].getD j 0

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

def checkRow (g : Atlas) (k i : Nat) : Bool :=
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

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_33196

namespace PEqualNP.Outside.L_meta_33196
open PEqualNP.Outside.L_meta_33196.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2024d801a00e862a000004a6022a220519c562121718145003c09480405940f064d31f3284022005090e009c58734043000184180081048241ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xac000050000000008cd000003944610c0098000044000000000000000000012c0001100159409ce8288904a81c00740000000000000000b40000f03000a4a0bd68912964dd093820d448714c0001202c84015c18000000000011253400000080153c000954540000000401600000ecd8b0003c01147950c4000000f4c840c0fcf834006ccc000000e4005cb80c0064004c009400005800687c0119480000000000011c0024000000e000010130000406000004060000040008141800100206000000080a08020204040c1d5d5490ebca521dbd4943b6292879f5450f9ea4a1d714943e6292874c5250ebca621d794f42aea9e859d43d0abea6a15714d42cea1a855e5310abaa6215d94442baa88857a5010af2a02157d5232aeaa4655e528ca7ca8194f55032bb2886575510caf4a0195e54032afaa0659e540cabaa81967550328eaa0655e520cb9ca41973d0832e621065d6510cbaaa2197694032eca80655e53d06baa7a0ded4141bc282835e53106baa620db94841b6a90837a50106f2a020db94a31b6a9463cc32c86f4a190de54321af29c435d53886bea690d714d21e6192435e53d02baa7a05dd4540ba28a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a9461cc32c82eca3905d54720af29c415d53882bea6905714d20e6192413e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1ac00418b80a267a4a9400000a02c00000000400001280e19c3000000085a20800000020020050b466114943d15845250f4a6014943d25805250e8c6250f4287596540cb0c6255032c3553420ca4d6510832b1584420cac96010832c5552510cb155454432c6552500cb195454032d4545500ca4c6254f41a359032c87483254321a3590324864c6254f40a359032c83443254720a359032483315444010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x9040000c0001905856014943a0ae2312a81950970189540ca84ba064a8643415d03254720
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2697+((h/30+packedAt s0K4 (2457+(h % 30)*8) 8) % 176)*8) 8
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s0K2 (249+((h/1+packedAt s0K2 (245+(h % 1)*4) 4) % 12)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x8fe1e3f1fc3c7fe38e3e3870ff1c0ffe34333f
  | 2 => 0xf1fe03fe3fc07ffc0fc7c07f0fe00ffec8cc3f
  | 3 => 0x1fffc003fff871ff007ff800ffff1c10f0fcc
  | 4 => 0xfe0000003ffff81ffff800000ffffe01f00ff0
  | 5 => 0xffffffffc000001ffffffffff0000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc42484a205809201820a09106504a254141315
  | 2 => 0x284849404819240c044442260a2144a8484c2a
  | 3 => 0x2484406490883024900693022348610c0d054c
  | 4 => 0x481993892330465b2e90040ccc938831f00ab0
  | 5 => 0x1110200022240924921244880020001a2a000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffcfffcffc0c0c0fffcfffcffc0c0c0fffcfffcffc0c0c0fffcfffcffc0c0c0fffcfffcffc0c0c0fffcfffcffc0c0c0fffcfffcffc0c0c0fffcfffcffc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_33196
namespace PEqualNP.Outside.L_meta_33196
open PEqualNP.Outside.L_meta_33196.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x80000540000a2c0006e0002f00000003c240230039d80000000000000030000000420000008640004894394560000000d40005a00000000001240000006600000000001b22d94000001300000188d000002c00b8500024dc860000000008801a0000000703148000000000000000003ce9c64a8c1f0000b0800d1d27045c0000000030000103000005000002000000020204000000010201bd286877950d0eeca321dd54643b7a92876c5250ebca6215754c42bb28885755110af4a0215e540429f2a0653d540caeca2195d54432bd2806579500cabca620d754c41b7290836d52106f4a020de540419f2a6633d54cc6dca518db54a31bda826378504c6f4a190de54321af29c435d538867ea890cf15121af29e815d53d02dca5205b54a40bba8a8174515027ca8184f55030b7290616d520c2eca2185d54430bb28e417551c827ca9104f55220afa9a415c534827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 60
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (731+((h/13+packedAt s1K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s1K4 (1780+((h/20+packedAt s1K4 (1620+(h % 20)*8) 8) % 151)*7) 7
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3f838f8f1f1fff8e38fc707071c1fffe36427f
  | 2 => 0xc7fc0fffe01f1ff03f1f807ffe01c1fec87c4f
  | 3 => 0x7fff00fffe01c7fc01fff807ffe01c10f8f8c
  | 4 => 0xf800000fffffe07fffe000007ffffe01f00ff0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10a81111482a10061034151410445464164215
  | 2 => 0xa1112602064428300908822362188898481c4a
  | 3 => 0x9209032442064092400d2301348c050c0a868c
  | 4 => 0x20524c4894100968aa40080a49312811e00960
  | 5 => 0x46208009898924d34924c4c00203021b56000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffafff0ffaaa0a0fffafff0ffaaa0a0fffafff0ffaaa0a0fffafff0ffaaa0a0fffafff0ffaaa0a0fffafff0ffaaa0a0fffafff0ffaaa0a0fffafff0ffaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_33196
namespace PEqualNP.Outside.L_meta_33196
open PEqualNP.Outside.L_meta_33196.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x78289745520000d8026540cd8052eda00625c000000000a70009801ecd79600a05803e8c0003400cb06e0000000188005c94000005102756c8688223838172482355ab00183a0002138300024400003820400382040808728100800204210bd286877950d0eeca321dd54643b7a92876c5250ebca6215754c42bb28885755110af4a0215e540429f2a0653d540caeca2195d54432bd2806579500cabca620d754c41b7290836d52106f4a020de540419f2a6633d54cc6dca518db54a31bda826378504c6f4a190de54321af29c435d538867ea890cf15121af29e815d53d02dca5205b54a40bba8a8174515027ca8184f55030b7290616d520c2eca2185d54430bb28e417551c827ca9104f55220afa9a415c534827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 60
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (718+((h/13+packedAt s2K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s2K4 (1760+((h/20+packedAt s2K4 (1620+(h % 20)*7) 7) % 88)*7) 7
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3f838f8f1f1fff8e38fc707071c1fffe36427f
  | 1 => 0xc7fc0fffe01f1ff03f1f807ffe01c1fec87c4f
  | 3 => 0x7fff00fffe01c7fc01fff807ffe01c10f8f8c
  | 4 => 0xf800000fffffe07fffe000007ffffe01f00ff0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10a81111482a10061034151410445464164215
  | 1 => 0xa1112602064428300908822362188898481c4a
  | 3 => 0x9209032442064092400d2301348c050c0a868c
  | 4 => 0x20524c4894100968aa40080a49312811e00960
  | 5 => 0x46208009898924d34924c4c00203021b56000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffeeffccffaa8888ffeeffccffaa8888ffeeffccffaa8888ffeeffccffaa8888ffeeffccffaa8888ffeeffccffaa8888ffeeffccffaa8888ffeeffccffaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_33196
namespace PEqualNP.Outside.L_meta_33196
open PEqualNP.Outside.L_meta_33196.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xf546800822a06a7382c0801400118266cb2c1288ea000bc61e20009004a143955a011833e38c9452015a6421170000900170c1400030062c5004187705005ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x340c001066436848503a218d884153480042002b0049230038c8000027800343d3b94c0067408c4140000000067e42800bc761703400003d0cc00580d8807c4c2802cfa78288b0e85d370004a6c33000286f398009a84358fc965f38988f26015148266a00104ca7b0108c884538170180e12154e440030706a801321cc23b001186e114302400683f8e052632d16c3c00410880039028bc782b0c8102e000012800000009cae54001d4b27c168748e080b0001e480807c9c01130d01000a0c0604010329002c0c000017181c010300010b051b010908020000000d03110105010501060301bd286877950d0ebca7215754e42af298855d5310aeca2215d54442bd28085795010abaa3995794332aea9c65cf524cabea2995714132af298655e53906baa720d794c41aea98836e52106daa420de94041bca80835d52cc6bca198d754e31afa9263d7514c6b8a098d794c31af29e435d53c86bca710d754e219faa2433c54486bca690d754d219f2a0433d54086bca610d754c21f2908437a50086f2a010d794f40aea9e819e53d033aa7a067ccb40ce996819f31d033a63a04f55240afa9a815c535033ea6a06714d40cf992819d325033e62a0674c540dda82813e541037281984f952309eaa4619e548c33aa9185754a30aea8c615e508c33e811867502309f2a0613d540c2dca4185b54830bb2886175510c37280186795030ceaa061ce520c2baa4187354830a6a9061d6510c2baa2187554430aaa88615e500c3b4a01867d0030ed200619d400c3b280186650030af29e415d53c839a65904f952209eaa4415f53882b8a7106e50220afa9a415c534839a64906e501209f2a0413d54082bca6105754c20bb288417551082bca7885754f10ea98e213e548427aa90857d4e10ae29c21b940842bea6885714d10ea98a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x98f2e60223583520036bc707440000016958a0005829e5000f9400b410a18680113a04029069c02b00a84102a9802e3200321380048000c000024020001d0408100000c1000014e8495584504ca4d62141318e58054486586054d21c955121087612154021a61813250298604c540a698f50503295250030cc545400c30e5454830c3551520c3455294430c5951510c3155454430d1949510c3455254430a6592500c21d65d0030c354b400c31551d0030a6592400c3495290030d4546400c21f6550030c3549400c3155150030d2549400c3515150030a6d95400c31b6550030e2949400c3195250030e2549400c3095250030e4945400c3195150030e4545400c311515003095584538831853502209319532483185350120e24c9404824d6214e10c614d4084254654c510c614d40443913150110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x314e01050400c6a1245c4604c940912e430262a070152945400c381292a2a0061c05495150030a22e229a8110508754c94048284b90a6a0421441d53150110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (864+((h/16+packedAt s3K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s3K4 (4032+((h/45+packedAt s3K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s3K3 (2012+((h/16+packedAt s3K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s3K2 (453+((h/3+packedAt s3K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1e3f838e3cfffe3f1c71e3870c7ffe3f0e43cf
  | 1 => 0x1fc7fc0fff0f1fc7e07e3c07ff8e0fc7307d33
  | 2 => 0xe007fff03ff01ff8ff803ff80ff00ff8c38e3c
  | 4 => 0xfff800003fffe000ffffc0000ffff000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8300a01044441040082060a140128224064045
  | 1 => 0x44110824082024082012040224842482101512
  | 2 => 0xa21100900248014480091009204910408a28
  | 4 => 0x48b05b4d22aa0c92f5548050ae496192f80f80
  | 5 => 0x9104620802cc91249a693264c0018024af6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefefcfceaeae8e8fefefcfceaeae8e8fefefcfceaeae8e8fefefcfceaeae8e8fefefcfceaeae8e8fefefcfceaeae8e8fefefcfceaeae8e8fefefcfceaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_33196
namespace PEqualNP.Outside.L_meta_33196
open PEqualNP.Outside.L_meta_33196.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2c0600aa74a31419420001a56257800018800409968f0200c003c70b024638894106c6ae544d100482ce8a0e48f8452000052e00024e0cd30d1032c20c0002ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fa40fd40f940fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x6d1aa0cfa86008a400003b9c8fc613196876711b000cc191709c905b078a0d41a380f4f41c1b988001d2f154ce0000100ae69360283600001e446820f040d613290fc005d42130700000094b02f000443e06280c0482a04801000009194044e3c1ec000300000ea00001fc420020800724a2f9d8c843370c47c264392478342293c405c0c0501c0537958844d020acd0151981c00222205c74000594d0a162891c64002a00000000612cb200230b00008069f0e6603a2045a04060408020019010a001700000a29011201070102040800040c2e04060600010d0203000d03000000030b0902bd286877950d0ebaa5a1d754743ed28687d950d0ebca721db94843b6a9087765110eeaa221de94043bca80875e5410f3ca821f394843aea9087cd5210e9aa421f594443aea8887d55110eaaa221f694043eca80877a50d0af2a1a15794e42aea9c855f5350ab8a6a15794c42aea9885765110aeaa2215e94042bca80855e54ccab8a9995754732aea9c655e544cab8a89973d4932e721265cd424cabea2995794c32bd286837950d06bca720d754e41afa9a835c53506bca620d754c41b7290836d52106f4a020de54041af2a6635c54cc6baa598d754e31af2a2635c544c6bea498f5d4531eb20a63d5414c6bca618d794f21aea9e435e53886baa710d794d21aea9a437b50486f0a090cf950219eaa0435e53086baa610f948421bd2804379500873887a05794e40aea9c817954903b4a7207654e40eda1c81d843903b66520764ca40ed98c81d931902bea6a05714d40ce21a81bb54503b6a6a07614d40eda1a81ba435037086a07610d40cc21a81bb425037284a076cc940ec99281bb415037282a076cc540ec98a817a501027ca9184f55230af29e415d53c827ca8104f55020af298415d53082eca2105d54420af29e215d53c427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x30f01005518a605132f345842b003c028009c58000000000c4000000100170e60fa93a0071c00b5600404d29254b8005420000062652031a08009008888036001812300080800000080141400aa65825410f455294443d19495110f455254443d254a5010f515194043d25495010f5151540439558454cca55611513293195424ca4d621533193588544c65465505318719153486396414121c955121087612154021a358843d02956110f40b258843902d16110e40a358843502956110d40a698f545025a65d0d40a698e43502a96210d40ac584435025a6510d40b258843502d16110d40a6994435031a6510d40e298843502996210d40e258843502896210d40e498443502996110d40e458443502916110d40a618d425029864cc940a61913250389424c940a618d415029864cc540a61913150391414c540
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc41150708000180001a058a6110d40d04c4b0886a0681625844350248b88c999281245c4644c940910eca1264a0489721933150244b90c898a81241d9414c540
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (864+((h/16+packedAt s4K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s4K4 (4032+((h/45+packedAt s4K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf0e3c38e3cffe3f38e38238e38ff8ff3243cf
  | 1 => 0xff03fc0fff1ffc7c0fc03c0fff1ff0f407cf3
  | 2 => 0xf0003fff03fe3ff8ff0003ff03fe3ff0838f3c
  | 3 => 0xffffc00003ffc000fffffc0003ffc000fc0fc0
  | 5 => 0xfffffffffc000000fffffffffc000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa1a046114469244028a0ca0c308248aa324145
  | 1 => 0x42048882808408084044104049109204401492
  | 2 => 0x491120090090019100209202242440808a28
  | 3 => 0x646c01b4d2249c92da6938020bc90666d40fc0
  | 5 => 0x888022000009212424924324900000882b6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfffcfffce8e8e8e8fffcfffce8e8e8e8fffcfffce8e8e8e8fffcfffce8e8e8e8fffcfffce8e8e8e8fffcfffce8e8e8e8fffcfffce8e8e8e8fffcfffce8e8e8e8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_33196
namespace PEqualNP.Outside.L_meta_33196
open PEqualNP.Outside.L_meta_33196.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x40785811e9c010060038c0058000267c00034341064a5c9282a10a2948a8e0936010910a215a314991000074c8e3004001708000104a000087ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x4e274a240c4c000017183b4623594d032000420043513900223413094f002f323c1b191c290731003f0840332d0b2c2b0a550e3749145641215250105a2a571e3e001d12153d041644353638301145480253000654001f581a013a280f0005264b0000000d0000472e000000002503000001d06841000410d812c4c08a56bc0880204005140000c555d50d0ebca721db94843b6a9087765110eeaa221de94043bca80875e5410f3ca821f394843e6a9087d65110faaa221f694043aea8087d95010eb2a021e710f42bb28e857551d0abca7215754e42afa9a855c5350b3886a14f952329eaa4659c43d06dca5a0db54b41af29c835d53906bea6a0d714d41ce21a833e548c67aa918cf950219eaa0435e53086baa610f948421bd280437950086bca7205754e40ce21c815f53502b8a6a05794c40aea98819c43102dca4205b54840bb288817551102bca9985715330aea9c613f544c278a89867d5130af2a2615c544c338a8984715130eda8261da404c3b280985794c30af29c415d53882eea2905d145209f2a0413d54082bca6105754c20bb288417551082bca7085754e10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x41a10648e91600001400ab9820001e02c800a0298002a00c03000001c88400300000103455254443d29495010f495254043d49455010f515154043a658043d0b144354742a65804350a996010f41c310d52d06996010d41d848550086996010e40c310d5210314435444087992544c30e6215130c3588544c3166115130c5584544c3196015130c6152404c258655013087191538821c6454e10
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x100048c01445c04354742a12e021aa5a0e0562584544c304b12c02a261845856015130
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2667+((h/30+packedAt s5K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s5K3 (998+((h/8+packedAt s5K3 (950+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s5K2 (249+((h/1+packedAt s5K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf8f1fffc3ffc7e1c71c0c7ffc7fc1fe10f3cf
  | 1 => 0xf00fe1e3fc7ff8fe07e00f8e1f8ffe1e634cf3
  | 2 => 0xffe03ff8fff1ff8000ff01ff1ffe1838f3c
  | 3 => 0xfff00003fff0001ffffff0001ffe0001fc0fc0
  | 4 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x20110440480088004104201244124044101145
  | 1 => 0x52250849145010a0621448488849418614492
  | 2 => 0xca448909222a00358802892111212981828a28
  | 3 => 0x6300ccd209239246d348e0005e480cccb40fc0
  | 4 => 0x8c081100324c249924930e49800031114be000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8ffeae8e8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_33196
namespace PEqualNP.Outside.L_meta_33196
open PEqualNP.Outside.L_meta_33196.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x26001ff1013000ffe6098013fb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ffc813000ffc4098007fc204c003ff8826001ff8413000ff82098003ff65480017fb2a400eff99520035fcca90003fd65480017eb2a400eff19520035f8ca90003ff64480017fb22400dff9912002dfcc890003fd64480017eb22400dff1912002df8c89003bff544801bff2a24000ff5512006ff8a890003ff63480017fb1a400cff98d20025fcc690003fd63480017eb1a400cff18d20025f8c69003bff5348019ff29a4000ff54d20067f8a690037ff4348019ff21a4000ff50d20067f88690006ff6248007ffa924003ff9492001ffaa49000ffc5248007ffa124003ff9092001fdc849000ffd4248001f6a124003ff1092001ffe649000ffe3248007fe9924003ff0c920007fec290002ff6148017ff30a4002bf98520007fac29002ffc61480057e30a400effd452005ffca290003fd5148017fe28a400dffd052005ffc8290003fd4148017fe20a400cffcc52005ffc6290003fd3148017fe18a4003ffc852001fde429000ffe2148007fe90a4000fb4852001ff84290006ff6048003ffa824001ff9412000ff4a090007fd5048001fca824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe409000ffb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824000ffd9510005feca8802bfe654400d7f32a2000ff59510005faca8802bfc654400d7e32a2000ffd9110005fec888027fe644400b7f3222000ff59110005fac888027fc644400b7e322200affd511004ffca888003fd5444013fe2a22000ffd8d10005fec688023fe63440097f31a2000ff58d10005fac688023fc63440097e31a200affd4d10047fca688003fd5344011fe29a2009ffd0d10047fc8688003fd4344011fe21a2000ffd8910005fec48801ffe62440077f3122000ff58910005fac48801ffc62440077e312200affd491003ffca488003fd524400ffe2922009ffd091003ffc8488003fd424400ffe2122008ffcc91003ffc6488003fd324400ffe1922001bfd8510017fea28800bfe5144005fea8a2002ff14510017fe828800bfe4144005fb20a2002ff50510007ea828800bfc4144005ff98a2002ff8c510017fa628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001fe9411000ffaa088003f95044003fe2822001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd3154031fe18aa019ffc85500c7fc42a8003fd2154031fe10aa001bfd815000ffea0a801bfb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001ffd01500bff680a8007fe4054003fe202a001fe1015000ffe60a8007fe3054003fd182a001ff0c15000ffe40a8007fe2054003fd102a001ff0815000ffe20a8007fe1054003fd082a001ff04150007fecaa0002ff655002dff32a8006bf99540007facaa0002fd655002dfe32a8006bf1954000dfec8a0017ff545000bff2a28005ff5514002ff8a8a0003ff63500017fb1a8015ff98d40025fcc6a0003fd635002bfe31a8004bf18d400b7fea6a0057fe5350001fea9a8015ff14d4002ffe86a0017fe435000bfea1a8005ff10d40007fec4a0002ff6250029ff3128003bf98940007fac4a0053fc62500077e3128016ffd49400a7fca4a0003fd5250029fe2928005ffd094002f7e84a0017fe425000bfea128000ef5094002ff884a0057ff3250029ff1928000ff4c9400a7f864a0003ff61500017fb0a8013ff98540015fcc2a0003fd6150027fe30a8002bf185400b7fea2a004ffe5150001fea8a8013ff1454002ffe82a0017bf415000bff20a8005ff505400077a82a0017fc415002bff98a8013ff8c540007fa62a004ffc3150029ff90a8013ff88540007fa42a004ffc21500037fb028001ffd414000ffca0a0007fd5050003fe2828001ffd014002ff680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ff460a0007fc3050003ff9028001ff8814000ff840a0007ff1050003ff0828001ff04140007feca98002ff654c025ff32a6006bf99530007faca98002fd654c025fe32a6006bf19530007fec898002ff644c001dfb226000afd913008ffcc898016fe644c001feb226000bf5913008ff8c898016fc644c001de3226005af19130097fea898047fe544c001feaa26011ff1513000dfec698013ff534c025efa9a6004ff94d30027faa698013fc534c009ee29a6004ffd0d30027fc8698013de434c009fea1a6000f750d30027f88698003ff624c0017fb126010ff9893001dfcc498003fd624c021fe3126003bf18930097fea498043fe524c001fea926010ff1493008ffe8498043fe424c001fea126010ff10930027fe6498013df324c009ff1926004ff4c930007ba6498013fc324c001ffb0a6000bfd853007ffcc29800afe614c001feb0a600fff18530015f8c29804bff514c01fff28a6000ff5453007ff8a298047ff414c01fff20a6000ff5053007ff88298013ff314c009ef98a6004ff8c530027fa6298003dd314c009fe18a6010ffc853007ffc4298003fd214c01ffe10a6001bfd813000ffea098007fe504c003fd2826001ff54130007f2a098007fc504c003ffa026001ff9013000ff48098007fd404c001fca
  | 2 => 0x31027fe6498813df324c409ff1926204ff4c931007ba6498813fc324c4057fb0a6202ffd4531017fca29880bf6514c405fea8a6200fd54531017f8a29880bff414c405ff20a6202fd90531017fa8298803f5414c405fe20a6202ffcc531027ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff90a6202ff88531017f84298803ff604c4017fb02621fff9813100dfcc098803fd604c43ffe3026201bf18131117fea09887ffe504c43ffe2826221ffd01310fffc809887ffc404c409ff9826204f7cc131027fc6098813fc304c441ff902621fff881310fff8409880bff104c405ff0826202ff04131007feca90802ff654843dff32a4206bf99521007faca90802fd654843dfe32a4206bf19521007fec890802ff644843bff3224205bf99121007fac890802fd644843bfe3224205bf191210f7fea890877fe5448401feaa2421dff15121007fec690802ff6348439ff31a4204bf98d21007fac690802fd6348439fe31a4204bf18d210f7fea690873fe5348401fea9a421cff14d210effe8690873fe4348401fea1a421cff10d21015fec49080fff5248407ff2924203fb9492101ffaa490803ed5248407fe2924203ffd092101ffc849080ffd4248407fe2124203ffcc92101ffc649080ffd3248407fe1924202bfd8521017fea29080bfe5148405fb28a4202ff54521007eaa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017fa629080bfc3148405ff90a4203fdc8521017fc429080bee2148405fe10a4202fb08521017e8429080be42148401ffb024200bfd81210dffcc090806fe6048401feb02421bff1812100df8c09087bff5048437ff282421bff141210effe809086ffe4048437fe202421cffcc1210dffc609086ffc3048407ff9024203fbc812101ffc409080ffc2048405ff8824202fdc4121017fc209080bfc10484037fb2aa000ffd9150005fec8a805ffe645400b7f322a000ff591500bff8c8a8016fc645400dffaa2a006dfd5150037fca8a801bfd5454001beaa2a006ff15150007fec6a8002ff6354035ff31aa004bf98d50007fac6a806bfc63540097e31aa006ffd4d50037fca6a806b7e535400dfea9aa006ff14d50036f8a6a805fff4354035ff21aa000ff50d500d7f886a8003ff62540017fb12a019ff9895001dfcc4a8003fd6254033fe312a003bf18950037fea4a801b7f525400dff292a006ff54950006faa4a801bfc525402fffa12a019ff90950007fa84a8067fc4254035ff992a019ff8c950007fa64a8067fc3254001ffb0aa000bfd85500c7fcc2a800afe6154001feb0aa018ff18550015f8c2a801bff515400dbfa8aa006ff94550037faa2a80037d515400dfe28aa017ffd05500c7fc82a8003fd4154031fe20aa01affcc5500c7fc62a800
  | 3 => 0xfb1aa200bfd8d5114ffcc6a8812fe6354401feb1aa229ff18d51025f8c6a881bff535440dff29aa206ff54d51037f8a6a88abff4354453ff21aa200ff50d5114ff886a8803ff62544017fb12a228ff9895101dfcc4a8803fd6254451fe312a203bf18951037fea4a881b7f525440dff292a206ff54951006faa4a881bfc5254455ffa12a228ff90951007fa84a88a3fc4254453ff992a228ff8c951007fa64a88a3fc32544057fb0aa202ffd4551037eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405ffa0aa202ff90551017f882a880bff3154405ff18aa202fd8c551017f862a880bff2154405ff10aa202fd88551017f842a8803ff60544017fb02a227ff9815100dfcc0a8803fd605444ffe302a201bf18151037fea0a881b7f505440dff282a206ff14151157fe80a889ffe405444ffe202a229ffcc15113ffc60a889ffc3054451ff902a227ff8815113ff840a880bff1054405ff082a202ff04151007fecaa0802ff655044dff32a8206bf99541007facaa0802fd655044dfe32a8206bf19541015fec8a0817ff545040bff2a28205ef9514102ffaa8a0803bd545040bfe2a28200ffd8d41005fec6a0897fe63504097f31a8200ff58d4112ff8c6a0812fc635044dffa9a8225ff94d41007faa6a0897fc535040bffa1a8205ff90d4112f7c86a0817fd435040bfe21a8205ef10d41007fec4a0802ff6250449ff3128203bf98941007fac4a0893fc62504077e3128226ffd4941127fca4a0803fd5250449fe2928205ffd094102f7e84a0817fe425040bfea128200ef5094102ff884a0897ff3250449ff1928200ff4c941127f864a080aff6150405ffa8a8202ff94541017faa2a080bfc5150405ffa0a8205fdd0541017fc82a080bbe4150405fe20a8202ef10541017e882a080bff3150405ff18a8202fd8c541017f862a080bff2150405ff10a8202ff08541007fec0a0802ff6050447ff3028201bf98141007fac0a088ffc60504037e3028226ffd414111ffca0a088ffc505040bffa028205efd014102ffc80a0817fc405044bff9828223ff8c14111ff860a0893ff2050447ff1028223ff08141017fe20a080bf71050405ff0828202ff04141007feca98802ff654c445ff32a6206bf99531007faca98802fd654c445fe32a6206bf19531007fec898802ff644c443ff3226205bf99131007fac898802fd644c443fe3226205bf19131117fea898887fe544c401feaa26221ff15131015fec698813ff534c409ff29a6204f794d31027faa698803dd534c409fe29a6204ffd0d3110fbe8698813fe434c409fea1a6204ff10d31027b88698803ff624c4017fb126220ff9893101dfcc498803fd624c441fe3126203bf18931117fea498883fe524c401fea926220ff1493110ffe8498883fe424c401fea126220ff109
  | 4 => 0xcffe60548037f302a400ff5815219ff8c0a9006fc605480dffa82a406dfd4152037fca0a901bfc505486dffa02a433ff9015219ff880a90d7ff3054867ff182a433ff0c15201ffe40a900ffe2054807fe102a434ffc415219ffc20a90cffc1054801ffb2a8400bfd9542197fccaa101afe6550801feb2a8400bf59542197f8caa101afc65508077fb228405ffd514202ffca8a1017be545080bfeaa28400ef5514202ff8a8a1003ff63508017fb1a8431ff98d42025fcc6a1003fd6350863fe31a8404bf18d42197fea6a10c7fe5350801fea9a8431ff14d4202ffe86a1017fe4350863df21a8405ff50d4202ff886a1017bc43508077fb128403ffd494201ffca4a100ffd5250807fe2928403ffd094202fde84a100ffe4250807df2128403ff1094201f7884a100fec4250807ff9928403ff8c94201fdc64a100ffc3250801ffb0a8400bfd8542187fcc2a100afe6150801feb0a8430ff18542015f8c2a10cbff5150861ff28a8430ff1454202ffe82a1017bf415080bff20a8405ff1054218ffe62a10c3fe3150861fe18a8403ffc854201ffc42a100ffc2150801ffb028400bfd814217ffcc0a1006fe6050801feb02842fff1814200df8c0a10cbff505085fff282842fff1414202ffe80a1017bf405080bff2028405ff1014218ffe60a10bffe305085ffe1828403ffc814201fde40a100ffe2050807fe1028430ffc414217ffc20a10bffc1050801ffb2a6400bfd9532177fcca9901afe654c801feb2a6400bf59532177f8ca9901afc654c801ffb226400bfd913216ffcc899016fe644c801feb226400bf5913216ff8c899016fc644c85dffaa2642dff95132007faa8990b7fc544c8077fb1a6404ffd4d32027fca699013de534c809fea9a6400f754d32027f8a699013ff434c85befa1a6404ff90d32027fa8699013fc434c809ee21a6403bfd893201ffea49900ffe524c807f72926403ff54932007daa49900ffc524c807ffa126403ff9093201fdc849900ffd424c801f6a126403ff1093201ffe6499013ef324c807ff1926403f78c93201ff8649900fdc324c807f61926400ffd8532005fec2990b3fe614c8057f30a6400ff58532167f8c29900afc614c85dffa8a642cff94532167f8a2990b7ff414c859ff20a642cff10532027fe6299013df314c809ff18a6404ff0c53201ffe429900ffe214c807fe10a6400ffd8132005fec0990affe604c8037f3026400ff5813215ff8c099006fc604c85dffa82642bff9413215ff8a0990b7ff404c857ff202642bff10132027fe6099013df304c809ff1826404ff0c13201ffe409900ffe204c807fe102642cffc413215ffc20990affc104c8057fb2aa200ffd9151005fec8a88abfe645440b7f322a200ff59151157f8c8a8816fc645440dffaa2a206ff95151037faa8a881bfc5454401f
  | 5 => 0x5153037f8a8a9812ff6354c09ffa9aa606f7d4d53027fca6a98137e5354c09fe29aa604df14d53027b8a6a9813ff4354c09ff21aa604ff10d53007fec4a9802ff6254c7bff312a603bf98953007fac4a98f7fc6254c077e312a606ffd4953037fca4a981bfc5254c7dffa12a63dff909531eff884a9813ff3254c09ef992a604ff8c953027f864a9803ff6154c017fb0aa63cff98553015fcc2a9803fd6154c79fe30aa602bf18553037fea2a981bfe5154c0dfe28aa63effd05531e7fc82a98f3fc4154c09ff98aa604f7cc553027fc62a9813fc3154c7bff90aa63cff885531e7f842a9803ff6054c017fb02a63bff9815300dfcc0a9803fd6054c77fe302a601bf18153037fea0a981bfe5054c0dfe282a63effd01531dffc80a98effc4054c09ff982a604ff8c153027f860a98f7ff2054c77ff102a63bff081531e7fe20a98effe1054c77fe082a600ffd9543005fecaa18ebfe6550c0d7f32a8600ff59543005facaa18ebfc6550c0d7e32a8604bfd914302ffea8a1817fe5450c0bdf2a28605ff551430077aa8a1817fc5450c097fb1a8604ffd4d43027fca6a1813fd5350c09fe29a8604ffd0d4302fbe86a1813fe4350c09df21a8604ff10d430277886a1813dc4350c01ffb128600bfd89431cffcc4a180efe6250c01feb128639ff1894301df8c4a18ebff5250c73ff2928639ff1494302ffe84a1817fe4250c0bfe2128604ffcc943027fc64a1813fc3250c01ffb0a8600bfd85431c7fcc2a180afe6150c01feb0a8638ff18543015f8c2a18ebff5150c71ff28a8638ff1454302ffe82a1817fe4150c0bfe20a8604ffcc543027fc62a1813fc3150c73ff90a8638ff885431c7f842a1803ff6050c017fb028637ff9814300dfcc0a1803fd6050c6ffe3028601bf181431d7fea0a18dffe5050c6ffe2828605ffd014302ffc80a1817fc4050c09ff9828604f7cc143027fc60a1813fc3050c73ff9028637ff881431bff840a18e3ff1050c6fff0828637ff0414301dfecaa9003ff64548017fb22a436ff9915202dfcc8a9003fd645486dfe322a405bf19152037fea8a901bfe545480dfeaa2a406ff15152007fec6a9002ff635486bff31aa404bf98d52007fac6a90d7fc63548097e31aa406ffd4d52037fca6a901bfd535480dfe29aa436ffd0d521affc86a9003fd435486bfe21aa403bfd895201ffea4a901bef5254807ff292a403df9495201ff8a4a900f7c5254807f6292a403ffd095201ffc84a900ffc4254807ff992a403ff8c95201fdc64a900ffc3254801ffb0aa400bfd85521a7fcc2a900afe6154801feb0aa434ff18552015f8c2a901bff515480dbfa8aa406ff94552037f8a2a90dbff4154869ff20aa434ff105521affe62a90d3fe3154869fe18aa403ffc855201fde42a900ffe2154807fe10aa400ffd8152005fec0a9
  | 6 => 0x301605c028030020081700001605000830000120000030020900000500004c0000000000c0e8020120000380800000c02800020000048090000080180c01403c03800000030060000060040581200a0100100c0000380501802802c0c0130000880000000a0100000002204c000030b20201300c0060080000700800c1e003000000028050000e80080f04800000800000020000070060080600c02e0000080703001000002000020008e3000004000010060181400100600001009032008030000000000180900000c0700000002c05803004048008380080800600000206c008080000080207f0160040000400605c010010000000280301a0180281c04000002003004014000020020d40000301a0083f02402a008008000000081480400c0080980b008014000060d006c0e00000c01c08800004038038010080000700501203800828008010078000140240e015004000128080600180b00000001402000000008080020080000482200800000007034058020040120240380101800c03814002080000040360241800900a00004804006004008330080340001604012c0a0370180000780000207803005000000058090180bc04000062020008000000180480001c00000810004018038020020081400000804c008740100040280000002400004010000070050020000500100003c21800032000020120000040480e01605c060020020000d0000180040300200001409006004024088020200100680300600401816ff655500b7fb22a805ffd51540377ea8aa017fe545500bbf2a2a805ff1515402ef8a8aa017bc5455001ffb1aa800bfd8d54007bec6aa002df6355085ff31aa804bf98d54007fac6aa10bfc63550097e31aa800f718d54025b8c6aa01bff535500dbfa9aa806ff94d54037f8a6aa017ff435500bdfa1aa805ff90d5402ff886aa003ff62550017fb12a841ff9895401dfcc4aa003fd6255083fe312a803bf18954037fea4aa01bfe525500dfe292a805ffd095402f7e84aa017fe425500bfe212a842ffcc95420ffc64aa107fc3255001ffb0aa800bfd8554207fcc2aa00afe6155001feb0aa840ff18554015f8c2aa01bff515500dff28aa806ff1455402ffe82aa017bf415500bff20aa805ff10554217fe62aa103fe3155081fe18aa841ffc8554207fc42aa103fc2155001ffb02a800bfd81541fffcc0aa006fe6055001feb02a83fff1815400df8c0aa01bff505500dbfa82a806ff94154037f8a0aa017ff405500bff202a83fef9015402ff880aa017bc4055085ff982a83fff8c1541fff860aa107ff205507fff102a83fff08154207fe20aa0fffe105507ffe082a804bfd9553007fec8a9802ff6454c7dff322a605bf99153007fac8a98fbfc6454c0b7e322a606ffd5153036fea8a981bfe5454c0dfeaa2a600df5
  | 7 => 0x4f03615a0e00080000001308000f50000000002751a7a7f0000000140002c70819bf000000222a85aad80004b80e8391ae9dd169ac58000eb9dc0cf1bc0549c52c62bb0000388001331a70fe1898e302b2000002bd1830f0a6188e03f9d31bd00000029c8000002a499400000026c0002809a50129610000e50000001b19db14f82d8001a19ab13419fa848af2731869130001d7aa80ba9bb2721b80b9238a628000098000001cf03b0002bf0000000000000dc0e08002878000000001191432bb80007a80022e1a21509c99e58b8a5aa6f00000018b0001d424a18480028186911d19d29a0950b588ba3a000135aa9a7a96e1de1951758000dd8002608a98002558240000000a30f7000141804166000257277000000229952800059a6d1af8d79960c30fc800000277a92aae80028b20105ca520518000469e2a0c8d180008f8d20bb20b01527b2bdaa00000f2ab1a9421a80012700000000000009c2540e8a4b00027392787227885080022a0d880000011c8000f380016f02780018780386e04e91b8000000000000000001979740d394282280000020700000000026300024c0000000df0000e40422989691930e123980011b000237a93000000282a7e0001be14a0ef2131e083129110d161a531189c903c92529e1c70fb20d2a38858000000f909480000000012300000025e0000de025091140887235099aba80025d036a798000cc89a9440ab8ada4d92580005a17e17616c95180b80000000000000f8a600024205d1e400027111d9889e38d50088001bd9c885321600023fa158001a38000002b80520002079bf8bd14b1b207707ca109ea8930298001b8ac103e97f9a98679d895307e05127c9fa1818840000218f314e2271f997813601c182ac3a4294d01f0a82358e2a430c218e8768a4916ab913b1a696407484e2c2a319cd17b8262589718019ec89229e800042a83ab097c0b6ac20b080009b14cac90cc00017021800000000005898b9f798ca2788e80000001d90f08780010d9492660a89e18f00689118000d5958a762922b68538888000df8002ab065a4381717223202baac8aa1928001079ad0e60bc8011510f18d02c80ee8a18d91d100015d06989680000001a96586aa8f1021ac1f921200014e8c09c18f8a999d28808110da22480000000e0002b40729af1d92152b30cb82aa9f8d718000000002f2081221669ab8000fc1090001e69cb06d1520af9ea14705f8f48002791a908c1559b0119a9d9d180000000000004509e8030b1ab9aa080003200780b00801404816010114030000020d0118b800603000002006000318000000100080203a000000020000d000800000070040040160380e800002000008110000040601000400c208260001043400e00800c0201302e0000080000c03c0900700004410000000000010
  | 8 => 0x29ad96d03e1e105f1b290b2c02290002bc8001f680000000b1128a5a44818941039aa79a813c0002280002340000ae95e83a28305b1609de89f80000f1d584f85693493890b82583a95b99e1070402490b200022d9d70f10c003b8002470de9e4962a14955211a59a069892678e58471a128701d2c9a06135185a639e5077a6c94b9a624a93925b04d2241098e780009b80006380019c23492a0000c59ba8001c600019e8002a9070a7c06505e2880001219ef10a0bd8c29368000000ca80017500018a80023e00000019a23094380002a0a712a8efa0095a93d1a2a5696a8460370002c320b98fa8a9f282200000000098c0000000048a418d25a1bc9dc96520f80000014228c00000007388f11419683d0000ee1e62a518a1631970001d21aaa8d0002548000002508000000f82899b49df12019a92f10308287c0c716c011a8e9870308eb00a26519b22ea5785b8ba0ea04aa12937a0926f9faa3cabfa2099811e1e80c39c114986092fa8217a85704dab3aa71779ee8ed2b495f115aa40e9922a4c8758ca00000024d00000d29192da5b9cc1da0bb80292d1f62b5a329562600e729d0642690909ce2959bb84c0d423f25108c9cc824aba1709a31b90000000db1f09e70b10c8800000047816a4e89e1d80050f58199068f9a0ea6e90e1c08c6abe9850ec037a0c2ab8000b800007b1f20b78cd9b30a91ee21380013100000001e8559990940ab1448681c212e240a6e2238c789900009da9707d16489a20597680000013198400011c27281020512e9d5097ac41c308a2582afa0d9339dfa7184b0001be954178a4992396393a23817385c2371b509f06120aa3010102305823a9fb982286217a02a0a21987607ba9f24024f83f2c19f12cb1cb91e8300292a8a04ab11b399c9500021c492b14607d8b523b0bc0158a011127d27a03c1db8dd15792904c9fe9771171fd15f8cd20406e9711b79fb0989102640f79a581795812b9a42440c507f883a6a2aaa410529f00bea0387821d87111a8891371958d61d6a45103a53a1d2ac2b009390ea1f19222a81f82e98127ba419280319862948590e68a217283508d86a102aa316728a17b06b80d8c48338731a01d008816b24618f22c8160f429a8be0109b117daad10c03814d800259247a0e0540d99f31d3a4b9d48d083323c1b608b05513a89606c1679591242a586d8212ca24683490ca680120b48e82b790a85e9da87a04996b8802a118e0e1aa191f124a202171689988d2abe14f000026a4802c265a5528000a82d0502b600005d9f50ad092aa680699f091aa614795b29619084480623b8418000db8001322210000000ff80026b0b30002840792a280021694c0c40fe81a0fda5c2708239dd8b60f218d8071911b99301aca88a9500c8001f710594007000000013d8000001b70002901730002
  | 9 => 0x25286ca4e06283411626212c1cea26a610d4a3e9fd8d80000001261cda741e99ec11f9b6800000000126820000000000000000000168005ac4a3601e03d8000fd2102019ae12c80028ca3910f8000aa93f00000006616a29800025f00000c00019180000022ba96a1b86faa20b002fa0312095381382897921b0ea8fa8ce8270799381c79f3ab288229ba2b1a89e88408a38f60001c026ba0f1f18a69ed9c3857a8d8079d98cb1749c401800027e80025d8001ca28fa3d28691490415d84f0ac2699c809d1e22850ec8970c9139a9900015718390184923128ba74a7f8b98000ce1569ca8000e21ed29c22f117ac69fc9c58fba5e8a09fe19da811eb8a100016d84395c21f97a0632c088986020214aaae0430b70bf8001468c12978000001181998000e90a786f0000000000da8002331298958000000dc9ba115268ac89e78130a2800066a938560fa0002111fc13e06b1108000000ae00008d0000001621cf8830329ff2759b596e959abc0850d693b87f02e0208f6a1a22c1c69f81548191600480c822f99b8cfaca80026702c8e488629b266a5028e1f42339f895e0359d627691209c8001e00411f48aca6d87e84a09805a9081aa208ac7a5c904aaa1b08b41450ed8d117e8848148bf17d2700000090001eb13f9052221e322d1008619328719a09210a52af0811809f5a2887411a225148078ab8a45a51a1eab204426a97cab721916fa781089938751902218e3848a1e0c613c88aa099ef8b289026486498817995ca3da5f8001b4106000289218a258d32368001ff81c8868c1800000113a1401ba908ff1a4a261e9000248a7d8672b514593e9949d080000000021c900045a231488c98280000620b38002c5000128a1c01b25617f1c
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf71d8910014fe71d891000cfd71d8910014fc71d8910246ef21d8910246ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910236fa50d8910236ef20d8910236ed20d891001cff765891003eec625891022df7715891023dfb7058910004ff7558910034fe7558910034fc7558910004ff745891002cfe745891002cfc7458910004ff7358910024fe7358910024fc7358910234ff7258910006ef725891022cff7158910006f771589100dcff7058910006fb70589100defa5058910004ff7654910004fe7654910004fd7654910004fc76549100367e65549100067d655491000dfa7054910004ff7650910004fe7650910004fd7650910004fc765091002ebe6450910006bd6450910015f67150910004ff764c910004fe764c910004fd764c910004fc764c910026de634c910006dd634c910006ef624c91001eec624c91000df4765051002ef4765051000cf47650510015f77450510017b77450510007b7645051002ef6645051002ef4645051004fb4645051004fb65450510007b55450510006f76350510006f56350510227b6435051004fb44350510005f7725051004fb74250510007b54250510007f3705051000df6705051000df4705051011ff07050510016f76050510017f3605051011ff2505051011fb7405051011fb5405051011ff2205051000df4764851001ef4764851000cf47648510006f76548510006f56548510005f77448510005f57448510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851001ee4624851003fe65248510007e55248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100dff250485100dfe720485100dff220485100dfe52048510015f87654110036f87654110014f8765411000dfb755411000f7b75541100077b6554110036fa6554110036f865541100577865541100befa64541100bef864541100577b5454110007795454110006fb6354110006f9635411021f7a5354110057785354110005fb7254110006fb6254110006f962541100577b5254110007795254110007f37154110015fa7154110015f871541100c7f0715411000efb615411000ff361541100c77b51541100c77951541100c7f24154110007f141541100c7f22154110007f12154110015f8764811001ef87648110014f87648110005fb7548110005f97548110006fb6548110006f9654811000dfb724811000feb7248110007eb624811001efa624811001ef8624811003fe8624811003fea4248110007e94248110007f37148110015fa7148110015f8714811005ff0714811000efb614811000ff3614811005ff24148110007f1414811005feb214811005ff2214811005fe9214811003ff12148110007e12148110
  | 1 => 0x95102a67f51d95102a67d51d95102a6f621d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102967f50d95102967d50d9510296fa20d9510034ff76595100567c6559510005ef725951003dec725951028df7715951029dfb7059510294ff75595100067f7559510004ff745951002cfe745951002cfc7459510004ff7359510024fe7359510024fc7359510004ff7259510006ef7259510004ef725951001cfe725951001cfc7259510006ec725951001cec72595100567f525951028cff7159510006f771595100c6f6215951013cff7059510006fb705951013efa205951002cfe76d911004ebe64d9110034fe75d9110004fd75d9110034fc75d911011cfd74d911004ebe54d9110024fe73d9110004fd73d9110024fc73d9110006be43d911004ebc43d911001cfe72d9110004fd72d911001cfc72d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110286bf41d9110286bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110276bf40d9110276bd40d911002cff765911004ebc645911026df7715911027dfb7059110004ff7559110034fe7559110034fc7559110274ff7459110006bf7459110004ff7359110024fe7359110024fc7359110004ff725911001cfe725911001cfc725911004ebf425911026cff7159110006f7715911011cff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc7655110006bf645511002ebc6455110005df7355110045dc7355110024fe76d8d10046de63d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d1001cfe72d8d10004fd72d8d1001cfc72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10266f641d8d10266df31d8d10266dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10256fa50d8d10256df30d8d10256dd30d8d10024ff7658d10005bf7458d1004dbc7458d10046dc6358d1024df77158d1025dfb7058d10004ff7558d10034fe7558d10034fc7558d10004ff7458d10006bf7458d10004bf7458d1002cfe7458d1002cfc7458d10006bc7458d1002cbc7458d10254ff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d10046df3258d1024cff7158d10006f77158d1007ef64158d100fcff7058d10006fb7058d100fefa5058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1001cfe76d891003eee62d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d8910006ef52d891003eec52d891003eee32d891000cf
  | 2 => 0x4bf7458d2002cfe7458d2002cfc7458d20006bc7458d2002cbc7458d202d4ff7358d20006df7358d202ccff7258d20006ef7258d20086ee4258d20004ff7158d20014fe7158d20014fc7158d20066df3158d2015cff7058d20006fb7058d2015efa5058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2000dec765092002eec765092000cec765092001def745092001faf7450920007af645092002eee645092002eec645092006fac645092006fae5450920007ad5450920006ef6350920006ed63509202c7ae435092006fac4350920005ef715092006faf4150920007eb705092000dee705092000dec705092017fe8705092001eef605092001feb605092017fea505092017faf405092017fad405092017fea1050920014fe76d852005ef661d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d8520006f751d852005ef451d852005ef631d852005ef621d85202bef521d852000cfe70d852001cfd70d852000cfc70d852022efa50d852022ef710d852005ef461585202b5fb7058520004ff7654520004fe7654520004fc76545200367e65545200067d655452000dfa7054520004ff7650520004fe7650520004fc765052002ebe6450520006bd645052001dee7250520007ad4250520004ff764c520004fe764c520004fc764c520026de634c520006dd634c520006f7614c520016f4614c52000dec7648520016ec764852000cec7648520006ef6548520006ed6548520005ef7448520005ed744852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe46148520016e4614852005fe65148520007e55148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200dfea50485200dfe710485200dfea104852001df87654120036f8765412001cf8765412000dfb755412000f7b75541200077b6554120036fa6554120036f865541200777865541200befa64541200bef864541200777b5454120007795454120006fb6354120006f963541202af7a5354120077785354120007eb725412001dfa725412001df872541200cfe8725412000efb625412000feb62541200cf7b52541200cf7952541200cfea4254120007e94254120005fb7154120006fb61541200777b51541200077951541200cfeb2154120007e92154120034fe76d95100567e65d951013cfd75d951002cfe74d9510004fd74d951002cfc74d9510024fe73d9510004fd73d9510024fc73d951001cfe72d9510004fd72d951001cfc72d951000cff71d9510014fe71d951000cfd71d9510014fc71d
  | 3 => 0xb3154130007d93154130025f8765013002ef87650130024f87650130005fb7550130005f9755013000dfb745013000fbb7450130007bb645013002efa645013002ef8645013008fb86450130007db7350130025fa7350130025f873501300afd8735013000efb635013000fdb635013032fdb53501300afd853501300afda435013008fd9435013008fbb4250130007b942501300afdb3250130007d9325013008fbb4150130007b941501300afdb3150130007d93150130034fe76d95200767e65d952019cfd75d952002cfe74d9520004fd74d952002cfc74d9520024fe73d9520004fd73d9520024fc73d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203267f52d95203267d52d9520014fe71d9520004fd71d9520014fc71d9520326ef21d952001cff70d952001cfd70d95203167f50d95203167d50d9520316fa10d9520034ff76595200767c655952030def7259520005f7715952005df4715952031dfb7059520314ff75595200067f7559520004ff745952002cfe745952002cfc7459520004ff7359520024fe7359520024fc735952030cff7259520006ef7259520004ff7159520006f77159520004f77159520014fe7159520014fc7159520006f47159520014f471595200767f51595200ceef215952019cff7059520006fb705952019efa105952002cfe76d912006ebe64d9120034fe75d9120004fd75d9120034fc75d912017cfd74d912006ebe54d9120024fe73d9120004fd73d9120024fc73d9120006be43d912006ebc43d912000cff72d912001cfe72d912000cfd72d912001cfc72d9120306bf42d9120306bd42d9120014fe71d9120004fd71d9120014fc71d912001cff70d912001cfd70d91202f6bf40d91202f6bd40d912002cff765912006ebc64591202edef72591202fdfb7059120004ff7559120034fe7559120034fc75591202f4ff7459120006bf7459120004ff7359120024fe7359120024fc73591202ecff7259120006ef7259120004ff7159120014fe7159120014fc715912006ebf415912017cff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc7655120006bf645512002ebc6455120005df7355120065dc7355120024fe76d8d20066de63d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202e6ee42d8d202e6df32d8d202e6dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d2001cff70d8d2001cfd70d8d202d6fa50d8d202d6df30d8d202d6dd30d8d20024ff7658d20005bf7458d2006dbc7458d20066dc6358d202cdef7258d202ddfb7058d20004ff7558d20034fe7558d20034fc7558d20004ff7458d20006bf7458d20
  | 4 => 0x4930006bf64549301b6bc6454930005df7354930025dc7354930004ff7650930004fe7650930004fc7650930006bf645093002ebc6450930025de735093018f9e435093001eee625093000ddc764c93001edc764c93000cdc764c930095de754c930095dc754c930006df654c930006dd654c930005df744c930005dd744c9300079f644c93016ede644c93016edc644c9300079c644c93016e9c644c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c930087ce524c930007cd524c930087ce424c930007cd424c930005df714c930007db704c93000dde704c93000ddc704c93015fd8704c930026df604c930027db604c93015fda504c93015fda404c930014fe76d8530006bf64d8530006bc64d853007ef661d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d853033edf32d8530006dd32d853007ef631d853033ef531d8530024fd70d853024efa50d853024ef710d8530005bf745853008dbc7458530006bf6458530006bc645853007ef46158530335fb7058530004ff7654530004fe7654530004fc7654530006bf6454530156bc6454530005df7354530025dc7354530004ff7650530004fe7650530004fc7650530006bf645053002ebc6450530025de735053012f9e4350530016f6615053000ddc764c530016dc764c53000cdc764c530095de754c530095dc754c530006df654c530006dd654c530005df744c530005dd744c5300079f644c53010ede644c53010edc644c5300079c644c53010e9c644c530005df724c530006df624c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6514c530007d5514c53007fd6414c530007d5414c530007db704c53000dde704c53000ddc704c5300ffd8704c530026df604c530027db604c5300ffda504c5300ffda404c530004ff7648530004fe7648530004fc7648530006bf64485300eebc6448530025de7348530005dd734853007fe42148530005fb704853000df87048530025f87654130036f87654130024f8765413000dfb755413000f7b75541300077b6554130036fa6554130036f86554130097786554130005fb7454130007bb64541300befa64541300bef86454130007b864541300beb864541300977b5454130007795454130007db7354130025fa7354130025f873541300d7d8735413000efb635413000fdb6354130097db53541300d77a53541300d77853541300d7d853541300d75853541300d7da4354130007d94354130006fb62541300977b52541300077952541300d7db3254130007d93254130006fb61541300977b51541300077951541300d7d
  | 5 => 0x6bd75d9130006bc75d9130366bf73d913037ebe73d9130366bd73d9130366bc73d913037ebf53d913037ebe53d913037ebd53d913037ebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bc52d913037ebf32d913037ebe32d913037ebd32d913037ebc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bc51d913037ebf31d913037ebe31d913037ebd31d913037ebc31d9130006bf21d9130006be21d9130006bc21d9130366bf70d9130366be70d9130366bd70d9130366bc70d9130366bf50d9130366be50d9130366bd50d9130366bc50d9130366bf30d9130366be30d9130366bc30d9130366bf20d9130366be20d9130366bd20d9130366bc20d9130366bf10d9130366be10d9130366bd10d9130366bc10d913002cff765913008ebc645913036ddf7359130375fb7059130004ff7559130034fe7559130034fc7559130364ff7459130006bf745913036cff7359130006df7359130004ff725913001cfe725913001cfc7259130004ff7159130014fe7159130014fc71591301bcff7059130006fb7059130365be761913008ebe7619130364be761913008f3e751913008f3d7519130006bf6519130006be6519130006bd6519130006bc651913035f9e73191303579d7319130356bf63191300079f531913035f9c531913008fae721913008fad7219130006be6219130006bc621913035f9f321913008fb6711913008fb57119130006be6119130006bc611913035f9f3119130357ba701913035fb97019130356bf6019130357ba501913035fbb30191303579e30191303579c3019130357b83019130004ff7655130004fe7655130004fd7655130004fc76551300367e65551300067d6555130006bf645513002ebc6455130005df7355130025dc73551300975f535513000dfa70551301ffba405513000ddc7650d3002edc7650d3000cdc7650d30095de7550d30095dc7550d30025df7450d300279f7450d300079f6450d3002ede6450d3002edc6450d3008f9c6450d3008f9e5450d300079d5450d30005df7250d30005df7150d30007db7050d3000dde7050d3000ddc7050d301bfd87050d30026df6050d30027db6050d301bfda5050d301bfda4050d3001cfe76d8930006bf64d8930006bc64d8930086ee62d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930086ee32d893034eed32d8930014fe71d8930004fd71d8930014fc71d893034edf31d8930024fd70d89302cefa50d89302ceef20d8930005bf745893008dbc7458930006bf6458930006bc6458930086ec6258930345fb7058930004ff7654930004fe7654930004fc765
  | 6 => 0xc73d854001cfe72d8540004fd72d854001cfc72d85403aebf42d8540006bd42d854009ef641d85403aef541d854002cfd70d854026ef710d854009ef461585403a5fb7058540004ff7654540004fe7654540004fc765454000dbc7650540016bc765054000cbc7650540006bf6550540006bd655054012ebe635054012ebc6350540005bf7250540006bf625054002dbf715054002fb77150540007b76150540016be6150540016bc615054009fb4615054009fb63150540007bb705054000dbe705054000dbc705054011fb8705054002ebf605054002fbb605054011fba305054011fb71050540004ff764c540004fe764c540004fc764c540006df634c540026dc634c540007b5414c540004ff7648540004fe7648540004fc764854002dbe7448540005bd744854009fe42148540034fe76d95300967e65d9530025de73d953000ddd73d95300975f53d95301dcfd75d953002cfe74d9530004fd74d953002cfc74d953000cff73d9530024fe73d953000cfd73d953038edd73d953000cdd73d9530024fc73d953039e7f53d9530096df53d953039e7d53d953039edc53d953001cfe72d9530004fd72d953001cfc72d953039edf32d9530014fe71d9530004fd71d9530014fc71d953039edf31d9530024ff70d9530024fd70d953038e7f50d953038e7d50d9530034ff76595300967c6559530005bf745953008dbc7459530385df73595300d75c5359530395fb705953038cff75595300067f7559530004ff7459530006bf7459530004bf745953002cfe745953002cfc7459530006bc745953002cbc74595300967f5459530384ff7359530006df7359530096df53595300d67e53595300d67c53595300d6dc5359530004ff725953001cfe725953001cfc72595300d6df3259530004ff7159530014fe7159530014fc71595300d6df31595301dcff7059530006fb705953002cfe76d913008ebe64d9130034fe75d9130004fd75d9130034fc75d91301bcfd74d9130006bf54d913008ebe54d913008ebc54d913000cff73d9130024fe73d913000cfd73d9130024fc73d913037ebf43d913037ebd43d913001cfe72d9130004fd72d913001cfc72d913008ebf42d9130006be42d913008ebc42d9130014fe71d9130004fd71d9130014fc71d913008ebf41d9130006be41d913008ebc41d9130024ff70d9130024fd70d9130366bf40d9130366bd40d9130355be76d913002cbe76d9130006bf65d9130006be65d9130006bd65d9130006bc65d91303679f73d91303679c73d91300079f53d913037f9c53d9130006be62d9130006bc62d913037f9f32d9130006be61d9130006bc61d913037f9f31d913037fbb70d9130367b870d9130367ba50d913037fbb30d91303679e30d91303679c30d9130367b830d9130006bf75d9130006be75d9130
  | 7 => 0x55000df870505500bfbb4050550004ff764c550004fe764c550004fc764c5500057f754c5500357c754c550026de634c5500d75e534c55000775514c55000dfa704c550004ff7648550004fe7648550004fc76485500357e75485500057d754855001eee62485500076d5248550016f661485500077551485500c7e4214855000dfa7048550034fe76d95400b67e65d95401fcfd75d954000cff74d954002cfe74d954000cfd74d954002cfc74d95403ee7f54d95403ee7d54d9540024fe73d9540004fd73d9540024fc73d954001cfe72d9540004fd72d954001cfc72d95403eebf42d9540014fe71d9540004fd71d9540014fc71d95403eebf41d954002cff70d954002cfd70d95403de7f50d95403de7d50d95403eefb40d95403debe40d95403debc40d95403def840d95403defa30d9540034ff76595400b67c65595403d5bf7459540005df73595400addc73595403e5fb70595403dcff75595400067f75595403d4ff7459540006bf7459540004ff7359540006df7359540004df7359540024fe7359540024fc7359540006dc7359540024dc7359540004ff725954001cfe725954001cfc72595400bebf4259540004ff7159540014fe7159540014fc71595400bebf41595401fcff7059540006fb70595400befb40595401febe40595401febc40595401fef840595401fefa3059540024fe76d8d400aede63d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d40006df53d8d400aedc53d8d400aede43d8d403cedd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d400aedf32d8d40014fe71d8d40004fd71d8d40014fc71d8d400aedf31d8d4002cfd70d8d4036edf30d8d400aedc6358d403c5fb7058d40004ff7654d40004fe7654d40004fc7654d4001cfe76d89400a6ee62d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89400a6ee42d89403beed42d8940014fe71d8940004fd71d8940014fc71d89403bebf41d894002cfd70d89402eeef20d89400a6ec62589403b5fb7058940004ff7654940004fe7654940004fc765494000dbc765094001ebc765094000cbc7650940006bf6550940006bd655094018ebe635094018ebc635094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400a7ac62509400a7ae3250940005bf7150940007bb705094000dbe705094000dbc705094017fb8705094002ebf605094002fbb605094017fba305094017faf2050940004ff764c940004fe764c940004fc764c940006df634c940026dc634c940007ad424c940014fe76d854009ef661d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540024fe73d8540004fd73d8540024f
  | 8 => 0x357e75d8d5000d7d75d8d500d6de63d8d500d75e53d8d5000cfd75d8d503867d75d8d5000c7d75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d5042e7f54d8d500067d54d8d500d67e53d8d500d6de53d8d5042edd53d8d500d67c53d8d50006df43d8d500d6dc43d8d5001cfe72d8d50004fd72d8d5001cfc72d8d50014fe71d8d50004fd71d8d50014fc71d8d50034fd70d8d50386df30d8d50005bf7458d500bdbc7458d500d6dc6358d500d75c5358d50425fb7058d50004ff7650d50004fe7650d50004fc7650d500057f7550d500357c7550d500073d5450d50005fb7050d5000df87050d5001cfe76d89500ceee62d895000cfd75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d8950024fe73d8950004fd73d8950024fc73d89500ceee52d895041eed52d8950014fe71d8950004fd71d8950014fc71d895041e7f51d8950006ee21d89500ceec21d8950034fd70d895030eef20d895030efa10d89500ceec6258950005f771589500c5f47158950415fb705895000d7c765495001e7c765495000c7c76549500057f74549500d57e73549500d57c73549500357f72549500376f72549500076f625495001e7e625495001e7c62549500cf6c62549500cf6e32549500057f71549500cf6f21549500077b705495000d7e705495000d7c705495019f7870549500367f60549500377b605495040f7b405495019f78405495019f7a305495019f7a205495019f7a1054950004ff7650950004fe7650950004fc76509500357e75509500057d755095002ebe64509500073d5450950005fb705095000df870509500bfbb4050950004ff764c950004fe764c950004fc764c9500057f754c9500357c754c950026de634c9500d75e534c9500076d524c95000dfa704c950014fe76d85500c6f661d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d8550024fe73d8550004fd73d8550024fc73d855001cfe72d8550004fd72d855001cfc72d85504067f52d85500067d52d85500c6f651d8550406f551d8550006f721d85500c6f421d8550034fd70d855028efa20d855028ef710d8550005ef72585500cdec72585500c6f461585503fdfb705855000d7c76545500167c765455000c7c76545500057f74545500d57e73545500d57c73545500057f72545500067f62545500357f71545500377771545500077761545500167e61545500167c61545500c77461545500c77631545500c77621545500077b705455000d7e705455000d7c705455013f7870545500367f60545500377b60545503f77b405455013f78405455013f7a305455013f7a205455013f7a1054550004ff7650550004fe7650550004fc76505500357e75505500057d755055002ebe64505500073d5450550005fb705
  | 9 => 0xc7558d210347c7558d21004ff7458d2102cfe7458d2102cfc7458d2144cff7358d21006df7358d210e6de5358d21006df4358d210e6dc4358d21444ff7258d21006ef7258d21106ee5258d21164ff7158d21006f77158d21166f65158d21004ff7058d2100cfe7058d2100cfc7058d210e6df3058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21026de6354d21006dd6354d211e7e42154d21004ff7650d21004fe7650d21004fd7650d21004fc7650d211c7e42150d21015ec7654921036ec7654921014ec765492101def755492101f6f75549210076f6554921036ee6554921036ec65549210f76c6554921006ef6354921006ed6354921007e77154921015ee7154921015ec71549211a7e47154921015e4715492101eef615492101fe761549211a76f51549211a7e651549211a76d5154921005ef70549210f76f50549211a7e7105492101df47654521036f4765452101cf47654521015f77554521017777554521007776554521036f66554521036f465545210f7746554521006f76354521006f56354521007e7725452101df6725452101df47254521147e4725452101de47254521016f76254521017e76254521147775254521147e652545211477552545210f7e55254521007655254521005f770545210f7775054521147e7205452100cfe76d812123fe421d81210defa60d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d812101cfd71d812100cfc71d8121006fb40d81210def840d81210defa30d81210defa20d81210defa10d812105fe421581210def8605812102cfe76d91500bebe64d915000dfa70d9150035f970d91500bfbb40d915000cfd75d915002cfc75d91500bebe54d915043ebd54d9150024fe73d9150004fd73d9150024fc73d9150006be43d91500bebc43d915001cfe72d9150004fd72d915001cfc72d9150014fe71d9150004fd71d9150014fc71d9150034fd70d91500bef970d9150034f970d91503d6bf40d91500befb40d91503d6f840d91503d6fa30d91500bebc6459150005df73591500d5dc7359150435fb70591501ffb8405915000d7c765515002e7c765515000c7c76551500357f74551500373f74551500073f645515002e7e645515002e7c64551500bf3c64551500075f73551500d57e73551500d57c73551500075c73551500d55c73551500bf3f43551500057f72551500bf3f42551500057f71551500bf3f41551500077b705515000d7e705515000d7c70551501ff7870551500367f60551500377b60551500bf7b40551501ff3e40551501ff3c40551501ff7840551501ff3840551501ff7a30551501ff7a20551501ff7a1055150024fe76d8d50
  | 10 => 0x8131004fd72d813101cfc72d8131336df32d8131006dd32d8131024fd71d813125ef641d8131006f541d81310fefa30d81310fefa10d8131005bf745813110dbc74581310fef86058131034fe76d95210f67e65d952148fe421d95211a4fd75d952102cfe74d9521004fd74d952102cfc74d95210f67f54d9521024fe73d9521004fd73d9521024fc73d95210067e53d95210f67c53d9521014ff72d9521014fd72d952149e7f52d952149e7d52d952101cff71d952101cfd71d952148e7f51d952148e7d51d952100cfe70d9521004fd70d952100cfc70d9521034ff76595210f67c6559521485ef7259521495f771595211a7e4215952148cff75595210067f7559521004ff745952102cfe745952102cfc7459521004ff7359521024fe7359521024fc7359521484ff7259521006ef72595211a4ff7159521006f77159521004ff705952100cfe705952100cfc70595210f67f505952102cfe76d91210eebe64d91210e5de73d9121005dd73d912146fe421d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121024fe73d9121006de73d9121024de73d9121004fd73d9121006dd73d9121004dd73d9121024fc73d9121014ff72d9121014fd72d912147ebf42d912147ebd42d912101cff71d912101cfd71d912146ebf41d912146ebd41d912100cfe70d9121004fd70d912100cfc70d912147eef20d912146ef710d912102cff76591210eebc6459121465ef7259121475f77159121187e42159121005fb70591210ddf87059121004ff7559121034fe7559121034fc755912146cff7459121006bf74591210eebe5459121004ff7359121024fe7359121024fc7359121006be43591210eebc4359121464ff7259121006ef7259121184ff7159121006f77159121004ff7059121006fb7059121004fb705912100cfe705912100cfc7059121006f8705912100cf870591210eebf4059121126ef2059121186f71059121004ff7655121004fe7655121004fd7655121004fc76551210067f65551210367c655512102ebe6455121006bd6455121005df73551210e5dc7355121207e42155121024fe76d8d210edbe74d8d21005bd74d8d210e6de63d8d2144fe421d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21006be74d8d2102cbe74d8d21004fd74d8d21006bd74d8d21004bd74d8d2102cfc74d8d21164fd73d8d21014ff72d8d21014fd72d8d2145eee52d8d2145edf32d8d2145edd32d8d2101cff71d8d2101cfd71d8d2144ef651d8d2144edf31d8d2144edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21024ff7658d210057f7558d210f57c7558d210e6dc6358d21445ef7258d21455f77158d21167e42158d21004ff7558d210067f7558d210047f7558d21034fe7558d21034fc7558d210067
  | 11 => 0x4fe7655131004fd7655131004fc765513102ebe6455131006bd6455131005df7355131025dc735513110f9f4355131015f67155131015dc7654d31036dc7654d31014dc7654d31025df7554d310275f7554d310075f6554d31036de6554d31036dc6554d311175c6554d3110dde7454d3110ddc7454d311175f5454d310075d5454d31005df7254d31007d77154d31015de7154d31015dc7154d311e7d47154d31026df6154d31027d76154d311e7d65154d311e7d64154d31005df7054d3101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d89314b6de53d8931006dd53d8931006df43d89314b6dc43d8931106ee32d89314b6ed32d8931024fd71d8931446f651d8931446ef21d893100cfe70d8931004fd70d893100cfc70d89314b6df30d89310057f75589311157c7558931106ec62589314adf77158931004ff7654931004fe7654931004fc7654931025de735493101eee6254931004ff7650931004fe7650931004fc7650931006bf645093102ebc6450931005df7350931025dc735093118f9c4350931015dc764c93101edc764c931014dc764c931005df754c931005dd754c931006df654c931006dd654c93110dde744c93110ddc744c93116ede644c93116edc644c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c931107cc624c931107ce524c931007cd524c931107ce424c931007cd424c931007d7714c931015de714c931015dc714c931167d4714c931026df614c931027d7614c931167d6514c931167d6414c931005df704c931025f47654531036f47654531024f47654531015f77554531017777554531007776554531036f66554531036f46554531117746554531005f77454531007d77354531025f67354531025f4735453114fd47354531016f76354531017d7635453114fd65354531117d553545314a7d7435453114fd44354531006f7625453111777525453100775525453114fd73254531007d5325453111777505453114fd73054531025f4765053102ef47650531024f47650531005f77550531005f57550531015f77450531017b77450531007b7645053102ef6645053102ef4645053110fb4645053110fb65450531007b55450531007d77350531025f67350531025f4735053112fd47350531016f76350531017d7635053112fd65350531007d5535053110fd7435053112fb6435053112fb4435053112fd4435053112f94435053110fb74250531007b5425053112fd73250531007d5325053110fb7405053112fd7305053100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d
  | 12 => 0xc62589414fdf77158941005fb705894111df87058941004ff7654941004fe7654941004fc765494102dbe7454941005f77154941015f47154941015bc765094101ebc7650941014bc7650941005bf7550941005bd7550941006bf6550941006bd655094112dbe735094112dbc735094118ebe635094118ebc635094102dbf725094102faf7250941007af625094101ebe625094101ebc6250941127ac6250941127ae3250941007b77150941015be7150941015bc7150941187b4715094102ebf615094102fb76150941187b63150941005bf7050941127af2050941187b71050941004ff764c941004fe764c941004fc764c941005bf744c94102dbc744c941006df634c941026dc634c94112f9c434c941007ad424c94100cfe76d814111efa60d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d814101cfe72d8141004fd72d814101cfc72d81413a6bf42d8141006bd42d814102cfd71d814111efa50d814111efa40d8141006fb20d814111ef820d814111efa10d814111ef86058141034fe76d95311167e65d95311e4fd75d953102cfe74d9531004fd74d953102cfc74d9531014ff73d9531014fd73d95314f67f53d95314f67d53d953101cfe72d9531004fd72d953101cfc72d95310067e52d95311167c52d95314f6df32d9531024ff71d9531024fd71d95314e67f51d95314e67d51d953100cfe70d9531004fd70d953100cfc70d95311167f50d9531034ff76595311167c65595314dddf73595314edf771595314e4ff75595310067f7559531004ff745953102cfe745953102cfc74595314dcff7359531006df7359531004ff725953101cfe725953101cfc725953114edf32595311e4ff7159531006f77159531004ff705953100cfe705953100cfc705953102cfe76d913110ebe64d9131025de73d9131015dd73d913110f9f43d9131034fe75d9131004fd75d9131034fc75d91311c4fd74d9131014ff73d9131014fd73d91314c6dd73d9131014dd73d91314d6bf43d913110edf43d91314d6bd43d91314d6dc43d913101cfe72d9131004fd72d913101cfc72d913110ebf42d9131024ff71d9131024fd71d91314c6bf41d91314c6bd41d913100cfe70d9131004fd70d913100cfc70d9131006be40d913110ebc40d91314d6df30d913102cff765913110ebc64591314bddf735913112f9c43591314cdf77159131004ff7559131034fe7559131034fc75591314c4ff7459131006bf745913110ebe54591314bcff7359131006df735913110edf435913112ebe435913112ebc435913112edc4359131004ff725913101cfe725913101cfc72591311c4ff7159131006f77159131004ff705913100cfe705913100cfc705913112edf3059131004ff7655131
  | 13 => 0x951004fe7650951004fc765095102ebe6450951006ef625095101eec6250951004ff764c951004fe764c951004fc764c951026de634c9510076d524c951015f6714c95100cfe76d815113efa60d8151014fd75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d8151024fe73d8151004fd73d8151024fc73d815101cfe72d8151004fd72d815101cfc72d81513fe7f52d81510067d52d8151034fd71d815129ef621d815113efa50d815113efa10d8151005ef7258151145ec725815113ef86058151034fe76d95411367e65d9541204fd75d9541014ff74d9541014fd74d95415367f54d95415367d54d9541024fe73d9541004fd73d9541024fc73d954101cfe72d9541004fd72d954101cfc72d9541536bf42d954102cff71d954102cfd71d95415267f51d95415267d51d9541526f631d954100cfe70d9541004fd70d954100cfc70d9541034ff76595411367c655954151dbf7459541005df735954112ddc735954152df77159541524ff75595410067f755954151cff7459541006bf7459541004ff7359541006df7359541004df7359541024fe7359541024fc7359541006dc7359541024dc7359541004ff725954101cfe725954101cfc7259541156bf4259541204ff7159541006f77159541206f63159541004ff705954100cfe705954100cfc70595411367f5059541015bc7655141036bc7655141014bc765514102dbf755514102f3f75551410073f6555141036be6555141036bc65551411373c65551410079f735514112dbe735514112dbc73551410079c735514112d9c73551411373f5355141005bf7255141007b77155141015be7155141015bc7155141207b4715514102ebf615514102fb76155141207b63155141005bf70551411febe60551411febc60551411373f5055141207b71055141024fe76d8d4102dbe74d8d41015bd74d8d4112ede63d8d4112f9e43d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d414bebd74d8d41014bd74d8d41516be54d8d41006bd54d8d41006df53d8d4112edc53d8d4112ebe43d8d4112ede43d8d41516dd43d8d4112ebc43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4112edf32d8d4102cfd71d8d414bedf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d4112edc6358d4112f9c4358d4150df77158d41004ff7654d41004fe7654d41004fc7654d41005bf7454d4102dbc7454d410073d5454d4101cfe76d8941126ee62d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941506be54d8941006bd54d8941024fe73d8941004fd73d8941024fc73d8941006be43d8941506bc43d8941126ee42d8941506ed42d894102cfd71d8941466ef21d894100cfe70d8941004fd70d894100cfc70d8941506bf40d8941466f710d8941126e
  | 14 => 0x56fcf43549321afcc43549321776f51549321afcf31549321776f50549321afcf3054932025ec765093202eec7650932024ec7650932005ef7550932005ed755093201def745093201faf7450932007af645093202eee645093202eec645093216fac645093216fae5450932007ad5450932007cf7350932025ee7350932025ec735093218fcc735093201eef635093201fcf635093218fce5350932007cd535093216fcf435093218fae435093218fac435093218fcc435093218f8c435093216faf415093218fcf315093216faf405093218fcf3050932014fe76d8532166f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d85324aede53d8532006dd53d8532006df43d85324aedc43d8532024fd72d8532456ee52d8532006ed52d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d85324aedf30d85320057f75585321757c7558532166f4615853200cfe76d813215efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d81322deee42d8132006ed42d8132014fe71d8132004fd71d8132014fc71d8132346df31d813215efa30d813215efa20d8132005bf745813216dbc745813215ef8605813202cfe76d9151156be64d9151014fd75d9151156be54d9151566bd54d9151024fe73d9151004fd73d9151024fc73d915101cfe72d9151004fd72d915101cfc72d9151034fd71d915151ebf41d915151ef631d915100cfe70d9151004fd70d915100cfc70d91515667f50d9151156bc6459151005df735915114ddc735915155df77159151024fe76d8d5114ede63d8d51014fd75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5114ede53d8d51556dd53d8d51006df43d8d5114edc43d8d5101cfe72d8d51004fd72d8d5101cfc72d8d51034fd71d8d514dedf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d5114edf30d8d5114edc6358d5154df77158d51004ff7650d51004fe7650d51004fc7650d5101cfe76d8951146ee62d8951014fd75d895102cfe74d8951004fd74d895102cfc74d8951024fe73d8951004fd73d8951024fc73d8951146ee52d8951546ed52d8951146ee42d8951034fd71d8951486ef21d895100cfe70d8951004fd70d895100cfc70d89515467f50d8951006ee20d8951146ec20d8951146ec625895153df771589510157c765495101e7c76549510147c76549510357f72549510376f72549510076f625495101e7e625495101e7c62549511476c62549511476e32549510077771549510157e71549510157c71549511a77471549510367f61549510377761549511a77631549511a76f21549511a77621549510057f7054951004ff765
  | 15 => 0xa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d814202cfd72d8142014fe71d8142004fd71d8142014fc71d81423b6bf41d814217efa50d814217efa40d814217efa20d8142006fb10d814217ef810d814217ef86058142034fe76d95321767e65d95321ecfd75d953202cfe74d9532004fd74d953202cfc74d953201cff73d953201cfd73d95325ae7f53d95325ae7d53d9532024ff72d9532024fd72d953259e7f52d953259e7d52d9532014fe71d9532004fd71d9532014fc71d95320067e51d95321767c51d95325aedf31d953200cfe70d9532004fd70d953200cfc70d95321767f50d9532034ff76595321767c6559532595df73595325a5ef725953259cff75595320067f7559532004ff745953202cfe745953202cfc7459532594ff7359532006df73595321ecff7259532006ef7259532004ff7159532014fe7159532014fc71595321aedf3159532004ff705953200cfe705953200cfc705953202cfe76d913216ebe64d9132025de73d913201ddd73d913216f9f43d9132034fe75d9132004fd75d9132034fc75d91321ccfd74d913201cff73d913201cfd73d913257edd73d913201cdd73d913258ebf43d913216edf43d913258ebd43d913258edc43d9132024ff72d9132024fd72d913257ebf42d913257ebd42d9132014fe71d9132004fd71d9132014fc71d913216ebf41d913200cfe70d9132004fd70d913200cfc70d9132006be40d913216ebc40d913258edf30d913202cff765913216ebc6459132575df735913218f9c4359132585ef7259132004ff7559132034fe7559132034fc755913257cff7459132006bf745913216ebe5459132574ff7359132006df735913216edf435913218ebe435913218ebc435913218edc43591321ccff7259132006ef7259132004ff7159132014fe7159132014fc7159132004ff705913200cfe705913200cfc705913218edf3059132004ff7655132004fe7655132004fd7655132004fc765513202ebe6455132006bd6455132005df7355132025dc735513216f9f435513201dee725513201ddc7654d32036dc7654d3201cdc7654d32025df7554d320275f7554d320075f6554d32036de6554d32036dc6554d321775c6554d3216dde7454d3216ddc7454d321775f5454d320075d5454d32007cf7254d3201dde7254d3201ddc7254d321efcc7254d32026df6254d32027cf6254d321efce5254d321efce4254d32005df7154d32005df7054d32025ec7654932036ec7654932024ec765493201def755493201f6f75549320076f6554932036ee6554932036ec65549321776c6554932005ef7454932007cf7354932025ee7354932025ec73549321afcc735493201eef635493201fcf63549321afce5354932177cd5354932
  | 16 => 0x85521a6f651d85521a6f641d85521a6f621d855200cfe70d8552004fd70d855200cfc70d855253e7f50d8552006f610d85521a6f410d85521a6f4615855200cfe76d815219efa60d815201cfd75d815202cfe74d8152004fd74d815202cfc74d8152024fe73d8152004fd73d8152024fc73d8152034fd72d8152014fe71d8152004fd71d8152014fc71d81524167f51d815231eef21d815219efa50d815219efa20d8152005f771581521a5f4715815219ef86058152034fe76d95421967e65d954220cfd75d954201cff74d954201cfd74d95425de7f54d95425de7d54d9542024fe73d9542004fd73d9542024fc73d954202cff72d954202cfd72d95425ce7f52d95425ce7d52d95425ceee32d9542014fe71d9542004fd71d9542014fc71d95425debf41d954200cfe70d9542004fd70d954200cfc70d9542034ff76595421967c65595425c5bf7459542005df735954218ddc73595425d5ef72595425ccff75595420067f75595425c4ff7459542006bf7459542004ff7359542006df7359542004df7359542024fe7359542024fc7359542006dc7359542024dc735954220cff7259542006ef725954220eee3259542004ff7159542014fe7159542014fc71595421b6bf4159542004ff705954200cfe705954200cfc70595421967f505954201dbc7655142036bc765514201cbc765514202dbf755514202f3f75551420073f6555142036be6555142036bc65551421973c65551420079f735514218dbe735514218dbc73551420079c735514218d9c73551421973f5355142007af725514201dbe725514201dbc725514220fac725514202ebf625514202faf625514220fae3255142005bf7155142005bf70551421febe60551421febc60551421973f505514220faf2055142024fe76d8d4202dbe74d8d4201dbd74d8d4218ede63d8d4218f9e43d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d42576bd74d8d4201cbd74d8d425bebe54d8d42006bd54d8d42006df53d8d4218edc53d8d4218ebe43d8d4218ede43d8d425bedd43d8d4218ebc43d8d4202cfd72d8d42576df32d8d42014fe71d8d42004fd71d8d42014fc71d8d4218edf31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d4218edc6358d4218f9c4358d425b5ef7258d42004ff7654d42004fe7654d42004fc7654d42005bf7454d4202dbc7454d420073d5454d42014fe76d8542186f661d8542034fe75d8542004fd75d8542034fc75d854201cfd74d85424febe54d8542006bd54d8542024fe73d8542004fd73d8542024fc73d8542006be43d85424febc43d854202cfd72d8542186f641d8542186f621d854200cfe70d8542004fd70d854200cfc70d85424febf40d8542476ef20d8542186f46158542005fb705854217df8705854200cfe76d814217ef
  | 17 => 0x6167d53d954301cfe72d9543004fd72d954301cfc72d9543014fe71d9543004fd71d9543014fc71d954300cfe70d9543004fd70d954300cfc70d95431d67f50d9543034ff76595431d67c655954360dbf7459543605df7359543614ff75595430067f755954360cff7459543006bf7459543214ff7359543006df7359543604df7359543004ff725954301cfe725954301cfc7259543004ff7159543014fe7159543014fc7159543004ff705954300cfe705954300cfc7059543025bc7655143036bc7655143024bc765514302dbf755514302f3f75551430073f6555143036be6555143036bc65551431d73c65551430079f7355143025be7355143025bc73551432179c735514302ebf635514302f9f63551432173f53551432173d53551431febe60551431febc60551431d73f50551432179f305514301cfe76d89431ceee62d8943034fe75d8943004fd75d8943034fc75d8943024fd74d89435b6be54d8943006bd54d894302cfd73d89435b6df43d8943586be43d8943586bc43d8943586dc43d89431ceee42d89431ceee32d8943014fe71d8943004fd71d8943014fc71d894300cfe70d8943004fd70d894300cfc70d8943586df30d89431ceec6258943014fe76d85431c6f661d8543034fe75d8543004fd75d8543034fc75d8543024fd74d854350ebe54d8543006bd54d854302cfd73d854350edf43d85434cebe43d85434cebc43d85434cedc43d854301cfe72d8543004fd72d854301cfc72d85431c6f641d85431c6f631d854300cfe70d8543004fd70d854300cfc70d85434cedf30d85431c6f4615854300cfe76d81431befa60d8143034fe75d8143004fd75d8143034fc75d8143024fd74d814302cfd73d814301cfe72d8143004fd72d814301cfc72d8143014fe71d8143004fd71d8143014fc71d81431befa50d81431befa40d81431befa30d81431bef8605814302cfe76d91521b6be64d915201cfd75d91521b6be54d91525febd54d9152024fe73d9152004fd73d9152024fc73d9152034fd72d91525c6bf42d91525c6ee32d9152014fe71d9152004fd71d9152014fc71d915200cfe70d9152004fd70d915200cfc70d91525fe7f50d91521b6bc6459152005df73591521addc73591525f5ef7259152024fe76d8d521aede63d8d5201cfd75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521aede53d8d525eedd53d8d52006df43d8d521aedc43d8d52034fd72d8d52596df32d8d52014fe71d8d52004fd71d8d52014fc71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d521aedf30d8d521aedc6358d525e5ef7258d52004ff7650d52004fe7650d52004fc7650d52014fe76d85521a6f661d855201cfd75d855202cfe74d8552004fd74d855202cfc74d8552024fe73d8552004fd73d8552024fc73d8552034fd72d
  | 18 => 0xc6258954014fe76d8554006df63d8554006dc63d8554206f661d855402cfd75d8554034fd74d8554024fe73d8554004fd73d8554024fc73d855401cfe72d8554004fd72d855401cfc72d855452ebf42d8554206f651d8554206f641d855400cfe70d8554004fd70d855400cfc70d855455e7f50d8554005df7358554215dc7358554006df6358554006dc6358554206f4615855400cfe76d815402dbe74d8154035bd74d8154006df63d8154006dc63d81541fefa60d81541ffba40d815402cfd75d8154034fd74d81541febd74d8154034bd74d8154024fe73d8154004fd73d8154024fc73d815401cfe72d8154004fd72d815401cfc72d81543e6bf42d8154014fe71d8154004fd71d8154014fc71d81543e6bf41d81541fefa50d81541febe40d81541fefa40d81541febc40d8154005df7358154215dc7358154006df6358154006dc63581541fef860581541ffb8405815402cfe76d91531f6be64d9153024fd75d91531f6be54d9153636bd54d9153034fd73d915360ebf43d915301cfe72d9153004fd72d915301cfc72d91531f6bf42d9153014fe71d9153004fd71d9153014fc71d91531f6bf41d915300cfe70d9153004fd70d915300cfc70d9153006be40d91531f6bc40d91531f6bc645915362ddf73591530257c765515302e7c76551530247c76551530357f74551530373f74551530073f645515302e7e645515302e7c64551531f73c64551530075f73551530257e73551530257c73551532175c73551530367f63551530375f63551532173f43551531f73f42551532175f32551531f73f41551532175f31551536273e40551531f73c405515301cfe76d89531eeee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d89531eeee52d89531eeee32d8953014fe71d8953004fd71d8953014fc71d89535a6df31d895300cfe70d8953004fd70d895300cfc70d89531eeec6258953014fe76d85531e6f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d855301cfe72d8553004fd72d855301cfc72d85534eedf32d85531e6f651d85531e6f631d855300cfe70d8553004fd70d855300cfc70d85531e6f4615855300cfe76d81531defa60d8153024fd75d815302cfe74d8153004fd74d815302cfc74d81534267f54d81530067d54d8153034fd73d8153426df53d81533967e53d81533967c53d8153396dc53d815301cfe72d8153004fd72d815301cfc72d8153396df32d8153014fe71d8153004fd71d8153014fc71d8153396df31d81531defa50d81531defa30d8153005bf74581531f5bc74581531def86058153034fe76d95431d67e65d9543214fd75d9543024ff74d9543024fd74d954361e7f54d954361e7d54d954302cff73d954302cfd73d95436167f53d9543
  | 19 => 0x6001800000200d00080000000000008034000004002004400000c00100040120000070040030002001001800c001003800400800800280080000000030000004003008000400000200b80080180000018028004001001809801c0060040008000006024fe76d8d54216de63d8d5402cfd75d8d54034fd74d8d54216de53d8d54216de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54216df32d8d54006de32d8d54216dc32d8d54014fe71d8d54004fd71d8d54014fc71d8d54216df31d8d54006de31d8d54216dc31d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54216df30d8d54006de30d8d54216dc30d8d54215de76d8d54024de76d8d546075f75d8d546075c75d8d5462f9f74d8d546079c74d8d5462f9f54d8d546075e54d8d546075c54d8d546079c54d8d54006de62d8d54006dc62d8d546079f42d8d54006de61d8d54006dc61d8d546079f41d8d54006de60d8d54006dc60d8d5462f5f50d8d540079e40d8d546079c40d8d54606df75d8d54216de75d8d54606dd75d8d54606dc75d8d54606df74d8d54216de74d8d54606dd74d8d54606dc74d8d54606df54d8d54606de54d8d54606dc54d8d54006df72d8d54006de72d8d54006dd72d8d54006dc72d8d5462edf52d8d5462ede52d8d5462edd52d8d5462edc52d8d54606df42d8d54606de42d8d54606dd42d8d54606dc42d8d54006df71d8d54006de71d8d54006dd71d8d54006dc71d8d5462edf51d8d5462ede51d8d5462edd51d8d5462edc51d8d54606df41d8d54606de41d8d54606dd41d8d54606dc41d8d54006df21d8d54006de21d8d54006dc21d8d54006df70d8d54006de70d8d54006dd70d8d54006dc70d8d5462edf50d8d5462ede50d8d5462edd50d8d5462edc50d8d54606df40d8d54606de40d8d54606dd40d8d54606dc40d8d54006df20d8d54006de20d8d54006dc20d8d54006df10d8d54006de10d8d54006dc10d8d54216dc6358d54605de7618d54216de7618d542175e7518d542175d7518d54616df6518d542179e7418d542179d7418d5460edf6418d546479f5418d5463f5e5418d5463f5c5418d5463f9c5418d54217ce7218d54217cd7218d54006de6218d54006dc6218d5463f9f4218d54217d67118d54217d57118d54006de6118d54006dc6118d5463f9f4118d54217da7018d54217d97018d54006de6018d54006dc6018d546475f5018d540079e4018d5463f9c4018d5401cfe76d8954006df63d8954006dc63d895420eee62d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d895420eee52d895420eee42d8954014fe71d8954004fd71d8954014fc71d89545d6bf41d895400cfe70d8954004fd70d895400cfc70d89545f67f50d8954005df7358954215dc7358954006df6358954006dc635895420ee
  | 20 => 0x2001803002800d014000000800000200080040000020064024006005800800a001000000c0000040008000006010000800c01000c0028004034005003800001000300980040020010030000058000001800000a002000000401201200e8028000000009001801e00300080280000220000000000002003800400c0000000030010001006801400200c0030014024000001000000c025000800400600000e800002800000100140000000000000000005007000000800000180000000030080048066009003002000e0020000038006011000000002600d00100b800200700000300080050000020006004001802000400c004002000000e007000800400100480200000030000000006000000804c0000000008000002001000000000000b000001400c003000801c00600200200c800a0020020018000000018010c000001000000400800900d80180040110000004000006000808c00800d009000c040005001002800000900280000040010000004004003000000000000000000080000090000024006005000002000200000b001c08800202c801800000200500140000060010008000004000000000000100000100180160108000008001007800003c00100780a000002900000280060050020020002004002000401e000000800002602b00600180000050050000018003000000c0040000010028008014004804c00a004004000001e00a005005000200000000000000000000000010001001800000400500680140060000018000006003007800c0220000030018000003002008000000e0008000004005001002c000001000800404a001003801000801900d802000c0000008028018007003001801200a001800400a006007802c000000001800c00000a003800000200c00080000060010098000000007000000000600300080040000000010060008000000000c002006003000000e00c001000400a003002000001e0000058024000003002001800001d000000c00000000000140020020010010014004008001805e000000001801e01b000006800800000000080180070008000008012006001001000000000300020120050000034002001800c02a001013800800600100180000020000000050004005003000c0000150008024000001000000000a005007000000a00100000040140010020020028000001801800200b001800001000f00000100040000000014004005000000800600c006001800400200400080020070000008000023002000c00200700880300000090000000008006001000403200500280000000010010004000000001000000a00000000000000010008000002003005006400600200200080020050058064000006000000c01e001009801000000a002000000200001e8000000001005800400000
  | 21 => 0xc20000000000dcca2920491747ec0001ae8000cd60c660488254ac00059c000146067028100010ce357000000129c0002b82c54e2e0d425681158f8cca630a55c35c88b0001dbd46e3262e72780dc036f2e1139caaaaed4c22d810be246437b2156f6ada2432ce4f1a742011068d664c3a0eb8d410245cd1198671414b8b000000000000000000000000004fd800093232c0000db93ba0004689d7c00068f0fb0b598fc72d29510ed41a08029aaae50ca8572ae0b6cf68c70216213d4a8bb73c12ca94861cd15324fc03e39535b2a100007cc5208000000aa65159fb10363d4394086c77400036793dc88055a1b62870f646fe00023f876200014025a813400001da92041a305025b398e9200021e172470ca120000c1c00000000028c800034a00026f51ae5c5139b3b809c7f54d6000000000380000320010000058032007000000c000001008000001600f0000000000010009801000001e000000802c001000800800200600080000040010030004012000000001402001f0080008000008001001c00e0000018050002019004800c00000e000800402a00e004802c00c0000040010000006000006000a00d000803c02600000000280000000030000000000005805800a0040000008002001000000000a0110008008000002006001c002001001004000000000c8000014000015000000600700500040140090000050000000002000c0040020038004000003000805c014007007000000c00500080c400001400000040320110010040004000012000000400c00000080120030000000000001007801c006009000000c0100020040010006001003800001e00200c802803800a000000c004001001001400a001000800c03600c001000000200e0010084000000000002400e0000000008002000001800000a0090000024012000001002c0020000008000004002007800000000300080040fe001000800c0020290020000002001001802801e0070018000002004002001c00c0000020008008002000003000400400000000000040000004012001003000801000000000400040020000008018000000000c0100010010000000004002001805a00a0058000002001001800002c0010178000028000000000c00000700f800c00602600000580140110000000000007007002005e0030060044020001001001002a00100d802000001f002000c0080010000004000000003000c02c008001806c00a00d00a000000600b009804400c003003003000e019002009c0000000000018004004002801c006041000000000800200000200140020038040000021001001c00000300100040040170030020024001000003001800f00400000000000000000002002000005000401a001801001a00d00000000320020000004006003003800000000300280
  | 22 => 0x8280007c0a88609a644000000585075000077a5928474bea8043842a89156b7900016fcb1e8cb4e6267cfc8a0f19a1a0d8c0ae30fe00001fa0a9528800000000000000000000006449a8c19a7524858dd80001940003220000000000243c0000004ffaa959261270e78ddd72233a050a4e1814a405412c4c27888e63505cd006cc238d1db8676c5827d1e68d6058d01983d98b4a7d06fad616c47f303314680ca5a52cca08459c3cc12a8dfc2283d64c08000a38b5b2d9076850c71e1c18fa8986d26587000195cb820002f0126677e46faf041ae0000001e644f600000000013040005a285292820004392ed000000006290780000000000300ae25244a20000f4c5574daaa9d3e00004fa00005086df57b9fe000097200000000007f4000000000086b692866c00000000000000000000000010000aa846200005f60003342738bde0f33008000000321000336038253163300017de00039593095760000001bd9240c992aa000000047151681cca64c173d10a5423059c13631e08dc9422db981c5c22ca0c2302c6844640d49adce4c00030200010ee0002383244000c20085307d7400000001a05a601f7448af1ce7e86303080b80004c80000001a880000ab9f3d420aac11d80016ea00069d11d46360000a59e0087282b2150a6d56247765e9cc4000a620003285232ac200000000002dd5af2ba0000c774eda7a08d610c4449e3c000c9a3859f685b236800008940007af06224114f472c55a2e412682d713eab348e6000000029d6869a6345030c00077b41a32f0fce4a646f2f7000049c544a1b16940000588f84aa4ccc12da164a68ade420b16d9e01a648ea074912b6c2608000c3c44d4132ee44b40001980000ed435912eb23097e54431e000000000028c08b52c00001189f781e80005ca1a986100f051e9df082c00045634200007bb0928de9118a190b099cc7dc00051f248cdd48840001684000b1847e00004c25ee3b80000b9449228801050ead0402e15ac7464695c605fcebc33745995b012c12e46296b8cb400000033482f804955f2a0c0002401591e0413a0004c499e97d6c7556a17605d6ce04e90d990660000000000c4eb215a6800199257f18780004202ae1769b3572464f0d125d862a86661c1284c441c66608ae8d3809b5e99d8ccc25cf09694344bc8af099893918418f02a2060f38af80aa01ed0c44fc25481bd564b532f431ac088965000178c69273b19701542565b5413afc400000032303b0dc2578467a8740009b631e800086c4d331980013f447a00024dd25685300b1ac400000023f1b0c0007540b58e5878687b5cdaaac8b07c60e6000000000000033c942cc6560803704c434b3a817f935452b52fa07982454d2362e8cfe04451470485412000000000137cce4563828c99a79100000000009a3217a5717
  | 23 => 0x5d6000000000031d0001c4c0000000000000dfeb4768f0e100004df00006e8000cdc00000000002f663707a83400004960a78cbe8420a1800000000013818f8a500000000000c880000002c480003aa0000304000832000000181c3543bc99992ba58000010484be000000344c000689000000000000000019308bc90500001740003d5471000070e0001351c5000043e1c6000135e5db089a0b19e800000028b0b10840000154d448bf548612756ee6b939533a174ccf568aa324b0a7125960b34e9632f1318608cf8abf0000e8400000069729fd0c200000008680003e8145255950a3e500010d000000059d93005facfe2510000eeca9e3910000baa00003527f8a3e0001c81cf0334000539a3b86fcc813bf858c3bc000100b2d08be54703eb47c000000000300178ab283c60d1c000000193932800054e535800000000005c80014ec0000000b45964aff2828015688221596800082e68000028e812097b34800000006c85f4a5609ca4d50a116cc0008544ee0f5d6caafe5c6a0c5472a00673b2f80004490002514000000000236c000000566034c000000000252c000bb30c81f600f40005ec0f20772000154800198e00044d2d8433ecab60c24197269321f3aaa96c81980000000e22000567212145e3e23ca8740680ca6446a578000ae6400ae9c32a19e01497e4e0241b43b1324f52d0a22100c118200000023d92420ae44c340077a2af2b3851930065c113ac8c6820e51b285f53803820b8092d7f466a44d93480e414f01211d8000b6a2260ff10522160000aa096c472667040c9fc9c909ca2582343b562c8fe885c00028ca23c00000000000015be7eb0002b540009474349db4000a0c00003e4000c2e000000197e00000000016280004cc800000000000000014a000063680003fa0370001d740003bc00018b59da594000000000000000000015b00002890000d700b610002300000000000fdc532000365b41c0bc0000000000f2084314e2ed421cd325f1b450ecec8e0660c5816a8b22978000f4a81a356b0c80000005d0800178cbd41a980017023a254ca7bcc327ef11022f113c3812ea121cce80005212438f1000000002780000424b49a480000000791e756b86865d818fca8c45b2f69500e0000024603d495c0db0002d51128afa000272c9c2c8068e0c191aa1b200018e148a2380000648ed662e0990000daa158034a68448e4b858d31140004d00590df4a78bc45238000afc6a94d006e5094c722f01fe4fd42b616480007b8000623800155a1af33196e471e7e05cc883c93c610068260d2c65150c70b500005f02911ee955c0b8603aeb01780001db84d8a7c74c00000000005873c19e8540a0002ab15bd07e35f000000000000019685bcd78ae9000328989436354da6918f200813484ed8423293a000003261623
  | 24 => 0x50f801d70ad2b54b0000bbeaa14bd10340006764b80410e9494c560a9389e200043a1b615b80000000000000bab4fb2dc5986ad01f9000000000019f10cd7f02fe64a2330000000129800000000068b9f0962226700000003e800068c0000ee60066280ec10fc97c00026604509bf00000000000000000000000000453000179c00000008d09ec0002af13459526a700005980000005a7000000000000000001148c000000000c40000001f5c72445054e24247340000001c7c6c28904c3800080e52502180015ce0005ba1954332bf4568a65c0009681e3120010e8d90e900004c00002fe8d3000000000032540008cd0000000c6e22b0000001146623483aba96181ca1aa947419e79818b85240000002bb12ccbe893e49306fda1a91a51b335cfdc11e6a10ce40001164e980018f454c68b0fcc5fe4f3514257cb0c9783210f98dc67b300002d00000e1000000000000043e2b5800015e41780018760001438000a842f969babd8000ad90ee0000fba0ed26a0000000b3600000012cc88068580000002523b48d600ee00121405810d02051d91a81260bec5bd158054276800000000000000000cac7a471d6160be88ce00030d8000628410000032846c2b40fa925070000058bb50c79a000000000159000005f0001878c6947e92290f07e800000006e0c4c3e6800000075b00000002b600000000011ac0005a79b1da5e0003e533fc000b1d1cc8cf17d09d90002b4ca8246a03e234d2542d026588fd85289215e9090000cbb2a59e792766f50000000714b27546902cc2c20b2f98000c604ff69629bc886050341328c2e22ab41aaa2d1b8bf61f78e9406816760430b400058354984985967e10002a5d5e4d3d3060b9d3f27710f59c659a03b44da000000058915027910000190c39d5c5b8cb75cd16602ee51b44fa9b000000023c9f100004f92fd00003b01d921806856aa8235e4a5890120004f51f7c0000001e8a95c0000005a01a20f1610b4bb83816dc1970a4172000031204e18994a696b2ac95840007a45eb2018000ae12d6800101a2e812e1ec08fab09146acf0f284852eb823cd7e3c0015821928c2c2470224c000d1d4be9c25360c2837633d966e00007e000078250b33d82ac3882ef24231f55f69c721109fd7f292469ca1ccd941c74140c904b2ca428412dc0000000002e7c000bf000002510bc0003c3937869e0000d58000000a1400013b400000029d91f046e39e0001cb880000012800000b07155b1a7c512a5bb08416c06345f84ad9a6c9688e15b5847d73c0000003310306000000300400089d218b2199666d4089218193c4974c326ccb2642348e184ccde6564b7817c05423a000282000000039a00088ac0005a4b0dc96291815b809cea61750001e24dd200005680000000003cb8000130c540c509bc00037c4d70000
  | 25 => 0xcfaacd100d1d6451e24f5959c949542923ad18140806845be014425250115823e98567fe0002d2c5bc3de041a2a84922f553407c16103b604205b50ac367548804479e0005b30000e368f44feaff16601e94a40dcc0000002d600000005af0000da80009884570be0000000000072587aa2064100000004e40169fa4e3060b16180300002d50002b2c0006bd25e0000000a7900000007f00005d42f3582c2f066980000009311702da132864a077b0c00007e500000011dec900000000b528c62f113e08340386010b005c6b0226eb2a97387bc0002b800000000bcaf6cd9ccad42a87e544200022780002600002c9000178694a06aa9ec174c5e4539bf4748c2f3a281a00003780000000fb2d0922a0000e82ad26998a50000bd16240614792917000000010a27c000144c0000000003158cfa00035218200004d6607834853e0000002c051ca000166284c9cc0000a903ac30200024703eced80000000000074b505500000000aef0002b880000002e9000000057d5bf07a15668462b19ae80007752e2015c8b47583d885f898cc1d40297c45d88025389df40008d065600017be9ca2369ce0a7497900000000008fb2b4a6689d404833aab7493600030e800000000029cb38482a4be675997842ac7b000034418e3be00006a00008f04c98f387267841c4a960da27743c9936008e144153a2e1a7c9750000298d8000000000248d007455e212400000044b87b92041df2f6000080a00000000000000000000000a0007569033dce38c062a1907c3c873328719b81f40005401a759a87a01a683758d86da4891f896ae111087b3000007480ab2e200dc2bc315b29cf2caf05cc145922a7561d722dc75273a46d05690e272400026a040804a00000002125e100019f9a7090100031fd3f826458da9711ea7b7005048d2a48ce611910538c124375ad491421e251a8fece1ea740002434c8294920c1ee4d349ad60e000012a000000138116240115d89f951ebd73e09f14e9c35100012d460800064d800000065b00000013900004f08c8087a4e84bf2054ffe00b09b80014aad1032a1154de897155c0ecd1d0b6d00007749300783ea0001606b5f01e82213b44f404cac980b4aeb4d10000000bbe41b00012ce6e711795dcda400003581e4b9872115f0864386695511000029aab736b0dc56b45f709f9fc901484e3fd0cfc0008701a1a7952aa0000b5160572e1ef57e1995226bd93789f49152ba200004e1078a1a0001bbc00000038710110b000047523b54b40000001450000b6f5ff16e0000cfa37281b092258a1ab2811338b7d5dc086030003f3fe94b58c61b0585a6c4030ac61209a956321bc5d8a931a7685d000204c00000000000015e86f30000a2d6ba4f01f1800000000003b00749d20a02b333698224d72272294cd8772000275cc62000
  | 26 => 0xc4e7983c4ee9c42258620000b674101e49a320e746e8000c5276110fa458e140000e88480b3c0000e5b0a992c29d0f3aed93360006018db47da8875678d1800052c639b1007fa7ab0f900010980000002ad93d600051390516083130a980000000004b200013bc0004f6a2f864449542db13806c0000001aad0a480e08819213a2000152220c0000002759b4cc28000376800047a0a445d9a2d0b40a539b26c8ddc653508a63d9623ad0d6af480000ce14b800031600025580001c4000000201c000408000343d972000422937066488a3fda69400081f666b40400056e000000098abdd61f94790446a200027340a6000627a12c000a6121294cd9062120000000f7ac5300020f40002ac1f8974400048212a1ee198a16838380004cc0000e700006bc2e220e1f8c00069400a911979687a0002f28df057206d000000092f2832d584265750001a34a52bba3d4120c7360000a030f800059f00001b54a4c870000b952b2000000000000000000009b4abeb861c680006b440e00034f07940003120630446d06000000000022e05518846ea5510752bb13c6035397af3d3c47646750000c7249005e80019300005318efcef00002a41e9c00000000016743ca43a58f960894ea751b5800167414723d8e80e9e122163076c85274443c8000380747267291115a7ad000249d07c22940619fc00000067da3e57fe78a23fa11c5ee6e459a2a04000746179a8cceaad112f9202c8909964949b159bc00000000003480001ee8ad41e200063780016827fc3a1800000057b00006dd5aea70000000061626b3e700004aec22000348804ca4d12195a89580250000c0c00000000000bcb4c46100000007a00002061f44000000000333c4f40004c6b36556a6c13e1a3dd3aaa1839aa47800000000000000005300eb00016207ed4e1abc567c11c00033b0000b8a000000000091b13c319c10472907b80000005be13b327115031f199800161e0000b21ed473a2c569a0afc34e0000001148c2a0003540ba8bce0c810b9efc000635169a6acc68b3f07481c475e2f20100000c0412846a128c0000002dd152840e1be0000000e2000019ea11000000065823494d25964368000bd644a41d0c08000b310320bf0ac49920b286194ee09726d8000d300925f6800140cc8b689000072200060a1f6c6183e45ef309d95e2aa24d177960ad3f38216a16840000c68000d88abd23a149cfa6bf23bbaf98710b3541d8f6da344fb5e614b855a6fb56502cc422a4b594a4f4cc48c850089a0c64b3d4e8018d5dc02c4c29205160060562b23d8662c14e126e12a80e600b85e93e49730000da44dcb5944c86d56980005d90000000465694b05400000020797d926c4131c2a5d0d2e5dc62b9834630a0e16f80397128eb62e07f809a4514ca972d4b299e5bc19e4458ac91d307c
  | 27 => 0x6099859164b80002be56839188881029b900980017ee00018000002b8230472143054a0002e080000000000000000a70d0c5ed0000d267f626cada51ce2140b90000000b0651c23b006413a43f8000c96a2600000011c6d36000221800000000005a59aca98128800199085c4d3870984a1b15c2348cc0048d536800048400009f03580002b8543a7a4fa07be0000000eca0005461e7d52064d10e006c00007f34f8000a4c82a0bb0780000c5f479916468a6fa2191c3000000000005d00000000002d20cda0002de2bf59aa59535f00000500001988a2066c3cb000000047295a61a3144b54000082b4d40006f22d2145ccce38b35929807b0cba119045d0485c64c7000086a10618c9c3478a59b00000000001150000000dba85034c8000000352184a220728a7800008a87e00000000001a5484d5e11a84ab08b60c48a145e80000000f0856601e132a750cb224a00000007eaa670001818c76c360000a2564400024b25b800039726780000009e62b980c400000065c00000009002cb80012802c40278fe5320b2e5dea494a8a8374fb80f800093a5f980000000004f98ca03c6000428982437a2f15bf8000ca08a03e3b014000cb634880000003e95582dc1640c6800000016e495050f2e1c0000000000eacd583380002b6cd2cc76000183800091106c8d893dc03900018819083791410d80948c8a0001acc3fe88240c8c798c80000fd2050e7a550208a070000a070000541a480004370000c8a00058e06ec00000034f00011025ff00032a0098c492f52eb4000cfc0001a1d378c424c517f158852102ca8555f246f2c60a6175e89c2ad97401fe65137e29a91f08084b0b0645208b902b13bc8421553ee08300788102de8530258a170001d7168c11b363004155e0006a09b6d3824f52a7aa751b0a4619a88080000000000c4400094d29bb4b593a9ba2be24f097408e5f2a9b98e800000018a00004064748898e6461711e190d7dca230002ccccf059a00021a800056447933bc7fe5fb0770d6d74a00000000019c400000000019bea02381883820e72739b971cdf257400019740007ae62e96104e200054fb294000c040000c3429c95300000004e8a3f2b299c80a46472051cf8dee8f108c8a4c000438000030800000000000012d846300016d00000912a494fc8405e931d1640000a5d36f16ac7881aa43e9c18cae6d700012f425e0b04e283a1a069ec37829f1a0a4c75d4867438a53d000231d75400000004094c8c62694232924400038b24a093e67125c8b1c0000000f6872163c1fb0f620b57d41e6374253d16868c5de193886e8b54db9abc000bfd32c28ec28a5b657996c5a1cb8f364ac35228cdb29b0ea1546a4f40ba5451ccaa917210b59ca50367ea7608560233b32e38c14a9416906cc7b4000006ae542f656d1269ea81bc24
  | 28 => 0x49c80019f2ccb05608f93cec523429948562cdd0fc176557475121fa4b857216e00004d573a00f00008288c444762092200000000000000000d1b4180a3101e76029009583aa91033492a0024be21ae09144882080e98a885b010d5dda7e00000000000000000885000027c27a8bd2bc924cc4a57a2822a2800000062581f80001b61872f90d1c0004c5800186aac06799688bca29a00019dc71c0005728000522720112100c3222ee3150000c5e0675df9f2c6380005248001318000098acbd7ce30100e057400000000021918620004efb1548b82e900006e1836a922791ab80003723db28940000000231e6c268348010800123e00054304007d650750d800000000000026a4dc40001a71ad4000aa40f080000000005fdb3a40000000001e3800058b2132bd5872bd55e82d442b2d4011a82a04eac0c51525fc0003a73e4914cfacac3046a4b400027900000014cc4570000000da050f0000b3d4bc0f80000c400b690a0000ff80000005803034c381013980e7c6e88110001aa843c4b0000267400000039c86b00000003660d100284c400015749400001b2349c000460649282da425e662228d0e9a325151a40ccc0000646aa540000003d1af80fe25a33fb98d8a146b43e41e157063ac1bda8c40004b22d000009c600063888748f0b761032e9000061800000012100705e40000fcc0001e3800094a42700000000000004a1b1348ccb0714b33c53ea00065a8000f5858e0002a680004ec0512e0183400018510080000001950000112000000000183c000000000198c5c300002fd94000012c0e7077678646180019c600016d1110cc841d1ef800126aa2e00018441266bb572000016e3b83091b647b20cb0000c8d84c3ec41713f4000b96071b27c00000047f80000005a70b60000976a7e291b4c47a6cf80000000000640324800000000000003251480002478001a04000000311800000051e000036812a26d00004e46dc0000000000141141800ca221a553280000003f430d2928c3ea8e16422fd070000000022c95e2e60000000000c245391d88ba6a0358b05e1072a5b2f200013762034eb17001c800000017696e60fe00006589167c05d700009c424841293b83e2b2420c980d02c28105db10ca125dd38118b01b08a2057a5b4d8415145d0e
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf195450d504c103c70c8a92a09806ad620d5254130095ac42a64a8260cae98644c9504c001e92a4992a0981fb8e19151541300d5ac41aa2a826012b58854c5504c193d30c898aa098003d45453154130024ed41eeaa0260048f8865d5404c0df970edb2280980172e1d942501300266c3b264a026000f89424c9404c00b970eca0a8098013361d93150130007c8a0a62a0260028f687dc565480019cee438aca9001237a0e76551200046ec1cecaa240008df835d954480091b906bb2a8900023de0576551200147a40aecaa240068be87d915448001938e7b22a8900162fa1f7458d200045fc22eca9a40058bc845d953480011ef02bb2a69000a3d2057654d200045fc22eca1a4005cac7655142480b171906aa28490016aba13635092002c7643ac6a1240008bf845cf614800b17908b9ec29000a1f21d65545200145e43ac8a0a40028dc8758d314804353908b1a62900123da1f614c5200157240eca90a40028ec8759521480055c902b2a42900063b219744852001573436c290a4000ae4865452148001ccacaa8a429005f8e19154541202adac41aa8a824006a7a85d8d504800d1f10eb1aa09005eae2116354120004f443a84a824001ae8865095048001e52a8a12a09000378c87715412000739a8ec2a824000f615148550480031f100ba6ca8800e3ba1f725951000672396e2b2a20048de839d954440011bb073b2a88800237e0d76551100246e41aecaa220008ef825d954440071d904bb2a88801a2fa1f64551100064e39ec8aa220058be87dd1634400117f08bb2a6880162f2117654d1000477c12eca9a20038ec825d9534400117f08bb286880022fe1173d891002c5e422e7b1220018fa87dc162440011df04bb2a4880023de05765491001c3e43acaa9220008fb805d942440071790eb2284880021fe15764c9100343e42aec99220008bf845d9324400b17908bb2648800e3721d634c91016d4e422c699220048ee87d89324400b968ecaa28288112e520d545051002d5b426c6a0a20058f48758d41440075c905b2a428800e3d21d654851001d72412ca90a20018f4865d121440075cd0db124288002b9219524851000732b2aa490a2017e386455150440876b106aa2a08801a9ea1763541100347c43ac6a822017ab88458d5044001bc443b92a0880039ad4b62541100347c43ac4a8220009f08750550440035e10ca0aa088003cc5514154110007b0a9242a8220028f8865d520440071f10eb2a4088003e8509414811000df043a429022002de08748520440037c50c90a4088006f8219214811001f70432429022003ee3764852044005bc4ec90a408800b781d9214811001f703b2429022002ce0764852044001bc6ea90a4088003785d5214811000771b2a429022000ee16548520440017c70890a4088002f86112148110
  | 1 => 0xd07bb242a00023760f764854000c5e432e890a80058be87dd1654c001938e9b9aca980030f5d754d91300055cc06a9b22606ca9e86d4f644c0d793ceda9ec89800387d9753d91303654ec1eebb226000c3d751d7644c0d9575003aec8981beae60075d913037d4f418e5b22606ca9d831cb644c00117d0e296c8980022f61c52d913037d4f418a5b226000a9d8314b644c00156d02296c898002ad60452d91303655d400a5b226000ab98014b644c0df53d0638ec8981b2a760c71d91300045f438a3b2260008bd87147644c0df53d0628ec898002a760c51d913000557410a3b226000aad82147644c0d95750028ec898002ae60051d91300045f43843b2260008bd87087644c00147d0a10ec8980028f61421d913037d4f41843b226000a9d83087644c0d95750010ec898002ae60021d91300045ec3cca32260d1e1c53994644c19957301328c8980022fe1d65191306854fc1aca322606ba9c83194644c0d557500328c8981aaa7a1b53191300070e32ea632260cfa9d83988644c19d53b07308c8980022fe1176551300046fc1aecaa260048dc831d9544c0018bea63b2a8980032e900765513002c3e43acaaa260068be87d91544c0df938e7b22a89800637a1b73551306064e326e6aa2606cc9c76d91434c0093390eaa28698002a72195450d3002e4e3b2a8a1a606bc9c73193624c0071b906ba6c4980022fa1f64589300045f438c8b1260058be84dd9524c00117b09bb2a49800637a1b73549300064e326e6a926000c9e431d9424c00717d0fb22849800e3721d654c93016d4e422ca992602dc9c64dd1324c001b3481ba2649800637219744c93035d4f436c8992606cc9c76d91324c0d5938ec3226498003a3193624c930024e643aa499260ade8c64549324c05bd18c8a12649800327193714c93035e4e398c9b0a60028dc835d3614c0d91790dba2c2980022fa1f64585300045f438c8b0a60058be84dd9514c00117b09bb2a29800637a1b73545300064e326e6a8a60058bc841d9414c00193c863b2829800a2fa1f64505300146e43aca98a6021a9c84595314c043938c9ba2629800366903744c53000c6e432e898a606ba9e86d91314c0d9938edb2262981ab271d8644c5300064e326e498a6000e9464d85314c0093a90ea8a6298253a5191514c53010f4a3228298a60058be84dd9214c00117b09bb24298003a9087644853000c6e432e690a601295c855cd214c001938c8b9a42980123ea1b70485300065c326e090a6017cb864dd1504c001b3487ba2a0981aaaea1b645413037e5c3b6c8a8260cdf1853d91504c0d7970ec322a0980038ed9464541300071c328c8a8260ccf1853191504c0014f10caa2a09805f8e19154541300d5ac41aa8a8260cbb5a85dcd504c001d30c9b9aa098006b62194354130095ac42a86a826000
  | 2 => 0xf7454531007a2a9264a8a62048f4865d5414c44b72906aa28298b5ee5a13735053110dca422a6a0a6200f155454d414c40b968eca128298896e520d42505310266a3b264a0a6221b94844c9414c401f0a8499282988063720d75d81310047dc02e9b2a42018f8805d36548401b8842b9ec89081237e1d73d9121006f010ee0b224200a9e83dd164484d9970e121ac8908063ea1f70591210246f41cecaa242008dd839d954484011bf06bb2a8908123720d76551210047dc02ecaa242018f8805d9544840b0fd0fb2aa890803171cf65551210345e43ac8aa24200c9c73591544847f57100b22a890803710877355121006d210ae9b1a42058bf875d36348401ac843baac69081a1fa1f7558d210054f426e6b1a42c5c5c75d0d634840b17d093b2a6908022f6127654d210043fc2aeca9a42068dc8758d534840117b093b286908023760e7650d210043fc2aeca1a420687c855d943484011f700bb286908063e2017650d210347643ac6a9242029e687dc552484053c903b82a49081a3d21d635452101cf343ee4a8a4202b64875495148407ac90ea92a29080a5921d5254521015b3432a4a8a4202b6486549514840dcc90ca92a29081b99dd9525452101eb33b2a4a8a4203d6476549514840dcc8eca92a29080399d8d525452100732b1aa4a8a4200b678054951484073c905b82a2908035954b70545210043fc2ae7b02420687c855cf6048401a38e7b22a8a806a57a1f73551506062e3b6e6aa2a0d6f1840dcd545418f8b8ec39aa8a8003561c073551506af8c200e6aa2a03fb3a84dc15454001ab0e7b82a8a806a9720d54d8d500052ec2e87b1aa000e1d54d0f63540030fd0dbaa86a801a4f21d5450d501fe9c382a8a1aa0068fa86dc143540011bf06ba6c4a80123720d74d89500045fc22e7b12a0058bc845cf62540032f501ba2a4a80035c843715495000c3e432eaa12a01a95c835d542541a963906aa284a80ff4e1c154509500347d436e0a12a00187e86dd5325400d2d90ea9264a80031b1d9524c9500046fc1ae9b0aa0048dc835d3615400117f08b9ec2a80162f21173d855000732a9643b0aa00197a80dd15154001ad441b92a2a800399887625455000c3e432eaa0aa01a95c835d541541a763906aa282a80ff4e1c154505500347d436e0a0aa00187e86dd5315400d2e90ea8a62a80031d1d9514c5500067210cec90aa0058be841d9215400117b083b242a801237a0c76485500046ec18ec90aa000ce4211d921540030f90cbaa42a834b0fdd774595400246f43ee6b2a8000c9f741cd65500d917f08b9ec4a000e2f21173d894001c5e43acaa128031a9c8359542500071bd0fb1a64a00c7a318d424c9403645fc22e7b0a80028bc845cf61500051790eb2a82a0096a720d65505400146f43ec698a8025e946350531500091b
  | 3 => 0x180000c0205c040040800c0803c30068120000203c3837e4f3b481b1aa8c0a9e841cb635518b53b08396c6aa302a7a1071d8d5462d4ec20e3b1aa8008de8708763550011bb0e10ec6aa31697a1421d8d540052ec2843b1aa8c0a9e84087635500153b0810ec6aa002b6a0021d8d540056cc0043b1aa8c5a9d84dc3635518b4bd0a386c6aa3029761470d8d540046f43841b1aa8008dd87083635518b4bd0a106c6aa0029761420d8d546054f42041b1aa800a9d8408363550015ad02106c6aa002b560420d8d540046f43821b1aa8008dd87043635518b4bd0a086c6aa0029761410d8d546054f42021b1aa800a9d84043635500159d04086c6aa002b360810d8d546fd4ec24c431aa8dea9d8498463551ab4bb0b300c6aa377a61026018d540074c3048031aa8b0c9c7418f62550011bd0fb1ac4aa00237a1c63589544ce4e3a0c7b0aa8008de87d8d61550011bd0e31ac2aa317275d363d81543962e3a8c7b02a86bc9e7418f605519193ae831ec0aa10a3721b73581540046f43ec6b02a8008de8718d60551b993ee831ac0aa10b171db735515362c6fc1ae9b12a6c58df835d36154c0b87ce8aa6c0a99be2fe1170d95436de1fbaee8b2a8642c9c76dcd5450d811bf06baec0a180237e0d74d85520246e41ae9b0aa4dac3f75dd165508091bd0fb9acaa10c667a1f735514262e4e3b6e6aa284c8c9c761cd5450801b18e7b92a8a10c6a720d54d8d420062ebaea7b1a8400a9d84d4f6350801c3aa9a9ec6a100e2fa1b7454d4202c9e43aa8a9a8400a9c8355361508011bf06baec0a10123720d75d81420045fc22e1b2a64058bc845c3654c8011bf06bb2a89900327d0c76551320345e43ac8aa264038de86dcd544c8092b90eaa2a69901273a0f745493202476432eaa126431b8c83551424c9b371d09b9a84990b6e3211535093200786aa2a6a1264008df835d362544091b906ba6c4a88163ba1f625095100c3e42ae7b02a2058bc845c365505b187eebba2caa081237a1f735954112ccf43ee6aa282c5c9c76dcd5450591938ec39aa8a0803651cf715514112d4e41aa9b1a8200a9d84d4f6350401c3aa9a9ec6a080a2fa1b7454d4102c9e43aa8a9a8200a9c83553625040b1ed0db8aa4a080a2f219755094112cce41aeaa1282038bc87595425046353906b2a84a08036cc4370509410145f436e899282038de87d8d325040b3590ea1264a08c7a318d424c9410046fc1aebb0282048dc835d76050401d5285906c0a08029760e52d95310045fc22e1b2a62058bc845c3654c4011bf06bb2a89880327d0c76551310345e43ac8aa262028de86dcd544c4092b90eaa2a69880e2fa1f64509310146f436e6a126200d5651dd5324c4051b90cbaa64988039394b654c93101c6e43aca99262049cc87509324c45bd18c8a12649881275a0
  | 4 => 0xb8579dd298420000002387fc879650f60ccbf1e72b8000001920b200000000000000000001e05608680001673c000000ce000e000017c38c9216d0000e45d0c60000009e0000760000000041c600100123122fc190c70f066c650b33a45540000018689ce118200000000087080000dc8000d60f87c1a343a4e40722406a34c2a87f1ee5e49e85730a110811330540002707400a174178d8068660a80e40fa000510001a20008d8eb40045caf8112ac4783088b13a798000242943a8a68d023456ccf000154001068001a811c7009b12e4fce6a072c41b8000000006d400000000000c68000821b4ce0ae0004a000062150000bf800000000000423907e8d09ec000304f181e2a44182e16b000460000ad1128640002d3f67cc0c13026429c4e1d4122000d8894436794a70863a045042172146550679c34403700d1b83fa324ad129416868a292a4240c0e999908c3c891000172160001d51ba898e5873086018d3000000180bba220ec3984c98f00080c2893700003ce092c0004ac460802d0000a988a0007dc2291f31048c409481da87c24a170007f0bd9d843c158580002a23682f1193d4480a014b1a4850159933e407c29800000744d011304a1f0eb08f28c7884b03119662cd48001b2130ca8750000005c2041dc0009a00028e3340502627c000c3079000650080770700e8cf800000000000003e26e81e0000582f4ec800106000110002c67e4011bd2e83f47b000002000002092c26409d0482e23e42518437839c390293c001c4f09502e3fd0b0042203a4be10517600053071414690e305a24e09cf69013766f82d9c4188034e70f334e42d0091d1d000c6d973302214728d70365f4f20092143002a1661406a0109da1ac3d4c18001be1b0d29ab09641c061d744a444820b541e7287d18e198400d70e10ca000bb00024a6d0ed80018a134000a51048440006821c630a79ad2d28545913609e148ab8b10f4284fc1b64260a0db8b722c5a81f9b03d21a40a223000784320903de4b4890002767f85a0f40003f0d10003d02905b1780c6668f580006c0010118a2840010e01d000574561cc1fc6a8118a932e71c4d0002de000af16033a770f71c928250d081df2422343f0fb02a4543312f32217d041c5124014000480104413074000181a02006004010040203c030040c02802038150040a0b002008000000f0000002001000000000100c000040004c02050000981b0004a000010100500c05038090140000c05000080680001405020010001108401008010000c10c06008010000b0200201c160001200401088041580f004000000100c0000001018080040a0000700c0400000010090000002c0001c070040900c0e00c1f00c0403004000050b8020000c00401000010040b014040840a0040102c0002c0000018010000580001806
  | 5 => 0x10c206262524f809f37e7789a8d51de000b81f43ec3b0281ac2f42f0610163ea658a20c80d424c7896740a04cba9030de4241e93830e0b8d7a2106e070930ce4182acd915925c5b000000130000440e2366064380de2c84300400011c5
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x600480449521a0a7008f3c7c000146000b1c015a82a1c8001050d800c4509332006121a093964010ba33aa93005204044a2e000010100c50c18cc32615454d424c84b31498551535053112ce1261424c9414c463c8476509325053100551654215cf64484015c19008573d912100478a6021dc16448401561950877059121006262007359154484015459508773551210057064021dcd54484015259508574d8d2100568640215d36348401166980877558d210055864021dd563485cb91a841cf705515000519654219d921540014e190086764855000439660211d9215400146595084764855000538640211d92154001c1b53900765513035c2725c86551434c001625950876448530005a864021d91214c00181c85191734853072686a1464dcd504c035318985514354130005862595450d504c07fa188655143541300d4d2261524c9504c1c7e086454932541300d4d4261514c5504c1c5e1064545315413018f221d9424c9404c04bc907650531501300149926165545214807fa2886551425412070dc224d5450950480072649859552485101fe8c2195450550441c1710935514154110015382597548520440074e0975952148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2200002099a920073591544840100ed490a322e690a60e58862a0965514354130
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x98a
  | 12 => 0x98c
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x9ca
  | 16 => 0x9cb
  | 17 => 0x9cd
  | 18 => 0x9ce
  | 19 => 0xa0a
  | 20 => 0xa0b
  | 21 => 0xa0c
  | 22 => 0xa0e
  | 23 => 0xa4d
  | 24 => 0xa4a
  | 25 => 0xa4b
  | 26 => 0xa4c
  | 27 => 0xb09
  | 28 => 0xb0c
  | 29 => 0xb0d
  | 30 => 0xb0e
  | 31 => 0xb49
  | 32 => 0xb4b
  | 33 => 0xb4d
  | 34 => 0xb4e
  | 35 => 0xb89
  | 36 => 0xb8b
  | 37 => 0xb8c
  | 38 => 0xb8e
  | 39 => 0xbc9
  | 40 => 0xbcb
  | 41 => 0xbcc
  | 42 => 0xbcd
  | 43 => 0xcc9
  | 44 => 0xcca
  | 45 => 0xccd
  | 46 => 0xcce
  | 47 => 0xd09
  | 48 => 0xd0a
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0xd49
  | 52 => 0xd4a
  | 53 => 0xd4c
  | 54 => 0xd4d
  | 55 => 0xe89
  | 56 => 0xe8a
  | 57 => 0xe8b
  | 58 => 0xe8e
  | 59 => 0xec9
  | 60 => 0xeca
  | 61 => 0xecb
  | 62 => 0xecd
  | 63 => 0x1049
  | 64 => 0x104a
  | 65 => 0x104b
  | 66 => 0x104c
  | 67 => 0xa4954
  | 68 => 0xb8954
  | 69 => 0x1549
  | 70 => 0x1409
  | 71 => 0x150a
  | 72 => 0x128a
  | 73 => 0x16c9
  | 74 => 0x1449
  | 75 => 0x168a
  | 76 => 0x12ca
  | 77 => 0x1849
  | 78 => 0x1489
  | 79 => 0x180a
  | 80 => 0x130a
  | 81 => 0x19c9
  | 82 => 0x14c9
  | 83 => 0x198a
  | 84 => 0x134a
  | 85 => 0xa4994
  | 86 => 0x138b
  | 87 => 0x124b
  | 88 => 0xd0994
  | 89 => 0x1709
  | 90 => 0x15c9
  | 91 => 0x168b
  | 92 => 0x12cb
  | 93 => 0x1889
  | 94 => 0x1609
  | 95 => 0x180b
  | 96 => 0x130b
  | 97 => 0x1a09
  | 98 => 0x1649
  | 99 => 0x198b
  | 100 => 0x134b
  | 101 => 0xa09d6
  | 102 => 0x138c
  | 103 => 0x124c
  | 104 => 0x150c
  | 105 => 0x128c
  | 106 => 0x589
  | 107 => 0x10c
  | 108 => 0x1789
  | 109 => 0x18c9
  | 110 => 0x180c
  | 111 => 0x130c
  | 112 => 0x1a49
  | 113 => 0x17c9
  | 114 => 0x198c
  | 115 => 0x134c
  | 116 => 0x138d
  | 117 => 0x124d
  | 118 => 0x150d
  | 119 => 0x128d
  | 120 => 0x168d
  | 121 => 0x12cd
  | 122 => 0x1a89
  | 123 => 0x1949
  | 124 => 0x198d
  | 125 => 0x134d
  | 126 => 0xbca55
  | 127 => 0x138e
  | 128 => 0x124e
  | 129 => 0xd4a55
  | 130 => 0x150e
  | 131 => 0x128e
  | 132 => 0x168e
  | 133 => 0x12ce
  | 134 => 0x180e
  | 135 => 0x130e
  | 136 => 0x170a
  | 137 => 0x15ca
  | 138 => 0x16cb
  | 139 => 0x144b
  | 140 => 0x188a
  | 141 => 0x160a
  | 142 => 0x184b
  | 143 => 0x148b
  | 144 => 0x1a0a
  | 145 => 0x164a
  | 146 => 0x19cb
  | 147 => 0x14cb
  | 148 => 0xbcb55
  | 149 => 0x154c
  | 150 => 0x140c
  | 151 => 0x18ca
  | 152 => 0x178a
  | 153 => 0x184c
  | 154 => 0x148c
  | 155 => 0x1a4a
  | 156 => 0x17ca
  | 157 => 0x19cc
  | 158 => 0x14cc
  | 159 => 0x154d
  | 160 => 0x140d
  | 161 => 0x16cd
  | 162 => 0x144d
  | 163 => 0x1a8a
  | 164 => 0x194a
  | 165 => 0x19cd
  | 166 => 0x14cd
  | 167 => 0x154e
  | 168 => 0x140e
  | 169 => 0x16ce
  | 170 => 0x144e
  | 171 => 0x184e
  | 172 => 0x148e
  | 173 => 0xd4cd5
  | 174 => 0x18cb
  | 175 => 0x178b
  | 176 => 0x188c
  | 177 => 0x160c
  | 178 => 0x1a4b
  | 179 => 0x17cb
  | 180 => 0x1a0c
  | 181 => 0x164c
  | 182 => 0x170d
  | 183 => 0x15cd
  | 184 => 0x1a8b
  | 185 => 0x194b
  | 186 => 0x1a0d
  | 187 => 0x164d
  | 188 => 0x170e
  | 189 => 0x15ce
  | 190 => 0x188e
  | 191 => 0x160e
  | 192 => 0x1a4d
  | 193 => 0x1a8c
  | 194 => 0x194c
  | 195 => 0x17cd
  | 196 => 0x104ed1
  | 197 => 0x18ce
  | 198 => 0x178e
  | 199 => 0x5cd
  | 200 => 0x58e
  | 201 => 0xb4a55
  | 202 => 0xcca55
  | 203 => 0x5c9
  | 204 => 0x10a54
  | 205 => 0x130a54
  | 206 => 0x58b51
  | 207 => 0x58cd1
  | 208 => 0x59a51
  | 209 => 0x198114
  | 210 => 0x1a9951
  | 211 => 0xb8a54
  | 212 => 0xd0a54
  | 213 => 0x5ca55
  | 214 => 0x1a4a55
  | 215 => 0x58a
  | 216 => 0x1a9952
  | 217 => 0x58b
  | 218 => 0x1a9953
  | 219 => 0x1a9954
  | 220 => 0x59316
  | 221 => 0x1345d5
  | 222 => 0x58b96
  | 223 => 0x58d16
  | 224 => 0xb8a495c
  | 225 => 0xd0a499c
  | 226 => 0xbcb4a5d
  | 227 => 0xd4cca5d
  | 228 => 0x585d1
  | 229 => 0xa4114
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1431
  | 6 => 3397
  | 5 => 552
  | 4 => 44
  | 3 => 3
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (58194+((h/477+packedAt gbK7 (52947+(h % 477)*11) 11) % 1718)*12) 12
  | 6 => packedAt gbK6 (177772+((h/1132+packedAt gbK6 (163056+(h % 1132)*13) 13) % 4484)*13) 13
  | 5 => packedAt gbK5 (34408+((h/184+packedAt gbK5 (32568+(h % 184)*10) 10) % 663)*11) 11
  | 4 => packedAt gbK4 (3164+((h/14+packedAt gbK4 (3080+(h % 14)*6) 6) % 53)*7) 7
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe3811c1c01c71c063fff8ff83ff0664810f3cf
  | 1 => 0xfc01e01ffe07e007c703f1ffc1f1880e634cf3
  | 2 => 0x1ffe01ff80007f803fe3ffe061071838f3c
  | 3 => 0xfffe00001ffffff80003ffc000081f81fc0fc0
  | 4 => 0x1ffffffffffc0000000fe001fff000
  | 5 => 0xffffffffe000000000000000000ffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa0a50505004104100948824825202648101145
  | 1 => 0x44082008ca0620a24211109280c08802614492
  | 2 => 0x1048c0158801449022242518021011828a28
  | 3 => 0x691c004046d34870000bc9018c601a80b40fc0
  | 4 => 0x4002829924938724b00006108fc0014be000
  | 5 => 0x926193130000020000c00000210d656c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffefffcffeae8e8fffefffcffeae8e8fffefffcffeae8e8fffefffcffeae8e8fffefffcffeae8e8fffefffcffeae8e8fffefffcffeae8e8fffefffcffeae8e8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_33196
namespace PEqualNP.Outside.L_meta_33196
open PEqualNP.Outside.L_meta_33196.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 60 := (concat bs1_4_0 bs1_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 40 := (concat bs1_5_0 bs1_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 60 := (concat bs2_4_0 bs2_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 40 := (concat bs2_5_0 bs2_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 9 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 50 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_128 : Interval s3Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 136 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 48 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 9 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 50 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_128 : Interval s4Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 136 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
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
theorem bs5_4_64 : Interval s5Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 91 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 44 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_544 : Interval gbAtlas 5 544 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 552 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)))))
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
theorem bgb_6_3392 : Interval gbAtlas 6 3392 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3397 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)))))) (concat (concat (concat (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528))))) (concat (concat (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)))) (concat (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)))))))
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
theorem bgb_7_1408 : Interval gbAtlas 7 1408 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1431 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672))))) (concat (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832))) (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))) (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 32, 40),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffffffffffffffefffeffeaeaeafffefffefffefffefffefffcffeae8e8fffffffffffffffffffefffeffeaeaeafffefffefffefffefffefffcffeae8e8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 12 := by
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 12)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 12 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_33196.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.or,[7,1]⟩,⟨.or,[6,7]⟩,⟨.or,[2,8]⟩,⟨.or,[1,8]⟩,⟨.or,[6,4]⟩,⟨.and,[5,12]⟩,⟨.and,[3,0]⟩,⟨.and,[9,13]⟩,⟨.and,[10,11]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,20,monoShape,by change 13 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_33196

open PEqualNP.Outside.L_meta_33196 in
theorem PEqualNP.Outside.L_meta_33196 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
