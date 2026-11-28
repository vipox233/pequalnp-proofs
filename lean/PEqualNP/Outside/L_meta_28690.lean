import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_28690.Model
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


end PEqualNP.Outside.L_meta_28690.Model

namespace PEqualNP.Outside.L_meta_28690
open PEqualNP.Outside.L_meta_28690.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_28690

namespace PEqualNP.Outside.L_meta_28690
open PEqualNP.Outside.L_meta_28690.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x8002600400000fb10f610f410f810f010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x4100c801580b725084364a8086c55010e929821d153043c4a4087854810
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x40403115454c10c855152043415354810
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 5
  | 3 => 7
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
  | 4 => packedAt s0K4 (84+((h/1+packedAt s0K4 (80+(h % 1)*4) 4) % 13)*4) 4
  | 3 => packedAt s0K3 (197+((h/2+packedAt s0K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt s0K2 (117+((h/1+packedAt s0K2 (114+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x78f0f1ff0f1fff1c78e0f1c1fc707ffcc3333f
  | 2 => 0x80ff01fff01fffe07f00fe01ff807fff0c3c3f
  | 3 => 0xfffe0fffe0f8ff8000fffe3fff8e000fcfcc
  | 4 => 0xff00000fffff00ffffff00003ffff003f00ff0
  | 5 => 0xfffffff0000000ffffffffffc0000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x111a42a1682a501c282a5054541512a8c31315
  | 2 => 0x6224a5428654a0e05114a228a88a25530c2c2a
  | 3 => 0x14422064220601248000348c0d23081805454c
  | 4 => 0x20044988440032491a460000324c4061500ab0
  | 5 => 0x408880008898c4926498c93100000182aab000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xffffffc0ffc0c0c0ffffffc0ffc0c0c0ffffffc0ffc0c0c0ffffffc0ffc0c0c0ffffffc0ffc0c0c0ffffffc0ffc0c0c0ffffffc0ffc0c0c0ffffffc0ffc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_28690
namespace PEqualNP.Outside.L_meta_28690
open PEqualNP.Outside.L_meta_28690.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x3e8930054bc50e3024a164a5c99e485402334b88ad1a9c580020091d38000084200d80001081900001800000002000000600002ac00a07a90eac000000100018000000000000000000000000018012000011450004ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21f621fd21f521fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10f610fd10fc10f410
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x138001a34804c43e328e0560c3a9300000401080e540009cb40007878da00001a046523800014000000094572880022870b8d82685130d0000000000cc000a8007200001ac004f0286000211412c9a6400164000000038e2002490c00003b000be000021816000000000483380074443e8a508311a8000000318007e45418000025020000003000003a823e000f20000170001f390008c00398004000080c878000015800001b8b8001c2e834581b041848e003c16cd47f37008ee243a180241640800762a0a0005e7b3f1e86022281b0b05319818326f20024aa2d208f4bc0002000b0712040a0200020000020a000605000518000001070500050400000105050004380001270100000300bb28c87755190edca421db54843bb28887755110ef4a021de54043bb28c85755190abca6215754c42bb28885755110af4a0215e54042bb28e657551ccaeca3195d546329faa2653c544ca7ca8194f55032e69906576510caeaa2195e94032bca80657a50d06f2a1a0dd54e31baa946376508c7aea698ddd4931ba2826376510c6eea710dd54e21baa94437650886eea690dd54d21f3a92437450486eca210dd94740baa8e81b651d036aa3a06d8c740da98e81b621d036a43a04f55240bba8a8174515036ea2a06d14540db18a81b5315036c42a06d48540dda82813e54102eca3985d54730ea98e613e548c27aa9186e50230bba8a6174514c3aa62986e501309f2a0613d540c2dca4185b54830bb2886175510c2eca3905d54720f290e413e548827aa9106e50220bba8a417451483ca42906e501209f2a0413d54082bca6105754c20bb2884175510837281884f952109eaa421b6548436aa9085dd4e10baa9c217752842eaa5085d94210dba0421b5408427ca8084f55010af298215d53042dca4085b54810dca0021b6540436aa8085dd4c10eb298217553043aaa6085554c10bba9021e652042eaa4087954810b2a90217650043e4a0086dd0010f920021b540043e280086c50010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xc30480264abc3ac606458a3e1101500c48ab00411800000b94486968054589800c9cd8050000000000f0802007831a004823a8570e0aa51003816008020028000002c204000401c8e580544cb0d544c832d24c9500ca6562141319c18153486556314121ac18131502b06048540ac98750503305150130e44c5404c3305150120e848540483195350010ca549400426562d4c109559653043165454c10c5551530425563d48109959652043455394810c995152043255454810d194d52043455354810ac592500423565d0010c554f400432552d0010ac59240043515390010d854a40042376550010c554d40043255250010d454d40043615250010acd9540043336550010ccd4d40043925350010cc54d40043915350010c454d40043335250010e894940043315250010e854940043215250010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc8110a000c20380121285c8604c540922e630242a052172d4d4004288baca6a0021445cf5250010a42eb292800870153949400438129aa4a0021c054d5250010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (880+((h/16+packedAt s1K5 (768+(h % 16)*7) 7) % 82)*7) 7
  | 4 => packedAt s1K4 (4032+((h/45+packedAt s1K4 (3672+(h % 45)*8) 8) % 198)*9) 9
  | 3 => packedAt s1K3 (2012+((h/16+packedAt s1K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s1K2 (453+((h/3+packedAt s1K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x78e3c71fcf1ffff11c70e387c71ffff2130ff
  | 2 => 0x7f03f81ff01e3c7e1f80fc07f81c71fc63c93
  | 3 => 0xf8003ffe3ffe03f8fe000fff8ffe07e007cf1c
  | 4 => 0xffffc0003ffffc00fffff0000ffff800f80fe0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40c04602048281001081440a10106188211025
  | 2 => 0xb12c89658a654688e148aa452c8c9256c62c92
  | 3 => 0x10211020902048012200029105240442024518
  | 4 => 0x2204010920400092445220000a491004480ac0
  | 5 => 0xc44822400289932499a4cd2640002098b5b000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xffffffa0ffaaaaa0ffffffa0ffaaaaa0ffffffa0ffaaaaa0ffffffa0ffaaaaa0ffffffa0ffaaaaa0ffffffa0ffaaaaa0ffffffa0ffaaaaa0ffffffa0ffaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_28690
namespace PEqualNP.Outside.L_meta_28690
open PEqualNP.Outside.L_meta_28690.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x34324346001550002090000000069800a3eb0000008401444009235aa441e0074019000060b009c716005cdab26442af38a8087009410000417201e0014000020848108000064c68526ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21f621fd21f521fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10f610fd10fc10f410
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1d4a2040a8000630000b08000378004a001903c00000006000211586c0a77071fcb4861aa1c8200210d1007e0017c3836348006e2e38028900237090bc000000000000021400270000022001c800c000000000000000000006298a0703e3582434001e9480214279c400000000000000020c885400000004d3a184f40000210526d038c4001d1d1a0ce0000000b27d251d8aa1617888f85c231749208131e4ac4e3908c9862228cc5a190004c96000f198e63c000002e0000000000b00031045b10000ae781f90c007b00194206a00001021206990b02a0f8ec8e00281b0c60002000d070014040000061100000004030305000507000000050307000600000b050003030308070101090105bb28c87755190edca421db54843bb28887755110ef4a021de54043bb28c85755190abca6215754c42bb28885755110af4a0215e54042bb28e657551ccaeca3195d546329faa2653c544ca7ca8194f55032e69906576510caeaa2195e94032bca80657a50d06f2a1a0dd54e31baa946376508c7aea698ddd4931ba2826376510c6eea710dd54e21baa94437650886eea690dd54d21f3a92437450486eca210dd94740baa8e81b651d036aa3a06d8c740da98e81b621d036a43a04f55240bba8a8174515036ea2a06d14540db18a81b5315036c42a06d48540dda82813e54102eca3985d54730ea98e613e548c27aa9186e50230bba8a6174514c3aa62986e501309f2a0613d540c2dca4185b54830bb2886175510c2eca3905d54720f290e413e548827aa9106e50220bba8a417451483ca42906e501209f2a0413d54082bca6105754c20bb2884175510837281884f952109eaa421b6548436aa9085dd4e10baa9c217752842eaa5085d94210dba0421b5408427ca8084f55010af298215d53042dca4085b54810dca0021b6540436aa8085dd4c10eb298217553043aaa6085554c10bba9021e652042eaa4087954810b2a90217650043e4a0086dd0010f920021b540043e280086c50010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x31b3e3d380008570d3400005481c09d183811c00a15000048000328d615000000900bcc003cac0112e00231268169460411164a98500002c18852001029316241850e0000306000818e580544cb0d544c832d24c9500ca6562141319c18153486556314121ac18131502b06048540ac98750503305150130e44c5404c3305150120e848540483195350010ca549400426562d4c109559653043165454c10c5551530425563d48109959652043455394810c995152043255454810d194d52043455354810ac592500423565d0010c554f400432552d0010ac59240043515390010d854a40042376550010c554d40043255250010d454d40043615250010acd9540043336550010ccd4d40043925350010cc54d40043915350010c454d40043335250010e894940043315250010e854940043215250010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x20cc81000509c611285c8604c540922e630242a052172d4d4004288baca6a0021445cf5250010a42eb292800870153949400438129aa4a0021c054d5250010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (880+((h/16+packedAt s2K5 (768+(h % 16)*7) 7) % 69)*7) 7
  | 4 => packedAt s2K4 (4032+((h/45+packedAt s2K4 (3672+(h % 45)*8) 8) % 198)*9) 9
  | 3 => packedAt s2K3 (2012+((h/16+packedAt s2K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s2K2 (453+((h/3+packedAt s2K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x78e3c71fcf1ffff11c70e387c71ffff2130ff
  | 1 => 0x7f03f81ff01e3c7e1f80fc07f81c71fc63c93
  | 3 => 0xf8003ffe3ffe03f8fe000fff8ffe07e007cf1c
  | 4 => 0xffffc0003ffffc00fffff0000ffff800f80fe0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40c04602048281001081440a10106188211025
  | 1 => 0xb12c89658a654688e148aa452c8c9256c62c92
  | 3 => 0x10211020902048012200029105240442024518
  | 4 => 0x2204010920400092445220000a491004480ac0
  | 5 => 0xc44822400289932499a4cd2640002098b5b000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffff88ffaaaa88ffffff88ffaaaa88ffffff88ffaaaa88ffffff88ffaaaa88ffffff88ffaaaa88ffffff88ffaaaa88ffffff88ffaaaa88ffffff88ffaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_28690
namespace PEqualNP.Outside.L_meta_28690
open PEqualNP.Outside.L_meta_28690.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15a316440000000aa700282190a7868006904072424d1f0000021504c7013000000007432900500202c94b804c6d500384060244007800000004040100b083103043ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x480c0000fca13150800158013800000000010401644d0074000000002454012c000001100068007c000000cd1800c928314c0000e000f91c88002c9800e80000ec000000002800f4b54470010c8c78345920e42008013d5cc0385d08c49c8418154160b8f000bd25491490a850d0a41c44b0dc609400106c000440d801543d6934ac64d4040000000a040412020008000422040202020404100000000842020002013e5390e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110f6aa221ee940439ea8087b95010e72a021d794e42aea9c859c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a655e53906baa720e710f31b7296636d52cc67ca918cf552319faa2633c544c7388698cf950219eaa0435e53086baa610f948421bd2804379500867ca7a04f55240afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f950409faa6613c54cc27ca9184f55230ce21c61b9408c27ea8984f15130dca02613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a4413d54882eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9084f55210b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x60000c00eb9c880400226014580280c0400000000000002a092780900a2c8066800810000c00b255254443ca9495010f295254043cc9455010f315154043a658043ccb144354732a6580434ca996010f31c310d52cc6996010d31d8485500870e6214d40c358853503166114d40c558453503196014d40a6580438c29863502308e195404c21d6510c30c310d520c31443544308718d548821c6355210
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8c0000500001445c04354732a12e021aa598e05625845350304b12c029a81845856014d40
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2697+((h/30+packedAt s3K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s3K3 (998+((h/8+packedAt s3K3 (950+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s3K2 (249+((h/1+packedAt s3K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 1 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 2 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 1 => 0x52228891414810a0521244248449414612512
  | 2 => 0xaa444512412900354802489092092941828a28
  | 4 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8ffffe8e8eaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_28690
namespace PEqualNP.Outside.L_meta_28690
open PEqualNP.Outside.L_meta_28690.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x920000000001801d285c000002d1264aac01c0430010003d38a368d48400200112aa0016340150532901981a780200e01089007c0131c340000084040000280003ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2504004000000079280c0000e8e0a400d134000000011560000000852c6000fc000000cc01500110bcc8c40064008c00000000000001394ca000002c013d545c00000000b8ac00ec000000000000140000014800700000008800015c7cf0005800509800015920f8005434009400189c1c6cb4c001186800d50c800000000000d84d1c28100090b030484420f43c3804e5014568000001080000014000a800000001240000013000dd647400080000000408021c00120002040006000800000812000000000a000a00000212053e5390e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110f6aa221ee940439ea8087b95010e72a021d794e42aea9c859c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a655e53906baa720e710f31b7296636d52cc67ca918cf552319faa2633c544c7388698cf950219eaa0435e53086baa610f948421bd2804379500867ca7a04f55240afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f950409faa6613c54cc27ca9184f55230ce21c61b9408c27ea8984f15130dca02613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a4413d54882eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9084f55210b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xa230e930b8002612872c81828001e016500006000008a8001a40048008008600147255254443ca9495010f295254043cc9455010f315154043a658043ccb144354732a6580434ca996010f31c310d52cc6996010d31d8485500870e6214d40c358853503166114d40c558453503196014d40a6580438c29863502308e195404c21d6510c30c310d520c31443544308718d548821c6355210
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1008004000c0001445c04354732a12e021aa598e05625845350304b12c029a81845856014d40
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2697+((h/30+packedAt s4K4 (2457+(h % 30)*8) 8) % 176)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (249+((h/1+packedAt s4K2 (245+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 1 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 2 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 3 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 1 => 0x52228891414810a0521244248449414612512
  | 2 => 0xaa444512412900354802489092092941828a28
  | 3 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_28690
namespace PEqualNP.Outside.L_meta_28690
open PEqualNP.Outside.L_meta_28690.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630bea8c617e508c3f481187e50230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3be6298774c530fd20261f9404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec82887d50510fb18a21f531443ec42887d48510fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ee21e657e51ccbeca3995d94732bea8e65f551ccaeaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a89977d0d32ee21a65ee424cbda84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83be43d077887a0df94b41f7296836e52d06faa5a0fb54b41b6a9683bf42d077a85a0df94341bea86837d54906fca720f794e41af29c837d53907baa720d754e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f7d0f31ee21e637e52cc7dca598db94b31bea9663ed52cc6daa598f7ccb31ee996637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf294637d528c6fca318fd90631faa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7b88698dfd4931be29263df324c7ba6498fd90531faa0a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fd90721faa0e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887dc8510fb50a21f719443ed32886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821f721043ed42087dc6410fb4c821bf28843f641087ea8210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9
  | 2 => 0x2340005e000000189af1c6001228000000007b0000000a0e20000004c80000000047400000190000ec2a4000168710003d6824a79dd000000001510000012389c4b4000001562d4470000df2b8618000000004bc000000009c40023700013040800000080db1f42dc5180916c0007cc73a3550641c9712d54a944cc0000009f151800000aa08c88b000600000000008904187b00017c0023b234a140e0002d2000000000ea0000580048482c7f8003b21ac0026b16e54d040e5000420029aa00000000000000000001bc49e0d46c1131ea7504291709aa5518000000a452a0002880014024c00000000000000000e40aa14673d118001641593d26933a354288960004d8749db3b8020789314720008795508a85ce9952478300000003d02cd172220c219c7720e13c5e017a4e54486cc5a2a0326454d8004c4504ca9452ae0007a0002b672800234000000000002401c0c10000002600005c03c77c000000000fccf16b382200000004e00000394e000000001bd00000064838000254000d644e1b90503635a665320870da400001153989a04118318646c5a16442c5c5370af40e9ec5c9c01a20010794247c6ecfd09a2fe974000001208040000039c000920fd000595158cc52e640b80002305ec3494907c7b0328000128506d0a903603c00266000000010000103001020000140001803004000180801c1001415004020240301c00000050040c0000104c0301002000000041a00000004030000101802000010080400400000070000001c000e8020001c0280101004018070040000c010940b03003014030140f00402000000800100401000090040e0040700000004000340003400028000041500002030000002a004000000001000000000000400400004000101402000034040041204400000000080000c0900c0300c02000030080d00c02000000140e0000402c1e054010000000000008110000101012000000040002c01004040000b014000080005c1c00c0002811014010080b0140e0000000400000060040406c04008000340300c120042100003000070040200001042fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443fb28887765110efaa221fd54443baa88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85be43d0b7887a15f94742fb28e857651d0afaa3a17d54742baa8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857
  | 3 => 0xc146c9b4f1206272000a19fc4a4a24000002fc0011d0e451a36cfc15f0008b4000001c23e8000000004400001f1500009b844196580a80f33120013020d074920e68bd1707f82d8004bea50d290901a3103ba752da0ac5d93c51e520bc85802a33c2aa2031a68ceb28b352684ea9a44ae6f8030621083dc58a6a008000d0000000a40960c7000578822931d4904d321a19c7841621e27405c561273de430958000040003009204ea700014d00047cdb800042a64000003ee0014fa7d0006680026c020928570000000000018f0000000992a22c0010c08a122399490b636a7c8000dc0fa000002550000000010b3181d07e000000a1800000000000279e02ce00000079000000000000000000020045e1392c28c280000e90941e40442084049a14c0000048c0000007f000000b99de206000342770002fc0c0000000014c0720004280010e0000012c8001d8000000003669f8b325e00099c0013f3d43e43222840a0013900044229cd38000004e00009b3b44843f2763580010f8000005d00026303a000000000005680000055266c282a105c34801854000434ca0004327147580028e00000282000000aa1974968306115d0906e4c200e488855328930547b4000330003792b17c0b279cdc0002c4118449bf38c000001f1000000001d1000000001633640006b9b40a4294bb0423ae72cc08341f0364001f50002c00009d2ee8c89128a0349d01e82d2f44510e135064124b087a078220b41344fe6894b2433925f46a06a06e0004b9930000002388e1560000025b178000000fe424001308784086ac5103b3a071c001ff0000013c93b1e0790001b13f2000000003c6000f80005080000000000041800000000000fb0e8000128000e00008c49829e0003403300002c56456aa03388411e8000721c41197500080c63025310000000000006e8110ef0483b48280a30e7989eaa60526b899800000a744f87c3606a0cf8dd44c874318b53fa7b9281580965bcc9000000a0509a532980000006f384328360000000000005701800114800000001438be51c4f86281400000047a380000000008c000000430000002905d000386528932332507953780004c001398003f6844508003d2000000a00e6004000cd000000002780ba001441720604482198e0ec404c2a3f2968b08f2a7314445248005346584c9231f68952e00000029800000252000928d3404409200
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x514823d64145209798c514825d6314520cd99051483356414520d598c51483556314520d990851483654214520d98c851483653214520dc580514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020b9185200836551480209ed95200837151480209798f54c425d63d53109b98a54c426d62953108f99353c423d64d4f109b98a53c426d6294f108f99052c423d6414b109798c52c425d6314b10b558e41c42b5648c710d914921c425f63552109718d548425e63152109758c548426e62152109b588548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e6414a108f590528425e6314a109758c52843675208610bc58021843e02188210bc18520843e321482109b98a544426d629511097d8d544425c63551109bd89544426c62551109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109b98a524427761549108f990524423d64149109798c524425d63149109b994524432e6414910cb590524434e6314910d358c52443656114910da58052442d56390510d914a41442746550510d914941442b5648c510d914a3144274654c510d914931442766588510d914a21442746548510d914921443685288110f888620442786548110f8485204436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109e980520427565c8410cd553210435553c8410d954b21042756508410cd55021043555308410d954821042f16008410cd553100435553c4010d954b10042796584010da54a10042776544010cd55110043555344010b9189100436552440109ed9510043695244010
  | 1 => 0x873a5454021ce551500875a5354021d654d50087e12154021da90950087694254021da8c950087693254021dc90550087714154021dc8c550087713154021dac8550087722154021da48550087712154021d8485500865e6394b409758e52d02b561d0b409798e51d025d6394740ab58b41d02b96010e409dd8552902746154a409bd89519026c62546409b988535026d6214d409d98453502756114d40d3988535034d6214d40d598453503556114d40d6580535023e65d0d40c714f435031c5350d40c714f42502b561d0940c714d425031c53d0540ab58b415031c5350540c714e405023d6590c40c754e431031d5310c40ae580431034e5394840d354e521034e5354840d354d521032e4354840cb10d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103364354440cd10d511031d53d0040cb54b401033551d0040d654e401023f6550040a718d401031d5350040cb549401033551500409ed95401035953500409b98854cc26d62153309d98454cc2756115330c715143cc23e6494b308f59252cc2d561ccb308f99251cc23d6494730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b6580438c2776154a309d185528c26f62546309b189518c3984390230b618d408c39b43502308f992544c25f63551309b988544c26d62151309d984544c27561151308f994544c31d6315130cb988544c32d6215130cd984544c3356115130ce580544c25e6590d30c7152434c25c6550d30c7151434c31c54cc930b5587324c31c544c930c7153314c2cd62cc530c7151314c3385490130e690e404c2786550130e650d404c31c548c1309b98b540c26d62d50309d987540c27561d50308f596540c31c63550308f990540c25e63150309b988540c26d62150309d984540c27561150309e980540c25d65d0c30c7553430c25d6510c30c7550430c2d96010c30cb952520c32d5494830cb951520c32d5454830d3d0d520c34c4354830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430c7553300c34d52cc030d5547300c339548c03097d95300c29c644c030c7551300c34d524c030d5545300c27b654c030ce551300c25e63d53209758f54c827661953209d58654c823e64d4f208f59353c82766194f209d58653c82cd6390b20ab59232c825f63552209718d548825e63152209758c548827661152209d584548823f6454e208f191538823e6414e208f59053882766114e209d58453882e960086209d9865448275619512097d8d544825c63551209dd85544827461551209d98653482756194d208fd91534823c6454d209dd8553482746154d20b358e424826c6550920ab592324826c654c9208f99
  | 2 => 0x6494732cd59251ccb574354732d510d51cca7661952329d586548cb2e6295232cd986548cb356195232cb951428cb1e54cca32b9987328ca7661951329d586544ca5e65d0d32c7550434cace6210d32b5584434cad96010d32b398e424ca6c6550932e310d424cae661cc932a7992324ca3e64141328f590504ca7661141329d584504ca5e63d50329b988540ca7661150329d584540ca7a60150329e580540ca3e64948328f592520ca5f654c8329bd95320cb1d5310f41ab58843d06b96010f419798e52d065d6394b41d398e52d074d6394b41cb90d52d072c4354b41cb94942d066e6294e419b58a539074e6294e41d358a53907566194e41c794f41906e662d0641ab58843506b66110d41ae58043506b661d0941b998b415069e63905419798c505065d63141419b988505066d62141418fd95411067765504419b98b54cc66d62d53319b98854cc66d62153319e98054cc6796015331c755043cc6cd6210f31b658043cc63e6494b318f59252cc72e6494b31cb59252cc74f4354b31d310d52cc74e524cb319b98a548c66d6295231cb98a548c72d6295231cd986548c7365450631c7953318c6e662cc6319b98a544c66d629513197997434c71d5410d31b3588434c6d66110d31b6580434c6d661cc931b598e414c6746550531e510d414c6e662cc531a7992314c63e64141318f590504c66e62141319b588504c65e63d50319b988540c66d62150319d984540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c65e63d53219758f54c863e64d4f218f59353c86d56390721ad59231c865e63d52219758f548863e64d4e218f59353886cd6390a21ab592328865e63d51219758f544866d62951219d586544863e64d4d218f593534866d6294d219d586534863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d6595021cb98a540873661950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a53087566194c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530866d6590821b358e420874d5390821b9586420872e5450821d354d420866d658c821ab592320872d548c821b9586320872d544c821d394d32086756590421b558e41087555390421b958a41087365450421d554d41087a542504219d59631086b5648c421cd55231086e5628c421cd5513108756534c421f14c931086e562884219bd9521086776548421b9d9521087676548421b9d9121086e56448421e995121087a55448421b9d8d21086e56348421f194d21087c55348421b9181210873a5494021ce552500875a5394021d654e50087e12194021d9485500
  | 3 => 0x4000692e45283d0000005d460800000728000004f80003105343835cf29232e05045d22e3320001b00019a354598340005300e8d60000009e2052f400077244000a1c000000000000003e20c0001009f0006254d8950000000000000000000214276964c211b1f40480003714289c301bd350554071a04fc3e4001274d48d8b41f843644c001de3ae3ac3a2251be01c191bc20898c5aaa921c0004e0000a80002f0e82888fc4125d1589186d0f1558000400000141d8c1800000ab4941b94fe5f1661455a473146090094000901d20000014710a3582c46d8713e2a5c04191352095041da00055cd58002bc139292303008100000027200016000000b00000000000007626b3165955d2b34d00003f8004da000cf24c022660000de00000000197554000001a10005dc399350009595a88a59259c6a00d11e2b5452671fc864dd8014e869d1e1af0b27911da321a6a7c132cb2205f80018a3844e074851000000010040300001008000240100406000080081400801000000000100c0001000000000140400402040010000001c0e0000000000024020080a01001000010400200804000000141501c010000300c05008050040a00c0000c0201c0201c320140100c080300001c2d0440901c08008000440e0140100c0000013000000040001000000070040003006008100302600005000110300400404008020140a004000780400803040030000e064020280802c0a000020200100c0102c01000010100c0000a0200f018090ec200040d004000000000404028060280100015010020540702c020000100001060060041000415000010000f01c0a00c0d0301200c050100000803010000040101c000380a01c00018000040d0000201803024030140201005050120000e0140000c010027661d49439d5875250e6e62d45439b58b5150e6e62141439b5885050e7661141439d5845050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9f6150c43a71814310f8d4394843e350d5210f954394443d994a5110f655294443e550d5110f665254443d95495110f994394043da94a5010f695294043dc9465010f715194043c750d5010f994354043da9495010f695254043dc9455010f715154043ced0d5010f5a4354043ce50d5010f594354043c650d5010f1d5310f42ad58443d0ab96010f429798e51d0a5d6394742d598e51d0b556394742cd90d51d0b3443547429d9865390a756194e42d398a5390b566194e42d55865390b1e53d0a42b99874290aae6210d42ad5844350ab96010d42b99874250a9e63909429798c5050a5d63141429d9845050a7561141428fd954210a6f65508429d98754cca7561d53329d98454cca7561153329e98054cca796015332c755043ccad56110f32b658043cca3e64947328f59251ccb36
  | 4 => 0x13a0005740603c012088490185325b82b043000055330a002c015239f4000b3c2e03a5a81851c1b451a9e9098001b2a704ea4e000658708d20009e4800b42224088f0c617016c000f21a24ac6600020a4b55227b0009c4000002b60012806e0004d84a2a2416b290829d1f6000b1156590a00f82960000011a00010c0cc0002b2849bd619c8374000201760004f439000000001372901eca547514f3601bc3dab60ea001532720f2000970fc3705407797139ca60422183662d8d2800000000002af30e000002353802882b917000868719481c8000ac0002f06315ba550729150095a41e108c09fe0006f8000934ee97008194038a108c8003d61980d1ea00006d120413fe000000001e82950a9ee05a30c0f169000000920001ce000000c818a950730b711a5343f11200020cafaae422825151c709e260000000009906805d2cc714be8ca000300020f53f683800000210000b980009a3fc0025f172744eb2d100063c000ae0008340008e0002988aa0a34c4c44c95957040d2f1fa4802c04d216054001001db5a0aad5f00051e310000000007dcb082f07022d288001c40011e9c6472000aa0000000013a80000000115800462a18c716b000000002430460000025b3b00000000030a0002f8001e62a5259880e03e1312073ea161630a3000ad0002854e0405459df0008a4ce1cb3c0770d203b0281acec80244c79d119222d47cc5ea030003dc001e80001b07800011246840934060118908293d25b44b20c4a6000ea9e329c6b8da8aa336121199333c251952a5814e1a834000000655329cf4c2000a1aa800067c61052000648591255340002589e17c000fb08858aafc87a2c2feb3910a81000a500010910a000000004905d15805a06a88927a8323a880931b6392934439b7000ae4000000005ecd523e00087cb18443fa6c8c81513f252476a4a1c079828000000000001b15762fc9f06d00cb04f128254e4a4489ad22c6342a83f00007cb7800386b4d500002388089804500066800077000000c312c0925e4328bb20e190978000424fcfe1141569d88c00000051c09800000001301d005c000858783260906e0a400074c3eaa33e47b4000d800003c000ce45e000000bc000374ea00039a0016390c3468a1498033880004d93200031c0012a000000b228900025ca99a20160000000000000000000000a78e08af2803f4002060620000000045a0000ca3a5424dc869dd0000000025a43a904002b1196b08678e52c08dc4627d00095c0007c098af00014b4d867413a1708e0008f8172d887814000484608f62bd000b103383d5109cc64ab252218cf7a124f06fc542cd2b89a40015252492
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x190b22048009289b8013af000a140c000024802180001c001a800a930032102c00088011a90780002780160b871a000016a105a3b0318d8000000020978010b2ab2a92b100001f81a82d8000309f0288002e01002b95970018150e2e85229c862a001b112703020e8f2fa31d89809d039e86a684240d2000000c988014ad00000f801200000000298000002c80001e0025a52619830000000082000080004000408101c2c00045c002400000008080c4000000c000c1e4ab8ec4a1887235cb6150c4391ae43028621c95711814310f82a1aa4a8887c250e5254043e1286a92a021f11439455010f88a1aa2a8087461d94354043a36e4a1aa021d1b7150d5010f0ca9ac021e854c5c04354742c32a8b0087995517010d51ccb0caa2c021a65615c44350932b12e021a84996195358043d0694b8086a9683865516010f31a92e021aa598e1954580434c6c2b9086a0a63645c04350531e0aa6a128210f05544c93108662b9ec890843295d36348421e0aa8a9a4210ca5741812108662b98c090843c89512154021e42a890aa010f425348550087a0a9a42a8043525ce4254021ac2e3212a010d29748c950086b0b8c64a8043545ce4154021ac2e520aa010f21425055008698ba462a8043585ca3154021e826498aa010d607648550086b1ba242a8043585d12154021ac6e690aa010d61734855008722b12c229a81925896014d40ca2c2b00a6a061453587425030629ac5a0a814a5c04354840a62e021aa22060c63549401030a31aa2a008186d516010e30934eda1a811862562584544c30cb1ac02a2618a5896015130c62c2b00a89861454587324c3062a2c598a61469d64390130c30caa1a809861954580430c2a4b8086a9061545c04354430838ecaa2601860c64549300c30a322a298061855916314520a8ae7210a290525748c85148318b22c028a419458d6014520c52a8b004210649535802108312aa0c2900419154c6148020cc6a4b0043084e276c852084306b22c6292218a5916014910c92c6b00a488661615805244322b18a520a2189590528c510ac4eb10c4088660654852044318aa2c0108219454d6008410cc2a4b004208625541891004322a98c488021191d95244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x6e0a0c24800909821d94354043911811d9435404391181dc9435404390982dc54354043921841d92154021941831d9215402194183dd1215402192184dcd2154021
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
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
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (20684+((h/227+packedAt s5K5 (18414+(h % 227)*10) 10) % 990)*11) 11
  | 4 => packedAt s5K4 (29960+((h/241+packedAt s5K4 (27550+(h % 241)*10) 10) % 958)*11) 11
  | 3 => packedAt s5K3 (5270+((h/34+packedAt s5K3 (4998+(h % 34)*8) 8) % 148)*8) 8
  | 2 => packedAt s5K2 (488+((h/2+packedAt s5K2 (480+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 2 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 3 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 2 => 0x1a912289244a801ac80524849212530c28a28
  | 3 => 0x488c032520240c92352918000e498192540f80
  | 4 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_28690
namespace PEqualNP.Outside.L_meta_28690
open PEqualNP.Outside.L_meta_28690.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d243179f00b1c3100d4e200000022128c00a1e057390000da80e192306e21a363a515804c845bb0601d322e0022d2c9c99866408804a68f192a39e805218341020604000280c4800c08800264c18002ffd5009fe5402ff55009fc5402ffd4c07fe5302ff54c07fc53027fd0c07fe43007f50c07fc4302ffd4805fe5202ff54805fc52027fd0805fe42007f50805fc4201ffcc805fe32007f4c805fc3202ffd4403fe5102ff54403fc51027fd0403fe41007f50403fc4101ffcc403fe31007f4c403fc31017fc8403fe21007f48403fc2102ffd400b7f5002ff9400bfd50005f5400bfc50027fd0001fe40007f50009fc4001ffcc001fe30007f4c007fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24006ff08120037d8409000bf8204801fff8824006ff04120037fecb0801aff658400dff32c2005bf99610036fccb080167e658400dfeb2c200ebf59610036facb080027d658400dfe32c2006bf19610037fec90801aff648400dff3242004bf99210037fac908002fd648400dfe3242006bf19210077fea908037fe548401dfeaa4200dff15210037fec70801aff638400dff31c2003bf98e10037fac708002fd638400dfe31c2006bf18e10077fea708033fe538401dfea9c200cff14e1006ffe8708033fe4384001fea1c200cff10e10037fec50801aff628400dff3142002bf98a10037fac508002fd628400dfe3142006bf18a10077fea50802ffe528401dfea94200bff14a1006ffe850802ffe4284001fea14200bff10a10067fe650802ffe3284001fe994200bff0ca1000dfac308007ff5184003ff28c2001ff5461000ff8a308007ff4184003ff20c2001ff5061000ff88308007ff3184003ff18c2001ff4c61000ff86308007ff2184017fb90c2001ff8861000ffa4308007fc2184003fa10c2006bf98210037fea10801b7f508400dff2842006ff54210036faa10801bfc508400dffa042006ff90210037fa810801bfc408400dff9842006ff8c210037fa610801bfc308400dff9042006ff88210037f4410801bfd2084001fc9042006ff08210037fe210801bf71084003fd8842006ff04210037f0210802bff65440157fb2a200aff9951002dfcca8802bfd65440157eb2a200aff1951002df8ca88003ff64440017fb222009ff99110025fcc888003fd64440017eb222009ff19110025f8c88802bff5444013ff2a2200aff5511004ff8a888003ff63440017fb1a2008ff98d1001dfcc688003fd63440017eb1a2008ff18d1001df8c68802bff5344011ff29a200aff54d10047f8a688027ff4344011ff21a2000ff50d10047f88688003ff62440017fb122000fbd8910005dec48801ffe62440057f3122000ff58910005fac48801ffc62440057e3122000fb18910015d8c48802bff524400fff292200aff5491003ff8a488027ff424400fff2122000ff5091003ff88488023ff324400fff1922000ff4c91003ff8648801aff6144003ffa8a2001ff9451000ffaa288007fc5144003ffa0a2001ff9051000fec8288007fd4144001faa0a2001ff1051000ffe6288007fe3144003fb18a2001ff4c510007ea6288007fc3144003ff90a2001ff8851000fec4288007fd2144001fa90a2001ff0851000dfec08802bff5044015bfa822006ff94110057faa0880037d504400dfe2822009ffd0110037fc8088003fd404400dfe2022008ffcc110037fc6088003fd304400dfe1822007ffc8110037fc4088003fa2044001fe9022000fe48110037f84088007ff1044003fd8822006ff84110037ec208801bfc104400dfa0822001fe04110
  | 1 => 0x37d504c035fca826000de54130037f8a098067ff404c00dff2026000fe90130007fa8098003f9404c00dfe2026003ffcc13001ff6609801bfe304c00def1826006ff0c130037b8609800ff8304c031ff9026006ff081300bffe209801bfc104c00dffb2c4006bfd9620037fccb10016fe658800dbf32c40059f99620037facb1005afd658800dbeb2c40009f59620037f8cb1001afc658800dffb244006bfd9220037fcc910012fe648800dfeb244000bf59220037f8c91001afc648802dffaa44015ff952200b7faa910057fc548800dffb1c4006bfd8e20037fcc71000efe638800dfeb1c4000bf58e20037f8c71001afc638802dffa9c4014ff94e200b7faa710053fc538802bffa1c4014ff90e20007fa8710053fc43880057eb144002ffd4a20017fca51000bfd5288005fe2944002ffd0a20017fc851000bfd4288005fe2144002ffcca20017fc651000bfd3288005fe1944006ffd8620037fcc310006fe618800dfeb0c4000bf58620037f8c31001afc618802dffa8c4013ff946200b7faa31004ffc518802bffa0c4013ff90620007fa831004ffc4188029ff98c4013ff8c620007fa631004ffc3188005ff90c4002ff8862009fdc431000bfd2188005fe10c4002fb08620035fcc11001bff508800dbfa844006ff94220037faa11001b7d508800dfe2844006ffd0220037fc811001bfd408800dfe2044006ffcc220037fc611001bfd308800dfe1844006ffc8220037de411000bfb208800dfe1044006fe08220037fe211001bfc1088025ffb2a4012bfd9520097fcca90016fe6548025feb2a4012bf59520097f8ca90016fc6548001ffb224000bfd912008ffcc890012fe6448001feb224000bf5912008ff8c890012fc6448025ffaa24011ff95120097faa890047fc5448001ffb1a4000bfd8d20087fcc69000efe6348001feb1a4000bf58d20087f8c69000efc6348025ffa9a4010ff94d20097faa690043fc5348023ffa1a4010ff90d20007fa8690043fc434800d7fb124002ffd4920017fca49000bfd5248005fe2924002ffd0920017fc849000bee4248005fea124000fb50920017f8849000bff3248005ff1924002fb8c920017fa6490003ed3248005fe1924000ffd8520005fec290003f761480017bb0a400fff9852000dfcc290003fd614801ffe30a4001bf18520007e8c290006f46148025ffa8a400fff94520097faa29003ffc5148023ffa0a400fff90520007fa829003ffc4148021ff98a400fff8c520007fa629003ffc3148005ff90a4002fbc8520017fc429000bfd2148001f690a4002ff08520015fec09004bff5048025bfa824006ff94120097faa0900037d504800dfe2824011ffd0120037fc8090003fd404800dfe2024010ffcc120037fc6090003fd304800dfe1824002ffc8120017f6409001bfe204800df71
  | 2 => 0x400fff8a2a0013ff4150009dfa0a8004ff90540027fa82a0003bd4150009fe20a8021ffcc5400fffc62a0003fd315003ffe18a8020ffc85400fffc42a0003fd215003ffe10a8004bfd8140117fea0a008b7f505000dff2828022fe94140117faa0a00037d5050045fca828000de54140037f8a0a0013ff4050009fda028006ff901400377c80a001bfc405000dde2028004fe1014010ffe60a001bfc3050041ff9028006ff081400fffe20a001bfc105000dffb2c6006bfd9630037fccb18016fe658c00dbf32c60059f99630037facb1806efd658c00dbeb2c60009f59630037f8cb1801afc658c00dffb246006bfd9230037fcc918012fe648c00dfeb246000bf59230037f8c91801afc648c037ffaa4601eff952300dffaa91807bfc548c0077eb1c6003ffd4e3001ffca71800ffd538c007fe29c6003ffd0e3001ffc871800ffd438c007fe21c6006ffd8a30037fcc51800afe628c00dfeb146000bf58a30037f8c51801afc628c037ffa94601dff94a300dffaa518077fc528c03dffa14601dff90a30007fa8518077fc428c007ff9946003ff8ca3001ffa651800ffc328c00dffb0c6006ff9863000dfcc31801bfd618c0017eb0c6006ff18630035f8c31806fff518c039ff28c601bff546300e7f8a31807bff418c039ff20c6000ff506300e7f8831800fff318c007ff18c6003ff4c63001ff86318077ff218c039ff10c6000ff486300e7f8431801afe608c00dffa846006dfd4230037fca11801bfa508c00dfea846006df542300dff2a11800379508c00dfe2846006ffd0230037fc811801bfa408c00dfea046000fe50230037f8811801bff308c00def9846003fecc230037f8611801bf8308c00dff9046006ff08230037fe211801bfc108c035ffb2a601abfd95300d7fcca98016fe654c035feb2a601abf595300d7f8ca98016fc654c001ffb226000bfd91300cffcc898012fe644c001feb226000bf591300cff8c898012fc644c035ffaa26019ff951300d7faa898067fc544c00d7fb1a6003ffd4d3001ffca69800ffd534c007fe29a6003ffd0d3001ffc869800fde434c007fea1a6000f750d3001ff88698003ff624c0017fb126018ff98930015fcc498003fd624c031fe3126002bf189300d7fea498063fe524c035fea926018ff149300cffe8498063fe424c001fea126018ff1093001ffe649800fdf324c007ff1926003ff4c930007ba649800ffc324c001ffb0a6000bfd85300bffcc298006fe614c001feb0a6017ff1853000df8c29806bff514c02fff28a601aff545300bff8a298067ff414c02fff20a6000ff505300bff8829800fff314c007ef98a6003ff8c53001ffa6298003dd314c007fe18a6018ffc85300bffc4298003fd214c02ffe10a6003bfd81300d7fea09806b7f504c00dff282601afe941300d7faa09800
  | 3 => 0xfa82422ddfd412116ffca0908b7fd504845bfe282422cffd0121167f880908afff3048457fe1824202ffc8121017de409080bfc2048403ff8824201fdc412100ff820908037f6454055bf322a000df59150156f8c8a80037f6354053bf31aa000df58d5014ef8c6a80ab7f4354053bf21aa000df50d5014ef886a80037f6254051bf312a000df58950146f8c4a80ab7f4254051bf212a000df50950146f884a80a77f3254051bf192a000df4c950146f864a80037f615404fbf30aa000df5855013ef8c2a80ab7f415404fbf20aa000df5055013ef882a80a77f315404fbf18aa000df4c55013ef862a80a37f215404fbf10aa000df4855013ef842a80177f605400b3fb02a005ded8150156fe80a801b7c4054053bf982a006df0c150146fe40a801b7c205404fbf882a006df04150037fecb2001aff659000dff32c8005bf99640036fccb200167e659000dfeb2c8023bf59640036facb200027d659000dfe32c8006bf19640025fac920013ff5490009ff2a48004ff55240027f8a92001bff639000dff31c8003bf98e40037fac720002fd639000dfe31c8006bf18e4011ffea72009bfe5390047fea9c8026ff14e40027fe8720013fe4390009fea1c8004ff10e40037fec52001bfe62900057f3148006ff58a40005fac52001bfc629000d7e3148023ffd4a4012ffca52008ffd529004bfe2948004ffd0a40027fc8520013fd4290009fe2148026ffcca4012ffc6520003fd329004bfe1948006ffd8640037fcc320006fe619000dfeb0c8000bf58640037f8c32001afc6190047ffa8c8024ff9464011ffaa320093fc5190009ffa0c8004ff90640027fa8320013fc419004dff98c8024ff8c640007fa6320093fc319004bff90c8024ff88640007fa4320093fc219000d7f3048006ffd4240036fea12001bfe509000dfd2848006ff54240036faa12008ff95090001bca848006ff14240037fe812001bbf4090009fda048006ff10240037f0812001bff309000dfe1848006ffc8240037f8412001bff109000dfe0848022ffd9540115fecaa008bfe655000b7f32a8022ff59540115facaa008bfc655000b7e32a8006bfd9140027fea8a0013fe5450009feaa28004ff15140007fec6a0002ff6350043ff31a8003bf98d40007fac6a0087fc63500077e31a8022ffd4d4010ffca6a008bfd5350043fe29a8004ffd0d400277e86a0013fe4350009fea1a8000ef50d40027f886a0003ff62500017fb128020ff98940015fcc4a0003fd6250041fe3128002bf18940117fea4a0083fe5250045fea928020ff14940027fe84a0013bf4250009ff2128004ff509400077a84a0013fc4250043ff9928020ff8c940007fa64a0083fc3250001ffb0a8000bfd85400fffcc2a0006fe6150001feb0a801fff1854000df8c2a008bff515003fff28a8022ff545
  | 4 => 0x813fc4250465ff9928231ff8c941007fa64a08c7fc32504037fb0a8201ffd454100ffca2a0807f65150403fea8a8233fd5454100ff8a2a0807ff4150409fba0a8201ff9054100f7c82a0807fc4150403de20a8201fd1054100ffe62a0807fe3150403fb18a8201ff0c54100ffe42a08c7f72150403ff10a8201ff0854100fe842a0803ff60504017fb028200ff98141007fac0a0803fc605040d7e3028233ffd414119efea0a08cffe5050467fea828233ff14141027fe80a0813bf4050409fe2028232ffcc141197f860a08c7ff2050463fe1028201ffc414100fee20a0807fc1050461ffb2a6230bfd9531187fcca98816fe654c461feb2a6230bf59531187f8ca98816fc654c401ffb226200bfd913117ffcc898812fe644c401feb226200bf5913117ff8c898812fc644c461ffaa2622fff95131187faa8988bffc544c4037fb1a6203ffd4d3101ffca69880ffd534c407fe29a6203ffd0d3101ffc869880ffd434c407fe21a6200ffd8931005fec4988bbfe624c4057f3126200ff58931177f8c49880afc624c461ffa92622eff94931187faa4988bbfc524c45fffa12622eff90931007fa84988bbfc424c407ff9926203f7cc93101ffc649880ffd324c401ee9926203ff0c93100dfec298807ff514c403ff28a6201fd9453100ffaa2988c3f5514c403fe28a6201ffd053100ffc8298807f6414c403fea0a6200fd5053100ff88298807ff314c407fb98a6201ff8c53100fbc6298807fc314c403ee18a6201fd0c53100ffe42988bbf7214c403ff10a6201ff0853100fe84298803ff604c4017fb026200ff98131007fac098803fc604c40d7e3026230ffd4131186fea0988c3fe504c461fea826230ff1413117ffe80988bffc404c407ff9826203f7cc13101ff860988bbff204c45dfe1026201ffc413100fee2098807fc104c45bffb2a422dbfd952116ffcca90816fe654845bfeb2a422dbf5952116ff8ca90816fc6548401ffb224200bfd9121167fcc890812fe6448401feb224200bf59121167f8c890812fc644845bffaa2422cff9512116ffaa8908b3fc5448401ffb1a4200bfd8d2115ffcc69080efe6348401feb1a4200bf58d2115ff8c69080efc634845bffa9a422bff94d2116ffaa6908affc5348459ffa1a422bff90d21007fa86908affc43484037fb124202ffd4921017fca49080bfd5248405fe2924202ffd0921017fc849080bfd4248405fe2124202ffcc921017fc649080bfd3248405fe1924201bfd852100ffea290807fe5148403fea8a4201ff1452100ffe8290807fe4148403fea0a4201ff1052100ffe6290807fe3148403fe98a4201ff0c52100ffe429080bf72148403ff10a4201fb8852100ff84290807ec2148403fa10a4201f908521007fec090802ff6048401ff3024200ff58121007f8c09081afc604845bf
  | 5 => 0x95421cff8caa1016fc65508057fb228404ffd5142027fca8a1013fd5450809fe2a28400ffd8d42005fec6a10e3fe63508077f31a8400ff58d421c7f8c6a100efc6350873ffa9a8438ff94d421cffaa6a10e3fc5350809ffa1a8404ff90d42027fa86a1013fc43508057fb128402ffd4942017fca4a100bee5250805fea928439fb54942017f8a4a100bff4250809f7a128402ff909420177c84a100bfc4250805de2128402fb10942017fe64a100bfe3250805f71928402ff0c942007fec2a1002ff615086fff30a8401bf98542007fac2a10dffc61508037e30a8439ffd45421bffca2a10e7fd515086ffe28a8404ffd05420277e82a1013fe4150809fe20a8438ffcc5421bffc62a10dffc3150805ff90a8402ff885421bfdc42a100bfc2150805f610a8400ffd8142005fec0a1003fe6050801feb028400ff18142035f8c0a10e7ff5050873bfa828439ff941421cffaa0a10e7fc5050809ffa028404efd0142027f880a10e3ff3050871fe1828402ffc8142017de40a100bfc205086fff8828437ff041421b7feca990daff654c86dff32a6405bf995321b7faca990dafd654c86dfe32a6405bf19532007fec899002ff644c86bff3226404bf99132007fac899002fd644c86bfe3226404bf191321b7fea8990d7fe544c86dfeaa26435ff15132015fec69900fff534c807ff29a6403ff54d3201ff8a69900fff434c807ff21a6403ff50d3201ff8869900aff624c805ffa926402ff94932017dca49900bfd524c86df6a926402ff14932017fe849900bfe424c805f72126402ff50932007da849900bfc424c805ff9926403fbcc932017fc649900bde324c805fe1926402f70c932017d86499003ff614c8017fb0a6434ff9853200dfcc299003fd614c869fe30a6401bf185321b7fea2990d3fe514c86dfea8a6434ff145321affe82990d3fe414c869fe20a6403ffcc53201fbe629900ffe314c807fe18a6402ffc8532017fc42990d3ee214c805fe10a6402fb08532007fec099002ff604c801ff3026400ff58132007f8c09901afc604c86dffa826436dfd41321b7fca0990dbfd504c86dfe2826435ffd01321aff8809900fff304c807ef9826403ff0c132017fe409900bef204c805fe1026434ffc41321a7f820990cfff65504677fb2a8233ff9954102dfccaa08cffd65504677eb2a8233ff1954102df8caa0806ff6450409ffaa28204ff95141027faa8a0813fc5450401ffb1a8200bfd8d41197fcc6a080efe6350401feb1a8232ff18d4101df8c6a08cfff5350465ff29a8233ff54d41197f8a6a0813ff4350409ff21a8204ff50d41027f886a0803ff62504017fb128231ff98941015fcc4a0803fd6250463fe3128202bf1894119ffea4a08c7fe5250467fea928231ff14941027fe84a0813bf4250409ff2128204ff509410077a84a0
  | 6 => 0x140581300a028030050000080000401e01c018080060100500905a0500200000212c0005402201800004008004020000000100180001c0540381100a0000801000c1900000700a00401010000000000000040080002e002014008000040000300315e00c010000020340202b00c00c00802000000020060040080081102e23401800000008268100040000783100000c0c81a0080080600803a0500b8130040240100400606402804000020000020181940000000c02c07804002060048080340d40000e00e01c010050000100b0020000040300700000c0280000e0bc1100b00e000048070200140980000c0640180200004c01800000000140020000080100000a0080300500002c010080080380000d03a00804800002000010050020000280100000c00004000000108160000041400107c0041080101400008000042038018000000001380500601400818004004008050000280280000005c0b00a00601c0002302400000013000018060060000180200500601c03825008034058000080340100202800001005012000018110400180100300a0700400b004018048020680080380901c0000080000200013000002064000030380401283b016000048000040000400201006c000740000140280e002000008030060280902b0080c4000000020001283401605c01013002000208010180000103a04a0040080e00c0100000900a0040080a000010640020120980382500e0541100101a0000080300006c000020020003a8080040040400708a020010000100000385100c0a879ffb2a863cbfd9543006fecaa18027f6550c79ff32a8605bf995431e7facaa18f2fd6550c79fe32a8605bf195431e6f8caa18167c6550c077fb228604ffd5143027fca8a1813be5450c09feaa2863cef55143027f8a8a180eff6350c07ffa9a8603ff94d4301fbca6a180ffd5350c79eea9a8603ff14d4301ffe86a1813df4350c07ff21a8603ef90d4301ff886a180fbc4350c07ee21a8603e710d43007fec4a1802ff6250c77ff3128602bf98943007fac4a18effc6250c057e312863cffd49431dffca4a18f3fd5250c77fe2928604ffd0943027fc84a1813fc4250c07ff9928603ff8c94301ff864a1803ff6150c017fb0a863aff9854300dfcc2a1803fd6150c75fe30a8601bf185431e7fea2a18ebfe5150c79fea8a863aff14543027fe82a1813fe4150c09fe20a8603ffcc54301ffc62a180ffc3150c77ff90a863aff885431d7f842a1803ff6050c017fb028600ff98143007fac0a1803fc6050c0d7e302863cffd41431e6fea0a18f3fe5050c79fea82863cff14143027fe80a1813bf4050c09fe2028603ffcc14301fbe60a180ffc3050c77ff902863bff081431d7fe20a18ebfc1050c73ffb2a8439bfd95421cffccaa1016fe6550873feb2a8439bf5
  | 7 => 0x3c30001f800016c33a00009d1420000003381fe00038100000050800031600048b2a02f63d045d1a026400000037749d38d21a1f440f1110005125820903062db0000e906928c5872861d71f12050bc4333634b20fb26522e14a2bb45950355a1265574c83e30702b807516959157a0a93640d006006d0000001830001ec29f1002ea2c60f20682754340215164f63f630c4180531bf01900053040e4d40003ce1240c700000035f0000592b90e82e11fb58e1311353ef07b00c08d56d40d1d447711758349041e4d91cb0002bc2c000037a2f409a1e00dc0291900d90001460b52f50000f422100031200034c3d71f031816a0004bc31422d0001fa0520003fc43b00012b0004f442f15b01d48423f5790002c51a21ea11211954653504e1bd14e53c4fe4874d614c0884262fe3e60d70000c204c00038348e0004022c90a80003744a600013b5273083d13ca22c00b27d11541b26028736c3c73b33ba58912004500044a0fe46a3a520e53e4005155403013ad3460c64b507f32a00025920700006634513d00001a07d0005601030040005014662914141e63501732e259015129b58605c2610dd4410002ee4644233a10002c10f000000034456b00553b2a61ae2c816311c00032802854724c0774031841b13bd0000004f51ac5560d628539f23615a1684b000024d25656c03727931e0003340fd57c09e53f47000000043005b0003d30824733dc0180001450002fc5635740fc0945843681500570bb0000000000002ec0004520001911770003754e90004b30005060001c011e2f73274420995381ba32c12225c5372ae5653af14308b4e019d0005590003b930a0003880b64a52161b45611ad54509b08155c47d14703d3951364721d552146132e2190a21ff1ab1740c348a42e2b44d527a02b17958857b0e73ae49c3ea27607300043749449a1180004c700000004a00010d00f4195540745753730000111803cd51d17651b00d0001665220003e23003e05260423b70001e846050d00009f0001080000002443f20004ce0f60ba0562400a410c0002d02b037d00054b52a45a20221d20057241f0b228220a47f4270644d70444454790162304ec4ca2d83394ea4ab56815922819b09724a31d48f12a1bb33c4a34203a749b4292880a117c39b2151ca2ed5532683331c81573c252d3512350004ee36f2e736d01b00019f4f91dc4a941246e30d5523793300f33d255e25724b3612a113450e21c3211640a75703df4c40ff1c73a957300026955852900016519c57825d3f100000008a3da12d22200055b0004be3ee17e3c04e80650120040000701000c0000503a008008030000a000022018000000150000000100300a0a8370030880040000400e0480380100004c010040000d8470190220000002302817000000002004008020000
  | 8 => 0x485342a437600a5391a70000ec0000001870000000000d527f0002290030005814c33b03f74bf49542b2931df4a819245c34312c4622a93931a44dc0354bd2cb4282b10151e408e08627e13e23457d1290c82c329918528a17d58006102a18c3f452847e1d941c1aa2093221813802cd1f35770792bf3fd0ca1cf3d836e4d049e05e23b01e4690304d252526c11b1100ac49f1e151113242a17f31c51f4245022475002500512a74502840e32731ee0144403414922e40b73e70b30390e522a42c0d42b20bf27418a3e80e10b12ac1395625440061de33d4051562f146f4091b858c3711e75511c14f326d3570f154225e2372a52f044b0073903b147a56f05f0873323893ff18f0784753020671051065762140ef23852b1f21994ad19503611614429e1cd49907203b4551620ea2954cc18e1863b238e2ba3d61ce2973f94532242ef3e15073a432010a0db21857f2783701754bb1ef3f02a80c14e22d51f518904d39723c2ff4252c402e00000000007115400045816f00026e2892113ac00009300025f0380003de0be2b61e30003eb0005230003664510003690c000000044336a00056757e0a02af36b50a00000032b38c1b54e42fa23d3bc4e64a14ac50f3941d60852581da5144972802f911d03e3c101c34226f44727b3194652523991142042aa1270003bf25429449317b0000003370001b93d94541eb4eb29608958b1c50652d20003a000052400053a00014b00053d2b72254ff02c0320eb0001700002bd02d39614d24e0f93dd56e3b831f0001490f800032504b0001981940005200004911400004ba45b10f3290a600004f4e54382fd0005101d300000000020d37f52c07c38b3fb35e25b1c30ab24f39c22f07e2ab27c35c0002620d807a0000f71882da4d10004564d34ed2a24444de4dd1520af0000001d032d00046316e41d00044601303a3b624200000038a02532f4df03300000028139e50b0000002230002d426328d46725a49800000051333e2de0cf43200000034d0000003ab00012800045f16d0004d80e20000830000220c53034fd1e50003a248c00000002351c2e00000004365481a10481010003472060003534573a60002f34cd48300112340143d52e44e0493db00041a1f94f04fb00045e58a2b30403cf2f800028b2df0003c63983b52e91533a82eb06c58f4c62260aa29837c1380ae54f31a0412481af02030f47b39143c2665503315410004c051834b4f23e40ce0000df0003071304c232630e04302f1610bd4fa2172e52d721340c1b20001041581c43d43841602cf4fc3ec0000001be29d2d60000e65040000002ce1722ad0005322670004080000630c40004061a90d10000000000e400043916b06246c30900930408451a51e39a05544903c09210950c48d4a415f0001a30001370910005360004c9220
  | 9 => 0x34834031b1821a64150cd00006a0004da37855f3be21020f40a13f35a0004e347c2c70000000000000950001c92083175641d801f13a11a19741658509624140400000024628306e33b3153650001712900000b017813c26a1d21331db14f0b410235528f00049657100000000000001705441054e2532b52fb2a30001ed05a4ef4860b92395170272331f65092dd2e80000261c652f33633500000000019a00015e2430a30000000344a708000000032400028e2122720000004480003520004e156a3c900010e09c26b23a3130003cc0cc19e0002f200000000044d0f54311fc0240004890022d142d3052270ed55d47624908f4af43f21e35d3860084b932331100036043e0000000e05050000004cf39254c54a2e600000037244f3543585333aa4781b315c48500055500029c3f33872310001b037e00000000004600016729a3e50003fe1960b82324a22be00e12537b00000035934e2550000314c50004b62510000003d51934353c848812133f4222701a50d32cc2c205008c3ed51906f0004cb56600011f00038540b00000000018d0001dd4ae00009817a30b3b40de4800004211b735b3672452ca3cb4813f84110003494132714aa56912f1e944c27720121b05d4820001cc34a10b3c443a2dc0004b123e0ee4681f70000472d920b20c46d0003c51d11070001a84b80000580a52920c92030761fd4db1c254953121f38200000003f4a04e70da4f83bb0fa31022b01238f3f54f11b618b4c13fa1410cb15d3a306b0ad0101e24f736211358d54d1bc3e912e0004b739d5432e300034f4b42d30003564170004710d215540747446b0000001
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x6634c51001ef4634c510047d4634c510005f7724c510007e7624c510176f6624c510176f4624c510007e4624c510176e4624c510047d7324c510007d5324c510007f3704c510035f6704c510035f4704c510007f0704c51000ef7604c51000ff3604c51020777504c510047d7304c510035f47648510016f47648510034f47648510005f77448510005f57448510005f77348510005f5734851000df7724851000fe77248510007e76248510016f66248510016f4624851003fe46248510016e46248510007f37048510035f67048510035f47048510007f0704851000ef7604851000ff360485101ff77504851003fe7204851002e7f765411013e7e765411013e7d765411002e7c76541100067f64541101567e64541100067d64541101567c64541100067f635411014e7e63541100067d635411014e7c63541100067f62541100076f62541100066f62541101467e62541100067d62541101467c62541100076c62541101466c625411000777715411013f7471541100367f615411013f76415411000775415411013f76315411000775315411013f7621541100077521541100357f70541100577b70541100367f60541100377a40541100377a30541100377a205411013f7b1054110037761054110037741054110037781054110037701054110024ff765011000cfe76501100fcfd765011000cfc7650110006bf6450110026bc6450110006ef6250110106ec6250110005f7715011000df47150110007b5415011000779505011001cff764c11000cfe764c1100bcfd764c11000cfc764c110006df634c11001edc634c110006ef624c1100c6ec624c110005f7714c11000df4714c110007d5314c11000779504c1101f5fa7688110036fa76881100377a758811003779758811007df9728811009feb6288110016fa6288110016f8628811003fe86288110016e86288110037f3718811000dfa7188110035f87188110037f07188110036fb6188110037f3618811009ff24188110007f1418811009ff23188110007f1318811009fea218811009ff2218811009fe2218811003ff1218811009fe82188110014ff764811000cfe764811007cfd764811000cfc7648110006ef6248110016ec6248110005f7714811000df47148110007e521481101ef7b5048110007795048110037e82048110037f0104811000df87648110016f8764811000cf87648110035fb7248110037eb7248110007eb6248110016fa6248110016f8624811003fe8624811003fea4248110007e9424811003fea3248110007e93248110007f3714811000dfa714811000df8714811007ff07148110036fb6148110037f3614811007ff24148110007f1414811007ff23148110007f1314811007feb214811007ff2214811007fe9214811003ff12148110007e12148110
  | 1 => 0x8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910226ef71d891009eee71d891009eed71d891009eec71d891009eef51d891009eee51d891009eed51d891009eec51d891009eef41d891009eee41d891009eed41d891009eec41d891009eef31d891009eee31d891009eed31d891009eec31d891009eef70d8910226ee70d891009eed70d8910226ec70d8910006ef50d89100066f50d8910226ee50d8910006ed50d8910226ec50d8910006ef40d8910226ee40d8910226ec40d8910006ef30d8910226ee30d8910226ec30d891009eef10d8910226ee10d8910226ec10d891003eec625891021dfb7058910004ff755891002cfe7558910004fd755891002cfc7558910004ff7458910024fe7458910024fc7458910004ff735891001cfe735891001cfc735891009cff7258910006ef725891007cff7158910006f7715891005cf7715891021cff7058910006fb70589100067f505891009dee761891003eee761891009cee761891003f6e751891003f6d7518910006ef6518910006ee6518910006ed6518910006ec651891003fae741891003fad7418910006ef6418910006ee6418910006ed6418910006ec641891003fce731891003fcd7318910006ef6318910006ee6318910006ed6318910006ec63189101f7e6711891003fe57118910216ef6118910216e761189101f7e641189101f7e631189101f7e970189101f6ef60189100076f50189101f7eb1018910217e61018910217e410189101f7e81018910004ff7650910004fe7650910004fd7650910004fc7650910026be6450910006bd6450910006ef6250910016ec625091000df671509101bfe62150910004ff764c910004fe764c910004fd764c910004fc764c91001ede634c910006dd634c910006ef624c910016ec624c91000df6714c9101a7e6214c910035f47650510026f47650510034f4765051020ef7655051020ef5655051000df7745051000fb77450510007b76450510026f66450510026f4645051004fb46450510005f77350510006f76350510006f56350510005f77250510007e7625051018ef6625051018ef46250510007e4625051018ee4625051004fb74250510007b54250510007f37050510035f67050510035f47050510007f0705051000ef7605051000ff3605051020f77505051004fb74050510035f4764c51001ef4764c510034f4764c510206f7654c510206f5654c510005f7744c510005f5744c510006f7644c510006f5644c51000df7734c51000fd7734c510007d7634c51001ef
  | 2 => 0x4ebe64d9110004ff75d911002cfe75d9110004fd75d911002cfc75d911001cfe73d9110004fd73d911001cfc73d9110014fe72d9110004fd72d9110014fc72d9110034ff71d911000cfe71d9110034fd71d911000cfc71d9110126bf41d9110126bd41d9110126f631d9110034fe70d911000cfd70d9110034fc70d91100067f50d911004ebf40d911004ebc6459110005ef725911003dec7259110235fb7059110004ff755911002cfe7559110004fd755911002cfc7559110124ff7459110006bf7459110004ff735911001cfe735911001cfc7359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec725911004ebf42591100fcff7159110006f771591100fef63159110234ff7059110006fb70591100067f505911001cfe76d8d10046de63d8d10004ff75d8d1002cfe75d8d10004fd75d8d1002cfc75d8d10024fe74d8d10004fd74d8d10024fc74d8d10014fe72d8d10004fd72d8d10014fc72d8d10034ff71d8d1000cfe71d8d10034fd71d8d1000cfc71d8d100e6f641d8d100e6df31d8d100e6dd31d8d10034fe70d8d1000cfd70d8d10034fc70d8d100067f50d8d10046df30d8d10046dc6358d10005ef7258d1003dec7258d1022dfb7058d10004ff7558d1002cfe7558d10004fd7558d1002cfc7558d10004ff7458d10024fe7458d10024fc7458d100e4ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d10046df3258d100bcff7158d10006f77158d100bef64158d1022cff7058d10006fb7058d100067f5058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100557c7550d100479c4350d101deec6250d1000df67150d10014fe76d891003eee62d8910004ff75d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d891001cfe73d8910004fd73d891001cfc73d8910006ef52d891003eee52d8910006ed52d891003eec52d8910006ef42d891003eee42d891003eec42d8910006ef32d891003eee32d891003eec32d8910034ff71d891000cfe71d8910034fd71d891000cfc71d891009eef21d891009eed21d8910034fe70d891000cfd70d8910034fc70d89100067f50d891003eef20d89101f5ee76d8910014ee76d8910006ef65d8910006ee65d8910006ed65d8910006ec65d8910006ef64d8910006ee64d8910006ed64d8910006ec64d8910006ef63d8910006ee63d8910006ed63d8910006ec63d8910227e771d891009fe471d891009fe641d891009fe631d891009feb70d89100076f50d891009feb10d8910227e610d8910227e410d891009fe810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d
  | 3 => 0xf215961013e7e215961013e7d215961013e7c21596100367f70596100347f70596100367e70596100367d70596100347d70596100367c70596100367f40596100367e40596100367d40596100367c40596100367f30596100367e30596100367d30596100367c30596100367f20596100367e20596100367d20596100367c20596100367f10596100367e10596100367d10596100367c1059610004ff755921002cfe7559210004fd755921002cfc7559210036bf7459210004ff735921001cfe735921001cfc735921006ebf4359210004ff7259210014fe7259210014fc725921006ebf42592100febf41592100febd4159210006f721592100fef42159210034ff7059210034fe7059210034fd7059210034fc70592100367f50592100367d5059210036be4059210036bc4059210036f71059210036f51059210004ff7558e1002cfe7558e10004fd7558e1002cfc7558e10004ff7458e10024fe7458e10024fc7458e10036df7358e10066de4358e10004ff7258e10014fe7258e10014fc7258e10066df3258e100bedf3158e100bedd3158e10006f72158e100bef42158e10034ff7058e10034fe7058e10034fd7058e10034fc7058e100367f5058e100367d5058e10036de3058e10036dc3058e10036f71058e10036f51058e10004ff7650e10034fe7650e10004fd7650e10034fc7650e100057f7550e100757c7550e101e67e6550e100067d6550e10026be6450e10006bd6450e1001ede6350e10006dd6350e100679c4350e10004ff7558a1002cfe7558a10004fd7558a1002cfc7558a10004ff7458a10024fe7458a10024fc7458a10004ff7358a1001cfe7358a1001cfc7358a10036ef7258a1005eee4258a1005eee3258a1005ef77158a1007eef2158a1005ef72158a1007eed2158a1007ef42158a10034ff7058a10034fe7058a10034fd7058a10034fc7058a100367f5058a100367d5058a10036ee2058a10036ec2058a10036f71058a10036f51058a10004ff7650a10034fe7650a10004fd7650a10034fc7650a101ce7e6550a100067d6550a10026be6450a10006bd6450a10016ee6250a10006ed6250a10005f77150a1000df47150a101bfe42150a10004ff764ca10034fe764ca10004fd764ca10034fc764ca101b67e654ca100067d654ca1001ede634ca10006dd634ca10016ee624ca10006ed624ca10005f7714ca1000df4714ca101a7e4214ca10035fb764821023efb76482100377a6548210037796548210037eb7248210037eb6248210016fa6248210036f86248210037e8624821005fea4248210007e9424821005fea3248210007e9324821005ff3714821000dfa714821000df8714821007ff0714821000df0714821007feb214821005ff3214821005fe3214821007fe9214821007ff02148210024fe76d9110
  | 4 => 0x852007f757518520006f76518520006f66518520006f56518520006f4651852007fb6741852007fb57418520006f76418520006f66418520006f56418520006f4641852007fd6731852007fd57318520006f76318520006f66318520006f56318520006f4631852007fe6721852007fe57218520216f76218520216e7621852023fe64218520007e5421852023fe63218520007e5321852007ff1701852021ef7601852000777501852023ff32018520217e62018520217e4201852023ff02018520004ff7650520004fe7650520004fc7650520026be6450520006bd6450520015ee7250520007ad4250520006f7615052000ef4615052018fe72150520004ff764c520004fe764c520004fc764c52001ede634c520006dd634c520015ee724c520007cd324c520006f7614c52000ef4614c520177e7214c520035ec764852000eec7648520034ec7648520005ef7448520005ed7448520005ef7348520005ed7348520015ef7148520017e77148520007e7614852000eee614852000eec614852007fe4614852000ee46148520007eb7048520035ee7048520035ec7048520007e87048520016ef6048520017eb60485202476f504852007fe7104852002e7f76541201467e76541201467d765412002e7c76541200067f64541201567e64541200067d64541201567c64541200067f635412014e7e63541200067d635412014e7c63541200076f72541201476c72541200367f62541201476e42541200076d42541201476e32541200076d32541200067f615412000777615412000677615412013e7e615412013e7c615412000774615412013e7461541201476f21541200076d21541200357f70541200977b70541200367f60541200377a40541200377a30541201477b20541200376e20541200376c20541200377820541200376820541200377a1054120024ff7650120014fe7650120104fd7650120014fc7650120006bf6450120026bc6450120005ef7250120015ec7250120007ad4250120006f761501200fef4615012000779505012001cff764c120014fe764c1200c4fd764c120014fc764c120006df634c12001edc634c120005ef724c120015ec724c120007cd324c120006f7614c1200bef4614c12000779504c1200067f74596100067e74596100067d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f42596100067e42596100067c42596100067f32596100067e32596100067c325961013e7f715961013e7e715961013e7d715961013e7c715961013e7f415961013e7e415961013e7d415961013e7c415961013e7f315961013e7e315961013e7d315961013e7c315961013e7
  | 5 => 0x266ef6550920266ed6550920015ef7450920017af7450920007af6450920026ee6450920026ec645092008fac6450920005ef7350920006ef6350920006ed6350920005ef71509201beee61509201beec61509201bee4615092008faf4150920007eb7050920035ee7050920035ec7050920007e87050920016ef6050920017eb60509202676f505092008faf4050920035ec764c92001eec764c920034ec764c92025eef654c92025eed654c920005ef744c920005ed744c920006ef644c920006ed644c920015ef734c920017cf734c920007cf634c92001eee634c92001eec634c920087cc634c920005ef714c9201a6ee614c9201a6ec614c9201a6e4614c920087cf314c920007eb704c920035ee704c920035ec704c920007e8704c920016ef604c920017eb604c92025f6f504c920087cf304c92000cfe76d852007ef661d8520004ff75d852002cfe75d8520004fd75d852002cfc75d8520024fe74d8520004fd74d8520024fc74d852001cfe73d8520004fd73d852001cfc73d8520034fd72d852000cfc72d8520006f751d852007ef651d8520006f551d852007ef451d8520006f741d852007ef641d852007ef441d8520006f731d852007ef631d852007ef431d852007ef621d852005ef521d8520034fe70d8520014fd70d8520034fc70d85200067f50d852007ef710d852007df676d852000cf676d8520006f765d8520006f665d8520006f565d8520006f465d8520006f764d8520006f664d8520006f564d8520006f464d8520006f763d8520006f663d8520006f563d8520006f463d8520257e772d852005fe472d852005fe642d8520007e542d852005fe632d8520007e532d852005ff370d85200077750d852005ff320d8520257e620d8520257e420d852005ff020d8520006f775d8520006f675d8520006f575d8520006f475d8520006f774d8520006f674d8520006f574d8520006f474d8520006f754d8520006f654d8520006f554d8520006f454d8520006f773d8520006f673d8520006f573d8520006f473d8520006f753d8520006f653d8520006f553d8520006f453d8520006f743d8520006f643d8520006f543d8520006f443d8520256f772d852007ef672d852005ef472d852005ef752d852005ef652d852005ef552d852005ef452d852005ef742d852005ef642d852005ef542d852005ef442d852005ef732d852005ef632d852005ef532d852005ef432d852005ef770d8520256f670d852005ef570d8520256f470d8520006f750d85200067750d8520256f650d8520006f550d8520256f450d8520006f740d8520256f640d8520256f440d8520006f730d8520256f630d8520256f430d852005ef720d8520256f620d8520256f420d852007ef4615852024dfb705852005df6761852007ef6761852007f76751
  | 6 => 0xc7650e200057f7550e200b57c7550e201e67e6550e200067d6550e20026be6450e20006bd6450e2001ede6350e20006dd6350e200a79c4350e20004ff755862002cfe7558620004fd755862002cfc7558620004ff7458620024fe7458620024fc7458620004ff735862001cfe735862001cfc7358620036f7715862009ef6415862009ef6315862009eee215862009ef6215862003ef5215862009eec2158620034ff7058620034fe7058620034fd7058620034fc70586200367f50586200367d5058620036ef2058620036ed2058620036f61058620036f41058620004ff7650620004fd7650620034fc765062019e7e65506200067d6550620026be6450620006bd6450620005ef7250620015ec725062000ef66150620006f5615062009fe42150620004ff764c620004fd764c620034fc764c6201867e654c6200067d654c62001ede634c620006dd634c620005ef724c620015ec724c62000ef6614c620006f5614c62009fe4214c620024fe76d912008ebe64d9120004ff75d912002cfe75d9120004fd75d912002cfc75d912001cfe73d9120004fd73d912001cfc73d9120034ff72d9120014fe72d9120034fd72d9120014fc72d912012ebf42d912012ebd42d912012eee32d912000cfe71d9120004fd71d912000cfc71d9120014fd70d91200067f50d912008ebf40d912008ebc6459120005f7715912007df47159120275fb7059120004ff755912002cfe7559120004fd755912002cfc755912012cff7459120006bf7459120004ff735912001cfe735912001cfc7359120104ff7259120006ef7259120106ee3259120004ff7159120006f77159120004f7715912000cfe715912000cfc7159120006f4715912000cf4715912008ebf4159120274ff7059120006fb70591200067f505912001cfe76d8d20086de63d8d20004ff75d8d2002cfe75d8d20004fd75d8d2002cfc75d8d20024fe74d8d20004fd74d8d20024fc74d8d20034ff72d8d20014fe72d8d20034fd72d8d20014fc72d8d200eeee42d8d200eedf32d8d200eedd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20014fd70d8d200067f50d8d20086df30d8d20086dc6358d20005f77158d2007df47158d2026dfb7058d20004ff7558d2002cfe7558d20004fd7558d2002cfc7558d20004ff7458d20024fe7458d20024fc7458d200ecff7358d20006df7358d200c4ff7258d20006ef7258d200c6ee4258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d20086df3158d2026cff7058d20006fb7058d200067f5058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200957c7550d200879c4350d20015ee7250d201d6f46150d20035ec7650920026ec7650920034ec7650920
  | 7 => 0x13010df97490130026fa6490130026f86490130037db739013001dfa7390130035f87390130037d87390130036fb6390130037db6390130137da43901300cfd94390130137db3290130007d93290130137db3190130007d93190130024ff765013001cfe765013010cfd765013001cfc7650130006bf6450130026bc6450130005df735013001ddc73501300079d435013027f7b5050130007795050130037b84050130037d8305013001df87650130026f8765013001cf87650130285fb7550130285f9755013027efb655013027ef96550130035fb7450130037bb7450130007bb6450130026fa6450130026f864501300cfb86450130007db735013001dfa735013001df8735013010fd87350130036fb6350130037db635013010fbb435013010fda435013010fb943501300cfd943501300079943501300cfbb4250130007b9425013010fdb3250130007d932501300cfbb4150130007b9415013010fdb3150130007d931501300067f74596200067e74596200067d74596200067c74596200067f73596200067e73596200067d73596200067c73596200067f43596200067e43596200067c43596201467f72596201467e72596201467d72596201467c72596201467f42596201467e42596201467d42596201467c42596201467f32596201467e32596201467d32596201467c32596200067f71596200067e71596200067d71596200067c71596200067f41596200067e41596200067c41596200067f31596200067e31596200067c31596201467f21596201467e21596201467d21596201467c21596200367f70596200367e70596200367d70596200367c70596200367f40596200367e40596200367d40596200367c40596200367f30596200367e30596200367d30596200367c30596200367f20596200367e20596200367d20596200367c20596200367f10596200367e10596200367d10596200367c1059620004ff755922002cfe7559220004fd755922002cfc7559220036bf7459220004ff735922001cfe735922001cfc73592200aebf4359220106bf4259220106bd4259220004ff715922000cfe715922000cfc71592200aebf4159220006ee2159220106ec2159220034fe7059220034fc70592200367f50592200367d5059220036be4059220036bc4059220036ef2059220036ed2059220004ff7558e2002cfe7558e20004fd7558e2002cfc7558e20004ff7458e20024fe7458e20024fc7458e20036df7358e200a6de4358e200c6df3258e200c6dd3258e20004ff7158e2000cfe7158e2000cfc7158e200a6df3158e20006ee2158e200c6ec2158e20034fe7058e20034fc7058e200367f5058e200367d5058e20036de3058e20036dc3058e20036ef2058e20036ed2058e20004ff7650e20034fe7650e20004fd7650e20034f
  | 8 => 0x14fc72d8530066df32d8530006dd32d85300bef631d8530066f531d8530006f721d85300bef421d853001cfd70d85300067f50d85300bef710d8530005ef72585300c5ec72585300bef461585302cdfb7058530004ff7650530004fe7650530004fc765053001dde735053000ef66150530035dc764c53000edc764c530034dc764c530005df744c530005dd744c530005df724c530006df624c53001ddf714c53001fd7714c530007d7614c53000ede614c53000edc614c5300bfd4614c5300bfd6514c5302bfd5514c5300bfd6414c530007d5414c5302c7d7214c5300bfd4214c530007db704c530035de704c530035dc704c530007d8704c53001edf604c53001fdb604c5302bf5f504c5302bfda504c5302bfd9504c5300bfd7104c530004ff7648530004fe7648530004fc764853001dde7348530005dd73485300bfe4214853002e7f765413014e7e765413014e7d765413002e7c76541300067f64541301567e64541300067d64541301567c64541300075f735413014f5c73541300367f635413014f5e43541300075d43541300067f62541301467e62541301467c625413014f5f32541300075d32541300067f615413013e7e615413013e7c615413014f5f31541300075d31541300357f70541300d77b70541300367f60541302b77b40541300377a405413003778405413014f7b30541300375e30541300375c30541300377830541302af7b20541300377a20541300377820541302a77b10541300377a10541300377810541300d77b765413002e7b765413014f78765413002e7876541300077b74541302b77a74541300077974541302b77874541300077b64541300067b64541302b77a64541300077964541300067964541302b778645413014f7b73541300075b735413014f7a735413014f79735413014f78735413014f5873541300377b63541300367b63541300375b635413014f7b435413014f7a435413014f5a435413014f79435413000759435413014f7843541300077b72541302af7a72541300077972541302af7872541300077b62541302af7a62541300077962541302af7862541302b77b42541302af7a42541300077942541302af78425413014f7b325413014f5b325413014f7a325413014f79325413000759325413014f7832541300077b71541302a77a71541300077971541302a77871541300077b61541302a77a61541300077961541302a77861541302b77b41541302a77a41541300077941541302a778415413014f7b315413014f5b315413014f7a315413014f79315413000759315413014f7831541302af7b21541302a77a21541300077921541302a778215413029dfa7690130036fa7690130035fb75901300377a7590130295f9759013003779759013000579759013028efb659013028ef9659
  | 9 => 0x97550230036fb65502300377a65502302fef96550230037796550230006796550230037bb7450230037bb6450230026fa6450230036f86450230037b8645023001dfa735023001df8735023010fbb435023010fb943502300f7bb4250230007b942502300f7bb4150230007b94150230024fe76d91300cebe64d9130004ff75d913002cfe75d9130004fd75d913002cfc75d9130006bf54d91300cebc54d9130034ff73d913001cfe73d9130034fd73d913001cfc73d9130136bf43d9130136bd43d9130014fe72d9130004fd72d9130014fc72d913000cfe71d9130004fd71d913000cfc71d913001cfd70d91300067f50d9130006fa50d9130006f950d91300cebf40d91300057f75591300d57c75591300cebc64591302f5fb7059130004ff75591300067f75591300047f755913002cfe7559130004fd755913002cfc75591300067c755913002c7c7559130134ff7459130006bf745913010cff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff715913000cfe715913000cfc71591302f4ff7059130006fb70591300067f5059130006fa5059130006f95059130035dc7650d30026dc7650d30034dc7650d300075f7550d302ef5c7550d302eedf6550d302eedd6550d3001ddf7450d3001f9f7450d300079f6450d30026de6450d30026dc6450d300cf9c6450d300269c6450d300cf9e5450d302ef9d5450d30005df7250d30005df7150d30007db7050d30035de7050d30035dc7050d30007d87050d3001edf6050d3001fdb6050d302ef5f5050d302efda5050d302efd95050d300cf9f4050d30014fe76d89300c6ee62d8930004ff75d893002cfe75d8930004fd75d893002cfc75d8930024fe74d8930004fd74d8930024fc74d8930034fd73d8930014fc73d89300c6ee32d89300a6ed32d893000cfe71d8930004fd71d893000cfc71d89300a6df31d8930006ee21d89300c6ec21d893001cfd70d89300067f50d89300c6ef20d89300c6ec6258930005f771589300bdf471589302e5fb7058930004ff7650930004fe7650930004fc765093001dde7350930016ee6250930035dc764c930016dc764c930034dc764c930005df744c930005dd744c93001ddf724c93001fcf724c930007cf624c930016de624c930016dc624c9300c7cc624c9300c7ce524c9302d7cd524c9300c7ce424c930007cd424c930005df714c9302dfce214c9300c7cc214c930007db704c930035de704c930035dc704c930007d8704c93001edf604c93001fdb604c9302d75f504c9302d7da504c9302d7d9504c9300c7cf204c93000cfe76d85300bef661d8530004ff75d853002cfe75d8530004fd75d853002cfc75d8530024fe74d8530004fd74d8530024fc74d8530034fd73d853000cfc73d8530014fe72d8530004fd72d8530
  | 10 => 0x96300367d10596300367c1059630004ff755923002cfe7559230004fd755923002cfc7559230036bf745923010ebf435923010ebd4359230004ff7259230014fe7259230014fc72592300f6bf4259230004ff715923000cfe715923000cfc71592300f6bf4159230034fe7059230034fc70592300367f5059230036fa50592300367d5059230006f95059230036be4059230036bc4059230036df3059230036dd3059230004ff7558a3002cfe7558a30004fd7558a3002cfc7558a30004ff7458a30024fe7458a30024fc7458a30036ef7258a300eeee4258a300eeee3258a30086ed3258a30004ff7158a30006f77158a30004f77158a3000cfe7158a3000cfc7158a30006f47158a3000cf47158a300eeef2158a30034fe7058a30034fc7058a300367f5058a300367d5058a30036df3058a30036dd3058a30036ee2058a30036ec2058a30004ff7650a30004fd7650a30034fc7650a301ce7e6550a300067d6550a30026be6450a30006bd6450a30016ee6250a30006ed6250a30004ff755863002cfe7558630004fd755863002cfc7558630004ff7458630024fe7458630024fc7458630004ff7258630006ef7258630004ef7258630014fe7258630014fc7258630006ec7258630014ec7258630036f771586300e6f641586300e6f63158630046f531586300e6f62158630034fe7058630034fc70586300367f50586300367d5058630036df3058630036dd3058630036f61058630036f41058630004ff7650630004fd7650630034fc765063019e7e65506300067d6550630026be6450630006bd645063000ef66150630006f56150630004ff7648630004fd7648630034fc764863016e7e65486300067d6548630016ee6248630006ed624863000ef66148630006f561486300e7e421486300377b76542300357b765423032e7b76542300077b74542303277a74542300077974542303277874542300377b64542300367b64542300377a645423003779645423000679645423003778645423014f7b735423014f7a735423014f79735423014f78735423014e79635423014f7b435423014f7a435423014f79435423014f7843542300077b725423031f7a725423000779725423031f7872542300377b62542300377a62542300377962542300377862542303277b425423031f7a425423000779425423031f78425423014f7b325423014f7a325423014f79325423014f7832542300077b71542303177a71542300077971542303177871542300377b61542300377a61542300377961542300377861542303277b41542303177a415423000779415423031778415423014f7b315423014f7a315423014f79315423014f78315423031f7b21542303177a2154230007792154230317782154230035fb765023030efb7650230305fb7550230305f
  | 11 => 0xef6614c540007b5414c540004ff7648540004fe7648540004fc7648540025be7448540005bd74485400ffe4214854002e7f76541401567e76541401567d765414002e7c76541400073f74541401573c74541400367f64541400067f635414014e7e635414014e7c63541401573f43541400073d43541400067f62541401467e62541401467c62541401573f42541400073d42541400067f615414013e7e615414013e7c61541401573f41541400073d41541400357f70541401177b70541400367f60541401577b40541400373e40541400373c40541400377840541400373840541403477b30541400377a305414003778305414033f7b20541400377a20541400377820541403377b10541400377a10541400377810541401177b765414002e7b765414015778765414002e7876541401577b74541400073b74541401577a74541401577974541401577874541401573874541400377b64541400367b64541400373b64541400077b73541403477a73541400077973541403477873541400077b63541400067b63541403477a63541400077963541403477863541401577b43541401573b43541401577a43541401577943541400073943541401577843541400077b725414033f7a725414000779725414033f7872541400077b625414033f7a625414000779625414033f7862541401577b42541401573b42541401577a42541401577942541400073942541401577842541403477b325414033f7a325414000779325414033f7832541400077b71541403377a71541400077971541403377871541400077b61541403377a61541400077961541403377861541401577b41541401573b41541401577a41541401577941541400073941541401577841541403477b31541403377a315414000779315414033778315414033f7b21541403377a21541400077921541403377821541400067f74596300067e74596300067d74596300067c745963014e7f735963014e7e735963014e7d735963014e7c735963014e7f435963014e7e435963014e7d435963014e7c43596300067f72596300067e72596300067d72596300067c72596300067f42596300067e42596300067c425963014e7f325963014e7e325963014e7d325963014e7c32596300067f71596300067e71596300067d71596300067c71596300067f41596300067e41596300067c415963014e7f315963014e7e315963014e7d315963014e7c31596300067f21596300067e21596300067c21596300367f70596300367e70596300367d70596300367c70596300367f40596300367e40596300367a40596300367d40596300367c40596300367f30596300367e30596300367d30596300367c30596300367f20596300367e20596300367d20596300367c20596300367f10596300367e105
  | 12 => 0xf75d8d4002cfe75d8d40004fd75d8d4002cfc75d8d40034fd74d8d4001cfc74d8d40006df53d8d4010edc53d8d4010ede43d8d400f6dd43d8d40014fe72d8d40004fd72d8d40014fc72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d40024fd70d8d400067f50d8d40006fa50d8d40006f950d8d4010edf30d8d400057f7558d401157c7558d4010edc6358d40385fb7058d40035bc7650d4001ebc7650d40034bc7650d400073f7550d4037f3c7550d4037ebf6550d4037ebd6550d40025bf7350d400279f7350d400079f6350d4001ebe6350d4001ebc6350d4010f9c6350d4001e9c6350d4010f9e5350d4037f9d5350d40005bf7250d40005bf7150d40007bb7050d40035be7050d40035bc7050d40007b87050d40026bf6050d40027bb6050d4037f3f5050d4037fba5050d4037fb95050d4010f9f3050d40014fe76d8940106ee62d8940004ff75d894002cfe75d8940004fd75d894002cfc75d8940034fd74d8940014fc74d894001cfe73d8940004fd73d894001cfc73d8940106ee42d89400aeed42d894000cfe71d8940004fd71d894000cfc71d89400aebf41d8940006ee21d8940106ec21d8940024fd70d89400067f50d8940106ef20d8940106ec6258940005f771589400fdf47158940375fb7058940035bc7650940016bc7650940034bc7650940005bf7350940025bf7250940027af7250940007af6250940016be6250940016bc6250940107ac6250940107ae5250940367ad5250940107ae3250940005bf715094036fae2150940107ac2150940007bb7050940035be7050940035bc7050940007b87050940026bf6050940027bb60509403673f5050940367ba5050940367b95050940107af2050940004ff764c940004fe764c940004fc764c940025be744c940005bd744c940016ee624c940007ad424c94000cfe76d85400fef661d8540004ff75d854002cfe75d8540004fd75d854002cfc75d8540034fd74d854000cfc74d854001cfe73d8540004fd73d854001cfc73d8540014fe72d8540004fd72d8540014fc72d854006ebf42d8540006bd42d85400fef641d854006ef541d8540006f721d85400fef421d8540024fd70d85400067f50d85400fef710d8540005ef7258540105ec72585400fef4615854035dfb7058540035bc765054000ebc7650540034bc7650540005bf7350540005bf7250540006bf6250540025bf7150540027b77150540007b7615054000ebe615054000ebc61505400ffb461505400ffb6515054034fb551505400ffb63150540357b721505400ffb42150540007bb7050540035be7050540035bc7050540007b87050540026bf6050540027bb605054034f3f505054034fba505054034fb950505400ffb71050540004ff764c540004fe764c540004fc764c540025be744c540005bd744c540
  | 13 => 0x96400367f10596400367e10596400367d10596400367c1059640004ff7558e4002cfe7558e40004fd7558e4002cfc7558e40036df7358e40136de4358e400cedd4358e40004ff7258e40014fe7258e40014fc7258e40136df3258e40004ff7158e4000cfe7158e4000cfc7158e40136df3158e40034fe7058e40034fc7058e400367f5058e40036fa5058e400367d5058e40006f95058e40036bf4058e40036bd4058e40036de3058e40036dc3058e40004ff7558a4002cfe7558a40004fd7558a4002cfc7558a40004ff7358a4001cfe7358a4001cfc7358a40036ef7258a4012eee4258a4008eed4258a4012eee3258a40004ff7158a40006f77158a40004f77158a4000cfe7158a4000cfc7158a40006f47158a4000cf47158a4012eef2158a40034fe7058a40034fc7058a400367f5058a400367d5058a40036bf4058a40036bd4058a40036ee2058a40036ec2058a40004ff764ca40004fd764ca40034fc764ca401b67e654ca400067d654ca4001ede634ca40006dd634ca40016ee624ca40006ed624ca40004ff755864002cfe7558640004fd755864002cfc7558640004ff735864001cfe735864001cfc7358640004ff7258640006ef7258640004ef7258640014fe7258640014fc7258640006ec7258640014ec7258640036f77158640126f6415864004ef54158640126f63158640126f62158640034fe7058640034fc70586400367f50586400367d5058640036bf4058640036bd4058640036f61058640036f41058640004ff764c640004fd764c640034fc764c6401867e654c6400067d654c64001ede634c640006dd634c64000ef6614c640006f5614c640004ff7648640004fd7648640034fc764864016e7e65486400067d6548640016ee6248640006ed624864000ef66148640006f56148640127e421486400377b76542400357b76542403a67b76542401577b74542401577a74542401577974542401577874542401567964542400077b735424039f7a735424000779735424039f7873542400377b63542400377a63542400377963542400067963542400377863542401577b43542401577a43542401577943542401577843542400077b72542403977a72542400077972542403977872542400377b62542400377a62542400377962542400377862542401577b42542401577a425424015779425424015778425424039f7b32542403977a32542400077932542403977832542400077b715424038f7a715424000779715424038f7871542400377b61542400377a61542400377961542400377861542401577b41542401577a415424015779415424015778415424039f7b315424038f7a315424000779315424038f7831542403977b215424038f7a215424000779215424038f78215424001cfe76d8d4010ede63d8d40004f
  | 14 => 0x1557c74585500057f735855014d7e735855014d7c73585500057f72585500076f72585500056f72585501457e72585501457c72585500076c72585501456c72585500067f62585500067d625855013d7f715855000777615855013e7e615855013e7c615855013f74615855013f76415855013f7631585503c57f70585500077b70585503c57b70585500567f60585500577b60585500057f76505500057e76505500057d76505500057c765055013d7f74505500057f735055014d7e735055014d7c73505500057f72505501457e72505501457c72505501573f42505500073d425055013d7f715055013f76615055000775615055015777415055013f3e415055013f3c415055013f74415055013f7631505503bf77215055013f7421505500057f70505500357e70505500357c70505503ae7f605055019f7b60505501573f405055013f7710505500057f764c5500057e764c5500057d764c5500057c764c5500057f744c5501557e744c5500057d744c5501557c744c55013d7f734c5500057f724c5501457e724c5501457c724c55014f5f324c5500075d324c55013d7f714c55013f76614c55000775614c55013f76414c55000775414c55014f77314c55013f5e314c55013f5c314c55013f74314c5503b777214c55013f74214c5500057f704c5500357e704c5500357c704c5503ae7f604c5501877b604c55014f5f304c55013f77104c5500057f76485500057e76485500057d76485500057c76485500057f74485501557e74485500057d74485501557c74485500057f734855014d7e73485500057d734855014d7c734855013d7f724855013d7f714855014777214855013f6e214855013f6c214855013f74214855013f6421485500057f70485500077b70485500057b70485500357e70485500357c70485500077870485500357870485503ae7f604855016f7b60485501476f204855013f7710485501567f74596401567e74596401567d74596401567c74596400067f73596400067e73596400067d73596400067c73596401567f43596401567e43596401567d43596401567c43596400067f72596400067e72596400067d72596400067c72596401567f42596401567e42596401567d42596401567c42596400067f32596400067e32596400067c32596400067f71596400067e71596400067d71596400067c71596401567f41596401567e41596401567d41596401567c41596400067f31596400067e31596400067c31596400067f21596400067e21596400067c21596400367f70596400367e70596400367d70596400367c70596400367f40596400367e40596400367d40596400367c40596400367f30596400367e30596400367a30596400367d30596400367c30596400367f20596400367e20596400367d20596400367c205
  | 15 => 0xf7158d5013d7e7158d5013d7c7158d503f57f7058d500077b7058d503f57b7058d500d67f6058d500d77b6058d500057f7650d500067f7650d500047f7650d500057e7650d500057d7650d500057c7650d500067c7650d500047c7650d5014d7f7450d501573e6450d500073d6450d5014d7f7350d5014f5e6350d500075d6350d501575f4350d5014f3e4350d5014f3c4350d5014f5c4350d5014f1c4350d500057f7250d501457e7250d501457c7250d500057f7150d5013d7e7150d5013d7c7150d500057f7050d500357e7050d500077a7050d50007797050d500357c7050d503ee7f6050d501e77b6050d501573f4050d5014f5f3050d501457e76d89501557e74d89500057d74d89501557c74d895014d7e73d89500057d73d895014d7c73d89501467e62d89501476e62d89501467c62d895013d7e71d89500057d71d895013d7c71d89500076e21d89501476c21d89500357e70d895002d7d70d89500b67f60d89500b77b60d89501476f20d89500057f74589501557e74589501557c74589500057f735895014d7e735895014d7c73589501457f72589500076f62589501467e62589501467c62589501476c62589501476e42589501476e32589500057f715895000777715895000577715895013d7e715895013d7c715895000774715895013d7471589503e57f70589500077b70589503e57b70589500967f60589500977b60589500057f76509500057e76509500057d76509500057c76509501457f74509500057f735095014d7e735095014d7c73509501457f72509501476e62509500076d62509501576f42509501473e42509501473c42509501476c42509501476e32509500057f715095013d7e715095013d7c71509501573f41509503df6e21509501476c21509500057f70509500357e70509500357c70509503ce7f60509501cf7b60509501573f40509501476f20509500057f764c9500057e764c9500057d764c9500057c764c9500057f744c9501557e744c9500057d744c9501557c744c9501457f734c9501457f724c9501476e624c9500076d624c9501476e424c9500076d424c95014f6f324c9501475e324c9501475c324c9501476c324c9500057f714c95013d7e714c95013d7c714c95014f5f314c9503d76e214c9501476c214c9500057f704c9500357e704c9500357c704c9503ce7f604c9501b77b604c95014f5f304c9501476f204c95013d7e76d85501557e74d85500057d74d85501557c74d855014d7e73d85500057d73d855014d7c73d85501457e72d85500057d72d85501457c72d85500067f62d85500067d62d855013e7e61d855013f7661d855013e7c61d85500077721d855013f7421d85500357e70d855002d7d70d85500767f60d85500777b60d855013f7710d85500057f74585501557e7458550
  | 16 => 0x8d2140ef421d8d2140ee421d8d21034fe70d8d21004fd70d8d210067f50d8d2141eef20d8d2140ef710d8d2101cff7658d2115edc6358d21405ef7258d21415f77158d211a7e42158d21004ff7558d2102cfe7558d21004fd7558d2102cfc7558d21004ff7458d21024fe7458d21024fc7458d2140cff7358d21006df7358d21404ff7258d21006ef7258d211a4ff7158d21006f77158d21176f72158d211a6ee2158d211a6ec2158d211a6f42158d211a6e42158d21004ff7058d21034fc7058d210067f5058d2115edf3058d21176ef2058d211a6f71058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d2116d7c7550d2115f9c4350d211d7e42150d21034fe76d812121fe421d8121004ff75d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d812101cfe73d8121004fd73d812101cfc73d812100cfd72d8121014fd71d81210067f50d8121006fa50d8121006f950d812124efa20d812121efa10d812116d7e75981210057d7598121226ef6298121256f7619812109fe42198121006fb609812107fe4215812116d7e75181210057d7518121165be7418121005bd741812115dde7318121005dd7318121226ef6218121256f761181211f7e42118121036fa6018121006f960181211557e76d91501567e64d91501573e64d91501563e64d91501567c64d915014d7e73d91500057d73d915014d7c73d91500073e43d91501573c43d91501457e72d91500057d72d91501457c72d915013d7e71d91500057d71d915013d7c71d915011f7b70d91500357e70d915002d7d70d915011e7f60d915011f7b60d91501573f40d91501557f74591500073f64591501567e64591501567c64591501573c64591501563c64591500057f73591500075f73591500055f735915014d7e735915014d7c73591500075c735915014d5c73591501573f43591500057f72591501457e72591501457c72591500057f715915013d7e715915013d7c71591503fd7f70591500077b70591503fd7b70591501167f60591501177b605915014d7e76d8d501557e74d8d500057d74d8d501557c74d8d500067f64d8d500067d64d8d5014e7e63d8d5014f5e63d8d5014e7c63d8d500075f43d8d5014f5c43d8d501457e72d8d500057d72d8d501457c72d8d5013d7e71d8d500057d71d8d5013d7c71d8d500df7b70d8d500357e70d8d5002d7d70d8d500de7f60d8d500df7b60d8d5014f5f30d8d500057f7458d500073f7458d500053f7458d501557e7458d501557c7458d500073c7458d501553c7458d500067f6458d500067d6458d5014d7f7358d500075f6358d5014e7e6358d5014e7c6358d5014f5c6358d5014e5c6358d5014f5e4358d500057f7258d501457e7258d501457c7258d500057
  | 17 => 0x1fcf724c931007cf624c931016de624c931016dc624c931177cc624c931177ce524c931457cd524c931177ce424c931007cd424c931007d7714c93100dde714c93100ddc714c9311a7d4714c93101edf614c93101fd7614c9311a7d6514c931457d5514c9311a7d6414c931177d7214c9311a7ce214c9311a7cc214c9311a7d4214c9311a7c4214c931005df704c9314575f504c931177cf204c9311a7d7104c93101df47650531026f4765053101cf4765053144df7755053144df57550531446f76550531446f5655053100df7745053100fb77450531007b76450531026f66450531026f4645053117fb46450531007d7735053101df6735053101df47350531197d4735053100ef7635053100fd76350531175f67250531175f4725053118ef6625053118ef4625053117fb74250531007b54250531197d73250531007d53250531005f7705053144777505053117fb74050531197d73050531034fe76d8131004ff75d813102cfe75d8131004fd75d813102cfc75d8131024fe74d8131004fd74d8131024fc74d813100cfd73d8131014fe72d8131004fd72d8131014fc72d81312cedf32d8131006dd32d813101cfd71d813122ef641d8131006f541d81310067f50d81312cefa30d813122efa10d81311857e75981310057d7598131006fb6098131005ef7258131175ec72581311857e75181310057d751813117dbe7418131005bd7418131175ee7218131005ed7218131036fa6018131006f96018131024fe76d9121166be64d912142fe421d9121004ff75d912102cfe75d9121004fd75d912102cfc75d91211bcfd74d912101cfe73d9121004fd73d912101cfc73d912100cff72d912100cfd72d912143ebf42d912143ebd42d9121014ff71d9121014fd71d912142ebf41d912142ebd41d912143ef721d912142eee21d912142eec21d912142ef421d912142ee421d9121034fe70d9121004fd70d91210067f50d912143eef20d912142ef710d9121024ff7659121166bc6459121425ef7259121435f771591211bfe42159121004ff755912102cfe7559121004fd755912102cfc755912142cff7459121006bf7459121004ff735912101cfe735912101cfc7359121424ff7259121006ef72591211bcff7159121006f7715912118ef721591211beee21591211beec21591211bef421591211bee42159121004ff7059121034fc70591210067f5059121166bf405912118eef20591211bef7105912101cfe76d8d2115ede63d8d2140fe421d8d21004ff75d8d2102cfe75d8d21004fd75d8d2102cfc75d8d21024fe74d8d21004fd74d8d21024fc74d8d211a4fd73d8d2100cff72d8d2100cfd72d8d2141edf32d8d2141edd32d8d21014ff71d8d21014fd71d8d2140edf31d8d2140edd31d8d2141ef721d8d2140eee21d8d2140eec21d
  | 18 => 0xf7250941027af7250941007af6250941016be6250941016bc625094118fac625094118fae525094148fad525094118fae3250941007b7715094100dbe715094100dbc71509411bfb47150941026bf6150941027b761509411bfb6515094148fb551509411bfb6315094118fb721509411bfae21509411bfac21509411bfb421509411bfa42150941005bf705094148f3f505094118faf20509411bfb71050941004ff764c941004fe764c941004fc764c941006ef624c941016ec624c941007ad424c941005f7714c94100df4714c9411a7e4214c941034fe76d8141004ff75d814102cfe75d8141004fd75d814102cfc75d814100cfd74d814101cfe73d8141004fd73d814101cfc73d8141014fe72d8141004fd72d8141014fc72d814135ebf42d8141006bd42d8141024fd71d8141236f631d81410067f50d814135efa40d8141236fa10d814119d7e75981410057d7598141006fb6098141005ef725814118dec725814119d7e75181410057d7518141195de7318141005dd731814118dee7218141005ed7218141036fa6018141006f96018141024fe76d913117ebe64d9131004ff75d913102cfe75d9131004fd75d913102cfc75d91311d4fd74d913100cff73d913100cfd73d9131486bf43d9131486bd43d9131014fe72d9131004fd72d9131014fc72d913101cff71d913101cfd71d9131476f651d9131006f551d9131476bf41d9131476bd41d9131006f721d9131476f421d9131034fe70d9131004fd70d91310067f50d9131486df30d9131476f710d9131024ff76591310057f75591311857c755913117ebc645913146ddf735913147df77159131004ff75591310067f75591310047f755913102cfe7559131004fd755913102cfc75591310067c755913102c7c7559131474ff7459131006bf745913146cff7359131006df7359131004ff7259131014fe7259131014fc72591311d4ff7159131006f771591311d6f65159131006f55159131006f721591311d6f42159131004ff7059131034fc70591310067f505913117ebf4059131196df30591311d6f71059131014fe76d8931176ee62d893100df671d893101df571d8931177e721d8931004ff75d893102cfe75d8931004fd75d893102cfc75d8931024fe74d8931004fd74d8931024fc74d893100cfd73d8931176ee42d8931176ee32d8931466ed32d893101cfd71d8931176f571d893101cf571d8931406ef21d8931176f721d8931406f421d8931034fe70d8931004fd70d89310067f50d8931466df30d8931176ec20d8931406f710d8931176ec625893145df771589311a7e42158931004ff7650931004fe7650931004fc7650931006ef6250931016ec6250931005f7715093100df471509311bfe4215093100ddc764c931016dc764c93100cdc764c93101ddf724c931
  | 19 => 0x91324ccff7459132006bf74591324c4ff7359132006df73591321dcff7259132006ef72591321deee5259132006ed5259132004ff715913200cfe715913200cfc7159132006ee21591321deec2159132004ff7059132034fc70591320067f50591321aebf40591321c6df30591321deef205913201dec7650932026ec765093201cec76509324bdef75509324bded75509324b6ef65509324b6ed6550932015ef7450932017af7450932007af6450932026ee6450932026ec64509321afac6450932007cf735093201dee735093201dec73509321c7cc7350932016ef6350932017cf63509321a5ee71509321a5ec71509321beee61509321beec61509321afaf41509321c7cf3150932005ef70509324b76f50509321afaf40509321c7cf305093200cfe76d8532015ee72d853201ded72d85321a6f661d85321a7e621d8532004ff75d853202cfe75d8532004fd75d853202cfc75d8532024fe74d8532004fd74d8532024fc74d8532014fd73d853201cfd72d85321a6ed72d853201ced72d85321a6f641d85321a6f631d85321a6ee21d85321a6f621d85321a6ec21d8532034fe70d8532004fd70d85320067f50d853245edf30d8532416ef20d85321a6f410d85321a6f461585321a7e42158532034fe76d8132004ff75d813202cfe75d8132004fd75d813202cfc75d8132024fe74d8132004fd74d8132024fc74d8132014fd73d813201cfd72d813226eee42d8132006ed42d813200cfe71d8132004fd71d813200cfc71d81322e6df31d81320067f50d81322e6fa30d813226efa20d81321b57e75981320057d7598132006fb6098132005f771581321a5f471581321b57e75181320057d75181321adbe7418132005bd74181321a5f67118132005f57118132036fa6018132006f9601813201cfe76d8d41196de63d8d41004ff75d8d4102cfe75d8d41004fd75d8d4102cfc75d8d4100cfd74d8d41196de43d8d414aedd43d8d41014fe72d8d41004fd72d8d41014fc72d8d41024fd71d8d4146ef651d8d41006f551d8d4146edf31d8d41006f721d8d4146ef421d8d41034fe70d8d41004fd70d8d410067f50d8d414aebf40d8d4146ef710d8d410057f7558d4119d7c7558d41196dc6358d414a5f77158d41014fe76d894118eee62d894100df671d8941025f571d894118fe721d8941004ff75d894102cfe75d8941004fd75d894102cfc75d894100cfd74d894101cfe73d8941004fd73d894101cfc73d894118eee42d894149eed42d894118eee32d8941024fd71d894118ef571d8941024f571d8941426ef21d894118ef721d8941426f421d8941034fe70d8941004fd70d89410067f50d894149ebf40d894118eec20d8941426f710d894118eec6258941495f771589411bfe4215894100dbc7650941016bc765094100cbc7650941025b
  | 20 => 0x67f65d81430067c65d81432f79c43d8143004ff75d81430067f75d814302cfe75d8143004fd75d814302cfc75d81430067c75d814302c7c75d814301cfd74d8143024fd73d8143014fe72d8143004fd72d8143014fc72d814300cfe71d8143004fd71d814300cfc71d81430067f50d8143386fa40d81432f6fa30d81431e57e75981430057d75981430067f65981430067c65981431379c4398143006fb60981430057f75581431e57c75581430067f65581430067c655814310f9c43581431e57e75181430057d75181430067f65181430067c651814329f9c43181431ddee7218143005ed72181431d5f67118143005f57118143036fa6018143006f9601814301cfe76d8d421c6de63d8d42004ff75d8d4202cfe75d8d42004fd75d8d4202cfc75d8d42014fd74d8d421c6de43d8d424eedd43d8d42024fd72d8d424c6ee52d8d42006ed52d8d424c6df32d8d4200cfe71d8d42004fd71d8d4200cfc71d8d42006ee21d8d424c6ec21d8d42034fe70d8d42004fd70d8d420067f50d8d424eebf40d8d424c6ef20d8d420057f7558d421cd7c7558d421c6dc6358d424e5ef7258d4200cfe76d8542015ee72d8542025ed72d85421bef661d85421bfe621d8542004ff75d854202cfe75d8542004fd75d854202cfc75d8542014fd74d854201cfe73d8542004fd73d854201cfc73d8542024fd72d85421beed72d8542024ed72d85421bef641d85421bef631d85421beee21d85421bef621d85421beec21d8542034fe70d8542004fd70d85420067f50d8542496bf40d8542436ef20d85421bef410d85421bef461585421bfe42158542034fe76d8142004ff75d814202cfe75d8142004fd75d814202cfc75d8142014fd74d814201cfe73d8142004fd73d814201cfc73d8142024fd72d8142276ee32d814200cfe71d8142004fd71d814200cfc71d8142376bf41d81420067f50d8142376fa40d8142276fa20d81421cd7e75981420057d7598142006fb6098142005f771581421bdf471581421cd7e75181420057d75181421c5de7318142005dd73181421bdf67118142005f57118142036fa6018142006f96018142024fe76d91321aebe64d9132004ff75d913202cfe75d9132004fd75d913202cfc75d91321dcfd74d9132014ff73d9132014fd73d91324debf43d91324debd43d913201cff72d913201cfd72d91324ceee52d9132006ed52d91324cebf42d91324cebd42d913200cfe71d9132004fd71d913200cfc71d9132006ee21d91324ceec21d9132034fe70d9132004fd70d91320067f50d91324dedf30d91324ceef20d9132024ff76591320057f75591321b57c75591321aebc64591324c5df73591324d5ef7259132004ff75591320067f75591320047f755913202cfe7559132004fd755913202cfc75591320067c755913202c7c755
  | 21 => 0x20040008004006000001000401a009008803401000800000040280000020024006023004001801800000a001002000a000000400000000c00000020000000050008000000001c000001006800c000016010000000200a0068060000000001000801600000f000800e0050038014000005000002400000500880180040000008014000019000000000c00100000180040150010000002001002000c00600300300100060005057e76d95431e67e76d954302c7e76d95434f73f74d95434f73c74d95434ff5f73d95434f75c73d95434ff5f43d95434f73e43d95434f73c43d95434f75c43d95434f71c43d95430067e62d95430067c62d95430067e61d95430067c61d95430057d70d95434ff3f40d95434f75f30d95434f67f74d95434fe7e74d95434f67d74d95434f67c74d95434f67f73d95434f67e73d95434f67d73d95434f67c73d95434f67f43d95434f67e43d95434f67d43d95434f67c43d95430067f72d95430067e72d95430067d72d95430067c72d95434fe7f42d95434fe7e42d95434fe7d42d95434fe7c42d95434f67f32d95434f67e32d95434f67d32d95434f67c32d95430067f71d95430067e71d95430067d71d95430067c71d95434fe7f41d95434fe7e41d95434fe7d41d95434fe7c41d95434f67f31d95434f67e31d95434f67d31d95434f67c31d95430067f21d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430047d70d95430067c70d95434fe7f40d95434fe7e40d95434fe7d40d95434fe7c40d95434f67f30d95434f67e30d95434f67d30d95434f67c30d95430067f20d95430067c20d95430067f10d95430067c10d9543014fe76d89430067f65d89430067c65d89434d79c43d89431deee62d89431d5f671d8943005f571d8943004ff75d894302cfe75d8943004fd75d894302cfc75d894301cfd74d8943024fd73d89431deee42d89431deee32d894300cfe71d8943006f671d894300cf671d8943004fd71d8943006f571d8943004f571d894300cfc71d8943034fe70d8943004fd70d89430067f50d89434e6bf40d89434d6df30d89430057f75589431e57c75589430067f65589430067c65589431c79c43589431deec625894300cfe76d85430067f65d85430067c65d854347f9c43d85431ddee72d8543005ed72d85431d6f661d8543004ff75d854302cfe75d8543004fd75d854302cfc75d854301cfd74d8543024fd73d8543014fe72d8543006ee72d8543014ee72d8543004fd72d8543006ed72d8543004ed72d8543014fc72d85431d6f641d85431d6f631d8543034fe70d8543004fd70d85430067f50d85434a6bf40d854347edf30d85430057f75585431e57c75585430067f65585430067c65585431979c43585431d6f46158543034fe76d81431e57c75d8143
  | 22 => 0x4001803000a0020030010008000000800004800a000804000200200000040100000058000000002008004800a00000a8000004002000800400000800000bc00200e002001400e009003000000201300000000140040030000008006000801800a00500a000c028003003005400a0010010000000002005801400e000000803001c008013002c0000000018000000000002800000800700000340040010010014002004001000400e00500580a4002000006000c04c00200380380080070008000000006000005400201a003000400c0370020000048002000803000000d0038008000002000004002400000000a000c0030060008004002002000005a008004801400000100000100000000018030004000000000c02800d00000040060250020008000004003804400c0030008018000008003000400e01c00400300060010058004006002000000402c0000050020000000005000001c0000000000002010001000c00c000000001400e0030030050002003004000c002001004000000a00000180580140000080030004005000000402a008000000800000100300540020020008030000000001000c014000004002c004000012000800000c003800000400b0018000000000002802000400300280000000060008084000001000003402c000002800c00e007001800000800200000080000080038008004012000801c004005001001c00000200d8030000000000001800000c00900000000020000000002000002000000200c000001400e00200000180000010010000000002000003c000000000806800200400000000060000068008000001001000000201700000800000210000018014006000000000c01600380200000190080000000002000000000a00000280000160010060000022000005001c00001b0008040000000014800404a00d0000024000003000800800200d000000c0020000000000018026005803400e0000000024004001003004c004026001802c040000000000000400500000700000060020014004008002800002c0020108000012011000800800c0010000010012000000800c00e015000002c00200400200000320000000004000001012800401e000000004001e00e00b800c000001000004c016000002804801000e00a80140040020000008002005001006c002000005804800e0070038004016000001002c004003000800000800900500500060090080008000002002801c0160000020004024009000000800000100180080060080060010000001010800000200e0000018000000001000c01c00400600380000120000034002000002802000c001003000801600200180000040020040010004001003803c00c0010000014000000003800000800a000000800c00000000380020000030028026008002803
  | 23 => 0xf17291e200000000240000000000f996be6ae33f80018620b818413e11a8a800002d78aca000000000108226d6e580000000002d324d5cee0006bd055421c5a4238a518000d554db26a5cc0dba00034c80003223da9440d4c8b042e04c8cbed2d627a71523ce203bf970138cab97170001b623f1418131143aa06000179c0000000000900cda000729b2a011e54565e8db8208d3700019a0b3825808093dcfd62a60000000000c144b81848a4e41d61d8000c740003ef8b240006bf0000acc00000013a0002001001800800400900100840040000018004020000003000401600301b803c054009000802c0100000010004020000002801400a007002805c002000002800c00000a002805c008000001800400a000002800002000000280200160000000000004000001000000000a001800c004000000000400e005000800000201700080700200020078008000001000000c0080040008064010002001000001801a00a801800400c001001c01800000180080240080040014002011000002400000b00380000040000038028002008006003801c0000018080000001000001400a006000000800000101100000020040018030000000004800400a001002001c000001012800c016004000802c000000004000000000000000000040000010000004002006001400200500f0000006006000000000001900100080040030018048002001002000800a0000000010000004014801800200000000140360160050020008000001000c00200300280240020020000038002000004000c02c009001005800e011001000c00e0010020000004003000000001a002001000c020001002800003a002000000001000a006000000000a000801400400000a000400000e003800c01002300000000080010000004000001001000801c005001012002e00200c801800a0050008074000001002000c0040070090028000006005801000e0000000000002001000000402e003001000000e06b004000800400100280000040020050000002006002001c00002f000003400e0020018004000000000802401803400200000000000000004000002000000c024005002004402000200180500040080028000000019005800400000a00000000120030028044014000000004800a00100080000000000000020004000006001802c003002000000e007005801c004011001802800400c00180280000000008030008002003800001600b005000c0060000048008004005001001000001d004001400000300000080000050000018004003000004400200a000003c002001005000000200a000801c052002008800000200200680080080010048004020006008000400000100180100260010040000010000000801000600100100380060010000014002004000000800000
  | 24 => 0xa600000000001900000001684a50db00e387f48fc18a5da9be0eea35b6f2977800065b00000000000001b30dad67648c25a80000000001e31fe40009e23082f65be492a0c4055dbde00049d000169e0000000000462c893358eb12b82c8000000057000046e2d2c00083a1a58eec000bac6e69134000c090001b180000240d9b7b4e1682863a9b7c4f237f06b26c995e00000014480005800000000000460288a5dcce27ec669995c5fccfa680ab399b07c143a0f08d027040002f99774d176b6b545a5c8f63d492bdc6a74105300000de0003a9a7480e462e000002c0002fc00b00000000003f18e540001331358170342e0a20b111c61ae0e667203c25edae1848e2d5c41f8090218c0002983b1a6c4d40000000026c000000325ba300008e96c503240000000d780000000001d893046244cf13490cd39443b2e1a004d30aa426d017cf3a3b73f400018fa000463356000053400000000008db22517f88a8af60d58000888963000000080063c00009fd47436004d00000001da69a0001cbc000000072ca0ee144379f80de85ce04f0354f3832a000000188077864b10f93f8cd90000000828732494a6900000e906a111590ea4c2260ba0000000000000056ee6243d17a066c3b33e1a905454e2a00010b800016f0000000c0e00000012d00000000002c2d3de00054b384498a4b90000000e1adaf12515f800000054e10c0d4e82c1a90efda1e00000000007a400000000018b00495882239b880b62c0b0b0c6400015a86580000004030000000000579269c3dcc6f0e7268c0000003969630892281730800056c4a94f3303c5ba1a564a0fa42dc0000000000eb4d9c21b00000700002211aa51ba8162af13cc000cee56011556ea4c726e8afc0000006391cc19ec0001f218713387a6000114c2ce1b630ca21c000d414de00003d200061e800160e23b000204462c0c70000000000de21c78c60000000555800000024d00039d952a7c400012084a400000001d479000056d26acafee3e00011204b8cde0000cb86aa0000002f38976d0c0000f78d0e00066794b45b22cb0001aa8000554676000020c7761900000c145f60868000ae298f000000000005312880011ac59b4d680007da00000000000008c423600011403854871a00000e225b38e240007fd314abb4f223a800806087f22834d9a7d1b9e271000344910c5054fc85984685f2219126c00061e0002c31cb811d7200b30350bf63dd2fdd96ee4c0002149662d742ab84412164c24f29950baaa6758920a51ce6a12a9140562e99444f953d902dc56119f905e4472310a490a623c711133300da0001f91cd8c56a751160da984cda70930a11048790000000000000063b0000b980000000000000000000000000000030b96680008b10000d8800cdd650d1fe9bf096614339596d40006f
  | 25 => 0x8e267964e3100000e70000c4a181164c00074b0bdab402a07b10161494d62e6547d0000000518525800073ec4b0000f757ea20d3d9282cbc8a6c37807fcb14a594551f9800096828ea0143ba35033f000013a10f0faabdc0003ca73f030d86480e28a0854000000000000067200001b04a550cd6347e0001006000449053800084200014b81a0c2f3e89781bb60000718d00000894707b36c0000004879dc00003c11db0d240007b073a2b455bc0004ff18a000000000001a80002df3ef1b313aac47446b5083ac2fb36923356ac1955cf91e4112578379a33865e09553ea9558f80502a40ec85fe9155c2a0556de50b0eca5fc3b07022caaf20b54e7146f2a3862214a25407c4cc400042533040007542ae8abc0e2d4417a19a800048a000397cb3ebc924f94898825536fa35fc6ece6c6f61d642d61f62350ced330bec72a194d0c2e1625b8a755f4de86e41c14a640dc27035995eabb04fb9e942bec0b0cc9088694e6a03b378491ab2437e2ebd37415b2d600007c0c1b57ea7d923e17069312c16a2dca154b9ada347ef00393300524ef5e99e1530ed9271485ccb56b861529d09032b7843f1f1400002844b95a521097163a0000520a224058000b4a5f534eb52862e5b561203a80000002a5000000033471d1e85014555000060d22000042b8001034d6c36a00015588c34a700014d00004cb0001924237073800079c54300c26044f4e073a69f5971e72041c800007200000011fcfba5a90000000a6e0002a880018f26450000000000a42258941000000001d9c5c000914000384c00000057d8000ecc000377000074a07c0e90001bee614000279c000e10744a688ede93d1a78984fdc12e741264417e2326dcadf9ba8bb937d000000000051380645deb5400022fd3a8b4c69d130c3bc75f0000f0c0000001908000000a1732cb32c6f43270002e34a2c6362c70000c1600000000015929303d1b074e42ab04ad00000001f366fa5f84b276962700009ce000296258967c00000029d002ecb129e396d5309852bd2fa83947ca176b2683dacef3e38001c4826e56f81981a251a642a8d5634b874a7a434bbad9d0b50c152e6b2c1c20f9cd76c1603c0ea8000a7e00001053a05d36c79c892f600000000000000cb0000c752ba13f1bb9b6c0008385ca18e016217810281000007a23c5b7680001f7255b0013bac5346098a8d6ec0e00026480001190000f68000d5c0000a444d83b84e18c1d1e03ae4b6a38525e0005390e78cba5e200024b193c95428136257aa0000000000a36345000010c224266000151d636c390000f5d856000559256400010966a1d3c0002a04eb8000000de367117e98aa7390fd9f3900e58900013c0218b233c02f142d842f56aa9991d4d5b4602080f84000651a89800009822d2bd048c00001128104067290001c710
  | 26 => 0xbcee864be000028200000000001ee1b90002a753e2000000180cee234331286183a25b950a0001384000499b395672c2a5ae9dec3c82f66611c306c21d50001b647be00056b8000340c780000000f300001988b1000086c00016c5a6600000011889241930000000000b092ca079d7c0af11ac0625b8e2a8312156855cdfc6b226bc06804e3be20cd5d2e3f63f3744d1e8d0044025c0f211c537b15c62acbb1f41719b3cdfd08c1184298bfa435803c1e84bd36eb4b082e3ee309a76c000000000348483650d5ad29257386bd5b0270464604a605350c4180000a68001700bd061a9f5470c00061f3531820000000251d16e86e58b289000061a6b49fc42869cb000000057ca500e98000dfaa900003354f66af94269cc502027e01b9b61c3e4fc0002cdd1440000001b1c00081b0000001064000000000179e00000000000000000fe1ef12f0b022bc8a1da9230f26f00014860001c1b4950f2313352b23c0c251f1c680000000002b70190000000000000175a6fe0679e589c2000000304c0000ed42c3270000ba000003c40003fd5530000000e05000000000000042200003e023f5e08c680a821e33e10f00004e6467800000000024828058ee91d6008095c9ad7600000003c276e0001e5565600035d348004c0000000b3404e0000239d84000b4e30027914b80000000db423c01229f8561918cfd3330000ac4ca637680c400080052205e4000616000000089c00009535800ca2e000000f92ca24525280014a63a634ab1b439a6da575180964488f3731f6c036b0500688b533e1245e5162d43e0000003118a880f60779218000be50001fc910a8960002d85288000126200816ec045c51e3dc9c0000002aa161c38145404d8bd65e3090a725890bbc1962270c185610c58001b7ae8300028300002505099665a48396000135c000404425b111570000418b60d75624b45aae656e6a3700010dc0000005d2988800000000030680000000000df10683993629bac1b6000183207400000004a0000d349bf09113ecf18e2700028e09d80005c08000d144405c902d4910893000057000000072cb27c0003b94bb242997e06c456016556c9b9719868c6e45be2a7065d73a84e07f31fc824b28372a8f00eedf63469464bf08af045215445e58600038c45800003a30000e307cc5f18e88ffed3b2db9c058302b144c1724e2800000024d80004f612f8ba587400000034716e2a5a000382db6e3734de80012460000000000bb223a000048d4b600017c0d8d1ca00000005c99700ae000253400000049080002fe002000000111676435919e852400000012f858e0903cd8d513b2d6b4c825a45ca9e95513328000a88171951809a0f536a828400000062e9040b9e0f8507213d234ae65caa38852e035578190949e84370638bd2040004c100017bcd4b1
  | 27 => 0x23408b84603a06beae0c53e0002bb9d0126eb793f500744c0ddf32500004d0a840002c191a400000000008f0a360000001aa40002de35c0f5879e5a38f34beed6e6d31070c98e0453123287a80e2082a991630922234af0922c21316f318520a8b800001f434c2ac253204c00000000000015820003a280013125d1428a36524c0000000b50d26acb1000000e1e6ce59830a4d9ec6a12db5e543800046395c80000fc66393f57b662c00034a8850b342841d80d9a1a46f72e59a9cb0d0228000f14b635639cf14125a86c018fd1b08c869c94e086ae1e18033586567e26f5b1804523a442f021994a62312b81c1a7813c1ab800093000038809216220da3df209505448e01f99a52a227d00002edc8407f0a3142517200070e85a000012c000000000070a0001d410e633e00001480009611fb800000000024b2c0ce46c6e0fd024433a1390000001294d103ca1d8800000000006a801c4290000da1b300001650ed59640005300d18b1a0f92ba0000f7a35a5572bb9954e3855e814536e88163332d848e0964a610e87fc2115650e6152409c39c3638896bfe674b16cc1c7432ce8c10000b3d0d90f59b4a9033c71f3c0000005e9087d4940000f59b1149a0004d080000000004ba842c448d0a000000107c00000000000000003778001caa0000000000f720002e29db000000000037cc0005730002a940000ce638a0240ce28c000193c916000000000092a0000002ddc00017e000000116801e59aa1a543cb7c4e037e4000000554800000000053880017f60000359834000d5d27d0154000000506b618d80394731b67d07e18c4570cd4226000000000131c00000031787aa73e1038fbc00082627a8ca40000000001eec842c426640000c925f0000071800000067080007520004ac0a14fea79f1ec2a4cb30e19129ac7d6ae0000f10000b240003bf2fe0000a21000000045000000011dc00063b00000019a483c13d8f01d10d306919955ab400028639b82629130001811c1a2b24958000000ab71e2ba15b366f54339bc97dab440458fd08cab4d56219216dc044062a4fce6e2bb18606619e45ef5439ddc11a1445cd328444a6c246b8b9c144733483a9fdc0428d441a7ad06a40762cb8b5284e09371a8fd58c9d158f25d000000013b22f545e00005d0af195a30a0e2a7797981775d08a090ccc6807000017ac3eb671800000000001500000005c13c4ae8940e5ff678b280000a632c88000af6b662ac00009a4e360000000f0e0d70002c0400000004990d0cace5a5080b6800008731a2939c8cb3f3a382e489ecc574700804acad46bf1b05868d056d500010b484755f00004023742a09e0800000000001e8000000000000000072f6e0800000000000019709aa000000012cf68c255821190000000000000000000000000000000000000001
  | 28 => 0x636e18532b209968685642047d4f2c2749280016ec4d047dab086e0b8b00006d00002b441bab85a6a00044ea694fe071d00000300bc0000d600019a20000ce33ac71c267093a08cde2e2640680000000001921b44e0e0006e0000147a8da6a805d1cea5e90002e241be0c66cbb334dee00000004202b22701d5b25c8fa3fa724889890ab26000152c95c72831a8e28000acc597800000000000000000000000002d08000000331a120b7eb626b12e30d70768000034cc8e83d3489c64c62890000114852c22b1d380000005684b7150035c3880d8800189ac2e171392c2fa0006228d9072ea4820c0001bea000000000159a41900000000000002d680000007c66832050feecac664a7b4fc2ba700013b53b0bd100008a852600300000000c08f30f002a94502ad62d2b742f4e5d1013a041b200007f91750764704a90a55c8ab295f106dcac01bc3271428488a035538ffc37a4c95da02c1832bb60721fb400021d000255cda000058538e40000005fe0000be6000724386c0007926703501a0e5fd19d2ea19f217146a9054000cf063d2edc00019416a800000000016803980009840000001a1a0000c8ac95686d156bc25c9a285396d936a467a4a1221ad240001cf392a6f9566000619915c0004ee1689d44e5c34253690180000001b48e8c206bbf00000000000c000031415b8000000078c00052b70031b08b6000218ade8b3c42d6d12c640004fe0001d617524df52000003d800000000000004d46f000000000006da08f192ae4a4592d18ba418e01d05f19a0a47127a45c4aa00000026b17e0bdd3440dd5c6e35624b9104ba84020001119a12e681e8800047200029326816ca2e123a9a1194e0000001158d6c00021280008dc6773b69a89546ba46b925b00006523ab8000b760233aa800000006818180002766725fa12fd05a73a33a80f40badc92f0a579c7a00041b00000007a400026d4c029a642b2c3c3900832ec37ec00061851c9cb0a74a024dd8f71574a05465903875e0a36eb8c78bda1be35834a0b0442a2c192c978601310907302eac510000295a000000003665c1000000015305e6aaf00e0054cf073b000259c0000f3000000000000044f0000000000000000000000067fa9dc2dac6735603a02005a3508af1d63a9fb6ca8000cf66ec01732880002413079ea0cfa8f24f1aa7cbb400046100018c4cf550d9c7cc4c8600000a78000bf22488000c228ee00000000005af0002b65d169fa000000006600026400000005036a3b5ccf6e000609000090800022c80002900000002a3c2ac1f900000011486e41bc80000000004be88e00e600000002f93149a80001b59932abf0000f645e20003cd03c800000014424a180a8cc6ac8000d9400000000000000007290000336dc3688a591462c910f306795e67aa0da96e90b20a7
  | 29 => 0xb2e243b6acdc04890001ae400098052e9bd8f5e3e23ab1068000c544ccb0fd52edd230d9d289745235d881a437e2642b3888000253554d990004230e16da464214000289a71d2ded314443021c566c81c92505c76bef6b084ac2b455f28a8d050f0d1b28e064025ad675428fb0eb678d37d923d2f202d1f0909142437b215a66d27800073395b000000010cab21c686c9575b739c8664100023fc00000057183b873a000000000115200000025e95d0de615180007a00004a814cc0007da09d076c0000002aca8542a803c11199bca403ea00006e828a00053c0000000000319b01ca3c8a35c818dd6d800066b95d4000000000000151675d6c0800033400033283b04a84a36602f8484c92e00010fd15a1ea3d019c19fc00049a0f6c00010700032ac000d9406090e0056b982672734000aef73c8e31c6477a1c39f2066e4f43e6800130cb3c70b8000000a2571439619f62435b697348ec9002b81a408101bb49d8bc17042334e99559a326510dc1d246fa93234483287eca162eb98e4bf6000000103081ec90624a02112254900004d48c6a523d711ada7e1dc14487bdabcd8b73980000000000000001504e1c16c30300000003f49b7117c12519980013d0000000355c000bf94cbaf50d387cb000237c0006b5000161d65a0006ee80000004aa0001aac00000022fa5ad0e20003931c91cae0000001d9503e00019432c16408fd4e4013cff06af34c982427a74c00038540003d3351a2296287930001874fa8a5447580000000005699b79b5a4134da0000416e6f0002a69aacba30001f480000004ef8bad0fa9f526ca9cc59c81221e9200e88c4c5b834119c8bbb177300d56a0007400000e9c9ce00000007e6000000373000069b0000001770b2a5ada8c9ce0e121b28000000a6a272aded460d3d7452e38d046943e49f9d20c0005aa8000bb80002c280006be00043ba3981326462e81d2046a00000002a000061500fb2759dabdc45980007f6cf7684000000000800033e085800032f0000384152000000066000000017080000000c38cb4be80000000000d2400027c8eb4ad42725e31af96944e400000002962a100000010181a95a09388ea40000000f940000005f580000000000cf8000cc8cea44d006905ee7d60b80011c0e8d25b24718448ec695ab58204b840568d7494e6794158b5864a46d2378ec1562a2907809f16389ee15392b41525b05a981d0e56c37601000159e20e0211bfdcf4e060758001410b48632800000098c07d00002340000a78000000cc32d380015c000000000001ca63e6afa391c82e726bd97b87e05214230d44f80d181378000acc3fc0000824b0872a00000009b03cb0311c2499a4c01af088405ea8d10212797d2d2f0001490000864498aa800645ec00000000005975d536d98f6a99228075
  | 30 => 0x80fae9ff34b26753e463d3fd9f703aeabb1c1349c236bd70002da1a5200536b932944634e000222513604c7239c012244232fcae5d9b415d0ef9c19092c4319fb4f82c02f55ae16e0582000132b6849d65644719dadbd2000000337081600a3dfa7cd7e200045b29f0000c2112480006889cc13aabe0000ddc3030000cb40000408000000c3c1ac886cb8847a5d30000b908ed310124c9027845449fd17be13064504443a0dbc000340c9c6bbd0d6b74d432e7f4f0b4d929200039a80012be3710411f60380cbe74200000004e816294f80008a55bf8000000c1c3d3aeb91d076a5cf262c978e64233117827cb3809a36d5bb01c3455b9b5c340c248d94a84301635462011b1ae030f28000fa015e44c9cfcc4e5e600000017e687051f20618c89ae2560310fe6a9e0002881c02d822dea09c2ec8c9000242400041f00024058c60001df000000000000000010f82c243500000001530003398000df12e3990d4a23cf58a80000003bd0180a28d5077d38895d92c018400006c00008ef0000000700d6f059b8f0938a0a649aa04f028c529836686cede428b93a96e8850393a05d61092d1cdb47800000000000018bed710001288c883264d833180003ba5a000000000002830000000ad8000000000000022c35352703c94a431ccce60001d085a4484a6e05580000000000000000c3e5295001a39710c86359b5a8b1e56d6ff896983c31449f27f4ff80004f833ccfca0001350334b4429a47a00000000000003754000ca918c8000bf80000000000000b6438d8000000c8b3b9800022c58833608f99300002b7a83d6faa706c981ecc104db00000000000000000001bb240a4dc353c4202fa000000000000049c80016420007108a710eaa69139a1ece0656b0b093c46de00455a1a0d78827800020714f634c4902c4cf06713728198179630106e869c948a2b0b29cd00001144888000d3ee3066e95f0788500000018d6648655e6b0340000004a18000df22b01c98001bf4d684401319cf82943460829a04280000000186057d48639a49a2dc66d1850000000000000010981f25f429e8a7a7745a83894000d1f6738230b6809f14791d18a46c314cad64000ae551a000083c4d3000295d1eab720fa39ed23092700013c91f2d480002d154bc7125169a90768d540002188000bb2000217c000c833ae00005b8a5f000135991cc0600021b40000006d22f9cb6c87645d976d91ad776cb0d4d28000043434393f037e00000000000925f70b9830a0000000000e7a5364110158d5a69e00012cc47a1c90f400005c800000012e0000000345b07c00000018f81f8d2e4110001d793262c622e2af18d23781078a6d9486ea13132e560063009b863c0000a000036ec0004ff4e7b170ac69ea24a000173604600000000006d300028605740006be29594c200
  | 31 => 0x361555aa83522932c31a47b561981593681e374b45800020860882383446e100037780b600043f8000d9600061b19b80007ad0002aa80008a61513631b70dd042eaecccb02fd3c3000177c99a0002f9000006e0001c6800000068e8704cec8d163582152b635c6740b3d7fe62f0000000c5a00053580000003910002780f6c0004ed08d90e450e2a6b220e102ea5170648d0c6bc000137195c4513281005b7cd875a925587ea49d1cd33d0f321fe38a84541b07b84413310ce8c281e639e18acdc233399344eea3b54a02118400006598ae5b7e0e102d02f197898353b225469a2d3640172c15eaa11031ba05168212c82dac6d86b400023e0198000040177ca5e3f83b90000000000728885080a00002c165911800024d1c5914e71e569388d2d4b9157217a8ece0fb4e2391084eac54a9a5541a4000599a0b828e5d63d585905d825d19c0c2c4386e7000000000000000000000007883ff354c42c54245d0e411a6e4f47f27b02928a137102904c690417ca6206789956f50af5b082ab15222f002805757e156cb6653b2018ef0284cba127143d85a0b2241a8cdbe00b407e845c51c85406f2a28812a466c82515aca2d22502d602700004eb00014b015159d0589b22dac161aa45a7085b422abb0000d2220699845aebd871600000005a000010e40009dc12f000015818000030e1aea3473ec8001b66b3657f11f1ccc2f70088f8d9f8d13573b5140009aa15502f4fecaff4202f68ef221a56da8b0b64d0b6383518ab82174c68001726bfd1a40000b5c1812a82f0110879760a8cc8be28f7239ba1c38800002417940007d3000108000000009400008ce0000000000000b690001c39b5000000013a5b10cb5000000044e4994a5b6
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe6761d4062440011df04bb284880023de05765091000673108eca1220028bc8759142440091dd0fb1284880023be09764c9100047bc0aec99220028ec821d932440019cc423b2648800a3721d634c91001c7743ec49922000ce462dcd41440091e90eb1a82880c6b920963505102147b436e4a0a2031ce462dc9414407d5cd0db128288113391db6250510216733b0c4a0a2042ce4761894144001d4ec831282880c7a91894250510005f0c10e0a0a2000ce462dd1314400d1e90cba2628800339189744c510034f8402e898a20038f487591314405d5c904b22628810a3da1b724c51017672316e498a203eae686d8931440899c8edb12628810b399d8624c510216723b0c498a2000ec763189314405dd88c49926288002f8608704c51043e72316e890a20068f4865d121440639c8c4ba2428820f3918b73485100347a432e690a202ece4625cd21440055cd0db124288113391db6248510226f1b90e090a2006a7880d9150440014df04b22a0880a29b20964541100353c406c6a822000a6f8258d50440514d904b1aa08810a9ba1b6254110227b0086c4a822044c6f70d895044001cd6e1b12a0881139a903625411022735186c4a82204aa778158950441474f700b12a0881129ba18625411021733b08c4a8220a2e6b601895044085ec020312a08801a9da1b715411000732316e2a822006b7280dc5504400d4e90ca0aa0881df991894154110035b840282a822006a74864c550440edcc8c498aa08801adc20131541100353a43242a822028e6462485504400d6e10090aa0880033918b7150110034da43a82a022006ab48650540440d5d48c4a0a808801aec201415011013e3c3b2a0a022000e3b645414044055c70c8a8280880039ad89505011033f34312a0a022027d70715414044001e6282a8280880033918b714c110034ea43a629822006ad4864c530440b1d88c498a608801af4201314c11013e3c3b2a09822000e5b635413044001cd6c4a8260881579a189504c11013eb838aa09822000f513154130440017c704a0c40880c7b81894188110005f1c1263102202eee0624c620440279c8e3b12408801a3da1b714811005e72316e290220069e487485204400d5c90c90a4088007391d92148110035f04024290220a1f6350485204404f8f0eca8240880a39a189504811013eb838aa09022000f612154120440279d0edb12408800b3a1d94248110016743b264902200fcf076dc520440039e0eca0a4088003e8509414811000e783b2629022000fc1324c5204400d7c10e90a40880077821d2148110035f1432429022006be0864852044005dc10c90a408800bb8dd9214811000ef13b2429022001de0764852044005dc0ec90a4088007381d92148110005f1c22429022000be18448520440017c70690a4088002f860d2148110
  | 1 => 0x3003a2cb080028fe1173596100051e422e6b2c2000a3e841cd658400147b0839acb08003175cc735961000537410e6b2c2000a6d821cd658404f4ed0239acb080029d60473596100353d400e6b2c200ea79801cd65840010fd0e21acb080021f61c43596100053741086b2c2000a6d8210d658404f4ed0221acb080029d60443596100353d40086b2c2000a798010d658400d4f501392cb0829a9e60272596100053bc0ae4b2c2027a74815c9658404f4ed03a12cb080029d60742596100353d40084b2c2000a7980109658404f4ed03992cb080029d60732596100353d40064b2c2000a79800c965840011bf06baac90800e3720d75592100067210ee4b2420008bf845d5638400917908baac708003390877258e1002c3e42eeca1c200087f855d9438400b0f90abb287080021f61b7550e100043f43acaa1c200087c875954384001c3886b2a870801a2f21d6450e1001d4e41ac8a1c20068dc8758d438400953908b1a870801a2f21d6450a1052f5210ac8a1420068ec87589428400d1b90eb1a6508293b1085634ca100347643ac49942000be381509208406fbc0e2a124108002f8e0532482101a6f038a64904204a8f7815cb64440031e902b96c88800237e0d755911001c6e41aeab2220008ef825d564440051d904baac88800a3ba1f725911000672396e2b222000c6f72d4164440f38d8e5a82c88812a3de0572d8d1000c7a40ae5b1a20448ec86dc9634400117f08baac6880122f2117558d1000477c12eab1a20028ec825d563440051dd0fb92c688003391cb7158d1000637b96a0b1a2079c6c72d4163440051dd05bb286880023b60b7650d1002c3f42ceca1a200087d859d943440010ff0abb286880161f2157650d1000477c12eca1a20028ec825d943440018d8c5baa86880163be1d52d8910216373b6a1b122013ae6811d362440895cb023a6c4880038bd5254d891000477438a9b1220008ed87153624400159d062a6c488002b360c54d891009d73408a9b122000ae58115362440895d5002a6c488002ba60054d891009d73408e7b122044ae5811cf62440011dd0e29ec4880023b61c53d891000557420a7b122000aad8414f62440275cd0229ec488002b960453d891022575400a7b122000ae98014f62440014df0aa1ec4880029b21543d89100047743887b1220008ed8710f62440014dd0a21ec4880029b61443d891000746a1887b122013ae68110f62440015cb0221ec488112baa0043d891000574c0087b1220008ef825d562440011ef02baac48812b1ddc7505891000476c3cca3122000ae58199462441455d301328c4880023be1d651891000573c0aca31220008ed8799062440015cb03320c4880023be1d64189101f573408c831220008ed8798c62440015cb03318c4880023be1d63189101f573408c63122042
  | 2 => 0x1744c92001c7643ac89924034ae48159132480851dd0db8a64900d339187714c920005f0c08e099240058f78754761480955c90ca16c2900df399d942d85202557243265b0a4034ce6764cb61480858eceda86c29002eb9a0874d852025572c10e9b0a4000e375495361480011ed0e2a6c2900023d61c54d85200056b418a9b0a4000ad58315361480175cd042a6c290002b960854d852025579400a9b0a4000af18015361480175cd0439ec29012ab960873d85200047b438a7b0a40008f58714f614800156d0829ec290002ad61053d852005d73410a7b0a4000ae58214f61480955e50029ec290002bc60053d85200053bc2a87b0a4000a748550f61480011ed0e21ec2900023d61c43d85200053b42887b0a4000a758510f6148001d2a8621ec29002eb9a0843d852000572c1087b0a404aaf28010f61480015e30021ec2900023d61e651852000572c14ca30a40a7af18099461480011ef0eb28c290002b9e0965185200047ac3cc830a4000ae58299061480011ef0eb20c290216b9a0864185200047ac3cc630a4000ae58298c61480011ef0eb18c290206b9a086318520215734328430a4042ae4865086148001d4ec8a10c29010ab9a193218520215724326430a4000ec7634c86148085ccec5a80c29000339c84765052000c5e43ac8a0a4037ea46150941480091ed0fb0a82900063d204764c52000673908ec98a40018dc8758d3148069d88c2992629000e3da1f614c52042e7230ee890a40068ec865d1214806f9c8c2ba2429020739187734852003476432e690a4034ce4615cd21480035cd0db0a429012b391db6148520256f1b88e090a4000a7781591504804f4e902b22a0900029de05635412013d3a40ac6a824000e6461dc9504800d6d501b92a09001a9b21942541203df3230a84a824006b6880509504800d4d90c992a0901eb991853254120035b440264a824042a7686d855048095ec041b0aa0900039cdc3615412025739206c2a82404ae7230d855048085ccec430aa09028f9cd806154120217b0100c2a824006a6c86485504804fcc8c290aa09001ada20121541200067230ee4a0240069ac87509404800d5590ca1280901b7a91854250120035d440284a024028c78765414048001c76c8a8280900ab8e1915050120146b4392a0a024000f29425414048001ce6c2a82809019b9c18550501200067230ee498240069cc874c9304800d5990c992609016fb1185324c120035e4402649824028c78765413048001cb6c6a8260900a35a1c9504c120007a4992a09824000e736154130480a9ce0c2a8260900030fdd274596100052fc1ae8b2c2000a5c835d1658400187ae83a2cb0800297a0c74596100052ec18e8b2c2000a6e821d165840014db043a2cb0809e9da0474596100053ac08e8b2c2006a7a801d1658401d4f
  | 3 => 0x3202600699c8750d404c00d5390ca1a809800f271d94350130035cc40286a0260abf1b5050d404c0d18f2eca8280980a71e1d950501300071db22a0a02602ae3864541404c001ab6e6a828098003c650d5050130035cc43a86a026003d988750d404c00d7350ca1a809801ae621943501300274c43286a026004e9b7650d404c007b34eca1a809800f661d943501300274c3b286a026003c987650d404c001e370aa1a80982afc62154350130566cdbaa86a0260acd997550d404c157d36caa1a80982afa65954350130005cdc1286a026000b9b8150d404c001733089928098003e25093250130005ccc2262a026000f91414c5404c00187ee93a2cb1000297e0d74596200052e41ae8b2c4000c3d741d165880014bd063a2cb100029760c745962014537410e8b2c4000a6d821d165880014ed023a2cb100029d60474596200353d400e8b2c4016a79801d1658800147f08b9acb100028f21173596200051f420e6b2c4000a3d841cd65880018bae639acb100a29ba08735962000536c10e6b2c4000a76811cd65880014eb0239acb1001a9ea0073596200b53cc00e6b2c400087e8710d65880010fb0e21acb100a29ba08435962000536c1086b2c4000a768110d65880014eb0221acb1001a9ea0043596200053cc0086b2c4006a7a809c565881554f30138acb100029be09715962014536412e2b2c4028a6e82d0565880014db05a0acb1001a9ea0041596200053cc0082b2c4028a6e82cc565880014db0598acb1001a9ea0031596200053cc0062b2c40008df835d564880071b906baac9100033908771592200045fc22eab1c40048bc845d563880019c843b8ac7100161f2177650e200043fc2aeca1c400587c855d943880010fb0dbaa87100021fa1d6550e200043e43acaa1c4000e1c43595438800d1790eb22871000ea720d6450e200346e43ac6a1c4004a9c8458d438800d1790eb2283102a7a908564506200347a43ac2a0c40068dc8758d3188151d8842b1a631001a3d21d614c62022477c12e3b2240028ec825c764480011bf06baac89000e3720d75591200047bc0aeab2240018f4815d564480031ed0fb8ac89000339dc871591200063bb8ea0b224075c7471d4164480891df04b8ec69000a3b20971d8d202547a436e2b1a40008bf845d5634800917908baac6900023de057558d2000c7a40aeab1a40018f687dc563480019cee438ac6900031ddc75058d203ae3a38ea0b1a40018f681dd943480011eb03bb286900161fa167650d200043ec2ceca1a400087f855d9434800b0f90abb286900023de057650d2000c7a40aeca1a4000c7461dd543480019c8c3b9a84900123b21d63509201bd7240ac6a1240428ee86dc5424806f9c8c3b8a8490002f860470509200067230ee899240068ec865d132480019c8c2ba2649001a7a20
  | 4 => 0x14c0b7b8842b9a42980a69e603645413058f1da06c8a82600087f87591504c00b0f90eb22a0980025721d43541300352e43286a82602ae1c6450d504c0ade3680a1aa0980a69e60362541300352e43264a826055f4b204c9504c0534f301b0aa09801a9721931541302a7a988262a826029b5883dd1504c001e3487ba2a0980029ee19745413014d3c432e8a826056d38745d1504c0016b706ba2a0980a6d620d745413058f1d326c8a826074a7a87d91504c0474f10fb22a0980038edd3645413058f1c3a6c8a826006a7b83d91504c00d4f307b22a0982cb8ed0f64541305971ca1ec8a82600097b87591504c0352f10eb22a0982c78e19164541300063dc3ac8a826005a7a87591504c00b4f10eb22a0980031e21d645413002c3c43ac8a826073a7b84591504c001c7708b22a0981a29ee0d64541300072dc1ac8a826029b5a87dcd504c053ab50fb9aa09801ad6a1b7354130035ac436e6a826029d5a76dcd504c053ab0edb9aa098002d66137354130006adba6e6a826000d5974dcd504c0016b305b9aa098002d66077354130006adc3a86a826000b5a8750d504c0016b10ea1aa0980035621d4354130035ad43286a826006b588650d504c0536b708a1aa0980a7c6e1143541302b78d3a286a826000f197450d504c001e36c8a1aa09815bc61914354130005adc1286a826000b5b8150d504c0536b107b92a0980029ee19725413014d3c432e4a826000b5b835c9504c0536b106b92a098002dce0572541302a5b840ae4a8260b0e6862589504c0016e702b12a098152dc205625413014dad41a84a826000b5a874c9504c0016b10e992a09801ad6a193254130035ac43264a826000b5b844c9504c0016b308992a0980a6d6e09325413014fa5c1264a826055f4a724c9504c001e92e4992a098003d2d8932541302afa431264a826055f4a424c9504c001e9284992a098002d6e05325413057fa510a64a826055f48214c9504c0536b107b8aa0980029ee19715413014d3c432e2a826000b5b835c5504c0536b106b8aa098002dae0971541302adb4412e2a826000b6b82585504c0ab6d104b0aa0982bb9c185615413014dad41a82a826000b5a874c5504c0016b10e98aa09801ad6a193154130035ac43262a826000b5b844c5504c0016b30898aa098002d6e09315413014dadc0a62a826029f53814c5504c0a9ea4e298aa098003d45c53154130007a9b0a62a826054f50614c5504c0a9ea48298aa098003d4505315413056fa990a62a826054f50214c5504c0014f70c90aa0980029e219215413014dad41a42a826000b5983485504c0a9ec04290aa09800356e0d7590130006ac41aeb2026006c7b635d6404c00dab6c6bac809815b5690d75901302b6aca1aeb2026000d5b325d6404c001ab662bac8098003565d53290130006acbaa6
  | 5 => 0x80030f5d0745963014d2f418e8b2c6000a5d831d1658c0014dd043a2cb180029b60874596300053b408e8b2c6000a75811d1658c00d4f5003a2cb1806e9e60074596300053bc0ae4b2c6000a74815c9658c0014ed03a12cb180029d60742596300353d40684b2c6000a7980d09658c00d4f500212cb180029e600425963000537c12e2b2c6000a6c825c5658c0014dd05a0acb180029b60b41596300353d40682b2c6000a7980d05658c00d4f50020acb180029e60041596300043f43842b2c600087d87085658c00147d0810acb180028f610215963014d2f41842b2c6000a5d83085658c00d4f50010acb180029e600215963002e3d3aaa0b2460008f7815d5628c0031e902baac5180063da1f7158a302563ba86e2b14604ac7550dc5628c0959ae61b8ac51812b354c37158a3021673b90e2b1460008f7815d9428c0031e902bb2851801a2f21d6450a300347643ac4a146037ae481589428c0011df04baac31800a3b20975586300147743ee4b0c6044c6f50dc9618c0898daa1b92c31811333cc3725863022666986e4b0c6042ce7711c9618c0011df04bb2831800a3b20976506300345e43ac8a0c60068f487585418c0635c904b0a83180039908565486300347643ac490c6001ae481589218c00d1e90eb0a431800ab920961486300053dc32e8a846064d38745d1508c0016b706ba2a1180a6d620d74542300053d43ac8a846064a7887591508c00dc7708b22a1180038edd1645423059f1c3a2c8a8460b4e3b43591508c169c7286b22a1182cf8ed09645423059f1da0ac8a846000a7b865c9508c0016e702b92a11818adc20572542300071cb2284a846000a7b865c5508c0016d704b8aa11818eda20971542300071cb2282a846000a7b86485508c00d4f10c90aa11818bd808521542300071dc22caa046000e3884595408c00d8f6e8b2a811801b8edd165502303471da1acaa046068e3943595408c001c7684b2a81180038ed0565502300071cb2a84a046000e3965505408c00187aebaa6c898002ae60354d91300047bc0ae5b2260018f4815cb644c0011df04b8ec89800a3b20971d913002e3d3aaa1b226000e3b54543644c0adc70a8a86c8980161fa1f75591300045fc22eab2260008df835d5644c0010fd0e3aac8980030f1d774591300062e3aee6b22600087e87d41644c00b0f90fa82c8980171e1d6505913002c7c43aa0b22609fc5c76dd5434c13fc38c9baa8698012a7a1b6450d30004eac0ee4a1a60009cd82dc5434c0016b30a382869801a37219744c93001ce6c16e29926000b59851c1324c00173308382649800b339c932d85302df6210a65b0a60068dc865d1314c0073ab03b926298006b5a07624c5305476210ec498a6000b59851c1314c00173308382629800339086764853000672108ec90a60068dc865cd2
  | 6 => 0x59cc28e0a128000b99831c1425000d1790cba264a000b2b9c942d854036f5210a85b0a80049b581dc9415000356d03b1282a02a7a908762505400059cc28e0a0a8000b99831c1415000d1790cba262a000339086764854000672108ec90a80068bc865d121500dbb4842ba242a001a6e20174485401561f3b6e8a828006b3a80dd150500554f301b1aa0a00024f21d43541400351e43286a828029e1c6350d505000d67100a1aa0a01a3c6cc143541401553cc06c4a828006a3c86509505000d67100a12a0a019fcac8142541401553cc06c2a828006a3c86505505000d67100a0aa0a019bccc4141541401559d43ee8a82802ad3a87dd1505000d6750dba2a0a001ace21b74541401569d3b6e8a82802ad3876dd1505000167307ba2a0a0002ce60b74541400059cc0ee8a82802ab3884dcd5050001a76e9b9aa0a0003c6d0f73541400053dc32e6a82802aa78865cd505000167708b9aa0a00aace21173541400069dba2e6a828068d58735cd50500cb4f50fb1aa0a006e9e21f63541400353cc26c6a828000e5b73d8d5050169cb0e7b1aa0a02d39690f635414059f2ca1ec6a82800097b8758d50500452f10eb1aa0a00034ee1d43541400059d43a86a828000b388750d5050001a710ea1aa0a001acea1943541400359c43286a82802ab3b8350d5050055e3706a1aa0a01a3c69cd43541400078cb9a86a828000f1b6350d50500d1e30c6a1aa0a0002cee0943541400059dc0a86a82802ab3884dc950500014f70cb92a0a00aa9e21972541400059dc22e4a82802ab38845c950500016e702b92a0a019adc20572541405c734312c4a828000b738158950500cd6e102b12a0a0002cea1d42541400059c43a84a828006b3a86509505000d6710ca12a0a0002cee0d42541401559dc1284a82802af2b8250950500cfe54e4a12a0a0003ca5c9425414000795b1284a828067f286250950500cfe5464a12a0a0002cee0542541405bf9510a84a828067f2821509505005567508992a0a0002ce611325414000794a1264a82802ab3884dc550500014f70cb8aa0a00aa9e21971541400059dc22e2a82802ab38845c550500016d704b8aa0a019eda2097154140005b5c12c2a828067b6882585505016dce0c2b0aa0a0002cea1d41541400059c43a82a828006b3a86505505000d6710ca0aa0a0002cee0d41541400059dc1282a82802ab3b815055050055e6702a0aa0a019bcc9c5415414000798b8a82a828000f336150550500cde60c2a0aa0a019bcc8c541541405af9990a82a828066f302150550500556750898aa0a0002ce611315414000798a0a62a828000a7b8648550500014f10c90aa0a00aacea1121541400059cc2242a828066f6021485505000187ee93a2cb1801a9ea0274596303053cc04e8b2c6000a5f835d1658c0534b906ba2cb1
  | 7 => 0x5c874c931540f5e884299262a80a65d21d614c5503b5b2412c298aa0bcb738058531540532e90ea0a62a80025e6037648550006b210cec90aa00096f825d921540012ef02bb242a80025ee017648550006b2108ec90aa0bbd6421dd121540f7ac842ba242a80025ee017448550034bc402e890aa0bad6421dcd21540f5ac842b9a42a80025ee017348550034bc402e690aa00697a87dc12154173ec043b8242a80165ea1b704855002cbc436e090aa00097984dc121540012f307b8242a8002ce6107048550005acc18e090aa044d6b721c12154095ae6e238242a828bd808470485500353d404e6b2c8051a79809cd659000147f08b9acb200aa8f21173596401551f420e6b2c8000a3d841cd65900018bae639acb200029ba08735964000536c10e6b2c8000a76811cd65900014eb0239acb2001a9ea00735964011d3cc00e6b2c8000a77815c965900014e902b92cb200029da0732596400053ac0e64b2c8006a7a80cc965900014f301992cb2001a9ea0032596400053cc0064b2c8000a6f825c565900014d904b8acb200029ba0b315964000536c1662b2c8006a7a80cc565900014f30198acb2001a9ea0031596400053cc0062b2c800087e8708565900010fb0e10acb200aa8fa1021596400051ec2042b2c8000a5e8308565900014bb0610acb2001a9ea0021596400053cc0042b2c8005c7a7554163900011ef02baac5200063d2057558a4000c7b43ee2b14804ac7750dc562900958eaa1b8ac52012b2dd037158a402565aa06e2b148042ce7721c562900011ef02bb265200063d205764ca400346e43ac699480068ec8758932900695c902b1265200023be09755864001476412eab0c80028ee87dc961900898dea1b92c3201131b543725864022657a06e4b0c8044cad40dc961900859cee2392c3200023be09764c64001476412ec98c80068dc8758d319000d1e90eb0a63200bab9209614c6400073210aca90c80068ec8758921900035c902b12432001a3d21d614864001572412c290c8000a7b865cd509000167708b9aa1200aace211735424039eac39ae6a848000a7a8758d50900e74f10eb1aa12001b96e0d63542400072db9ac6a8480b2e587358d5090165cb486b1aa1202c79650d63542405972d992c6a8480b2e5b3158d50900014f70cb92a120002dce05725424038db840ae4a848000e59634c950900014f70cb8aa120002dae097154240395b4412e2a848000e59634c550900014f70c90aa12001a9e219215424038fb010a42a8480008f7815cb63500031e902b96c6a00023be0971d8d4001476412e3b1a8005c7a755436350001cb6a6a86c6a01a39614d50d8d404f61e3b6eaa1a809ee1c63dd5435000753d0db1a86a00026d6077250d40004d6c16e2a1a8000b39851c14350001a76ea38286a00126b60b71509400
  | 8 => 0x61ba2c6a80034e4c37458d500061fbb0e8b1aa000e1c631d163540010fd0fb22c6a80ab0f1d36458d5014d2e41ec8b1aa000e1e43d9163540530f90eb22c6a80ab0f1d16458d5014d2e41ac8b1aa029a5e86d8d6354001a38e9b1ac6a80034edd37058d500069c3a6e0b1aa0c5d5b73dc16354189cb0c7b82c6a80025e6037650d500070e21eeca1aa000c7980dd943540018f481bb286a80031e8c37650d500043f434eca1aa000d1c439d9435400127f08bb286a800257e0d7650d50004bdc02eca1aa000d1c431d943540512dd043b286a80025b6087650d5013cbb408eca1aa000975811d94354001c38863b286a80030fa107650d500061ec20eca1aa000c5e831d943540018bb063b286a800317d0c7650d500061f218eca1aa000c3c431d943540018b8863b286a80030710c7650d5000637410eca1aa000c6d821d943540018ed023b286a80031d6047650d500063cc00eca1aa000c3f401d943540018f4803b286a80031e5007650d500062f980eca1aa000c7a301d943540018f2603b286a80a64f21d6450d500061e3b2c8a1aa029b1c83591435418767700b2286a80aa5721d6350d500062e3b2c6a1aa02ab1c8458d4354001c3ac8b1a86a830ad6e016350d5013cbb40ee4a1aa00097581dc9435400d2f501b9286a80025e6037250d50144b7416e2a1aa00096d82dc5435400d2f501b8a86a80025e6037150d500063dbb4e0a1aa000c78769c14354165e308738286a80f29e2197050d500063c3b2e0a1aa0b4f18435c1435404f2ed0fb8ac4a80031dd837158950006b9b06e2b12a000d67721c56254183ad6e5b82c4a80035cdc77058950006b838ee0b12a00097980dd942540012bf06bb284a80a65720d7650950004bbc0aeca12a027974815d942540012f700bb284a80aa5b21d62509503ddb240ac4a12a0c0b6b8058942540552db05b8a84a80025e603764c9500049fc22ec992a02a93c845d932540012ef02bb264a809e5d205764c950004bdc02ec992a00087f865d132540010f90cba264a80a65b21d624c9503d5b240ac4992a0bfb6b8058932540532d90ea1264a80a65b60b714c95013c3ec3ec5b0aa000e6421d8b615404f4e902b16c2a80a25ba1f725855000637b06e4b0aa000d6b60dc961540518d8e5b12c2a809e1f21d6258550006b2396c2b0aa000d6b72dc16154001ad0e5b82c2a82fb5cdc77058550004bcc06eca0aa00095f835d941540532b906bb282a80025be097650550144b6412eca0aa00097b805d941540552eb03b9282a809e4f21d42505503df9210a84a0aa02a9748758541540ef6c904b0a82a82f6dce016150550004bcc06ec98aa00093f845d9315405527908bb262a80025be09764c550144b6412ec98aa00097b805d931540010ff0cba262a80021f219744c55014cbac0ee498aa0279
  | 9 => 0x725913202c7643aa4b22640087e87d41644c80b0f90fa82c89900e3b60b75d85323ee36b96a1b0a640087f855d3604c80b0f90aba6c0990023ee1d601813200c5ec26ebb1a8200ce4215cb63504091eb03baec4a0b3b1d5c750d89411bdd3416e2a1282038ee87d8932504055590ca1264a08032b1d9424c9411bed238a8499282048f686dc532504010ff0ab9ec0a08161f21573d81410047dc3ac030282018dd83dd7644c4019c842b96c8988161fa1f75591310043ec06eab22620087e871d5644c4015cd05b8ac8988163d21d51591310043f43ea0b22620587c87d41644c4071eb03baec4989f71d5c750d89310247743ec4a1262038f686dc5424c405998eca1264988d2f1205424c9311a5e3416e299262019b487509414c4015690ca1282988c7a9189425053100d6a43264a0a622edc4724c9414c401f0a8499282988021fe1574d813102c3e42ae9b0262008fb87580604c4071bd07baec8908023760f75d91210067210ae7b2242cde6421d436448599d4843ba2c8908033908773591211bd73416e2b2242cbe6421d41644840917d09baec6908022f61375d8d210067210ae9b1a42cae6421d4363484019c843ba2c690b27b10877358d211a573416e2b1a42c8e6421d4163484011db05bb286908023d6077650d2102c3f42ceca1a420087d859d943484019c8433b286908021fe157650d2102c3e42aeca1a4200ce4215d943484011f700bb2869081a3e2017650d21006b210eeaa1a42058fb875436048401ac842bacc09081b1e18175981210063cbaec13024200d64215d4604848995ec4ba0c09092b2dd857418121006d210ae83024244ccf625cc60484959aec2b98c0908037108573181210047dc3ac03024244aeb8258060484955e702b00c0909fa5ee0173d9150034bc402e7b22a000a3d8690f64540016730121ec8a80025de0572d915013cba40ae5b22a07c97b805cb645400d2f100b96c8a80025be0971d9150144b6412e3b22a07897b805c7645400d2f100b8ec8a80aa8fa1b645915014caf43ee6b22a000e1c64dcd6454001ab701b9ac8a800317d837359150006adb06e6b22a000d5a40dcd6454001ab281b9ac8a800317dd873591500068fba0e6b22a000e1c641cd645418fa76e9b82c8a831b8e1937059150006adb9ee0b22a000d5873dc164540ff2f700ba6c6a801a5e20174d8d5014c3ec3ec9b1aa02ac3e74d936354001c3887b26c6a80021fe1d64d8d501561e3a2c9b1aa029a5c8359363540014bb0da1ec6a80038759343d8d50005acc0687b1aa000977815cb635404f2e902b96c6a81f25ee0172d8d50034bc402e5b1aa00096f825c763540512d904b8ec6a81e25ee0171d8d50034bc402e3b1aa02a93e87dd16354001c38c7ba2c6a80034ee037458d500061fb06e8b1aa000d3b60dd16354001a74
  | 10 => 0x300200100200000080180180180000080000200100180000080080180100080000480000000080100100080100000a8020030000018000000000018000040010008000000000028018000000010000008000000018018008010028008008008000000048000008010010034710d70d95430053b40ee5b2a8600a7581dcb6550c014dd05b8ecaa18029b60b71d95430043f43843b2a860087d870876550d3f47d0810ecaa18028f61021d95434f52f41843b2a8600a5d830876550c014f50010ecaa18029e60021d95430063db84e1b2a869fa3e841c36550d3d47b08386caa1a7a97a0c70d95434fd2ec18e1b2a8600a6e821c36550c014db04386caa18029da0470d95430053ac08e1b2a860087e870836550c010fb0e106caa1a7e8fa1020d95430051ec2041b2a869ea5e830836550c014bb06106caa18029da0420d95430053ac0841b2a860087e870436550c010fb0e086caa1a7e8fa1010d95430051ec2021b2a869ea5e830436550c014bb06086caa18029ba0810d954300536c1021b2a8600c7671d976250dadc388632ec4a18031d9c465d89430053cc00cbb128600c77655c76250c018e8cab8ec4a18036510d71d894300c7b40eebb1286008f581dd76250c031ef0eb8ec4a18032dd0171d89430066b982e3b128675c7671d436250c018eae3a86c4a18034710f75589430043f43ecab12860087e871956250dabc388632ac4a18029e600655894300637396cbb0a86d4e1c431976150c018dce432ec2a18029e60065d854300637b2ae5b0a8600c6c655cb6150c01b1886b96c2a180a3ba0b75d854300476c16ebb0a86028ef875cb6150c0195e80b96c2a180333cc172d85433ce37396a1b0a8600c6d72d436150c01a3887baac2a18021fa1f65585430043f438cab0a86d3e1c431956150c014f30032ac2a18029e60375d81430053cc00ebb02860087f855cb6050c0b0f90ab96c0a18021fe1571d814302c3e42ae3b028600d1c435d66050da5c388632cc0a18029e600659814302c3f436eab02869e87c86dd56050c01a3887baac0a18021fa1f65581430043f438cab0286d2c3f741956050da38bee632ac0a18034710d75181430363d302ea302863c87d87d946050c018dce5b28c0a18031d9c765181430053cc06ca30286a0c3d741946050da18bae6328c0a1b3f8710c651814300637390ca3028600c76711946050c014f300328c0a18031bd9572181430063632ae43028600d8c435c86050c018eecab88c0a18031d1957118143006ca21ae230286008fb875806050c018f2eab00c0a180a2f61375d8d420067210ae3b1a84048ed82dd7615099d8dae5a86c2a10021fe1573d814202c3e42ae7b0284008fb8758060508051bb07baec8990033908571d913202c3f43eeab22640087d80dd5644c8010fd0e3aac899002b9a07
  | 11 => 0x4e50003451f500045400000026100007c0001ec00000000000055400000000000000039600040312d03c1281735643e13d022014c0c158d4580005252ef0000000000000000f10002d73bb0d938900045751f47b00028d0000ae11200000000056e22c19c23a0002870680000325bd3a900000000000000000000000000017725142c14f0dc2f52370000000000a00000d200005200000000018400032700000000038e27700000000000000012e23b3e51b33241c42de1f136d0004710bb0004d13474b42153ca3b300000000007b3c70004050002a70b800007922505b39f0000002992700000000003f30000000000000000000004390004fc2af0003df29f00034e0000002062c616942655e1b04100ba25441900000000000000000029718053100042431f40e0000000004e654800000038200000000000000035f00003400000027c34f0004bd0001ba55d02f00000034a32c0000005a01053af5a70000000000335860853920001e427814443400050c30a00080000000300080000000100200000000000180000100200080000280100300080000100200000000180980100000480480100080000000100000000100000080080380100080100580000100280280080000000180000100000900380000680000000100100280100200380000000080000080000080100080180080100100480000000100100300000080100000000180000080000600000180a00080000100000200000000100200080080280000080100000080180080380080000080180180000000100000000480080100000000000000000280100100080000080200000080000000180000380280180080280000100200000480000000000080000400100080100180080000000000000500100100000000100000400000180480000000080280080080280000100100100000080180500000000900000000300380100100080080000e00180180200300080180000000300180080300000100080100000480080000300000180180280080000000000000000100000000080180280080200000100080000000680000000000280280080400200100080080000100080180100200280080080200000080000000800000080000000100200200180000500000000000000180200080200080100000080000000c00000000100000100000000000000200200000000080180400000080000000080000180080000100000000080080280100000100380080200080400680000080300080180080000100000100000000300100000000000100580000080400000400000180400500080080000000080380100000980000080080000000080280000000000200080200080000080280080080080000380580080000080880080780080000380000000100000500000200380080
  | 12 => 0x1ad1b51330004273513850570ed49d42a06f40a02a4a20004044970000000000000005bc34b2882310351ea3260004e80000000005a158900000024d00010231e4d400000000000000000000000000002b0000ab00000000000000024212c0002d30000003f90005c55d700035c00000000b0000843b10000250000d40005ba0003f004719920e0b300000028f11113d00042f5982890000000000002f908c4f352d5be57c04f0002b71162cb44e2e300047a3350fe1000001583752d61d000039058e1d43b938f0005ce1fc3770d633e3bc36b0ca0001c208a10c31500019800000025c43f0fb0000293295c15a600000000043300000037100017e20b0000884cc3da3810005b12684a40000002963b72f21600280003ae4f94091095e80003180000f80000000000000000000000005b90cf24a0005120000000000005930000000000004760005b70003010000005375210000000000000c41310004a90003f10000000000000001ab4670004233344060054220002850000003c45101070000004b60000002010000004b31290000000005e101c36047c5c71c34b20d82130000003d44860000ad43b1d15db2be41a1512534b83d30005c829a3a51014350000000000000002170000000003830001300000000e84120000000005513480000000000000000002f10000000003b85604753720af0000000005da0000000003c553200026c0a440c33c2713a800000017d23f11e10f00000000050000026d00000000059134c2c40000001de0903500e35d921b0004560000000000004dc1dc00018f06d0001180000002c800000000011010b08131a50d00050900000000000000000040b0000002b600039a42e4f83d14c00000003de0000000005df00018c0000000c20655c90000f60004284b94e70000003d70000000005bb00000000000000003800018b59f3b054b00000000028349b3c00b22193865690001173ba3e34804f415c0001241762fd23d5de1454770bc3870003ab0000000003f20002a10005e50000000191d90920000000f00002470001643550000000365ca00000000000000019f0002550002bd2eb0003cc5952215230002080002c50004b10003c200035b0000004de0000000004bb0002660001380003ee59c00a00000000000030e0000630000004003300000002bb0000000000005730750b50000004be1a22672240003e61c91c500000000000000000017a56507a0980000004c55dd0005675dc56157a00039802100d0000000002b11c84383190004cf4ba0cd4ca0002b301e26f0f900009e0003ea0000000005810e40001c051a3d50001903e71920000003732ed1b92dc0001ee2a40005224595b85570b12ad3bf46604509c00021a2503f600000000005e2da3030000c6000273583000223000000000000
  | 13 => 0x20514100012100018a0000003e041b5e425f3090005535d808b2bc0001140000000005b432a00000000004000000029c0970000000000000003a700033a2aa0001a50000000002640000000000000000000000000000002655b30000000000001490de27257b00830d00029200000000044847e2d10b63120000220000002a50000000000000001d53d606c0003670000002b00000002ac0000003f42cf50a03057836233725a04e4d24785a82e017946f4bc4470533c145241816621c0004980000d00001973fa0005071a40000000000d347f1741371812d85200ac04900000024516d1f703e4df0000000950002b800000000057d04816f01249a35700000000000e00000000000051100053000000000000050f0000551320b000000000039c05f0003ad00000000000011a1b70002102ec1ff0000001fe0000005595d200000017f0000004e330200000c20050e24f08f00000011f0001ce0002860c74ee15900000034d0000000d100000000000001d1750770002ff0000000002182b94c300000000019439546c0000000005923065a215d34900000030c50b2ba4165335270001c74ab54000051b2580000000000000002cc05900004c00016555c0000000002b209f00324657f0000180000003e205458200014b1c65a30003db45c0a75554895964c100003f0731d200000039d41507f1bf3fc1d82cd00000000045d31100000000044200000001500000035e0000f35790000000004d013a5b60005cc00015353600015700058a0000000000000000004304550000000000b701a4f23f73dd12312000041e40d0004811830000a556f00031446453f31c5840004e400000019d2b509600002d5d400000056b0000001db3643660004880000bd09b0005340045cb00000000048f44408354200004331700000000000050600000041411c01741337a00046e2e50005381eb24346928c1780005c34110000005ac1e60004b74ff0000000000000000001150000002c715252900000006200000044d00000016a20a0000000004f70002a333f2092fe5e044a4504e925b28a0a251c3104850781b10ec0392604af00f0000002a20004ce00000000000000000000026e2f60003e80000000002d507e07659d0000000003c600000043e00057425d3e900027d0000001850005240003130000005441af43a0001860bf37c1fd0000002a60000000000000944d300000000000000051e0000004a60000000e90000600000000000000000000000000000000c02841f826200024404a0f403715f5720000002560000004450000000410000004b019514d0004c800000000013e00017145f0e12980000000000000002a81960000000000001221da2dd2fc22a00000000053b2760000740003a000000055b1ca3aa0001f00000004e20003160002a00
  | 14 => 0x3533a209113f00000000000051519346d3f83be0ce0892362c13a41ac0000004aa00057616b15020700000058f0000000003361b60004cb28b4430cb37e00040f00008213b00054a4ec00000000000005a42508700010a0e20cc15b3000000000000000000000004c741f16803a1045182ae45a5973a14da0000001d30004fd20f43d0000003b65172480000000000000005475cd00000029b20d0000005350da00027a3231b836115a0800eb3070004ea0000000002db3580000000000b93380004b50000000000000000000000002c00000000a12e44935941420000000000000000000000000000230e64f000013600000000012f21421e0000003930003220001622f40003ce35956a05c2c90d738b3941630000000000500a30c31823d200000054533332b51600001b0001cf0000700000000000004dd5703a60000992d00004fb0002e70000004cd0005e700030430f00000000053e0260000003ed12549c3b257151d5ae0000003390000000000000000001aa00000033b22b10d00007d22957e29d11d0002fa00048d4e11e75d351336f54100000039754321153956c03d3740f24e052636931b5033213762d93200000000e000058524e2ee45e2d44eb3843c800020200000051900000000000000057718936800000048200059e00000006e0000000002750fa4c244033d0310000863800660010000005cf00004b00052f00000025206a00002e3655801c12d207200041700019b47454e3430001a00ef1bc16e0000000002ea3c358854f00023900000000028e3e40000000e721232d1f90000000002281e50000000130000e501100000000015400052800018d01025700000000000000032f22d23834600038a52c37b1874a80000000005465a500000000055227900023425e00000040112711b0000001fb4070000000001b25990000002e147221d00018e0005490ee3520000000000000004a100056215e00024923c48c22e0003eb1e03311880004703cf0000001e32a902c17c4790933780f536c4924964ed2f01720004d60440001fa2f300000058b1084d51a909a12b00013526b38d1e21342b41670275aa5021560000000000000004650df0000002e62bf30b00039e0be26344600059000055a0001a14a746b00041c0000000ea4ae0005500003ec20c4834361f40420000000005ad3404db1e94f50000000005560140004ad3882c351427e27f0002ce00022652b00032e0003bd1b44200005874414633fd0000000000005c048e54c3323915d11df2c220336e4515c42f80000002744ac1a60000000000000ff4fe00044f0611f200000000000000010e00700000039931d0000002320b40d50000c83a30001430003084a500058c50800059b56600000045306b04638c1460000004374d714a3c944b1e829000000000000
  | 15 => 0x3ac22748704d55f54d08e00056342100000000000000000047d0001ae4902ca10300000000023e2e800000028039b0000000003700aa2224d844c24129e0642351ef49412600022f0000020000004fa08d00000000040240852a53a3cb23029300000057526a1a70002df3ef00032817000000046235630500000000000000000000000000000000006956856d0004c90000003dc00034236a29400000005627b2822e90db05800035d0671555d641d2e22fb4a00000c51400004f10a60004ef5c600000000029149e0f75bf0714c409d00013c59a48453c3541a30001bd3415a91d61f35b000000016c00000000037d0000001cc0001ed48a0000004294684bf00014845b28152e00000035a1470000a83440001f60001be50400049f1bb00000000050500000000003b0003b400000000019e5d500000000900014e0001134613f50002335e60fd3b52591dd2164f60004911cd42b0000000000002954a353d05d0000000000000000200000005ab00000000042d4d94325b543c3fb2404493d901600037f0004313ff0000000c900036300000000000012a0000000000000000000001d70000000000000000000dd5d024c1190005af0000000000000001a80003790005010510245e346a1065e25b248b3d800000000017b0003251910000001390a93cd00021f3fe00600049526924b5581610004990005c22040004c60000004600005a40000fc01f19a1cb1e12ab0004730000002f7
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x13299221d4354140004cc6448750d505000191b8321d4354140154c62617350d5050001918875cd4354140155862597350d505000133191e094354140004ca64b8150d5050055328985c942541405bdc824572509505005532992e054254140154cc647825055050055330985c541541405adc8249715055050001a602121921541400348e25984485505016fb202161121541400040fe61741d1658c00181d7460c74596300059864021595218c0016199321165502300058a64884595408c0016319121165502300058c64742595408c00162992d05655023000538640219d9214c0858c583084764853000538640211d9214c00181c6421d43541300060e21f84591504c00185887e0d645413014d1625974dcd504c0013539160b7354130004d2e4981dcd504c0013499221d4354130004d46448750d504c00191b8421d435413014cc62617450d504c001918875d1435413014d862597450d504c00135191e094354130004d264b8150d504c053348985c9325413057dd0245724c9504c05334992e05325413014cd4647824c5504c053350985c5315413056dd0249714c5504c001a602121921541300349625983485504c15fb402160d215413000546650835d6404c0015499220d759013000554644835d6404c00155191cc975901300055264b315d6404c0013189850d50501300358625943541404c053c187650d50501304fe8621b8550d404c13dc1876e154350130004e46478250d404c00138992e0543501300040fe61741d1658800141c935d07459620006075d1831d1658800141c945cc735962000607611731cd65880014e19008771592200053864021dc5638800121d9810d6550e200060721c4359543880016199010d6550e2021638200615d132480012719021543d8520006856154310f6148001a914360043d852021698a0061dc9504800d5289750950501200358a25942541404816fe206150950501200355225d32541304815fe40614c9504c1200040fe61741d1658400141c935d07459610006075d1831d1658400141c945cc735961000607611731cd65840014e19008772592100053864021dc9638400b0799021d6550e100048766043595438400181c8710d6550e10005866404359543840851e297e05424821021478a5f814c920840012699021543d8910006836154310f6244001a894360043d891021638200625d13144085a628018b71541100354c25d41541404400d6309650550501105af8818941541404400d550974c5504c11056f901893154130440852e296e094188110214b8a5b824c6204400d5609748550481100359825921541204404fc607648550481101bf281d9425052044069cc0764c9314811042e381db84485204406f8e076611214811040e381db8348520440698e07660d2148110
  | 1 => 0x30051a640655c86050c0150d9510d721814300703194435c86050c015899010d72181430051c640655c46050c015159510d711814300705194435c46050c015919010d711814300538640215c763508014e19008571d913200538640215cb63504014e19008572d91311a56125d424c9414c46fa8486509325053100538640215cf64484014e190087735912100538640215d363484014e1900877458d2100538640219d943484014e1900857650d2121638200215d94348401561900877550d2100558640215d66048485c6060085759812100558640215d460484015a190085741812100570640215cc604840103f9761a43d915000487a6064dcd645400141e97193735915000507a5b741cd645400121d98190735915000507a5c641cd64540016199010f64d8d5000417e5d86d0f635400121f9859343d8d5000507e5d64d0f635400121e9818f7458d5000507a5c63dd1635400121d9818c7458d5000507a5e43d91635400181e8790f6458d5000607a1874d8d635400121e9810f7650d500058664043dd9435400141d9610e7650d5000546640439d9435400111d9810c7650d5000507658431d943540015199010c7650d5000487660431d943540016199010c7650d506be86600431d9435400181d8460c7650d5000516643431d9435400141e9390c7650d500050e642431d9435400103d9810c7650d500050e640431d9435400105d9810c7650d5000516640431d9435400141f9810c7650d5000607a60431d9435400141d9810c7650d5000607660431d9435400101d9810c7650d5000703a48431d94354001c0d9210c7650d5000705a44431d94354001c159110c7650d5000706a40431d9435400141d9010c7650d5000706640431d943540014199010c7650d500070310e821d94354001c0c436087650d500070510e811d94354001c14436047650d5000619609811d94354001839846007650d500061660d801d94354001c18436007650d500061aa09801d94354001869826007650d500061ca05801d94354001871816007650d500070610e401d9435400141c94cc07650d500070610e301d9435400181c831d96450d50006072107658d435405321c985916350d5014d0725d6458d435405581c875916350d500070610c769c1435400107a981d97050d500060ee10765c1435400185b831d97050d500059864021d8b615400156190086764855000558640211d921540859608008476485502264adc9841c12154095933716107048550006c8085841c1215408994b7260c704855025654dc5831c12154001b402160c704855000607611731cd659000166190085654864000538640219d921500858a584084764854000538640211d9215000181c6321d4354140004cce4582dd1505000132b9260774541401560e21b745cd5050
  | 2 => 0x2d0a83a400000fe40c0000011000db000ed304d73a0b62804c418002fc0000000000350003c3d4000007000000000003780000000370000004300033000280000000000024831005b098d23ac3200000114fb18863424943889c0000015c003e800034980000000000000ff000000005a000542a80000000204c3000000ac0039c2300014320002146d1f0033608b3180f190fc354132c80013902000000dc1a1cc3d00019210f43c0a5000003cc0e000fd000bd314650008e338a4000210bc5e33067000000000000101000002c02c17cf934c00000751bc00110001ec000004b00050218001e878144001600000004000ea000000003a30800000af42800060b30c008240da1e41f00000000f2300e63b0002c47224400000003800033c000004a07800000000004132ccd264050010021d071ac15274b900006254003446c1dc0001c00288000002a0000026848000ba0ec490803e000610a4001fcf80004d000001a80009400394710903622069000b826c53278002b8e42581d23cdd2ac5c174f62f0a3180f700000000c7048000880023000340002a4000000006c002b4102983841476001080fc000008d2f8000000000000410000000000074000d4000002eca10007d0d0d63280000092364000300000068000822006e13c93008e3228f12b00b2d49f000560c4a709cc4070e11088916400198df0b80a3bc39058b725c47004ee05cc91182d1485500000000000007e0000603010000000000000c1c0281022000000800000100008010400400000201400030682812000080404090000c02030282c0001008880c020200400000200000020301010050180800030480004000300008000281000020180000010001c0004038040111e9810d70d954300546640435c36550c01075989c465d89430068610d801976250c018727160065d89430051c640655c76250c015159510d71d894300705194435c76250c015919010d71d894300447a6043dd56250c015199010f75589430068610d801956250c0106d989c865d85430068610d801976150c0186a7260065d85430051a640655cb6150c0150d9510d72d854300703194435cb6150c015899010d72d854300447a6043dd56150c015199010f75585430068610d801956150c0111d9810d759814300546640435d66050c01a1843600659814300447a6043dd56050c015199010f755814300447660435d46050c015199010d75181430060e5d1801946050c018597360065181430061a9c9801946050c0187271600651814
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2080058d80161e14191c1b11950009000d0a8c1112908b8080219a19880001959d2100181e8b0a068e0f040312079b851a8e9c93021f171f8384828006001680000880001380148f899897a0100c9d87010000060aac08f0000d030c0810210102841a200110044335221b0032ec4a1802415a9194435c76250c01608d00ca21ae3b128600d041959010d71d89430044335221b0032ac4a1802219a910d801976150c01206d48ca21ae5b0a8600b026806510d72d8543006810cac8086b96c2a1802219a910d801956150c0110cd4886c00cb30286009036a46510d7218143006810cac8086b90c0a1802415a9194435c46050c01a0832b2021ae230286428382a1900857650d212148c14cc8042bacc090802219a8640431d9435400120cd0730218eca1aa000c03a899810c7650d5000601b44cc0863b286a8003016a1660431d9435400180ad0b30218eca1aa000c066819810c7650d5000601b31490863b286a800300d98648431d9435400180acc522218eca1aa000c056619110c7650d5000680b24c88863b286a800301998a40431d9435400180ccc320218eca1aa000d02a499010c7650d5000681324c80863b286a800341291640431d94354001a08c8b20218eca1aa000906ea19010c7650d5000501b5021d043b286a8002c09a010e821d94354001406d4086c10eca1aa000b02680436087650d5000502b5021d023b286a8002c11a010e811d9435400140ad4086c08eca1aa000b04680436047650d5000700886c13023b286a8002419a910d801d9435400140cd4086c00eca1aa000e0210d826007650d5000702086c0b003b286a8002819a810e401d9435400140cd4087180eca1aa0009066a4431da7050d5000503350218ed38286a810a163a8640219d92154085850c2320108ec90a8000a06a9b8321d43541400060312c43ae6a1aa0a010b22194084864855050085860c1b20108ec90a60008076a46421d43541300050354dc210ea1aa0980030189621d7450d504c085920c984243242a826000c061d89850d505013000403b5243886b2a87100030188764043595438800100ed490e21acaa1c2000c0621d9010d6550e10
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x6e80c24a0000004411ba1959010d71d8943004409ba1959010d72d8543006005a26859810c7650d50006009a26819810c7650d50006011a16819810c7650d50005801b010d826047650d50005009b910d826007650d50005011b910d816007650d50
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x1
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x124b
  | 12 => 0x124c
  | 13 => 0x124d
  | 14 => 0x124e
  | 15 => 0x98a
  | 16 => 0x98c
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128a
  | 20 => 0x128c
  | 21 => 0x128d
  | 22 => 0x128e
  | 23 => 0x9ca
  | 24 => 0x9cb
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12ce
  | 28 => 0x12ca
  | 29 => 0x12cb
  | 30 => 0x12cd
  | 31 => 0xa0a
  | 32 => 0xa0b
  | 33 => 0xa0c
  | 34 => 0xa0e
  | 35 => 0x130e
  | 36 => 0x130a
  | 37 => 0x130b
  | 38 => 0x130c
  | 39 => 0xa4a
  | 40 => 0xa4b
  | 41 => 0xa4c
  | 42 => 0xa4d
  | 43 => 0xb0c
  | 44 => 0xb0d
  | 45 => 0xb0e
  | 46 => 0xb4b
  | 47 => 0xb4d
  | 48 => 0xb4e
  | 49 => 0xb8b
  | 50 => 0xb8c
  | 51 => 0xb8e
  | 52 => 0xcca
  | 53 => 0xccd
  | 54 => 0xcce
  | 55 => 0xd0a
  | 56 => 0xd0c
  | 57 => 0xd0e
  | 58 => 0xe8a
  | 59 => 0xe8b
  | 60 => 0xe8e
  | 61 => 0x98956
  | 62 => 0x8a
  | 63 => 0xb0956
  | 64 => 0xb4956
  | 65 => 0xb8956
  | 66 => 0x209
  | 67 => 0x150a
  | 68 => 0x1409
  | 69 => 0x168a
  | 70 => 0x180a
  | 71 => 0x4b
  | 72 => 0xb0996
  | 73 => 0x138b
  | 74 => 0x1549
  | 75 => 0xcc996
  | 76 => 0xd0996
  | 77 => 0x168b
  | 78 => 0x180b
  | 79 => 0xa09d6
  | 80 => 0x9ca16
  | 81 => 0x1309d6
  | 82 => 0x9d316
  | 83 => 0x10c
  | 84 => 0xa49d2
  | 85 => 0xa49d3
  | 86 => 0xa49d5
  | 87 => 0xb49d6
  | 88 => 0xb49d3
  | 89 => 0x138c
  | 90 => 0xcc9d6
  | 91 => 0xcc9d2
  | 92 => 0x150c
  | 93 => 0xe89d6
  | 94 => 0x180c
  | 95 => 0xa12d6
  | 96 => 0x12ca16
  | 97 => 0xcd
  | 98 => 0xa52d2
  | 99 => 0xa52d3
  | 100 => 0xa52d5
  | 101 => 0xce
  | 102 => 0xa4a12
  | 103 => 0xa4a13
  | 104 => 0xa4a14
  | 105 => 0xb8a16
  | 106 => 0xb8a13
  | 107 => 0x138d
  | 108 => 0xd0a16
  | 109 => 0xd0a12
  | 110 => 0x150d
  | 111 => 0xe8a16
  | 112 => 0x168d
  | 113 => 0xa5312
  | 114 => 0xa5313
  | 115 => 0xa5314
  | 116 => 0x10e
  | 117 => 0x198a
  | 118 => 0xb4a53
  | 119 => 0xb8a53
  | 120 => 0x138e
  | 121 => 0x198b
  | 122 => 0xcca52
  | 123 => 0xd0a52
  | 124 => 0x150e
  | 125 => 0x198c
  | 126 => 0x168e
  | 127 => 0x180e
  | 128 => 0x170a
  | 129 => 0x15ca
  | 130 => 0x16cb
  | 131 => 0x144b
  | 132 => 0x188a
  | 133 => 0x160a
  | 134 => 0x184b
  | 135 => 0x148b
  | 136 => 0xb8b56
  | 137 => 0xb4b96
  | 138 => 0xccb56
  | 139 => 0x154c
  | 140 => 0x140c
  | 141 => 0x18ca
  | 142 => 0x178a
  | 143 => 0x184c
  | 144 => 0x148c
  | 145 => 0xd0b96
  | 146 => 0x154d
  | 147 => 0x140d
  | 148 => 0x16cd
  | 149 => 0x144d
  | 150 => 0xd0cd6
  | 151 => 0xccd16
  | 152 => 0x18cb
  | 153 => 0x178b
  | 154 => 0x188c
  | 155 => 0x160c
  | 156 => 0x170d
  | 157 => 0x15cd
  | 158 => 0x194c
  | 159 => 0x17cd
  | 160 => 0x74c
  | 161 => 0xb09895e
  | 162 => 0x8a52
  | 163 => 0xa5512
  | 164 => 0x9ccd2
  | 165 => 0xa0d12
  | 166 => 0x124996
  | 167 => 0x4a53
  | 168 => 0x9cb53
  | 169 => 0xa0b93
  | 170 => 0x128956
  | 171 => 0xe8a09de
  | 172 => 0xe89ca1e
  | 173 => 0xb4a49db
  | 174 => 0x9ca52
  | 175 => 0xcca49da
  | 176 => 0x9ca53
  | 177 => 0x9ca55
  | 178 => 0x130a54
  | 179 => 0x12ca55
  | 180 => 0xa0a54
  | 181 => 0xb8a4a1b
  | 182 => 0xa0a52
  | 183 => 0xd0a4a1a
  | 184 => 0xa0a53
  | 185 => 0x150a52
  | 186 => 0x15ca52
  | 187 => 0x160a52
  | 188 => 0xb5396
  | 189 => 0xb9396
  | 190 => 0x139256
  | 191 => 0xcd516
  | 192 => 0xd1516
  | 193 => 0x151296
  | 194 => 0xe9696
  | 195 => 0xe9816
  | 196 => 0x198a54
  | 197 => 0x1692d6
  | 198 => 0x198a55
  | 199 => 0x181316
  | 200 => 0x198cd2
  | 201 => 0x15ccd2
  | 202 => 0x1995d2
  | 203 => 0x198d12
  | 204 => 0x160d12
  | 205 => 0x199612
  | 206 => 0x198d
  | 207 => 0x74114
  | 208 => 0x5cd
  | 209 => 0x5d2d5
  | 210 => 0x75314
  | 211 => 0x74b94
  | 212 => 0x75854
  | 213 => 0x74d14
  | 214 => 0x75894
  | 215 => 0x58e96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1426
  | 6 => 3727
  | 5 => 1513
  | 4 => 267
  | 3 => 68
  | 2 => 8
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (57987+((h/475+packedAt gbK7 (52762+(h % 475)*11) 11) % 1712)*12) 12
  | 6 => packedAt gbK6 (195042+((h/1242+packedAt gbK6 (178896+(h % 1242)*13) 13) % 4920)*13) 13
  | 5 => packedAt gbK5 (95315+((h/504+packedAt gbK5 (89267+(h % 504)*12) 12) % 2656)*12) 12
  | 4 => packedAt gbK4 (19491+((h/89+packedAt gbK4 (18690+(h % 89)*9) 9) % 426)*10) 10
  | 3 => packedAt gbK3 (5662+((h/22+packedAt gbK3 (5508+(h % 22)*7) 7) % 82)*8) 8
  | 2 => packedAt gbK2 (744+((h/2+packedAt gbK2 (736+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1c71c0e3f0c63831ffe3ffe03ff0810f00f3cf
  | 1 => 0xe07e00fc7f07c03e387c70ffc1f30633334d33
  | 2 => 0xff8000ff8ff8003fc07f80fffe0c183cc38e3c
  | 3 => 0xffffff000fffffc0007fff0000001fc0fc0fc0
  | 4 => 0xfffffffff800000000fe000fff000
  | 5 => 0xfffffffff000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8204820900008004c00982010808105001045
  | 1 => 0xa0521244250642921124224a81630612314512
  | 2 => 0x548024890ac80524824904952c0c1828c28a28
  | 3 => 0x65148600035291800072460184200a40540f80
  | 4 => 0xca526392300000608452000abe000
  | 5 => 0x9a6938f24000000004000818318ad5bf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffe8ffeaeae8ffffffe8ffeaeae8ffffffe8ffeaeae8ffffffe8ffeaeae8ffffffe8ffeaeae8ffffffe8ffeaeae8ffffffe8ffeaeae8ffffffe8ffeaeae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_28690
namespace PEqualNP.Outside.L_meta_28690
open PEqualNP.Outside.L_meta_28690.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 3 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 7 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 5 := bs0_4_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 9 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 50 := (concat bs1_3_0 bs1_3_32)
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
theorem bs1_4_128 : Interval s1Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 136 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
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
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 9 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 50 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_128 : Interval s2Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 136 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
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
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 5 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 91 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
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
theorem bs4_4_64 : Interval s4Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 91 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 8 := bs5_2_0
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
theorem bs5_3_96 : Interval s5Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 102 := (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96))
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
theorem bs5_4_704 : Interval s5Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 725 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 (concat bs5_4_192 bs5_4_224)) (concat bs5_4_256 (concat bs5_4_288 bs5_4_320)))) (concat (concat (concat bs5_4_352 (concat bs5_4_384 bs5_4_416)) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512))) (concat (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)) (concat bs5_4_640 (concat bs5_4_672 bs5_4_704)))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 682 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 bs5_5_384) (concat bs5_5_416 (concat bs5_5_448 bs5_5_480))) (concat (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)) (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 8 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 68 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_256 : Interval gbAtlas 4 256 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 267 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
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
theorem bgb_5_1504 : Interval gbAtlas 5 1504 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1513 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504))))))
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
theorem bgb_6_3712 : Interval gbAtlas 6 3712 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3727 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)))))) (concat (concat (concat (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496))) (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))) (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456))) (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584)) (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712)))))))
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
theorem bgb_7_1408 : Interval gbAtlas 7 1408 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1426 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672))))) (concat (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832))) (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))) (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 2 zero,inputs.getD 7 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffeeffeeffffffe8ffeaffe8ffffffffffeeeeeeffffffe8ffeaeae8ffffffffffeeffeeffffffe8ffeaffe8ffffffffffeeeeeeffffffe8ffeaeae8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,8,136)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,8,136)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_28690.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,5]⟩,⟨.and,[8,7]⟩,⟨.or,[1,3]⟩,⟨.and,[10,6]⟩,⟨.or,[0,2]⟩,⟨.and,[12,5]⟩,⟨.or,[0,1]⟩,⟨.or,[14,6]⟩,⟨.or,[4,7]⟩,⟨.and,[15,16]⟩,⟨.or,[9,11]⟩,⟨.or,[18,13]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_28690

open PEqualNP.Outside.L_meta_28690 in
theorem PEqualNP.Outside.L_meta_28690 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
