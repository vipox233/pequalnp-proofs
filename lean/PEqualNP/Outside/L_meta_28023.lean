import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_28023.Model
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


end PEqualNP.Outside.L_meta_28023.Model

namespace PEqualNP.Outside.L_meta_28023
open PEqualNP.Outside.L_meta_28023.Model
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

def SBf (j : Nat) : Nat := [7, 6, 6, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_28023

namespace PEqualNP.Outside.L_meta_28023
open PEqualNP.Outside.L_meta_28023.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x397950e4ccad0019d804e0028148a8fb66825ba134c5aae00012943c094a2220061b1aa11b0203d038165cb2c0060400000000400e41803a995926628e3a640e443a9140000114d00000018f000450108b7290876d5210eeca221dd54443bd28087795010ebca6215754c42bb28885755110af4a0215e54042bd286657950ccaeca3195d546329faa2653c544caf4a1a0de54341b7294836d52906bea6a0d714d419f2a0633d540c6dca418db54831bd2806379500c6bca790d754f219f2a4433d54886f6a090de14121bb28e817551d02bca7205754e40b7a92816c52502dca5985b54b309f2a4613d548c2eea2985d145309f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 60
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (731+((h/13+packedAt s0K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s0K4 (1760+((h/20+packedAt s0K4 (1620+(h % 20)*7) 7) % 73)*7) 7
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xe3c7c7f1fe3ff8e38e0e383f1f83ffe61339f
  | 2 => 0xf03f807fe3ffe3f03f00fc03fe3ff83e863cf3
  | 3 => 0x3fff8ffc03fc7fc000fffc7fc03fc107cf1c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x404610c15105400a182a40a0a0490d18611185
  | 2 => 0x288849228a4204502110a449121490a4862432
  | 3 => 0xa511282408c880b4400429185482a285024e18
  | 4 => 0xc40132484080c9268a46001069230309280bc0
  | 5 => 0x8224000931312493498d26200040430d5b000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xffffffc0fcf0ccc0ffffffc0fcf0ccc0ffffffc0fcf0ccc0ffffffc0fcf0ccc0ffffffc0fcf0ccc0ffffffc0fcf0ccc0ffffffc0fcf0ccc0ffffffc0fcf0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_28023
namespace PEqualNP.Outside.L_meta_28023
open PEqualNP.Outside.L_meta_28023.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xca0ee32ed32bf40bd40
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (67+((h/1+packedAt s1K4 (64+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3c38f1e3f3fc7ffc631c38e0f8fc3fff21327f
  | 2 => 0x3fc0fe03fc7f8f1f83e03f00ff1fc70f463d93
  | 3 => 0xc000fffcff800fe3fc003fff1fe007f087ce1c
  | 4 => 0xffff0000fffff003ffffc0001ffff800f80fe0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x6011804122084004105102820242184211025
  | 2 => 0x88a2214a2948182282222912490a822a462492
  | 3 => 0x819444c241192205a4008a461a419462824e18
  | 4 => 0x11100490801002492848800414911040880b40
  | 5 => 0x222089000a624c92539334988002208c75b000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xffffffa0fafaaaa0ffffffa0fafaaaa0ffffffa0fafaaaa0ffffffa0fafaaaa0ffffffa0fafaaaa0ffffffa0fafaaaa0ffffffa0fafaaaa0ffffffa0fafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_28023
namespace PEqualNP.Outside.L_meta_28023
open PEqualNP.Outside.L_meta_28023.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x990df32dd32bf40bd40
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (67+((h/1+packedAt s2K4 (64+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3c78f0e3f3fff8fc638e0c70f8fff87f1133cf
  | 1 => 0x3f80ff03fc78ff1f83f00f80ff1c3f8f623d33
  | 3 => 0xc000fffcff80ffe3fc000fff1fe03ff083ce3c
  | 4 => 0xffff0000ffff0003fffff0001fffc000fc0fc0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x6011804122041004102841420260844111045
  | 1 => 0x8852228a29419022829128884908950a622512
  | 3 => 0x1244440401220052400412212412220804a28
  | 4 => 0x9130065281103249a8a460021c918322a40f80
  | 5 => 0x224088800a64c49253498e4c8002044c5bb000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xffffff88eeaaee88ffffff88eeaaee88ffffff88eeaaee88ffffff88eeaaee88ffffff88eeaaee88ffffff88eeaaee88ffffff88eeaaee88ffffff88eeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_28023
namespace PEqualNP.Outside.L_meta_28023
open PEqualNP.Outside.L_meta_28023.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x603001e8d21628a8082368089a262d2af10787092e7052900a112e3ab4392320068058980030aacf84005538018010802000000619900d08614908f041ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x178f000020010c7b40800003e001d8ea4e2c88d0e221b0e43e00001202e641000000610c0ec0e0008800000f0611068130c90800003c9004e3d42800b80a351c8e6513193c0030000e81a2e00058ac7e001683c35268fc1065000c84a00188000000330000000379889600341303660009c000452994092802c0b4f400290ac00092b80000001e11c048414818fe33001a400410e800582602800fa002f80000004104800033606800000020cda38001502a001202caa5d0a1d06e46359f0ee7114000006e0e000002a000005e4a00000200e3380086002d8840003010000000a02000b2001020700090000000003000000010001070000020106000b0200000000030c02020600bb28c87755190e7ca721cf54a43db28c87b55190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed94443daa8887ba5010e7aa021ee540439ca80873e53d0a7aa1a14f552429e29a85af5250a7ea0a14f950429faa6653c54ccaeca3995d547329f2a4653d548cb5a85194fd51329e2a265ad424ca7ca8194f55032bb2886575510caf4a0195e54032af29c835d53907388798cf952319eaa463b6548c76aa918dd54e31db21c63b4438c76e8518ed50a319faa2633c544c7388698edd5131da2a263d7534c7ae8698ed90d31da21a63d4434c7288698edd0931daa1263d7324c7aa6498dd944319f2a6433d54c867ca810cf55021af298435d53086f4a010de540219f29e813d52d036c63a06d4c7409eaa4813c535027ea4a06d8c540da98a81bb505027ca8204fd53309e2a6617651cc2eaa398754c7309f2a4613d548c37281184fd51309e2a261d5314c37280984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9904f952209eaa4413e544827aa8905dd4520ba28a413e540827aa8105794c20aea98417651082eaa2107a480209f2a4213d548427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x18854032468a163200004565c424468800e5a00005608038d5c0002a147d3ac3001789026c88662a401c00001004c40aa5167498f3c24604300a20d247f00000000a55865310f255294443c95495110f295294043ca9495010f295254043cc9455010f3151540438e5805350a3960153328b195424ca8d6210f31a658043cc6a56210e31ac580438c68d6210d31a6580434c69664d4d318d996434c6966390d318d994434c6a56210d31ac580434c6c56210d31b4580434c6966510d31c5994434c7866210d31a5588434c7856210d31a1588434c7926010d31a5580434c7916010d31a4580434c6946350931a5193324c694644c931e1509324c62d6214d40c514d315022d6215330c515131cc314544c5308e195404c39131501308718d54482556314520d254d20083615148020
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xc20940400c07020005a058a6010d31d04c4b008698e8162580434c648b80c6a1263245c064cc931908eca126498d057214d3150282b90a898e61841953150130
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
  | 4 => packedAt s3K4 (4032+((h/45+packedAt s3K4 (3672+(h % 45)*8) 8) % 198)*9) 9
  | 3 => packedAt s3K3 (1996+((h/16+packedAt s3K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s3K2 (453+((h/3+packedAt s3K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf1e3c7fc78ffe3f18e3838fe38ff87f10f1cf
  | 1 => 0xfe03f9ff80e3fc7e0fc03f1fc0e3f8f633933
  | 2 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x41404600421408400840908240830824105045
  | 1 => 0xa20c89489128540860a42910a424930a612912
  | 2 => 0x9110112400a0019100422409402440828228
  | 4 => 0x2404010a010004922229080032288102240d80
  | 5 => 0xc8d82250364d3924dcd273c90041066cdbf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_28023
namespace PEqualNP.Outside.L_meta_28023
open PEqualNP.Outside.L_meta_28023.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2c06480273e108151a9800046252a150187af400170002640003c5ce82480088536507082c6910c262cc000e2952b5a000293800010b5c300b403200580000ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x7d3b1490c733d008003d259b4166a121d064091d1e47e372790494672d86c42640f9c82c3c2e05cb081130f8107c270bc70801c9b8566314174b411021150e500e90cb2530f134bc220000040000019400471184058830d01ccc613400c666b420b84a0c3c0280000300c0d87f2a000900000000ee001a8000000310b43229200382a000009c0c46001c0001202800ae0024870a27b42800ac551d8008400000d0543126000260d001c42882221bc1e01001d4d27e2f8606c1101163600230f010201001701080300081506021149041801020009000712000000030a00002d020300080f02b7294876d5290e7ca721eb94a43d6a94873d5190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010e7aa021ee540439ca80875e5390abaa7216710f329f2a4653d548cb5ca9196b55232b6a9c65ae438cb5887194fd51329e2a2659c434cb5ea8996b15132e7a9a65cf434cb5c86996b10d32e621a658c434cadca4194f94f41d719683ad32d067aa1a0cf552419e29a83ae325075a64a0edd45419fa82833e541067ea998cf15331b7296636d52cc79a6598cf952319eaa463b5418c67ea898cf15131e699263b5414c67ca818cf55031b7290636d520c6f4a018de540319f2a4433d548867ca810cf55021af298435d53086f4a010de540219f29e81ae32d035a65a04f547409eaa4813c535035c64a06b4c9409fa8a81bb505027ca8204fd53309e2a6616e52cc2daa598734cb309f2a4613d548c37281184fd51309e2a261cd324c37280984f950309eaa0616e520c2daa4185d94430baa88613e548827aa9104f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa8885bd4910b6292213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x30000000000000000001e1800050614800048a80567802d0044c8d3e0801b00708005c10b1d0090720601c431002509300b002746991170a2c500060178028052800069500001000280024000000188840000280a358a5310f265254443c95495110f315194043ca9495010f295254043cc9455010f315154043a558443cca996010f32a9584438caa96010e32a5584434ca996010d32a3993534ca2e6590d32a398e434ca2e6510d32a9584434caa96010d32b1584434cac96010d32a3994434cb0e6510d32e1984434ca8d6110d32e1584434ca856110d32e2980434ca8d6010d32e2580434ca896010d328e580535070c534c9418e58054cc70c544cb31c3151324c6346550531e14c9414c6356114d40c314d32502356115330c315132cc30c544c9308e195404c38932501308718d544424d6314910d454d10043615244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x200000404a720cc2805a05866010d32d04c2b00869968161580434ca84b80a699283425c0544cb31c08ca9928298d057114d3250282b88a899661821953250130
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
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 80)*7) 7
  | 2 => packedAt s4K2 (456+((h/3+packedAt s4K2 (441+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e1e3c7fc7f1fe3f1c63838fe3f1f87f10f4cf
  | 1 => 0x1fe03f8ff8fe3fc7e07c03f1fc7e3f87233b33
  | 2 => 0xe0003ff3ff003ff8ff8003fe3f803ff8c3cc3c
  | 3 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x42804600424208400820908240910822105045
  | 1 => 0x84088840908050084044211084281204212112
  | 2 => 0x15511292424a401b4804a242904a550c28c28
  | 3 => 0x8440122002004922509080032448110440e80
  | 5 => 0xd198224836c93924da7273c900090666bbf000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_28023
namespace PEqualNP.Outside.L_meta_28023
open PEqualNP.Outside.L_meta_28023.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x427928a0ea0b1f067008d32500002280795302c1064e00829441092a4c00d93000118e0a2158000252003474b8c0004000b08000705f000040ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1406a4000d079da900a9aaa88017a489252c8b0eaa28101723839a929a1892020027812b9d001c1b080180040026060f04a321228c2c001ba59580072d94800e0b801f80089e800a1680050019271e2191a2209600001310952d0fab058c938d82899f198a83001ca6912000180000008702000010c10600040c10c20001081e0c705062c0001800301bb28e877551d0edca521db54a43af29c855d5390abca6215754c42bb28885755110af4a0215e540429f2a6653d54ccb3ca9996755332aea9c65cf524cb9e84997310932af298655e53d06baa7a0e794f41cea9e839f32d073a65a0cf55241cf992839d325076ea2a0cf95041daa0e633e548c67aa918cf950319eaa0636e520c6daa418ed50431bd2806379500c6bca790d754f21e6996433e548867aa910ed50621e699243b5414867ca810cf55021af298435d53086f4a010de54021af298815d53102dca4205b54840bb2888175511027ca8184f55030b7290616d520c2eca2185d54430af29e415d53c839a65904fd51209e2a241cd324827ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a838857d4d10ae29a21b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x434003386012de93808c0800a2804a80428d58654cca956195332a3993524cac56110932b2580424ca4d6294f41a358a53d061d65ccb41a598f51507255250431cc505500c78532505218d584544830c544c9209358853443145350510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1418090ae3326a4994857298f5150682b88a899241415c85350510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s5K3 (633+((h/5+packedAt s5K3 (608+(h % 5)*5) 5) % 22)*5) 5
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3cfe3c7fc7e3f1f8c63c70fe3f0fc78474cf
  | 1 => 0xf03f1fc063f9fc7e3f07c780e3c7f1f99a4b33
  | 2 => 0xffc01fff83fe007fc7f807ff03f801fe638c3c
  | 3 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1040200804004020000081020090040001045
  | 1 => 0x10888411049080c042024484484240a10a4112
  | 2 => 0x22024888090049200948012202902514208c28
  | 3 => 0x441241aa5225402495d4900a1324ac14740e80
  | 4 => 0x88a091304035924926a7264c9800c8215f6000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_28023
namespace PEqualNP.Outside.L_meta_28023
open PEqualNP.Outside.L_meta_28023.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d243179f00b1c3100d4e200000022128c00a1e057390000da80e192306e21a363a515804c845bb0601d322e0022d2c9c99866408804a68f192a39e805218341020604000280c4800c08800264c180027fd5007fe54007f55007fc54027fd4c05fe53007f54c05fc5301ffd0c05fe43007f50c05fc43027fd4801fe52007f54809fc5201ffd0801fe42007f50807fc42017fcc801fe32007f4c805fc32027fd4401fe51007f54409fc5101ffd0401fe41007f50407fc41017fcc401fe31007f4c405fc31007fc8401fe21007f48401fc21027fd40017f5000ff94001fd50005f54003fc5001ffd0003fe40007f50003fc40017fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24009fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007fe1048003fd0824001ff0412002ffecb88016ff65c400bff32e2004bf9971002ffacb88002fd65c400bfe32e2005bf1971002ffec988016ff64c400bff3262003bf9931002ffac988002fd64c400bfe3262005bf19310067fea98802ffe54c4001feaa6200bff1531002ffec788016ff63c400bff31e2002bf98f1002ffac788002fd63c400bfe31e2005bf18f10067fea78802bfe53c4001fea9e200aff14f1005ffe878802bfe43c4001fea1e200aff10f1002ffec588016ff62c400bff3162009bf98b1002ffac588002fd62c400bfe3162005bf18b10067fea588003fe52c4001fea96200cff14b1005ffe8588003fe42c4001fea16200bff10b10057fe6588003fe32c4001fe996200aff0cb1000dfcc388017ff51c400bff28e2005ff5471002ff8a388017ff41c400bff20e2005fd9071002ffa8388003f541c400bfe20e2005ffcc71002ffc6388017f631c400bfe98e2000fd4c71002ff86388017ff21c400bff10e2005fd8871002ffa4388003f521c400bfe10e2001bf5831000ffea1880077f50c4003ff2862001ff5431000efaa188007fc50c4003ffa062001ff9031000ffa8188007fc40c4003ff9862001ff8c31000ffa6188007fc30c4003ff9062001ff8831000ffa4188007fc20c4003ff0862001fd8431000ff42188007fc10c4003fa0862000ffd9510005feca88023fe65440097f32a2000ff59510005faca88023fc65440097e32a2000ffd9110005fec88801ffe64440077f3222000ff59110005fac88801ffc64440077e3222008ffd511003ffca888003fd544400ffe2a22000ffd8d10005fec68801bfe63440057f31a2000ff58d10005fac68801bfc63440057e31a2008ffd4d10037fca688003fd534400dfe29a2007ffd0d10037fc8688003fd434400dfe21a2000ffd8910005fec488003fe62440137f3122000ff58910005fac488003fc62440137e3122008ffd4910007fca488003fd5244011fe2922007ffd0910007fc8488003fd424400ffe2122006ffcc910007fc6488003fd324400dfe1922001bfd8510047fea288017fe5144001fea8a2005ff1451003ffe8288017fe4144001fb20a2000ff50510007ea8288017fc414400dff98a2005ff8c510007ec6288003fd3144001fa98a2005ff0c510007fe4288017fe2144001fb10a2000ff48510007ea4288017fc21440037fb022001ffd411000efea088007fe5044003fea822001df5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff104400bfd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd214c001fe10a6001bfd813000ffea0980077f504c003ff2826001fe9413000ffaa0980077d504c001fca826000de5413000ff8a098007ff404c003ff2026001ff5013000ff88098007ff304c005fd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffc4098007fc204c003ff0826001fe8413000ff82098027ff65c80137fb2e4009ff99720025fccb90027fd65c80017eb2e4009ff1972004df8cb90027ff64c80137fb264009ff9932001dfcc990027fd64c80017eb264009ff1932004df8c99004bff54c8023ff2a64000ff5532008ff8a990027ff63c80137fb1e4009ff98f20015fcc790027fd63c80017eb1e4009ff18f2004df8c79004bff53c8021ff29e4000ff54f20087f8a790047ff43c8021ff21e4000ff50f20087f88790006fe62c8013ffa964009ff94b2004ffaa590027fc52c8013ffa164009ff90b2004fdc8590027fd42c8001f6a164009ff10b2004ffe6590027fe32c8013f71964009ff4cb20007da6590027fc32c8013ffb0e4009ff9872002dfcc390027fd61c80017eb0e4009ff18720097fea390003fe51c8001fea8e4012ff1472008ffe8390003fe41c8001fea0e4011ff10720087fe6390003fe31c8001fe98e4010ff0c72004ffe4390027ef21c8013ff10e4009ff48720007da4390027fc21c80037eb064001ffd432000efea190007fe50c8003fea864001df5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff0864001ff04320007feca90002ff654801fff32a4004bf99520007faca90002fd654801ffe32a4004bf19520007fec890002ff644801dff3224003bf99120007fac890002fd644801dfe3224003bf1912007ffea89003bfe5448001feaa2400eff15120007fec690002ff634801bff31a4002bf98d20007fac690002fd634801bfe31a4002bf18d2007ffea690037fe5348001fea9a400dff14d20077fe8690037fe4348001fea1a400dff10d2000dfec49003fff5248013ff2924000ff5492004ff8a49003bff4248013ff2124000fb90920007fa8490003ed4248013fe212400dffcc92004ffc6490003ee3248001fe9924000fb4c92004ff86490003ff61480017fb0a4000ff98520007fac290003fc614800b7e30a400fffd4520007fca290003fd514801ffe28a400effd0520007fc8290003fd414801dfe20a400dffcc520007fc6290003fd314801bfe18a4009ffc8520007de4290003fe2148001fe90a4000fb4852004ff84290006ff6048003ffa824001dfd412000ffca090007fd5048003bea824001ff1412000ffe8090007fe4048003fd2024001ff50120007f28090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9
  | 2 => 0x50006fac6a805f7c6354031bfa1aa017df90d50006fa86a805f7c4354001bfb12a000df98950006fac4a80037c6254031bfa12a000df90950006fa84a80637c425402fbf992a000df8c950006fa64a805f7c3254001bfb0aa000df98550006fac2a80037c6154031bfa0aa000df90550006fa82a80637c415402fbf98aa000df8c550006fa62a805f7c3154001bf90aa000df88550006fa42a80037c2154003bfb02a0019fd8150026f6c0a80077f4054003bf202a001de9015000ef880a80077f3054003bf182a001de8c15000ef860a80077e2054003be102a001df8415000ef820a8003ff65500017fb2a8016ff99540025fccaa0003fd65500017eb2a8016ff19540025f8caa0006ff6450007ffaa28003ff9514001ffaa8a000ffc5450001ffb1a8000bfd8d400affcc6a000afe6350001feb1a8015ff18d40015f8c6a005bff535002bff29a8000ff54d400aff8a6a000fff4350007dfa1a8003ff90d4001ffa86a0003bd4350007fe21a8000ffd8940005fec4a0003fe6250001feb128000ff1894004df8c4a005bff5250001ff2928000ff549400b7f8a4a000fff4250007dfa128003ff9094001ffa84a0003bd4250007fe2128015ffcc940007fc64a0003fd325002bfe1928000ffd8540005fec2a0003fe6150001feb0a8000ff1854002df8c2a005bff5150001ff28a8000ff545400b7f8a2a000fff4150007dfa0a8003ff9054001ffa82a0003bd4150007fe20a8015ffcc540007fc62a0003fd315002bfe18a8000ffc8540007fc42a0003fd2150001fe10a8001bfd814000ffea0a00077f5050003ff2828001fe9414000ffaa0a00077d5050001fca828000de5414000ff8a0a0007ff4050007fda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffe60a0007fe3050003fe1828001ff8814000ff440a0007fc2050003ff0828001ff04140007feca98002ff654c029ff32a6004bf99530007faca98002fd654c029fe32a6004bf19530007fec898002ff644c027ff3226003bf99130007fac898002fd644c027fe3226003bf191300a7fea89804ffe544c001feaa26013ff1513000dfec69800bff534c005ff29a6002ff54d30017f8a69800bff434c005ff21a6002f790d30017fa8698003dd434c005fe21a6000ffd8930005fec498003fe624c001feb126000ff1893004df8c498053ff524c001ff2926000ff549300a7f8a49804fff424c001ff2126000ff5093009ff8849800bff324c005ef9926002ff8c930017fa6498003dd324c005fe1926000ffd8530005fec298003fe614c001feb0a6000ff1853002df8c298053ff514c001ff28a6000ff545300a7f8a29804fff414c001ff20a6000ff5053009ff8829800bff314c005ef98a6002ff8c530017fa6298003dd314c005fe18a6000ffc8530007fc429800
  | 3 => 0xe298421dffd0c210e7fc8610803fd4308439fe2184209bf9882104ffea410827fe5208413fea904209ff1482104ffe8410827fe4208413fea104209ff1082104ffe6410827fe3208413fe9904209ff0c82102dfcc210817ff510840bff2884205ff5442102ff8a210817ff410840bff2084205ff5042102ff88210817ff310840bff1884205ff4c42102ff86210817ff210840bf79084205ff8842102fec4210817fd210840bf69084209fd4842102ffec010817fe60084037f3004205fe9802100df4c010817fd60084017eb004205fe58021005f2c010817fc60084037e300421effd40210dffca01086ffc500843bffa00421bff900210dff88010873ff3008437ff180421bff0c02104ffc4010827fc200840bff0804205ff04021026fec9a80137e64d4009beb26a004df19350026fec7a80137e63d4009beb1ea004df18f500d6fe87a80677e43d4001bea1ea019df10f50026fec5a80137e62d4009beb16a004df18b500d6fe85a80037e42d4001bea16a01adf10b500cefe65a80037e32d4001be996a019df0cb50026fec3a80137e61d4009beb0ea004df187500d6fe83a80037e41d4001bea0ea01adf107500cefe63a80037e31d4001be98ea019df0c750006fe43a80037e21d4001be90ea000df0875000cfac1a80077f40d4003bf206a001df1035000efe61a80077e30d4003be186a001df8835000ef841a80077e10d4003be086a001bfd9550007fec8a8002ff6454031ff322a003bf99150007fac8a8063fc64540077e322a004ffd5150026fea8a8013fe5454031bf2a2a004ff55150006faa8a8013fc5454009be2a2a000ffd8d50005fec6a805ffe63540057f31aa000ff58d500bff8c6a800afc6354009ffa9aa004dfd4d50027fca6a805f7e5354009fea9aa000df54d50027f8a6a80137c5354031ffa1aa017ff90d50007fa86a805ffc4354001ffb12a000bfd8950007fcc4a8003fd6254001fe312a009bf18950027fea4a80137f5254009ff292a000df94950027faa4a80037d5254009fe292a004df149500c7fe84a8003fe4254001fea12a018ff109500bffe64a8003fe3254001fe992a017ff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8016fc6154009ffa8aa004dfd4550027fca2a80037e5154009fea8aa000df54550027f8a2a80137c5154031ffa0aa000ff90550007fa82a8063fc415402fff98aa000ff8c550007fa62a805ffc3154001ff90aa000ff88550007fa42a8003fc21540037fb02a001ffd4150027f6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ffa02a001ff9015000ff480a8007fc4054003ff982a001ff8c15000ff460a8007fc3054003ff102a001ff0815000ffc20a8007fc1054001bfb22a018df99150006fac8a80637c6454001bfb1aa017df98d
  | 4 => 0x827fc20c844fff0864205ff0432102ffecb10816ff658840bff32c4204bf9962102ffacb10802fd658840bfe32c4205bf1962102ffec910816ff648840bff3244203bf9922102ffac910802fd648840bfe3244205bf19221137fea910897fe5488401feaa44225ff1522102ffec710816ff638840bff31c4202bf98e2102ffac710802fd638840bfe31c4205bf18e21137fea710893fe5388401fea9c4224ff14e2112ffe8710893fe4388401fea1c4224ff10e21005fac51089bff5288413ff2944200ff54a2104ff8a510897ff4288413ff2144200ff50a2104ff88510893ff3288413ff1944200ff4ca2104ff86510816fe618840bffa8c4205ff9462102ffaa310817fc518840bffa0c4205ff9062102fec8310817fd4188401faa0c4205ff1062102ffe6310817fe318840bfe98c4205ff0c62102ffe4310817ef2188413fb90c4205ffd822102ffcc110806fe608840bfeb044200bf5822102ff8c110806fc608844dffa844223ff9422111ff8a110897ff4088447ff2044223ff10221127fe611088ffe3088447fe1844223ff8822104ff84110817fe108840bfe0844200ffd9521005feca9088bfe65484097f32a4200ff59521005faca9088bfc65484097e32a4200ffd9121005fec890887fe64484077f3224200ff59121005fac890887fc64484077e3224222ffd512110ffca890803fd5448443fe2a24200ffd8d21005fec690883fe63484057f31a4200ff58d21005fac690883fc63484057e31a4222ffd4d21107fca690803fd5348441fe29a4221ffd0d21107fc8690803fd4348441fe21a4222ffd492104ffca490803fd5248413fe2924221ffd092104ffc8490803fd4248413fe2124220ffcc92104ffc6490803ee3248401fe9924200fb4c92104ff8649088bff514840bff28a4200ff5452102ff8a290887ff414840bff20a4200fd90521007fa8290803f5414840bfe20a4220ffcc52102ffc6290803fd314840bfe18a4209ffc852104fee4290817fe214840bf710a4200ffd8121005fec09087ffe60484037f3024200ff581210fff8c090806fc6048445ffa82421fff941210fff8a090887ff404843fff202421fff10121107fe609087ffe304843ffe182421fff8812104ff8409087ffe104840bfe0824205ffd942102dfeca10817fe65084097f3284205df99421024fcca10817fd65084017eb284205df59421004faca10817fc650840b7e3284205ffd902102dfec810817fe64084077f3204205ef9902101d7cc810817fd64084017eb204205ef590210057ac810817fc640840b7e320421effd50210effca810803fd540843bfe2a04205ffd8c2102dfec610817fe63084057f3184205f798c21015bcc610817fd63084017eb184205f758c21005bac610817fc630840b7e318421effd4c210e7fca610803fd5308439f
  | 5 => 0xe3102ffec518817fe628c4137f3146205ff58a31005fac518817fc628c461ffa946200ff94a31007faa5188c3fc528c45fffa146200ff90a31007fa85188bffc428c405ff9946202ff8ca31017fa651880bfc328c40b7f30c6205ffd463102ffca318817f6518c40bfea8c6200fd5463102ff8a318817ff418c40bff20c6205ff5063102ff88318817ff318c40bef98c6202fdcc63102ff86318817f4318c40bffb046205ff9823100dfcc118817fd608c4017eb046205ff1823100df8c1188c3ff508c45dff284622eff1423117ffe81188bbfe408c45dfe2046202ffcc231017fc611880bfc308c45dff104622eff0823102ffc2118817fc108c401ffb2a6200bfd953116ffcca98812fe654c401feb2a6200bf5953116ff8ca98812fc654c401ffb226200bfd9131167fcc89880efe644c401feb226200bf59131167f8c89880efc644c45bffaa2622cff95131007faa8988b3fc544c40b7fb1a6202ffd4d31017fca69880bfd534c405fe29a6202ffd0d31017fc869880bfd434c405fe21a6200ffd8931005fec498803fe624c401feb126200ff1893104df8c4988b7ff524c401ff2926200ff5493116ff8a4988b3ff424c401ff2126200ff50931167f8849880bff324c405ef9926202ff8c931017fa6498803dd324c405fe1926202bfd853116ffea298817fe514c401fb28a6200ff54531007eaa298817fc514c459ffa0a6205ff90531007fa8298817fc414c405ff98a6202fdcc53102ffc6298817de314c40bfe18a6205f70c531017e86298803ff604c4017fb02622bff9813100dfcc098803fd604c457fe3026201bf1813116ffea0988affe504c457fe282622cffd013115ffc80988affc404c405ff9826202f7cc131017fc609880bfc304c457ff102622bff0813115ffc2098817fc104c413ffb2e4209bfd972104ffccb90812fe65c8413feb2e4200bf5972104ff8cb90826fc65c8413ffb264209bfd932104ffcc99080efe64c8413feb264200bf5932104ff8c990826fc64c8455ffaa64229ff95321007faa9908a7fc54c8413ffb1e4209bfd8f2104ffcc79080afe63c8413feb1e4200bf58f2104ff8c790826fc63c8455ffa9e4228ff94f21007faa7908a3fc53c8453ffa1e4228ff90f21007fa87908a3fc43c8413ffa964209ff94b2104ffaa590827fc52c8413ffa164209ff90b2104ffa8590827fc42c8413ff9964209ff8cb2104fdc6590827fd32c8401f69964209ff0cb21157fea390817fe51c8401fea8e4205ff1472114ffe8390817fe41c8401fea0e4205ff10721147fe6390817fe31c8401fe98e4205ff0c72104ffec190827fe60c84037f3064209ff58321005fac190827fc60c84037e306422affd432113ffca19089ffc50c8453ffa064227ff9032113ff881908a3ff30c844fff1864227ff0c32104ffc4190
  | 6 => 0x9ffa82a204dfd4151027fca0a8813fc5054473ffa02a237ff901511bff880a88e3ff305446fff182a237ff0c1511bffc40a88dffc205446fff082a205ff0415102ffecb20816ff659040bff32c8204bf9964102efccb208127e659040bfeb2c8200bf5964102efacb208027d659040bfe32c8205bf1964101dfac92080fff5490407ff2a48203ff5524101ff8a920817ff639040bff31c8202bf98e4102ffac720802fd639040bfe31c8205bf18e411b7fea7208d7fe5390401fea9c8235ff14e4101ffe872080ffe4390407fea1c8203ff10e4102ffec520817fe62904137f3148205ff58a41005fac520817fc629046dffa948200ff94a41007faa5208dbfc5290407ffa148203ff90a4101ffa852080ffc429046bff9948200ff8ca41007fa65208d7fc329040b7f30c8205ffd464102ffca320817f6519040bfea8c8200fd5464102ff8a320817ff419040bdfa0c8203fdd064102ff88320817f4419040bff98c8235fdcc64102ff86320817f4319040bffb048205ff9824100dfcc120817fd60904017eb048205ff1824100df8c1208dbff5090469ff2848234ff1424101ffe812080ffe4090407fe2048235ffcc2411a7fc61208d3fc3090469ff1048234ff0824102ffc2120817fc1090401ffb2a8200bfd954119ffccaa0812fe6550401feb2a8200bf5954119ff8caa0812fc655040b7fb228203ffd514119f7ea8a080ffe5450407feaa28203ff1514101f78a8a0803ff63504017fb1a8232ff98d41015fcc6a0803fd6350465fe31a8202bf18d4119ffea6a08cbfe5350401fea9a8232ff14d4101ffe86a080fbf4350407ff21a8203ff50d410077a86a080ffc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128209bf1894119ffea4a0803fe5250401fea928233ff1494101ffe84a080fbf4250407ff2128203ff509410077a84a080ffc4250465ff9928200ff8c941007fa64a08cbfc32504077fb0a8233ffd454102ffca2a0803f65150401fea8a8200fd5454102ff8a2a080fff4150407fba0a8205ff9054102f7c82a0817fc415040bde20a8203fd10541197fe62a08cbf7315040bfe18a8232fd0c541007fec0a0802ff6050463ff3028201bf98141007fac0a08c7fc60504037e3028233ffd414118ffca0a08c7fc5050407ffa028203efd014101ffc80a080ffc4050465ff9828231ff8c14118ff860a08c7fe2050463fe1028231ff8414102ff820a0817ff658c40b7fb2c6205ff99631025fccb18817fd658c4017eb2c6205ff1963102df8cb18817ff648c40b7fb246205ff9923101dfcc918817fd648c4017eb246205ff1923102df8c9188c3ff548c45fff2a46200ff5523117ff8a91880afd638c405ffa9c6202ff94e31017faa71880bfc538c405ffa1c6202ff90e31017bc871880bfd438c401eea1c6202ff1
  | 7 => 0x990ffff544c87dff2a26400ff551321f7f8a899026ff634c805ffa9a643ff7d4d32017fca69900bfd534c805fe29a6402f714d32017fe869900bfe434c805ef21a6402ff50d32007ba869900bfc434c8057fb12643fffd493204ffca499003ee524c801fea926400fb5493204ff8a4990fbff424c87df7a126409ff90932007fa8499027fc424c87df62126402ffcc932017de6499027fe324c813ef1926409ff0c93204fb8649900bec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6405bf185321fffea2990fffc514c87dffa0a643eff10532017fe629900bdf314c805fe18a6400ffd8132005fec0990f7fe604c8037f3026400ff581321eff8c099006fc604c87fffa82643dff941321eff8a0990fbff404c87bff202643dff10132017fe609900bdf304c805ff1826402ff0c1321effc4099027fc204c87bff082643dff04132025facb28817ff649440bff324a203bf9925102f7cc92880ebe649440bfeb24a200bf5925102f7ac928802bd649440bfe324a205bf19251027fea928813fe5494409feaa4a204ff1525102ffec728817fe63944057f31ca205ff58e51005fac728817fc639440b7e31ca204ffd4e51027fca728813fd5394409fe29ca23cffd0e511dffc8728803fd4394477fe21ca205ffd8a5102ffcc528826fe629440bfeb14a200bf58a5102ff8c528813ff5294409ff294a204ff54a51027f8a5288f3ff4294401ff214a200ff50a511e7f885288efff3294401ff194a200ff4ca511dff86528816fe619440bffa8ca205dfd4651027eea328817fc519440bfa28ca205ffd065102ff88328817ff319440bfe18ca205ffd825102ffcc128806fe609440bfeb04a200bf5825102ff8c128806fc6094409ffa84a204dfd4251027fca128813fc5094479ffa04a23aff902511d7f881288efff3094475ff184a23aff0c2511d7fc41288ebfc209440bff084a205ff0425102dfecaa8803ff64544017fb22a239ff9915101dfcc8a8803fd6454473fe322a203bf19151027fea8a8813fe5454473bf2a2a204ff55151027f8a8a88137c5454401ffb1aa200bfd8d511c7fcc6a880afe6354401feb1aa238ff18d51015f8c6a8813ff5354409bfa9aa204ff94d51027faa6a88037d5354409fe29aa239ffd0d511c7fc86a8803fd4354471fe21aa200ffd8951005fec4a8803fe6254401feb12a200ff1895104df8c4a8813ff5254409bfa92a204ff94951027faa4a88037d5254409fe292a239ffd0951007fc84a8803fd4254473fe212a238ffcc951007fc64a8803fd3254471fe192a204bfd8551027fea2a8813f7515440bff28aa205df9455102ff8a2a88177c5154409fa28aa239ffd055102ff882a88e3ff315440bfe18aa200ffd8151005fec0a88dffe60544037f302a200ff581511bff8c0a8806fc605440
  | 8 => 0xfd4a4204ffca521027ee5290813fea948400fb54a4204ff8a521027ff4290813dfa148403fbd0a4204ff88521027ec4290813ff9948409ff0ca4204ffec321027fe619080b7f30c8409ff58642005fac321027fc6190891ffa8c8448ff1464201ffe832100ffc419088fff98c8447ff0c64204ffec121027fe60908037f3048409ff58242005fac121027fc60908037e3048448ffd4242237fca12111bfc5090807ffa048403ff9024201ff8812111fff309088dff1848446ff0c24204ffc4121027fc209088dff0848446ff04242007fecaa1002ff655088bff32a8404bf99542007facaa1002fd655088bfe32a8404bf1954204dfec8a100fff5450807ff2a28403ff5514201ff8a8a1003ff63508017fb1a8444ff98d42015fcc6a1003fd6350889fe31a8402bf18d4222ffea6a1113fe5350801fea9a8444ff14d4201ffe86a100ffe4350807fea1a8403ff10d4201dfec4a1117ff5250813ff2928400fb94942007faa4a1003ed5250813fe2928403ffd094201fde84a1027fe4250813df2128409ff1094204f7884a100fec4250889ff9928409ff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1016fc615088bffa8a8445ff1454201ffe82a100fbf4150807fe20a8444ffcc542227f862a1003ff60508017fb028443ff9814200dfcc0a1003fd6050887fe3028401bf1814222ffea0a110ffe5050887fe2828403ffd014201f7e80a100ffe4050807fe2028444ffcc14221ffc60a110ffc3050887ff1028409ff0814221ffc20a110ffc1050813ffb2c6409bfd963204ffccb19012fe658c813bf32c64049f9963204ffacb19002fd658c813beb2c64009f5963204ff8cb19026fc658c813ffb246409bfd923204ffcc91900efe648c813feb246400bf5923204ff8c919026fc648c885ffaa46441ff95232007faa919107fc548c8057eb1c6402ffd4e32017fca71900bfd538c805fe29c6402ffd0e32017fc871900bfd438c805fe21c6409bf98a3204ffea519027fe528c813f72946409ff54a32007daa519027fc528c813ffa146441fbd0a3204ffc8519027fd428c813fe2146409fb10a3204ffe6519027df328c805f79946409ff0ca3204fd86519027ff618c813ff30c6405bf9863204ffac319002fd618c813fe30c6442ffd4632217f8a319107ff418c883fe20c6402ffcc632017f86319027ff608c813ff3046401bf9823204ffac119002fd608c813fe3046401bf18232217fea119103fe508c881fe2846441ffd0232207fc8119103fc408c805ff9846402ff8c232017f86119027fe208c813fe1046440ff84232207f82119003ff654c8017fb2a643fff99532025fcca99003fd654c8017eb2a643fff19532025f8ca99003ff644c8017fb22643eff9913201dfcc899003fd644c8017eb22643eff1913201df8c8
  | 9 => 0xc05ff9928602f7cc943017f864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c0b7e30a8650ffd4543287f8a2a180fff4150c07dfa0a8603ff10543017fe62a180bfc3150c05ee18a8600ffd8143005fec0a193ffe6050c037f3028600ff5814327ff8c0a1806fc6050ca1ffa82864fff9414327ff8a0a180fff4050c07dfa028603ff9014301ff880a180bff3050c05ef9828602ff8c143017f860a193ffe2050c9ffe102864fff8414327ff820a1812fd6594813ffb24a409ff9925201dfcc929027fd64948017eb24a409ff1925204df8c929013ff5494809ff2a4a404ff55252027f8a929027ff6394813ff31ca402bf98e5204fbcc72900ade6394813feb1ca400bf58e5204fbac729002dd6394813fe31ca409bf18e52027fea729013fe5394809fea9ca404ff14e52277fe8729137fe4394801fea1ca44dff10e5204dfcc529027ff5294813bfa94a404fbd4a5204ff8a529027ec5294813ffa14a409ff10a5204ffe6529027fc3294813ffb0ca409ff9865202dfcc329027fd61948017eb0ca409ff18652027fea329013fc519489dffa0ca44eff1065226ffe6329137fc3194813ffb04a409ff9825200dfcc129027fd60948017eb04a409ff1825200df8c129013ff5094809bfa84a404ff94252027f8a12913bff4094899ff204a44cff1025226ffe6129133fe3094899fe184a409ff8825204ff84129133fe1094899fe084a409bfd9552007fec8a9002ff6454897ff322a403bf99152007fac8a912ffc64548077e322a404ffd5152026fea8a9013fe5454809feaa2a400df55152027f8a8a9003ff63548017fb1aa44aff98d52015fcc6a9003fd6354895fe31aa402bf18d52027fea6a9013fe5354895bf29aa404ff54d52027f8a6a90137c5354897ffa1aa44aff90d52007fa86a912bfc43548097fb12a404ffd4952027dea4a9027fe5254813bf292a409ff1495204ef8a4a9013ec5254897ffa12a409ff10952257fe64a9027fc3254801ffb0aa400bfd8552007fcc2a9003fd6154801fe30aa405bf18552027fea2a90137f5154809fe28aa44bffd055225ff882a912bff3154895fe18aa400ffd8152005fec0a9127fe60548037f302a400ff5815224ff8c0a9006fc6054809ffa82a404dfd4152027fca0a9013fc5054897ffa02a449ff9015224ff880a912bff3054893ff182a449ff0c15224ffc40a9027fc2054893ff082a449ff0415204ffecb21026ff6590813ff32c8404bf9964204ffacb21002fd6590813fe32c8409bf1964201dfac92100fff5490807ff2a48403ff5524201ff8a921027ff6390813ff31c8402bf98e4204ffac721002fd6390813fe31c8409bf18e42247fea72111ffe5390801fea9c8447ff14e4201ffe872100fbf4390807ff21c8403ff50e420077a872100ffc43908137f3148409f
  | 10 => 0x800001200a00400e00c00400000000200200000200e00000400001000000c00200203000000400201400a01c00200a00200001a00400201600201000600200600601000200c01000000200000200000000200400800200000000602600000800201e00000000000000200600a00800000200800000001600400000a00a01202200000000605a01a00400400a00400200000001c00200c00000000000001000200000200200401000200200200000000000403bfd955401dfec8aa00fff5455009dfaa2a803ff9515401efca8aa00ffc5455007be2a2a803ef15154007fec6aa002ff63550a9ff31aa802bf98d54007fac6aa153fc63550057e31aa804ffd4d54027fca6aa013fc5355007ffa1aa803efd0d5401ffc86aa00ffc4355001ffb12a800bfd8954007fcc4aa003fd6255001fe312a809bf18954027fea4aa0137f5255009fe292a803ffd095401ff884aa153ff32550a9fe192a800ffd8554005fec2aa003fe6155001feb0aa800ff1855402df8c2aa013ff5155009fe28aa803ffd055401ff882aa153ff31550a9fe18aa800ffd8154005fec0aa14ffe60550037f302a800ff5815429ff8c0aa006fc6055009ffa82a804dfd4154027fca0aa013fc5055007ffa02a803ff9015401ff880aa153ff30550a7ff182a853ff0c15429ffc40aa14ffc20550a7ff082a853ff04154015fecaa9803ff6454c017fb22a652ff9915301dfcc8a9803fd6454ca5fe322a603bf19153027fea8a9813fe5454c09feaa2a604ff15153015fec6a980bff5354c09efa9aa602ff94d53016fca6a980bfc5354c05be29aa602f714d53017fe86a980bfe4354c05ef21aa602ff10d53007fec4a9802ff6254c01ff312a600ff58953007f8c4a9826fc6254c09ffa92a604ff14953297fe84a994bfc4254c05ff992a602ff0c953007fec2a9802ff6154c01ff30aa600ff58553007f8c2a9816fc6154c09ffa8aa604dfd4553027f8a2a994bff4154ca5fe20aa602ffcc553017f862a9803ff6054c017fb02a651ff9815300dfcc0a9803fd6054ca3fe302a601bf18153027fea0a98137f5054c09ff282a604ff14153297fe80a9947fe4054ca3fe202a602ffcc153017fc60a980bfc3054ca3ff102a651ff0815328ffc20a9947fc1054c01ffb2a8600bfd9543006fecaa18027f6550ca1ff32a8604bf99543007facaa1802fd6550ca1fe32a8604bf19543006f8caa18127c6550c057fb228603ffd514301ffca8a180fbe5450c07feaa28600ef5514301ff8a8a180aff6350c05ffa9a8602ff94d43017bca6a180bfd5350c01eea9a8602ff14d43017fe86a180fdf4350c05ff21a8602ef90d43017f886a180bbc4350c05ee21a8600ffd8943005fec4a1803fe6250c01feb128600ff1894304df8c4a1943ff5250ca1fe2928603ffd094301ff884a180fbc4250
  | 11 => 0x42503a803600600000600000c00000000c00e00400000400000200000200600600001400401400000000200000200000c00800e00800000401800600400000e00200400000e00400600400000000000400c00001000800800000200200200c00000400004c00401200c00603005e00600402600603200400000600000200e00a00200000200601600800601000200200000a00801000000600000800000401200e00000800400200002c00200200201400c00000400202800000200a00000400000200200000400600002602200402000400000600000200000000000200800000400200001600e00001a00003200600600400000000000000200401600000200800400200000000000000201800001000600000a00600400000200200000200602400e00200000000600000801e00c00200000600a01600200003200e00000a00200000000400000600000000400200601601200e00800800200400c00200400202204a00800a00000202a00200000000600800000200200000600401600e04000400200000000001200000000000000801400200800201200200000000200000400a00001000400a00c00000000e00000000e00800400000600003e00000200000801c00200600000000803c00000001000400400600200001000200002200000000000000000001a00400600600000e00e00601600400a00001e00600400200800a00e00000000000200200400000805800000200401200a00000000000002400000801e00800401000400200200000200000000600000002600000e00000800000e00801000400a00000400000000e00000c00600401603400600a00000000600200802000001000600200201c06c00400a01000200000600a00e00a00000000000000200200000200600000400200200400000c00200400000000600000c00600601200000200c00000200002401e00800c00400001401200400000600200000200000000401001400400400201400000001200002c00e00200a01000600c00000000400000000e00400200600200e00e00000601201200000401001401000800000000400200400c01601200000800a01200a00000000400200600200000600000200000401601000401400000000000200200a00a01000200800000400200a01200400400600203e00000000e02201200000400800000e00000600c00200400201802400000201a00600000000a01803000600402400e00001200600200001001000000600001000200800200a00600400e00000000400400000600000200000200400000e00000001e00000000600400000200000000e00000000200000800401000000001a00800000200200000000000200001800800200801600400003000000000200200400000200000200c0000080020080120020000080020
  | 12 => 0x85567df000194c9926293fe93784b081937e8e000001660450000fe612043da48800028d3bd0000000000000000020e12c08c9ba4000000222000112c72649e105c00000041b00000008b7235965811c52a1c680000000c81bb8000c006452d7000037c00042b8000a6600000022306307690001254d3492c0000298000000000151853e2830001becce25fa3c508b475c3a73f888ec1008ae0268fe82ac7752e2903459e84d12c94dc3e858121108041b444300411509488eb00000001124860000000e74000007987800085d29200000000d22948ba0aec8da272978057a3b425b1ed11960d937987f0ce438b3ee16309a641912f814000090d445112000028c3d20b68000000000198c18c30f029097800086c41c844c000000000000000000049f800000000000000006fc00043911f92661e900000008c26b71a90c0c94436800008e80000000fc00002c82a23cc80007343fd0000cfcd3a0000000000000000000035000051c1f621800006bc115888d26a49f17792580004370001c3800000000000004c05510b2800066467808408400000002c580005888c64448fdc0002163cb00000f27fa0000000000000000206800093200003704b60003b517bcb8217f01f00005c40000a20000b0042c000000000013000000000000000000000622000325800000000000000000001820001a8116c19a0001a6c00000019200006183a4371a25406a0532d78000d6c5c902512386727392338000a9e000180800000000000025347c80001b38000a20000000000103000000006bca3600002c02140005d0000083c00000014c800000000000000003b466800000008aa5230000cad0b884b236800026866e1af00000000004399f18ed00000000f9d16a00000000000000000001d580000000001a7800065c161000051613223a14600005b615c8000d2a000000186498a2f61be0000878790447104c00000000021a90740001a998b000e72a27482a060c17700017d40000000f418c000033c000000000032300000000004c048317742563c922f0ff80ac0823670ca007a2a44020b051de6ac082000083645c00000003d88d100019040e816a0be03ed1dc0003e80f280008b418da03480c000000033c0001882f50b383bc8442f19e5c3b24213901fc845e5b54850008ed651723296fc0000000000dc45080000000000a040000002108fa627c00014b528000000003d00000001a486640000d115f242c000000350800061253c138a0c490288b0000ac0ae44054989b080a24d50a0830800000037580008c800022d98d11505a000000000005982300bdc000920226061800013f0719b1022a6f912787283586cc2d99a9501e000000143846006420895b077a2b71788000e1093400013b0000000000218cc0c09d27a85d80000000000e70ef80f0
  | 13 => 0x400000000000004aa2104000000000141800000000000002ea22600000000000000001ba840e000471a0e034c000000000000000000000000009020000000a9800013a9bd800000018900000009252b301980004bb2e780000000001508ff00004903e69308af85733ac00cd18a00032e80008760002b01fa41ee0002879bc400033e25589ec1fa80b00a193cf348bb4400e8d14c000052880cae04e7035000000000029a83a40001e507311c800019d000000000050500016110ea0001e88000a2227a09480000000000000a55000180452800000000000002c400000004e00012928ac15680008e600000005e44a62fa25b85d04988d043790f925a6d71cb12301dc923000215000089a3401a08af63a1000000000075700000000000002838000bf00000ea8000f6c000000000017a4203f6140c6165c328a0e4c7901681669ca43248dc0001b34ade00000000000000000000000e2c6f040100000000002a210d0f4c8f71a580144fe0002ab8114262272000220d124000000253c3e04b20b19f08b3a03200009500740003bf87092421484a401c80004680000000000000000000000000040b0000000000000000000000000018e41e60cb44ca0c000000000000010a20a4000000109092b188069520200000015900000000d400003905e600016a00008b30d893b870678219d9d18974687426019c00000031f10500000001949e6c26a73110980005fc1d4000000000006e0000ae800000000004f847c0000000000a8a3f03e092100000000001b2c0006ab000000026650c3e4000052200039a23e4fa2000000000000000000000000000280000000e1892a3dd0e08ffc48b00000000000003dc80c00008a440aa1f4f2600043312803c01b7459010c70e16200c204cf8801534185c912840a4139a04c923e81c9078404a3f61840000000000000000000005a39e0000b624993848f046f44e10000bac3221670df9748bee5341281bdcb488691b2847047a000032800117e432476800112e7ed0000000c560df000000000000000000009c87b50d48000c9800014a0000cbc7590000000dda00012107a8e5023c310047d28e00000006f50ee3b833d01a4ef01b5000070400088431b00008ec621000110000000000000000004571481acc72000021c000000000000000000000000001c7000000000000000000000001cb82b45d11e9912800000000013b400000019085800000c41a30000d864922ee069cfea66242c14200a86a7015a0f108c1493d50530b328b13d488305660c341416407e65ab1170bcc38800000000003180100d700005a00000578b1c6903b61ad8d3812a88d000135000069c345108cd542a63cc14100005b8200164cf0a0003010000000336000000073a1142929df8cfc00033c8b780004753bb000104232a228971
  | 14 => 0xc800006208d0000ee6000305000000055d37098fc00006f0001274c501d300000000007171dd9fd06006551148aa8a443c33a7a38493c15033b00000000003f5968c0005013b880000000994a90000dca27700012447520a10001db850402c39280011c033a145005865a00013789246400001f30000b7815926d1bb000093b44991a8d3228f3360000c208823b3800123e90c1cda3a000000037d1b140000dd38a80006d8000064800000000000002e10ec00000017f4fb60003d61ec40007473d5a21499000000005f8b1a1580000000ac21712ec20a80000000a700000002ff46b92b50a063b0000ce05f86581fc1d4800078d00010fc0000e808098c905c4fb3518028c4e62e0e19e845784d22c290307ba1ef3990000a42000069800083030736aa30c11e0000000000ce076608911f10f4000386825c0002680001cace4600000010245126e6000193904c25a1df142923207f06388900f80003939458db815d0a51e012746852779b2056a777046000018240f0001cf409000046f800000000000000000000000000a04c9a00026b8000000000000000000020a22e8c14e3684330f9ea000000011624c03da00000000005620000000b64dc024327124f83a44fe2fa04b91841df10a88dc0004292ad1c502440000000000ede00014e89ac00054b0829344b4c11d025935828057f0001b90a7400047380000000000000000d822b42d8045876a3980c800012381113ffa40c00010314b05440008be0e71a98f1e000000237400000041009580d62f02f680000005303e79ec119a51d34a18c47144b32d49d904368f33d399a81242441c41b4c48a30422b226000000000000000000002c880008be2923c7007c0000000001f680000001ec818528c00c4790cd43744c748915b4e8061d11118989e435d3a98cdc74057e32c9f643ae000352040103c7d800000000005ff0d58390000000000236d0763340000f704ae00014e1f94f4a57d33a8870e948ca3f20864b06722473093854a3e130997ccf9c0cc000088400000000005f4000000000000002e3ff32881186ac8bc000254c0004db00023940000000000b2cd8e71836d82a4a8603c0000000a240000000000a760000000000b4a00000000000000000000678eb60d8000000000000033080004fa0003af0000000000000091c0002f50000c686dc0030000000ae80001aa00012ac87106a92f076259427fa4b80d05190d0889cb5a00024d884849a4c60eb186c9a00004511cec16818f1a88ac80003d200000000ee00007f930d01860816009b489e10f29000006260000e324a45c09053f7a33ce2691d000048400064815382dcf061e422993e025a6883fc0f5809c3c73ad0a20cd27033b18920a167f932f8000b44200000000029659a4539cdc2d28e401d8100be2084023a21c00004
  | 15 => 0x571a28000000000000000000000030d21ac1589551af80011d22fd1c6211c00000000224409605e70000000000340000000119803813b1398f640002e6962897a34d3068d1c9049380de055000c0000940e18cca000000000000017008824d81f00000a380000000001380abc00055e4a2000000000000000000007072429ff005e0000000000338000000129c98800000002e8d2c0002a41e4400037f0ee840904886400018380000004938380f163ab07f00012107e618b02c8fce000000000099800000000010584f020388949fa02141118e10ce1b317399d07a07d230a90c0d9e10b48b8034a5e30d32106ecc1669335a80000001cc000175c3fe2ed0fd92244d492400023fcf2a00039800009140000000001188000387a1a0ace43326c1670e0c91b2578000000000000000027a00000000011fc16f2958000b9c0860000000bc20751aa80000000493a091ec1da6922f49eec0000be000066089a498000202425e57130a000114253d000000024655400000005e42513048000000000083000000015f3ae80005f26523f19c281ec7e223f9c107b44703a5800119c42b35697d8de857847b12b90248d91be9380f463cf28f953876095825a15087a804103f12e4d7c7c92cd8b18f7e00011999aceca00000006a80007190000b5c23600005183d421c2870a1a1580003992140d3c1d684543080000005ac00000000006e809b066c0000000ca13cc1540700000000ab80000000000d7000000000000000000000000b7a0002eb0b8c0000591660000000000000000085a41f09c1e3000000001480000000000001148b4e4bf0000f187e200010f00000003df1ba800095817b00008d04721b90001a2c3ee7862d50fb400020e07d00009b88d300011e81ce5db00000011ea000000000000000001880446940003a2163c3600b52899e746f000041b959400063d00000d05ba29a3de8c7800055b3088000db20a2221232414e01d000000006e5df475114115600013f000032e56242d9fb8b6e000000000000000015000000000001fd8000a1292f00000008e27b31fa15d400000031b9a600001e300000000000000000b540006504a2800084e88600000009281b6106800000000000020d40000000000000e5e01c1812358000538000062c40a1a327c8498ab2173448856cb1c3c511c0f38cee6d647e80006f609a03d9e8053c4ea3ba0fa52860004a592e07f265b3aa80005d40001b68cc404c62a00010d80008ec3a616e900e22a00000003a02ee000064c28a00029600002c200900000000000000000001228000000000000090000001b000050d00022406c80001b90314000595026111ce347ca10120cc2dc0242b40ebc0349130f91f00000000000172800000026f956000000000000000000000001c14000000000082400000000017
  | 16 => 0x7ca7e0478099c0000001ca0ef044046f169000084a8e23470d408547be00000002a436348c00009e80b00000000dde7b80e580000001fa2058000f6e00000013c400000019714c40001fe1d3152800000031280000000002719c2c7883de12321e00007d50000000000241000000109e7d408f1328000000000181cf240001a1000111e8052c400006986971e5816c0004930000000000000000170000056a39080000000000000b14ccc8c840d9c0842e41d33f887cb965d347d8dac0000000000000c660000ee00000000000000000882000000000006c8d8000053c000439000000000000000000011f40002e40000000000000000028481f0000eb51707a20e8800037044b000079c18046e23b824017200000000000000001c200000002ca0000000a80000000216800000000000007740001ec17b0b240000001468dbc8bd30080000006f233695a4c243b3312133c0004aa04c14f8bf61f617a1d140f00000788000cfa3763be84340ba327000082d0e071f37e14547720e231d21f125029b3eb8000c5a3953fb8dbc5f64f60c68da813c00e30c1078b8e93709b8eb05865fe0000b44fac95a212107113e0003b90a001ae0002270000b0e4872d9000034400000000a80000003890fac00000009c85b000000000017c0000466222800000000026c80000000000000000e7c46c00009e40001db0002498c08000000020c0000000000000000832000000102e4584051ac89340002bd05b509c3bf1f1123c94600110e96f91bc0001d51bfc11a4ce1b1199ca5054712a918833e6af4ac83591aa556000000107a05f31aa27864c74d00009d021800045181cc592000000000009e00000000000006d216c1e7c428000260a1b4570117000125c00000020910e800000015f800019c87400002cc83465a1f19d5089200004583f00006401d9020400072d0000aa000072400007984f0401000000000000000000000002f800010f40000003f505709d6664000000039e00014b800000090e068129800012736e84e846200018f80004340003ee8000000000000000102038100000001bc00000000000000002a8000041095c1cf00011020001b095e400000000000000003910001b88e3c07d049833505a0001b48994e84563351010915261c0f10de4d087e8478a0740400000001b60ed86d039aa14c9ba03930b191c0000002b721b8a825000098000302000000000000074808c1534da80001c722c000079441280000000000000000e6c00043f9c40000000000000000000000009b80000000001be04b83d700018140000000001054000285000099923c1240001b180005de000154c3e640e1c79a4499a2a300000000000003ae244405a7000001bb8c465eb330000064a6bf000000000000011b179000000000007140007510000d640006
  | 17 => 0x87e000000000059f0000000000000000000000000000022e91e800000017080000000000c7400016b00000007b66a800016086c056b000000067a7cc44ea2a8f782110d0000000083e3960000000000000000000000000017a0000000000061d20800005680000ae00000009b00000000000d980007841201a2457641600007603922a902e2538952000000100900600000002441780004849d7c0000000000c5c0000000000384000000000000005c78739f8000d180000001b68000788368800000000000000005b800045680011a8000000000000089c11a892c00034405d8000f966c0036962400018a0c28c2800060c0001e7800017a00006911f04b53018000000023000000000000027b800000000013980000005e23e18d600003cd0fa800064400002a80001943a8000217c16c806000000000002700000011a418437f14b81de2e1483800101c0003bd8000a6c00000000000001c04a8000000003f000000038e82b0fe9200aaa8af1ba0d5d17279c000039400009b1a199f04942e600014e435a18e32206c80000000000f0040c0001f91aecc9400000c9b9d29402200007c417e15e0000bb000000000000000003e00001eb8d1e3ee4a088c847e1f90000000f5a6733b82188d0c4460001e0462a5f939c2530000000000176800000000000000006a92a49294c4400000000007440ec0000edc00035c2170f3000084924680005c8157000018c68220406d800010e32f0000000ec27430000a60b686ca050000095091618a000000007a0001d80b0c00000000000000003c49d240000002ea800078400016f800032c811000000122a00000000001565274aba0040000000bc000000000000000004c61cd000000031246300011680007502990000cac00009d93a0fe06b10090b58d1a5b91f78e5c2a600000011e42aa14d35a0e94a3c00004a0000254829000157c6387fb44d99ec6320003bc860c7d490f187000000000041194fc71228624e132caa488841f8a4cbdc00000017100006170000000000000000000127200047e23040bc261084a164fbc0713a7027cbca6541fa80012b62ac13200000008522cb8000e2243536f800000040335c82b80006f52ec975003c10a1eaa0bc00000035816845a60001cf9098906000000183c00000035d09880006903b68258000408000000051c000000000000000027e000000012500000000008c700016ec00059e00019bc8f037000018f00004a123e82200000003218000a4c00000009a428c8084600dcc59000012e8000000000258a1e400000048d1d880007330000000aee5fc0f5a1940ec7af16a1ab8d923332e6000097c2280000000000000000065400093d42f01810aa7c700013e8036000000000000083407c800000095116d8ba4fc262f0da10c40001ee00580000000000000
  | 18 => 0x91084019603c843000000009480003300001a7cfec000000000103800038e9c04d7a00000011a455c2e522c80000008142178d6870a2b645000012846463e2904000000009e0000808
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7508c51017775508c510177f2308c510177f2208c510014ff764c51000cfe764c51015cfd764c51000cfc764c510006df634c510016dc634c51002fd4314c510005fb704c51000df8704c51002ff0104c51000df4764c510016f4764c51000cf4764c510006f7654c510006f5654c510005f7744c510005f5744c51002df7734c51002fd7734c510007d7634c510016f6634c510016f4634c510037d4634c510005f7724c510037d7324c510007d5324c510007f3704c51000df6704c51000df4704c51015ff0704c51002ef7604c51002ff3604c51015f77504c51015f75504c51015fd7304c51015ff2304c51015fd5304c51015ff2204c51000cfe76c851000cfc76c8510006ef62c851004eec62c851000dfa70c8510005f970c85100ddf6768851002ef6768851002df77488510005f57488510006f76488510006f5648851002df77388510005f573885100fdf5728851004ef6628851004ef4628851002ff3708851000df6708851000df4708851002ff0708851002ef7608851002ff3608851011f77508851011f75508851011ff2308851011ff2208851004cff764851000cfe76485100fcfd764851000cfc7648510006ef624851004eec624851002fe42148510005fb704851000df8704851002ff0104851000df4764851004ef4764851000cf47648510005f77448510005f57448510006f76448510006f56448510005f77348510005f5734851002df7724851002fe77248510007e7624851004ef6624851004ef46248510007e46248510007e63248510007e53248510007f3704851000df6704851000df470485100fff0704851002ef7604851002ff360485100ff7750485100ff7550485100fff230485100ffe720485100fff220485100ffe5204851002df8764c110016f8764c11002cf8764c110006fb654c110006f9654c11000dfb734c11000fdb734c110007db634c110016fa634c110016f8634c110037d8634c110037da434c110007d9434c110005fb724c110037db324c110007d9324c110007f3714c11002dfa714c11002df8714c110007f0714c11000efb614c11000ff3614c110007f2414c110007f1414c110037db314c110037f2314c110007d9314c110037f1314c110007d1314c110007f2214c110007f1214c11002df8764811004ef8764811002cf87648110006fb6448110006f96448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811004efa624811004ef86248110007e86248110007ea4248110007e94248110007ea3248110007e93248110007f3714811002dfa714811002df87148110007f0714811000efb614811000ff36148110007f24148110007f14148110007f23148110007f13148110007eb2148110007f22148110007e92148110007f12148110007e12148110
  | 1 => 0x891001cfc7458910004ff7358910014fe7358910014fc7358910006ef725891013cff7158910006f771589100fcff7058910006fb70589100fe7f50589100fe7d505891011cfe76189100457e75189100057d751891003dbe7418910005bd7418910035de7318910005dd731891004eee6218910006ed621891004cff7694910004fe7694910004fd769491004cfc7694910035de7394910005dd7394910006ef629491004eec629491002df67194910005f5719491000dfa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc76549100267e65549100067d6554910006ef625491004eec625491004cff7690910004fe7690910004fd769091004cfc769091002df67190910005f5719091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc765091001ebe6450910006bd645091004cff768c910004fe768c910004fd768c91004cfc768c9100457e758c9100057d758c91004eee628c910006ed628c91002df6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c910016de634c910006dd634c91004eee624c910006ed624c91000dfa704c910024ff765451000cfe76545101bcfd765451000cfc76545100067f65545100267c6554510005fb705451000df8705451002ff010545102bdf6769051002ef6769051002f76759051002f757590510006f76590510006f5659051018df5749051001ef6649051001ef46490510005f573905101aef663905101aef46390510005f57290510006f76290510006f5629051000df6709051000df4709051002ef7609051002ff360905101a77750905101a77550905101a7f230905101a7f2209051001cff765051000cfe765051018cfd765051000cfc7650510006bf645051001ebc645051002fb44150510005fb705051000df8705051000df4765051001ef4765051000cf47650510006f76550510006f5655051002df7745051002fb77450510007b7645051001ef6645051001ef4645051003fb464505102b7b7545051003fb45450510005f77350510196f66350510196f4635051003fb74350510007b54350510005f77250510006f76250510006f5625051003fb74250510007b54250510007f3705051000df6705051000df4705051018ff0705051000df0705051002ef7605051002ff3605051018f77505051018f75505051018fb7405051018fb5405051018ff2305051018ff220505102adf6768c51002ef6768c510006f7658c510006f5658c51002df7748c510005f5748c51015df5738c510016f6638c510016f4638c510037d6438c510007d5438c510005f5728c51002ff3708c51000df6708c51000df4708c51002ff0708c51002ef7608c51002ff3608c5101777
  | 2 => 0x467c5459510004ff7359510006df7359510004df7359510014fe7359510014fc7359510006dc7359510014dc73595100467f5359510004ff725951004cfc72595100467f52595102dcff7159510006f771595102d67e51595102d67c51595101bcff7059510006fb70595101be7f50595101be7d50595101befa305951001cfe76d91100457e75d91100057d75d911003ebe64d9110024fe75d91100067e75d91100247e75d9110004fd75d91100067d75d91100047d75d9110024fc75d9110014fe73d9110004fd73d9110014fc73d911004cfe72d9110004fd72d911002cfe71d911000cfd71d911002cfc71d911003ebf41d911002cff70d911000cfe70d911002cfd70d911000cfc70d91101a67f50d91101a67d50d91101a6bf40d91101a6bd40d91101a6fa20d911003ebc6459110005ef7259110005ec72591102cdf77159110004ff7559110024fe7559110024fc75591101a4ff7459110006bf7459110004ff7359110014fe7359110014fc735911003ebf4359110004ff7259110006ef7259110004ef725911004cfc7259110006ec725911004cec725911003ebf42591102ccff7159110006f7715911018cff7059110006fb705911018e7f505911018e7d505911018efa2059110004ff7655110004fe7655110004fd7655110004fc7655110014fe76d8d10036de63d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df53d8d10036dc53d8d10036de43d8d1004cfe72d8d10004fd72d8d1002cfe71d8d1000cfd71d8d1002cfc71d8d10036df31d8d1002cff70d8d1000cfe70d8d1002cfd70d8d1000cfc70d8d101767f50d8d101767d50d8d10176df30d8d10176dd30d8d10036dc6358d102c5f77158d10004ff7558d10024fe7558d10024fc7558d10004ff7458d1001cfe7458d1001cfc7458d10174ff7358d10006df7358d10004ff7258d1004cfc7258d10036df3258d102c4ff7158d10006f77158d1015cff7058d10006fb7058d1015e7f5058d1015e7d5058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100267e6554d100067d6554d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100457c7550d1001ebe6450d10006bd6450d10006df6350d10016dc6350d1004cfe76d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910014fe73d8910004fd73d8910014fc73d8910006ef42d8910006ec42d891002cfe71d891002cfc71d891002cff70d891000cfe70d891002cfd70d891000cfc70d891011e7f50d891011e7d50d891011eef20d891011eed20d8910006ef62989100fdf5719891013df77158910004ff7558910024fe7558910024fc7558910004ff745891001cfe745
  | 3 => 0xc6350f1002df67150f102ffd63150f10004ff7558b10024fe7558b10024fc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10014fe7358b10014fc7358b1002eef7258b1002cff7158b1000cfe7158b1002cfd7158b1000cfc7158b1002ef64158b1002eee2158b1002eec2158b100fe7f5058b100fe7d5058b100feef2058b100feed2058b1002efa1058b1002ef91058b1004cff7694b1002cfe7694b10004fd7694b1002cfc7694b10055de7394b10005dd7394b1002df67194b10005f57194b10004ff7654b1002cfe7654b10004fd7654b1002cfc7654b100267e6554b100067d6554b1004cff7690b1002cfe7690b10004fd7690b1002cfc7690b1002df67190b10005f57190b10004ff7650b1002cfe7650b10004fd7650b1002cfc7650b1001ebe6450b10006bd6450b1002df67150b1004cff768cb1002cfe768cb10004fd768cb1002cfc768cb100657e758cb100057d758cb1004eee628cb10006ed628cb1002df6718cb10005f5718cb10004ff764cb1002cfe764cb10004fd764cb1002cfc764cb10016de634cb10006dd634cb1004eee624cb10006ed624cb1002df6714cb1002df776507102f6f7765071002ef76550710006f5655071002fb7745071002fb7645071001ef6645071002ef4645071002fb464507102efb7545071005fb45450710005f77350710196f6635071002ef4635071005fb74350710007b54350710005f7725071002ef76250710006f5625071005fb74250710007b5425071000df6705071000df4705071018f77505071018f75505071018fb7405071018fb5405071002df7764c7102e6f7764c71002ef7654c710006f5654c710005f7744c710005f5744c71002fd7734c71002fd7634c710016f6634c71002ef4634c71002fd4634c710005f7724c710057d7324c710007d5324c71000df6704c71000df4704c71015f77504c71015f75504c71015fd7304c71015fd5304c71002df77648710006f77648710005f77448710005f5744871002ef76448710006f56448710005f77348710005f5734871002fe7724871002fe7624871004ef6624871002ef4624871002fe46248710007e63248710007e5324871000df6704871000df470487100ff7750487100ff7550487100ffe720487100ffe52048710024fe76d95100467e65d951001cfe74d9510004fd74d951001cfc74d9510014fe73d9510004fd73d9510014fc73d951004cfe72d9510004fd72d951002cfe71d951000cfd71d951002cfc71d95100467f51d951002cff70d951000cfe70d951002cfd70d951000cfc70d95101d67f50d95101d67d50d95101d6fa30d95100467c6559510005df7359510035dc73595102ddf771595101d4ff75595100067f7559510004ff745951001cfe745951001cfc74595100067e5459510
  | 4 => 0x852002eec61c852004feb70c852000dee70c852000dec70c852004fe870c852004eef60c852004feb60c852013f6f50c852013f6d50c852013fea40c852013fea10c852000cfe76885200fded7288520006f7618852002ef4618852000dfa7088520005f9708852000cfc7648520006f7614852002ef4614852004fe42148520005fb704852000df8704852004fe8204852000dec764852002eec764852000cec7648520005ef7448520005ed7448520005ef7348520005ed7348520006ef6348520006ed634852004def714852004fe77148520007e7614852002eee614852002eec6148520007e46148520007e64148520007e54148520007eb704852000dee704852000dec70485200ffe8704852004eef604852004feb60485200ff6f50485200ff6d50485200ffea40485200ffea104852004df8765012001ef8765012004cf87650120006fb6550120006f9655012000dfb745012000fbb7450120007bb645012001efa645012001ef86450120077b86450120077bb4350120007b94350120007eb725012004dfa725012004df87250120007e8725012000efb625012000feb6250120077bb4250120077ea4250120007b94250120077e94250120007a94250120007ea3250120007e93250120005fb7150120077bb4150120007b94150120007eb2150120007e9215012002e7f7559710004ff745971001cfe745971001cfc74597100067e54597100667c5459710004ff7359710014fe7359710014fc73597100667f5359710004ff725971004cfc72597100667f525971002cff715971000cfe715971002cfd715971000cfc715971002e7e515971002e7c515971002ef6415971002ef631597101be7f50597101be7d5059710004ff7559310024fe7559310024fc755931002ebf7459310006bf545931005ebc5459310004ff7359310014fe7359310014fc735931005ebf4359310004ff725931004cfc725931005ebf425931002cff715931000cfe715931002cfd715931000cfc715931002ebe415931002ebc415931002ef6215931018e7f505931018e7d505931018ebf405931018ebd4059310004ff765531002cfe7655310004fd765531002cfc7655310004ff7558f10024fe7558f10024fc7558f10004ff7458f1001cfe7458f1001cfc7458f1002edf7358f10004ff7258f1004cfc7258f10056df3258f1002cff7158f1000cfe7158f1002cfd7158f1000cfc7158f1002ede3158f1002edc3158f1015e7f5058f1015e7d5058f1015edf3058f1015edd3058f1002efa1058f1002ef91058f10004ff7654f1002cfe7654f10004fd7654f1002cfc7654f100267e6554f100067d6554f10004ff7650f1002cfe7650f10004fd7650f1002cfc7650f100057f7550f100657c7550f1001ebe6450f10006bd6450f102fedf6350f10016d
  | 5 => 0x4faf7450920007af645092001eee645092001eec6450920077ac6450920005ef7350920005ef7150920077af4150920007eb705092000dee705092000dec705092021fe8705092004eef605092004feb605092021f6f505092021f6d505092021faf405092021fea405092021fad405092021fea105092030dee768c92004eee768c92004f6e758c92004f6d758c920006ef658c920006ed658c92004def748c920005ed748c92020eee648c92020eec648c9201eded738c920016ee638c920016ec638c920005ed718c92000dee708c92000dec708c92004eef608c92004feb608c9202076f508c9202076d508c920207ea408c920207ea108c920014ff764c92000cfe764c9201ecfd764c92000cfc764c920006df634c920016dc634c92004fcc324c920005fb704c92000df8704c92000dec764c920016ec764c92000cec764c920006ef654c920006ed654c920005ef744c920005ed744c9201f6ee644c9201f6ec644c92004def734c92004fcf734c920007cf634c920016ee634c920016ec634c92006fcc634c920307cf534c92006fcc534c92006fce434c920007cd434c920005ef714c92006fcf314c920007eb704c92000dee704c92000dec704c9201efe8704c92000de8704c92004eef604c92004feb604c9201ef6f504c9201ef6d504c9201efea404c9201efcf304c9201efcd304c9201efea104c92002cfe76d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520014fe73d8520004fd73d8520014fc73d8520006ee32d8520006ed32d8520006f731d8520006f431d852000cfe70d852004cfd70d852000cfc70d852013e7f50d852013e7d50d852013ef710d8520006f7619852007d7e75185200057d7518520075be7418520005bd741852006dde7318520005dd731852002ef66118520006f56118520004fe7694520004fd769452002cfc7694520075be7494520005bd749452004dee7294520005ed7294520006f7619452002ef4619452000dfa7094520005f97094520004ff7654520004fe7654520004fc76545200267e65545200067d6554520006f7615452002ef46154520004fe7690520004fd769052002cfc769052007d7e75905200057d759052004dee7290520005ed729052002ef6619052000dfa7090520005f97090520004ff7650520004fe7650520004fc765052001ebe6450520006bd6450520007ad425052000dfa7050520004fe768c520004fd768c52002cfc768c52004dee728c520005ed728c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520016de634c520006dd634c520007cd324c5200ddee76c852004eee76c852004def74c8520005ed74c852004def73c8520005ed73c8520006ef63c8520006ed63c852002eee61c
  | 6 => 0xc5259520004ff715952002cfc715952007e7f515952024cff7059520006fb705952024e7f505952024e7d505952024efa405952001cfe76d9120076be64d9120024fe75d9120004fd75d9120024fc75d9120006bf54d9120076bc54d9120014fe73d9120004fd73d9120014fc73d9120076bf43d912004cfe72d912000cfd72d912004cfc72d9120076bf42d912002cfe71d9120004fd71d912004cff70d912004cfd70d91202367f50d91202367d50d9120236bf40d9120236bd40d9120076bc6459120325ef7259120004ff7559120024fe7559120024fc7559120234ff7459120006bf7459120004ff7359120014fe7359120014fc7359120324ff7259120006ef7259120004ff715912002cfc7159120076bf415912021cff7059120006fb705912021e7f505912021e7d5059120004ff7655120004fe7655120004fd7655120004fc76551200267e65551200067d6555120014fe76d8d2007d7e75d8d200057d75d8d2006ede63d8d20024fe75d8d200067e75d8d200247e75d8d20004fd75d8d200067d75d8d200047d75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d2004cfe72d8d2000cfd72d8d2004cfc72d8d2006edf32d8d2002cfe71d8d20004fd71d8d2004cff70d8d2004cfd70d8d202067f50d8d202067d50d8d20206df30d8d20206dd30d8d20206fa10d8d2006edc6358d2031def7258d20005f77158d20005f47158d20004ff7558d20024fe7558d20024fc7558d20004ff7458d2001cfe7458d2001cfc7458d20204ff7358d20006df7358d2006ede4358d2031cff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2002cfc7158d20006f47158d2002cf47158d2006edf3158d201ecff7058d20006fb7058d201ee7f5058d201ee7d5058d201eefa1058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d2007d7c7550d20006bf6450d2001ebc6450d20016de6350d20006dd6350d20024ff765492000cfe765492024cfd765492000cfc76549200067f65549200267c6554920005fb705492000df8705492004fe82054920315ee769092004eee7690920006ef6590920006ed659092021ded749092001eee649092001eec6490920005ed7390920077af4390920007ad4390920005ed719092004feb709092000dee709092000dec709092004fe8709092004eef609092004feb60909202376f50909202376d5090920237ea4090920237ea109092001cff765092000cfe765092021cfd765092000cfc7650920006bf645092001ebc645092004fac4250920005fb705092000df8705092004fe8205092000dec765092001eec765092000cec7650920006ef6550920006ed655092004def7450920
  | 7 => 0xf2001ebc6450f20016de6350f20006dd6350f2004dee7250f20357ae4250f2004def7650b2034eef7650b2004eef6550b20006ed6550b2004faf7450b2004faf6450b2001eee6450b2004eec6450b2004fac6450b20005ef7350b20005ef7150b2008faf4150b2000dee7050b2000dec7050b2021f6f5050b2021f6d5050b2021faf4050b2021fad4050b2004def764cb20346ef764cb2004eef654cb20006ed654cb20005ef744cb20005ed744cb201f6ee644cb2004eec644cb2004fcf734cb2004fcf634cb20016ee634cb2004eec634cb2004fcc634cb2033fcf534cb20087cc534cb20087ce434cb20007cd434cb20005ef714cb20087cf314cb2000dee704cb2000dec704cb201ef6f504cb201ef6d504cb201efcf304cb201efcd304cb20004ff7558720024fe7558720024fc7558720004ff745872001cfe745872001cfc7458720004ff7358720014fe7358720014fc735872000cfc725872004eee3258720006ed325872004ef7715872004ef7215872004ef421587200fe7f50587200fe7d505872004efa205872004ef920587200fef7105872002cff769472004cfe7694720004fd769472008dbe7494720005bd749472004dee7294720005ed7294720004ff7654720004fd765472004cfc76547200267e65547200067d655472002cff769072004cfe7690720004fd76907200957e75907200057d759072004dee7290720005ed729072002ef66190720006f56190720004ff7650720004fd765072004cfc765072001ebe6450720006bd645072004dee7250720007ad425072002ef66150720006f5615072002cff768c72004cfe768c720004fd768c72004dee728c720005ed728c720004ff764c720004fd764c72004cfc764c720016de634c720006dd634c72004dee724c720007cd324c72004def7648720006ef7648720005ef7448720005ed7448720005ef7348720005ed734872004eef6348720006ed634872004fe7714872004fe7614872002eee614872002eec614872004fe46148720007e64148720007e5414872000dee704872000dec70487200ff6f50487200ff6d5048720024fe76d952007e7e65d952001cfe74d9520004fd74d952001cfc74d9520014fe73d9520004fd73d9520014fc73d952004cfe72d952000cfd72d952004cfc72d952007e7f52d952002cfe71d9520004fd71d952004cff70d952004cfd70d95202667f50d95202667d50d9520266fa40d952007e7c6559520005bf7459520075bc7459520335ef7259520264ff75595200067f7559520004ff7459520006bf7459520004bf745952001cfe745952001cfc7459520006bc745952001cbc745952007e7f5459520004ff7359520014fe7359520014fc73595200067e535952007e7c5359520334ff7259520006ef725952032e7e525952032e7
  | 8 => 0xbf7853541300bfda4354130007d943541300a77b52541300077a52541300077952541300a77852541300bfdb3254130007d93254130005fb71541300a77b51541300077a51541300077951541300a77851541300bfdb3154130007d931541300a77b76541300267b76541300bf7876541300267876541300077b745413035f7a745413000779745413035f7874541300077b64541300067b645413035f7a645413000779645413000679645413035f7864541300bf7b73541300075b73541300bf7a73541300bf7973541300bf7873541300bf58735413000f7b635413000e7b635413000f5b63541300bf7b43541300bf7a43541300bf5a43541300bf7943541300075943541300bf7843541300077b72541300077a72541300077972541300077872541300077b62541300077a625413000779625413000778625413035f7b42541300077a425413000779425413035f7842541300bf7b32541300bf5b32541300bf7a32541300bf7932541300075932541300bf7832541300077b71541300077a71541300077971541300077871541300077b61541300077a615413000779615413000778615413035f7b41541300077a415413000779415413035f7841541300bf7b31541300bf5b31541300bf7a31541300bf7931541300075931541300bf7831541300077b21541300077a215413000779215413000778215413004e7f7559720004ff745972001cfe745972001cfc74597200967f5459720004ff7359720014fe7359720014fc73597200067e53597200967c535972004cff725972000cfe725972004cfd725972000cfc725972004e7e525972004e7c525972004eee425972004eee3259720004ff715972002cfc71597200967f515972024e7f505972024e7d5059720004ff7559320024fe7559320024fc755932004ebf7459320004ff7359320014fe7359320014fc735932004cff725932000cfe725932004cfd725932000cfc725932004ebe425932004ebc4259320004ff715932002cfc715932008ebf415932021e7f505932021e7d505932021ebf405932021ebd405932004efa205932004ef92059320004ff765532004cfe7655320004fd765532004cfc76553200267e65553200067d6555320004ff7558f20024fe7558f20024fc7558f20004ff7458f2001cfe7458f2001cfc7458f2004edf7358f20006df5358f20086dc5358f20086de4358f2004cff7258f2000cfe7258f2004cfd7258f2000cfc7258f2004ede3258f2004edc3258f20004ff7158f2002cfc7158f20086df3158f2004eef2158f201ee7f5058f201ee7d5058f201eedf3058f201eedd3058f20004ff7654f2004cfe7654f20004fd7654f2004cfc7654f20004ff7650f2004cfe7650f20004fd7650f2004cfc7650f200057f7550f200957c7550f20356bf645
  | 9 => 0xf724c930017cf724c930007cf624c93004ede624c93004edc624c930007cc624c930007ce524c930007cd524c93036fcf424c93036fcc424c930005df714c930007db704c93000dde704c93000ddc704c9301efd8704c930016df604c930017db604c9301ef5f504c9301efda504c9301ef5d504c9301efda104c93002cfe76d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853000cfd73d853004cfe72d8530004fd72d8530366df32d8530006dd32d8530366f631d8530366f531d8530014fd70d85302c67f50d85302c67d50d85302c6f710d8530006f76198530035f97098530055fb70585300a57e75185300057d751853009dbe7418530005bd7418530005ee7218530005ed721853002ef66118530006f56118530004fe7694530004fd769453002cfc769453009dbe7494530005bd7494530015de7394530005dd739453000dfa7094530005f97094530004ff7654530004fe7654530004fc76545300267e65545300067d655453000dfa7054530004fe7690530004fd769053002cfc76905300a57e75905300057d7590530015de7390530005dd7390530006f7619053002ef461905301afd7319053000dfa7090530005f97090530004ff7650530004fe7650530004fc765053001ebe6450530006bd6450530015de73505300079d4350530006f7615053002ef46150530197d7315053000ddc764c53002edc764c53000cdc764c530005df744c530005dd744c530005df724c530006df624c530015df714c530017d7714c530007d7614c53002ede614c53002edc614c530007d4614c530007d6514c530007d5514c530007db704c53000dde704c53000ddc704c53015fd8704c530016df604c530017db604c53015f5f504c53015fda504c53015f5d504c53015fda104c530004fe76c8530004fd76c853004cfc76c8530015de73c8530005dd73c853004eee62c8530007cd32c8530006f761c853002ef461c8530004fe7688530004fd768853002cfc7688530015de7388530005dd738853000dfa7088530005f97088530004ff7648530004fe7648530004fc7648530015de7348530005dd7348530007cd3248530004fe7608530004fd760853002cfc76085300a57e75085300057d750853009dbe7408530005bd7408530015de7308530005dd7308530006f7610853002ef4610853000dfa7008530005f97008530015f87654130026f87654130014f8765413000dfb755413000f7b75541300077b6554130026fa6554130026f865541300a7786554130006fb6454130006f964541300a77b545413035f7a54541300077954541300a7785454130007db7354130015fa7354130015f873541300bfd8735413000efb635413000fdb63541300bf7b53541300bf7a53541300bf795354130
  | 10 => 0x95303a67d50d9530024ff76595300a67c655953039ddf73595300cdfb70595303a4ff75595300067f7559530004ff745953001cfe745953001cfc745953039cff7359530006df73595300be7e53595300be7c53595300bede4359530004ff725953004cfc7259530004ff715953002cfc71595300a67f515953028cff7059530006fb705953028e7f505953028e7d505953001cfe76d913009ebe64d9130024fe75d9130004fd75d9130024fc75d913027cfd74d913000cff73d9130014fe73d913000cfd73d9130014fc73d9130396bf43d9130396bd43d913004cfe72d9130004fd72d9130396df32d913002cfe71d9130004fd71d9130014ff70d9130014fd70d91303867f50d9130386fa50d91303867d50d9130386bf40d9130386bd40d913001cff76591300057f75591300a57c755913009ebc645913037ddf735913038dfb7059130004ff75591300067f75591300047f7559130024fe7559130024fc75591300067c75591300247c7559130384ff7459130006bf745913037cff7359130006df7359130004ff725913004cfc72591300aedf3259130004ff715913002cfc715913009ebf415913027cff7059130006fb705913027e7f505913027efa505913027e7d5059130004ff7655130004fe7655130004fd7655130004fc765513000ddc7650d3001edc7650d3000cdc7650d300075f7550d300075c7550d30006df6550d30006dd6550d30015df7450d300179f7450d300079f6450d3001ede6450d3001edc6450d3009f9c6450d3009f9e5450d300079d5450d30005df7250d3009f9c4250d30005df7150d302fedc6150d3009f9f4150d30007db7050d3000dde7050d3000ddc7050d3027fd87050d30016df6050d30017db6050d3027f5f5050d3027fda5050d3027f5d5050d3027f9f4050d3027f9d4050d3027fda1050d3004cfe76d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893000cfd73d8930376de43d8930006dd43d8930376ee32d8930376ed32d893002cfe71d8930004fd71d8930376df31d8930014fd70d893031e7f50d893031e7d50d893031eef20d893031efa10d89300a57e75989300057d7598930006ef629893006df97098930005f77158930005f47158930085fb705893004eee6218930006ed6218930004fe7694930004fd769493004cfc7694930015de7394930005dd7394930004ff7654930004fe7654930004fc76549300067f65549300267c6554930004fe7690930004fd769093004cfc7690930015de7390930005dd73909300079d4390930004ff7650930004fe7650930004fc7650930015de735093000ddc764c93004edc764c93000cdc764c9301fede654c9301fedc654c930005df744c930005dd744c930006df644c930006dd644c930015d
  | 11 => 0x79d438c540004ff764c540004fe764c540004fc764c54001dbe744c540005bd744c540004fe76c8540004fd76c854004cfc76c854001dbe74c8540005bd74c854000dfa70c8540005f970c8540004fe7688540004fd768854002cfc768854001dbe7488540005bd7488540006ef628854004eec628854002ef66188540007b54188540004ff7648540004fe7648540004fc764854001dbe7448540005bd7448540007b54148540004fe7608540004fd760854002cfc76085400b57e75085400057d750854001dbe7408540005bd74085400adde7308540005dd7308540006ef620854004eec620854000dfa7008540005f9700854001df87654140026f8765414001cf8765414000dfb755414000f7b75541400077b6554140026fa6554140026f865541400b7786554140007bb745414001dfa745414001df874541400c7b8745414000efb645414000fbb64541400c77b54541400c77a54541400c77954541400c7785454140006fb63541400b77b53541403b77a53541400077953541400b77853541400c7bb4354140007b94354140005fb72541400b77b52541400077a52541400077952541400b77852541400c7bb4254140007b942541400b77b51541400077a51541400077951541400b77851541400c7bb4154140007b941541400b77b76541400267b76541400c77876541400267876541400c77b74541400073b74541400c77a74541400c77974541400c77874541400c738745414000f7b645414000e7b645414000f3b64541400077b73541403b77a73541400077973541403b77873541400077b63541400067b63541403b77a63541400077963541403b77863541400c77b43541400c73b43541400c77a43541400c77943541400073943541400c77843541400077b72541400077a72541400077972541400077872541400077b62541400077a62541400077962541400077862541400c77b42541400c73b42541400c77a42541400c77942541400073942541400c77842541403b77b32541400077a32541400077932541403b77832541400077b71541400077a71541400077971541400077871541400077b61541400077a61541400077961541400077861541400c77b41541400c73b41541400c77a41541400c77941541400073941541400c77841541403b77b31541400077a31541400077931541403b77831541400077b21541400077a2154140007792154140007782154140024fe76d95300a67e65d953028cfd75d953001cfe74d9530004fd74d953001cfc74d95300067e54d95300a67c54d953000cff73d9530014fe73d953000cfd73d9530014fc73d95303ae7f53d95303ae7d53d95303aede43d953004cfe72d9530004fd72d95300a67f52d953002cfe71d9530004fd71d9530014ff70d9530014fd70d95303a67f50d
  | 12 => 0xc7050d4027fb87050d4001ebf6050d4001fbb6050d4027f3f5050d4027fba5050d4027f3d5050d4027f9f3050d4027fba2050d4004cfe76d8940024fe75d8940004fd75d8940024fc75d894000cfd74d8940014fe73d8940004fd73d8940014fc73d89403ceee42d89403ceed42d894002cfe71d8940004fd71d89403cebf41d894001cfd70d89403267f50d89403267d50d8940326ef20d8940006ef6298940075f9709894008dfb70589400b57e75189400057d75189400adde7318940005dd731894004eee6218940006ed6218940005f67118940005f57118940004fe7694940004fd769494004cfc769494001dbe7494940005bd74949400adde7394940005dd739494000dfa7094940005f97094940004ff7654940004fe7654940004fc76549400267e65549400067d655494000dfa705494000dbc765094004ebc765094000cbc7650940005bf735094001dbf725094001faf7250940007af625094004ebe625094004ebc6250940007ac6250940007ae5250940007ad5250940005bf7150940007bb705094000dbe705094000dbc705094021fb8705094001ebf605094001fbb605094021f3f505094021fba505094021f3d505094021fba2050940004fe768c940004fd768c94004cfc768c9400b57e758c9400057d758c94001dbe748c940005bd748c940006ef628c94004eec628c94020faf428c94000dfa708c940005f9708c940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940016de634c9400079d434c940006ef624c94004eec624c9401f7af424c94002cfe76d8540024fe75d8540004fd75d8540024fc75d854000cfd74d8540014fe73d8540004fd73d8540014fc73d85403c6bf43d8540006bd43d854004cfe72d8540004fd72d85403c6bf42d8540006bd42d85403c6f641d85403c6f541d854001cfd70d85402ce7f50d85402ce7d50d85402cefa20d85402cef710d85400b57e75985400057d7598540006f7619854003df97098540005ef7258540005ec725854005dfb705854002ef66118540006f56118540004fe7694540004fd769454002cfc769454001dbe7494540005bd7494540004ff7654540004fe7654540004fc76545400067f65545400267c655454000dbc765054002ebc765054000cbc765054019ebe655054019ebc6550540005bf7350540006bf6350540005bf7250540006bf625054001dbf715054001fb77150540007b7615054002ebe615054002ebc6150540007b46150540007b65150540007b551505403bfb731505403bfb43150540007bb705054000dbe705054000dbc705054018fb8705054001ebf605054001fbb605054018f3f505054018fba505054018f3d505054018fba2050540004fe768c540004fd768c54002cfc768c54001dbe748c540005bd748c540
  | 13 => 0x85501377b608855011f7a408855011f7a308855011f7710885500057f76485500057e76485500057d76485500057c76485500057f74485500c57e74485500057d74485500c57c74485500057f73485500bd7e73485500057d73485500bd7c73485500076e32485500076d324855000776414855000775414855032f7721485502d76e21485500fd7f70485500077b70485500057b704855000d7e704855000d7c70485500ff78704855000d7870485500fe7f60485501177b60485500ff7a40485500ff7a30485502d57f76085500057e76085502d67e76085500047e76085500057d76085502d67d76085500047d76085502d57c76085502d57f74085500c57e74085502d73e74085500c53e74085500057d74085502d73d74085500053d74085502d57c74085502d57f73085500bd7e73085502d75e73085500bd5e73085500057d73085502d75d73085500055d73085502d57c730855013d7e720855011d7e71085502d76f21085502d77621085502d76d210855032f7521085500dd7f700855000d7e70085500df7a700855000d7a70085500dd7d70085502d779700855000579700855000d7c70085500de7f60085500f77b60085500df7a40085500df7a3008550024fe76d95400b67e65d954029cfd75d954000cff74d954001cfe74d954000cfd74d954001cfc74d95403f67f54d95403f67d54d9540014fe73d9540004fd73d9540014fc73d95400067e53d95400b67c53d95403f6bf43d954004cfe72d9540004fd72d954002cfe71d9540004fd71d95400b67f51d954001cff70d954001cfd70d95403ee7f50d95403ee7d50d9540024ff76595400b67c65595403e5bf74595400d5fb70595403ecff75595400067f75595403e4ff7459540006bf74595400c67e54595400c67c5459540004ff7359540014fe7359540014fc73595400c6bf4359540004ff725954004cfc72595400b67f5259540004ff715954002cfc715954029cff7059540006fb705954029e7f505954029e7d5059540014fe76d8d400aede63d8d40024fe75d8d40004fd75d8d40024fc75d8d4000cfd74d8d40014fc74d8d400aede43d8d403dedd43d8d4004cfe72d8d40004fd72d8d4002cfe71d8d40004fd71d8d403debf41d8d4001cfd70d8d4037e7f50d8d4037efa50d8d4037e7d50d8d4037edf30d8d400057f7558d400b57c7558d400aedc6358d403d5fb7058d40004ff7654d40004fe7654d40004fc7654d4000dbc7650d40016bc7650d4000cbc7650d400073f7550d400073c7550d40006bf6550d40006bd6550d4001dbf7350d4001f9f7350d400079f6350d40016be6350d40016bc6350d400af9c6350d400af9e5350d400079d5350d40005bf7250d40356bc6250d400af9f3250d40005bf7150d400af9c3150d40007bb7050d4000dbe7050d4000db
  | 14 => 0x40f7a301855040f77101855040f7510185502d57f76905500057e76905502d67e76905500047e76905500057d76905502d67d76905500047d76905502d57c769055018d7d74905500bd7e73905500057d73905502d57c739055032d7e72905500057d72905502bd7e71905502d77661905500077561905502d73f41905500c77741905502d77441905504077731905502d77431905501a57f709055000d7e70905501a57d709055000d7c70905501a67f60905501b77b60905501a77a40905501a77a30905501a77710905500057f76505500057e76505500057d76505500057c76505501a57f74505500073f64505500c73c64505500057f73505500bd7e73505500bd7c73505500c73f43505500073d43505500057f725055032d7c72505500c73f42505500073d42505502cd7f71505500077661505500077561505500c77741505502d73e41505502d73c41505500c77441505503ff7731505503ff74315055018d7f705055000d7e705055000d7c705055018e7f605055019f7b605055018f3f405055018f7a405055018f7a30505502d57f768c5500057e768c5500057d768c5502d57c768c5502d57f748c5500c57e748c5500057d748c5502d57c748c55015d7d738c5500075f638c5500bf5c638c5500bf5e438c5500075d438c55032d7e728c5500057d728c5502ad7e718c5502d776618c55000775618c5502d75f318c5500bf77318c5502d774318c5501757f708c55000d7e708c5501757d708c55000d7c708c5501767f608c5501877b608c5501777a408c5501777a308c55017777108c5500057f764c5500057e764c5500057d764c5500057c764c5500057f744c5500c57e744c5500057d744c5500c57c744c5501757f734c5500057f724c55032d7c724c5500bf5f324c5500075d324c5502c57f714c55000776614c55000775614c5500bf77314c5502d75e314c5502d75c314c5500bf74314c55015d7f704c55000d7e704c55000d7c704c55015e7f604c55016f7b604c55015f7a404c55015f5f304c55015f7a304c55032d7f76c85500057e76c85500057d76c855032d7c76c855032d7f74c85500c57e74c85500057d74c855032d7c74c855032d7f73c85500bd7e73c85500057d73c855032d7c73c855032f6e32c85500076d32c855013d7f70c855000d7e70c855013d7d70c855000d7c70c855013e7f60c85501577b60c855013f7a40c855013f7a30c855013f6f20c85502d57f76885500057e76885500057d76885502d57c76885502d57f74885500c57e74885500057d74885502d57c74885502d57f73885500bd7e73885500057d73885502d57c73885500fd7d72885500dd7e71885502d77641885500077541885502d76f218855032f77218855011d7f708855000d7e708855011d7d708855000d7c708855011e7f608
  | 15 => 0xf425095032f3e425095032f3c42509500c76c42509500057f71509502d57c71509500c73f415095021d7f705095000d7e705095000d7c705095021e7f605095022f7b605095021f3f405095021f7a405095021f7a305095032d7f768c9500057e768c95032e7e768c9500047e768c9500057d768c95032e7d768c9500047d768c95032d7c768c95032d7f748c9500c57e748c9500057d748c95032d7c748c9501ed7d738c95030d7e728c95032f6e628c9500076d628c95042f6f428c95032f6c428c95032f5f328c9500bf6f328c95032f6c328c9502d57e718c9500057d718c9502057f708c95000d7e708c9502057d708c95000d7c708c9502067f608c9502177b608c9502077a408c9502077a308c9502076f208c9500057f764c9500057e764c9500057d764c9500057c764c9500057f744c9500c57e744c9500057d744c9500c57c744c9502057f734c9500075f634c9500bf5c634c9500bf5e434c9500075d434c95031d7f724c9500076e624c9500076d624c9504276f424c9504276c424c9500bf6f324c95032f5e324c95032f5c324c9500bf6c324c9500057f714c9502d57c714c9500bf5f314c9501ed7f704c95000d7e704c95000d7c704c9501ee7f604c9501ff7b604c9501ef7a404c9501ef5f304c9501ef7a304c9500c57e74d85500057d74d85500c57c74d85500067e64d85500067c64d85500bd7e73d85500057d73d85500bd7c73d85500067f63d85500067d63d855032d7e72d85500057d72d85500067f62d85500067d62d85500257f70d85500257d70d85502de7f60d855041f7b60d85502df7a40d85502df7a30d85502df7710d85502df7510d85500c57e74985502d73e74985500c53e74985500057d74985502d73d74985500053d74985502d57c74985500bd7e73985500057d73985502d57c739855032d7e72985500057d729855040d7e71985502d67f61985500077761985501d57d70985502d77970985500057970985501d67f60985500677b60985501d77a40985501d77a30985500057f74585500c57e74585500c57c74585500067e64585500067c64585500057f73585500075f73585500055f73585500bd7e73585500bd7c73585500075c73585500bd5c73585500067f63585500067d63585500057f725855032d7c72585500067f62585500067d62585500077761585502d67e61585501bd7f70585500077b70585500057b70585500477b60585501bf7a40585501bf7a30585502dd7e76185500c57e74185500057d74185502d57c74185500bd7e73185500057d73185502d57c731855032d7e72185500057d72185501d57e71185502d67f61185502d77661185502d67d61185500077561185500257f701855000d7e70185500257d701855000d7c701855040e7f60185504177b601855040f7a4018550
  | 16 => 0x8d5028f7a4058d5028f7a3058d500057f7650d500067f7650d500047f7650d500057e7650d500057d7650d500057c7650d500067c7650d500047c7650d503857f7450d500c73e6450d500073d6450d5037d7f7350d500bf5e6350d500075d6350d500c75f4350d500bf3e4350d500bf3c4350d500bf5c4350d500057f7250d5032d7c7250d500c73c4250d500bf5f3250d500057f7150d502d57c7150d500c73f4150d500bf5c3150d5027d7f7050d5000d7e7050d5027f7a7050d5000d7a7050d50007797050d5000d7c7050d5027e7f6050d502877b6050d5027f3f4050d5027f7a4050d5027f5f3050d5027f7a3050d500c57e74d89500057d74d89500c57c74d89500067f64d89500067d64d89500bd7e73d89500057d73d89500bd7c73d89500067e63d89500067c63d89502d57e71d89500057d71d89500257f70d89500257d70d89503367f60d89504477b60d89503377a40d89503377a30d89503376f20d89503376d20d89500c57e74989500057d749895032d7c74989500bd7e739895032f5e73989500bd5e73989500057d739895032f5d73989500055d739895032d7c73989504357e729895032e7f62989500076f62989502d57e71989500057d71989502657d709895032f7970989500057970989502667f60989500977b60989502677a40989502677a30989500057f74589500073f74589500053f74589500c57e74589500c57c74589500073c74589500c53c74589500067f64589500067d64589500057f73589500bd7e73589500bd7c73589500067e63589500067c63589500076f625895032e7e62589500057f71589502d57c715895024d7f70589500077b70589500057b705895007f7b605895024f7a405895024f7a30589503357e76189500c57e74189500057d741895032d7c74189500bd7e73189500057d731895032d7c73189502657e721895032e7f621895032f6e621895032e7d62189500076d62189502d57e71189500057d71189500257f701895000d7e70189500257d701895000d7c70189504367f601895043f7b60189504377a40189504377a30189504376f20189504376d201895032d7f76909500057e76909500057d769095032d7c769095021d7d74909500073f64909500c73c64909500bd7e73909500057d739095032d7c73909500c73f43909500073d43909503157e729095032f6e62909500076d629095032f3f42909500c76f429095032f6c42909502d57e71909500057d71909502357f709095000d7e70909502357d709095000d7c70909502367f60909502477b60909502377a40909502377a30909502376f20909500057f76509500057e76509500057d76509500057c76509502357f74509500057f73509500bd7e73509500bd7c73509503257f72509500076e62509500076d62509500c76
  | 17 => 0x1bf7870545500267f60545500277b60545501bf7a40545501bf7a3054550004fe7690550004fd769055002cfc76905502d57f75905500257e75905500057d75905500257c759055002ef661905502d7765190550007755190550004ff7650550004fe7650550004fc76505500057f75505500257e75505500057d75505500257c7550550006bf645055001ebc645055019f3f54505500c73c5450550007765150550007755150550004fe768c550004fd768c55002cfc768c5502d57f758c5500257e758c5500057d758c5500257c758c550006df638c550016dc638c55002ef6618c5502d776518c55000775518c550004ff764c550004fe764c550004fc764c5500057f754c5500257e754c5500057d754c5500257c754c55000776514c55000775514c550004fe76c8550004fd76c855004cfc76c855032d7f75c85500257e75c85500057d75c85500257c75c8550004fe7688550004fd768855002cfc76885502d57f75885500257e75885500057d75885500257c7588550004ff7648550004fe7648550004fc76485500057f75485500257e75485500057d75485500257c7548550005fb704855000df87048550004fe7608550004fd760855002cfc76085502d57f75085500257e75085500057d75085500257c75085500c5be7408550005bd74085500bdde7308550005dd730855000dfa7008550005f970085504657e76d91500c67e64d91500c73e64d91500c67c64d91500bd7e73d91500057d73d91500bd7c73d915032d7e72d91500057d72d91500c73c42d91502d57e71d91500057d71d91500c73f41d91500257f70d915045f7b70d915000d7e70d91500257d70d915000d7c70d91503e67f60d915045f7b60d91503e73f40d91503e77a40d91503e73d40d91503e77a30d91503ed7f76591503e57f74591500073f64591500c67e64591500c67c64591500c73c64591500057f73591500bd7e73591500bd7c73591500c73f43591500057f725915032d7c72591500057f71591502d57c715915029d7f70591500077b70591500057b70591500b77b605915029f7a405915029f7a30591504557e76d8d500c57e74d8d500057d74d8d500c57c74d8d500be7e63d8d500bf5e63d8d500be7c63d8d5032d7e72d8d500057d72d8d500bf5f32d8d502d57e71d8d500057d71d8d500bf5c31d8d500257f70d8d5044f7b70d8d5000d7e70d8d500257d70d8d5000d7c70d8d5039e7f60d8d5044f7b60d8d5039f7a40d8d5039f5f30d8d5039f7a30d8d5039f5d30d8d503a57f7658d500057f7458d500c57e7458d500c57c7458d5039d7f7358d500075f6358d500be7e6358d500be7c6358d500bf5c6358d500bf5e4358d500057f7258d5032d7c7258d500057f7158d502d57c7158d5028d7f7058d500077b7058d500057b7058d500a77b605
  | 18 => 0xe72949500276e729495032e7f62949500076f629495032f6c62949502d57e71949500057d719495000d7e70949502677a709495032f79709495000d7c70949500267f60949500277b60949502677a40949502677a309495000d7c765495004e7c765495000c7c76549500057f74549500c57e74549500c57c74549500067f64549500057f73549500bd7e73549500bd7c73549502567e63549502567c63549500257f72549500276f72549500076f625495004e7e625495004e7c62549500076c62549500057f71549502d57c71549500077b705495000d7e705495000d7c705495024f7870549500267f60549500277b605495024f7a405495024f7a3054950004fe7690950004fd769095004cfc769095032d7f75909500257e75909500057d75909500257c7590950006bf649095001ebc649095004eee629095032f6e52909500076d5290950004ff7650950004fe7650950004fc76509500057f75509500257e75509500057d75509500257c75509500076e52509500076d5250950004fe768c950004fd768c95004cfc768c95032d7f758c9500257e758c9500057d758c9500257c758c95004eee628c95032f6e528c9500076d528c950004ff764c950004fe764c950004fc764c9500057f754c9500257e754c9500057d754c9500257c754c950006df634c950016dc634c9501ff5f534c9500bf5c534c9500076e524c9500076d524c95002cfe76d855000cfd75d85502de7d75d855001cfe74d8550004fd74d855001cfc74d85500067e54d855041e7c54d8550014fe73d8550004fd73d8550014fc73d855041e7f53d85500067d53d855004cfe72d8550004fd72d855041e7f52d85500067d52d855041ef651d855041ef551d85502d67c51d8550024fd70d85502defa30d85502def710d85500c5be7498550005bd7498550006f76198550045f97098550005df73585500bddc7358550065fb705855002ef66118550006f5611855000d7e76945501d67e769455000c7e76945500c57e74945502d73e74945500c53e74945500057d74945502d73d74945500053d74945502d57c74945500bd7e73945500057d73945502d57c739455032d7e72945500057d72945500257e71945500277671945502d67f61945500077761945502d774619455000d7e70945501d77a70945502d779709455000d7c70945500267f60945500277b60945501d77a40945501d77a309455000d7c765455002e7c765455000c7c76545500057f74545500c57e74545500c57c74545501ce7e64545501ce7c64545500057f73545500bd7e73545500bd7c73545500067f63545500057f725455032d7c72545500067f62545500257f715455002777715455000777615455002e7e615455002e7c61545500077461545500077b705455000d7e705455000d7c7054550
  | 19 => 0x87500dd7f700875000d7e70087500df7a700875000d7a70087500dd7d700875047f79700875000579700875000d7c700875001cfe76d91500257e75d915000d7d75d91500c6be64d91500c73e54d915000cfd75d91503e67d75d915000c7d75d915001cfc75d91500c67e54d91500c6be54d915045ebd54d91500c67c54d9150014fe73d9150004fd73d9150014fc73d915004cfe72d9150004fd72d915045e7f52d91500c6bc42d915002cfe71d9150004fd71d91500c6bf41d9150024fd70d91503e6bf40d91500c6bc6459150475fb705915000d7c765515001e7c765515000c7c76551500257f74551500273f74551500073f645515001e7e645515001e7c64551500c73c64551500057f73551500bd7e73551500bd7c73551500c73f43551500057f725515032d7c72551500057f71551502d57c71551500077b705515000d7e705515000d7c705515029f7870551500267f60551500277b605515029f7a405515029f7a3055150014fe76d8d500257e75d8d5000d7d75d8d500bede63d8d500bf5e53d8d5000cfd75d8d5039e7d75d8d5000c7d75d8d50014fc75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d500be7e53d8d500bede53d8d5044edd53d8d500be7c53d8d5004cfe72d8d50004fd72d8d500bedf32d8d5002cfe71d8d50004fd71d8d5044e7f51d8d500bedc31d8d50024fd70d8d5039edf30d8d500bedc6358d5046dfb7058d5000d7c7654d500167c7654d5000c7c7654d500057f7454d500c57e7454d500c57c7454d500257f7354d500275f7354d500075f6354d500167e6354d500167c6354d500bf5c6354d500bf5e4354d500057f7254d5032d7c7254d500057f7154d502d57c7154d500077b7054d5000d7e7054d5000d7c7054d5028f787054d500267f6054d500277b6054d5028f7a4054d5028f7a3054d50004ff7650d50004fe7650d50004fc7650d500057f7550d500257e7550d500057d7550d500257c7550d5001ebe6450d500c73e5450d500073d5450d50016de6350d500bf5e5350d500075d5350d5000dfa7050d5004cfe76d895000cfd75d89503367d75d895001cfe74d8950004fd74d895001cfc74d89504467f54d89500067d54d8950014fe73d8950004fd73d8950014fc73d89500067e53d89504467c53d8950446ee52d8950446ed52d895032e7c52d895002cfe71d8950004fd71d89504467f51d8950024fd70d8950336fa40d8950336ef20d89500bdde7398950005dd7398950006ef629895007df97098950005bf74589500c5bc7458950095fb705895004eee6218950006ed621895000d7e76949502667e769495000c7e76949500c57e74949500057d749495032d7c74949500bd7e739495032f5e73949500bd5e73949500057d739495032f5d73949500055d739495032d7c73949500257
  | 20 => 0x19d7f76507500257e765075019d7d76507500257c765075019f3f64507500d73c64507500057f73507500cd7e73507500cd7c73507500d73f43507500073d43507500057f72507504857c72507500d73f42507500073d42507502cd7f715075019f76615075019f7561507500d777415075047f3e415075047f3c41507500d774415075048f77315075048f74315075018d7f705075000d7e705075000d7c705075018f3f405075047d7f768c7500257e768c7501857d768c7500257c768c75047d7f748c7500d57e748c7500057d748c75047d7c748c7500cf5e438c7500075d438c7504857e728c7500057d728c7502ad7e718c75047f76618c75018775618c75047f5f318c7500cf77318c75047f74318c7501757f708c75000d7e708c7501757d708c75000d7c708c75017777108c75016d7f764c7500257e764c75016d7d764c7500257c764c7500057f744c7500d57e744c7500057d744c7500d57c744c7500057f724c7504857c724c7500cf5f324c7500075d324c7502c57f714c75016f76614c75016f75614c7500cf77314c75047f5e314c75047f5c314c7500cf74314c75015d7f704c75000d7e704c75000d7c704c75015f5f304c7504857f76c87500257e76c87501557d76c87500257c76c87504857f74c87500d57e74c87500057d74c87504857c74c87504857f73c87500cd7e73c87500057d73c87504857c73c87504876e32c87500076d32c87501577661c87501577561c875013d7f70c875000d7e70c875013d7d70c875000d7c70c875013f6f20c875047d7f76887500257e76887501357d76887500257c768875047d7f74887500d57e74887500057d748875047d7c748875047d7f73887500cd7e73887500057d738875047d7c73887501376e62887501376d628875047f76418875000775418875047f6f218875048777218875011d7f708875000d7e708875011d7d708875000d7c708875011f7710887501157f76487500257e76487501157d76487500257c76487500057f74487500d57e74487500057d74487500d57c74487500057f73487500cd7e73487500057d73487500cd7c73487500076e32487500076d324875000776414875000775414875048777214875047f6e21487500fd7f704875000d7e704875000d7c704875047d7f76087500257e760875047e7e76087500247e76087500f57d760875047e7d76087500047d76087500257c760875047d7f74087500d57e740875047f3e74087500d53e74087500057d740875047f3d74087500053d740875047d7c740875047d7f73087500cd7e730875047f5e73087500cd5e73087500057d730875047f5d73087500055d730875047d7c73087504876e62087500f76d620875047f7661087500f775610875047f6f210875047f76210875047f6d210875048775210
  | 21 => 0xa415802102ef9415802102ef8415802102efb315802102efa315802102ef9315802102ef8315802102efb215802102eeb215802102efa215802102ef2215802102ef9215802102ee9215802104ef1215802102ef821580212857f7650f500067f7650f500047f7650f500257e7650f502857d7650f500257c7650f502867c7650f500247c7650f503857f7450f500d73e6450f502873d6450f5037d7f7350f500cf5e6350f502875d6350f500d75f4350f500cf3e4350f500cf3c4350f500cf5c4350f500057f7250f504857c7250f500d73c4250f500cf5f3250f500057f7150f5047d7c7150f500d73f4150f500cf5c3150f5027d7f7050f5000d7e7050f5000d7c7050f5027e7d6050f5027f3f4050f5027f5f3050f504857f7690b500257e7690b502457d7690b500257c7690b500cd7e7390b500057d7390b504857c7390b500d73f4390b500073d4390b503157e7290b504876e6290b502476d6290b504873f4290b500d76f4290b504876c4290b5047d7e7190b500057d7190b502357f7090b5000d7e7090b502357d7090b5000d7c7090b502376f2090b5022d7f7650b500257e7650b5022d7d7650b500257c7650b500057f7350b500cd7e7350b500cd7c7350b503257f7250b5022f6e6250b5022f6d6250b500d76f4250b504873e4250b504873c4250b500d76c4250b500057f7150b5047d7c7150b500d73f4150b5021d7f7050b5000d7e7050b5000d7c7050b5021f3f4050b504857f768cb500257e768cb504867e768cb500247e768cb502157d768cb504867d768cb500047d768cb500257c768cb504857f748cb500d57e748cb500057d748cb504857c748cb5030d7e728cb504876e628cb502176d628cb504a76f428cb504876c428cb504875f328cb500cf6f328cb504876c328cb5047d7e718cb500057d718cb502057f708cb5000d7e708cb502057d708cb5000d7c708cb502076f208cb501fd7f764cb500257e764cb501fd7d764cb500257c764cb500057f744cb500d57e744cb500057d744cb500d57c744cb501ff5f634cb500cf5c634cb500cf5e434cb500075d434cb5031d7f724cb501ff6e624cb501ff6d624cb5049f6f424cb5049f6c424cb500cf6f324cb504875e324cb504875c324cb500cf6c324cb500057f714cb5047d7c714cb500cf5f314cb501ed7f704cb5000d7e704cb5000d7c704cb501ef5f304cb5047d7f76907500257e769075047e7e76907500247e76907501b57d769075047e7d76907500047d76907500257c76907500cd7e73907500057d739075047d7c73907504857e72907500057d72907502bd7e719075047f7661907501b775619075047f3f41907500d777419075047f74419075049777319075047f7431907501a57f709075000d7e70907501a57d709075000d7c70907501a7771090750
  | 22 => 0x8c2100cfe7058c2100cfc7058c210e6df3058c21006de3058c210e6dc3058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2104edf7258c2104ede7258c2104edd7258c2104edc7258c2104edf5258c2104ede5258c2104edd5258c2104edc5258c2104edf4258c2104ede4258c2104edd4258c2104edc4258c2102edf7158c2102ede7158c2102edd7158c2102edc7158c2102edf5158c2102ede5158c2102edd5158c2102edc5158c2102edf4158c2102ede4158c2102edd4158c2102edc4158c2102edf2158c2102ecf2158c2102ede2158c2102edd2158c2102ecd2158c2102edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dc5058c21006df4058c21006de4058c21006dc4058c2104edf2058c2104ede2058c2104edd2058c2104edc2058c2102edf1058c2102ede1058c2102edd1058c2102edc1058c21004ff7654c2102cfe7654c21004fd7654c2102cfc7654c210267e6554c210067d6554c21296be6454c21006bd6454c21016de6354c21006dd6354c2128efa6054c21004ff7650c2102cfe7650c21004fd7650c2102cfc7650c210057f7550c210f57c7550c212867e6550c210067d6550c2101ebe6450c21006bd6450c21016de6350c21006dd6350c2127efa6050c21004ff7558021024fe75580210067e75580210067d7558021024fc7558021004ff745802101cfe745802101cfc7458021004ff7358021014fe7358021014fc735802100cfd725802100cfd715802102eef215802102ef6215802102eed215802104ef5215802102cff705802102efb7058021006fb50580210defa50580210def85058021006fb40580210defa40580210def84058021006fb30580210defa30580210def8305802104efb205802104ef8205802102efb105802102ef81058021006fb7558021006fa75580210067a7558021006f97558021006797558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f8435802104efb725802104efa725802104ef8725802104efb525802104efa525802104ef9525802104ef8525802104efb425802104efa425802104ef9425802104ef8425802104efb325802104efa325802104ef9325802104ef8325802102efb715802102efa715802102ef8715802102efb515802102efa515802102ef9515802102ef8515802102efb415802102ef
  | 23 => 0x4e7f725942104e7e725942104e7d725942104e7c725942104e7f425942104e7e425942104e7d425942104e7c425942104e7f325942104e7e325942104e7d325942104e7c325942102e7f715942102e7e715942102e7d715942102e7c715942102e7f415942102e7e415942102e7d415942102e7c415942102e7f315942102e7e315942102e7d315942102e7c315942102e7f215942102e7e215942102e7d215942102e7c21594210067f70594210047f70594210067e70594210067d70594210067c70594210067f40594210067e40594210067c40594210067f30594210067e30594210067c305942104e7f205942104e7e205942104e7d205942104e7c205942102e7f105942102e7e105942102e7d105942102e7c1059421004ff7559021024fe7559021024fc755902102cff745902102ebf7459021006bf54590210eebe54590210eebc5459021004ff7359021014fe7359021014fc73590210eebf4359021006be43590210eebc435902104cfe725902104cfc725902104ebe425902104ebc425902102cfe715902102cfc715902102ebe415902102ebc415902102ef6215902104ef52159021004ff705902100cfe705902100cfc70590210eebf4059021006be40590210eebc4059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bc535902104ebf725902104ebe725902104ebd725902104ebc725902104ebf525902104ebe525902104ebd525902104ebc525902104ebf325902104ebe325902104ebd325902104ebc325902102ebf715902102ebe715902102ebd715902102ebc715902102ebf515902102ebe515902102ebd515902102ebc515902102ebf315902102ebe315902102ebd315902102ebc315902102ebf215902102ebe215902102eb6215902102ebd215902104eb5215902102ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bc5059021006bf3059021006be3059021006bc305902104ebf205902104ebe205902104ebd205902104ebc205902102ebf105902102ebe105902102ebd105902102ebc1059021004ff765502102cfe7655021004fd765502102cfc76550210267e65550210067d655502101ebe6455021006bd64550212a6de635502129efa6055021004ff7558c21024fe7558c21024fc7558c21004ff7458c2101cfe7458c2101cfc7458c2102cff7358c2102edf7358c21006df5358c210e6de5358c210e6dc5358c21006df4358c210e6de4358c210e6dc4358c2104cfe7258c2104cfc7258c2104ede3258c2104edc3258c2102cfe7158c2102cfc7158c2102ede3158c2102edc3158c2102eef2158c2102eed2158c21004ff705
  | 24 => 0xc638c92102dee718c92102dec718c92104eef618c92104fe7618c921005ed708c92102cfc764c921006df634c921016dc634c92104fcc324c921005f7714c92102df4714c92102dec764c921016ec764c92102cec764c921006ef654c921006ed654c9211f6ee644c9211f6ec644c92104def734c92104fcf734c921007cf634c921016ee634c921016ec634c921107cc634c9214b7cf534c921107cc534c921107ce434c921007cd434c921007e7714c92102dee714c92102dec714c921007e4714c92104eef614c92104fe7614c921107cf314c921005ef704c921107cf304c921024ff7654521114fd765452104cfc76545210067f65545210267c6554521005ef725452104dec725452102fe42154521005f6769052102ef6769052102f76759052102f757590521006f76590521006f5659052110df5749052101ef6649052101ef464905211aef663905211aef4639052104df6729052102df4729052102ef7629052102fe76290521007e63290521007e53290521005f5709052101cff765052110cfd765052104cfc7650521006bf645052101ebc6450521005ef725052104dec725052102fb4415052104df4765052101ef4765052104cf47650521006f76550521006f5655052102df7745052102fb77450521007b7645052101ef6645052101ef4645052110fb464505214afb7545052110fb45450521196f66350521196f4635052110fb74350521007b54350521007e7725052104df6725052104df47250521007e4725052102ef7625052102fe7625052110fb74250521007b54250521007e63250521007e53250521005f7705052110fb74050521014ff764c521104fd764c52104cfc764c521006df634c521016dc634c521005ef724c52104dec724c521007cd324c52100cfe76d81210fefa60d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121014fe73d8121004fd73d8121014fc73d812102cfd72d812100cfc72d8121006ee32d8121006ed32d812104cfd71d812100cfc71d8121006f641d8121006f541d81210fefa50d81210fefa20d81210fefa10d81210fef8605812102cff755942102e7f7559421004ff745942101cfe745942101cfc74594210f67f54594210067e54594210f67c5459421004ff7359421014fe7359421014fc73594210f67f53594210067e53594210f67c535942104cfe725942104cfc725942104e7e525942104e7c525942102cfe715942102cfc715942102e7e515942102e7c5159421004ff705942100cfe705942100cfc70594210f67f50594210067e50594210f67c50594210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067c4359421
  | 25 => 0x62102fb464506214bfb7545062112fb45450621196f6635062102ef4635062112fb74350621007b5435062104df6725062104df4725062112fb74250621007b54250621005f7705062112fb74050621004ff7558221024fe7558221024fc7558221004ff745822101cfe745822101cfc7458221004ff7358221014fe7358221014fc735822102cfc715822102ef64158221006f5415822102eef215822102eed215822102efb705822111efa305822111efa205822102efb105822102ef81058221024fe76d95211167e65d952101cfe74d9521004fd74d952101cfc74d9521014fe73d9521004fd73d9521014fc73d952102cfd72d95211167f52d952104cfd71d95211167f51d952100cfe70d9521004fd70d952100cfc70d95211167f50d95211167c6559521114ff75595210067f7559521004ff745952101cfe745952101cfc7459521004ff7359521014fe7359521014fc7359521134ff7259521006ef7259521154ff7159521006f77159521004ff705952100cfe705952100cfc70595211167f505952101cfe76d912110ebe64d9121024fe75d9121004fd75d9121024fc75d9121014fe73d9121004fd73d9121014fc73d912110ebf43d912102cfd72d912110ebf42d912104cfd71d912110ebf41d912100cfe70d9121004fd70d912100cfc70d912110ebc6459121004ff7559121024fe7559121024fc755912110cff7459121006bf7459121004ff7359121014fe7359121014fc735912112cff7259121006ef725912114cff7159121006f77159121004ff705912100cfe705912100cfc705912110ebf4059121004ff7655121004fe7655121004fd7655121004fc7655121014fe76d8d21106de63d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21106de43d8d2102cfd72d8d21106df32d8d2104cfd71d8d21106df31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21106dc6358d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21104ff7358d21006df7358d21124ff7258d21006ef7258d21144ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21106df3058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d211157c7550d21006bf6450d2101ebc6450d21006df6350d21016dc6350d2102cfc76549210067f65549210267c6554921005f7715492102df4715492104fe4215492102cfc7650921006bf645092101ebc6450921005f7715092102df47150921005ee768c92104eee768c92104f6e758c92104f6d758c921006ef658c921006ed658c92120eee648c92120eec648c921105ed738c921016ee638c921016e
  | 26 => 0x57f7550f211557c7550f21356bf6450f2101ebc6450f21016de6350f21006dd6350f2104def764cb210e6ef764cb2104eef654cb21006ed654cb211f6ee644cb2104eec644cb2104fcf734cb2104fcf634cb21016ee634cb2104eec634cb2104fcc634cb214c7cf534cb21147cc534cb21147ce434cb21007cd434cb2102dee714cb2102dec714cb21147cf314cb21005ef704cb21147cf304cb21024ff765472104cfc76547210267e65547210067d6554721005ef725472104dec725472101cff765072104cfc765072101ebe6450721006bd6450721005ef725072104dec7250721014ff764c72104cfc764c721016de634c721006dd634c721005ef724c72104dec724c721007cd324c721004ff7558321024fe7558321024fc7558321004ff745832101cfe745832101cfc7458321004ff7358321014fe7358321014fc735832102cfc725832104eee3258321006ed325832104ef6215832104ef5215832104efb705832113efa405832104efb205832104ef8205832113efa105832102e7f7559621004ff745962101cfe745962101cfc74596210067e54596211367c5459621004ff7359621014fe7359621014fc73596211367f53596211367f525962102cfc715962102e7e515962102e7c515962102ef64159621004ff705962100cfe705962100cfc70596211367f5059621004ff7559221024fe7559221024fc755922102ebf7459221006bf545922112ebc5459221004ff7359221014fe7359221014fc735922112ebf435922112ebf425922102cfc715922102ebe415922102ebc4159221004ff705922100cfe705922100cfc705922112ebf405922102ef71059221004ff765522102cfe7655221004fd765522102cfc7655221004ff7558e21024fe7558e21024fc7558e21004ff7458e2101cfe7458e2101cfc7458e2102edf7358e21126df3258e2102cfc7158e2102ede3158e2102edc3158e2102eef2158e2102eed2158e21004ff7058e2100cfe7058e2100cfc7058e21126df3058e2102ef71058e21004ff7654e2102cfe7654e21004fd7654e2102cfc7654e210267e6554e210067d6554e21004ff7650e2102cfe7650e21004fd7650e2102cfc7650e210057f7550e211357c7550e2101ebe6450e21006bd6450e212fedf6350e21016dc6350e2104ef72158a2102eee2158a2102eec2158a2102ef42158a21024ff7654a2102cfc7654a210267e6554a210067d6554a21005f77154a2102df47154a2101cff7650a2102cfc7650a2101ebe6450a21006bd6450a2104fac4250a21005f77150a2102df47150a21014ff764ca2102cfc764ca21016de634ca21006dd634ca21005f7714ca2102df4714ca2102df776506210eef7765062102ef76550621006f5655062102fb7745062102fb7645062101ef6645062102ef4645
  | 27 => 0xd644c931015df724c931017cf724c931007cf624c93104ede624c93104edc624c931007cc624c931007ce524c931007cd524c9314dfcf424c9314dfcc424c931007d7714c93102dde714c93102ddc714c931007d4714c931016df614c931017d7614c931005df704c9314d5f6769453102ef676945311c5f57594531026f66594531026f4659453102fb6749453102fb57494531006f76494531006f56494531015f6739453102df4739453102ef7639453102fd763945311dfd73294531007d53294531005f5709453116f7750945311dfd73094531024ff7654531014fe76545311c4fd7654531014fc76545310067f65545310267c6554531005df7354531015dc735453102f745154531015f47654531026f47654531014f4765453102df7755453102f777554531007776554531026f66554531026f4655453116f746554531006f76454531006f564545314cf76545453116f745454531007d77354531015f67354531015f473545311c7d4735453102ef7635453102fd763545311c77753545311c775535453116f7752545310077552545311c7d73254531007d53254531005f7705453116f7750545311c7d7305453101cff7650531014fe7650531194fd7650531014fc7650531006bf645053101ebc6450531005df7350531015dc7350531196f7615053102fd4315053100cfe76d813115efa60d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d813102cfd73d813100cfc73d813104cfe72d8131004fd72d8131056df32d8131006dd32d8131014fd71d813115efa30d813115efa10d813115ef8605813104e7f7559721004ff745972101cfe745972101cfc74597211567f5459721004ff7359721014fe7359721014fc73597210067e53597211567c535972102cfc725972104e7e525972104e7c525972104eee32597211567f5159721004ff705972100cfe705972100cfc70597211567f5059721004ff7559321024fe7559321024fc755932104ebf7459321004ff7359321014fe7359321014fc735932102cfc725932104ebe425932104ebc425932114ebf415932104ef6215932104ef52159321004ff705932100cfe705932100cfc705932114ebf405932104eef2059321004ff765532104cfe7655321004fd765532104cfc76553210267e65553210067d6555321004ff7558f21024fe7558f21024fc7558f21004ff7458f2101cfe7458f2101cfc7458f2104edf7358f21006df5358f21146dc5358f21146de4358f2102cfc7258f2104ede3258f2104edc3258f21146df3158f21004ff7058f2100cfe7058f2100cfc7058f21146df3058f2104eef2058f21004ff7654f2104cfe7654f21004fd7654f2104cfc7654f21004ff7650f2104cfe7650f21004fd7650f2104cfc7650f21
  | 28 => 0x4631026f6655463102ef4655463102f74655463102ef76454631006f564546314ff765454631187745454631015f67354631015f473546311c77753546311c77553546311c7d64354631007d54354631187775254631007755254631005f77054631187775054631004ff7558231024fe7558231024fc7558231004ff745823101cfe745823101cfc7458231036de4358231006dd4358231004ff725823104cfc725823102cfe715823102cfc715823102edf315823102edd315823102efb7058231176fa3058231176fa205823102efb105823102ef81058231024fe76d953116e7e65d953101cfe74d9531004fd74d953101cfc74d95310067e54d953116e7c54d953102cff73d953102cfd73d95311de7f53d95311de7d53d953104cfe72d9531004fd72d953116e7f52d9531014fd71d953116e7f51d953100cfe70d9531004fd70d953100cfc70d953116e7f50d953116e7c65595314f5f771595311dcff75595310067f7559531004ff745953101cfe745953101cfc74595311c4ff7359531006df7359531004ff725953104cfc72595314f4ff7159531006f77159531004ff705953100cfe705953100cfc705953116e7f505953101cfe76d9131166be64d9131024fe75d9131004fd75d9131024fc75d913102cff73d913102cfd73d91311aebf43d91311aebd43d913104cfe72d9131004fd72d91311aedf32d9131014fd71d9131166bf41d91311aef731d91314eede31d91314eedc31d91311aef431d913100cfe70d9131004fd70d913100cfc70d91311aedf30d91310057f755913116d7c7559131166bc64591314e5f77159131004ff75591310067f75591310047f7559131024fe7559131024fc75591310067c75591310247c75591311acff7459131006bf7459131194ff7359131006df7359131004ff725913104cfc7259131196df32591314e4ff7159131006f77159131196f731591312fede31591312fedc3159131196f43159131004ff705913100cfe705913100cfc7059131166bf4059131196df3059131004ff7655131004fe7655131004fd7655131004fc7655131024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d893102cfd73d8931126ee32d8931126ed32d893100cfe70d8931004fd70d893100cfc70d8931126df30d893116d7e75989310057d7598931006ef6298931105f57198931145f7715893104eee6218931006ed6218931004fe7694931004fd769493104cfc7694931015de7394931005dd7394931004ff7654931004fe7654931004fc76549310067f65549310267c6554931004fe7690931004fd769093104cfc7690931015de7390931005dd7390931004ff7650931004fe7650931004fc765093102cdc764c9311fede654c9311fedc654c931006df644c931006d
  | 29 => 0x26f4765454101cf4765454102df7755454102f777554541007776554541026f66554541026f4655454119f746554541007b7745454101df6745454101df474545411cfb4745454102ef7645454102fb7645454119fb754545411cf7654545411cf7454545411cfb454545411cf345454541195f67354541195f47354541006f7635454119f7753545410077553545411cfb74354541007b54354541005f7725454119f7752545410077552545411cfb74254541007b54254541005f7705454119f7750545411cfb7405454100cfe76d814118efa60d8141024fe75d8141004fd75d8141024fc75d814102cfd74d814100cfc74d8141014fe73d8141004fd73d8141014fc73d814105ebf43d8141006bd43d814104cfe72d8141004fd72d814105ebf42d8141006bd42d814101cfd71d814118efa40d814118efa10d8141005ef7258141005ec725814118ef8605814102e7f7559631004ff745963101cfe745963101cfc74596310067e54596311867c54596311c67f53596311c67d53596311c6de4359631004ff725963104cfc72596311867f525963102cfe715963102cfc715963102e7e515963102e7c5159631004ff705963100cfe705963100cfc70596311867f5059631004ff7559231024fe7559231024fc755923102ebf7459231006bf545923117ebc5459231196bf4359231196bd4359231004ff725923104cfc725923117ebf425923102cfe715923102cfc715923102ef6515923102ebe415923102ebc4159231196f7315923102ef43159231004ff705923100cfe705923100cfc705923117ebf405923102ef71059231004ff765523102cfe7655231004fd765523102cfc76552312fddf7650e3101edf7650e3101cdf7650e310075f7550e310075c7550e312fedf6550e31006dd6550e31015df7450e310179f7450e3101ede6450e312ff9e6450e312ff9d6450e3101edc6450e3117f9e5450e310079d5450e3117f9c4250e312fddf7150e31007d77150e312ffd47150e31016de6150e31017d66150e312ffd65150e312ff9f4150e312ff9d4150e3117f9f4050e31004ff7558a31024fe7558a31024fc7558a31004ff7458a3101cfe7458a3101cfc7458a31106de4358a31006dd4358a3102eef7258a31106ee3258a31106ed3258a3102cfc7158a3102edf3158a3102edd3158a3102eee2158a3102eec2158a31004ff7058a3100cfe7058a3100cfc7058a3102ef71058a3104cff7694a3102cfe7694a31004fd7694a31015de7394a31005dd7394a31004ff7654a31004fd7654a3102cfc7654a310267e6554a310067d6554a3104cff7690a3102cfe7690a31004fd7690a310079d4390a31004ff7650a31004fd7650a3102cfc7650a3101ebe6450a31006bd6450a3102df77654631506f7765463102f77755463102f77655
  | 30 => 0xf40d8d410057f7558d4119d7c7558d41196dc6358d4151df77158d41197d43158d41004ff7654d41004fe7654d41004fc7654d41005bf7454d4101dbc7454d41005f77154d4102df47154d4102dbc7650d41016bc7650d4102cbc7650d410073f7550d4119dbe7550d4119dbc7550d410073c7550d4119d3c7550d41006bf6550d41006bd6550d4101dbf7350d4101f9f7350d410079f6350d41016be6350d41016bc6350d411979c6350d411979e5350d410079d5350d41005bf7250d41356bc6250d411979f3250d41007b77150d4102dbe7150d4102dbc7150d41007b47150d4101ebf6150d4101fb76150d41197b73150d412ff9c3150d41197b43150d41197943150d41005bf7050d411979f3050d41024fe75d8941004fd75d8941024fc75d894102cfd74d8941014fe73d8941004fd73d8941014fc73d894112eee42d894112eed42d894100cfe70d8941004fd70d894100cfc70d894112ebf40d8941006ee20d8941006ec20d8941006ef629894110df5719894114df7715894119d7e75189410057d7518941195de7318941005dd731894104eee6218941006ed621894118dfa7018941005f97018941004fe7694941004fd769494104cfc769494101dbe7494941005bd7494941195de7394941005dd739494102df67194941005f57194941004ff7654941004fe7654941004fc76549410267e65549410067d6554941005bf745494101dbc745494119f3f545494102cbc765094119dbe755094119dbc7550941005bf735094101dbf725094101faf7250941007af625094104ebe625094104ebc6250941007ac625094104eac6250941007ae5250941007ad5250941007b7715094102dbe715094102dbc7150941007b4715094101ebf615094101fb76150941517b73150941517b43150941005bf7050941004fe768c941004fd768c94104cfc768c94119d7e758c9410057d758c94101dbe748c941005bd748c941006ef628c94104eec628c94120faf428c94102df6718c941005f5718c941004ff764c941004fe764c941004fc764c94101dbe744c941005bd744c941016de634c9410079d434c941006ef624c94104eec624c9411f7af424c941005f7714c94102df4714c941197d7314c94150df6769454102ef676945411cdf57594541026f66594541026f4659454101df6749454102fb6749454101db6749454102fb5749454102df4749454102ef7649454102fb7649454119fb754945411e7b45494541195f6739454102df47394541006f763945411e7b74394541007b54394541005f572945411e7b74294541007b54294541005f5709454119f7750945411e7b74094541024ff765454101cfe76545411ccfd765454101cfc76545410067f65545410267c6554541005bf745454101dbc74545411cf3c545454101df47654541
  | 31 => 0x8a41024fc7558a41004ff7358a41014fe7358a41014fc7358a4102eef7258a4110eee4258a4110eed4258a4102cfc7158a4102ebf4158a4102ebd4158a4102eee2158a4102eec2158a41004ff7058a4100cfe7058a4100cfc7058a4102ef71058a4104cff7694a4102cfe7694a41004fd7694a410267e6594a410067d6594a411adde7394a41005dd7394a4102df67194a41005f57194a41004ff7654a41004fd7654a4102cfc7654a410267e6554a410067d6554a4102df67154a4104cff768ca4102cfe768ca41004fd768ca411b57e758ca410057d758ca412167e658ca410067d658ca4104eee628ca41006ed628ca4102df6718ca41005f5718ca41004ff764ca41004fd764ca4102cfc764ca411fe7e654ca410067d654ca41016de634ca41006dd634ca4104eee624ca41006ed624ca41005f7714ca4102df4714ca411afd7314ca4102df7765464152ef7765464102f777554641026f6655464102f76655464102676655464102f75655464102ef4655464101df6745464101df474546411cf7654546411cf7454546411adf673546411adf47354641006f563546411b7775354641007755354641005f772546411b7775254641007755254641005f770546411b7775054641004ff7558241024fe75582410067e75582410067d7558241024fc7558241004ff7358241014fe7358241014fc7358241004ff725824104cfc725824102cfe715824102cfc715824102ebf415824102ebd415824102ef6215824102efb70582411a6fa40582411a6fa30582411a6fa205824102efb105824102ef81058241024fe76d954119e7e65d954101dbe74d954102dbd74d954119f3f54d954102cff74d954102cfd74d954119ebd74d954102cbd74d95411e67f54d954119ebf54d95411e67d54d95411e6bc54d9541014fe73d9541004fd73d9541014fc73d95410067e53d954119e7c53d95411e6bf43d954104cfe72d9541004fd72d954101cfd71d954119e7f51d954100cfe70d9541004fd70d954100cfc70d954119e7f50d954119e7c65595411cf3c5459541525f771595411e4ff75595410067f75595411ccff7459541006bf745954119ebf54595411ce7e54595411ce7c54595411cebc5459541004ff7359541014fe7359541014fc73595411cebf4359541004ff725954104cfc725954119e7f5259541524ff7159541006f77159541004ff705954100cfe705954100cfc705954119e7f5059541014fe76d8d41196de63d8d4102df671d8d4101df571d8d41197d731d8d41024fe75d8d41004fd75d8d41024fc75d8d4102cfd74d8d41196de43d8d4117edd43d8d4104cfe72d8d41004fd72d8d4101cfd71d8d41196f571d8d4101cf571d8d41196df31d8d41196f731d8d41196f431d8d4100cfe70d8d41004fd70d8d4100cfc70d8d4117eb
  | 32 => 0x57f7054951004fe7690951004fd769095104cfc76909510257e75909510057d75909510076d5290951004ff7650951004fe7650951004fc76509510057f75509510257c75509510076d5250951004fe768c951004fd768c95104cfc768c9510257e758c9510057d758c95104eee628c9510076d528c951004ff764c951004fe764c951004fc764c9510257e754c9510057d754c951006df634c951016dc634c9511ff5f534c9510076d524c95100cfe76d81511befa60d815147e7f75d815102cfd75d815100cfc75d815100c7c75d815101cfe74d8151004fd74d815101cfc74d81510067e54d81510667c54d8151014fe73d8151004fd73d8151014fc73d81510667f53d81510067d53d815104cfe72d8151004fd72d81510667f52d81510067d52d8151024fd71d815147e7e51d815147e7c51d81511be7f50d81511befa50d81511befa10d8151005df73581511c5dc73581511bef8605815102e7f75596411ce7f54596411ce7d5459641004ff7359641014fe7359641014fc73596411b67f53596410067e53596411b67c5359641004ff725964104cfc72596411b67f52596411b67c525964102cfe715964102cfc715964102e7e515964102e7c5159641004ff705964100cfe705964100cfc70596411b67f50596410067e50596411b67c50596411ce7f74596411ce7e74596411ce7d74596411ce7c74596410067f73596410067e73596410067d73596410067c73596411ce7f43596411ce7e43596411ce7d43596411ce7c43596410067f72596410067e72596410067d72596410067c72596411ce7f42596411ce7e42596411ce7d42596411ce7c42596410067f32596410067c325964102e7f715964102e7e715964102e7d715964102e7c715964102e7f415964102e7e415964102e7d415964102e7c415964102e7f315964102e7e315964102e7d315964102e7c315964102e7f215964102e7e215964102e7d215964102e7c21596410067f70596410047f70596410067e70596410067d70596410067c70596411ce7f40596411ce7e40596411ce7d40596411ce7c40596410067f30596410067e30596410067c30596410067e20596410067c205964102e7f105964102e7e105964102e7d105964102e7c1059641004ff7558e41024fe7558e41024fc7558e4102edf7358e411aede4358e41166dd4358e41004ff7258e4104cfc7258e411aedf3258e4102cfe7158e4102cfc7158e4102ef47158e4102cf47158e4102ef65158e4102ebf4158e4102ebd4158e411aef73158e4102ede3158e4102edc3158e4102ef43158e41004ff7058e4100cfe7058e4100cfc7058e411aedf3058e4102ef71058e41004ff7654e41004fd7654e4102cfc7654e410267e6554e410067d6554e41005f77154e4102df47154e41004ff7558a41024fe755
  | 33 => 0xc2158a51004ff7058a5100cfe7058a5100cfc7058a511167f5058a5104cff7690a5102cfe7690a51004fd7690a5101ebe6490a51006bd6490a51004ff7650a51004fd7650a5102cfc7650a5101ebe6450a51006bd6450a5104cff768ca5102cfe768ca51004fd768ca510257e758ca510057d758ca5120ebe648ca51006bd648ca5104eee628ca51006ed628ca51004ff764ca51004fd764ca5102cfc764ca511f6be644ca51006bd644ca51016de634ca51006dd634ca5104eee624ca51006ed624ca510067d7558251004ff745825101cfe745825101cfc7458251004ff7358251014fe7358251014fc7358251004ff725825104cfc725825102cfe715825102cfc715825102e7f515825102e7d515825102ef6415825102ef6315825102efb70582511d67f50582511d6fa50582511d6fa30582511d6fa205825102efb105825102ef8105825101cfe76d91510257e75d91511cebe64d91511cf3e54d915102cfd75d915102c7d75d91511ce7e54d91511cebe54d91511b6bd54d91511ce7c54d9151014fe73d9151004fd73d9151014fc73d915104cfe72d9151004fd72d91511b67f52d9151024fd71d91511cebf41d915100cfe70d9151004fd70d915100cfc70d91511b67f50d91511cebc64591511cf3c545915153df77159151014fe76d8d511c6de63d8d5102cfd75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d511c6de53d8d51186dd53d8d511c6de43d8d5104cfe72d8d51004fd72d8d511c6df32d8d51024fd71d8d511c6df31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d511867f50d8d51006de30d8d511c6dc30d8d511c6dc6358d51535f77158d5102d7c7654d510167c7654d5102c7c7654d511cd7e7454d511cd7c7454d510257f7354d510275f7354d510075f6354d510167e6354d510167c6354d511c75c6354d511c75e4354d510057f7254d51007777154d5102d7e7154d5102d7c7154d51007747154d510267f6154d51027776154d510057f7054d51004ff7650d51004fe7650d51004fc7650d510057f7550d510257c7550d5101ebe6450d511cf3e5450d51006df6350d51016dc6350d510075d5350d5102cfd75d895101cfe74d8951004fd74d895101cfc74d8951014fe73d8951004fd73d8951014fc73d8951136ee52d8951136ed52d895100cfe70d8951004fd70d895100cfc70d89511367f50d89511c5de7398951005dd7398951006ef6298951115f57198951155f7715895104eee6218951006ed621895102c7c76549511cd7e74549511cd7c74549510067f64549510057f73549512567e63549512567c63549510257f72549510276f72549510076f625495104e7e625495104e7c62549510076c625495100777715495102d7e715495102d7c71549510077471549510267f6154951027776154951
  | 34 => 0x932006bf645093201ebc6450932005df7350932015dc7350932545ef725093204fac4250932024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853204cfd73d8532146f631d853200cfe70d8532004fd70d853200cfc70d8532146df30d8532006f610d8532006f410d8532006f761985321fd7e75185320057d75185321f5be7418532005bd741853202ef66118532006f561185321edfa7018532005f9701853200cfe76d81321eefa60d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813204cfd73d8132086de43d8132006dd43d8132014fd72d813202cfe71d8132004fd71d8132086df31d81321eefa30d81321eefa20d8132005f77158132005f471581321eef8605813202ebf74592511e6be545925119ebd5459251004ff7359251014fe7359251014fc73592511e6bf4359251006be43592511e6bc4359251004ff725925104cfc72592511e6bf42592511e6bc425925102cfe715925102cfc715925102ebe415925102ebc4159251004ff705925100cfe705925100cfc705925119e7f50592511e6bf4059251006be40592511e6bc405925119ebe755925119ebd75592511e6bc7559251006bf7359251006be7359251006bd7359251006bc735925119ebf535925119ebe535925119ebd535925119ebc5359251006bf7259251006be7259251006bd7259251006bc725925119ebf525925119ebe525925119ebd525925119ebc5259251006bf3259251006bc325925102ebf715925102ebe715925102ebc715925102ebf515925102ebe515925102ebd515925102ebc515925102ebf315925102ebe315925102ebd315925102ebc315925102ebf215925102ebe215925102ebd215925102ebc2159251006bf7059251006be7059251006bd7059251006bc705925119ebf505925119e3f505925119ebe505925119ebd505925119ebc5059251006bf3059251006be3059251006bc3059251006be2059251006bc205925102ebf105925102ebe105925102ebd105925102ebc1059251004ff7458e5101cfe7458e5101cfc7458e5102edf7358e511dede5358e5116edd5358e51004ff7258e5104cfc7258e511dedf3258e5102cfe7158e5102cfc7158e5102e7f5158e5102e7d5158e5102ede3158e5102edc3158e51004ff7058e5100cfe7058e5100cfc7058e5116e7f5058e511dedf3058e51004ff7650e51004fd7650e5102cfc7650e510057f7550e510257c7550e5101ebe6450e51006bd6450e51016dc6350e5102df67150e51004ff7458a5101cfe7458a5101cfc7458a51004ff7358a51014fe7358a51014fc7358a5102eef7258a51116ee5258a51116ed5258a5102cfc7158a5102e7f5158a5102e7d5158a5102ef64158a5102eee2158a5102ee
  | 35 => 0xcfe705953200cfc70595321fe7f505953201cfe76d91321f6be64d913204dee72d9132015ed72d91321f7af42d9132024fe75d9132004fd75d9132024fc75d913204cff73d913204cfd73d913223ebf43d913223ebd43d9132014fd72d913223eed72d9132014ed72d91321f6bf42d91321f6ef42d91321f6ec42d913202cfe71d9132004fd71d913200cfe70d9132004fd70d913200cfc70d913223edf30d91320057f75591321fd7c75591321f6bc6459132545ef72591321f7ac4259132004ff75591320067f75591320047f7559132024fe7559132024fc75591320067c75591320247c755913223cff7459132006bf7459132224ff7359132006df7359132544ff7259132006ef72591321f6ef4259132356be4259132356bc42591321f6ec4259132004ff715913202cfc71591321f6bf4159132004ff705913200cfe705913200cfc70591321f6bf4059132226df3059132004ff7655132004fe7655132004fd7655132004fc7655132005df7355132015dc7355132005ef725513204dec725513204ddc7650d3201edc7650d3204cdc7650d320075f7550d321fdde7550d321fddc7550d320075c7550d321fd5c7550d32006df6550d32006dd6550d32015df7450d320179f7450d320079f6450d3201ede6450d3201edc6450d321f79c6450d321f79e5450d320079d5450d32007cf7250d3204dde7250d3204ddc7250d32007cc7250d32016df6250d32017cf6250d321f7cf4250d323579e4250d323579c4250d321f7cc4250d321f78c4250d32005df7150d322fedc6150d321f79f4150d32005df7050d321f79f4050d3254dee769493204eee7694932255ed7594932026ee6594932026ec65949321f5ee749493204dec7494932006ef6494932006ed6494932015ee739493204fce7394932015ce739493204fcd739493204dec739493204eef639493204fcf63949321ffcf539493226fcc539493226fce4394932007cd4394932005ed719493226fcf3194932005ed70949321ff6f509493226fcf3094932024ff7654932014fe7654932254fd7654932014fc76549320067f65549320267c6554932005df7354932015dc73549322575c5354932015ec7654932026ec7654932014ec765493204def755493204f6f75549320076f6554932026ee6554932026ec65549321ff6c65549321f5ee74549321f5ec7454932006ef6454932006ed64549321ff6f54549320076d5454932007cf7354932015ee7354932015ec7354932257cc735493204eef635493204fcf63549321ffcf53549322576e53549322576c5354932257cc53549322574c5354932257ce4354932007cd4354932005ef71549321ff6f5154932257cf3154932005ef70549321ff6f5054932257cf305493201cff7650932014fe7650932224fd7650932014fc765
  | 36 => 0xd71596320067c71596320067f41596320067c41596322567f31596322567e31596322567d31596322567c315963204e7f215963204e7e215963204e7d215963204e7c21596320067f70596320047f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067c40596322567f30596322567e30596322567d30596322567c305963204e7f205963204e7e205963204e7d205963204e7c20596320067e10596320067c1059632004ff7559232024fe7559232024fc755923204ebf7459232226bf4359232226bd435923204cfe725923204cfc725923204eec725923204cec725923204eee525923220eef425923204ebe425923204ebc425923204eec425923204edf325923204edd3259232004ff715923202cfc715923220ebf4159232004ff705923200cfe705923200cfc705923220ebf405923204eef2059232004ff765523204cfe7655232004fd765523204cfc76552320267e65552320067d6555232005ef725523204dec725523204def7654a3255eef7654a3204f6f7554a32026ee6554a3204f6e6554a320266e6554a3204f6d6554a3204eec6554a3220dee7454a3220dec7454a3204eef6454a32006ed6454a322176f5454a320076d5454a32015ee7354a32015ec7354a322576e5354a322576c5354a32005ef7154a322176f5154a32005ef7054a322176f5054a32004ff7558632024fe7558632024fc7558632004ff745863201cfe745863201cfc745863204cfc725863204edf325863204edd325863204ef77158632106f6315863204ef7215863204ef42158632004ff705863200cfe705863200cfc705863204eef2058632004ff7558232024fe75582320067e75582320067d7558232024fc7558232004ff745823201cfe745823201cfc745823204cfe725823204cfc725823204edf325823204edd3258232004ff715823202cfc715823204eef215823204efb7058232206fa4058232206fa305823204efb205823204ef82058232206fa1058232024fe76d95321fe7e65d9532015de73d953204ddd73d95321ff5f53d953201cfe74d9532004fd74d953201cfc74d95320067e54d95321fe7c54d953204cff73d953204cfd73d95321fedd73d953204cdd73d953226e7f53d95321fedf53d953226e7d53d953226edc53d953226ede43d9532014fd72d95321fe7f52d953202cfe71d9532004fd71d953200cfe70d9532004fd70d953200cfc70d95321fe7f50d95321fe7c65595322575c5359532555ef725953226cff75595320067f7559532004ff745953201cfe745953201cfc7459532254ff7359532006df73595321fedf53595322567e53595322567c5359532256dc5359532256de4359532554ff7259532006ef7259532004ff715953202cfc71595321fe7f5159532004ff7059532
  | 37 => 0x9542014fc7359542584ff7259542006ef7259542004ff715954202cfc7159542004ff705954200cfe705954200cfc705954222e7f5059542014fe76d8d42226de63d8d42024fe75d8d42004fd75d8d42024fc75d8d4204cfd74d8d42226de43d8d4220edd43d8d4201cfd72d8d4220eef42d8d4257ebe42d8d4257ebc42d8d4220eec42d8d42226df32d8d4202cfe71d8d42004fd71d8d4220ebf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d4220ebf40d8d420057f7558d4222d7c7558d42226dc6358d42575ef7258d42004ff7654d42004fe7654d42004fc7654d4256dee769494204eee769494225ded7594942026ee6594942026ec659494201dee749494204dec749494204eef649494204faf649494204fce739494204fcd7394942006ef6394942277af4194942005ed709494222f6f5094942277af4094942024ff765494201cfe765494225cfd765494201cfc76549420067f65549420267c6554942005bf745494201dbc745494204f6c525494204fac425494201dec7654942026ec765494201cec765494204def755494204f6f75549420076f6554942026ee6554942026ec655494222f6c6554942007af745494201dee745494201dec745494225fac745494204eef645494204faf645494225f6f545494225f6d5454942006ef63549425676e535494222f6c535494222f6f515494225faf4154942005ef705494222f6f505494225faf4054942024fe75d8542004fd75d8542024fc75d854204cfd74d8542014fe73d8542004fd73d8542014fc73d854214ef641d854200cfe70d8542004fd70d854200cfc70d854214ebf40d854222d7e75985420057d7598542006f7619854202ef66118542006f5611854200cfe76d814221efa60d8142024fe75d8142004fd75d8142024fc75d814204cfd74d8142014fe73d8142004fd73d8142014fc73d814201cfd72d814202cfe71d8142004fd71d814208ebf41d814221efa40d814221efa20d814221ef8605814204e7f7559632004ff745963201cfe745963201cfc74596322167f54596320067e54596322167c54596322567f53596322567d535963204cfe725963204cfc725963204e7e525963204e7c5259632004ff715963202cfc71596322167f51596322167c5159632004ff705963200cfe705963200cfc70596322167f50596320067e50596322167c50596320067f74596320067e74596320067d74596320067c74596322567f73596322567e73596322567d73596322567c73596322567f43596322567e43596322567d43596322567c435963204e7f725963204e7e725963204e7d725963204e7c725963204e7f425963204e7e425963204e7d425963204e7c425963204e7f325963204e7e325963204e7d325963204e7c32596320067f71596320067e71596320067
  | 38 => 0x4fd73d8152014fc73d81520067e53d81520967c53d8152024fd72d81524867e52d81524867c52d815202cfe71d8152004fd71d81520967f51d815224e7f50d815224efa50d815224efa20d8152005bf745815225dbc745815224ef8605815204e7f755964225e7f545964225e7d5459642004ff7359642014fe7359642014fc73596420067e53596422467c535964225ebf435964204cfe725964204cfc725964204e7e525964204e7c5259642004ff715964202cfc71596422467f5159642004ff705964200cfe705964200cfc70596422467f5059642004ff7558e42024fe7558e42024fc7558e4204edf7358e42006df5358e4223edc5358e4223ede4358e421f6dd4358e4204cfe7258e4204cfc7258e4204eee5258e421f6ef4258e4204eec4258e4204ede3258e4204edc3258e42004ff7158e4202cfc7158e4223edf3158e42004ff7058e4200cfe7058e4200cfc7058e4223edf3058e4204eef2058e42004ff7654e42004fd7654e4204cfc7654e42355bf7650e42016bf7650e42014bf7650e420073f7550e420073c7550e42356bf6550e42006bd6550e4201dbf7350e4201f9f7350e42016be6350e423579e6350e423579d6350e42016bc6350e4223f9e5350e420079d5350e42355bf7250e42007af7250e42357ac7250e4201ebe6250e4201fae6250e42357ae5250e423579f3250e4223f9c3150e4223f9f3050e4204def7654a42596ef7654a4204f6f7554a4204f6f6554a42026ee6554a4204eec6554a4204f6c6554a4201dee7454a4201dec7454a4225f6f5454a4225f6d5454a42006ed6354a4258f6e5354a422476c5354a4225faf4354a42007ad4354a422476f5154a42005ef7054a422476f5054a42004ff7558642024fe7558642024fc7558642004ff7358642014fe7358642014fc735864210ebf4358642006bd435864204cfc725864204ebf425864204ebd425864204ef7715864210ef6415864204ef7215864204ef42158642004ff705864200cfe705864200cfc705864204eef2058642004ff7558242024fe7558242024fc7558242004ff7358242014fe7358242014fc7358242076bf4358242006bd435824204cfe725824204cfc725824204ebf425824204ebd4258242004ff715824202cfc715824204efb7058242236fa405824204efb205824204ef82058242236fa1058242024fe76d954222e7e65d954204cff74d954204cfd74d95422767f54d95422767d54d9542014fe73d9542004fd73d9542014fc73d95420067e53d954222e7c53d954201cfd72d954222e7f52d954202cfe71d9542004fd71d954222e7f51d954200cfe70d9542004fd70d954200cfc70d954222e7f50d954222e7c6559542585ef7259542274ff75595420067f755954225cff7459542006bf7459542004ff7359542014fe735
  | 39 => 0xf7058e52006de7058e52006dd7058e52006dc7058e521fedf5058e521fe5f5058e521fede5058e521fedd5058e521fedc5058e52006df4058e52006de4058e52006dc4058e5204edf2058e5204ede2058e5204edd2058e5204edc2058e52006de1058e52006dc1058e52004ff7650e52004fd7650e5204cfc7650e520057f7550e520257c7550e5201ebc6450e52016de6350e52006dd6350e5204dee7250e52004ff745865201cfe745865201cfc7458652004ff7358652014fe7358652014fc735865204cfc725865204e7f525865204e7d525865204eee325865204ef77158652116f6515865204ef7215865204ef42158652004ff705865200cfe705865200cfc70586521167f50586520067d7558252004ff745825201cfe745825201cfc7458252004ff7358252014fe7358252014fc735825204cfe725825204cfc725825204e7f525825204e7d525825204eee425825204eee3258252004ff715825202cfc715825204efb70582522667f5058252266fa5058252266fa405825204efb205825204ef82058252266fa105825201cfe76d915225ebe64d915204cfd75d915225ebe54d9152246bd54d9152014fe73d9152004fd73d9152014fc73d915225ebf43d9152024fd72d915225ebf42d915202cfe71d9152004fd71d915225ebf41d915200cfe70d9152004fd70d915200cfc70d91522467f50d9152006be40d915225ebc40d915225ebc64591525a5ef725915204d7c765515201e7c765515204c7c76551520257f74551520273f74551520073f645515201e7e645515201e7c645515225f3c64551522557e73551522557c735515225f3f43551520076f725515204d7e725515204d7c72551520076c72551520267f62551520276f62551520057f71551520057f7055152014fe76d8d520257e75d8d52256de63d8d522575e53d8d5204cfd75d8d5204c7d75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d522567e53d8d52256de53d8d52216dd53d8d522567c53d8d52024fd72d8d52256df32d8d5202cfe71d8d52004fd71d8d522167f51d8d5200cfe70d8d52004fd70d8d5200cfc70d8d522167f50d8d52256dc6358d522575c5358d5259def7258d52004ff7650d52004fe7650d52004fc7650d520057f7550d520257c7550d52006bf6450d5201ebc6450d520073d5450d52016de6350d522575e5350d5204cfd75d855201cfe74d8552004fd74d855201cfc74d8552014fe73d8552004fd73d8552014fc73d8552156f651d855200cfe70d8552004fd70d855200cfc70d85521567f50d855225dbe7498552005bd7498552006f7619855202ef66118552006f5611855200cfe76d815224efa60d81524867f75d815204cfd75d815201cfe74d8152004fd74d815201cfc74d81520967f54d81520067d54d8152014fe73d8152
  | 40 => 0x8943004fd75d8943024fc75d8943014fd74d8943546bd74d894301cfd73d8943576ee42d8943356bc42d8943546ee32d894302cfe71d8943004fd71d8943576bf41d894300cfe70d8943004fd70d894300cfc70d8943576bf40d8943546df30d89432857e75989430057d75989430067f65989430067c6598943006ef6298943357ac42989430057f75589432857c75589430067f65589430067c65589431f7ac42589430067f65189430067c651894304eee6218943006ed621894302cfe76d85430067f65d85430067c65d8543024fe75d8543004fd75d8543024fc75d8543014fd74d854301cfd73d854351edd73d854304cfe72d8543004fd72d85434e6df32d854351ef641d85434e6f631d85432fedc31d854300cfe70d8543004fd70d854300cfc70d854351ebf40d85434e6df30d85432857e75985430057d75985430067f65985430067c6598543006f761985432ffd431985430057f75585432857c75585430067f65585430067c6558543197d431585430067f65185430067c651854302ef66118543006f5611854300cfe76d81430067f65d81430067c65d814327efa60d81430067f75d8143024fe75d8143004fd75d8143024fc75d81430067c75d8143014fd74d814301cfd73d814304cfe72d8143004fd72d814338edf32d814302cfe71d8143004fd71d81433d6bf41d814327efa40d814327efa30d81430057f75581432857c75581430067f65581430067c655814327ef8605814304ebf7459252276be545925222ebd5459252004ff7359252014fe7359252014fc735925204cfe725925204cfc725925204e7f525925204e7d525925204ebe425925204ebc4259252004ff715925202cfc7159252276bf4159252004ff705925200cfe705925200cfc705925222e7f5059252276bf4059252004ff7458e5201cfe7458e5201cfc7458e5204edf7358e5226ede5358e521fedd5358e52006df4358e5226ede4358e5226edc4358e5204cfe7258e5204cfc7258e5204ede3258e5204edc3258e52004ff7158e5202cfc7158e5226edf3158e5226edc3158e52004ff7058e5200cfe7058e5200cfc7058e521fe7f5058e5226edf3058e52006de3058e5226edc3058e521fede7558e521fedd7558e5226edc7558e52006df7458e52006de7458e52006dd7458e52006dc7458e521fedf5458e521fede5458e521fedd5458e521fedc5458e5204edf7258e5204ede7258e5204edc7258e5204edf5258e5204ede5258e5204edd5258e5204edc5258e5204edf4258e5204ede4258e5204edd4258e5204edc4258e52006df7158e52006de7158e52006dd7158e52006dc7158e521fedf5158e521fede5158e521fedd5158e521fedc5158e52006df4158e52006dc4158e5204edf2158e5204ede2158e5204edd2158e5204edc2158e52006d
  | 41 => 0x5ad7e76d95430247e76d95435bf3f74d95435bf3c74d95435d75f73d95435bf5c73d95435d75f43d95435bf3e43d95435bf3c43d95435bf5c43d95435d73c42d95435bf5f32d95435d73f41d95435bf5c31d95430057d70d95430067e60d95430067c60d95435d73f40d95435bf5f30d95435be7f74d95435d67e74d95435be7d74d95435be7c74d95435be7f73d95435be7e73d95435be7d73d95435be7c73d95435be7f43d95435be7e43d95435be7c43d95430067f72d95430067e72d95430067d72d95430067c72d95435d67f42d95435d67e42d95435d67d42d95435d67c42d95435be7f32d95435be7e32d95435be7d32d95435be7c32d95430067f71d95430067e71d95430067d71d95430067c71d95435d67f41d95435d67e41d95435d67d41d95435d67c41d95435be7f31d95435be7e31d95435be7d31d95435be7c31d95430067f70d95430067e70d95430067d70d95430047d70d95430067c70d95435d67f40d95435d67e40d95435d67d40d95435d67c40d95435be7f30d95435be7e30d95435be7d30d95435be7c30d95430067e20d95430067c20d95430067e10d95430067c10d9543024ff76595432867c65595435c5bf74595435cddf73595435bcff75595430067f75595435c4ff7459543006bf74595432a4ff7359543006df7359543004ff725954304cfc7259543004ff715954302cfc7159543004ff705954300cfe705954300cfc70595432867f50595435bd7e76195432867e76195435bc7e76195435b73e74195435af3d74195435ae7f64195435af5e73195435b75d73195435ae7f63195435b75f43195435af3e43195435af3c43195435af5c43195432876e72195432876d72195435b73c42195435af5f32195432877671195432877571195435b73f41195435af5c31195432877a70195430057d70195432877970195430057970195430067e60195430067c60195435b73f40195435af5f3019543015bc7655143026bc7655143014bc765514301dbf755514301f3f75551430073f6555143026be6555143026bc65551432873c65551430079f7355143015be7355143015bc73551432a79c735514301ebf635514301f9f63551432a79e5355143355bc72551432873f52551432a79f3255143005bf71551432a79c3155143005bf70551432873f50551432a79f305514301ddc7654d43026dc7654d4301cdc7654d43015df7554d430175f7554d430075f6554d43026de6554d43026dc6554d432875c6554d430079f7454d4301dde7454d4301ddc7454d432979c7454d43016df6454d430179f6454d432979e5454d432879d5454d43005df7254d432979c4254d432fddc7154d432875f5154d432979f4154d43005df7054d432875f5054d432979f4054d4304cfe76d89430067f65d89430067c65d8943024fe75d
  | 42 => 0xd70d8d5400cfc70d8d545de7f50d8d542a6dc6358d5404cfe76d895401cfd75d8954024fd74d8954014fe73d8954004fd73d8954014fc73d89545a6ee52d8954586ee42d895402cfe71d8954004fd71d895400cfe70d8954004fd70d895400cfc70d89545a67f50d89542a5de7398954005dd7398954006ef629895404eee6218954006ed621895402cfe76d855401cfd75d8554024fd74d855453ebf54d85545267e54d85545267c54d8554526bc54d8554014fe73d8554004fd73d8554014fc73d8554526bf43d855404cfe72d8554004fd72d855453e7f52d855453ef651d8554526f641d855400cfe70d8554004fd70d855400cfc70d855453e7f50d8554006f7619855402ef66118554006f5611855400cfe76d815429efa60d81540d67f75d815401cfd75d8154024fd74d81540d67e54d81540d67c54d8154014fe73d8154004fd73d8154014fc73d81540d6bf43d815404cfe72d8154004fd72d81544767f52d815402cfe71d8154004fd71d815429e7f50d815429efa50d815429efa40d815429ef8605815401cfe76d9153296be64d9153014fd75d9153296be54d91535e6bd54d9153024fd73d91535c6bf43d915304cfe72d9153004fd72d915302cfe71d9153004fd71d9153296bf41d915300cfe70d9153004fd70d915300cfc70d91535e67f50d9153296bc64591535dddf735915304cfe76d8953014fd75d895301cfe74d8953004fd74d895301cfc74d8953024fd73d895359edf53d89535567e53d89535567c53d8953556dc53d8953556de43d895359eee52d8953556ee32d895302cfe71d8953004fd71d895359e7f51d895300cfe70d8953004fd70d895300cfc70d895359e7f50d8953006ef629895304eee6218953006ed621895302cfe76d8553014fd75d855301cfe74d8553004fd74d855301cfc74d8553024fd73d855304cfe72d8553004fd72d8553536f651d85534f6f631d855300cfe70d8553004fd70d855300cfc70d85535367f50d8553295be7498553005bd7498553006f7619855302ef66118553006f5611855300cfe76d815328efa60d81530ce7f75d8153014fd75d815301cfe74d8153004fd74d815301cfc74d8153024fd73d81530ce7e53d81530ce7c53d81530cede43d815304cfe72d8153004fd72d815302cfe71d8153004fd71d815346e7f51d815328e7f50d815328efa50d815328efa30d815328ef86058153024fe76d95432867e65d95432a4fd75d9543014ff74d9543014fd74d95435d67f54d95435d67d54d954301cff73d954301cfd73d95435be7f53d95435be7d53d954304cfe72d9543004fd72d95432867f52d95432867c52d954302cfe71d9543004fd71d95432867f51d95432867c51d954300cfe70d9543004fd70d954300cfc70d95432867f50d95430067e50d95432867c50d9543
  | 43 => 0x300000000000001003c00300280120004001000c00d0000002000c000002c002002400100080020000000000c00600040020008002000000700100060000000001c01f00680020004017000c003000400c003c00000040040014003000000a0014000002c002000c002000c0030000009000000100000040000001000000a0000001000000600080050000000001c00000000000008000000000f0000000001800000000040008000000400d0000002001800000080010000002001c002000400600300000020000000800a00080000004000000c00000040000010000000000100080000004001000400000000020000002001c00300000010000001000c0010018005002800a004400000140150034000000800000040040014001000400500000000010007001400c00140010000002000400000040000014000000c0000028002002400700000030000001000c000001c0070008000000800300080000000006000000000080000018005001400b0000008000c001000000300180030008002000400400040070008000000000000180050030008000000300000050010000000c0050000003000c00000180010004000001000900000000000001000800300040000018000000400000000000000000001400100000080010001000800100040000010000000800600000010008001000000900000000000001000800000340020000000002400a0000007001c000000000c0000000001c00200080000008007000c00100100010008002000c007000000100000010000000000000400000050034007000400000080030004009000400300200000000000000400a0000000000000000000050000005000c000000000400000010004004001800b0004001002c0010004003000401a00180010000002000400000100040004002000400000000030028002000c0010014000000400100040010000007001c00100040040004001000400000080070000000000800100000020000004000000200000020008005000c006000c0000020000000c008003801f00080010000005002c001000c0050000000004400000000010000014001c002000400b0024003002c00400000040034009001400100140010024000003400000040050034001003000f000400000000050000002000400500000030010000000c0000000005000000400140020008003000c0040010000001c0010000000000000100000000004000001800100a0000000000f00080030008000000000000000030000003000400500000000020000002800100000050008003001c0000008006014fe76d8d542a6de63d8d5401cfd75d8d54024fd74d8d542a6de53d8d542a6de43d8d5404cfe72d8d54004fd72d8d542a6df32d8d5402cfe71d8d54004fd71d8d5400cfe70d8d54004f
  | 44 => 0x8000000c00200000010008001001c00000180000000001001000200000020008006000400800000010000002000c00000080040000002004000a001c007000c00000040000004000001c010000000a00040040004000000c002000400700000160010000003400000040010004001000c00800000000000007001000000100020014000002000000000010018000000400000080030010000000000600000000000000001000900000060004015000c001001400100240030000008000000300180020008005000c00000140020010003000400000040000008000000400a0000000000000a00440000000000000000a0000006001000b000000000100030008001000000000000050008001003c000000c0000078001003400500000000008000003400100040000030001000400000080020020000000000b000000200040000004000000000a001c0000000000000c001000c0030004001002c0040000005001c0120020008000c002001c0010000000000400100080000000004000c0010000000000000300500030000003002c0020004000002c002001c0040010001004400800000030000001000000300000030010001002000000000000028002000000000700010000001000c00300100000004009001c00200080020000000003c000001000100500000000001001000300000080000002001400500040000000000000000000040000050006000800d0000005001800000040000028006000000e00080060000002001c000000000c0024004000000000040000008003004c00000000030010008001001a0000001000800000040010004000000c00b001801e0004000000000400080000000001001c0040030001003c00e0008007000c00700080190004000001800000000000008001001000d0004001000c0000004000001400200040000004002000000300000080020000000c00700180000004001007000000300010000000000000900040010000004000401e00000030000000000000400000010000000001c0020000007000c0010000000000000000100010000000000000500040040000001000000300200040008000003c00500040160004000001400700000000000009000c0070004005000401b000c00500000000000004002c000002400f000c00300180020000019004c005000800100000000000007000000d005c0050000005000400000000000000002000c0000000008001800500000030008003001400100000070004000000c0000008005000000000100030000002001000100000000000004000800600000070004000005c000000000400000020008000001400e00000000004000000000c000400100040010000006000c0070018005002c003001c000000000100000030014010000c00e0008004000c
  | 45 => 0x300080080008000000000c0014005000000000140000004006000000000080020004005001c000001800200080070034000002c00a00000020004001001c00100040000004005000c00000080080018001000800300000050000000000400c00040010000006000000500000000000004001000100080080014001000000000380000000001001800c0000001001c004000400000000020008002001c0010018000001c00200140000000000000c0060008001000c002000c002002400d00000010000000000800200000000000001000c006000000100000000000000001800c0004003000400100000030020000000800300000010018002001800000000080000009000c0000000000000000000000010004007000000e000000100000060004000000c00f0000006000c00f000400200000020030000000800100040070000001000c00c00000040028003000000000040000004005000400000040050018000001400100000020000004000400000000090004004000400100000020004002000c00400180040000002000000200000010004003000400300000000018000003c00200040030004005000c00200000010000002000c0080004001000c00000000140004001000000a000800000200000014000000c001000c00100040000000001002000000140060000003000400000000030018000000001600000060008001001400600040010004000000c000000800000040020014000000c006000c000002400200040080004004002000d00000000028005000800300000000000000001c0040000004001400500200090000009000400000180000000001000000000040070010000000c00000040000008001000800700000000000000000c0010000000001000000000140014000003c000000400000040010000001001c00000080020004003001c001001800100100040024008000801300080020020000000c002000c00300040080004000000c00100080170000007000c0030010003001400a004800c00080010030009001000200000000008001008800e0000014000800f001001d000000400080040000004001000100040060004000000c0000004009001400200380090004000001000100280030004002001400400080000020000001c0000000002000c00000240010000000000400200000010020001000000100080040008008000000100100000004002002400000300000000000000800000000000008000002000000040150010008001000200580050004001000c000000000100340090000000000c0000000002000c002000c00100040000000003002c0010008003000400c0004001000c00500000000000000002c000000400b0000000001000700000000008003000c0010000001000400400140040014009
  | 46 => 0x120008007001400300000000014001009000300100000000000002c002002000300000010004006000400100000000000000000401100000000010000002800400100010030000000000900540010028007001c01f00000010010000000c0000094002000c003000800100040090004000000000100140000000003000c001002000100000010000000000000f001000000000050000005001000100040000000006000400100380010030012001c000000400400000080004000001800000000040004000002800000000040004000003800d000400200000010010000001800000140000004000003000800000000000002002000c0020000000000600040040010004000c00000000000000000000000600540000014001000000100180010008006002801a000000300000000000000002800200200000000008001000100000020008000000c00000080050028000001400400280140008000000c0030018000000000000040050000004000800500000000008003000000100000000000000000c00500040000054006000400100000000000000000c000000000000000000000000000800000240020000004000c0000008000001000000040020004007000000100040010004001000800800140000000005000400000140020000002001c0000004000000000100040010000000000001e0000000000400000040000000002000c0000000002000800400180020004001000000000000000008002001800100080020020007002c00a000000000000050004006001c00500000030038000006c001000400000180010000000000800c000c00400040000000000001800000080000000000001c0000000001000c00200040000008002000000100000010000003000800a000801100000050024003001c006000400300400000000004000c003002000000080000084000000c0000000007001800700000010020001000c00500040010008002001c0000008005001c006000400400000110000008000000d0014000000c0010000000000400600000080000008001000300040040014009000400b00000100004000001c00400000150000007000001c0020000000000f001c0000000000000400400000010000005000c002000000200000030014003000c00000000020000002000400a000000b00040020028008002800000000040020002000c00700080040008000000000d00000010000002000c0040018003000800100040000004002000c0070004002000400c0010000001c001000400000000010014000000000000000000018004000002300040010000004000400900000030000000002400000000000028001000400100000040010000000c00000180000010000002400000140050068001001400100000000040003000
  | 47 => 0x229600007869f600008e20d560001fb607bb26a0af8000000000000000009be80008e7961a0002f7600000009d93378d62000065fab8aada2ceee04b394405362e66e80000000000d31a4be6dc87561dd9190b083868ae223ca61e38d45580000000310c0002a4000000000000000b7fa91800000000000000e2580000000000000000000000000000000000367e0000000000000000023380000000a7303b20000000000010a63e01fe0b3b0b400002045c900000000000cc6364460c092600000000001a4867303e0000000000005321cc00000002c5c00016f473880000000000000000000033ca000000000000006ee2002c9f8a04a4f00002c30000867000074c0f4c64d196e0002c3ebb400004c30000000000023703fc00000002790000000117646980000002878000000044901d8637165c08800d600000008310648c04abc89611cfa05fb2ae00019180000d6e9e7319e12bb1da000000000000000000042000000000000000000000af0b01a00000000000e50000281a94c00000000000ba100000000000000000000011e4000319c000358a05c13c200000008a78b1872c2fea02427f4626249e6582e7a50c9d605a6a3187498398000070e72ba53653d202e60b800018080000002c86070000059c00000059adc000231c9060000a051f4028d8ddeb1410fe58d80007b8a716cdc000095235d8adb252005e32e8b5a1c62653b29c8b8827c2070000a8400000e28000da880006690000a6880002200000c3a20348ca990867b00006e9098c3ef175697f94bc000000000000000000d7052a2dc0000330e00000002808000000000024babf20932b9c62c8316a7a002c620a3ee26c0000000000056580006748760ae100000d583f66c480004cb0d8abfdb3900002b300002314d1a1e6c0000f2e972a5ce000000000014dc00000000002ab6301947a26f13f836780008a0800000014960000000e35800000009e200033fa74a800014f800000000000000000000000000000004979bd00000fe4638037acdd04204f8011027d2c4e23f20c8640000000000000008001002800300000000000001001800000240050000003000000000000000000002000400a001c0000000004000000300000020000000002c001004c0010004004002800700180020000004000800200380010024002002000000040000000000000c00100040050004003000800300000010008002000000500000000018002000001b00040040000000000c001001c00200040000000000000000000000000000000000000600100000008001000402700000030000001000000e000c0000008000002c000000c0010034000000000000980010004000000400200000000000002000400d000000800140000000001000c0020010001001000900080000000001001400
  | 48 => 0xe6999b5d00000efc0000000cd003e65d0a75000000000001cd85f89100e3e800001d8000000000000000000000000408859a5060000ad928700000cca10d9bbcb1fa2d6a5d1daa483186ea391f24de49a78883a77024115c0a2580000e4071695f8000000198e0000000000000053f000033521e4bf38000a1b826cb31800000026a23259f3e0000000c5136b600000009fe00005b3295c354893297b8000057ab7a6c8a7563e18000b6882144bb31d68831fac2df0000831926416292d60002c82cffac0c000000000000000003172000000089d0cf0000100abc880006c0000056280000001b1e000000000c00000002ac8cf08000e301f32559800009711ca03115de83e121c91d12260000000a0fa420330111c36d800047b9b540000000a5086b800033dc0000000000139e055a1d65768000d4f800000000000000000000000000032081728d200001f1e0001ff471309d031a00000000e94a791b387e180000002ef2000091c0000000c9b8000ce200000000000000000000000000000bdc881a030cec36c2b619c6a4c607345168d3819b16f0ca5000000000000000fac0002d9ec438000848b76ab43b4a49f6b2c09fb23b83e5000011000008f69884c1131a88c4000000036f0c26800030a9164000273e708818624800000001b3c000000000028a6000000033aa0a40001df64dc92c0d42800018a800000008824120998ab78f34bc6800000026d0000021628a0a1e00000009a3013200d1574000152249cb1fc1308b3200021b644d80006eb1f5400020a8424248e8ae9b42000333285209ce72894e285c8000000012e0000c7a4a0a4fa8e19eac32eb8a80000000000000000016a864b8000052254a2c820847941ace17e000000034b6d9b0b129d1b4cc0000000000000000000000001804bbf223081312800d836924e981f8dfc1700b1ea00a3972b8c862931ebac1dbe0bf26ee059323e00030fca079c0200028bab0b9a9628630700000000cf8092a19eabd26f780ee0003254e33a7c666700002c186f8c7c000000000003c4b6ba00000000000000000000003400000720ceebd5a2b2d01a1a2303a96000fb4eec62b06e0001984000030abf29b4e6d22d50b6b800000036582bab196b6999243788c3800000004f60000c7e0000000307400000000001e46897166800026d4000052058103ee52c201e00010849a6889a85592a89d28750d8780001d6b77c6d938aa9aab83ab732b94bee0d3000001a84098070a3233c07b1a1fe1f000b8455982882fa31a4ab144600010ec85180000000000c1a1f067ca000080f000092100000282a7a0000000000000000000000000000e0610522648528d15366a0000000df3800099c835e33c8d1c88ea8d40ef8516c000e9000000000000000a8ab06c0000f3ab5900004a800001e7076c00
  | 49 => 0x48000000000001a000000000000000000c6a81d200000800000000255b70a00009a60000a6c000000002d000033f000000005a000037b657f1cded99ab98de300000000000c611bd6c8d8000000359e00000001d89cbcbd3afbccce1ef647cab122030000a358bd0d6000000002d1a78f391c00016aabc2057e9ed00006088742150a0dee2d893470f0000000075400000008df96240000000000000000000000002aeade23436a469f925b38e921a9001e000000015caf520000000aed0ab80000000000000000000006ab21c6e559ca65c0800099b000054ba3160000000db61c3a27a00000000000000338a000327a0ab00000000000000000000000000000ea83f800000002f1c0000e5ebc780000000000000244ab2db60e00000008f59f5c3478aca103800037524e880100c65e30000000145800008a800016fc3c580000000792c37910800012f400000008a3800023b90460002f1400000005a71bc200000000000000000354800031d2c3711407af10b8e1000fac2a191213133d03ea3846bde1bea570982cb5e0be63f7aa48731a4648848000a9c80ea1ba04424e3a690105ae9a11b98da2a69f9a74f03fe0001464d94135a00000000000000796000000000000000000a4a0e4642d9ce80000b24000000074580002d3800000027acde7056e8dca5f2a80b9300482c7ca5eac522831d20d2f1d5a163980240b05f462222220001a66bfa0000b7880e20e500007b80518618000000000000000000700000044f000049a0e607f788d22a38a52e3217d653300004c900001c2a1980000c22000000098814ce78c0000000000000000005a22014000375ec5aa4b4a5307643ee800000000000000000040102a00027dcbb60c28000173aa20916029a0000000000000000002038f00ddda2b60002d84000375a00021ae81db7e00002576a4aa77600000000cb000000000000000000922abea652b3960000000b5895b0000000058a0000687a54083a0b8e1f800005c98f320000000000000000029ec92ba0ee00027826739dfa00020947f90bb60001824cdf2a20c3000005f6861800000006f8000039b8000685034a3fa8000000000000034800001db2000000000035ac804b8ea9ea0000dd3000097db13ac3aa7ee5011d6eb8b8000a9c030400000000000000a6202667932216000000082307f26342812000272e00000005f71dc2c07a6f40000014bc2800043a2dba00004b443b9bca00014c8ac5000000025b0c1a800000009fc0000000590979e000000078200000000cb63c814560000626000000000016442ca8000000000000000008f50c0c1290000000000000000001e380000000000000314a5cd852a79506da3bc8000d2a0000cec80009ab800054400000003192bea8000bb51a4ad29b160000242600000009ab000054480
  | 50 => 0x96c80000002a060002b8e00016d855c067ca788000000055a0000000c69109200000000000000b622be2e34000000000000001b66000000000000c20000000000000000015f00000f9a00000007dc0000000189a3b98000cb6149a25e0ce0e3b00000002f82000390a000000051d800000000000000000000354a9828000000384ce4a84080002522e0d917e7b59cd45af199e069204a51280000000b7200000004bc87ac00012b2c2205c00000000000000000000000e72f2a6b48000000000000000001e2000019d893ee56054058420e00001594a018000b07b8086dd0000c458f4400004ac2fa2b38d568fee26ca7060cd8000000308455411fe0003476000000000000006a100000000000c4b8000e4a000098ba3a08638000000141e27603088c1189ec92800000000e8b029368b0c99f6581a78400036fea6b800054700006b81fc200000f800000000001d5c47b1c0a00000003c717de66a2de43b3339e36aa3b42be1c60000218400003c8ac1ad02000057a69380000000000000106cd7f9e78818b2062faaae85dfb4aa8af80000412e78977347081b365e55538145cc9f66a27000044a054800000ae00036f4db3a02cdc580004ec80005d00b34000143ea0aa00c0000000000000000012928a11ed2000162c6f1a0522ea1dde00000004961166d222bfc11632ac02597764172f5c7578a6e00000000000000b7980000002992a52800000038a263f14f200000008d614c00000bcea288ba48b7260c1d20000d8e2c22000000081e800054d80000002e226c28000dd094d800032145e4916e0002ad271e33f4547826ee3d05760001f5ed7a2512000000000014fe00002e8073298040c9c2ca3eb2a000036e60ba9be2000013e06d1006922000064fa35e742321c26eace4bf6000000000000002578b51a7e841c80000002d3a0001fa0000046aab5965acb08000d6d000000006e29c800000000000af6ae5cac880001ec80000002ba85b79a54bc30000b48a7f045331828ea8000233127a0da17a0b3e19e46f2191edcc000013fae9800000000002ff4aed8504d50000000000000002f046e3000000000000e233a651f8dca0001cea2fd2544a3f12144d8b614a9f000000003f295d01900000000b52a6f0000000000000000000cfe41a00004ba00000ef276a00019d4000000020180000000000abd8f74942000000007ee00000000000d740c800005f900004f78000000000075e380a13890dc000102400026e00000000000000000000000001ff60000000b7d00003d50d54000000017b816e46ea3ea8db800042f2a1a20000000c89ff85a88e1c000163413811aa0000000c1614a076d2fc20000d621f7a7b0622ad720000000955b7e6dd996ec89b0000c651e724dd80009d98000ad20000000167c6c500005
  | 51 => 0x7acae0200009a82dd800000026d6000000000018ce00024da00000001b6027e00023dcc499e860001182d6a9b863de9168e1d8000b6aa582de60a3a17a00007ce8000a010000a8b3170c2e8000ad78e240be209c247b7b2ada84c0e38011e000000055eb88c00000006b601dcd9599a2cbb098092338729cc35c280e1a7a28500009e89e1a96700005eab4a23c3991ad4021323f08c8a3a6054cd1aa9f8cb3325079691d467017a800029440001a8ee43044ea55367256b10b275f80001641f007d19648beba0e495e9c9017980007ab88a479590cc10f242800031c2c9030920000afa933b79e6df928490fb03400012c4000370c0000000000000000000003f21ec00000000628800000037f44d200e4b302838045800000000006801998aec04f0ca223fe7d8b7c49c71ab25000a50000354c0000000bb58e280f40000101b48cb0b26820000000000318cb659b027c5aad021c2a7e654b380b5609460003412d7b8000afa17f09f9000070595080002a16082a1acd320cb4d71b624000000000000000000000000000000000000000000000238e00016e68d88000000000074a1c824059dd27e138b86dba8fe00000003a10e1600000000708e7200000001b91d98ccf0000000000000000001a8364000000000002fb23591f08bc99786c8b03e80000000000098851aacd66489ae2000000000000007b280003e6313699285f200030a216f886457c8364000308024b188e000000000007700001abe00019e00000d8283c24de0f329fc00031bce0783340000000cfc0000d3d8000000000000000003ed00000000000d1c80002641e9a000234a5408000c3c22b4000000035607ec00013d65018000000022e783b32485b8cd0181a3520000000b3380000000000a80000000026a00000000adc8bfae178cf84903278aca887a789800010e0f360000b0e168b8fea8937d0094a98c6909fd600033640e6981600000000001494d6330480000000df318fa1dfa80a8651ed0975395c1e806c89240e04000336e0002fa8000000070780000002e740003072441a60e000000000013f6c51920443980000000eb200016f60001f0e6ada6bc462045ca8380002d11bfc000000000000a277b29624bf80000000000000000000032f6cd62aaa6858ccc0000c189bf9e3e0003306bcd239800000000001f2024e80000001e0c0003674b8028f24cc9e6020e234c08f286abd41ca41780f2a7e99b807ff20aa00018a0484823ee00380648d0f02830aaaecd800000002f7cdb928d08800000000380cb9185c48669da25d293ac000000012c94aa182b28e00006820002e1600000001a62c8a54e000061d96f8c6c98d88178a6a0001bb2d4c800000000000000000c350000451800043180000ea0000083800005a80009af800000000000001a8a0000
  | 52 => 0xb2fa0000000000232c7e39200222155c0002a040000000c8586167b508b424c361c00035b6000369a751042400000002a9a970d1ba18c000055e4f4af400001e8850e80001001c7200000000001ef09ffa6120db05fab4d082072389c20000000d4e925ce2fa4ec612993a34580009790818000137aa5e000000037d6183847aa7500008b111740952ad80000000000000000008320000d34d421010e378000bb3140800017841ed258a00000001cd89768300e7a9fc92dadbda3acbe8b32219f905017aaa96a0b84f400000000000000c5080009072eacb44a0a04fc000000000000000000a18800046d9bbe37d000014b98ba00830f6d949acc3f19aea45c00002988de8ac787ea000000000000000000426000000000000000000000488ae5486e80000000000df0000000000000003728acd177a0000000000000000036623db002e000095800017180001bee4711e4400031f612a8000314a62266d000097c0e2e1b3895a00027787c70284000034c1f69acadc804225d984988d1108ae348000000000000000005918000a561d34000367c0000000000000094f07cea17854e000000000022fa0000000ac91e8a509a54e51e2e803801c4a2b1181c0e315300000000000000000000007a709706320000722b71e0003082000000000000002388df29d323c4bfe000000000005d48000000000091b2b18e0908b881ab0f4a4b98660000fb64e880000002732ad1800000004fc89c800062d80000002618000000000000000000000000000000000000000bda1590a4c03515720000000a369a10de100000000c6000000002d60ed0682b736acb8d7e5b2a07c9033616c9880002cf1004000000000000000003046869b91200008262f1b2b68508000dcf211a00031480001920867950e982014203c8000db119dac568000bab80000dcafb6000303877d237c46f000016b9940c14a4f215d1e4813a33ba60022e800000000001d3e00007b6b0580002952a64b74a9ba00030bc44c035800000000001aa600000000a6800000000000000000c8d0002df6b1300000bd698ca89e5d91614adfb352000072800020d61b2b44aa9880000001f22b278a5c8d1b86e0c39f383a2a8f622b35b80000000249178e0002846000000087300003b1aa38d61084c00020ac47e1b2489da06e64a00005d700d8000000000010f800004ec00031ce882324ce5b174c00018ee0000000cf191c6d180c30e458064a2bad5260f2cb0e0fb59a7da1c76a2ab5de2ff95e0da52e8a51b362200025fc7de14a233a2116b0f1a985ed296a9949762a49000000001e2c5714609859cb87658c9024414d0000015a2d4b4aeaf8000070b903c3b08000bc410f20000000000000000000007768000d3a21d004388deb5238dc000094219c800076300000a580002bb2704dd60000
  | 53 => 0xace91678e20000000037f2cf7b25800024e0000000000000000000000a0f000000011a2818000000000000001fb40000000000110c3a2175873fa79aa09b602000000000004624a3000043880001368df6c1f00000001a5275c31a6000284e00000002848f66aafad38b0c243a6f6b5a86d8800097980009410dc600000000000000000049cdea9dd4159ae522ba2a9293a800016600000000000000000000000004639de400031805c48000d7134da454a2d233d2fd400022c841e8000b7eb4180002370c799490772a026a712c285d12e1c73900008a9800000006600003510c3b8000258000089a1354ba400ac00029ca1249e18000140e79a26960001308000000000004840000e64abd0000491800000006fc000318e0002bd60000000a2307bc1f13222b192434000268400003c403700000000000000000044e8e7e43daae43ba933a0000fa6ae89e3893bad60c6db1b47370000ad5aba039c000063880000000000000000000000000000ba200000000002f389630000000390000000004d98000d691a32de0b6340002c6e99e86d62a027d26d801265ba89388501b9049c172c053af983c31d127c2b1debe20b6ab3e800031b80009b4b910412a4fe7ad8000ca180002e70000000000037f800000000005188d72966255c5221c3000000001758000000000000000000002c70000000000003ec0be80006ed000000037c2c7bb5d2e208570bad0000ad0246e00000005b537482a2ae34ad71d50000221c00014b80001b3492cae260001d0c000276c000000083480000000000d3e80004208000ceb2f7e05e80009cb072000032280263356e390000000000000007caa7721daa31b2f200000000eb800000018d400033d6000296400019460001a889c2800029cb410000000000000008560000c9b0000494800000000000001518bd9800076f00000001c04c6b0000bcbb0c80f69c9453994c200000000d700000002db400000000002b8600000005a6000000000008bd80000000000af2af6437695aeb1588fe3222254b830baa19bb4904fea2b8cbf15b6ac0a898c7aa558833362abe51f105381c66d4a118a7452f0e2e2a99c123b91edc08d3aa38279862f0000324a968261b4e23e70c1aa483636000000074713ae4cf962600000000c01f949d505080001ab0e3280007618b563632e508fa18266f0140245e38ac00000007082d760f7a220a9d8000000000031f8000c669fb00000000000000012989fa00000006860efe48900000000000000363000000000000000000000000e2328974923000013aa00000003238000000000000000000000ef443d1d38c4681fa6e7add00741340000305a46f985a835235400026f64a2849489a8000d3c9fa4000000034aa9a4000146800000000000000323000070c80003eca9ce6a01e2ebf1
  | 54 => 0xa315e0002478e1500000001dae19702f200015bcc3e80000000000394800000037ae58f277e0003864d4300000000cfa00016d669d2d5a000232e10cb688c48824e96f029cac6aa32000000059019bc7fe9208d99129a20a112e000230a00000de000000089b80003da80007a80000000296ccefa64238e38f8d250cd600003a4d7585ec79f80000000000000000000000007cf131434f9cca61e91100001734d450994ddea52ae4b00605c595fe01b1c7000000240001eea86831e0e05b9027172b5800000000000000000000000000005fa00007bf0c9acb8800000000000000000000000000000000002e688bd0fd086a80008f900008408000a9b0f26c76000084907184b414721820000d4631ca000233ad918a1c16d800098f1f7a8571d2c0000000641894eaa700005b880007100000ca90000e1a8000000136a0000000cba80000c0b682521800061f0d4a21100000000000583907073023a2e530000363800086400006b9b8d8b4d800000a00008fd80002fc8000cdb00000001e4006c17ba9e03096caa00185980a7671b00004020000000000044fb3fc0000bb4a4e00006bbb3a814d89c005295ced822cfc0bf80000000000dfa8000992000000000000000000e0080000000000b2d2390e5aabac00018061ee80006eaa2480000c5caf3b88e75d8f6036c80009981a626900000b7c88bc0000000bf88f725532480a0329325a516c673125700000242000396663c2e9c3fd954e59b00006fd20e65f3b52e04e00000000000a5d800018da1de00028603be800000020b82d1a01c475a76849880006f70000c9f2752d7e24acde91038ac0177082c00000002c6ad768000801a6108ef1b8a04a29e6aef805253bb0944d43422436082accf8000000204e6fd832869bb5ca31196a0c7b35a2d340268194816229faf8406638cc049011cda2a5ec64f2a308750b3800000006d32900000000025a075e000000003f37687f886680001e843b100000000000000000087c80000000000000256200018920000000b37000083fb34c00000000000d7c0001c92000047e00038ee000093cbd280000002fd600000000002eb23408000bfb944e0001cd00000000000138ab0700001ef80000000cce9de8e0a000000068081ec31528c47ac00003d3aeea00000000000e32000033a58facba8b68d6a0001e9e00002806cb00000002bfe0000000000317cd6f94f6000329200000000000000de500000000000000000047800000002dfca6c17fcc29800000002e4c6e9192d15b89a5108000cf6b2684910000bb3800001b91802af8000000064600000008b90000a82a48296880001cf252800000002fc0000024800036e8000022360a9e18000000238a55a0b904c08ffc000000066000001c8813c9d680006e819f87fc2ec08f20950365a55a1b72e6
  | 55 => 0xcc58000ae48000bbc0d2c76a26ea00000000003772b690b8c95403240002f8c0000000a6b2e0a3452b04b99000019d10beb57390658a8b029fdb37e6e9800065980000000000e46066a0002b2600015800001d4c000000085a80005f807fa00000000002ddc000000000300000002042d328e82ca6b4b8a539a263a0136e6cc1d6c5961abc50e229cc5f88f60003326b7c0000000041050b000000000000000b6c000098a05c800032c2de840d2f8ed5800005b90000000000076c00002f300000000a56a39800000000002ab00000002828000000038b302620f0ba62d723a641f2952000116a6f4aa4c4ae03b40001b067d4a108a8d82b48948c7c51b8d9c871089222c1060754b404794800000000000000a86a7839440b52f204a3800038f18640b482ee0000000003acea21898404ad07dc46c2534466129c7762cd274100008bc92ee6be1d4659423808fc9944b75a32006e16baae98000abeb63c76124d6d92007e00020868c080000002e3600033c40000000000000013634b0bb202c69332b740000000000000000014d6b960e6cdd800004b380001b4b45c000000000000009400000246b4fc0002d800000000ad40bb800021b000008cee2f2a3e000000000000000001bd86140000000000000020f600003920d413b0000300200000000000000000000026f8c040000000926800065e800000022d81adb8f61232986000000003f80003e397040001c8000000001b9aaac00023d28090000ae5a0ca31c00002240d3200000004f980000002ee0ba1b8c600026b000010f056221fc902a41e0000000764927800035963022efe00000000002c360e5ae08c0f048a0001562635b5dc0000000000000000012d80002d20522b2186a782285051b086f300000000000000217c973153c0b33060ad800000002d1e000063a92f000004a80000000000cac00000002a8600028343709df20271e6a000124c2b0062807f1eb87f9af06b198fcec970966000097290119c6af334e40000704000000052491c0b57983658600005f99a6cdb03796a471bba943350400000000001d2e00010a60000000deb37064f1aea8b360000b06b1e2000000000000000003458949800012e8ade2c11e3a0002d16000000069680ba00035380000dc09a735261df01767972ede792abf0d4801f467236c6000045ace100002f909a0de1b3ec4b98000d6c085cb23b7d86d180000000000000000045f1f82886105a00037a0caa8000c038000b37a050000000000000005c7357602cb5f65bc999a422111611c1c5ea2c9dcc6590f9e0a4287a11419329e500000002bb2b6f99e20000f68756230e61c00002431a220001498000369e0002de006f9b0e04e80000002f3e0002d4e0001e828890b7884b000000000000000632000217600027de0000c3491
  | 56 => 0x5500000000000107400020666ae000000006fe0002c588cd1b68514835454c8000a87b3ce1de09de7ef8b1615b30989f20000905b57e4a88a7cdd19b401880c82304b61a7e00000000205676e800000000000002c4a000010231000c87462fc0000000049b80000001b70b6cafba00000000001d3200033ae000000000004d6561a2d00003764188a1804e41da487b2f4476736b87850e400002a46695a68030e8568afb800055680000000996946277c904b71880ca56aa19ae12b17857ce0734babd52b6e4238000531b94a605080a12c00004a900000000000ad480000df01d40001036945a454baa86c2a4b088ee1d2ce233632e600000000002aee0001730d6c81bc0000000379a112873a4fc48b9544d189656c84b1f286d1b5c0000d1800026b453100003b6aba400024a2a7b800023a03d6ce4a6e28541ccc000078cb40000000031be0000c4cc7f9e42d338000092948253933f8aaf05dad7380000b100006030000000019687aa4d8da700000000c1c480800037f0dd0000369851300004438000e012d545fe00000002294000242200000000000000000000000000000003270c0b80002d800000000eb8a8d0000305014025e800000022e00002f6c000000021d00004e9326400000009c4800000000000000f5698a800000000000001c540000000000000011b0000c17800000014164190000000000000000006e880008a40000000000000028dcd5e000056400000002b16b909d9e2bc96840000bd40000000dab259a0ad8144726000000011f45a38000a100000865a47600000000000816b4fa668000000084283ce0000f7e0000000d2f8000204000000030ac02383d43eb8c0a0000000e57b82ec4b0000427104e4ef1af00000000000130612400002a903869ca34d40000000b2215f66a18000000000000030d80000000827800000000000feb72c000000000026242720000617b27416989180001fe01dc8000699000050c00007bb8708cb58b84bdaa908216001c31db690e0b05527a309ea84b870009a85fc56f8000000000069604460001f5600013be9b901a05dcaffe7c10000000161c00000000000000200aaa600037d25ef97b6063095c0001d220a6000000000728878b140000000000000084780000001728000368e4e6800000000006aa38ae00029500003210c5d8000daf0000000365c000047c0000000d2d00000000000000354eb5c175051c31fa85986c6000000000000000000000b8c872a0002a520000d94dcd2a5890a800000004b6269075210a80009eb800000004f8000000000035c052d9b56cd980009bf00da3a198aa1f50d3c0002b1c8d980009869384000000000032b200000009e300000002b320002e7c2ca000000000007e20b64912389c6f11266dc8913878a09520002ccc0001788cfd80
  | 57 => 0x7140000610bb8800000036dc00008a29a29f8a14ea6e872681f24d79e02be92e142328c6a068800000010c20000000d9d80008440000da98e6ae311dfc7aea588911a44ce540f240000000062850ccfa28b49f127b25b129b46729d0046925b4081b0aae12805e00008da0000000e1f0f9000037b027b8aaa78d25d600000000001fc8adc349a0000ee800017966df00000002ac6d41b150bf4940a0000000000000000018fed45a1f6a959cba4352330739b7787c3259052027383d69b26dbe8e0e6d1195888418425eba7c0bb497c4d5b00002f60d980001832016157c9b02ef800014369468da00001664000000000000000000000000000000029d800015e60000000b2b8000d3b00000000ebe0001250725996a0000000befb8ba7052c4000000002a882607cdb3d868813160792baed6ba7b6000311400000000000a42000000082d06b032a86ac8e123080000000000121a00038f200000000000000000036e00023c20550000d2b2068000000031780000000e56c3b2e480c1a20453b0000788ab4e9fe8bec0000000319221ac75176800016e08a33440b64a9302f2aab2e08aeb84ed887603d9dc6b0e09c400015cc00000004f38f2c5a5ae186378000736901e0000a26e081cf2d312b3e00024500eb0000000182ad930c48000000000000000000a46593800000018c69f386f42ef800091c8000e280000d4d000000000000002cd4cef2d3c00000000002ea49778184000007cbbd0000000000058e0000e1b000000006963b60000d722580af98000000218600e80006f98000d25acb2b0e8db400029d65088000947031a2420c742f80584ad8a300504011a021000000000000002f80000000000000000000e8e0000000000073e997800010780000000bc4000000000034740ae0428373a74286f86d019c150cc192a3a57592980a2886e457295e0002010000000000000cc26e2cf00518854a302fdc969ad9ce52139ca30856242616765e6a93e50b8ab4000000066da760310a6f8cbd125a1738270325000099000000001c0600000008aa1c100898000000256686e336a0153336a2c1ad600000000000dfa00000001ec0000000312000019020c41148c29322a00021caba3800000038700000a4895480004df800020689a21a200001658000a170000000000000000000002f245a480004cc2ca61aa800000014a4000000000028a400020f2564a66e0003878a4e8000b9cac727f28d5c902186cbcf268e1ae80007cd0bee00000000000000ae400001750486000000000000001a29996a3a000010d0000713b166235b9347be80006e224d425a800086a00003d1919c000075843f000068e8a846ae8000000000000006a6c040200000284a00005c802f06faa20000072b0a78ad680000000dbeb1d80000000000d5b800000018e60
  | 58 => 0x9d43298000000253a25d189c6310000000000000031a022f9b181f4b8c2288381a00025b800035309a234b200037d401680000001094a9d12d20a527d08fc1d68000163aa69ad1c14e0aba00003f024587943dc0dc4645851e00007d090f0000ab980009b1a6ec00013282b20000179375c000049a2fe0cec00033200001aaa00000006c6909600000003d61ea6000000091fa08e0000000b0a80000000000b24a99e99123b6c21b7523fa1f445e029364959558000360c5068d48000126043480567b22ff2e0c9dc00a48000b6e00000003866c1000009491ed80001d7c0002b0c2552df800032820000000df2966a9cea26658780002cc35ea93e27be117a9100000000beb2098bbb171a643b8a443595269e98000299a4987fcb6860000000bc58000e112ce897680000001d8060eaf0000000000000000000000064124ca0002a5e00028220001058000000000009acd17919ecb700001a1800005b2e1074e80000000000a2f0000293aaf8d7891eac231d06d5190de1320d7aca98c260a79afaa61263e7ef11a02b80c2c1d134f030c87240c7912ccb21ac0b6500004a4374e0000000000383c3688db85d83920d9a000016c34e00000000dc90a4066ab3542c01cb460280000000000e4e96fac0531a29a7984ec561424c2db23ac5a01b688f96a62401dce5459ea837615400d000004c424e2b70b65aa0d869000033509c6000004600000000000000000067ab32e384800000000000000000000000000000000c7000000027360000000313b20200000002c70000000396200016fe0002f2847680000000000000000000000001a32d105f62104000235000038b448f15280f723e600019c400013b40000000000368062f8c24000000096dafc8a899f4e0000000386b2b87b30000c3127e000000000000000dad1e0435100005ff80001400000000321e0000000000370400000009960bba0001992000000081c000000025e20958f10000305c00025f4000114e9898000e3a00003392996c771b960001deaa131fd80000000b4b0000b8f1794a7407d6a21b6e2000189400000000000000000009400000000000000000000050a1da6d038000d283400e0e2286000298a08302da2730cc8000033e0120b5eda833b89c2070c4f8af9c85c24028909808c198166c4d1a3e5d1905672a000088b987e000106ab8a8ada000000000005a40002ac4ac28000583037e1c7ad7abe80000e5901687ea800000000000002d281dd0000098800000000005db317800000000001d489db9f7207a2b425feb64a0000000cad2dd89cd12102829c1828cb6b091595420000000a22800000017380001322b020da825100000000000a1680000000000c3e00000003368000000016e2090c228000000000000000008e688f89c68d06a93a9563f680000001
  | 59 => 0x16a80004d2800000000000000de0dee1a902e638da0000dcc9d11bce000290c7ad1818020b204cb49c2400027aae16b43a8cf0000c4e14b284500000000000662a52c0002bc076e22021651b3e0002816da58c9e00000004652dac000000066300004ee0000898185856904568058000c0c00000002b4a2a7b3ee0eaaf12b2a8000000099a541a022819129e000344e0001c0894519fcdbe0a24000000000000003899524aad000000023cc000349800000000000684000000000000000000f849f989ec69caf920000000000264e00000006c837a6862100cdce152a9b28272a6a0e48cc41172000000083f02180002cc4a97210e6a70000d12000000000002d680004612dc400000003ce00000002a44c5300000cc8000000000000015a0000291e5e08c624dc00007e70000d0c0000afb00003be124a0570faa000000049d0eae00023569c7800077e210c00008aa16ca5e80000000000325232f214e2d3000063c80743401d425db800014380000000314b750000c4200000000000000023600000000018000000000000013a811518ec0000000000000000023d800008ea00000007c9a1f80000fd8a7d0000bd219ae2528000492038415e00000002b7c0000000000327639e278a6de0000000000000000000000d0c000311c6e122a4ca888f26ec1030000289a000353c19011f6d028d2400030c20e00000000000053500000002360dd280000000000649828c0000000b038000217800054808c00000f6418d2604c1594489a484d0000243600000000002cc8000267e0000000e188000101126ac6c000000020740000836ced8000bd302761a89b36000000099d0000e2997a44063304bdc0d04ce39ef4c01a0f488f04c676b25c43602a8424d8daeb29000000005580001d622ac0000391269844a8b625f09ea40d9888414c22c2164800072a9706c4035f00000e2080a8000e4202ec0000824ad10b82000205c0000f1a00000001ab800032ba5ea440b28c0ca8000838949e733a51ede01d24348b482000253ecc6972a16b046871202386579b7a62c046000032fe000254c00030282c7800060d000083b28ec752800000035f40000000816b23c6bb2ad44009228baf2dda2db9d661bd897e6b438b2002adeed278c36e228000112b6048b9944400037dc0000000cfc9b329f580001770000000266a8de95c4bf1000004c000000028000001de800000000000000000120a94b8ec877200000001c0c00000009e792ba7b080001d98000000000000029269a52e1a00000003f51d540000cb81449b5e089281c2cb2e28b2a00a45b0a47c0000010c388000542b428df19ddc14f0000000230c06984bc6d400000000a440000b864320480284320c0000000d1e800000016ac00001f60000000000099c0ab80007c69f9012f94fa
  | 60 => 0xdf200ca03d385828d00000000000000283068195d02cb808604305d2243ae40134964a25f22145b49f9ebcca2bc6ce945ce4c934c000000092d8000c4f07f000023fa000261ea982092a41878a00007320000000c31800018480001d386ee42800000000000000190a000000062180000ac19826232ca249b34460f093ea20b80005998f8a09e36ca3001012853335e05f27fc18786f28ec97c6b369a0e0769ca00001cf8d552192449986aca62e4a4e500004bf0000195064a1068df000016b20001e5e00000008db0c98000233ea2400000001d8e0002636a638000dc68000ace8000aa400000000000c740c7225b25a467e96120000f520000000b6311e6c89ae040000000de880008f780000000000000000000000007f5158c63300005cbb0b8000075c0002096c1080000000000d81861c275a3ae5b6a972cdea1e0d5909da0002d7e00008e490380007409fee2c98000981b0cc9650cf66328b3adbb2ab031400003a896089590d28dff80003c786b4000000084f00001890000ce68000228333a00000007f000002960000561000000000000000a381da0a98634acec2d0a8f8bd7847873c21c277414accc7000000000000002dc63a791589618000000063e00000006910fc40002e0e2aa195cba59e069c41fda56792fab040fa2bcd96804cd1ceeb969346000040268c00005d780000000000d951ebeb2f8ff4018acc296ba7968bb28ce0000714000000038336da7f3868000000000001c520cb80000000000cd0800080000008d9019c000180ec1da9b69341a28aa5000065c800088c98a8cd237541b80000c2793608f88000cb82a4200035fc000008cb9f840a4b28472b2b32ba0d0aa8c61487962eb0000000167a000000000000007071d10c443572000004052d077a2acb1e87b680007e610760002e9eb5129461c424141ff00004e0a506d68384800033d2a7002109f500005978000b1230da00000008f1a0a68548acea86062c3b900001d00c16000212a71a0ba000000000000000816337200012e000013c8a03800092a191c0f60f0a2e680000d231b80000000000000000005f600028583498000307a8a0000000000000006fe00000000000655a0365f331c056e90b0654275e478800000000000000000997000067c1da07880000000121688b04e600000005a0ae4400002dc0bd1e32439241a00007fe000000000015a6000000028f098400026b68da00000000000b9da29a3bb200884c2c600000840000213400000002199232c3ca1b273584ee4509ac49ae301c00020a2000000039a00004f911b2b3980000000000a38aafec4180000900ede7ba29aa43400009bc837042e800000000001830f28ba5000000000000000000bf80000000261c37b00000001d3679d23ec000000000020ced0980000000000e24a888721
  | 61 => 0x904000001980001bb00008748000000000000026c20000000000000000031866d480009308000000000000000000000b88000050201ab38618e13fc0ee00000b2b24e7d600000003512d8e9e7c57a15aa5c3994c000302ccb41a7c00025d0be2968c62599dc39395d4c5500a60000000687329e199b16ee17362cc891a9a2141aa48d22aa4defb52a32b0000be79d6a000356600010acdc200009390000000207e0000000a10ad2a38600001e680003fe00000002e7000000006f9000000013fe96810ae0e8800000026868ac0c66ad300002e59d82000160000000003d0aa9845e8886b6db4ea2bb80000000000cb90000dea00000003302000341453a150459889628ab1b76a830000000363200000003ac225ebbe8000387a8ee0f1b95aa8a010800008347ea00000001cf40000b4a0001f12957aeb6486108c420217e0003568dba2894000287e00019fe1511dee0fd09c6532971e5ba02c8c39afa600016ee7b99b2ac34abd4000000085e0000000203ed479086d1b00360002bb800000000000a2a1e901b200000000002fe6000155e00000007230000a3c000000015ec41b8000d370000b410fc0337170800000000000000000328a00000000000000000042c000383491804dc00000006bd000053e2b28c4900000000000000127c21a802a0000b1a16180000000000000000000022aa00026a408d000000000002318000dbf30d00a98ffa0f480006bc8000a090000000000000012d45ae376e08e8000dc983440001e762ef05d000011d804880006110000000000008c800067580000000000000000000000000000000daf9a4c0a09bec0e98e5a4338ff27bfacfee0ab7ba5c415985ef242cbdd0bd28e300d20ec2f627aa800069c03ea0000000292b4d2000222683608600000000925aa9a01e8000a722994000034e5da8000191000000000008b017545f03432ab02106000132e000135807a800096a0000000384e000053489e000021cae6e7bca4c8d5f00001708000000000017c0a2c7b93712b430a5e46baa78c7932f800000002af082cab80790321098ed0d2cbcda300004fca2cc00000000001b160003700ba08000afe0ad63e220b6db4a65400000000002c461af91e82ff00003ef80000d68d4e3809ede0000000a1900000000000267800032c983835780003fc33e6334b35ad24b050000213e55e34089c01398a850fb8be5949c000224e000000000029c236686cc727b07e03b2336d00860423612c20b029340001748e2c0000d609f646a5033800032c64cd81cecafa4f45b20554cc02c9477c17203ad165455b8b4068e28ac000000000018ea0000000000000000000007b122cac0901ae730aca0d0720eadef0000330a722dfb80000002ab80000000000153a00000000542234000000066e000000021e80000a7
  | 62 => 0x61a00025ba000000000024c4017220a7b7257200019389e2000000000000000000000000000000001f600005aba4580000000000104091c025ea7d800025302446e518f669f9874b26a5ac9cf25aa09ea792af90f303e91fd000013f40001564820800000000003ec26da00000000001028daa8000d0b8eaa47e8000aef3484000135281c8706000294000000000000000c12ae3e71400004df000000000000000000000000000000003318000000000087e800000000002148c0219380004b19b5abf7a904000000000029f2000310a000084800030d64b72edc00013ec000123aaf7aace00980005b000000000000000355200000007f11440d07ad6ab108000be4000000000000000000000364eaf71bd4353137811230e4e4504180ae84447640000ca400000002e066eb8000149138c00000000000000c9180008e08000b42000031e023079b92940000000a153112390a4dc6643626aa000e0a968ef0000377000026341fd08465fba28a0000000000379a84995343931a5c000388400019789c3800059c94540000000ba32144a6f0f3e4a1800071085a89d22ea600020baa7fa98200000006e08678a1da45cba8b87a0dd00007ca8000000000000000007110000000000016235e6746b6de7db8000b5bab100e80288cb387a20002a22a640000000283200000000001948000288e00000000000000a1b2d1461880000000ee012200000002bc654f8eca00031c42159206c8b93920001e2c68489d20002d240a914f0ddd046490ba6dca9a88ba088b1c86820a5aa36389024487e241e0dd257a81aace093383b5b8e6934901c000235c545000007100004110000000316250d0ad0e4fa1820001c9c34b99deda909407ee3312a95245a0000000a43a9b20000000c4a800000000008b5000000030627d305de0000000000000000003c067639041072d7489c2a681048000d1480000002c140000964d750000488113200000aa3d79386e15970a0002136a87000062b275800000000000000c028ad44a580000000000a00b58eb99ac8c70f80007df80002b600000002c24931ab820002c8035080000000000bb0b92400000000a383ba1d323740001f021ce00000000000000000000000000000000000009e0000f18acf0000a68245e878936c000052c51789ca0000382bcc000067a07a6000000071f38fc000081e0448ece00000000001c7ee49a7409e40dac47422360002676bc60000000304c00030b20000000747b42c58280000002a122050b5400000005a400000000000000044c000245200000007382850b6400004b917f4000000083700000000000000065ed5400000001a1a000059c0002d9aaeea90a000071a0000000000181000000000000000344979800024f053a800000032f046b0000658ab548c90000d300e6200
  | 63 => 0x2e274ed4736ccab08a0ea040000364923837222a0012842ee2500006c70da4000000000000006d600008c9800027988e66048000b4c154a4189d720000b66de400000000000ca1299a00000005239cec7eea4c088e0000b50800000000000003424000000069180000001fdc28b8000ab89cb20000000e508000a7680000002d2e21f800009400003fb000087726a689006de0620000000116216794da1f19312dca80005a18c5a00031564af930e18f27140000000b3d00000000000ca5856a0cf1c882bda27ec058000013b05400026780000bc000036ee22600000000526000110a65a262c0000000b42981aabb21a47d68ffe4311fea0000000d86074acd381608fe322037b8000457aaa23df0aa01989f2cb6a17a23f726c8896159a0001cb69e3b19800025c0dc50000cd288e000027e20000d9000004304f12298b738000bdb8000000172200002e204d25c800024a60001b040d880000002c4c00000000000e9c00017d40000ed288a12f6000246a27c00002c8a49246307ae176156c00000000001fb23b88ddc0e384fa70d97f29b9973e5d680000000f0400010425af80000001a3400016d07ff8000000120e6ca105e57e1f2e32fb022bd084ca91980f0a1f1114d192b08aa2362067090aa68b80006980000000309052faeba8080000891b32800003ca0001d9400000009b78f4a5299e8000000000000000473a6706ffb238000000098080003d880000000eee0f8b558b2700000000896709800022700000000692000084ec9780005b70eac537819a026b3c80002a50000373e47c0000970934e1718000d398000dd4000081e00000002b2000021e64c10eba0daa5100000000000031800000000002c120001820b1b250ab978000000000000000000000000cb535ba00000000000000160b5922b8864cba48f5ca5f9bb60002d8a0000bde4290000630800000000003c1a018c5b058c98c32ca87d18a4000127e3c51b4ab7aaf46da12f0226d00000000000152800036180007323438328339cd0680005e42d8230b9622706b842d6500000000dea00000048b1800000011fc0aa3670771000000000005788e9a0002dbc000000000000006b78000db5b47e30f80000002af200001e03bda3ba1f224babf32c446c43598b559f4200029165ada3fc00007e8dd00650bff387e3dd90b450f2646d9080001962264351800000006f00000b3e00000000000000af123d074380002eba3c00000ce623b3008958088a61730e073d80000002c0048a800000000000000914bd60b369c0860056d06c400000001990000b418208ae000000000000000000000000003af00000002ec4856a912120ac540001942d7e9910d7ca3ce9b6327211d99e69acb0183421ada4528ab61731d8840ea31e85795ee4d0977400012f0b8e2b760000000cd100
  | 64 => 0x778afd8e2281000009ca8da6b340000d508000bb1800058c00000000000000000000007e4762ae3a98e8000bbdb104630283adfa244266228de000000013386309ee00000000000de28e2aa59b7fc12a11180000000aa82dca000345a0d480004e59af6aa080000001b2e00000000000000000000000000002e7acca00006ea00000226e70000000282c69415b2639000000004d400010e0000179c000166e00000000000000000111eb95800000000008bfa5c60000000000000007180000d180002dc0000000000000000000000a1abf428b6a7789e025200000000000000000000000008e48d6600000002f8ab7800000000001c742de82a20338d5a8221dd6a5b958e362000000000000000000dfb12e200027ea0000000aa79fa2000069420100007a61eec0001d5638c38888529cfcb00800002fb43e0002dec000308e0000000ce32856bcb00004480a6000000000000000000227ae548a1600030fed57800047200000000000b3c8000000000040f9320000000069d8522b72000030430ae1428c800ddb8f04af0a64e552e4cbed0000cd708c400028480000f8c00038863c898b8dc401529dcb18800018680001930719378e00039380002656000000000034f87b380000000f480000000011392271b82b20000000000170c5a78000580ae60b2e353669784a07048ae60a1819e5eb239c3a813daa7197a65cf3102dfe89f2560af729ae80000bd9e36a451344ba21ac221a087c07280002a5800009d000000015a800000000000e3a00029ea7f333aab0d17b8c98000043e87e600013ee0000000000072e0000000c829a0c2ab9a68000249406086b200016a478ab36207c30a0338b24865d80001570d6c00000000002d40000000035013a0000000000037f600000007a5000000000002b900000000000d488000000000000017ea0ed8ca2000010635a00000bc0000811391aa33000010f938000000000000000d8f964cb5b0000000394098a2462b211e00c6ba24438520da3582d8eb4c8d362bf9b8e000000000000004b7800000000000000000000000000000000003556000332c4aab4f4000347c0000fd200000000002b66000000000000000002ebe0001bf2000000000000000001d9a000115407582dec90869a3e837569992f3a4f506bc8d393ca495000054b0d0e000236ad4087cc00000001e7a50e40b800000000001ea00007e5800098e0b4800008c200000003db80000c4800000000000001a3c0000000b01025a000000000000000000000000000000000008c8b280000000000011c200024aa99f2c680b0803c92c3036000148c0000000bb687120002312bda0000000348e0003152000258e000000068936003b7356a00022569b10b920001fd200036f2a8b8000000018e05600000001fe8000132a00000005f402d09
  | 65 => 0x1d400000000b8920facbb88a6114a440e43a35a000037800020bc6e4a99800012f8158000000025961450e7c000275c000115a02d8000cb78d1a50aa546787940c00007262fd8000000000020fa5be68a992c0001f489c336c8000000000033cc000000000011b800012ae0000000000203a000302a0000000084a4000002c78000168a000000028f84f200000005ec000000000006a804f60001880db82e6c75eb078c1e87f8000000089282e000000006ba0000000000000012b00002df648b1de28be1632d49392ecc500001392e4e95f000000027cc00000009408000846000084e181e6a335ec72195d20000fe631b0000000000062d085a00000003d0119a00038300000000000177c9781e4e000000000037e20000000d5e80000000000000000010e88220000ac67841ab443aa47a240800062b80003f8a24ca0200005f20000144030c85e8f5061300009018000000000000011cc69a9e6225ba42400000000000000000256c000000000000004068000000073a000089e00000006fa021e0000fccb8b2ffaae68d8429d00002d42c5a7d835700000000000000000000000002376403b93c0b60000b2400005e280003de145000037f87e31e1c85500000000580d30b70e223004cc27190cbd80ed492719a02a486c01e6123e3a99288d0a99be59d100020eb3340002adad19b1403a91c7a38d00000000812474955238daa0857d265a0001e16c13955651980000001f3000000002e513649508a9c2342ff000026a806b01361d180007dd3968000159cb6606a832a09dcdf79150000000000010a8e4d8000000373ac8cad26bde80001c098e800000000000000b9880000000000000000000028720000000af600003e4a01a44d020200021ee0000000aae8000674000075d1f1800002aa0000c4ab8c2f9a0000d104279e7000000000000000000324400000000000000000000087c049e399b1283a596b408b1ea202c00000002ee884a05b40003960d141c58ded2486a40a44e315b49ccf9259e66c0000bec05fe36f00000003004477090600001941e015caddf80008f80a88848000000015e4cdd80004618000cfa80003928af4c5e8000000289205d23a82800cc400000001daa16000000007118000e0a00000003628316000089f000000000000000000000350e0000c3c288a7246c3000018bb66e022800000029fa3e01e9006013ba0e7a22a64daaf0000264c1f080002dfa72604b09ae63d0000e2609aa68b16b000000000002d1870a0000d3f9546898800000000008722c06d5d0000c99800000000004d5b6ae2ec00007d40000571b0ce000000084000000000000ae783f8000000000001baa5f000068d8ad258580002bc00000000000734a25a3b01e9295a021ca1a2a4aced0a904f706563e5b0cac7d089421e183e6619
  | 66 => 0x5bc0000e3e000116c9e9000000015b87d280000002818000000000002d6c2f800081220806a480000000a8c629ae20a08000067b80004130d7600022880002da00000000a8f00000002432257803200028b828c1ba80000246000284400029480000000000233290c19740002eee4e21ac81cb10a26db00009ee800000000008b797ca00000000001f6a7890b80bd6b48a35e355ccb10b082a5076ee51a538d6f000022cb40c0000000799200e146800000019f27a5a3f4178a028ce833988aba922079800000000001e1151a00027ca39500000c993ccd7836d000025fa4268000446aa8ab598000955351a0002d7c811b8600003230000000000012a6327112200032dad8480000000a826feb420782b89e8d080005fd869c000277400000000000000000000001e0c44a99921e202000091124f6a3d33300f912b60002fda2da0000c538546000000000019a661580000000000000000000029f00cc1e6685a1fec20c0000000000000000000001a0400000000020000ab2b6789291652000330c22ba88400000000001c5ad67380e8baa09a70d0df870a984813a8614dc71faeab735ccaf40afc5fb1d4e2eca17494c80005070c86d360000b77a6ccd2180008e500a800013000000bc27dd800000009822c28eb6822b11e834216c9f08000d980000b3800000000000bb980000000000196800000000000000d5009928be0001de682b8000b0987aa4c69ad43a3374429e80008ec000000000000452eca342999400004de46d135c5400a080001c384c9800000007822b080008bba56e23c37320000000b0627bcba800007df287443680008d000002b334448472b2c006890a939b03a8e91ef83082c748e58000c2c27a00001d641331de0c5d0000b6c1c5600028d299433d400017d200002e60002a8e00000008a0359000480004c2992a12e12ccab30000000000000000006e6947c0003032db5000033695fac080e76147000061c800012880c0000332a0001db60002fe427f80004513562c4f88c823500000000000552107e79e8b7405335440001112c838000645050655a80006a888421c700003c200000001dfe00008fa000000024a0258c969aae6fc15762b73442000376c00014d2d1e13c062400001a7a292bfb049610331c6656931c0922baab878000432a95aa329afc611884a49dabfa0000000000000000007b8d37800050822fc9281f140000000c03000000025d886f000049399f472f80008c19066000285265b325633792c80a821d8329000065f000022d93d087023be3f58e74cd1a9b8acd84740000de4aaa041400000007038b10577000026db21a16eac967f18db0c0f80006550000abf1020000381000014badaa00000000000c7307f65d380000000fcadbaad4c51d3308d0f36b2e53b72e00020b238212ea0000000
  | 67 => 0x81529d20003190d6980006da967e27e0000000367a00015d8000352c0000000248804600008f400013e858ba43800033a20000000000216484e8000000000046a32bcd791e1200011960000000a2a1e8e000000000019b200034168a8800000038e21559ac6c4612360002762415216200000001b5000000000008de01de6b9021aafd2662190b8260002ee4df922ce000000000016200002c62ac38000e1400001a3948400034d63758000014330ad840a06b3d8e100000000cc79b9852b80009851d0a00000000000000c59000044122f000018548940bc83e08e58be1ac9821b00000000000000385265c1a827db15a29b38000a3a8000000000000000000000e0600025f81199afe66b00000003200cf881924dd3586000133c000124255f8000572000043037623cf26000af344c27da9be5ec822a477b13200000000000000a9b80009648000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8de87d8d43440018b8ebb1a868800237e0d75d89100146e41aebb122000a6d8510b62440015cb02216c488002ba60042d891004e67312e631220008ef87588624400199ae6b10c4880263b209769491000c7a432e329220058f8865c2524400117f08bb2a48800e2f21176549100046fc1aeca9220028dc835d952440130f90eb2aa48812a9720d65549100247743ec4a9220018f4865c6424400b1f10cb8484880121fa1676509100043ec2ceca1220008ef825d942440131790eb228488026ab209645091004c77414ed19220018f4865c6324400b1f10cb8464880023de05764c9100243f428ec992200087d851d9324400717d083b264880022f610764c91004c6e43ac699220028ec87589324406b5a906b2c82880d63d219739051019d1f42ec8a0a2003ab684d9541440071e90eb2a82882f78d15165505101956a41acaa0a2056b3685d9141440033e101b9a828815acd21543505101974a31a86a0a20019f080dc94144001bc441b928288003a9d0b625051001c7a43ac4a0a20019f287dc141440055a906b2c62880067c201748c5100147a43aca98a20018f4865d131440033e100ba262880067c201748851004d72412c910a20018fa86dc121440031e90cba242880067c201744851004c7a43ac890a20018f4865cd214400178b063124288002f860232485100147c43aca9822002cd87650d30440017630838a6088002f8608714c11002e783b4829822000bd18390530440013e10ea0a60880173c1d9414c110007c8a1a8298220019d8874c5304400b9b0ec98a6088017741c5314c11000de843a629822005dd0874c530440037a50c98a6088006f4219314c11001768432629822002ed3764c5304400bba4ec98a6088017741d9314c110017683b2629822000ed3654c53044001da2ca98a6088002f4e11314c110005e8c22629822000bd3824c53044001ba6e498a6088002f460e214c110005e8c1a429822000fc13248530440131f10eb2240880163e2197348110005d4c20c49022000bc98318920440017c3032124088003aa5914248110005f0c0c649022000ae8864c920440017630838a4088002f460c7148110005f0c148290220009f0875052044001f4284a0a4088002f860a3148110006e8b9a629022000fc1324c5204400b9d0ed90a40880173c1da21481100fdf0c144290220019e887485204400b9d0ec90a4088017781c5214811000d78432429022005cf0764852044013dc0c490a4088006f821d214811002ef043a429022001be28648520440037c10c90a4088027b8219214811004f71bb2429022005de276485204400bbc0ec90a4088027b81d92148110005f1c22429022000be1844852044001dc6c890a4088003b85912148110005f1c1a429022000be1834852044001bc6e690a4088003785cd2148110
  | 1 => 0x902bb2869000a2fa1f6450d200061e3aec8a1a40038dc8758d43480bf5a902b1a869000eab211659092000cf4402e721240038ec87595424808355908b2c64901063b219748c9201fd2f42ec69924002ace83d9532480051d90eb2a64900faab211654c9205ff2629aca99240019e880dd132480031d90cba264900067a201744c920305a742ec69924060b4c8550d324807dd18c8a1a64900067a203714c920006f1086e299240019ea87dc1324800117f08baec29000e2f21175d85200076299663b0a4000a75850c761480015cb0418ec290002bc60031d852002e5b30ae830a40008f787584614800196ae8b08c2900163d205769452000c76432e528a400587c87595514807347908b2aa2900123da1f615452002c7b40ced20a40018ec865ca41480090fd0a3b282900021f61476505200146f418eca0a40008dd831d9414800b1790eb2282900032b1d9425052000c76432e518a400487e859d931480010fb0b3b262900163721d634c52000cf4402e790a4005ae48158f21480031d90cba242900063b219734852000cf4402e690a40058ec8758d214800174b0830a4290002f8602414852001c7c43acaa024003cb87650d4048001793063928090002f8604725012000cdc43a84a024009cb8765094048013b50e4a128090006ea21d425012004ed443a84a024001baa8650940480037510ca12809000faa219425012001f55bb284a024009daa765094048013b50eca12809000faa1d9425012000755b2a84a024000ea965509404800175706a128090002eae05425012004e743b464a024000ba9848c940480013d10e99280900273a1d93250120005d4c2264a024000f89434c94048001b5285b8a8090002ea6132150120005d4c2242a024000fa141485404800b0fd0f2a2cb880162fa1f545931001c7ac0ee6b26200587c8759553c40071bb07bb287880063da077650f100043fc2aeca1e200487c855d943c400b1790eb2287880030f1d56450f1002c3e43acaa9620018f681dd942c400b1790eb228588026ab2096450b1000c7b40eec99620058dc8758d32c400b1d90eb1265882fb8d15165507101947ac36e6a0e205db348550d41c40bfd28c6a1a83880023de1973487105be2e39ca8b2a20028de87dcd65440018bea1b9aca880031754373595100053cc04ebb22200487f875d7644411f0ff00baec88816a1f60175d911002c7a40ae7b2220098ee87dc964440018dea1b92c8880031b54372591100043ec2cecaa220008df835d954440051b906bb2a8880023be09765511004c76412ecaa220008ef825d363440131d904ba6c68800237e0d7654d100143e43acaa9a200487e859d943440010fb0b3b286880021fe157650d100243e42aeca1a20008ef825d943440131d904bb2868800a2f21d6450d1035556412c8a1a2003
  | 2 => 0xe62541301edacc1cc4a826040b5b83589504c0016e702b12a098002dc205625413000734b10c4a826017b5a83909504c0016b307212a098003c650e42541300bdad41a84a826000b5a874c9504c0016b10e992a098006d6a19325413000dac43264a82603fe5b764c9504c02fcb0ec992a098002d6e113254130005acc2264a826000e5b644c9504c001cb2c8992a09818ed6e0932541300bfa5c1264a826000f4a724c9504c001e92e4992a098003d2d893254130007a431264a8260c1f4b424c9504c183e9084992a098002d6e0532541300bdac41ee2a826000d5b73dc5504c02f4f50d38aa0980029e61a715413035d9d424e2a826000b39849c5504c02f6b50738aa098002d660e71541300053dc32e2a826017a78865c5504c0016b706b8aa09805ed620d7154130006adb9ae2a826017b5a831c5504c0016b30638aa0980aed660e6154130175adc1ac2a82600097a87185504c02f2f30e30aa0981aecea1061541300059cc20c2a826000b6a82185504c0016d30430aa0980039c5846154130004bd43c82a82600097987905504c02f6b50720aa098002d660e4154130407a998c82a826000e3964505504c02f6b506a0aa098003c650d41541303ffa998a82a826000b5a874c5504c0016b10e98aa098006d6a19315413000dac43262a826000b5b844c5504c0016b30898aa098002d6e0931541302c5adc0a62a826017f53814c5504c001ea4e298aa098003d45c53154130007a9b0a62a826000f50614c5504c02f6b50790aa098002d660f2154130007a499642a826017b5a83885504c0016b30710aa0980029ee1921541300053c43242a826017b5a83485504c0016b30690aa098003d24c92154130004bd43842a82600097987085504c0014f50c10aa0980029e618215413035d9d42042a826000b3984085504c02f6b50610aa098002d660c215413004c3f43ca6b2e400987c8759554c80051db05ba2c79002637a1f5358f200145ec26eca1e40018ee82dd943c80010ff0abb287900121f2157650f2004c6e43ac6a1e4000c5c7558d43c8181c98a6b2a65900fa3b61b744cb2033da642a86996406ae8c6450d32c80031dd05bb283900272b1d9425072004c7a43ac2a0e40018ee82dd931c80011df0cba2439000e2fa1f74595200061fa86e8b2a4000c3d50dd16548175878e929aca900030f5d754d91200047bc0ae7b2240058f4815cf644800117f08bb2a89000e1f21d65551200053cc04ebb1a400487f875d763481210ff00baec6901961f60175d8d2004c76412e9b1a40058f687dc563480018eea1b8ac6900031d5437158d200043ec2ceca9a40008bf845d9534800717908bb2a6900023de057654d2002c7a40aeca9a400487e859d943480010fb0b3b286900021fe157650d200243e42aeca1a40008f7815d9434800b1e
  | 3 => 0xaa1a60b6c5c761d5434c0016b3003aa8698003879536550d3001c6e43acaa1a6003c9e7450f624c0011df0eb10c4980263720e769493000c6e432e729260008f7815da424c00b1e902bb48498006372197390930014cfc3a8721260029cd82dd1324c0031b90cba26498026b3a0b644c93004c6e43ac8992603fa5c85591324c00159d0d29264980ff93195524c930006e9086e2992600087f855d3614c0090f90aba6c2980023de1d611853000c6e432e728a60058f8865c2514c00b0f90eb2aa2980163d205769053000c6e432e720a60058f8865c2414c00b9e0c2b8482980162f21d645053019d1e42ac8a0a605fe946150d414c0071ed0fb0a829800637219744c530005aac28c298a6000bd180945314c00b1dd053b642980063721973c853000762996c390a60018dc865ce214c00b1f10cb84429800637219734853002c6e41cec10a60018f8809d8214c00b968c2ba042980063721973085300065aba6c210a6000cd573d84214c00b1f10cb8042980033cd85700853002e7830ae010a6004a7a85d91504c0091f10eb22a0981afc695143541300078caa286a826017b5a83949504c0016b307292a0980131e1d952541300166c3b264a826000f4a524c9504c001e92a4992a0980065ea1e515413035d9d424a2a826000b3984945504c02f6b50728aa098002d660e5154130007a928a62a826000f51514c5504c02f6b107ba2a0980029ee1974541300bd3c432e8a826000b5b835d1504c02f6b106ba2a09830b8e993645413062d3d43ec8a82608ba7887d91504c09f4f309b22a0980069ee0f645413000d3cc1ec8a8260c4e3b43d91504c189c7287b22a09831396ccb6454130004bdc3ac8a82601497887591504c0df6b706b22a0980031ee1d64541300253d43ac8a826004a7887591504c0018f10eb22a0980121e21d64541303853dc22c8a826000e3b84591504c0df4f706b22a09800396e0d645413061f2d992c8a8260c2e3b41591504c1156b50fb9aa09805f56a1f735413000dad436e6a826001b5886dcd504c02fab4edb9aa09805f561db7354130005acc26e6a826000b5982dcd504c0016b303b9aa09800356e1d4354130005ad43a86a826000b588750d504c001ab10ea1aa098006d6a19435413000dac43286a826070b5b8450d504c02fe3708a1aa0981afc69d143541300078cba286a826000f1b6450d504c0d7e30c8a1aa098002d6e09435413035f8c21286a826000b5b8150d504c0d7e3682a1aa0982231e1db72541300bdac41ee4a826017a7a869c9504c0014f30d392a09805ed6a0e7254130005acc1ce4a826000a7b865c9504c02f4f10cb92a09803f1e1d972541300059dc22e4a82606bb38845c9504c0016b706b92a09805ed620d72541300bdad418e4a826000b59831c9504c0292f50f312a0980025e61
  | 4 => 0x501134f10fb1aa0a00069e613635414061f2d21ec6a8280c7e5943d8d505018fc7683b1aa0a00025ee1d63541400b4bc43ac6a828070b3b8458d5050001a770ea1aa0a0002cea1d43541400059c43a86a828000d388750d50500036750ca1aa0a0006ce219435414037d9dc1a86a828018f1b8350d50500ede34e6a1aa0a0003c65cd43541400078db1a86a828076f186350d505000167704a1aa0a01dbc6cc943541400059dc0a86a828076f183150d505003167109b92a0a00034edd372541400c53d434e4a828000a79869c9505003167509392a0a0002ce61272541403b5ad41ce4a828000b59839c950500014f70cb92a0a00629e21972541400059dc22e4a828018b38845c95050001a76e8b92a0a0062cea1072541400059cc20e4a828043b3984989505008d67708b12a0a00025ea1c62541400c4bcc38c4a828076b5a8318950500016b306312a0a00039a5886254140005b9408c4a828000b718118950500016750ea12a0a0002ce21d425414000d9d43284a828001b3886509505000167706a12a0a0192cee0942541400c795c1284a828000f2a725095050001e52e4a12a0a0003cad8942541400079431284a828000b3b8150950500012f50f192a0a00025e61e32541400c59d42464a828000b39848c9505010be5685192a0a0062cea1132541400059cc2264a828000f19434c95050109e5684992a0a020f1e1db71541400c59c426e2a828018a7a869c550500014f30d38aa0a0062cea1271541400059cc24e2a828000a7b865c550500314f10cb8aa0a00231e1d971541400059dc22e2a828018b38845c550500016b706b8aa0a01dad620d71541400c59d420e2a828000b39841c5505002d2f50f30aa0a00025e61e615414018d9cc24c2a828034b3b8458550500016d704b0aa0a0002da209615414000738b08c2a828000b3a8750550500016710ea0aa0a0006cea19415414000d9c43282a828033e3b765055050031c70eca0aa0a0002cee0d41541400071db1a82a828000b3b8250550500b367702a0aa0a0063cce0541541400079938a82a828000f31715055050001e66c2a0aa0a0003cc18541541406379998a82a8280c6f303150550500316750918aa0a0002ce61231541400078ca1c62a828018b3a844c550500016730898aa0a0062cea1321541400059cc2642a828018b3a8488550500016730910aa0a0003cc50621541400053dc3242a828000a788648550500316750890aa0a0002ce611215414000798a0a42a82800097a8708550500012f30e10aa0a00029ea1821541400053cc3042a828018b3a8408550500016730810aa0a01dad6a0c2154140005acc1842a828000c3d74953654c0014bb072a6ca9800a3720d71d91300243f43eeab22600087f80dd5644c0010fb01baac8980021fe1576551305d62e3b6e
  | 5 => 0x80025ee01744855000cbc402e890aa00197880dcd21540012f700b9a42a80065e20173485502d4b643a6490aa0659748750521540032f50fb8242a80125ea1b7048550024bc436e090aa00097984dc121540012f307b8242a80035a8cb7048550006b4996e090aa000d7241dc12154001ae283b8242a80065e20276085500063db04ec10aa00487f809d821540018f7013b042a80121f60276085502d63c404ec10aa000c7a409d821540018f4613b042a80025ee0176085500063db02ec10aa08f87f805d821540018f700bb042a80031e90176085500063d182ec10aa00197a805d02154001a7480ba042a816b4d885740855032e9a90ae810aa000d3a805d02154001a7300ba042a823f0fd8174085500069db02e810aa000d3a305d021540032f500b9842a8003568c173085502d6a790ae610aa05ad4d215cc2154001ab500b9842a800356601730855047e2fb02e610aa000d5b605cc2154001ab480b9842a80125ea19700855047e3d432e010aa05ac79865c021540092f10cb8042a80025ee117008550004bdc1ae010aa05ad6b215c021540b5ae442b8042a816b5a485700855032eb890ae010aa000a3d8494f655000517908b96c6a02df0f1db7550d405ae1e3b0eaa1a8000b39801d54350001c3ca7b2a86a000a2f21d6550d400043fc2ae7b12800487c855cf62500011df0eb10c4a00062f219749494004c7c432e1292800987c87595525000165b0a31284a0002ea602525094004c76412ed19280018bc865d232500131f10cb8464a00273a189708c94000c5e432e8992806ae8c6250d32500051dd0fb1264a000b279cd43d85400047bc3ac230a80058bc849da51500031790cba4a2a000e6d607735054002d5b40ec6a0a8000daa20dc9415000156d0d28a82a00cf8d195515054000477c12ed18a80098ec825da31500031790cba462a000e67e1d438c54000c5e432e898a80018bc865d321500131f10cb8642a00163da06768854000c5e432e910a8000ea76250621500031790cba242a00162f212760854000c5e432e810a8009ccc625cc215000195ae9b1042a0003335cf620854002c7c432e010a8000ceb625c021500139d0c4b8042a00129ea1763541403b78d29a86a828000f195350d50500032f50f292a0a0062cea1252541400059cc24a4a828076b5a8394950500016b307292a0a0003ca949425414000794a9284a828018b3a8494550500016730928aa0a00131e1d9515414001e5c3b282a828000f32515055050001e62a2a0aa0a0232cea1f74541400c69d43ee8a828001b3a86dd150500036710dba2a0a00634e9db74541400c69c3b6e8a828000b3983dd1505000167305ba2a0a0002ce60774541400c59c426e6a828000a7b865cd50500314f10cb9aa0a0002cee1173541400c59c422e6a8280c8a7a87d8d5
  | 6 => 0x2d96422c5192a000b6b8058a32540012f700b8c64a80065e201718c950004bcc06ec992a00093f845d9325403127908bb264a80025de05764c9502d4ba40aec992a00097b805d9325402f2db05ba264a80021fe19744c9500043e432e8992a06595e87d8d32540cb2b90ea1a64a800297219434c9504278621286992a017b4e8398932540016d30131264a805e5b21d624c95042596422c4992a000e4c6358932540016d700b1264a816a1f61c64d85500052ec18c9b0aa000a6d8219361540b54ed02326c2a816a1f61f63d85502d43ec3ec5b0aa000a3c8458b6154001a7500ba4c2a80034e601749855047e1fb02e930aa000d3b605d26154001a7460ba4c2a80025ee117098550004bdc1ae130aa000d73615c261540b5ae0c2b84c2a816b5c90570985502d6b918ae130aa00197880dd161540018b8e7322c2a80029760c64585500062e398c8b0aa000a6d8219161540b54ed02322c2a80065e20373585500bcaf43ee6b0aa000d5b80dcd6154001ab101b9ac2a800356d837358550006ad206e6b0aa017c5c73d8d61540b50f90eb1ac2a8003171cf62585502d43e43ac4b0aa000a3c8458961540018b8e6b12c2a800356dcf7058550006ac39ee0b0aa00197a86dc161540032f10db82c2a80025e6137058550004bcc1ee0b0aa000d7361dc161540252f700b90c2a80025de1d6118550005b9c02c230aa05a976819da41540b58ed033b482a816b0fd0676905502d61ea0ced20aa00487f809da41540090fb013b482a80031e90276905500063ca04ed20aa000c7a309da41540b58ee213b482a80031d4427690550004bdc02ed20aa000c7b805da41540018f480bb482a80031e8c176905502d4ba40ae720aa00097b805ca41540032f100b9482a80031d9d96190550405aa41ac320aa000b738058641540012f301bb282a800257e0d76505500bcae41aeca0aa00096f825d941540cb2d904bb282a80025ee0176505502d49f43ec8a0aa01897581dcd41540b52790ea1a82a80028f21943505503ff8a18a86a0aa05a93c8750941540cba58e4a1282a8062cda126150550005b8c04c2a0aa018974875854154001c68c8b0a82a81fed520d6150550005b9c02c2a0aa05a976819da31540012f700bb462a806257e1d438c5500052e4328718aa00097b805ca31540032f100b9462a805ed520d618c5500072bb1ac318aa000b738058631540012f301bb262a80025ee01764c5500043fc32e898aa00087c865d131540b52b90e99262a8002dc602614c5500bcba43ac298aa000b7380585315400127f08bb642a80624f21176c8550004bdc02ed90aa00095f835da215402f2b906bb442a80025ee017688550004bcc06ec90aa00093f845d9215403127908bb242a800257e0d76485500bcae41aec90aa00097b805d921540032f101ba242a
  | 7 => 0x78805cf64540252f700b96c8a80065e20172d9150004afc1ae3b22a01795c835c764540192f700b8ec8a80065e20171d9150024bdc26e0b22a00497984dc16454001a76c9b82c8a832b4e1937059150004bcc1ee0b22a0cad3b43dc1645411d2f700ba6c6a80065e20174d8d500049fc22e5b1aa01893c845cb63540252f700b96c6a80065e20172d8d50064bdc02e3b1aa001978805c763540012f309b82c6a80125ee0f7058d50024bcc1ee0b1aa000d5b63dc16354193ab0c7b82c6a83275690f7058d50004bcc06eca1aa000c7a70dd943540018f301bb286a80031e9037650d500063d186eca1aa00087e869d943540012f700bb286a81965ba087650d50004b6c10eca1aa05a976811d943540012eb023b286a80030fa107650d500061ec20eca1aa000c5e831d943540018bb063b286a80031ba087650d5000636c10eca1aa000c3c421d943540018be643b286a80031da047650d500063ac08eca1aa000c3f411d943540018b8623b286a80121fe007650d500063d400eca1aa00487d801d943540018f3003b286a80030fd007650d500063d200eca1aa000c3d401d943540018f2803b286a800317cc07650d500063d180eca1aa000c5d301d943540018f2603b286a805e4f21d6450d500059dc02c8a1aa01895c8758d43540016b700b1a86a80065ea037250d50004bcc06e4a1aa00197a80dc543540012f301b8a86a81429e2197050d500063c3b2e0a1aa06587d87d9362540cb0fb0e31ec4a80028f61063d89500053ac08c7b12a000d5a805ce6254001ab300b9cc4a824317d817398950006adb02e7312a000d5a405ce62540012f708b84c4a80025ee0d7098950006b5b12e1312a065d68625c262540cbad484b84c4a81975a8c970989500c49f43ee8b12a000d3b80dd16254001a7101ba2c4a80034ed8374589500069d186e8b12a018c3c74d9162540cb0f90eb22c4a80030f1d263589500051ec20c6b12a000c3c7418d62540cb4dd0431ac4a80029d60463589500069dba6e0b12a000d3874dc162540012f309b82c4a80025e60f7058950006b5b16e0b12a00096f8758862540016d700b10c4a80325ee01711895032cb7414ed212a00097b805da425400187aedb2484a805e4fe1d43909500051e43287212a018b2c8458a4254001c5ec8b1484a8002dae016290950004bdc02e3212a001978805c642540012f301bb284a80025ee017650950005b4c04c4a12a01896c8758942540016d700b1284a81965ba0a768c95032e37414ed192a065c5f329da32540cb8ba653b464a80121fe02768c9500243ec04ed192a000c7a409da32540018f4613b464a80031e4c2768c95032e37904ed192a000c6d209da32540012f700bb464a80031ee01768c9500063d202ed192a000c7a305da32540cb2d904ba464a80031b9d9628c9504
  | 8 => 0xaa1ac0108030fd037650f500061ea06eca1ea000c5f30dd943d40018ba61bb287a80664fe1d4390b5048637902ed196a000c6d205da32d41212d904ba465a80665b60b744cb500043fc32e8996a00487c865d132d41212b90ea1a65a80fe97219434cb5049f8621286996a08fc77105da41d40018ea20bb483a823e5d20573907500d4bac0ee6a0ea08f93c8750d41d40674790ca1a83a8247c50c543507504869639284a0ea01a95f8750e31d40010ff0cba263a80121f219744c75047cb643a6490ea0909748750521d411f8f500bb043a80031e601760875048697312e810ea000d2d625d021d411fa6cc2ba043a80034d585740875047e9b10ae810ea090d35215d021d4121a9cc4b9843a800353589730875047eab30ae610ea000d55615cc21d411fa9e42b9843a823f53485730875047cbdc32e010ea090d6a625c021d4001ad2c4b8043a823f5c9857008750006b8b0ae010ea08fd6b215c021d411fae442b8043a823f5a4857008750486b890ae010ea0008df835c764540051b906b8ec8a80022fe1172d8d5001c5e422e5b1aa00487c851d9435400187ca83b286a80031794c7650d5004c77410eca1aa0008ed821d9435400b1ed023b286a80023d6047650d5000c3f436eaa1aa00197a80dd543540030f90cbaa86a80124f21d5450d50024ae43aa6a1aa0008ef875886254001ab460b9ca4a800356a017394950006acc02e7292a090c5f605ce525407fab6c0b9ca4a80035690173949500069d206e8a92a018c3c74d9152540030fb0b3b484a80263ba0a769095000c3e432eb212a000c3d75d924254001c5ec8a9484a80061fa1b755095000c3e432eaa12a00496c8754942540030fb0b3b464a80261f216768c95004c77414ed192a00187c865d632540018dceca9464a80061fa1b754c95032caec1eea992a00187c865d5325402f69d0729264a80125b21d524c9502572631aa4992a0008f7875846154001a7480ba4a2a80034ea0174945500069cc02e928aa08fc3f605d25154067a76c0ba4a2a80034e8c17494550006ad186e6a8aa017c5c73d8d51540030fb0b3b482a80161f216769055002c7b40ced20aa00187c865d641540018ececa8c82a80061fa1b75505502d49ec26eaa0aa00187c865d5415403166d0928a82a80125d21d51505501cf1a322a2a0aa00187d859da315400b1ed033b462a80061f219758c5500072bb1aa318aa00187e86dd531540030f90cbaa62a80125d21d514c55000c3ec2ced90aa0008bf845db215400717908bb642a80061f21975c855000c3ec2ced10aa0008df835da21540051b906bb442a80061f219758855000c3f436ea90aa00187c865d521540032f100baa42a80123ea1b704855000c3ec2cec10aa00587c859d821540030f90cba842a80163e219700855046cbdc02e7b22a0019
  | 9 => 0x4358c210052f42c60b184200a5d858c1630840153d083aac610802a76107558c2104d67410eab18421cacd821d5630840b5ad023aac610872b56047558c210056d400eab184200ad9801d5630841359d05ba2c610872b360b7458c2102d6b40ce8b184200ad5819d163084014bf0aba2c610802972157458c210046f438a8b1842008dd87151630841359d042a2c610802b36085458c2102d6b408a8b184200ad58115163084015b5002a2c610802b66005458c210052f42ce0b184200a5d859c1630840b5a902b82c61080297a147058c210052ec28e0b184200a9e841c1630840153b08382c610826b3a087058c210e566c10e0b184205ad6811c163084395ab02382c610826b3a0b5058c2100566c16a0b184205ad681d4163084015ab03a82c61080297a164058c210052ec2c80b1842008de8710163084011bb0e202c61080297a144058c210052ec2880b184209ace82101630840159b04202c610816b5a044058c210056ac0880b18420587c87595530840b1b90eb1aa6108121f2177650c210043fc2aeca18420487c855d943084010fb0dbaa8610aeb0f9937550c215be2f31eeaa184200c7a60dd543084010fd0eb2a86108021f21d6550c2102c5e43ac8a184200c3f755914308401878eab2286108163721d6350c210062fbaac6a184200c5c7558d43084b54f3013aac010a3e9ee0175580210243f42ee8b00420087d85dd160084090fd0bb9ac0108021f617735802104d75416a0b004205af281d4160084135d5053aac010802ba60a755802102d7940ceab004200af1819d56008521cd5053aac0108039a60a755802147f3940ceab004200e71819d5600851fcd6433aac010a3f9c886755802147f3490ceab004290e71219d560084018f70ebaac01096b9ac8575580212d73910aeab00425ae69215d560084cbce242baac0108029ea1774580210053cc2ee8b004200c7975dd160084018f2eaba2c010826ba20974580210053d428e8b004200a79851d160084015b5063a2c010802b660c745802104d75410e8b00421bae9821d1600840b5e5023a2c01086ebc60474580210047d438a8b0042008f98715160084015b5062a2c010802b660c545802104d75410a8b004200ae982151600840b5e5022a2c010802bc60454580210053d42ee6b004200a7985dcd60084018f2ebb9ac0108031e5d5735802102d7840ae6b004200a7a851cd60084014f30a39ac010802aea1073580210055cc20e6b004209aea821cd60084375d30439ac010816bca0473580210dd78c08e6b0042008fa8714d60084011f30e29ac010802aea1053580210055cc20a6b004209aea8214d60084015d30429ac010816bca04535802100578c08a6b004205af281d0d60084015e303a1ac010826baa0a435802100574c1486b004200a7b8550d60084014f1
  | 10 => 0xa0c425fe946350d418840b3690ea128310827691c942506210243f42ee8b04420087d85dd160884090fd0b3b286908021f6167650d210043fc2aeca1a420487c855d943484011f700bb286908063e2017650d210145f43ec8a1a42038de87d8d434840559d07b2a649080a3b21d654c921016663b2869924296b4c8550d324847dd18c8a1a6490802e9610714c921005f0c00e29924205ae4864ca414840756d09b2a829080e3d21d655052101e5a3b286a0a4295b348550d4148465d28c6a1a8290802f160c7250521005f0c00e4a0a42059b4875094148413968eca128290827691c9425052104e723b464a0a42009e4874c9414840b5c90c9928290827391d93250521007c2a1a64a0a42059cc874c9314840b5990c9926290816f1205324c52102c3f43ca8b28420587e8794d65084030f90bb82ca1080297a0c74594210052ec18e8b284209a6e821d1650843d4db043a2ca108169da0474594210f53ac08e8b284200a7a801d165084014f3003a2ca108028fa1073594210051ec20e6b284209a6e821cd650843d4db0439aca108169da0473594210f53ac08e6b284200a7a801cd65084014f30039aca108169da0743594210053ac0e86b284209a6e8290d65084014db0521aca108021fa1e40594210043ec3c80b28420087e8710165084010fb0e202ca1080297a0c40594210052ec1880b284209a6e8210165084014db04202ca108169da0440594210053ac0880b28420087e878c165084010fb0f182ca108021fa1c30594210043ec3860b284200a3e840c1650840147b08182ca108269ba08305942100536c1060b284205a76810c165084014eb02182ca108162fa1f545902102c5f43c86b204209aae8290d640840147d0b202c8108028f61640590210054f418eab204200a9d831d5640841355d043aac810876ab608755902102d5b408eab20421dab5811d56408401575003aac810802ae600755902102d5b40ee6b20421dab581dcd640841355d0539ac810802ab60a73590210051fc2ae6b204200a3c855cd640840117d0e29ac8108022f61c535902104d57410a6b204200aad8214d640840b56d0229ac810802ad60453590210055d400a6b204200ab98014d640840147d0b382c8108028f616705902104d56412e0b204200a3e851c1640840147b0a382c810802a7a0c70590210054ec18e0b204209aae821c1640843b55b04382c810816ada0470590210ed5ac08e0b204209aae82d41640840155b05a82c810816ada0750590210055ac0ea0b204200a3e858c1640840147b0b182c8108022fa1c30590210045ec3860b204200a3e850c1640840147b0a182c810826aba08305902100556c1060b204205ab6810c1640840156b02182c8108161f21d655502102c5e43ac8aa042058de87d4d630840b1bd0fa1ac610816b5a07
  | 11 => 0x9040b2e90ea9aa3208029de1953546410053bc32a4a8c825aa79809d5609051f4f700baac1208121fa1773582410043ec2ee6b04820487e85dc960904010fb0bb92c1208028f61253d954101c7b436e2a9a82b693e87dd5435056f878edbaa86a0b43c50c77550d415ae1e3b0eaa1a82cff14311d54350401673003aa86a08cf0f1d76550d410070f29ecaa1a82028bc8759543504073390ea9a86a097ee52055350d410069a3aee2a1a8200d34751c543504bf7290638a86a08021fe1573d89410243e42ae7b128200aad84083625040159b06106c4a0802b960420d894100477c3ac43128209cea625c062504019d2c4b80c4a08263d219719494104c3e43acaa9282afcac62dcd425040b36d03b9a84a0826aba1b625094100596c28c4a128200ba98018942504073590ea9284a0802ab219525094104c76412ed1928209cac625d232504131e90cb8c64a082739189718c94102c5e432e8992823393c855d132504d5958c4ba264a0803271d9434c9416758e42a86992826ae8c6250d32504bfb28e2a1a64a080a3ba1f624c94101c7b436e299282328f587d8e515040136f0ea1ca2a08cecd21543945412feca39a8728a82039b6845ca515040136f0ea14a2a080e6da1170945411cd9b42ee8a8a82059748754d515047366908a9aa2a08026d21d435454119d9a42a86a8a8232d947350d5150401e2aa6a1aa2a08e6cd211525454119d9a42a84a8a8200f2552509515057da68a9b82a2a08021fe1573d81410243e42ae7b02820587e87951658c4014bb072a2cb188162fa1f54592315d62fbb6eaa1c62b6c5f761d5438c4016b3003aa8718803879516550e311956ac36e2a1c6203c9c7450d628c40193aeca1c8518826ab2096450a3166f1a2a2c8a8c629ff165450d518c4090fd0bba2c1188021f61774582310061eba4a9b2a620487e87dd5644c4010fb01baac8988021fe15765513100477c3ac431262038be849d9524c40117b093b2a498826b3a0b644c93104c6e43ac8992623fa5c85591324c40159d0d29264988ff93195524c931005aac28e29926200bd1801c5324c4094e90ab24a2988129da1764545310247a43ac8a8a6204c7476549514c4013a90e992a29880b351d93254531007a2a9264a8a629de9431d91414c4010ff0aba6c0988121f21574d813104c3f43ca6b2e420987c8759554c84131bd0fa9ac79080a2f6137650f210043fc2aeca1e420487c855d943c84131b90eb1a8790803171d56350f216672629aca9964298b4c8550d32c84d5d18c8a1a65908272b1c9645072102ce643a6498e420487e85dcd60c84010fb0bb9ac1908161fa1e545962102c5f43ea8b24420587c8759553884071bb07bb287108021fe157650e210243e42aeca1c42058bc875914388401878eab228710b2f8d15165506214bd9a42a86
  | 12 => 0x816ada0773592511e55ac0ee6b24a200aae829cd649440155b0539ac928816ada0673592510055ac0ce6b24a200a3f855cd649447947d0a392c9288028f61472592510054f418e4b24a200a9d831c9649440195ae4392c928816ada0472592511e55ac08e4b24a200aba801c9649440157300392c9288022fa1f32592510045ec3e64b24a205ab6810c9649440156b02192c9288ce8fa1670592510051ec2ce0b24a23ca3e851c1649440147b0a382c928802a7a0c70592510054ec18e0b24a200aae821c1649440155b04382c928816ada0470592511e55ac08e0b24a233a3e858c1649440147b0b182c9288022fa1c30592510045ec3860b24a233a3e850c1649440147b0a182c928802aba08305925100556c1060b24a205ab6810c1649440156b02182c9288ce8fa1620592510051ec2c40b24a2008be87081649440117b0e102c9288ce8fa1420592510051ec2840b24a200a9e83081649440153b06102c928816ada0420592510055ac0840b24a2038be84dc9639440117b09b92c72880e3760f7650e5102c7b40eeca1ca2bac3e64dd5439440b1790eb2287288030fdd56450e5119e1e3aac8a1ca209aac82591429440187cc8bac65288cf0f9d5648ca510061ebaac9194a200c6d7558a329440b1d90eb126528a3e9ee0175582510061f2a0eca1aa2b7c5c63dd543544071bd0fb1a86a88125721d5350d510152e432a6a1aa2008ef8758862544051bd07bb284a88023760f7650951024b643aa4a12a2098ee829da32544018dceca9464a88161f219754c9512572631aa4992a20187c855d360544030f90ab9ec0a8a3e1f21d53d815100c3e42ae5b02a205a74815cd659047347d0839acb208028f610735964100537410e6b2c8200a6d821cd659040b4ed0239acb208da9d60473596410053d400e6b2c8200a79801cd65904014bd07392cb208029760e725964102d3b40ce4b2c8239a3e84cc9659040147b09992cb208169da0432596410053ac0864b2c8205a76819c165904014eb03382cb208021fa1e30596410043ec3c60b2c820087e870c165904010fb0e182cb208e68fa1030596410051ec2060b2c8200a6e820c165904014db04182cb208169da0430596410053ac0860b2c820087e8788165904010fb0f102cb208021fa1c20596410043ec3840b2c8239a3e84081659040147b08102cb2080297a0c20596410052ec1840b2c8205a768108165904014eb02102cb208163d2057654e4102c3e43acaa9c8200c7565dc553904090fd0bb9ac5208021f6177358a410062f39acb294823fc5e655ce52904018bacab9ca5208031d5957194a4102c7b40eeca94820487e855da32904010ff0cbac65208021fe1d658ca410043ec3acb19482058f4815d9329040b1d90eb126520817391c5624ca411ac7a43ac6a8c8204a768558d51
  | 13 => 0x54ec2020b1ca409ace82041639480159b04082c72900a2f6137650e5204c77416eca1ca4b7c5e63dd543948131b90eb1a87290ff171d56350e524853dc02eab04a400a3d8590364548018bca63b286a92eb0f1937550d520145f43ec8a1aa40493c8755143548074790caa286a90023de1d61185524843e43aa9b02a40187c855c7605480147b0929acb212df0fddb7550e425ae1fbb0eaa1c8400b39801d54390801c3ca6b2a87210faab61b7250e4200697baee4a1c84d3e4c5358d5290963e1ca6a1aa52100b271cd43586420243f42ee6b04840087d85dcd60908094dd0bb1aa4a10023de1d61185420043fc2ae7b02840487c855cf60508130fd0f2a2cb190269b20974596322552f418e8b2c6400a5d831d1658c8134dd043a2cb1910a9b60874596320053b408e8b2c6400a75811d1658c8014f5003a2cb190029e60074596320051f424e2b2c6400a3d849c5658c8134dd0538acb1912a97a0f41596320052ec1e82b2c6409a6e82105658c8014db0420acb190269ba0a705963200536c14e0b2c640087e87901658c8010fb0f202cb190021fa1c40596320043ec3880b2c644aa5e83101658c8014bb06202cb190269ba08405963200536c1080b2c6400a7681101658c8014eb02202cb190021fa1e10596320043ec3c20b2c640087e87041658c8010fb0e082cb190028fa1010596320051ec2020b2c644aa5e83041658c8014bb06082cb190269ba08105963200536c1020b2c64098ec825d9548c8130f90eb2aa9190031b597725523220c7643ac8a946404a6e85591528c8132d90eaa2a5190029be195454a320243f42ee8b0c640087d85dd1618c8cb4f3013aac1192429ee0175582320243f42ee8b04640087d85dd1608c8090fd0bb8ac1190021f61771582320061eba4a9b2a6400a5d83953654c8090fd0fbaac8990021f60375591320043fc2aecaa264098de86dcd544c8051dd0db92a8992d657a1f7550d325d62e3b6eaa1a64d2f0c42dd5434c96d8b8ec3aa8699347c31087550d32005acc00eaa1a643fc5c75d95434c801c3ca9b2a869900e3721d6550d32014ce43aa8a1a646ab8c82551434c801a98ebb928699003531d47250d32355c6420e4a1a643e8ed87d92524c8094d90ab24a49900273e1d43949321fda642a87292646ad8c7450e524c80539d06b8ca49900a73a0d70949320247643ac8a92640996c87551524c89569906aa2a49912ad3a177354932004e643a86a92643fb4c8550d524c87db18e8a1aa499003c35514354932606a629ee0a9264afd8c42dcd424c8010ff0aba6c2990121f21574d85320055ac2021b0a6400ad583043614c8015cb04086c2990023de1d611853202e7930ae030a6400cf1615c0614c8010ff0aba6c0990121f21574d81320055741486b24a200aad8290d649440147b0b202c928
  | 14 => 0xd84dcb6550d754bb06396caa1aea9760f71d95435bd1ec20e3b2a8600c7b709c36550d7547d08386caa1ade8f61070d95435bd2f418e1b2a86baa5d831c36550c014dd04386caa18029b60870d95430053b408e1b2a8600a75811c36550c010fd0f106caa18021f61e20d95430043f43841b2a860087d870836550d7547d08106caa18028f61020d95435bd2f41841b2a8600a5d830836550c014ed02106caa18029d60420d95430043f43c21b2a860087d878436550c010fd0e086caa18021f61c10d95435d51f42021b2a8600a3d840436550d6f4bd06086caa18029760c10d95430053741021b2a8600a6d820436550c01a7680b80caa180356cc170195430063d432e032a8600d3a845c06550c01a7308b80caa1af31ed917019543006ad41ae032a8600d59835c06550d778f6c6b80caa180356d0d70195430069d21ae032a8600d38435c06550c01ab086b80caa18034e1097019543006ad992e032a8600d3b415c06550c01ab062b80caa18031e5c2601954300537410c032a8600a6d821806550c014ed02300caa18029d60460195430063cb80c032a86b7c3c76d955450c0533d07b8aa8a1aeb171db6554d4301ccf426e4a9a8600a79801976250da38bae632cc4a18029e60065989430043f43ecab1286d2e2c42d956250c010fd0e32ac4a18029e60065589435ae2f398ca3128600a79801946250c011df0eb10c4a18029e60065d854367e1eba0cb30a8600a79801966150c010fd0fb2ac2a18021fa1c65585430053cc00cab0a86b6c3e741946150c014f300328c2a18023de1d61185430053cc06ebb028600a79801d76050c010ff0ab96c0a18121f21572d81430043fc2ae3b02860487c855c76050d6f0f90dbaac0a18021fa1f65581430043f438cab0286028de83dc564948011bb07b8ac929002b5a074358e520056ac0e86b1ca400a5d858c1639481359d05ba2c729136b360b7458e5204d67414e8b1ca400acd829d163948015ad033a2c729002b56067458e520052fc2ae8b1ca44da5e851c563948014bb0a38ac729002a7a107158e520054ec20e2b1ca409ace821c5639489b59b0438ac729002b6a007158e520056cc00e2b1ca4008de87d0563948011bb0fa0ac729026b3a084158e5200566c1082b1ca43fa5e859c163948014bb0b382c72913697a147058e520052ec28e0b1ca400a9e841c1639480153b08382c729026b3a087058e5226d66c10e0b1ca400ad6811c163948015ab02382c7290fe97a164058e520052ec2c80b1ca4008de8710163948011bb0e202c7290fe97a144058e520052ec2880b1ca409ace82101639480159b04202c729002b5a044058e520056ac0880b1ca43fa5e8584163948014bb0b082c72900237a1c1058e520046ec3820b1ca43fa5e8504163948014bb0a082c729002a7a101058e5200
  | 15 => 0xc00000c0000180140e800000002c00c00003412400000401c00406c00008400816800804400400400000407800007c00001400402000006400000c00808c0100000000b402400400c00005403000802c02c00003c02c0b800802c07c00001000404801800000005c06c13800000000c02c01002000000008c00002401001c03000800000003400c00006400c00001800c01001c01800402003004800403001c03401400400400000005001400001400000001c07c00007c00002800000c11000c0200180080180000200080d401000008400005801409400003003c02401000000400004c0040080c800804800000007400000801001400405400401400c00006400000403003400000000001c00000c03008000402400000007801407800400800802802800002c02802005c00000001408800c00801800801c0e002400000c02800411400000c00000c00800000000408405400402800c00c0040a40240280000100280140bc01000401801c00c02001c02800003801000001000010800c0080380000380000580080080300080dc0280000340240e400c00803800403801c03002800000001005400003000000000004c0280080ac01400000c00000002800411c07802801401807c0040440680080e00000000000000cc00000009400c04c00801001c00000001002c0040081880600140280100100340000000180000a80d000401c00000000c00c0000000c402800000005401c00002800803401400800000004c00001c05c00c00004c07817400001004400000403000800006c00000000c0100000fc00403002001800803c02001800001400800004800000803c0000000000040b405400002002416c06c01c0480340040140a800400801c00c02001c0300140000100d800000000c01c06000000c03c02800401800800000c00007400400804400003401c0380240000040000240000200f801004000004800008800c02c0140000000000180080f000800001804800000001002814400c0200bc06c0180b804407800816802000000c01401003002407401811800c00000801803c00c01000800400400800c05800801c03002400400400000402001000003800400007403c04c03800800c00c02000800801c08c04400c0000141240000d408000417802800c00000000002005802000803c000065750ff0ab9ec4aa02733189739895400666b9ec5312a8008ef8758862551af8eaebb0cc2aa35b2d5d361985540047bc3ac230aa8ba87f855cf60551ab8daebb14c4a9b53335cf629895300477c3ac4312a6b787f855d36154c0b968c2ba4c2a98032d5d361985530047bc3ac230aa6b787f855d36054c0147b09286caa19421f61c60d954300537410c1b2a8600a6d821836550c014ed02306caa18029d60460d95430063cb80c1b2a86b7a3
  | 16 => 0x220fb0561c04af075f20b855c4061f90000368c0880611d800083074a0fd1d7400044031d9b94d3027a2e794c4eda19b2798998a960e22448e004b431711a945c4944c60000f8800019722680000002a00e88a3c77642c3a10da4e547d030e99044a0006195102c3b63643b19c6035a5c602a0fdc53c1ca14116d84620191ca098489e23f3bb891013a3662ef93e4bba07402d90f8ce269401f02000ca2751978a9c0004da0340000eb400004409c85763871e981b4cfc53e19c0c3c6480000001e644d000020d80007c6656338116870200006a840000000035f00d003a77a00000006680002490000ea22ef01780002a247f1938b3c1dc4032fb80000003db000126cda000015a89900000001d09914ddc5c0137800007a3fd0001ff0cd24791218a7069e49f3599c88ba606f2088d602ca6e24179ea100e2632888ad0c2206941a0658e2c0000000410a3a3fc0570948e6e5bc07c800000077214f8f4097069a3300de42623351c91fb0b9239b27718482865642ff93102b81662a7817c7464392159410e402272ec170c6f81e23f111a06ba4641ee807c6fe5cc052803002669315c88243a02fa1899e74e3c25c1dc91a42c42c037c88e836e3f43249550e2247c0938b5100400031f07b4e1e4432f714e0268137246892c1ce13a082938c6967c508183f40c839101880a500059b1da035c5823fe2eb1fa833e4bd3dc99904721aa207829ce0833735600004ec7a108c8fc0c0c09a1d794a8c56000277874800228b00010a80000000001b000000000000520ccc000391844ce2015300005e43481670a210202dc43108e8d840882741d69610a786621a48a4c00056900010b800024224114142c03932fb00007c02a100015fc2167bb1488ea8da846535d9c845560041fc8000fc64740f7992016c00031990c0f7a00030593ac0001ce3c58f1000653220a95140003d43ed0cd905c1e11020a480d47c32bc91641445941b29e4857012e2d71e1c546110253895100a78a0a688f8dac7c83b986c83ce55e1a00c88a806b803e893cedc70212d836c27a02825106083566b2000058c13e4f02c1037028a5711141504e4c46c1798000b3e0611ff9a202fe5660621a001f41e91c110980000002b38a1c61651400000007c80001df800801000400800000400c00402400002c00000003802c00400c01807800000000000003400000809c0a400c01402c05401c00000c01401400805c01805009001400002c00c04c01c00404c0140000000240e00100b80080040880240080000100040000e00000d00b400403800005800000800003000c0b406c00401000000c03000000c03400804803c05804800404c0200a40340080080c400000400001004c00004007801401000c0e800800c1640d801c0c400000400c00000001c01c02806001801400400c05
  | 17 => 0x7292282540a60668bf87e414c41c0acc0cc48127b1c309c05b83689bfcc4c0c62f50c303a817e22617c448e14e0d60d68b7644b34ba098e7e56023e83a8d821df3e794206d819325f170401456a18481d42d008c3570dc85b2445083885c7646462830ba00007e42358fa89203d8000165c83a5701e08144b9a0f42a48828cc21892d59dfc5d81bf2ba8cf0d4a00031f80006a877b06b168491e0003a68ef40004aa000027800080f0011b0c5da0002b7800010c0002fe91543cc0003eb9184c140000fa9e9904452201c8000f9441a0001944bde4361790e408644a025220a472a70624d06542e80f21e1904ccb41d81881008ca873e00009fc7de06e05180000003f62c48d344165d9289084468a0922488ab8fa650d0f18c38de66fa05d189ca4a1c73341604a300000001d900560000001a2800032000002b45e200000000006be5f81d3860c88826e3b41de0000000211910459218e006800023812900017e4dc24b200015accb87900b096b00007aa00000005ee69e0b49b5c0c400014300e88be1f138e006800052015118f0f5c0cf3468000da43b128d800059c1700ad98700000002be03802604fe0181d7800060901919004e67a02731640a484cd05a8af0e364731f603dcc740d9314071106609531c04206b85c21f70b44840775021971cc1e5980110040e0000805da0446a667d3b294c0e2431830a9cc07142c430d8b284387be394042400013e1cc9b301023302661a585f811f35a8b801420363628cc8ff00002f58ed4eaa1983c49f60e961d507a8734b7c214365883d0486ba3d21fdc6e20eb24295850306433e380008ec76f00708e0ecc6ce096a06c5ec57d1a90d1cfec4a322d873cfe80000000f5443e3cd0090918a6c2991db1c9400000f19097b049c4c72958c7836a7dd00003c00007fd2e50000cf25b533902f000000029d1f94ea040a000086c4fa0e31b79468faa5a01730c0ce8e1f0042039460a42d30d0b5c6906f50cc80007e22f837013a0cae24904d9014daa75c1e88dd800034a0c780000000002ce1db0d600000000460a147de2a61bd01227fb0201ff8dbe3312250e688186a332f202d0540001119600c3020d000118000a1920799e8caa26b10bb875c4904943a08c6ca66708042a080ef83d70230d4000000011b20ac0002ff0001dac17e58a0001cc40005da02280000000b1000194c0004ad2d18000b8a0000000000aaa33f31a1e4c64c5dc335a0704f801413d915000000022411580f643b0001fb80007790001fc8dde36e3610174bda45005a0d648bc04e3cd00449f04ba3dd14a4e0e0002931bc43ca5a911b8000b1a3083e900000000003a2000000000712f1bf40001a03271d84db00000000d0c5a073a2c18000f925370c01f043e670e26800000007ce000000050273d2d89bb425654200000002
  | 18 => 0x38180000002bf0000000d201b92b62010c405851f3000106c000136a09cc5e7f132e8208eec31c2461ccce925433ca8cf84ee7f914706c0d0a5581c20d18b0e73435e8e5c0362941c2a08c7302130769780a3c36205519cc6ee1880d999dc15267c108055445a3113ac053c0a058b00000009f40002ef0000f6479c1d314b444019400010d073c4c33c2079048004b32393a49ca25d2b920dc39631235111b82242f4407089091c1fe17e8f58e5278c31b8ce8370588000180409a6a100000000001460001f9cf78115000000000008700010fd02a6420000d5493c00000000010640003361cb00000000e3207c00063534a9a4400039c04e1d5c31a0002690f688006dc1719f5088e31517716d0ed47dc1149a107664063a99c5caf66820918a6c1f082c03985d8e343ed2e88a00d327a503000008200cb186813cc9858e04c8000cbe4d62d400007062df00009c4d8e40726f8f18d6c03c0d89274d3a50900010cccb05a71ec800019425537487b0fd22a40b61690a4e70a05c0b488c467a0e1000004c17837c14383505963991a1c21e1f712c9b285540ce1d8156c35c5130bd9e504ca33314188cc0001f43c892d0f9a3c808088c09fe1e023d0e746bc81d328081809808b228817882828d40496c8c4455001090d40001323f31ad00000003b48a200700000000fe018a2071e9187c000421316000081c00005219bcbe8427064802400032d0911d6462c2790318f784ce3510ee85ac0005282c90b18de447505f000026c46a28a802c00050700000b45b814b20680001300c700004e43a661900013f0ada08909780544543fa047076899600003d203452c3cb06f041851401628097a496a1643c7143c37614a2e41934f9815213505cc00036d3da82c0d4e0ec2ca89302b42341360858c264c10001a80cb28013418af80ae6a906a1878b7e71f26e925cea85d71579a309ae6b9000148c60018637803a0a9a82839c8308d7e1c80fe8000f020c81df1ed856c2f02679adc4a243c30186e84ae3a50de808c6088170d39a706565ad3d806d81c21a5010034086e5213958b74dd84670ef19e03080c011917e879810c3a79c5488c0fe3621ecc4005b305c85e883e1a63f598388443dc0358838c522ac2cd0730fbe11703b1010cce6f72819e34c286de31819d042a48821480b063a5860c29b90b4c6bc22e130871213f26e12bc92c3862a505085347ef0000408e0a5e823d90785ac15f0000000f687ab24aa0b45aa0002af80007562692c982cc3b20000999d9c44c00000000000000000000f38afc6cf3a605643187b1000000000012019c9094b607f02e20ef0f0a285000000000044202a9e5805c0533cd8688ac40ff0b500003163f300014ecf064533868b4cbcc4f237f1ab42786d90fb17f89fa7383551d487ea26216d8158d167a21
  | 19 => 0x27a8478d3600036d80000000000c08b144326443ff8094ab205c236996c71e4d50290ac8c482841548da052a20114e80000000003449df8a041a92b7129902c0002f2954ca203ba1638558f04762183000000056300007a0cec000000163ca6800031b00009c40ab22700009da0003060000518270158953873e0001ba0facba021a00001dc0002de3169bac63431f39d80fcb3a7362e9204c5840002291cd4e4e80a3a19d6caac00004a0dec69c4bf40d15942505f20f7081421c5a203c9c740000e421413dc0000000fe08f4a2c5f325e00000000000001b20150000000062859a4d11a20cb02de41940f00008e0190000090471c38b0001a7cf7e10d33a9574c1a67b2d782f42a000024315203800973108af45d46c9304046887000000019a80000cc3e0066843a3ae1739ea4fc023c3371e002a84b33028e800004d40001d8048a47e0a4823c00000040613280003ca29700000002c33150f7ce900000a0121ccca4123d7a00c0007ad2dc96dc00000028580009261bc3038b84000000000000083805800007fc0001dc00000004a617114c01c41cc0d300020402ea0000000000b4a18700008bc5d64630fc12acdf67b700000000006d3000000000000027a005ccfe000000000008e6e6278988c5b030a1be93206526da31900005b443d01d9c903d437e1e78000e8000000000006e64770000cb856e1c90001aa0a887e800000007c20001041364f70771308042903248b23917c0c4a0002f10000000577000130106a3963898000000568000070c00000000000000006a40f902bc0007970360cf4c962a815d0000aec83119181c05c40591640304e7868f22e8ca00664c52121a180000410151d1800000022ba048e5e4093b80000000535257172c0000001b380002ba22237b00000005740f5955cc7253d06f87ec5603fb0688e30d5670b2800d5c54c01c12681f882c04229795cc00003529c8000ee8000000000000051900000010283a4366800059809600010049423600000dd4b320000001fb45f600000c08b800007f0001bf045617d33192a07925aa2739b8cb9c33b00001e0e8a77d1e012005c8692078927000000010f175406e00011085044fc0002a317ec4f000028f897cb2279f0d18eb0fea5e32580848b7a0dd02400004b08081ad800000015809c00000000930001430092314329176c34200009a98580000000001f0899220c000136c00037027d96e8f8c20217a84582282a50001b74c040003409f10bce3881ab046c8740670d79f4494a7cb0ce1f6c1f81c51d405c896c0830920de00000ef06c01f01146550cf030c6c601e1e293846040272330f1cf104b92761c240007f31749e6069825638c98b828e5f5000133800072e09280000000f60b6951c7ce46f269800085e0001f28000b1805a0000ea40007560c88090
  | 20 => 0xf0c3b700014b03ac5fc0af20e4c9e1213369f644c07e12ad0fa4f5836a1d11f5890834131e98007d000000004ec43000026f11e0e9c3b818082c8ab822c2548000c2e000375000000000025613a8f4e4830000e34ba87143531fe906017c325000104a59e09301c81d25e12f209ac96e12c0001abc7840d205b828068409031891249304b13968a243821b43740a4104279e156800037c19d00011c46f44580468c9452e3073471b9c9c836b3c7954800051c29f92ec00004a24c95e80004d83630894000319000000000000017c8b2c000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x9a582d86dd77250e42006161d9801d5434c801b08426007550d320055264075dc9434c801549901d47250d32254c32615450d524c8d550c9755143549320062a5c9801c96494401838766007550d41006c40c5801d54350401531901d77150d410054c640751c543504733149854d43545412fd4525d5350d515047332498549425454100616dd9801d5438c495c44765493254531005166407558d43c8401439901d56450e210066121d434c941484bfa848650d3250521357211d9434c941485b17049550d32505210048e640855cd6408401259902157458c210041e640875954308401439901d56450c21005166407558d430840107997215435802100709589615d021d4001c4562585730875000718589615c021d400182d846087650d500050d644421d94354001439901087650d5000516643321d9435416785980cc87650d500061560d811d94354001865826047650d500050e643411d9435414f83980d047650d5000513648311d94354001459900c47650d500060e611801d94354001859836007650d500061aa09801d94354001869826007650d500061ca05801d94354001871816007650d5000706501301d9435400107a981d97050d500040f6607418d6254001839801d063589500060d1d18118d6254001a0c42219434c95000583650635893254001a0c8418d624c9500059164463589325400105d981cc64585500061660073191615400184c73608645855000607210735896154001a143121943505500058564c645854154001a1483191615055000589648645854154001838766007550d401cf0c1d951505505000131b936077454140004ca6488750d50500013319121d43541400c4c62617350d505003183886dd172541400c4ca2617250950500315299718942541400c4cc647835055050031632969c541541400c4cc26171505505017bc30765c54154140635c424d71505505003131b9850e31541400044e25d844c55050003238966112154140006161d9801d5434c095c487654932541300241ea6387591504c00131b9460b7354130004d26488750d504c0013519121d43541300bcc62617450d504c02f31b9850e42541300bcd264b844c9504c0011589761132541301fd1625d644c9504c02f64a969c932541300bcd2261724c9504c17fc48765c9325413060dc2251724c9504c02f85886dcd715413019d0e25d64505504c02f350985c531541300bd5465c614c5504c0032589660d2154130005166407558d43c8001439901d76450d2000c6a25d844c940480d5c887650d32501200050e6407559143c4001459901d76350d102ff241d94350530440031d097611314c11004d2a25d6450920440012a99421932481100047464c8750520440019a087509414811000c7825d8448520440032e09660d2148110
  | 1 => 0x1a1a43c0636008cc003696c5e2e1d00006002b800be000d0302c0b00148b800000990c7d4118c000000000b064001ec2083000001e46001fcee87191d0f219098a8505a2800000112a9f800181c1a0ea293880008000005c780716130944d00034c03f3b1780056398ec8a6f118e4801b07184621425920382d2a214a67c090d44a0a110009c812e885086a00000f03631200a21f358208e012100060152c8f89e2704880e043221c87a49338dc561d19814ca24371e88201030302000205080d090301050029100b010e0400000611060400000003021b000b03010000000607190c340200554a47435c06550c0152a9290d70195430050ea58435c06550c0145a9610d70195430044e660425c06550c0151a9310970195430054c644425c06550c0151a94cc9701954300546a4f415c06550c01159980c5701954300546a50315c06550c01549920c570195430061aa09701806550c01869825c060195430061ca05701806550c01871815c06019543006165cd801966250c018397460065985430060edd9801d54390
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x520c000182d000003812058188129c588011802309a9109801d5434c801580d0884c00eaa1a64008c46a4316007550d410056034418b003aa86a0802a05a11088650d3254001504d008443286992a0008836a48418d624c95000641320420c6b1264a80032048464463589325400100ed490839ac4b0aa000a81688312194350550005423401890ca1a82a8002215a920c645854154001908c8106322c2a0aa000c8120d921916150550
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x3
  | 10 => 0x138c
  | 11 => 0x138d
  | 12 => 0x138e
  | 13 => 0x98c
  | 14 => 0x98d
  | 15 => 0x98e
  | 16 => 0x150c
  | 17 => 0x150d
  | 18 => 0x150e
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0xa0c
  | 22 => 0xa0e
  | 23 => 0xa4c
  | 24 => 0xa4d
  | 25 => 0x198c
  | 26 => 0x198d
  | 27 => 0x209
  | 28 => 0x20c
  | 29 => 0x20d
  | 30 => 0x20e
  | 31 => 0xb09
  | 32 => 0xb0c
  | 33 => 0xb0d
  | 34 => 0xb0e
  | 35 => 0x1409
  | 36 => 0x140c
  | 37 => 0x140d
  | 38 => 0x140e
  | 39 => 0x1549
  | 40 => 0x154c
  | 41 => 0x154d
  | 42 => 0x154e
  | 43 => 0xb49
  | 44 => 0xb4d
  | 45 => 0xb4e
  | 46 => 0x1449
  | 47 => 0x144d
  | 48 => 0x144e
  | 49 => 0xb89
  | 50 => 0xb8c
  | 51 => 0xb8e
  | 52 => 0x1489
  | 53 => 0x148c
  | 54 => 0x148e
  | 55 => 0xbc9
  | 56 => 0xbcc
  | 57 => 0xbcd
  | 58 => 0x14c9
  | 59 => 0x14cc
  | 60 => 0x14cd
  | 61 => 0xcc9
  | 62 => 0xccd
  | 63 => 0xcce
  | 64 => 0x15c9
  | 65 => 0x15cd
  | 66 => 0x15ce
  | 67 => 0xd09
  | 68 => 0xd0c
  | 69 => 0xd0e
  | 70 => 0x1609
  | 71 => 0x160c
  | 72 => 0x160e
  | 73 => 0xd49
  | 74 => 0xd4c
  | 75 => 0xd4d
  | 76 => 0x1649
  | 77 => 0x164c
  | 78 => 0x164d
  | 79 => 0xe89
  | 80 => 0xe8e
  | 81 => 0xec9
  | 82 => 0xecd
  | 83 => 0x1049
  | 84 => 0x104c
  | 85 => 0x249
  | 86 => 0xb8956
  | 87 => 0x289
  | 88 => 0x16c9
  | 89 => 0x1849
  | 90 => 0xa4a
  | 91 => 0x19c9
  | 92 => 0x4c
  | 93 => 0xb9396
  | 94 => 0x4d
  | 95 => 0xe8a
  | 96 => 0xcc996
  | 97 => 0x3c9
  | 98 => 0x409
  | 99 => 0x1709
  | 100 => 0x1889
  | 101 => 0xa4b
  | 102 => 0x1a09
  | 103 => 0xcd516
  | 104 => 0x8c
  | 105 => 0x8d
  | 106 => 0xe8b
  | 107 => 0xa49d5
  | 108 => 0x124c
  | 109 => 0xcc9d5
  | 110 => 0x128c
  | 111 => 0x18c9
  | 112 => 0x1789
  | 113 => 0x180c
  | 114 => 0x130c
  | 115 => 0x1a49
  | 116 => 0x17c9
  | 117 => 0x134c
  | 118 => 0xa4a14
  | 119 => 0xb8a14
  | 120 => 0x124d
  | 121 => 0x128d
  | 122 => 0x168d
  | 123 => 0x12cd
  | 124 => 0x1a89
  | 125 => 0x1949
  | 126 => 0x134d
  | 127 => 0xb8a54
  | 128 => 0x148a54
  | 129 => 0x2c9
  | 130 => 0x4e
  | 131 => 0x124e
  | 132 => 0xcca55
  | 133 => 0x15ca55
  | 134 => 0x449
  | 135 => 0x8e
  | 136 => 0x128e
  | 137 => 0x12ce
  | 138 => 0x5c9
  | 139 => 0x130e
  | 140 => 0x749
  | 141 => 0x168e
  | 142 => 0x180e
  | 143 => 0x198a
  | 144 => 0x198b
  | 145 => 0xb9994
  | 146 => 0x149994
  | 147 => 0xcd995
  | 148 => 0x15d995
  | 149 => 0xb8b16
  | 150 => 0xccb16
  | 151 => 0xb9416
  | 152 => 0xcd556
  | 153 => 0xbcb55
  | 154 => 0x2cc
  | 155 => 0xccb55
  | 156 => 0x184c
  | 157 => 0x178a
  | 158 => 0x19cc
  | 159 => 0xbd455
  | 160 => 0x24e
  | 161 => 0x2cd
  | 162 => 0xd0b94
  | 163 => 0x16cd
  | 164 => 0x19cd
  | 165 => 0x28e
  | 166 => 0x16ce
  | 167 => 0x184e
  | 168 => 0x188c
  | 169 => 0x44c
  | 170 => 0x1a0c
  | 171 => 0x3ce
  | 172 => 0xd4d14
  | 173 => 0x44d
  | 174 => 0x170d
  | 175 => 0x18cb
  | 176 => 0x1a0d
  | 177 => 0xd5614
  | 178 => 0x40e
  | 179 => 0x170e
  | 180 => 0x188e
  | 181 => 0x74c
  | 182 => 0x5cd
  | 183 => 0x194c
  | 184 => 0x1a8c
  | 185 => 0x1a4d
  | 186 => 0x17cd
  | 187 => 0x18ce
  | 188 => 0x178e
  | 189 => 0x94b96
  | 190 => 0x138b96
  | 191 => 0x98cd6
  | 192 => 0x150cd6
  | 193 => 0xcca49dd
  | 194 => 0x9ca55
  | 195 => 0xa0a54
  | 196 => 0x130a54
  | 197 => 0x10e
  | 198 => 0xb8a4a1c
  | 199 => 0x12ca55
  | 200 => 0xce
  | 201 => 0x198a54
  | 202 => 0x198a55
  | 203 => 0x140b96
  | 204 => 0x154cd6
  | 205 => 0x144bd5
  | 206 => 0xccb96
  | 207 => 0x74b94
  | 208 => 0x194b94
  | 209 => 0x5ccd5
  | 210 => 0x17ccd5
  | 211 => 0x160d54
  | 212 => 0x170cd6
  | 213 => 0x1a0d54
  | 214 => 0x184b96
  | 215 => 0x19cbd5
  | 216 => 0xccb8b1e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2397
  | 6 => 7351
  | 5 => 2106
  | 4 => 136
  | 3 => 15
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (98277+((h/799+packedAt gbK7 (88689+(h % 799)*12) 12) % 3828)*13) 13
  | 6 => packedAt gbK6 (387148+((h/2450+packedAt gbK6 (352848+(h % 2450)*14) 14) % 11741)*14) 14
  | 5 => packedAt gbK5 (132678+((h/702+packedAt gbK5 (124254+(h % 702)*12) 12) % 2528)*13) 13
  | 4 => packedAt gbK4 (9880+((h/45+packedAt gbK4 (9520+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt gbK3 (1240+((h/5+packedAt gbK3 (1215+(h % 5)*5) 5) % 24)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe31c0e3f18c78e0ff1f83f83fc20878474cf
  | 1 => 0x703e00fc7e0f8f00e1e3fc3fc3cc1199a4b33
  | 2 => 0x7fc000ff8ff00fff01fc003ffc1061e638c3c
  | 3 => 0x7fffff000ffff00001ffffc000207e07c0fc0
  | 4 => 0xf800000000ffffffffe000000003f8007ff000
  | 5 => 0xffffffffff000000000000000003ffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40410482090001020300482081102082801045
  | 1 => 0x9202210442404890444215013028c1090a4112
  | 2 => 0x5a40228902900252014808a4a810614208c28
  | 3 => 0x2128486000ba9200a099229808820220740e80
  | 4 => 0x3000004000d4e4c8c8c00310100a48005f6000
  | 5 => 0xc6d3938f24000001010004206331b5df800000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffe8fefaeee8ffffffe8fefaeee8ffffffe8fefaeee8ffffffe8fefaeee8ffffffe8fefaeee8ffffffe8fefaeee8ffffffe8fefaeee8ffffffe8fefaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_28023
namespace PEqualNP.Outside.L_meta_28023
open PEqualNP.Outside.L_meta_28023.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 60 := (concat bs0_4_0 bs0_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 40 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 4 := bs1_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 4 := bs2_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 16 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 92 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 15 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 136 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_2080 : Interval gbAtlas 5 2080 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2106 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))))) (concat (concat (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280))) (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))) (concat (concat (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664)) (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792))) (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)))))))
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
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7351 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)))))) (concat (concat (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720))))) (concat (concat (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392))) (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648))))))) (concat (concat (concat (concat (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 bgb_6_4096)))) (concat (concat (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320))) (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544))))) (concat (concat (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768))) (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 bgb_6_4992)))) (concat (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat (concat bgb_6_5120 bgb_6_5152) (concat bgb_6_5184 bgb_6_5216))) (concat (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)) (concat (concat bgb_6_5376 bgb_6_5408) (concat bgb_6_5440 bgb_6_5472)))))) (concat (concat (concat (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat (concat bgb_6_5600 bgb_6_5632) (concat bgb_6_5664 bgb_6_5696))) (concat (concat bgb_6_5728 (concat bgb_6_5760 bgb_6_5792)) (concat (concat bgb_6_5824 bgb_6_5856) (concat bgb_6_5888 bgb_6_5920)))) (concat (concat (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016)) (concat (concat bgb_6_6048 bgb_6_6080) (concat bgb_6_6112 bgb_6_6144))) (concat (concat (concat bgb_6_6176 bgb_6_6208) (concat bgb_6_6240 bgb_6_6272)) (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400))))) (concat (concat (concat (concat bgb_6_6432 (concat bgb_6_6464 bgb_6_6496)) (concat (concat bgb_6_6528 bgb_6_6560) (concat bgb_6_6592 bgb_6_6624))) (concat (concat bgb_6_6656 (concat bgb_6_6688 bgb_6_6720)) (concat (concat bgb_6_6752 bgb_6_6784) (concat bgb_6_6816 bgb_6_6848)))) (concat (concat (concat bgb_6_6880 (concat bgb_6_6912 bgb_6_6944)) (concat (concat bgb_6_6976 bgb_6_7008) (concat bgb_6_7040 bgb_6_7072))) (concat (concat (concat bgb_6_7104 bgb_6_7136) (concat bgb_6_7168 bgb_6_7200)) (concat (concat bgb_6_7232 bgb_6_7264) (concat bgb_6_7296 bgb_6_7328))))))))
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
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2397 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)))))) (concat (concat (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440)))) (concat (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))) (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))))) (concat (concat (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888)) (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 (concat bgb_7_2016 bgb_7_2048)))) (concat (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208))) (concat (concat bgb_7_2240 bgb_7_2272) (concat bgb_7_2304 (concat bgb_7_2336 bgb_7_2368)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
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
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
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
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 4 zero,inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffffffffffffe8fefaeee8fffffffffefeeeeeffffffe8fefaeee8ffffffffffffffffffffffe8fefaeee8fffffffffefeeeeeffffffe8fefaeee8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,64,192)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,64,192)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_28023.Model.Repr at out
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

def mono : List Gate := [⟨.or,[7,5]⟩,⟨.or,[7,6]⟩,⟨.or,[0,2]⟩,⟨.or,[4,10]⟩,⟨.or,[4,8]⟩,⟨.or,[7,10]⟩,⟨.and,[5,13]⟩,⟨.and,[9,11]⟩,⟨.and,[0,3]⟩,⟨.and,[12,1]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_28023

open PEqualNP.Outside.L_meta_28023 in
theorem PEqualNP.Outside.L_meta_28023 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
