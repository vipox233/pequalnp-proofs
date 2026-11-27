import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_27835.Model
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


end PEqualNP.Outside.L_meta_27835.Model

namespace PEqualNP.Outside.L_meta_27835
open PEqualNP.Outside.L_meta_27835.Model
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

end PEqualNP.Outside.L_meta_27835

namespace PEqualNP.Outside.L_meta_27835
open PEqualNP.Outside.L_meta_27835.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x4e0099e5604e0e1a0c81900146001400a96521c900487d08f2200b800000c00002d00044000000c6c00250012a600015001200a1d008c008006820600000080006380830c0828bff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fa40fd40f940fc40ff30fb30fe30fd30fc30f830ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x8c482540000000e4fc009c000028cc0000000118350000000000516494005c00f000400000000000000070003000008400007c00000000014538c0011c00010400000000d4002000000000000000000148004c0154e000b55ca400000000000000010c006878e9580000014c1d612cbd08ac0010c4012000b06c0c380000593c2cdc000000880004140018000000b8f460a8f8743c0000549124c800644534000000d0015000000081100000011400080000000000000000d800a00099316928ec0004000a08000200040026000800000002000208000000040402000000017a50d0ef2a1a1ded4143bc282876e5210edaa421dd94443baa88877a5010ef2a021de94342bca8685775150ae8a2a15794c42aea9885765110aeaa2215e94042bca80857651ccaeaa3995e94232bca84657b504caf0a0995e94341bca86836f52506d8a4a0d794c41aea98836e52106daa420de94041bca80836e52cc6daa598de94231bca84637b504c6f0a098cf950219eaa0435e53086baa610f948421bd280437950086f2a9205e94e40afa9a815c5350376a8a076d4d40bc29a81d853502b0a6a06ed0d40dca1a817a50102f6a9985e55330bd284613e540c27aa8185b94830b6a906176510c2eaa2185ed5030dd2a06179540c372a8184e55030bd29861da530c3b686187610c30f529061e9520c3b66418764c830f928861f1510c3b66218764c430af29e415d53c82bca7885754f10
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x79200c0aa11802400ec26b2e680280500590880a0670880012002d1d25863543429618d50d07255448421d298853503496214d40d498453503516114d40c614f43502396595030c618d540c31954d0c3096594430c2c96210c30b4584430c3295494830ca551520c31954cc830b4587320c319544c830cc552510c3315454430d8549510c31954cc430b258b310c319544c430
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc408010000001905896114d40a12e431aa8185117118d540c308aa2c3990618255162cc430
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
  | 5 => packedAt s0K5 (802+((h/14+packedAt s0K5 (704+(h % 14)*7) 7) % 69)*7) 7
  | 4 => packedAt s0K4 (2697+((h/30+packedAt s0K4 (2457+(h % 30)*8) 8) % 193)*8) 8
  | 3 => packedAt s0K3 (990+((h/8+packedAt s0K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s0K2 (249+((h/1+packedAt s0K2 (245+(h % 1)*4) 4) % 12)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xf8f038e3c7fff071c70e3870f1fffc04cc3fc
  | 2 => 0xf00ffc0fff878ff81f80fc07ffe381fe80fccf
  | 3 => 0xffff03ff80fffe000fff80ffc01ff0f0f0f
  | 4 => 0xfff000003ffff01fffff00000ffffe01f00ff0
  | 5 => 0xffffffffc000001ffffffffff0000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xa3119914475508251418e0d1a304cc4c4cc15c
  | 2 => 0x25222928093012080c822402652114948054c5
  | 3 => 0x4a44520492032413200449300a482929050b0a
  | 4 => 0x4c0062492022065a492600204c923031900ea0
  | 5 => 0x800880000044488492489244800040006aa000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffff0fcccf000fffffff0fcccf000fffffff0fcccf000fffffff0fcccf000fffffff0fcccf000fffffff0fcccf000fffffff0fcccf000fffffff0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_27835
namespace PEqualNP.Outside.L_meta_27835
open PEqualNP.Outside.L_meta_27835.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xc5a00b9e469ccae2a4d40b0e0110534214810008b123a942031481580385109f00986863024780000120e00bc010540002c0000d91001402c00410ca18311010014bff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fa40fd40f940fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3d91906872b1505c472d0841a103b87c225e000641252000ece6001a8dcec00000a436280d1080e06279d0ea270000c1000001b06c80001b8024d1c0cc005c00000007900124e47105010580018800b02a1e17c00000000000412712c4c0f0000000500016400001e9fc00002602ce0394218902172a9a03a2f000009067001f8462d0c090d48234800c8000a1f4a253220ac000009000683f43128000000088000030800b60e001140000368c8de1e31894601c42858c02000198f83a09808800c3d0000057001740000001e07c6500000d60002800004300054000102030c00030001020100000200040c000f0b01070002060000000101090001111003000e0201020003000202bd286877950d0ebaa5a1d754743ed28687d950d0ebca721db94843b6a9087765110eeaa221de94043bca80875e5410f3ca821f394843aea9087cd5210e9aa421f594443aea8887d55110eaaa221f694043eca80877a50d0af2a1a15794e42aea9c855f5350ab8a6a15794c42aea9885765110aeaa2215e94042bca80855e54ccab8a9995754732aea9c655e544cab8a89973d4932e721265cd424cabea2995794c32bd286837950d06bca720d754e41afa9a835c53506bca620d754c41b7290836d52106f4a020de54041af2a6635c54cc6baa598d754e31af2a2635c544c6bea498f5d4531eb20a63d5414c6bca618d794f21aea9e435e53886baa710d794d21aea9a437b50486f0a090cf950219eaa0435e53086baa610f948421bd2804379500873887a05794e40aea9c817954903b4a7207654e40eda1c81d843903b66520764ca40ed98c81d931902bea6a05714d40ce21a81bb54503b6a6a07614d40eda1a81ba435037086a07610d40cc21a81bb425037284a076cc940ec99281bb415037282a076cc540ec98a817a501027ca9184f55230af29e415d53c827ca8104f55020af298415d53082eca2105d54420af29e215d53c427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1880562869432000000c0132100009b000a03af009419a466c920029070b4e2078c0000b0004416852a88e1700b800000756003ca8f80302421152020028a000008122001060218003a65825410f455294443d19495110f455254443d254a5010f515194043d25495010f5151540439558454cca55611513293195424ca4d621533193588544c65465505318719153486396414121c955121087612154021a358843d02956110f40b258843902d16110e40a358843502956110d40a698f545025a65d0d40a698e43502a96210d40ac584435025a6510d40b258843502d16110d40a6994435031a6510d40e298843502996210d40e258843502896210d40e498443502996110d40e458443502916110d40a618d425029864cc940a61913250389424c940a618d415029864cc540a61913150391414c540
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x45218034000101c401a058a6110d40d04c4b0886a0681625844350248b88c999281245c4644c940910eca1264a0489721933150244b90c898a81241d9414c540
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
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 63)*7) 7
  | 4 => packedAt s1K4 (4032+((h/45+packedAt s1K4 (3672+(h % 45)*8) 8) % 198)*9) 9
  | 3 => packedAt s1K3 (2012+((h/16+packedAt s1K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s1K2 (453+((h/3+packedAt s1K2 (441+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf0e3c38e3cffe3f38e38238e38ff8ff3243cf
  | 2 => 0xff03fc0fff1ffc7c0fc03c0fff1ff0f407cf3
  | 3 => 0xf0003fff03fe3ff8ff0003ff03fe3ff0838f3c
  | 4 => 0xffffc00003ffc000fffffc0003ffc000fc0fc0
  | 5 => 0xfffffffffc000000fffffffffc000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xa1a046114469244028a0ca0c308248aa324145
  | 2 => 0x42048882808408084044104049109204401492
  | 3 => 0x491120090090019100209202242440808a28
  | 4 => 0x646c01b4d2249c92da6938020bc90666d40fc0
  | 5 => 0x888022000009212424924324900000882b6000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffff0faa0faa0fffffff0faa0faa0fffffff0faa0faa0fffffff0faa0faa0fffffff0faa0faa0fffffff0faa0faa0fffffff0faa0faa0fffffff0faa0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_27835
namespace PEqualNP.Outside.L_meta_27835
open PEqualNP.Outside.L_meta_27835.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xbc1340a007006c98b3a006cf290651100108c00012186b14ae480000819b81484fad38acca7243c00000600373a1d8282200000000190b000000000ec02c02009b5009020000b8017343002a2a06041810004011080000008046800008083b7290876d5210eeca221dd54443bd28087795010ebca6215754c42bb28885755110af4a0215e54042bd286657950ccaeca3195d546329faa2653c544caf4a1a0de54341b7294836d52906bea6a0d714d419f2a0633d540c6dca418db54831bd2806379500c6bca790d754f219f2a4433d54886f6a090de14121bb28e817551d02bca7205754e40b7a92816c52502dca5985b54b309f2a4613d548c2eea2985d145309f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
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
  | 0 => 0xe3c7c7f1fe3ff8e38e0e383f1f83ffe61339f
  | 1 => 0xf03f807fe3ffe3f03f00fc03fe3ff83e863cf3
  | 3 => 0x3fff8ffc03fc7fc000fffc7fc03fc107cf1c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x404610c15105400a182a40a0a0490d18611185
  | 1 => 0x288849228a4204502110a449121490a4862432
  | 3 => 0xa511282408c880b4400429185482a285024e18
  | 4 => 0xc40132484080c9268a46001069230309280bc0
  | 5 => 0x8224000931312493498d26200040430d5b000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_27835
namespace PEqualNP.Outside.L_meta_27835
open PEqualNP.Outside.L_meta_27835.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x6802b00846805c01d1300e51b8009c01f6eb1a8000947805400000100001222ec0280e6c0005e01a10388000032000333a902a608600002ed980c00544b104043161ca4514442d6b23c0018000020c3810004081180410000100810838007b7290876d5210eeca221dd54443bd28087795010ebca6215754c42bb28885755110af4a0215e54042bd286657950ccaeca3195d546329faa2653c544caf4a1a0de54341b7294836d52906bea6a0d714d419f2a0633d540c6dca418db54831bd2806379500c6bca790d754f219f2a4433d54886f6a090de14121bb28e817551d02bca7205754e40b7a92816c52502dca5985b54b309f2a4613d548c2eea2985d145309f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 60
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (718+((h/13+packedAt s3K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s3K4 (1760+((h/20+packedAt s3K4 (1620+(h % 20)*7) 7) % 88)*7) 7
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe3c7c7f1fe3ff8e38e0e383f1f83ffe61339f
  | 1 => 0xf03f807fe3ffe3f03f00fc03fe3ff83e863cf3
  | 2 => 0x3fff8ffc03fc7fc000fffc7fc03fc107cf1c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x404610c15105400a182a40a0a0490d18611185
  | 1 => 0x288849228a4204502110a449121490a4862432
  | 2 => 0xa511282408c880b4400429185482a285024e18
  | 4 => 0xc40132484080c9268a46001069230309280bc0
  | 5 => 0x8224000931312493498d26200040430d5b000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfffff8f8ececa8a8fffff8f8ececa8a8fffff8f8ececa8a8fffff8f8ececa8a8fffff8f8ececa8a8fffff8f8ececa8a8fffff8f8ececa8a8fffff8f8ececa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_27835
namespace PEqualNP.Outside.L_meta_27835
open PEqualNP.Outside.L_meta_27835.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xb8000800190a0000b00b118812bc3a72c889a80070d8000000002a6808a5c0078622a80044800000280000300ad30d00001000084000007c0004a00f2d00000001800018247482900000001c00001070000400001c0040400003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21f621fd21f521fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10f610fd10fc10f410
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xca0000000c63f0c80000000000000850c0000000000dc000400000200900000000000104000018984000000178d80000000001700000000000018004033000005d3507c00000000000000000000000000000000000000002d800000000000000000000003d00000007800000001b211180000000000000000000000001d00000001f82622120000000000001600348cc0057000000000000000000000000000000000000000000000000000000008000000000000000001c0de87258005000000000a00000000055420000058388000000002040083000000000000000000001e400000009c0625000000073000000000000000000000000000310005c00000009a56000000000000003c000000000000000000003b000000005000002310800000000000000026000ee070000000540000000003e8008649000008e4f151e840002500010000000000003d800000c000ec003900000005a0000000001d0000000131b89c44000001a48000000000000002a00000000059002080000001a05829338000000000000000000006845000000000001b400000000000000a000c82f000d4ea6b0017cb802001485600000007c00000483a531c000fe000004400000b0c80000000005a00001f0003600000000000000000043200a200390c000000780000000e000000000000000000000c0000000000000000000000700000501e068030080400000000804010000000010080000000000004000000c00000000c0000000000000008000200000100400000040000bb28c87755190edca421db54843bb28887755110ef4a021de54043bb28c85755190abca6215754c42bb28885755110af4a0215e54042bb28e657551ccaeca3195d546329faa2653c544ca7ca8194f55032e69906576510caeaa2195e94032bca80657a50d06f2a1a0dd54e31baa946376508c7aea698ddd4931ba2826376510c6eea710dd54e21baa94437650886eea690dd54d21f3a92437450486eca210dd94740baa8e81b651d036aa3a06d8c740da98e81b621d036a43a04f55240bba8a8174515036ea2a06d14540db18a81b5315036c42a06d48540dda82813e54102eca3985d54730ea98e613e548c27aa9186e50230bba8a6174514c3aa62986e501309f2a0613d540c2dca4185b54830bb2886175510c2eca3905d54720f290e413e548827aa9106e50220bba8a417451483ca42906e501209f2a0413d54082bca6105754c20bb2884175510837281884f952109eaa421b6548436aa9085dd4e10baa9c217752842eaa5085d94210dba0421b5408427ca8084f55010af298215d53042dca4085b54810dca0021b6540436aa8085dd4c10eb298217553043aaa6085554c10bba9021e652042eaa4087954810b2a90217650043e4a0086dd0010f920021b540043e280086c50010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x34000214c7431f0094b1946a828100bcf2b20900001aa400000718270001422266c52e28242312a381ac5a608a0100800b0e4878c2e2810800094851010050800488e580544cb0d544c832d24c9500ca6562141319c18153486556314121ac18131502b06048540ac98750503305150130e44c5404c3305150120e848540483195350010ca549400426562d4c109559653043165454c10c5551530425563d48109959652043455394810c995152043255454810d194d52043455354810ac592500423565d0010c554f400432552d0010ac59240043515390010d854a40042376550010c554d40043255250010d454d40043615250010acd9540043336550010ccd4d40043925350010cc54d40043915350010c454d40043335250010e894940043315250010e854940043215250010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x314040000310007404001285c8604c540922e630242a052172d4d4004288baca6a0021445cf5250010a42eb292800870153949400438129aa4a0021c054d5250010
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
  | 5 => packedAt s4K5 (880+((h/16+packedAt s4K5 (768+(h % 16)*7) 7) % 90)*7) 7
  | 4 => packedAt s4K4 (4077+((h/45+packedAt s4K4 (3672+(h % 45)*9) 9) % 459)*9) 9
  | 3 => packedAt s4K3 (1996+((h/16+packedAt s4K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x78e3c71fcf1ffff11c70e387c71ffff2130ff
  | 1 => 0x7f03f81ff01e3c7e1f80fc07f81c71fc63c93
  | 2 => 0xf8003ffe3ffe03f8fe000fff8ffe07e007cf1c
  | 3 => 0xffffc0003ffffc00fffff0000ffff800f80fe0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x40c04602048281001081440a10106188211025
  | 1 => 0xb12c89658a654688e148aa452c8c9256c62c92
  | 2 => 0x10211020902048012200029105240442024518
  | 3 => 0x2204010920400092445220000a491004480ac0
  | 5 => 0xc44822400289932499a4cd2640002098b5b000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfff8fff8faa8faa8fff8fff8faa8faa8fff8fff8faa8faa8fff8fff8faa8faa8fff8fff8faa8faa8fff8fff8faa8faa8fff8fff8faa8faa8fff8fff8faa8faa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_27835
namespace PEqualNP.Outside.L_meta_27835
open PEqualNP.Outside.L_meta_27835.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x388000a1ea0c25004008e0058000268400d362c1064e009290e10a2a4c68f1522011800a2159744252003a7cc8c0604000608002404d240040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xdd550000008818e8500000011564e40000005400000000013c0000994c000034011c4cf4004150012cd9100044fc00000000000000d40080300038ad3548009cecc128cc5804000121596000000000680168009400000000f0b86400000000007000200000000104000000004828011800006cf94400910800015c0010140000742d241c60d0e1310cb03c008c007c00a45c0024000000c8000000080000000001400000000000000000a00cb538a80000840000000000000078000000c4bc00020800060c0204000004040a04000002000000020e0404000000020205765190eeaa321dd94642baa8c853e540ca7aa819734c832bb2886575510caf4a0195e540329f28c833d50906bca620d754c41b7290836d52106f4a020de54041cf298839d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331b7294636d528c7688318cfd51319e2a263b4414c67ca990cf55321af29c435d53887688310cfd51219e2a243b4414867ca3a04f55240bba8a8174515036ea2a04f14540da28a81345150376a0a04f950409f2a4613d548c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca9104f55220afa9a415c534827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f55210da20c21b9408427ea8884f15110dca02213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb0e72e006c0c00081a0000148a4212a80616a0a98401e09000200004504327493254032c354d521071a5354041c654d501072a5254041ca54950107255210631ac580418c6b16010531c554c41886b16010621ac58041487166314540c558c51503266214540c9588515033160145408d185548c2346155220ac58041842b061502108e19540442356510410c554c41043255210410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc0840000101885496010631c22a6b008310e05635885150308b1ac028a81885896014540
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
  | 4 => packedAt s5K4 (2697+((h/30+packedAt s5K4 (2457+(h % 30)*8) 8) % 193)*8) 8
  | 3 => packedAt s5K3 (998+((h/8+packedAt s5K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (249+((h/1+packedAt s5K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 1 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 2 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 3 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 4 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4028004410502000420502480101429008c025
  | 1 => 0x24448c080c88910601209086c832244c221c92
  | 2 => 0xa88094912409402a8802a41252500944870518
  | 3 => 0x41529224820125515480024a4a4a009700ac0
  | 4 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_27835
namespace PEqualNP.Outside.L_meta_27835
open PEqualNP.Outside.L_meta_27835.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x26001ff1013000ffe6098013fb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ffc813000ffc4098007fa204c003fe1026001ffc413000ffc2098007fc104c001ffb2a4000bfd9520077fcca9001afe6548001feb2a4000bf59520077f8ca9001afc6548001ffb224000bfd912006ffcc890016fe6448001feb224000bf5912006ff8c890016fc644801dffaa2400dff95120007faa890037fc5448001ffb1a4000bfd8d20067fcc690012fe6348001feb1a4000bf58d20067f8c690012fc634801dffa9a400cff94d20007faa690033fc534801bffa1a400cff90d20007fa8690033fc43480037fb124003ffd492001ffca49000ffd5248007fe2924003ffd092001ffc849000ffd4248007fe2124003ffcc92001ffc649000fee3248007fe9924000fb4c92001ff86490003ff61480017fb0a400bff98520015fcc290003fd6148017fe30a4002bf18520077fea29002ffe5148001fea8a400bff1452006ffe829002ffe4148001fea0a400bff10520067fe629002ffe3148001fe98a400bff0c52001ffe429000fef2148007ff10a4003ff48520007da429000ffc21480037fb024001ffd412000ffca090007fa5048003fea824000fe5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001fe8c12000ffa6090003f93048003fe1824001ffc812001ff64090007fe2048003f71024001ff0812000fd84090007f82048003ff8824001ff8412000ff82090003ff65440017fb2a200aff99510035fcca88003fd65440017eb2a200aff19510035f8ca88003ff64440017fb222009ff9911002dfcc888003fd64440017eb222009ff1911002df8c88802bff5444013ff2a22000ff5511004ff8a888003ff63440017fb1a2008ff98d10025fcc688003fd63440017eb1a2008ff18d10025f8c68802bff5344011ff29a2000ff54d10047f8a688027ff4344011ff21a2000ff50d10047f88688003ff62440017fb122007ff9891001dfcc488003fd62440017eb122007ff1891001df8c48802bff524400fff2922000ff5491003ff8a488027ff424400fff2122000ff5091003ff88488023ff324400fff1922000ff4c91003ff86488006ff6144005ffa8a2002ff94510017faa28800bfc5144005ffa0a2002ff90510017fa828800bfc4144005ff98a2002ff8c510017ec628800bfd3144001fa98a2002ff0c510017fe428800bfe2144005fb10a2002ff48510007ea428800bfc21440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fa4044003fea022000fe5011000ff88088007ff3044003ff1822001ff4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd315402ffe18aa018ffc85500bffc42a8003fd215402ffe10aa001bfd815000ffea0a801bfb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001ffd015000ffc80a8007fa4054003fe202a001ffcc15000ffc60a8007fa3054003fe182a001ffc815000ffc40a8007fa2054003fe102a001ffc41500bff620a8007fe1054003fe082a001fe04150007fecaa0002ff655002dff32a8006bf99540007facaa0002fd655002dfe32a8006bf1954000dfec8a0017ff545002ddfaa28005ff9514002ffaa8a0017fc545000bde2a28000ffd8d40005fec6a0057fe63500097f31a8000ff58d400aff8c6a0012fc635002dffa9a8015ff94d40007faa6a0057fc535000bffa1a8005efd0d4002ffc86a0017fd4350001dea1a8005ff10d40007fec4a0002ff6250029ff3128003bf98940007fac4a0053fc62500077e3128016ffd49400a7fca4a0003fd5250029fe2928005ffd094002f7e84a0017fe425000bfea128000ef5094002ff884a0057ff3250029ff1928000ff4c9400a7f864a0003ff61500017fb0a8000fdd8540005eec2a004ffe61500057f30a8000ff5854009ff8c2a000afc6150001fa30a8002bd185400b7fea2a004ffe5150001fea8a8013ff1454002ffe82a0017bf415000bff20a8005ff505400077a82a0017fc415002bff98a8013ff8c540007fa62a004ffc3150029ff90a8013ff88540007fa42a004ffc21500037fb028001ffd414000ffca0a0007fa5050003fea828000fe5414000ff8a0a0007ff405000bfda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffe60a0007fe3050003fe1828001ffc814000ffc40a0007fc2050003ff8828001ff8414000ff420a0007fc1050001ffb2a6000bfd9530097fcca9801afe654c001feb2a6000bf59530097f8ca9801afc654c001ffb226000bfd913008ffcc898016fe644c001feb226000bf5913008ff8c898016fc644c025ffaa26011ff95130007faa898047fc544c0037fb1a6004ffd4d30027fca698013fd534c009fe29a6004ffd0d30027fc8698013fd434c009fe21a6000ffd8930005fec498043fe624c0077f3126000ff58930087f8c49800efc624c025ffa926010ff94930007faa498043fc524c023ffa126010ff90930007fa8498043fc424c009ff9926004f7cc930027fc6498013fd324c001ee9926004ff0c930007fec298002ff614c01fff30a6002bf98530007fac29803ffc614c0057e30a6012ffd453007ffca298003fd514c01ffe28a6011ffd053007ffc8298003fd414c01ffe20a6004ffcc530027be6298013fe314c009fe98a6000f74c530027f86298043ff214c01fff10a6000ff4853007ff84298006ff604c003ffa826001ff9413000ff4a098007fd504c001fca826001ff1413000ffe8098007fe404c003fea
  | 2 => 0x31027f8649880aff614c405ffa8a6202ff94531017eca29880bfd514c401faa8a6202ff14531017fe8298887f7414c405ff20a6202ff50531017f8829880bf4414c405ff98a6204fdcc531017fc629880bde314c405fe18a6202f70c531017e8629880bff214c405ff10a6202fd88531017f84298803ff604c4017fb02621fff9813100dfcc098803fd604c43ffe3026201bf18131117fea09887ffe504c43ffe2826221ffd01310fffc809887ffc404c409ff9826204f7cc131027fc6098813fc304c441ff902621fff881310fff8409880bff104c405fb8826202ff84131017f82098803ff65484017fb2a421eff99521035fcca90803fd65484017eb2a421eff19521035f8ca90803ff64484017fb22421dff9912102dfcc890803fd64484017eb22421dff1912102df8c89087bff544843bff2a24200ff551210eff8a890803ff63484017fb1a421cff98d21025fcc690803fd63484017eb1a421cff18d21025f8c69087bff5348439ff29a4200ff54d210e7f8a690877ff4348439ff21a4200ff50d210e7f8869080aff6248407ffa924203ff9492101ffaa49080ffc5248407ffa124203ff9092101fdc849080ffd4248401f6a124203ff1092101ffe649080ffe3248407fe9924203ff0c921015fec29080bff5148405ff28a4202fd94521017faa290803f55148405fe28a4202ffd05210efee829080bfe4148405fea0a4202ff10521017e8829080bff3148405ff18a4202fd8c521017fa6290803f53148405fe18a4202ffc852101fee429080bfe2148405f710a4202ff08521017d8429080bf42148401ffb024200bfd81210dffcc090806fe6048401feb02421bff1812100df8c09087bff5048437ff282421bff141210effe809086ffe4048437fe202421cffcc1210dffc609086ffc3048407ff9024203fbc812101ffc409080ffc2048405ff8824202fdc4121017fc209080bfc10484037fb2aa000ffd9150005fec8a806bfe645400b7f322a000ff591500d7f8c8a8016fc645400dffaa2a006ff951500d6fca8a801bfd545400dfe2a2a006df15150007fec6a8002ff6354033ff31aa004bf98d50007fac6a8067fc63540097e31aa006ffd4d50036fea6a801bfe535400dfea9aa000df54d50037f8a6a806bff4354033ff21aa000ff50d500cff886a8003ff62540017fb12a018ff9895001dfcc4a8003fd6254031fe312a003bf18950037fea4a801b7f525400dff292a006ff54950006faa4a801bfc5254035ffa12a018ff90950007fa84a8063fc4254033ff992a018ff8c950007fa64a8063fc3254001ffb0aa000bfd85500bffcc2a800afe6154001feb0aa017ff18550015f8c2a801bff515400dbfa8aa006ff94550037faa2a80037d515400dfe28aa01affd05500bffc82a8003fd415402ffe20aa019ffcc5500bffc62a800
  | 3 => 0xf2a2a206ff55151006faa8a881bfc5454401ffb1aa200bfd8d5114ffcc6a8812fe6354401feb1aa229ff18d51025f8c6a881bff535440dff29aa206ff54d51037f8a6a88abff4354453ff21aa200ff50d5114ff886a8803ff62544017fb12a228ff9895101dfcc4a8803fd6254451fe312a203bf18951037fea4a881bfe525440dfea92a206ff14951157fe84a88a3fe4254401fea12a228ff1095114ffe64a88a3fe3254401fe992a228ff0c951015fec2a880bff515440dfba8aa202ff94551016fca2a880bfc5154405be28aa202fd14551017fe82a880bfe4154405fb20aa202ff10551017fe62a880bfe3154405fb18aa202ff0c551017fe42a880bfe2154405fb10aa202ff08551007fec0a8802ff605444fff302a201bf98151007fac0a889ffc60544037e302a206ffd4151036fea0a881bfe505440dfe282a22affd015113ffc80a889ffc4054453ff982a227ff8c15113ff860a88a3ff205444fff102a227ff08151017fe20a880bfe105444ffb082a202ff04151017e820a8803ff65504017fb2a8226ff99541035fccaa0803fd65504017eb2a8226ff19541035f8caa080aff645040bffaa28205ff9514102ffaa8a0817fc5450401ffb1a8200bfd8d4112ffcc6a0812fe6350401feb1a8225ff18d41025f8c6a089bff535044bff29a8200ff54d4112ff8a6a0817ff435040bff21a8205ff50d4102ff886a0803ff62504017fb128224ff9894101dfcc4a0803fd6250449fe3128203bf18941137fea4a0893fe5250401fea928224ff1494102ffe84a0817fe425040bfea128205ff1094112ffe64a0893fe3250401fe9928224ff0c941015fec2a080bff5150405ff28a8202fd94541017faa2a0803f55150405fe28a8202ffd054102fee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff98a8202ff8c541017f862a080bff2150405ff10a8202ff08541007fec0a0802ff6050447ff3028201bf98141007fac0a088ffc60504037e3028226ffd414111ffca0a088ffc505040bffa028205efd014102ffc80a0817fc405044bff9828223ff8c14111ff860a0893ff2050447ff1028223ff08141017fe20a080bfe1050405fe0828200ffd9531005feca9888bfe654c40d7f32a6200ff59531005faca9888bfc654c40d7e32a6200ffd9131005fec898887fe644c40b7f3226200ff59131005fac898887fc644c40b7e3226222ffd513110ffca898803fd544c443fe2a26202bfd8d31027fea698813fe534c409fea9a6204ff14d31027fe8698813fe434c409ef21a6204ff50d31007ba8698813fc434c401ffb126200bfd8931107fcc49880efe624c401feb126220ff1893101df8c49888bff524c441ff2926200ff54931107f8a498887ff424c441ff2126200ff50931107f88498813ff324c409ff1926204ff4c9
  | 4 => 0x6fe6054801feb02a433ff1815200df8c0a901bff505480dbfa82a406ff94152037f8a0a90dbff4054867ff202a433ff101521affe60a90cffe3054867fe182a403ffc815201ffc40a900ffc2054869ff882a433ff8415219ff820a9003ff65508017fb2a8432ff99542035fccaa1003fd65508017eb2a8432ff19542035f8caa100eff645080bffaa28405ff9514202f7ca8a1017fd5450801deaa28405ff15142007fec6a1002ff6350863ff31a8404bf98d42007fac6a10c7fc63508097e31a8432ffd4d4218ffca6a1003fd5350863fe29a8405ffd0d4202f7e86a1017fe435080bfea1a8400ef50d4202ff886a100eff6250807ffa928403ff9494201fdca4a100ffd5250801f6a928403ff1494201ffe84a1017ef4250807ff2128403ef9094201ff884a100fbc4250807f62128403ffcc94201ffc64a100ffc3250801ffb0a8400bfd8542187fcc2a100afe6150801feb0a8430ff18542015f8c2a10cbff5150861ff28a8430ff1454202ffe82a1017fe4150861df20a8405ff1054202f7882a10c7ff3150861ff18a8430ff0c54201ffe42a100fef2150807ff10a8403ff08542007fec0a1002ff605085fff3028401bf98142007fac0a10bffc60508037e3028432ffd414217ffca0a10bffc505080bffa028405efd014202ffc80a1017fc4050863ff982842fff8c14217ff860a100fff2050807ff1028403ff08142187fe20a10bffe105085ffe0828400ffd9532005feca990bbfe654c80d7f32a6400ff59532005faca990bbfc654c80d7e32a6400ffd9132005fec8990b7fe644c80b7f3226400ff59132005fac8990b7fc644c80b7e322642effd513216ffca899003fd544c85bfe2a26403bfd8d32027fea699013fe534c809ef29a6404ff54d32007baa699013fc534c809ffa1a6404ff90d32027fa8699013fc434c8077fb126403ffd493201ffca49900fee524c807fea926400fb5493201ff8a49900fff424c807ff2126403ff5093201ff8849900fff324c809f79926403ff8c93201fbc649900ffc324c807ee1926403fb0c93201f986499003ff614c8017fb0a642cff98532015fcc299003fd614c859fe30a6402bf18532177fea2990b3fe514c859fe28a642dffd0532167fc82990b3fc414c809ff98a6404ff8c532027f8629900fff214c807ff10a6403ff08532007fec099002ff604c857ff3026401bf98132007fac0990affc604c8037e302642effd413215ffca0990affc504c85bffa02642bff9013215ff88099013ff304c809ef9826404ff8c132027f8609900fff204c807f79026403ff8813201ff840990b3ff104c857ff082642bff04132015fecaa8803ff64544017fb22a200efd91510057ec8a88abfe645440b7f322a200ff59151157f8c8a8816fc6454401de322a205af19151037fea8a881b7f545440df
  | 5 => 0xd53027fc86a9813de4354c09fe21aa600ffd8953005fec4a98f7fe6254c077f312a600ff589531eff8c4a980efc6254c0dffa92a606dfd4953037fca4a981bfc5254c7dffa12a63dff909531eff884a9813ff3254c09ef992a604ff8c953027f864a9803ff6154c017fb0aa63cff98553015fcc2a9803fd6154c79fe30aa602bf18553037fea2a981bfe5154c0dfe28aa63effd05531e7fc82a98f3fc4154c09ff98aa604ff8c553027f862a98f7ff2154c79ff10aa63cff08553007fec0a9802ff6054c77ff302a601bf98153007fac0a98effc6054c037e302a606ffd4153036fea0a981bfe5054c0dfe282a63effd01531dffc80a98effc4054c09ff982a604ff8c153027f860a98f7ff2054c77ff102a63bff081531e7fe20a98effe1054c77fe082a600ffd9543005fecaa18ebfe6550c0d7f32a8600ff59543005facaa18ebfc6550c0d7e32a8604bfd914302ffea8a1817fe5450c0bdf2a28605ff551430077aa8a1817fc5450c097fb1a8604ffd4d43027fca6a1813de5350c09fea9a8600f754d43027f8a6a1813ff4350c0befa1a8604ff90d430277c86a1813fc4350c09de21a8604f710d43007fec4a1802ff6250c73ff3128603bf98943007fac4a18e7fc6250c077e312863affd49431cffca4a18e7fc5250c0bffa128605efd094302ffc84a1817fc4250c09ff9928604ff8c943027f864a1803ff6150c017fb0a8638ff98543015fcc2a1803fd6150c71fe30a8602bf185431d7fea2a18e3fe5150c71fe28a8605ffd054302ffc82a18e3be4150c0bfe20a8605ef10543027fe62a1813df3150c09ff18a8604ff0c5431cffe42a18e3fe2150c71fe10a8600ffd8143005fec0a18dffe6050c037f3028600ff581431bff8c0a1806fc6050c75ffa828637ff941431bff8a0a1817ff4050c0bdfa028605ff9014302ff880a1813ff3050c09ff1828604ff0c1431cffe40a18dffe2050c6ffe1028638ffc41431bffc20a18dffc1050c077fb2aa400ffd9152005fec8a90dbfe645480b7f322a400ff591521b7f8c8a9016fc645480dffaa2a406ff95152037faa8a901bfc5454801ffb1aa400bfd8d521affcc6a9012fe6354801feb1aa435ff18d52025f8c6a901bff535480dbfa9aa406ff94d52037faa6a90037d535480dfe29aa436ffd0d521affc86a9003fd435486bfe21aa403bfd895201ffea4a901bef5254807ff292a403df9495201ff8a4a900f7c5254807f6292a403ffd095201ffc84a900fee4254807fe212a403ffcc95201ffc64a900fee3254807fe192a400ffd8552005fec2a90d3fe61548057f30aa400ff585521a7f8c2a900afc615480dffa8aa406ff94552037f8a2a90dbff4154869ff20aa434ff105521affe62a90d3fe3154869fe18aa403ffc855201ffc42a900ffc2154801ffb02a400bfd815219ffcc0a9
  | 6 => 0x100005c000030100000e0000160500402b000018000010140900a0000000000000000400037802012000008060000100980001a0000c80c0000540000a010048010010000f8040160080041101200205c0000b0000100002c006070008020000d0008210120080007300c0000280e0260100b80200201c040060000040882d0100000200400c0a40100c00c00001800000010000000060300103d01a0000281800c0080001000002c0001b0800040000601e01c008050000001480500a00400800000030258030000280580000002401805000050048180080c0068000022300081d00a0000100c00800c028060000500080200000408001006024000210100000380000201802001000038000030020083680100805c0080000002c0380300a004020010200000000201000c0280100c0200800001401c0001e016000080010060700001001201430800014090060030120002101100401c0e80000201402801002004058100000000680f00a00c0000002e0040100100a01c0000100400c03803000048008050380240381100a000000040160180082100c0280481201411800009026000040030020e4030080000041980601404c058000240140080701002c05803006000008070000400380200200c058000080540002000800801000000020000040140240200100005c028100260142100001a01000009006004018050080400680200e000030030100040100400001c0180501a02c088060060640580f00607401816ff655500b7fb22a805ffd51540377ea8aa017fe545500bbf2a2a805ff1515402ef8a8aa017bc5455001ffb1aa800bfd8d54217fcc6aa012fe6355001feb1aa842ff18d54025f8c6aa01bff535500dff29aa806ff14d5402ffe86aa017bf435500bff21aa805ff10d54007fec4aa002ff6255083ff312a803bf98954007fac4aa107fc62550077e312a806ffd4954037fca4aa01bfc525500bffa12a805efd095402ffc84aa017fc4255085ff992a841ff8c95420ff864aa003ff61550017fb0aa840ff98554015fcc2aa003fd6155081fe30aa802bf18554037fea2aa01b7f515500dff28aa806ff1455402ffe82aa017fe415500bfe20aa842ffcc554207fc62aa103fc3155083ff90aa840ff88554207f842aa003ff60550017fb02a83fff9815400dfcc0aa003fd605507ffe302a801bf18154037fea0aa01bfe505500dfe282a805ffd015402ffc80aa017fc4055085ff982a83fff8c1541fff860aa107ff205507fff102a83fff08154207fe20aa0fffe105507ffe082a804bfd9553007fec8a9802ff6454c7dff322a605bf99153007fac8a98fbfc6454c0b7e322a606ffd5153037fca8a981bfd5454c0dfe2a2a604bfd8d53027fea6a981bdf5354c09ff29aa604df94d53027f8a6a98137c5354c09ee29aa604ffd
  | 7 => 0x94a4f95a8e00070348000000001320808000002791a6a83800000013ac700000d8001bf2b022328980004b0000000379ad0002bf969a648eb8002c60cf0541c68ae2bd8000370e31dc93508c0000fe02a2000be9bd0f083f1a61829ba9510000000392a09d42a799200000027000000004e11d8129a40000000001aa0e51dc1882772889a01361af82ca850ab19e1851142760002658b8961a371b61d90b72aaa3891c8001b9009ac188aab30000001e500003a8e08dc00011a800155800000240a8b87995222e2be1cb1a08b6a5d0a22730002860000dd9d5189a4b00020c868a9e0b38002100f723a1378000912ac0001939de96e17527e80002319ba6300000025680018389e1949440000a596628f25827b00000022a1540109ada710590d78fc8c200000000027b8002b100000000005c29780000020700020c0d200008d0b927fa0aa5327f1c00140d2aa42c021b2b42990460002778000000f280024c2550000e889727c92897722a8000d887100000000000000002691f18600000386e04e91e00000016f1738c88000000d4021945996000000237929000190a6600014c0000df24d0e4041a9d0000001690e123980011d0000000000000000002828000000001be21383c0302869caa958ef1622542a211a0001c88fb12680020d0848000f90000000000000002a70de00003508e024000143000095894abd00025f924a7d8000cc97d927234975a4e8a98a785980008616c95300b00000000000000e8a100024311f9e385c9e32751870d59bd807a609ca2980528001a22402168000000002161568518002ba8761b00002509c08bb07b9548900288001f8ac31a897f0671ce9da0001ea1789b69f91811380f32c48e2820a2785108314e87d01e14f9820c118c0a4243a8101b03e164abb89f9ec1182441a587387584d8002310b217c0250b493d00188f0000000582c3a5aaa2a3514e1a2ac90422b28000000cc0000aca2809628780017197018b01c9f68000000000a486810e80010d14ba188001e18f02692968c00531590baa7a2b9111887a448dfaad99000006501600023182aaaf0a618a1d28bf0000e6001107800152923ac80d08f19d20001f808695d819a938ee9c49658699ac21286a8d91c29501ab0da1022a18d71d38100f887fa2500000d092829ab68719da9e62b584f2158002a380000000017f8b1a078001668000ab9aa9090118001cc86d1538000001e98f480000006200002e11b0000cb9a80001d00000001ae25389a0330adabc27d1499fd00480b0120ac01807018018020180041481708201e05c0200100600c2c801010020008090060000200a00001806000000030020170020080a80000c008008070160080280e00c0000000b000154108060060040600002a008008000460402300000200c07000000000008
  | 8 => 0xd8000c98382298001e10002c296d143abf1f591303f8d500000019a8000178388000001a72458002288a093e2338aa9df00010b95c05aa8716105600e2481d693a93680005015715f0f12aa0248398af1d890722da5b0f5a1524a25c0be0de9630e59111e419ca8b20698781c1782c9a1214d20621483b13726aa6684c87699fa709e4a4b9a525d93b2248468e78000969098000c48000000001b890a0002341c7aab92b92300006f86328c1eea8085d8000fb8c18648bb9388000000000000ef80000020123e1890ca8000001460a280002916a80012c28e9a100018d13f045835a9700020b000198ac40211f200095b00025780025c80409f1dd1bb8fa20f80018a80000000000000007288c91519503c8001959e5aa80ee1639889991448692910f82559969e7a9020da680b81df9a98111b28c610307b08197792196c0eb2931858ea130a08999a2e82fa589d329221304a25180a2739399f995f85685b20f0000c2ac21ff9c228da6417b06022104d2b62a993111723c9ee0ed2b71bc0e992424d8748ca099a6c24e0b98029cd80000c00025e0001db92e8001f52962b82628e715786392f2322a129a9ba04b9cf97088b2521ce023abc8001e69a19f023f8000db0ad0470c820b80000010699d24f0990000f50001b71d98188b610d8f98002c12ae184015a7283617487a0ec0c58000000b59b10000a51328cda1407c12f81d8551978000a70000679c32721468002240c71e000000009889429c0002058951760001be96515511e80000f20520e115893a7693013304aab1a549359d62599f185b9c4275a0a24a92516413c24197317900009a8609b3181a02a38022057a501ed88928a07c8751faa1a2369c187aaa30cfa411f083eacb1202b382f028218204aab2098b303b92c99b23b1488ce23a9cd0ba002014a7e28189b90110f8a315884c18f9fe17691892a9fc1b58168cd1c62041fa1710dd0f79602421401a492d1a323026711c0c407724505221e07e8bca03a6d22b1ef9519391b41108d6247a4607021d9941b1ab22ae90e21f9298e6a4c9bb09082da4294f19e972184830a9989d180a2c90a86a0bc2afa8005896b18c80c8c383288811206b81e88a24710288701508b88280f9af28e0f396710c036872053a5ba48a0e9470d99f29d117b9d5a9e86d8d1054a3c15993c90386c020125967aa8aca0080791d49bc9d82c510c8b2a6b2ba0e805e0921bf84907f16baa51208e1833aad050a209261508122a58fe8ae825a4919703214a256284968ac082b00aa68a17ab88000001f425a19d88eaa908f8a929b18e0440dba3b84115b80502c14da219ab85d26e9338d30c300580baa6878217022a6f06f0190b01de2748fda5e8f20b418b94280628c9b793198e9059b9a9a0000000001f60000ff80013f9dd8002881929b5172a3f2
  | 9 => 0x2a485f21186c803117a6512da27031000263a3e9fc8d80000001279cf2781eb8d49211b480000000004481f00000003d0000000000001682c5a3581d0048fd2108001281ac92e000000000000239000141a9090f25926186580000000000018f000191a9b8a682e8ac21c21b800200aa61a780000002793a16a2b50262018ea9221c51c907880000004022b9799e813489e8f61c100026fa9f9f10001ed000057291a030cb006974017230a602831db0001c59cba3d28a90411628f95e0980a828904f8ec9e20a19018c928408129d9581c993b893048983294278a6c8b79190001cc0001138ce8002a022f0fc2c68e22611eb1c709c1d708899c0bf89c85fa2020215ca8584306297a83a16d9fd94cab08428b50bd80014900000019829c8000091198e906e8a38000000da8000001100000919fba328dc9b8000055a6b9e712b00009d8842989168fa9e906b0000131fb15a2110820000aa140a799050661d0a6a1feac8831a9f22c2be9f38d682d16e87e13d81f8f685a22f9609f721a8180c78479561b399a0d02330979628e4aca8852699eca511c81f30c6a92a5f03415ea7a91280004082b9421a9049a71ac79f787d8a89080001d7a082ac9ea97e1e08b11478ed883a7411b8d18bd0801c397d0089048a0267a2d1ae9b0a1f10086113407094a81a9451229801e29f4a6e0732bb225a22ab9a6d877a52a469088742b497c99f21996f8000e398d843a7c22204821e8f40000002621ef2290af88da8d13e88997a19123da360001062090ff0c521922615d1b20640d381b90b1930001148859868002268c0800000295000282141066ab79481ff1d18001a380021d04502705ea2389b10014b2498b08618001e880021c92a01a25717e83
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7558d10034fe7558d10034fc7558d10004ff7458d1002cfe7458d1002cfc7458d1024cff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d10244ff7158d10006f77158d1007ef62158d100fcff7058d10006fb7058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10006bf6450d1002ebc6450d1001cfe76d891003eee62d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d891000cff71d8910014fe71d891000cfd71d8910014fc71d891023ef631d891023eef21d891023eed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891022eef20d891022eed20d891001cff765891003eec6258910225f77158910235fb7058910004ff7558910034fe7558910034fc7558910004ff745891002cfe745891002cfc7458910004ff7358910024fe7358910024fc735891022cff7258910006ef7258910224ff7158910006f7715891005ef631589100dcff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc7654910004ff7650910004fe7650910004fd7650910004fc7650910006bf645091002ebc6450910004ff764c910004fe764c910004fd764c910004fc764c91003fcc324c910015f6714c91000df4764c510026f4764c51000cf4764c510006f7654c510006f5654c51010ef6644c51010ef4644c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510047d6434c510007d5434c510005f7724c510006f7624c510006f5624c510007f3704c51000df6704c51000df4704c5100fff0704c510016f7604c510017f3604c5100fff2404c5100ffd7304c5100ffd5304c51000df4764851001ef4764851000cf47648510006f76548510006f565485100eef664485100eef46448510005f77348510005f57348510006f76348510006f56348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851003fe64248510007e54248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100dff240485100dfe720485100dfe52048510015f8765011002ef87650110014f87650110006fb6550110006f9655011000dfb745011000fbb7450110007bb645011002efa645011002ef8645011004fb8645011021fbb545011004fb8545011004fbb4350110007b9435011004fbb4250110007b94250110007f37150110015fa7150110015f8715011009ff0715011000efb615011000ff3615011009fbb415011009fb9415011009ff23150110007f1315011009ff22150110007f12150110
  | 1 => 0xc12001cf8764c120005fb754c120005f9754c120006fb654c120006f9654c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120067d8634c120007eb724c12001dfa724c12001df8724c120087e8724c12000efb624c12000feb624c120087db324c120087ea324c120087d9324c120067e9324c120007c9324c120067db314c120007d9314c120087eb214c120007e9214c120034fe76d95100567e65d951013cfd75d951002cfe74d9510004fd74d951002cfc74d9510024fe73d9510004fd73d9510024fc73d951001cfe72d9510004fd72d951001cfc72d951000cff71d9510014fe71d951000cfd71d9510014fc71d951029e7f51d951029e7d51d951029ef631d951029ef621d9510014ff70d951000cfe70d9510014fd70d951000cfc70d951028e7f50d951028e7d50d951028efa40d951029efb10d951028ef610d951028ef410d951028ef810d9510034ff76595100567c6559510005bf745951004dbc7459510285f77159510295fb705951028cff75595100067f7559510004ff7459510006bf7459510004bf745951002cfe745951002cfc7459510006bc745951002cbc7459510004ff7359510024fe7359510024fc7359510004ff725951001cfe725951001cfc7259510284ff7159510006f771595100bef631595100bef6215951013cff7059510006fb705951013efa40595100befb105951013ef6105951013ef4105951013ef8105951002cfe76d911004ebe64d9110034fe75d9110004fd75d9110034fc75d911011cfd74d9110006bf54d911004ebc54d9110024fe73d9110004fd73d9110024fc73d911004ebf43d911001cfe72d9110004fd72d911001cfc72d911004ebf42d911000cff71d9110014fe71d911000cfd71d9110014fc71d911027ebf41d911027ebd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d911026ebf40d911026ebd40d911002cff765911004ebc6459110265f77159110275fb7059110004ff7559110034fe7559110034fc755911026cff7459110006bf7459110004ff7359110024fe7359110024fc7359110004ff725911001cfe725911001cfc7259110264ff7159110006f77159110264f7715911011cff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc7655110024fe76d8d10046de63d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d1001cfe72d8d10004fd72d8d1001cfc72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d1025edf31d8d1025edd31d8d1025ef621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d1024edf30d8d1024edd30d8d10024ff7658d10046dc6358d10245f77158d10255fb7058d10004f
  | 2 => 0x14fe71d8d20004fd71d8d20014fc71d8d2001cff70d8d2001cfd70d8d202cefa50d8d202cedf30d8d202cedd30d8d20024ff7658d20066dc6358d202c5ef7258d202d5fb7058d20004ff7558d20034fe7558d20034fc7558d20004ff7458d2002cfe7458d2002cfc7458d202ccff7358d20006df7358d202c4ff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d2015cff7058d20006fb7058d2015efa5058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200367e6554d200067d6554d2000dfa7054d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2002ebe6450d20006bd6450d20006df6350d20026dc6350d2000dec764c920026ec764c92000cec764c920006ef654c920006ed654c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c920026cc634c920067ce534c920007cd534c920005ef714c920007eb704c92000dee704c92000dec704c92015fe8704c92001eef604c92001feb604c92015fea504c92015fcf304c92015fea304c92015fcd304c920014fe76d852005ef661d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d852005ef651d8520006f741d852005ef441d852005ef621d85202bef521d852000cfe70d852001cfd70d852000cfc70d8520226f710d852005ef461585202b5fb7058520004ff7654520004fe7654520004fc7654520005bf745452006dbc7454520006f76154520016f46154520004ff7650520004fe7650520004fc7650520004ff764c520004fe764c520004fc764c52001dee724c520016f6614c52000dec7648520016ec764852000cec7648520006ef6448520006ed6448520005ef7348520005ed734852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005fe65148520007e551485202afe7414852005fe4414852005fe63148520007e53148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200dfea50485200dfea30485200dfe7104852001df87654120036f8765412001cf8765412000dfb755412000f7b75541200077b6554120036fa6554120036f86554120077786554120006fb6454120006f964541202a77a5454120077785454120005fb7354120006fb6354120006f963541200777b5354120007795354120007eb725412001dfa725412001df872541200c7e8725412000efb625412000feb62541200c77b52541200c77952541200c7ea3254120007e932541200befa61541200bef861541200777b51541200077951541200c7eb2154120007e9215412001df8764c120026f8764
  | 3 => 0xf604c530027db604c5300ffda504c5300ffda204c5300ffd7104c530004ff7648530004fe7648530004fc7648530025de7348530005dd7348530016f66148530007d53148530025f87654130036f87654130024f8765413000dfb755413000f7b75541300077b6554130036fa6554130036f86554130097786554130006fb6454130006f964541303277a5454130097785454130007db7354130025fa7354130025f873541300cfd8735413000efb635413000fdb63541300cf7b53541300cf795354130005fb7254130006fb62541300977b52541300077952541300cfdb3254130007d932541300befa61541300bef861541300977b51541300077951541300cfdb3154130007d93154130034fe76d95200767e65d952019cfd75d952002cfe74d9520004fd74d952002cfc74d9520024fe73d9520004fd73d9520024fc73d952000cff72d952001cfe72d952000cfd72d952001cfc72d952031e7f52d952031e7d52d952031eee32d9520014fe71d9520004fd71d9520014fc71d952001cff70d952001cfd70d952030e7f50d952030e7d50d952030efa30d9520034ff76595200767c6559520005df7359520065dc7359520305ef7259520315fb705952030cff75595200067f7559520004ff745952002cfe745952002cfc7459520004ff7359520006df7359520004df7359520024fe7359520024fc7359520006dc7359520024dc73595200767f5359520304ff7259520006ef72595200c6ee3259520004ff7159520014fe7159520014fc715952019cff7059520006fb705952019efa305952002cfe76d912006ebe64d9120034fe75d9120004fd75d9120034fc75d912017cfd74d9120024fe73d9120004fd73d9120024fc73d912000cff72d912001cfe72d912000cfd72d912001cfc72d91202febf42d91202febd42d9120014fe71d9120004fd71d9120014fc71d91202feef21d912001cff70d912001cfd70d91202eefa50d91202eebf40d91202eebd40d912002cff765912006ebc64591202e5ef7259120005f7715912005df471591202f5fb7059120004ff7559120034fe7559120034fc75591202ecff7459120006bf7459120004ff7359120024fe7359120024fc735912006ebf43591202e4ff7259120006ef7259120004ff7159120006f77159120004f77159120014fe7159120014fc7159120006f47159120014f471591200a6ef215912017cff7059120006fb705912017efa5059120004ff7655120004fe7655120004fd7655120004fc7655120024fe76d8d20066de63d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d20006df53d8d20066dc53d8d20066de43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202dedf32d8d202dedd32d8d20
  | 4 => 0x95301defa205953002cfe76d913008ebe64d9130034fe75d9130004fd75d9130034fc75d91301bcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d913036ebf43d913036ebd43d913001cfe72d9130004fd72d913001cfc72d9130014fe71d9130004fd71d9130014fc71d913036edf31d9130024ff70d9130024fd70d913035efa50d913035ebf40d913035ebd40d913002cff765913008ebc6459130355df7359130005f7715913007df47159130365fb7059130004ff7559130034fe7559130034fc755913035cff7459130006bf7459130354ff7359130006df7359130004ff725913001cfe725913001cfc725913008ebf4259130004ff7159130006f77159130004f77159130014fe7159130014fc7159130006f47159130014f471591300aedf31591301bcff7059130006fb70591301befa5059130004ff7655130004fe7655130004fd7655130004fc765513001cfe76d8930086ee62d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930006ef52d8930086ec52d8930086ee42d8930086ee32d893034eed32d8930014fe71d8930004fd71d8930014fc71d8930024fd70d89302c6fa50d89302c6ef20d8930086ec6258930345fb7058930004ff7654930004fe7654930004fc76549300367e65549300067d655493000dfa7054930004ff7650930004fe7650930004fc765093002ebe6450930006bd6450930006ef625093001eec625093000ddc764c93001edc764c93000cdc764c930006df654c930006dd654c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c93001ecc624c930087ce524c930007cd524c930005df714c930007db704c93000dde704c93000ddc704c93015fd8704c930026df604c930027db604c93015fda504c93015fcf204c93015fda204c930014fe76d853007ef661d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d853007ef651d8530006f741d853007ef441d853007ef631d853033ef531d8530024fd70d8530246f710d853007ef46158530335fb7058530004ff7654530004fe7654530004fc7654530005bf745453008dbc7454530006f76154530016f46154530004ff7650530004fe7650530004fc765053000ddc764c530016dc764c53000cdc764c530006df644c530006dd644c530005df724c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6514c530007d5514c53032fd7414c53007fd4414c53007fd6214c530007db704c53000dde704c53000ddc704c5300ffd8704c530026d
  | 5 => 0x9fd6731854009fd57318540006f76318540006f66318540006f56318540006f4631854039fb74318540007b5431854009fe6721854009fe57218540006f76218540006f66218540006f56218540006f4621854039fb74218540007b54218540397f2701854009ff17018540396f76018540397f2501854039ff34018540397b64018540397b44018540397f04018540004ff7654540004fe7654540004fc76545400367e65545400067d6554540005bf745454002dbc74545400b73f5454540006f76154540016f4615454000dfa705454013ff2105454000dbc7650540016bc765054000cbc76505400b5be75505400b5bc7550540005bf7350540005bf725054002dbf715054002fb77150540007b76150540016be6150540016bc615054009fb46150540016b4615054009fb65150540007b55150540007bb705054000dbe705054000dbc705054011fb8705054002ebf605054002fbb605054011fba505054011fba1050540004ff764c540004fe764c540004fc764c54002dbe744c540005bd744c540026de634c5400079d434c540006f7614c540016f4614c54010fb7414c540004ff7648540004fe7648540004fc764854002dbe7448540005bd744854001eee6248540007ad4248540006f76148540016f461485400efb7414854002df87654140036f8765414002cf8765414000dfb755414000f7b75541400077b6554140036fa6554140036f865541400b7786554140007bb745414002dfa745414002df874541400d7b8745414000efb645414000fbb64541400b7bb54541400d77a54541400d77854541400d7b854541400d7385454140006fb63541400b77b53541400077953541400d7bb4354140007b94354140006fb62541400b77b52541400077952541400d7bb4254140007b94254140005fb7154140007f361541400befa61541400bef86154140007f061541400bef061541400b77b51541400077951541400d7bb4154140007b94154140034fe76d95300967e65d95301dcfd75d953002cfe74d9530004fd74d953002cfc74d953000cff73d9530024fe73d953000cfd73d9530024fc73d953038e7f53d953038e7d53d953001cfe72d9530004fd72d953001cfc72d953038edf32d9530014fe71d9530004fd71d9530014fc71d9530024ff70d9530024fd70d953037e7f50d953037e7d50d953037efa20d9530034ff76595300967c6559530375df7359530005ef7259530085ec7259530385fb705953037cff75595300067f7559530004ff745953002cfe745953002cfc7459530374ff7359530006df7359530004ff7259530006ef7259530004ef725953001cfe725953001cfc7259530006ec725953001cec72595300967f52595300cedf3259530004ff7159530014fe7159530014fc71595301dcff7059530006fb705
  | 6 => 0xf745494002dbc74549401a6f4615494000dbc765094001ebc765094000cbc76509400b5be75509400b5bc7550940006bf6550940006bd6550940005bf7350940006bf635094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400a7ac62509400a7ae5250940007ad5250940005bf7150940186be6150940186bc6150940186b461509400a7af2150940007bb705094000dbe705094000dbc705094017fb8705094002ebf605094002fbb605094017fba505094017fba1050940004ff764c940004fe764c940004fc764c94002dbe744c940005bd744c9400a7cc324c940166f4614c940005fb704c94000df8704c940014fe76d854009ef661d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540024fe73d8540004fd73d8540024fc73d854001cfe72d8540004fd72d854001cfc72d8540006f751d854009ef651d854009ef451d854009ef641d85403aef541d8540006f731d854009ef631d854009ef431d8540006f721d854009ef621d854009ef421d854002cfd70d8540266f710d8540395f676d8540014f676d8540006f765d8540006f665d8540006f565d8540006f465d8540267b774d8540267b474d8540007b754d85403afb454d8540006f763d8540006f663d8540006f563d8540006f463d85403afb743d8540007b543d8540006f762d8540006f662d8540006f562d8540006f462d85403afb742d8540007b542d85403aff370d8540267f070d8540267f250d85403aff340d8540267b640d8540267b440d8540267f040d8540006f775d8540006f675d8540006f575d8540006f475d8540266f774d854009ef674d8540266f574d8540266f474d85403aef754d85403aef654d85403aef554d85403aef454d8540006f773d8540006f673d8540006f573d8540006f473d8540006f753d8540006f653d8540006f553d8540006f453d85403aef743d85403aef643d85403aef543d85403aef443d8540006f772d8540006f672d8540006f572d8540006f472d8540006f752d8540006f652d8540006f552d8540006f452d85403aef742d85403aef642d85403aef542d85403aef442d8540006f732d8540006f632d8540006f532d8540006f432d8540266f770d8540266f670d8540266f570d8540266f470d8540266f750d8540266f650d8540266f550d8540266f450d8540266f740d8540266f640d8540266f440d8540266f730d8540266f630d8540266f530d8540266f430d8540266f720d8540266f620d8540266f520d8540266f420d854009ef461585403a5fb7058540265f6761854009ef6761854009f76751854009f757518540006f76518540006f66518540006f56518540006f4651854009fb67418540397b57418540396f76418540007b7541854039fb45418540
  | 7 => 0x550004ff764c550004fe764c550004fc764c5500357e754c5500057d754c550016f6614c55000775514c550005fb704c55000df8704c5500bff3104c550004ff7648550004fe7648550004fc76485500357e75485500057d7548550016f66148550007755148550005fb704855000df870485500bff31048550034fe76d95400b67e65d954002dbe74d954000dbd74d95400b73f54d95401fcfd75d954000cff74d954002cfe74d954000cfd74d95403debd74d954000cbd74d954002cfc74d95403ee7f54d95400b6bf54d95400b63f54d95403ee7d54d95403eebc54d9540024fe73d9540004fd73d9540024fc73d95403eebf43d954001cfe72d9540004fd72d954001cfc72d95403eebf42d9540014fe71d9540004fd71d9540014fc71d954002cff70d954002cfd70d95403de7f50d95403de7d50d9540034ff76595400b67c65595403d5bf74595400d73c5459540005f7715954009df471595403e5fb70595403dcff75595400067f75595403d4ff7459540006bf74595400b6bf54595400d67e54595400d67c54595400d6bc5459540004ff7359540024fe7359540024fc73595400d6bf4359540004ff725954001cfe725954001cfc72595400d6bf4259540004ff7159540006f77159540004f77159540014fe7159540014fc7159540006f47159540014f471595400b67f51595401fcff7059540006fb7059540024fe76d8d400aede63d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d400aede43d8d403cedd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d403cebf42d8d40014fe71d8d40004fd71d8d40014fc71d8d4002cfd70d8d40356fa50d8d40356df30d8d400aedc6358d40005f77158d4009df47158d403c5fb7058d40004ff7654d40004fe7654d40004fc7654d40005bf7454d4002dbc7454d401e6f46154d4000dbc7650d40026bc7650d4000cbc7650d400b5be7550d400b5bc7550d40006bf6550d40006bd6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400af9c6350d400af9e5350d400079d5350d40005bf7250d40005bf7150d401c6be6150d401c6bc6150d401c6b46150d400af9f3150d40007bb7050d4000dbe7050d4000dbc7050d401bfb87050d4002ebf6050d4002fbb6050d401bfba5050d401bfba1050d4001cfe76d89400a6ee62d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89403bebf43d8940006bd43d89400a6ee42d89403beed42d8940014fe71d8940004fd71d8940014fc71d894002cfd70d89402e6fa50d89402e6ef20d89400a6ec6258940005f7715894009df471589403b5fb7058940004ff7654940004fe7654940004fc7654940005b
  | 8 => 0xcf5f3254d500057f7154d500077b7054d5000d7e7054d5000d7c7054d501df787054d500367f6054d500377b6054d501df7a4054d501df7a3054d501df7a2054d5041f7b1054d501df781054d50004ff7650d50004fe7650d50004fc7650d500057f7550d500357c7550d5002ebe6450d500d73e5450d500075d5350d5000dfa7050d5001cfe76d89500c6ee62d895000cfd75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d8950024fe73d8950004fd73d8950024fc73d89504167f53d89500067d53d89500c6ee52d8950416ed52d8950006ef32d89500c6ec32d8950014fe71d8950004fd71d8950014fc71d8950034fd70d8950306fa30d8950306ef20d8950005df73589500cddc73589500c6ec625895040dfb705895000d7c765495001e7c765495000c7c76549500d57e74549500d57c74549500057f73549500067f63549500357f72549500376f72549500076f625495001e7e625495001e7c62549500c76c625495001e6c62549500c76e42549500c76e32549500057f71549500077b705495000d7e705495000d7c705495019f7870549500367f60549500377b605495019f7a405495019f7a305495019f7a20549504077b105495019f781054950004ff7650950004fe7650950004fc76509500057f75509500357c755095002ebe64509500d73e54509500076d525095000dfa7050950004ff764c950004fe764c950004fc764c9500357e754c9500057d754c950026de634c9500075d534c95001eee624c9500076d524c9500c7cc324c95000dfa704c950014fe76d85500bef661d855000dfa70d8550035f970d85500bff310d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d8550024fe73d8550004fd73d8550024fc73d855001cfe72d8550004fd72d855001cfc72d85500bef651d85503fef551d8550006f741d85500bef441d8550034fd70d85500bef970d8550034f970d8550286fa40d8550286f710d85500befb10d8550286f810d8550005bf74585500d5bc74585500bef461585503f5fb705855013ff0105855000d7c76545500167c765455000c7c76545500073f74545500d57e74545500d57c74545500073c74545500d53c74545500067f64545500057f73545500057f72545500357f71545500377771545500077761545500167e61545500167c61545500bf7461545500bf7641545500bf7631545500bf7621545500077b705455000d7e705455000d7c705455013f78705455000d7870545500367f60545500377b605455013f7a405455013f7a305455013f7a20545500bf7b105455013f76105455013f74105455013f78105455013f701054550004ff7650550004fe7650550004fc76505500057f75505500357c7550550007755150550005fb705055000df8705
  | 9 => 0xf615092101fe76150921187e651509210efe74150921187ae4150921187ac4150921187e44150921187a44150921187e63150921005ef70509210efaf4050921187e7105092101df47654521036f4765452101cf47654521015f77554521017777554521007776554521036f66554521036f465545210f7746554521007b774545210edf674545210edf47454521007b474545210edb47454521006f76454521006f564545210f7775454521007755454521005f77354521006f76354521006f56354521007e7725452101df6725452101df47254521147e47254521016f76254521017e76254521147e64254521007e54254521005f7705452113ef6605452113ef460545210f7775054521147e7205452101df4764c521026f4764c52101cf4764c521005f7754c521005f5754c521006f7654c521006f5654c5210edf6744c5210edf4744c52110ef6644c52110ef4644c521015f7734c521017d7734c521007d7634c521026f6634c521026f4634c5210e7d4634c5210e7d6434c521007d5434c521007e7724c52101df6724c52101df4724c521107e4724c521016f7624c521017e7624c521107e6424c521007e5424c521005f7704c5210e7d7304c521107e7204c52100cfe76d81210defa60d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d812101cfd71d812100cfc71d8121236f631d8121006f531d81210defa50d8121006fb30d81210def830d81210defa20d81210defa10d81210def8605812102cfe76d91500357e75d915000d7d75d91500d6be64d91500d73e54d915000cfd75d91503d67d75d915000c7d75d915002cfc75d91500d67e54d91500d6be54d91500d63e54d915043ebd54d91500d67c54d9150024fe73d9150004fd73d9150024fc73d915001cfe72d9150004fd72d915001cfc72d9150014fe71d9150004fd71d9150014fc71d915043e7f51d9150006be41d91500d6bc41d9150034fd70d91503d6bf40d91500d6bc64591500d73c5459150005f771591500bdf47159150435fb7059150024fe76d8d500cede63d8d5000cfd75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500cede53d8d5042edd53d8d5001cfe72d8d50004fd72d8d5001cfc72d8d5042e7f52d8d50006de32d8d500cedc32d8d50014fe71d8d50004fd71d8d50014fc71d8d50034fd70d8d50376df30d8d50376fa20d8d500cedc6358d50005ef7258d500c5ec7258d50425fb7058d5000d7c7654d500267c7654d5000c7c7654d500d57e7454d500d57c7454d500357f7354d500375f7354d500075f6354d500267e6354d500267c6354d500cf5c6354d500265c6354d500cf5e4354d500057f7254d50
  | 10 => 0x952102cfc7459521006bc745952102cbc7459521004ff7359521024fe7359521024fc7359521484ff7259521006ef7259521146ee42595211a4ff7159521006f771595211a6f63159521004ff705952100cfe705952100cfc70595210f67f505952102cfe76d91210eebe64d9121015f671d912101df571d91210efb741d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121006bf54d91210eebc54d9121024fe73d9121004fd73d9121024fc73d91210eebf43d9121014ff72d9121014fd72d912147ebf42d912147ebd42d912101cff71d912101cfd71d912147ef571d912101cf571d912146ef651d912146ebf41d91210eef741d912146ebd41d912146ef441d912100cfe70d9121004fd70d912100cfc70d912102cff76591210eebc6459121465ef7259121475f77159121187b44159121004ff7559121034fe7559121034fc755912146cff7459121006bf7459121004ff7359121024fe7359121024fc7359121464ff7259121006ef7259121184ff7159121006f77159121186f651591210eef74159121186be4159121186bc4159121186f44159121004ff705912100cfe705912100cfc70591210eebf4059121004ff7655121004fe7655121004fd7655121004fc7655121005f77155121015f47155121024fe76d8d210e6de63d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21164fd73d8d21014ff72d8d21014fd72d8d2145edf32d8d2145edd32d8d2101cff71d8d2101cfd71d8d2144ef651d8d21006f741d8d2144ef441d8d2144edf31d8d2144edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d2145eef20d8d2144ef710d8d21024ff7658d210e6dc6358d21445ef7258d21455f77158d21005fb7058d210ddf87058d21004ff7558d21034fe7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d2144cff7358d21006df7358d21444ff7258d21006ef7258d21164ff7158d21006f77158d21166f65158d21006f74158d21166f44158d21004ff7058d21006fb7058d21004fb7058d2100cfe7058d2100cfc7058d21006f87058d2100cf87058d210e6df3058d21106ef2058d21166f71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21005ef7254d2101dec7254d21015f67154d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2102ebc6450d21005f77150d21015f47150d211c7b44150d21015ec765092102eec7650921014ec7650921006ef6550921006ed655092101def745092101faf7450921007af645092102eee645092102eec64509210efac64509210efae5450921007ad54509210efaf4350921007ad4350921007e77150921015ee7150921015ec7150921187e4715092101ee
  | 11 => 0x1c6be41591311c6bc41591311c6f44159131004ff705913100cfe705913100cfc705913110ebf4059131004ff7655131004fe7655131004fd7655131004fc7655131005f77155131015f47155131015dc7650d3102edc7650d31014dc7650d31006df6550d31006dd6550d31025df7450d310279f7450d310079f6450d3102ede6450d3102edc6450d3110f9c6450d3110f9e5450d310079d5450d3110f9f4250d31007d77150d31015de7150d31015dc7150d311c7d47150d31026df6150d31027d76150d311c7d65150d3110fd74150d311c79e4150d311c79c4150d311c7d44150d311c7944150d311c7d62150d31005df7050d3110f9f4050d311c7d71050d3101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d8931106ee32d89314aeed32d8931024fd71d8931446f651d8931006f741d8931446f441d8931446ef21d893100cfe70d8931004fd70d893100cfc70d89314aedf30d8931446f710d8931106ec62589314a5f77158931005fb70589310fdf87058931004ff7654931004fe7654931004fc7654931005df7354931025dc7354931015f67154931004ff7650931004fe7650931004fc7650931006bf645093102ebc64509310079d4350931005f77150931015f47150931187b44150931025f47654531036f47654531024f47654531015f77554531017777554531007776554531036f66554531036f46554531117746554531007b7745453110df6745453110df47454531007b4745453110db47454531006f76454531006f56454531117775454531007755454531007d77354531025f67354531025f4735453114fd47354531016f76354531017d7635453114fd64354531007d54354531005f77254531006f76254531005f7705453113ef6605453113ef4605453111777505453114fd7305453100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d8131024fd71d8131256f621d81310fefa50d81310fefa30d8131006fb20d81310fef820d81310fefa10d81310fef86058131034fe76d95210f67e65d95211a4fd75d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521004fd73d9521024fc73d9521014ff72d9521014fd72d952149e7f52d952149e7d52d952149eee42d952101cff71d952101cfd71d952148e7f51d952148e7d51d952148ef631d952100cfe70d9521004fd70d952100cfc70d9521034ff76595210f67c6559521005bf74595210edbc7459521485ef7259521495f7715952148cff75595210067f7559521004ff7459521006bf7459521004bf745952102cfe745
  | 12 => 0xe62d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d8941126ee42d89414feed42d894102cfd71d8941466f651d89414fef741d8941466be41d8941466bc41d8941466f441d8941466ef21d894100cfe70d8941004fd70d894100cfc70d89414febf40d8941126ec62589414f5f77158941004ff7654941004fe7654941004fc7654941004ff764c941004fe764c941004fc764c941127cc324c94102df47654541036f4765454102cf47654541015f77554541017777554541007776554541036f66554541036f46554541137746554541007b7745454102df6745454102df47454541157b47454541016f76454541017b76454541157775454541157755454541006f76354541006f7625454113ef6605454113ef46054541137775054541157b7405454100cfe76d814111efa60d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d814101cfe72d8141004fd72d814101cfc72d814102cfd71d814111efa50d814111efa40d814111efa10d814111ef86058141034fe76d95311167e65d95311e4fd75d953102cfe74d9531004fd74d953102cfc74d9531014ff73d9531014fd73d95314ee7f53d95314ee7d53d95314eede43d953101cfe72d9531004fd72d953101cfc72d9531024ff71d9531024fd71d95314de7f51d95314de7d51d95314def621d953100cfe70d9531004fd70d953100cfc70d9531034ff76595311167c6559531005bf745953110dbc74595314d5df73595314e5f771595314dcff75595310067f7559531004ff7459531006bf7459531004bf745953102cfe745953102cfc7459531006bc745953102cbc74595314d4ff7359531006df735953114ede4359531004ff725953101cfe725953101cfc72595311e4ff7159531006f771595311e6f62159531004ff705953100cfe705953100cfc70595311167f505953102cfe76d913110ebe64d9131015f671d9131025f571d913110fb741d9131034fe75d9131004fd75d9131034fc75d91311c4fd74d9131006bf54d913110ebc54d9131014ff73d9131014fd73d91314cebf43d91314cebd43d913101cfe72d9131004fd72d913101cfc72d913110ebf42d9131024ff71d9131024fd71d91314cef571d9131024f571d91314bef651d91314bebf41d913110ef741d91314bebd41d91314bef441d913100cfe70d9131004fd70d913100cfc70d913102cff765913110ebc64591314b5df73591314c5f771591311c7b44159131004ff7559131034fe7559131034fc75591314bcff7459131006bf74591314b4ff7359131006df7359131004ff725913101cfe725913101cfc72591311c4ff7159131006f771591311c6f6515913110ef74159131
  | 13 => 0x8d51004fd72d8d5101cfc72d8d51034fd71d8d514d6df31d8d514d6f621d8d5100cfe70d8d51004fd70d8d5100cfc70d8d5154e7f50d8d51005bf7458d51155bc7458d51006bf6458d51006bc6458d5114edc6358d51545f77158d51004ff7650d51004fe7650d51004fc7650d51006bf6450d5102ebc6450d510073d5450d51026de6350d51015f67150d511c7b64150d5101cfe76d8951006bf64d8951006bc64d8951146ee62d8951014fd75d895102cfe74d8951004fd74d895102cfc74d8951024fe73d8951004fd73d8951024fc73d8951146ee52d895153eed52d8951034fd71d8951486f631d8951486ef21d895100cfe70d8951004fd70d895100cfc70d895153e7f50d8951005bf7458951155bc7458951006bf6458951006bc6458951146ec6258951535f77158951004ff7650951004fe7650951004fc7650951006bf645095102ebc64509510073d545095101eee6250951015f67150951187b64150951004ff764c951004fe764c951004fc764c9510057f754c9510357c754c951006bf644c95116ebc644c951147cc324c951015f6714c95100cfe76d8151006bf64d8151006bc64d8151015f671d8151035f571d815113efa60d815113ff210d8151014fd75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d8151024fe73d8151004fd73d8151024fc73d815101cfe72d8151004fd72d815101cfc72d8151034fd71d815113ef571d8151034f571d8151296f631d8151296f621d815113efa50d815113ef610d815113efa10d815113ef410d8151005bf7458151155bc7458151006bf6458151006bc645815113ef8605815113ff01058151034fe76d95411367e65d9541204fd75d9541014ff74d9541014fd74d954152e7f54d954152e7d54d9541024fe73d9541004fd73d9541024fc73d954101cfe72d9541004fd72d954101cfc72d954102cff71d954102cfd71d954151e7f51d954151e7d51d954100cfe70d9541004fd70d954100cfc70d95411367f50d9541034ff76595411367c6559541515bf7459541525f7715954151cff75595410067f7559541514ff7459541006bf7459541514bf7459541004ff7359541024fe7359541024fc7359541004ff725954101cfe725954101cfc7259541204ff7159541006f77159541004ff705954100cfe705954100cfc7059541024fe76d8d4112ede63d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4112ede43d8d4150edd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4102cfd71d8d414b6f651d8d4150ef741d8d414b6be41d8d414b6bc41d8d414b6f441d8d414b6df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d4150ebf40d8d4112edc6358d41505f77158d41004ff7654d41004fe7654d41004fc7654d4101cfe76d8941126e
  | 14 => 0x6fb10d813215ef810d8132087cc325813215ef8605813202cfe76d9151156be64d9151014fd75d9151156be54d9151576bd54d9151024fe73d9151004fd73d9151024fc73d9151156bf43d9151006be43d9151156bc43d915101cfe72d9151004fd72d915101cfc72d9151156bf42d9151006be42d9151156bc42d9151034fd71d9151516bf41d915100cfe70d9151004fd70d915100cfc70d9151156bf40d9151006be40d9151156bc40d915155dbe76d915102cbe76d91515173f75d91515173c75d9151006be63d9151006bc63d9151006be62d9151006bc62d9151577b771d9151517b471d9151577b751d91515173e51d91515173c51d9151517b451d9151517b631d9151517b621d9151006be60d9151006bc60d91515773f50d9151007b610d9151517b410d9151516bf75d9151156be75d9151516bd75d9151516bc75d9151006bf73d9151006be73d9151006bd73d9151006bc73d9151576bf53d9151576be53d9151576bd53d9151576bc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d9151576bf52d9151576be52d9151576bd52d9151576bc52d9151006bf32d9151006be32d9151006bc32d9151516bf71d9151516be71d9151516bd71d9151516bc71d9151516bf51d9151516be51d9151516bc51d9151516bf31d9151516be31d9151516bd31d9151516bc31d9151516bf21d9151516be21d9151516bd21d9151516bc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d9151576bf50d9151576be50d9151576bd50d9151576bc50d9151006bf30d9151006be30d9151006bc30d9151006bf20d9151006be20d9151006bc20d9151516bf10d9151516be10d9151516bd10d9151516bc10d9151156bc645915156df77159151515be7619151156be76191511573e751915155f3d751915155ebf65191511579e73191511579d7319151006be6319151006bc6319151157ae7219151157ad7219151006be6219151006bc621915155fb67119151157b5711915155ebf6119151567b7511915155f3e511915155f3c511915155fb4511915155fb6311915155fb62119151157ba7019151157b97019151006be6019151006bc60191515673f5019151007b6101915155fb410191510157c765515102e7c76551510147c76551510357f74551510373f74551510073f645515102e7e645515102e7c64551511573c64551511573f43551511573f42551510077771551510157e71551510157c71551512077471551510367f61551510377761551512077641551512077631551512077621551510057f7055151557761055151207741055151024fe76d8d51006bf64d8d51006bc64d8d5114ede63d8d51014fd75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5114ede53d8d5154edd53d8d5101cfe72d
  | 15 => 0xf7259532004ff7159532014fe7159532014fc7159532004ff705953200cfe705953200cfc70595321767f505953202cfe76d913216ebe64d9132587cc32d9132165f671d9132005f571d9132034fe75d9132004fd75d9132034fc75d91321ccfd74d913201cff73d913201cfd73d9132596de53d9132596bf43d9132596bd43d9132024ff72d9132024fd72d9132586ee52d9132586bf42d9132586bd42d9132014fe71d9132006f671d9132014f671d9132004fd71d9132006f571d9132004f571d9132014fc71d913200cfe70d9132004fd70d913200cfc70d913202cff76591320057f75591321757c755913216ebc645913257ddf735913258def72591321cfcc3259132004ff75591320067f75591320047f7559132034fe7559132034fc75591320067c75591320347c7559132584ff7459132006bf745913216ebe545913257cff7359132006df735913218ede53591321ccff7259132006ef72591321ceee5259132004ff7159132014fe7159132014fc7159132006be415913216ebc4159132004ff705913200cfe705913200cfc705913216ebf4059132004ff7655132004fe7655132004fd7655132004fc765513202ebe6455132006bd645513220fcc325513201ddc7654d32036dc7654d3201cdc7654d32025df7554d320275f7554d320075f6554d32036de6554d32036dc6554d321775c6554d32006df6454d32006dd6454d32007cf7254d3201dde7254d3201ddc7254d321efcc7254d3201dcc7254d32026df6254d32027cf6254d321ef5f5254d321efce5254d321ef5d5254d32005df7054d321775f5054d321efcf2054d32025ec7654932036ec7654932024ec765493201def755493201f6f75549320076f6554932036ee6554932036ec65549321776c6554932006ef6454932006ed6454932007cf7354932025ee7354932025ec73549321afcc7354932025cc735493201eef635493201fcf63549321af6f53549321afce53549321af6d5354932177cd53549320074d5354932005ef70549321776f50549321afcf3054932014fe76d853216dbe74d8532005bd74d8532457cc32d8532166f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532006be74d853202cbe74d8532004fd74d8532006bd74d8532004bd74d853202cfc74d853201cfd73d8532024fd72d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d85324a6df30d8532456ef20d8532107cc3258532166f46158532005fb705853215df8705853200cfe76d81322d7cc32d813215efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d8132014fe71d8132004fd71d8132014fc71d813215efa40d813215efa30d813215efa20d8132
  | 16 => 0x8d42004fd75d8d42034fc75d8d4201cfd74d8d425cebe54d8d42006bd54d8d4218ede43d8d425cedd43d8d4202cfd72d8d4257eee52d8d4257edf32d8d42014fe71d8d42004fd71d8d42014fc71d8d42006be41d8d425cebc41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d425cebf40d8d420057f7558d421957c7558d4218edc6358d425c5ef7258d42004ff7654d42004fe7654d42004fc7654d4202dbe7454d42026de6354d4201dbc7650d42026bc7650d4201cbc7650d42005bf7550d42005bd7550d42006bf6550d42006bd6550d4202dbf7350d4202f9f7350d420079f6350d42026be6350d42026bc6350d4218f9c6350d4218f9e5350d420079d5350d42007af7250d4201dbe7250d4201dbc7250d421cfac7250d4202ebf6250d4202faf6250d421cfae5250d42185be7150d42185bc7150d421c6be6150d421c6bc6150d4218f9f3150d421cfaf2150d42005bf7050d4202dec7654942036ec765494202cec765494201def755494201f6f75549420076f6554942036ee6554942036ec65549421976c6554942007af745494202dee745494202dec74549421b7ac745494201eef645494201faf64549421b7ae5454942197ad5454942006ef63549421976f53549420076d53549421b7af4354942007ad4354942005ef71549425bfae41549421b7ac41549421976f50549421b7af4054942014fe76d854202dbe74d854201dbd74d8542186f661d8542187b641d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542186bd74d854201cbd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d8542186be41d8542186f641d8542186bc41d8542186f631d8542186f621d854200cfe70d8542004fd70d854200cfc70d85424f6bf40d8542006f610d8542186f410d8542186f46158542187b4415854200cfe76d814217efa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d81423b6bf43d8142006bd43d814202cfd72d8142014fe71d8142004fd71d8142014fc71d81422f6ef21d814217efa40d814217efa20d8142005f77158142185f4715814217ef86058142034fe76d95321767e65d95325a7cc32d95321ecfd75d953202cfe74d9532004fd74d953202cfc74d95320067e54d95321767c54d953201cff73d953201cfd73d95325b67f53d95325b67d53d9532024ff72d9532024fd72d95325a67f52d95325a67d52d9532014fe71d9532004fd71d9532014fc71d95321767f51d953200cfe70d9532004fd70d953200cfc70d9532034ff76595321767c655953259ddf73595325adef72595321efcc32595325a4ff75595320067f7559532004ff745953202cfe745953202cfc745953259cff7359532006df73595321ecff7259532006e
  | 17 => 0x34fd72d91525d6bf42d9152014fe71d9152004fd71d9152014fc71d9152006be41d91521b6bc41d915200cfe70d9152004fd70d915200cfc70d91521b6bf40d91521b6bc6459152605ef7259152024fe76d8d521aede63d8d5201cfd75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521aede53d8d525fedd53d8d52034fd72d8d5259edf32d8d52014fe71d8d52004fd71d8d52014fc71d8d521aedf31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d525fe7f50d8d52006de30d8d521aedc30d8d521aedc6358d525f5ef7258d5201d7c7654d520267c7654d5201c7c7654d520357f7354d520375f7354d520075f6354d520267e6354d520267c6354d521af5c6354d521af5e4354d520076f7254d5201d7e7254d5201d7c7254d521ef6c7254d520367f6254d520376f6254d521ef6e4254d521ef5f3254d521ef6e3254d520057f7054d52004ff7650d52004fe7650d52004fc7650d5202ebe6450d520075d5350d5201dee7250d52014fe76d85521a6f661d855201cfd75d855202cfe74d8552004fd74d855202cfc74d8552024fe73d8552004fd73d8552024fc73d8552034fd72d8552496ee42d85521a6f651d85521a6f621d855200cfe70d8552004fd70d855200cfc70d85525367f50d8552005bf74585521b5bc74585521a6f4615855200cfe76d815219efa60d815201cfd75d815202cfe74d8152004fd74d815202cfc74d8152024fe73d8152004fd73d8152024fc73d815240e7f53d81520067d53d8152034fd72d8152316ee32d8152014fe71d8152004fd71d8152014fc71d815219efa50d815219efa20d8152005df73581521addc735815219ef86058152034fe76d95421967e65d954220cfd75d954201cff74d954201cfd74d95425ee7f54d95425ee7d54d9542024fe73d9542004fd73d9542024fc73d95420067e53d95421967c53d95425eebf43d954202cff72d954202cfd72d95425de7f52d95425de7d52d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542004fd70d954200cfc70d95421967f50d9542034ff76595421967c65595425d5bf74595425e5ef72595425dcff75595420067f75595425d4ff7459542006bf7459542004ff7359542024fe7359542024fc73595421b6bf435954220cff7259542006ef7259542004ff7159542014fe7159542014fc7159542004ff705954200cfe705954200cfc705954201dbc7655142036bc765514201cbc765514202dbf755514202f3f75551420073f6555142036be6555142036bc65551421973c6555142005bf7355142007af725514201dbe725514201dbc725514220fac725514202ebf625514202faf625514220fae5255142185be7155142185bc71551421973f515514220faf2155142005bf7055142024fe76d8d4218ede63d8d42034fe75d
  | 18 => 0xe76d95431d67e65d9543214fd75d9543024ff74d9543024fd74d95436367f54d95436367d54d954302cff73d954302cfd73d95436267f53d95436267d53d954301cfe72d9543004fd72d954301cfc72d95430067e52d95431d67c52d9543636bf42d9543014fe71d9543004fd71d9543014fc71d954300cfe70d9543004fd70d954300cfc70d95431d67f50d9543034ff76595431d67c655954361dbf745954362ddf7359543624ff75595430067f755954361cff7459543006bf7459543214ff7359543006df7359543004ff725954301cfe725954301cfc72595431f6bf4259543004ff7159543014fe7159543014fc7159543004ff705954300cfe705954300cfc7059543025bc7655143036bc7655143024bc765514302dbf755514302f3f75551430073f6555143036be6555143036bc65551431d73c65551430079f7355143025be7355143025bc73551432179c735514302ebf635514302f9f63551432179e5355143005bf72551431c5be71551431c5bc71551431d73f51551432179f3155143005bf705514302ddc7654d43036dc7654d4302cdc7654d43025df7554d430275f7554d430075f6554d43036de6554d43036dc6554d431d75c6554d430079f7454d4302dde7454d4302ddc7454d431f79c7454d43026df6454d430279f6454d431f79e5454d431d79d5454d431d75f5254d431f79f4254d43005df7154d436179e4154d431f79c4154d431d75f5054d431f79f4054d4301cfe76d89431ceee62d8943034fe75d8943004fd75d8943034fc75d8943024fd74d89435c6be54d8943006bd54d894302cfd73d894358ede53d8943006dd53d89431ceee42d89431ceee32d8943014fe71d8943004fd71d8943014fc71d8943006be41d89435c6bc41d894300cfe70d8943004fd70d894300cfc70d89435c6bf40d89430057f75589431d57c75589431ceec6258943014fe76d854302dbe74d8543025bd74d85431c6f661d85431c7b641d8543034fe75d8543004fd75d8543034fc75d8543024fd74d85431c6bd74d8543024bd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d85431c6be41d85431c6f641d85431c6bc41d85431c6f631d85431c6f621d854300cfe70d8543004fd70d854300cfc70d8543506bf40d8543006f610d85431c6f410d85431c6f461585431c7b4415854300cfe76d81431befa60d8143034fe75d8143004fd75d8143034fc75d8143024fd74d814302cfd73d814301cfe72d8143004fd72d814301cfc72d81433c6bf42d8143014fe71d8143004fd71d8143014fc71d8143366df31d81431befa40d81431befa30d8143005f771581431c5f471581431bef8605814302cfe76d91521b6be64d915201cfd75d91521b6be54d915260ebd54d9152024fe73d9152004fd73d9152024fc73d9152
  | 19 => 0x401400300000040000010010018012003003800c002001006800c010007000000805c00900000080060000008004002002000003c0000000050000004001024fe76d8d54216de63d8d5402cfd75d8d54034fd74d8d54216de53d8d54216de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d5462ebf42d8d54014fe71d8d54004fd71d8d54014fc71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54216dc6358d5401cfe76d895420eee62d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d89545e6bf43d895420eee52d895420eee42d8954014fe71d8954004fd71d8954014fc71d895400cfe70d8954004fd70d895400cfc70d895420eec6258954014fe76d8554206f661d855402cfd75d8554034fd74d8554024fe73d8554004fd73d8554024fc73d855401cfe72d8554004fd72d855401cfc72d8554206f651d8554206f641d8554206f631d8554206f621d855400cfe70d8554004fd70d855400cfc70d8554006f610d8554206f410d8554206f4615855400cfe76d81541fefa60d815402cfd75d8154034fd74d8154436bf54d81543e67e54d81543e67c54d81543e6bc54d8154024fe73d8154004fd73d8154024fc73d81543e6bf43d815401cfe72d8154004fd72d815401cfc72d81543e6bf42d8154014fe71d8154004fd71d8154014fc71d81544367f51d81541fefa50d81541fefa40d8154005f77158154205f471581541fef8605815402cfe76d91531f6be64d9153024fd75d91531f6be54d9153646bd54d9153034fd73d915361ebf43d915301cfe72d9153004fd72d915301cfc72d9153014fe71d9153004fd71d9153014fc71d9153006be41d91531f6bc41d915300cfe70d9153004fd70d915300cfc70d91531f6bf40d91531f6bc645915363ddf735915301cfe76d89531eeee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d89531eeee52d89531eeee32d8953014fe71d8953004fd71d8953014fc71d89531eeef21d895300cfe70d8953004fd70d895300cfc70d89535f67f50d8953006ee20d89531eeec20d89531eeec6258953014fe76d85531e6f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d85534e6de43d855301cfe72d8553004fd72d855301cfc72d85531e6f651d85531e6f631d855300cfe70d8553004fd70d855300cfc70d85535467f50d8553005bf74585531f5bc74585531e6f4615855300cfe76d81531defa60d8153024fd75d815302cfe74d8153004fd74d815302cfc74d8153034fd73d815301cfe72d8153004fd72d815301cfc72d81534267f52d8153386df32d8153014fe71d8153004fd71d8153014fc71d81531defa50d81531defa30d8153005ef72581531edec72581531def86058153034f
  | 20 => 0x100900080100030040000000001001800008400000080000060000020008002002001000800000000780080000000138000024009000000000000b000000400400d000000400e0040010010000000000800000c0030058000002011000001c0060000000000010000000000400a00200a0000018000000000400800500100000080000080010034000000002c01400000080000000000010018052001000001c000000000003c01200100100240000000018028004008001800c00c00d0010004000000000000400200000200000000060000008000000012000000e002006006c0020030008020000002005004c000006003001c008001001000400e012005800002a000000000800c003001002000200b00100000020010058048006019002001800400000080040040000000000022000000000000600000100000120020008000000012000000800200b001000c000002004800000c0090010000016001000800000600200080100000000000008000007004001000c0000008018004002001001c014040000002000c00500100140160060070000002002001803800200c0008004000001002005c0200010000040006005001801400800100100180000010028000000004001000400000000180140000070018000006008002001c00000600000300020000000000000002000003c0040000040000020003001002c000010007000000600000e8000000002001000c0020050038000002002001000c0000010018008000000000802c00200200000000000000000014000001002800000e0000008004000001000001400400f0000008000002001000000400100280000020120000004002003005000000200b0018010000001001000c014007000000000600e0008000000002001000c0020000000004002000008801000a0000000000000000002000800600100280000040060000000000004004002400e000001801c008002003003401001b0018000000001007002000600c000007400000100080040260000038014000001000000400400000100000060100020020004017000000000000100080200000000010010002008000000c01400200200040060000000000000006000000c00e0040000010000013004007002e000000800000000d002001c000003002800800000000000100020000040000000003000000800c000000000c00c00600080040040080018000004004004800400c005003000800a005006803000a0020090010006003005000001200200080000000000000018000000001003c00200301b00000000010008040004005006000800000300080080020150000020022003002000402800000100040000020060000008000001800c01a006000800000600000380000000010018034000010003800000000f000004
  | 21 => 0x58000c0ead8642a31d6d853a6931c58b8a078000000000000000000017ba00000000000007106a100000002150000000e9618300000000000004eca624000000000000000000036f00005d45e600000000006c510880000000ff00000010780000c60000bd858c00ba29d4a088c4451964020b2d3aa88480000005fc10b100e9b92c18ee460ca2928a2738000b9c14c15685a058600000013d80be2fb8000c527170001eb800053368c8000000000000113000010e419b0fc4b00000fd089d3e60002b780007ea0e413f80000000002eca3c40009480002214f86cdc513800117400000001dc0000000000000b50000072800000000000008a0d8c00021b8000806af748023f08eeb14479000e00100000000060000000034000000000800401c0020000004008000005000800400000080000160000058014000002000004001e00000000040020040008028012000004000000400d003000800000100180080020090010028000004001800400e0130038000004001005000000e00100e801800400400000000020050098018008000003800000000700080040000110000028006004004000800c0000010004002003003001c00400c000000000600200100000020030008030000012002803c00c0060000074008004000003c00a0020008004000003001800000200300000180020000090004012000000000000000c001800000200800200000180010038014000003000000002200500000000020020038004000002000001401a00100080200060120010008004003004800402c000004801c006000004804c000006001000c00800100000000000030008000000001001001400600700c000002000700680480060010000004004001001801002800b006000c01600400000000000020000024004003001800800000200000980000010038008012005000800400600000000000000080010080000002001800c0000030060004006000000002800400a0000018008000000800c0020010010044006000000000402a0000030020002001000000402e004000800000000000000100720010008008000002000000c00400100280080080010010000006002007000003401c002000002200e0000044000006000000400a003001800c00e00c000801000801100000040140030000024002000000000000400500000200000000008004002002001004400c0000018000004002000803001200b0008000008001004800000600600b8004002000004000c000003009802c00200400000080020000080004000005003000400400300300100040050000000000004000806800a00a002001400e0020008014008001005000000200300000080000010048004002000000001400c0020000000006000000000c010001000000000a000000000000000
  | 22 => 0x7e7340000000f3c70e12600000000004910f8125c00000000014d059f5b10000af8b8848180012184b067718d96504a21631aec44ca7f3c51d04ff80b23eb13bccd8c3a0c0800041cac015ba730000c153c088510b4c1a4671844fe60005d8800186266566d0ac98a0b4d0221f8c84a9dc5370000d1845600000000004283f78e28976a8200008212c4adf2f400012541d34651d59964a0c0620001520000000000000080b264979cc6e00000033bc00000000015c80002fe45d9c1d132a5934522009d60e9000087147425a2788000000cdd57480006a010914389b086a0004ed0000000925000281c0bc16215a304d14200045b20997c0cbb46b1fc40ec0000a780000000000a30000bd289e5c280000121bc000035c000d0c00008ac5c000013031b80000001d6800019831f6790b0800000031e80004620004ef800118000000000000000000000000f3e00056d80000000002a70c55a4e2632919c6000000048f09e800003c65c245c00015839c00000000004488000a76bba00030101f0379220134197a000075b4e82e204651c2670d4c929480a3809689c02aa28c00001402a11b29772bc931ca1cd46e29154913887ceb400ff352076844904a25b59268a53dc88ccada4883941e399bc0006969d7d2ce00019c80005c4be841c21a0000c3d000049800000000008d511c1c100011a00f47b41e68000000176000000026e00048724e0bb40000000fc000000036b1208aba5020002da089aaf629580002c800000026fc0008cc5ae000000000022f104c000000644b0f8000299000000000000000010398be000000076c89e95027a8000e6caaf061a42427479c10691f5a0898c31286c8fdcbae42c9bccf4ac4f409b1a91b80000000e982a8c5a38fb3a40000001fe0000000000000000031a0000000000b6088100009d5320d1b0658000000000000000000027d1cc2a1c720b1d10c848da12c6432f0bf4dce0001a400009640000002cec6da0001a6000091c00069d80000000a54921f540000004b2857810ec840000000326b3509721a993682c00008f8e0833e0e003b47ae0001ffaeac14e4220000000c4c8b34958000000a2059c12715c2bc5511b1e406200027496b833cb9f6561f752c0acf13da6c838a5f050f1084734d2531108e16ee06b00000002ce000000000000000000000000000e3608800006e00000020ac30c0003a40000cb000034d2d6d5bc37a1ba847c04c0000000000f6400028f06000003202ee80000000003ff9e1129a0002d380000007c700001fda5eb94000000000000005da4508aa93c58580006225453e0075c36e18257302302ea4aa6130000dc64720481030ea686249880000000f026d9880f82000539afcd0beb050b780015d84831c7873c998d063b980019c8000434992d5424fe4da8348d402165b
  | 23 => 0x131e7f8038905020cb765f180005060003621ba40006d160b00f424a00000010f9a58c6503e2d148f640810d2324c38574077827d498333026800055447800000000002b51988000000000000000171e00000000019f200036180004e88fa540ae84e7e0003b61e80528177000000057864215b0000ba84ad00004d400000007c8648ef65285f3019d29e9b05cc99dd832ae344c13f0c7e17c5cd98a937400055603285e400000008fc00000062da3f4c3a95401a9da52fe0004f31e08bc80000001bf000050f000095057027816f8000d5400000027a00008881bd83540001410b71df43744cf00000d800000065d33940002bb55f8b3466400058880000007644608000000bb2000121152200000008e40000003b582e016883d088000024800005129083421f5064a648000000000000000087128f86bd1a65581e1800000076e4e595b80dab8c5a593e000015a090000183636c0c418514f89a96522d441ee7b042bafd920a68b3879c69754b012092144a7a67852a8d391584b11d8800184600000001ec50c490000139095855f0001d6049c0345241ab08a200000005a8e5a73a51900011200001df8000c560001861a0800003864b0000286b2e00000000000003dc0f1c000c5851c80000005100dc80000000006701f7000000e0001708000a4018430e04883da4e11ce543483b3e6000019e8c400000017300001d100000006604e6a399a1ab63000000073a30e3e10f650920005728001a520001e030b822c00044b19880008423679fc12e881522d87e56d210000002112ea0000000afc146c086181e8555a0000000000000000449800159200069225e41501c92bb9958ce0cbf24097cca5a7302c410142663f16900e18952a76699abc54786b81b924ec0001785d19a88156bcc427190498e0000938f404dccb53599ab4000d4441f2d5c000c1010129855541ed57a000000034f0a60000db6000177000199c71b35481a81e60003d99e0c00094e12a9120000d0854b8a34eee762011ad251968f9338964149223b24aabec5402f500017400001e5382aa7cf7e655000000000000031191cc0007ad29131815360000ab03880005fc000242d26453e57c084ca26000000330c172c6f00000000000002e98a68000aa8671004836823a02d26a8000cd41d283d117e8944a1800000077c00000000000003d3a334000c9a41b2cb0d420005e31ba000000000280019600003f0176c00029e000040c000b1531726054d21c23cea9e4000a45482108c38c88b000149d6cc000022800154c7aa64a80000004a02189e480002c9000124400057d0002179496000522000175a16d43580000000001aa171800000028600019660406272fe580a0002220000ac00b14a200000001dc28aa97503e5ee3428000000000305262d6b20613fd00012
  | 24 => 0xa63a902ba04015cbff1de83f19f087900000000000000000a8400000000000008f859e60b80000000000003399476a83641000101854d08b80011ce4f20000000b0a00014ba2e528c91637c8e652429662da9c251409862e1aa58f50309238adb91448be00002b04be00001d0a40cae9a251ab3a8682c4156b80000005e0215323c0008080001d70e1831c0002fc00006b74f8b0840005ad0f8aef01d00000003178e580004bba12092c33a3bca748b725cb16b2d5445ab730fd82486a4a475c9012c87a3ac2a7b294a2200000000018e825600000002040001600a00000a4a00000004366b00d4aefd932c012931bbc000b23191800002c9690601b540a856713200014c05320000f7467052037f8e251c4194689abf8000ce80002fdc15e0001563318a0a08d4420aacdf43b269e00010aa57845400003a067f04e1bb108630b0002088e6e00069a813000000000000009943873231c7867e00000015552ec00000009884ec45058f00000002fc4ed8d4d5d0cfa3a328940000005811bf80000000d1800000000000000013dc7271190a8c25e6b242a00008f283f4c7000000048900031c035c1a2000276177a0003949fc941a72e1fc92f92842e75e5ab0508eabc5f28c0467a8db5d6135d9d87fe2dd28580007e50c380000000003b5083190043600027f40001bf56281cd2dc79300003b86763ce52bab1800071500015716480005b38000f1e9bd1148000000bfd41280000000000000f5000095146b9c2165257f5c0000000046100000008a40000002ccc1b436b0530cd000000000000000006dc61500001ce8a60002c9da300005e0939460a024662966d64a85300022a8d6c7ca3238000e800000b600000000000e5b2780000000000001a8a38500029780008750000000c0c6cc00000013c647532200000000000000000000531340800000000000031f89dc0004ae0e3924600066100000005df0002254f2228400007a4f560d1013800022a86f42615f8000b6f62232193584b53e880000006126391ebca300000001bb96440004bc00103940003dd00013323165b680000000000002df8d280005822b10a960000000000cc200000000000000005049660000add23529580000003d60000000000669b2845e01a75dc2090000000000000007613b2750000e269e94fe0000ec24f73608000b220004d18000000b7511e00015dc0002fd80000005a52508bbc68e9d119b004cb0e00046a800171600000009dc0005c749c84a938cacc555af005166791d724082fa28563a854800009943099f13e42cc5428f14106bc213324a182400004d192149ab4628e0a08e784fb2c692000001384b7b3856b400144ea2b40be1b05bd0000f2800000017587660560000b8d41c76d46110c07602953e6a2c05a2c4b0348f840007671b53468000cf10
  | 25 => 0x5e6a1019fe00027fa48116a6ea1b0159463200006f00cc000aeb1c21f6cad01601e200010d872a58513b40009ea65b8b1586e0001982d05a2e05958fa2f0d500001950cb595e92f27610701103712ffb4090ec0004af15e567cb4f4b19d74316968551b4896f094b44126e10dc0605beb3588640004100000a0669b36b9ef4ad20000ffa0c8f9c38856533f4d6a85000026203624bf0001a012fa00036f9e68222c3600000000000005682bbd93a22f538b43d2940002d8aca86580000c880000000000000e7d8ee30400000010969c50002790a08000000000000032f000000000093d42b1c94000000110800000081e2468af44f800000027d82b8c87112800000034429082f4f9e0002010000000ad50000908b6c400000184d7d668340498c909456600009a42b6a144a3b1513fe6b43b28738c945c425d07b87a649746d310d23012c0e6ac8156ea6706b34846fc2472f1a6451d277145881d12b6cfc36023fd2ac24508c8000058994243894c00000000001048b04b33a2000000000063c3198cc600000020c00008343e48d90b7667a56990ccc7854a55c00000009c90a22dc000000000026780001e424a010d91600004c02153a61ac00034b80000000001f9c00000000000001cc0000001fd00000000002e1c00000000000011a00001fb99b452ca9d216a2d097aca6000061000000054d0f54b8000029a0b600000000002b68d7e1e242e01f471884f3a5020000064d595a004b04ba712302f15520001e500005cca2f0001c496ba00000021745380004f395e8b2ed1c000000000000000000018f64a50dd800108a0000000000aa47df00000000000000000001a62ced40d0000d7c87400030880004170000000956000008a5017d85005d30000000827063800000000000000019b600000000008fe000000000145a84166f91b153c00036e87d82d655b000325c8740005fa000000000000023612be9bb05480000004c800010b94f42eb5a42a3c5102b3297a55c1b80002338a258e6af0031318cb647194a98b50950a0f30b80011a467e00004280000004fbaa70d32be45c08000e7c34230c9d5c0006c23b020085e84e830b2f7098c1bd0000000000be123284700000000129108000ae702880000006bc00d80000006da000082c0005d20002d780000004c210757b46b90f8204400000000000000008f75151bc44f2b3f203275c000cf561224f8cb6a2b00003416882fa4d39c0d8d284d4a6331115639760eb1445f2434000219d562575000233c8120003bb00004aeb5f00018e15e60005f10000ee8000000000018a0006248000000997304ab71a0050d547266d06e96a00f1428b025ef00000000000003bc30b12261eb2320000b3a87a6070de0da6c7c29600018fa0003de1bdc6fa6a5262aa5054a000163b1a02026c760e2c38
  | 26 => 0x9530865561b03015477f032880000064300010119c6ba03cc9e88a5266447daa9da2066e326000074018e00012180e400065018c000000040e800017e63369e97c8000218000000000042400004783a86a4370a38476a14564c0dcd18ab1343b8000000c5d2d9b080ac47de4faa9acdf68df4572394eb25563299d152b253513534500003a40efafa457c19a3b79c040002a81452cc00000000000000c4e00000000008727426648a749aa5fe000106000045d48ca0389ec3e657e2cc89c09e568f8d5c10417a5f7a3a8f7600041a9c00f0a0000002af8fa06401f4057d81600032d2f4c0c60003f50e054de2010fb8fb47c635c4cc06ac2780001b3000077400043c165803272b000000000000025186d89260000f63328000d4a14da654cf67230d22ef8c0a8bd372b15976eb953df0dd9a564c007f0420f900b30001c744d05bc4d080000000005819a794500000039f905da72616d95c47fc22c08d080c1eaaf90002b3800000000026a051e000657252400000019e30ed96c8191568000e620000f0348c9240cd3e2085c82a7e8479800154015050d9770cba52a0b28001a3a7510898000a6e00016ab36000056a2808000ca20000000001568000000201400005d000000195400002832283880000000000bb000050280617ac7e14cd00013401ef5e3a4c19464bc0002ad961aa0043f0000000105265b45893420409a2df0ee435b01722703ba99315d003131a00000019f597200057900000000005890b640000001c8800000062d3c3011d4e01fd3fe96e0d1e1281ef2a358aea4f501b34550c7a45d2837c000a7d2f8af7da02c94583850871600000034c00009ca0001b34000b4e18b884102c39c5ea27ac1845944d6a86400091532f94fc00068d4d2000077699f6491638742a6c49b9e302e0ccf60505d0c7642b49d0d9592223603718f95c09a6237ab500009360278d8c0a42c426080005e25730a580002567b660a0ebc0f2a933c4922d4cc43f0ae833980683963884c412c60b2fd26b8a2c0005848000a1c0004d593601b02ce5bc8ac00008b85860d18b7e0000000d7c0000002dbae453aaca700011145baad12311720f2a7245208000fd21045eca870000b183e98000b7c0001fb2560000000615b130000000298000000014a0001998d46000403076800000058d0b0cdb0911000178837c1b5000154c338be7000022d5c80000000da000000000013e800017b1fd89c400039b1e400016320000000b782720000d000009c22cf62900000005a419b8374f2c17e365b42c822343000158483e0003f100000000000000001a6eacd07880010060000910000bfa38300013c03a4bb428eb341088bee18a1950000695195800000025140e00007e6cf4000000099c22004e8becdecc02000219878c8d400000000000000000000000447
  | 27 => 0x866b9e34b260002da00006aa21f000297c49200019480015c40004b997300003cc0003304a16c9000010bc00015969c8000000a58607800000000000030b464e000619800000000053d9264c3c00000028fc000bd06798a7d0625d50ab800172062c0aa9c44ba2b2f410afc4ce40003293301416ac84ee8cb93e086317b0000fb444a0fc0000000000000000040a00000000001b626f02114d97ea49b00000008321e626ea5f18001961461bac77c0000001e5c0000000d3000000037f2a428186b46f00002dc445419d348a95166c97b000005413658920f311c31e5f90bc83d80000551be151032a05b00017292aa0200000000000000000000161e00049aa05c0cc9ef69906b4000000000000000029330d1a2152ac590000fb98120003eb8f58704000544000148c60e12e00000000004740d008364a60001f50000185688a968f8c0005c1220c0d063a234983597c0002e712d8aec31d0b30000000000000000000040b49324b00900001b0800000000025b800147c3a710e800175ed2a00317353c05643b1a61c0007980001a6000000068900000000004b80000fee0000a68c885f000000000015f4000357800005ecbc5d800003201f44a0a970a0c00030f92bc000afd000260c81e41a00000004ba4432c018218647f623f247d21400021dadd0d1ca3160c0000ea42720000f7c0003a34640c6cf4c3f23108c34000889449047400000034b80000105994e0800000000000000005c80005e8b0a06ac00043919d19d63b75391fec9ccb212209809872000390870d25a8f8157b204f1000050a8000000ca844f958c82c42600032880003bc430042c0002611cb26cc000bca5c20a90000a6247180000005120cc18403a29af1fc003412a05c58001f90283210f1a3c151864900019d82d2b7224f800121e0d90000000692ca96368000000b3d56cabd42183b83a626591c8abd18030d4ad80005a800000003ec56580008dab390cc89798686284579c713f40ea04517a88d6cc70a703f4e925a943dad0c64c30f16407657aab605e201242d05436030cd56a470a333800880e0700001a253bcc2900028083d4c4000016112e48ef1e4851c4825e543fa3743544b822d20e80000003da8000000000000024d8fe0006a0044800000000000012b400000028cc6244c20000878000000000000199a0001f480009a8d0e4df351c18290d5e1aa2c9ac410000000c73c2223f58000b5850900000000000003ec8c6047a30339a800105436700017b441200028b800193845427a15c166e97a05a888c0000000000000000ab53c800004b63db00000000005de00000a06ee73b00023d51d60e134215645c2a1d1942dec000a3d000000051c549153800000000027cae3940200000031b04e0130000000145ccf0355a08c69a77526c800048600037a231
  | 28 => 0x90af620600000000000004fd8e4c0000001760001a0aaa5172a3b407c03f1748ea0bea0004fc800000000055800018d600000000000000006a080017e4b3400000006bc00058b1b911644d269b05cd20ea7516b962d8ce0000000000000000000005105a00057680011520001e8800000000000000000000006308000000b420002ed800095d4d88f894a600000016ac00000000020a07c874d1fa2e24490846673980c2fe0000000000000bed64184d8e2846600000000000000000000000000000000000000000000015fe3454689275a86000136b0f1726000337a3b07009fe1f28000d2c00000000014208c348300000007a300000005ee0000000000000c1f5a5163c00017218f1de924e88f00024686b2395032000093c00000000004a4cd25f52a2516e668606b18809cbc82a00b4937877036a00017ae85205001bd85ec553bf28d09a6aa2105000000000000000001d8000292800193e0004ea00011dc00000033dd4c674e5592034000bb31db09f800080027e800000000003a800000000000000014a24c429c261415aaa42f589003d04cd189ae6991ca4369fb3ed12e3ea0000000f529c3229b4e00001212e48075422a7e3e291180162d35bf80011b282946f003c84e00000034f92d652459880007b00004bf2a28000693000045000000040c35180000002718a98d0c72f00018d4c360001fd00000000004da18bc4a0bd804b80000002650001b9957600000034a000000000000006347f56838204000bdb00000010140000002048000b10083915c00070d5fd11c00006040000ac51fc00000000000d835d3672b586480a14f691b840e5a6300299400061844d800025244e0ef0000b2423736832340446345b51541410a0a000000079673d58d8d2c90ac07000287c0000002100ff400053c0000aa501e6d91408000e4000048ea889408c7a1ba2d5021a1c70002e0c0561fc000000139000000000008c69d00000bfc000000000219150019706a141d1466fd65880019fc0002a60028d38000542000000000035880003666693aa00016ca00000000012385e123b27849e6b974db2ea184a0002258000fa448c000000000000030a8000f961a829c8ea99565083a7800138800000000019965bd322800000078726d1970b5e00021e1cc83c200066400009140000000000000ac23b42f497f80005290000d920b62fa134400036230780014f06010000000000c532d01c08160c4d0000000230c46624260979c24f00000000002340a4800049a3cf40d800027a4a400000010da37050980000000005ac000110e39200029d14da000622afec0000000eaa218122aba339ad908be5f81740000290d153f6000041e2f31180c1c000d1e047ace800022e43e00018ec9d60521c1955c0003c5ae2911aa1747b00000006755a9a6950b61c
  | 29 => 0x8b247400032d0c1882f05d07c99aa00000000000000000c5000019000000000011e800068521600006502a3aed4b446313350000728163000000000000000000006040fb57504c973a00050c246cd3a6ba0001fb400011b0000b058b818902c0000bec1d64b0aff968e6d2343ae34a36b6168184fc8f445c3c02788d5c4294e380b549c1a5014a4cc034ad24fc0dbc00087031215452100000000000f625571b48000eb491000002394c8c8c25728489bc3c1000000000000007925c40000000002d58b4254655992e40000005930000e44000000000184e34a15c9d4000059a2a0a7d0ff25aa0000000b46351192af78eb608900029a813c0005a6000000000000000e4000b9e38583180000000000b70000a5b00017042c2b9644d054400000060f2a64b2a01f0002e88a320004a9336400000018832b4c9ca2600031280003eb5831d9810c99d1b721f49ce6ed000201087000001803e80386f25c3066c3980004b609293002a23f3000105cac726fa8b00002ae48900008023d2000000175224b000099c7de6e2000167174800016d0b2cad635837a9af54ee64f2970000d3e02a58b95780000006211be167800000002dc0009cf0a984b44b2000000000000000067b0000dc01f34a2a8904e60e00ec2628baebbb1d584f859479b0252885a6838d069800157219f2069a9cebcd491122c70000000010962800074700026dce66bcf08780003702920001468fb03c224c1edc064690230079d46c0003358f700000000001029998b080000001268c88000137094e00000000004d66c8261923cb9e30a3a1a290d2400000025
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ee87d89424c00759905b2a649800e3721d654c93001d66412ca9926003ace86d89324c0015990ca92649800393595524c93002c5f424eca8a60008bd849d9514c00d1ed0fb0aa2980032d1d361545300156b40ec898a60028dc87591314c0059a8eca8a6298196e5211514c53000c6e432e690a6006a7a85d91504c00d1f10eb22a09805ebc2056454130006e5996e4a826000e6b52d89504c001e92a4992a0980029e21951541303259c422a2a826017e7061545504c0013b10e98aa098006b62193154130007a8a8a62a8260018f8805c765480091bd0fb9aca90003331cf72595200147b43ee2b2240008df835d954480091b906bb2a8900023de0576551200147a40aecaa240008f7815d363480051e902ba6c69000237e0d7654d2000477c12eca9a400487c8759553480094b906b2aa6900021fe157650d200343e42aeca1a40008f7815d943480051e902bb286900122f21d6450d201c55a40ac8a1a40058de87d8d434800959907b2a64900123b21d654c9200256641aca9924004ace86d8d32480015990ca9a649000393595534c92002c5f424eca8a40008bd849d9514800d1ed0fb0aa2900032d1d361545200157340ec890a40028ec8759121480031d90cb9a429000b391d951485202add2422a290a4006a7a85d91504800d1f10eb22a09005ebc2056454120006e5196e6a824000e5b53d8d504800d1f10eb1aa090003d254d32541200053c432a2a824054b3884545504802fce0c2a8aa0900027a21d215412000d7443242a824000f615148550480071f10cbaa60900123e21d654c12000de443a649824003dc8874c930480037950c9926090006f2219324c12002764432649824004ecb764c93048007b94ec992609000f721d9324c120027643b2649824003cc8764c93048001b96ea9926090003725d5324c12000765b2a649824000ec9654c93048001797029926090002f260d214c120007e098a4298240058be87dd16544001968e9b8aca880030f5d754d91100045fc22ecaa220008f7815d954440991ef02ba6c68800a3d20574d8d100045fc22eca9a20058bc845d953440011df04bb2a68800e3b2097654d100047bc0aeca1a20048be87d9143440991ef02ba6c48800a3d20574d891000c7d43ee0b1220008bf845d9524400b17908bb2a48800237e0d76549100246e41aeca9220008f7815d9424400717d0fb2284880162fa13764c9100045ec26ec99220008fb805d932440091e90eb2a6288086ad211654c51010f4a3228698a20048f48758931440071e90eb2a4288076ad211654851000c7a432e690a20038f48758d214403bd48c8a124288016aea13655011002c7c43acaa022005cb87650d404400b970eca12808804f3c1db7150110016783b262a022000f91434c540440059e0ec90a8088003e85092150110
  | 1 => 0xd03bb264a00023d607764c94000c5e432e8992801693c855d13250001968c2ba264a00066e201744c94002c7d436e09928000cf061dc1325009956d0daa6c2a028b2d9db54d85400071bb2ea9b0a804cbb280d5361500995690ca1ec2a00e32d9d943d85402655a43285b0a8030cb67650b615009956b09baec2a0132bca0075d85403ad78c00ebb0a8075ab6841cf615009956b0839ec2a00023da1c53d85400047ac38a7b0a8075ab68414f615000156b0829ec2a0002b9a0853d854000572c10a7b0a804caf28014f61500015e30029ec2a01d6ada1072d85402655ac20e5b0a80008f68714b61500011eb0e296c2a01d6ada1052d85400055ac20a5b0a8000ad68314b61500015ab06296c2a0132bca0052d854000578c00a5b0a80008f6870cb61500011eb0e196c2a00029da1432d85400053ac2865b0a8075ab6840cb615000156b08196c2a0003b14c832d85402657940065b0a8000af1800cb61500011eb0f328c2a03478d152651854064d78c04ca30a80008f78759461501a156f08b28c2a02aead210651854039579400ca30a8072ab686d506150001c6ecbaa0c2a00038d1975418540395d9406a830a80008f58798c615019f56b09318c2a00023de1d63185404b55b420c630a8072ab48650c6150001d2ec6a18c2a00023d61e62185406755ac24c430a80008f787588615011956d08310c2a01caad219421854000753b128430a80058bc841d9515000187ea83b2a2a00033c84076545400143e43acaa8a80018be86dd15150145968c3ba2a2a00066ea0374545400347b43ec2a8a8075cb474d85515012d968c3b9a82a02332d18772505400155b436c2a0a804ccb476d85415000b3690ea8a82a0002ad21951505400165a3b2a2a0a8000cb7411d931500031790cba262a00e32d185744c5401c74a30a8698a80048f687d8531500051e9023b242a00032dd04764854000c5e432e890a8030cb4615d12150061d48c2a1242a000e3da1f614854066d9d42ee8a828000eb061dd1505003567108a9aa0a020f9c18553541400b59c42a86a828000f195350d5050199d60c2a1aa0a006ace21152541404073830aa4a828016b38855095050001e52a4a12a0a032fac18542541400be7830ee2a828000db341dc550500e55e50db0aa0a01d73c1db6154140657982a6c2a828073cf0761855050001ce6ca30aa0a00039c194615414064f982a0c2a828000a7886545505003567108a8aa0a005f9c185515414000d5c43282a828016b3885505505002fd60c2a0aa0a0003cc545415414001c7743ee4b2a6000ccf731c9654c0051ed0fb8ac8980023be09765513001c76412ecaa260008f7815d9544c0051e902bb2a8980023de0574d89300147a40ae9b12600387c87595524c0074d904b2aa49800e2f21d64509301855a40ac8a126005
  | 2 => 0xf7058d210045fc22eca9a42058bc845d953484011f700bb2a6908063e2017654d2101477436e4a9a420087f855d9434840d0f90abb286908023ee017650d2100c7c402eca1a42048be87d9143484071ed0db8a86908163b21d6550921185d240aa8a124205cac7650d424846174902a1a84908c2e9a13715092155cdb43ee8a8a42aecb476dd15148559968ec3a2a2908772d1d364545210071baa6c8a8a42068f48759151484052e90eaa2a2908032d1d363545210347a43ac6a8a4200cb47458d514844f5e100b1aa290803691d372545210eed23a284a8a4200f255450951484071e90cbaa62908766d211754c5210247a43aca98a4221ab48459531484053a90ea1a6290887a5191434c521015724328498a421dda4745093148401f0a86a12629080378c83704c5210045fc22ebb0242058bc845d76048401da263986c0908028f61641d91500047bc0ae9b1aa0028f4815d3635400117f08b8ec6a80162f21171d8d500252f436c6a9aa000d6a20dc953540032f501b8aa6a80061fa1b7550d5000cbd406eaa1aa00695c8754d43540018b8eca9a86a80023de0574d89500147a40ae9b12a004c5c7354f6254001c9aa7996c4a80022fe1171d895002c5e422e3b12a000d5a30dcd52540074d905b1aa4a8003938cb635495001d37436c4a92a00197a80dc552540030fd0dbaa84a80065ea037550950034b643aa4a12a000c6c765494254001998653b264a80162fa10764c9500045ec20ec992a000ccc321d932540051ed023b264a80023d604764c95000c3e432ea992a000c5c7654d32540018d8eca9264a806a4fa1f74545505161e3b6e8a8aa000d3870dd151541ade6021ba2a2a82af0f1d874545500069c380e8a8aa0d5f30101d15154035878e9b22a2a80038d907645455000cbc406e6a8aa00197880dc95154001a68e9b0aa2a80065ea1f70545500069c3a6e0a8aa027b7281dc151540030fd0dbaa82a801a5d21d515055013eb8382a2a0aa0068fa86dc141540030f90cbaa62a806a4f211754c55000cbc402ea98aa0d4b3484545315404fae0e0a8a62a801a3ea1b704c55000c3e432ea90aa01a93c845d521540032f100baa42a834ecd211514855013eb8382a290aa0068fa86dc121541a587eebba2caa000a3da1f71595400065bba0e2b2a80048bc845c763500051ed03bb2a6a00023d6077654d4000c5f436e8a9a8000cb461dd153500091790eb2a86a00e2ad2056550d4002cce43aa6a1a80c2e946154d4350001968c3b9286a00e32d1877150d40006d9086e2a1a80038bc845c762500991e90db8ac4a000a3da0776549400047ac0eeca9280018be86dd15250001968c3ba2a4a000e2f21d65509401855a40acaa128000cb461dcd425000b3590ea9284a02dfa918552509401865a30ee2a128000db210dc542500051e
  | 3 => 0x8b2264aec3c75905644c8051ed033b2a8990023d60676551320043fc2aecaa264068bc87591544c80d1b90eb22a69900e73a1f7254d3201ce6416e0a9a64068ec87591524c80939d0fb9aa49900ed321d5354932026a643aa6a92640394c8754d524c80769d0ca9aa49900ed3219535493203726432a6a926406e4f7654d524c809a9ceca9aa499013531d95354932037263b2a6a926400e4f6454d524c801c9ac8a9aa499002d3e015354932024e641ee0a926400d4d53dc1524c801b1864ba6c2990162fe1d74d8532006e4196e0b0a640087f855d3604c80d0f90aba6c0990028f61640d915155e5b3b421b22a2a2ab6811cf645455d56b0239ec8a8a8aada0472d91515755ac08e5b22a2008be870cb645440117b0e196c8a8aba8fa1432d91510051ec2865b22a2a2ab6810cb645440156b02196c8a8802aea0032d91510055cc0065b22a2aeab581dc36454401976e1386c8a8aba8fa1470d91515151ec28e1b22a2008be870c3645440117b0e186c8a8aba8fa1430d91510051ec2861b22a200aae820c3645440155b04186c8a8a8aada0430d91510055ac0861b22a2008be87083645440117b0e106c8a8aba8fa1420d91510051ec2841b22a200a9e83083645440153b06106c8a8a8aada0420d91510055ac0841b22a2dbab58198c64545b556b03310c8a8b568f61660191516cf58084c0322a200eb0608406454545878edb22a8a880a5da07705515155e5a388c9b1aa2008be87d91635440117d0e322c6a88032d9047650d510245f43ec8a1aa205a3c865514354557968e2326c4a88022fa1f64589510045f438c8b12a200cb6411d9425440717d0fb2284a88168f219545095102c5f426ec992a2008bd84dd932544050fd0dbaa64a88030f193754c95100746196c8992a2aecb571d9360544f9878ea326c0a8aaf2d9c464d81515665ab88c9b02a20187c855d360545451790dba2c0a88022fa1f64581510045f438c8b02a2d8cb77119160544eb1ef02b86caa0b5f0fdd774595410045ec26ec992822acb476dd1515054517f08baec0a08062f21175d814102c5f43ee8b2a6200c3d75d53644c40156b03aa6c8988022fe1176551310247b436e2aa262058dc87595434c47172902aa286988e2e5a137150d310146f436e6a9262038be87d91424c40b5390ca1a84988e3651c543509310247b436e2a1262ab9b687dd1514c55d968edba2a298ab32d1d8745453110e5a3a6c8a8a6200e3754d91514c40d1e90eb22a29880a5d21d5454531006ca3a6e6a8a6221d947450d514c401e2aa8a1aa2988032d1d362545310045fc22ebb0262058bc845d7604c4051e902b86ca908162fa1f74595210061ebaea9b224200ab581d53644840117f08bb2a89080e3da1b71551210055b426e2b1a42008f687d0563484999e0e1a0ac6908063ea1
  | 4 => 0xea34e4604f0961fa0000010746a8e0b317b1f8790378a000046442000000000b822800026c0010f412000000003885b4520002c80009800015e664000030900001f800000784000fe382000000c8350840000690000007705b00040c00000000000000511fe00000000000014002160f0000000000000b000232000738000003301592290a1b42e81d857130798db8a100082c0005f0000003e800000608dda3400000000080282000ee81630e084778000002689880018c3d8fa8731f2794928002420e0490c00e0830fe902276604960003840002c000000000000000e43082c83205c3c1131ba09c18c0000014a6d00017c38e000af136000734cd0e21708dc659f11a2000730070004204c8001140002a8340fe000ee0f10cc56800220000000c31d52080000000f3e6451218142be4140e8002ea4b467a1b16e2c0001f900047d2090e3f400000000000000001f038631c920000000000000012800000000072000ff82a00062413000000330000002800004423d15400043000328208f900029c20c1e9333b40006b8000000011580045a00000000000000bc8002aa180140290008fceca140000000018f0000000000043c828d800000045c0012827e000002063a40002696a1c28905f13c0008b0eb1830003341801f0b86e0d200041c370281003b0194808c90007d8a60003386d8b29110ea0007691002e6b40007a1c07400022f16613cfd80048c570910eb01a094000003527a0001e7252820a39aa0745746f88f3420001880046280c000d9268000000000000100200000004020080501c00014000040004c000000200006000000040200c0400016018010141a01c00008010080800800004000240102400064020100200c0100000000070000700000000030080500c0600c00018060040b0000f0100000800000040080000c040000002000000000000000c01008030000201c09004030400001c010000d0000200001000090100400c010080000c04000010800000c0202c030000000401090050200000c0000c00008020040200401004020080b0080f01806000000000000400020080040800000018010140200819008000040104000000010000100400014050480600401040005745fc22e3b1aa8ae8bf845c7625500117f08b8ec4a98162f21171d89530051ec24a5b2a86008f7815c36550c051e902b86caa1b770fdd7745954302ccf426e2a9a86008bf845c7635480b17908b8ec6a90028f61253d95420047bc0ae1b2a84028f4815c365509b987eebba2caa10034b94b7550d4201c5e432eaa1a8400e1e53d9543508091790eb2a86a1003c354d435494202cd7426e2a928400c3d74953654c8011f700b8eca990063e20171d9532006e2192e3b2264028f7875c7644c801a9865baac89901a1fa1f75591320055b40ee
  | 5 => 0x6f86a00000000000000000000c6000000000000810007b80017a31c00036000466000000000003740019d000000428002ac000000d84301104600015a38c6b2222740000019b3c0834051b34843051b00028422ca515846064c001ac27248cbf80000000000000000348001913ae6c40012f476000000003f00780a90c04e188b00f50f6520df8001d235400000000000000000000000022700058cb91270820ccd1a072d26409aa193f8000e58f70000602909f0002340000016a5449c03622c3e86211e254910000000940010296132c0000010622a000fa23c0467443c8a60005dd0a997000000100ae308000f480005e730d719542e5f43b91c44a5a0e300000004d0e1a2000000a916c0d4648298002c444cd0126000868da800392000990002b2000001121645190f8b61e8678000060007000000048e000000000001c4001880fc4ac000000000011f1373da000b78e4034000cf8a708083c088000000000001b19c000628002160006f00025c6e4ef80000011400000000424001af12659cff00000046c4888e0008a42e86b3ee7b0a48bd2fc1d044978000728aa000000000249e317834000067000088760004265acab800000000de8ab0c8000211710160003713e0002c4020a212a0202195b4243280000045c0007294b0000000003c44621c001442a01d800000000810698001f028c0000006e0010ea3a37800000173000000a78002dc0006d8003563c8c50bb0480aca2a2127a6142320213a000369cf0005d816800158600ea0352e8000000000000000c920018474238a80963a0f5a013900005c8000000000000012000000000316000000002a61f0000001860002a000168000000003de000000681ce7a83080000476d150004220000e00000000000000000000e99c50000400000934a468d900017e000090a90bc0000709728643400000000778000fb0b48e4f10004003cc0014d0029000000007c0004e04c31a698
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1526007803250000101cea04a700020038d003ca930000100a146a0d910048322161520a12a4b2c1a0cbad4e00c10567c6032020db0cc0520c300020100551654325c7644c8015c1900c971d913200453a6032dd5644c801549900cb755913200543654325d3614c801589900c974d853200472a6032dc1614c801549950cb70585320058365432d913254401689900cb644c9511c54525d5450d514c4018b0801d163545211854925d5450951484615849750d424c5211c6a121943509314840144d950ca764c95000532640329d932540010cd980c8764c95000513654321d932540014c9900c8764c9506ae4ca0474dc1515400183485185744c94000691615320cb6150001ac13260032d85400070cd52101d951501570b49721951505400d4c62615350d50501c5e106154d43541400d4ca2615250950501c3e206154942541407058c2506518550500353309854541541400058c25951505505004fa3086545415414001c9326165549324c00744c97595524c93013e94219514c5504c1bf710945453154130024932616554d324800944c97595534c92013e982195148550481bd72094545215412001d32259754c930480094c897595324c1201c7241d9434c54044061ca0765092150110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x140000000020b1a92007458d514840101ad490a30ae899280e388c2a0965454154140
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
  | 23 => 0xa4a
  | 24 => 0xa4b
  | 25 => 0xa4c
  | 26 => 0xa4d
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
  | 67 => 0xa0956
  | 68 => 0x1549
  | 69 => 0x1409
  | 70 => 0x150a
  | 71 => 0x128a
  | 72 => 0x16c9
  | 73 => 0x1449
  | 74 => 0x168a
  | 75 => 0x12ca
  | 76 => 0x1849
  | 77 => 0x1489
  | 78 => 0x180a
  | 79 => 0x130a
  | 80 => 0x19c9
  | 81 => 0x14c9
  | 82 => 0x198a
  | 83 => 0x134a
  | 84 => 0xa4995
  | 85 => 0xb0995
  | 86 => 0x138b
  | 87 => 0x124b
  | 88 => 0x1709
  | 89 => 0x15c9
  | 90 => 0x168b
  | 91 => 0x12cb
  | 92 => 0x1889
  | 93 => 0x1609
  | 94 => 0x180b
  | 95 => 0x130b
  | 96 => 0x1a09
  | 97 => 0x1649
  | 98 => 0x198b
  | 99 => 0x134b
  | 100 => 0xa49d5
  | 101 => 0xb49d5
  | 102 => 0x138c
  | 103 => 0x124c
  | 104 => 0x150c
  | 105 => 0x128c
  | 106 => 0x18c9
  | 107 => 0x1789
  | 108 => 0x180c
  | 109 => 0x130c
  | 110 => 0x1a49
  | 111 => 0x17c9
  | 112 => 0x198c
  | 113 => 0x134c
  | 114 => 0x289
  | 115 => 0x4d
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
  | 126 => 0x138e
  | 127 => 0x124e
  | 128 => 0xd4a52
  | 129 => 0x150e
  | 130 => 0x128e
  | 131 => 0xeca52
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
  | 148 => 0x154c
  | 149 => 0x140c
  | 150 => 0x18ca
  | 151 => 0x178a
  | 152 => 0x184c
  | 153 => 0x148c
  | 154 => 0x1a4a
  | 155 => 0x17ca
  | 156 => 0x19cc
  | 157 => 0x14cc
  | 158 => 0x154d
  | 159 => 0x140d
  | 160 => 0x16cd
  | 161 => 0x144d
  | 162 => 0x1a8a
  | 163 => 0x194a
  | 164 => 0x19cd
  | 165 => 0x14cd
  | 166 => 0x154e
  | 167 => 0x140e
  | 168 => 0x16ce
  | 169 => 0x144e
  | 170 => 0x104bd1
  | 171 => 0x74a
  | 172 => 0x28e
  | 173 => 0x184e
  | 174 => 0x148e
  | 175 => 0x18cb
  | 176 => 0x178b
  | 177 => 0x188c
  | 178 => 0x160c
  | 179 => 0x1a4b
  | 180 => 0x17cb
  | 181 => 0x1a0c
  | 182 => 0x164c
  | 183 => 0xd4d12
  | 184 => 0x170d
  | 185 => 0x15cd
  | 186 => 0x1a8b
  | 187 => 0x194b
  | 188 => 0x1a0d
  | 189 => 0x164d
  | 190 => 0x170e
  | 191 => 0x15ce
  | 192 => 0x188e
  | 193 => 0x160e
  | 194 => 0xece92
  | 195 => 0x1a8c
  | 196 => 0x194c
  | 197 => 0x1a4d
  | 198 => 0x17cd
  | 199 => 0x18ce
  | 200 => 0x178e
  | 201 => 0x4a55
  | 202 => 0x124a55
  | 203 => 0xd0a52
  | 204 => 0xe8a52
  | 205 => 0x749
  | 206 => 0x28d11
  | 207 => 0x28e91
  | 208 => 0x29a91
  | 209 => 0x198055
  | 210 => 0x1a9951
  | 211 => 0xb0a55
  | 212 => 0xb4a55
  | 213 => 0x74a52
  | 214 => 0x1a8a52
  | 215 => 0x1a9952
  | 216 => 0x29256
  | 217 => 0x134752
  | 218 => 0x28b16
  | 219 => 0x28b56
  | 220 => 0x1a9953
  | 221 => 0x1a9954
  | 222 => 0xb0a499d
  | 223 => 0xb4a49dd
  | 224 => 0x28751
  | 225 => 0xd4d0a5a
  | 226 => 0xece8a5a
  | 227 => 0xa4752
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1431
  | 6 => 3403
  | 5 => 584
  | 4 => 46
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
  | 6 => packedAt gbK6 (178086+((h/1134+packedAt gbK6 (163344+(h % 1134)*13) 13) % 4941)*13) 13
  | 5 => packedAt gbK5 (36396+((h/194+packedAt gbK5 (34456+(h % 194)*10) 10) % 932)*11) 11
  | 4 => packedAt gbK4 (3310+((h/15+packedAt gbK4 (3220+(h % 15)*6) 6) % 56)*7) 7
  | 3 => packedAt gbK3 (247+((h/1+packedAt gbK3 (243+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x8e3838e0e1c71f8fc06383fffff1842619c0ff
  | 1 => 0xfc03f00fe07e3f1fffc038383f218c6667c93
  | 2 => 0xf0003fff1ff803fe007ffc03fc0400f9878f1c
  | 3 => 0xffffc0001ffffc00007ffffc00081f01f80fe0
  | 4 => 0x1fffffffff800000000fe001fff000
  | 5 => 0xffffffffe000000000000000000ffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x840a102820420502440080d0d181842208c025
  | 1 => 0xa44a91246012090a36419090a6218c4221c92
  | 2 => 0x10000a460a8802a40929280228240048870518
  | 3 => 0x22918000151548001252522800480901700ac0
  | 4 => 0x1000419e693491c006030308ca001dde000
  | 5 => 0xcd2634988000000020000040430356b6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffff8feecfaa8fffffff8feecfaa8fffffff8feecfaa8fffffff8feecfaa8fffffff8feecfaa8fffffff8feecfaa8fffffff8feecfaa8fffffff8feecfaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_27835
namespace PEqualNP.Outside.L_meta_27835
open PEqualNP.Outside.L_meta_27835.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 60 := (concat bs3_4_0 bs3_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 40 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bgb_4_32 : Interval gbAtlas 4 32 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 46 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_576 : Interval gbAtlas 5 576 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 584 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)))))
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
theorem bgb_6_3392 : Interval gbAtlas 6 3392 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3403 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)))))) (concat (concat (concat (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528))))) (concat (concat (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)))) (concat (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 0 zero,inputs.getD 5 zero,inputs.getD 1 zero]
def fullWord : Sig := 0xfffffffffeeefeeefffffffcfeecfeecfffffffffeeefeeefffffff8feecfaa8fffffffffeeefeeefffffffcfeecfeecfffffffffeeefeeefffffff8feecfaa8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,2,130)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_27835.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[8,3]⟩,⟨.or,[9,5]⟩,⟨.and,[10,7]⟩,⟨.and,[2,6]⟩,⟨.or,[0,1]⟩,⟨.or,[13,4]⟩,⟨.or,[5,6]⟩,⟨.and,[14,15]⟩,⟨.and,[0,4]⟩,⟨.or,[11,12]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_27835

open PEqualNP.Outside.L_meta_27835 in
theorem PEqualNP.Outside.L_meta_27835 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
