import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_28152.Model
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


end PEqualNP.Outside.L_meta_28152.Model

namespace PEqualNP.Outside.L_meta_28152
open PEqualNP.Outside.L_meta_28152.Model
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

end PEqualNP.Outside.L_meta_28152

namespace PEqualNP.Outside.L_meta_28152
open PEqualNP.Outside.L_meta_28152.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xa42871c9d72d004ddb564000191400323185db0d56010096e08792344161c002dc84420581d00611384aa99a45e013002258f8310d0a0050558800000dba3c0e202000a10701040800b12003820600000b7290876d5210eeca221dd54443bd28087795010ef4a1a15e54342af29c855d5390aeea2a15d14542bb28e657551cca7ca9194f55232bda826578504cabca620d754c41b7290836d52106f4a020de54041b7296636d52cc6f4a118de542319faa2633c544c67ca810cf55021af298435d53086f4a010de54021b7296816d52d02eca3205d54640afa9a815c535027ca8184f55030b7290616d520c2eca2185d544309f2a0413d54082bca6105754c20bb288417551082bca7885754f109f2a4213d54842dea4885b14910
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
  | 1 => 0x3e3c1f8f1fffe38e38e0e3f071fff83e23c3f3
  | 2 => 0xc03fe3ffe0e3fc703f00fc7ffe383fc044fd9c
  | 3 => 0x3ffc0fff03ffffc000ff807fc03fff870e1f
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x844648114a81040428286095104c889421c0b1
  | 2 => 0x8c88c902460440901902242332119184405594
  | 3 => 0x31111224904a806a4014890844822629860a0a
  | 4 => 0x180191480440c9329246000269230308c80f40
  | 5 => 0x202202009893124d2498d24c0004043137a000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffcf0fcccfc00fffffcf0fcccfc00fffffcf0fcccfc00fffffcf0fcccfc00fffffcf0fcccfc00fffffcf0fcccfc00fffffcf0fcccfc00fffffcf0fcccfc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_28152
namespace PEqualNP.Outside.L_meta_28152
open PEqualNP.Outside.L_meta_28152.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x34007922a00023000098038000000000b0a4c1800054411243a9c0003e084180001580000000100110800064d801c0c00050000000001280160060500a4000001c000005c0003c00000004400d0050020000000012000010002042000608000000c000ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x460d55094d505432392f172e4e0004000f40421e594c00331d035a00000010000030004f2653152d0b4a344b16183b003635370705520a4741253f2a01001200000031290e380622434400113a1a49002114272b0c195828513e0045481c24131f2c23003d081b0002563c57200005264001d0200082082439a00542030000000002468d0600000075d51d0ebca721db94843b6a9087765110eeaa221de94043bca80875e5410f3ca821f394843e6a9087d65110ebaa221f554443aaa8887da5010fb2a021e710f42bd286857950d0abca7215754e42afa9a855c5350b3886a14f952329eaa4655e53906baa720e710e41afa9a835c53506bca620d754c41ce218836e52106daa420de94041bca80835e54cc6b8a998d754e319faa2633c544c73ea898d795131ae2a2639c544c638a898f5d4531eb20a63d5414c6bca618d794e21aea9c437b50486f0a090cf950219eaa0435e53086baa610de94021bca80439c43d02dca5a05b54b40af29c815d53902bea6a05714d40ce21a813e548c27aa9184f950209eaa0415e53082baa6105d94420baa8841e920082bca7885754f10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2201269001ebaa580086918030500a0c39c00028020402c0268020064c300127465254443d15495110f515194043d25495010f515154043a558443d0b184354342a55844350a956110e41c310d5210718435404187992544c70e6215131c3588544c7156115131c6980544c7196015131c5152414c65465505318719153886956110f40c310d52d02956110d40d8545200821c6454f10
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x8004000c101445c44354342c0ac4b08a898e0962580544c708b0ac02a263415c44354b40
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s1K5 (802+((h/14+packedAt s1K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s1K4 (2667+((h/30+packedAt s1K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s1K3 (998+((h/8+packedAt s1K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x78f0fe3c7ffc7e3c71c0c7e1c7fc3fe31c3cf
  | 2 => 0xf80ff1fff87ff8fc07e00f8fff8ffc1e427cf3
  | 3 => 0xffe03ff8fff1ff8000ff01ff1ffe1838f3c
  | 4 => 0xfff00003fff0001ffffff0001ffe0001fc0fc0
  | 5 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x5011844452448801450524128412415430c145
  | 2 => 0x1222080810101040220408448848808401492
  | 3 => 0xa6444909242a003a8802892111213281830a28
  | 4 => 0x33006cd21123924cd348e0005e4818ccd40fc0
  | 5 => 0xc4088100264c249324930e49800023112be000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffaf0faa0faa0fffffaf0faa0faa0fffffaf0faa0faa0fffffaf0faa0faa0fffffaf0faa0faa0fffffaf0faa0faa0fffffaf0faa0faa0fffffaf0faa0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_28152
namespace PEqualNP.Outside.L_meta_28152
open PEqualNP.Outside.L_meta_28152.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2018f0056000153071381002cb02320000052006054624b8f1a849130e000000000026140018000000000000e800044fa210000000094004540001a0050da050907008206001800030202000c184ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x580e0056003a441d00010b36003e131c4700092c1145412e0c0d22571e1a494c2a0023543702081251433d354d17001b293128331021003f204b345052030f2f262b0607194e593b0053000a00165a0042152d463c4f040000001f0000273855304a052514183932402448000001060d1030a20580001030d0000200000003e003848508c488d073e5390e7aa321db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010f72a021d794e42aea9c859c43ccaf4a1995e543329f2a4653d548ca7ea8994f15132ce21a653e53d067aa920d7d4d41ae29a839f5350678a6a0e714d418e29a83b7515067ca820cfd53319e2a6633e548c67aa918e710e31daa0c633f544c678a898ed505319f2a0633d540c7388618db94831b6a90637a500c6f2a018cf952219eaa4437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53902baa7206710f30b7296616d52cc27ca9184f552309faa2613c544c33886984f950209eaa0415e53082baa6105d94420baa8841e9200827ca9884f55310b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x61a380792b04aa6c0000082851c5822a400c89002e00818a3180e6a13265254443c95495110f315194043ca5495010f315154043a558443ccb184354332a5584434cb0e6214d41c358853507156114d41c698053507196014d41a5584438c69463506318d195414c61d6510c31c310d520c71843540318718d54886956110f30c310d52cc2956110d30d8545200821c6355310
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x1000048c01445c44354332c0ac4b08a6a0e09625805350708b0ac029a83415c44354b30
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s2K5 (802+((h/14+packedAt s2K5 (704+(h % 14)*7) 7) % 75)*7) 7
  | 4 => packedAt s2K4 (2667+((h/30+packedAt s2K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s2K3 (990+((h/8+packedAt s2K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s2K2 (249+((h/1+packedAt s2K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x78f1ffc3f8fc7e3c71c0e3fc7e1c3fe30f70f
  | 1 => 0xf80fe1ffc7fff8fc07e00fc7f8fffc1e4339f3
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x50118484921288014304a2094124414c305305
  | 1 => 0x2221009040401080421044208509010412052
  | 3 => 0xa5444912212900368802489092092a81828c28
  | 4 => 0x31004ca081019244d1486000e48c08c4940f80
  | 5 => 0xc6089103364e249b26938f24001033196bf000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_28152
namespace PEqualNP.Outside.L_meta_28152
open PEqualNP.Outside.L_meta_28152.Model
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
end PEqualNP.Outside.L_meta_28152
namespace PEqualNP.Outside.L_meta_28152
open PEqualNP.Outside.L_meta_28152.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2c060122620a4617008c02800252931a187af400001e02b40193800d8244acd182c4472a009d08a2a2c0080e7c21d280092e0a0001030883522c0281880046ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x7426834c2100090092232293cda603e92d0844409dcae59140585c53350f4c4002d138321b031c014724387c2878320bcd26724170586823000000941000a03a001f8e21e0d000ca002f89438181c9080083000986602001fcbc3500158005d2d9980e03121ec00003b03c7e2b3a8c4d8581f1b800000010ca8290014800800e8006c110288800123c8e02a7a00010007c3189c403b358f04285150008e2d059040000398002e0c19000264c070dc104a1a0006055289bd0c00050000010000000807040412001c010525040200040e020000031e11090601020014021a000901192f12001e9f296873d50d0e7aa921e7d4d439e292873f5050e7ca821dd94642baa8c853d5390a7ca5216d94642daa8c853d5090abca6215754c42bb28885755110af4a0215e54042cf298853d5310b3aa6214754c429f29085ae5210b6ca2216d54442dd280853d5010b72a0214e540429f2a6653d54ccb3a87994fd52329e2a46576518caeaa3194fd51329e2a2659d434ca7ca8194f55032bb2886575510caf4a0195e54032b7294836d529067ca998cf553319f2a0633d540c6dca418db54831bd2806379500c7588590cf952219eaa443b6548876aa910edd0e21daa1c4375528876c8510ed10a219faa2433c54487588490edd5121da2a243b7434876a8690f9d4921f3a1243b642487688490f910921d221243e632487ca6490dd944219ea9e813e52d036c43a06d487409eaa4813f5350278a4a06d88540da90a81bb505027ca8204f953309eaa6613e548c27aa9184f951309eaa26177514c2e8a2984f950309eaa0616e520c2daa4185d94430baa8861d9300c27ea9904f15320bb28e417551c83ca43904f952209eaa441b9408827ea8904f15120f290a41b9404827ca8104f55020af298415d53082eca2105d544209f2a4213d548427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x7a40000031004cc1400b50191a2830000000292030d2a5c0001b5e00880000000010b0f800a1c000420142212380000000902000400000c138000aca9600000000078b80062d2a6080119d38000428300040800010002080c0048e5805250ea56194842c554e5110b155354442c654e5010b1a5354042c654d5010b325154042cc5455010a39601523287195434ca8d6310b21aa58042c86956310a21ac580428868d6310921aa58042486a46250d21a999352486366590921a998a42486366510921a558c42486b16010921b158c42486e16010921a999442487266510921e198c42486a56310921e158c42486856310921e898042486a56010921e858042486a16010921a919232486a4644c921e150d324861d6314940c9149215022c625513099588514c349524c030d4545300c21d6315320c915121c832454485208e19540483a12150120
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x608083008a7400005285c06250d21d02c73008490e82635804248740b1ac021243285c0648c921908eca1a6490d05731492150282b98a890e41881952150120
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
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 88)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf1f8f1fc78f8fff18e3f1c1e38e1fff19307f
  | 1 => 0xfe7f01ff80ff1c7e0fc7e01fc0fe38f663993
  | 2 => 0xf007ffe3fff001f8ff007ffe3ff003f087ce1c
  | 3 => 0xfff80003fffffe00ffff80003ffffc00f80fe0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4180a020421210800820a048408208c4091025
  | 1 => 0xa25106489125030860445214a424c12a262892
  | 2 => 0x20420209010124012100148429204222024a18
  | 3 => 0x4004892240800129289002012491000d00540
  | 5 => 0xc8946c10364e49a4dcf269390041984cfdb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfef8fef8fea8fea8fef8fef8fea8fea8fef8fef8fea8fea8fef8fef8fea8fea8fef8fef8fea8fea8fef8fef8fea8fea8fef8fef8fea8fea8fef8fef8fea8fea8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_28152
namespace PEqualNP.Outside.L_meta_28152
open PEqualNP.Outside.L_meta_28152.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x17000000200520008000000135a550121a5001f06440285801198041459b125d78c0c7511a4a21096541c79c484050e566530000780004e0031c100229200514020e0c9ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3421190541207980ae002f000006f0012464172a9cc00000016d02013c12c004f0008cda0000168004d199b87251181d800682f8147a00291f048463c8e0784e1886c30661b910e250310402c142e0389022428a4d22b03a00144a00208001a3f00cca1c41930e8000f0b0267a001ac0002421f4002f200103226060000025339b0a8200f90cee723d9040c1135164123b1d07400004300000281f800ac453a800ba63238b400362c054e00d299850e35139fc163e040b842000e0805000000030100010a020008142b0307130f07000000080101080d1e38030603000100000004000100009f28e873d50d0e7aa921e7d4d439e28a873f5050e7ca821dd94642baa8c853e54cca7aa9994f950329eaa06576510caeaa2195e94032bca80656e52906daa520cf54e41d729483ad529067ca320cf54241af298835d53106dca420db54841bd2808379501073ca620cf54c41cea98831d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331cea1e633f548c678a918db94a31b6a94633f544c678a898e750d319f2a0633d540c6dca418db54831bd2806379500c67ca990cf55321d72a643ad54c875e8790eb50f21d720e43ac41c86daa510ed106219faa2433c54487688290ebd5121d62a243af434875a8690f9d4521f3a0a43ae41487588290f910521d220a43e631487ca6290db948219ea9e813e51d035e43a06b487409eaa4813f5350278a2a06bc8540d690a81bb505027ca8204f953309eaa6613e548c27aa9184f951309eaa2616f524c2d8a4984f950309eaa0616e520c2daa4185d94430baa8861d9300c27ca9104f552209f2a0413d54082bca6105754c20bb2884175510827ea9884f15310b7296216d52c43ca43884f952109eaa421b9408427ea8884f15110f290a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4650c9b0000d035e7c91330008311c742064e00000523400f4c5400056000a000c001c0008022009488a2c0048c5aa92005084f2c00b8b851600000001c0001000000070400180042800002342808e5805150f0d5394841c354d52106a56294441c654e501071a5354041c654d501072a5254041ca5495010639601523187195434c68d6310721aa58041c86956310621ac58041886956310521ac58041486a46150d21a9993514862e6590521a9986414862e6510521a358c41486a96010521b158c41486e16010521a999441487266510521e198c41486a56310521e158c41486856310521e898041486a56010521e858041486a16010521a919231486a4644c521e150d314861d6314540c91452150234615513099584524c349524c030d4545300c21d6315310c915121c432454485108e19540443a12150110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x60000c11200029c00010403285c06150d21d02c73008290e82635804148740b1ac020a43285c0648c521908eca1a6290d05731452150282b98a890e21881952150110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s5K5 (864+((h/16+packedAt s5K5 (768+(h % 16)*6) 6) % 63)*7) 7
  | 4 => packedAt s5K4 (4032+((h/45+packedAt s5K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s5K3 (2012+((h/16+packedAt s5K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e1f8fe3c7c78fff1c63f1f823871fff19c07f
  | 1 => 0x1fe7f1fff807f1c7e07c7e3ffc07e387267993
  | 2 => 0xe007fe03fff801f8ff807fc03ff803f8c78e1c
  | 3 => 0xfff80003fffffe00ffff80003ffffc00f80fe0
  | 4 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8280a004410a10800420a049008108a408c025
  | 1 => 0x444104408091020820041210a4124112021892
  | 2 => 0x415204c91281250168805482a9304252470a18
  | 3 => 0x8004912240400129149000412449000b00540
  | 4 => 0x91946980372649a4de72692700609864fde000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8feecfea8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_28152
namespace PEqualNP.Outside.L_meta_28152
open PEqualNP.Outside.L_meta_28152.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826001f78c13000ff86098007dc304c003fc1826001f60c13000ffe4098007fe204c003fd1026001ff0813000ffe2098007fe104c003fd0826001ff04130007feca90002ff654801dff32a4006bf99520007faca90002fd654801dfe32a4006bf19520007fec890002ff644801bff3224005bf99120007fac890002fd644801bfe3224005bf19120077fea890037fe5448001feaa2400dff15120007fec690002ff6348019ff31a4004bf98d20007fac690002fd6348019fe31a4004bf18d20077fea690033fe5348001fea9a400cff14d2006ffe8690033fe4348001fea1a400cff10d2000dfec49000fff5248007ff2924003ff5492001ff8a49000fff4248007ff2124003ff5092001ff8849000fff3248007ff1924003fb8c92001ffa6490003ed3248007fe1924000ffd8520005fec29002ffe61480057f30a4000ff5852005ff8c29000afc614801dffa8a400bff94520007faa29002ffc514801bffa0a400bff90520007fa829002ffc4148019ff98a400bff8c520007fa629002ffc3148007ff90a4003fbc852001ffc429000ffd2148001f690a4003ff0852000dfec090007ff5048003ff2824001fe9412000ffaa090003f95048003fe2824001ffd012000ffc8090007fd4048003fe2024001ffcc12000ffc6090007fa3048003fe9824000fe4c12000ff86090007ff2048007fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffe2090007fe1048003fe0824000ffd9510005feca8802bfe654400d7f32a2000ff59510005faca8802bfc654400d7e32a2000ffd9110005fec888027fe644400b7f3222000ff59110005fac888027fc644400b7e322200affd511004ffca888003fd5444013fe2a22000ffd8d10005fec688023fe63440097f31a2000ff58d10005fac688023fc63440097e31a200affd4d10047fca688003fd5344011fe29a2009ffd0d10047fc8688003fd4344011fe21a2000ffd8910005fec48801ffe62440077f3122000ff58910005fac48801ffc62440077e312200affd491003ffca488003fd524400ffe2922009ffd091003ffc8488003fd424400ffe2122008ffcc91003ffc6488003fd324400ffe1922001bfd8510017fea28800bfe5144005fea8a2002ff14510017fe828800bfe4144005fea0a2002ff10510017fe628800bfe3144005fb18a2002ff4c510007ea628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001fe9011000ffa8088003f94044003fe2022001ffcc11000ffc6088007fa3044003fe9822000fe4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xffe4154001fea0aa017ff105500cffe62a805ffe3154001fe98aa017ff0c5500c7fe42a805ffe2154001fe90aa017ff0855000dfec0a8007ff505400dfda82a001ff9415000efca0a8007fc5054003be282a001fe1415000ffe80a8007fe4054003fd202a001ff1015000ffe60a8007fe3054003fe182a001ffc815000ffc40a8007fa2054003fe102a001ffc415000ffc20a8007fc1054001ffb2a8000bfd95400b7fccaa001afe6550001feb2a8000bf595400b7f8caa001afc65500037fb228005ffd51400b77ea8a0017fe545000bfeaa28005ff1514002f78a8a0003ff63500017fb1a8015ff98d40025fcc6a0003fd635002bfe31a8004bf18d400b7fea6a0057fe5350001fea9a8015ff14d4002ffe86a0017bf435000bff21a8005ff50d400077a86a0017fc4350001ffb128000bfd89400a7fcc4a000efe6250001feb128014ff1894001df8c4a005bff5250029ff2928000ff549400a7f8a4a0017ff425000bdfa128005ff9094002ffa84a0003bd425000bfe2128015ffcc9400a7fc64a0003fd3250029fe1928000ffd8540005fec2a004ffe61500057f30a8000ff5854009ff8c2a000afc615002dffa8a8013ff94540007faa2a004ffc515000bffa0a8005efd054002ffc82a0017fd4150001dea0a8005ff105400affe62a004ffe3150001fe98a8013ff0c5400a7fe42a004ffe2150001fe90a8013ff0854000dfec0a0007ff5050003ff2828001fe9414000ffaa0a0003f95050003fe2828001ffd014002ff680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ff860a0007ff2050003ff1028001ff0814000ffe20a0007fe1050003fd0828001ff04140007feca98002ff654c025ff32a6006bf99530007faca98002fd654c025fe32a6006bf19530007fec898002ff644c023ff3226005bf99130007fac898002fd644c023fe3226005bf19130097fea898047fe544c001feaa26011ff1513000dfec698013ff534c009ff29a6004ff54d30027f8a698013ff434c009ff21a6004ff50d30027f88698003ff624c0017fb126010ff9893001dfcc498003fd624c021fe3126003bf18930097fea498043fe524c001fea926010ff1493008ffe8498043fe424c001fea126010ff10930027fe6498013df324c009ff1926004ff4c930007ba6498013fc324c001ffb0a6000bfd853007ffcc29800afe614c001feb0a600fff18530015f8c29804bff514c01fff28a6000ff5453007ff8a298047ff414c01fff20a6000ff5053007ff88298013ff314c009ef98a6004ff8c530027fa6298003dd314c009fe18a6010ffc853007ffc4298003fd214c01ffe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe6098013fb304c003ff1
  | 2 => 0x31007fa8498883fc424c409ff9926204ff8c931027fa6498813fc324c4057fb0a6202ffd4531017fca29880bfd514c405fe28a6202ffd0531017fc829880bfd414c405fe20a6202ffcc531027ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff90a6202ff88531017ec429880bfc214c401ffb026200bfd81310fffcc098806fe604c401feb02621fff1813100df8c09888bff504c43fff282621fff1413110ffe809887ffe404c43ffe2026204ffcc131027be6098813fe304c409fe1826220ffc81310fffc409887ffc204c405ff8826202fdc4131017fc209880bfc104c401ffb2a4200bfd95210f7fcca9081afe6548401feb2a4200bf595210f7f8ca9081afc6548401ffb224200bfd91210effcc890816fe6448401feb224200bf591210eff8c890816fc644843dffaa2421dff95121007faa890877fc5448401ffb1a4200bfd8d210e7fcc690812fe6348401feb1a4200bf58d210e7f8c690812fc634843dffa9a421cff94d21007faa690873fc534843bffa1a421cff90d21007fa8690873fc43484057fb124203ffd49210f7dea49080ffe5248407fea924203ff1492101fd8a49080fff4248407ff2124203fb9092101ffa8490803ed4248407fe2124203ffcc92101ffc649080fee3248407fe9924200fb4c92101ff8649080aff6148405ffa8a4202ff94521017eca29080bfd5148401faa8a4202ff14521017fe8290877f74148405ff20a4202ff50521017f8829080bf44148405ff98a4202ff8c521017ec629080bfd3148401fa98a4202ff0c521017fe429080ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843dffa82421bff941210dff8a090877ff4048437ff202421bff101210e7fe609086ffe3048437fe1824203ffc812101fde409080ffe2048407fe1024202ffc4121017ee209080bfe1048405fe0824201bfd9550007fec8a8002ff6454035ff322a005bf99150007fac8a806bfc645400b7e322a006ffd5150037fca8a806b7e545400dfeaa2a006ff15150036f8a8a8003ff63540017fb1aa019ff98d50025fcc6a8003fd6354033fe31aa004bf18d50037fea6a801b7f535400dff29aa006ff54d50006faa6a801bfc5354035ffa1aa019ff90d50007fa86a8067fc4354001ffb12a000bfd89500c7fcc4a800efe6254001feb12a018ff1895001df8c4a801bff525400dbfa92a006ff94950037faa4a80037d525400dfe292a01affd09500c7fc84a8003fd4254031fe212a019ffcc9500c7fc64a8003fd3254031fe192a000ffd8550005fec2a805ffe61540057f30aa000ff585500bff8c2a800afc615400dffa8aa006dfd4550037fca2a801bfd5154001bea8aa006ff145500d7fe82a805
  | 3 => 0xfaa2a206dfd5151037fca8a881bfd5454401beaa2a206ff15151007fec6a8802ff6354453ff31aa204bf98d51007fac6a88a7fc63544097e31aa206ffd4d51036fea6a881bfe535440dfea9aa200df54d51037f8a6a88abff4354453ff21aa200ff50d5114ff886a8803ff62544017fb12a228ff9895101dfcc4a8803fd6254451fe312a203bf18951037fea4a881bfe5254451bf292a206ff54951037f8a4a881b7c5254455ffa12a228ff90951007fa84a88a3fc4254453ff992a228ff8c951007fa64a88a3fc32544057fb0aa202ffd4551037eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405ffa0aa202ff90551017ec82a880bfc4154405ff98aa202ff8c551017f862a880bff2154405ff10aa202fd88551017f842a8803ff60544017fb02a227ff9815100dfcc0a8803fd605444ffe302a201bf18151037fea0a881b7f505440dff282a206ff14151157fe80a889ffe405444ffe202a229ffcc15113ffc60a889ffc3054451ff902a227ff8815113ff840a880bff1054405ff082a202ff04151007fecaa0802ff655044dff32a8206bf99541007facaa0802fd655044dfe32a8206bf19541015fec8a0817ff545040bff2a28205ff5514102ff8a8a0803ff63504017fb1a8225ff98d41025fcc6a0803fd635044bfe31a8204bf18d41137fea6a0897fe5350401fea9a8225ff14d4102ffe86a0817bf435040bff21a8205ff50d410077a86a0817fc4350401ffb128200bfd8941127fcc4a080efe6250401feb128224ff1894101df8c4a089bff5250449ff2928200ff54941127f8a4a0817ff425040bff2128205ff5094102ff884a0897ff3250449ff1928200ff4c941127f864a080aff6150405ffa8a8202ff94541017eca2a080bfd5150401faa8a8202ff14541017fe82a0817f74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ffcc541017fc62a080bfc3150405ff90a8202ff88541017f842a0803ff60504017fb028223ff9814100dfcc0a0803fd6050447fe3028201bf18141137fea0a088ffe5050447fe2828205ffd014102f7e80a0817fe405040bfe2028225ffcc14111ffc60a088ffc3050449ff9028223ff8814111ff840a080bff1050405ff0828202ff04141007feca98802ff654c445ff32a6206bf99531007faca98802fd654c445fe32a6206bf19531007fec898802ff644c443ff3226205bf99131007fac898802fd644c443fe3226205bf19131117fea898887fe544c401feaa26221ff15131015fec698813ff534c409ff29a6204ff54d31027f8a698813ff434c409ff21a6204f790d31027fa8698803dd434c409fe21a6200ffd8931005fec498883fe624c4077f3126200ff58931107f8c49880efc624c445ffa926220ff94931007faa498883fc524c443ffa126220ff909
  | 4 => 0x6fe6054801feb02a433ff1815200df8c0a901bff505480dbfa82a406ff94152037f8a0a90dbff4054867ff202a433ff101521affe60a90cffe3054867fe182a403ffc815201ffc40a900ffc2054869ff882a433ff8415219ff820a9003ff65508017fb2a8400dfd9542004fecaa10cbfe655080d7f32a8400ff59542005facaa10cbfc655080d7e32a8400df19542034f8caa100eff645080bffaa28405ff9514202f7ca8a1017fd5450801deaa28405ff15142007fec6a1002ff6350863ff31a8404bf98d42007fac6a10c7fc63508097e31a8432ffd4d4218ffca6a1003fd5350863fe29a8405ffd0d4202f7e86a1017fe435080bfea1a8400ef50d4202ff886a100eff6250807ffa928403ff9494201fdca4a100ffd5250801f6a928403ff1494201ffe84a1017ef4250807ff2128403ef9094201ff884a100fbc4250807f62128403ffcc94201ffc64a100ffc3250801ffb0a8400bfd8542187fcc2a100afe6150801feb0a8430ff18542015f8c2a10cbff5150861ff28a8430ff1454202ffe82a1017fe4150861df20a8405ff1054202f7882a10c7ff3150861ff18a8430ff0c54201ffe42a100fef2150807ff10a8403ff08542007fec0a1002ff605085fff3028401bf98142007fac0a10bffc60508037e3028432ffd414217ffca0a10bffc505080bffa028405efd014202ffc80a1017fc4050863ff982842fff8c14217ff860a100fff2050807ff1028403ff08142187fe20a10bffe105085ffe0828400ffd9532005feca990bbfe654c80d7f32a6400ff59532005faca990bbfc654c80d7e32a6400ffd9132005fec8990b7fe644c80b7f3226400ff59132005fac8990b7fc644c80b7e322642effd513216ffca899003fd544c85bfe2a26403bfd8d32027fea699013fe534c809ef29a6404ff54d32007baa699013fc534c809ffa1a6404ff90d32027fa8699013fc434c8077fb126403ffd493201ffca49900ffd524c807fe2926403ffd093201ffc849900ffd424c807fe2126403ffcc932027de649900ffe324c807ef1926403ff0c93201fb8649900fec324c801ffb0a6400bfd8532167fcc29900afe614c801feb0a642cff18532015f8c2990bbff514c859ff28a642cff1453216ffe82990b3fe414c859fe20a6404ffcc532027fc6299013fc314c807ff90a6403fbc853201ffc429900ffc214c801ffb026400bfd813215ffcc099006fe604c801feb02642bff1813200df8c0990bbff504c857ff282642bff1413216ffe80990affe404c857fe2026404ffcc132027be6099013fe304c809fe1826403ffc813201fde409900ffe204c807fe102642cffc413215ffc20990affc104c8057fb2aa200ffd9151005fec8a8803bf64544015fb22a22aff9915102dfcc8a8803fd6454455fe322a205bf1915100778c8a8816bc645440df
  | 5 => 0x4d53027fe86a9813fe4354c09ef21aa604ff10d53007fec4a9802ff6254c7bff312a603bf98953007fac4a98f7fc6254c077e312a606ffd4953036fea4a981bfe5254c0dfe292a63effd09531effc84a98f7fc4254c09ff992a604f7cc953027fc64a9813fc3254c01ffb0aa600bfd85531e7fcc2a980afe6154c01feb0aa63cff18553015f8c2a981bff5154c0dbfa8aa606ff94553037f8a2a98fbff4154c79ff20aa63cff10553027fe62a9813fe3154c09fe18aa63dffc85531e7fc42a98f3fc2154c01ffb02a600bfd81531dffcc0a9806fe6054c01feb02a63bff1815300df8c0a981bff5054c0dbfa82a606ff94153037f8a0a98fbff4054c77ff202a63bff10153027fe60a9813fe3054c09fe182a63dffc81531dffc40a98effc2054c79ff882a63bff841531dff820a9803ff6550c017fb2a863aff99543035fccaa1803fd6550c017eb2a863aff19543035f8caa1812ff6450c0bffaa2863aefd514302ffca8a1817fd5450c0bfe2a28605ef15143025fec6a1813ff5350c09ff29a8604f794d43027faa6a1803dd5350c09fe29a8604ffd0d4302fbe86a1813fe4350c09df21a8604ff10d430277886a1813dc4350c01ffb128600bfd89431cffcc4a180efe6250c01feb128639ff1894301df8c4a18ebff5250c73ff2928639ff1494302ffe84a1817bf4250c0bff2128605ff10943027fe64a1813fe3250c09fe1928600ffd8543005fec2a18e3fe6150c057f30a8600ff585431c7f8c2a180afc6150c75ffa8a8638ff945431c7f8a2a1817ff4150c0bdfa0a8605ff9054302ff882a1813ff3150c09ef98a8604ff8c543027f862a18e7ff2150c71ff10a8638ff08543007fec0a1802ff6050c6fff3028601bf98143007fac0a18dffc6050c037e302863affd41431bffca0a18dffc5050c0bffa028605efd014302ffc80a1817fc4050c09ff9828604ff8c143027f860a18e7ff2050c6fff1028637ff081431c7fe20a18dffe1050c6ffe0828603bfd9552007fec8a9002ff645486dff322a405bf99152007fac8a90dbfc645480b7e322a406ffd5152037fca8a901bfd545480dfe2a2a400ffd8d52005fec6a90d7fe63548097f31aa400ff58d521aff8c6a9012fc635480dffa9aa406dfd4d52037fca6a901bfd5354801bea9aa406ff14d521b7fe86a90d7fe4354801fea1aa435ff10d5201dfec4a900fff525480df7a92a403ff9495201efca4a900ffc5254807be292a403fb1495201ffe84a900ffe4254807f7212a403ff1095201ffe64a900ffe3254807fe192a400ffd8552005fec2a90d3fe61548057f30aa400ff585521a7f8c2a900afc615480dffa8aa406ff94552037f8a2a90dbff4154869ff20aa434ff105521affe62a90d3fe3154869fe18aa403ffc855201ffc42a900ffc2154801ffb02a400bfd815219ffcc0a9
  | 6 => 0x1f01004c0000300e0000a8000020640381f00206c000010140000a0040000280000000e008000020080000002400000c068000220000b80c0000080180a01403c028010000a42000c00c00c0f815002000010060000240002400615c0080c00204c0000001a00800005006048038030a206c1b801002040038040000241c00700c0000280400c0a801015004000018000000380a0000000301981101a00c0001900c01000003000010008070020040000200600c00801004000050030620081600000003c4200800001c4580000000c0700b00400403001008098050000020440080800a0080081d01c01c0580a000060008010040040180100602c000020420000380000201800002002058000030140043c001008008000000000000300104200402000008010000020020000c00600002025000030008018130180000880c006050030100120140a0000120700a8210020003d02902e01806003002008028000000040680d0000000082400a00c0000100e0040500100001c0000102e00c030030000080100500a05c1200200a0000000501a0080080700a090050070641241e80c002000070000060780080b0000001a80601c020018000180080080700a0300380b004000018100060400380200200c02000004060000320320080280001e0640000200002c01805000038028250060180280d0060100600b004004018070140080781b0100000b8010060040600500001c01806002024040080020540001400a2e80b816ff655500b7fb22a805ffd51540377ea8aa017fe545500bbf2a2a805ff1515402ef8a8aa017bc5455001ffb1aa800bfd8d54217fcc6aa012fe6355001feb1aa842ff18d54025f8c6aa01bff535500dff29aa806ff14d5402ffe86aa017fe435500bfe21aa800ffd8954005fec4aa107fe62550077f312a800ff5895420ff8c4aa00efc625500dffa92a806ff94954037f8a4aa017ff425500bdfa12a805ff9095402ff884aa10bff3255083ff192a841ff0c954007fec2aa002ff6155081ff30aa802bf98554007fac2aa103fc61550057e30aa806ffd4554036fea2aa01bfe515500dfe28aa805ffd055402ffc82aa017fc4155085ff98aa840ff8c554207f862aa107ff2155081ff10aa840ff08554007fec0aa002ff605507fff302a801bf98154007fac0aa0fffc60550037e302a806ffd4154037fca0aa01bfc505500bffa02a805ff9015402ff880aa10bff305507fff182a83fff0c15420ffe40aa0fffe205507ffe102a840ffc41541fffc20aa0fffc10550097fb2aa600ffd9153005fec8a98fbfe6454c0b7f322a600ff591531f7f8c8a9816fc6454c0dffaa2a606ff951531f6fca8a981bfd5454c0dfe2a2a606df15153025fec6a9813ff5354c0defa9aa604ff94d53026fca6a9813fc5354c09be29aa604f71
  | 7 => 0x4f1319582940080358000000000001a30818002781a3a828002c701480000e8002b09be1d3a232891db84c0000000389ab0000001670000e90e08cdac60551c5abe2c026383800000013488d1800fb82b1fe0bd8000ee0401bc1ad9b980000000003a2a10002a819011d94e80026f00004f11c0138001a10001a715f0e29db19b986a7627502d935a87a840ac00018391199d8002368b79b82649b50b61d82ab23800a91b2400000000d980000000019203b9880de0000001188000000002b394fa0a87aac1a2e2be8a31ca1e30b5a5c27195300000028b1d4a4a8db29e80028500008b86a20e0922399371911990b2aaca7d9dd16b8f497280000000026200000002400000009f0002561438a6963a7a25780015198122a0fa05a2708000d08d50000c12b4800011a7a9abab180028e80005d29700025280004720a0d00001bf0b800020880027e08e2a480000027ea192c0a988000000002768000f00980002548150e624ba7b96c9749280000d622a87297100000000002791e18480000380004f91c8001b20700c78000000000228d194480018f20500012899380026500000024c8000dc8e1842a9d0000001498dea3900011b966a371260000000002818001bd0001c7a11a85a950ec83d15fa538311c9aa29178000000f880000020b0858000f680000000008f0db8002a780021417b025087142895896868abd80025e92427c8360cb80012697323485a8aaa4e00000025f96a0a880c00029795080000f8000a224285d9e11e1a7411e9858d31bc8088001c92888539b380023fa1480019f1540ba2bb0529ae0001bf8772c4a5000000007c9520910299e80002c317c9cd9aa8681d90002431159b59f71a5a800841ea137821a2785217614c01f1f694d17f8c018a8a50e011901c2438f09620a083f2bc07e1a287487684e979a312599ce02617e80000180013c89000000000014b869ac90b399f8432b30002c38cb0adaa309705928680014901d96d96f1f498980018e80010c0a5a2800010aa168001df8eda960002680540bf0002792b99568662440dd2ae10f0888b981710523182baaf8a71888000000000e38000010001500ceac80ec1f60be0ef1d188795b06b1a80001c39632931a981a86ca1094d82a9230ff8d79c18000000110f600022500000e0938d68809d30001d9ab62b70502a400000000000017d0d4a058001642138001a79068ac8129cb86f1511e40001e78f2000000119aa202f0630001ac1a527c1fb0002530caa3e09b0340aeabc9209cfa5a80480b00805c010030160780201400001c1784f01a0300980200200c2e80100c0540080702c0000181900001806000000040060080020300e80900e000008080140081180e00e0000000b00012c0100b0060040a81301c00c0080000c0002700000200408802000000008
  | 8 => 0xe800108a299df0000001f3ac28000002bf910a3396a9a41ae81893d83921a1430000000002450572288a190915e8ab800039840a8605b80f19a025a1995993a10495ca478510ee9360002aaa9d8628af1d7954a2d83a8f3160a49a128bd0dc25b00001d1e220483c2c9a8a975a0404da1014aa13136a698e318626584799d26f9071e2a4b1a225c93aa248778e51980978000c39b78f900023412b0000001079c6aac00007180012285ea8b80027f8640001ec8c08658ba9381878000000001ff0c98000ed00000000000023d94519602a0a390e82212b96813ea9c19e18b846836a96800209000000158a8e1f0000000ac400000025b8a02570041ba9dc0f7a0d8001890000000002a887388d9129929c119303d9e38000eb961187255144196a90a929e586a80028f9de20b9dd8f59b09a68c518410087c0828b70e89211698e7812130206830a6722e9972580eaa91a1104b19405780b1391f7a3c28d25105c2c22210c19309fd975061263178a729d284e2aa24d92e914ab795d1239bb0e72b6a4d0758c909aa6b1ec1cc8028000b8a5d0000002959da92e2a19f31552b8a618e49cf0648c4a9a00d04c9b918323216e08c2519cd024abd1e480000021e23f0000d899e8ae0c71ee0000000f724e89a10421d8f28000480000000b510b019aae9b6182000016a098001d899a8e987b1af0000b48cca120950371c313212f0a601e85619520d0a81720691c20000002710c6224241145899a0c07d29b89620397380000009492f9529329b101020311311d2b2275a7484ba702591629351d5a0800705c9bd90d24a00012496193b800176970acb000061a00a3789ba360230588290fea4fa89a3011f88a2180762b42a383f97f2409ee87b9c091f1f8830216207a02aab9cc1b299880212c2021ef87d9eb9740b91c501589ca8083c9a023a8b215604d0a41fc1b491612a1fa0cc01793f8daa3a27d16e9f80f515da41a661a192c91a98e0c32449af88b0781a88bb87f8d3a01a6c21d1ed90e1388721f22af06c24588ca1ca4c191ab290b88921f853100164a5409182ea4203192916f97e1ba2990838e409e22b06b99c28da7f059ab018b00d8c283394c8bb10f86da2ca4696888801314f0160108f11ad01f85490983787329f25a24820c9f08d723e9d09d40559d71d50cf15723b8931beaca06e1651252a62a906faba9828091bbaad8b190a17926a1080e585f03307a04a0801692a59200df034851925a209012c502116613c14e026a4719494798ca67a83a55ac102c00b8aa0002b908f80005e2488050fc2a9805890a9a8d904511823b04215902382d00022180000026d93321580014b0c20792a70fb00ca6e21501a0b007127394225d99b0b30ef98a28c0069b693118d0001b8a999701030001f40000fd1dc93f0000002870001b40dd8002
  | 9 => 0x2a506020f86e80300026400022703226291512d1fa8d59271d21cea350001e9a770d21b30000000000458200000000000048000000000002c596581e0000fa83e20e9279aa12d80000000000023880014129010c80000006680000000025898d806260a9b00002f8ad21b0a7aa69fe9340000000270289399678e821a9ff9eb1218001c800000000000022b89f9e61772b58f38001c026eaa01ef0410799c40582911a4a0100789928201825f2880001809c4a93a3ca8a1ca9138ff0ca1018a915b8509da1e028f0ea28315588229e0000a29c889404980027793b1169718b69998c81cb11126b89d8f9a2f2002c68dfa601e91c609d0cd2a08000bea72060a2000015a16b044063978089a849fb94a2b10438b40000bc94703b23080000029c80a1170e68708a49958000d80000001f98000928002328da1b712aa6a90d9e505689e9b19142982c88f800006d00020f0141f907f1578ab0831400002788671d0197a2f9fc8002bf1e716c00008513d03282082e05b0f429fa2c1ea9f504881915e1818c6a188ce1c7098953a690e20d40862ca9a61602509f123329215c03504aa799101f184182ca5e2688c58a99d6ac7aad1058bc0002061de87e88497b9a90b11460eb0002731f58cf9e897aa4610280990211a0fc8a11aca2d2258fe062133a1f08114810612217da6d1f2abb9e08742ba13e078a6ca94a521fd075044ab517a19ca1796d1850e118c00027b2220490f1a1e95a800266941a228af88e9ed22908a97798fa3580026110380023d20721728c9b00d106500001c886a4900011222601b8000000bfa269e68000c8940a81067ab81468c41d109c00000021c0280461d62239488fd85f9a08000b0990a1b8d29c292981b25697c03
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910236fa30d8910236ef20d8910236ed20d891001cff7658910005df7358910045dc735891003eec625891022df7715891023dfb7058910004ff7558910034fe7558910034fc7558910004ff745891002cfe745891002cfc7458910004ff7358910006df7358910004df7358910024fe7358910024fc7358910006dc7358910024dc7358910234ff7258910006ef725891003eee325891022cff7158910006f7715891005ef631589100dcff7058910006fb70589100defa3058910004ff7654910004fe7654910004fd7654910004fc7654910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100557c7550910006bf645091002ebc6450910004ff764c910004fe764c910004fd764c910004fc764c91001eee624c910006ed624c910015f6714c91000df4764c510026f4764c51000cf4764c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510047d6434c510007d5434c510005f7724c510006f7624c510006f5624c510007f3704c51000df6704c51000df4704c5100fff0704c510016f7604c510017f3604c5100fff2404c5100ffd7304c5100fff2304c5100ffd5304c51000df4764851001ef4764851000cf47648510006f76548510006f565485100eef664485100eef46448510005f77348510005f57348510006f76348510006f56348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe46248510227e7524851003fe4524851003fe64248510007e5424851003fe63248510007e53248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100dff240485100dff230485100dfe720485100dfe52048510015f8765011002ef87650110014f87650110006fb6550110006f9655011000dfb745011000fbb7450110007bb645011002efa645011002ef8645011004fb8645011021fbb545011004fb85450110005fb735011004fbb4350110007b9435011004fbb4250110007b94250110007f37150110015fa7150110015f8715011009ff0715011000efb615011000ff3615011009fbb415011009fb9415011009ff23150110007f1315011009ff22150110007f12150110015f8764c110026f8764c110014f8764c110005fb744c110005f9744c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110047d8634c110026d8634c110006fb624c110006f9624c110047db324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c11000efb614c11000ff3614c11007fdb314c11007ff2314c11007fd9314c110047f1314c110007d1314c11007ff2214c110007f1214c110
  | 1 => 0x95102a67f51d95102a67d51d95102a6f621d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102967f50d95102967d50d9510296fa40d9510034ff76595100567c6559510005bf745951004dbc745951028df7715951029dfb7059510294ff75595100067f7559510004ff7459510006bf7459510004bf745951002cfe745951002cfc7459510006bc745951002cbc7459510004ff7359510024fe7359510024fc73595100567f5359510004ff725951001cfe725951001cfc725951028cff7159510006f771595100bef6215951013cff7059510006fb705951013efa405951002cfe76d911004ebe64d9110034fe75d9110004fd75d9110034fc75d911011cfd74d9110006bf54d911004ebc54d9110024fe73d9110004fd73d9110024fc73d911001cfe72d9110004fd72d911001cfc72d911004ebf42d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110286bf41d9110286bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110276bf40d9110276bd40d911002cff765911004ebc645911026df7715911027dfb7059110004ff7559110034fe7559110034fc7559110274ff7459110006bf7459110004ff7359110024fe7359110024fc735911004ebf4359110004ff725911001cfe725911001cfc725911026cff7159110006f7715911011cff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc7655110024fe76d8d10046de63d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d10046de53d8d1001cfe72d8d10004fd72d8d1001cfc72d8d10006de32d8d10046dc32d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10266df31d8d10266dd31d8d10266f621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10256df30d8d10256dd30d8d10024ff7658d10046dc6358d1024df77158d1025dfb7058d10004ff7558d10034fe7558d10034fc7558d10004ff7458d1002cfe7458d1002cfc7458d10254ff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d1024cff7158d10006f77158d1007ef62158d100fcff7058d10006fb7058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100367e6554d100067d6554d10006df6354d10026dc6354d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1002ebe6450d10006bd6450d1000dfa7050d1001cfe76d891003eee62d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d891000cff71d8910014fe71d891000cfd71d8910014fc71d8910246f631d8910246ef21d8910246e
  | 2 => 0x6df6350d20026dc6350d2000dec764c920026ec764c92000cec764c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c920067ce534c920007cd534c920005ef714c920007eb704c92000dee704c92000dec704c92015fe8704c92001eef604c92001feb604c92015fea504c92015fcf304c92015fea304c92015fcd304c920014fe76d852005ef661d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d85202c6ee32d8520006ed32d852005ef621d85202c6f521d852000cfe70d852001cfd70d852000cfc70d852022efa30d852022ef710d8520005df7358520065dc735852005ef461585202bdfb7058520004ff7654520004fe7654520004fc76545200067f65545200367c6554520005bf745452006dbc7454520004ff7650520004fe7650520004fc7650520004ff764c520004fe764c520004fc764c52001dee724c520016f6614c52000dec7648520016ec764852000cec76485200f6ee65485200f6ec6548520006ef6448520006ed6448520005ef7348520005ed7348520006ef6348520006ed634852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005fe65148520007e551485202b7e7414852005fe4414852005fe63148520007e53148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200dfea50485200dfea30485200dfe7104852001df87654120036f8765412001cf8765412000dfb755412000f7b75541200077b6554120036fa6554120036f86554120077786554120006fb6454120006f964541202af7a5454120077785454120005fb73541200777b5354120007795354120007eb725412001dfa725412001df872541200c7e8725412000efb625412000feb62541200c77b52541200c77952541200c7ea3254120007e932541200777b51541200077951541200c7eb2154120007e9215412001df8764c120026f8764c12001cf8764c120005fb754c120005f9754c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120067d8634c120026d8634c120007eb724c12001dfa724c12001df8724c120087e8724c12000efb624c12000feb624c120087db324c120087ea324c120087d9324c120067e9324c120007c9324c120006fb614c120067db314c120007d9314c120087eb214c120007e9214c120034fe76d95100567e65d951013cfd75d951002cfe74d9510004fd74d951002cfc74d9510024fe73d9510004fd73d9510024fc73d951001cfe72d9510004fd72d951001cfc72d951000cff71d9510014fe71d951000cfd71d9510014fc71d
  | 3 => 0xf7648530004fe7648530004fc7648530025de7348530005dd734853001eee6248530007cd3248530016f66148530007d5314853000dfa70485300dfd83048530034fe76d95200767e65d952019cfd75d952002cfe74d9520004fd74d952002cfc74d95200067e54d95200767c54d9520024fe73d9520004fd73d9520024fc73d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203267f52d95203267d52d9520014fe71d9520004fd71d9520014fc71d95200767f51d952001cff70d952001cfd70d95203167f50d95203167d50d9520034ff76595200767c655952030def725952031dfb7059520314ff75595200067f7559520004ff745952002cfe745952002cfc7459520004ff7359520024fe7359520024fc73595200767f535952030cff7259520006ef7259520004ff7159520014fe7159520014fc715952019cff7059520006fb705952002cfe76d912006ebe64d9120034fe75d9120004fd75d9120034fc75d912017cfd74d9120024fe73d9120004fd73d9120024fc73d912000cff72d912001cfe72d912000cfd72d912001cfc72d9120306bf42d9120306bd42d9120014fe71d9120004fd71d9120014fc71d9120306ef21d912001cff70d912001cfd70d91202f6fa50d91202f6bf40d91202f6bd40d912002cff76591200057f75591200757c755912006ebc64591202edef72591202fdfb7059120004ff75591200067f75591200047f7559120034fe7559120034fc75591200067c75591200347c75591202f4ff7459120006bf7459120004ff7359120024fe7359120024fc735912006ebf43591202ecff7259120006ef7259120004ff7159120014fe7159120014fc71591200a6ef215912017cff7059120006fb705912017efa5059120004ff7655120004fe7655120004fd7655120004fc7655120024fe76d8d20066de63d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d20066de43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202e6df32d8d202e6dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20066dc31d8d202e6ef21d8d2001cff70d8d2001cfd70d8d202d6df30d8d202d6dd30d8d20024ff7658d20066dc6358d202cdef7258d202ddfb7058d20004ff7558d20034fe7558d20034fc7558d20004ff7458d2002cfe7458d2002cfc7458d202d4ff7358d20006df7358d202ccff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d20086ef2158d2015cff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200367e6554d200067d6554d2000dfa7054d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2002ebe6450d20006bd6450d20
  | 4 => 0x9130014fc71d9130366df31d9130024ff70d9130024fd70d9130356bf40d9130356bd40d9130356fa10d913002cff765913008ebc645913034ddf7359130005f7715913007df4715913035dfb70591301bfd83059130004ff7559130034fe7559130034fc7559130354ff7459130006bf7459130006bf545913008ebc545913034cff7359130006df7359130004ff725913001cfe725913001cfc725913008ebf4259130004ff7159130006f77159130004f77159130014fe7159130014fc7159130006f47159130014f4715913008ebf41591300aedf31591301bcff7059130006fb70591301befa1059130004ff7655130004fe7655130004fd7655130004fc76551301ffd8305513001cfe76d8930086ee62d89302cfd830d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930006ef52d8930086ec52d8930086ee42d8930086ee32d8930346ed32d8930014fe71d8930004fd71d8930014fc71d8930024fd70d89302ceef20d8930086ec625893033dfb705893015fd83058930004ff7654930004fe7654930004fc76549300367e65549300067d655493019fd83054930004ff7650930004fe7650930004fc76509300057f75509300957c755093002ebe6450930006bd6450930006ef625093001eec625093017fd8305093000ddc764c93001edc764c93000cdc764c930006df654c930006dd654c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c930005df714c930087cf214c930007db704c93000dde704c93000ddc704c93015fd8704c93000dd8704c930026df604c930027db604c93015fcf204c93015fda204c93015fda104c930014fe76d853007ef661d853024fd830d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d853007ef651d8530006f741d853007ef441d853007ef631d8530336f531d8530024fd70d853024ef710d853007ef4615853032dfb70585300ffd83058530004ff7654530004fe7654530004fc76545300367e65545300067d6554530005bf745453008dbc7454530006f76154530016f4615453013fd83054530004ff7650530004fe7650530004fc765053002ebe6450530006bd645053011fd8305053000ddc764c530016dc764c53000cdc764c530006df644c530006dd644c530005df724c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6214c530007db704c53000dde704c53000ddc704c5300ffd8704c53000dd8704c530026df604c530027db604c5300ffda204c5300ffd7104c5300ffda104c530004f
  | 5 => 0x4ff7654540004fe7654540004fc76545400367e65545400067d6554540005bf745454002dbc74545400b73f545454000dfa705454000dbc7650540016bc765054000cbc76505400b5be75505400b5bc7550540005bf7350540006bf6350540005bf725054002dbf715054002fb77150540007b76150540016be6150540016bc615054009fb4615054009fb65150540007b55150540007bb705054000dbe705054000dbc705054011fb8705054002ebf605054002fbb605054011fba505054011fba1050540004ff764c540004fe764c540004fc764c54002dbe744c540005bd744c540026de634c5400079d434c540004ff7648540004fe7648540004fc764854002dbe7448540005bd744854001eee6248540007ad4248540006f76148540016f461485400efb7414854002df87654140036f8765414002cf8765414000dfb755414000f7b75541400077b6554140036fa6554140036f865541400b7786554140007bb745414002dfa745414002df874541400d7b8745414000efb645414000fbb64541400b7bb54541400d77a54541400d77854541400d7b854541400d73854541400b77b53541400077953541400d7bb4354140007b94354140006fb62541400b77b52541400077952541400d7bb4254140007b94254140005fb71541400b77b51541400077951541400d7bb4154140007b94154140034fe76d95300967e65d953008dbe74d9530005bd74d9530377d830d95301dcfd75d953002cfe74d9530006be74d953002cbe74d9530004fd74d9530006bd74d9530004bd74d953002cfc74d953000cff73d9530024fe73d953000cfd73d9530024fc73d95303867f53d95303867d53d953001cfe72d9530004fd72d953001cfc72d9530386df32d9530014fe71d9530004fd71d9530014fc71d9530024ff70d9530024fd70d95303767f50d95303767d50d9530376fa20d9530034ff76595300967c655953036ddf7359530005ef7259530085ec725953037dfb70595301dfd83059530374ff75595300067f7559530004ff745953002cfe745953002cfc74595300067e54595300967c545953036cff7359530006df7359530004ff7259530006ef7259530004ef725953001cfe725953001cfc7259530006ec725953001cec72595300967f52595300cedf3259530004ff7159530014fe7159530014fc71595300967f51595301dcff7059530006fb70595301defa205953002cfe76d91300957e75d91300057d75d913008ebe64d9130357d830d9130034fe75d91300067e75d91300347e75d9130004fd75d91300067d75d91300047d75d9130034fc75d91301bcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d9130366bf43d9130366bd43d913001cfe72d9130004fd72d913001cfc72d9130014fe71d9130004fd71d
  | 6 => 0xf7459540006bf74595400b6bf54595400d67e54595400d67c54595400d6bc5459540004ff7359540024fe7359540024fc7359540004ff725954001cfe725954001cfc72595400d6bf4259540004ff7159540014fe7159540014fc71595400b67f51595401fcff7059540006fb7059540024fe76d8d400aede63d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d40006bf54d8d403b6bc54d8d400aede43d8d403b6dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d403b6bf42d8d40014fe71d8d40004fd71d8d40014fc71d8d403b6bf41d8d4002cfd70d8d4034edf30d8d4034efa10d8d400aedc6358d40005f77158d4009df47158d403adfb7058d40004ff7654d40004fe7654d40004fc7654d400067f6554d400367c6554d40005bf7454d4002dbc7454d401f73c5454d4000dbc7650d40026bc7650d4000cbc7650d400b5be7550d400b5bc7550d401d6be6550d401d6bc6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400af9c6350d400af9e5350d400079d5350d40005bf7250d40005bf7150d400af9f3150d40007bb7050d4000dbe7050d4000dbc7050d401bfb87050d4002ebf6050d4002fbb6050d401bfba5050d401bfba1050d4001cfe76d89400a6ee62d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89403a6bf43d8940006bd43d89400a6ee42d89403a6ed42d8940014fe71d8940004fd71d8940014fc71d894002cfd70d89402eefa50d89402eeef20d89400057f75589400b57c75589400a6ec625894039dfb7058940004ff7654940004fe7654940004fc7654940005bf745494002dbc745494000dbc765094001ebc765094000cbc76509400073f75509400b5be75509400b5bc75509400073c75509400b53c7550940006bf6550940006bd6550940005bf7350940006bf635094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400a7ac62509400a7ae5250940007ad5250940005bf7150940186be6150940186bc61509400a7af2150940007bb705094000dbe705094000dbc705094017fb8705094002ebf605094002fbb605094017fba505094017fba1050940004ff764c940004fe764c940004fc764c94002dbe744c940005bd744c940005fb704c94000df8704c940014fe76d854009ef661d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540024fe73d8540004fd73d8540024fc73d8540396bf43d8540006bd43d854001cfe72d8540004fd72d854001cfc72d854009ef641d8540396f541d8540006f731d854009ef431d854009ef621d854002cfd70d854026ef710d854009ef4615854038dfb7058540
  | 7 => 0x89500067d53d89500c6ee52d89503f6ed52d8950006ef32d89500c6ec32d8950014fe71d8950004fd71d8950014fc71d89500c6ef21d8950034fd70d895030eef20d89500c6ec62589503edfb705895000d7c765495001e7c765495000c7c76549500d57e74549500d57c74549500057f73549500067f63549500357f72549500376f72549500076f625495001e7e625495001e7c62549500c76c62549500c76e42549500057f71549500077b705495000d7e705495000d7c705495019f7870549500367f60549500377b605495019f7a405495019f7a2054950004ff7650950004fe7650950004fc76509500057f75509500357c755095002ebe64509500d73e54509500076d525095000dfa7050950004ff764c950004fe764c950004fc764c9500357e754c9500057d754c950026de634c9500075d534c950014fe76d85500bef661d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d8550024fe73d8550004fd73d8550024fc73d85503e67f53d85500067d53d855001cfe72d8550004fd72d855001cfc72d85500bef651d85503e6f551d8550034fd70d855028efa40d855028ef710d8550005bf74585500d5bc74585500bef461585503ddfb705855000d7c76545500167c765455000c7c76545500073f74545500d57e74545500d57c74545500073c74545500d53c74545500067f64545500057f73545500067f63545500057f72545501467e62545501467c62545500357f71545500377771545500077761545500167e61545500167c61545500bf7461545500bf7641545500bf7621545500077b705455000d7e705455000d7c705455013f7870545500367f60545500377b605455013f7a405455013f7a2054550004ff7650550004fe7650550004fc76505500057f75505500357c7550550007755150550004ff764c550004fe764c550004fc764c5500357e754c5500057d754c550005fb704c55000df8704c550004ff7648550004fe7648550004fc76485500357e75485500057d7548550006ef624855001eec62485500f76f5248550016f66148550007755148550034fe76d95400b67e65d954002dbe74d954000dbd74d95400b73f54d95401fcfd75d954000cff74d954002cfe74d954000cfd74d95403c6bd74d954000cbd74d954002cfc74d95403d67f54d95400b6bf54d95400b63f54d95403d67d54d95403d6bc54d9540024fe73d9540004fd73d9540024fc73d95400b67f53d954001cfe72d9540004fd72d954001cfc72d95400067e52d95400b67c52d95403d6bf42d9540014fe71d9540004fd71d9540014fc71d954002cff70d954002cfd70d95403c67f50d95403c67d50d9540034ff76595400b67c65595403bdbf74595400d73c54595403cdfb70595403c4ff75595400067f75595403bcf
  | 8 => 0xf7e75254521147765254521147745254521147e45254521147645254521147e64254521007e54254521147e63254521007e53254521005f770545210f7775054521147e7205452101df4764c521026f4764c52101cf4764c521005f7754c521005f5754c5210edf6744c5210edf4744c521015f7734c521017d7734c521007d7634c521026f6634c521026f4634c5210e7d4634c5210e7d6434c521007d5434c521007e7724c52101df6724c52101df4724c521107e4724c521016f7624c521017e7624c52141fe7524c521107e4524c521107e6424c521007e5424c521107e6324c5210e7e5324c521005f7704c5210e7d7304c521107e7204c52100cfe76d81210defa60d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d81212beee32d8121006ed32d812101cfd71d812100cfc71d812123ef631d8121006f531d8121006fb30d81210def830d81210defa20d81210defa10d8121005df73581210e5dc73581210def8605812102cfe76d91500357e75d915000d7d75d91500d6be64d91500d73e54d915000cfd75d91503be7d75d915000c7d75d915002cfc75d91500d67e54d91500d6be54d91500d63e54d9150416bd54d91500d67c54d9150024fe73d9150004fd73d9150024fc73d91500d6bf43d915001cfe72d9150004fd72d915001cfc72d9150014fe71d9150004fd71d9150014fc71d91504167f51d9150006be41d91500d6bc41d9150034fd70d91503bebf40d91500d6bc64591500d73c545915040dfb7059150024fe76d8d500cede63d8d5000cfd75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500067e54d8d504067c54d8d500cede53d8d50406dd53d8d5001cfe72d8d50004fd72d8d5001cfc72d8d504067f52d8d50014fe71d8d50004fd71d8d50014fc71d8d504067f51d8d50034fd70d8d5036edf30d8d5036efa20d8d500cedc6358d50005ef7258d500c5ec7258d503fdfb7058d5000d7c7654d500267c7654d5000c7c7654d500d57e7454d500d57c7454d501f67e6454d501f67c6454d500357f7354d500375f7354d500075f6354d500267e6354d500267c6354d500cf5c6354d500cf5e4354d500057f7254d500cf5f3254d500057f7154d500077b7054d5000d7e7054d5000d7c7054d501df787054d500367f6054d500377b6054d501df7a4054d501df7a2054d50004ff7650d50004fe7650d50004fc7650d500057f7550d500357c7550d50006bf6450d5002ebc6450d500d73c5450d500075d5350d5001cfe76d89500c6ee62d895000cfd75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d8950024fe73d8950004fd73d8950024fc73d89503f67f53d
  | 9 => 0xe7655121004fd7655121004fc7655121005ef725512101dec7255121005f77155121015f47155121024fe76d8d210e6de63d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21164fd73d8d21014ff72d8d21014fd72d8d21446df32d8d21446dd32d8d2101cff71d8d2101cfd71d8d21436df31d8d21436dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d210e6dc30d8d21446ef20d8d21436f710d8d21024ff7658d210e6dc6358d2142def7258d2143df77158d21005fb7058d210ddf87058d21004ff7558d21034fe7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d21434ff7358d21006df7358d2142cff7258d21006ef7258d21164ff7158d21006f77158d21004ff7058d21006fb7058d21004fb7058d2100cfe7058d2100cfc7058d21006f87058d2100cf87058d210e6df3058d21106ef2058d21166f71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210367e6554d210067d6554d21005ef7254d2101dec7254d210f76f5254d21015f67154d21004ff7650d21004fe7650d21004fd7650d21004fc7650d2102ebe6450d21006bd6450d2101dee7250d21005f77150d21015f47150d210efb74150d21015ec765092102eec7650921014ec76509210076f75509210f5ee75509210f5ec75509210076c75509210f56c7550921006ef6550921006ed655092101def745092101faf7450921007af645092102eee645092102eec64509210efac64509210efae5450921007ad5450921005ef73509210efaf4350921007ad4350921007e77150921015ee7150921015ec7150921187e4715092101eef615092101fe76150921187e651509210efe74150921187ae4150921187ac4150921187e44150921187a44150921187e63150921005ef70509210efaf4050921187e71050921015ec764c921026ec764c921014ec764c9210f5ee754c9210f5ec754c921005ef744c921005ed744c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c9210e7cc634c9210e7ce534c921007cd534c921007e7714c921015ee714c921015ec714c921167e4714c92101eef614c92101fe7614c921167e6514c921427e7414c921167e4414c921167e6314c921005ef704c9210e7cf304c921167e7104c92101df47654521036f4765452101cf47654521015f77554521017777554521007776554521036f66554521036f465545210f7746554521007b774545210edf674545210edf47454521007b474545210edb47454521006f76454521006f564545210f7775454521007755454521005f773545210f7775354521007755354521007e7725452101df6725452101df47254521147e47254521016f76254521017e76254521
  | 10 => 0x8931024fd71d893142eef21d893100cfe70d8931004fd70d893100cfc70d8931496df30d893142ef710d8931106ec625893148df77158931005fb70589310fdf87058931004ff7654931004fe7654931004fc7654931004ff7650931004fe7650931004fc76509310057f75509311157c7550931006bf645093102ebc64509310079d435093100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d8131024fd71d813125ef621d81310fefa50d81310fefa30d8131006fb20d81310fef820d81310fefa10d81310fef86058131034fe76d95210f67e65d952101dee72d9521015ed72d95210f76f52d95211a4fd75d952102cfe74d9521004fd74d952102cfc74d95210067e54d95210f67c54d9521024fe73d9521004fd73d9521024fc73d9521014ff72d9521014fd72d9521476ed72d9521014ed72d95214867f52d95210f6ef52d95214867d52d9521486ec52d9521486ee42d952101cff71d952101cfd71d95214767f51d95214767d51d952100cfe70d9521004fd70d952100cfc70d9521034ff76595210f67c6559521005bf74595210edbc745952146def72595211476c525952147df77159521474ff75595210067f7559521004ff7459521006bf7459521004bf745952102cfe745952102cfc7459521006bc745952102cbc7459521004ff7359521024fe7359521024fc73595210f67f535952146cff7259521006ef72595210f6ef52595211467e52595211467c5259521146ec5259521146ee42595211a4ff7159521006f77159521004ff705952100cfe705952100cfc70595210f67f505952102cfe76d91210eebe64d9121015f671d912101df571d91210efb741d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121006bf54d91210eebc54d9121024fe73d9121004fd73d9121024fc73d9121014ff72d9121014fd72d9121466bf42d9121466bd42d912101cff71d912101cfd71d9121466f571d912101cf571d9121456f651d9121456bf41d91210eef741d9121456bd41d9121456f441d912100cfe70d9121004fd70d912100cfc70d912102cff76591210057f75591210f57c75591210eebc645912144def725912145df77159121187b44159121004ff75591210067f75591210047f7559121034fe7559121034fc75591210067c75591210347c7559121454ff7459121006bf7459121004ff7359121024fe7359121024fc73591210eebf435912144cff7259121006ef7259121184ff7159121006f77159121186f651591210eef74159121186be4159121186bc4159121186f44159121004ff705912100cfe705912100cfc70591210eebf4059121004ff7655121004f
  | 11 => 0x137746554541007b7745454102df6745454102df47454541157b47454541016f76454541017b76454541157775454541157755454541137775354541007755354541157b74354541007b54354541006f762545414e7765254541137745254541137775054541157b7405454100cfe76d814111efa60d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d814138ebf43d8141006bd43d814101cfe72d8141004fd72d814101cfc72d814102cfd71d814111efa40d814111efa10d814111ef86058141034fe76d95311167e65d95311e4fd75d953102cfe74d9531004fd74d953102cfc74d9531014ff73d9531014fd73d95314de7f53d95314de7d53d95314dede43d953101cfe72d9531004fd72d953101cfc72d9531024ff71d9531024fd71d95314ce7f51d95314ce7d51d95314cef621d953100cfe70d9531004fd70d953100cfc70d9531034ff76595311167c6559531005bf745953110dbc74595314c5df73595314d5f771595314ccff75595310067f7559531004ff7459531006bf7459531004bf745953102cfe745953102cfc7459531006bc745953102cbc74595314c4ff7359531006df735953114ede4359531004ff725953101cfe725953101cfc72595311e4ff7159531006f771595311e6f62159531004ff705953100cfe705953100cfc70595311167f505953102cfe76d913110ebe64d9131034fe75d9131004fd75d9131034fc75d91311c4fd74d9131006bf54d913110ebc54d9131014ff73d9131014fd73d91314bebf43d91314bebd43d913101cfe72d9131004fd72d913101cfc72d913110ebf42d9131024ff71d9131024fd71d91314aebf41d91314aebd41d913100cfe70d9131004fd70d913100cfc70d913102cff765913110ebc64591314a5df73591314b5f77159131004ff7559131034fe7559131034fc75591314acff7459131006bf74591314a4ff7359131006df7359131004ff725913101cfe725913101cfc72591311c4ff7159131006f77159131004ff705913100cfe705913100cfc705913110ebf4059131004ff7655131004fe7655131004fd7655131004fc7655131015dc7650d3102edc7650d31014dc7650d31006df6550d31006dd6550d31025df7450d310279f7450d310079f6450d3102ede6450d3102edc6450d3110f9c6450d3149f9f5450d3110f9c5450d3110f9f4250d31007d77150d31015de7150d31015dc7150d311c7d47150d31026df6150d31027d76150d311c79f4150d311c79d4150d311c7d62150d31005df7050d3110f9f4050d311c7d71050d3101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d8931106ee32d8931496ed32d
  | 12 => 0xd545095101eee62509511476e5250951015f67150951187b64150951004ff764c951004fe764c951004fc764c9510057f754c9510357c754c951006bf644c95116ebc644c9510075d534c95100cfe76d8151006bf64d8151006bc64d815113efa60d8151014fd75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d8151024fe73d8151004fd73d8151024fc73d81513de7f53d81510067d53d815101cfe72d8151004fd72d815101cfc72d8151034fd71d815129ef621d815113efa50d815113efa10d8151005bf7458151155bc7458151006bf6458151006bc645815113ef86058151034fe76d95411367e65d9541204fd75d9541014ff74d9541014fd74d95415267f54d95415267d54d9541024fe73d9541004fd73d9541024fc73d95411367f53d954101cfe72d9541004fd72d954101cfc72d95410067e52d95411367c52d954102cff71d954102cfd71d95415167f51d95415167d51d954100cfe70d9541004fd70d954100cfc70d95411367f50d9541034ff76595411367c655954150dbf745954151df77159541514ff75595410067f755954150cff7459541006bf745954150cbf7459541004ff7359541024fe7359541024fc7359541004ff725954101cfe725954101cfc7259541204ff7159541006f77159541004ff705954100cfe705954100cfc7059541024fe76d8d4112ede63d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4112ede43d8d41506dd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4102cfd71d8d414a6df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41506bf40d8d4112edc6358d414fdf77158d41004ff7654d41004fe7654d41004fc7654d410067f6554d410367c6554d41015bc7650d41026bc7650d41014bc7650d411d6be6550d411d6bc6550d4102dbf7350d4102f9f7350d410079f6350d41026be6350d41026bc6350d4112f9c6350d4112f9e5350d410079d5350d41007b77150d41015be7150d41015bc7150d411c7b47150d4102ebf6150d4102fb76150d411c7b65150d411c79f3150d41005bf7050d4101cfe76d8941126ee62d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d89414f6bf43d8941006bd43d8941126ee42d89414f6ed42d894102cfd71d894144ef651d89414f6f741d894144ebe41d894144ebc41d894144ef441d894144eef21d894100cfe70d8941004fd70d894100cfc70d89414f6bf40d89410057f75589411357c7558941126ec62589414edf77158941004ff7654941004fe7654941004fc7654941004ff764c941004fe764c941004fc764c94102df47654541036f4765454102cf47654541015f77554541017777554541007776554541036f66554541036f46554541
  | 13 => 0x9151566bc50d9151006bf30d9151006be30d9151006bc30d9151006bf20d9151006be20d9151006bc20d915150ebf10d915150ebe10d915150ebd10d915150ebc10d9151156bc645915155df7715915150dbe7619151156be76191511573e75191515573d7519151556bf65191511579e73191511579d7319151006be6319151006bc631915154f3f5319151157ae7219151157ad7219151006be6219151006bc62191510073e521915154f3c5219151557b67119151157b57119151556bf611915154fb751191515573e51191515573c5119151557b45119151557b62119151157ba7019151157b97019151006be6019151006bc601915154f3f50191510157c765515102e7c76551510147c76551510357f74551510373f74551510073f645515102e7e645515102e7c64551511573c64551510057f73551511457e72551511457c72551511573f42551510077771551510157e71551510157c71551512077471551510367f61551510377761551512077641551512077621551510057f7055151024fe76d8d51006bf64d8d51006bc64d8d5114ede63d8d51014fd75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5114ede53d8d51546dd53d8d5101cfe72d8d51004fd72d8d5101cfc72d8d51034fd71d8d514c6df31d8d514c6f621d8d5100cfe70d8d51004fd70d8d5100cfc70d8d515467f50d8d51005bf7458d51155bc7458d51006bf6458d51006bc6458d5114edc6358d5153df77158d510157c7654d510267c7654d510147c7654d510057f7454d510073f6454d511f67e6454d511f67c6454d510073c6454d511f63c6454d510357f7354d510375f7354d510075f6354d510267e6354d510267c6354d5114f5c6354d5114f5e4354d511457e7254d511457c7254d5114f5f3254d51007777154d510157e7154d510157c7154d511e7747154d510367f6154d51037776154d511e7764154d511e7762154d510057f7054d51004ff7650d51004fe7650d51004fc7650d510357e7550d510057d7550d51006bf6450d5102ebc6450d511d73f5450d51026de6350d510075d5350d5101cfe76d89510357e75d89510157d75d8951006bf64d8951006bc64d8951146ee62d89511476e52d8951014fd75d895146e7d75d89510147d75d895102cfe74d8951004fd74d895102cfc74d8951024fe73d8951004fd73d8951024fc73d89515367f53d89510067d53d89511467e52d8951146ee52d8951536ed52d89511467c52d8951034fd71d895146eef21d895100cfe70d8951004fd70d895100cfc70d89515367f50d8951005bf7458951155bc7458951006bf6458951006bc6458951146ec62589511476c525895152df77158951004ff7650951004fe7650951004fc76509510057f75509510357c7550951006bf645095102ebc64509510073
  | 14 => 0x1ccff7259132006ef7259132004ff7159132014fe7159132014fc71591321ceef2159132004ff705913200cfe705913200cfc705913216ebf4059132004ff7655132004fe7655132004fd7655132004fc765513201ddc7654d32036dc7654d3201cdc7654d32025df7554d320275f7554d320075f6554d32036de6554d32036dc6554d321775c6554d32006df6454d32006dd6454d3256f5e5454d321775c5454d32007cf7254d3201dde7254d3201ddc7254d321efcc7254d32026df6254d32027cf6254d321ef5f5254d321ef5d5254d321775f5154d321efcf2154d32005df7054d321775f5054d321efcf2054d32014fe76d8532166f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532024fd72d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d853248edf30d853243eef20d8532166f46158532005fb705853215df8705853200cfe76d813215efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d8132014fe71d8132004fd71d8132014fc71d81322deef21d813215efa40d813215efa30d813215efa20d8132006fb10d813215ef810d813215ef8605813202cfe76d9151156be64d9151014fd75d9151156be54d9151566bd54d9151024fe73d9151004fd73d9151024fc73d9151156bf43d9151006be43d9151156bc43d915101cfe72d9151004fd72d915101cfc72d9151156bf42d9151006be42d9151156bc42d9151034fd71d915150ebf41d915100cfe70d9151004fd70d915100cfc70d9151156bf40d9151006be40d9151156bc40d9151555be76d915102cbe76d915150f3f75d915150f3c75d9151006be63d9151006bc63d91515673f53d9151006be62d9151006bc62d91510073e52d91515673c52d9151567b771d915150fb471d9151567b751d915150f3e51d915150f3c51d915150fb451d915150fb621d9151006be60d9151006bc60d91515673f50d915150ebf75d9151156be75d915150ebd75d915150ebc75d9151006bf73d9151006be73d9151006bd73d9151006bc73d9151566bf53d9151566be53d9151566bd53d9151566bc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d9151566bf52d9151566be52d9151566bd52d9151566bc52d9151006bf32d9151006be32d9151006bc32d915150ebf71d915150ebe71d915150ebd71d915150ebc71d915150ebf51d915150ebe51d915150ebc51d915150ebf31d915150ebe31d915150ebd31d915150ebc31d915150ebf21d915150ebe21d915150ebd21d915150ebc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d9151566bf50d9151566be50d9151566bd50d
  | 15 => 0xc7150d4218f9f3150d421cfaf2150d42005bf7050d4202dec7654942036ec765494202cec765494201def755494201f6f75549420076f6554942036ee6554942036ec65549421976c6554942007af745494202dee745494202dec74549421b7ac745494201eef645494201faf64549421b7ae5454942197ad54549421976f53549420076d53549421b7af4354942007ad4354942005ef71549425b7ae41549421b7ac41549421976f50549421b7af4054942014fe76d85420067f65d85420067c65d854202dbe74d854201dbd74d8542186f661d8542187b641d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542186bd74d854201cbd74d8542024fe73d8542004fd73d8542024fc73d85424eebf43d8542006bd43d854202cfd72d8542186be41d8542186f641d8542186bc41d8542186f621d854200cfe70d8542004fd70d854200cfc70d85424eebf40d85420057f75585421957c75585420067f65585420067c6558542186f46158542187b4415854200cfe76d81420067f65d81420067c65d814217efa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d814239ebf43d8142006bd43d814202cfd72d8142014fe71d8142004fd71d8142014fc71d81422feef21d814217efa40d814217efa20d81420057f75581421957c75581420067f65581420067c655814217ef86058142034fe76d95321767e65d95321ecfd75d953202cfe74d9532004fd74d953202cfc74d95320067e54d95321767c54d953201cff73d953201cfd73d95325ae7f53d95325ae7d53d9532024ff72d9532024fd72d953259e7f52d953259e7d52d9532014fe71d9532004fd71d9532014fc71d95321767f51d953200cfe70d9532004fd70d953200cfc70d9532034ff76595321767c6559532595df73595325a5ef725953259cff75595320067f7559532004ff745953202cfe745953202cfc7459532594ff7359532006df73595321ecff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff705953200cfe705953200cfc70595321767f505953202cfe76d913216ebe64d9132034fe75d9132004fd75d9132034fc75d91321ccfd74d913201cff73d913201cfd73d913258ede53d913258ebf43d913258ebd43d9132024ff72d9132024fd72d913257ebf42d913257ebd42d9132014fe71d9132004fd71d9132014fc71d913257eef21d913200cfe70d9132004fd70d913200cfc70d913202cff76591320057f75591321757c755913216ebc6459132575df7359132585ef7259132004ff75591320067f75591320047f7559132034fe7559132034fc75591320067c75591320347c755913257cff7459132006bf7459132574ff7359132006df735913218ede5359132
  | 16 => 0x95425de7e42d95425de7c42d95425de7f32d95425de7e32d95425de7d32d95425de7c32d95420067f71d95420067e71d95420067d71d95420067c71d95425f67f41d95425f67e41d95425f67d41d95425f67c41d95420067f31d95420067e31d95420067c31d95425de7f21d95425de7e21d95425de7d21d95425de7c21d95420067f70d95420067e70d95420067d70d95420067c70d95425f67f40d95425f67e40d95425f67d40d95425f67c40d95420067f30d95420067e30d95420067c30d95425de7f20d95425de7e20d95425de7d20d95425de7c20d95420067f10d95420067e10d95420067c10d9542034ff76595421967c65595425e5bf74595425edef72595425dcff75595420067f75595425e4ff7459542006bf7459542004ff7359542024fe7359542024fc735954220cff7259542006ef7259542004ff7159542014fe7159542014fc7159542004ff705954200cfe705954200cfc70595425dd7e76195421967e76195425dc7e76195425cf3e74195425d73d74195425d67f64195421975e73195421975d73195420067e63195420067c63195425cf3f43195425d76e72195425cf6d72195425d67f62195425cf6f42195425d73e42195425d73c42195425d76c42195421977671195421977571195420067e61195420067c61195420073e41195425cf3c41195425d76f21195421977a70195421977970195420067e60195420067c60195425cf3f401954201dbc7655142036bc765514201cbc765514202dbf755514202f3f75551420073f6555142036be6555142036bc65551421973c6555142005bf7355142007af725514201dbe725514201dbc725514220fac725514202ebf625514202faf625514220fae5255142185be7155142185bc71551421973f515514220faf2155142005bf7055142024fe76d8d420067f65d8d420067c65d8d4218ede63d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d4218ede43d8d425c6dd43d8d4202cfd72d8d42576df32d8d42014fe71d8d42004fd71d8d42014fc71d8d42576ef21d8d4200cfe70d8d42004fd70d8d4200cfc70d8d425c6bf40d8d420057f7558d421957c7558d420067f6558d420067c6558d4218edc6358d425bdef7258d42004ff7654d42004fe7654d42004fc7654d420067f6554d420367c6554d4202dbe7454d421f73e5454d42026de6354d4201dbc7650d42026bc7650d4201cbc7650d42005bf7550d42005bd7550d420073f6550d421d6be6550d421d6bc6550d420073c6550d421d63c6550d4202dbf7350d4202f9f7350d420079f6350d42026be6350d42026bc6350d4218f9c6350d4218f9e5350d420079d5350d42007af7250d4201dbe7250d4201dbc7250d421cfac7250d4202ebf6250d4202faf6250d421cfae5250d42185be7150d42185b
  | 17 => 0x1b6bf43d9152034fd72d91525e6bf42d9152014fe71d9152004fd71d9152014fc71d9152006be41d91521b6bc41d915200cfe70d9152004fd70d915200cfc70d91521b6bf40d91521b6bc645915260def7259152024fe76d8d521aede63d8d5201cfd75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521aede53d8d52606dd53d8d52034fd72d8d52596df32d8d52014fe71d8d52004fd71d8d52014fc71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d526067f50d8d521aedc6358d525fdef7258d5201d7c7654d520267c7654d5201c7c7654d521f67e6454d521f67c6454d520357f7354d520375f7354d520075f6354d520267e6354d520267c6354d521af5c6354d521af5e4354d520076f7254d5201d7e7254d5201d7c7254d521ef6c7254d520367f6254d520376f6254d521ef6e4254d521ef5f3254d520057f7054d52004ff7650d52004fe7650d52004fc7650d52006bf6450d5202ebc6450d520075d5350d52014fe76d85521a6f661d855201cfd75d855202cfe74d8552004fd74d855202cfc74d8552024fe73d8552004fd73d8552024fc73d855252e7f53d85520067d53d8552034fd72d855252eef52d855247e7e52d855247e7c52d855247eec52d855247eee42d85521a6f651d85521a6f621d855200cfe70d8552004fd70d855200cfc70d855252e7f50d8552005bf74585521b5bc74585521a6f4615855200cfe76d815219efa60d815201cfd75d815202cfe74d8152004fd74d815202cfc74d8152024fe73d8152004fd73d8152024fc73d81523ee7f53d81520067d53d8152034fd72d8152014fe71d8152004fd71d8152014fc71d815219efa50d815219efa20d815219ef86058152034fe76d95421967e65d954220cfd75d954201cff74d954201cfd74d95425f67f54d95425f67d54d9542024fe73d9542004fd73d9542024fc73d95421967f53d95420067e53d95421967c53d954202cff72d954202cfd72d95425de7f52d95425de7d52d9542014fe71d9542004fd71d9542014fc71d95421967f51d95420067e51d95421967c51d954200cfe70d9542004fd70d954200cfc70d95421967f50d95420067e50d95421967c50d95425d57e76d95420347e76d95425df3f74d95425df3c74d95420067e63d95420067c63d95425f73f43d95425f76f72d95425df6c72d95425f76f42d95425df3e42d95425df3c42d95425df6c42d95420067e61d95420067c61d95420073e41d95425f73c41d95425df6f21d95420067e60d95420067c60d95425f73f40d95425de7f74d95425f67e74d95425de7d74d95425de7c74d95420067f73d95420067e73d95420067d73d95420067c73d95425f67f43d95425f67e43d95425f67d43d95425f67c43d95425de7f72d95425de7e72d95425de7d72d95425de7c72d95425de7f42d
  | 18 => 0xe72d8153004fd72d815301cfc72d81533fe7f52d815337edf32d8153014fe71d8153004fd71d8153014fc71d81533fe7f51d81531defa50d81531defa30d8153005ef72581531edec72581531def86058153034fe76d95431d67e65d954302dbe74d9543025bd74d95431d73f54d9543214fd75d9543024ff74d9543024fd74d9543626bd74d9543024bd74d95436367f54d95431d6bf54d95431d63f54d95436367d54d9543636bc54d954302cff73d954302cfd73d95436267f53d95436267d53d954301cfe72d9543004fd72d954301cfc72d95430067e52d95431d67c52d9543636bf42d9543014fe71d9543004fd71d9543014fc71d954300cfe70d9543004fd70d954300cfc70d95431d67f50d9543034ff76595431d67c655954361dbf74595431f73c545954362ddf7359543624ff75595430067f755954361cff7459543006bf74595431d6bf54595431f67e54595431f67c54595431f6bc5459543214ff7359543006df7359543004ff725954301cfe725954301cfc72595431f6bf4259543004ff7159543014fe7159543014fc71595431d67f5159543004ff705954300cfe705954300cfc705954302ddc7654d43036dc7654d4302cdc7654d43025df7554d430275f7554d430075f6554d43036de6554d43036dc6554d431d75c6554d430079f7454d4302dde7454d4302ddc7454d431f79c7454d43026df6454d430279f6454d431d79f5454d431f75e5454d431f75c5454d431f79c5454d431f71c5454d431d75f5254d431f79f4254d43005df7154d431d75f5154d431f79f4154d431d75f5054d431f79f4054d4301cfe76d89431ceee62d8943034fe75d8943004fd75d8943034fc75d8943024fd74d894302cfd73d8943586de53d8943006dd53d89431ceee42d89431ceee32d8943014fe71d8943004fd71d8943014fc71d894300cfe70d8943004fd70d894300cfc70d89435bebf40d89430057f75589431d57c75589431ceec6258943014fe76d85431c6f661d8543034fe75d8543004fd75d8543034fc75d8543024fd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d85431c6f641d85431c6f631d85431c6f621d854300cfe70d8543004fd70d854300cfc70d85434febf40d8543006f610d85431c6f410d85431c6f4615854300cfe76d81431befa60d8143034fe75d8143004fd75d8143034fc75d8143024fd74d8143006bf54d81433aebc54d814302cfd73d814301cfe72d8143004fd72d814301cfc72d81433aebf42d8143014fe71d8143004fd71d8143014fc71d81433aebf41d814335edf31d81431befa40d81431befa30d8143005f771581431c5f471581431bef8605814302cfe76d91521b6be64d915201cfd75d91521b6be54d9152616bd54d9152024fe73d9152004fd73d9152024fc73d9152
  | 19 => 0xb00000040120040008014004000000000c0020020008000000000001000000400200000280040090000020002001000800000000100100040000010000004002000000000c000000024fe76d8d54216de63d8d5402cfd75d8d54034fd74d8d5463ebf54d8d5462e7e54d8d5462e7c54d8d5462ebc54d8d54216de53d8d54216de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d5462ebf42d8d54014fe71d8d54004fd71d8d54014fc71d8d5463e7f51d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54216dc6358d5401cfe76d895420eee62d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d895420eee52d895420eee42d8954014fe71d8954004fd71d8954014fc71d895420eef21d895400cfe70d8954004fd70d895400cfc70d895420eec6258954014fe76d8554206f661d855402cfd75d8554034fd74d8554024fe73d8554004fd73d8554024fc73d855401cfe72d8554004fd72d855401cfc72d8554206f651d8554206f641d8554206f621d855400cfe70d8554004fd70d855400cfc70d8554206f4615855400cfe76d81541fefa60d815402cfd75d8154034fd74d815440ebf54d81543ce7e54d81543ce7c54d81543cebc54d8154024fe73d8154004fd73d8154024fc73d815401cfe72d8154004fd72d815401cfc72d81543cebf42d8154014fe71d8154004fd71d8154014fc71d815440e7f51d81541fefa50d81541fefa40d81541fef8605815402cfe76d91530357e75d91530257d75d91531f6be64d91531f73e54d9153024fd75d915361e7d75d91530247d75d91531f67e54d91531f6be54d91531f63e54d9153646bd54d91531f67c54d9153034fd73d915361ebf43d915301cfe72d9153004fd72d915301cfc72d9153014fe71d9153004fd71d9153014fc71d91536467f51d9153006be41d91531f6bc41d915300cfe70d9153004fd70d915300cfc70d91531f6bf40d91531f6bc64591531f73c545915363ddf735915301cfe76d89531eeee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d89531eeee52d89531eeee32d8953014fe71d8953004fd71d8953014fc71d89531eeef21d895300cfe70d8953004fd70d895300cfc70d89535fe7f50d8953006ee20d89531eeec20d89531eeec6258953014fe76d85531e6f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d85534d6de43d855301cfe72d8553004fd72d855301cfc72d85531e6f651d85531e6f631d855300cfe70d8553004fd70d855300cfc70d855353e7f50d8553005bf74585531f5bc74585531e6f4615855300cfe76d81531defa60d8153024fd75d815302cfe74d8153004fd74d815302cfc74d81530067e54d81533fe7c54d8153034fd73d815301cf
  | 20 => 0x10004002000000800400000200000000020000020000002001000800c000001000000000000800100000040000008000000002000800c00400100000000000000000000000000003800000000200080000040030000004000001001003400600300000000020020008000004000000000000200100000000080030020000000000000001000800600180040000010010004008008001000000400100000080000000000004016000000800c000003000000400200300000080000020010000000006000000000c00000000000040000008000004000000000000000a00100200040000030000006001000800000000000180040000000000020004000004800400c004000800000400600000040080000018004006004000803c0000010000004000001000000800000000080300000010000000004000000803c002001000800800a00000080080020030000004000001000800400a000005800c002006000000400000300280000000010000004004000000800400200000000000000010040000002000000000000000400480000000010008004002000004002c0000000000004008000000800000000100000000020000000000006000001800800c006003000400400300100000040010010000008001000000000400100100080000000000008000000004000000400300280080020030020000000001002800000000000000000000000010018000002000000000200a0008004008000007000c002000000001c002005000800000200400080140000000020024004000002000c00400400d00000020040000004000006000000000a001000000400200000480200000000060000002006001800400c001000003400200200080040000010000010000000000800000000000380000060000000000002001000001400200b0000008002002000000800400100100000060050048028004000003001800000a0000010000002000000400800200000240000000000014002000001001000000300080040000030010008006000001800c00200000080080160030000000000003001000000000000280180040000008000004004002800400000200000040040010000004000000000800000200300480040000010010004000002003800c000000000001c0000010000014000001000000000000000000000020070048008000000001800c000003001001400400000000000000000000014004001000000c010000000000000a001000800400000000000040060030000000012003000800400600100200040000010010018000004000800800000000000000080010000000000002001000000000f001800000c0020020000012005000000000a00300000100020000018004000004004000400600a002800000e002000800000000000500000
  | 21 => 0x5c25b949d0000af0267000000141e0000002b8400018c000000000000000000000000003d2339800011b0000aa86ea000129944124a000000082198a00000000000001755bda61ce5c0000000000c3052a2b4800000030352e800000a1e52c197100007bf000000102a106655800169482d00003e88a013600000000000000000000000000449989808458600026200003e9476018c75a000000000000000018c800000056800000000003942a38e60000c035b631c5452a8a0002374c0600000027f46664830f02d38000000273800000000000000000000000da8000000ce260902b591e2b63588b192ae0000000e480000002c6000000000000000000002d15400000000000116afbc00000000000019760003b0000000000280040020080000008000005000803400a000001001400200000080000000000008000002002000800001c000000802c00400100000000020110000014000000000801c0180020000000002002000000800e000003000c006000000000c00200000000000000000000004002000000800000200400700180000000010000002001000002c0000060018004006001000000000000100180080020010000004002008000001000600400000080000000000000004000000000c000000000002000400000000100020000000004000000001000000200100080000000000018020000001006000800000000000000060020030010000002000000400800000000100140000000000000000002800c000001000800000200100080000000000058008000005000000c004007000000000000100000000000010000000000002000001400000000000000020020028000000000000000400a0000008024006004000000000400100500040000000080004004001001800000000000080000080000020000000000000000800000000000240020000008000002001000800000c000000000800c00200380000100050000000008002000000c00200000000000000040008020004003000000000400000000000040000000000002000003800400e00100000080020000008008000000002000800c0030018000004000000000c000001003800000a000000000c0000010020000000000003000c000001000001400000400100040000000000000000000006005c00000f000000000000300080040060010008000000001003003800800200000000060010008000012002006000000200000000040040010000020000004000000800200300000000000010000000002003001000c0040010010000000001000000400800000000040020030000008000000001000c00200100100040020000010004002003002000000200600000040060000000000000001000000400a0010000018000003000000000400100000040040010
  | 22 => 0x738000321434a7b811419c800000006a919825410c0000000000743000000000000000028b50fcb1a52290b46b600056e0b340000006a20000000b2d650800000000000000000006550000df87620004a30158c80b0c61088d45e0ac300000013120000d1250c0000000002d4000075b000165099a5ba179a69883800069a8f640008683d708ad24c000000000000000000000006b200000000000006215e7800000027f0001a1c0003bd00000000009a9348a7f81be83832089002a46ff0000000000000000000000000000013f400008b4c994c568a00000028e8000a92000000000022755b1b64970cec12e1dac000000553000000000000000015b094d31100017da25054082ac54495235f0e552840003ba0000c2ed1c653ac340000002792af4b9ac8000002d059e38e31497b400096800000018900000920064000000470ab5817c0000000000000000000000000090019e80000000000000000000897000000062e0000000000000a9764900008100000000000000a730000384338c640000000000b4d0000000000be800000013b26c869b8638412000417b3d097aa02027a3356d05420003034000000000161d4865df3aba580c98b9f1fb34e8110c0239a0000000a5f22188f008c4fb00034fc5520005bea8a96c20000001ff800000000017680000600e880000009c331a000059005d000000037c5f41868000eca0000000000000000000278800000000000e01a6000383000000000000000003621fd2f588388f64f00001b14a640005a331a0000ac2000000164ad390003104000000512000196e00000001dc0000000000000000bb72361371202000000191cfe00000000000000000000000155aa4e00005f0000886127000000093700000005084770000000000b3c0000000000278363000192c98b0002888000abb000273868c000089860cb78a945088094046000214909400000023e83b40002cc28080000000000000000000b245bb0000adc00000009f000093e3730000820551000000186200038a8464000c0900000013c864b0002b200000000000dc10aa83f2200000a361a7000000129664215fabe1272000206a32c000c3d00031613b400000000012c24332048f391581570001ec800066262f2c0555c0000001e640000000000ea400067a0002b8800033f0000000e801b6311800000008500021947387fc35d000000000000022800006f8000000000015500024d8ea4000128a6040000000001c88f50b6b00021f4000cfc303800000049d00000010ec33c3471b0c50e00301b800000000000000006760001021bd0b862bd0000001692000000203c000ad13789cecb089c96999098daa00000017f92c41db3c90ae400000000012c00007f81d293dcbf4000000000000000016daf597680000a502c00001a42220
  | 23 => 0x858c4060002070db83762ef474a1ec00000029100000007010000265630000000000000052c176a058dce000614800000000000000006443b8688252000065469a00016960000000000000000543a984142000000000119c0004a70000000000000053000059321a800000000000000000000000001014000891082800000099a0000000bdc00000000000000003f40b0cab80bf00000007780002670190a3e0002d617300000f7000186856a6790000000000ac5000129c0001b016202d4000000495aca00000000000000000c6a0000ffc000000000000000000000000000000000000000efc000552000054e00000000015500af00000003f800000000000000000000000f6000000000007820002b306400000002228000b38428000237c000000000042400091b43200000006e900004203280001fa8000000a1e3d9800000000000032400008d9000338c0004170ea036d45600000000000006b229c1bac3cc00000000001fe0003cb8001a3e1d75ae09ac000bc30000790000c9c1ea0f5cbea00000000007e42313e200000000000000001146000000240800086b4f406e8000000000000000000004d8000e7e00000000003d200000001480000000001cd4ab40003bc8000000ba457384444f20000000000000000295a6b000000061a00000008c042b00017e400000000000240000000000000b30616800055080d2ae926496a88259b00000001f5466005400027a4cd800000041800015d575600000009b461032017b342c26083000000000000000e58a4c2f680e000281c368000000241000080000010647f200000000000007be000000000000034c00000b40004fc24700001610000001a520000000001a3ccd660f0000b440002d20000dae00034e800000000000000000008b800004740002440002238d3600000017418f05c01e621d18f20000000bd56120000002d10000921000000197e0000a29558000a9e0001799a62000588800044c0320000d400000003c880000000001fc000000000060a800000000000008440004ed1b19a40000000000000000022f00033483e6cda00000017741d0638049800045800029ac00000000000000008633c080000000000000f80000000000000000000062b800173c0f02400ae00000005fb2c280001d913116659b08fe5db00013182d200000000004360000000000cdf17baecce0e0005d700006825cf4d11a9c2d60000000cd45a09df00008955940000000001046ab02a226f80004ac336027ca7600057e1d880005ce00024a59d472c5042aac1020001d1a9a4000000000000018e0ae0001c20b66307623a814000000000000000008c0000000000aa90001f040004ee11080000008453d00000d9a07c0001ef4000ca21f3800000000000000000000fb0001bb13c0ba903f1018ece
  | 24 => 0x156c0002001b501ac000000000244873c0005df1a6400000059f000151600000001b800000000000000000000000000000000472a4b58dc0000002f2c000c4a0000000000000000000179c00000024d40000002110ee800000000000000000000001a4c1280003fa00000208af000000000082a00006f000000025891cc1e46ee5380000c5e7e75fd08b84ec7112a080000006fa0000000000017000000000000034b87ec94c2a500003f000021b0d51c7404200000000007663002c92c3816e81730432051527a700001d841e1f000032e40001c00002abc00000000007e400014100030fc000000236829c000000000000000000036a2eb400000063f335577e00021c21610e0cbd00007613304010000b295e44f82ea00000000000002a6cb3c42a2f3a6b40000000000001a1e91700000010a80003378000000be920faa7c000000000000000087c07307101440000002c7c00004a59880015c8000000000000097705013d9a0c2ff00025d00002b12ef00919101481c3800167e0000001e4caa800000028281949110001c486ac71c06f0000000000000000000058e1330000f440004fe00000000000001e1c0000d40000000000aba000123c000c7c3bba600af80004dd00000001420c6a0c8000d3e000217c000000443971c0000000000000000c0700030b092200000000000500004529f4400005f4871b89a4c8bd3e580457c05c62970000eeacc355f80001080005fa3428426000164af600008d155f34f495a2490000000000b9d06b149c78609c41306840000000000000000b5b4d180000000000000000c6c0001f7800000017100000003fe59b2b093d011200000010480006941db00000004de567800000000000000000009e6000000000000000000000000000000000000000000000000000000000000008bf60faddcba428b0000000000018594800038200057a000000000000000019b800028b00019ba3443e61460cac0000000000018b620002644b6a00063fac0800000000011953e20000000000000000000000000004936e000079e0000d600000003a4000108cee636800012a8fe40f13d797740000da50000005b8000644b460f6a0001848000fbec5926580000000000000000000000000000000000023d16a0000c182d908e40002fd0000560eb23792451754d6a51d67fa948e7c9eb0001494000c4924134b193063915580000000000001abc0000004c1800000000000000000000000002ffd8d602f0002be8bcac37000326c0000000cd000000000006c8000000172187825c0000003a50ba94620002748f358d84021c58000000000000000000000000000000000003db32bd922000665a2c10e23ec2949a2455c290654002400003300028e59a800000000009280003db823538800036583e056e5f05dd
  | 25 => 0x1ba0f4a6d600000000000000000000000000000000132000000028e04600951d59ef0ccc6960000000000000000070c00000000000013f60000000000240000000000000000000012c800000017c3148eda73c61230653d8cae0000d850842333278c690723624c6976120ad095e4058068e23701e2d04f16421000298c000b5535f82088c0000605af04bac74d1808c9c20650d6330000ef600000028c000075142c800000000000029f8764513000201165c15b60e2468000b331e8800000016e00000007369c1000000086200000000019160001a8a1cd6702b40000000a6c00000015c80000a454b000000019d3bfb4104bc15667a800000000021b9f14ac6bc200031180aa0000002dcc0003de6431d5000092a000201400078f00008f80e02fe000000017400032480018c66ae000000000000036d2bd40000000001ca40003e65c491fc00000062b26380000001aa21e0930000000194800000000000000000006670000000a3f000000056000013500002f000000012dc0005f9277800000009000000000000002d8850132c30a25e2c7086400000000000000000002f68000000000000000061d57800000000000000000000000000000000000041480b00005f70000000000ce40002d7800039d0002d64e8c4df02f0000000000699267c000000000000000058800000014a8000261a5bd8bac9d00003cd4b40000000000cf02150000000860b3a65a80000005ea00015d988400000004cc000c100002a24e487e30000a240006300000efc01600000000000000000000d2007ebc70000cd807a5064fa9a3c1fc000000202d7e66a8000047800000000000014948de564849c09064a67996813cac433a983915b6180067ae70fa855e576a3b8bb8ca405da4ec62000000000000009ef000000065e71000031ec000a44000000070c13900011d000000000000000001465fda234000000052848c19a6ce09609648c45795b22ac457800016ca1287dab632249e5400037200000000000003bd0000000afe20500000003bb26480000000000000000e6c000675a88409a00000000000005b00001fb800000000022f0000000090800000000000000011c6357405000109600000001ecb5c1ed3021becfecc360880a900007630000000000000577296c5cc00047d3154000000486800000000029a8000000000000000025c00000033dd62c00000000007ee9d40000000fe2d48000000000073300034352ba6e04f093745a848941e17293424fc000000078e5f20002e40f908fc0000c580000003ab0000ce6000000000187c66500005f40000002e4800128094a000253c0000000000000e2e21965000002708e4511800000000026880019a27724cb9b74000bf80e500000000003bc0000000a5300000000000002d68000000000000000000
  | 26 => 0xc73a27f8a04f760000000000000730000000025e15f5a10000000000000000000000053c2bf400000000029349e278c0000db158ed1400000004c6b8f00031456a29b605e800000000053900009f42700000408000000000000111ed0307a2fe483a087178b23400000000022b400000064a873c00000000000000000000002e8598807400f800085e9cd00005fc0008f500005cc0000001e400000000000001df4000cf801a854c0000000002d680005be0000a3800014f4139f3c4bea6514ea7e893ca0d000000000072100006f57ea000000213000000000027c0000b4c00034202d000000000000000000000000000000068aa44d0282400027094820004e7adfc1d0ae8000054400000000000000000000000000000000000000000000000000000007ef0000c780000910000001354ca33720000cf8000585b15000000000023cc04000052b8df472c0000001c0c9b078400026ac00084d0002fb00000004b200000003423810000000283409000162a615510000140c54028b92851662730001c580000001b4ac4029c0000002c000000001b680004ae00000007a80000000000a500000000dc29f06860004b28001a44be42759fac0007273782368340920000000035c2f4000178d4dc34b6140000d68000000045ccd4bea00000000001ab0000000000000300800125c00040d000103c6a200009b0000000303000184400000000004ea0000000001288cb84af9db16dc000000202544e000000000000033e000003cd40aa11f23408d3c00027ab51d6ea0004e380015403d00000000000b9a000000021600000011640006b700000008e00003a429008d20000308000000ba82b216fd8ead164e52144000000270917c0ce58a58ca2100000000ee8c7cc20aa309d0fc40000004aab3c9a7803951402e4a5e00000027746568a20000000000b6f00021fc000000000122c0000cb000062cf5400000000000000000000000000b0600000000000000001e08384c0f4102d4cd3e2ce2e100000000000ca8000000b8700032f00000004be90f47ca3640050918e18446196000000050e4ce1294b3000000000009d8000360800116a2f900029a80008ef2d5a57912a7140002e94000ae331e10ac060adf30713103fc6de63980001587e400000000001c94b60a680006c9148800000025500000000000000000000eb8000000117092e0ec11d800000027b00000000008ba0aa000010c00043c859400090c018987c8ec4a265297c5a5a4394850a6c1709cb67d8000000b781320000000000000800000000025c81440006580002dc542c0002a4a69400000000005bd54a875633995c8d024d4c5297136e000387ac78f3cb650002f1400000000000000004ea00000000000003303330f8400000000005c40005178000000ab30000000f3000000
  | 27 => 0x918c74c32378627a41915400039527d000e000632b50c0006840000f1800040b000000113610700000000000003e38000000c1d2c495d19265e83168a200cc2420000000e1c000232000000076f00025658f46f624680016281142bf8b6028e96e53a034955863f3ecb49d74443b5e210e875e000302912000000000028ec40e0000001dc1554cfa56d00000000006061bf400000064a000024a3d65c3190c55eb3953026518666c231005e800000009f12acd8800013480018640005d1800109c0000000ea1656000692ab940007ce16f0ded7ce6d836509c4000d2e00017d80000000f733c40002ee565800000000004d02282fc00032800011300000002c9c9a656f261332400000052400000002a60f8800000070d49880014fe0000000000ca2000000000000000038000012d60000000000d067dd680000000000000033a0c902df129000107a46a3fc800197437700000000003a6000000000000000000010d83a20000001a500000001a1400058d5dc84d000003b00010817dc51e1c0000000069c00000000009d700000000001a8000087476810d096a3816fc31c00000000001c700025c9a220ea000000079400006400017c46636300000000afb000000000000000012d80005bd5dc24bd5bc35521a00000006280000c8d5a0a1c202000106e0000518000cdc00024825f960600000000000000000000000bd20000000000000000000113000016600000000000004c10000000000583abdd4ee55800018300000000000001124bb042babd81800000000000f1c00000000016d20000d480000000000611424974b9100033c007c00000000000000000000001702000000000000000000000000000005cd913c0000001b992d04c240c3ca33b8c8a0e000100014323813d49c4cfaa00000000007fa00000000008bc0000001c2d37200014e00000000004162e089aa0005e880000000000001f98ed42951c508082ce1cd04c31f400072b5021e342380002a18411260ae900018c843e000246000000041a07e92581cebf0613957d2f600020da9248780000000000c7600000000000000000002d0d232170000000033223d45ba0303b4c250b6000000000000000000000000070001a400006918cc800050a41a04c4a4200050ba6fd03085000005b59daa68000033830a44a0ba18a97804270a8000000045100000000000000000928e0a1e700000000007ea0000000eb40000000000000000462000000000020880008ae000000000091c000000000000000029680000008110000000000bd35fb80000003fa0001c7800000000005dc49e45256b903ccec8c20000000000552467aad498ea8c3a61e8c7047ac0000e69a549a8000213cf74390000000123a00000000000008b11a6000000019354328d489a5a72b880000000006a30b68d
  | 28 => 0x5db0002ea8000bc9085000000000041b061d1f607f0000001690000000000151e8ab3348000000a7a5a0269c000057000000043800000000009c8000000011475800000000000000000000000000487000000189a5d900000000009af000000000000044f8000000cca09e01cd3b6bd44458001a2600000025ccedcb2f49223219900831ae000093407260880000004d20000001a1834a162b3d800083526db3043e8903000000000056c1ee0784cb459750e800045400001391e53a60000efb0e90b681431d000000000000006fcd760000000000540d07368a49da5e4a40000000000000000000000000019c0000000000000000000000059b80000009921ea91d400050c0000150b8a31b30f16bcac07ec11103890440000000000648a2566d9cb51d03a0000210ca2ac1300200b524408f07b0000000000000000000099e49900000000005668b580000000001cc400058200000014aa000489a0b9a3400013f03d564cb5835322e5a5637f0000000f2cb1342493f80008c11508034f9a9842b9a4cc5aa5ec50630b865aba04e9044800023400000000003b05d90000000966271000108e63d1d71c680002360001304b905084378400f1234e00011c4a080eb1ff0e3ceba4934a09ca0564000000211150a0001f1800000000000000007e6a3c5d33014000609000000026ecfe0000000f8000000000000000000000000000000000000000000000000000009ff4ba8001a8a00057500000004c65fe2f5c708000000000196c7b11ec2f857b86161c48000d420005a7800161e36f3e51f198340002ebb3f42d40005b3af34622d213358000000a8d000200993265d28d32f995a23f0002ae000039300006580006bc0000000a04acc2db800152a65f0311f402c49bb14600000000000000000424add6280000000000000000000080100000007d61280000001a3200000011840008521028000c4800000000012b000065a2a8800042e4692c6c000388000000000097100000000007e1000000000030400000000000000000001120b92000000000000000000008b6be500000011e000043680009b23054adaec400000000000006c03be00030387e00000000a010d20001ed800000040300000009a80004ae000000000000007c80000000d19f580001791a68018e8a0005ecb46ce4aa5000000000000225758000b0a42400000000000000000a1400019f000000000083e5cb2a6000000014b000173037c000212000018f3469315100000430a530b8200000000000000dd091000000035a000225800000054c80000000003708b9c5ae0000000001534af33ff864400020a5498000642000371b4c027a0002940e9d0eec0012a199d3a26d04b51058c7000063117cc3240e90ef00000009d6637953000000045f00000002c761e254c4206753
  | 29 => 0x62604d40005b8000169800097633680011c43581dc85d80000002208f0800058b4ca80005c00000ae0000d1078605b000196600000000000000000000000a000003160f48a6600047e800111893835c3020546baf00000000006ed666b50116c000000014092a000000000015061156a21697ba00012d000151caff3cd17800e20b345086dc742d1d34aa9b000000029800012d200000000000000003402c20cb29510002dc0e72000145000000000000000004ee6ea00026f400053e3eb9ac064c68b0000000000000000000000000000000000006e50001c616a873d000000072e6f33c1800000001d00000000000000acadd000000025700005045fd19b8534bdead315d13581886d22b81df07d4000634800018251200000016ba00000030e4e3685d0f1a0a0e8200014c883018a68a00022694de881000000000000000014d000016900000000000004520edcafc00033a1444000cc73c528d8000934000000000000000000000000002c898010b80000000000026000000104cb6c0000000000e1281300009593c6000000132922c45a0000001a1c5f800000006180003fa8bb00000004331d900000005891f4c00000057c8c086ba0000fb80000000001fd9d380000000000000000000000251439c8f800031d12a0000570101c9901c603280000009bc1a2a6c800063700000000006bd4da013998c00000030ed9a000000011c8000000307a7d80000000000000000000527800000093c0001ed137087a3fe83bc0000000002db487e867000186d3d20c62371d1c00022000a0c380000000000f4d3b80000000000000cac000000000000000000000000000002c10000000000000000000000000000000000000f100000000002e0c6500003d58868000a5133d800000060a29b94805c6000622a9e4000000000000000037a2c02f7d6400e508714e41ae03600000000000000000100c9c00000000010dc6db0000000ebc9f2000266400038d553800000000027980000000004a39fed854000000000000000000000008de79b0002f18b684880002094000000000243c00068c6438cc000060b4350000b4602967080000006df00b154000065c000000062800000020205d059a48ab3a400037625400000004c05418000a7800050f800198088900000000007580001f60d340005e606e4eec30b1c1ab041f2b84469800095e00050db0512fe000000043d16800000013401989de192a215808a843e49514ba26cc441800160a0003ef00018ee4141fa00000000001b300008ba00000020c40000003011ab462410110b000000000000020640003153c2b230c5c5cb16580010560004f38574ad6ab70ee0000000b884c78468000b9500001a143077100026800000000000000b3a9c824f96ed19257a09f8d484ca79c4539a904300476a13184
  | 30 => 0x718d3b00e07e84bacde329890cc6600047c99184b6a9c625912c43c00004721c80005a54c280013f215e00000000005230000f000b609d2fd800000090b000242029200000000000003e20000000000000000000000000037c81b400000000033bc53e00040810794667da48f225000061c233a7a95d823a4962d5d76ac6d00000011d6000641800173201e00014e857c00000000018600004e319c552006a0000000f5a000000000000036b00000000002e5000000000000063b00000000000000d7c276caa000000000000000000000002ac000091c000000000000171c6c764f80017140000000000a9c70469b114c12400000000017160000000000464bde00000000000001f400000000000002ef4000720000201cc4a298000045800000000000000000000158000000bfd00000000003df0000000000000000000000095a00025e5a02c4e3b086797e28bb0000000ea000010580016d400000000004dc5550000001654ac633080000005242beaf4000083b64f0f2c00000022100000000004d200000009701a0000168e0003f100000000000000000000000000138c0008461fe0000000b35000000000083a0000000000000000000000000000000000f4000000231800000037f183596000000000005664cc00011acfa4562250092d7262600002105194000692000000075f00000000000004849aa800000000000000007c30000000000000000000000000000000000000000002b4800067e31f0000d9e0004a48dd090200037b80016440000001654000c5a0e600006300000000960c2600046c00017a400000000000006316a0800000089900003400000000000000000a1052c01d4c5600000000019ce00000000000004d73493018000bca62012180004a91790e148f88f632f050c4700004300c187920003a5b208000c5b0f600006a60000000000000a66000174c00000055cb33c65273200000000000000000000a3200046b80016c0c200000000000a12004000016249b124000122805c351a36d38a07d59a00000001af0000000000a1a00000000000001b88000e5e7424bc28c8446b7a000284c000000577800135c4bf0000098000c230001a948fc000000302800039f1970000000c165590e457006b6000000000000051a3229080a2c16e80000000000000000000780322285030214b000000000066425d8000e8800046380000000000000ba400000000000004fa00040e845400089e021a3fca7ecd75b3136800089d10315340007b9000074d59c0000c48000000000000159ce92000000000000057b66c989d4b200005924a000000000000000000000002cec0008e746b00000008ae20000000001320001fcc12c000287800000000000000000000000002700000cd300019353dc0002cb00007ba0005d629780de8f4
  | 31 => 0x19c12460000000cc499e1c53d318487b491800000000001ad0000068000000000000000000040d800019200000023c547c000000000167ac353f680009c000000000e84e82d337796854060004ec0164000a26000000000000000000016a4a6400000000000001f080000004e661c0000aca00000007ac36422c16129085f8a7600000015880003c4000000063500000001b800002600000000005eda82c00000000000013629b30000000000000000000000066800002a80000000002df00000004031159a0aa561260ea800000014b8000000000000000000000000000000000000002854cb653d0c40000068abc0f78b0400011f24e066cdea0000000000e3ea674ea8d948c69675ea92ccb200000000000a9ecb20000001952a7b34100000000002ff80000000000000001038726000074800000058ea7cc0004a3000140c00028f57322219c085327c80008a800046a8000000d1700000005808d400000000006ac000305c0000690000001138000517000000000000000000000000002c5c00000000000019f2b974aa0000feeab400000000006c0000000000000065884a405c6fc00012100000004d82674000000354921520e0005b9000000000000000018be1442238000000000122952c00000000008340001820000000088bfe000066055a8c34019acc4d0a3d5388d3d91c2290000ca80005144da8000a0e0000002c840000000000f1400026f14f25e800000000028240007550000000000000000014c0002410003098f20a6d06c00005d60003cf800140281f5c6800000039900000000007db00000000000000000b9000054600000019ca00000000004020000000000000000000000000098600000000007e90000001a240002cfb06c000a465ab000000052647680000000000001c653ee67d33b830cd566f21a4963da705570f4237188800000000015e24780000000000ac0629800000000000022c8d7242c2fe298850cd152f0810553a4e50d985680000000000a3572800000009c98b818a2bb800122000064b82f039082100000000000000d315b4668b790000000000000000247ced00ee65300000002fa00033098e40000c30000000000468000000000000000000000000002f8c0001d50001f9400000000016a4000000000000067479d10b82781c600000000015104150000000000000000000000096d0002b5400000000000009d097c00000000008c5000000032e43e05480000000000000000000a82000000000012b3b301b11d44555070000bc400017da9d400000059600000009ed04023995b233953e8000fb80004ab00000360000001cdc000a3700000000005810eb152814c0004e630ad27e67f479293000000000000000000002d51f80000b230000ed4000118431000000085e0001d3cab21f62272e3
  | 32 => 0xa9055310a000005400002c2228448a475af80017d66d30001790924164189a58c0000000fc00000000000001da400000047b800000000000030bc00000030a22986ce00028e01e00000004540000096c845de0000576000282b2683080001af0000f4200000000000003ee000024c0007fa0000a48000a4b285b0057cc9d049e81e400070a41992f8ad4b32000000170a00000000000000000f12e9c00000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87d851d9214c00b17d083b242980022f61076485300066c180ec90a60018dc865cd214c0033b100b9a42980030f5d254d95200343f43eeab22400087f855d954480010ff0aba6c69001a1f21574d8d2000477c12eca9a400487c8759553480010ff0abb2869001a1f2157650d200047bc0aeca1a40028f4815d943480091790eb2286900ea8f2156450d200254e41ac8a1a40058de87d8d43480051d904baec2900162fa1276545200045ec24eca8a400287e87d955148001878e9b2aa29000ab9a0764485200147643ac890a401ea6c855912148001b9461b9a42900063b21973485200076318ec690a40028ec8758d214803dcc8caa8a429015ae921151485200353d42ec8a8240068f8875915048001e92a6992a09001b1e1d951541202ad9c422a2a8240009e88748550480079d0ec90aa090003d8545215412001c7c432ea9824004ada86d8d30480037910e992609000f7221d324c12000de5432649824001bc8864c93048009d910c9926090006b2219324c12002765bb2649824003dca764c93048007b90ec9926090013b21d9324c120006e5baa649824000dc9754c93048001797029926090012b620f614c12000764996c29824000ad8864c530480017930690a6090003f04c5214c12002c5f43ee8b2a2000c3d75d53644400117f08bb2a8880022fe1175d8d1002c5e422ebb1a20008bf845d9534400b17908bb2a6880023be097654d1001c76412eca9a200487c87595534407d47908b2aa6880129720d6554d100346f43ec6a9a20008f7815d943440091790eb22868800a3d20574d89100246f43ee6b1220018fa87dc162440019b0e7b82c4880022fe11765491002c5e422eca9220008df835d952440091b906bb2a48801a1fa1676509100043ec2ceca12200087f855d9424400d0f90abb2848800237e0d76509100246e41aeca1220038be87d914244001878ebb22848800237e0d764c9100047dc02ec99220048ec8758932440091e90eb12628800eb9a0b654851001c7a43aca90a201dab4845952144001ba461b9a42880063d219734851000763196c690a20038f48758d21440896c90aa124288077a9191424851002d5d426caa0220058f887595404400b970eca12808810ece2154250110007c8a1a62a0220009f08748540440059e0ec90a8088003e850921501100147c432e89822004ada86d8d30440095b107b1260880123e21d624c1100256c41ac49822000ad8864c93044001d92c49926088006f421d314c110016e843a629822001bd2864c530440037a10c98a6088013b4219314c11000d68432629822004ed3764c53044005ba4ec98a608800b741d9314c110027683b2629822000dd3744c53044001ba2e898a6088002f4e09314c11000769b12629822000ed1624c530440017a30690a6088003f04c9214c110
  | 1 => 0x90ea9a86a80fb871915350d5000726a9e65b12a0008bf845c7625400b17908b8ec4a801a1f21476509500061f2a0eca12a00187e86dd542540032f501baa84a801a5b21d525095000c3e432ea992a00287c855cb615403527d0fba2a2a82870f1db74545500069c386e8a8aa0aac3c761d15154035878e9b22a2a80038d90764545500061e3a6c6a8aa000d3874dc151540030fd0dbaa82a801a5d21d515055000c3e432ea98aa01a93c845d531540032f100baa62a801a3ea1b704c55000c3e432ea90aa01a93c845d521540051dd0fb1242a8332cd211514855014732312a290aa000a3d8494b655019787eebba2caa00122f21175d8d400243f43ecaa9a80018be86dd1535000187ecbba2a6a00166721d5350d401d70e32aa6a1a8000db210dc5435000717908b8ec4a00062fa1b74549405cc9f43eeaa1280bbc3c76dd54250001a70e1baa84a02eb0f1d875509400b61e3aecaa128000e2e52d9542500071790eb2a84a00030f1d7635094002cd643aa4a128000d3875dc142500031790cba264a005a4f215744c94000cdc402e899280058fa86dc132500010ff0ab96c2a001a1f21572d85400074aa1e63b0a80058bc841d9515000187ea83b2a2a000a1f21d655454000c5f436e8a8a80019ba80dd1515000b3690ea8a82a00062f219744c54000c5e432e890a801693c855d121501956590aa1242a00c3a9185424854001c7b43ec290a80c9b3a85dd1505000d8f0eca9aa0a006ace211535414002e5c3b286a828016b388550d5050001e32a6a1aa0a006ace21152541400b59c42a84a828000f2952509505003567108a8aa0a005ace215415414000798a8a82a828000d98305d3654c00b17f0eba6ca98003720c372595300051f426eab2a6000c3f74951654c1778d8e52a2ca9800e3ba1f7259530006ac182ebb22600687f875d7644c001ba061b8ac8980028fa1774591300061fbaea8b2260a1cb471d51644c0051ed0fb8ac8980021f61676551300045ec24ecaa260008ef825d9544c0071d904bb2a8980023de0576551300147a40aecaa260008f7815d3624c0051e902ba6c4980162fa1276549300045ec24eca92600387c87595524c0074d904b2aa49801a1fa1676509300043ec2ceca126000d5830dd5424c0071790eb2284980030f1d564509301855a40ac8a1260058ee87d89424c0018d8ebb12849800e3721d654c93000cec406e299260019da87dc1324c0011df04baec29800e3b20975d853002c5f424eca8a60008bd849d9514c0050f90eb2aa2980030f1d1655453014536412caa8a6000d9830dd1514c00d1ed0fb0aa2980032d1d361545300343f42ceca0a600087d859d9414c0051790eb22829800aad20564505300146e43ac898a60019d880dc9314c0033b50fb826298003360c376485300343f428ec90a6000
  | 2 => 0xf64509510061fbaec8a12a2acc3c75d91425440d2790eaa284a88168f21954509510061e3b2a8a12a2058be84dd9325440117b09bb264a880a1fa1b754c9510061e326ea992a20695c8754d325455bc38c8a9a64a89e70f1d464d815100c3e42ae9b02a2a18bc86dd1605440117d0fb22c0a88022fa1c64581516a61fbaee8b2a82a18bf845d763504090fd0fb2aa6a08eb871955350d411565a3b6e8a8a8206c747654d515040b968eca1aa2a0803c554d43545410353b42ec4a8a82a18bf845d7605040317908baec0a08162fa1f74595310061ebaea9b2262008bf845d9544c40b53d09b2a86988163721d6550d310343f42ceca12620087d859d9424c40717d0fb2284988030f1d7645093102d4e43286a126293d1c7550d424c40117f08baec0988162f21175d81310061eba4a9b2a4200a6d82953654840b17d0fba2ca908030fdd474595210061ebaea9b224200ab581d53644840d0fd0fbaac8908030f1d774591210043fc2aecaa242008bf845d954484051dd0db92a89080e3da1b71551210045fc22ebb1a42058bc845d763484010ff0aba6c69081a1f21574d8d2100c7d43ee0b1a4200cdb731c1634840117f08bb2a6908162f2117654d210047dc02eca9a42018f8805d953484090f90eb2aa6908fa8f2116554d2101477436e4a9a420087f855d9434840d0f90abb286908023ee017650d2100c7c402eca1a42048bc8759143484754790ab22869080e3da1b7150d215d4b743eeaa1242bec6c76dd542485a7e4883baa8490ae71b1d87550921006b2388eaa1242d2f24411d5424843d8d8ebb2a84908038b953655092102c7643acaa124200d2c75d9142484073590eaa284908c2e9205545092168e963aa86a124230ba48150d4248401ac8ebb8a84908c2e9a137150921014f340ee899242028ec865d1324843d2d90aba2649080e7321d534c92100566432a69924200de310dc13248401a68e9b2aa290aaa6da1f74545215665a3b6e8a8a42d0f2452dd15148553968ec3a2a290803691c8745452167f92290e8a8a421dcb474d915148401c6ea9b22a29081a3d21d6454521014ba43aa8a8a4228b6482551514859da68e8a9aa2908a2d9209535452166db342ee4a8a4200da474dc951484013c90ea12a29087ad921542545210eed23a284a8a4200f2554509514843d6c90a992a290a13691d13254521007a2a9a64a8a42039e682dd531484071e90cbaa62908766d211754c521014ea43a8698a4200ad48650d31485076c90aa126290877691d1424c521007c2a1a8498a4200de320dc1314840117f08baec0908162f21175d81210043fc2ae9b02420687c855d36048401d9265986c090803b44c730d81210051ec2c83b22a00487c855d36354001ad441b92a6a80061fa1b7550d500245f43ec8a1aa000c3f75d91435400d2b
  | 3 => 0x3b2a8400c7b709c3655097d47d08386caa12ee8f61070d95420043f43861b2a840087d870c3655097d47d08186caa10028f61030d95425dd3741061b2a8400a6d820c365508014ed02186caa10029d60430d95420043f43821b2a840087d87043655097d47d08086caa10028f61010d95420052f41821b2a8400a5d8304365509774dd04086caa10029b60810d95426ee1fbaee8b2a84dca3d8498c65509a54db05308caa136f8d10661195420071a30c8232a84daa3d849806550977878edb2aa8a12e70f1d065d8d420043f43ecab1a840087e87195635080187ca83b2a6a10121fa1f6554d420252f41ecaa9a843ac3c65dd54350801a5ca5baa86a100e2f2197550d425cd1f436caa1a84bbc3c76d954350801c38c7b2a86a12eb0f1d86550d420070e32ec6a1a843ae1c6554d4350801878cbb8286a12fb1b1db6554942036363b2a6a928405cac7650d5250801e1aa6a1aa4a10166ba1371549425de1eba6cbb0a8400e3641d97615097387ce832ec2a12eb0f5d065d85425d636390cbb0a840087e87d9561509a7c6883b2ac2a10021fa1c65585426ce1fba0cab0a84b9c3c7419760509770f90dbaac0a10021fa1f65581420043f438cab028400c3d74953654c80d0fd0fbaac8990021fe1576551320352f42ec8a9a64068dc87591534c8010ff0aba6c09901a1f21574d81320051ec2c87b22a200a3d85903645457d87ced296c8a880327dce73d91515651f428e7b22a2a1a3d851cf645454347b0bb96c8a8a86ada0472d91515655ac08e5b22a2008be870cb645440117b0e196c8a8ab28fa1432d91510051ec2865b22a2a1ab6810cb645440156b02196c8a8802aea0032d91510055cc0065b22a200cbb709c3645455947d0a386c8a8a868f61470d91510045f43861b22a2008bd870c3645455947d0a186c8a88028f61430d91510055741061b22a200aad820c3645454356d02186c8a8802ad60430d91510045f43841b22a2008bd87083645455947d0a106c8a88028f61420d91510054f41841b22a200a9d83083645454356d02106c8a8802ad60420d91516c51ec2cc6322a2d7e2c52988645459f56b03310c8a88038b18a52191516b51ec2cc0322a2a1c3c76d91545458b878ea326c6a88022fa1f6458d510045f438c8b1aa23ec3c64dd15354401a6c83ba2a6a88fa8fa1b6454d5150e1e3b6c8a9aa200e1c63d915354555878ec322a6a8803871936354d510061e326e0a9aa200c3f541d943544050f90cbaa86a88122fa1f6450d510254f41ec8a1aa23ee1c6454d435454387aebb26c4a88038b94b64d89515ce1f3a8c9b12a2aac3d751936254555968e2326c4a88022fa1f645895168716296c8b12a2008be8719162545ab87eea322c4a88031b94876509510065b208eca12a20287e86dd5425457d878c9baa84a880e2fa1
  | 4 => 0x3c20000006e46800000000404844001ed412000000002400011b000000000c480017e158608193e27bcc7a3000000078800082168000000000009122d0000000008928a000278003805f8a51c300a114af842000668bca2501c8b8001621f8000d319c05c000870d40001d40008c0006a8ad1690c4760000002781ec2a8b1000000d6800000000000c6000000001360de0001d1712760000000018604438226202828eb80040e0007ea3729a100fe8d30044f81814423a364921df10a69c45800000000c421f0b6000df89a17a6882580009a52c8e000126914da9f02705a8bb800308540360583c8000c30aa2120001480006e524db91917802c6e9782c05bc6a80c2b6048951f613e2e07a07a456000da000358000b420e0a48a9029f7000000831350be4c82509e3e6000341143a2000faa0c22a89d042490000000000021051c92800426000a980022c3fc930000000000010f1c46ec0d8782220000000029c0000000002e6384b01f008000668000000005100000000000000000000d292e328270758e10008b0980800002748c0002063ccd988726637c5a06b39e0bcf49c90ec298e98af47c430000002141c8ba92d000000001ec3d42b90b0d1114088741211de740f29dd19c3403290737a71cf38001d208c0021702a000000002ca000308ab31a0c4640363305ec3a0013fc500f19374806c405242000000000000001500012b18a0008f00000e000a901e47a3900019000028511a1b000000979461480006b9041b0010040000001400000050000c010010340a00800000010000a0042d0300000c030080701c0a0000001402008000000102c0c0000000009008030000a03c0100c000680303006010060000000400004030000200401018160000001c0000010004020100000c0202c0b018080000c000110080001c020101201c010140b050000300400c0100c1600401000010000100001000000200100801000000000500c0000000000020040200c04000010040101405018010040001010008120000200002000000480500c0003802004050700300400010000040b00802000000080100401000000140202000018010000001404010070055917f08b8ec4aa2fa1fe1572d85540051ec2c83b22a6008bf845c76254c0b17908b8ec4a98028f61252d95436fe1fbaee8b2a86deb1e85dd15350c010ff0ab96c2a181a1f21572d85435dc3fc2ae9b1aa4048be87d91435487dc38c8a9a86a92ee1fe1574d81520051ec24a7b2a8400a3d84943655097387ced20ecaa100317dce73d95425f51f420e7b2a84bba3d841cf655097747b09b8ecaa12ee9ba0871d95425f536c10e3b2a840087e870c765508010fb0e18ecaa12fa8fa1031d95420051ec2063b2a84bba6e820c765508014db0418ecaa10029ea0031d95420053cc006
  | 5 => 0x3f9d438a860c590d41a2b1219ae2ce024fd20b1dc0d47f15c4705647b1db090850761c40867f0ac0f02e62cc5008200062849099000000f308f0003b4fa12339c2040000000003c000000002c8f006d0000001f0ba150000e31cc0008689a000120550002240004083b8000ba600000e0000238000001cc000001ab0005b82319e0481f44d83d0644a40d0e5000000001f840838c0000016a0004a03f10c000b80001d429ccb23f0266440010b35e468ce9633b40acbd2220766c8cc86a0c015cbe00005a000000003e48e86b1eb1601646e220000000db0f90a033c8d8cc348000ae87c0300007d02843a00000161000001149b92d877800000000348000000000000e9a3432654988ca2725d8e10262aa040941e22fa39c828000544487c1be0000009d11f2a22ec000000000e4c12350788c44b96b000000000003528c833800000000001172da8bc0b21004e000569274068f051a153706143981c0d20e012800000000882481e4904001bc000590000003365d0ea89116e000161d2360578a421e12a0005280000014cc38f740255c659cb0bc6a0d0800476598ab0003400000019f0b891ca62064728a06024601a124a080041e5fc0004e32e0185b1fb0f2000898201ea0000012c0c60005f0000008cc0013d000000000c2390000320004242106d8081bc4fc3f18100050cdd0c939a000b90003f2000238210280004c0001b4198288b90007fc000001887701a14f00000000000000000000fb32400122000000000000000000000000043800000000098630000880e220c019d60007b8e503300060c639004002a4220002847040000011a000000003267a000000000000eca2100000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x9000000000000054d0c00000805a74d800000f8a0600025400918038000000e006800000900000000028010850000b8000580083c0000000000000000980009d5a2509948f322c018000071000000005e000000000300000000058a9709000000022000000800000800000003000818300000081f7031d95350d52509a74359790765d85420060d10687d9561509a142d9794b64d89510060b14a87d916254401c265290476509515cc0f26076551425447dc147654d435454172e49a1075dc542485c9926851d37254521144c92615450951484615249755142545210064921d5450951484513449854d325452171f411d1534c951484615849750d424c521716c12154350931484353189854d43541401f7061d95350d50500353289854942541400d4cc261515055050001589920c174d953000564644305d3654c0011ca980c372595300057064430dc9654c001549920c175d913000554644305d7644c0011d2980c371591300057064830dc5644c001549920c375509300055464430dd5424c001834811d564509300060b20874595514c001589920c374545300056464430dd1514c0014c9920c376485300053464430dd9214c0010d9980c0764853000532648301d9214c0014d1910c07648530147181d95148550481c372094545215412000cb2259834853048061ca0765092150110705c82554248540440092c898589324c110024b4261624c530440032d09660d214c110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x8100039a124a921d54509514840101ad49023aac8a12600080b6a4821d16554530
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
  | 68 => 0xb0956
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
  | 85 => 0xa4995
  | 86 => 0xb0995
  | 87 => 0x138b
  | 88 => 0x124b
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
  | 101 => 0x138c
  | 102 => 0x124c
  | 103 => 0x150c
  | 104 => 0x128c
  | 105 => 0x18c9
  | 106 => 0x1789
  | 107 => 0x180c
  | 108 => 0x130c
  | 109 => 0x1a49
  | 110 => 0x17c9
  | 111 => 0x198c
  | 112 => 0x134c
  | 113 => 0x138d
  | 114 => 0x124d
  | 115 => 0x150d
  | 116 => 0x128d
  | 117 => 0x168d
  | 118 => 0x12cd
  | 119 => 0x1a89
  | 120 => 0x1949
  | 121 => 0x198d
  | 122 => 0x134d
  | 123 => 0x138e
  | 124 => 0x124e
  | 125 => 0x150e
  | 126 => 0x128e
  | 127 => 0x168e
  | 128 => 0x12ce
  | 129 => 0x180e
  | 130 => 0x130e
  | 131 => 0xb4b16
  | 132 => 0xccb15
  | 133 => 0x170a
  | 134 => 0x15ca
  | 135 => 0x16cb
  | 136 => 0x144b
  | 137 => 0x188a
  | 138 => 0x160a
  | 139 => 0x184b
  | 140 => 0x148b
  | 141 => 0x1a0a
  | 142 => 0x164a
  | 143 => 0x19cb
  | 144 => 0x14cb
  | 145 => 0x154c
  | 146 => 0x140c
  | 147 => 0xe8b56
  | 148 => 0x18ca
  | 149 => 0x178a
  | 150 => 0x184c
  | 151 => 0x148c
  | 152 => 0x1a4a
  | 153 => 0x17ca
  | 154 => 0x19cc
  | 155 => 0x14cc
  | 156 => 0xbcb93
  | 157 => 0x154d
  | 158 => 0x140d
  | 159 => 0x16cd
  | 160 => 0x144d
  | 161 => 0x1a8a
  | 162 => 0x194a
  | 163 => 0x19cd
  | 164 => 0x14cd
  | 165 => 0x154e
  | 166 => 0x140e
  | 167 => 0x16ce
  | 168 => 0x144e
  | 169 => 0x28e
  | 170 => 0x74a
  | 171 => 0x184e
  | 172 => 0x148e
  | 173 => 0xeccd5
  | 174 => 0x18cb
  | 175 => 0x178b
  | 176 => 0x188c
  | 177 => 0x160c
  | 178 => 0x1a4b
  | 179 => 0x17cb
  | 180 => 0x1a0c
  | 181 => 0x164c
  | 182 => 0xd4d12
  | 183 => 0x170d
  | 184 => 0x15cd
  | 185 => 0x44d
  | 186 => 0x74b
  | 187 => 0x194b
  | 188 => 0x1a8b
  | 189 => 0x1a0d
  | 190 => 0x164d
  | 191 => 0x170e
  | 192 => 0x15ce
  | 193 => 0x188e
  | 194 => 0x160e
  | 195 => 0x1a8c
  | 196 => 0x194c
  | 197 => 0x1a4d
  | 198 => 0x17cd
  | 199 => 0x18ce
  | 200 => 0x178e
  | 201 => 0x749
  | 202 => 0xb0a16
  | 203 => 0x1a9951
  | 204 => 0xb0a55
  | 205 => 0x44a
  | 206 => 0xecb15
  | 207 => 0x28b16
  | 208 => 0x148b16
  | 209 => 0xe8b16
  | 210 => 0x44b15
  | 211 => 0x164b15
  | 212 => 0x1a9952
  | 213 => 0x75652
  | 214 => 0x74a52
  | 215 => 0x154296
  | 216 => 0x74ed2
  | 217 => 0x75493
  | 218 => 0x74a13
  | 219 => 0x140455
  | 220 => 0x74e93
  | 221 => 0x1a9953
  | 222 => 0x74c
  | 223 => 0x1a9954
  | 224 => 0xb0a095e
  | 225 => 0xb0a499d
  | 226 => 0xe8b4b1e
  | 227 => 0xecccb1d
  | 228 => 0x74452
  | 229 => 0x74293
  | 230 => 0xb0455
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1431
  | 6 => 3401
  | 5 => 586
  | 4 => 48
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
  | 6 => packedAt gbK6 (177977+((h/1133+packedAt gbK6 (163248+(h % 1133)*13) 13) % 6572)*13) 13
  | 5 => packedAt gbK5 (36524+((h/195+packedAt gbK5 (34574+(h % 195)*10) 10) % 851)*11) 11
  | 4 => packedAt gbK4 (3472+((h/16+packedAt gbK4 (3360+(h % 16)*7) 7) % 118)*7) 7
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x18e3f1c0e38c7e3f0238383ffff0c19319c07f
  | 1 => 0xe0fc7e00fc0f8fc7ffc03fc1c1f10663267993
  | 2 => 0xff007fff1ff00ff803ffc001fe02087cc78e1c
  | 3 => 0xffff80001ffff00003fffffe000c0f80f80fe0
  | 4 => 0x1ffffffffc000000000ff000fff000
  | 5 => 0xffffffffe000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x820a048208414091008081468c0c09108c025
  | 1 => 0x60445212440082428a40928085210262021892
  | 2 => 0x210014860d100a902a91808114220024470a18
  | 3 => 0x928900201229200041262528000c0d00b00540
  | 4 => 0x41bce4d247003010c18465000fde000
  | 5 => 0xdcf2693880000000800406302189afdb000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffef8feecfea8fffffef8feecfea8fffffef8feecfea8fffffef8feecfea8fffffef8feecfea8fffffef8feecfea8fffffef8feecfea8fffffef8feecfea8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_28152
namespace PEqualNP.Outside.L_meta_28152
open PEqualNP.Outside.L_meta_28152.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 5 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 91 := (concat bs1_4_0 (concat bs1_4_32 bs1_4_64))
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
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 5 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 91 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
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
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 9 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 50 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_128 : Interval s5Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 136 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 48 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_4_32 : Interval gbAtlas 4 32 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 48 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_576 : Interval gbAtlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 586 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)))))
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
theorem bgb_6_3392 : Interval gbAtlas 6 3392 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3401 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)))))) (concat (concat (concat (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528))))) (concat (concat (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)))) (concat (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffefefffffefefffffefafeeefeaafffffefefffffefefffffef8feecfea8fffffefefffffefefffffefafeeefeaafffffefefffffefefffffef8feecfea8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_28152.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[3,8]⟩,⟨.or,[0,2]⟩,⟨.or,[5,6]⟩,⟨.or,[0,1]⟩,⟨.or,[9,12]⟩,⟨.and,[6,4]⟩,⟨.and,[12,8]⟩,⟨.and,[11,10]⟩,⟨.and,[13,7]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_28152

open PEqualNP.Outside.L_meta_28152 in
theorem PEqualNP.Outside.L_meta_28152 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
