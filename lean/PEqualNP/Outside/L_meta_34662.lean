import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_34662.Model
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


end PEqualNP.Outside.L_meta_34662.Model

namespace PEqualNP.Outside.L_meta_34662
open PEqualNP.Outside.L_meta_34662.Model
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

def SBf (j : Nat) : Nat := [4, 6, 6, 7, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_34662

namespace PEqualNP.Outside.L_meta_34662
open PEqualNP.Outside.L_meta_34662.Model
def s0K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (5+((h/1+packedAt s0K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 2 => 0xdbf19f3f1c3f8d9c
  | 4 => 0xffffffffffffffffffffffeffe1fffe03ffe1f
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff40640108248920b1
  | 2 => 0x24ac285909932594
  | 4 => 0x1101502242244a0a
  | 5 => 0xe091ab493064f40
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 54 s0Pos s0Neg, 0xfcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000fcfcccccfcfc0000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_34662
namespace PEqualNP.Outside.L_meta_34662
open PEqualNP.Outside.L_meta_34662.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x2401c000b00d18400f20c08500040a0c138668801bf43bd43bf42ee42bd42ed42ad42ee32ed32bf41bd41ef21ed21be40bc40ee20ec20
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x900000000000b0cc2884803c01400141823804c41c13400110100000000060014b54b439aa8e872d5490a5ea6a14bd454296282852d548cacaa3194b551328ea9e832d52d065aa990d354f2196aa2431d531025aa4204d5444097aa4412d540829aa6105954420
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x60001020895875350a0d63d45428358c5050a256114142
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (297+((h/5+packedAt s1K4 (272+(h % 5)*5) 5) % 23)*6) 6
  | 3 => packedAt s1K3 (609+((h/7+packedAt s1K3 (567+(h % 7)*6) 6) % 36)*6) 6
  | 2 => packedAt s1K2 (156+((h/1+packedAt s1K2 (152+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff0ff83ffff83e0fffffc1fc1fff93f27f
  | 2 => 0xf0783ff0ffc3c1ffc7f0e0f0fe1fe3c3ed4d93
  | 3 => 0xff803fff0003fe1ff800ff00ffe003fc718e1c
  | 4 => 0x3ffffffc001fffff0000fffffc007e0fe0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10000100004000000001011000240040001025
  | 2 => 0x2512522252051309429068a25209428b254492
  | 3 => 0x4336b44636aab13ad988ba84f540cb39718e18
  | 4 => 0xa452888a420a454ad2a1008a99298105a0b40
  | 5 => 0x8c6630ecc733399f37ccdcce310312227fe000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0fafaaaaafafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_34662
namespace PEqualNP.Outside.L_meta_34662
open PEqualNP.Outside.L_meta_34662.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa36194b49c0041002004000827bf43de43bd43dd439d43ee42ed42ee32ed32ef21ed21ee20ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x730000508006240d40de502c040b80184118eaa4878e5250f1aa4a1e350e42c6a1a858d438cb1a86994b55321a6a9e438d43c871a8690e350e2096aa0414d530831a86105954420
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x34010a15865250e0d6550f218359543083054354420
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (228+((h/4+packedAt s2K4 (208+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s2K3 (457+((h/5+packedAt s2K3 (432+(h % 5)*5) 5) % 24)*5) 5
  | 2 => packedAt s2K2 (155+((h/1+packedAt s2K2 (152+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3fc7f87fc7f87fff0f0fc3f87c3f87ffa9327f
  | 1 => 0xc7f87f87f87f870ff1f0fc3f8fc3f8e1d6cd93
  | 3 => 0x7ff8007ff8007f1fe00ffc00ffc00fe670e1c
  | 4 => 0xf8000007fffff801ffff00000fffff00780fe0
  | 5 => 0xfffffff800000001fffffffff00000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x400080400080000001004800048020001025
  | 1 => 0x80811008811008101010441104411045024492
  | 3 => 0xb5133555133556837688ea832ea8329d670e18
  | 4 => 0x14364666246442a5abaa22044b326608780b40
  | 5 => 0x26246444364664c9cdccb326622044107da000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeeeeeeeaa88eeeeeeeeeeeeaa88eeeeeeeeeeeeaa88eeeeeeeeeeeeaa88eeeeeeeeeeeeaa88eeeeeeeeeeeeaa88eeeeeeeeeeeeaa88eeeeeeeeeeeeaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_34662
namespace PEqualNP.Outside.L_meta_34662
open PEqualNP.Outside.L_meta_34662.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15234c3c00b0014a80007c2191478024069c4072024d00006002150486812e0000000003003a4c0200094b2b226d480380861444007000000004078300b081043203ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x11002a13049d82a2019a9e98039928a996ad9e2b1b138997140a8518a1a68c8426001c8000000023068c001b8008248f1194808d252401199580209a2c100e88922a8d8b0200202800000ba3a7210a0f858007001f861780002c92802780258900031f152bad2900161d1c0e229087969106180000414aac280c000042ce011410016020c004005c000b7296876d52d0f5ca5a1eb54b439eaa4879f5350e7ca821d794f42aea9e85765190aeaa3214f953329eaa6659d438ca7ca8194f55032cea186576510caeaa2195e94032bca80656e52906daa520d794c41aea98836e52106daa420de94041bca80833e54cc67aa998e750f31b7294636d528c73a8698cf950319eaa0636e520c6daa418de94031bca80633e54c867aa990eb95321d6aa643af43c875a8790db54a21d7a1a43ad43487cea290f9d0521f220a43e631487ca6290db94821af298815d53102dca4205b54840bb2888175511027ca9984f55330cea1e619d434c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca8104f55020af298415d53082eca2105d54420b7296216d52c43ca43884fd51109e2a221e5214427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xae391e31000c09900680095a8a29c029958652d0ea56194b43a398b5350f154354432c650d500ca1d6395321a358e54c862d65d0f21a999351486c56310521b85804148785434c521c350c524c26561149308758c54443245448510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x2058090ae3316a6a1c85739935148702a1ac229261415cc5448510
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
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
  | 4 => packedAt s3K4 (2694+((h/30+packedAt s3K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s3K3 (633+((h/5+packedAt s3K3 (608+(h % 5)*5) 5) % 20)*5) 5
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf3c7e7f1fc78e3ff8c47c7e1e3871ff89307f
  | 1 => 0xf03f9f8fe3f80fc63f078f8fe3c07e7196c993
  | 2 => 0xffc01ff003fff007c7f80ff003ff807e670e1c
  | 4 => 0xffffe00003fffff807fff00003ffff80780fe0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1040200204010400000101200081010001025
  | 1 => 0x10890422048124084100848442412425024892
  | 2 => 0x22834826491304940b480d20ca93044d270a18
  | 4 => 0x44100148922408009495200111244900580540
  | 5 => 0x8822514c0036492526e64a49980609087da000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefeeeeefefea8a8fefeeeeefefea8a8fefeeeeefefea8a8fefeeeeefefea8a8fefeeeeefefea8a8fefeeeeefefea8a8fefeeeeefefea8a8fefeeeeefefea8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_34662
namespace PEqualNP.Outside.L_meta_34662
open PEqualNP.Outside.L_meta_34662.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc1501842432c70000813c000e288344010a2de43dd43ee42ed42df32ee32dd32ed32cd32df31dd31ef21ed21de30dc30ee20ec20
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xe0a82966987005000248040104808800081a678c0010008080d354a43aaa8c874d5390acaa3215354e32a7aa2654d544ca9ea29953141328eaa6634d52cc65aa990d354f21a6a9a431d540c29aa4185554430a7a9c412d540829aa6105954420
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x11600091587544ca0d64d453283590504ca456114132
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (297+((h/5+packedAt s4K4 (272+(h % 5)*5) 5) % 23)*6) 6
  | 3 => packedAt s4K3 (602+((h/7+packedAt s4K3 (567+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s4K2 (155+((h/1+packedAt s4K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf87fc1fffffffff83e0fc1fc1fffffff924fff
  | 1 => 0xff87fe1f0783c1ffc7f0fe1fe383c3c3edb293
  | 2 => 0xfff8001ff803fe1ff800ffe003fc03fc71c31c
  | 3 => 0x1ffffc001fffff000003fffc007e03e0
  | 5 => 0xffffffe00000001ffffffffffc0000007ffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8000201000000000001002400044040000425
  | 1 => 0x5111902231148a88c2504a08c1a28a8b249292
  | 2 => 0x6232b554535b28bb5948ed414aea133971c318
  | 3 => 0x47653998a651acddaf6a290293733a127e03c0
  | 5 => 0x84462110c4623116358cb193184020205b6800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeeeeeeaaa8aaa8eeeeeeeeaaa8aaa8eeeeeeeeaaa8aaa8eeeeeeeeaaa8aaa8eeeeeeeeaaa8aaa8eeeeeeeeaaa8aaa8eeeeeeeeaaa8aaa8eeeeeeeeaaa8aaa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_34662
namespace PEqualNP.Outside.L_meta_34662
open PEqualNP.Outside.L_meta_34662.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc004980502801120e0591800000de43dd43df32dd32df31dd31ef21f621ed21f521e521de30dc30
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x32007101256008003dab505c30001044c0a6a9487555190ecaa510f1cc521e298a43c7324878a6490f194d21e2a9a43c6434878a8690f1486308eaa0614d520c2aaa2187148430
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x6880a159253486456590d2191595210c3055448430
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | 2 => packedAt s5K2 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (228+((h/4+packedAt s5K4 (208+(h % 4)*5) 5) % 20)*5) 5
  | 3 => packedAt s5K3 (457+((h/5+packedAt s5K3 (432+(h % 5)*5) 5) % 22)*5) 5
  | 2 => packedAt s5K2 (155+((h/1+packedAt s5K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc7f878787fffffff0c30f0e1c3ffffff820fff
  | 1 => 0xf8ff807f8f0f0e1ff03f1f01fce1e1e3cd3293
  | 2 => 0xffff800ff00fe1ffc01ffe00fe01fc71c31c
  | 3 => 0xff0000000ffff001ffffe00000fffe007e03e0
  | 4 => 0xfffffffff0000001ffffffffff0000007ffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x40080080810000000000202040022020000425
  | 1 => 0x92511534126254a9311515049871454b451292
  | 2 => 0x346234152426688b5544164c08b50999514318
  | 3 => 0x2647666648cc4ccdedb6441832d99d127e03c0
  | 4 => 0x844040008881108a288891220010002aa800
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8fefeaaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_34662
namespace PEqualNP.Outside.L_meta_34662
open PEqualNP.Outside.L_meta_34662.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42005c0000188c0000746600348e0c6c6e366256144690285a007002687e32004800002a00205000001a640e12000082782c06886a3a00243e400000005e160086007200001c00008a6092384c4a5800000000002e00300a804e52000800000000007c007a10540000768400042200443c1e002604002000404104000408004000890048001021800002ffd50017f54027f95001fd54005f55009fc5401ffd4c07fe5301f794c07fd53007754c07fc5301ffd0c07fe4301f790c07fd43007750c07fc4302ffd4805fe52007f54805fc52027fd0805fe42007f50805fc4201ffcc807df32017f8c807fd3200774c805fc3202ffd4403fe51007f54403fc51027fd0403fe41007f50403fc4101ffcc407df3100ff8c407fd3100774c403fc31017fc8401ef2100ff88401fd21007b48403fc2102ffd4001fe50007f5400bfc50027fd0001fe40007f50009fc4001ffcc007fe3000778c007fd3001ff0c007dc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc6007f71863007fbea318033de518c001eea8c600cf714630077be8318033de418c001eea0c600cf71063006fbe4318003cf218c019ef10c6000f7486300079a4318033dc218c00fef3046003b79823001fb4c11803fdf508c00fef2846000f75423003fb8a11803bdf408c00fef2046000f75023003fb88118037df208c00fee104600cf7c423003fb82118002ff658800b7f32c4000bf5962002df8cb10002ff64880097f3244000bf59220025f8c9100037f5488001beaa4400abfd8e2003fbec710002df63880077f31c400abf58e2001df8c71001fdc63880076e31c400af794e20007baa71002bde4388001eea1c4002bf58a2005fde851000bec4288005ef9944002f74ca2000dfcc310002fd61880037e30c400af7cc620007ba631000bef2188001f690c4002bf98220007f48110003f9408800fef1844007f70c220017de411000bfb2088005fc1044000bfd952002dfcca90002fd654800b7e32a4000bfd9120025fcc890002fd64480097e3224000dfd5120006faa890026ff6348001efb1a4000b7d8d2001dfcc690026fd63480077e31a4009f718d2001db8c690027de5348001eea9a4009f790d20007ba869000aff6248005f72924000fb54920017dc8490003ed4248005ef9924002fb8c920017ba6490027ed3248001e69924000bfd852000dfcc290006fc6148013ef98a4000f74c520017de4290003ed21480057fb024000fe90120007f28090003de3048013ee1824002fec8120007dc409000bec2048005fc1024000bfd961002dfccb08002fd658400b7e32c2000bfd9210025fcc908002fd64840097e3242000dfd5210006faa908022ff638400fefb1c2000b7d8e1001dfcc708022fd63840077e31c2007f718e1001db8c708023de5384001eea9c2008f790e10007ba8708002ff62840057f3142000bf58a10015f8c508023df3284001ee9942001bf5861000fbe6308007dd3184003f790c2001fb4861000dfcc108003fa5084001fca842000fe90210007f2810801fde308400fee1842001fdc421000ff62108007f810840017fb2a2000dfd9510004feca88016fe65440017eb2a2005bf19510006f8ca880167c65440017fb222004bf99110005fac888012fc6444001bfaa22000df55110035fec688003df63440016fb1a2003bf98d10035fac68800efc634400dee31a2003b718d10037bca688003dd534400def21a2000f750d10005fec48800afe62440017eb122002bf18910037be6488003dd32440037fb0a2001fd94510007eaa288007f64144001faa0a2001f7cc51000fec6288007dd314400dfa98a2000f54c51000fde4288007f62144003f690a2000fd48510007ca4288006ff6044001fd2822000fe54110007f48088003f94044001ef1822006f70c11000ff62088003f61044003fa0822001fe04110
  | 1 => 0x7ef3148403e798a4201fb8c52100fda6290807cd3148403f618a4200fbd8121007dcc090803ed6048401f63024217fbd41210bfd8a09085bef404842df62024215fbcc1210afdc6090857ed304842bf61824215f30c12100fde2090807e71048403f60824205bf59650025fcc928002fd64940097e324a005dfd5250006faa92804eff639400fefb1ca003bf98e5009dfac72800efc639400fee31ca003b718e5002fbca728017dd5394027ef21ca000f750e50015fcc528002fd62940057e314a013f7cca50007ba6528006fe61940017eb0ca001bf186500a6fca3280177c5194027ef98ca000f74c650007de4328003ed219400b7f304a005dfd425002ff6a128017f8509400fee184a005bfd9550005fec8a8012fe64540097e322a005dfd5150006faa8a804aff6354001efb1aa000b7d8d5001dfcc6a804afd63540077e31aa012f718d5001db8c6a80177f535400bef29aa012df54d5002fbaa6a80035d5354025ef21aa000f750d50005fec4a800afe62540057e312a005dfd4950006faa4a804bdf3254001ee992a000bfd855000dfcc2a8006fc615400bbfa8aa000df54550097be62a8003dd3154001f790aa000fb4855002dfec0a8017fb5054001bf282a005df1415002ff0a0a804bdc30540017fb2c8005bf99640005facb20016fc65900097eb248004dfd5240026faa920046ff639000fefb1c8003bf98e4008dfac72000efc639000fee31c8003b718e4008fbca720003dd5390009ef21c8004f750e40015fcc520002fd62900057e3148011f7cca40007ba6520006fe61900017eb0c8001bf1864008fbe6320003dd3190001f790c8000fb48640025fcc120013bf4090009fda048004fe1024003fb86120002ff655000b7f32a8000bf5954002df8caa0012ff6450009bfaa28004ef95140026faa8a0003bd54500019eaa28010bfd8d40007bec6a0002df63500077f31a8010bf58d4001df8c6a0043dc63500076e31a8010f794d40007baa6a0013bf4350009ef21a8010ef50d40027ba86a00039d43500017fb128000fbd8940005dec4a000afe62500057e3128000fb18940015d8c4a0013bf4250001dea128010f7cc940007ba64a0002ff61500037f30a8001bf185400277e82a0003bd4150021ef98a8000f74c540007de42a0003ed21500097fb028004fed01400077c80a0013bc4050009fc2028010f70c14003fbecb18002df658c01fef32c6000f759630005bacb1801fdc658c00fefb246000b7d9230077bcc918003dd648c0016eb246007f71923007fbea9180035f548c01def2a46000f755230006baa91803bdc548c00fefb14600df798a30007bac518002dd628c00fee314600ff7d4a3006fbca518003dd528c01bee294600ef7d0a3006fbc8518003dd428c01bee2146007f7d8630067bcc318003dd618c0016eb
  | 2 => 0x310efb8ca98803df644c4016fb22621cf799131007bac898802dd644c439ee322621df7d5131006bea898873de544c401eeaa26200d7551310e7b8a898803df624c4016fb12621bf798931007bac49886fdc624c43befa92621bf794931007baa49886fdc524c439efa12621bf790931007ba849886fdc424c403efb0a6201b7d853101faec298807df514c403ef28a6201f75453100fb8a298807df414c403ef20a6201f75053100fb88298807df214c403ef10a6201f708531007bec098803de604c401eeb026200f718131005b8c098877df504c43bee282621cf7d01310e7b8809886fdf204c437ee1026201f7c413100fae2098807dc104c405f7b2e4202fb99721016dccb9080bed65c8405b6b2e4202fb19721017dec99080bee64c8405f6b264202fb193210d7dea9908036f54c8433f72a64200fb55321006daa990867ec54c8405f7b1e4202fb98f210179cc79080bed63c8405e6b1e4202fb18f210c7dea790863ee53c8431e729e4218fb54f210079aa790863ec53c8431f7a1e4218fb90f210c79c8790863ed43c8401e6a1e4218fb10f2100ddac390807ef51c8403f728e4201fb5472100fd8a390807ef41c8403f720e4201fb5072100fd88390807ef31c8403e798e4201fb8c72100fda6390807cd31c8403f618e4202fbd8321017dcc19080bed60c8405f6306421afbd43210d7d8a190867ef40c8433f62064218fbcc3210c7dc6190863ed30c8431f61864218f30c32100fde2190807ec10c84017fb2a4205bf99521005faca90816fc65484017fb224204bf99121005fac890812fc6448401bfaa24200df551210adfec69080efe634842bef31a4203b798d210adfac690803dd63484016eb1a4203bf18d210afbca690803dd534842bef21a4200f750d2100dfec49085fef5248405f72924200fb54921017d8a49085bef4248405f72124200fb50921017d8849080bdf324842bf79924215f3cc921017dc649080bdd324842bf69924200f34c921017d86490806ff614842ffba8a4201fd1452100fec8290803f54148403ef98a4201f74c521017ee4290807ee2148403f610a4201fd08521005fec090802fc604842bee1824202fbc8121017d84090807f71048401f7b2a4217fb99521007daca9085fec6548401f7b224216fb99121007dac89085bec644842ff7aa24200dbd51210b7dca890803ed5448401b6aa24216fb151210afdec690857ee634842be731a4215fb58d210079ac690857ec634842bf7a9a4215fb94d210af9ca690857ed5348401e6a9a4215fb14d210afde8690857ee434842be721a4215fb50d210079a8690857ec4348403f7b0a4201bbd8521017cec290807ef514842ff3a8a4201fb9452100fdaa290807ec5148403f228a4201fbd052100fdc8290807e64148403f6a0a4200f95052100fd8829080
  | 3 => 0xe10a8600f7d8143007bcc0a1803dd6050c01ee3028600b71814314fbea0a18a7dc5050c09efa028604e7d0143027b880a18a3df2050c51ee1028627f7c414313fb820a180aff65548017fb22a404bf99152025f8c8a90177f5454801beaa2a424bfd8d5201dfcc6a9093de63548076f31aa424bf58d52007bac6a900efc635480bef29aa405f754d52127bc86a9003dd43548057fb12a405fbd4952016fca4a900b7c5254805f6292a426fbd0952017d884a900bdf32548017fb0aa401bf9855200df8c2a90977e515480bbe28aa424f7cc552017de42a9002ff60548017e302a405dfd4152127b860a900bef20548017fb2a8405bf99542005facaa1016fc65508057fb228404dfd5142026faa8a108eff63508077f31a8423f798d4201dbcc6a108efd6350801eeb1a8403bf18d4211fbca6a1003dd5350809ef21a8404f750d42015fec4a1013ef4250805df2128402ef10942017d884a100bdf32508017fb0a8401bf9854200df8c2a108fdf3150805f790a8400bfd8142005f8c0a1013bf4050847ee1828402fbc8142007beca99002df654c845ef32a6400f759532005baca9908bdc654c801efb226400b7d913210fbcc899003dd644c8016eb226421f719132117bea8990035f544c843ef2a26400f755132006baa899087dc544c805efb126402b7d893201f9ec49900bdf524c805ef2926402f754932017b8a49900bdf424c843e7a126402f790932017ba849900bdc424c805e62126400f7d8532005bec299083de614c801eeb0a6420f718532117bea299083de514c841ee28a6421f7d0532107bc8299083dc414c805ef90a6402f3c8532017bc429900bdc214c801efb026400f798132007bac099003dc604c8016e3026422f7d4132117b8a099087df404c843ee2026402f7c81320179e409900bdc204c841ef8826420f70413200dfecaa8802ff64544097f322a204bf1915102efea8a88037d545443f7fb1aa203bf98d510ffbcc6a880ede635443f7eb1aa200f758d5101df8c6a8817de535440beea9aa21ff790d51007ba86a8802ff62544057f312a202bf189510ffbe64a8803dd32544037fb0aa205fdd455100efca2a88077c5154403fa28aa201f7cc551005fec0a8802fc605440bbfa82a21ff70c15100fee20a8802ff655040b7f32a8200bf5954102df8caa0806ff6450409bfaa28204ef95141026faa8a0803bd54504019eaa2821ebfd8d4101dfcc6a087bde63504076f31a821ebf58d41007bac6a080efc635043def29a8200f754d41027bc86a0813dd43504017fb128202bf98941015f8c4a087bdf3250401ee9928201bfd8541027ee82a0807be4150403de20a8201fd1054100fbe62a0807f621504017fb028200bf181410277e80a087bdc3050403fb8828200f7d9531005beca98877de654c401eeb2a6200b7595
  | 4 => 0x137c41d5065bf98ea832d7cc754186fc63aa0cb7d31d5061be18ea831dfc8754186fc43aa0c37c21d500bbfb06a805df9835402efac1aa0177c60d5009bfa06a804df10354196fe61aa0cb7e30d5065be986a832df0c354196b861aa0c77f20d5063be106a830dfc4354186f821aa012ff65550097fb22a805efd5154026fca8aa0137c5455009de2a2a82fbfd8d5401dfcc6aa0bfde63550076f31aa82fbf58d54007bac6aa00efc635500bbfa9aa82fdf94d5402fbca6aa0bf5e535505fbea9aa805df14d54027bc86aa002ff62550057f312a802bf1895402efea4aa0bb7e525500bbe292a82eef909540277884aa0bfdf32550017fb0aa801bf9855400df8c2aa0177f515505bbf28aa805df145540277e82aa0bfdf31550017fb02a800bf1815402efea0aa0177c5055009dfa02a82ff70c154026fec8aa0127f645500b9fb22a82fdfd8d5417efcc6aa0bf5e635505fbeb1aa800d758d5417ef8c6aa0137f4355009bf21aa804d790d54026fa86aa0137c4355001bfb12a82edf98954006fac4aa0bb7c6255009bfa12a804df909541767c84aa0137c42550099e212a82fdfcc95417ebe64aa0bb7e325505fbe992a82edf0c954006fec2aa0b77e6155001beb0aa82ddf18554026fe82aa0133f4155009bf20aa804df1055417efe62aa0bf5f315505bbf18aa82fdf4c55416ef862aa0bb7f215505bbf10aa82ddf08554006fec0aa0037e6055001beb02a800df18154026fe80aa0133f4055009be202a82fdfcc15417efc60aa0bf7d305505fbe182a82fd70c154176fe40aa0bb7c205505bbf882a82ddf0415401fbecaa980edf6554c07afb2aa600f7d9153005bec8a98b3de6454c01eeb22a62cf71915302fbea8a98175f5454c0bef2a2a605f755153006baa8a9817dc5454c01efb12a600b7d895315fbcc4a9803dd6254c57ee312a605f7d495302fbca4a9817dc5254c59efa12a62bf79095315fb884a9803df6154c016fb0aa62af798553007bac2a98abdc6154c0befa8aa605f794553156bca2a9817dc5154c0bae28aa62cf7d0553157bc82a98abdc4154c57ef90aa62af788553157b842a9803df6054c01ef302a600f758153007b8c0a9802dc6054c0befa82a605d7d415302fb8a0a98b3df4054c59ee202a62bf7c815315fb840a98abdf1054c55ee082a600f7d9543005becaa18a7de6550c01eeb2a8600b75954314fb8caa180fdf6450c076fb228603e7d9143027bea8a18135f5450c09ef2a28604f755143026baa8a1813dc5450c01efb128600b7d8943147bcc4a1803dd6250c51ee3128629f7d4943147bca4a18a3dc5250c09efa128604f790943027b884a1803df6150c016fb0a8627f798543007bac2a189fdc6150c53efa8a8627f79454313fb8a2a1813df4150c09ef20a8604f710543147be42a189fde2150c4fe
  | 5 => 0x2a00003882ca00040c51200056a5460de0005082880001d00000004680246a43625dc17c7f45447b85863ce00000020a00027a6621680000000c40004be24a00086600017435478884e00015c0d06040500002ac0003a45644fe81c00000070c74a82e00041400002a7c200051a2442a46ba6a039a67a0000003a88a44a60a04de00000000024687c7ea11c2088b80002ec0000006d48106f00cc00000036c0ea0e41460005c463c5e808c3ac5aa00016a0000e62e089643400043075400000071444674c2346ec6a84840002d07608884420000003741485ac6006d63fc6a60003b07320000003483942ae0003787b218c7e00007840004f238a50205a53e00015e00049600000045a1da0005903b20400008244a42cc44812600070e0000000000006c21d21e42620007980000003222720001c667851000000028600021a8506285d681e0007a861013033e6602560003da00000035c72000076e00029800003403800000000004018000060040400901000c0080600e0180080200c00c028080000001280000002800800000004010000180040080b008000090010040000200100000804801006000050040000080280007600c0300100000401011000000028080020000580b00c03000011000008000000060000300301a0000780000e050010000000000880700a0040480e00002c0480500004c0000301000c06801000000000010000000700d00002c0180b02a00c0000b0000180b0000000040200000402000000000000000010160040001c0000400000000a0180500002c000010000080480281000007c00805004028040010000440180101201c0200200c010010000020000980a0000100500b00003002003010004018010020080b00000601001804006004008030000040000000a00819800028004000050140480680101201c00804024000038160060000580001001002005000018000050020380401901c0000000600200c0300400a00810001000060010060180080080b02000c138020340000100d004068068020020000000000e000040080020140000600a00005808000008008060040080081600601c0080100a008000010060080300b000020058070180240000d0000ac0100000401400000016008040040000040100900c020000090080200680d012020008150040040100003a07402803000000000000020380180000401c008127d64d500bbfb1ea805df98f5402ebcc7aa0177d63d500baeb1ea805df18f54026fe87aa0137e43d5009af21ea804df50f54026f887aa0177f62d500bbf316a805db98b5402efac5aa0176d62d500bbe316a804dfd0b54026fc85aa0137c42d5065bf996a832d7ccb5418efc65aa0cb7d32d5063be196a805dfd875402efcc3aa0177d61d500bbe30ea804dfd0754026fc83aa
  | 6 => 0xe00051c78015a1ae29e46200000029c00000047600061c4e80001d663a0000f28641080c04f40007a642c01627e1e888000443c22a3383d06c42ba12a3865ae0d60002fa0000007006ce03a56e0008e48420008381f83362a831a1786e26dc3807742f28763de39e0006ac00065c6bc6440000000383281627d860e25a5947ee1383423403460303c67ae00045082254c5286fe1ac23672658049a2520525ec0d456c2c08682663246be8da81a8ac39c5d001406e5fe4bc65a7ca0005841a68e200052c8ba0000001367ba1be2ee84000081262c1f200000073400067e36e0000ec0005e600000000000025c0960105b623274472237e8ca57a1985d24d405813c2385b00ce5a855c2188446c00dc6fa0680b000060239279445c4f04d86e064e3700208b65721de6fc0343b42803f63ee58c6762d429677861219c8c65fc89005468a0000005241823e600012c0480000ae0004ec07000044a3cc8841b80002785a02066063ba75068e3646188cc6580a611268c0c84561800820f82c66207644da36800083e0da0000000b63983e259880e00000000000000869600030e8a054254e3d620e10648c4443f84ae6882de00009288e5a200025e1dc00041600000066c0000000000006420003e026e2e26c834e0007fa00030818a8608321002e86de53200053822800000004a0008204ea7760000005a45580000005de0000005f47b40003aa0000e00904e460c3d41ca0006983b82f45be6cc2024aa35047009a0002be07a1965a600000047c2042708528a800043a4b20360000b28b06684383300005e20008466f48088d661400048e1588c21848581a854a2e400c63421c0125140007c062e6547dc0f000051852a00000040e49283c41c7480982504e015647e8d844e4606160321a28d424e00029218663005e22285c0a872c6d84ca8702d267237612e0944f641e06a2543d85560727d66ca89c4005c62306f20000007c60006e88041bc4c88a671265638200a09c46a16e4d650c6a21ce1103ea7463dc3e44a033a65e07411807e08489852e00089e6b00fe29028a35a6ee33c5fa0e845814010c1c46aa4785c08b20005166e61d453a32c43e03e79600068473a6b223e6361e05742747be01a00000042400000000011a81641219e1220001fa5d42242400000ca5b432e00000000077000000022c0003ca07c58a72a00071e5e04740000007f80184083c862489482848a00050469016687a2ea0006ea3bc29a1f60000000000000005600001c86d25307928de5360006084e60008d076a0002123120004203261b48784884cc7ce83000008817a1ec0000000000006d067c5620001fe0000000000000001ee7160d80000001700001f02fc4e282a0004664280c62f64260005f224800000087e0000000003664ce00047254804200200071c14e0
  | 7 => 0x73875e50a6c626021e0000005c810200631e75a8ae6260003c002e00062a1b006c3900b839600036a2fe0001907f040a09e10473057e00026449c0008dc7040560000fc46e00000069400000000005c61a26868686e2261ba0000005760008c00ac6227fc8340625524c24fa1c23022f01443163d254020014a38442e70a3c440400e0be50e6f800045278e0002b80005f60008360000008020000007560e200013478a00073e00086a0b40760008824b685401e7ec0000003f030a0007360004b40000220000007b60fa00053c2840000004c079e5ce14c0008d200073c02c7d42d64d04065681a430035804c66a2a287208671069c0000f466e70200064a7e624c0000800000000004a851e0aa3443040261327660005342b41a085e78c32022006050000027c0004b800074e00000056600022e0bc68200000028c3fa82600049e1ea00010a08a0008a200000052269e55a00058e19a4988741fc7288ce37c6328c828e5d80000000008c484813a2da59a1c04ee0005bc18e00000038e00000000077c71a6e46b40000001cc5543b60007a20002bc69a8140000007de47a00059c00084c00025875c74000018880c0007a419217e3321e62141281763522761200005f000000088a7587726701f47c403c0004a23344b06da2e635e0004fc6800004105c28006385ba79c44c00049080a7240000000007bc30c88c83a0008be00059669274279a4945880ba3a020c48634a3c20004f87087d00004ba0005701aa5780001e21b60007da0004220007f62b011604460a46434c64689a11e07815477e0000002c841a2b62ce7180003140007cc5ee6b64022f80460000000000c27d26f600000013e00000066400046c7e82b23be3e80000ee0647905ea4dc37a11400076c0004804402d800038c00029486200043631c1646406662825507a07e43061606483a226a26c45e0a25828bc85659e23c6ae0288923ec1d804e50665261e4d278601c6b87063a610e8863f27c82167ac4542420a45f842a3fe32a59223a5b87622aa1722100d264c0003567f22c284a7e22c482c5e48060000005266503108180004c41947825cc7aa52072e76831877a2dc4ac0000660000000008b40000006747525b20f64827fe0001244c68e00002a63725ca0008aa08e57c00000085a00000055e16c1b286c0001507b04320000001524185da1423f40000003ae36000063
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd54d8e10004dd72d8e1003ed571d8e10066cf21d8e10066cd21d8e1003cde70d8e1003eda70d8e1003ed710d8e1003cde7654e1003cdc7654e1002e5e6554e100065d6554e1003cde7650e1003cdc7650e100269e6450e100069d6450e1003cdc73d8a10004df7358a1001cdc7358a1003cde764ca1003cdc764ca10016ce624ca10006cd624ca1000cf9769421000759535421000cf9769021000739545021000799435021001cdc73d95100065e53d951002c7e76d95100065c63d95100047d74d95100065f73d95100065c73d95100065e43d95100065f32d95100a65f31d95100a65d31d95100a66f21d95100a66d21d95100065c30d9510004df735951001cdc73595100a47e76195100053d74195100065c631951001cdc73d91100047f755911002c7c7559110004df735911001cdc7359110004ef7259110014ec72591100047e76d511002c7c76d51101965c63d51100047e76551100047c76551100263e64551100063d645511017e5c635511001cde76d8d100065f65d8d100065c65d8d10004dd75d8d10004dd74d8d100065f54d8d100065d54d8d10004dd72d8d1003cdf71d8d10064dd71d8d10066cf21d8d10066cd21d8d1003cde70d8d1003cdc70d8d10004de7654d10004dc7654d100065f6554d1002e5c6554d10157565154d10004de7650d10004dc7650d100065f6550d1014e5c6550d1001cdc73d89100047f755891002c7c7558910004bf7458910024bc7458910004df735891001cdc7358910004de764c910004dc764c9100065f654c9101165c654c910016ce624c910006cd624c91002cf47654510024f4765051000735545051001ed7764c510035d4764c51001ed4764c51001cd4764c510005d7754c510005d5754c51000757654c51000754654c510005d7744c510005d5744c51000757544c51000755544c510005d7724c510007d3704c51003dd4704c510007d0704c51000ed7604c51000fd3604c510014f476485100be746548510005d573485101a7c73248510007c53248510016e77648510016e476485100076765485100bee665485100bee465485100076465485100be646548510006e76448510006e564485100076754485100076554485101a7c67348510007c57348510007c763485101a7c463485101a7c65348510007c553485101a7c64348510007c54348510007e37048510007e0704851000ee7604851000fe360485101a7c4304851002e7865941100a7725194110007d13194110007e1219411000cf87654110007595354110007715154110007d13154110007e12154110007d13190110007e1219011000cf87650110007395450110007994350110007b14150110007d13150110007e1215011019cde768c1100065f658c11007e5c658c110007c5218c11000cf6768411003dd77384110
  | 1 => 0x863006f4e75c863006f4d75c8630006cf65c8630006cd65c8630006cf64c8630006cd64c86300074f54c86300074d54c8630065cd71c8630066cd61c863019ece60c86300c7ca60c8630004dd7648630006cd6248630006d56148630006ce7648630006cd7648630006cf6548630006cd6548630006cf6448630006cd64486300074f54486300074d5448630065cf714863006fc77148630067c66148630066cd6148630007c56148630006c561486301c7c75148630067c45148630067c64148630007c5414863019ece60486300afca6048630067c710486301bcdf765423003e5f65542301b4df765023003e9f64502300071d5450230005cf725023006dcc725023003cdc73d9620004df735962001cdc735962003cdc73d9220004df735922001cdc73592201965c63d52200263e64552200063d645522017e5c63552201772c4255220004dd75d8e20004dd74d8e200065f54d8e200065d54d8e2003ecd72d8e20006cf42d8e2006ecc42d8e20004dd71d8e2006ecf21d8e2003cde70d8e2003eda70d8e2003ecf20d8e2003cde7654e2003cdc7654e2002e5e6554e200065d6554e2003cde7650e2003cdc7650e200269e6450e200069d6450e20005cf7250e200047f755862002c7c7558620004df735862001cdc735862003cdc764c62000ed6614c620006d5614c62000cef7648620006cf63486200aecc634862000ee66148620006e56148620014f97690220007395450220007994350220015e8725022005fab425022001cdc73d9520004df735952001cdc735952001cdc73d9120004df735912001cdc735912005cef72591201965c63d51200063f64551200263c645512017e5c63551201772e425512001cde76d8d20004dd75d8d20004dd74d8d200065f54d8d200065d54d8d2003cdf72d8d2006cdd72d8d20004dd71d8d2006ecf21d8d20004de7654d20004dc7654d20004de7650d20004dc7650d2002cec7654920024ec765092001ecf764c92004dcc764c92001ecc764c92001ccc764c920005cf754c920005cd754c920005cf744c920005cd744c92010ece644c92010ecc644c9200074f544c9200074d544c920005cf714c920007cb704c92003dcc704c920007c8704c920016cf604c920017cb604c92001cdc73d852000cec72d8520006cd32d8520004de764c520004dc764c52000cec7648520005cd7348520006cf63485200aecc6348520006e76148520007c93290120014f87650120007395450120007994350120007a94250120007c932501201acde768c12003dcf738812003cdc73d9610004df735961001cdc735961003cdc73d9210004df735921001cdc7359210004ef7259210014ec72592101965c63d52100263e64552100063d645521017e5c6355210004dd75d8e10004dd74d8e100065f54d8e100065
  | 2 => 0x14ee76d89400072d54d8940006cf63d8940006cc63d89400078d43d894005e6f54d894005e6d54d8940006cf73d8940006cc73d8940006ce53d8940006cd53d894005ece43d894005ecd43d8940004ed71d8940006cf31d8940006cc30d89400072d5418940006cf6318940006cc63189400078d4318940005e57118940014bc7650940004de764c940004dc764c9400059d744c9400071d544c940006cf624c940016cc624c94010f8f424c9400063d54d854001cdc73d854000cbc7650540004de764c540004dc764c5400059d744c5400071d544c540006cf624c5400decc624c540004ee76c8540014ec76c85400072d54c8540006cf63c85400c6cc63c85400078d43c8540004ee7648540004ec76485400072d5448540006cf63485400aecc63485400078d434854000ee66148540007a54148540094dd75d9630004dd74d963007e5f54d9630004dd72d9630004dd71d96300065e51d963007e5c51d963003cde70d963003eda70d963003e5f50d963003cdf755963003e5f7559630004df745963007e5f5459630004df725963007e5f5259630004df715963007e5f515963003cde705963003cdc705963003e5e505963003e5c5059630004dd75d9230084dd74d9230004dd72d9230004dd71d923003cde70d923003eda70d923003e9f40d9230005cf725923006dcc7259230004df755923003cdf745923003e9f74592300769e5459230004df7259230006cf7259230004cf7259230006cc72592300769f4259230004df71592300769f415923003cde705923003cdc705923003e9e405923003e9c405923007e5e76d523007e5d76d523017d5d74d52300765f64d52300765d64d523007f4e72d523007f4d72d52301965e60d52301975a60d523003cde7655230004dd76552300065f65552300065d65552300069d64552300065e76552300065d76552301955f745523007f1f74552300765f64552300771e64552300765d64552300071d64552300061d64552301cf1e42552300771c42552300771f415523017e5e605523017f5a60552300771f4055230004df7558a30004df7458a300065f5458a300065d5458a3006ece5258a3006ece4258a30004df7158a3006ecf2158a3003cde7058a3003cdc7058a3003ece2058a3003ecc2058a30004dd7654a300065d6554a30006cd6254a30004dd7650a300069d6450a30006cd6250a300055f755863007d5c7558630004df75586300065f75586300045f75586300065c7558630004df74586300065f54586300065d5458630004df7258630066d65158630066d64158630066d6215863003cde705863003cdc705863003ed6105863003ed41058630004dd76546300065d6554630006d56154630004dd76506300069d64506300071d5450630006d5615063006ece76c863006ecd76c
  | 3 => 0x54350521005e770505210b7a740505211dfc430505210adce73d8121005cd73d8121006cd63d81210adcc73981210056f75581210bd6c7558121005af74581210b5ac7458121005cf73581210adcc7358121006cd63581210bd6e75181210056d75181210b5ae7418121005ad74181210adce7318121005cd7318121004df735925001cdc7359250004ef7259250014ec72592500247f76552500263e64552500063d645525017e5c635525003cdc7650e500269e6450e500069d6450e50004df7358a5001cdc7358a5003cdc764ca50016ce624ca50006cd624ca50004df735865001cdc735865003cdc764c6500055f754c65000ed6614c650006d5614c6500c6cc63c86500aecc634865000ee66148650006e561486500a76451486500247c75d915001cdc73d91500247c76551500063f645515017e5c635515001cde76d8d50004dd74d8d5007e5f54d8d500065d54d8d50004dd72d8d50004dd71d8d5001e5f7654d500955c7654d5001e5c7654d5001c5c7654d500055f7454d500065f6454d500055f7254d500055f7154d501565e6154d501565c6154d500075b7054d5003d5c7054d50007587054d5002e5f6054d5002f5b6054d50004de7650d50004dc7650d500055d7550d5001cdc73d89500147c7654950004de764c950004dc764c9500055d754c95001cdc73d855000c7c7654550004de764c550004dc764c5500055d754c550006cf63c85500c6cc63c85500074d53c8550006cf63485500aecc63485500074d5348550006e7614855000ee461485500bf67514855003cdc73d9640004df735964001cdc735964003cdc7654e4002e5e6554e400065d6554e40004df7358a4001cdc7358a4003cdc764ca40016ce624ca40006cd624ca400047f755864002c7c7558640004df735864001cdc735864003cdc764c64000ed6614c640006d5614c6400c6cc63c86400aecc634864000ee66148640006e5614864001cdc73d9540004df735954001cdc7359540004ef7259540014ec7259540004f7715954000cf4715954002cbc76551401d71e5355140176ac625514002e3f765514002e3c76551401d71e73551400071d73551401d71c63551401763e62551401763c62551401762c62551401d71f32551401d71f31551400073b70551400073870551400263f60551400273b60551401d71c305514001cde76d8d400071d54d8d40004dd75d8d400765f54d8d400765d54d8d40004dd72d8d40004dd71d8d40004de7654d40004dc7654d4002e5e6554d400065d6554d400071d5454d4015ecc6254d4001e9f7650d400859c7650d4001e9c7650d4001c9c7650d400059f7550d400059d7550d400059f7250d400059f7150d400079b7050d4003d9c7050d40007987050d400269f6050d400279b6050d4001cdc73d8940006cf32d8940
  | 4 => 0xc92101ecc764c921005cf754c921005cd754c921005cf744c921005cd744c92110ece644c92110ecc644c9210074f544c9210074d544c921007c7714c921105cd714c921107c4714c921016cf614c921017c7614c921217c7514c921107c4514c921107c6414c921005cc704c921107c7104c921014f476505210073554505211dfc73250521007c5325052101cde73d8121004dd73d8121006cd32d812102c7e75181210047d7518121024be7418121004bd741812101cde7318121004dd73181210adce73d9521005cd73d952100de671d9521015e571d95210bf6751d95210adce7359521005e7715952112f6451595210adce73d9121005cd73d91210b6ac64591210adce7359121005e771591210be6e76d51210be6d76d512116d6d74d51210bf4e73d51210bf4d73d512120f4e63d51210b74e43d51210bf6771d51211876471d51211866f61d512118f6761d51211876641d51211874f31d51211874d31d512120f4c30d51211876710d51210adce73551212074e5355121005e7715512100de471551210bf67515512116f6451551211856f74551210bf2f74551210072f64551210b72c64551212074e73551210074d73551212074e63551210b74e435512100767715512116f64715512116e6f615512117767615512116f2f415512116f66415512116f2d415512116f4f315512116f4d31551210b72f40551212074c305512116f6710551211fdcf7658d210aecf7658d21005cf7558d21005cf7458d21006ce6458d21006cc6458d210074f5458d210074d5458d21105cf7158d21007c77158d21005c77158d21106cf6158d210dfc76158d21007c75158d21107c45158d21107c64158d21005cc7058d21107c71058d21005cf7654d21005cd7654d211f5cf7554d210af4f7554d210074f6554d210bf4c6554d21005cf7454d210bf4f5454d210074d5454d21155cf7154d21007c77154d21005c77154d21155cd7154d21157c47154d21156cf6154d2115fc76154d210bfc75154d211574e5154d211574c5154d21157c45154d21157445154d21157c64154d21005cc7054d210bf4f5054d21157c71054d21005cf7650d21005cd7650d21005cf7550d21005cd7550d211edcf7450d210af8f7450d210078f6450d210b78c6450d210b74f5450d210b74d5450d2113dcf7150d2113dcd7150d2113ecf6150d21147c76150d211e7c75150d2113fc45150d2113fc64150d21005cc7050d210b78f4050d2113fc71050d21015e67650521015e476505210bde675505210bde4755052100de7745052100fa77450521007a764505210b7a464505210b76754505210b7a654505210b7655450521007a554505210072554505211dfc67350521007c573505211dfc66350521007c563505211dfc65350521007c553505210b7c643505210b7c
  | 5 => 0xe65f64551310e65d64551312371e42551310e71c425513100757715513116f54715513116e5f615513117f57615513116f1f415513116f1d41551310e71f405513116f571055131004dd75d8931004dd74d89310065f54d89310065d54d8931104dd72d893101cdd71d89311fecf21d893103cde70d89311fed710d89310c5d77158931004de76549310065f6554931004de7650931035d571981310055f75581310ed5c7558131045d771581310ed5e75181310055d75181310e59e74181310059d74181310ddce7218131005cd721813103e5e7518131004dd751813103e5d75181310045d751813103e9e7418131004dd741813103e9d74181310049d74181310065f54181310065d541813103ece7218131004dd721813103ecd7218131004cd721813101cdd711813103ed5711813119ecf211813119ecd211813103ed7101813103eda101813119ed9101813118d6f76d532118e6e76d532118d6d76d53210d66d76d53210046d76d53210d74e73d53210d74d73d532118f4e63d532118f4d63d53210cf4e43d53211874f31d53211874d31d532122f4c30d53210c5ce73553212274e53553211756f76553211756d76553210d72f74553211772f64553211772c64553212274e73553210074d73553211774e63553211774d63553210cf4e435532116f2f415532116f2d415532116f4f315532116f4d31553210cf2f40553212274c305532115dcf7654f2115dcd7654f211f5cf7554f210c74f7554f2115f4e6554f2115f4d6554f21005cf7454f210d74f5454f210074d5454f21155cf7154f21155cd7154f21156cd6154f211574e5154f211574c5154f21005cc7054f210d74f5054f21145cf7650f21145cd7650f21005cf7550f21005cd7550f211474e6550f211474d6550f211edcf7450f210c78f7450f210cf4f5450f210cf4d5450f2113dcf7150f2113dcd7150f2113ecd6150f21005cc7050f210cf8f4050f2101cde73d9521004dd73d952100ced72d9521014f571d952101cde735952101cde73d9121004dd73d912100ced72d912101cde73591211965e63d512120f4f32d51210063f64551210263c645512117e5e63551211772e42551211772c42551212074f325512101cdf7658d211fdcf7258d2121dd77158d21004df7558d21004df7458d210065f5458d210065d5458d211fcdf7258d21006cf7258d21006cf4258d210decc4258d21104df7158d21006d77158d2103cdc7058d210decf2058d21106d71058d21004df7654d21004dd7654d210065f6554d2102e5c6554d21005cf7254d21005d77154d21157545154d21004df7650d21004dd7650d210069f6450d210269c6450d21005cf7250d2100cec76549210adce735492100de4715492112f64515492100cec7650921026ac64509210adce735092101ecf764
  | 6 => 0xe70d853221ecf20d8532265cf72585320aecf625853204dcd7298132055cf72581321155e75181320055d751813210d9e74181320059d7418132105d67118132005d5711813203e5e7518132004dd751813203e5d75181320045d751813203e9e7418132004dd741813203e9d74181320049d74181320065f54181320065d541813201cdd721813203ecd7218132006cf42181321aecc421813203ed67118132004dd711813203ed57118132004d571181321aecf211813203ecf201813203eda20181321aed9201813201cde73d9151004dd73d9151014ee72d9151004ed72d915100c7c76551510063f645515117e5e635515100d74715515125dd77158d51004df7650d5101cde73d8951004dd73d8951004df764c95101cde73d8151004dd73d8151024be7418151004bd741815101cde7318151004dd7318151014ee7218151004ed721815101cde73d9541004dd73d954101cde735954100cbc76551412571e535514102e3f765514102e3c76551412571e73551410071d73551412571e63551411763e62551411763c62551412571f325514100737715514116f3471551410263f615514102737615514116f1f315514116f3621551412571c305514116f3710551410071d5458d4124dd77158d41004df7654d410065f6554d4102e5c6554d410071d5454d4101cde73d8941004dd73d8941004df764c9410071d544c941006cf624c941016cc624c9410063d54d814101cde73d8141004dd73d814102c7e75181410047d751814101cde7318141004dd7318141014ee7218141004ed7218141154dd75d9531004dd74d95310ee5f54d9531004dd72d95310ee5f52d953101cdf71d953101cdd71d95311f65f51d95311f65d51d95311f6cf21d95311f6cd21d953103cde70d95310ee5c50d95311f6d710d95310ee5c6559531245d771595311f4df75595310065f7559531004df74595310ee5f5459531004df7259531154df7159531006d771595311565e51595311565c515953103cdc70595310ee5f5059531156d710595310ddce72d9131005cd72d9131004dd75d913113cdd74d9131006ce72d9131004dd72d9131006cd72d9131004cd72d913101cdf71d913101cdd71d91311ee9f41d91311ee9d41d91311eecf21d91311eecd21d913103cde70d91311eed710d913123dd77159131004df75591311ecdf74591310069f7459131004df725913113cdf7159131006d7715913103cdc70591310e69f405913113ed710591310ee5e76d51310ee5d76d513116d5d74d51310e65f64d51310e65d64d51310ef4e72d51310ef4d72d51311865f61d51311975761d51311875710d5131004de7655131004dd76551310065f65551310065d6555131005d7715513100dd471551310065e76551310065d76551311855f74551310ef1f7455131
  | 7 => 0x81432a65d541814303ece7218143004dd721814303ecd7218143004cd721814303ed67118143004dd711814303ed57118143004d5711814303e9f401814303eda40181432a6d9401814301cde73d9152004dd73d915202ced72d91520147c76551520063f64551520263c645515217e5e63551521772c425515229dcf7258d52004df7650d52005cf7250d520147d75d855201cde73d8552004dd73d855201cde73d8152004dd73d8152024be7418152004bd741815201cde7318152004dd731815200cf67118152004f5711815201cde73d9542004dd73d954201cde7359542295cf7258d42004df7654d4202c7e75d85420047d75d854201cde73d8542004dd73d854201cde73d8142004dd73d814202c7e75181420047d751814201cde7318142004dd731814200cf67118142004f5711814215cdd75d9532004dd74d95321165f54d953201cdf72d953201cdd72d95322865f52d95322865d52d9532006cf42d9532286cc42d9532004dd71d9532286cf21d953203cde70d9532286cf20d953228dcf7259532284df75595320065f7559532004df74595321165f545953215cdf7259532006cf7259532006cf425953215ecc4259532004df71595320065e51595321165c515953215ecf215953203cdc70595321165f505953215ecf2059532015ce72d913201dcd72d913210f8f42d9132004dd75d9132144dd74d913210e9e54d913201cdf72d913201cdd72d913227ecd72d913201ccd72d913226e9f42d913210ecf42d913226e9d42d913226ecc42d9132004dd71d913226ecf21d913203cde70d913226ecf20d9132275cf7259132004df755913226cdf74591320069f7459132144df7259132006cf725913210ecf4259132146cc4259132004df7159132146cf215913203cdc705913210e9f4059132146cf20591321165e76d51321165d76d51321755d74d513210e5f64d513210e5d64d513218f4e72d51321174d72d513218e5f62d51321974f62d513210f4f42d513218f4c42d513218f4f21d513218f4f20d5132004de7655132004dd76551320065f65551320065d65551320069f6455132005cf7255132015cc72551321778c42551320065e76551320065d765513218d5f74551321171f745513210e5f64551320071f64551320061f645513210e5d645513210f1c64551320074f72551321774c72551321765f625513217f4f625513210f4f42551321771e42551321771c42551321774c42551321770c425513210f1f41551321774f215513210f1f40551321774f20551321155e75d85320055d75d85320c6cf62d85320065e75d8532004dd75d85320065d75d85320045d75d8532004dd74d85320065f54d85320065d54d85320c6cf72d853201cdd72d8532006cf42d853221ecc42d8532106cf21d8532106d621d853203cd
  | 8 => 0x65d63581540056f72581541756c725815400577715815416d74715815417d5e73181540055d73181541756e72181540056d721815416d7671181540057571181541965f65d915315dce72d9153005cd72d91531965f75d915301cdd75d91531965f54d91531669e54d91532e69d54d9153006ce72d9153004dd72d9153006cd72d9153004cd72d9153004dd71d91530065e51d91532e65c51d915303cde70d91532e65f50d91532b55f755915317e5f655915301d5e765515317e5e765515301d5c765515302d5f745515302f1f74551531665f64551530071f64551530061f64551531671c64551532df1e42551531671c42551531555e71551531555c71551531671f41551530055f70551531671f405515301cdd75d8953004dd74d895329e5f54d89530065d54d895315ece52d8953004dd71d89530065e51d895329e5c51d895315ecf21d895303cde70d895329e5f50d89532d55f755895302d5e75d855301d5d75d85531575651d855301cdd75d85531565d75d855301c5d75d8553004dd74d855325e5f54d85530065d54d8553004dd72d85531565e51d8553156d651d85531565c51d8553156d621d855303cde70d855325e5f50d85532cd5f75585530955d759815309d5f75581531659e74181530059d741815315dce7218153005cd7218153155d67118153005d5711815301cdd751815303e5d751815303e9e7418153004dd741815303e9d74181530049d74181532c65f54181530065d541815303ece7218153004dd721815303ecd7218153004cd721815303ed67118153004dd711815303ed57118153004d571181530065e51181532c65c511815303e5f501815303eda50181532c6d9501815317cdd75d954301cdf74d954301cdd74d95432be5f54d95432be5d54d9543004dd72d9543004dd71d954303cde70d95432be9f40d95431959f74595432b4df75595430065f7559543194df74595430069f74595431665f545954317e5d5459543004df7259543004df71595430065e515954314e5c515954303cdc705954314e5f50595431669f4059543004dd75d894301cdd74d89432965f54d89432965d54d8943146ce52d8943146ce42d8943004dd71d8943146cf21d894303cde70d89432969f40d8943146cc20d894327d9f7458943146cc625894314d5e75d85430055d75d85430065e75d8543004dd75d85430065d75d85430045d75d854301cdd74d854324e5f54d854324e5d54d8543004dd72d854313ed641d854303cde70d854324e9f40d85432ad9f74585430859d749814308d9f7458143005cf7258143145cc725814314d5e75181430055d7518143145ce7218143005cd721814313dd67118143005d5711814303e5e7518143004dd751814303e5d75181430045d751814301cdd741814303e9d74181432a65f541
  | 9 => 0xc8119082fba35adc0b809f0000001de1c70801bc0d0a9e07800019b8000680e6b0e957a938020000420000280a02800420807000048040020121600500000802c0000500007000000056010000070000240180f0140040980100000401000004054018020080080080800402800022010014018000300200400101c0040100a00005009007000028028010020000000201a00c0180700e0180380000a0041c80400200c0100500c008000090ac0000400100003c01800000004018080040140884402c05c040330000280000000c018048000060040280200400000003104004020050260000080a0100340000504401c0581900a02c00808004000280050040080000000e06801080000024010020040580700000203c00810000020008030000480880d01601802011000004000010020000000000c004000010100000d806002004480290080080f0040060a0008000320300c80103e03c0000900001c0d002004014038000240200080c00001002000008000028290020141780000e0300300301002000010000000000040060400180f008010090000120640200a004000018000040f8000110000080e0080600100480d0080200080200c02c0800701c008048060060042a03300c0000000c006030098000020240400003e0040e80a0020080280500e0000680d00601c000070040000000202a0000b80800400000800002000000040080000080401a11c038070020000000b0060001e8020000040d80103401c1280101a0100381d0000d40b02913e0200380000000c0002702005403001020040028000540100080001c0a407002066000008110000280080b00000c00000036008018040180380301900c0540300405c024000000020100200401002801800000018088040140140900000001001001008028018000100d80100000002c0101500c0040182c024090050220020040980100a02000000018004038080000180600201c0000081100602c0181d0100001500a038014000250380500003f0000080001100e0201e00501c0040100600e008058040247d75d895402cbd74d895401cde73d8954004dd73d89540247d75d855401cde73d8554004dd73d855401cde73d8154004dd73d815401cde7318154004dd7318154014ee7218154004ed721815400cf67118154004f5711815417e5f7658d540071f7458d5414f1f6458d540055f7258d540071e4258d541671c4258d540055f7158d540065e6158d540065c6158d541671f4158d540055c7058d541671f4058d540253e74d895402d3d74d895417d5e73d89540055d73d89541772e42d895417d5e73589541772c425895417d5e73d85540055d73d855417d5e735855416e74615855417d5e73d81540055d73d81540065d63d815417d5c73981540055f735815417d5c7358154
  | 10 => 0xa250000fb24a1c30b90d319b2bb1490da9941ae02e171036a082f592d2ccaf5238a5289c14e0628001d6a4f8f424200000000000024d84b9698000000588c21bc8820000aaa4f0000209030001ce2929e800011a11b800300a39ad080017c93c0002e70920b01ed2958001c50002642d616325f8000000ba9d50002bc28e17ea5e8810001838062f694c00025c17e0c30000000000d180000026c10b8000001e98358000001c827c23e8001912502872c58000a32cfae32fb10a9e426eb130002349861b00d41e4af290996b1171a1a572260890879072b6a8300696c1d9a9600001897622c81ca192be162299a65af7ac5127ae40a18002e4931abaa6e1898002578d911dadc9040000000942d18643082e90d10d28900000eb3109708eea60a5aaf1a5c87486e9a81e62e080022b88414300000000000000014480000006dabd8000002c900021f0000000000e00000002d53072a5a03ad296f22a00b0002d48448a6aadac18000d8afe85d2dd00b92f1ee1e38001539771549672090300e38001b28ef034ad59df97795224c8dd0560be06323baa900d96caa62a80cfa129a88c5ad924b8cb2aaa6bad39909588fa03315014a14716e97420b9c18bd94287a103af82209b51b6ad68413022281100c2851a85a4427885e1351cd03d2cf2dda2001e1599e29840081b91dc9b71628dd817a0e8e29e030aa668c49d09251f80240e406c800a9911495419f1fd0fb8ec9aa151110983251a919370a2238072a2f8a817591ea7291f1bf2672ad1e0a09905012a591a90421af89719e94f1ac93f93d0041ec03114d13685322c027a7695b2ed96d8769359f31e2088ae38500f8a3f9282249790a78c3acb1179ad82c83b1fc255ab22a097f80000000014f8002a39f682b01d8afaff18da2f00022e80024480000000007607b21b104984a9000018183e0000000000b60002b12b00000001f9887231b018e5a4703e84327f91f9cc06e22400016d2be800000133979800078800048921abf8000000000001928002a88001601ff0478001a60ab9c60482af9209801fd8df1fb2341c28000000001782511ee9fa8050fc1738ae9f09128898bd0f9aca8e31652a780121824802f9e526388c0048c60d704920113124928e921284a3a88d8fc8ea09a2d989cae1a048002cd16e0ebab89060be8609b59568388700c6800208abc98681eac890d2068089c492e80f80000000003c0af0f19c68001b20002a685a8001288eaa33b12ab5ae1222211911ac31bb1011d780010ea508000000e99e580012fa760e80db2498ad8000000fe8648001b600000012280021a0b6a8aa2b0ce0000f708b30c800148800085297a8380002da62a6b0bc94d9c38670470b300028c8001f4ac98000002df0000000c121e2f62980bb8001a48000000000de00017892a1f42ecb08a7
  | 11 => 0x678b5ac80000000002368000000000002932f2000281852a428000e1ae7af904400009a8c8aeab060ac26d0cf0000002ac17509b18f03f80020f9b79e1a1030e1678001dd10c0001ea19d04e2158002f428b0939fe9cf05816480000a86b05f29519313e8f3a3c80924392c85f9e10831e91a30930c0998aabb0f0cdac7237a148bc00014b8001f38000512140000000f58718000cb88d05215f00d1a00000ae2258f50a280f1a09498a88918002ee88695600005a10a2948001c410c99c22e1ba212140800000314a018001e30e221c82680005c06b8b50002d79058000003042ef000013a4023e0798b8b09a4130b1182f131380012e2af0000000002d30000002ae8000000d78d5a238000000108000ac8712f88b22d1000193ade80009e8001cc972863a8a0000000000000000dc966aa02c23051ca226b118000c80000370001d584f2298002550111d319a8cd0002fa8a70340d218a06230c043a9205eaefb059a38172ae1f786c0da0339be1689268d39b895700007580029891685b08ca702e81f60001f280008e8000ccae01cf80011a8001b99348002a71bd2ac9f8a9a829a5d21e89b839a1a90e15c138971a45a022b793d88a00000009800023c21798e80000018c800000221a4a8000000002488000000bf9608001f22a987ea5b82193a099800132a521fe31593780013b11cb0781482f000173025918a05a2291c0000461458f10c90c72a2a7318a8329baafa2f30198f828d1f903780012580004d1478c78690f31958c01321c0800038042a648000000002bb8222758002f72ab11b00020a81f000277123a462b52d890da469202171d912ba0297b065a1517aac28541c9941a6320e20d2ff9581a69292c791e115a7b9882d40f22a4a28854abf2698a9279a078232749b096f9142040750f2ae6231266073ada91d09e0c530694eabd1531d20ff96607904b0cc188a541efacc22d1cb88298780029d8732e6a000fd0000ad3028000b998b92202ba2702d20c0000000000002eb08e01401595f85d8001dc05999200012a9be8458ceab393326a8bf17f0001c923730b8002008002db1612b7061a5f00026500000000304f9af28928999523207d82127a9cd9ef07e001a5a0a1282a7f0000d99ed9fcab61d292c1df277906888219a7e2970182c38001fa05519e03190906d0272f3a860961f193900030a0df99f803a3b197b000f080c28f841a912c694104ca432e98191c20002f4aa11968b3b0fa612111da00023a26f0f92791820a60ca96a161a9f1eb81b80018907d1abaca00015aac0002916174a841231d1a3d9b3a9c8b1218a8895d80001a12b000180ac0853a942b9938050a5d89f8950958969ea9768b4a53260077a0dacb99a30d2f9afc0001de80029e9298002a50b70002fd07f9d492605917a17c0b08e12c493c823
  | 12 => 0x1f115e9ce9d714503a0001d386f01b1e7902af081c0b78bb24e01314cab293002c0071c019983521c16a97d0d81120dea8ba1f83a88a8a5ae51152c41d618b1ffac61ecab40000a4a1b9442851078000000fa97205c8e51b480013a8001cb1f58000003152df97000007ca7a0e0ada24b1919a70000570000860000a086613f000000303a73a80a41a8680000021d8078308c98000ca06880023d0000248000e4a8000012d8000001a581514b0910b2ad82d21d40000e60409ca8002708000000002ea00000000000026a1a51f0210a690a0069adbaa19e8ab800e9bb9a79c7ae88d000018580000000000000017b8000002ce9b80ab2621558aa27d26825b10f9f5247ae2a329508002782599c103bb140291971b1acda8c27d86108f000304aee16bae20ec06a2580dba451aa809a4d30d800000261b1220b07c2ec13420702610201606a884a71000094a0a00007403f29d0000002a41a10002b90c40000001008f001680029a00ca162909518002e593097d8000002fcafd93622923002a00a0a401f9b40001130e718faed2350000000401949468001e715c8e898c23319c82804a1d100595b822a881ae9da9638499d803227e856a7201a9c88f628f0200720f79192750d50fd8003092aa05592702e8e79850ff0d480015d1421ac0c1ace0dc24ea67ade1a20ee2a202893e2053032409249692060b41a29ad10b22a8f68a999d93987b8fe29f80019900009794007aad70808001019d00e915e1e68a3a230efac124c2ba1d89592d000004aa0ca16a8122d98e1ab26ca71ab1924268aa302a9dba5499800e28d866a5e2b0a56a7b310046a823111088121c58a519010f0ed0020ed9a998d25896423615506026f9111b304c04515281016583cb0115a23088f982898a9bab48360f49b10d6a5398726d9db070a9c2212b307f08b8d61dd885890a1384d80000021d09914823f09d20301d2f008398120f06f82513b839143afe057a9b2969f71462742eb9fb83da130b1a5606505b968000287919a2794a9bf9bd9960928002391a410007709d9eb1138ba04e8818
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xb0c82591548c001c1f04b22a9180038320964552300050fc0ac8aa46000c1f74551628c073c1c84aa2c5180021761375586300062790eeab0c6000c4d21dd5618c00143b083aac31800217a1f54586300042f43aa8b0c600085f855d9518c0010bf0abb2831800233e0976506300060ebb2a8a0c6000e1554585418c00119f0eb2643180025361f54c863000706b22a990c600085f855d9218c00113f08bb2431800293e15764863000547c22ec90c6000ac7815d9218c00158b03b2a431817b91147654863000563c0aca90c605ee4751595218c00158b03b22431800233e1d644863000706b22a890c6038b4485585218c001c8f0ab0a431800391215614863000563c22c290c6000e4754585218c001c8aa8b0a4318002b1619414863000742b228290c6000f0554505218c0a983eecaa281180e7431c954502300060eba2a9b1c4039e0c4255363880010bf0ab8ec71001e1721d6554e2003c4e43ac8a1c40078d487585318800158b03b1a431005e99215614862017694392a8a044000b8b8250d408800119f04ba6c69000217e1571d8d2003c66432ea99240008ce86dd1324800f1990cba264900cb131db544c92017e263b2a89924000d0f745513248043c18c8aa2649000253617714c920005c4c20e099240188cc874cb614800f1990cb9a42900130e1d95450120016643b264a024000b89844c94048001e12a899280900ba8b209645521000467c12e9b1c2000c1d74553638400f0b90eb2aa70801e2721d6450e1003c6643ac49942000a4d8218f654400149b0439eca880029560473d951000526c1487b2a200085e870c3654400143b08186ca880029360830d95100060eba0c632a2000a4d8218c654400b0790eb22a8880ba8b20964551100050ec20cbb1a20008cf825d3634400183ae8aa6c688002336087654d100062b288eca9a20008cd821d943440071990eb126488086a3211624c91003c6a432ea98a2000c5476d9531440018a8ec32a6288002c5610654c510004e2c16e898a20078d4865d131440658a8edaa2628800295219544c51017e2a3b2a898a2000b51851c1314400172308382628801e35219734851003ce8402e690a2042e44654c921440bb4cd0db2a4288002c9610654851000722318ca90a20028e487591214402f4c90ab22428805e9921b544851000532432a890a2000e256455121440015890cb9a4288003911957348510005e0402e690a2000e4465d8d21440015890ca9a428805f9119553485101e72232a8690a2000dc173dc121440016c30a3824288002e86107048510005a9c2a632822017e6065486504400b8b0eca9aa088002d4615315411000e703b242a822000f415348550440017230898a8088003c4551315011000790aa242a022000f8143485404406798cec90c60880e391195218c110
  | 1 => 0xb0a382c690802636107058d21004c6c26eca9a42009c581dd95348401a88a3bb2a69080271e057654d21006a228aeca9a421594e87d95534840119b0dba2a69098b511477454d2100687ba2a8a9a422ab4481551534845568d0bb8aa6908ab51a177154d21156a2c2ee2a9a4200d4765dc553484c3a88cbb8aa690802716137154d2130ea3aa6e2a9a4200d4554dc553484c3a8ea1b8aa690802336187054d21004c6c20e0a9a42009c5811c153484c1a88a2382a690802536177650d21004e2c0eeca1a4200c8c645d9434840138f02bb28690802716077550d21004e3c0aeaa1a423cd44515d5434842b31d0fb228690802336187050d21004a6c28e0a1a42009c5811c143484033490eaa2829097fc194d54505210be93c3aa8a0a422dd2487551414845da4cecaa282908bb491d954505212ff8341aa8a0a4200f058355141484bfe0ce6aa2829097fc198d54505212ff82182a8a0a423db87845cd4148401e0aa8b9a829080271e1d63505210de623b2c6a0a4200b878458d4148401d08c8b1a8290803c15516350521004e3c3aa6a0a4217d447554d4148401e0aa8a9a829080349553705052121ce3c0ae7b0242158cc8758d6048401918e8b1ac0908ba8b209645525003c4e43ac8a1ca0078cc87589329400f1a90eb0a632800233e0974d8d50004a6c16e8a9aa03285c87d9153540010bd0db8aa6a8002d46047054d5003c2e432eaa1aa00785c865d5325400f0b90cbaa62a80629321953c85500ad26432a690aa000b478154d2154055c88c2a9a42a801e1721d6554e4003c6643ac499480078d487585319002f4c90ab0a432000287219735514000706312e6aa28000b18805cd5450001a32e7b82a8a0002ca608705514000598c08e0aa2800085f855c763500070b90eb2aa6a00aa952056554d402df06312a8a9a800789c865d5435000f33100baa86a0002476177150d40005c4c10e0a1a8000b91811c1435005d85cecaa6c4a00029361463d894000526c28e7b128000a8d841cf625000149b0b98ec4a000233a1c30d894000526c2861b128000a8d840c3625000158b02186c4a000383553631894000526c28c63128000e0d5418c62500015190ca18c4a000349551711894000663b1ae23128000cc4635c46250001b0a86b88c4a000217614764c94000647a10ec992800789c865d13250001838ecaa264a00bb83189544c9400042ec28ec98a800789c865d1315008dc18c4aa262a00bb0b1d954c85400c5464328790a8000c2c76551215000158b03b1a42a0056a32194348540006463b28690a80008cf825d3658c0010bf0ab8ec91800313d53725923000626aa6e4b2460008cd81dc9648c00158b02392c91800233e0976552300046bc0aecaa46000a1d849d9548c00143f08bb2a91800293e0976552300052bc0aecaa46039
  | 2 => 0x974d85320042ec3ea9b0a640085d87553614c8cdc1884aa6c299003135d742d85320042fc22ea3026400c4c425d4604c80189e42ba8c09901f13c81751813203e26902ea3026400c8c425d0604c80183d0aba0c09900307615741813200647c12e83026400c8c825d0604c80191e42ba0c09901f23c81741813203e4d102e83026407c8d205d0604c80193240ba0c0990021761f54181320060eba6a8302640085d87550604c80183ae8aa0c09919783109541813200466c3e843026400c4d75d08604c80191ae9a10c09900331c8571181320062baa2e23026400c55545c4604c80198d04b88c09900331609711813200663a12e23026400cc4425c4604c80f98e40b88c09901f31481711813217517416c8aa2a20085d85dd943544010bb0bbb264a88a7071d973551410058bc0ae6aa28249d1771551635040119b05bb2a6a080e17a1f6554d4102d0e432a8a9a8200c1f7655153504010bb0bbb264a080307dd9544c94117706312a899282038ce87d89325040119b05ba2ca98992b160672d913100627aa2e5b226200c4d545cb644c43119f02b96c89880331c4172d913100466c14ecaa2622ac5471595544c4071ad0db8aa89880287612765513100526c14ecaa26200a1f845d9544c4018a8e2bb2a8988be95a1b71551310060eba2a9b12620085f845d4604c40189e42ba8c09880313485751813103e2b882ea3026207c5a105d4604c40f8aa20ba8c0988031644175181310060f42ae83026200c1d855d0604c40191e42ba0c09880323485741813103e4b882e83026207c9a105d0604c40f92a20ba0c0988032644174181310042ec3ea83026200c1d74d50604c4010bb0eaa0c098803075d1541813100627aa2e43026200c4d545c8604c40f98e20b90c09881f3144172181310062741aedaa64200c4d835db54c840189c86bb6a9908031350d76d53210062798aedaa64200c4d315db54c840189860bb6a9908023361b7454f2100687ba2a8a9e42008cd861c153c840131b08382a790802716047054f2100466c30e0a1e420094d851c143c840138b02382879080307dd15458d2123706212a8b1a42008ce87d09634840113b09bb2a69080e17a1f6554d2131ea228ee4a9a420085d85dd9434840713d0fb22869090b51145754c92110e46322e89924200d0f745513248443c18c8aa2649090ad1a17714c921004a6c28e0992420098d841c13248409868ecaa2829097fc1cc95450521016623b264a0a4200f05544c9414848738f02b9ec89085e59a177159121005a3c0ae6aa24200d44715cd544842b19d0f322c690802b26006458d2100687ba2a8b1a4200e0c64551634840168d0bb8ac69080351a177158d21006a2c2ee2b1a42009c584dc56348401a8ea9b8ac690803515537158d21004e343ea2b1a4200d4775d45634840129
  | 3 => 0x291414a710e8800000000e68003c0808000f90000009c1890002302d0000567f4671c714473c0e800000544ea0090000402c0a0001900009020010080a038040080b00c080240d0080300c00028000041000401004010000000801004060100602c0302005024000200104806000060080f0000000000000000400800004008050281100002000000080400c000041001c00060000280b01009000010080300005050010700004c070000c0000801005040000100008006010010301d0100001801000030040b0001b0242a0ac000280500017010040040200c0200c070040101c000080012c0000c0303c0c004150000f0040000004000090000000002034000340a0140500587416e8b1aa800d0f7290963550014b30030ac6aa002536087058d54004aac08e0b1aa85c91f845cf61550b923f08b9ec0aa003151c5635815400562c0ce5b22a600c4f855cb6454c018990ab96c8a980313d5172d915300626aa2e5b22a6008cf815cb6454c01898a2b96c8a980313d4172d91530062a28ae3b22a600c4d729476454cb761d05b22a8a980383a0b645515300706c16c8aa2a600a1d81d915454c0183ae8aa6c4a980307d5174181530060f42ae8302a600c1d855d06054c01838a2ba0c0a981f07d41741815303e0ea82e8302a600c4f545c86054c0189aa8b90c0a980233e0572181530062628ae4302a607c4f505c86054c0f89aa0b90c0a98031514571181530062bc2ae2302a600c54855c46054c018aea8b88c0a980315551711815300663412e2302a600cc5825c46054c0f8aea0b88c0a981f34941711815303e2aa82e2302a600cd1505c46054c010bb0f288c0a9803075d2511815300626b94a2302a600c55719446054cd783eebba2caa19aa8761275d85431942fc22ebb0a862f85d845d76150c0189e42baec2a18031348575d85430060fa02ebb0a862f85d845d46050c0f83e80ba8c0a181f07501751814300627aa2e43028600c4d545c86050c0119f02b90c0a181f23d01721814303e65202e43028607c8d405c86050c0199280b90c0a180315d5171181430062aaa2e23028600cc6825c46050c0198b04b88c0a181f25d01711814303e69202e23028607c95405c46050c019a280b88c0a180233a1f42595320042ec2ee2b2264008d5819d9544c8d3c1885b2aa8991a383109655513201c67436e4aa26400a1d849d9544c801c18853b2a8990029560676551320050fc22ecaa26400e0c425d9544c843c1d05b22a8990878360b645513233f06396c8aa26400a1d81d91544c8cfc1e43b22a89919f83c83645513217d27436e4aa2642eb0e84dc9544c801c1ec9b92a8990028761275d85320042fc22ebb0a6400c4f825d7614c80189904baec2990031310975d85320062790aebb0a6400c4d215d7614c80189e40baec2990032310
  | 4 => 0x380d0449b43ea110279960c67fcba8b6374240859882b408ca310c2b03f41f07c02c5642f1ca372004370191781e49213f0a26505f93b0c40003a80011c6c4c185b13e0009291c0000dcd71b83b65406d0002327a49090a3141a0da85332a4104594d2a40007114514e07c0008f2ce668df90e2c6478270931c67e4bd9d21f8480c715c00070c000000001185515d30200c2a8d53645acbe99701248c089f004c52c150a005c1007b80d2a8694d08711ea7e0760d00d87d08280b2bc500381030f466c218380ae0c8aa83d07250cf28ea2665ccd809d0ba000000000d65108b8ab000000000dc25c678000000001983b95b23a73812182146440e60f4234218c98f01fc05000020100000001f60000408c0870822e08a98c0004bc5a1792a678c17899000000d687d000000981e4050000000451f40f09598020c47c0006001e2f89500000053c000001d24d80016a32219ca50d9278680e9800000000cc8c4000000878003ba000249921747141a8000006cc6c186000614000d1000674e08982ae5f8000000fc7640000027c000001a40007a04d902000000f98923ce318329c90000006483b1520003783a24e298969c80625f0040043d604c250183ac61c028733e43d8001350985bc000ad000000fba060ec5c8d58c31f0768011e62220000015f11a3c8de80015c37c0000000000000000402088db939000134000e818a504590d740a0000003f024000701420000842391b1947544d17416a700679373f80006e800000378bd0d40180006384b3ae320b7000258538000c01025c48b0000d463cf70000001580001e0002a00a8000002cc00147000000a400012a09c00161350150001b634481cc2000000358d18360001e00000034e01c000002fe304b20000000010019f000810580303bc598f882c000000000001e20004e19c2d20000001b01c000001ed3b870877000376000000ff17230800122000000421ec000290050000001b400000264588e313d3c22b09a0003f66bcf10cb0002088018b298420b6852122334d30003787bc001df0005b0000002ec000001680006a4c6888000448001091980004199804a0a44f1ac0a02845d9313964045e80005a1fc730740b24a4000ed1a4000031491d63cc89800250434ec19037c17cbc0723d4228838000f61a44b8db0b8000b80000002dc708d3000258578000c2190720ef000214ab1602ee4982c1d00000cc5881a3547e8240fb0843940009440639c000173fc4e8b
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2cd95d3ccc440000c470ecd00000b12095414d14f000316ce418257400011c60000000100058011164000000014404d5587d0ce92d180879003c8c5534ac68bd6800a83928e0fc9d6090dd306c34a0740000f8012400488020648548c9084088b40150f4501c280000157000000154000000990400a44c5c0cb938c0008850204a800a280071408600060018a0c0050a04ac1820004004004c164682dd1635500144691e1572d915300503650515cb6454c014499014572d915300505650515c76454c014519014571d91530058164682d915454c0101d98145741815300506640515d06054c0140d94145721815300512640515c86054c0141594145711815300505650855c46054c0145190215711815300611215825c46054c01c0b54501721814300704d51405c46050c0120d9810a765513200581644429d9544c8016099010a765513200681109819d9544c80160591109765513200582640425d9544c80120d98d93725513200503a53825d7614c8014459110975d853200512640425d7614c8014859110974d853200522640425d3614c80180c4261d54d853200413e6175d0b614c80144591109751813200512640425d4604c80148591109741813200603614825d0604c80148591209741813200522640825d0604c80180c4261d541813200431660425c4604c801c0554109711813200530640425c4604c801451901c5765513100710c85105d4604c401c8321441741813100413660305db54c840140d940c176d532100511644305db54c845dc0476551325052100550640715cd5448401609901915458d21004c165285dc5634840150594a177158d210045166051dd95348401505941477654d210064161051dd95348401541901477654d2100541650515d95348401541901457654d210061114586dd1534840114598d977154d2100611145861c15348401904516107054d2100522640645d943484799048760d5450521005a06406458d4148401907875516350521237011d95458d414845550497551535052100641e1d5454d414840124696e05534855000581644625cd5450001309922017355140004c4644805cd545000120d95219431894000701553635c462500014459518d711894000701550635c462500014849650d71189400058164482591548c0016059421561486300068161954505218c00140e96dd1544c920177021d9544c9404800180d746086319510006051d98419531440014459718c65485100068161063195214402f2249859154485101750925d645512144001605941957348510004d0654805cd21440013819420173485100058165065d8d2144055c407654d2154110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x90688000020000c59410068080a00078e08071049898821900a00500b4842b04b88c0a9802205a9109819d9544c801500d0084c0cecaa26400a016844261d54d8532005013402130eaa6c29900300585644825d0604c801402d0884c3aa83026400a026804261d541813200600b30aa084b88c09900340154640425c4604c801082d4b0828eeca9a4200c40611901477654d2100500b4828b0dba2a690802841a014586dd15348401402d20a2c30e0a9a4200a10680516187054d2100420b5228b08382a690802901a0145841c15348401202d292ca1ae23128000c0165d8418c6548510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x94c
  | 7 => 0x1
  | 8 => 0x124c
  | 9 => 0x98c
  | 10 => 0x128c
  | 11 => 0x128d
  | 12 => 0x12ca
  | 13 => 0x12cb
  | 14 => 0x12cd
  | 15 => 0x12ce
  | 16 => 0xa0c
  | 17 => 0x130c
  | 18 => 0xa4c
  | 19 => 0x134c
  | 20 => 0x134a
  | 21 => 0xb0c
  | 22 => 0xb0d
  | 23 => 0xb0e
  | 24 => 0x154c
  | 25 => 0x154d
  | 26 => 0x154e
  | 27 => 0xb4b
  | 28 => 0xb4d
  | 29 => 0xb4e
  | 30 => 0xb8c
  | 31 => 0xbcc
  | 32 => 0xcca
  | 33 => 0xccd
  | 34 => 0xcce
  | 35 => 0xd0c
  | 36 => 0xd4c
  | 37 => 0xd4a
  | 38 => 0xd4d
  | 39 => 0xe8a
  | 40 => 0xe8b
  | 41 => 0xe8e
  | 42 => 0xeca
  | 43 => 0xecb
  | 44 => 0xecd
  | 45 => 0x104a
  | 46 => 0x104b
  | 47 => 0x104c
  | 48 => 0x1a8a
  | 49 => 0x1a8b
  | 50 => 0x1a8c
  | 51 => 0xca
  | 52 => 0xb0954
  | 53 => 0xcb
  | 54 => 0x180c
  | 55 => 0x198c
  | 56 => 0xb12d6
  | 57 => 0x1052d3
  | 58 => 0x104a14
  | 59 => 0xb8b14
  | 60 => 0xe8b16
  | 61 => 0x178a
  | 62 => 0x17ca
  | 63 => 0x170a
  | 64 => 0x104b14
  | 65 => 0x1a8b14
  | 66 => 0xccb16
  | 67 => 0x16cb
  | 68 => 0x105554
  | 69 => 0x1a9554
  | 70 => 0x104b53
  | 71 => 0x184c
  | 72 => 0x19cc
  | 73 => 0x16cd
  | 74 => 0x104b94
  | 75 => 0x16ce
  | 76 => 0x140c
  | 77 => 0x178b
  | 78 => 0x188c
  | 79 => 0x160c
  | 80 => 0x17cb
  | 81 => 0x1a0c
  | 82 => 0x170d
  | 83 => 0x170e
  | 84 => 0xcd
  | 85 => 0x148c
  | 86 => 0x194c
  | 87 => 0x17cd
  | 88 => 0xce
  | 89 => 0x14cc
  | 90 => 0x164c
  | 91 => 0x104ed3
  | 92 => 0x178e
  | 93 => 0x14a
  | 94 => 0x12cb16
  | 95 => 0x104b8b1c
  | 96 => 0xcb16
  | 97 => 0x16cb16
  | 98 => 0x178b16
  | 99 => 0x170b16
  | 100 => 0x148b14
  | 101 => 0x1040d3
  | 102 => 0x1056d3
  | 103 => 0x179053
  | 104 => 0xed053
  | 105 => 0x17d053
  | 106 => 0x185054
  | 107 => 0x1a9954
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 74
  | 6 => 1139
  | 5 => 1580
  | 4 => 520
  | 3 => 94
  | 2 => 20
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | 2 => packedAt gbK2 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | 2 => gbHint (packedAt gbK2 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (2092+((h/24+packedAt gbK7 (1924+(h % 24)*7) 7) % 116)*8) 8
  | 6 => packedAt gbK6 (46312+((h/379+packedAt gbK6 (42143+(h % 379)*11) 11) % 1503)*12) 12
  | 5 => packedAt gbK5 (81626+((h/526+packedAt gbK5 (75840+(h % 526)*11) 11) % 1897)*12) 12
  | 4 => packedAt gbK4 (32410+((h/173+packedAt gbK4 (30680+(h % 173)*10) 10) % 687)*11) 11
  | 3 => packedAt gbK3 (6797+((h/31+packedAt gbK3 (6580+(h % 31)*7) 7) % 124)*8) 8
  | 2 => packedAt gbK2 (1650+((h/6+packedAt gbK2 (1620+(h % 6)*5) 5) % 29)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f83f81f0c0c1f0e0707fffffff11249820fff
  | 1 => 0xc1fc3fe1f00fe1f007f8e0f078722db64d3293
  | 2 => 0x1ffc001fff001fff800ff007f8cce3871c31c
  | 3 => 0xfe000001fffffe000000ffff800f0fc07e03e0
  | 4 => 0x1ffffffffffff0000000ff0007ffc00
  | 5 => 0xfffffffe0000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2004800000002020100011008000000800425
  | 1 => 0x409410c13044a150123068a151600492451292
  | 2 => 0x11da814555508164b010ba8267244e38514318
  | 3 => 0xb4520289ef6ed4406062dccf424f0fc07e03c0
  | 4 => 0x200004108a8b188944c60004000bb0002aa800
  | 5 => 0x3963271c0302100180841008040ffb6d000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfefeeeeefefeaaa8fefeeeeefefeaaa8fefeeeeefefeaaa8fefeeeeefefeaaa8fefeeeeefefeaaa8fefeeeeefefeaaa8fefeeeeefefeaaa8fefeeeeefefeaaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_34662
namespace PEqualNP.Outside.L_meta_34662
open PEqualNP.Outside.L_meta_34662.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 17 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 16 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 13 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 16 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 17 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
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
theorem bs5_4_0 : Interval s5Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 13 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 20 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 94 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_512 : Interval gbAtlas 4 512 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 520 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)))))
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
theorem bgb_5_1568 : Interval gbAtlas 5 1568 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1580 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))))) (concat (concat (concat (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960))) (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)))) (concat (concat (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)) (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344))) (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568))))))
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
theorem bgb_6_1120 : Interval gbAtlas 6 1120 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1139 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 74 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 16, 20),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffffffffffffffffffaaa8fffefffefffefffefefeeeeefefeaaa8ffffffffffffffffffffffffffffaaa8fffefffefffefffefefeeeeefefeaaa8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,16,144)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,16,144)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_34662.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[8,3]⟩,⟨.or,[6,7]⟩,⟨.and,[9,10]⟩,⟨.and,[2,5]⟩,⟨.or,[0,1]⟩,⟨.or,[13,7]⟩,⟨.or,[4,5]⟩,⟨.or,[15,6]⟩,⟨.and,[14,16]⟩,⟨.or,[11,12]⟩,⟨.or,[18,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
    exact ⟨mono,19,monoShape,by change 12 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_34662

open PEqualNP.Outside.L_meta_34662 in
theorem PEqualNP.Outside.L_meta_34662 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
