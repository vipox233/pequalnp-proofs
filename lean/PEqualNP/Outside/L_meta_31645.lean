import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_31645.Model
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


end PEqualNP.Outside.L_meta_31645.Model

namespace PEqualNP.Outside.L_meta_31645
open PEqualNP.Outside.L_meta_31645.Model
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

end PEqualNP.Outside.L_meta_31645

namespace PEqualNP.Outside.L_meta_31645
open PEqualNP.Outside.L_meta_31645.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4080000620ef32de32dc32ec32cc32
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1080d4058000014e528cb1ca8196355032e328865c5510cb94a0197254032
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xa03055454432c2551500cb415154032
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
  | 4 => packedAt s0K4 (84+((h/1+packedAt s0K4 (80+(h % 1)*4) 4) % 10)*4) 4
  | 3 => packedAt s0K3 (197+((h/2+packedAt s0K3 (189+(h % 2)*4) 4) % 13)*4) 4
  | 2 => packedAt s0K2 (116+((h/1+packedAt s0K2 (114+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfe1ffc7f07c7ff0f1c7e3f07fc701ffc33333f
  | 2 => 0x1fe1ff8ff807fff01f8fc7f83f801ffccccc3f
  | 3 => 0x1ffe000ffff878ffe00ff8003fffe3830f0fcc
  | 4 => 0xe000000fffff80fffff000003ffffc03f00ff0
  | 5 => 0xfffffff0000000ffffffffffc0000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x424828813009100304120901941144a8111315
  | 2 => 0x84845012019220300884423028828950444c2a
  | 3 => 0x4844992452834155200e90528d24c2190f054c
  | 4 => 0x81996248a50432aa5d2000a5324b1062f00ab0
  | 5 => 0x11118000c62444cc924924c6000c0003aaa000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfffcfcfcffc0c0c0fffcfcfcffc0c0c0fffcfcfcffc0c0c0fffcfcfcffc0c0c0fffcfcfcffc0c0c0fffcfcfcffc0c0c0fffcfcfcffc0c0c0fffcfcfcffc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_31645
namespace PEqualNP.Outside.L_meta_31645
open PEqualNP.Outside.L_meta_31645.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x360088028000004a00a803c000000000b80141800000492263ea000042084000001580000068100111800064e1a1e400035200000000139d002c60500a8000001c00000600004000000004c00e0058022000000012000000000002000608000000c000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xd001514c0000000070d4000010200000000000004000b800cc00480108008c00007400dc94b408f4540100000000a954c400001c0000006000355c00900120e830fcf024b07c0088000018010cbc04140000000000013569400000015928002ca400a0011130011c0c5c0000007828c0e5452c380000013c00011914680000ecd9612400000000008504000064e000980000000000005138004cac0000000000016400005800c800009c6cf8443d488000000a02000a0200040000000400040200000a000c180e04020600001403765190eeaa321dd94642baa8c853e540ca7aa819734c832bb2886575510caf4a0195e540329f28c833d50906bca620d754c41b7290836d52106f4a020de54041cf298839d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331b7294636d528c7688318cfd51319e2a263b4414c67ca990cf55321af29c435d53887688310cfd51219e2a243b4414867ca3a04f55240bba8a8174515036ea2a04f14540da28a81345150376a0a04f950409f2a4613d548c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca9104f55220afa9a415c534827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f55210da20c21b9408427ea8884f15110dca02213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x498522000406b9a99cc24216a0400a38002c02078ca82015670650003493254032c354d521071a5354041c654d501072a5254041ca54950107255210631ac580418c6b16010531c554c41886b16010621ac58041487166314540c558c51503266214540c9588515033160145408d185548c2346155220ac58041842b061502108e19540442356510410c554c41043255210410
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc05000080001885496010631c22a6b008310e05635885150308b1ac028a81885896014540
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
  | 4 => packedAt s1K4 (2697+((h/30+packedAt s1K4 (2457+(h % 30)*8) 8) % 176)*8) 8
  | 3 => packedAt s1K3 (990+((h/8+packedAt s1K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 2 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 3 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x4028004410502000420502480101429008c025
  | 2 => 0x24448c080c88910601209086c832244c221c92
  | 3 => 0xa88094912409402a8802a41252500944870518
  | 4 => 0x41529224820125515480024a4a4a009700ac0
  | 5 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_31645
namespace PEqualNP.Outside.L_meta_31645
open PEqualNP.Outside.L_meta_31645.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x15000000052380803000000004cea23e000212c1c01e009d51000300020c3d21c465c20022005923465426369400a563501400201890a0c10010c010010000c003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x4d4541025a1f00240e2b371928160d3d3f38000f532954000000000012400b4a263b003e3a464b002a103549250c010055135721001d4805200000110000002700181c070a0000064c00581b00304f503400003600170052144722003c5100040933431a004e0039032f1e004223081559562d2e44322c00311e1a081000200687060c086002000700000840000280020010503765190eeaa321dd94642baa8c853e540ca7aa819734c832bb2886575510caf4a0195e540329f28c833d50906bca620d754c41b7290836d52106f4a020de54041cf298839d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331b7294636d528c7688318cfd51319e2a263b4414c67ca990cf55321af29c435d53887688310cfd51219e2a243b4414867ca3a04f55240bba8a8174515036ea2a04f14540da28a81345150376a0a04f950409f2a4613d548c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca9104f55220afa9a415c534827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f55210da20c21b9408427ea8884f15110dca02213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2ab9253028c70e116024000a028a600020069882c786412e029a5393493254032c354d521071a5354041c654d501072a5254041ca54950107255210631ac580418c6b16010531c554c41886b16010621ac58041487166314540c558c51503266214540c9588515033160145408d185548c2346155220ac58041842b061502108e19540442356510410c554c41043255210410
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x84100c1885496010631c22a6b008310e05635885150308b1ac028a81885896014540
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
  | 5 => packedAt s2K5 (788+((h/14+packedAt s2K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s2K4 (2667+((h/30+packedAt s2K4 (2457+(h % 30)*7) 7) % 121)*8) 8
  | 3 => packedAt s2K3 (990+((h/8+packedAt s2K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s2K2 (249+((h/1+packedAt s2K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 1 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 3 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4028004410502000420502480101429008c025
  | 1 => 0x24448c080c88910601209086c832244c221c92
  | 3 => 0xa88094912409402a8802a41252500944870518
  | 4 => 0x41529224820125515480024a4a4a009700ac0
  | 5 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_31645
namespace PEqualNP.Outside.L_meta_31645
open PEqualNP.Outside.L_meta_31645.Model
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
end PEqualNP.Outside.L_meta_31645
namespace PEqualNP.Outside.L_meta_31645
open PEqualNP.Outside.L_meta_31645.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2d0650729421092f568c01c1629388541888f440142e020080000680024a590130000e8030792004c34d8c0e644ac0a5c0153e0004001830070c2204580002ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x802001f47c00001c49e00000b8006b00000f000000280000000004800000000000000009446001a428820000000851b000fe482b8804a720008800000711c0e00371ec883a1d8d43e7632830b07e2c8f43a313a96c0000031b09227000000070000008a732a0bd086d2004832002d108160910800506634000000001879002c06800000000174363f2f940de001c19c005343130521a0000066621a05c0039000005a612a800d45e0b0000a131b80086000000000001e1f00010001d000002e00106000e158007a2883c960043800602a001382a183218d020013000000000134000020800227900148007700020642300980560000010400000001170001000701010002011e0000040004000801000001040007150001000100050003000a00bd286877950d0ebca7215754e42af298855d5310aeca2215d54442bd28085795010abaa3995794332aea9c65cf524cabea2995714132af298655e53906baa720d794c41aea98836e52106daa420de94041bca80835d52cc6bca198d754e31afa9263d7514c6b8a098d794c31af29e435d53c86bca710d754e219faa2433c54486bca690d754d219f2a0433d54086bca610d754c21f2908437a50086f2a010d794f40aea9e819e53d033aa7a067ccb40ce996819f31d033a63a04f55240afa9a815c535033ea6a06714d40cf992819d325033e62a0674c540dda82813e541037281984f952309eaa4619e548c33aa9185754a30aea8c615e508c33e811867502309f2a0613d540c2dca4185b54830bb2886175510c37280186795030ceaa061ce520c2baa4187354830a6a9061d6510c2baa2187554430aaa88615e500c3b4a01867d0030ed200619d400c3b280186650030af29e415d53c839a65904f952209eaa4415f53882b8a7106e50220afa9a415c534839a64906e501209f2a0413d54082bca6105754c20bb288417551082bca7885754f10ea98e213e548427aa90857d4e10ae29c21b940842bea6885714d10ea98a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x184c0ab005938a62012800414e80003d480308c01f000001900017893650ba81c34904061c02400b15005a8532e00011113400e00002cab04020f100c041828900300040410005002810095584504ca4d62141318e58054486586054d21c955121087612154021a61813250298604c540a698f50503295250030cc545400c30e5454830c3551520c3455294430c5951510c3155454430d1949510c3455254430a6592500c21d65d0030c354b400c31551d0030a6592400c3495290030d4546400c21f6550030c3549400c3155150030d2549400c3515150030a6d95400c31b6550030e2949400c3195250030e2549400c3095250030e4945400c3195150030e4545400c311515003095584538831853502209319532483185350120e24c9404824d6214e10c614d4084254654c510c614d40443913150110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x10c04280e600400020061245c4604c940912e430262a070152945400c381292a2a0061c05495150030a22e229a8110508754c94048284b90a6a0421441d53150110
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
  | 4 => packedAt s4K4 (4032+((h/45+packedAt s4K4 (3672+(h % 45)*8) 8) % 217)*9) 9
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e3f838e3cfffe3f1c71e3870c7ffe3f0e43cf
  | 1 => 0x1fc7fc0fff0f1fc7e07e3c07ff8e0fc7307d33
  | 2 => 0xe007fff03ff01ff8ff803ff80ff00ff8c38e3c
  | 3 => 0xfff800003fffe000ffffc0000ffff000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8300a01044441040082060a140128224064045
  | 1 => 0x44110824082024082012040224842482101512
  | 2 => 0xa21100900248014480091009204910408a28
  | 3 => 0x48b05b4d22aa0c92f5548050ae496192f80f80
  | 5 => 0x9104620802cc91249a693264c0018024af6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfefcfefceae8eae8fefcfefceae8eae8fefcfefceae8eae8fefcfefceae8eae8fefcfefceae8eae8fefcfefceae8eae8fefcfefceae8eae8fefcfefceae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_31645
namespace PEqualNP.Outside.L_meta_31645
open PEqualNP.Outside.L_meta_31645.Model
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
end PEqualNP.Outside.L_meta_31645
namespace PEqualNP.Outside.L_meta_31645
open PEqualNP.Outside.L_meta_31645.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d243179f00b1c3100d4e200000022128c00a1e057390000da80e192306e21a363a515804c845bb0601d322e0022d2c9c99866408804a68f192a39e805218341020604000280c4800c08800264c18002ffd5009fe5402ff55009fc5402ffd4c07fe5302ff54c07fc53027fd0c07fe43007f50c07fc4302ffd4805fe5202ff54805fc52027fd0805fe42007f50805fc4201ffcc805fe32007f4c805fc3202ffd4403fe5102ff54403fc51027fd0403fe41007f50403fc4101ffcc403fe31007f4c403fc31017fc8403fe21007f48403fc2102ffd400b7f5002ff9400bfd50005f5400bfc50027fd0001fe40007f50009fc4001ffcc001fe30007f4c007fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24006ff08120037d8409000bf8204801fff8824006ff04120037fecb0801aff658400dff32c2005bf99610036fccb080167e658400dfeb2c200bbf59610036facb080027d658400dfe32c2006bf19610037fec90801aff648400dff3242004bf99210037fac908002fd648400dfe3242006bf1921005ffea90803bfe5484017feaa4200eff15210037fec70801aff638400dff31c2003bf98e10037fac708002fd638400dfe31c2006bf18e1005ffea708037fe5384017fea9c200dff14e10077fe8708037fe4384001fea1c200dff10e10037fec50801aff628400dff3142002bf98a10037fac508002fd628400dfe3142006bf18a1005ffea508033fe5284017fea94200cff14a10077fe8508033fe4284001fea14200cff10a1006ffe6508033fe3284001fe994200cff0ca1000dfac308007ff5184003ff28c2001ff5461000ff8a308007ff4184003ff20c2001ff5061000ff88308007ff3184003ff18c2001ff4c61000ff86308007ff2184003ff10c2001ff4861000ff8430801afe608400dffa842006dfd4210037fca10801bfa508400dfea842006df5421005ff2a10800379508400dfe2842006ffd0210037fc810801bfd408400dfe2042006ffcc210037fc610801bfd308400dfe1842006ffc8210037fc410801bfa208400dfe9042000fe48210037f8410801bff108400dfb8842001fec4210037f8210801bf81084015ffb2a200abfd9510057fcca88016fe6544015feb2a200abf59510057f8ca88016fc6544001ffb222000bfd911004ffcc888012fe6444001feb222000bf5911004ff8c888012fc6444015ffaa22009ff95110057faa888027fc5444001ffb1a2000bfd8d10047fcc68800efe6344001feb1a2000bf58d10047f8c68800efc6344015ffa9a2008ff94d10057faa688023fc5344013ffa1a2008ff90d10007fa8688023fc4344001ffb122000bfd891003ffcc48800afe6244001feb122000bf5891003ff8c48800afc6244015ffa922007ff94910057faa48801ffc5244013ffa122007ff90910007fa848801ffc4244011ff9922007ff8c910007fa648801ffc324400d7fb0a2001ffd451000ffca288007fd5144003fe28a2001ffd051000ffc8288007f64144003fea0a2000fd5051000ff88288007ff3144003ff18a2001fd8c51000ffa6288003f53144003fe18a2001ffc851000ffc4288007f62144003fe90a2000fd4851000ff84288006ff6044015ffa82200adfd4110037fca08802bfa5044015fea822000df54110057f2a08800379504400dfe2822009ffd0110037fc8088003fd404400dfe2022008ffcc110037fc6088003fd304400dfe1822007ffc8110037fc4088003fa2044001fe9022000fe48110037f84088007ff1044003fd8822006ff84110037ec208801bfc104400dfa0822001fe04110
  | 1 => 0xbfe504c035fea826000df54130037f8a098067ff404c00dff2026000fe90130007fa8098003f9404c00dfe2026003ffcc13001ff6609801bfe304c00def1826006ff0c130037b8609800ff8304c031ff9026006ff081300bffe209801bfc104c00dffb2c4006bfd9620037fccb10016fe658800dbf32c40059f99620037facb1004efd658800dbeb2c40009f59620037f8cb1001afc658800dffb244006bfd9220037fcc910012fe648800dfeb244000bf59220037f8c91001afc6488027ffaa44016ff9522009ffaa91005bfc548800dffb1c4006bfd8e20037fcc71000efe638800dfeb1c4000bf58e20037f8c71001afc6388027ffa9c4015ff94e2009ffaa710057fc538802dffa1c4015ff90e20007fa8710057fc43880057eb144002ffd4a20017fca51000bfd5288005fe2944002ffd0a20017fc851000bfd4288005fe2144002ffcca20017fc651000bfd3288005fe1944006ffd8620037fcc310006fe618800dfeb0c4000bf58620037f8c31001afc6188027ffa8c4014ff9462009ffaa310053fc518802dffa0c4014ff90620007fa8310053fc418802bff98c4014ff8c620007fa6310053fc3188005ff90c4002ff88620017fa431000bfc218800d7f3044006ffd4220036fea11001bfe508800dfd2844006ff54220036faa11004ff95088001bca844006ff14220037fe811001bfe408800dfea044006ff10220037fe611001bfe308800dfe9844006ff0c220037fe411001bef2088005fd9044006ff08220037f0411001bff108800dfe0844012ffd9520095feca9004bfe654800b7f32a4012ff59520095faca9004bfc654800b7e32a4000ffd9120005fec890047fe64480097f3224000ff59120005fac890047fc64480097e3224012ffd512008ffca89004bfd5448023fe2a24000ffd8d20005fec690043fe63480077f31a4000ff58d20005fac690043fc63480077e31a4012ffd4d20087fca69004bfd5348021fe29a4011ffd0d20087fc8690003fd4348021fe21a4006bfd8920017fea49000bfe5248005fea924002ff14920017fe849000bfe4248005f72124002ff50920007da849000bfc4248005ff9924002ff8c920017dc649000bfd3248001f69924002ff0c920007fec290002ff614801fff30a4001bf98520007fac29003ffc61480037e30a4012ffd452007ffca29004bfd514801ffe28a4011ffd052007ffc8290003fd414801ffe20a4010ffcc52007ffc6290003fd314801ffe18a4002ffc8520017de429000bfe2148005fe90a4000fb48520017f8429000aff6048025ffa824012dfd4120037fca09004bfa5048025fea824000df54120097f2a09000379504800dfe2824011ffd0120037fc8090003fd404800dfe2024010ffcc120037fc6090003fd304800dfe1824002ffc8120017f6409001bfe204800df71
  | 2 => 0x40117fea2a007ffe5150045fea8a801fff14540027fe82a0013bf4150009ff20a8004ff505400077a82a0013fc4150043ff98a801fff8c540007fa62a007ffc3150041ff90a801fff88540007fa42a007ffc21500097fb028022ffd4140116fea0a001bfe5050045fea828000df54140037f8a0a0013ff4050009fda028006ff901400377c80a001bfc405000dde2028004fe1014010ffe60a001bfc3050041ff9028006ff081400fffe20a001bfc105000dffb2c6006bfd9630037fccb18016fe658c00dbf32c60059f99630037facb1807afd658c00dbeb2c60009f59630037f8cb1801afc658c00dffb246006bfd9230037fcc918012fe648c00dfeb246000bf59230037f8c91801afc648c03dffaa4601dff952300f7faa918077fc548c0077eb1c6003ffd4e3001ffca71800ffd538c007fe29c6003ffd0e300efbe871800ffe438c007fea1c6003ff10e3001fb8871801bff628c00dff3146002bf98a30037fac518002fd628c00dfe3146006bf18a300f7fea518073fe528c03dfea94601cff14a300effe8518073fe428c001fea14601cff10a3001ffe651800ffe328c007fe9946003ff0ca30037fec31801bfe618c0037f30c6006ff58630005fac31801bfc618c00d7e30c601effd46300dffca31807bfd518c037fe28c601dffd06300dffc8318003fd418c037fe20c6003ffcc63001ffc631800ffd318c007fe18c601cffc86300dffc4318003fd218c037fe10c6006bf98230037fea11801b7f508c00dff2846006ff54230036faa11801bfc508c00dffa046006ff90230037f4811801bfd408c001fca046006ff10230037fe611801bdf308c007fd9846006ff0c230037f0611801bff208c00dfe1046006ffc4230037f8211806bff654c0357fb2a601aff9953002dfcca9806bfd654c0357eb2a601aff1953002df8ca98003ff644c0017fb226000efd91300057ec898067fe644c0097f3226000ff59130005fac898067fc644c0097e3226000ef1913002578c89806bff544c033ff2a2601aff551300cff8a89801aff634c007ffa9a6003ff94d3001ffaa69800ffc534c007ffa1a6003ff90d3001fbc869800ffd434c001eea1a6003ff10d30007fec498002ff624c031ff3126002bf98930007fac498063fc624c0057e312601affd49300c7fca49806bfd524c031fe2926019ffd09300c7fc8498003fd424c031fe2126003ffcc93001fbe649800ffe324c007fe9926000f74c93001ff86498003ff614c0017fb0a6017ff9853000dfcc298003fd614c02ffe30a6001bf185300d7fea29805ffe514c035fea8a6017ff145300cffe829805ffe414c001fea0a6017ff1053001ffe629800fdf314c007ff18a6003ff4c530007ba629800ffc314c031ff90a6017ff88530007fa429805ffc214c0077fb02601affd41300d6fea09801
  | 3 => 0xfa82422ddfd412116ffca0908b7fd504845bfe282422cffd0121167f880908afff3048457fe1824202ffc8121017de409080bfc2048403ff8824201fdc412100ff820908037f6454055bf322a000df59150156f8c8a80037f6354053bf31aa000df58d5014ef8c6a80ab7f4354053bf21aa000df50d5014ef886a80037f6254051bf312a000df58950146f8c4a80ab7f4254051bf212a000df50950146f884a80a77f3254051bf192a000df4c950146f864a80037f615404fbf30aa000df5855013ef8c2a80ab7f415404fbf20aa000df5055013ef882a80a77f315404fbf18aa000df4c55013ef862a80a37f215404fbf10aa000df4855013ef842a80177f605400b3fb02a005ded8150156fe80a801b7c4054053bf982a006df0c150146fe40a801b7c205404fbf882a006df04150037fecb2001aff659000dff32c8005bf99640036fccb200167e659000dfeb2c8026bf59640036facb200027d659000dfe32c8006bf19640025fac920013ff5490009ff2a48004ff55240027f8a92001bff639000dff31c8003bf98e40037fac720002fd639000dfe31c8006bf18e40137fea720097fe539004dfea9c8025ff14e40027fe8720013fe439004bdf21c8004ff50e40027f88720013bc439000dffb148006ff98a40015fcc52001bfd62900017eb148006ff18a40035f8c52009bff5290049ff2948026ff54a40127f8a520013ff4290009ff2148004ff50a40027f88520097ff3290049ff1948000ff4ca40127f8652001bff619000dff30c8001bf98640037fac320002fd619000dfe30c8006bf18640137fea32008ffe519004dfea8c8023ff14640027fe8320013fe4190009fea0c8004ff1064012ffe632008ffe3190001fe98c8023ff0c640127fe432008ffe2190001fe90c8023ff08640035fcc12001bff509000dbfa848006ff94240037faa12001b7d509000dfe2848006ffd02400377e8120013fb409000dfe2048006fe10240037fe612001bfc309000dff9048006ff08240037fe212001bfc1090045ffb2a8022bfd9540117fccaa0016fe6550045feb2a8022bf59540117f8caa0016fc655000d7fb228004ffd5140027fca8a0013fd5450009fe2a28000ffd8d40005fec6a0003df63500016fb1a8021ff98d4001dfcc6a0003fd6350043fe31a8003bf18d40007b8c6a000edc6350045ffa9a8021ff94d40117faa6a0087fc5350009ffa1a8004efd0d40027fc86a0013fd4350001dea1a8004ff10d40007fec4a0002ff6250041ff3128002bf98940007fac4a0083fc62500057e3128022ffd4940107fca4a008bfd5250041fe2928004ffd09400277e84a0013fe4250009fea128000ef50940027f884a0087ff3250041ff1928000ff4c940107f864a0003ff61500017fb0a801fff9854000dfcc2a0003fd615003ffe30a8001bf185
  | 4 => 0x8c7fc32504037fb0a8201ffd454100ffca2a0807fd5150403fe28a8201ffd0541027ee82a0807fe4150403df20a8201ff1054100f7882a0807f44150403ff98a8201ff8c54100fec62a0807fc3150403ff90a8201ff8854100ff842a0803ff60504017fb028200ff98141007fac0a0803fc605040d7e3028233ffd414119efea0a08cffe5050467fea828233ff14141027fe80a0813bf4050409fe2028232ffcc141197f860a08c7ff2050463fe1028201ffc414100fee20a0807fc1050461ffb2a6230bfd9531187fcca98816fe654c461feb2a6230bf59531187f8ca98816fc654c401ffb226200bfd913117ffcc898812fe644c401feb226200bf5913117ff8c898812fc644c461ffaa2622fff95131187faa8988bffc544c4037fb1a6203ffd4d3101ffca69880fde534c407fea9a6230f754d3101ff8a69880fff434c45fefa1a6203ff90d3101ffa869880ffc434c407ee21a6200ffd8931005fec4988bbfe624c4057f3126200ff58931177f8c49880afc624c461ffa92622eff94931187faa4988bbfc524c45fffa12622eff90931007fa84988bbfc424c407ff9926203f7cc93101ffc649880ffd324c401ee9926203ff0c93100dfec298807ff514c403ff28a6201ff5453100ff8a298807ff414c403ff20a6201fd9053100ffa8298803f5414c403fe20a6201ffcc53101fee6298807fe314c403ef18a6201ff0c53100fb86298807f4314c403ff90a6201ff8853100ff84298803ff604c4017fb026200ff98131007fac098803fc604c40d7e3026230ffd4131186fea0988c3fe504c461fea826230ff1413117ffe80988bffc404c407ff9826203f7cc13101ff860988bbff204c45dfe1026201ffc413100fee2098807fc104c45bffb2a422dbfd9521006feca908027f654845bff32a4205bf9952116ffaca908b6fd654845bfe32a4205bf1952116ef8ca908167c6548401ffb224200bfd9121167fcc890812fe6448401feb224200bf59121167f8c890812fc644845bffaa2422cff9512116ffaa8908b3fc5448401ffb1a4200bfd8d2115ffcc69080efe6348401feb1a4200bf58d2115ff8c69080efc634845bffa9a422bff94d2116ffaa6908affc5348459ffa1a422bff90d21007fa86908affc43484037fb124202ffd4921017fca49080bee5248405fea92422dfb54921017f8a49080bff4248405ff2124202ff50921017f8849080bff3248405ff1924202ff4c921017f86490806ff6148403ffa8a4201ff9452100feca290807fd514845bfaa8a4201ff1452100ffe8290807fe4148403fea0a4201ff1052100ffe6290807fe3148403fe98a4201ff0c52100ffe429080bf72148403ff10a4201fb8852100ff84290807ec2148403fa10a4201f908521007fec090802ff6048401ff3024200ff58121007f8c09081afc604845bf
  | 5 => 0x5142027f8a8a1003ff63508017fb1a8438ff98d4201dfcc6a1003fd6350871fe31a8403bf18d421cffea6a10e3fe5350873fea9a8438ff14d42027fe86a1013fe4350871df21a8404ff50d42027f886a1013bc43508057fb128402ffd4942017fca4a100bfd5250805fe2928402ffd0942027de84a100bfe4250805df2128402ff109420177884a100bec4250805ff9928402ff8c942017dc64a100bfc3250801ffb0a8400bfd85421bffcc2a1006fe6150801feb0a8437ff1854200df8c2a10e7ff515086fff28a8439ff545421bff8a2a1013ff4150809dfa0a8404ff90542027f882a10e3ff315086fff18a8437ff0c542017fe42a100bfe2150805fe10a8400ffd8142005fec0a1003fe6050801feb028400ff18142035f8c0a10e7ff5050873bfa828439ff941421cffaa0a10e7fc5050809ffa028404efd0142027f880a10e3ff3050871fe1828402ffc8142017de40a100bfc205086fff8828437ff041421b7feca990daff654c86dff32a6405bf995321b7faca990dafd654c86dfe32a6405bf19532007fec899002ff644c86bff3226404bf99132007fac899002fd644c86bfe3226404bf191321b7fea8990d7fe544c86dfeaa26435ff15132015fec69900fff534c807ff29a6403f794d3201ffaa6990dbdd534c807fe29a6403ffd0d321afbe869900ffe434c807fea1a6403ff10d3201fb8869900aff624c805ffa926402ff94932017faa49900bfc524c805ffa126402ff90932017dc849900bfd424c801f6a126402ff10932017fe649900fef324c805ff1926402f78c932017f8649900bdc324c805f61926400ffd8532005fec2990d3fe614c8037f30a6400ff585321a7f8c299006fc614c86dffa8a6434ff945321b7faa2990d3fc514c86bffa0a6434ff905321a7f8829900fff314c807ef98a6403ff8c53201ff8629900bff214c805ff10a6402ff08532007fec099002ff604c801ff3026400ff58132007f8c09901afc604c86dffa826436dfd41321b7fca0990dbfd504c86dfe2826435ffd01321aff8809900fff304c807ef9826403ff0c132017fe409900bef204c805fe1026434ffc41321a7f820990cfff65504677fb2a8233ff9954102dfccaa08cffd65504677eb2a8233ff1954102df8caa0806ff6450409ffaa28204ff951410277ca8a0813fd5450467deaa28204ff15141007fec6a0802ff6350465ff31a8203bf98d41007fac6a08cbfc63504077e31a8233ffd4d41197fca6a08cffd5350465fe29a8204ffd0d41027fc86a08cbbe4350409fea1a8204ff10d410277886a0803ff62504017fb128231ff98941015fcc4a0803fd6250463fe3128202bf1894119ffea4a08c7fe5250467fea928231ff14941027fe84a0813bf4250409ff2128204ff509410077a84a0813fc4250465ff9928231ff8c941007fa64a0
  | 6 => 0x5c0000a02e014020070000240380a01000802801002000010000020040f80201803400001008078000030020080500100a0a40e805056068030a30240140401800c1a00000100804c0180400005c00000004048010240020000100100203002003160004080150040200d03e00800400002000000010040080240700800c2240280000002c0d01201401c050240040000900e00c0001000103a0240681602c0000000500a064038020260040000301e10813800006004048000000240480100201000001004008040090000100680f00e0000486200001c0280500c2701180200600001812098014070000000300180700003402005002000090020020140080000a0b8030090000f014010000008060000260040a0000020180180500405c0300801e01400000006000178110000040900107e0040380200e0001580004403c00009000000128000000080080001a000008080040040a802000010070070120281c81302c02c0000c0020100780502601c008010180082280100204c0281d00a0200000203a00001801000000020050400040000401e0640380800806c120020380080300a01000400000014000018070140280180000e01c5f018024000008090000000080300a0040007a00400c00011004000148060080000400d00c004030010000100e83e01001c0080900a01819010002000000210000540002000600401007026014008070000000600500001c0181a00c00c0500101a0000080300000c00005004000018030000040380108c0080000000a0000288a01a09879ffb2a863cbfd95431e7fccaa1816fe6550c79feb2a863cbf595431e7f8caa1816fc6550c077fb228604ffd5143027fca8a1813fd5450c09fe2a28603bfd8d4301ffea6a180ffe5350c07fea9a8603ff14d4301ffe86a1813df4350c07ff21a8603ef90d4301ff886a180fbc4350c07ee21a8603e710d43007fec4a1802ff6250c77ff3128602bf98943007fac4a18effc6250c057e312863cffd49431dffca4a18f3fd5250c77fe2928604ffd0943027fc84a1813fc4250c07ff9928603ff8c94301ff864a1803ff6150c017fb0a863aff9854300dfcc2a1803fd6150c75fe30a8601bf185431e7fea2a18ebfe5150c79fea8a863aff14543027fe82a1813fe4150c09fe20a8603ffcc54301ffc62a180ffc3150c77ff90a863aff885431d7f842a1803ff6050c017fb028600ff98143007fac0a1803fc6050c0d7e302863cffd41431e6fea0a18f3fe5050c79fea82863cff14143027fe80a1813bf4050c09fe2028603ffcc14301fbe60a180ffc3050c77ff902863bff081431d7fe20a18ebfc1050c73ffb2a8439bfd95421cffccaa1016fe6550873feb2a8439bf595421cff8caa1016fc65508057fb228404ffd5142027fca8a1013be5450809feaa28439ef5
  | 7 => 0x4d100000014133a21b38116c09d1f53cb0001fd00000033800029d3d80003160004aa2f44c74611a01103e94d04a337728938e0001f10e958150e5183042644172dc09006806f4931d45093631ee43b0240bc2060fe1494b80a940d31245d2b828356212505f55f2650000742b55910d016936400042006c0000000004fc00010343c1e92c71833fa27506739d29c30a0f50000001232e822c1bc01c0525384de4163be00000000035f3d600c0580003f307a0e81f809a0c72bd4dc1304155751161342b64e149816a58700000047f1d137a0ee2f20001dd1c802c3180001450000b50dc0f72f32201903104260000d91ed2b94c00000002c534c00036c05100031300022b4411f74fa12a43702000011149600053d1a22c440023d1ba0a80d714d54404d50422a11842e2fc48f08a3ec38348c00014b00000004b00040613a54e0c20004ac37420f00052d1e73a93d900b27d1144231013063d22842603b758b11f07c3cf0460000044790652ca5462ff4043b14701730c607e00032a34625951a00000034513c01d0004bb00056838f5485073c02a346c41c28e3500002985901501e305b2082610dd4470002ec0004ab0000004690002822c95435730050763a33a554f1ae1632c015b02b3441b140700011b24a24b09e5820f300047a55e0001ac2343c34b642b00032825657403a3340d616810001b0ea2794760000003e243805a0000815473db1841fc45631e00000056b0ff5882ea36809414f05657c2fa0004fb0000003754b909b0bb1771914f11441b81bd0002f515554044850c11d32709953f3b332c25c0a20001214cf00008c0004e81423885612ab3bd00000019d0b656954d1744851ad0803b21355641b41465272174924781d24652be32e4361ab56d21a0860c32b14dd04058a00002e27a4a21fe1795200e73970002763085230734a011753000000000004900f55c07242110c37357d0000000000003c60003d501100000d52852c1800000001662fe3e83e65133bb4641e500009f00004331d0000eb0000ba1763f623e57a0f90a410b2ad4df4d62d100000022e37d1ff4270b210939f28020b55353145e48704520148121e15a0a14f444b4f23390634d219b4a93ab5700972481a649742f33c0181b94282eb4b14314a128517c2161c72d92262683333793ca0005351c536f1294f62330a72e51513301591c455a19f41a4741d94ff16430b0550f65662572493da55b29e13300001e4af36d21d5143e53214cb1023513ad26900056025d24216519c0000003f558008b57b4c252f5630003f24f057824436141d3c803900002c0001f00c0800000a0180180100100405000017028000050140000000082100c0642200005a0040107c00a0080400100205c0200800008049004040000000190541840000100402c0080d01a0
  | 8 => 0x4153c0ef37600027f1a72a100000000000018700a0d50001475864c90034c429049c4ae3fb3b44332271dc08e19239534346033d12b1a408803813d4c12cc0602ae4e44301e101529b29245423258327e1852c21314661282a60c802d18c2963f852e4862bc17d2872ce20a0331f01d642457f0783804013221cc3df36e1814a41aa5324da0ca4750214a511a10f0ac17f1de50805d4d843231c26c51701a05001424e42c3b50c10e32455253412735060b71384463ee49a3ed46f1eb4342a40e52392af0bf1be03c2740e12e30d41582a940f54c1db3713570b318f40a18a2ef58e3c75590b11e426d00646a39c0f423505e2a22ee33200711544f4bd57719522853339240348238907730006610757e10619925e47d0ec1ef50d4b318e0391ca1431f22360f20713901621cb56a4d40db4591863b603e2b73de54a2944ea4c32ed0893e73fd3a832049f21958517523a4572031ec2123f42a52222152781b53702d618904c2fd0003e403107009342d39915600000025f4090000003b016f00003b26e0be00000056f0002c32b30000000000003663694550001d71e03982861d336a52b0a05844a72ac00045c32b0005104ec52936b0c044d0003c20413425152584b23f039608738c23b3c949d11c2f701f26f44927b0003c546b31939b4ee1132052a71260000002912542f800000033717b2514583e00160002934f31e81c206458d2d30003e354252a3a400000000046754500014a2b402f2ba0ed03514c5050000300fc17024c0fb3bc19457600000014800052631f13f0003252a819810e1d04992233ff45f04a4bf43f3290a604e4ed0002fb00000000000053420e35e29f51652107b00025b22d37f2d524d1c00004e53a027c0ab00000026207d1880fa35c4f54d945a2db4db0794e625344a1cd38a0af15349b0000000d825a00032d01344c16e03d4253ba0000002404e702832f03600000000046851100028a0000e238b26346d00033e00000000051900000043a00034d2212df0cf00000012708446316d4e02e10175030253013a23af49e1e20002074940c53a60000000265220003aa45b43e0001a155000000000034700010400148b3e12f14d55010001224050005364433532b00000000484521f600000058c4f84223d70004623ce2880000002f63b92e739a2e906b51e4ce22429504237c0ae1375570aa31a3ac2464421fb0003932e03ea15426602351c4c554930d3153054f95580440df0ce12f0003264c83310321c10000bd00021821434b10530c1b21612d829a41439e38416000050a0001bb2d71af3dc2d02aa0000004835000001720000e653a26740e0620c45022cf0000001a90d10003074400e400003f00000016b06140b30208547251220451f5240090004950920541a315f00044e00013609100000053e00021f
  | 9 => 0x34817e56712c0001820cd08231b0003780004e23c42112104110692c813e41e48400000035a5890003400951d531706d1c602200013911919709620900040823f56c26a0000000002813140003650b400033b0b000017841848e28d1d814e13b4eb17128c00013235502a0001cf1f30190534ca5564f73242f92a01ea2525372b20b905923751b57923150f2de0003360291c30002722e633515200035d19a00000024115e0000370004ad0a307f0002c628b5722130004e90000004103520003d100000000009c19e26b2383110000f80cc00000008f2f000000000000000000002743538d1f910d3035650830f024747e4b54910020000082d222555444555d36045144430f3720000e03ae0003230004d74395520002e448045350b3543bf53b1b335800015c38600048d3d43f73870001b000038529722f04737e2993941672501960004020b82304a81242bb42937b00e0003eb12034e1930004cd3590000002550003dd51d43d0003d003442a04f2704901a52cd4bc2c133f00008d06e4d30003f10000d300024356e00011e3b84130001da00018d0000983d34b40de17a0003090000000003674882cb4891b70000004fe3fc27134941947b2dd1e612e4b020021c0001c900010a34a05c00048a00041b35b3cc0f11f423c2da4b72773cd3c147345046e20c5714be1080c953905728f2021ce0a50750004e31bf0002294a638200020d4cc3f91fa24f4ef30e1400da0fd01200039118b3a70cb4c61b62bf41206a0ad1120000104fd3fe36258f1df5550000003561a854b15d3a147712d4ba2e22d455141f00000047c0d23ef15740c47134f0005
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa30541100377830541102177b20541100377a205411003778205411013f7b10541100377610541100377410541100377810541100577b765411002e7b765411013f78765411002e7876541100077b74541102277a74541100077974541102277874541100077b64541102277a64541100077964541102277864541100077b735411021f7a735411000779735411021f7873541100077b635411021f7a635411000779635411021f7863541102277b435411021f7a435411000779435411021f7843541100077b72541102177a72541100077972541102177872541100077b62541100067b62541102177a62541100077962541100067962541102177862541102277b42541102177a425411000779425411021778425411021f7b32541102177a325411000779325411021778325411013f7b715411000773715411013f7a715411013f79715411013f78715411013f7071541100377b61541100367b615411003773615411013f7b415411013f7a415411013f72415411013f79415411000771415411013f78415411013f7b315411013f7a315411013f72315411013f79315411000771315411013f78315411013f7b215411013f7a215411013f72215411013f79215411000771215411013f782154110024ff765011000cfe76501100fcfd765011000cfc7650110006bf6450110026bc6450110005df7350110045dc7350110005f7715011000df47150110007b5415011000779505011001cff764c11000cfe764c1100bcfd764c11000cfc764c110005bf744c11004dbc744c110006df634c11001edc634c110005f7714c11000df4714c110007d5314c11000779504c11020dfa7688110036fa7688110035fb75881100377a7588110205f975881100377975881100057975881101fefb65881101fef9658811007df97288110016fa6288110016f86288110037f3718811000dfa7188110035f87188110037f07188110036fb6188110037f361881100a7f24188110007f141881100a7f23188110007f131881100a7f2218811003ff12188110014ff764811000cfe764811007cfd764811000cfc7648110006ef6248110016ec6248110005f7714811000df47148110007e521481101ef7b5048110007795048110037e82048110037f0104811000df87648110016f8764811000cf876481101f5fb75481101f5f975481101eefb65481101eef96548110035fb7248110037eb7248110007eb6248110016fa6248110016f8624811003fe8624811003fea4248110007e9424811003fea3248110007e93248110007f3714811000dfa714811000df8714811007ff07148110036fb6148110037f3614811007ff24148110007f1414811007ff23148110007f1314811007feb214811007ff2214811007fe9214811003ff12148110007e12148110
  | 1 => 0x89100a6ed21d8910034fe70d891000cfd70d8910034fc70d89100067f50d8910006fa50d8910006f950d891003eef20d89100057f75589100557c755891003eec6258910255fb7058910004ff75589100067f75589100047f755891002cfe7558910004fd755891002cfc75589100067c755891002c7c7558910004ff7458910024fe7458910024fc7458910004ff735891001cfe735891001cfc73589100a4ff7258910006ef725891007cff7158910006f77158910254ff7058910006fb70589100067f5058910006fa5058910006f95058910004ff7650910004fe7650910004fd7650910004fc7650910026be6450910006bd645091000df67150910004ff764c910004fe764c910004fd764c910004fc764c91001ede634c910006dd634c91000df6714c910035f47650510026f47650510034f4765051000df7745051000fb77450510007b76450510026f66450510026f4645051004fb4645051004fb65450510247b55450510005f77350510006f76350510006f5635051024fb6435051004fb44350510005f7725051004fb74250510007b54250510007f37050510035f67050510035f47050510007f0705051000ef7605051000ff36050510247775050510247f25050510247f1505051004fb74050510035f4764c51001ef4764c510034f4764c510005f7744c510005f5744c510006f7644c510006f5644c51000df7734c51000fd7734c510007d7634c51001ef6634c51001ef4634c510047d4634c510047d6534c510237d5534c51023fd7434c510047d4434c510005f7724c510047d7324c510007d5324c510007f3704c510035f6704c510035f4704c510007f0704c51000ef7604c51000ff3604c51023777504c510237f2504c510237f1504c510047d7304c510035f47648510016f47648510034f4764851000777754851022f74754851022ef7654851022ef56548510005f77448510005f57448510005f77348510005f5734851000df7724851000fe77248510007e76248510016f66248510016f4624851003fe46248510016e4624851003fe6524851022fe55248510007f37048510035f67048510035f47048510007f0704851000ef7604851000ff3604851022f77504851022ff2504851022ff1504851003fe7204851002e7f765411013e7e765411013e7d765411002e7c76541100067f64541101567e64541100067d64541101567c64541100067f635411014e7e63541100067d635411014e7c63541100067f62541101467e62541100067d62541101467c625411000777715411013f7471541100367f615411013f76415411000775415411013f76315411000775315411013f7621541100077521541100357f70541100577b70541100367f60541102277b40541100377a405411003778405411021f7b30541100377
  | 2 => 0x28778325421013f7b715421013f7a715421013f79715421013f78715421013e79615421013f7b415421013f7a415421013f79415421013f78415421013f7b315421013f7a315421013f79315421013f78315421013f7b215421013f7a215421013f79215421013f782154210035fb764821027efb7648210275fb7548210275f97548210036fb65482100377a654821026ef96548210037796548210006796548210037eb7248210037eb6248210016fa6248210036f86248210037e86248210067ea4248210007e94248210067ea3248210007e9324821000dfa714821000df8714821007feb214821007fe92148210024fe76d911004ebe64d9110004ff75d911002cfe75d9110004fd75d911002cfc75d911001cfe73d9110004fd73d911001cfc73d9110006be43d911004ebc43d9110014fe72d9110004fd72d9110014fc72d9110034ff71d911000cfe71d9110034fd71d911000cfc71d911011ebf41d911011ebd41d911011ef631d9110034fe70d911000cfd70d9110034fc70d91100067f50d911004ebf40d911004ebc6459110005df7359110045dc7359110265fb7059110004ff755911002cfe7559110004fd755911002cfc755911011cff7459110006bf7459110004ff7359110006df7359110004df735911001cfe735911001cfc7359110006dc735911001cdc7359110004ff7259110014fe7259110014fc725911004ebf42591100fcff7159110006f771591100fef63159110264ff7059110006fb70591100067f505911001cfe76d8d10046de63d8d10004ff75d8d1002cfe75d8d10004fd75d8d1002cfc75d8d10024fe74d8d10004fd74d8d10024fc74d8d10006df43d8d10046dc43d8d10014fe72d8d10004fd72d8d10014fc72d8d10034ff71d8d1000cfe71d8d10034fd71d8d1000cfc71d8d100def641d8d100dedf31d8d100dedd31d8d10034fe70d8d1000cfd70d8d10034fc70d8d100067f50d8d10046df30d8d10005bf7458d1004dbc7458d10046dc6358d1025dfb7058d10004ff7558d1002cfe7558d10004fd7558d1002cfc7558d10004ff7458d10006bf7458d10004bf7458d10024fe7458d10024fc7458d10006bc7458d10024bc7458d100dcff7358d10006df7358d10004ff7258d10014fe7258d10014fc7258d10046df3258d100bcff7158d10006f77158d100bef64158d1025cff7058d10006fb7058d100067f5058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100479c4350d1000df67150d10014fe76d891003eee62d8910004ff75d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d891001cfe73d8910004fd73d891001cfc73d8910006ef52d891003eec52d8910034ff71d891000cfe71d8910034fd71d891000cfc71d89100a6ef21d
  | 3 => 0xd40596100367c40596100367f30596100367e30596100367d30596100367c30596100367f20596100367e20596100367a20596100367d20596100367c20596100367f10596100367e10596100367d10596100367c1059610004ff755921002cfe7559210004fd755921002cfc7559210036bf7459210004ff7359210006df7359210004df735921001cfe735921001cfc7359210006dc735921001cdc7359210076bf4359210004ff7259210014fe7259210014fc7259210076bf42592100febf41592100febd4159210034ff7059210034fe7059210034fd7059210034fc70592100367f50592100367d5059210036be4059210036bc4059210036f71059210036f51059210004ff7558e1002cfe7558e10004fd7558e1002cfc7558e10004ff7458e10006bf7458e10004bf7458e10024fe7458e10024fc7458e10006bc7458e10024bc7458e10036df7358e1006ede4358e10004ff7258e10014fe7258e10014fc7258e1006edf3258e100bedf3158e100bedd3158e10034ff7058e10034fe7058e10034fd7058e10034fc7058e100367f5058e100367d5058e10036de3058e10036dc3058e10036f71058e10036f51058e10004ff7650e10034fe7650e10004fd7650e10034fc7650e101e67e6550e100067d6550e10026be6450e10006bd6450e1001ede6350e10006dd6350e1006f9c4350e10004ff7558a1002cfe7558a10004fd7558a1002cfc7558a10004ff7458a10024fe7458a10024fc7458a10004ff7358a1001cfe7358a1001cfc7358a10036ef7258a10066ee4258a10066ee3258a1007eef2158a1007eed2158a10034ff7058a10034fe7058a10034fd7058a10034fc7058a100367f5058a10036fa5058a100367d5058a10006f95058a10036ee2058a10036ec2058a10036f71058a10036f51058a10004ff7650a10034fe7650a10004fd7650a10034fc7650a101ce7e6550a100067d6550a10026be6450a10006bd6450a10016ee6250a10006ed6250a10004ff764ca10034fe764ca10004fd764ca10034fc764ca101b67e654ca100067d654ca1001ede634ca10006dd634ca10016ee624ca10006ed624ca100377b76542100357b765421029e7b76542100077b74542102977a74542100077974542102977874542100377b64542100377a64542100377964542100377864542100077b735421028f7a735421000779735421028f7873542100377b63542100377a63542100377963542100377863542102977b435421028f7a435421000779435421028f7843542100077b72542102877a72542100077972542102877872542100377b62542100367b62542100377a62542100377962542100067962542100377862542102977b42542102877a425421000779425421028778425421028f7b32542102877a3254210007793254210
  | 4 => 0x41201567c64541200067f635412014e7e63541200067d635412014e7c63541200076f72541201476c72541200367f62541201476e42541200076d42541201476e32541200076d32541200067f615412013e7e615412013e7c61541201476f21541200076d21541200357f70541200977b70541200367f60541202b77b40541200377a40541200377840541202af7b30541200377a30541200377830541201477b20541200376e20541200376c20541200377820541202a77b10541200377a10541200377810541200977b765412002e7b765412014778765412002e7876541200077b74541202b77a74541200077974541202b77874541200077b64541202b77a64541200077964541202b77864541200077b73541202af7a73541200077973541202af7873541200077b63541202af7a63541200077963541202af7863541202b77b43541202af7a43541200077943541202af7843541201477b72541200076b72541201477a72541201477972541201477872541201476872541200377b62541200367b62541200376b62541201477b42541201477a42541201476a42541201477942541200076942541201477842541201477b32541201477a32541201476a32541201477932541200076932541201477832541200077b71541202a77a71541200077971541202a77871541200077b61541200067b61541202a77a61541200077961541202a77861541202b77b41541202a77a41541200077941541202a77841541202af7b31541202a77a31541200077931541202a77831541201477b21541201476b21541201477a2154120147792154120007692154120147782154120024ff7650120014fe7650120104fd7650120014fc7650120006bf6450120026bc6450120005df7350120085dc7350120005ef7250120015ec7250120007ad425012000779505012001cff764c120014fe764c1200c4fd764c120014fc764c120005bf744c12008dbc744c120006df634c12001edc634c120005ef724c120015ec724c120007cd324c12000779504c1200067f74596100067e74596100067d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f42596100067e42596100067c42596100067f32596100067e32596100067c325961013e7f715961013e7e715961013e7d715961013e7c715961013e7f415961013e7e415961013e7d415961013e7c415961013e7f315961013e7e315961013e7d315961013e7c315961013e7f215961013e7e215961013e7d215961013e7c21596100367f70596100347f70596100367e70596100367d70596100347d70596100367c70596100367f40596100367e40596100367
  | 5 => 0x86df30d8d20005bf7458d2008dbc7458d20086dc6358d202edfb7058d20004ff7558d2002cfe7558d20004fd7558d2002cfc7558d20004ff7458d20006bf7458d20004bf7458d20024fe7458d20024fc7458d20006bc7458d20024bc7458d200e4ff7358d20006df7358d200c4ff7258d20006ef7258d200c6ee4258d20004ff7158d2000cfe7158d2000cfc7158d20086df3158d202ecff7058d20006fb7058d200067f5058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200879c4350d20015ee7250d20035ec7650920026ec7650920034ec7650920015ef7450920017af7450920007af6450920026ee6450920026ec645092008fac645092008fae54509202dfad5450920005ef7350920006ef6350920006ed63509202e7ae435092008fac4350920005ef715092008faf4150920007eb7050920035ee7050920035ec7050920007e87050920016ef6050920017eb60509202df6f50509202dfea50509202dfe9505092008faf4050920035ec764c92001eec764c920034ec764c920005ef744c920005ed744c920006ef644c920006ed644c920015ef734c920017cf734c920007cf634c92001eee634c92001eec634c920087cc634c920087ce534c9202cfcd534c9202d7cf434c920087cc434c920005ef714c920087cf314c920007eb704c920035ee704c920035ec704c920007e8704c920016ef604c920017eb604c9202cf6f504c9202cfea504c9202cfe9504c920087cf304c92000cfe76d852007ef661d8520004ff75d852002cfe75d8520004fd75d852002cfc75d8520024fe74d8520004fd74d8520024fc74d852001cfe73d8520004fd73d852001cfc73d8520034fd72d852000cfc72d8520006f751d852007ef451d852007ef621d8520066f521d8520034fe70d8520014fd70d8520034fc70d85200067f50d8520006fa50d8520006f950d852007ef710d85200057f75585200957c755852007ef461585202c5fb7058520004ff7650520004fe7650520004fc7650520026be6450520006bd6450520015ee7250520007ad4250520004ff764c520004fe764c520004fc764c52001ede634c520006dd634c520015ee724c520007cd324c520035ec764852000eec7648520034ec76485200076f75485202bf6c75485202beef65485202beed6548520005ef7448520005ed7448520005ef7348520005ed7348520015ef7148520017e77148520007e7614852000eee614852000eec614852007fe4614852000ee4614852007fe651485202bfe55148520007eb7048520035ee7048520035ec7048520007e87048520016ef6048520017eb60485202bf6f50485202bfea50485202bfe9504852007fe7104852002e7f76541201467e76541201467d765412002e7c76541200067f64541201567e64541200067d645
  | 6 => 0xe7458620024fc7458620004ff735862001cfe735862001cfc7358620036f771586200a6f641586200a6f631586200a6f6215862003ef52158620034ff7058620034fe7058620034fd7058620034fc70586200367f5058620036fa50586200367d5058620006f95058620036ef2058620036ed2058620036f61058620036f41058620004ff7650620004fd7650620034fc765062019e7e65506200067d6550620026be6450620006bd645062000ef66150620006f56150620004ff764c620004fd764c620034fc764c6201867e654c6200067d654c62001ede634c620006dd634c62000ef6614c620006f5614c6200377b76542200357b76542203167b76542200077b745422030f7a745422000779745422030f7874542200377b64542200377a64542200377964542200377864542200077b73542203077a73542200077973542203077873542200377b63542200377a635422003779635422003778635422030f7b43542203077a43542200077943542203077843542201477b72542201477a72542201477972542201477872542201467962542201477b42542201477a42542201477942542201477842542201477b32542201477a32542201477932542201477832542200077b71542202ff7a71542200077971542202ff7871542200377b61542200377a615422003779615422000679615422003778615422030f7b41542202ff7a41542200077941542202ff7841542203077b31542202ff7a31542200077931542202ff7831542201477b21542201477a2154220147792154220147782154220024fe76d912008ebe64d9120004ff75d912002cfe75d9120004fd75d912002cfc75d912001cfe73d9120004fd73d912001cfc73d9120006be43d912008ebc43d9120034ff72d9120014fe72d9120034fd72d9120014fc72d9120126bf42d9120126bd42d9120126ee32d912000cfe71d9120004fd71d912000cfc71d9120014fd70d91200067f50d912008ebf40d912008ebc6459120005df7359120085dc73591202f5fb7059120004ff755912002cfe7559120004fd755912002cfc7559120124ff7459120006bf7459120004ff7359120006df7359120004df735912001cfe735912001cfc7359120006dc735912001cdc7359120104ff7259120006ef7259120106ee3259120004ff715912000cfe715912000cfc715912008ebf41591202f4ff7059120006fb70591200067f505912001cfe76d8d20086de63d8d20004ff75d8d2002cfe75d8d20004fd75d8d2002cfc75d8d20024fe74d8d20004fd74d8d20024fc74d8d20006df43d8d20086dc43d8d20034ff72d8d20014fe72d8d20034fd72d8d20014fc72d8d200e6ee42d8d200e6df32d8d200e6dd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20014fd70d8d200067f50d8d20
  | 7 => 0x130007d93190130024ff765013001cfe765013010cfd765013001cfc7650130006bf6450130026bc6450130005df735013001ddc73501300079d435013031f7b5050130007795050130037b84050130037d8305013001df87650130026f8765013001cf87650130035fb7450130037bb7450130007bb6450130026fa6450130026f864501300cfb86450130007db735013001dfa735013001df8735013010fd87350130036fb6350130037db635013010fbb435013010fda435013010fb943501300cfd943501300079943501300cfbb4250130007b9425013010fdb3250130007d932501300cfbb4150130007b9415013010fdb3150130007d931501300067f74596200067e74596200067d74596200067c74596200067f73596200067e73596200067d73596200067c73596200067f43596200067e43596200067c43596201467f72596201467e72596201467d72596201467c72596201467f42596201467e42596201467d42596201467c42596201467f32596201467e32596201467d32596201467c32596200067f71596200067e71596200067d71596200067c71596200067f41596200067e41596200067c41596200067f31596200067e31596200067c31596201467f21596201467e21596201467d21596201467c21596200367f70596200367e70596200367d70596200367c70596200367f40596200367e40596200367d40596200367c40596200367f30596200367e30596200367d30596200367c30596200367f20596200367e20596200367d20596200367c20596200367f10596200367e10596200367a10596200367d10596200367c1059620004ff755922002cfe7559220004fd755922002cfc7559220036bf7459220004ff7359220006df7359220004df735922001cfe735922001cfc7359220006dc735922001cdc73592200b6bf4359220106bf4259220106bd4259220004ff715922000cfe715922000cfc71592200b6bf4159220034fe7059220034fc70592200367f50592200367d5059220036be4059220036bc4059220036ef2059220036ed2059220004ff7558e2002cfe7558e20004fd7558e2002cfc7558e20004ff7458e20006bf7458e20004bf7458e20024fe7458e20024fc7458e20006bc7458e20024bc7458e20036df7358e200aede4358e200c6df3258e200c6dd3258e20004ff7158e2000cfe7158e2000cfc7158e200aedf3158e20034fe7058e20034fc7058e200367f5058e200367d5058e20036de3058e20036dc3058e20036ef2058e20036ed2058e20004ff7650e20034fe7650e20004fd7650e20034fc7650e201e67e6550e200067d6550e20026be6450e20006bd6450e2001ede6350e20006dd6350e200af9c4350e20004ff755862002cfe7558620004fd755862002cfc7558620004ff7458620024f
  | 8 => 0x1dde73509301c79e4350930016ee6250930035dc764c930016dc764c930034dc764c93033edf654c93033edd654c930005df744c930005dd744c9300079f644c9301aede644c9301aedc644c9300079c644c9301ae9c644c93001ddf724c93001fcf724c930007cf624c930016de624c930016dc624c9300c7cc624c9300c7ce424c930007cd424c930005df714c930007db704c930035de704c930035dc704c930007d8704c93001edf604c93001fdb604c93033f5f504c9300c7cf204c93000cfe76d8530006bf64d8530006bc64d85300bef661d8530004ff75d853002cfe75d8530004fd75d853002cfc75d8530024fe74d8530004fd74d8530024fc74d8530034fd73d853000cfc73d8530014fe72d8530004fd72d8530014fc72d853006edf32d8530006dd32d85300bef631d853006ef531d853001cfd70d85300067f50d85300bef710d8530005bf74585300cdbc7458530006bf6458530006bc64585300bef46158530335fb7058530004ff7650530004fe7650530004fc7650530006bf6450530026bc645053001dde73505301979e435053000ef66150530035dc764c53000edc764c530034dc764c53032edf654c53032edd654c530005df744c530005dd744c5300079f644c53017ede644c53017edc644c5300079c644c53017e9c644c530005df724c530006df624c53001ddf714c53001fd7714c530007d7614c53000ede614c53000edc614c5300bfd4614c5300bfd6414c530007d5414c530007db704c530035de704c530035dc704c530007d8704c53001edf604c53001fdb604c53032f5f504c5300bfd7104c530004ff7648530004fe7648530004fc76485300057f75485300d57c7548530006bf6448530166bc644853001dde7348530005dd73485300bfe4214853002e7f765413014e7e765413014e7d765413002e7c76541300067f64541300073f64541300063f64541301567e64541300067d64541301567c64541300073c64541301563c64541300075f735413014f5c73541300367f635413014f5e43541300075d43541300067f62541301467e62541301467c625413014f5f32541300075d32541300067f615413013e7e615413013e7c615413014f5f31541300075d31541300357f70541300d77b70541300367f60541300377a405413014f7b30541300375e30541300375c30541300377830541300375830541300377a20541300377a1054130325fa7690130036fa76901300377a759013003779759013010df9749013012fbb6490130026fa6490130026f864901300cfb86490130026b86490130037db739013001dfa7390130035f87390130037d87390130036fb6390130037db639013012fba439013012fda439013012f9a43901300cfd9439013012fb8439013012fdb3290130007d9329013012fdb319
  | 9 => 0xc62d913012f9f32d9130006be61d9130006bc61d913012f9f31d913012fbb70d91300073f50d913012fbb30d91303679e30d91303679c30d913012fb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130366bf73d913012ebe73d913012ebd73d913012ebc73d913012ebf53d913012ebe53d913012ebd53d913012ebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d913012ebf32d913012ebe32d913012ebd32d913012ebc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d913012ebf31d913012ebe31d913012ebd31d913012ebc31d9130006bf21d9130006be21d9130006bc21d913012ebf70d9130366be70d913012ebd70d9130366bc70d9130006bf50d91300063f50d9130366be50d9130006bd50d9130366bc50d913012ebf30d9130366be30d9130366bc30d9130006bf20d9130366be20d9130366bc20d9130006bf10d9130366be10d9130366bc10d91300cebc645913035dfb7059130004ff755913002cfe7559130004fd755913002cfc755913012cff7459130006bf745913010cff7359130006df73591300ecdf7359130004ff7259130014fe7259130014fc7259130004ff715913000cfe715913000cfc715913035cff7059130006fb70591300067f505913012dbe76191300cebe761913012cbe76191300cf3e75191300cf3d7519130006bf6519130006be6519130006bd6519130006bc65191303279e73191300cf9d7319130356bf63191303569f63191300cfae72191300cfad7219130006be6219130006bc62191303279f32191300cfb671191300cfb57119130006be6119130006bc61191303279f3119130327b97019130326bf60191300073f5019130327bb30191303579e30191303579c3019130327b83019130035dc7650d30026dc7650d30034dc7650d3001ddf7450d3001f9f7450d300079f6450d30026de6450d30026dc6450d300cf9c6450d300269c6450d30005df7250d30005df7150d30007db7050d30035de7050d30035dc7050d30007d87050d3001edf6050d3001fdb6050d3034f5f5050d300cf9f4050d30014fe76d8930006bf64d8930006bc64d89300c6ee62d8930004ff75d893002cfe75d8930004fd75d893002cfc75d8930024fe74d8930004fd74d8930024fc74d8930034fd73d8930014fc73d89300c6ee32d89300aeed32d893000cfe71d8930004fd71d893000cfc71d89300aedf31d893001cfd70d89300067f50d89300c6ef20d8930005bf74589300cdbc7458930006bf6458930006bc64589300c6ec6258930345fb7058930004ff7650930004fe7650930004fc7650930006bf6450930026bc6450930
  | 10 => 0x92300eedf735923010ebf43592300eedf435923010ebd435923010edc4359230004ff7259230014fe7259230014fc72592300eebf4259230004ff715923000cfe715923000cfc71592300eebf4159230034fe7059230034fc70592300367f50592300367d5059230036be4059230036bc4059230036df3059230036dd3059230004ff7558a3002cfe7558a30004fd7558a3002cfc7558a30004ff7458a30024fe7458a30024fc7458a30006df4358a30086dc4358a30036ef7258a300e6ee4258a300e6ee3258a30086ed3258a30004ff7158a3000cfe7158a3000cfc7158a300e6ef2158a30034fe7058a30034fc7058a300367f5058a300367d5058a30036df3058a30036dd3058a30036ee2058a30036ec2058a30004ff7650a30004fd7650a30034fc7650a301ce7e6550a300067d6550a30026be6450a30006bd6450a30005df7350a3001ddc7350a301c79c4350a30016ee6250a30006ed6250a30004ff755863002cfe7558630004fd755863002cfc7558630004ff7458630024fe7458630024fc7458630006df4358630046dc4358630004ff7258630014fe7258630014fc7258630036f771586300def641586300def63158630046f531586300def62158630034fe7058630034fc70586300367f50586300367d5058630036df3058630036dd3058630036f61058630036f41058630004ff7650630004fd7650630034fc765063019e7e65506300067d6550630026be6450630006bd6450630005df735063001ddc73506301979c435063000ef66150630006f56150630004ff7648630004fd7648630034fc76486300057f75486300f57c754863016e7e65486300067d6548630016ee6248630006ed624863000ef66148630006f561486300dfe42148630035fb765023036efb76502300377a6550230037796550230037bb7450230037bb6450230026fa6450230036f86450230037b864502300efdb735023001dfa735023001df8735023010fd8735023001dd8735023010fbb43502300efdb43502300ef9b435023010fb9435023010fd843502300efbb4250230007b942502300efbb4150230007b94150230024fe76d91300cebe64d9130004ff75d913002cfe75d9130004fd75d913002cfc75d9130006bf54d91300cebe54d9130006bd54d91300cebc54d9130034ff73d913001cfe73d9130034fd73d913001cfc73d913012ebf43d913012ebd43d9130014fe72d9130004fd72d9130014fc72d91300cebf42d9130006be42d91300cebc42d913000cfe71d9130004fd71d913000cfc71d91300cebf41d9130006be41d91300cebc41d913001cfd70d91300067f50d91300cebf40d9130325be76d9130024be76d9130006bf65d9130006be65d9130006bd65d9130006bc65d91303679f73d913012f9c73d9130006be62d9130006b
  | 11 => 0x2cfe75d8540004fd75d854002cfc75d8540034fd74d854000cfc74d854001cfe73d8540004fd73d854001cfc73d8540014fe72d8540004fd72d8540014fc72d8540076bf42d8540006bd42d85400fef641d8540076f541d8540024fd70d85400067f50d85400fef710d8540005df735854010ddc7358540006df6358540006dc63585400fef4615854037dfb7058540035bc765054000ebc7650540034bc7650540376bf6550540376bd6550540005bf73505400079f6350540196be6350540196bc63505400079c63505401969c6350540005bf7250540006bf6250540025bf7150540027b77150540007b7615054000ebe615054000ebc61505400ffb461505400ffb63150540007bb7050540035be7050540035bc7050540007b87050540026bf6050540027bb60505403773f50505400ffb71050540004ff764c540004fe764c540004fc764c540025be744c540005bd744c540006df634c54001edc634c54017f9f434c54000ef6614c540007b5414c540004ff7648540004fe7648540004fc76485400057f75485401157c7548540025be7448540005bd7448540006df634854015edc63485400ffe4214854002e7f76541401567e76541401567d765414002e7c76541400073f74541401573c74541400367f64541400067f63541400075f63541400065f635414014e7e635414014e7c63541400075c635414014e5c63541401573f43541400073d43541400067f62541401467e62541401467c62541401573f42541400073d42541400067f615414013e7e615414013e7c61541401573f41541400073d41541400357f70541401177b70541400367f60541401577b40541400373e40541400373c40541400377840541400373840541400377a30541400377a20541400377a10541400067f74596300067e74596300067d74596300067c745963014e7f735963014e7e735963014e7d735963014e7c735963014e7f435963014e7e435963014e7d435963014e7c43596300067f72596300067e72596300067d72596300067c72596300067f42596300067e42596300067c425963014e7f325963014e7e325963014e7d325963014e7c32596300067f71596300067e71596300067d71596300067c71596300067f41596300067e41596300067c415963014e7f315963014e7e315963014e7d315963014e7c31596300067f21596300067e21596300067c21596300367f70596300367e70596300367d70596300367c70596300367f40596300367e40596300367d40596300367c40596300367f30596300367e30596300367d30596300367c30596300367f20596300367e20596300367d20596300367c20596300367f10596300367e10596300367d10596300367c1059630004ff755923002cfe7559230004fd755923002cfc7559230036bf745
  | 12 => 0xc74d8d400eedf54d8d400eede54d8d400eedd54d8d400eedc54d8d40006df72d8d40006de72d8d40006dd72d8d40006dc72d8d40006df52d8d40006de52d8d40006dd52d8d40006dc52d8d400eedf42d8d400eede42d8d400eedd42d8d400eedc42d8d40006df71d8d40006de71d8d40006dd71d8d40006dc71d8d40006df51d8d40006de51d8d40006dd51d8d40006dc51d8d400eedf41d8d400eede41d8d400eedd41d8d400eedc41d8d40006df21d8d40006de21d8d40006dc21d8d400eedf70d8d403a6de70d8d400eedd70d8d403a6dc70d8d40006df50d8d400065f50d8d403a6de50d8d40006dd50d8d403a6dc50d8d400eedf40d8d403a6de40d8d403a6dc40d8d40006df20d8d403a6de20d8d403a6dc20d8d40006df10d8d403a6de10d8d403a6dc10d8d4010edc6358d4039dfb7058d400edde7618d4010ede7618d4010f5e7518d4010f5d7518d40006df6518d40006de6518d40006dd6518d40006dc6518d4010f9e7418d4010f9d7418d40356df6418d403569f6418d4010fce7218d4010fcd7218d40006de6218d40006dc6218d4036f9f4218d4010fd67118d4010fd57118d40006de6118d40006dc6118d4036f9f4118d4010fd97018d4035edf6018d400075f5018d4036fdb4018d403579e4018d403579c4018d4036fd84018d40035bc7650d4001ebc7650d40034bc7650d40025bf7350d400279f7350d400079f6350d4001ebe6350d4001ebc6350d4010f9c6350d4001e9c6350d40005bf7250d40005bf7150d40007bb7050d40035be7050d40035bc7050d40007b87050d40026bf6050d40027bb6050d403973f5050d4010f9f3050d40014fe76d8940006df63d8940006dc63d8940106ee62d8940004ff75d894002cfe75d8940004fd75d894002cfc75d8940034fd74d8940014fc74d894001cfe73d8940004fd73d894001cfc73d8940106ee42d89400b6ed42d894000cfe71d8940004fd71d894000cfc71d89400b6bf41d8940024fd70d89400067f50d8940106ef20d8940005df735894010ddc7358940006df6358940006dc6358940106ec625894038dfb7058940035bc7650940016bc7650940034bc7650940386bf6550940386bd6550940005bf73509400079f63509401c6be63509401c6bc63509400079c63509401c69c6350940025bf7250940027af7250940007af6250940016be6250940016bc6250940107ac6250940107ae3250940005bf7150940007bb7050940035be7050940035bc7050940007b87050940026bf6050940027bb60509403873f5050940107af2050940004ff764c940004fe764c940004fc764c940025be744c940005bd744c940006df634c94001edc634c9401af9f434c940016ee624c940007ad424c94000cfe76d8540006df63d8540006dc63d85400fef661d8540004ff75d8540
  | 13 => 0x96400367f10596400367e10596400367d10596400367c1059640004ff7558e4002cfe7558e40004fd7558e4002cfc7558e40036df7358e4012ebe4358e4012ede4358e400cedd4358e4012ebc4358e40004ff7258e40014fe7258e40014fc7258e4012edf3258e40004ff7158e4000cfe7158e4000cfc7158e4012edf3158e40034fe7058e40034fc7058e400367f5058e400367d5058e40036bf4058e40036bd4058e40036de3058e40036dc3058e40004ff7558a4002cfe7558a40004fd7558a4002cfc7558a40004ff7358a4001cfe7358a4001cfc7358a40006be4358a4008ebc4358a40036ef7258a40126ee4258a4008eed4258a40126ee3258a40004ff7158a4000cfe7158a4000cfc7158a40126ef2158a40034fe7058a40034fc7058a400367f5058a400367d5058a40036bf4058a40036bd4058a40036ee2058a40036ec2058a40004ff764ca40004fd764ca40034fc764ca401b67e654ca400067d654ca40005bf744ca40025bc744ca4001ede634ca40006dd634ca4012f9c434ca40016ee624ca40006ed624ca40004ff755864002cfe7558640004fd755864002cfc7558640004ff735864001cfe735864001cfc7358640006be435864004ebc4358640004ff7258640014fe7258640014fc7258640036f7715864011ef6415864004ef5415864011ef6315864011ef62158640034fe7058640034fc70586400367f50586400367d5058640036bf4058640036bd4058640036f61058640036f41058640004ff764c640004fd764c640034fc764c6401867e654c6400067d654c640005bf744c640025bc744c64001ede634c640006dd634c64012f9c434c64000ef6614c640006f5614c640004ff7648640004fd7648640034fc76486400057f75486401357c754864016e7e65486400067d6548640016ee6248640006ed624864000ef66148640006f5614864011fe4214864001cfe76d8d4010ede63d8d40004ff75d8d4002cfe75d8d40004fd75d8d4002cfc75d8d40034fd74d8d4001cfc74d8d40006df53d8d4010ede53d8d40006dd53d8d4010edc53d8d4010ede43d8d400eedd43d8d40014fe72d8d40004fd72d8d40014fc72d8d4010edf32d8d40006de32d8d4010edc32d8d4000cfe71d8d40004fd71d8d4000cfc71d8d4010edf31d8d40006de31d8d4010edc31d8d40024fd70d8d400067f50d8d4010edf30d8d4010dde76d8d4001cde76d8d40006df65d8d40006de65d8d40006dd65d8d40006dc65d8d403a79f74d8d400ef9c74d8d40006de62d8d40006dc62d8d400ef9f42d8d40006de61d8d40006dc61d8d400ef9f41d8d400efdb70d8d400075f50d8d400efdb40d8d403a79e40d8d403a79c40d8d400efd840d8d40006df75d8d40006de75d8d40006dd75d8d40006dc75d8d403a6df74d8d4010ede74d8d400eed
  | 14 => 0x76f72585500056f72585501457e72585501457c72585500076c72585501456c72585500067f62585500067d625855013d7f715855000777615855013e7e615855013e7c615855013f74615855013e74615855013f7621585503c57f70585500077b70585503c57b70585500567f60585500577b60585500057f76505500057e76505500057d76505500057c765055013d7f74505501573e64505500073d64505500057f735055014d7e735055014d7c73505503bf3e43505501573c43505500057f72505501457e72505501457c72505501573f42505500073d425055013d7f715055015777415055013f3e415055013f3c415055013f74415055013f7631505500057f70505500357e70505500357c70505503ae7f605055019f7b60505501573f405055013f7710505500057f764c5500057e764c5500057d764c5500057c764c5500057f744c5501557e744c5500057d744c5501557c744c55013d7f734c55014f5e634c5500075d634c5503b75f434c55014f5c434c5500057f724c5501457e724c5501457c724c55014f5f324c5500075d324c55013d7f714c55013f76414c55000775414c55014f77314c55013f5e314c55013f5c314c55013f74314c5500057f704c5500357e704c5500357c704c5503ae7f604c5501877b604c55014f5f304c55013f77104c5500057f76485500067f76485500047f76485500057e76485500057d76485500057c76485500067c76485500047c76485500057f74485501557e74485500057d74485501557c74485500057f734855014d7e73485500057d734855014d7c734855013d7f72485501476e62485500076d624855013d7f714855013f76614855000775614855014777214855013f6e214855013f6c214855013f74214855013f6421485500057f70485500357e70485500077a70485500077970485500357c70485503ae7f604855016f7b60485501476f204855013f7710485501567f74596401567e74596401567d74596401567c74596400067f73596400067e73596400067d73596400067c73596401567f43596401567e43596401567d43596401567c43596400067f72596400067e72596400067d72596400067c72596401567f42596401567e42596401567d42596401567c42596400067f32596400067e32596400067c32596400067f71596400067e71596400067d71596400067c71596401567f41596401567e41596401567d41596401567c41596400067f31596400067e31596400067c31596400067f21596400067e21596400067c21596400367f70596400367e70596400367d70596400367c70596400367f40596400367e40596400367d40596400367c40596400367f30596400367e30596400367d30596400367c30596400367f20596400367e20596400367d20596400367c205
  | 15 => 0xc7158d5014f5f3158d503f57f7058d500077b7058d503f57b7058d500d67f6058d500d77b6058d500057f7650d500057e7650d500057d7650d500057c7650d5014d7f7450d5014d7f7350d501575f4350d5014f3e4350d5014f3c4350d5014f5c4350d5014f1c4350d500057f7250d501457e7250d501457c7250d500057f7150d5013d7e7150d5013d7c7150d500057f7050d500077b7050d500057b7050d500357e7050d500357c7050d50007787050d50035787050d503ee7f6050d501e77b6050d501573f4050d5014f5f3050d501457e76d89501557e74d89500057d74d89501557c74d895014d7e73d89500057d73d895014d7c73d89501467e62d89501476e62d89501467c62d895013d7e71d89500057d71d895013d7c71d89500076e21d89501476c21d895009f7b70d89500357e70d895002d7d70d895009e7f60d895009f7b60d89501476f20d89500057f74589501557e74589501557c74589500057f735895014d7e735895014d7c73589501457f72589500076f62589501467e62589501467c62589501476c62589501466c62589500057f715895000777715895000577715895013d7e715895013d7c715895000774715895013d7471589501476f21589503e57f70589500077b70589503e57b70589500967f60589500977b60589500057f76509500057e76509500057d76509500057c76509501457f74509501573e64509500073d64509500057f735095014d7e735095014d7c73509503df3e43509501573c43509501457f72509501576f42509501473e42509501473c42509501476c42509501476e32509500057f715095013d7e715095013d7c71509501573f41509500057f70509500357e70509500357c70509503ce7f60509501cf7b60509501573f40509501476f20509500057f764c9500057e764c9500057d764c9500057c764c9500057f744c9501557e744c9500057d744c9501557c744c9501457f734c95014f5e634c9500075d634c9503d75f434c95014f5c434c9501457f724c9501476e424c9500076d424c95014f6f324c9501475e324c9501475c324c9501476c324c9500057f714c95013d7e714c95013d7c714c95014f5f314c9500057f704c9500357e704c9500357c704c9503ce7f604c9501b77b604c95014f5f304c9501476f204c95013d7e76d85501557e74d85500057d74d85501557c74d855014d7e73d85500057d73d855014d7c73d85501457e72d85500057d72d85501457c72d85500067f62d85500067d62d855013e7e61d855013f7661d855013e7c61d85500077721d855013f7421d855005f7b70d85500357e70d855002d7d70d855005e7f60d855005f7b60d855013f7710d85500057f74585501557e74585501557c74585500057f735855014d7e735855014d7c73585500057f7258550
  | 16 => 0x8d21415f77158d211a7e42158d21004ff7558d210067f7558d210047f7558d2102cfe7558d21004fd7558d2102cfc7558d210067c7558d2102c7c7558d21004ff7458d21024fe7458d21024fc7458d2140cff7358d21006df7358d2115ede5358d21006dd5358d21006df4358d2115edc4358d21404ff7258d21006ef7258d211a4ff7158d21006f77158d21004ff7058d21034fc7058d210067f5058d2115edf3058d21176ef2058d211a6f71058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210067f6550d211e67c6550d2115f9c4350d211d7e42150d21034fe76d812116d7c75d81210067f65d81210067c65d8121257e421d8121004ff75d81210067f75d812102cfe75d8121004fd75d812102cfc75d81210067c75d812102c7c75d8121024fe74d8121004fd74d8121024fc74d812101cfe73d8121004fd73d812101cfc73d812100cfd72d8121014fd71d81210067f50d81212c6fa20d8121256fa10d812116d7e75981210057d75981210067f65981210067c65981210a7e42198121006fb60981210057f755812116d7c75581210067f65581210067c655812107fe4215812116d7e75181210057d75181210067f65181210067c6518121165be7418121005bd741812115dde7318121005dd731812120fe42118121036fa6018121006f960181211557e76d91501567e64d91501573e64d91501563e64d91501567c64d915014d7e73d91500057d73d915014d7c73d91500073e43d91501573c43d91501457e72d91500057d72d91501457c72d915013d7e71d91500057d71d915013d7c71d91500357e70d915002d7d70d91501367f60d91501377b60d91501573f40d91501557f74591500073f64591501567e64591501567c64591501573c64591500057f73591500075f73591500055f735915014d7e735915014d7c73591500075c735915014d5c73591500057f72591501457e72591501457c72591501573f42591500057f715915013d7e715915013d7c71591501573f41591503fd7f70591500077b70591503fd7b70591501167f60591501177b605915014d7e76d8d501557e74d8d500057d74d8d501557c74d8d500067f64d8d500067d64d8d5014e7e63d8d5014f5e63d8d5014e7c63d8d500075f43d8d5014f5c43d8d501457e72d8d500057d72d8d501457c72d8d5013d7e71d8d500057d71d8d5013d7c71d8d500357e70d8d5002d7d70d8d500f67f60d8d500f77b60d8d5014f5f30d8d500057f7458d500073f7458d500053f7458d501557e7458d501557c7458d500073c7458d501553c7458d500067f6458d500067d6458d5014d7f7358d500075f6358d5014e7e6358d5014e7c6358d5014f5c6358d500057f7258d501457e7258d501457c7258d5014f5f3258d500057f7158d5013d7e7158d5013d7
  | 17 => 0x44f7721d95214476e21d95214476c21d95214477421d95214476421d95210057d70d952144f6f20d95214477710d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067c43d95214467f72d952144e7e72d95214467d72d95214467c72d952144e7f42d952144e7e42d952144e7d42d952144e7c42d952144e7f32d952144e7e32d952144e7d32d952144e7c32d95214467f71d95214467e71d95214467d71d95214467c71d95214467f41d95214467e41d95214467d41d95214467c41d95214467f31d95214467e31d95214467d31d95214467c31d95214467f21d95214467e21d95214467d21d95214467c21d95210067f70d95210067e70d95210067d70d95210047d70d95210067c70d95210067f40d95210067c40d95210067f30d95210067c30d952144e7f20d952144e7e20d952144e7d20d952144e7c20d95214467f10d95214467e10d95214467d10d95214467c10d9521024fe76d91210067f65d91210067c65d9121166be64d912115dde73d9121005dd73d912142fe421d9121004ff75d912102cfe75d9121004fd75d912102cfc75d91211bcfd74d912101cfe73d9121006de73d912101cde73d9121004fd73d9121006dd73d9121004dd73d912101cfc73d912100cff72d912100cfd72d912143ebf42d912143ebd42d9121014ff71d9121014fd71d912142ebf41d912142ebd41d9121034fe70d9121004fd70d91210067f50d912143eef20d912142ef710d9121024ff76591210057f755912116d7c75591210067f65591210067c6559121166bc6459121425ef7259121435f771591211bfe42159121004ff75591210067f75591210047f755912102cfe7559121004fd755912102cfc75591210067c755912102c7c755912142cff7459121006bf7459121166be5459121006bd5459121004ff735912101cfe735912101cfc7359121006be4359121166bc4359121424ff7259121006ef72591211bcff7159121006f77159121004ff7059121034fc70591210067f5059121166bf405912118eef20591211bef7105912101cfe76d8d210067f65d8d210067c65d8d21165be74d8d21005bd74d8d2115ede63d8d2140fe421d8d21004ff75d8d2102cfe75d8d21004fd75d8d2102cfc75d8d21024fe74d8d21006be74d8d21024be74d8d21004fd74d8d21006bd74d8d21004bd74d8d21024fc74d8d211a4fd73d8d2100cff72d8d2100cfd72d8d2141edf32d8d2141edd32d8d21014ff71d8d21014fd71d8d2140edf31d8d2140edd31d8d21034fe70d8d21004fd70d8d210067f50d8d2141eef20d8d2140ef710d8d2101cff7658d210057f7558d2116d7c7558d210067f6558d210067c6558d2115edc6358d21405ef725
  | 18 => 0x710d9131024ff765913117ebc6459131485df73591311979c4359131495f77159131004ff755913102cfe7559131004fd755913102cfc755913148cff7459131006bf7459131484ff7359131006df735913117edf4359131196be4359131196bc4359131196dc43591311969c4359131004ff7259131014fe7259131014fc72591311d4ff7159131006f77159131004ff7059131034fc70591310067f505913117ebf4059131196df30591311d6f71059131014fe76d8931176ee62d8931004ff75d893102cfe75d8931004fd75d893102cfc75d8931024fe74d8931004fd74d8931024fc74d893100cfd73d893147ede53d8931006dd53d8931006df43d893147edc43d8931176ee32d893147eed32d893101cfd71d8931406ef21d8931034fe70d8931004fd70d89310067f50d893147edf30d8931406f710d89310057f75589311857c7558931176ec6258931475f77158931004ff7650931004fe7650931004fc7650931006bf6450931026bc6450931005df735093101ddc73509311c79c435093100ddc764c931016dc764c93100cdc764c93146ddf754c93146ddd754c931466df654c931466dd654c93117dde744c93117ddc744c9311aede644c9311aedc644c93101ddf724c93101fcf724c931007cf624c931016de624c931016dc624c931177cc624c931177ce424c931007cd424c931007d7714c93100dde714c93100ddc714c9311a7d4714c93101edf614c93101fd7614c9311a7d6414c931005df704c9314675f504c931177cf204c9311a7d7104c93101df47650531026f4765053101cf4765053100df7745053100fb77450531007b76450531026f66450531026f4645053117fb4645053117fb6545053145fb55450531007d7735053101df6735053101df47350531197d4735053100ef7635053100fd76350531197d6535053145fd5535053117fd74350531197b64350531197b44350531197d4435053119794435053117fb74250531007b54250531197d73250531007d53250531005f7705053145f77505053117fb74050531197d73050531034fe76d8131004ff75d813102cfe75d8131004fd75d813102cfc75d8131024fe74d8131004fd74d8131024fc74d813100cfd73d8131014fe72d8131004fd72d8131014fc72d8131336df32d8131006dd32d813101cfd71d813125ef641d8131006f541d81310067f50d8131336fa30d813125efa10d81311857e75981310057d7598131006fb6098131005bf745813117dbc74581311857e75181310057d751813117dbe7418131005bd7418131175ee7218131005ed7218131036fa6018131006f960181314557e76d952116e7e76d952102c7e76d95210067e64d95210067c64d95210067e63d95210067c63d95214476f72d95214476c72d952144f7771d95214477471d9521
  | 19 => 0x8132006fb6098132005bf74581321adbc74581321b57e75181320057d75181321adbe7418132005bd74181321a5f67118132005f57118132036fa6018132006f9601813201cfe76d8d41025be74d8d4100dbd74d8d41196de63d8d411979e43d8d41004ff75d8d4102cfe75d8d41004fd75d8d4102cfc75d8d4100cfd74d8d41486bd74d8d4100cbd74d8d41196be43d8d41196de43d8d414cedd43d8d41196bc43d8d41014fe72d8d41004fd72d8d41014fc72d8d41196df32d8d41024fd71d8d41486df31d8d41034fe70d8d41004fd70d8d410067f50d8d414cebf40d8d41196dc30d8d41486f710d8d41196dc6358d411979c4358d414c5f77158d41014fe76d894118eee62d8941004ff75d894102cfe75d8941004fd75d894102cfc75d894100cfd74d89414bebe54d8941006bd54d894101cfe73d8941004fd73d894101cfc73d8941006be43d89414bebc43d894118eee42d89414beed42d8941024fd71d8941426ef21d8941034fe70d8941004fd70d89410067f50d89414bebf40d8941426f710d89410057f755894119d7c755894118eec62589414b5f7715894100dbc7650941016bc765094100cbc76509414adbf75509414adbd75509414a6bf65509414a6bd6550941195be7350941195bc73509411c6be63509411c6bc6350941025bf7250941027af7250941007af6250941016be6250941016bc625094118fac625094118fae3250941007b7715094100dbe715094100dbc71509411bfb47150941026bf6150941027b761509411bfb63150941005bf70509414a73f505094118faf20509411bfb71050941004ff764c941004fe764c941004fc764c941005bf744c941025bc744c941006df634c94101edc634c9411979c434c941007ad424c941034fe76d8141004ff75d814102cfe75d8141004fd75d814102cfc75d814100cfd74d814101cfe73d8141004fd73d814101cfc73d8141014fe72d8141004fd72d8141014fc72d814137ebf42d8141006bd42d8141024fd71d8141266f631d81410067f50d814137efa40d8141266fa10d814119d7e75981410057d7598141006fb6098141005df7358141195dc735814119d7e75181410057d7518141195de7318141005dd731814118dee7218141005ed7218141036fa6018141006f96018141024fe76d913117ebe64d913101dde73d913100ddd73d913117f9f43d9131004ff75d913102cfe75d9131004fd75d913102cfc75d91311d4fd74d913100cff73d913100cfd73d913148edd73d913100cdd73d913149ebf43d913117edf43d913149ebd43d913149edc43d9131014fe72d9131004fd72d9131014fc72d913117ebf42d913101cff71d913101cfd71d913148ebf41d913148ebd41d9131034fe70d9131004fd70d91310067f50d913117ebc40d913149edf30d913148ef
  | 20 => 0x57f75585421cd7c75585421bef46158542034fe76d8142004ff75d814202cfe75d8142004fd75d814202cfc75d8142014fd74d814201cfe73d8142004fd73d814201cfc73d8142024fd72d81422f6ee32d814200cfe71d8142004fd71d814200cfc71d814238ebf41d81420067f50d814238efa40d81422f6fa20d81421cd7e75981420057d7598142006fb6098142005df73581421c5dc73581421cd7e75181420057d75181421c5de7318142005dd73181421bdf67118142005f57118142036fa6018142006f96018142024fe76d91321aebe64d913201dde73d9132015dd73d91321af9f43d9132004ff75d913202cfe75d9132004fd75d913202cfc75d91321dcfd74d9132014ff73d9132014fd73d91324e6dd73d9132014dd73d91324f6bf43d91321aedf43d91324f6bd43d91324f6dc43d913201cff72d913201cfd72d91324e6bf42d91324e6bd42d913200cfe71d9132004fd71d913200cfc71d91321aebf41d9132034fe70d9132004fd70d91320067f50d91321aebc40d91324f6df30d91324e6ef20d9132024ff76591321aebc64591324dddf73591321c79c43591324edef7259132004ff755913202cfe7559132004fd755913202cfc75591324e4ff7459132006bf74591324dcff7359132006df73591321aedf43591321c6be43591321c6bc43591321c6dc43591321c69c43591321dcff7259132006ef7259132004ff715913200cfe715913200cfc7159132004ff7059132034fc70591320067f50591321aebf40591321c6df30591321deef205913201dec7650932026ec765093201cec7650932015ef7450932017af7450932007af6450932026ee6450932026ec64509321afac64509321afae54509324d7ad5450932007cf735093201dee735093201dec73509321c7cc7350932016ef6350932017cf63509321c7ce53509324d7cd53509321afcf43509321c7ae43509321c7ac43509321c7cc43509321c78c43509321afaf41509321c7cf3150932005ef70509324d76f50509321afaf40509321c7cf305093200cfe76d85321a6f661d8532004ff75d853202cfe75d8532004fd75d853202cfc75d8532024fe74d8532004fd74d8532024fc74d8532014fd73d8532476de53d8532006dd53d8532006df43d8532476dc43d853201cfd72d85321a6f631d85321a6f621d8532034fe70d8532004fd70d85320067f50d8532476df30d8532416ef20d85320057f75585321b57c75585321a6f46158532034fe76d8132004ff75d813202cfe75d8132004fd75d813202cfc75d8132024fe74d8132004fd74d8132024fc74d8132014fd73d813201cfd72d81322eeee42d8132006ed42d813200cfe71d8132004fd71d813200cfc71d8132346df31d81320067f50d8132346fa30d81322eefa20d81321b57e75981320057d759
  | 21 => 0x801b001802c01400d0000020000019000801004401400780200020090010054008000000800006800200200040060020008000022002005800c02800000080000040000010008016000002801400600c003804000002f0048118000013009000c00000d000001800000000780180080000030000002001001800800e006009800c000000000001800002d0020008000003000000c0160010000018000000000022c002005000003c00c00a014fe76d89434ef9c43d89431deee62d8943004ff75d894302cfe75d8943004fd75d894302cfc75d894301cfd74d8943024fd73d89434fedf43d89434eebe43d89434eebc43d89434eedc43d89434ee9c43d89431deee42d89431deee32d894300cfe71d8943004fd71d894300cfc71d8943034fe70d8943004fd70d89430067f50d89434febf40d89434eedf30d89431c79c43589431deec625894300cfe76d85434979c43d85431d6f661d8543004ff75d854302cfe75d8543004fd75d854302cfc75d854301cfd74d8543024fd73d85434c6df43d8543496be43d8543496bc43d8543496dc43d85434969c43d8543014fe72d8543004fd72d8543014fc72d85431d6f641d85431d6f631d8543034fe70d8543004fd70d85430067f50d85434c6bf40d8543496df30d85431979c43585431d6f46158543034fe76d814335f9c43d8143004ff75d814302cfe75d8143004fd75d814302cfc75d814301cfd74d8143024fd73d8143014fe72d8143004fd72d8143014fc72d814300cfe71d8143004fd71d814300cfc71d81430067f50d8143006fa50d8143006f950d814339efa40d814335efa30d81431e57e75981430057d7598143366bf64981433a6df639814312f9c4398143006fb609814310f9c43581431e57e75181430057d7518143366bf64181433a6df63181433279c43181431ddee7218143005ed72181431d5f67118143005f57118143036fa6018143006f9601814301cfe76d8d42025be74d8d42015bd74d8d421c6de63d8d421c79e43d8d42004ff75d8d4202cfe75d8d42004fd75d8d4202cfc75d8d42014fd74d8d424debd74d8d42014bd74d8d421c6be43d8d421c6de43d8d42506dd43d8d421c6bc43d8d42024fd72d8d424dedf32d8d4200cfe71d8d42004fd71d8d4200cfc71d8d421c6df31d8d42034fe70d8d42004fd70d8d420067f50d8d42506bf40d8d421c6dc30d8d424deef20d8d421c6dc6358d421c79c4358d424fdef7258d4200cfe76d85421bef661d8542004ff75d854202cfe75d8542004fd75d854202cfc75d8542014fd74d85424b6be54d8542006bd54d854201cfe73d8542004fd73d854201cfc73d8542006be43d85424b6bc43d8542024fd72d85421bef641d85421bef621d8542034fe70d8542004fd70d85420067f50d85424b6bf40d8542436ef20d8542
  | 22 => 0x20280058000010027028006000800100100080240010070010014001000000002201700680000000010000010002005003803000800500080180020170018000002002007800c016003000000003e000001000000c009010801000a0010000004028001001003400000000080c400600400700540020030000000000003000000400400200580280720010000014000002000000000200f0000008000010003802001400000e00180160280040000002004000000400000700000040180000028018000003005001c00001f0000028000004000800000c0000048030000000001001001200000d002800e00100b004c014000005002800600b000801c00600101000080260010010004002000001804403c000005803c00c02d00c001000600b002800400a0030000008006011001002c016001000007800400a010001402a00100200100020040000038018001009802c0ac01b000000800200e01d00280080000010028020004000001c000002000000404e00200a0008000000005000400401e000000001a007004001c000019000800001600d001002c03a004002000402400e0010010004001007001801c00200a000c00400000a800800201001e0048006010002801c000000000002000200b000000001602000f010802a0070070004066000002005004000800a00140000090028014000000002000c05e02600000340360000010008000001000003400400c0000034008001000000000400a000003c01c01900200000a200f000000000a001000001000a0210008000000000000007406600b00f0000042019000001805a000001002000200a000002000200000000140040000008038002005000801000600d01f80540020110010000006001000000001c00100b001402c011001000004c00a005001c0000050000030016002002000400002a002800400000a002001c008011009801c00c0000000000002003004803401201300400000000050028000000007001801416800d0000000000009001806400c0040028000046002007802800201501580000000020000018000000009000c0060000000048000003007000002a01a000001801200000380140640040040040002001003000000c001001001000002300f802400a009004001400401000b00000800000030008000003000003800c003003002002c005005000000c001000007800c00f0008000000003006001c02600600a8034000000002806c0000000028004004004000000800e0000000004002002000002c00c06a000000402c00900c8018000001000001c00000b005004801400e000801001000100400100440130060028002001004800002400c0070018006000001000c01800201d800400000100f005000e000006800000c004000003c0020000030018
  | 23 => 0x117000035f554000017c35e7441001430ce62d119f0d9a33418603a424c8555738efc9920c51ac005973e39530799dc83a94124ca2d1c8e57738e25c10bce300480ca81ec42b16d25cc02429900000016dc35700031954aa8ed2f3ad79be267204881fc2bcdbb68f800023cba500032f81ca17d60e000010473557e00000000004dc95f471ada51500e080384522b4b73d7bab6150b1b044ac29a62292490ccc8555cb018cfa90b5890f94922e68685904915ca2726c2cf5340bbc0bd887d5b4b8c11fb95dad2daf5f98034002002806801000000000a8014014001000c006001000800000c002002802800001a00000000040060018058000000001002802400900080380000050060004000001003000c00c00501c000c00a014001800c00800100300300000000000004006004004001001002600600180200030000004020003000803c0000090010010036001006800c030000000802005e001003800000c00000b801800c001000000000200100a0078000000003002001800f0000030006010003000400200100a0000004002001802400400c0008010034006004000c000000001006c00205400500080000060008000004019001808002000800f0000000000003807400a004005802804e0030008028002000000800001400600a8000000000009000c01a0010118014006006000000400001d0000000016009007800401600c0000000002034006000001c004002800802a00101280040000050050008004002001000006e003002000000400500100d4008009001801000200c00a004000a0010010000024004006801400e00800180240020020018014096000006800000000e0040024018001000808c00200d00180000000080048014000003000800002806b010800403c00c000000002800f0000008008000003000000202c0050044000017000000400600800880740020030018000010001000002c0020100000004004008001800c00a00000000c4000037002000402a006017802005e01a000001000e002006002c00a014001004000800100300140680090000000000003000803800200600380400000010010010004000000006c012010002001001e00300b801002602100600c0000000001800001401004d8018002003001009403800f000000c00600500000bc0020250000004000001007800000205300080bc03000b004000c006000001806000200b000007400800f0050024038001002814000000400a007c03600100100080340050060000016011008801c014008000000405a001000004800400a000802002a010000003000000e003001000200300f0044012000005000400600e00e000800400100c002c000003000801402601201500080000000000004006000000002404602b004801400001f0018014000022
  | 24 => 0xd3064026c0a2600064f80011b64df316b9481120002d08001374e8950580001e459e2100000fbe000028b3d00001176821a3800000056631d80001610001bcc6ac00045d800000027e1ef326983ee18390800000035d6448b750ea0000001b7ceb0d45000000055ae6f36b800000043c41a230c0f402b44e856d56e53a36423700009ac68a2ef922e09f41d331927a64b00004c45140002972ac0eca9e45a781247ec5fc4d5393809695d5671e1ccc467159b1c2d070670626810d1e2d463292d540000d010909613c20000002e057ecdaa46724e02d02f14b3240d58203760518c50641b830107ec164b2d0001a184322320e90409732cec4d9a8918b2d9152c247079e9686cb24b4d240004c61134d308b30641fb0f663646a61fbc294cd322f00000008af60a830dd18000194000000000000039649f0c5b67e9c648900004d12978b18220000278c436db013128a135e1a45e30b6c0b0683000286563a4701650184eb678c0002b5c722a4b00000950500a400039d02ba6aa3fa270536889b0001be8d4ee2a5ea24d80c64c70001424eec8f50563125ad8000000292884219972e9ec4928080159b4d17485607021a580000bd25327c80d896f38b88144a8d97375b9357600001138c5400000000028847f400062f99244fa20370a3561c5885b0dd3884f529f50001bb94ec47e4250001bc295961018685ea0006c30001ab44ee0003a0dc2cd81032983175800009f9228c4ab436df8561386306587b98c000000381a8a40005d1239961112c5ad6e61d65504de46c20db13f836332f13dd3ec000000081dc6817e4ddaf141f60484ce3085ce61e13920524000c1900000000000006470000964925686000152a0002b431616ae89834038c993255e6cc80002b489162082a4682dc73f9a6111ce2780002ce05ca7496298ff87869453fe20ad7462fe675ad0166270736dab78baa79e120153c03a47a1a7293981e79b00c00000000000000000f5e0000001e9937c00000028b50dad3a0002fc8ac20000002c1d6920000000cb90a8d3b4fc9f4432ec912540a14422000000212400000000029e80000003450b3d34e0002b580009a05d61be80012a610b0001189a12994239017c2020006d3800041c00013b81040000000ee895c61cdf00f6923426000057530c422cacf0000001b9400068d80004103964082a4813ca3f000000000000008c000000055029f236900400068f2f00000a5952b2874d64ad46251ec8dc01bd31a392048c8f4570b1084346d321939e5cb45862410030d6cb9a38eaf903f05f93572228a2e0710c193c46e019e65227c0812000326213c0764c416aa94c1e297938a80014ce3f23b70af18801156882e2d85ad9c570218dcea4dc6f198a93a67ce6c3932d6e667a42d304575e00000000019025910002ab1010222000
  | 25 => 0x900015fa000700b5d0494a5425c8300276b793ca962d2c674c19aac61bd68922bb0000000826000249093a71000005bdc6628843b0354000ca206f04b17fe4ce4be1390d38b633cb088cc76ca6646000005e6d805020a48be1060001ef05dc5660000000702ae50a69a90000be8588193db3e000632146d73c83b00016fd32a000000000000081966100000000000de00000007fa323a33c0001ea59800004b8000000000cb6679a65880014840002f2800000093a0000000eea00040e9da148e00012eb78874eb0432aa1e00008571d421217c26910002bc5bf60000000000bc031228a1a8574e46455f27506f43ea0000bfd4726e311c1a80a20b586d139f934a00000036b491c22b73880001a869967a894800000043910b800018964986606a8720460ab1da522b20001fa95c6abb4a520959b066a0002850d5600000000012861c900000016127644f518113aa26e2a280f060e37f5a91105b3656f4460b1c00a67e4c936d4fecd5725b328440484d016a720f967742b980000b8be659d0b1993a51934e9f0191e7610002aad44c9a845b258801c00000002200008c83142a88c7e13a02aad6d89c81f43f8001396d5b4ad000002ec843f298c8e50ce351c1204b1219521dad0988834d0ed90a400844421e92314e87bd5beb3b956c31a3b4afb17640332028a343a85fe6bf948d6a030f11aa5ecd08e1e22a800118c8844cd159514a6c0373a601b9a0006be95280009f73ce1a1d08603a43808f5528a374e709cd6d0526397a71ce90c6b2181f18562c7e0470f80536bb502294c8c5c5cf334ad94744ca04198c298ba7d3073aa64a5649f1421a24000af0000135043026600000014142e10008aa00003fb0bbb8e40001e358fa9a40001fc5ee149ca1e1dc6872d380003d12fd806565061f694023000013e0000000416248444ab2dba22cd5930d18000b97000195cbd4e225dd24a470a7881459545ace4a36eb83d00e4000000151c000dff0003a100009321f08000714000004a9e1aa85ec3dd2f400008301359ed80003f820f0000000b826840bf48b23eb03ab3583ece080001b1d42217100009a14fee8a39d2b6082a70400017c80001621b129896101045da39300b4a231a6322c02a099000134d41c000059abe90849fe5922c813524f048f34d9abab8d2cdb04c53a7363b6b0000000002b10000310cc800016bc362cd430389940003836ab302425c02367c214c35473f4879f0cf022bd20b1eb486e531416a220000a663f30000af80004fd8e7800026d3720000f00a311d612792bc72c521b390e94ae20e711ec94ae0633321190f46230faad2000000007700011e04c611a1a542be0e10001d187180006a728f8000cb50001c2938863a0e315ed4bea2f5fe9b3d208bb605a25d0b1e4b42dc24a0000714272a84c03e9d16f61cc000
  | 26 => 0xf44612bf09e5144b700000da1958c6a5efa9102e49d80fd2fe8d70ac61d2000000051f00002e134c000000315c0000000003a08f7c24500013fc0009e51649c5800068f0fcb92c52480160c23e43948ba5fa248413ac2400021300000005740000c66db970d955c00000070580007b4e4a00000009625c200000780000003138c6d1fcacd00000009d6be30000000a2c9815dd9bd88160dd3080b908f20000000ce586814401437705a0a3d3d2800000086f3f71a6d32e00051b2b015160b56608000f580c100000015a2c3d5290400a22a4d0002d3120ccd540c00001844285208ee02d476031311304aa0bc2168e989dee1d0b990d861655242910640000000a10d1539a86c23880000005f167da40106c6ac0a41138538b010d68b145b2ae90000001096770046832c0002de28418641e000039f00013fab154371f5961a00000020480008b045c113dbf014f1cca35c09e91553cb79ca544c10a824b97a607639c9d0904696c281267c8666f522c12917aa61437820e5c1ec6662436a0f32d6d51e30b814281b386172c04c39251995d0000a7b63eb47487499b18414295926de0002814000a8c53e9825994bca0a00bbda700005100519a8e4fe3afb8299cee0c26786751400000001c6c7d00002f08001cfadfa54e1c7d4000001e0b2bd6342f3008858db280000c7afe40000002eeb15400006b4f88000d187130000b041ea1145eb385d86600017b375993ce1f2138000768dd941aa5547c82c019f044d57e3713eca9b4ae4883000121cfbc78b56536dd0be4c52ed39d877657944118f92d20004e52fc0a9a37c6b219e582caf30002c5cf5c3a332997bd16e6e548b3a05bfccad3b524817ee8680ca36200003e60000000000000384365566a00000015740000000002ac9492d7917b875c3a22bb666af21c488e25ba23549f4b882a097b48966502aa8aac14cab40002c2977e000000249cb4012d59f800000093104d00004e817465a14d860490a08fa76812a3886f9868c1b6cb35bfb349864533310b0754b640e706a5340cecc70b82dc5b8c6b021c870112ae866afb6b96da3dd0e42b7dbd05fa3fc8cecb4e00050f9ba907e0000000000e9e94b0002c305ce1c430ba36054e02c5e91d68080a302552550a0e77f71297f43521c155980012340006a200010ac40d00000015745db57c3898e8a8d25528ae9bc05464300000000a020000ee40001f13d402c55ba5c71bbb7480009ad0c587f98ee61c6a8000120a16600000010622a40001615c0e9982db1844b04c7f14734dc0000002e99b10e522f25d9b1b9cf8ce116900b9a86bc212f8ab086a54856993d007c0a550e0d715ac94e34b8dd4952e0e33b2a140f21902ac956044c2162333089464c943919db12a05dc14608cc65222f0b2a4643869bd2cc26e16b80000e6091c5020000d
  | 27 => 0xb227acd964404658ec9c80827000000105e00000000c400052d4bf2570ad80000000000a7ad2c402ac64970a8d4e799b0e1ac375318349c78c952f49ad17c065c19b0dac83e56a16a09905123096ef87591ca0001e100013046006148000ef8b894cf1fed19a000661978d8e402961fb498c8a0005360069b903e900000007a09e90000854000c2702980000000000000000c6e00001a2e98000a70376376c460e490000c581560000003715bca0002e500011e6a1011d9b64c78cf3045094ccca9d24a604f012e9520002460000ded37e0001c00ba10f7a8488540000000fcc0002d658584bc18e087120932002034b2cd239987244559503bd0d413d67fa8d02d20002c7340826a0eb4b693a00001cf0001c881d860300008748d400000022a83cc7340000001b4c0000001f4930e8fa714b9940600e20000eac2fe5a90039b0db1eb54659141152083e66617e18988d9000000170e54400000003d00000120000a52c5e652824c64417a0273711cee9e86b012195f2c5c26d1c143b49f44d5a2c8aa614e0b214e41be99d0368028f6e712613046d3c4d22000000000000000019d13dc2eb00031c59f400000006b800000072fb4c400009b5f4a3dcadc3b0000147931e00072116949667c24df800063219f1ec80008dc0da54c2bc8336ca7411077cd7cc080e6a3b1b30b7721f0f60500e550da0fdd54c11963a2ee410862c0c00338b6a88f6061ddceae16c0668cc0d7adbe01c1cf5aaad595bb004d5a4e6b11f12fc6ec3c62ca9a4017690d5c18018b321bb63e0fb8a064184f6a0dd5de3dc174011c40cc4f30b13ec82627a5958894dd25f50000001364aeb69786953168dd5bd2a0cce6738691b18d53a1eb4e337a571cd6f24d1714df2d90000340d7dca6b6a091758de32330528d5c764110001f415eae6602c88b95d892c0001820a42c0e60d32f179c44943b80003c000054b07fc5b0c9649830f052ce4400021f07fe2a368a8d200002cb0a6134926800071000002341363ddb8e19520862060001874c8732f80000000003f880000000003660000e228c96c12d9c0000006518811586b595379f1063c2b625f00005a20006c48cc80000000000b09bdc0000838608000000401930ccde3ce36921612ca0004ff9b9967c9c044ca7802a2b275421a68000d526908df8d1adb412610bcfaee3f0001099c7422800000000000004ef80013ba00046980007c619a37a21d0ef0cbf1cb8b71b846130e59e0c00427c71e91ad4a20fd00036f40008b97458c15886e5e086000162255a37fb30144a8b17228000b3a52f00000019969890001334f280003e69e40308160376b88ce9623c39702d912ee2d49b8a840bad336d1b70cc7087b3c227e00001556022741914aae4048d551fa3b36831abc098ccf0d5843916a7402ea34f973a69e37c3615a
  | 28 => 0x85e00054d8000efc3b5152b9fdc3256d0002500c9c95f09519299e48671780001d1a0004b5a058cb07e80b689d46ce13852780000e8bcf0578e6c000d3d00780013220000ae025824e00000009c9960bb800006840006bb0003220e1eb2132e83e0dfc00016f92e84de000599084ce66488211174831a0b96d8a2a4fc85e601fb6e983c5814238fd13cc4143649fd559000016980008de41c0001e90e12d5e54500005680e8356b701a84b855a0ab14d280696a4119d18aaa048e988815ab801979e48ea68074ad84a401019c46122acb3889f6952390106d5c257b0e145cb985cb14f13107eb65b8a790b896a0feb684bb0e123ea9159bb4c232662dc9b9676f4c186d8000d610d987a4000901291000050e0001e51c981a2b6c5f794fc79a9581bcb58c0c077160585b9ce400071b114cbbc6784b02c886ccd0d3830c41b700004a403a99507665720e409aa00005501191ec8f850610192922ed629281da388c700016c80d07e31b90d481f40563ab2639becd2730d92ad55200044833e4b4c154672a1a4be0b943071aa1ca64e70001901974d7b0d32811cd26d64841bed48a00059c8c7c0000a86672d99256431000300cc3a2505db869cee47a03458e71aee0003339f6cea8a860001e8d142a064601e7c0000004db38bd22206442202b8000c5a7011cf05907e2248384042065b72c31cc6b4e4f587071c000bda6552a200005960000001ce0cd93c9800049e00054d00011c2b1c5c52e8908a4e066eb42878e6633fb86812fe7626d903fdba88ac3eeb095d0e0503952a0580e83c06639184520f923ba2b44121795be179077c450474181458647c1008151562dfc64c34f0054cfe6152f11bcc7371b7168c5f6b533f92c6c0ae0006c634b4c823533708e84cac1875d516f10a2da00003529736a0f1a229c481edd800001cc07248961d8001a225cc65e9eac9ec6d52f4024970864d4b2120011668248831a48146ef3680000c24a5a09cabb817e5bd2cfb9e8c1a00001b0179342bcc5bc2f5d8a80005b480004745c30001d48f9218c11b25e11bcd68539a5d953e50b000354c92a82a2a1b705a1edb6365204437c3730698250f0a71a2d8893466e5374eb2a9d412afb1e9a971accad933a8398eb85c011b91e088c28f4eba4fc7965ac35b908db661f065b0261a2646022d3638160aa464819b86583ad1938214bae4ea0c082dc3e4e432bf8be0220dc913501bc000cdc73d8e7c0fc48b5d4b1880f803d2ecac599bc4246180325ad400036e95e8cc22675929fe16780c62011620028b234a79a0400000056a85e13bc00036a35c87e0bae6bc33f0000000000213800000044f335c06a3b767b98a57869423f800009ea4d90002f886c026c6fa8000fd288b28a80006860006feb41d7562595b11e087124ca42e99fc57c3d40002a003e6d802
  | 29 => 0x1289710000e03000000000000018690956962ce0a18470ef4adb1fc83804d200000027651880005a3800000090e4de13894ca00044a2918abe00063c0688fb4137236353cb9299300031c18580f75faac4d2ce00035e0ebd8d0b5a1fab18117edf760da55cbc47b049a86e4d8446966fb82586aa505499910642d162731b141b84b000000007980000002e4480edd05ab0f20d72141516396c0005490001acc4621050002fb455c86527eb9b17928a7720ab084428e320808702405206682e701b0d4b1eb22386665f355e07d00002834400111cc05356d62bb525e10923ab7d0a96374085029d7826202c9244d60c8934e61490bbe25a636947514633d26f1ed0a5841747d91510e2ba86f7a21d7fc0a345e81345cc1b5544b2ac8086e218e2640b562d71b68189476b8f1deaf3527ccb8417395908062f03bb5cc8868ca4ab11f54fc65a1e9384422474d3498f244141e269720307f82975341860e3cd253a39344000d2b2790000630a0d0002619aec0005a516e526678f0f616dca7000047fa2a07bed65674348045414515fb380b0e91419021cd7b650e0c31de44187b854f13cd3debb13b58aa998820000017186dee542e8048400096143f1b44000b2e3b1b668bd67021b4b84c9ae0003212dec1c8d703e7a511936c866c93690836c285b78088fc2755192862849c0000dbb3a8ac688131e8329a00d3940a9cac5884dd3031e60f8a09c40bb4602662e009a03f85f828600006384e29ec138000000000070e22f1038b956091e2400000000000019a20001308cb40000004cc80014ae0000002b703a6000000054800000000039858d801b25e0444cc00000002bdc8d00002042d4400000000024ec74039813b1d051d20000002fe00000002e700000000001750f540007503230e740004476082cec95a57870d29c80007d400000003a0b9218000016c09a402125d49304933870d952a200000020b19d27c85801690530d930000000fb000046a0001cd478d00000014542b56be15514c00ed00013b073457068924f1ac4a2229a085d0000003a70e181e6d4960090e154624b24204ad43ca4c3c89bc507a5713518adca9c0216eaa9002ec11d702800070e7b9628000085815605129dc55207b3e63679b1ae312fbad9156a5804430e9555adde62580350340002560000c2ab023939129ca05400002868000821649226862e80b10799ac2446514e2b9b871626039938d54c8dab11c9f1d52eced201b4fc32641a3d10ae07e297d65d8d3c4fe1c244e0790000bd1000035d4025b4732059c762e3e1c00d84f8200000019edad6000000000101a8ef00026d57f680e18a00000000002940000000c795f59d9d522c1428e076585600023f8000a0c3d700000c930a000067b325272a5d0000000000157000325d10addd3d09e5cc5634a0000001
  | 30 => 0x1b690b24573240ae40f00003a180004bcc7a36300007544c20002b1175ad8b00000000009770000d45cda68571412b96fc1750ea99b42a6df92ab1e18a247dc18233685c49c91248a50b5cc3e1510d6cc165b0180af6441a00031cabd000078a280143437e8ea2df035852ac67535064496e5a871b8000944e2b00033bd00c58a6b729b87c4dd34359144bfe6e80cb251ce4a87d7312bfc9da3db122000035000051d00000fa394000002d148b032ba81499724e108421883ce17c4b880000006a519f800000035917d1f28ef60002ae1b3911aaaf00033c10400006ba8a7cde40002cbac50d749a33df88b01880001fe80000007e727e18d50260000003a15afc0001dd016c0008cc31b00003b096e13d9430000bd8000000094e00057f2b4045a9c21f3afa8dfac020000000b741ee0a3920d6885c10001cb4c86d9d1a82bd99044a0354aca40d4bc759a13e54ea9960acada97401e568b8cf181a79d33423f09ac8d15c81640ffa8eb121a2f97969261e2aef5224bf167126b825033a55e8909a343ed62b14042963786570b305f273b17481c101e00050ba29988cd353588f11244c83405116d3ce1850372184e6281e6992190e02dce3af1ed4bec53b19c3404d6a7a72a6149443c8d62369d1087e82423a08916588140878a40094e8009939706f60d91de0a44000c366f90000000000000399d082ae61a006c00000000000000d7e0003b99d4560abfc0001e380409dc0002a3db528f222132712464e932ca8ac0004bb2fa06b12042ec483819804ed2446f9f8142a4a123b38b868e5aa1c9923db0619221a33d8f548e00000c4d63c0004b9136c35eb3325a97b9c4ea7c5ae8eb9b145422ca2a84000c8d34fa4a95542e334416ecc3cb2f04080002464972c68bd18f698a4a31194ca8d514bd0000fda8506288a096d6cdb00000012365835a3085017466468c84940007fe12d8fb09c6e15504118c1c64960920c0cc60a486a6b11d008e78047a7e957032418e87144c68d00000000ace0004f98d249808794db800000055b00000000003845438000eba5055ef000078077d00031d40006244863314a606f72e6aa3890a0005a68000a3400024daf9d66eb86728900400000050180014c2be5300a4245269db0000000db832624e247c20659300023b8ffe5181578001a802a600026c46840005c9843400000038c05ad6be1de0000cc59e298d0000000d44d716f52d143ee0003803015436c615ba83f071c4bd1f7b05db785c80000cac62238f1b51a98000d0515800007523b6
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe6921d8950440012f70eb12a08802a5e21d62541100063dc3ac4a822005a7a87589504400b4f10eb12a0880031e21d625411002c3c43ac4a82205fa7b825895044001cd704b12a0881529ee05625411000739c0ac4a822027b7281509504404f6e502992a08809edca1f715411013eb943ee2a822006b7286dc5504400d6e10db8aa08809f5c9db715411013eb83b6e2a822000b7184dc550440016e307b8aa088002dc60b7154110006b9b96e2a822000d7172dc550440016e50ea0aa088002dc21d4154110035b943282a822006b7086505504404f6e708a0aa08809fcce114154110227993a282a822000f31745055044001e66c8a0aa088113cc1914154110005b9c1a82a8220a4f32435055044089e6086a0aa088002dce09415411022799a1282a822000f314250550440016e50e98aa088002dc21d3154110035b943262a822006b70864c550440016e70898aa088002dc611315411013db9c1a62a822027f53834c55044087ea4e698aa088003d45cd3154110007a9b1a62a822043f50634c55044147ea68698aa08810fd410d3154110005b9c1262a822043f53324c55044001ea26498aa0880035ce1d2154110005b943a42a822000b70874855044001ae10e90aa08801adca192154110035b843242a822000b738448550440016e30890aa088002dce0d2154110005b8c1a42a822027b7382485504404fec70490aa08810bd89c92154110007b0b9242a822000f63624855044085ec0c490aa088003271cf6450110034da43a82a022006ab4865054044093b28e6a0a808801aec201415011013e3c3b2a0a02202ae38645414044001ab6e6a82808810f561cd5050110006b9b8aa0a022000f31415414044001938e9b1a608801a7521d314c1100356a432629822047d94744c5304400d7a10098a608809f1e1d9504c1100069dba2a09822044d38745413044053cb0c6a8260880035cdc5504c110007a898aa09822000d73815d62044001ae102bac408801b1ed857588110036b9b0aeb1022000d72415d62044001ae462bac408810b5c8857588110216b890aeb1022000d71755062044001ae2ea98c408801a3da1b7148110034f243a429022006ae48648520440039c8ec90a408801af8201214811050fb1a82429022054c7976541204404f8f0eca8240880039ad895048110006b9b8aa09022000f61215412044001f4284a0a4088003f04c93148110035f043a429022001de087485204400d7c50c90a408801af8219214811001770432429022002ee3764852044003bc4ec90a4088007781d92148110017703b2429022001ce0764852044001ec70a90a4088287d82152148110516f1baa4290220a2de1754852044143dc6ca90a4088287b85952148110005f1c22429022000be18448520440017c70690a4088002f860d2148110
  | 1 => 0x104b2a410801b1edc9654821003735b92ca9042000e6a425952084001cd464b2a41081539ac8565482102a73490aca9042000e69655092084001cd2ca992410800237e0d755911001c6e41aeab2220008ef825d564440051d904baac88800e37a1f73591100064fba0e6b222000c5f73d4164440fb8b8e7a82c8880022fe117558d100245e422eab1a20008ef825d563440051d904baac6880122fa1f7458d100064e3a6e6b1a2000c3f74d416344157878e9a82c6880032710e7650d100045fc22eca1a20008df835d94344001938863b2868800237e0d74d891001c6e41ae9b1220008bf845cf624400917908b9ec4880171e9d550d891000735a92a1b122042e6852543624400b0fd0fbaac4880023be0975589100047bc0aeab12200087e871d562440018d8ebb92c4880031d1d771589100043f43ea0b12200587c87d41624400b8f0eb282c4880163e21d50589100043fc2aeca12200587c855d942440011bf06bb2848800e3720d76509100145e43ac8a122038a9c8359142440010ff0abb264880161f215764c9100045fc22ec99220048bc845d932440051b90eb1a64880d6a7211634c91000cdac26e6a0a2004ab684d8d4144155d2887b1a82880123d21d6350510005b8c28e0a0a2000be1821c141440033ab07ba2628801a3d219744c51024eca21ae898a2003ad683d913144153d2887b22628800e3d21d644c510005b8c28e098a2000be1821c131441138e8edbaa42882279918b7548510004eac1ee890a20068f4865d1214400136b09b9a428801a3d219734851001573436c490a2000b71851c1214404f4f301b22a0882a38ed0364541100052fc1ac8a822029a5c83591504404f4f301b1aa0880028fe1163541101551e422c6a822027a7980d89504400d4f101b12a0880021fe1d625411002c3e43ac4a822006a7686dc5504400d4e90ca0aa088113ccd0141541100353a43262a822043f53304c550440012e90e90aa08801a9d21921541101473231242a822042f6320485504404f6e103ba2a0880029ee19745411013d3c432e8a822000b5b835d150440876b106ba2a088002dce05745411013db840ae8a8220a8e3a64d915044151c70c8b22a088002d6e0d645411021dac41ac8a822027b7081dcd50440014f70cb9aa08809e9e21973541100059dc22e6a822044b38845cd50440016e702b9aa08809edc20573541100059dc22c6a822044b388458d504414fcb0c6b1aa0880029ee1943541100053c43286a822043f184350d504404f6e502a1aa08809edc2077254110007b110ee4a822000a7b865c9504404f4f10cb92a08810b5a1c97254110005b9c0ae4a822027b70815c950440c54f50fb12a08804e9e21f625411000735b96c4a8220a6e6872d89504400d4f703b12a08801a9e607625411052f3590ec4a8220a5
  | 2 => 0x9415412000794a1282a824028b6a824c55048001e926498aa0900035ae1d2154120005b543a42a824000b68874855048001ad10e90aa09001adaa192154120035b443242a824000b6b8448550480016d30890aa090002dae0d2154120005b4c1a42a824028b6b814855048051ec70290aa090153d89c52154120007b0b8a42a824000f636148550480a9ec0c290aa090003271cf6450120034d643a84a024006aac8650940480b9b18e6a12809001aea20142501201463c3b2a0a02402ae38645414048001ab6e6a828090157561cd5050120006b5b92a0a024000f29425414048001938e9b1a609001a7321d324c1200356643264982405ad8c744c9304800d7910099260900a31e1d9504c1200069dba2a09824056d38745413048053cb0c6a8260900035adc9504c120007a4992a09824000c3f749d165840014bf06ba2cb080029720d74596100051fc22e6b2c2000a3c845cd65840010fd0e21acb080021f61c43596100053741086b2c2000a6d8210d658404f4ed0221acb080029d60443596100353d40086b2c2000a798010d658400d4f501392cb0813a9e60272596100053bc0ae4b2c2027a74815c9658400147d08392cb080028f61072596100052f418e4b2c2000a5d831c965840018dae4392cb0809e9da0472596100053ac08e4b2c2006a7a801c965840174f300392cb0800297a0e42596100052ec1c84b2c2006a7a8090965840014f301212cb0801a9ea0042596100053cc0084b2c2000a3e848c9658400147b09192cb0801a9ea0232596100053cc0464b2c2006a7a800c965840014f300192cb0800237e0d755921001c6e41aeab2420038de87dcd64840e98bea1b9ac9081d31754373592103a66b886e6b242074cd510dcd64840d593ee839ac9080022fe117558e100245e422eab1c20048be87dd163840d987ea1ba2c7081b30f5437458e103665b886e8b1c206ccb510dd163840d593ee63a2c7081b22fe117650e103a46fc1aeca1c2000e1c43595438400d1790eb22870800ea720d6450e100346e43ac6a1c2004a9c8458d438400b8f4eaa82c50800237e0d7650a1001c6e41aeca1420068bc87591428407153906b22850801a3b21d6250a100045fc22ec99420048bc845d9328400d1b90eb1a65080d6a7211634ca100347643ac49942000a7b865d150840016b706ba2a108146d620d74542100053dc32e6a842000b3b845cd50840a567108b9aa1080029ee1943542100353c43286a842051f184350d50840014f70cb92a1081435a1c97254210005b9c0ae4a842027b70815c950840014f50eb12a1081429e21d625421003735c12c4a842000e6b72589508415bcd0e4b12a1082b79a909625421056f35192c4a8420ace6b215895084159cd242b12a1080039a589425421000734b1264a842000e6b825952084001cd
  | 3 => 0xb1a40abc3c74d416348001938873b286900022fe117650d200046fc1aeca1a4000c9c431d9434800535b09b9a8490012aba13635092059f4621ec6a1240048ec8758d42480016d30a3828490002f86047050920014e6c1ee899240068ec865d132480b9b1886ba2649000eb3a0f644c9205974621ec899240038ec8759132480016d30a3826490002f8604704c9200046fc1ae9b0a40038dc835d3614800117f08b9ec2900122f21173d852002e3d3aaa1b0a4000e735154361480a9ce0a2a86c2900062f21d64505201954e41ac8a0a40018dc8758d314805f53908b1a62902231b1db75485204473230eea90a40009cd83dd1214800d1d90cba242900026b613734852003476432e690a4001ae686d8521480016d30a38242900a29e603645412058f1da06c8a824000a5f8359150480534b906b22a0900a29e60363541200051fc22c6a82402aa3c8458d504800d4d90ca12a09015bcad0142541200353643264a824055f4b304c950480514f301b0aa09001a9e2036154120004b643a42a824006a6c86485504804fcc8c290aa090153d8c412154120145b4416e8a824000a7b865d150480514f10cba2a090002d6e0d74541202adac41ae8a824000b6b825d150480516d104ba2a0902c78e993645412058f1c322c8a824000b5b8359150480ab6b106b22a0900a2da20b73541200053dc32e6a824028a78865cd504800167708b9aa09015ace2117354120005b5c12e6a824028b68825cd504800167708b1aa09015ace21163541205872c31ac6a824000a7b8650d50480014f10ca1aa090157c610d4354120145b541286a824028b6a87dc95048051ad50fb92a09001adaa1b7254120035b4436e4a824028d6a76dc95048051ad0edb92a090002da6137254120005b4c1ee4a824000b6981dc950480016d50ea12a090002da21d4254120035b543284a824006b688650950480516d708a12a0900a3cae1142541202b7953a284a824000f29745095048001e56c8a12a09015bca1914254120005b5c1a84a8240aff2a4350950480ade5086a12a090002dae0542541202b795a0a84a824000b6a874c950480016d10e992a09001adaa193254120035b443264a824000b6b844c950480016d308992a0900a2dae0d3254120147a5c1a64a824055f4a734c95048001e92e6992a090003d2d8d32541202afa431a64a8240aef4b434c950480abe9086992a090002dae0532541202afa598a64a824028b6882dc55048001ad6e5b8aa090003d8c8771541200053dc32e2a824028a78865c550480016d704b8aa0900a2da2097154120006b5b92e2a824054d70715c550480a74f50fb0aa09002e9e21f61541200353cc16c2a824000e7371d855048159ce0e3b0aa0902b39c887615412056f3890ec2a82400097b8758550480252f10eb0aa0900a2daa0
  | 4 => 0x4c00d73100a1a80982d3c6d41435013014e3c3b2a0a02602ae3864541404c053ab0e6a828098003c650d505013012e5c3b6c8a026021cd876dcd404c00d7310ea1a809800f6621d4350130035cd43286a026006b988650d404c009d310ca1a8098013a6dd9435013001ecd3b286a026003d987650d404c009d30eca1a809800f261d94350130005cdc1286a026000b9b8150d404c009970eca12809800f361d93250130005ccc2264a026000f89424c9404c009970eca0a809800f361d93150130005ccc2262a026000f91414c5404c00187ee93a2cb1000297e0d74596200052e41ae8b2c4000a3f845cd658800147908b9acb100021fa1c43596200043ec3886b2c4028a6e8210d65880014db0421acb100029da0443596200053ac0886b2c4006a7a8010d65880014f30021acb1001a9ea0271596201fd3cc04e2b2c4000a6f825c565880514d904b8acb100028fa1071596200051ec20e2b2c4000a5e831c565880014bb0638acb100a29ba08715962000536c10e2b2c4000c75711c5658800d4f50038acb1004e9e60071596200052f41c82b2c4000a5d83905658800d4f50120acb100029e60241596200353d40082b2c4000a7980105658800147d0918acb100028f61231596200353d40462b2c4000a79808c5658800d4f50018acb100029e60031596200046fc1aeab2440038dc835d564880071bd0fb9ac9101d317d4373592203a62ea86e6b244074ccf20dcd64880e999a41b9ac9101ab27dd073592200045fc22eab1c40048bc845d5638800917d0fba2c7101b30fd437458e203661ea86e8b1c406ccaf20dd163880d995a41ba2c7101ab27dcc7458e203645fc22eca1c40748df835d94388001c3886b2a871001a2f21d6450e2001d4e41ac8a1c40068dc8758d438800953908b1a87100171e9d550586200046fc1aeca0c40038dc835d9418800d1790eb2283100caa720d64506200347a43ac2a0c40008bf845d9318800917908bb2631001a3721d634c62017d4e422c698c40068f48758531880014f70cba2a110002d6e0d7454220305ac41ae8a844000a7b865cd508800167708b9aa110186ce21173542200053dc3286a844006a788650d50880c1e3086a1aa1100029ee197154220005b5c12e2a844028b68825c550880bfae0e2b8aa1100029ea1d61542202fd3c43ac2a844006e73815855088001ce6e2b0aa1102979c1c5615422052f3920ac2a8440a5e7231585508814bce442b0aa11029b9c485615422000738b0a82a844000e71614c550880011bf06baac89000e3720d75591200047bc0aeab2240018f4815d564480071bd0fb9ac89000327dd073591200062fb9ea0b22407dc5c73d41644800117f08baac6900122f2117558d200047bc0aeab1a40018f4815d5634800917d0fba2c690003271d37358d200061fba6a
  | 5 => 0x80021f21d65486300073210aca90c60068ec87589218c0035c902b12431801a3d21d614863001572412c290c6000b9b83509408c071b30e6a128118002e6e0d4150230196cc39a82a046000c3d75d53644c00b17f0eaa6c8981ab0f9db50d91300061eba8ebb226025a9e831cb644c0d953b06396c8980022fa1c52d91300045ec38a5b226025a9e8314b644c00153b06296c898002ada0452d91300055ac08a5b22606caba8014b644c00157300296c898096a7a0c71d91303654ec18e3b2260008be87147644c00117b0e28ec898096a7a0c51d91300054ec18a3b226000aae82147644c00155b0428ec8981b2aea0051d91300055cc00a3b2260008be87087644c00117b0e10ec8980028fa1421d91300051ec2843b226025a9e83087644c00153b0610ec8981b2aea0021d91300055cc0043b2260008bf845d5644c0011bf06baac8981d317dcf50591300045ec3cca3226000a9d83994644c16b57301328c8980022fe1d65191300054fc1aca3226000a9d83988644c00153b07308c8981ab87d8f50191300254f436c8a1a606cc9c76d91434c13f938c9b928698263271937150d30366cdba0e0a1a6064c9c73193624c0051b906ba6c4980022fa1f64589300045f438c8b126000c9e431d9424c00517d0fb2284981aa37a1b744c9301ae4e326e899260068dc865d1324c06b938c8ba26498192a7a1b644c9303664e3b6c8992606ac9e76191324c0d5938ec3226498003a3193624c9301af46322849926000c9c64dc5324c001733083826498193271cc64d853000c6e41ae9b0a606c8bc86dd1614c00117d0fb22c2980022fa1c64585300245e420eca0a6000c9e431d9414c00317d0fb2282981aa37a1b744c53017e4e326e898a60068dc865d1314c05f938c8ba26298192a7a1b644c5303664e3b6c898a606ac9e76191314c0d5938ec322629800327193724c5300074a326c298a602fe9464505314c0017330838262980122fa1376485300045ec26ec90a600587e859d9214c0010fb0b3b242980030f19375485300061fbaec890a6000c3c75d91214c001d4843b22429801a3721973485300064e322e690a60069d8805cd214c0d547d0db22a0981b3c60c364541303661fb86c8a826000e3b70d91504c0d9c7441b22a0981b38e84364541303a52fc1ac8a8260b6a7b80591504c0d947d0c322a0981ab87d8c64541305af1db00c8a82606af1830191504c001c38c9b9aa09801ad6a0373541300352e43286a82602ae1c6450d504c00d6b100a1aa09801a9721932541303d70e32264a826006b58804c9504c00d4b90c98aa0981db871913154130035ac40262a826000b9b844ca404c06bd30c89948098002e6e11319013017f4c322632026025c9c73d91404c03b938c9b9a809801a6721d43501300354e43286a026003c9c7650d4
  | 6 => 0x46fc3aca31a8000a9f84594635000153b09310c6a0002a76126118d403570fb26a031a8003a9e86d8d43500e9938edb1a86a02772718f7250d404964e31ee2a1a8074d9b731c1435013b938e831ec4a000a2f21173d89400046f43ec6b1280008de8718d62500d517d0db9a84a00e32718f73509401c54f436c6a128074c9c76d8d42500d593cec31a84a01ab271d863509400074631ec4a128000c9c63dc542500017330638284a000327d0c764c9400345e432e89928038c9c635d132500051bd0fb1a64a00e3a318d424c9404964e3a0c7b0a80018bc845cf61500e91b90db9ac2a000237a1f63585400046f438c6b0a806a8be86dcd4150065938c7b9a82a00caa7a1b63505403a64e3b6c6a0a806ac9e7618d41500d5938ec31a82a00032718f72505400074a31ec2a0a8000b99831c141500071b9063b262a000327d0c764c5400345e432e898a8032c9c635d131500031bd0fb1a62a00cba518d414c54001c6f41eec90a80008dd83dd9215000b0fd0b3b242a00021f61676485400062e31eea90a80068bc865d12150001938c6ba242a001a6e20174485400062fbaec690a8000c5c75d8d2150001d8843b1a42a00ab0f9db74541400070e31ee8a828006b3a80dd150500d54bd0db1aa0a01d3c610363541400072db86c6a828074e5a20d8d50500e9cb421b1aa0a01ab87d9063541405b72db00c6a82806af184018d505000d4790ca1aa0a00a78718d43541400359c40286a828006a3c8650950500f7c38c6a12a0a001ace20142541400351e43282a828077e1c63505505000d67100a0aa0a00030fdd274596300353d404e8b2c60b7a79809d1658c0014bf06ba2cb180a69720d74596300053bc0ae4b2c6000a74815c9658c00147d08392cb180028f610725963014d2f418e4b2c6000a5d831c9658c0018dae4392cb180029da0472596300053ac08e4b2c6006a7a801c9658c03d4f300392cb180a697a0e42596300052ec1c84b2c6006a7a80109658c0014f300212cb180029be09715963000536412e2b2c6000a3e841c5658c00147b0838acb180a697a0c71596300052ec18e2b2c6000a6e821c5658c0014db0438acb180031d5c471596300353d400e2b2c601ea79801c5658c0534bd0720acb180029760e41596300353d40082b2c6000a7980105658c0010fd0e10acb180021f61c21596300051f42042b2c6000a3d84085658c0534bd0610acb180029760c21596300353d40042b2c6000a7980085658c0011ef02baac5180063d2057558a300064e21ee8b1460068bc87591428c00d1d90eb1285182cfa310d6250a3000477c12eab0c60028ec825d5618c00193887ba2c31801a2f21d64506300347a43ac2a0c60aae9443585418c00b0f90bbb243180021fe15764863002c3e42aec90c600087d86dd5218c0010fd0eb2a431
  | 7 => 0x76811d921540018eb023b242a80031dc84764855000637108ec90aa000c6c211d921540018e8423b242a80031908476485500063cc00ec90aa000c6f201d921540018f4403b242a80031e48076485500063b880ec90aa000c7a101d921540018f2203b242a80a657a0f7448550004aec1ee890aa00697a80dd121540012f301ba242a80021fe1974485500043e432e890aa02a93e84dcd215400127b09b9a42a801a5ea037348550004bcc06e690aa00087f865cd21540010f90cb9a42a809e5b21d6248550006363b2c490aa027b648158921541776d700b1242a80a25d21d61485500063a3b2c290aa028b64825852154001ccac4b0a42a82eadce0161485500063dbb4e090aa000c78769c1215414bec04338242a80b69e21970485500063c3b2e090aa0acf60215c1215400d4f50139acb202e69e60273596400051fc22e6b2c802aa3c845cd65900014ef02b92cb200029d20572596401551f420e4b2c8000a3d841c965900014bd06392cb200029760c725964000636b90e4b2c8000a76811c965900014eb02392cb2001a9ea0072596401353cc00e4b2c802aa3e848c9659000147b09192cb2001a9ea0032596400053cc0064b2c8000a6f825c565900014d904b8acb200aa8fa1071596400051ec20e2b2c8000a5e831c565900014bb0638acb200029ba08715964000536c10e2b2c8000c75711c5659000d4f50038acb2009a9e60071596401551f42462b2c8000a3d848c5659000d4f50018acb200029e60031596400043f43842b2c800087d87085659005547d0810acb200028f61021596400052f41842b2c8000a5d83085659000d4f50010acb200029e60021596400047bc0aeab1480018f4815d5629000193887b9ac52001a3721d634ca400347643ac499480b2e8c4358932900011df04baac32000a3b20975586400064e21ee6b0c80068dc8758d319000d1e90eb0a63202a7a510d614c64002c3e42eec90c800087f855d9219000b0f90abb243200021f61b75486400043f43aca90c800087c875952190001cc842b2a432001a3b21d624864000d7240ac490c80068f48758521900055c904b0a432001637e1d53d8d403562f3b6a1b1a801da9e841cb63500e953b08396c6a000237a1c52d8d400046ec38a5b1a801da9e8414b635000153b08296c6a0002b5a0452d8d400056ac08a5b1a8074ada8014b63500015b300296c6a0076a7a1071d8d403a54ec20e3b1a80008de8714763500011bb0e28ec6a0076a7a1051d8d400054ec20a3b1a8000ace82147635000159b0428ec6a01d2b6a0051d8d400056cc00a3b1a80008de8708763500011bb0e10ec6a000297a1421d8d400052ec2843b1a801da9e84087635000153b0810ec6a01d2b6a0021d8d400056cc0043b1a80008dd87994635000153b09328c6a02e2b66026518d400
  | 8 => 0x6ba6c4a80a65720d74d89503fcbdc02e9b12a006978805d3625400127f08b9ec4a80aa4f21173d89503f4bdc02e7b12a006978805cf62540f12f700b8ec4a801a5e20171d8950005b4c0443b12a028a6e86d89625404f2ed0fb8ac4a80039918b7158950006b9c06e2b12a000c7760dc56254001ae6c1b8ac4a80035c8837158950006b8906e2b12a000c77761c56254001acee438ac4a800399188715895061eb5b96e0b12a0c2e6862dc16254001ae6e3b82c4a80035c1c77058950004bcc06eca12a00095f835d942540532b906bb284a80025de05765095013cba40aeca12a00097b805d942540512790eb2284a81eec720d645095060d9dc02c8a12a02893d84dcd42540012f301bb264a80024fe11764c9501549e422ec992a000977815d9325404f2e902bb264a80025ee01764c950144aec1ee8992a07bd1c435d132540012f700ba264a801a5e201744c950144ae43ac6992a07ab1c8458d32541816b700b1a64a80a65b21d424c9503df8621a84992a00095f835d361540532b906ba6c2a81fe5ee0174d8550034bc402e9b0aa00093f845cf615405527908b9ec2a81fa5ee0173d8550034bc402e7b0aa07c97b805cb615400d2f100b96c2a809e1f61f62d85500073210ec5b0aa00087f8758b61540518d8e4b16c2a809e9d20562d855000732b1643b0aa000b7180c8761540512dd0fb92c2a8003991877258550006b5c06e4b0aa000c6f60dc96154001ad6c1b92c2a80035a8437258550006b4886e4b0aa000c6f761c96154001cc8c2392c2a80021fa1f625855014636396c4b0aa027a7481d896154001ccc43b12c2a809e1f21d625855014636392c4b0aa027a7481589615404f4ed0db0ac2a8003591cb6158550006b5b96e0b0aa000d6872dc1615417fae6e3b82c2a82fb9c1877058550004bcc06eca0aa00095f835d941540532b906bb282a80025be097650550144b6412eca0aa00097b805d9415404f2790eb2282a81dec720d64505505ed9dc02c8a0aa02793d84dcd415404f2790ea1282a80025e603764c5500049fc22ec98aa02a93c845d931540012df04bb262a80a25b209764c550004bdc02ec98aa02795d83dd131540efa3886ba262a80025ee01744c550034bc402e898aa02795c8758d31540ed63908b1a62a82f2d6e01634c55013cae43a6498aa0299748750531540efe2886a0a62a80025e60376485500073210eec90aa000c7980dd921540018f441bb242a80031e84376485500043f434ec90aa000d64219d921540012df04bb242a80025de057648550004bdc02ec90aa02a93e841d9215400127b083b242a80a657a0c7648550004aec18ec90aa000d64211d92154001cc8423b242a80030fa1076485500061ec20ec90aa000c5e831d921540018bb063b242a80031ba08764855000636c10ec90aa000c
  | 9 => 0x65d912168732108cbb224200a798019764484018becab9ec8908031719573d9121006e210ae7b2242038de83dd764484011bb07baec89080e37e1d73d912100667902e7b224200cd7105cf64484fb8bce7a86c890803175cf50d9121006b210eeab22420087e87d9564484010fd0e32ac890b3f9908465591210053cc00cab22420587e87dd564484010fb01baac8908021fa1c75591210054f41ee8b2242058bc8755164484010fd0fa82c8908161f21f50591210061f3a6cbb1a4200c3e74197634859dcc84232ec6908029e60065d8d210061fb2ae9b1a4200c3c655d36348401b4842ba6c6908122fa1375d8d210045ec26ebb1a42048bf875d3634840195e40ba6c6908032dc4174d8d2155e1f3a6a1b1a4200c3d74d436348401ac843baac6908021fa1f6558d210043f438cab1a42cde642119563484014f30032ac6908161fa1f7558d210043ec06eab1a420087e871d5634840153d09b9ac6908163721d5358d210043f43ea0b1a420587c87d41634840b0fd0bbb286908021f6177650d210064e21eeca1a42008bd849d943484011bb073b286908021fe157650d2102c3e42aeca1a4200c9c435d943484011f700bb2869081a3e2017650d210070e21ecaa1a4200a7980dd760484014f3003aec0908021fe1574d812102c3e42ae9b02420087f855cf604840b0f90ab9ec09080359085759812166732108cb3024200a7980196604840b0fd0dbaac090a221f21b7558121006b210eeab02420087e87d9560484010fd0e32ac090b331bdc8655812165e3bb88cab024200d64215d4604840d8f4c0ba8c0908b61f61f65181210061f3a6ca3024200c5e73d9460484014f301b28c0908030f9d065181210062f398ca302428ac6d7219460485958eae2328c090b279908465181210053cc00ca3024200c3f655d06048401878caba0c0908036908574181210062fb2ae63024200c5c655cc6048401b8842b98c0908023ee1d60181210063cbaac03024200a3d8690f64540532bd0fb9ac8a800317d837359150006adb06e6b22a000d1f741cd6454191a76e9b82c8a800356dcf7059150006ac39ee0b22a02987d87d93635405587ce9b26c6a80038710f64d8d5014d2e41ac9b1aa000a5d86d0f635405527d0fba2c6a80030fd837458d500069db06e8b1aa02ac3c74d9163540530f90eb22c6a8003471d36358d500069dba6e0b1aa000d3874dc1635418fab6e7b82c6a80025e6037650d500068e21ceca1aa00093f845d943540012bf06bb286a80025ee017650d500068e218eca1aa0c6d1c43dc9435418ba3887b8a86a801a5ea1f7050d506278c21ee0a1aa00597a86dc1435400b2f10db8286a80025e60b7050d50004bcc0ee0a1aa06cd3b741c143540e9ab6e638286a82d7c610c7050d50005b4c10e0a1aa000b71811c143540012bf
  | 10 => 0x50220100101f02a0080100001a0303000e0060980300300000c04002000010020110020040680f01202800001004014038320320600000d00a050018020000100000701c024010000020140601700016800805014010088020000680105400c070000010080100200000a00000000006018010070000000000401201003800000000050090000000680b00000c0200100400c050000000000480b006034000000040040c00604601803000030008058000040000080000200c031ed03baec4a18023d60775d89430064e21ae3b1286d8e1c43d436250c051dd05baec2a18023b60b75d85430064e21ae5b0a86d7e1c43d436150c0b1f70ea86c0a18034710d75981430363c302eb3028600c7975d826050c01a3886ba8c0a19b32bd9172181433a667b1ae43028600d8c435c86050cd996ec8b88c0a19d335d8d7118143006ca21ae230286008fb875806050cd957708b00c0a19d2b6e0d60181430145ec26ebb1a8479c3d74d4363508091db05baec2a10032710d73d85420043fc2ae3b02840587c855c760508011f70eb00c0a100a3760f75d91323ce2eb9ea1b226438a9e84dcd644c9add1887b92c8990032710f71591326af0e21ea0b2264d4b8e84dcd424c8071db05baec2990032710d74d85320043fc2ae3b02640587c855c7604c8011f70eb00c0990062f61375d8d413ae1eba6a1b1a82048f581dd7625040193886b9ec4a08062fa1b744c9410146f43ec699282049ac875093250471d18c6a1264a08021fe1572d814102c3e42ae5b0282008fb8758060504031bb07baec8989d7175cf50d91311954f426e6b226200c9c43dc9644c5a7d2887b8ac898b4b8710f505913101c7ac0eebb126200c9c435d3624c40517d0fb22849880637a1b735093101ce643a849926235e8c64509324c5a372d09b9a82988132d1d94250531195ca41a84a0a6203cd4764c9414c45f729089928298803e150932505310043fc2ae5b02620587c855cb604c4011f70eb00c0988035908570d95210052f41ee9b2a4200a5d83dd3654840187ae83a6ca908028fa1373d95210051ec26e7b2a420087e8710f65484010fb0e21eca90a269ba0843d952100536c1087b2a4288a768110f65484014eb0221eca908029ea0043d95210053cc0087b2a4200c7b709c3654840147d08386ca908028f61070d95210052f418e1b2a4200a5d831c365485134dd04386ca90a229b60870d95214453b408e1b2a4289a75811c365484010fd0e206ca908021f61c40d95210052f41881b2a4200a5d8310365485134dd04206ca908029b60840d95214453b40881b2a4200a758110365484010fd0e186ca908021f61c30d95210051f42061b2a4200a3d840c365485134dd04186ca908029b60830d95214453b40861b2a4200a75810c365484018bce7b2ec890803179cc
  | 11 => 0x5026985917c8c1200a6a8470d39d42630002000790002c280028b9780078002de2dc2018da8001651059ac0000f287e9dd2e29d681092b80027a0cc122906a048000000510001cd8000000b927780007fa970d8a43ad7a200e780000000600018093006e0fa9e42320000000000000308000002b80000002160001600000e000005c244924800024a5783c8d680028900000000004da149fd8de9c603581b1192af0000ab8618000001ea85e1c984880d2eb0000001f71018d581a000259869a41a18a9aa6c000000000053a7e0f51881610138000fda290000928000021940000002ac0c99e92b300027c1bf17327d80009c8a58001dd8000000f58000000000000001ff1de8aa90a29a084000203826967a7810c16d0751ea14fa6b0690630958d40001270dba2b95d048205a65a660001ce29ba1a0c9122156a442b49728e39b7a4d0cb24f00002f8a6982250274126a2525b8d497a28d0002731549a3a8c04390aa4ca7e8bc00da012c98b62e00002a28002cc89f1ec11980e8c20a00771801431d99ba982a12803817ad6923899271a3a1708460a9898806940a6a2bc145a2391c24eaaa17d02c9f19351f204c0e417e809a4727b8001938c78261141a00529f983b00000003899d121a278b71a507b8399c09be80921b80017909d07f00000021408c0001bd8611e20002d625312b10d0c5a6e2ee0e98ec00019207996e8001348fe8a88000000d900900c000008048060000180a003054008010030300c4000200300000200200002c1e83500008c018000440a0008120040001c80800200801802002000058010000040000400000007008002004030400000100100001c000000130060000f00100e00401801002060068000000242880e000000020000000000281f00200c0700902202c0006602002821800002010018060000180380101a00c090010000200000302806000004002000010030100080180e0000140180e0120040000601606c04010024038108040001b0030300201d00b80e0160500b00400200c02800078000048070460100000a00e0680000500e008030060060040e801002018180230100080503b00001c1b0000000000000106400c0c0050000340200000401c028000500480000a0080440500000a000028000000b00000801409c038030000040500700001c028050100100080200e0400000e0020000180000c0140780001201c000030020000100102208c020070040140d8100080080b01400200006008008000150130240300c80600200c0500a006000000000480040300b0000001d0020660082100000002409803002028078000000200000c0000080b02006a04c00000000000010060080080080200200c0000d0000040602800007c00003000084008020080200080000a03c0d00400002803000000000
  | 12 => 0x51f080000004106724896219fa2300000020324d9909038002571508001f8127a8280015807c0002c721f09a8fb0118fc18693cad00361f000000004d2709419b409106c0232368001ba0000000310002c90000000000bd019a8a0000a08001ef0002762e404f00000023b1fb8972d3ac30802a4989a420140f717c00020d0e200007e1840b9a378eb01221c85d94c82820e9550c39ed258aa82acabfa261f2a9593f23d20895788a2280b11a784289a14211d891864acc0d18001d7a559ff80829793590c9630002330000000001d180000003f21aa340000000001a40c520c09b2e6ac48e60372e09e58002939bb8519b51981122e899a12025f2468f008d97b27713e8002388b281aaca8a90dc25a91a80017e2e50b59589a92ec26691188f11b06b0000040000001609102d5abea2e1c48fb8000d20000002508002371e680000004218d9a698b17697f23a90e05fa1f9a9a850000b80921d60ba0b48870468419dc92c05b2c5a09a2fa4b8ee9bb0322799500ef89e0d799d8fa2e11da1ee267015a9d11fad0a29a0d8cd040a868d80bf8001152122d91d9147a96929894aa115b25113091089f8dd0f40df19ba2683815e194876139aa62bb215a258782a1a4990028028329f2581181fa9328ac23b981a2d1ad2d4aa01ef96a20914b0939cfa2e83402b0be02084f96f12090097d961908aab1138d000f11ba46037a61a8f1e00b3183ada0c02319489e11562b5a19a7683ba5a05c99108f9799de1e3abc80015f2bf27919a92f1ac9830e319e0638cbaedab9855ac829298ca8124827f05f0f12e481c00a9e708b00010f2e60000c880021682d0ba99c17580000000487dad70cd94f0000878072b0800090a1507300000002f00000015200020f2a3a2a1079ab0b18a60748d08661d08000890000f699c9a12ea9dc134218232a6f29e11e099ab904322725d80001891480000002ea51a4aac180b0ef18925494c18121b2c20b78000002478b515a03d0e281f85a9b71012daace26214297f84920b2d41451cb80c2e3a6eabd8330de23e0271b114a16815b9fd206912ac517b8000318451eda1c1c30ca81d00011e9df8598d529f9b69739c29ce800000010022a3826d2390758001c90000000001f50000e891c9a62d89330339720002b707a86008d2362922ae93f8000000498001e2a888000200000bf00025e8000000002a59d02100ee0e483292d0001c6aaa8a310b1c70a4889a750448000549c106d13d8540969c80000001032a887784b2cd17713a8cc82992f8f91f393205ba0b97422d8561028c72e32ed1ae0acadd1480002bb87b00000f8962b4222ad2159040097a35076a4102c1aa07d15a9eb04a01cac78b228e20a1b4a4099786ea7394e29c2e5adc88486a8aea56a950278e08e91cb05219f03c2c10fe0ea0e585d0000f48868
  | 13 => 0xc680000022c8029ada8d8ffa0800010984e80017018e9a58bc8001a70ad09c11d0d118e03517a8001668001a302dab899713c0af825080a72a458000be8001c18000000df80014a80021d0390002cb0f98ca27f80e1f88002ab800073a9b0ab0788889fc2c427584e1e181486788c812952acf9719d12528a79e61930f188aa690c29f40980d727a80020e0aa05e91a1049c01378001902ad8c300000000010f8821c208e21d9d59f78000000001eba4f800278a6894025b000000144a3fabd2e819610dadb02108323000000000028826d8579b2195aa792c80006c8000b69e50f200007112d80022c26ca9ea849eea0a89d9879f49a898d0f882b9fe028a349c88058478032988089d210528fa5400000000023c1e09a2ae98d62680000000000588af01718a1638000002248000002b7a6106b80007186500022083a0c49a08002898001c5a6398f00000023984b8d99a82c681f0b40002871472170190fd2912b11b91ab8000a800b8000000e700020c8002df977a021082358002eea3d80008e8002d19888001db0bb8001b312e2b38811af9460000000000002642061d289302a00019922a80000025f9c51390002eb9d3202ab004a9be0002c09c795400008ba720b092e80000016f8000530a716481e8608240001210700002cb9fc8002d5021a490f62c02961b980c96e082885a91a932a92649f127c9629b58b383021198f99e8c61260f0aaf9f60f32ba8292992550ed9f31169bd13b062a5c2b60a1a139e794d1bc07a2ea22b1fa03e001ae78bdac89a216c1c381801128a9230c42ec8000c80002b198627d0fc9a1822155ac616a95d9e81cc9f91aa93e2d98951ec8001d52c380024027b1da81da0523c8f7a308a2a590f3a8216c93a00028b0942d2a4a065aa095c8d2a980c091893d1178e6936a33949a700000000642cda9da5390e99993604c915a650bb1171fb1092878881711f6836959ade8f80259b004581e1761672040cf8ea969a81a429d49929691b0a4c07c86f1288ad8b01b615196b1d82b21b29e4a22280a600688001851492b50ff11f03eaa522881303480a14b9571969db8861d8a998728150ce1469cd1b880013193800000027487080013b9d72be00003a91626f94d8e115f9918cf24516410400023e8002710a115310ba9000021306f800217a94a85acf1b384420fab6a6b8b883d968a942842dd86da1118c14e8a3ace8eb9e8a5e03fa5d2a98ed125283a1e9849bf8000000000000000001c414412401ba9ca5caa41af0000002078e801688500006690200000009baae1e9a1e1feaa6a521d38002e71b824e062260929174ab29ca82aadb8da19b221a240818901371511ca28600087418b95c1060c1a4b2210dc8002a32a2111128210a2f243185a8c9388ae0000d300005a1751339bc98700009e82e12a19
  | 14 => 0x1f596b8e1a070ec8509130ce8571070e50a51a49410721258a40552d8068000083800000153aa70000160001cf0001cc0000000001ae9df12aae91312e2000000000000056ae180016d9e328e8000000a2143aba0001b182396598a8db0052df15e80000000000016626786a2ad29099880123f2ca262a560580002d12192d32311788dd800
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1464925c4715964000619609711c565900014999010f7358a400052664043dcd61900012659808565486400061921c21595219000166190085654864035626200635d12150001459901d763485400059165421d8d21500016c190087634854035686a0063dd15050001464915c87259630006195c9811c9658c001464925c4715963000619609711c5658c0014999010f7458a300052664043dd1618c0012659808565486300061921c21595218c00166190085654863035466a5f83509408c0d519a97e0d41502300050e64075d91214c001625950876448530005a864021d91214c0d589880191734853035686a0064dcd504c0d529a96e113290130354a6a5b844c6404c00d5189750d50501300358625943541404c053c187650d50501304ee261db8250d404c12589876e0543501301c6261d9844c9404c071c88765093250130196261d9844c5404c065c9076505315013000619609711c565880016199010d6550e2000526640439d943480d588d8210c7650d2000526640431d943480018646121d21541200068610c8650d504800134b936137254120004cae5183dc95048051328985d1425412057dc224d74509504805132994e0d4254120144d264f844c9504800d26896611325412057ec210d844c95048051348985cd3254120575c2251734c9504805186886dc97154120004ca6508748550480013499321d215412000658e0487485504800134993e112154120004ca653834855048051360985c521541200065821d714855048051660965c521541200358a25942541404815fd087350950501200359225932541304815dd08744c9504c120006195c9811c965840016199010d6550e100058a650825952084001649932096548210005986448259520840016499390965482100058a6523259520840014999010e7650d1035625604431d943440014999010c7650d1000619188874855044001a1843219435411002c1ea6387589504400186887e0962541100061c21f815895044001353936137154110004cce5183dc5504404f470965cb715411013ccc261745055044149710935d1415411013ccc65383505504404f35193e1131541100349c259844c55044149b1043611315411013cd4261734c55044147710945cd3154110004cc6508748550440013519321d215411000658e0887485504400135193e112154110004cc65383485504404f360985c921541100065821d72485504404f660965c921541100358c259415414044149d1073505505011003594259315413044147d10744c5504c1100054c650815d6204400155193205758811000558648815d620440015519390575881100054c652315d6204400136098485504811013f181d9215412044111c6076e152148110004f064f8448520440013a194e0d2148110
  | 1 => 0x100551654215cf6448401c446508573d912100570640215cf64484011669808775591210055864021dd56448401a602160065591210040f66274197634840183a7460065d8d21006980858019763484014399019574d8d2100549654215d36348401c246508574d8d2100568640215d36348401166980877558d210055864021dd56348401a60216006558d210052664043dd943484014999010d7650d2135626200435d943484016199010f6550d2100459660215d66048401561900857598121006980858019660484011669808775581210055864021dd5604840116598085751812100558640215d4604840183a746006518121006169cd8019460484018697260065181210061c5c580194604840143990195741812100549654215d06048401c2465085741812100568640215d0604840145990195731812100551654215cc6048401c4465085731812100570640215cc60484016199010f64d8d5000546640439d943540015199010c7650d5035646200431d943540d992b746087050d503a652dcd821c14354001b08436087050d503664cdd1811c143540e9953736047050d50006c410d811c143540012669818b715895000519a5b721c562540012659818871589500059864021d8b61540012679858b21d855000519e5d62c87615400126698187725855000499660611c9615400146697887625855000619a1e21d896154001866861cb615855000499a6021dd9215400166190087764855000519658219d9215400156190086764855000459660211d9215400146596084764855000558640211d9215400126598084764855000598640211d921541b3a6180084764855000607611831d921540018658260476485500051c643211d921540014669188476485500051a642211d9215400106d9808476485500051a640211d921540010759808476485500051c640211d9215400146798084764855000619a60211d9215400146598084764855000619660211d9215400106598084764855000709a50211d92154001c2594084764855000709a10211d92154001c2584084764855000711a4c211d92154001c4593084764855000711a0c211d92154001c4583084764855000718a40211d9215400146590084764855000718640211d921540014619008476485500060ea11801d9215400183984600764855000616a0d801d921540018598360076485500061a609801d9215400187181600764855000718085801d92154001c602188076485500051924b101d92154001c6021840764855000619204765892154001864821d9614855013c9926162585215404f4649758961485501461921d625852154001c60211da70485500041ea60765c1215400186b821d970485500061ce04765c12154001464915c87259640006195c9811c96590
  | 2 => 0xa040001b40000001f400033a08d4e6700000680014a4c005243b65f432548000039051380055003a0d66626a000000002f87c00249a964384725018007e3a59cfd1d02de277139f9601946885eacf4532d426c41a90ea963281dcee230001982839b5cd0054491d6aaf6b000ae0038205a0165da31f600023a882852d20924432db55ccb67cb790c581f85dd69d56800c6370e0d4e278161b9ec4f09170fec11106c6c5f641142014772f05adf0703c90252e91078f86ea89e0900c2f498a376334c2ae1db70102a012c43cc51038d92c7390c000007015800002f38400b47227c00db6a025362b0e89822c44f07da2764e29508b86914594001eae4a6985d001fcd823395105455a98f8f70304c84da4d1882a595530116953d0cd2e0006800f2005428062d361bbd846f0000000000000002f434a451e005fbcc00b30000000c63d801322f79000c800123b55800000b800005b92c344a03002040701452030084016000100816000981828120401012040291c0023018408a000180806030210c06060e050020007000000e170002c070100000001580442000002800040283c140002010020401810080000044040c0181c320e02000014999010d71d894300526640435cb6150c015199010d759814335706180435d66050c015199010d751814300562640435c86050c015919010d711814300526640435cf61508014999010f715913200526640435d3614c8014999010d73d89410052664043dc9644c4014999010d74d8931194e1261424c9414c471c8476509325053100459a60215c365484015619008570d95210041766273197644840185a7360065d9121006980858019764484014599019573d912
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2191000c0016a0139883a0959d000e85951c14829982000003000008070004001a86190500140a010c9c800000121f8a800e17971f1d8880108f878b869300000d01800980161e00049b80211e8011929a000d891b008f18100b0184022c604240000a0e04981000058000182803548314cc8086bacc0a1802261a9085801976448401222d48ca10ae7b224200b106806508573d9121006880cac8042b9ec890802261a9085801956448401130d4842c00cbb1a42009096a46508574d8d210058434032842ba6c69080342065640215d36348401130d4842c00cab1a426a8262a19010d7650d210044c35210b0032cc090802425a9194215d06048401a1032b2010ae830242009116a4650857318121006880cac8042b98c0909aa11ba8640439d94354001130d4320108ec90aa00091868398084764855000604d48cc0423b242a8003025a4660211d9215400182351b30108ec90aa000c1168d9808476485500060c340cc0423b242a800302598a50211d92154001812cc328108ec90aa000c0966284084764855000604b30c20423b242a800304598a4c211d92154001822cc326108ec90aa000d0165193084764855000608b31418423b242a80030459860c211d92154001c02c2306108ec90aa000c186629008476485500060c330c80423b242a800342294640211d92154001a10ca320108ec90aa000d10a4d90084764855000688326c80423b242a8002463a8640211d92154001a1142320108ec90aa000d0861190084764855000688506c80423b242a800344183640211d92154001230d4842c00ec90aa000a186a02160076485500070430810b003b242a800384183085801d92154001430d4043100ec90aa000a186a02184076485500048c352108ed38242a8002861a8084769c12154001032d490e10aca90c8000c1821d9008565486400040cb5243842b2a43180030608764021595218c0d5844c1320218eca1a406ac826484321943541200050c54dc090e90aa0900030609621d7148550480d5848c0b20218eca1a20008196a46221d2154110356423222190ca1aa088002862a6e088748550440018304b10eb9242a822000c181d8984855048110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xc0a0002068e04002004441ba1959008573d9121004421ba1959008574d8d21006005a468d980847648550006021a4681980847648550006041a36819808476485500070018460d900847648550006021a9610216007648550006041a960c216007648550
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
  | 11 => 0x124e
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124d
  | 15 => 0x98a
  | 16 => 0x98c
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128e
  | 20 => 0x128a
  | 21 => 0x128c
  | 22 => 0x128d
  | 23 => 0x9ca
  | 24 => 0x9cb
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12ca
  | 28 => 0x12cb
  | 29 => 0x12cd
  | 30 => 0x12ce
  | 31 => 0xa0a
  | 32 => 0xa0b
  | 33 => 0xa0c
  | 34 => 0xa0e
  | 35 => 0x130a
  | 36 => 0x130b
  | 37 => 0x130c
  | 38 => 0x130e
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
  | 62 => 0x94996
  | 63 => 0x128956
  | 64 => 0x95296
  | 65 => 0x8a
  | 66 => 0xa4953
  | 67 => 0xa4954
  | 68 => 0xa4955
  | 69 => 0xb0956
  | 70 => 0xb4956
  | 71 => 0xb4955
  | 72 => 0xb8956
  | 73 => 0xb8954
  | 74 => 0x150a
  | 75 => 0x168a
  | 76 => 0x180a
  | 77 => 0x99256
  | 78 => 0x124996
  | 79 => 0x4b
  | 80 => 0xa5253
  | 81 => 0xa5254
  | 82 => 0xa5255
  | 83 => 0x4e
  | 84 => 0xa4992
  | 85 => 0xa4994
  | 86 => 0xa4995
  | 87 => 0xb0996
  | 88 => 0x138b
  | 89 => 0xcc996
  | 90 => 0xcc995
  | 91 => 0xd0996
  | 92 => 0xd0994
  | 93 => 0x168b
  | 94 => 0x180b
  | 95 => 0xa5292
  | 96 => 0xa5294
  | 97 => 0xa5295
  | 98 => 0x8e
  | 99 => 0xa09d6
  | 100 => 0x10c
  | 101 => 0xb49d6
  | 102 => 0x138c
  | 103 => 0xcc9d6
  | 104 => 0x150c
  | 105 => 0xe89d6
  | 106 => 0x589
  | 107 => 0x180c
  | 108 => 0x1789
  | 109 => 0xcd
  | 110 => 0xb8a16
  | 111 => 0x138d
  | 112 => 0xd0a16
  | 113 => 0x150d
  | 114 => 0xe8a16
  | 115 => 0x168d
  | 116 => 0x18c9
  | 117 => 0x198a
  | 118 => 0xb4a55
  | 119 => 0xb8a54
  | 120 => 0x138e
  | 121 => 0x198b
  | 122 => 0xcca55
  | 123 => 0xd0a54
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
  | 136 => 0x164a
  | 137 => 0x14cb
  | 138 => 0x44a
  | 139 => 0xb8b56
  | 140 => 0xccb56
  | 141 => 0xb4cd6
  | 142 => 0x154c
  | 143 => 0x140c
  | 144 => 0x18ca
  | 145 => 0x178a
  | 146 => 0x184c
  | 147 => 0x148c
  | 148 => 0xd0b96
  | 149 => 0xb8d16
  | 150 => 0x154d
  | 151 => 0x140d
  | 152 => 0x16cd
  | 153 => 0x144d
  | 154 => 0xd0cd6
  | 155 => 0x18cb
  | 156 => 0x178b
  | 157 => 0x188c
  | 158 => 0x160c
  | 159 => 0x170d
  | 160 => 0x15cd
  | 161 => 0xb09895e
  | 162 => 0xb09499e
  | 163 => 0xb4a495d
  | 164 => 0xb8a495c
  | 165 => 0x128a52
  | 166 => 0x94a53
  | 167 => 0x94a54
  | 168 => 0x94a55
  | 169 => 0x94b55
  | 170 => 0x94b94
  | 171 => 0x198d
  | 172 => 0x98a52
  | 173 => 0x124a53
  | 174 => 0xcca499d
  | 175 => 0xd0a499c
  | 176 => 0x98a54
  | 177 => 0x98a55
  | 178 => 0x98cd5
  | 179 => 0x98d14
  | 180 => 0xe8a09de
  | 181 => 0x10a54
  | 182 => 0xa5814
  | 183 => 0x12ca16
  | 184 => 0xca55
  | 185 => 0x1309d6
  | 186 => 0xb1396
  | 187 => 0xb1516
  | 188 => 0xb5696
  | 189 => 0xb9816
  | 190 => 0x198a52
  | 191 => 0x139256
  | 192 => 0xcd696
  | 193 => 0xd1816
  | 194 => 0x198a53
  | 195 => 0x151296
  | 196 => 0x180a54
  | 197 => 0x184a54
  | 198 => 0x188a54
  | 199 => 0x1692d6
  | 200 => 0x181316
  | 201 => 0x44092
  | 202 => 0x2cb
  | 203 => 0x2d253
  | 204 => 0x45292
  | 205 => 0x44cd2
  | 206 => 0x455d2
  | 207 => 0x44d12
  | 208 => 0x45612
  | 209 => 0x58a
  | 210 => 0x198b94
  | 211 => 0x184b94
  | 212 => 0x58b
  | 213 => 0x198d14
  | 214 => 0x188d14
  | 215 => 0x199854
  | 216 => 0x199894
  | 217 => 0x20b16
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1426
  | 6 => 3726
  | 5 => 1502
  | 4 => 255
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
  | 6 => packedAt gbK6 (194994+((h/1242+packedAt gbK6 (178848+(h % 1242)*13) 13) % 4472)*13) 13
  | 5 => packedAt gbK5 (94118+((h/500+packedAt gbK5 (88618+(h % 500)*11) 11) % 1803)*12) 12
  | 4 => packedAt gbK4 (18615+((h/85+packedAt gbK4 (17850+(h % 85)*9) 9) % 307)*9) 9
  | 3 => packedAt gbK3 (5662+((h/22+packedAt gbK3 (5508+(h % 22)*7) 7) % 90)*8) 8
  | 2 => packedAt gbK2 (744+((h/2+packedAt gbK2 (736+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc71e381c00c6380c7ffc7ffe0ff030e400f3cf
  | 1 => 0x7e3c01fff07c00f8e0f8e0ff0f0c307334d33
  | 2 => 0xf803ffe00ff8000ff00ff00fff030c38c38e3c
  | 3 => 0xfffc00000ffffff0000ffff0000c0fc0fc0fc0
  | 4 => 0xffffffffff00000000ff000fff000
  | 5 => 0xfffffffff000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x82060904800008001280128208801064001045
  | 1 => 0x1204008650640a484248424a0604101314512
  | 2 => 0x480090c00ac801492049204946010408c28a28
  | 3 => 0x5548024123529260000e496062240f80540f80
  | 4 => 0x4824ca5258e49600001844be000abe000
  | 5 => 0xa69327138000060001800180088ebaf6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffefefcffeaeae8fffefefcffeaeae8fffefefcffeaeae8fffefefcffeaeae8fffefefcffeaeae8fffefefcffeaeae8fffefefcffeaeae8fffefefcffeaeae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_31645
namespace PEqualNP.Outside.L_meta_31645
open PEqualNP.Outside.L_meta_31645.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_4_224 : Interval gbAtlas 4 224 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 255 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224)))
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
theorem bgb_5_1472 : Interval gbAtlas 5 1472 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1502 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))))))
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
theorem bgb_6_3712 : Interval gbAtlas 6 3712 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3726 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)))))) (concat (concat (concat (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496))) (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))) (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456))) (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584)) (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 5 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffffffffffffffffeaeaeafffefefeffeeeeeefffefefcffeaeae8ffffffffffffffffffffffffffeaeaeafffefefeffeeeeeefffefefcffeaeae8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_31645.Model.Repr at out
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

def mono : List Gate := [⟨.or,[7,6]⟩,⟨.or,[7,4]⟩,⟨.or,[0,2]⟩,⟨.or,[5,8]⟩,⟨.or,[0,8]⟩,⟨.or,[5,4]⟩,⟨.and,[7,13]⟩,⟨.and,[11,10]⟩,⟨.and,[1,9]⟩,⟨.and,[3,12]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_31645

open PEqualNP.Outside.L_meta_31645 in
theorem PEqualNP.Outside.L_meta_31645 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
