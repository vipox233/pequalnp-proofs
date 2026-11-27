import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_29442.Model
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


end PEqualNP.Outside.L_meta_29442.Model

namespace PEqualNP.Outside.L_meta_29442
open PEqualNP.Outside.L_meta_29442.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 6, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_29442

namespace PEqualNP.Outside.L_meta_29442
open PEqualNP.Outside.L_meta_29442.Model
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
end PEqualNP.Outside.L_meta_29442
namespace PEqualNP.Outside.L_meta_29442
open PEqualNP.Outside.L_meta_29442.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x38008802c00b804a009803c000000004c8018200000048aa63e1120042a0500000158000000000c6d1820000e800000805520c000000000000353871ca80000024000006800040500000060000003c022000000000005800100000000218000000c000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10f610fd10fc10f410
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xcd0c000121081800d800bc005000fc0000b8f0d0ec60900168387068080124980000000049300000a40000d4c910b1400000007c2c0000a80000000000000001480000300000000150016054a05844289400800000001c8d0040002515583c0000000c0014004d54e4dc00115c0000f4010400000000353c0000e000054c000021349c00880000c1445c013800f80000012c000000007800751cb40000e800c400000128ac000000656484000001186c0002060200000a180200000004040402001600000002000400000004000b9d4310edca421db54843bb28887755110ef4a021de54043bb28c85755190abea6a15714d42af298855d5310aeca2215d54442bd28085795010aeca3195d546329faa2653c544ca7ca8194f55032bb2886575510caf4a0195e54032bd286837950d06f4a198de54331baa94437650886f6a090de14121f3a9243f350486e8a090fc14121b8282437651086eca3a05d54740af29c815d53902eea2a05d14540bb28e617551cc27ca9184f55230bba8a6174514c2eca3905d54720f290e417751482e8a29079485209f2a0413d54082bca6105754c20bb288417551082eea5085d54a10bb284213e540427aa8085794c10aea98216e52042daa4086d95010daaa021d653043aaa6085dd4810f3290217552043caa4085954810bb28021f250043e480087c50010f918021f130043e640087c08010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2e700000a86b0290c82801a00061638850a0004b00009848907820015420010f0d43548439c1815190a706054632cc99050487316414121d498c50487516314121b818121c83155454c109959652043265454810c955152043465354810d154d52043606054810b458e40043615290010d854940042b1648c010d854a3004361524c010d854b20042716508010ac59020042d16308010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x80040000d00001845916314121a42e8302a408541731815204320b1aa52002188591528c010
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
  | 3 => packedAt s1K3 (998+((h/8+packedAt s1K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xc38f1e3fc78fffe31e3838e1f8e1fffe61327f
  | 2 => 0xfc0fe03ff80ff8fc1fc03f01ff01f87f863c73
  | 3 => 0xfffc3fff0ff1fe0003ffe3ffe3f8007cf9c
  | 4 => 0xfff00003ffff001fffffc0003fffc001f80fe0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x70118850541450030a0a902850284e28611225
  | 2 => 0x8b2254a8a32aa11c14452914a9149155862c52
  | 3 => 0x84404090102002420000a440a442104024498
  | 4 => 0x11004932120032494691800034990218a80b60
  | 5 => 0x22089000244cc492992634990000046155b000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_29442
namespace PEqualNP.Outside.L_meta_29442
open PEqualNP.Outside.L_meta_29442.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xb800000013523c1003400000060111f2801080006009e129d5003a38200104122300640062234a92006d426009461c5601016140028b0e0820010c00011000491c0ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10f610fd10fc10f410
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x5737520447021a0f3546124e4b00422040213e411b253930321023580700243a49222f134d533b05310111380b2c5a173f430036191f2a54000018144c1e00002e00440050082d4833454a4f260d000934003c15162b290000000056002700510a0628031d0e00550c3d59001c000e182025e201820818085002cb0a060822f08002130a000003d9d4310edca421db54843bb28887755110ef4a021de54043bb28c85755190abea6a15714d42af298855d5310aeca2215d54442bd28085795010aeca3195d546329faa2653c544ca7ca8194f55032bb2886575510caf4a0195e54032bd286837950d06f4a198de54331baa94437650886f6a090de14121f3a9243f350486e8a090fc14121b8282437651086eca3a05d54740af29c815d53902eea2a05d14540bb28e617551cc27ca9184f55230bba8a6174514c2eca3905d54720f290e417751482e8a29079485209f2a0413d54082bca6105754c20bb288417551082eea5085d54a10bb284213e540427aa8085794c10aea98216e52042daa4086d95010daaa021d653043aaa6085dd4810f3290217552043caa4085954810bb28021f250043e480087c50010f918021f130043e640087c08010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x980020a8000e70ab0091e4a21305020180001ae4160280086803000020410060cb0f0d43548439c1815190a706054632cc99050487316414121d498c50487516314121b818121c83155454c109959652043265454810c955152043465354810d154d52043606054810b458e40043615290010d854940042b1648c010d854a3004361524c010d854b20042716508010ac59020042d16308010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x68004201845916314121a42e8302a408541731815204320b1aa52002188591528c010
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
  | 4 => packedAt s2K4 (2667+((h/30+packedAt s2K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s2K3 (998+((h/8+packedAt s2K3 (950+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s2K2 (248+((h/1+packedAt s2K2 (245+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc38f1e3fc78fffe31e3838e1f8e1fffe61327f
  | 1 => 0xfc0fe03ff80ff8fc1fc03f01ff01f87f863c73
  | 3 => 0xfffc3fff0ff1fe0003ffe3ffe3f8007cf9c
  | 4 => 0xfff00003ffff001fffffc0003fffc001f80fe0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x70118850541450030a0a902850284e28611225
  | 1 => 0x8b2254a8a32aa11c14452914a9149155862c52
  | 3 => 0x84404090102002420000a440a442104024498
  | 4 => 0x11004932120032494691800034990218a80b60
  | 5 => 0x22089000244cc492992634990000046155b000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_29442
namespace PEqualNP.Outside.L_meta_29442
open PEqualNP.Outside.L_meta_29442.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x200084600df43be43bc43dc439c43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xc180854100d1e5390f1ca421e354843cb28887955110f34a021e654043
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x283055254443c25495010f115154043
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 5
  | 3 => 7
  | 2 => 3
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (84+((h/1+packedAt s3K4 (80+(h % 1)*4) 4) % 9)*4) 4
  | 3 => packedAt s3K3 (197+((h/2+packedAt s3K3 (189+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s3K2 (117+((h/1+packedAt s3K2 (114+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf8f0fff0fffe3f0f1e380e3fe3fe0ffc30f3cf
  | 1 => 0xff0fff0fffc7f01fc00fc7fc7ff07cc33cf3
  | 2 => 0xfff0fff0fff8ffe0000ff8ff8fff8303cf3c
  | 4 => 0xff0000ffff0000fffffff000fff00003fc0fc0
  | 5 => 0xffffff00000000ffffffffff00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1182212442440050a09220920920528305145
  | 1 => 0x5222842428480850144244424424a050c12492
  | 2 => 0xa4444848829001aa2004889089094a03028a28
  | 4 => 0x30066682221c92334690e000f2406319540fc0
  | 5 => 0xc088880ccce124cc99270f2400018c62abf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_29442
namespace PEqualNP.Outside.L_meta_29442
open PEqualNP.Outside.L_meta_29442.Model
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
end PEqualNP.Outside.L_meta_29442
namespace PEqualNP.Outside.L_meta_29442
open PEqualNP.Outside.L_meta_29442.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x36785031e9cc23004008e0058ba9267d30d34001064a009280010a2a4800e1522010800a21580122d1004074c8c0e04000609d00c04d140080ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x30029004e0d440008134a49594c413f000032253c141a51453b372f4b1721312d362a4607500056334315550b420a000023570e1b24002b35391d002019524d1034001c380440474802301126061e532700540f121f183a5a3d01004f0516282c00002e2209583e000c000000000002a220c18c183c4852a08203462c0890a00284180c39b013e5390e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110f6aa221ee940439ea8087b95010e72a021d794e42aea9c859c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a655e53906baa720e710f31b7296636d52cc67ca918cf552319faa2633c544c7388698cf950219eaa0435e53086baa610f948421bd2804379500867ca7a04f55240afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f950409faa6613c54cc27ca9184f55230ce21c61b9408c27ea8984f15130dca02613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a4413d54882eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9084f55210b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x980000600b80c0000068000000002c00028002401e000712000000a0010000019600020202a00000000000000000c00000000e8805100008000000000020003255254443ca9495010f295254043cc9455010f315154043a658043ccb144354732a6580434ca996010f31c310d52cc6996010d31d8485500870e6214d40c358853503166114d40c558453503196014d40a6580438c29863502308e195404c21d6510c30c310d520c31443544308718d548821c6355210
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc800004101445c04354732a12e021aa598e05625845350304b12c029a81845856014d40
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
  | 3 => packedAt s5K3 (1006+((h/8+packedAt s5K3 (950+(h % 8)*7) 7) % 81)*6) 6
  | 2 => packedAt s5K2 (249+((h/1+packedAt s5K2 (245+(h % 1)*4) 4) % 12)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 1 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 2 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 3 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 4 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 1 => 0x52228891414810a0521244248449414612512
  | 2 => 0xaa444512412900354802489092092941828a28
  | 3 => 0x230064a01101924651486000e48c0c44a40f80
  | 4 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_29442
namespace PEqualNP.Outside.L_meta_29442
open PEqualNP.Outside.L_meta_29442.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001027fd5007fe54007f55007fc54027fd4c01fe53007f54c09fc5301ffd0c01fe43007f50c07fc43027fd4805fe52007f54805fc5201ffd0805fe42007f50805fc42007fcc805fe32007f4c805fc32027fd4403fe51007f54403fc5101ffd0403fe41007f50403fc41007fcc403fe31007f4c403fc31017fc8403fe21007f48403fc21027fd4001fe50007f54009fc5001ffd0001fe40007f50007fc40007fcc001fe30007f4c001fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24000ff5012002ff88090003ff304800bff1824000ff4c12002ff8609000bff2048005fd9024005ff8812002fdc4090017fc204800bf61024002fe0812006ffe2090017fc104800bffb2c2005bfd961002ffccb08012fe658400bfeb2c2000bf5961002ff8cb08016fc658400bffb242005bfd921002ffcc90800efe648400bfeb242000bf5921002ff8c908016fc6484019ffaa4200bff95210007faa90802ffc548400bffb1c2005bfd8e1002ffcc708026fe638400bfeb1c2000bf58e1002ff8c708016fc6384019ffa9c2000ff94e10007faa708033fc5384017ffa1c2000ff90e10007fa870802ffc438400bffb142005bfd8a1002ffcc50800afe628400bfeb142000bf58a1002ff8c508016fc6284019ffa94200aff94a10007faa50802bfc5284017ffa14200aff90a10007fa850802bfc4284001ff994200aff8ca10007fa650802bfc32840037eb0c2001ffd461000ffca308007fd5184003fe28c2001ffd061000ffc8308007fd4184003fe20c2001ffcc61000ffc6308007fd3184003fe18c2001ffc8610057ee4308007fe2184003fe90c2001ff0861000fe84308016fe608400bffa842005ff9421002ffaa108017fc508400bffa042005ff9021002ffa8108017fc408400bff9842005ff8c21002ffa6108017fc308400bff9042005ff8821002ff44108017fd2084001fc9042005ff0821002ffe2108017f71084003fd8842005ff0421002ff02108003ff65440017fb2a2008ff99510025fcca88003fd65440017eb2a2008ff19510025f8ca88003ff64440017fb222007ff9911001dfcc888003fd64440017eb222007ff1911001df8c888023ff544400fff2a22000ff5511003ff8a888003ff63440017fb1a2000ff98d1004dfcc688003fd63440017eb1a2000ff18d1004df8c688023ff5344001ff29a2000ff54d10047f8a68801fff4344001ff21a2000ff50d1003ff88688003ff62440017fb122000fbd8910005dec48801bfe62440057f3122000ff58910005fac48801bfc62440057e3122000fb18910015d8c488023ff524400dff2922000ff54910037f8a48801fff424400dff2122000ff50910037f88488003ff324400dff1922000ff4c910037f86488016ff6144003ffa8a2001ff9451000ffaa288007fc5144003ffa0a2001ff9051000ffa8288007fc4144003ff98a2001ff8c51000fec6288007fd3144001fa98a2001ff0c51000ffe4288007fe2144003fb10a2001ff48510007ea4288007fc21440037fb022008ffd411002ffca088003fd504400bfe2822007ffd011002ffc8088003fd404400bfe2022000ffcc11002ffc6088003fd304400bfe1822006ffc811002ffc4088003fa2044001fe9022000fe4811002ff84088007ff1044003fd8822005ff8411002fec2088017fc104400bfa0822001fe04110
  | 1 => 0x2fd610c00bfab086000bd5843002ff8c218016fc610c02dffa886013ff94430007faa21804ffc510c02bffa086013ff90430007fa821804ffc410c013ff9886009ff8c43004ffa6218027fc310c029ff9086013ff88430007fa421804ffc210c00b7f3006005ffd403002ffca018017fd500c00bfe2806005ffd003002ffc8018017fd400c00bfe2006005ffcc03002fbe6018017fe300c00bfd1806005ff4c03002fba6018027f9300c00bff9006005ff0803002ffe2018017fc100c00bffb2c4005bfd962002ffccb10012fe658800bfeb2c4000bf5962002ff8cb10016fc658800bffb244005bfd922002ffcc91000efe648800bfeb244000bf5922002ff8c910016fc6488025ffaa44011ff95220007faa910047fc548800bffb1c4005bfd8e2002ffcc710026fe638800bfeb1c4000bf58e2002ff8c710016fc6388025ffa9c4000ff94e20007faa71004bfc5388023ffa1c4000ff90e20007fa8710047fc43880057eb144002ffd4a20017fca51000bfd5288005fe2944002ffd0a20017fc851000bfd4288005fe2144002ffcca20017fc651000bfd3288005fe1944005ffd862002ffcc310006fe618800bfeb0c4000bf5862002ff8c310016fc6188025ffa8c4010ff94620007faa310043fc5188023ffa0c4010ff90620007fa8310043fc4188001ff98c4010ff8c620007fa6310043fc3188005ff90c4002ff88620087dc431000bfd2188005fe10c4002fb0862002dfcc110017ff508800bff2844005ff5422002ff8a110017ff408800bff2044005ff5022002ff88110017ff308800bff1844005ff4c22002ff86110017ff208800bf79044002fec822002ff84110017f8208800bff8844005ff04220007feca90002ff654801fff32a4004bf99520007faca90002fd654801ffe32a4004bf19520007fec890002ff644801dff3224003bf99120007fac890002fd644801dfe3224003bf1912007ffea89003bfe5448001feaa2400eff15120007fec690002ff6348001ff31a4009bf98d20007fac690002fd6348001fe31a4009bf18d2007ffea690003fe5348001fea9a400fff14d20077fe8690003fe4348001fea1a400eff10d2002dfec49000bff5248005ff2924002ff54920017f8a49000bff4248005ff2124002ff50920017f8849000bff3248005ff1924002fb8c920017fa6490003ed3248005fe1924000ffd8520005fec290003f761480017bb0a400dff9852000dfcc290003fd614801bfe30a4001bf18520007e8c290006f4614801fffa8a400dff94520007faa290037fc514801dffa0a400dff90520007fa8290037fc4148001ff98a400dff8c520007fa6290037fc3148005ff90a4002fbc8520017fc429000bfd2148001f690a4002ff08520015fec09003fff504800bff2824000ff5412002ff8a09003bff404800bff2
  | 2 => 0x3002ffcc51800afe628c00bfeb146000bf58a3002ff8c518016fc628c03dffa94601cff94a30007faa518073fc528c03bffa14601cff90a30007fa8518073fc428c013ff994601cff8ca30007fa6518027fc328c00bffb0c6005ff9863000dfcc318017fd618c0017eb0c6005ff1863002df8c31807bff518c037ff28c6000ff546300dff8a318077ff418c037ff20c6000ff506300dff88318027ff318c037ff18c6000ff4c63004ff86318073ff218c037ff10c6000ff486300dff84318016fe608c00bffa846005ff9423002ff4a118017fd508c001fca846005ff1423002ffe8118017fe408c00bfd2046005ff50230007f28118017fc408c00bff9846005f7cc23004ff66118017ff208c00bfe1046005ffc423002ff82118003ff654c0017fb2a601aff99530025fcca98003fd654c0017eb2a601aff19530025f8ca98003ff644c0017fb226019ff9913001dfcc898003fd644c0017eb226019ff1913001df8c89806bff544c033ff2a26000ff551300cff8a89806bff534c013ff29a6000ff54d3004ff8a698067ff434c013ff21a6000ff50d3004ff88698003ff624c0017fb126018ff98930015fcc498003fd624c031fe3126002bf189300d7fea498063fe524c001fea926018ff149300cffe8498063fe424c001fea126018ff1093004ffe6498003df324c031ff1926000ff4c930007ba6498027fc324c001ffb0a6000bfd85300bffcc298006fe614c001feb0a6017ff1853000df8c29806bff514c02fff28a6000ff545300bff8a298067ff414c02fff20a6000ff505300bff88298027ff314c001ef98a6017ff8c530007fa6298003dd314c013fe18a6018ffc85300bffc4298003fd214c02ffe10a601affd413002ffca098003fa504c001fea826000fe5413002ff8a098067ff404c00bff2026000fe90130007fa8098003f9404c00bfe2026009ffcc13004ff66098017fe304c00bef1826018ffc813002ff8409805fff104c00bfe0826005ffd943002dfeca18017fe650c0097f3286005df99430024fcca18017fd650c0017eb286005df59430004faca18017fc650c00b7e3286005ffd903002dfec818017fe640c0077f3206005ef9903001d7cc818017fd640c0017eb206005ef590300057ac818017fc640c00b7e3206016ffd50300affca818003fd540c02bfe2a06009bf98c3004ffea618027fe530c013fea986009ff14c3004ffe8618027fe430c013fea186009ff10c3002ffec418017fe620c0057f3106005fb98830015dcc418017fd620c0017eb106005fb58830005dac418017fc620c00b7e3106016ffd48300a7fca418003fd520c029fe2906015ffd08300a7fc8418003fd420c029fe2106009ffcc83004ffc6418027fd320c013fe1906005ffd843002ffcc218006fe610c00bfb3086001bd9843002ffac21800
  | 3 => 0xca848005ff1424002ffe8120017bf4090007fda048005ff1024002ff08120017ff209000bfe1048005ffc424002ff82120003ff65500017fb2a8025ff99540025fccaa0003fd65500017eb2a8025ff19540025f8caa0016ff6450007ffaa28025efd514001ffca8a000ffd5450007fe2a28003ef15140007fec6a0002ff6350001ff31a8000ff58d40007f8c6a0026fc635004bffa9a8000ff94d40007faa6a0097fc5350007ffa1a8003efd0d4001ffc86a000ffd4350001dea1a8003ff10d40007fec4a0002ff6250049ff3128002bf98940007fac4a0093fc62500057e3128025ffd4940127fca4a0003fd5250049fe2928003ffd094001f7e84a000ffe4250007fea128000ef5094001ff884a0003ff3250049ff1928000ff4c940127f864a0003ff61500017fb0a8023ff9854000dfcc2a0003fd6150047fe30a8001bf1854012ffea2a008ffe5150001fea8a8023ff1454001ffe82a000fbf4150007ff20a8003ff505400077a82a000ffc4150001ff98a8023ff8c540007fa62a008ffc3150049ff90a8023ff88540007fa42a008ffc21500077fb028025ffd414002ffca0a0003fa5050001fea828000fe5414002ff8a0a000fff4050007fda028005ff9014002f7c80a0017fc405000bde2028003fe10140127fe40a0017fc2050047ff8828005ff0414004ffecb98026ff65cc013ff32e6004bf9973004ffacb98002fd65cc013fe32e6009bf1973004ffec998026ff64cc013ff3266003bf9933004ffac998002fd64cc013fe3266009bf19330117fea998087fe54cc001feaa66021ff1533004ffea798027fe53cc013fea9e6009ff14f3004ffe8798027fe43cc013fea1e6009ff10f3004ffec598027fe62cc0057f3166009ff58b30005fac598027fc62cc0057e3166022ffd4b30107fca598003fd52cc041fe2966021ffd0b30107fc8598003fd42cc041fe2166009ffccb3004fbe6598027fe32cc013fe9966000f74cb3004ff86598027ff61cc013ff30e6001bf9873004ffac398002fd61cc013fe30e6001bf18730117fea39807ffe51cc001fea8e601fff1473010ffe839807ffe41cc001fea0e601fff1073004ffe6398027df31cc013ff18e6009ff4c730007ba6398027fc31cc041ff90e601fff88730007fa439807ffc21cc045ffa866005ff94330007faa198017fc50cc043ffa066005ff90330007fa8198017fc40cc041ff9066005ff083300fffe2198017fc10cc00bffb2c6005bfd963002ffccb18012fe658c00bfeb2c6000bf5963002ff8cb18016fc658c00bffb246005bfd923002ffcc91800efe648c00bfeb246000bf5923002ff8c918016fc648c03dffaa4601dff95230007faa918077fc548c0017eb1c601effd4e3004ffca718003fd538c013fe29c601dffd0e3004ffc8718003fd438c013fe21c6005ffd8a
  | 4 => 0x17fe62940057f314a005ff58a50005fac528017fc629400b7e314a004ffd4a50027fca528013fd5294009fe294a02effd0a5016ffc8528003fd429405bfe214a000ffcca5016ffc6528003fd329405bfe194a005ffd865002ffcc328006fe619400bfeb0ca000bf5865002ff8c328016fc6194009ffa8ca004ff94650027faa328013fc519405dffa0ca02cff90650007fa83280b3fc4194001ff98ca02cff8c650007fa63280b3fc319405bff90ca02cff88650007fa43280b3fc219400b7f304a005ffd425002efea128013fb509400bfe284a005fe1425002ffe8128017fc409400bff904a005ff0825002ffe2128017fc109400b7fb2aa000ffd9150005fec8a80affe64540077f322a000ff5915015ff8c8a800efc6454009ffaa2a004ff9515015efca8a8013fd5454009fe2a2a004df15150007fec6a8002ff6354001ff31aa000ff58d50007f8c6a8026fc6354009ffa9aa004dfd4d50027fca6a8013fd5354001bea9aa004ff14d5015ffe86a8003fe4354001fea1aa02bff10d50007fec4a8002ff6254055ff312a002bf98950007fac4a80abfc62540057e312a004ffd4950026fea4a8013fe5254009fea92a000df54950027f8a4a80afff4254055ff212a000ff50950157f884a8003ff3254055ff192a000ff4c950157f864a8003ff61540017fb0aa029ff9855000dfcc2a8003fd6154053fe30aa001bf18550027fea2a80137f5154009ff28aa004ff54550006faa2a8013fc5154057ffa0aa029ff90550007fa82a80a7fc4154001ff98aa029ff8c550007fa62a80a7fc3154055ff90aa029ff88550007fa42a80a7fc21540097fb02a004ffd4150027f6a0a8017fe505400bbf282a005ff1415002ef8a0a8013f85054057ffa02a005ff10150157fe40a8017fc2054053ff882a005ff0415002ffecb20016ff659000bff32c8004bf9964002efccb200127e659000bfeb2c8000bf5964002efacb200027d659000bfe32c8005bf1964001dfac92000fff5490007ff2a48003ff5524001ff8a920017ff639000bff31c8009bf98e4002ffac720002fd639000bfe31c8028ffd4e40007fca720003fd5390051fe29c8003ffd0e4001ffc872000ffd4390007fe21c8005ffd8a4002ffcc52000afe629000bfeb148000bf58a4002ff8c520016fc6290051ffa948027ff94a40007faa52009ffc5290007ffa148003ff90a4001ffa852000ffc4290001ff9948027ff8ca40007fa652009ffc329000bffb0c8005ff9864000dfcc320017fd61900017eb0c8005ff1864002df8c3200a3ff519004dff28c8000ff54640137f8a32000fff4190007ff20c8003ff5064001ff88320003ff319004dff18c8000ff4c640137f8632009fff219004dff10c8000ff48640137f84320016fe609000bffa848005ff9424002ff4a120017fd5090001f
  | 5 => 0x873104ffec198827fe60cc40b7f3066209ff58331005fac198827fc60cc46dffa866236ff143311affe81988d7fc40cc469ff9066234ff0833100ffe2198807fc10cc401ffb2a6200bfd953119ffcca98812fe654c401feb2a6200bf5953119ff8ca98812fc654c401ffb226200bfd9131197fcc89880efe644c401feb226200bf59131197f8c89880efc644c467ffaa26232ff95131007faa8988cbfc544c4037fb1a6233ffd4d3104ffca698803fd534c413fe29a6232ffd0d3104ffc8698803fd434c413fe21a6200ffd8931005fec4988c7fe624c4057f3126200ff5893118ff8c49880afc624c467ffa926231ff94931007faa4988c7fc524c465ffa126231ff90931007fa84988c7fc424c413ff9926200f7cc93118ffc6498803fd324c401ee9926209ff0c93100dfec298807ff514c403ff28a6201fd9453100ffaa298803f5514c403fe28a6201ffd053100ffc8298807f6414c403fea0a6200fd5053100ff88298807ff314c413fb98a6201ff8c53100fbc6298807fc314c403ee18a6201fd0c53100ffe42988c7f7214c403ff10a6201ff0853100fe84298803ff604c4017fb026200ff98131007fac098803fc604c40b7e3026233ffd413119ff8a0988cbff404c465fe2026231ffc813118ff84098807ff104c403fb8826201ff04131007feca90802ff6548461ff32a4204bf99521007faca90802fd6548461fe32a4204bf19521007fec890802ff644845fff3224203bf99121007fac890802fd644845ffe3224203bf19121187fea8908bffe5448401feaa2422fff15121007fec690802ff6348401ff31a4209bf98d21007fac690802fd6348401fe31a4209bf18d21187fea690803fe5348401fea9a4230ff14d2117ffe8690803fe4348401fea1a422fff10d2100dfec49080bff5248405ff2924202ff54921017f8a49080bff4248405ff2124202ff50921017f8849080bff3248405ff1924202ff4c921017f86490806ff6148403ffa8a4201ff9452100ffaa290807fc5148403ffa0a4201ff9052100ffa8290807fc4148403ff98a4201ff8c52100ffa6290807fc3148403ff90a4202fdc852100ffc4290807ee2148403fe10a4201fb0852100fe84290807e42148401ffb024200bfd8121007fcc090803fd6048401fe3024205bf18121187fea0908c3fc504845fffa02422fff10121017fe409080bef2048405fe1024201ffc412100fee2090807fc10484097eb2ca005ffd925002ffcc92800efe649400bdf324a003af9925002ffac928002fd649400bdeb24a000af5925002ff8c928016fc6494009ffaa4a004ff95250027faa928013fc549400bffb1ca005ff98e5004dfcc728017fd63940017eb1ca005ff18e50027fea728013fe5394009fea9ca004ff14e50177fe8728003fe4394001fea1ca02eff10e5002ffec528
  | 6 => 0x1ffb1aa200bfd8d51007fcc6a8803fd6354401fe31aa209bf18d51027fea6a8813fe5354409fea9aa204ff14d511d7fe86a8803fe4354401fea1aa23aff10d51007fec4a8802ff6254473ff312a202bf98951007fac4a88e7fc62544057e312a204ffd4951026fea4a8813fe5254409fea92a200df54951027f8a4a88ebff4254473ff212a200ff509511cff884a8803ff3254473ff192a200ff4c9511cff864a8806ff6154403ffa8aa204fdd455100ffca2a88077e5154403fe28aa201df1455100fe8a2a8807ff4154403ff20aa201fd9055100ff882a8807fe3154403fb18aa201ff0c55100ffe42a8807fe2154403fe10aa200ffd8151005fec0a8803fe6054401feb02a200ff1815102df8c0a8813ff5054409bfa82a204ff141511d7fe80a88ebfc4054473ff902a239ff0815100ffe20a8807fc1054401ffb2a8200bfd95411c7fccaa0812fe6550401feb2a8200bf595411c7f8caa0812fc65504037fb228203ffd514101ffca8a080ffd5450407fe2a28200ffd8d41005fec6a0803fe6350401feb1a8200ff18d4104df8c6a08e3ff5350401ff29a8200ff54d411c7f8a6a080fff4350407ff21a8203ff50d4101ff886a0803ff62504017fb128237ff98941015fcc4a0803fd625046ffe3128202bf189411c7fea4a08dffe5250401fea928237ff1494101ffe84a080fbf4250407ff2128203ff509410077a84a080ffc4250401ff9928237ff8c941007fa64a08dffc32504037fb0a8201ffd454100ffca2a0807f65150403fea8a8200fd5454100ff8a2a0807ff4150407fba0a8201ff9054100f7c82a0807fc4150403de20a8201fd1054100ffc62a0807f63150403fe18a8201ffc854100ffc42a0807fc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028205bf181411c7fea0a08e3fc5050407ffa028203efd014101ff880a08dfff205046ffe1028201ffc414100ff820a0827ff65cc4137fb2e6209ff99731025fccb98827fd65cc4017eb2e6209ff1973104df8cb98827ff64cc4137fb266209ff9933101dfcc998827fd64cc4017eb266209ff1933104df8c9988dbff54cc46bff2a66200ff553311aff8a998806fe63cc413ffa9e6209ff94f3104ffaa798827fc53cc413ffa1e6209ff90f3104ffa8798827fc43cc413ffb166209ff98b31015fcc598827ee62cc405773166209ff58b31005fac598827ed62cc40176b166209ff18b31015f8c5988dbff52cc469ff2966200ff54b311a7f8a5988d7ff42cc469ff2166200ff50b311a7f88598827ff32cc413ef9966209ff8cb3104ffa6598803dd32cc413fe1966201bf5873100ffea398807fe51cc403fea8e6201ff1473100ffe8398807fe41cc403fea0e6201ff1073100ffc6398807de31cc403fb18e6201ff0c73100fb86398807ff21cc403ff10e6201ff0
  | 7 => 0xa1003ed5250805fe2928402ffd094201fde84a100bfe4250805df2128402ff109420177884a100bec4250805ff1928402fb8c942017f864a1003ff61508017fb0a8441ff9854200dfcc2a1003fd6150883fe30a8401bf18542217fea2a1107fe5150883fe28a8403ffd054201f7e82a100ffe4150807fe20a8441ff8c54220ff862a100bff2150805ff10a8402ff08542007fec0a1002ff6050801ff3028400ff58142007f8c0a1016fc6050885ffa828442ff1414201ffe80a100fbf4050807fe2028402ffc8142017f840a1107ff1050883fe0828409ffd973204dfecb99027fe65cc8097f32e6409ff59732005facb99027fc65cc8137e32e6409ffd933204dfec999027fe64cc8077f3266409ff59332005fac999027fc64cc8137e3266440ffd53321fffca999003fd54cc87ffe2a66402bf98f3204ffea799027fe53cc813fea9e6409ff14f3204ffe8799027fe43cc813fea1e6409ff10f32015fac59900bff52cc805ff2966402ff54b32017f8a59900bff42cc805ff2166402ff50b32017f8859900bfe32cc805ef1966402fb8cb32017f8659900bdc32cc813ffb0e6409ff9873200dfcc399027f661cc8037b30e6409ff58732005fac399027f561cc8017ab0e6409ff1873200df8c399103ff51cc87dff28e643eff147321fffe83990fbfe41cc87dfe20e6409ff8c73204ff8639900bff21cc805ff10e6402ff0873204ffec199027fe60cc80b7f3066409ff58332005fac199027fc60cc881ffa866440ff143321fffe81990fffc40cc805ff9066402ff083321f7fe21990fbfc10cc801ffb2a6400bfd95321effcca99012fe654c801feb2a6400bf595321eff8ca99012fc654c801ffb226400bfd91321e7fcc89900efe644c801feb226400bf591321e7f8c89900efc644c87bffaa2643cff95132007faa8990f3fc544c8057fb1a643dffd4d3204ffca699003fd534c813fe29a643cffd0d3204ffc8699003fd434c813fe21a6402bfd8932017fea49900bfe524c805f72926402ff54932007daa49900bfc524c805ffa126402ff90932017dc849900bfd424c801f6a126402ff10932017fe6499027ef324c805ff1926402f78c932017f8649900bdc324c805f61926400ffd8532005fec2990effe614c8037f30a6400ff585321dff8c299006fc614c87bffa8a643bff945321dff8a2990f3ff414c877ff20a643bff105321dffc6299027fc314c805ff90a6402ff885321dfdc429900bfc214c805f610a6400ffd8132005fec099003fe604c801feb026400ff1813202df8c0990f7ff504c87bfe282643cffd01321e7f8809900bff204c805f79026402ff081321dffe20990effc104c8037fb2aa200ffd9151005fec8a88ebfe64544077f322a200ff591511d7f8c8a880efc6454409ffaa2a204ff95151027faa8a8813fc545440
  | 8 => 0xf8ca4304ff86521827ff6190c13ff30c8601bf9864304ffac321802fd6190c13fe30c8601bf18643257fea321923fe5190c91fe28c8603ffd064301ffc832180ffc4190c13ff18c8609ff0c64324ffe4321923fe2190c91fe10c8609ffd824304ffcc121816fe6090c13feb048600bf5824304ff8c12192bff5090c95fe2848603ffd024301ff88121927ff2090c93fe1048648ffc4243247f82121803ff6550c017fb2a8600dfd9543004fecaa191ffe6550c097f32a8600ff59543005facaa191ffc6550c097e32a8600df19543024f8caa1826ff6450c07ffaa28603ff9514301f7ca8a180ffd5450c01deaa28603ff1514301dfec6a191fff5350c13ff29a8600f794d43007faa6a1803dd5350c13fe29a8603ffd0d4301fbe86a1827fe4350c13df21a8609ff10d4304f7886a180fdc4350c01ffb128600bfd8943237fcc4a180afe6250c01feb128646ff18943015f8c4a191fff5250c8dff2928646ff1494301ffe84a180ffe4250c07fe2128646ff8c94304ff864a1803ff6150c017fb0a8645ff9854300dfcc2a1803fd6150c8bfe30a8601bf1854323ffea2a1917fe5150c8bfe28a8603ffd054301ffc82a180ffc4150c8bff18a8609ff0c543237fe42a1917fe2150c8bfe10a8600ffd8143005fec0a1803fe6050c01feb028600ff1814302df8c0a191fff5050c8ffe2828603ffd014301f7e80a180ffc4050c8dff9028646ff0814322ffe20a1917fc1050c057fb2aa400ffd9152005fec8a9113fe64548077f322a400ff59152227f8c8a900efc6454809ffaa2a404ff95152027faa8a9013fc5454801ffb1aa400bfd8d52007fcc6a9003fd6354801fe31aa409bf18d52027fea6a9013fe5354809fea9aa404ff14d52227fe86a9003fe4354801fea1aa444ff10d52015fec4a900bff5254809f7a92a402ff94952016fca4a900bfc5254805be292a402fb14952017fe84a900bfe4254805f7212a402ff10952017fc64a900bee3254805fe192a400ffd8552005fec2a910ffe61548037f30aa400ff5855221ff8c2a9006fc6154809ffa8aa404dfd4552027fca2a9013fc5154889ffa0aa443ff9055221ff882a910ffe3154887fe18aa402ffc8552017fc42a900bfc2154801ffb02a400bfd8152007fcc0a9003fd6054801fe302a405bf18152027fea0a90137f5054809fe282a444ffd0152227f880a900bff2054805fe102a443ffc415221ff820a9003ff65508017fb2a8442ff99542025fccaa1003fd65508017eb2a8442ff19542025f8caa100aff6450807ffaa28403ff9514201ffaa8a100ffc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8409bf18d42217fea6a1003fe5350801fea9a8442ff14d4201ffe86a100ffe4350807fea1a8403ff10d42015fec4a100bff5250805ff2928402fb94942017faa4
  | 9 => 0x7ff212a803ff10954297fc64aa14bfc3255001ffb0aa800bfd855428ffcc2aa006fe6155001feb0aa851ff1855400df8c2aa013ff5155009ff28aa804ff1455401ffe82aa00ffe4155007fe20aa851ff8c55428ff862aa14bff21550a3ff10aa851ff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa016fc6055009ffa82a804ff1415401ffe80aa00ffc40550a5ff902a852ff0815428ffe20aa147fc10550097eb2ca609ffd925304ffcc92980efe6494c13feb24a600bf5925304ff8c929826fc6494c09ffaa4a604ff95253286fca929813fd5494c09fe2a4a604df1525304dfcc729827ff5394c13bfa9ca604f7d4e5304ff8a729827dc5394c13ffa1ca609ff10e5304ffec529827fe6294c057f314a609ff58a53005fac529827fc6294c057e314a604ffd4a53027fca529813fc5294ca1ffa14a64fff90a5327ff88529827fe3294c13fe194a609ffd865304ffcc329806fe6194c13feb0ca600bf5865304ff8c329806fc6194c09ffa8ca604ff94653027f8a329943ff4194c9dff20ca64eff1065304ffc6329827fc3194c9fff90ca64eff88653277f84329827ff6094c13ff304a605bf9825304ffac129802fd6094c13fe304a604ffd4253027f8a129943ff4094ca1fe204a64fffc825327ff8412993bff1094c9dfe084a609bfd9553007fec8a9802ff6454c01dfb22a600afd915326ffcc8a980efe6454c01feb22a64dff1915301df8c8a9803bc6454c075e322a604ffd5153026fea8a9813fe5454c09feaa2a600df55153027f8a8a9812ff6354c09ffa9aa604f7d4d5304ffca6a98277e5354c13fe29aa609df14d53027b8a6a9937ff4354c13fe21aa600ffd8953005fec4a9933fe6254c057f312a600ff58953267f8c4a980afc6254c09ffa92a604ff94953027f8a4a9937ff4254c99ff212a64cff10953267fc64a9827fc3254c01ffb0aa600bfd855325ffcc2a9806fe6154c01feb0aa64bff1855300df8c2a9813ff5154c09ff28aa604ff1455326ffe82a992ffe4154c97fe20aa64bff8c55304ff862a9933ff2154c97ff10aa64bff08553007fec0a9802ff6054c01ff302a600ff58153007f8c0a9816fc6054c09ffa82a604dfd4153027f8a0a9937ff4054c9bfe202a64cffc8153267f840a992fff1054c97fe082a609ffd964304dfecb21827fe6590c097f32c8609ff59643005facb21827fc6590c137e32c8603bf5924301ffea92192bbf5490c07ff2a48603ff5524301ff8a92180fbc5490c137f31c8609ffd4e4304ffca721827de5390c13fea9c8600f754e4304ff8a721827ff4390c13dfa1c8603f7d0e4304ff88721827dc4390c13ffb148609ff98a43015fcc521827fd6290c017eb148609ff18a43015f8c52192bff5290c93ff2948649ff14a4301ffe852180ffe4290c07fe2148609f
  | 10 => 0x80180000080000000080280000000180180000280c00800100600100100600200580c80000180080000800100000080000580580380180280500b00400100280000080000000100380000380b80680000500000680000080480100480000000000080080900300000080180300080180000080180480000080081380000080000380000000000000700180080080002000300000000a80180100580180100f80000300000080100600700080180000000000100400a00400000000a80000300180180380000600300000480700600080200180000000000080000000100100000000200700180000080000800000000080100000780080000080180380000080e80200100080000000280000180200100080400000000180100000580080000100180300380280300000000080000000300280780400000080900000280200000080180380100100000080080180080180100180100000080100580000180201000100800300580600380180080480500380080000000000200000080000780980480080180000080580300000180000000380000000300480080200780080000380200280480000080080600080000000080080281800680280480180200000300100480500100000200000380080500400080200300b80000100100080000100580000500080580000100500100180000100000200000000000d00700001e80180100780080080000080680000280100180500100000000200000580380100000080080980000000000580300080180080380080080080080100000180400000000080000c00100000280100580000080280b80280000580080100280080280400200080801880380100080600100000100000180280180400380000080080080000100000000400900200d80000000080000700080000400000200280000100280000080100300000300000180100200100180080080000000100000500000280601000000200400080800b80000700780280000180280300000080180380080000000280100180000180000000000080000000400000100500e80100000000800000180000080400080200080000100000000100000000000100080180000100080300080300300100180101080400100000580080480880100e80180280000300080200700100000000000000280080480880500080180100901780100780300080300900800eff65550077fb22a803ffd51540277ea8aa00ffe5455007bf2a2a803ff1515401ef8a8aa00fbc54550079e2a2a800ffd8d54005fec6aa003fe6355001feb1aa800ff18d5404df8c6aa013ff5355009bfa9aa804ff14d5401ffe86aa00fbf4355007fe21aa800ffd8954005fec4aa14bfe62550057f312a800ff58954297f8c4aa00afc6255009ffa92a804ff94954027f8a4aa00fff4255
  | 11 => 0x16bc000000000000000058e00000000003c521093c000007403d0000e2e3591eb1af8f640003679d80000000000025000000004980011828a41d48c24ad87ca16d11745f600025080000000003290578d0e35d02b9cbcc4a2470001d309c20003448f780003a745a0000000000000187cdaa16200018d49980003dca14800041f00000000003253fd8630b980252368a44fc821a24e96300005f831a0a0085c3ba12ea2dc7fa5c9392040857e00019b800000022a1670e2cbb42e23b298981a41270870d983f402f0001fe03b22711be01806e60000a49e40c840e711c82bc27600021b0674ce071c2d70f2c9188874338114d3c73626f1fb09942ea0da930496a2840299ae118a3083a90000e4c12c0da19f44ac00015880000002c03ed003117e1ec2da9310f0a30f2f68800a520000001648e720000001958000000000184000000000000009d25c100000005100002788000548000000041400036b000000000000000000002440003a500008e20b800000000004bc2648c34bcc4dc22880000003742c89f88d2c0511770b2000054c2539b281fe6ab112220900009a0031344a663222b880003fc1f30ee885404056744400000000000001c04ea600022f17cc15c3830001f3ce5c7d6000176c16a83639680001840e91d280005d277e3ac0a386682723b1907465815d1b480a8ee864403683f415821f2e205b0786415115842c26e89545880fd1567753b3000000024d00000000000000001ff400069b15419f8caa14c000223516400000000005940002b0881077a0d12a522ec0202bb3870bb4a58771000000000000000018380006532a0218c2900000e2865c0860643838a880fa00004284743d255942c8f70e683f000000002400000000644da400023294f40007463bc00000000003cc22bc00066433d9d144ec0000ee00000000000001aa50c0163076800073e0000c015ac6ea7b52f5a1b83f670c1ad1e749306203f983e000071d424076903281a0e891480007de2a30a18faa101160800020884a3630eac79c51123e1b2c0d8434400a1fc70c6082231c8909e00004a96980003b700100400400200080300300000100280680100880000600080000080100000000280000200600180000f80000200100700000180100680000180000480180480400d80000100000000180000080000080980c00000000080000080180300680000b80180000200000200480680000180080680500500000300000000000000080180080080e80000080100300280000000000080580080000280000080000500080180700000000100780000400100180100300180300d00500180100500080800080000000000500300280301780000000100680900e80100000080300080400080181a80780080a000000001004002003000006800000001000001
  | 12 => 0x808a39902f824c6fb131946c28e4c642085d0e762501fd8000e5615542a8d700c41f4000074cee60002041adc0100001cd8000946000000215000000038f00000000000001d400003be00000008ce00023c800000088000013c800042a0000000e960000db1dc05060000000000346367000222c0003df0001e9c5600000c8176000076216297d800017b29e00005ca7ad000000115a000148148ccca534000170cb606590868000a2e8a60020dc80f68c603ba1ac6063a0000000024a0000a995ec9b03ac00016b08c23990d587dcddc0001dc165d04e59845b0a30d3a3fa2b71cfd00e7ba2391f5cd7e1ea3e180c0be229525c97788f42f81779508c8a6631499e8c7603381e31f647f00001160f9000043e0548e20ffe6c80848000d9a8663e889987ce25916599e87a88bd40f000cc7c0000c71e3891c1fc06e8204c1e00013a96a40004d724b189cd321d200003b0000229000129054675116d8000d7400000005e000012118f0e540344202cb0000422310358002801a85f000227033c6800cc0c080000002da061d0ee44c398800055e00000000000006aa42e000000000000000008586222268fb4bba6e10001050bfa0000000000c0670008e000000077d04fa1bcf400000001c48c2600000000000002b90000000baa4c31e0800097c00014e0000000000000075c0007df26585ac9fa7bc000216822600027789307c445300000007ca64c000000000000026c800000000000000000000000ad06908c800043500008866a306480000003d50000eb814c3650000000d5082f0000000a5e2972cf1de856e2381f99b383ce4af000027416205f0001ba40002c642112b49541670590e9800071a24884c02506663b48c80f2e5b30e509540002d01b80fa02828861f4959868e23701d05409e61bf2d89e5800e0e32880e2861c43f0ff8d1080a87404917445b88181c4a0d4cb066d32485fc25401e38b0ac80f0000216904513421300007400000002249bf80e4857000000000000044c8000afa3ca0000000d1e1cd00019a07b20000c417b10460003a220f4a7448104c913800048f1d115205b28432360da11745f42b9066c20601920c06f450e5623ea2054f383eb0189e304460fb0ef936c0b21710e413e90222493700ce403a22d0c115a0dbe4624380d7c66682d3ee0ea800000041a0000ada618321800000000030a800100885021221b000068d2ec9dc800000013780000004df1b0000036600021880008180000000000aee00000000001c819a00011040000001e38000c9672c33080007d40d73601368a1c0001fe0000e740a33868780f5e00009795f862a00012d19f00000003e680003cc00016c1e1803e2140e20c849c471b00000dcb046b411a0d04000063000000000000019e000000068b05598f00000003648e590442b5000
  | 13 => 0xe800000000034b950c9d058402084909fe858000155c00000005980002280000000318000000117000000052d000000000000014d8000000000000127895643331f9c2c3c200003a8000d4811233c800000070218c1714f1e2943888000000000422883000072a1492124962530000013c0006a23fa85cc35a56a000000102000035c8bcc4e080a1b10c28b9e000000124d0666af3820000ae64e543f2024a1a70530f01344ce3541229c7c0525fa39e03980004c0195870443c0de1dd81bc000000333800000000004480004be7a20f400000000000000e30000000000000000000024d0d20ce666900007011700000000ab80000000000fd800031a180800041c0000001bb400060a00000001220000ca84e04a80003bc986c79e0000000ed8bf80003171facb9400012d93900787280b29e3454e0553c9a3110885d003480000dc79b309000000000000000000000ce00009a00ca0270000ca00f221c06f8000f1417228c0fc40001ce31980008963cd0001b98c1a66e289893caaa52408819d0bbe7ab3000dd881a0611c28f60fd417028a064c84c3970000000da054e00006a85322773df83b852c7060000000a623000001048c7a2dd3a11ef8dfe896390800000000000000000004d6000000000000000007c400000000000000004fc3ae12943640003f8111cd0200035000000001420001fe871e57f40a00000004780a500006f00000000000000000000000040c4952fd9874000847218000058402e00000000008252d512500000000ce0000000000000118c1ca00028d1510aca0002018000b0089d00013e00008721a583110c26f31f31f74000000000000000000000012cccd43803af80000007952d28000bc88bc3761d5800069f000000000000013490589c00391a1800046c0000001d7408460609a0000c2e00041d943c3aa5c7000000000000000000004501432f102f4a2c29f00000010400003fb12a430a45729909e9160116000175837478300000000006a63e083c400054b3c415a400076a00016dc8cc00000015f0b4626e3c005b8d6633e01a814046468300009acb6c15200000000007c90001975140000000004c41212e05c81fc6280000000000a6c08f28419781362e8012203400032441908600005631241f6c00000000014640002ad00001606bc2b800000003707842ca800071c18b0001fc511c00015a092cfee27800000000000001f600005880001a494541de1e40000000c62417061926cc8c0000000000f6000000012a000087d0000fd00007383e2000010042738a800000059d4141900000000000008c00000000000000000001bc80000ac0002a08000000805000208400006a2dd80000005940250d444840001e90fe4fda1a22531eb11120663c89b300002de17d09fc2b81b02211494a5458d0e321e8ed
  | 14 => 0x8a28f2fc80000000000000000000000281800000010c000000012e00000016f45ae39d1a701206da2400001f9c00000011d1a706244134420fbc280000166002d0800112761b9040a13c1780df46ac00045494e465e22201687c80000002850efc44240400020c400000033580b000032e0000000aa66f442b17c912260728e0bf05404b70001bf065408400001cc4c059a228000080400003b000051a7bb0410a98de45d4207045cade10a0bb988c9704c5290213885244500020f8a022df0001d7874240b35b1a9c72800002e800076a18434d05804ae729000000023e00031509f028c81b4571160fa060c3e1228d0a63d32bd0708f040f325e8ee51843533f08f248ac2440260a0810649034883649386c3000000087a2163bf8ec400000027b075807a5ee4550f08b12000000230c1800000000b581a02892080c9ce7a00000000005ec2cf0dd80002325090b51b9420c37132f8d8ce1e789000069831437e2bc00000000001cd0ef00000000000000e4a0000000000a9e000211941c000000391930885654d2ac1bf40b889200014b80000004538f10ff200000000008fc3310001af40007192dd103c17e0000508f300005c800000000e023e2c99d6cd880000001b8846033b01986e40960003c900000000003bd800000039e2d68218766000245800000017526700000002431a91410a925510b420b1180747000000000041b2000f6859a4ae3008000c9e1ed3689bc0c384ac1c120f083c0053a08d3c4825740000124b324fe0000000a6e6ae000109400015714d18b0000000000173800011109e95900003af08d98d87245e907a1a844c427e2f3933c1300cc06a02f0a3a253314836c39888c40e87509907fe0fa99e04fa1940bd11f44240f545120e426c16421904cc8a88682908c58ce401418f807000020a43ca05800068614c000016c03b32e11c05585350d4120000036e4149408c822ab3c38290f022033428000f5c000183800000000040615740005a200017a00000003980d5c36e000000000110a6390000000a0a0002718000000088000027800041c0000000748313000181400000008a8a78bfe0002ab1d00000407000006d0a23dd1d197dcdec6d41bf91fc6180ca001070c3c62d51b607f45ce00000011ecd7873e0002278fa601518b882cc5a1f80000000c940000000cc8c500000000000b8005e352a20d12600025d80000000ba12c0000b4000000000000d64f40439cd470e0000000c188b40000000000000001000061847e16f1931d68e06898013011c43634c3b7a03c61660b21a8b8c27e4a02890230e2050b3b700f800062b15e06a46a01592800f6cbde44006a85606941c92c81968f967e00001e985143640f78000f3e096164880414e00006980009aa0000000b5020e000301181000017d17c9c50eaa5d714
  | 15 => 0x19b0db455f0001f9800034d0000000e4e80b0000e70000657371974c960419346000023c8121888000c6423b10b808831232300000008c000024c9d5c0008b93e912d915051e0001da00880000000000e90637000000016e3f509a800034a0003e60a0429c72037590a014a16d3db8000000000047120868a89b0001be40000000f70e610967fc1131db40000000c180003ca1de0000d6cd100000d8994114a5813451fd02ac7542c184610480212250000f6800019a80000003814389980a8e0002bb004887620717892244324d02cd927c768000308800103800e0000000c743f2065a2b054a7e344a07d824655e204800027c2ba4071b080006f700000000000000000000dd000016980000000001e004b400000000000000000001691fc80008032ae106800000000016e0d58000000161800000043e00009ba63b0000f80be04fb24306bc0000e02f09ab414400025a0a140d026a0001f1c9107d809c89e475000014580000000f0404000000000022d800003000022404206382100000000dba0000001234dd400025fa2cca4e15f0800fb83f27e81761708cee0a008d0000d040001329b60d3086400020fc0007aa43d843c00037a17a97a80004f900016acc2843737d1780fd22c734a925c18e84c30c8000f4a50c13604c8000000000000060a19601c000031a64e070a2f846a3420f58000e3000000000000000000be155000039000003e85527ef000000000009c00003f87fc4440000000f704b239b8aa80004eb2b81e64a440003a791dc00000003e16a0a3e0003d40000a5027443c00010bc0000c0822c00000000000001d600012307c0d760001758d00b4e00005d95e48d439100000006aa0002ff1920f7a2e13e3072d10258702713d44a46e72de0bfc06c000389956800023336f14e072640100000000000003b58bd00006f127500008e862f0000f2060800036c996c2880000aa12280001661f188f01f26c10002194440000000000065a02b36b98245e40001f080000002640e380000000000001b5801e6d310121340120ad0001e850c459c1bd83609241ac3e003706de3460cf851400044f41816fcec800019800000b64550000ffd1202272a280008e600011e80c884433a0001dd83c422f0000000aa00003b080000000f719b10e4aea2bd1618bf800000041301c4ca800000000000000003492284870000000000000000000021d400087305a10180007b345a97480000002830000aa48063269bd40007330000000f3426d1fb838800014f0001334e8658821e00000006762b0169111e476277216c5fa000000163cb3e53b0000000000000000076c9da000000000000040a0000000cea000000000000000015b21750d2000000000000083a0000000f3c0002fa91acc8e83700000008b22be3591d2503e19918e80001
  | 16 => 0xcc42a134a11a0d260000001e9000007e43b1734000000098961512e0000949d9c90a33f0001df000046e000063c6ee25e1c6868034e61a0b480000000000a680000000f63a700000000d62d08f5c9a82e63e29c200004e727b98901541793d8823505c12b1598ec90260c122f9884db617607419c4000046269819c9a4000000000000000000002a00b4054384972c6c286d1250e100000003ca120c7a2000000000000014b2c58000bb800012e0000c600003f7000000069000016f82fc2730000000ca20cf0000000d6219225d10bc0000ea07e1398ab67ce3379ea43422f70a88000c2c6c70140b90bca00000010e802c20d2930c6502e8020b099fc4f60f2194887406853f19e9ed84620003bb94f837c78b0ad800000000000000000000000290894df02d10002228b141ae00000008b820800000003b000044f80008ea6840001a38944000000073c4c20002d91718000000000000000063806d131c000000415921c0000000000f400005e30582118eb28380481b7002e20f18d83200004690200000f9036a1271ad4fca2e000004e8e140cd0de16e475a4840000d6000025141511bce9a6c53778000a560000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc765091001ebe6450910006bd6450910006ef6250910016ec625091004cff76cc910004fe76cc910004fd76cc91004cfc76cc91004ede63cc910006dd63cc910006ef62cc910016ec62cc91000df671cc910005f571cc910004ff764c910004fe764c910004fd764c910004fc764c91004ede634c910006dd634c910006ef624c910016ec624c91000df6714c9101dfe6214c91002df4764c51004ef4764c51002cf4764c510006f7654c510006f5654c510006f7644c510006f5644c51000df7734c51000fd7734c510007d7634c51004ef6634c51004ef4634c510007d4634c510005f7724c510007e7624c51018ef6624c51018ef4624c510007e4624c51018ee4624c510007d7324c510007d5324c510007f3704c51002df6704c51002df4704c510007f0704c51002df0704c51000ef7604c51000ff3604c51002df47648510016f4764851002cf47648510005f77348510005f5734851000df7724851000fe77248510007e76248510016f66248510016f46248510037e46248510016e46248510007f3704851002df6704851002df47048510007f0704851000ef7604851000ff36048510037e72048510024ff765411000cfe765411014cfd765411000cfc76541100067f65541100267c6554110006ef6254110156ec6254110005f7715411000df4715411002ff0105411001cff765011000cfe765011011cfd765011000cfc7650110006bf645011001ebc6450110006ef6250110126ec6250110005f7715011000df4715011002ff0105011000cfe76cc11000cfc76cc110006df63cc11004edc63cc110006ef62cc110106ec62cc11000df671cc110005f571cc110007d531cc11002ff010cc11004cff764c11000cfe764c1100bcfd764c11000cfc764c110006df634c11004edc634c110006ef624c1100c6ec624c110005f7714c11000df4714c110007d5314c11029dfa768811002efa768811006df97288110087eb6288110016fa6288110016f86288110037e86288110016e8628811002ff3718811000dfa718811002df8718811002ff0718811002efb618811002ff36188110087f23188110007f13188110087ea2188110087f22188110087e22188110037f12188110087e82188110014ff764811000cfe764811006cfd764811000cfc7648110006ef6248110016ec6248110005f7714811000df47148110007e5214811002fe8204811002ff0104811000df87648110016f8764811000cf8764811002dfb724811002feb7248110007eb6248110016fa6248110016f86248110037e86248110037ea3248110007e93248110007f3714811000dfa714811000df8714811006ff0714811002efb614811002ff3614811006ff23148110007f1314811006feb214811006ff2214811006fe92148110037f12148110007e12148110
  | 1 => 0xd10004fd7650d10004fc7650d100057f7550d100457c7550d10236ec6250d10014fe76d8910036ee62d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d891004cfe73d8910004fd73d8910006ef52d8910036ee52d8910036ec52d8910006ef42d8910036ee42d8910036ec42d8910036ee32d8910036ec32d891002cff71d891000cfe71d891002cfd71d891000cfc71d8910086ef21d8910086ed21d891002cfe70d891000cfd70d891002cfc70d8910036ef20d891029dee76d8910014ee76d8910006ef65d8910006ee65d8910006ed65d8910006ec65d8910006ef64d8910006ee64d8910006ed64d8910006ec64d8910006ef63d8910006ee63d8910006ed63d8910006ec63d89102b7e771d8910087e471d8910087e631d8910087eb70d8910087eb10d89102b7e610d89102b7e410d8910087e810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d89102b6ef71d8910086ee71d8910086ed71d8910086ec71d8910086ef51d8910086ee51d8910086ed51d8910086ec51d8910086ef41d8910086ee41d8910086ed41d8910086ec41d8910086ef31d8910086ee31d8910086ed31d8910086ec31d8910086ef70d89102b6ee70d8910086ed70d89102b6ec70d8910006ef50d89102b6ee50d89102b6ec50d8910006ef40d89102b6ee40d89102b6ec40d89102b6ee30d89102b6ec30d8910086ef10d89102b6ee10d89102b6ec10d8910036ec62589102adfb7058910004ff7558910024fe7558910024fc7558910004ff745891001cfe745891001cfc7458910004ff735891004cfc7358910084ff7258910006ef725891006cff7158910006f77158910054f771589102acff7058910006fb7058910085ee7618910036ee7618910084ee76189100376e75189100376d7518910006ef6518910006ee6518910006ed6518910006ec6518910037ae7418910037ad7418910006ef6418910006ee6418910006ed6418910006ec6418910037ce7318910037cd7318910006ef6318910006ee6318910006ed6318910006ec631891029fe67118910037e571189102a6ef61189102a6e7611891029fe6311891029fe9701891029eef601891029feb10189102a7e610189102a7e4101891029fe81018910004ff7654910004fe7654910004fd7654910004fc76549100267e65549100067d6554910006ef6254910016ec6254910004ff7650910004fe7650910004fd7650910004f
  | 2 => 0xdf0714821006feb2148210057f32148210057e3214821006fe9214821006ff02148210024fe76d95100467e65d951001cfe74d9510004fd74d951001cfc74d951004cfe73d9510004fd73d9510014fe72d9510004fd72d9510014fc72d951002cff71d951000cfe71d951002cfd71d951000cfc71d95101667f51d95101667d51d9510166f631d951002cfe70d951000cfd70d951002cfc70d95100467f50d95100467c6559510005ef7259510035ec72595102c5fb7059510164ff75595100067f7559510004ff745951001cfe745951001cfc7459510004ff735951004cfc7359510004ff7259510006ef7259510004ef7259510014fe7259510014fc7259510006ec7259510014ec72595100467f525951014cff7159510006f7715951014ef631595102c4ff7059510006fb705951001cfe76d911003ebe64d9110024fe75d9110004fd75d9110024fc75d911004cfe73d9110004fd73d9110014fe72d9110004fd72d9110014fc72d911002cff71d911000cfe71d911002cfd71d911000cfc71d9110136bf41d9110136bd41d9110136f631d911002cfe70d911000cfd70d911002cfc70d911003ebf40d911003ebc6459110005ef7259110035ec72591102bdfb7059110004ff7559110024fe7559110024fc7559110134ff7459110006bf7459110004ff735911004cfc7359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec725911003ebf425911011cff7159110006f7715911011ef631591102bcff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc765511003f3c5455110296ec625511004cfe76d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10014fe72d8d10004fd72d8d10014fc72d8d1002cff71d8d1000cfe71d8d1002cfd71d8d1000cfc71d8d100dedf31d8d100dedd31d8d1002cfe70d8d1002cfc70d8d10006df6398d10035ee7298d10005ed7298d100bdf97098d10005ef7258d10035ec7258d100fdfb7058d10004ff7558d10024fe7558d10024fc7558d10004ff7458d1001cfe7458d1001cfc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d100bcff7158d10006f77158d100fcff7058d10006fb7058d100dcfe7618d1004ede6318d10006dd6318d1004cff7694d10004fe7694d10004fd7694d1004cfc7694d1027eec6294d1000df67194d10005f57194d10004ff7654d10004fe7654d10004fd7654d10004fc7654d10005bf7454d1003dbc7454d10266ec6254d1004cff7690d10004fe7690d10004fd7690d1004cfc7690d1024eec6290d1000df67190d10005f57190d10004ff7650d10004fe765
  | 3 => 0xf634c12004edc634c120005ef724c120015ec724c120007cd324c120006f7614c1200bef4614c12002e7f7559610004ff745961001cfe745961001cfc74596100067e54596100667c5459610004ff735961004cfc73596100667f5359610004ff7259610014fe7259610014fc72596100667f525961014e7f515961014e7d515961002cff705961002cfe705961002cfd705961002cfc705961002e7e505961002e7c5059610004ff7559210024fe7559210024fc755921002ebf7459210006bf545921005ebc5459210004ff735921004cfc735921005ebf4359210004ff7259210014fe7259210014fc725921005ebf425921011ebf415921011ebd415921002cff705921002cfe705921002cfd705921002cfc705921002ebe405921002ebc4059210004ff765521002cfe7655210004fd765521002cfc765521005f3c5455210004ff7558e10024fe7558e10024fc7558e10004ff7458e1001cfe7458e1001cfc7458e1002edf7358e10004ff7258e10014fe7258e10014fc7258e100bedf3158e100bedd3158e10006f72158e100bef42158e1002cff7058e1002cfe7058e1002cfd7058e1002cfc7058e1002ede3058e1002edc3058e1002ef71058e1002ef51058e1004cff7694e1002cfe7694e10004fd7694e1002cfc7694e10004ff7654e1002cfe7654e10004fd7654e1002cfc7654e100267e6554e100067d6554e10005bf7454e1005dbc7454e1004cff7690e1002cfe7690e10004fd7690e1002cfc7690e10004ff7650e1002cfe7650e10004fd7650e1002cfc7650e100057f7550e100657c7550e1001ebe6450e10006bd6450e10004ff7558a10024fe7558a10024fc7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a1004cfc7358a1002eef7258a10056ee3258a10056f77158a1006eef2158a10056f72158a1006eed2158a1006ef42158a1002cff7058a1002cfe7058a1002cfd7058a1002cfc7058a1002eee2058a1002eec2058a1002ef71058a1002ef51058a10004ff7654a1002cfe7654a10004fd7654a1002cfc7654a100267e6554a100067d6554a10005f77154a1000df47154a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a1001ebe6450a10006bd6450a10005f77150a1000df47150a1004cff76cca1002cfe76cca10004fd76cca1002cfc76cca1004ede63cca10006dd63cca1000df671cca10005f571cca10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca1004ede634ca10006dd634ca10016ee624ca10006ed624ca10005f7714ca1000df4714ca101dfe4214ca1002dfb76482102cefb764821002feb724821002feb6248210016fa624821002ef8624821002fe86248210057ea3248210007e93248210057f3714821000dfa714821000df8714821006ff07148210
  | 4 => 0x8520006f474d8520006f754d8520006f654d8520006f554d8520006f454d8520006f773d8520006f673d8520006f573d8520006f473d8520006f753d8520006f653d8520006f553d8520006f453d8520006f743d8520006f643d8520006f543d8520006f443d85202def772d852006ef672d8520056f472d8520056f752d8520056f652d8520056f552d8520056f452d8520056f742d8520056f642d8520056f542d8520056f442d8520056f732d8520056f632d8520056f532d8520056f432d8520056f770d85202def670d8520056f570d85202def470d8520006f750d85202def650d85202def450d8520006f740d85202def640d85202def440d85202def630d85202def430d8520056f720d85202def620d85202def420d852006ef461585202d5fb7058520055f6761852006ef6761852006f76751852006f757518520006f76518520006f66518520006f56518520006f4651852006fb6741852006fb57418520006f76418520006f66418520006f56418520006f4641852006fd6731852006fd57318520006f76318520006f66318520006f56318520006f4631852006fe6721852006fe572185202a6f762185202a6e762185202cfe63218520007e5321852006ff170185202aef760185202cff320185202a7e620185202a7e420185202cff02018520004ff7654520004fe7654520004fc76545200267e65545200067d6554520006f7615452000ef46154520004ff7650520004fe7650520004fc765052001ebe6450520006bd6450520006f7615052000ef46150520004fe76cc520004fd76cc52004cfc76cc52004ede63cc520006dd63cc520015ee72cc520005ed72cc520007cd32cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c52004ede634c520006dd634c520015ee724c520007cd324c520006f7614c52000ef4614c52018fe7214c52002dec764852000eec764852002cec7648520005ef7348520005ed7348520015ef7148520017e77148520007e7614852000eee614852000eec614852006fe4614852000ee46148520007eb704852002dee704852002dec7048520007e87048520016ef6048520017eb604852006fe71048520024ff7654120014fe7654120154fd7654120014fc76541200067f65541200267c6554120005ef7254120015ec7254120006f7615412014ef4615412002fe8205412001cff7650120014fe7650120124fd7650120014fc7650120006bf645012001ebc6450120005ef7250120015ec7250120006f7615012011ef4615012002fe82050120014fe76cc120014fc76cc120006df63cc12004edc63cc120015ee72cc120005ed72cc120007cd32cc120006f761cc1200fef461cc12002fe820cc12004cff764c120014fe764c1200c4fd764c120014fc764c120006d
  | 5 => 0x124ff7259120006ef7259120126ee3259120004ff7159120006f77159120004f7715912000cfe715912000cfc7159120006f4715912000cf47159120076bf41591202e4ff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc76551200773c545512028ef4615512004cfe76d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d2002cff72d8d20014fe72d8d2002cfd72d8d20014fc72d8d200e6df32d8d200e6dd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006df6398d2006df67198d20005f57198d200c5f97098d20005f77158d2006df47158d20105fb7058d20004ff7558d20024fe7558d20024fc7558d20004ff7458d2001cfe7458d2001cfc7458d20006df7358d200c4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d20104ff7058d20006fb7058d200e4fe7618d2004ede6318d20006dd6318d2004cff7694d20004fe7694d20004fd7694d2004cfc7694d20015ee7294d20005ed7294d20276f46194d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20005bf7454d20075bc7454d2025ef46154d2004cff7690d20004fe7690d20004fd7690d2004cfc7690d20015ee7290d20005ed7290d20246f46190d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d2007d7c7550d2022ef46150d2002dec764c92004eec764c92002cec764c920006ef654c920006ed654c920006ef644c920006ed644c920015ef734c920017cf734c920007cf634c92004eee634c92004eec634c920007cc634c920005ef714c9201deee614c9201deec614c9201dee4614c920007eb704c92002dee704c92002dec704c920007e8704c92002de8704c920016ef604c920017eb604c92000cfe76d852006ef661d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d852004cfe73d8520004fd73d852002cfd72d852000cfc72d8520006f751d852006ef651d852006ef451d8520006f741d852006ef641d852006ef441d852006ef631d852006ef431d852006ef621d8520056f521d852002cfe70d8520014fd70d852002cfc70d852006ef710d852006df676d852000cf676d8520006f765d8520006f665d8520006f565d8520006f465d8520006f764d8520006f664d8520006f564d8520006f464d8520006f763d8520006f663d8520006f563d8520006f463d85202dfe772d8520057e472d8520057e632d8520007e532d8520057f370d8520057f320d85202dfe620d85202dfe420d8520057f020d8520006f775d8520006f675d8520006f575d8520006f475d8520006f774d8520006f674d8520006f574d
  | 6 => 0xc5455220004ff7558e20024fe7558e20024fc7558e20004ff7458e2001cfe7458e2001cfc7458e2002edf7358e200c6df3258e200c6dd3258e20004ff7158e2000cfe7158e2000cfc7158e20006ee2158e200c6ec2158e2002cfe7058e2002cfc7058e2002ede3058e2002edc3058e2002eef2058e2002eed2058e2004cff7694e2002cfe7694e20004fd7694e2002cfc7694e20004ff7654e2002cfe7654e20004fd7654e2002cfc7654e200267e6554e200067d6554e20005bf7454e2008dbc7454e2004cff7690e2002cfe7690e20004fd7690e2002cfc7690e20004ff7650e2002cfe7650e20004fd7650e2002cfc7650e200057f7550e200957c7550e2001ebe6450e20006bd6450e20004ff7558620024fe7558620024fc7558620004ff745862001cfe745862001cfc7458620004ff735862004cfc735862002ef77158620086f63158620086ee2158620086f62158620036f52158620086ec215862002cff705862002cfe705862002cfd705862002cfc705862002eef205862002eed205862002ef6105862002ef41058620004ff7654620004fd765462002cfc76546200267e65546200067d6554620005ef7254620015ec7254620004ff7650620004fd765062002cfc765062001ebe6450620006bd6450620005ef7250620015ec725062004cff76cc62002cfe76cc620004fd76cc62004ede63cc620006dd63cc620015ee72cc620005ed72cc620004ff764c620004fd764c62002cfc764c62004ede634c620006dd634c620005ef724c620015ec724c62000ef6614c620006f5614c620087e4214c620024fe76d952007e7e65d952001cfe74d9520004fd74d952001cfc74d952004cfe73d9520004fd73d952002cff72d9520014fe72d952002cfd72d9520014fc72d952016e7f52d952016e7d52d952016eee32d952000cfe71d9520004fd71d952000cfc71d9520014fd70d952007e7f50d952007e7c6559520005f7715952006df471595202edfb705952016cff75595200067f7559520004ff745952001cfe745952001cfc7459520004ff735952004cfc7359520154ff7259520006ef7259520156ee3259520004ff7159520006f77159520004f7715952000cfe715952000cfc7159520006f4715952000cf4715952007e7f51595202ecff7059520006fb705952001cfe76d9120076be64d9120024fe75d9120004fd75d9120024fc75d912004cfe73d9120004fd73d912002cff72d9120014fe72d912002cfd72d9120014fc72d912013ebf42d912013ebd42d912013eee32d912000cfe71d9120004fd71d912000cfc71d9120014fd70d9120076bf40d9120076bc6459120005f7715912006df471591202e5fb7059120004ff7559120024fe7559120024fc755912013cff7459120006bf7459120004ff735912004cfc7359120
  | 7 => 0x830006bd6450830016ee6250830006ed625083020ef66150830004ff7558430024fe7558430024fc7558430004ff745843001cfe745843001cfc745843000cfd7358430004ff7258430014fe7258430014fc725843002cff715843002ef77158430006f7515843009ef6515843009ef45158430006f7415843009ef6415843009ef4415843004ef7315843004ef43158430006f7215843009ef6215843009ef4215843002cfc705843002edf305843002edd305843002ef6105843002ef41058430006f77558430006f67558430006f57558430006f47558430006f77458430006f67458430006f57458430006f47458430006f75458430006f65458430006f55458430006f4545843004ef7735843004ef6735843004ef4735843004ef7535843004ef6535843004ef5535843004ef4535843004ef7435843004ef6435843004ef5435843004ef44358430006f77258430006f67258430006f57258430006f47258430006f75258430006f65258430006f55258430006f45258430006f74258430006f64258430006f54258430006f4425843004ef7325843004ef6325843004ef5325843004ef4325843002ef7705843002ef6705843002ef4705843002ef7505843002ef6505843002ef5505843002ef4505843002ef7405843002ef6405843002ef5405843002ef4405843002ef7305843002ed7305843002ef6305843002ef5305843002ed5305843002ef4305843002ef7205843002ef6205843002ef5205843002ef42058430004ff7654430004fd765443002cfc76544300267e65544300067d65544301d6be6454430006bd64544301ceee6254430006ed625443000ef66154430006f56154430004ff7650430004fd765043002cfc76504301c67e65504300067d655043001ebe6450430006bd64504301beee6250430006ed625043000ef66150430006f56150430004ff7648430004fd764843002cfc76484301867e65484300067d654843017ebe6448430006bd6448430016ee6248430006ed624843000ef66148430006f5614843009fe42148430005fb704843002df8704843002e7f7559620004ff745962001cfe745962001cfc74596200067e54596200967c5459620004ff735962004cfc73596200967f53596201567f52596201567d5259620004ff715962000cfe715962000cfc71596200967f515962002cfe705962002cfc705962002e7e505962002e7c5059620004ff7559220024fe7559220024fc755922002ebf7459220006bf545922008ebc5459220004ff735922004cfc735922008ebf4359220126bf4259220126bd4259220004ff715922000cfe715922000cfc715922008ebf415922002cfe705922002cfc705922002ebe405922002ebc4059220004ff765522002cfe7655220004fd765522002cfc765522008f3
  | 8 => 0x6bc755903004ebf735903004ebe735903004ebd735903004ebc735903004ebf535903004ebe535903004ebd535903004ebc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006be5259030006bc525903004ebf325903004ebe325903004ebd325903004ebc3259030006bf7159030006be7159030006bd7159030006bc7159030006bf5159030006be5159030006bc515903004ebf315903004ebe315903004ebd315903004ebc3159030006bf2159030006be2159030006bc215903002ebf705903002ebe705903002ebd705903002ebc705903002ebf505903002ebe505903002ebd505903002ebc505903002ebf305903002ebe305903002eba305903002ebd305903004eb9305903002ebc305903002ebf205903002ebe205903002ebd205903002ebc205903002ebf105903002ebe105903002ebd105903002ebc1059030004ff765503002cfe7655030004fd765503002cfc76550300267e65550300067d655503001ebe6455030006bd64550300af3c5455030005df735503004ddc7355030296ee625503028ef66155030004ff7558830024fe7558830024fc7558830004ff745883001cfe745883001cfc7458830014fd735883002cff725883002eef7258830006ef52588300a6ee52588300a6ec5258830006ef42588300a6ee42588300a6ec425883004eef325883004eec3258830004ff715883000cfe715883000cfc71588300a6ef2158830006ee21588300a6ec215883002cfc705883002edf305883002edd305883002eee205883002eec2058830006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef5458830006ee5458830006ed5458830006ec545883004eef735883004eee735883004eec735883004eef535883004eee535883004eed535883004eec535883004eef435883004eee435883004eed435883004eec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef5158830006ee5158830006ec5158830006ef4158830006ee4158830006ec415883004eef315883004eee315883004eed315883004eec315883002eef705883002eee705883002eec705883002eef505883002eee505883002eed505883002eec505883002eef405883002eee405883002eed405883002eec405883002eef305883002ecf305883002eee305883002eed305883002ecd305883002eec305883002eef105883002eee105883002eed105883002eec1058830004ff7654830004fd765483002cfc76548300267e65548300067d6554830226be6454830006bd6454830016ee6254830006ed625483021ef66154830004ff7650830004fd765083002cfc76508302167e65508300067d655083001ebe645
  | 9 => 0xb639013002fdb6390130007db3290130007d93290130007db3190130007d9319013001cff76501300ccfd765013004cfc7650130006bf645013001ebc6450130005df735013004ddc735013002fb8405013004df8765013001ef8765013004cf87650130005fb7550130005f97550130006fb6550130006f9655013002dfb745013002fbb7450130007bb645013001efa645013001ef864501300cfb864501302f7bb54501300cfb85450130007db735013004dfa735013004df87350130007d8735013002efb635013002fdb63501300cfbb4350130007b943501300cfbb4250130007b94250130007db3250130007d932501300cfbb4150130007b94150130007db3150130007d9315013002cff755943002e7f7559430004ff745943001cfe745943001cfc74594300b67f54594300067e54594300b67c545943004cff735943004cfe735943004cfd735943004cfc735943004e7e535943004e7c5359430004ff7259430014fe7259430014fc72594300b67f52594300067e52594300b67c5259430004ff715943000cfe715943000cfc71594300b67f51594300067e51594300b67c515943002cfe705943002cfc705943002e7e505943002e7c505943002efa305943004ef930594300067f74594300067e74594300067d74594300067c745943004e7f735943004e7e735943004e7d735943004e7c735943004e7f435943004e7e435943004e7d435943004e7c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067c425943004e7f325943004e7e325943004e7d325943004e7c32594300067f71594300067e71594300067d71594300067c71594300067f41594300067e41594300067c415943004e7f315943004e7e315943004e7d315943004e7c31594300067f21594300067e21594300067c215943002e7f705943002e7e705943002e7d705943002e7c705943002e7f405943002e7e405943002e7d405943002e7c405943002e7f305943002e7e305943002e7a305943002e7d305943004e79305943002e7c305943002e7f205943002e7e205943002e7d205943002e7c205943002e7f105943002e7e105943002e7d105943002e7c1059430004ff7559030024fe7559030024fc755903002cff745903002ebf7459030006bf54590300aebe54590300aebc545903004cff735903004cfe735903004cfd735903004cfc735903004ebe435903004ebc4359030004ff7259030014fe7259030014fc72590300aebf4259030006be42590300aebc4259030004ff715903000cfe715903000cfc71590300aebf4159030006be41590300aebc415903002cfe705903002cfc705903002ebe405903002ebc405903002efa305903004ef93059030006bf7559030006be7559030006bd7559030
  | 10 => 0xc93004ddf724c93004fcf724c930007cf624c930016de624c930016dc624c9300c7cc624c9300c7ce524c930007cd524c9300c7ce424c930007cd424c930005df714c93030fce214c9300c7cc214c930007db704c93002dde704c93002ddc704c930007d8704c93004edf604c93004fdb604c9300c7cf204c93000cfe76d85300bef661d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853002cfd73d853000cfc73d8530014fe72d8530004fd72d8530014fc72d8530006df32d8530006dd32d85300bef631d8530006f721d85300bef421d853004cfd70d85300bef710d8530005ef72585300c5ec72585300bef46158530004ff7654530004fe7654530004fc7654530004ff7650530004fe7650530004fc7650530005de76cc53004ede76cc53004fce72cc530005dd72cc53004fcd72cc530005cd72cc530006df62cc5300bddd71cc53000ede61cc53000edc61cc53002dde70cc53002ddc70cc53004edf60cc53004fdb60cc53002cfc764c530006f7614c53000ef4614c53004fd4314c530005fb704c53002df8704c53002ddc764c53000edc764c53002cdc764c530005df724c530006df624c53004ddf714c53004fd7714c530007d7614c53000ede614c53000edc614c5300bfd4614c5300bfd6514c530007d5514c5300bfd6414c530007d5414c530307d7214c5300bfd4214c530007db704c53002dde704c53002ddc704c530007d8704c53004edf604c53004fdb604c5300bfd7104c530004ff7648530004fe7648530004fc764853004dde7348530005dd73485300bfe42148530005fa769413002efa76941300d5f97594130026fa6594130026f8659413002fba7494130005f9749413002fb97494130005b97494130006fb6494130006f9649413004dfa739413002df8739413002efb639413002fdb6394130007db3294130007d93294130007db3194130007d93194130024ff76541300d4fd765413004cfc76541300067f65541300267c6554130005df735413004ddc735413002f78505413004df87654130026f8765413004cf8765413002dfb755413002f7b75541300077b6554130026fa6554130026f865541300d7786554130005fb7454130006fb6454130006f964541302ff7a54541300d7785454130007db735413004dfa735413004df87354130007d8735413002efb635413002fdb63541300d77b53541300077953541300d77b5254130007795254130007db3254130007d932541300d77b5154130007795154130007db3154130007d93154130005fa769013002efa769013002dfb759013002f7a7590130005f9759013002f797590130005797590130006fb6590130006f965901300cdf9749013001efa649013001ef8649013004dfa739013002df8739013002ef
  | 11 => 0x2dfb76502300aefb7650230005fb7550230005f9755023002efb6550230006f9655023002fbb745023002fbb645023001efa645023002ef8645023002fb86450230317bb54502300efb8545023004dfa735023004df873502300efbb4350230007b943502300efbb4250230007b942502300efbb4150230007b94150230024fe76d95300d67e65d953001cfe74d9530004fd74d953001cfc74d95300067e54d95300d67c54d953004cfe73d953002cfd73d953004cfc73d95300d67f53d9530014fe72d9530004fd72d9530014fc72d953000cfe71d9530004fd71d953000cfc71d953004cfd70d95300d67f50d95300d67c6559530005bf74595300cdbc74595300d4ff75595300067f7559530004ff7459530006bf7459530004bf745953001cfe745953001cfc7459530006bc745953001cbc74595300f4ff7359530006df7359530004ff7259530014fe7259530014fc7259530004ff715953000cfe715953000cfc7159530114ff7059530006fb705953001cfe76d91300cebe64d9130024fe75d9130004fd75d9130024fc75d9130006bf54d91300cebc54d913004cfe73d913002cfd73d913004cfc73d91300cebf43d9130014fe72d9130004fd72d9130014fc72d913000cfe71d9130004fd71d913000cfc71d913004cfd70d91300cebf40d91300057f75591300d57c75591300cebc6459130004ff75591300067f75591300047f7559130024fe7559130024fc75591300067c75591300247c75591300ccff7459130006bf74591300ecff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff715913000cfe715913000cfc715913010cff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc76551300cf3c545513002cfc7654d300067f6554d300267c6554d30005bf7454d300cdbc7454d30005fb7054d3002df87054d3002cfc7650d300057f7550d300d57c7550d30006bf6450d3001ebc6450d30005fb7050d3002df87050d30014fe76d89300c6ee62d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893002cfd73d8930014fc73d89300c6ee32d893000cfe71d8930004fd71d893000cfc71d8930006ee21d89300c6ec21d893004cfd70d89300c6ef20d89300c6ec6258930005f771589300bdf47158930004ff7654930004fe7654930004fc7654930004ff7650930004fe7650930004fc7650930005de76cc93004ede76cc9300c5dd72cc930016de62cc930016dc62cc93004fd671cc930005dd71cc93004fd571cc930005d571cc93002dde70cc93002ddc70cc93004edf60cc93004fdb60cc93002cfc764c930006ef624c930016ec624c93004fcc324c930005fb704c93002df8704c93002ddc764c930016dc764c93002cdc764
  | 12 => 0xd6450330005df735033004ddc735033002e7f7559630004ff745963001cfe745963001cfc74596300067e54596300f67c54596300f67f5359630004ff7259630014fe7259630014fc72596300f67f5259630004ff715963000cfe715963000cfc71596300f67f515963002cfc705963002e7e505963002e7c505963002efa4059630004ff7559230024fe7559230024fc755923002ebf7459230006bf54592300eebc54592300eebf4359230004ff7259230014fe7259230014fc72592300eebf4259230004ff715923000cfe715923000cfc71592300eebf415923002cfc705923002efa505923002ebe405923002ebc4059230004ff765523002cfe7655230004fd765523002cfc76552300ef3c5455230005df735523004ddc735523002dfa705523004efb3058e3002ede3058e3002edc3058e3002ef83058e30024ff7654e3002cfc7654e300267e6554e300067d6554e30005bf7454e300edbc7454e3004f5c5354e30005fb7054e3002df87054e3001cff7650e3002cfc7650e300057f7550e300f57c7550e3001ebe6450e30006bd6450e3004f9c4350e30005fb7050e3002df87050e30004ff7558a30024fe7558a30024fc7558a30004ff7458a3001cfe7458a3001cfc7458a3002eef7258a300e6ee3258a30004ff7158a30006f77158a30004f77158a3000cfe7158a3000cfc7158a30006f47158a3000cf47158a300e6ef2158a3002cfc7058a3002edf3058a3002edd3058a3002eee2058a3002eec2058a30004ff7654a30004fd7654a3002cfc7654a300267e6554a300067d6554a30004ff7650a30004fd7650a3002cfc7650a3001ebe6450a30006bd6450a30014ff764ca30016ee624ca30006ed624ca30005fb704ca3002df8704ca30004ff7558630024fe7558630024fc7558630004ff745863001cfe745863001cfc7458630004ff7258630006ef7258630004ef7258630014fe7258630014fc7258630006ec7258630014ec725863002ef771586300def631586300def6215863002cfc705863002edf305863002edd305863002ef6105863002ef41058630004ff7654630004fd765463002cfc76546300267e65546300067d6554630004ff7650630004fd765063002cfc765063001ebe6450630006bd645063000cff764c63000ef6614c630006f5614c630005fb704c63002df8704c630004ff7648630004fd764863002cfc7648630016ee6248630006ed624863000ef66148630006f561486300dfe4214863002dfb76542300b6fb765423002f7b755423002f7b6554230026fa655423002ef8655423002f786554230005fb745423002efb6454230006f9645423031f7a54542300f778545423004dfa735423004df873542300f77b53542300077953542300f77b52542300077952542300f77b5154230007795154230
  | 13 => 0x414012f7b525414000779525414015fbb4254140007b9425414012f7b515414000779515414015fbb4154140007b9415414004e7f7559730004ff7459730006bf7459730004bf745973001cfe745973001cfc7459730006bc745973001cbc74597301167f545973002cfc735973004e7e535973004e7c5359730004ff7259730014fe7259730014fc7259730004ff715973000cfe715973000cfc71597301167f505973004efa305973004ef93059730004ff75593300067f75593300047f7559330024fe7559330024fc75593300067c75593300247c755933004ebf745933010ebe545933002cfc735933004ebe435933004ebc4359330004ff7259330014fe7259330014fc7259330004ff715933000cfe715933000cfc715933010ebf405933004efa305933004ef93059330004ff765533004cfe7655330004fd765533004cfc76553300267e65553300067d655533001ebe6455330006bd645533010f3c5455330004ff7558b30024fe7558b30024fc7558b30004ff7458b3001cfe7458b3001cfc7458b3002cfc7358b3004eef7258b30106ee5258b30106ee4258b3004eef3258b3004eec3258b30004ff7158b3000cfe7158b3000cfc7158b3004edf3158b30006ee2158b30106ec2158b30106ef2058b30004ff7654b30004fd7654b3004cfc7654b30016ee6254b30006ed6254b30004ff7650b30004fd7650b3004cfc7650b30016ee6250b30006ed6250b3004ddf764cb300a6df764cb3004fcf724cb3004fcf624cb30016de624cb30016dc624cb3004fcc624cb30107ce524cb30007cd524cb30107ce424cb30007cd424cb30005df714cb3032fce214cb30107cc214cb3002dde704cb3002ddc704cb30107cf204cb30004ff7558730024fe7558730024fc7558730004ff745873001cfe745873001cfc745873002cfc7358730004ff7258730014fe7258730014fc725873004edf3258730006dd325873004ef771587300fef651587300fef6415873004ef7315873004ef43158730006f721587300fef421587300fef71058730004ff7654730004fd765473004cfc765473000ef66154730006f56154730004ff7650730004fd765073004cfc765073000ef66150730006f5615073004ddf764c73009edf764c730005df724c730006dd624c73004fd7714c73004fd7614c73000ede614c73000edc614c73004fd4614c7300ffd6514c730007d5514c7300ffd6414c730007d5414c730327d7214c7300ffd4214c73002dde704c73002ddc704c7300ffd7104c730004ff7648730004fd764873004cfc764873004dde7348730005dd73487300ffe42148730005fb704873002df87048730024ff765433004cfc76543300267e65543300067d6554330005df735433004ddc735433001cff765033004cfc765033001ebe6450330006b
  | 14 => 0x2cbc765094012dbe755094012dbc7550940005bf735094001dbf725094001faf7250940007af6250940016be6250940016bc6250940127ac6250940127ae5250940007ad5250940127ae3250940005bf7150940007bb705094002dbe705094002dbc7050940007b8705094001ebf605094001fbb6050940004fe76cc940004fd76cc94004cfc76cc94001dbe74cc940005bd74cc94011df671cc940005f571cc94002dfa70cc940005f970cc940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940016ee624c940007ad424c94000cfe76d854011ef661d8540024fe75d8540004fd75d8540024fc75d854002cfd74d854000cfc74d854004cfe73d8540004fd73d8540014fe72d8540004fd72d8540014fc72d854005ebf42d8540006bd42d854011ef641d854005ef541d8540006f721d854011ef421d854001cfd70d854011ef710d8540005ef7258540125ec725854011ef4615854033dfb7058540004ff7654540004fe7654540004fc7654540005bf745454001dbc745454002dbc765054000ebc765054002cbc765054012dbe755054012dbc7550540005bf7350540005bf7250540006bf625054001dbf715054001fb77150540007b7615054000ebe615054000ebc615054011fb4615054011fb65150540007b5515054011fb63150540007bb705054002dbe705054002dbc7050540007b8705054001ebf605054001fbb6050540004fe76cc540004fd76cc54004cfc76cc54001dbe74cc540005bd74cc540125ee72cc540005ed72cc54002dfa70cc540005f970cc540004ff764c540004fe764c540004fc764c54001dbe744c540005bd744c54000ef6614c540007b5414c540004ff7648540004fe7648540004fc764854001dbe7448540005bd744854011fe42148540005fb704854002df87048540335fa769414002efa769414015df97594140026fa6594140026f8659414001dfa749414002fba749414001dba749414002fb9749414002df8749414002efb649414002fbb649414012fbb5494140177b85494140005f97394140006fb6394140177bb4394140007b94394140177bb4294140007b94294140177bb4194140007b94194140024ff765414001cfe765414015cfd765414001cfc76541400067f65541400267c6554140005bf745414001dbc745414015f3c545414002f78505414002fb8405414001df87654140026f8765414001cf8765414002dfb755414002f7b75541400077b6554140026fa6554140026f8655414012f786554140007bb745414001dfa745414001df8745414015fb8745414002efb645414002fbb645414012fbb545414015f7a545414015f78545414015fb8545414015f385454140005fb7354140006fb635414012f7b535414000779535414015fbb4354140007b9435
  | 15 => 0x8655424001dfa745424001df8745424015f7a545424015f785454240005fb7354240006f963542401477b53542400077953542401477b52542400077952542401477b5154240007795154240024fe76d954012e7e65d954001dbe74d954002dbd74d954012f3f54d954002cff74d954001cfe74d954002cfd74d954012ebd74d954002cbd74d954001cfc74d95401767f54d954012ebf54d954012e3f54d95401767d54d9540176bc54d954004cfe73d9540004fd73d954012e7c53d9540176bf43d9540014fe72d9540004fd72d9540014fc72d954000cfe71d9540004fd71d954000cfc71d954001cfd70d954012e7f50d954012e7c655954015f3c5459540005df7359540005dc735954034dfb7059540174ff75595400067f755954015cff7459540006bf745954012ebf545954015e7e545954015e7c545954015ebc545954015e3c5459540004ff7359540006df7359540004df735954004cfc7359540006dc735954004cdc735954012e7f535954015ebf4359540004ff7259540014fe7259540014fc7259540004ff715954000cfe715954000cfc715954034cff7059540006fb7059540024fe75d8d40004fd75d8d40024fc75d8d4002cfd74d8d40006df53d8d40006dc53d8d400eede43d8d400eedd43d8d40014fe72d8d40004fd72d8d40014fc72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d40006df6398d400cdf97098d400057f7558d4012d7c7558d4010dfb7058d4012d7e7518d400057d7518d4004ede6318d40006dd6318d40125ee7218d40005ed7218d4011df67118d40005f57118d40004fe7694d40004fd7694d4004cfc7694d400067f6594d400267c6594d4001dbe7494d40005bd7494d402873c5494d4002dfa7094d40005f97094d40004ff7654d40004fe7654d40004fc7654d400267e6554d400067d6554d40005bf7454d4001dbc7454d4012f3f5454d4002cbc7650d400073f7550d4012dbe7550d4012dbc7550d400073c7550d4012d3c7550d40006bf6550d40006bd6550d4001dbf7350d4001f9f7350d400079f6350d4004ebe6350d4004ebc6350d400079c6350d4004e9c6350d400079e5350d400079d5350d40005bf7250d40005bf7150d40007bb7050d4002dbe7050d4002dbc7050d40007b87050d4001ebf6050d4001fbb6050d40014fe76d8940126ee62d8940024fe75d8940004fd75d8940024fc75d894002cfd74d8940014fc74d894004cfe73d8940004fd73d8940126ee42d894008eed42d894000cfe71d8940004fd71d894000cfc71d894008ebf41d8940006ee21d8940126ec21d894001cfd70d8940126ef20d8940126ec6258940005f7715894011df47158940345fb7058940004ff7654940004fe7654940004fc7654940005bf745494001dbc745494002dbc7650940016bc7650940
  | 16 => 0x964015e7f415964015e7e415964015e7d415964015e7c41596400067e31596400067c31596400067f21596400067e21596400067c215964002e7f705964002e7e705964002e7d705964002e7c705964002e7f405964002e7e405964002e7d405964002e7c405964002e7f305964002e7e305964002e7a305964002e7d305964002e7c305964002e7f205964002e7e205964002e7d205964002e7c205964002e7f105964002e7e105964002e7d105964002e7c1059640004ff7558e40024fe7558e40024fc7558e4002edf7358e400cede4358e400cedd4358e40004ff7258e40014fe7258e40014fc7258e40004ff7158e4000cfe7158e4000cfc7158e4002cfc7058e4002efa5058e4002ebf4058e4002ebd4058e4002ede3058e4002edc3058e4004cff7694e4002cfe7694e40004fd7694e400267e6594e400067d6594e4002dfa7094e40005f97094e40004ff7654e40004fd7654e4002cfc7654e400267e6554e400067d6554e40005bf7454e4001dbc7454e4002dfa7054e40004ff7558a40024fe7558a40024fc7558a40004ff7358a4004cfc7358a4002eef7258a4013eee4258a40076ed4258a4013eee3258a40004ff7158a4000cfe7158a4000cfc7158a4013eef2158a4002cfe7058a4002cfc7058a4002ebf4058a4002ebd4058a4002eee2058a4002eec2058a40004ff7654a40004fd7654a4002cfc7654a400267e6554a400067d6554a4004cff76cca4002cfe76cca40004fd76cca402067e65cca400067d65cca4004ede63cca40006dd63cca40135f671cca40005f571cca4002dfa70cca40005f970cca40004ff764ca40004fd764ca4002cfc764ca401ee7e654ca400067d654ca4004ede634ca40006dd634ca40016ee624ca40006ed624ca40004ff7558640024fe7558640024fc7558640004ff735864004cfc7358640004ff7258640014fe7258640014fc725864002ef77158640136f6415864003ef54158640136f63158640136f6215864002cfe705864002cfc705864002ebf405864002ebd405864002ef6105864002ef41058640004ff7654640004fd765464002cfc76546400267e65546400067d655464004cff76cc64002cfe76cc640004fd76cc6401b67e65cc6400067d65cc64004ede63cc640006dd63cc64013dee72cc640005ed72cc64002dfa70cc640005f970cc640004ff764c640004fd764c64002cfc764c64019e7e654c6400067d654c64004ede634c640006dd634c64000ef6614c640006f5614c640004ff7648640004fd764864002cfc76486401867e65486400067d6548640016ee6248640006ed624864000ef66148640006f56148640137e42148640005fb704864002df8704864002dfb7654240356fb765424002f7b7554240026fa655424002f7a65542400267a655424002f79655424002ef
  | 17 => 0x14df47158950365fb705895002d7c76549500167c765495002c7c765495015d7e745495015d7c74549500057f73549500257f72549500276f72549500076f62549500167e62549500167c62549501576c62549501576e42549501576e32549500057f71549500077b705495002d7e705495002d7c70549500077870549500267f60549500277b6054950004ff7650950004fe7650950004fc76509500057f75509500257c75509500076d5250950004fe76cc950004fd76cc95004cfc76cc9500257e75cc9500057d75cc95014df671cc950005f571cc95002dfa70cc950005f970cc950004ff764c950004fe764c950004fc764c9500257e754c9500057d754c950016ee624c9500076d524c95000cfe76d855014ef661d855002cfd75d855000cfc75d855001cfe74d8550004fd74d855001cfc74d855004cfe73d8550004fd73d8550014fe72d8550004fd72d8550014fc72d85500667f52d85500067d52d855014ef651d8550066f551d8550006f721d855014ef421d8550024fd70d855014ef710d8550005ef7258550155ec725855014ef4615855035dfb705855002d7c765455000e7c765455002c7c765455015d7e745455015d7c74545500057f73545500057f72545500067f62545500257f715455002777715455000777615455000e7e615455000e7c615455014f74615455014f76415455014f7631545500077b705455002d7e705455002d7c70545500077870545500267f60545500277b6054550004ff7650550004fe7650550004fc76505500057f75505500257c7550550007755150550004fe76cc550004fd76cc55004cfc76cc5500257e75cc5500057d75cc550155ee72cc550005ed72cc55002dfa70cc550005f970cc550004ff764c550004fe764c550004fc764c5500257e754c5500057d754c55000ef6614c55000775514c550004ff7648550004fe7648550004fc76485500257e75485500057d754855014fe42148550005fb704855002df8704855002e7f755964015e7f545964015e7d5459640004ff735964004cfc73596401467f53596401467c5359640004ff7259640014fe7259640014fc72596401467f52596400067e52596401467c5259640004ff715964000cfe715964000cfc71596401467f51596400067e51596401467c515964002cfe705964002cfc705964002e7e505964002e7c505964002efa305964015e7f745964015e7e745964015e7d745964015e7c74596400067f73596400067e73596400067d73596400067c735964015e7f435964015e7e435964015e7d435964015e7c43596400067f72596400067e72596400067d72596400067c725964015e7f425964015e7e425964015e7d425964015e7c42596400067e32596400067c32596400067f71596400067e71596400067d71596400067c715
  | 18 => 0xf735865004cfc7358650004ff7258650014fe7258650014fc725865002ef77158650166f65158650046f55158650166f63158650166f6215865002cfe705865002cfc705865002e7f505865002e7d505865002ef6105865002ef41058650004ff7650650004fd765065002cfc765065001ebe6450650006bd645065004cff76cc65002cfe76cc650004fd76cc6501aebe64cc650006bd64cc65004ede63cc650006dd63cc65016dee72cc650005ed72cc65002dfa70cc650005f970cc650004ff764c650004fd764c65002cfc764c650196be644c650006bd644c65004ede634c650006dd634c65000ef6614c650006f5614c650004ff7648650004fd764865002cfc764865017ebe6448650006bd6448650016ee6248650006ed624865000ef66148650006f56148650167e42148650005fb704865002df8704865001cfe76d91500257e75d915015ebe64d915015f3e54d915002cfd75d915002c7d75d915001cfc75d915015e7e54d915015ebe54d915015e3e54d9150146bd54d915015e7c54d915004cfe73d9150004fd73d91501467f53d915015ebc43d9150014fe72d9150004fd72d9150014fc72d915000cfe71d9150004fd71d915000cfc71d9150024fd70d915015ebf40d915015ebc645915015f3c5459150005df7359150005dc735915036dfb705915002cfd75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d500f6de53d8d500f6dd53d8d50006df43d8d50006dc43d8d50014fe72d8d50004fd72d8d50014fc72d8d5000cfe71d8d50004fd71d8d5000cfc71d8d50006df6398d500d5f97098d50005bf7458d5015dbc7458d50115fb7058d5015dbe7418d50005bd7418d5004ede6318d50006dd6318d50155ee7218d50005ed7218d5014df67118d50005f57118d5002c7c7654d500073f7454d5015d7e7454d5015d7c7454d500073c7454d5015d3c7454d500067f6454d500257f7354d500275f7354d500075f6354d5004e7e6354d5004e7c6354d500075c6354d5004e5c6354d500057f7254d500057f7154d500077b7054d5002d7e7054d5002d7c7054d50007787054d500267f6054d500277b6054d50004fe7690d50004fd7690d5004cfc7690d500257e7590d500057d7590d50006bf6490d5001ebc6490d5015f3c5490d500075d5390d5002dfa7090d50005f97090d50004ff7650d50004fe7650d50004fc7650d500057f7550d500257c7550d5001ebe6450d5015f3e5450d500075d5350d50014fe76d8950156ee62d895002cfd75d8950014fc75d895001cfe74d8950004fd74d895001cfc74d895004cfe73d8950004fd73d8950156ee52d8950096ed52d895000cfe71d8950004fd71d895000cfc71d89500967f51d8950006ee21d8950156ec21d8950024fd70d8950156ef20d8950156ec6258950005f77158950
  | 19 => 0x812106fe421581211857e75181210057d751812117dbe7418121005bd7418121005de7318121005dd73181212b6ef62181212def7611812129fe4211812102efa6018121006f9601812102ebf7459250176be545925012ebd5459250004ff735925004cfc7359250176bf4359250176bc4359250004ff7259250014fe7259250014fc7259250176bf4259250006be4259250176bc4259250004ff715925000cfe715925000cfc7159250176bf4159250006be4159250176bc415925002cfe705925002cfc705925002ebe405925002ebc405925002efa305925012ebe755925012ebd7559250176bc7559250006bf7359250006be7359250006bd7359250006bc735925012ebf535925012ebe535925012ebd535925012ebc5359250006bf7259250006be7259250006bd7259250006bc725925012ebf525925012ebe525925012ebd525925012ebc5259250006be3259250006bc3259250006bf7159250006be7159250006bd7159250006bc715925012ebf515925012ebe515925012ebd515925012ebc5159250006be3159250006bc3159250006bf2159250006be2159250006bc215925002ebf705925002ebe705925002ebc705925002ebf505925002ebe505925002ebd505925002ebc505925002ebf305925002ebe305925002eba305925002ebd305925002ebc305925002ebf205925002ebe205925002ebd205925002ebc205925002ebf105925002ebe105925002ebd105925002ebc1059250004ff7458e5001cfe7458e5001cfc7458e5002edf7358e500d6de5358e500d6dd5358e50004ff7258e50014fe7258e50014fc7258e50004ff7158e5000cfe7158e5000cfc7158e5002cfc7058e5002e7f5058e5002e7d5058e5002efa4058e5002ede3058e5002edc3058e5004cff7690e5002cfe7690e50004fd7690e5001ebe6490e50006bd6490e5002dfa7090e50005f97090e50004ff7650e50004fd7650e5002cfc7650e500057f7550e500257c7550e5001ebe6450e50006bd6450e5002dfa7050e50004ff7458a5001cfe7458a5001cfc7458a50004ff7358a5004cfc7358a5002eef7258a5016eee5258a5007eed5258a5016eee3258a50004ff7158a5000cfe7158a5000cfc7158a5016eef2158a5002cfe7058a5002cfc7058a5002e7f5058a5002e7d5058a5002eee2058a5002eec2058a50004ff7650a50004fd7650a5002cfc7650a5001ebe6450a50006bd6450a5004cff76cca5002cfe76cca50004fd76cca501febe64cca50006bd64cca5004ede63cca50006dd63cca50165f671cca50005f571cca5002dfa70cca50005f970cca50004ff764ca50004fd764ca5002cfc764ca501e6be644ca50006bd644ca5004ede634ca50006dd634ca50016ee624ca50006ed624ca50004ff745865001cfe745865001cfc7458650004f
  | 20 => 0x2cfe70d9521004fd70d9521024ff76595211867c65595213adef72595213bdf7715952121fe421595213b4ff75595210067f7559521004ff745952101cfe745952101cfc7459521004ff735952104cfc73595213acff7259521006ef725952121cff7159521006f77159521004ff705952102cfc70595211867f505952101cfe76d912117ebe64d9121397e421d9121024fe75d9121004fd75d9121024fc75d912120cfd74d912104cfe73d9121004fd73d912100cff72d912100cfd72d91213a6bf42d91213a6bd42d9121014ff71d9121014fd71d9121396bf41d9121396bd41d912102cfe70d9121004fd70d912101cff765912117ebc645912138def725912139df7715912120fe42159121004ff7559121024fe7559121024fc7559121394ff7459121006bf7459121004ff735912104cfc735912138cff7259121006ef725912120cff7159121006f77159121004ff705912102cfc705912117ebf4059121004ff7655121004fe7655121004fd7655121004fc765512117f3c545512128fe4215512104cfe76d8d2137fe421d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2100cff72d8d2100cfd72d8d21386df32d8d21386dd32d8d21014ff71d8d21014fd71d8d2137edf31d8d2137edd31d8d21386f721d8d2137eee21d8d2137eec21d8d2137ef421d8d2137ee421d8d2102cfe70d8d21004fd70d8d21386ef20d8d2137ef710d8d211dcfd7698d21006df6398d211dded7298d2118df57198d211f7e42198d2104cff7658d211f5ef7258d211a5f77158d211dfe42158d21005fb7058d21005f87058d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21006df7358d211f4ff7258d21006ef7258d211dcff7158d21006f77158d2118ef72158d211deee2158d211deec2158d211def42158d211dee42158d21004ff7058d21006fb7058d21004fb7058d2102cfc7058d21006f87058d2102cf87058d2118eef2058d211def71058d2137cfe7618d2104ede6318d21006dd6318d21377e42118d2104cff7694d21004fe7694d21004fd7694d2104cfc7694d21277e42194d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21005bf7454d2117dbc7454d2125fe42154d2104cff7690d21004fe7690d21004fd7690d2104cfc7690d21247e42190d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d211857c7550d2122fe42150d2102cfe76d81212afe421d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d812104cfe73d8121004fd73d812100cfd72d8121014fd71d81212d6fa20d81212aefa10d81212b6ef62981212def76198121087e42198121006fb609
  | 21 => 0x571d89311f6ef21d893118ef721d89311f6f421d893102cfe70d8931004fd70d893118eec20d89311f6f710d893118eec62589311dfe42158931005fb7058931005f87058931004ff7654931004fe7654931004fc7654931005f7715493100df47154931004ff7650931004fe7650931004fc7650931005f7715093100df47150931375de76cc93104ede76cc9311dddd72cc931016de62cc931016dc62cc93100dde71cc93104fd671cc93100dd671cc93104fd571cc93100ddc71cc93104edf61cc93104fd761cc9311f7d651cc9311f7d641cc93118fd721cc9311f7d421cc931005dd70cc9311f7d710cc93100cfc764c931006ef624c931016ec624c931005f7714c93100df4714c9311dfe4214c93100ddc764c931016dc764c93100cdc764c93104ddf724c93104fcf724c931007cf624c931016de624c931016dc624c93118fcc624c93118fce524c931007cd524c93118fce424c931007cd424c931007d7714c93100dde714c93100ddc714c9311dfd4714c93104edf614c93104fd7614c9311dfd6514c9311dfd6414c93118fd7214c9311dfce214c9311dfcc214c9311dfd4214c9311dfc4214c931005df704c93118fcf204c9311dfd7104c93104df47654531026f4765453104cf4765453100df7755453100f777554531007776554531026f66554531026f4655453119f746554531005f77454531006f76454531006f56454531007d7735453104df6735453104df47354531007d4735453100ef7635453100fd7635453118df6725453118df4725453119f775254531007755254531007d73254531007d53254531005f7705453119f77505453104df4765053101ef4765053104cf47650531005f77550531005f57550531006f76550531006f5655053100df7745053100fb77450531007b7645053101ef6645053101ef46450531197b46450531007d7735053104df6735053104df47350531007d4735053100ef7635053100fd7635053118df6725053118df47250531197b74250531007b54250531007d73250531007d53250531005f77050531197b74050531024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d8131014fe72d8131004fd72d8131014fc72d8131006df32d8131006dd32d813104cfd71d8131006fb20d8131006f820d81310fefa10d8131006fb6098131005ef725813118dec725813119d7e75181310057d7518131195be7418131005bd741813118dee7218131005ed721813102efa6018131006f96018131024fe76d95211867e65d95213b7e421d952121cfd75d952101cfe74d9521004fd74d952101cfc74d952104cfe73d9521004fd73d952100cff72d952100cfd72d95213c67f52d95213c67d52d9521014ff71d9521014fd71d95213b67f51d95213b67d51d9521
  | 22 => 0xb3104cfc7650b31016ee6250b31006ed6250b3104ddf764cb313dedf764cb3104fcf724cb31016de624cb3104fce624cb31016ce624cb3104fcd624cb31016dc624cb311a7ce524cb31007cd524cb311a7ce424cb31007cd424cb3100dde714cb3100ddc714cb311dfce214cb311dfcc214cb31005df704cb311a7cf204cb31004ff7558331024fe7558331024fc7558331004ff745833101cfe745833101cfc745833100cfc7358331004ff7258331014fe7258331014fc725833104edf3258331006dd325833104ef6315833104ef5315833104efb705833104efb305833104ef830583310befa1058331024fe76d953119e7e65d953101cfe74d9531004fd74d953101cfc74d95310067e54d953119e7c54d953100cfd73d953119e7f53d9531014fe72d9531004fd72d9531014fc72d953104cff71d953104cfd71d95312767f51d95312767d51d9531276f641d953102cfe70d9531004fd70d953119e7c6559531005bf7459531195bc74595313d5df7359531274ff75595310067f7559531004ff7459531006bf7459531004bf745953101cfe745953101cfc7459531006bc745953101cbc74595313d4ff7359531006df7359531004ff7259531014fe7259531014fc725953125cff7159531006f7715953125ef64159531004ff705953102cfc705953119e7f505953101cfe76d9131196be64d9131024fe75d9131004fd75d9131024fc75d9131006bf54d9131196bc54d913100cfd73d9131196bf43d9131014fe72d9131004fd72d9131014fc72d913104cff71d913104cfd71d9131246f651d9131246bf41d9131246bd41d913102cfe70d9131004fd70d91310057f755913119d7c7559131196bc64591313cddf7359131004ff75591310067f75591310047f7559131024fe7559131024fc75591310067c75591310247c7559131244ff7459131006bf74591313ccff7359131006df7359131004ff7259131014fe7259131014fc725913122cff7159131006f7715913122ef65159131004ff705913102cfc7059131196bf4059131004ff7655131004fe7655131004fd7655131004fc76551311973c5455131005df735513104ddc735513100df67155131024ff7654d3100cfe7654d3125cfd7654d3100cfc7654d310067f6554d310267c6554d31005bf7454d31195bc7454d3104f5c5354d31005f77154d3100df47154d3101cff7650d3100cfe7650d3122cfd7650d3100cfc7650d310057f7550d3119d7c7550d31006bf6450d3101ebc6450d3104f9c4350d31005f77150d3100df47150d31014fe76d893118eee62d893100df671d893104df571d893118fe721d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d893100cfd73d893118eee32d893104cfd71d893118ef571d893104cf
  | 23 => 0x1d7b4745454100ef7645454100fb76454541005f77354541006f763545411c77752545410077552545411d7b74254541007b542545411c77750545411d7b7405454102cfe76d8141024fe75d8141004fd75d8141024fc75d814100cfd74d814104cfe73d8141004fd73d8141014fe72d8141004fd72d8141014fc72d814133ebf42d8141006bd42d814101cfd71d81412bef631d814133efa40d81412befa10d81411c57e75981410057d7598141006fb6098141005ef72581411bdec725814102efa6018141006f9601814104e7f7559731004ff745973101cfe745973101cfc74597311b67f545973100cfe735973100cfc735973104e7e535973104e7c5359731004ff7259731014fe7259731014fc725973125e7f515973125e7d515973104ef6315973104ef53159731004ff705973102cfc70597311b67f5059731004ff7559331024fe7559331024fc755933104ebf74593311aebe545933100cfe735933100cfc735933104ebe435933104ebc4359331004ff7259331014fe7259331014fc725933122ebf415933122ebd415933104ef6315933104ef53159331004ff705933102cfc70593311aebf4059331004ff765533104cfe7655331004fd765533104cfc76553310267e65553310067d655533101ebe6455331006bd64553311af3c5455331005df735533104ddc7355331296ee6255331004ff7558b31024fe7558b31024fc7558b31004ff7458b3101cfe7458b3101cfc7458b3100cfe7358b3100cfc7358b3104eef7258b31006ef5258b311a6ee5258b311a6ec5258b31006ef4258b311a6ee4258b311a6ec4258b3104eef3258b3104eec3258b311deef2158b31004ff7058b3102cfc7058b3104edf3058b311a6ef2058b311a6ec2058b31006ef7558b31006ee7558b31006ed7558b31006ec7558b31006ef7458b31006ee7458b31006ed7458b31006ec7458b31006ef5458b31006ee5458b31006ed5458b31006ec5458b3104eef7358b3104eee7358b3104eed7358b3104eec7358b3104eef5358b3104eee5358b3104eed5358b3104eec5358b3104eef4358b3104eee4358b3104eed4358b3104eec4358b311deef7158b311deee7158b311deed7158b311deec7158b311deef5158b311deee5158b311deed5158b311deec5158b311deef4158b311deee4158b311deed4158b311deec4158b3104eef3158b3104eee3158b3104eed3158b3104eec3158b31006ef7058b31006ee7058b31006ed7058b31006ec7058b31006ef5058b31006ec5058b31006ef4058b31006ec4058b3104eef3058b3104ecf3058b3104eee3058b3104eed3058b3104eec3058b311deef1058b311deee1058b311deed1058b311deec1058b31004ff7654b31004fd7654b3104cfc7654b31016ee6254b31006ed6254b31004ff7650b31004fd765
  | 24 => 0xe764c951004fc764c951006ef624c951016ec624c9510076d524c95102cfe76d815100cfd75d815101cfe74d8151004fd74d815101cfc74d815104cfe73d8151004fd73d8151014fe72d8151004fd72d8151014fc72d815135e7f52d81510067d52d8151024fd71d81512c6f631d815135efa50d81512c6fa10d81511d5be7498151005bd7498151006fb6098151005ef72581511cdec725815102efa6018151006f96018151024fe76d95411c67e65d954128cfd75d954100cff74d954100cfd74d95414167f54d95414167d54d954104cfe73d9541004fd73d95411c67c53d9541014fe72d9541004fd72d9541014fc72d954101cff71d954101cfd71d95414067f51d95414067d51d9541406f631d954102cfe70d9541004fd70d95411c67f50d9541024ff76595411c67c65595413fdbf745954140df77159541404ff75595410067f75595413fcff7459541006bf7459541004ff735954104cfc7359541004ff7259541014fe7259541014fc725954128cff7159541006f7715954128ef63159541004ff705954102cfc705954104cfe76d8d41024fe75d8d41004fd75d8d41024fc75d8d4100cfd74d8d413f6de43d8d413f6dd43d8d41014fe72d8d41004fd72d8d41014fc72d8d4101cfd71d8d413cef651d8d413cedf31d8d4102cfe70d8d41004fd70d8d413f6bf40d8d41006df6398d411bdee7298d41005ed7298d41195f57198d410057f7558d411c57c7558d411adf77158d4104ede6318d41006dd6318d41004fe7694d41004fd7694d4104cfc7694d410067f6594d410267c6594d4100df67194d41005f57194d41004ff7654d41004fe7654d41004fc7654d41005bf7454d4101dbc7454d4100df67154d41014fe76d89411beee62d8941024fe75d8941004fd75d8941024fc75d894100cfd74d894104cfe73d8941004fd73d89411beee42d89413eeed42d89411beee32d894101cfd71d894138eef21d894102cfe70d8941004fd70d89413eebf40d89411beec20d89411beec62589413e5f77158941004ff7654941004fe7654941004fc765494100dbc7650941016bc765094100cbc765094101dbf725094101faf7250941007af6250941016be6250941016bc62509411bfac62509411bfae5250941007ad52509411bfae3250941007b7715094100dbe715094100dbc715094120fb4715094101ebf615094101fb7615094120fb6515094120fb63150941005bf7050941004fe76cc941004fd76cc94104cfc76cc94100df671cc941005f571cc941004ff764c941004fe764c941004fc764c941006ef624c941016ec624c941007ad424c94101df47654541026f4765454101cf4765454100df7755454100f777554541007776554541026f66554541026f465545411c7746554541007b7745454101df6745454101df47454541
  | 25 => 0x932007af645093201eee645093201eec64509321e7ac6450932007cf735093204dee735093204dec7350932007cc7350932016ef6350932017cf63509321ddee71509321ddec71509321e7af4150932005ef70509321e7af405093200cfe76d8532015ee72d85321def661d85321dfe621d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d8532014fd73d853204cfd72d853204ced72d85321def631d85321deee21d85321def621d85321deec21d853202cfe70d8532004fd70d85321a6ef20d85321def410d85321def461585321dfe42158532005fb7058532005f87058532024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813204cfd72d813200cfe71d8132004fd71d813200cfc71d8132106fa20d8132006fb10d8132006f810d8132006fb6098132005f771581321ddf471581321ed7e75181320057d75181321e5be7418132005bd74181321ddf67118132005f5711813202efa6018132006f9601813201cfe76d91511d6be64d915100cfd75d91511d6be54d915143ebd54d915104cfe73d9151004fd73d91511d6bc43d9151014fe72d9151004fd72d9151014fc72d9151024fd71d91513febf41d91513fef631d915102cfe70d9151004fd70d91511d6bf40d91511d6bc6459151435f7715915104cfe76d8d5100cfd75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d5142ede53d8d5142edd53d8d51014fe72d8d51004fd72d8d51014fc72d8d51024fd71d8d513d6f641d8d513d6df31d8d5102cfe70d8d51004fd70d8d5142e7f50d8d51006df6398d511cdee7298d51005ed7298d5119df57198d51005bf7458d511d5bc7458d511b5f77158d5104ede6318d51006dd6318d51004fe7690d51004fd7690d5104cfc7690d51006bf6490d5101ebc6490d5100df67190d51005f57190d51004ff7650d51004fe7650d51004fc7650d510057f7550d510257c7550d5100df67150d51014fe76d89511ceee62d895100cfd75d895101cfe74d8951004fd74d895101cfc74d895104cfe73d8951004fd73d89511ceee52d8951426ed52d89511ceee32d8951024fd71d89513aeef21d895102cfe70d8951004fd70d89514267f50d89511ceec20d89511ceec625895141df7715895100d7c76549510167c765495100c7c76549510257f72549510276f72549510076f62549510167e62549510167c62549511cf6c62549511cf6e42549511cf6e325495100777715495100d7e715495100d7c715495121f7471549510267f615495102777615495121f76415495121f7631549510057f7054951004ff7650951004fe7650951004fc76509510076d5250951004fe76cc951004fd76cc95104cfc76cc95100df671cc951005f571cc951004ff764c951004f
  | 26 => 0x4ef5305873204ef4305873218ef7205873218ef6205873218ef5205873218ef42058732004ff7558332024fe7558332024fc7558332004ff745833201cfe745833201cfc7458332014fc735833204eee325833204eed3258332004ff715833200cfe715833200cfc715833204edf315833204efb705833204efb305833204ef830583320c6fa2058332024fe76d95321ee7e65d953201cfe74d9532004fd74d953201cfc74d95320067e54d95321ee7c54d9532014fd73d95321ee7f53d953204cff72d953204cfd72d953227e7f52d953227e7d52d953227eee42d953200cfe71d9532004fd71d953200cfc71d953202cfe70d9532004fd70d95321ee7c6559532005bf74595321e5bc745953244ddf735953227cff75595320067f7559532004ff7459532006bf7459532004bf745953201cfe745953201cfc7459532006bc745953201cbc745953244cff7359532006df7359532264ff7259532006ef7259532266ee4259532004ff715953200cfe715953200cfc7159532004ff705953202cfc70595321ee7f505953201cfe76d91321e6be64d9132024fe75d9132004fd75d9132024fc75d9132006bf54d91321e6bc54d9132014fd73d91321e6bf43d913204cff72d913204cfd72d913224eee52d913224ebf42d913224ebd42d913200cfe71d9132004fd71d913200cfc71d913202cfe70d9132004fd70d91320057f75591321ed7c75591321e6bc6459132445df7359132004ff75591320067f75591320047f7559132024fe7559132024fc75591320067c75591320247c755913224cff7459132006bf7459132444ff7359132006df7359132234ff7259132006ef7259132236ee5259132004ff715913200cfe715913200cfc7159132004ff705913202cfc70591321e6bf4059132004ff7655132004fe7655132004fd7655132004fc76551321e73c5455132005df735513204ddc7355132015ee7255132024ff7654d32014fe7654d32264fd7654d32014fc7654d320067f6554d320267c6554d32005bf7454d321e5bc7454d3204f5c5354d32005ef7254d32015ec7254d3201cff7650d32014fe7650d32234fd7650d32014fc7650d320057f7550d321ed7c7550d32006bf6450d3201ebc6450d3204f9c4350d32005ef7250d32015ec7250d3204dec7654932026ec765493204cec7654932015ef75549320176f75549320076f6554932026ee6554932026ec65549321ef6c6554932005ef7454932006ef6454932006ed6454932007cf735493204dee735493204dec7354932007cc7354932016ef6354932017cf63549321ddee71549321ddec71549321ef6f5154932005ef70549321ef6f505493204dec765093201eec765093204cec7650932005ef7550932005ed7550932006ef6550932006ed6550932015ef7450932017af745
  | 27 => 0xc7454942227ac7454942016ef6454942017af6454942005ef7354942006ef63549422176f5154942227af41549422176f5054942227af405494200cfe76d854220ef661d8542024fe75d8542004fd75d8542024fc75d8542014fd74d854204cfe73d8542004fd73d854201cfd72d854220ef641d854220ef631d854220ef621d854202cfe70d8542004fd70d85423e6bf40d854220ef410d854220ef4615854202cfe76d8142024fe75d8142004fd75d8142024fc75d8142014fd74d814204cfe73d8142004fd73d814201cfd72d81422e6ee32d814200cfe71d8142004fd71d814200cfc71d8142346bf41d8142346fa40d81422e6fa20d81422157e75981420057d7598142006fb6098142005f7715814220df4715814202efa6018142006f9601814204e7f7559732004ff745973201cfe745973201cfc74597322067f5459732014fe7359732014fc735973204e7e535973204e7c53597322667f52597322667d525973204eee325973204eed3259732004ff715973200cfe715973200cfc7159732004ff705973202cfc70597322067f5059732004ff7559332024fe7559332024fc755933204ebf74593321febe5459332014fe7359332014fc735933204ebe435933204ebc4359332236bf4259332236bd425933204eee325933204eed3259332004ff715933200cfe715933200cfc7159332004ff705933202cfc70593321febf4059332004ff765533204cfe7655332004fd765533204cfc76553320267e65553320067d655533201ebe6455332006bd64553321ff3c5455332005df735533204ddc735533228ef66155332004ff7558732024fe7558732024fc7558732004ff745873201cfe745873201cfc7458732014fe7358732014fc735873204ef77158732006f751587321f6f651587321f6f45158732006f741587321f6f641587321f6f4415873204ef7315873204ef431587321f6f62158732004ff705873202cfc705873204edf30587321f6f710587321f6f41058732006f77558732006f67558732006f57558732006f47558732006f77458732006f67458732006f57458732006f47458732006f75458732006f65458732006f55458732006f4545873204ef7735873204ef6735873204ef4735873204ef7535873204ef6535873204ef5535873204ef4535873204ef7435873204ef6435873204ef5435873204ef4435873218ef6725873218ef572587321f6f4725873218ef7525873218ef6525873218ef5525873218ef4525873218ef7425873218ef6425873218ef5425873218ef4425873204ef7325873204ef6325873204ef5325873204ef43258732006f77058732006f67058732006f57058732006f47058732006f75058732006f45058732006f74058732006f4405873204ef7305873204ed7305873204ef63058732
  | 28 => 0x915202cfe70d9152004fd70d9152226bf40d9152226bc6459152485ef725915204cfe76d8d52014fd75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d5247ede53d8d5247edd53d8d52024fd72d8d5244eee42d8d5244edf32d8d5200cfe71d8d52004fd71d8d5200cfc71d8d5202cfe70d8d52004fd70d8d5247e7f50d8d52006df6398d521eded7298d5221df67198d52005f57198d52005bf7458d52225bc7458d52205ef7258d5204ede6318d52006dd6318d52004fe7690d52004fd7690d5204cfc7690d52006bf6490d5201ebc6490d52015ee7290d52005ed7290d52004ff7650d52004fe7650d52004fc7650d520057f7550d520257c7550d52015ee7250d5200cfe76d855221ef661d8552014fd75d855201cfe74d8552004fd74d855201cfc74d855204cfe73d8552004fd73d8552024fd72d855221ef651d855221ef631d855221ef621d855202cfe70d8552004fd70d855241e7f50d855221ef410d855221ef4615855202cfe76d8152014fd75d815201cfe74d8152004fd74d815201cfc74d815204cfe73d8152004fd73d8152024fd72d81522eeee32d815200cfe71d8152004fd71d815200cfc71d81523667f51d8152366fa50d81522eefa20d8152225be7498152005bd7498152006fb6098152005f7715815221df4715815202efa6018152006f96018152024fe76d95422167e65d9542294fd75d9542014ff74d9542014fd74d95424767f54d95424767d54d954204cfe73d9542004fd73d95422167c53d954201cff72d954201cfd72d95424667f52d95424667d52d9542466ee32d954200cfe71d9542004fd71d954200cfc71d954202cfe70d9542004fd70d95422167f50d9542024ff76595422167c655954245dbf745954246def7259542464ff75595420067f755954245cff7459542006bf7459542004ff735954204cfc7359542294ff7259542006ef7259542296ee3259542004ff715954200cfe715954200cfc7159542004ff705954202cfc705954204cfe76d8d42024fe75d8d42004fd75d8d42024fc75d8d42014fd74d8d42456de43d8d42456dd43d8d4201cfd72d8d42446ee52d8d42446df32d8d4200cfe71d8d42004fd71d8d4200cfc71d8d4202cfe70d8d42004fd70d8d42456bf40d8d42006df6398d421e5ed7298d4220df67198d42005f57198d420057f7558d422157c7558d421fdef7258d4204ede6318d42006dd6318d42004fe7694d42004fd7694d4204cfc7694d420067f6594d420267c6594d42015ee7294d42005ed7294d42004ff7654d42004fe7654d42004fc7654d42005bf7454d4201dbc7454d42015ee7254d4201dec7654942026ec765494201cec7654942015ef75549420176f75549420076f6554942026ee6554942026ec65549422176c6554942007af745494201dee745494201de
  | 29 => 0x4967f63195434975f431954349f3e431954349f3c43195434975c431954323f6e721954323f6d72195430067e62195430067c621954323f76711954323f7571195430067e61195430067c611954323f7a701954323f7970195434973f401954304dbc7655143026bc765514304cbc765514301dbf755514301f3f75551430073f6555143026be6555143026bc655514323f3c65551430263c65551430079f735514304dbe735514304dbc73551430079c735514301ebf635514301f9f635514323f3f5355143005bf7055143495de7694d4304ede7694d4326ddd7594d432875f6594d43026de6594d43026dc6594d4323f5c6594d430265c6594d4304f9f7494d4301dde7494d4304ddc7494d4304f9c7494d4304edf6494d4304f9f6494d432875e5494d432879e5494d432871e5494d4323f9d5494d432875c5494d432879f4094d43024ff7654d4301cfe7654d4326cfd7654d4301cfc7654d430067f6554d430267c6554d43005bf7454d4301dbc7454d430073d5454d4304f5c5354d4304f9c4354d4301ddc7654d43026dc7654d4301cdc7654d4304ddf7554d4304f5f7554d430075f6554d43026de6554d43026dc6554d4323f5c6554d430079f7454d4301dde7454d4301ddc7454d4326f9c7454d4304edf6454d4304f9f6454d4326f5f5454d4326f9e5454d4326f5d5454d4323f9d5454d430071d5454d4323f5f5054d4326f9f4054d43014fe76d89430067f65d89430067c65d8943236ee62d8943024fe75d8943004fd75d8943024fc75d894304cfd74d894301cfd73d8943236ee42d8943236ee32d894300cfe71d8943004fd71d894300cfc71d894302cfe70d8943004fd70d89431febf40d89430057f755894323d7c75589430067f65589430067c6558943236ec625894300cfe76d85430067f65d85430067c65d854322ef661d8543024fe75d8543004fd75d8543024fc75d854304cfd74d854301cfd73d8543014fe72d8543004fd72d8543014fc72d854322ef641d854322ef631d854302cfe70d8543004fd70d85431aebf40d85430057f755854323d7c75585430067f65585430067c655854322ef461585430067f65d81430067c65d8143024fe75d8143004fd75d8143024fc75d814304cfd74d8143014fe72d8143004fd72d8143014fc72d814300cfe71d8143004fd71d814300cfc71d814310efa40d814323d7e75981430057d75981430067f65981430067c6598143006fb60981430057f755814323d7c75581430067f65581430067c65581430067f65181430067c651814302efa6018143006f9601814301cfe76d9152226be64d9152014fd75d9152226be54d915248ebd54d915204cfe73d9152004fd73d9152226bc43d9152024fd72d915245ebf42d915245eee32d915200cfe71d9152004fd71d915200cfc71d
  | 30 => 0xf5454e4326f5d5454e4326f9c5454e432575f5054e43004ff7558a43024fe7558a43024fc7558a4304cfe7358a4304cfc7358a4304eef7258a4324eee5258a4324eee4258a4304eef3258a4304eec3258a43004ff7158a4300cfe7158a4300cfc7158a43006ee2158a4324eec2158a43004ff7058a4302cfc7058a4324eef2058a43004ff7558643024fe7558643024fc755864304cfe735864304cfc7358643004ff7258643014fe7258643014fc725864304ef77158643246f65158643246f6415864304ef7315864304ef43158643006f72158643246f42158643004ff705864302cfc7058643246f71058643004ff7558243024fe7558243024fc7558243006bf54582430cebc545824304cfc735824304ebf435824304ebd4358243004ff7258243014fe7258243014fc7258243004ff715824300cfe715824300cfc715824304efb70582430cefa405824304efb305824304ef83058243024fe76d954323e7e65d954304cff74d954304cfd74d95432867f54d95432867d54d954301cfd73d954323e7f53d9543014fe72d9543004fd72d9543014fc72d954323e7f52d95430067e52d954323e7c52d954300cfe71d9543004fd71d954300cfc71d954323e7f51d95430067e51d954323e7c51d954302cfe70d9543004fd70d954323e7f50d954323e7c50d95434957e76d95430247e76d95434af3f74d95432873c74d95432875f73d95432875f43d95434af3e43d95434af3c43d95432875c43d95430067e62d95430067c62d95430067e61d95430067c61d95432873f40d95434ae7f74d95432867e74d95432867d74d95432867c74d95432867f73d95434ae7e73d95432867d73d95434ae7c73d95432867f43d95434ae7e43d95434ae7c43d95430067f72d95430067e72d95430067d72d95430067c72d95432867f42d95432867e42d95432867d42d95432867c42d95434ae7f32d95430067e32d95434ae7c32d95430067f71d95430067e71d95430067d71d95430067c71d95432867f41d95432867e41d95432867d41d95432867c41d95434ae7f31d95430067e31d95434ae7c31d95430067f21d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95432867f40d95432867e40d95432867d40d95432867c40d95434ae7f30d95434ae7c30d95430067f20d95430067c20d95430067f10d95430067c10d954323e7c65595434a5df7359543284ff75595430067f755954326cff7459543006bf7459543254bf74595434a4ff7359543006df7359543004ff7259543014fe7259543014fc7259543004ff715954300cfe715954300cfc7159543004ff705954302cfc70595432857e761954323e7e76195432847e76195434973e741954323f3d741954349e7f641954349e3f64195434975d7319543
  | 31 => 0x9153256bc51d91534c6bf31d9153006be31d91534c6bc31d9153006bf21d9153006be21d9153006bc21d9153006bf70d9153006be70d9153006bd70d9153006bc70d9153256bf50d9153256be50d9153256bd50d9153256bc50d91534c6bf30d91534c6bc30d9153006bf20d9153006bc20d9153006bf10d9153006bc10d915326ebc64591534bddf7359153255be761915326ebe761915326f3e751915326f3d751915349ebf651915349e3f651915326f9d73191534a6bf63191534b79f531915349f3e531915349f3c53191534b79c531915326fae721915326fad7219153006be6219153006bc621915326fb6711915326fb57119153006be6119153006bc611915326fba701915326fb970191534b73f501915304d7c765515301e7c765515304c7c76551530257f74551530273f74551530073f645515301e7e645515301e7c645515326f3c645515301e3c64551530075f735515304d7e735515304d7c73551530075c73551530267f63551530275f635515326f3f43551530057f7055153014fe76d8953006bf64d8953006bc64d8953266ee62d895304cfd75d895301cfe74d8953004fd74d895301cfc74d8953024fd73d8953266ee52d8953266ee32d895300cfe71d8953004fd71d895300cfc71d895302cfe70d8953004fd70d89532067f50d8953005bf745895326dbc7458953006bf6458953006bc6458953266ec625895300cfe76d8553006bf64d8553006bc64d855325ef661d855304cfd75d855301cfe74d8553004fd74d855301cfc74d8553024fd73d8553014fe72d8553004fd72d8553014fc72d855325ef651d855325ef631d855302cfe70d8553004fd70d85531b67f50d8553005bf745855326dbc7458553006bf6458553006bc645855325ef46158553006bf64d8153006bc64d815304cfd75d815301cfe74d8153004fd74d815301cfc74d8153014fe72d8153004fd72d8153014fc72d815300cfe71d8153004fd71d815300cfc71d8153116fa50d815326dbe7498153005bd7498153006bf6498153006bc6498153006fb6098153005bf745815326dbc7458153006bf6458153006bc6458153006bf6418153006bc641815302efa6018153006f9601815304e7f7559643256bf745964326e7f5459643256bf54596432563f545964326e7d545964326ebc545964304cfe735964304cfc735964304e7e535964304e7c535964304ebf435964304ebd4359643004ff7259643014fe7259643014fc7259643004ff715964300cfe715964300cfc7159643004ff705964302cfc70596432567f505964304ddf7654e434b6df7654e4304f5f7554e4304f5f6554e43026de6554e4304edc6554e4304f5c6554e432579f7454e4301dde7454e4301ddc7454e4326f9c7454e4301d9c7454e4326f5f5454e432579f5454e432571
  | 32 => 0x1d73c545855428ef4615855402cfe76d815434f3c54d815401cfd75d8154024fd74d815436ebf54d815434e7e54d815434e7c54d815434ebc54d815434e3c54d815404cfe73d8154004fd73d815436e7f53d815434ebf43d8154014fe72d8154004fd72d8154014fc72d815400cfe71d8154004fd71d815400cfc71d815436efa50d815434efa40d81541773c5498154006fb609815415f3c5458154005df7358154005dc73581543373c541815402efa6018154006f9601815404ebf74592532867e5459253286be54592532863e545925323ebd54592532867c545925304cfe735925304cfc735925304e7f535925304e7d535925304ebe435925304ebc4359253004ff7259253014fe7259253014fc7259253004ff715925300cfe715925300cfc7159253004ff705925302cfc7059253286bf4059253004ff7458a5301cfe7458a5301cfc7458a5304cfe7358a5304cfc7358a5304eef7258a5327eee5258a5327eee4258a5304eef3258a5304eec3258a53004ff7158a5300cfe7158a5300cfc7158a53006ee2158a5327eec2158a53004ff7058a5302cfc7058a5327eef2058a53004ff745865301cfe745865301cfc745865304cfe735865304cfc7358653004ff7258653014fe7258653014fc725865304ef77158653276f65158653276f6415865304ef7315865304ef43158653006f72158653276f42158653004ff705865302cfc7058653276f71058653004ff745825301cfe745825301cfc74582530067e54582530d67c545825304cfc735825304e7f535825304e7d5358253004ff7258253014fe7258253014fc7258253004ff715825300cfe715825300cfc715825304efb70582530d6fa505825304efb305825304ef8305825301cfe76d915326ebe64d915304cfd75d915326ebe54d9153256bd54d9153024fd73d915326ebf43d9153014fe72d9153004fd72d9153014fc72d915326ebf42d9153006be42d915326ebc42d915300cfe71d9153004fd71d915300cfc71d915326ebf41d9153006be41d915326ebc41d915302cfe70d9153004fd70d915326ebf40d915326ebc40d915326dbe76d915301cbe76d91534c73f75d91532573c75d91532579f73d91532579f53d91534c73e53d91534c73c53d91532579c53d9153006be62d9153006bc62d9153006be61d9153006bc61d91532573f50d91534c6bf75d915326ebe75d9153256bc75d9153256bf73d91534c6be73d9153256bd73d91534c6bc73d9153256bf53d91534c6be53d91534c6bc53d9153006bf72d9153006be72d9153006bd72d9153006bc72d9153256bf52d9153256be52d9153256bd52d9153256bc52d91534c6bf32d9153006be32d91534c6bc32d9153006bf71d9153006be71d9153006bd71d9153006bc71d9153256bf51d9153256be51d9153256bd51d
  | 33 => 0x700100ac0080120048014000005000001c018008003000c00000400b0040008000006002401e000004003000001f00100a800a001003804402800300000b4002000013006400000100280ec010008001003000c02701580040000000068008000000000000000200200000040000150000060034001005002c002003002801c0040000020008018004003005c03000b0018078036000000001800600900e000802a0000028004004000000005800a00400600040000010040000038004006001c008000006001000001a000800000a00901800240020000018054000000011803800a00600d8000000015003805002e004000000800800100180100000070000000042000000002003e0190038014006025003006000004d0088048014010000000c00000b011009800404a017801c010004001800000000f000000400000000b80c000a005002800c00000300a0000088011005800c00200d00580540080090000008006001002800804a00a0020004000002000000c01e0010000024002006001801c00a0010008010000001004804401e00c0050000008000005000000000000000380000020008000030006000001c0020140030000006000012000000a00100980140000170030008006008005002000401500000680000070010000040000002805c00000000000040020040030000000001003801800400e000001001a0000120000010006000000001e00a00100100000080000014000000001806806c00400500000020000000000022004000004802a00400800c4006000000000400a003000009400000000000180080100028008000001003001400a001008003800600b01c001800000200000000120130028038018005004000000000900080840060130148004000003000000001a00d000001c00e00104cfe76d8d544a73c54d8d5401cfd75d8d54024fd74d8d544bede53d8d544a6de43d8d54014fe72d8d54004fd72d8d54014fc72d8d5400cfe71d8d54004fd71d8d5400cfc71d8d5402cfe70d8d54004fd70d8d544ae7f6598d544c6bf6498d542873c5498d54006df6398d5426f3c5458d544ae7f6518d544c6bf6418d544973c5418d5404ede6318d54006dd6318d54295ee7218d54005ed7218d5428df67118d54005f57118d54005fa7018d54005f97018d54014fe76d895446f3c54d8954296ee62d895401cfd75d8954024fd74d895404cfe73d8954004fd73d8954296ee52d8954296ee42d895400cfe71d8954004fd71d895400cfc71d895402cfe70d8954004fd70d89542273c5458954296ec625895400cfe76d855440f3c54d855428ef661d855401cfd75d8554024fd74d855404cfe73d8554004fd73d8554014fe72d8554004fd72d8554014fc72d855428ef651d855428ef641d855402cfe70d8554004fd70d8554
  | 34 => 0x500780000600000040014006003003000800800600d000c00e00600900440000000010064002015005001400600001e00140080010180034010009000004802e00a001001800c0170040020002000000800c01202500780140000200038008098017001004c00e00100e0038014009009000c00200d000001c00a008004001801e00e000003c00c05e01100000260130000000004000004009c004000000004c048005007801802000400300dc00a000001803000000601a800400e003000000400000c000808c0960090038020042028024000c01000400400f001a00000000000000010050000000007000001c000001000002c016001004800c008006002001401c00400d0000000000007801c01a012006001c026001008000c004000008801000a006000004c02a0000000004014061003808002a02b0148000082000011800401e0370020000064002001800000a000000000402a001000800000601e003800800200f00000980000030030018044000000000001c000013001401200300a8010004003003004800000200380000080020058000004005002801c016001000007c00002f006802404c00300c8000000004000000003600d00580180160070058004002001000000c00400700a003000a0020000064006002000007800a00b00e000c032000001000002406200280280000050008014006000013000c0000030028000008002003801c02600e00080080040060008028004000000008c00a003001000001200e0030008008002001804400000d000000405a00100180000ce005031800c01000302e000800000a0098020010006005808400a01c000006c00e0050098000004004000800400403301a8000008004000000000e0000020068008007002005c00000700000180a4001000000000000400b000400000200480040080030038000002000009800000000000000080140040000008002003000802400200d000000004400e00400000160000000000002000000001c01e00101780080080010000000002004002800000e00000a804000e00002500000000000000010004000000800800e01700080340040060008004002001001800c00a008001000800600200c001401800900b8000004003000000000e004000001001200200600080000000000000032001000004c08e00b000000005802b000003c00200800180000aa008001800804400e000005000c01600000340000080000008036000004004c046000000000c0140060308040000000001801401400000d805400e01602c005800200c0000010020002001800001400c000006804800400b000c0260010000004002000002003400000c00a000c00803b000802401a000000003801c0110008008006006001804c06601600100a400400000800080020
  | 35 => 0x900d80000060010010050030002002800400e00001600080b6023000000000800100b800001e00300a0010004005004001004a020005001003600b0010018006000001800400000000400080080090008034000016000000c012001001003000600101d002400200000201280100000010030000006000007002202400182440140180010000008059000000000200e001000400002a000000800e03800d000800002200000f4002010000007c00000700b000c00002900000100140160030010000006002000401c00501f8000068019000001002c001000000002c01300000000060030020094014000009001005000c00080240000000038004004004018003002400600e805000a04102580500300010000040016001001803000c007003000401a00000c000001c02002400040020060000014006006015000001401100c8048002003000800400400100080080300000038014006000008000002e0000000010000000001000000800200080100080030018000014009000808c000000001805c00800200280080b000a0060000004013005803805000d004800000c000001809c038004000002000e021001800401000a0000084006019000002000800b000808c00e003000006001a00000080480000070160004000000003800c00a0060068008072004008803005400f001801003a008007003802600500100a4002000001800401e006001802407400c00080340020340000004010001001807000200c01d80180300180000060000004003002c00e00a0008160002001001009800200a004007801c00e000002c04e00500400ec02e000002002400000a001000402a001000001800000200000000120000020000002001000800000a01f00000000040000098008004003011000400a00100a800001000600000200020040008010016003002000c000005004003c036001008800c00e003008000c00c00f0008038002002002802800200300000c800c00c0030028000003002002800c00000000100060010000000002000004009401400000000280000010008008004002001805c02c002001003000000e000000000402400c800000e002002007400000000100300020000018054024001000804800204e0028090008005000000000400a0068000002013000000402e001001003000600e004001c01600a00280080120000000008000051001003000000600180340160080010000002000001801000e0000050070002006001000801e00f009002c0160150248014000004002000401c002001001400200900c8030028010001800000a00300280080060050020100012001002801000400100000000080010018010044008002000804c00900000380080000090008020003012005c00a00f0000018000001000000000002100f8
  | 36 => 0x62e882d100c8cbe089d2d1176d3972fb84f614b928121042973f4800019383bb05a4000000071934d807501952340000e0d29b51e3318461d171c60f024000001fc36b0b108ee1d2c0a243ec76724fc8cf3e600004f8910c26dc88b0000000566c617064d0d0511c7033aecc8819e8cdf0d950244c993744a30ac633b8f0c18f4fe152a4214259d4a456dc1bf240d410165497e4e105390c2c00000012d02b2000017b41ae0e9d0700a00cf40000c5c0000e3931980000e913db0000b80374c05f4794de137e95e73f68e731e604a12ec94f522d027c126c6732910d8a170d01000005e91ae04061ea55a5082514a3bd43ce37b4ecd475542c1340b3028c8fc6346d25400005e22cd08c9469c000524c000000135f1a4028e22ec55d00012ac24a4fbb25d444201b95ec377800000002433348000273c0003878a1c4fe42c000001801eec34c16e844e000075c34e4e2506940bc04f08f635e000015f48530d8147a56881451cfc18900012fe54e4790000014d31ad09f1f1d01a00000000000991421c39d4a2c0004bf4a02544126d2e04fb514bc9d137c54c904ccd682a5d11c4c6444b16e4ebd158cd97441c98b44a887f4511388474127c3fdcf404d000a63e500010a9d26c42d0889412cce000000000000a8e46d8d5f51c94de40140000e1c00042b4e7b435482d484000000b91bb0270dc824b4c2a1f0d0260a74fa24710d572c1c1821bbcfaa166cf0a2ff90b9417155c11e5073433868c42a00000000e7c2c915de4560c4b293800000011ad2b60cca3edc0000dd51600000000000000014641284aac0f10b54681219d0f93b64dad0000c090fa8b6055340000000a4d38a000000000001dc8000541c000000144a464c000000000001d000016d518704c400000005ff00000000000007016802801e0010000000016005001003007a005003000c000000000000400200a002803c000000003801400a00d00a807806c0010028010002005000001400000b00100180040150038024000000010000000000b003014000c008002801c002000000003c06a007003000404600200100040120410020000026001003004800800b00680840300070000008008013000002c00600c00300300040010058004034003000000400200300200f80000060000004032028000001c014000004800c01c00500280000060000100004000000000000003a010000000c02c000001002c006007000001c0000020000008014010002802800a00d008000401200000d800c01200000e001803e00a005000401a0210010000008000005001c11601200000080120010000028000004006803400000e00680380000090000000004000002000006200300480340020040068014000001000000c04e00100980040080000080030002007002001c0000010000000000
  | 37 => 0xc400000000000000000000110e33b00004c348e7582d4d73bcc4ec0fbc000000000015290532914ffd496d5d1000005e14d0000000029c1b08fb03c0460900013bc107151f50242e9000000043a935e1df8287000083212dc0005488eee0000000000000000004091374b9f1ba10a50578ea9481c0001118caa30d523a4ec40002d0000054c000037a0b9e42f87361d940003ce40004b6c00000000001f540004e54c030c9d5d506f4000284927e0b98000421904d3ee8b480001496487c40f00006eb000159a43f91a80000c5d3b54b2535d05862e947b510f40002e580001eac00000007600000bea3b7898745380002338887000074a11f083444944ed25909112f7c7c22ef41d13fa09b0448143001f94b4134c7a11fd04045138a555454e6e4e087552e28b5924144ae4074d010bac4680bdc000485d3c70000d600000a6400011fe000000023c8e5f57700002eb400041580000580a8b0e48c53000043634142a1527c49d50880000000c4e457922535b52b81600fbe230c94b0cd0d444f9054c1cf13fa127d18e3fe4a78000000053f51d80000620000100209bd0de26e0dcc3a695bc1bd8c1515c8a56000159312780000000000000000000000000d5000000000001cc44f00000c9623fcc041ef52bb0ca80004c100000000df914c4c8b57dcae62ecc0003b4c0004b307120bb948f12505843fc8b9137380b03078129570c0003eac234000104103d4d45000089e2770aeb37580003ee133c3a11389315c79b5658891151530342384634d48d6b24e8ade57e817230440332988166000023f000000000010bc36505a920a49c434340001b20e66232925e551400047040001768aab0000b8d2d94d0631e54e249746fd5188865070000027b0c692f78b9735cc7380000c743f7d4371c6872158344610000257403478f537400000000002ed0fd14a412a52b3c00000005ab0000000050150d01444f719b811500dd3b73e140dc000117220940001b1d4e400001e957392d900012b54ee00001a7000039340002a3512237a8dcf338d18d49fc0422d747e20a504c758a52f4015035f35dc45b1a5d32a135ca7220b8a5727500000138ac70000f8c44ac1853e74f224930095268400021ec12600014f444e8000000000000000000780fac5678000109400014100000000e8339c948d2c8000046e562e573015132309131a20f2e326852c5380ed249903c24fac970299946714491f85568000503ce3b073cf864a5c0f70afcfdb49ed0f741ec678010002553f870719211450decadd49bc95518c95f051a807c390cd75192c09b07d954147ac40209c4d7e416c8392a415a637191a949540000eccd8820f85260c8023d21341bb0b7d5254bdc50f48f874754906d24a7d24840f03812d68685273000000003e03db86bf4b4c060244881538190f
  | 38 => 0x7a000000000015ef56e160752a953d013400000002c3422cace3ad936a340084500013b32b551c73048e6938653441540a2634ed06a000073a2e640002a140000000cf130003ec06aca3f2ce0e9e53ad0762bc8819528c24854200fb5654c160a4ce812db12ba37f14a107384fb12d84204120e85381c8ef53840000000bb63c789f62d7108c217cf5900015052c00000553836f0720a0149d0c680e64774287d3ba27dd49b2a9814e55100000d3c0003244dee513d0a33338f7245895da180c1190bf062900013e60001483000107f3654bdd45cc0001c80000000062e00005f4547956f21f0e7100000eb2394c9000005b6000129920e8000000000009ad5cb26480002a6c000000000000006f0138c0003eb543c2e30c604d608ac53295ee3fcd30c211d6113238bf23d888280bcceba0f9cceb13a4c3f2c0d0514dc530700454e8173894f29787ac3cd95c02f6c75044f02592ee0f5812a01924c195d22ea05d34f2c06b31047dc516d463305cb61317cf04065cc1f0d6c8630b9c1c905c1272272400016bcb4310794bc15dcb9427004c522353350c84fcb20fc607512125719fc000000135a4fc85003538ab60000000000000000008d01ad8cba3c3824200000000000db00f5962d00004834ddd3ee4738000139cc46356c00000011ea4fc424c466d3d54a3c3162a051bc4f94daa21b509c43c800018bc8f14fb40004ed90230000000026054e4abd3160000000297cf504f005464f110e6286069e32e12162c5411001ec9d8000000045d83930350a9c155418652a129e146800057fc7aa4bc0c2300005912e9cc342de0ae136340001bf0000543cfdc237837f000000036a4aca2fed2cf00002b817513471e1012a0ae92b7030c15f354c6514f811123db09093da85614c9c99308e4d5a3bd831722e507c081ca9f0ea511a10ccc753fbc49952dc94426c92063f3816e00a04622ce8d582ae47525140e2d1c540fa17a14fc53713e1034162508747df0cccc33583815d1a452b63b611320085440101c41d2f341763e9025b49c40101354af42fdd4520cb94a522988061620d9e555d1d950ec8771a854c82bd8f2d1f68fc12f14eb42e801b33ce048e16b825c1ef14140b8c46503095652970f712e8d105571c76131bcdb5086439634582583a582d73ca142a3f087fa1e8824015e83283c00fe322f8bb947280d2161519209f526637b115732d041514fd35b3a2817433ec6b244500002408e221b3074800013ec40ac0000b0549d0000a91033915300010e8000076a000000a342000033d8a43402d359000156b42fd46b5014d4d106d50623186400e8859426f80bf0a146944f350ec41acd9b4864cd1257866d3d382053c5c1993d3c9a4000068716d0b8600004bb0000bae00000000e792e5480c000340929b00003630000ffb548435751
  | 39 => 0x8d407754a82cf00014af000076f54d42f64490559442c8a344789800000e765598b282a0c5cd3ff00000000dcd58a0c403bf8000154c96b18fc00056f879a2b4c8d31a6437d4654000401800000000004b5c000218110a3b6d62a3370b692fe92c004d448f286401936945eb0cb56202ff000024894b600f81f83d2470f1d750c006bc2fe42aca7f3088b2b0000c1923540000000000504c6ac000093158681d70000dfd2618000419045d000028f4d1892856d8d381790e3415d000024d4e9b4fa1404411499550a065f4fa4aa81c909e042c42ad0aa0bbf09154cd467869f2fa40001694000000146009940000000455532cf4a264086b256d0a4343808310146014da11c93804910267841945b01f230f111d01e08924f28cf045e8e3031b8d15080933e58c53b241492a84dfcafb00b0aa10a2065629ec0000014b7945b961f444c9d926f52a93c0957e0a0800030e88e1517402247d8f1c0000afa44f83244fd87290ce0e4202b000054a019d33787680ebc59a0f047fb47714ea16040003afc951558818815d42af32280632d9c56a521438523dd4c51f4003d2858e6a5728efa4ac000026e84210000c42208c000040132e494d1f0139132c4660ef4292c69808f15d4000160329514ba00000002b641aa0c6916f157140a12a83c54c755b04d40f970b48d352f4871c50fca60275c60c130c0e740f8e6344d157632f4793000104f1cb52c725c557a3f649262af11f200013110000f5c436407a03bd04a0c1c000000066f2dd8836407c7790000f7700004af151d2ad3788ab55524a4a13294e70310baa0c2480932f12e209815313fad16a0000a1d0b58de700008ab3b50c7b25b109a1f384db04d097c0c00a0a150cae751f069600001571e5d01812b06b3506c9b320301fc47a0f67000000007ed31750600005675279459053008d81f1141c46e5714cd455e45354b9857126d50920bd15c95790a5d1fad0721994b684b287f522a0f07514cfb353c039750841472c19572210ca4028ec1b25108f9949249af109cf9601406834b84a080fdccd856c44d1092862322f414f1efc2f23a18a6e21f54c4209d09436d108139d40271e20fff162c29927943f419805f60c6043b0d4856748a0c0d55404fc02305e611694642c2c9b441e4da43a1c00028381cc483c4b521e557f44180162bb031000005b0167c47707c00003cfd3911ad03fa025021605d4a0f47440c108981c158580661720323490128018a838d0001147000152d00004d200000004a9c121213c9764be0418339d20c0000ac0470c8e61758bd8235141638ace9538c81a3403028112c819028a468600008dc00000004f8c89603c800033184bc46c8000303c7e54a480002a88ac52628000364d584351d09810a80000000adc4ed4e740d853ce0bb45cf0000000114c1610000f
  | 40 => 0x3768c9432b4417000000000006a555e065d00000002af469b00000001504835000113d48d412b3e484f433955a44e804df440d08951306214860bbb1418e7a50d8e384624f4d0cf4a891bc4ac1460d24a4b051fc11a493b58cc40b16484ee35c400020350b31d00642000068b0000b1b12c55d63780be046702ea4f481c30b38f3400015e30d7863424cd0314ac8256027cf452df0e4632794322c3085c3cc88aa38f000051511523b210c33fa550900009370000ece4460710462109e0fac5b841c540b4bf0c95266429f52288fc4048c934e6c3ee182d46f1af1278521117f4f7d4063ee502925706724350d1e0d9d00951193282d2d4ae3648f9c425ce8b105844d5114f060610d1a29045dd1630b26000025028841e2577d282503146e12b496a119c4f209ed1f50000000393000032d906137dc00020980000000286000051158610653e8d1c603803024fbc1b547dc9532c3c0000f849ef2e54fee509416a000102e289400021d80001dcc00043188880000a4c2e2cef83ba557736b0000480004a0224ee2035c000527064a3af800040f400012f40003ebd1e0000112900000001f1148600011a30001291460400000000001f4470c3bec01a0d10000000153f00000000cf00002850000080c35c21553f01004a3a00008db000000051a4982435c0004d8c5ef1ecc0004078000000162252611ed1eb8ec6392058f2120f6b24280000aa478e08ecf432208cc10f74d9d58d042433e08a90000379046c3085394b0d2ee89724358b2d4960c82497cf302bf4b4e000000030e40001a480b30000b9004502be23140151288000350800018500001d115aa0000fc42d10f1439c04cc210147b11c162b0d681ec00003510000d7d000005a34f840a4b48f1606e8000110ca86036000045e054d0001383322426d29f4a761d0c00015b4bf128b156e5604376562401e28e404942594810000d12000114d300400038d489b3f1400012980a4000026e12e901c000000007a00c70c3d09000015293e2d3653c24a8842895ed50ad40724f100a2d4c0000000fe446106fa0000db80570c6226fcf4834b15f1384c5894c6c57c0bbc0000000ea62f4481446c400041a0b19351895914ac0003eb82372a508224e990f10001077000098d1c6c48d03e490e00013cc000153256b8bfd000123900011910000f565244000535400013e9222079001f49cd03600013420a88cac473479e19dc00043213be0000ec90c34000200128e054c0002fc12680000000000038e1474000000115b23f8000207888f2d30466525d4754f18f70278c628419cee12cfc03a29490e70bec3a806f902f3aacbd752c507a3c84cf93871133420c2dc4a98cd611f41771c60c0849ac53e4b10000129c000187000006e0ee32090e1d0e6cb6b354400000014ab097cbb720680001
  | 41 => 0x36104e04c4c6463a749eb3424e4f01904740df8be319ec9d545a11b3434d6004828e2a4e8851638b95c61bd50cb09fd04415e034326b908d38f8afc2d5c000263925c000117500000003b1000013511bf0000bc2000032f0000a7a0000f2f0f4400007681d02b88fc84cdcf5a3d4c67c19a885d0374c7e00007990e400003039426000000000001a204ec5a7000000000002f83d1caff0cf80003c94000131000021b0000395ce0a2040c2b4908000127000047e4df6415478b1c2c00006900000000a692ac4a5b000000038a51ba345005531e92e900014000274106443c0000000eb75708eaf21c400024d056b47a40000e705f04264ab7490c4280000d0a0000a3d05090490f700000a30493000000025e017158982840000370108c4ef01b4d1f00d95343cb05330bc4c3e26a0f7d418905e091c00045687414310000020077c00000f600000002d151112bc505d39789582434e7d3bac00e56b471f0b090741fc83b23e7c5aa498c08422406bd1fa8d792afce654c094351cc135c584137b1b10bc14cecda03db4bd52ef85621478c561f5c3821db10df0fc46c14c407b60cb07c923580d3091811315908593958b0243bc68414542d82d6c80a1200b854b201581be0d612a08aaa1fb06b909a0eff0d1c9dd0000251206c4120cc5276000065200000000000000000033f155c03f28f051b000026314f4b1200005ea0550ccd1934210406c36840cc00011c80000c981fe3e280003ed872637991393f9c0001bcc0003d4400025691a02bb8295088c1eb30bc00036f0a59573475718f0fdd5134ae91161370000000034cc00048f452a27b4a7039503721b8400018540002694c26023c0000000cfd30f52b1350d44106846e4184529440c9231570415529e4ae0312114823f491e2b08bff0c2847517095333a388374c906c92671205235c88421316081fa51e733fcd2013e0d63560c1633f60b2e014802b57106df17848cb4db509300c006c121cf1b26ec27339fd5fd492c58a0fe5605000026705300003e340000bb086945189e851dd1b50ff04951cbd0950000d254f78fc00b8124427387d4132533a11491fd35942b54b38447212d12302a13fc36705c00000a9328d80000000000000043800000c644087d3000000000009a744b483c04748e84684db93708fc310dcbcc33e877a25bd082381423550e80df4c2533353b496d2f9c6a703f487816b561b1838000000031e00013da3a7c93d03b8f13098400033d4c4300010f526b4000000054900013344c1553c0001615510c0ff1aa8fed3008000198872346bc7e71000e5524e458e27e00000000b9b0a4442600010ee2514ecc00003594c20ea328ac00041800000000f740000a38040c0000680e4b00014a20000f6653a40b933a473753b909d3dd8c5a41693e736a024b2bb548729a0
  | 42 => 0x4dbf0000e233a5000000008a000085d715089f53b7067d13000003ac400048104fe3d5c000110065b4af05a353c80002f40d311b8c000293d01742b06d4584c5581424000177c0000b740000000eb251b40001e30c2506509df17f49f0199163848a47d955c05170000000032132300000000110d3a286d62c0f4cfe53498000180066132911103f9849a2674450544c09e13a0e9013052de400c3580db47c813ac3a60548000204caf729402002388f5b3fe8ea74e05039326c34b158030400016120f5c00050e40000000cd515980ed179427635d922b0000bab0ab848a4c047773570283203c1094b70552227d1ae225c10f153d3a926e44a41a38ced22700e83e3c5d847992ea23a84923340ae848392ef21600a3067d51444ec14407942f93a203221ac54df52cd1c83ca8e17074860d454455e21d00f43b816230a2cac936f47e04e9039a061cf911ec8f8038c43ed1dacf5e1b70d2942ec8572e2079c21290433fd95400f1000048fc3714bad14c037819500007ba10fd1c01aa43d514142a633651800ea80000000711000091d3e5400000000001cd44a91e180080000fa140dc7322f9470a387c00014852e4285c00055583bd2d4453618dc2b924200bd00000000d1437a00003940848000000071453404f918cd41e000017a248c51801c44e13190d80466954b33a056e000018e0000f31195400047b89625430cae3c8d3a111101220938625081066b37ad0b6036893e55188700000a804c38abe355400000000004420000375cdc400001df0000d1349686270af0c77468838a0000cc30000000000000020accdb18182693298be41f14807441110123b0cb01b68a3550f80973ed0b142ab0861550c16d17f8000000113f0000d5e0b2cee5318c8a72ac05ca000000043695a74ea872800009402a4847a500c08731940003d30b56000000017310d21b600001d9835549c05f13c643ae00000001f05351250d357257c9bc3ec4b0e30a50a6533c77854b08bc298408e3c0d2f11bdcfd41020c84000081144a122c4bd4e0c00751fb00000004b740005231320000009645e4d69489c0005068eea58ec1d405b10140000000000128a121069325185bb36846c01368e1215a045c4a4d3ab4ba0ec544dd31a3574bc839f93a3113c8b7072958d0bf4000284ca87205cc5800003d416a00003e988811fb8d2200010c72b2cc8101655f8396517d49a4dc500e0ef7047ce5d00012671abc2c639b52c9050c000000092a000000000012864d9080202342db1878000000000036083781040bca00000000000ab343311940000000000000053e51aa260c0003a35238000048b000020b4db8cb50000db73a5c00042e94010000d590b2000000000004bb00003e80018360c9fa000034d333c0b41c953ae4ea03bc1ebc0001b6c3c95268d100001246
  | 43 => 0x33b98a6f5074e4704f55d045c01ee1d7c8d2396cf2639689494ef45f500011212fd842c15a54494be8fbf5344e411810e7734101c600a888c3e3878707995f511c5635253400057f155e078425a3e111f100003351670cea22e0ed0164c0002918dd502a877b57ac525084c46c23e8b7301cd1170f34b0916740d9205865a000000049f45f74bed30a5460000380d4f754bc0002721300000077f377c14938800003c4097a19612982ca939457ccc14529800000010fa08852bf000000000012da133d084505cb754cbc9fd3d8c0004820c7c00008490f980f83ec82061964c10585d0c902d4d1c041c55b4d2c72c504443124703131ab4fa72cdcd661e74cab3a9492f574d40e49b8c3021e84390000a4809e427000000415400df407d02cd36ec3f04564b70363152b00013f7447c7004344e1414048443b9059741b0f203fe11310604de94b80f6f4de46cf0000f7e2ef000000000000e8485b1edc5fa4e6521a00012be000023122552124e580002284e3f41509b1409c22c00008fb2cf94e635ecaad0c0cbd406e46630dd034644bc0000000000460851f0f0cc2d3ea414614a10dd116529c1868e91190c1b12b50e0f000019856ed34a4464a5a54485b20000bc909dd47600e485e4e14ea105587594055237475c702271406f194c85618f935410f819a1b781370fd84490a40a8a087c1324e940003b1cbf80000c511ec139a0000a042294edd000000010887832a9d2aa3d180000efc3e8000089438448935444bc63390d410cecd0c4be4e3745c40004f4136b489821e30306ed52f422a3aa899f4b6002311ec00022ccedf0000a0d05ccaae53cc0001b753bf17f000029ad592583c5e349450e0529c1d511e06ff19154fb3b9c34a2c8504e076d063471418a332470e57f827801703b5517c7d60ac8c6746f551620f558727d09c608cc0003e40c060000d2858e800028a000000001a814b55821c5c5830000b3d1224000000000b040877d187cfbc34f40004eb13550000ada4b54b7d0000eca00008984c88dfe00014d22d0560c56313cf0000d7c000031b3f40b9827fd19d1d500d13a2538b3640f1a20843010d986ec06b4000376cfcd4ebc0002598e020cdc4c608a12e7548caa9554c000245c3d212f8f7b03f87f9288017c1b0c42e43cc4e208bc00000006f43aa1376417c21c142102d2d4950104147f04f4c00000000001d4c306000000009d50dc582800045f80002d608b1000053b05ac0b20f60ad640d00863a494b922b838955d40f045ac00000014c71a741c42ddc63617cc000382552600000000000000000000019a473420140af3a08d1d44352503234ff5133946618e80000000a493dd4a6c4d0d22f0f65040361871e503554a311443a0d21275301c3be2680b420c480000be80000000000045d23b55cc00000014343ad
  | 44 => 0xa0762465d61c000102c1d38a7751cc000105012d0eb436400a54564dd4cb933f0d6f51715b434bc5d214394f800001b7000000052c80004f58000000091b3124cc24084fe019d0c87000121446c15f6000000032fd4890458000180898155d04f31d44ca811a801408200001c7473d2ba84484fd46471f4838800000003d540000000e3300000000000ad747743ff19d53f83ca4e500ff86b034903140fa538a000129658d83a5000115535a8fcf4280c833f282b104211653b3cfe20000b130000c0a0000b2355b128d0bfcb89060cd230000000519411800009d64df400053e86c617b000022c8b1f000038c4570dc9562d5fb020800012fc000000000016c4000000058701c80000000f7f20394334e3c00028400001aa000000012613f3000041f9598233400027cd04c249c9fb1b540003d08e26554404b000000023200001e2515408800be11fd1ec00004cb02b5177341cb010504f0d2bd400014803952be000000006673c7c00026892df53b145a1ce4b6d2360f0f42d49da49943da279c6ba58dc576304d21d063036c18607fc086117448a8d5656447fe0430b8e426c00050490223988b3c47e80003e7907848541e34c3c6543af13804cd81ef3148bd321691403c9000047d02ca2650aba00003730098c783260377494825e2814a300000a233e0cf35047926a1d14000478400000004a50d750bd1f00cfe00007700130514458d5711490a9950f451c0000c7d43ad2094d313c1083103846410cd30a05dc115c9250a6cacd57609e64731398185830c254024d19c413f03cc668013c8c051106a412ccb831b8064c4a200e1423cca30b146a0302d1855684d4b03595f42080ea43760c2c072c96937cd2ed1b1542958c95643588b1e4a54f1d22c038644b802f4b580001398d99000161d34fccc800b551d02049e429940460f2819c1698db608290c2507d3fb1e7cf8815bc73e1d0854b4cfd00f079cd4f2dbce452fcc9f90910ea006d95a941647a5589c610522c6f94de94ac2b7c9de1d8c0001a3c8540db8e2f1440efc3ea0000000000000006121f280e200003f206448c210f0d81000108a04293fd00000000000230000000000005f908892b337fcb7f50bc3cf0001423294c6492ad00002fd06e90000000461958000000001fbd52011780003a3ce9c0a489c33698000411cda74ee503a561532915fc00032a476e2a78de54400a6356f4bcb55547a3579400c2830f810fd413a4f14e4944c0a2f4658a714b347083c2d332363cc1b18646a61f789b6515c58d58c02a345854081fdc1dd1a8c38351f82a522fd06621880b73acc5a417b803407fcd481dd4522098934525cc5b711143c6266c0000ed000052f810d1678e1b11ad495123112644b0acc22e882a171417e2c88ec2000131253314270c7c24f496560619c11e242a921
  | 45 => 0xe44c780001c4c9011b44000272c000329d3dc1b2839154e85c92b9081c00000000000ab843f47a628183e41c190f44f613663d912d41adcef91ab81241550b4f4f64920000128900814924884dab000000025e40a0389c6cd46dcffe16f4d9a25ec9ea28f848200003ac316d141366139f3638000200400000009541bec00021cc9e900006e7285400030615024e9c6803cf850230ec1bc4ad137e2e115e84cb55b307d520114e02112ec500731c0c4a30c82b632dd5e918c0efd573c00343889041e54f184a155f227341252c602b453647cc13a92474bccec34de08a42e4ca2d06c0b8708e80003fd158f2cc559c45406ea546d224270427a04e025400000a94d9ceb903a414804b89142458bec56187942f84c804a808f501f408556655a85584a2e38f4111054017b370d5421ee40000000d4a21b89ca2cd560943602743bb0ba420b0be226a54e356c8da33774e8012d03ba1754e0830d94d651fc1f30b243d0258414a1ee139e0394e0043c06083d7c3f80e0149034d121b27b90b21db49422890cdd4778000459800054b82f500012a400000000000749000134f4628000097400007080004cac50d41b8fc7000000055304d8000000001a80005350eac31d86b5274d0b83614b9a56e40001b400002fd546c2e48c1d20e14da40ed24d43f11e4508106d45254384eed559345c0004bfc548420149e414026a2bcc4de0c44a96104c12c189939c3970a2a165902a51d0000313c0002219455000129a000000000005702ed449116b02290ec0be82ebc0ab10381cd3fc47cb26147c62a5400030c52cb24555e21f84c7f4b8d17b3b2d1cf08e118b38408ad0000b5417043c053fc9881ec49aa23acf1500003e3455800027f14ef04804dc125c000280d57b0a245cb3464a8c268cdd21d355631da55bf2d1cc8f0048b6e0e8c00000012b90ed919f2f1c8b52b940000000ad200000001bb8a3718b0ce600007a72ea403c119005b1af93fe21083e20000000000000055f4d873b00ce205bcbc44d204560ab09a64e4857b04d8d964ffc94104c0fde059048623b535611448e909243fd0000dca00009d2000069a000000720cc9573d2c5d13c9d2362f70fd331100003300ab2359d0881fe00003d100004c5478500009193a6042d3d8552710c94c60000000011400000012834e4094a51840002b6c0171d6c92c530072a0b88e52398524528453dd2460613530c86f4c8413e557c2de398031c45b4b0a38d93b413fc00014dc2154dc80000000af900705c425306792f980db000131800014700000b1600013c80aa833a42bc7fd0d3902546aca4208b87e32e706d726586e2001151900013c924ac7961e34f9b18b43ab4cc495d3cdc4a301d809933cd38735c88f91a884b8472c0003130dfb572141548f0cb3301475602b80583bc500042a425221
  | 46 => 0x8015a0a347762ce485133bc232536ccc549580932788aa52e84e2458908df2660b3b11293f334b49c701846e50090c3712ac0793ef40002dec1ac00005513df132521a820f16f00e40000caf3740bf9000081f000028a157cd2110303df39903c715b0a07000000000009f209c83192df8330022c0ca0000000000000000003f30000000000000049dc2660001451000000052d553704682c7040400000000000000000000000031c400000000000000dd41f3c29a48c000046b000000000000000bc3000000025b80002d7c00013589062cc955200003052ccd50e4f0cf121f60cd73f5815929d0ae301c01fd325cc6a0b4d1b44bc87cd41a43de231cb0439e4f7812415e6066c9520ec503f1bc8d0b00000004a8829800002d9236800040640001aec7ed000045f0000791000000015113730000a7e00006d651a047620c521c201074f0000ec13cecbac4fa800023451ef02480000000430100c9483a4cb1d0d040005470000000114f24c1349000000039e00004d4c0002c2006800000001ceca8f0000ca10cac18d0000000000159f56200000294000000000019980004118000000000000000002d5400002c40000000000000046f07e4e3a0000000282439f533800007147010000000237431d3a64000026905843e03fb40101674844000179ca1e00000c522013d127f817f3444d543ce8b17476c97d536050c4d755d905a037c2484e2c4da4d3250b427e0000808000162157e43cc48814794980db24c7c0b624684f1374425315f818b4ce53b02a74ccc07dc0004690e6f000000022654884a111352c68349553c1780024e183ac00cb30681fa2aecfd5048cb7a00001b400006ce1364c5942dc000077044137bc4a00000eda41bd4ad2f580671568fc91ef92870a9154723647a00904224556c65e37708f0446c9f133847a82740ca01258f8746f8d3735414f60354e0b5784a7311503e5015cf540b3094740807923150b9d059507d029c342299d0280f6d20d1f74a9821f90ed4d8432900014581b980bb36b8d6e00014d3276cdb143a4d2700000000d88590001800046954820e3caaf0aacccb1a2873341d544b0000350449cc240000f5d20c0a3112c09e10e80c1c000086636254c25410f5249e83c829a8d1800014c10000201540c35648b432505f40352430b7202454b039ad55437011df3fc021a0c552c64d88d0f51e094e01895ea2668c553ab4d0340050e52cb0aa0552026431b0a84144c2b7107d2410000e441b2cd2b241c2e523d10ff242d22e166521e222917c18887e400010ca0760000259553b003505710455601890d2e44540000cc9013542cac432709632f68c381fc40a11558b63459cc4d1c9c00000007ff12e400000000484e300000000b5e40d515f00013931034cbb00c4d7a022133d0000000291c00050908
  | 47 => 0xf68334ccc409540470000cc75264d8b09b0532575d5a02f645f21d7822b4b0891f438c00055f12bd10acc21071d60113d5639049d1383fa8cf725a001300008f800000001b4d30b378d0b01428527353064416fc38b19405b32c443693ba00534808de445a40001d1800030b961904e489d52382bd36450853548c7203b00c023110ae309cb822da948011cd1d255603b9463d56a48cc7f318e012f3bbca1a56b0b27000070d263c2e83cacc5e206078a0000a00000000022bc48543908f30894c9d542938e0a7870908385a2056c7713a315db28887a4258083b0ce42bb3e6835310d4b8f35fd0c12148a51568c9320da804334f1459452d0421765517255881d54d886438394193bc0aa451789ab29d55b50678ed73d940692630f052bbd60204391434cc00000c380cc160926226b0f69563856503f014b14f0bcf56e88e03d040000cd80ba3bb558a0b413d4202c9c21bf95af1ed09240334b2f493c5033ab8722042ce04565d53e074cdc1327cc7324d863b2c40f7355a0a272a68d3029f15e03688c9921d52321a54ed64314573238c7800bc092e2b0cb491f6c9382d884340698631585090f0b900002ec00000001590000000000002da1c140002f00000311c21b2c7141c46e0b4d4d8098446652c52ca450b3524f8225fc5792bc0ea217808461500cb216f8000148c18f00012f60410f3d3944d702fac4c22f3865c39293ad03a8df247680004f0913656acad0321844c0470f3318153860b8400023308b608f8000000000000000004698179367c000000155d00006410448cda4fd000032c51d41a34ba60324000388475a3bc800000007f600002a0000072e3de4b7433c80004508812006c0004ab80003d80657000156d00001ea17ed3142b44f8900000004d38e150000dc74574b7100014a039b00003764f3c4e740001828c851660d64463140214e8c503ae04fd00010e13960803017536c2bf805602e000054e05f84bb85291c58a344df11f31aad0081a24488003d24e0834e40436c22d4c706825650000581042f3e9403b18e4e6700011d63868ed118ad5672d2841a065887236f8a3336cd36f37d4000022864f25d048113201d919d80cf42848c140c00000a58a5800005c600005a0429d47d3e4c2174a8551a06a44cd36bce1619f83cb10a53d71fa13384a8c3b858bd4f125dcf0835b0dcb11b501647fcbef1e052232fb54bf424472b37e084e433c00017788832140000000111600007640e1088517400004b0d20b36e8e532c155dd3f5cc6d0e602b050c542e4424aa3139534d1d311d339a00001f9888e328956912600000000162186c2b30d0138d262478252e070452ecdf011f80001b64d400000000228900e4708e4e0398b4622684600b50ca552505a134a929d038c1ed20bc997069cfec0758f112d98b36282c7583
  | 48 => 0x4044000000000019b00002d909001eb53412d403b700001de000000000000005878c920000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87e859d943440010fb0b3b286880021fe157650d100243e42aeca1a20008ef825d943440051d904bb286880031b18b7550d1000717aa4a9b1220008ee8715362440011db0e2a6c4880038b55054d891000567418a9b122000acd8315362440215cd022a6c488002b960454d89102b575400a9b122000ae98015362440ad5cb0239ec488002abe1153d891000556422a7b1220008ee8714f62440011db0e29ec488002aba1053d891000556c20a7b122010ae68114f62440015cb0229ec48815abaa0053d891000574c00a7b122000a6f8550f62440014d90aa1ec4880023ba1c43d891000476c3887b122000a6e8510f62440014db0a21ec488042b9a0443d891000572c0887b122056aea8010f62440015d30021ec4880023b61e651891000572c0cca312209bae98099462440011df0eb28c4880023b61e641891000572c0cc8312209aae98099062440011df0eb20c4880023b61e631891000477c3ac63122099aeb8058c62440a75cd02318c4880023be0976549100047bc0aeca92200287c8759552440091dd0fb12a4880023be0976509100047bc0aeca1220028bc8759142440071dd0fb12848800a37a0e76cc91000c7a40ced9922002acc8258f32440219cce3b1664880163d21971cc91018e72312e399220059f0805c732440011df04bb264880023de05764c9100047dc02ec99220028ec821d932440019cc423b2648800a3721d634c91004c7743ec499220098f48759531440635c904b2a62880263d21d644c51018d72412c898a20548f686dc931440639c8c5b92628814eb9a1b624c5102b6723b6c498a2056de070d8931440a99ccec3126288153391d8624c51000763b18c498a2054de07018931440015ad0d99262880c7b118b324c51018f623126498a20059f287dc13144001dc0c5b826288002f8608704c51000770310e098a2070ce462dcd214400b1e90cb9a42880c739189734851002cf8402e690a2002ae686d8921440ad9c8edb12428815b78dc8704851000672316e2a822000ce462dc540440019c8c4b8e6088016b521931cc11032762312639822005bd0804c730440019c8c5b8a60880167521d314c11002d6a432629822060ec4624c5304400b7a10098a60880167c21d3188110005f1c12631022031ee0624c620440219c8e3b1240880163da1b714811005672316e290220059e487485204400b5c90c90a4088007391d9214811002df0402429022010ce876d8920440015d10c992408800b3a1d9324811006e783b6e290220009f0874c520440039e0ec98a4088003f04c9314811002df043a429022001de087485204400b7c50c90a4088016f8219214811001770432429022002ee3764852044003bc4ec90a4088007781d92148110017703b2429022001ce07648520440017c70690a4088002f860d2148110
  | 1 => 0x3002a6c29016eb960873d85200055bc22a7b0a4000ab48454f61480011ed0e29ec2900023d61c53d85200055b420a7b0a4000ab58414f61480155cd0429ec290002b960853d85202dd79400a7b0a4000af18014f61480014ef0aa1ec2900029d21543d85200047b43887b0a40008f58710f61480014ed0a21ec2900029d61443d85200557341087b0a4000ae58210f61480b75e50021ec290002bc60043d85200047ac3cca30a4000ae582994614813f5e301328c2900023de1d65185200047ac3cc830a4000ae582990614813d5e301320c2900023de1d64185200047ac3cc630a40008f78758c614813b5e700b18c2901beb9a0863185202a5734326430a4054ae4864c86148001d8ec6990c290152f8201321852000c3e43acaa8a40048f687d8551480031790eb22829000e3da1f615052000c6f41ced98a40028ec829db31480035a902b1e62900ef3918572cc52002cf4402e598a4000cce764cb3148077d88c2996629002b399cb61cc52000c7a408ec98a4000ce7211d931480031b90eb1a62900efb1185324c52037e7230ee690a40058ec865cd21480779c8c2b9a42900167a201734852000d73436c290a405bce476d8521480b7bc6e238242900033918772541200067230ee4a024000ce4615cb304800b5990c9966090197b118532cc12002de4402659824000ce461dc9304800b3990e9926090016b3219324c12030f6230a649824005bc8804c9304800b0fd0f2a2cb080030fdd2545961002c5f43ea8b242000c3f75d516484001878a9bb2a9080030f15176552100046fc1aecaa420098dc835d954840019c843b92c7080022fe117654e1001c5e422eca9c200587c875955384001878e8b2aa7080269720d6554e100043fc2aeca1c200487c855d9438400b1790eb2287080030f1d56450e1004d4e41ac8a1c200587c87595528400b1790eb2285080263de1971cca1004e6b31ae39942000cd5635c7328400b1b90eb1a6508273b1085634ca1002c7643ac49942005ae8864c920840017c70299241080ef781c532482100147743ee4b2a2000ce472dc565440051dd0fb92c888003391cb715911001477416ecaa220008ed82dd954440011bf06bb2a8880263720d765511000477c12ecaa220028ec825d954440b71ef02b96c68815a3b21b7258d100147743ee4b1a2000ce472dc563440019d0e5b82c68800237e1d6318d1000477c12ed29a20028ec825da534400b1e90cb8ca688003391897194d1002cf8402e329a20028ee82dd953440011db05bb2a68800e2fa127654d100045ec24eca9a20008bf845d9534400717908bb2a6880023be097654d1001476412eca9a2000cac62dd153440011df04bb4868800a3b2097690d1002c7a432e321a2000ce4625c6434400b3e100b8c868800a3ba0b7650d1000476c16eca1a2004
  | 2 => 0xd625483002c5e43ac8a1060058ec87589420c001c6ea92a2c218002b5e0d545843004d6a41aa8b0860008f687151610c0011eb0e2a2c2180038d550545843004d6b418a8b086000ad583151610c0015cd042a2c218002b9608545843002d79400a8b086000af180151610c00b5e100b92c2180029da1472584300053ac28e4b086000ab6841c9610c00156b08392c218026b5a0c725843009d6ac18e4b086000ce5721c9610c00b5e500392c21804ebc600725843002c3e42eeca88600587c87595510c00b1e90eb0aa2180162f213765043002c5e43ac8a0860058f487585410c00b1d905bb242180163d20776484300067210eec9086000ce4215d9210c00b1f100bb2421800399085654843002e3c382ca9086000ea421591210c00b970e0b2242180163b21d624843000d7240ac490860058f487585210c0055c904b0a42180031e59770484300065cb26e09086000ce962dc1210c0019e2c3b8242180161fa1e54596200061fba4a8b2c40058be87d51648800187eebaa2c9100030f15376552200061e2a2ecaa440008df835d954880131b906bb2a910003390877158e200045fc22eca9c40038bc845d9538800b0f90eb2aa7100030f1d16554e2004d2e41acaa9c400087f855d943880090f90abb287100162f21d6450e200061e3aac8a1c4009a9c83591438800b0f90eb2aa3100162f21d645062004e6731ae598c4000ccd635cb318800b1b90eb1a6310283b1085634c62000c7b43ee2b2a4000ce7721c565480031ed0fb8ac89000339dc8715912000c7b40eecaa240008f581dd954480011bf06bb2a8900263720d76551200047bc0aecaa240018f4815d954480ad1df04b8ec69016e3d21b7158d2000c7b43ee2b1a4000ce7721c563480019e0e3b82c69000237e1d6318d200047bc0aed29a40018f4815da534800b1d90cb94a690003391857294d2002cf4402e529a40018f681dd953480011eb03bb2a69000e2fa127654d200045ec24eca9a40008bf845d9534800717908bb2a6900023de057654d2000c7a40aeca9a4000cb461dd153480011ef02bb486900063d2057690d2002c76432e521a4000ce4615ca434800b3d100b9486900063da077650d200047ac0eeca1a400487e859d943480010fb0b3b286900021fe157650d200243e42aeca1a40008f7815d943480031e902bb286900031d1877550d2004c7643aca992403bae48159532480131d90eb2264900eeb9205644c9202a477436e2992403bce461dc5324800b3d50fb826490003b8187704c920005f0c08e09924000ee0611c132480b75c90c996c2900ef399d932d85202ddf040265b0a4000e375495361480011ed0e2a6c2900023d61c54d85200071aaa0a9b0a4000ad68315361480015ab062a6c29002ab9a0854d852000572c10a9b0a405baf28015361480015e
  | 3 => 0x9926000b99841c1324c00599ce4996c298187b108532d853004e67b02e598a6009dcb605cb314c0133ab03b926298006b5a07624c5305076210ec498a6000b59851c1314c00173308382629800339086764853000672108ec90a60058dc865cd214c0c3b8842b9a42980172ed8d749413002ecdb1ae92826004a7885592504c001b32e9994a098002f46073294130006ccba2652826000d9974cc6504c0017930598ca098003665d1319413002cbcc2ee8a82605fd3a54dd1504c0094f50bb22a09828b8e15364541300247c43ac8a826000bc9821cd504c0017a30239aa0980165e21d535413004e3c3b2a6a82605fb388454d504c013ab0e6a9aa098002f46073254130007a4a9264a826000bc982cc5504c001ea2a298aa0980171ed8d759013002eadb1aeb2026003ab884596404c001ab2eb9948098002f46073290130006acbaa652026000d5975cc6404c0017930598c8098003565d5319013002cdcc26eaa02605ed3b54dd5404c0131f10cbaa809817f4e151755013001d5d426caa0260a1e3854d95404c0071f10eb2a8098002f26087350130005e8c08e6a0260059b88750d404c013970eca1a809817ace215435013004ecc39a86a026000bd181cc9404c001f12849928098002f260b3150130007c8a0a62a02600587e87951650c00187ee92a2ca180030fdd2745943004d2e41ae8b286000c3d741d1650c0134bd063a2ca1805a9760c745943000537410e8b286000a6d821d1650c0014ed023a2ca180029d604745943002d3d400e8b286016a79801d1650c0010fd0e10aca180021f61c21594300051f42042b286000a3d84085650c0134bd0610aca180029760c215943002d3d40042b286000a7980085650c00b17d0faa2c8180030fdd754590300061fbaceab206009a9c835d5640c00187aea3aac818026a7a0c75590300ad4ec18eab206000aae821d5640c00155b043aac818002ada0475590300055ac08eab206005aba801d5640c02b573003aac8180022fa1c21590300045ec3842b206000a3e85085640c00147b0a10ac818026a7a0c21590300054ec1842b206005aba80085640c0015730010ac8180030f15376550300061e2a2ecaa060098dc835d9540c00b0f90eb2aa81800e8f211655503002c5e43ac8aa06004a3c85591540c0018bacbb9aa81800327593735503000717aa4a8b106000acf83551620c01359906aa2c4180023ba1c545883000476c38a8b106000e2d54151620c01359d062a2c418002b360c545883000573408a8b106000ae581151620c00b5d5002a2c418002ba600545883002d74402e2b106000a6e851c5620c0014db0a38ac418002aba10715883000556c20e2b106009ace831c5620c02959b0638ac418003395c4715883002d75400e2b106014ae9801c5620c00b0f90eb2aa4180163b21
  | 4 => 0x2500131f10cb8664a00162f219744c94012c9e42ae899280039b48754541500131f10cb8662a00162f219744c54012c9e42ae898a8000ce4219d921500019c8423b242a00162f219744854002cdc402e890a80038fa86dc1215000737508b9ca0a00026ee1d439414012d9c42a8728280009bb8750a50500013770ea0ca0a00030fd97745414015d9d42ee8a828000d9b43dcd5050001cb6a7b1aa0a00aece211535414012d9c42a86a828000f195350d505005767108a92a0a0096ce215425414000794a9284a82802bb3884545505004b6710aa0aa0a0003cc545415414001c5f43ee8b2e6098cba30dd165cc13197261ba2cb9824f0fdd474597300243f43eeab266095c7a30dd564cc12b8f261baac99824f0fdd075593304ac3fc2aecaa660988bf845d954cc0130f90eb2aa99800e8f211655533004c5e43ac8aa66004a3c8559154cc00117f08bb2a59800e2f2117654b3004c7643ac4a96600087f855d942cc0090f90abb285980263b21d6250b3032f6210a64b0e60008bf845d951cc00717908bb2a3980263d21d61547300043fc2aeca0e600487c855d941cc0131e90eb0a8398297b1085624c73002c6f41eec90e6000ce421dd921cc0019c842bb2439819771085734873002cec402e690e602ba3c8459550cc0138b8e6b2aa1980968f215645033004e4e39ac8a06600587e87951658c00187ee92a2cb180169ea02545963002c5f43ea8b246000c3f75d51648c00b57501aa2c9180030f153765523002c7d406ecaa46000c3c545d9548c001878e8b2aa7180030f1d56450e3000c7b43ee2b14605bcd730dc5628c0b79aa61b8ac51815339dc87158a300047bc0aeca9460018f4815d9528c00b0f90eb2aa5180023de057650a3000c7a40aeca1460058bc87591428c0775c902b1265180173a1c1624ca300147743ee4b0c6056ccf30dc9618c0ad99a61b92c31815339dc4725863000477c12eca8c60028ec825d9518c00b0f90eb2aa3180023be09765063001476412eca0c60058bc87591418c0635c904b0a63180173c1c1614c63002c7643ac490c6001ae481589218c00b1e90eb0a431800ab9209614863031e9d2a6e8a8460a4e3854591508c00b2f10ea9aa11818ece211535423004eac39aa6a846062d3b54dd5408c0c7a70a8baa81180267620d755023051f1c2a2caa0460059b88750d408c0c56710aa1a8118027661cd43502300061eba4a9b2a6000a7980953654c00717d0fba2ca980030fdd474595300064e3a6e6b2a6000c3d75d53644c00157301aa6c8980121fa1f75591300061e3aee8b226000c5c75dcd644c001878a93b2a8980021fe1576551300045fc22ecaa260008df835d9544c001878a83b2a8980030f1d36554d300061e3aec8a1a6009cd7605c7324c013ba6c0b8e64980267360b714c930005acc28e
  | 5 => 0x8002c76106354d500068e3a0c6a9aa000d3874dc15354001a76e8382a6a80030f5d76490d5004e2e3b2a721aa02bb1c8454e4354001c3ec8a9c86a80263e2197090d505169c2a2e121aa00487c851d9435400187ca83b286a80165ea037550d50024ae43aa6a1aa000c5c7654d43540092d90ea9284a80263e21970cc95002c3e432ea992a02b93c845d532540092e90ea8a82a80263e21970cc55002c3e432ea98aa02b93c845d531540019c8433b242a800339084764855002c3e432ea90aa005978805d521540091f50db8242a80169ea0273596400051fc22e6b2c802ba3e841cd659000147b0839acb20003175cc735964000537410e6b2c8000a6d821cd65900014ed0239acb200029d604735964002d3d400e6b2c8028a79801cd659000b4f500192cb200029e600325964002d3d40062b2c8000a79800c565900010fd0e10acb200021f61c215964015d1f42042b2c8000a3d8408565900014bd0610acb200029760c215964002d3d40042b2c8000a7980085659000b8f4e0b2ca7200031e5957094e4002c7d406eca9c802bc3c7459553900134b906b2aa72012b0f9977454e400061eb2ee8a9c800587c8759552900018ece2b2e65200171e9c165cca400063b32ae39948000c75655c732900139acc6b8e65200033558d71cca400063cb2ae199480058dc8758d329000b0f90bbb2a3200161f21d655464000637392cb98c8005c7a7059731900018dccab9663200031b59572cc64004e6731ae598c8000ccd635cb31900018f2cab8663200163721d634c64002c7c402ec90c8000e6421595219000b8f0e0b2a43200163b21d624864000d7240ac490c80058f48758521900055c904b0a43200031e59770486400253d42ac6a848000a7b8654d509005767108a9aa1200029ee1952542400053dc32a2a848000c5c651cd6550001a38a839acaa00ae8fa1774595400070e2a6e6b2a8000c5f751cd655000193ee839acaa00038715073595405371c2a6e0b2a8000a9d8414f63500015b30029ec6a00023de0572d8d4000c7a40ae5b1a80008ef825c763500051d904b8ec6a000237e1d6318d400052e42ac631a8000c3f655d253500131f10cb84a6a02874e1517094d4001c5e420eca9a8000c3f541d953500130f90eb2aa6a00af0f1d16554d4004d2e41acaa9a80059ba80dd1535012527d0fbaa86a02570f1db7550d404af0e31eeaa1a8093c3f761d54350127878ec3aa86a024f8718c7550d4049c5f43ecaa1a8025c3c75d9543500131790eb2a86a00970f1d56550d4004d4e41acaa1a8009a9e86d8d4350001a38ebb1a86a0002c76146350d400068e3a8c6a1a8009a9c8694d435004ba38eb29a86a000387d965350d4001cce43aa6a1a8000a9c8654d4350001c3acaa9a86a00034e1d77050d400069dba8e0a1a80039ac875494
  | 6 => 0x1c7a43acaa0a62019b487509414c4013ad0f99282988c7711c93250531007c2a1264a0a62008bf845d7604c40717908baec0988021fe1574d81310243e42ae9b026200ec932c83604c4015b306106c098802bc60420d81310047dc3ac03026200ae882580604c40b1f501bb2a8908023e603765512104c6f41cecaa242008dd839d9544854f99ae5b1cc690aa3355c76398d21006f010ee0b1a4256ceb621c163484b79e6c2382c690803780847058d2153f6210ee6b1a423bae682dc56348401dc043b82c6908033adc87058d2100679b88e0b1a4200ee0211c163484011bf0eb18c690803390867694d210067210aed29a42008fb805da534840b1f100bb4a69080e2fa127654d210045ec24eca9a42008bf845d9534840717908bb2a6908023ee017654d2102c7c402eca9a4200da421dd153484019c8433b48690803390857690d210047dc02ed21a42058f8805da43484090fd0b3b286908021f6167650d210043fc2aeca1a420487c855d943484011f700bb286908163e2017650d21006b210eeaa1a4200d64215d46048401b4842ba0c0908037108673181212b667b12e6302425bcd7615cc6048401b8842b98c0908023ee1d60181212b575c12c0302425baf381580604840b5750139ac9280028fe1573592501751f428e6b24a000a3d851cd649400193ae639ac928002aba08735925000556c10e6b24a000ab6811cd649400156b0239ac928016aea0073592501755cc00e6b24a005aba800c9649400157300192c928016aea0031592500055cc0062b24a0008be87085649400117b0e10ac9280968fa1421592500051ec2842b24a000a9e83085649400153b0610ac928016aea0021592500055cc0042b24a005cba705924394001972c8b8487280163ea037650e502861f326eaa1ca000c3f75591439404b878eab228728026a720d6450e5002c5e43ac8a14a000cb671593329400b974e0b2665280032d99171cca500065ab22e3994a009cd6635c732940019aac6b8e65280032e59170cca5002c6e43ac6994a0058bc84dd9419400b1790eb2283280032b9c964cc65002e5d382c998ca000cae645cb319400195ac8b9663280273398d72cc65000666b1ae598ca000cb9645c3319400b1b90eb1a63280163e20176486500075210ac890ca005cb870591219400b1d90eb124328006b9205624865002c7a43ac290ca002ae4825852194001972c9b8243280032719073591500068e2a0e6b22a000a5d8510f63540015b30021ec6a80023de0572d8d5000c7a40ae5b1aa0008ef825c763540051d904b8ec6a800237e1d6318d500054e422c631aa02b93e87dd15354131878edba2a6a82638718f7454d5049e1fbb0e8a9aa093c3c761d15354127c38c63a2a6a824e1fa1f6454d5015e1e3a6c8a9aa009a5e86d8d5354001a38e9b1aa6a
  | 7 => 0x3c8559154cc801c6ea92a2c399002b5e0d545873204d6a41aa8b0e64008f68715161cc8011eb0e2a2c3990038d550545873204d6b418a8b0e6400ad58315161cc8635cd042a2c399002b9608545873200579400a8b0e6400af18015161cc8135ad07382c399002b9e0970587320053b428e0b0e6400a75851c161cc80156d08382c399002ad610705873204d6b418e0b0e643ead5831c161cc87d5cd04382c399002b9608705873200678b80e0b0e6409ad68314161cc8015ab06282c399026b5a0c40587320056ac1880b0e6400c3d74953654c8014db052a6ca9900e2fa1f74595320061fba8e8b2a6400c3d75d53644c80155b05aa6c8990121fa1f75591320061e3aee8b226400c3c549d9544c8010ff0abb2a8990022fe1176551320061e2a0ecaa264028de86dcd544c801878e9b2aa6990030f1d76450d320247643ac8a9264098ec865d5424c8071d90eb2a84990033c1847058532006f0108e0b0a64008bf845d7604c80717908baec0990021fe1574d81320243e42ae9b026400ad983043604c8015d304086c0990023ee1d60181320057840ac030264008df8758c63544131e90cb8c86a88061fa1b7550d5104c7a432e3992a202a6c8654932544011f70eb00c0a8aa70fdd774595410046fc3ac631a82098f4865c6535040317d0dba2a6a08263d21971cc94101556432849928200f255250951504011f70eb00c0a08063720d765533104c3e43acaaa66203a3c8459554cc4131790eb22a9988128f215645533104c7743ea4b1662098ee87d0962cc401c5ea92a2c598802b3e0d5458b3104d6641aa8b1662008ee8715162cc4011db0e2a2c5988038b5505458b3104d67418a8b166200acd8315162cc4775cd022a2c598802b96045458b3100575400a8b166200ae98015162cc41359d07382c598802b9e057058b3100537428e0b166200a6d851c162cc40155d08382c598802ab6107058b3104d67418e0b166234acd831c162cc4775cd02382c598802b96047058b3100674b80e0b166209ace8314162cc40159b06282c598826b3a0c4058b3100566c1880b1662098ec8758952cc4131d90eb128598802b3e19524cb3100567c32849966202cce724c960cc40187ae92a6ca988029d60654d953101c5f43ee8b2a6200c3f751d1654c40187aebaa6c898802ad60754d91310243f43eeab226200c3c75dd1644c401878a93b2a8988021fe1576551310045fc22ecaa26200c3c541d9544c4031bd0db9aa8988030f1d36554d310061e3aec8a1a6200ce8621c1624c401bc042382c4988263da1b715493104c7b436e2a1262019d6815c3324c47778902a9264988eef1205424c9311dde3416e29926200dd310dc1324c4091e90eb22a2988065d21d5254531004eb43e64a8a6231dc4724c9514c401e8aa4992a2988263d21975505310
  | 8 => 0xeb18c6aa25697e156318d544c54fc22c631aa800d2c545c86355001a68a8b88c6aa0034e1527018d544ae3db2ae031aa898cbb645c06355001a70a8b80c6aa29b1e5d7609815458e5cba6c1302a800d1c54dcd605512b8beca39ac0aa26327d9073581540068e2a0e6b02a8008fb875806055001878a9ba2c1298022fa1c21d91530045ec3843b22a64aa3e850876454c0147b0a10ec8a9a62a7a0c21d91530054ec1843b22a600aba800876454c015730010ec8a98032edc270d91534c51ec28e1b22a6008be870836454c0117b0e106c8a992a8fa1420d91530051ec2841b22a698a9e830836454c0153b06106c8a9802ada0420d91530055ac0841b22a6008be870436454c0117b0e086c8a992a8fa1410d91530051ec2821b22a698a9e830436454c0153b06086c8a9802aba0810d915300556c1021b22a600a3d859886454d6153b07310c8a98028f616611915357d4ec1cc2322a603a3e86d915454d31878edb22a8a9a6347dd0735515334e1e326e0aa2a6008be87d916254c0117d0e322c4a98022fa1f64585530045f438c8b0aa6988bc86dd16054c0117d0fb22c0a98022fa1c64581535764fb98c8b02a669c3e751906054c011f70eb00c0a98030f15375582430043f43843b2a860087d870876550ca147d0810ecaa18028f61021d95434ad2f41843b2a8600a5d830876550c014f50010ecaa18029e60021d95430063db84e1b2a8695a3d841c36550c010fd0e106caa18021f61c20d95432851f42041b2a8600a3d840836550d2b4bd06106caa18029760c20d95430053b40841b2a8600a75810836550c010fd0e086caa18021f61c10d95432851f42021b2a8600a3d840436550d2b4bd06086caa18029760c10d95430053741021b2a8600a6d820436550c0147b09310caa1ab69760e62195430051ec24c232a86aca5d839846550c0947d0db2aa8a1a570f1db65551434ae8fba8e6aa2866dc3c65dc15450ca1878e9b2aa6a18030fd977454d432561e32ee8a9a860993c875515350c134790caa2a6a180f0f1d95454d4304d8e41aa8a9a8650c5c76d955350c9b938edba2a6a1826c721d5454d4301e8e43aa8a9a8609b1e865515350c136390caa2a6a1813872195454d430270fbb2a8a9a8603d1e765515350c07a38ecaa2a6a1813871d95454d4301e0e3b2a8a9a8600b1f805515350c010fd0fb2ac4a18021fa1c65589430043f43ecab0a860087e871956150d2b0f90dbaac0a18021fa1f65581430043f438cab0286abc5f731956050d2587ce8328c0a18023ee1d60181430046fc3ac631aa4098ec865ca43548050fd0dbaa86a90023ee1d60181525561fbaee8b2a84008df8758c63508131d90cb94a6a100a2fa1b7454d420047dc3ac030284028dc835d954cc8130f90eb2aa99900e8f211655533204c5e43ac8aa66404a
  | 9 => 0x10000000000000e88100000740088a297d1f026900013906511d8ff9189eb00022e8000140000000159c280002085a0420fca5999a9bb0408951f48fe21322085780021b0242588c08001240000001b700000001200000014aa628002011d800f80000015a08500000021c87d0659b307c0a595917c1f185e2298b78798000000911cf2250cba431fd08d0b01ad8000550b52441e5000000249a6b0e386000019a0f21818000001130000ab1ca1db1d30000f29ed22c80021480000000010c02c26a8f393c0b800000000000000014700010e9a700003c1c588e16f0000bd8af80000000000800000000000000013300013080012a00024b00000013283a8a195b14d0f00001e000000000000021780022f8000000000509df10891525f91384e8efa488eba398628d29599b590c92111609d8000db0318ad0002080000000000fb80024a8ee8001c920a1fe00d07f0f51949118001778000002019680000e18000d98000000001508001e58dc160a4e1180d5a34a6d8000000608000001b1000000000000000000000178a378ee00000016b0000808000e32321388de92f1ba8b58210000000002678001832318000000848000000e200000004593700003d00000000100801c010060080340000a0060240400900a0040100600000401000002000000000080040300000000800800006008020040000040400100000403000044000028070040040000100000c0880e000030000010080240001200c01001001004010000000000000000000400001000002004088070000000180000a00803800038000008010000000200300c01c0000301000009804032004008000080000080100e00c0080500000004001000010008010020000180001400c010030120100000200600c0080302000001002000008008010000100100b00200c0000d0080040280100001c0680100800400001000028010020000140000400a008050050120200000f00200000000000014010150000000100000e02c000000040080080001802000808002044080020060100101a014004008030000440080200600003803008060010000060000000000a030008000060040300200603c028040080100080100000000006000000008030020000100100000001802002004060000100300080400800000001000000008070040000300000200002000004000000000000000080601c000058000000040201301000c06013018004060080060300000200200804802002030050000000100000c0040080080100200c0181c00200c00003000004030010000000500600601802002006004008000000000080200400000001000000000020000000080000e010088000020140000000805c00001002000000010000000000000000801000000034000000000000080700a014011bf
  | 10 => 0x9c81550fa0001701a917c80001e1b385314580000011e80006d1b19928000001eb9209e98001080a10000041a00000000ef16310a80000000002312885f85018882e80010b8782068000002361a0a6205d9ef8001a18000000001e110a08e80026500000012d80017291784f0001a880012001c00b8339ba2140001f31300001c88000e6238875033170a118818000001b080004113f0000a9000037000035a548000ab8ba13b09e0d495e12d12c83b05b1e920aa2018f1cd0720001571cc9990001f106c9d580013980000004416c1d1a6e17e000000252180a68a490b21f70001d280011b8000000f700000000000013b8a30fb240a538000000000968001c20000710000000a00001a680000012b80009880000004600018c0660000e020b8bc24d16623a19b1c502494b0eda47194000000019800000000029a0301a8068000a48000e400023295880000000005c80002280005700000002697625a99686980014b8f680020d8670002578a524280000000000002f00c0001120000c2084222a2a9fa8c697b22f1b014d84e0b698da059c39e78c98858d38dd1ad00799884a2368c420b0038a80ac22810691c16396d8a623c08b11980016a00002880017400025e800000000000252989a1d219261a639f884b0472120a0976a6f00009a03e92903516b9bc19200026c00013e24a1c9a189db8000002400c70b480024f15600000016500012e80000017700009c0000a38000000c38000000aea3b8b424c9d90bd0000002460640000000000000000000d795800000022d0001731f90000001428000000002709468529060000000000000001a38001e624f9d78b713c80019c00000006d90b00002619e18b102a1a9c11cb11a83a10180017d80021b80a00000005d0ea17a9ff8000000fa80000022499984fa4590481b094226a5b14e134a0f81e9fe9a8241a1a0ca0c29a981180008b8000000000002230418eb00f1a21ce1f80001f20000da0000000000002448002701149d6800107126800000034a0c00010980000011c8402330598f98001e68001c40000000000000719d10620001a107680012a8320001e49b28dba001430c500496880007e11088a00001700002711d1040002570002050b2a0e16c800229216a531e381601f9ea0000d900009205a8328000548000000001da0000000f806691b1ea8000568f400000000025900715b9621870df02a98208713e86180018e81b89aa3a9409298001f602e22a24d8000ada5f151a0d07a0cb08c9b900000019fa340919ec0b08bf0f782a19185ba070000000000000000000000000000000148000fe8a215200000000000005380000022100015ca509669691c70bb03b8001c018581924513a97989c8000000001640a40000639f58000001738000c000000000015f80000000000000016
  | 11 => 0x18b9111cc2008ce8000000000be1260700000001461bc8c78000e508f1230749f9a4ea0e8000000001258000001781ee82ca160000018f625d88d88217517ba180510448bf80004c8cc1be0c10001a51a60000000000978cf24ba261daa1c0001f5165800000036a5b9d389f1980001bd0000001829c68590e8018a100381ac00000000011a01791f96fa0980000906b0000521000002668131f096aa6a03da108000558f90801ae00011f02d0000cc9e214c0000000000001b997900000000004910d0250588d1a15a0280016481d9ce8000000d12048981cf84987600988111e1038d207322e00000002380019f0ac838a6e97119e8d68001698000519ac93a00000000000000000006884da5000000026301c9ae8002020e089097a20f02d986800086a6014f8ea83e09980018a88c0891de8ca8428001c0800013a2700000000000012c00008380000000000001f00026d0b318100000000000000000000000010086e02018f8679aa80000025186a2438001e89938000000000e98d700023e80000014f1e400003c9168000000001d88fc1ed81299100000000014000021980010f8001628001aa14898e1ef14192800000000000013813d1540000001678001fc800238070a3f80000000026100000000000000018a00000013f9e712700000000005c15680006f80000000e0c18000e68002648000000002552288f485e9171721930a686ea6ba35269800112a5804b97593687700014c8001df8729e31ab0481479bd80c99518480023019d8001218c5800000089a278000000000000ce0001191a30bea478f30001979440000000000d087f8888398000001b617f8000000000000000000000000c885f25d00000000025a03f03614107910323f0e58df9058581361bf90d8001339d4a5e2390000011ee1a29961b20d01af15d00000006b8001010300000830a71c78540000220000000929cba640000d81b4a6800000000000000019026c99d0c30000000001538000430002220001f29f380000008f8000f88000000000000001852091d71fb0c481d0000e90000000391351530e78a795c17e800000000000115a1f8002040930fd8180028f59248cd8c908a9501548000000af0000000000000610990aa8000000000000001f40000378bc8000000000309d20ec0000d51a49be80022b8001090fd0dc89b0ae1de1b88000000002170000000000000000001239c480024120883f8058000000001a40e11bb81080000002b1fd9f68001b689d22380004c06a8001908b884889f91400006800000013d96d0eca1d8001b800000007c8001dd0001e19dc0050000000758b10cd0560bb8d890207a92200000012516014380009700000000000002ba3c8c80002370000001e81838001881ff0691342038218dd8000000001321fb927a30
  | 12 => 0x1c300000b00000006300000018780600000000023b1d615d8259af96ea338a88281619ab87b0baa468000000f10002218000000880000000000000000000001cd8000000b38468000000c60002128da8d60ed00025615f1e087d9228000001800000000001b51671d018d2609499b401a1491c18002658ff027a2c0000738949d0893834135a3e0e480015a8000000001c614525c98c8001fc00022b00000000002f8000f080000021e80007e80001694e931a670002481d981100012b0902558000aa00000e80000012e1718b90e7174a078002662110001dd80025692f80000025400000204a843a358861420001860d40001510000000000cf9890b994a00019b9558002241f79d409580000013100006f1dc80000000000000025c21f0000000000000b187ba4c09b9958b61a794808286c0f189e9bf1578001e28d302900d8961ca80019c80025115e9b78000310a980000326f80000022580000000000000000000000000011000007886480000013780015280024200000000018421500017f00010f00023100000000000000000000023d00000021e21380004d107a3d8000000001971a59d500022d8001fa1ec8000478e280000000004507780000000016e000000000105000000206087a0c9448de00000000001510e00000000000000000080000000000000000000000a8000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x4012e2980877058d21004b8660211c163484014e1900867694d2100538640215da53484a98e0800857694d210056864021dd153484014e1900867690d2100538640215da43484a98e0800857690d210055864021dd5434840156190085751812100568640215d060484015c190086731812100570640215cc604852741c955cc735925000607615731cd64940016a19008564486502a7281c021591219412781e861d36354d50004476607418d535412721e98d915390d5000538640219d921540014e190084764855049d07251731cd659000181d845cc7359640005986402159521900a9c6070085654864000487a6054dcd655000141e97153735954000487660541cd655000141e97150735954049c0fa63655d2535012781e861d76350d40004476607518d435012741e97d965350d4004c872616554d435001341c975955350d4015e0721d6554d43500014e190086764854000538640211d9215005703d98d97745414015cc62615350d505005732898549425414015ccc2615150550500014e190087764873000538640215d921cc00141d9315376552300040fa60545d9548c00141d9315176552300040f660549d9544c00141d9315276551300050764c541d9544c12783980150765513000538640219d9214c0a98c583084764853000538640211d9214c001991746073294130006625d182cc6504c001951756073290130006525d582cc6404c00103f985d0745943049d0724d741d1650c00103f985d4755903049d0724d751d5640c00103e9815376550300050764c54dd9540c00103e9815176550300050764c545d9540c12781c8315176550300048be6154151620c12760c9355054588300068355183151620c0a94e0905c471588300048de6154151610c1276149355054584300068555183151610c0a94e0905c872584300053864021dd9210c0014e19008576484302a638200215d9210c0016619008565484302a7181c021595210c0016a19008564484302a7281c021591210c00141d9315376552200040fa60545d9548800141d93151765522049e0720c545d954880014e1900877158e2049e0720c74595538812781c831d56450e202a638200615ca53480a98e0801857290d202a638a1c61dc132480012e198184704c9200048de61541536148001a155460c54d85200050764c54dd9548400103e9815176552100050764c545d9548412781c8315176552100053864021dc9638412781c831d16554e1049e0720c7559143840a91e297e0532482102a638200625c653440a98e0801897190d100048be61541536244001a0d5460c54d89102a638a1c62dc131440012e198188704c5102a4b8a5b824c62044077cc0764c9314811037e381db83485204400b1e09760d214811002cb82598348520440778e07660d2148110
  | 1 => 0x98001c8b80000220040000000dc0000002400030000e01c3f000010000141a8d60037000d845339f0e07302a04660403a44145a1e80058860008916320018062780620cf43a0000052693c8012c0f0019110033a8091e13041b4e8972e9591a101d99512711b0ac24403f92094942589d1c0000098420920858007b12000000000034d0001f0b4fa5f4a80000000000000000c98c9c061a87800760024822002f1990e00000f0a2001780016590d8009e1c12800005042001142a0008c8e003798830932b8002e002a000000000050e40000000008c000000082001dc84530014800340d080b6852a9182a492e1f8000026984861f2c0740000070801000f090208120500000000010000050503080100010010060a030400000300000f0805020e0202100105131701010050ba58545c8635500150d931517218d540050da58545c46355001515931517118d540050ea58549c06355001519931527018d540050ea58545c06355001519931517018d5400447a6054dcd605500141e96153735815400447660541cd605500141e9615073581540050764c54dd16094c0141d93153755824334e071db805515350c0123798550545873249d8524d5415161cc801a155460c54587322a538249701c161cc8018e1825c070587320040f660549d9544c80141d9315276551320050764c541d9544c80122f985505458b3149d8324d5415162cc401a0d5460c5458b312a538245701c162cc4018e1815c07058b310040f660549d9544c40141d9315276551310050764c541d9544c4775449754932545311dd6125d424c9414c4011e2980877058d2100478660211c16348
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x23c4e30c0c4014d080000240759440128049c42952aa3062a2c39924e20ca95518315162cc4a90705432010aed29a42548382a1900857690d212a49414ec8042b224328152460a764021595219012780cc03262a0ecaa26054c3060d90084764853049c03950c98a8bb2a81824e20ca955183151620c12710a54aa8c18a8b0860548382a19008576484302a48c14ec8042b2a42181524a0a764021591210c12700e543262a2ecaa440938072a1931517655210
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94b
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x4
  | 10 => 0x124b
  | 11 => 0x124d
  | 12 => 0x124e
  | 13 => 0x98a
  | 14 => 0x98d
  | 15 => 0x98e
  | 16 => 0x128a
  | 17 => 0x128d
  | 18 => 0x128e
  | 19 => 0xca
  | 20 => 0xcb
  | 21 => 0xcd
  | 22 => 0xce
  | 23 => 0x9ca
  | 24 => 0x9cb
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12ca
  | 28 => 0x12cb
  | 29 => 0x12cd
  | 30 => 0x12ce
  | 31 => 0x168a
  | 32 => 0x168b
  | 33 => 0x168d
  | 34 => 0x168e
  | 35 => 0xa0a
  | 36 => 0xa0b
  | 37 => 0xa0e
  | 38 => 0x130a
  | 39 => 0x130b
  | 40 => 0x130e
  | 41 => 0xa4a
  | 42 => 0xa4b
  | 43 => 0xa4d
  | 44 => 0x134a
  | 45 => 0x134b
  | 46 => 0x134d
  | 47 => 0xb0d
  | 48 => 0xb0e
  | 49 => 0xb4b
  | 50 => 0xb4d
  | 51 => 0xb4e
  | 52 => 0x16cb
  | 53 => 0x16cd
  | 54 => 0x16ce
  | 55 => 0xb8b
  | 56 => 0xb8e
  | 57 => 0xbcb
  | 58 => 0xbcd
  | 59 => 0xcca
  | 60 => 0xccd
  | 61 => 0xcce
  | 62 => 0x170a
  | 63 => 0x170d
  | 64 => 0x170e
  | 65 => 0xd0a
  | 66 => 0xd0e
  | 67 => 0xd4a
  | 68 => 0xd4d
  | 69 => 0xe8a
  | 70 => 0xe8b
  | 71 => 0xe8e
  | 72 => 0x178a
  | 73 => 0x178b
  | 74 => 0x178e
  | 75 => 0xeca
  | 76 => 0xecb
  | 77 => 0xecd
  | 78 => 0x17ca
  | 79 => 0x17cb
  | 80 => 0x17cd
  | 81 => 0x104a
  | 82 => 0x104b
  | 83 => 0x8a
  | 84 => 0x209
  | 85 => 0x150a
  | 86 => 0x1409
  | 87 => 0x180a
  | 88 => 0x198a
  | 89 => 0x4b
  | 90 => 0x138b
  | 91 => 0x1549
  | 92 => 0x180b
  | 93 => 0x198b
  | 94 => 0xa09d6
  | 95 => 0xa49d5
  | 96 => 0xb49d3
  | 97 => 0xcc9d2
  | 98 => 0xa12d6
  | 99 => 0xa52d5
  | 100 => 0xb5693
  | 101 => 0xcd692
  | 102 => 0x14d
  | 103 => 0x138d
  | 104 => 0x150d
  | 105 => 0x198d
  | 106 => 0x10e
  | 107 => 0x138e
  | 108 => 0x150e
  | 109 => 0x180e
  | 110 => 0x3ca
  | 111 => 0x15ca
  | 112 => 0x144b
  | 113 => 0x188a
  | 114 => 0x160a
  | 115 => 0x184b
  | 116 => 0x148b
  | 117 => 0x1a0a
  | 118 => 0x164a
  | 119 => 0x19cb
  | 120 => 0x14cb
  | 121 => 0x18ca
  | 122 => 0x1a4a
  | 123 => 0x24b
  | 124 => 0x154d
  | 125 => 0x140d
  | 126 => 0x144d
  | 127 => 0x1a8a
  | 128 => 0x194a
  | 129 => 0x19cd
  | 130 => 0x14cd
  | 131 => 0x154e
  | 132 => 0x140e
  | 133 => 0x144e
  | 134 => 0x184e
  | 135 => 0x148e
  | 136 => 0x18cb
  | 137 => 0x1a4b
  | 138 => 0x15cd
  | 139 => 0x1a8b
  | 140 => 0x194b
  | 141 => 0x1a0d
  | 142 => 0x164d
  | 143 => 0x15ce
  | 144 => 0x188e
  | 145 => 0x160e
  | 146 => 0x5cd
  | 147 => 0x74c
  | 148 => 0x1a4d
  | 149 => 0x194c
  | 150 => 0x58e
  | 151 => 0x18ce
  | 152 => 0x1a8c
  | 153 => 0x9692
  | 154 => 0x8a12
  | 155 => 0x8a52
  | 156 => 0x9ccd2
  | 157 => 0x5693
  | 158 => 0x4a13
  | 159 => 0x4a53
  | 160 => 0x9cb53
  | 161 => 0x9ca16
  | 162 => 0x9ca55
  | 163 => 0x12ca16
  | 164 => 0x12ca55
  | 165 => 0x168b53
  | 166 => 0x198a55
  | 167 => 0x15ccd2
  | 168 => 0x144b53
  | 169 => 0x1a9952
  | 170 => 0x1a9953
  | 171 => 0x5d2d5
  | 172 => 0x5cb55
  | 173 => 0x5ccd5
  | 174 => 0x592d6
  | 175 => 0x58b56
  | 176 => 0x58cd6
  | 177 => 0x180a16
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2247
  | 6 => 5692
  | 5 => 1250
  | 4 => 152
  | 3 => 16
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
  | 7 => packedAt gbK7 (92127+((h/749+packedAt gbK7 (83139+(h % 749)*12) 12) % 3262)*13) 13
  | 6 => packedAt gbK6 (297877+((h/1897+packedAt gbK6 (273216+(h % 1897)*13) 13) % 6831)*14) 14
  | 5 => packedAt gbK5 (78326+((h/416+packedAt gbK5 (73750+(h % 416)*11) 11) % 1997)*12) 12
  | 4 => packedAt gbK4 (11040+((h/50+packedAt gbK4 (10640+(h % 50)*8) 8) % 221)*9) 9
  | 3 => packedAt gbK3 (1321+((h/5+packedAt gbK3 (1296+(h % 5)*5) 5) % 22)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x8e381c7e1c71c0e3fc7ffe03ffc3021e10f3cf
  | 1 => 0xfc01f8fe07e00fc7f8e0ffc0fcc0c66633d33
  | 2 => 0xf0001ff1ff8000ff8ff00ffff030307983ce3c
  | 3 => 0xffffe001ffffff000ffff00000003f81fc0fc0
  | 4 => 0x1fffffffff0000000003fc001fff000
  | 5 => 0xfffffffe0000000000000000003ffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x409041208204820901382014503020a105045
  | 1 => 0xa424884a0521244248424a80a8c0c24612512
  | 2 => 0x900491215480248909204952a0303051828a28
  | 3 => 0xa290c000651486000e48601820801480a40f80
  | 4 => 0x19a6938f240008060c31540015bf000
  | 5 => 0x4d271e4800000000000101830c2aab7e000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffe8ffe8eae8ffffffe8ffe8eae8ffffffe8ffe8eae8ffffffe8ffe8eae8ffffffe8ffe8eae8ffffffe8ffe8eae8ffffffe8ffe8eae8ffffffe8ffe8eae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_29442
namespace PEqualNP.Outside.L_meta_29442
open PEqualNP.Outside.L_meta_29442.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 7 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 5 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
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
theorem bgb_3_0 : Interval gbAtlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 16 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 152 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_1248 : Interval gbAtlas 5 1248 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1250 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))))))
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
theorem bgb_6_5664 : Interval gbAtlas 6 5664 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5692 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))) (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))))) (concat (concat (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624))) (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))))))) (concat (concat (concat (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520))))) (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))) (concat (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))) (concat (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)))))) (concat (concat (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)))) (concat (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))) (concat (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832)) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))))) (concat (concat (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))) (concat (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184)) (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280)))) (concat (concat (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376)) (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472))) (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664))))))))
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
theorem bgb_7_2240 : Interval gbAtlas 7 2240 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2247 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376)))) (concat (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 (concat bgb_7_1632 bgb_7_1664))))) (concat (concat (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792)) (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 (concat bgb_7_1920 bgb_7_1952)))) (concat (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 bgb_7_2080)) (concat (concat bgb_7_2112 bgb_7_2144) (concat bgb_7_2176 (concat bgb_7_2208 bgb_7_2240)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 2 zero,inputs.getD 7 zero,inputs.getD 5 zero,inputs.getD 0 zero,inputs.getD 3 zero]
def fullWord : Sig := 0xffffffffffffffffffffffe8ffe8ffe8ffffffeaffeaeaeaffffffe8ffe8eae8ffffffffffffffffffffffe8ffe8ffe8ffffffeaffeaeaeaffffffe8ffe8eae8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_29442.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,5]⟩,⟨.and,[8,7]⟩,⟨.or,[0,3]⟩,⟨.and,[10,6]⟩,⟨.and,[2,5]⟩,⟨.or,[1,7]⟩,⟨.or,[4,6]⟩,⟨.and,[13,14]⟩,⟨.and,[0,3]⟩,⟨.or,[9,11]⟩,⟨.or,[17,12]⟩,⟨.or,[18,15]⟩,⟨.or,[19,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_29442

open PEqualNP.Outside.L_meta_29442 in
theorem PEqualNP.Outside.L_meta_29442 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
