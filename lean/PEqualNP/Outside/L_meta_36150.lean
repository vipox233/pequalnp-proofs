import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_36150.Model
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


end PEqualNP.Outside.L_meta_36150.Model

namespace PEqualNP.Outside.L_meta_36150
open PEqualNP.Outside.L_meta_36150.Model
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

def SBf (j : Nat) : Nat := [7, 7, 8, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36150

namespace PEqualNP.Outside.L_meta_36150
open PEqualNP.Outside.L_meta_36150.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2a18e800000f0052012a3566022a22040000a2121714006193e081a1405940f4e4d3123488d90005048e3834587001c300038e1081c104f2c1ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1402cb8e000d400d0b4b0ec9ce8a034007c0000a400a800f12c010410010c5c40840c7000e450005868ac00fc780138008800000090040000000065456400c8000054f800c554cc25301d34000000000800755800006c013d480014015c00008d1500dc3c004cf4011d10c0494c3801686044192494010820bc003120280080d919295160980034000c004c04020200040c0e0e02000000001006020c00000e00000c033e5390e7aa321db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010f72a021d794e42aea9c859c43ccaf4a1995e543329f2a4653d548ca7ea8994f15132ce21a653e53d067aa920d7d4d41ae29a839f5350678a6a0e714d418e29a83b7515067ca820cfd53319e2a6633e548c67aa918e710e31daa0c633f544c678a898ed505319f2a0633d540c7388618db94831b6a90637a500c6f2a018cf952219eaa4437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53902baa7206710f30b7296616d52cc27ca9184f552309faa2613c544c33886984f950209eaa0415e53082baa6105d94420baa8841e9200827ca9884f55310b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x6a488aa02716b9022c7aa018100506300c2681200e00000050302428b265254443c95495110f315194043ca5495010f315154043a558443ccb184354332a5584434cb0e6214d41c358853507156114d41c698053507196014d41a5584438c69463506318d195414c61d6510c31c310d520c71843540318718d54886956110f30c310d52cc2956110d30d8545200821c6355310
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x624801445c44354332c0ac4b08a6a0e09625805350708b0ac029a83415c44354b30
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
  | 4 => packedAt s0K4 (2697+((h/30+packedAt s0K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s0K3 (990+((h/8+packedAt s0K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s0K2 (248+((h/1+packedAt s0K2 (245+(h % 1)*3) 3) % 8)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x78f1ffc3f8fc7e3c71c0e3fc7e1c3fe30f70f
  | 2 => 0xf80fe1ffc7fff8fc07e00fc7f8fffc1e4339f3
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x50118484921288014304a2094124414c305305
  | 2 => 0x2221009040401080421044208509010412052
  | 3 => 0xa5444912212900368802489092092a81828c28
  | 4 => 0x31004ca081019244d1486000e48c08c4940f80
  | 5 => 0xc6089103364e249b26938f24001033196bf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffcc0fcf0fcc0fffffcc0fcf0fcc0fffffcc0fcf0fcc0fffffcc0fcf0fcc0fffffcc0fcf0fcc0fffffcc0fcf0fcc0fffffcc0fcf0fcc0fffffcc0fcf0fcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36150
namespace PEqualNP.Outside.L_meta_36150
open PEqualNP.Outside.L_meta_36150.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1e00c80244c0004a0001b0000000005450600000002098ea0042120000a000000ac000000021a2e8c701420000000014830000000180000b00153aa00000072c78000000001c223400028011003e004800000c000000000030400002121c2870210100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x11001c9225898cac001f15869e2399109b9517842d99989b2786231f9c020a13802700ad04a42891961698050f038b012902800d20a2a4a68b80170307801a8914a10c1e8000000e00002607220000002c8da50000001312aa9d2a202b1a01a80f94088e8008219029800a9dab858001000e245840230786000811310206800e0408808143800030003b7294876d5290edca421db54843bb28887755110ef4a021de54043bb28e857551d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290656e52d06daa5a0eb94b41d6a9683ae32d075a65a0cf55241d719283ad325076ea2a0cf95041b7296636d52cc79a6598cf952319eaa463b5418c79a6498ed505319f2a0633d540c6dca418db54831bd2806379500c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af298815d53102dca4205b54840bb288817551102dca5985b54b30e6996613f544c278a898734c9309f2a0613d540c2dca4185b54830bb2886175510c27ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a83885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xa00306003ced021200014472c00000001182000000000000000c10008d586548caa56195232a3993534cac56110d32b2580434ca4d6394b41a358e52d062d658cb41a998b51507853250531c554d410873141540218d584544c30c544c9309358c52443245250510
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x4c8090ae3326a6994857398b5150682b88a899261415cc5250510
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
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
  | 4 => packedAt s1K4 (2694+((h/30+packedAt s1K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s1K3 (638+((h/5+packedAt s1K3 (608+(h % 5)*6) 6) % 39)*5) 5
  | 2 => packedAt s1K2 (199+((h/1+packedAt s1K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf3c78f3ffc7c7f1f8c470c7fe3f1f0f80f4cf
  | 2 => 0xf03f80fc63f9f8fe3f0780f8e3c7e7f1934b33
  | 3 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 4 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x1040110004008020000100120090100001045
  | 2 => 0x10882222049101404204844848428241114112
  | 3 => 0x22035449492492a00dc80a92129054ac628c28
  | 4 => 0x44111009120080249151220003245024240e80
  | 5 => 0x88a26082403524c926a64ce4980080c95be000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffaaafafafaa0fffffaaafafafaa0fffffaaafafafaa0fffffaaafafafaa0fffffaaafafafaa0fffffaaafafafaa0fffffaaafafafaa0fffffaaafafafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36150
namespace PEqualNP.Outside.L_meta_36150
open PEqualNP.Outside.L_meta_36150.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630bea8c617e508c3f481187e50230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3be6298774c530fd20261f9404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec82887d50510fb18a21f531443ec42887d48510fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ee21e657e51ccbeca3995d94732bea8e65f551ccaeaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a89977d0d32ee21a65ee424cbda84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83be43d077887a0df94b41f7296836e52d06faa5a0fb54b41b6a9683bf42d077a85a0df94341bea86837d54906fca720f794e41af29c837d53907baa720d754e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f7d0f31ee21e637e52cc7dca598db94b31bea9663ed52cc6daa598f7ccb31ee996637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf294637d528c6fca318fd90631faa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7b88698dfd4931be29263df324c7ba6498fd90531faa0a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fd90721faa0e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887dc8510fb50a21f719443ed32886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821f721043ed42087dc6410fb4c821bf28843f641087ea8210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9
  | 2 => 0x7a4905983606510a474389d4158600000460de8c151a1c0000000000014c1101e17c0008cc840954ce5345083507e75cf993e53c8242da0b44c1553c8945323d93f1e32a6a18a4175224718cb82414422c91a63414808002a015c498a3a204884f46d81d2a842c319210002207d2a94d4a693a00052619c0029b11a60942a83190000001872d63900000053e33d3623c138a451b15928c8b0149680dc37d2c1f22184644925f52c000002770000b05f00026c7551d17a22e1ec2c9220fc38c6b0e9118869410ee3303a02724d2dc7ad228e70206a8efa56208184ae0050c00000000031e11cc21c300007cca8f23b200054a921bc418170003146e40020103053000000442000002083820009f8000007a8109ee3667b40013c000930000000001ccfb85a0006709017b05e000fa0533c8000db911000000000c9000864070004501fca81e80003e0b92a52001146621b202a74000000002f5301ca1d8680d69a902a848a91a51ca0700022d096630568000009747b800452814449d854c000ad1740006e0702380007f4bc8cb1ea794f313a0ec1acdf9994823006909314821c208001a6001342473f6129078ff47c47c7e2401f61f5380004cc9ad4a9e9050508d600b000860201f1000000000001726687f1342602bc5526938a634001cf1ae6f13ea3d1820140204c0104000008060580e034010041a0001003c0300001000000ec010500003c05000010d821010030080a01c01000050540b0380400476024230000102c2704c020081c058120000e0000f020080240008c050000306414004020640700000000010000001421004080001200c010141d0081e0040802000018010000001c080741407c1201400004000140e0140d08419000180ac05008140000000004004040281903800014030500300c0a0080c04c000101008c3901800000120080103491004000700c004170200001003004040040000400000020080d048010000201007000000c018018040001701c0301c03008180000402000000080380a0000e00009000000a80303c00000230100505405018000241700000006fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443fb28887765110efaa221fd54443baa88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85be43d0b7887a15f94742fb28e857651d0afaa3a17d54742baa8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857
  | 3 => 0xf38250000006387a348338000000007f8000004f04400000046e3682b92e4de94079a2f29640c0f09931c294ee85f01a30c939572141e034a7c4c83144807216a0dc9ca8a30a2384f8740002001a0072e23888722b3f8000c194f13c0e9152a80001712d0003a400011a840a406800232000618cf032114310000000000594380032620cb10140006207519452e93800000000000ab18136a13ce116d2fc71c412550541f0dd196500204101910143ace58061a87fc709bd1f28e41821f04c5907311526a4588d9ef42895cf61145286c483a1e3e028d4e10535c9ed0b84d2ca3605900418c03ca50333ac648352594fe2609680000009d24a3125e4cce024a4ca88d310000007810815f39010d399be06c0003315d000000d581700078400000000158bb1f82e6944cf9fa16c9b5031af21e948fa8000a8000001093880ec0024643a328040004dc6ec001db2ce000681a100093d088000000313916a000000d189d0a01dcd90ef0240b506000000088e71b600006501a6141c1453a8014841c00000000058cb0864176001110001a277929a2407a2e13b0cd51a8fd4c13712c5045e1134b64c8bf98b24a524be8a04e28001f0023121242e92c256835129553c4510049b40004e1458003f24a000000000478489310000c4cd8002b6a90001d11fa8d45f8d51da734001da476724ac1510d04702f16c0f24687809a51289cb812a2c00e4869d316800c00000166000158003988b83695e0365e0539a740e460cea434b85dcd424b4bc515470001baa85478b73440007a2882de0e06c9f62861d50a94e2522e8420dc2804082113b468640ee08f1621889228136025c430a8426309460ab54e3c4099690b08100004c544120089d034c26c580005208592a2
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x514823d64145209798c514825d6314520cd99051483356414520d598c51483556314520d990851483654214520d98c851483653214520dc580514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020b9185200836551480209ed95200837151480209798f54c425d63d53109b98a54c426d62953108f99353c423d64d4f109b98a53c426d6294f108f99052c423d6414b109798c52c425d6314b10b558e41c42b5648c710d914921c425f63552109718d548425e63152109758c548426e62152109b588548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e6414a108f590528425e6314a109758c52843675208610bc58021843e02188210bc18520843e321482109b98a544426d629511097d8d544425c63551109bd89544426c62551109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109b98a524427761549108f990524423d64149109798c524425d63149109b994524432e6414910cb590524434e6314910d358c52443656114910da58052442d56390510d914a41442746550510d914941442b5648c510d914a3144274654c510d914931442766588510d914a21442746548510d914921443685288110f888620442786548110f8485204436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109e980520427565c8410cd553210435553c8410d954b21042756508410cd55021043555308410d954821042f16008410cd553100435553c4010d954b10042796584010da54a10042776544010cd55110043555344010b9189100436552440109ed9510043695244010
  | 1 => 0x873a5454021ce551500875a5354021d654d50087e12154021da90950087694254021da8c950087693254021dc90550087714154021dc8c550087713154021dac8550087722154021da48550087712154021d8485500865e6394b409758e52d02b561d0b409798e51d025d6394740ab58b41d02b96010e409dd8552902746154a409bd89519026c62546409b988535026d6214d409d98453502756114d40d3988535034d6214d40d598453503556114d40d6580535023e65d0d40c714f435031c5350d40c714f42502b561d0940c714d425031c53d0540ab58b415031c5350540c714e405023d6590c40c754e431031d5310c40ae580431034e5394840d354e521034e5354840d354d521032e4354840cb10d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103364354440cd10d511031d53d0040cb54b401033551d0040d654e401023f6550040a718d401031d5350040cb549401033551500409ed95401035953500409b98854cc26d62153309d98454cc2756115330c715143cc23e6494b308f59252cc2d561ccb308f99251cc23d6494730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b6580438c2776154a309d185528c26f62546309b189518c3984390230b618d408c39b43502308f992544c25f63551309b988544c26d62151309d984544c27561151308f994544c31d6315130cb988544c32d6215130cd984544c3356115130ce580544c25e6590d30c7152434c25c6550d30c7151434c31c54cc930b5587324c31c544c930c7153314c2cd62cc530c7151314c3385490130e690e404c2786550130e650d404c31c548c1309b98b540c26d62d50309d987540c27561d50308f596540c31c63550308f990540c25e63150309b988540c26d62150309d984540c27561150309e980540c25d65d0c30c7553430c25d6510c30c7550430c2d96010c30cb952520c32d5494830cb951520c32d5454830d3d0d520c34c4354830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430c7553300c34d52cc030d5547300c339548c03097d95300c29c644c030c7551300c34d524c030d5545300c27b654c030ce551300c25e63d53209758f54c827661953209d58654c823e64d4f208f59353c82766194f209d58653c82cd6390b20ab59232c825f63552209718d548825e63152209758c548827661152209d584548823f6454e208f191538823e6414e208f59053882766114e209d58453882e960086209d9865448275619512097d8d544825c63551209dd85544827461551209d98653482756194d208fd91534823c6454d209dd8553482746154d20b358e424826c6550920ab592324826c654c9208f99
  | 2 => 0x6494732cd59251ccb574354732d510d51cca7661952329d586548cb2e6295232cd986548cb356195232cb951428cb1e54cca32b9987328ca7661951329d586544ca5e65d0d32c7550434cace6210d32b5584434cad96010d32b398e424ca6c6550932e310d424cae661cc932a7992324ca3e64141328f590504ca7661141329d584504ca5e63d50329b988540ca7661150329d584540ca7a60150329e580540ca3e64948328f592520ca5f654c8329bd95320cb1d5310f41ab58843d06b96010f419798e52d065d6394b41d398e52d074d6394b41cb90d52d072c4354b41cb94942d066e6294e419b58a539074e6294e41d358a53907566194e41c794f41906e662d0641ab58843506b66110d41ae58043506b661d0941b998b415069e63905419798c505065d63141419b988505066d62141418fd95411067765504419b98b54cc66d62d53319b98854cc66d62153319e98054cc6796015331c755043cc6cd6210f31b658043cc63e6494b318f59252cc72e6494b31cb59252cc74f4354b31d310d52cc74e524cb319b98a548c66d6295231cb98a548c72d6295231cd986548c7365450631c7953318c6e662cc6319b98a544c66d629513197997434c71d5410d31b3588434c6d66110d31b6580434c6d661cc931b598e414c6746550531e510d414c6e662cc531a7992314c63e64141318f590504c66e62141319b588504c65e63d50319b988540c66d62150319d984540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c65e63d53219758f54c863e64d4f218f59353c86d56390721ad59231c865e63d52219758f548863e64d4e218f59353886cd6390a21ab592328865e63d51219758f544866d62951219d586544863e64d4d218f593534866d6294d219d586534863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d6595021cb98a540873661950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a53087566194c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530866d6590821b358e420874d5390821b9586420872e5450821d354d420866d658c821ab592320872d548c821b9586320872d544c821d394d32086756590421b558e41087555390421b958a41087365450421d554d41087a542504219d59631086b5648c421cd55231086e5628c421cd5513108756534c421f14c931086e562884219bd9521086776548421b9d9521087676548421b9d9121086e56448421e995121087a55448421b9d8d21086e56348421f194d21087c55348421b9181210873a5494021ce552500875a5394021d654e50087e12194021d9485500
  | 3 => 0x68b080a0947c001491d92be7095d80036290ca1a08000000020000008787328a59c0013e8c9000000e525c000000509a9000460001bf0d4000001d52c4000000e1000a6d3a8000008ec0016f0784100005239a17c00071000000b380035e000a226a0300000025923636c0000007e6b55b042000834002a5000a04248002d2328499e70005195c1143ba0000027b45e0015a1ed3f6000001e900000054800106974002701dc0a4001bd53c500b09861e0000a380000028d1a81055c44485800000710001f70d26584e840516a242ca655922500000058000168ac214e3ac9e9fa45a9d0f41f50567e0330770000005827c4bea691401b10e0011ea97000a4c0000029e170981ae0c294cdb00004aa5946211182778001a54de001650fb1bc9c4000dc4e60009f19b07c00000000000838000d7000000001bc3dc0b0ee000002688008008000060200180600e000018020000000380000200c018000000000080a00000000004000000008000000080000500001406803000000030020040680180000200800803002000040030040000400000001404801000004018040000780380700000c0000f0020480180000400400002002000008070020080000900e00c020020000400000700000c028000020000000100600c008000000000100800003c000000000180380800c0080000100200003000002000000000000040480000000000005000030048000000040000b00200c05802006000000030080040180101c000008030000000000300800400000004004000020200040000400c02c0200000e00c008090000000500301201401803000034010070000200080700000c0080000a004028040040200600000601002004000000008020020040000001e01802806004000000020040027661d49439d5875250e6e62d45439b58b5150e6e62141439b5885050e7661141439d5845050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9f6150c43a71814310f8d4394843e350d5210f954394443d994a5110f655294443e550d5110f665254443d95495110f994394043da94a5010f695294043dc9465010f715194043c750d5010f994354043da9495010f695254043dc9455010f715154043ced0d5010f5a4354043ce50d5010f594354043c650d5010f1d5310f42ad58443d0ab96010f429798e51d0a5d6394742d598e51d0b556394742cd90d51d0b3443547429d9865390a756194e42d398a5390b566194e42d55865390b1e53d0a42b99874290aae6210d42ad5844350ab96010d42b99874250a9e63909429798c5050a5d63141429d9845050a7561141428fd954210a6f65508429d98754cca7561d53329d98454cca7561153329e98054cca796015332c755043ccad56110f32b658043cca3e64947328f59251ccb36
  | 4 => 0x4da000002ba00045c3a9cb210638dd19f112530b29e50f89dc5c82043e000001060f2000000001804d4be8000005808d0b8046000b989b5560000012d1de554289280dc65c1c8000009b05588e1eeb20b6a053a64580019c0146084300058a000000003340012588c50a0011a000000001438d633227ca0a8f00000067800498000f88272f203c35a7f25c13d6a2272269e0b624a17c3fd1c11e0000010c00000075000000376000ed0003a440d14800000000001a043601400102522001320000000000000000037c891eb0004889200000065168000000000001105086c81229547200109121318aa9679e21d02d07e000316000001510001289916e000000000441c6260000f342e0bc802a30f081c240950000006c9b90003d800000000034000000000000001a0000000017f000674481050ba2290a1494605c1668f40d0348000e521a00000000290a98e41be0009f859183004534000003b6aa4001260009152693b1c06d4000000c00013c91d4ce000000fe5980d8f1a0f3faa894305011a2688aa8854042946942000374c80c239c2215f20c4b00d0cf18f4e4000d09c70823112a26e0000f51b1e43bea74001501f4354ae000000000002a40005140005313c00000000000000000000009380a1f30006dc928004040000018115c000e604d0009415792319c704000000000000015d000000000001f20000015600049d4fa44408298790001fa0b44e09231031400184402918eb8000008cc001660fc64c001330603600018d0002f15b8560002a0230d43248e8000002d490400000000000a52c6000000eb00000047c000a01d84f0000003fc6a95a800000000000000000642c176000a50002cb49e00017298000744000000005c540043000000000001a27c80900027e8ac00290064320378000002d49ba2e48000015000174000000160000009b000000000369681e200058881000000000000000010015304cb040007003a890000634f4001638000000009a191000288000005640c5118002584e8d380c000000038004c40012a8ad0000013580034c73c001c5000000001781a04a400000196294000bb0000000a8000000014c8004d00dc0000000000128800000841290003601500000b0005c80f0990d8000d5800000470000005880000000000000000107066000262d30ce0180010f0009252b9540001550aaac2e87fc3e800000388000000000d4ad0c70003a4001c00007f000000240a9d0e263000614000960e6001589310004382597c0424e4d21e01660e800000000000860004cc5ec2f0000f4000000000007180017a5382a85e9520e4000000001d40015fa82000001030e40009d80000900053800000000000001c92c8654560c601c4e15e9a3000a0d109d80101d045a323cc000000004bcaccc01191081fc110f52d
  | 5 => 0x122001569f94260000022008a000d9a3c000000520c3000000000000000004b80009c0000026002600000000000334a5a4746e0000025a000b0c0015b1980a0000000b40015412f00098423800256628000000004a8d40380006e118a2a03e20842a69572560000ed0000000023f0005f912800000000000000000000015e000000002561f000001a8e5602fc00000000000ba8000000705b9e13861880b9984141ed212d236823c00248000741018003d896c7380015e000000000000ec000003d40006981143400032800000564fa17742ca850e963578200ab8da4447c03b06444c86400187000424c48000b60005b1ef3ec15d059ac
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x90007808c8000302c80151d801a28970312b2a1a406049a8e0b8fa9b1201c11001b8003a599b18c0017ab2ba11f9e86a524801880002a2d2a82a914909b139d000d80130a16278b1c802c1f2280000f20992305821826001001968022320d26afaf2800000008800e850a8107099e00002e11800000158000040023aea700001430ad880012000000c24140010103c00140008000c00000c000410000408181808000000283c10541e4ab8ec4a1887235cb6150c4391ae43028621c95711814310f82a1aa4a8887c250e5254043e1286a92a021f11439455010f88a1aa2a8087461d94354043a36e4a1aa021d1b7150d5010f0ca9ac021e854c5c04354742c32a8b0087995517010d51ccb0caa2c021a65615c44350932b12e021a84996195358043d0694b8086a9683865516010f31a92e021aa598e1954580434c6c2b9086a0a63645c04350531e0aa6a128210f05544c93108662b9ec890843295d36348421e0aa8a9a4210ca5741812108662b98c090843c89512154021e42a890aa010f425348550087a0a9a42a8043525ce4254021ac2e3212a010d29748c950086b0b8c64a8043545ce4154021ac2e520aa010f21425055008698ba462a8043585ca3154021e826498aa010d607648550086b1ba242a8043585d12154021ac6e690aa010d61734855008722b12c229a81925896014d40ca2c2b00a6a061453587425030629ac5a0a814a5c04354840a62e021aa22060c63549401030a31aa2a008186d516010e30934eda1a811862562584544c30cb1ac02a2618a5896015130c62c2b00a89861454587324c3062a2c598a61469d64390130c30caa1a809861954580430c2a4b8086a9061545c04354430838ecaa2601860c64549300c30a322a298061855916314520a8ae7210a290525748c85148318b22c028a419458d6014520c52a8b004210649535802108312aa0c2900419154c6148020cc6a4b0043084e276c852084306b22c6292218a5916014910c92c6b00a488661615805244322b18a520a2189590528c510ac4eb10c4088660654852044318aa2c0108219454d6008410cc2a4b004208625541891004322a98c488021191d95244010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xe40c06a0080201909821d94354043911811d9435404391181dc9435404390982dc54354043921841d92154021941831d9215402194183dd1215402192184dcd2154021
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20684+((h/227+packedAt s2K5 (18414+(h % 227)*10) 10) % 819)*11) 11
  | 4 => packedAt s2K4 (30201+((h/241+packedAt s2K4 (27550+(h % 241)*11) 11) % 1158)*11) 11
  | 3 => packedAt s2K3 (5270+((h/34+packedAt s2K3 (4998+(h % 34)*8) 8) % 135)*8) 8
  | 2 => packedAt s2K2 (488+((h/2+packedAt s2K2 (480+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 3 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 3 => 0x1a912289244a801ac80524849212530c28a28
  | 4 => 0x488c032520240c92352918000e498192540f80
  | 5 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36150
namespace PEqualNP.Outside.L_meta_36150
open PEqualNP.Outside.L_meta_36150.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5a4003c000001c98a50ac2193c14000069441a4c24b80200108052446810060f9d00180002400020009ca15008d500386c6024458700000010401410c7401183003ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x151d2799802482a815a9ac239d9b2c8011089c8c89960624000f19001781a285000e9f800c2300252680078380a61aa113a1a21b800da8ab169012119492a00b080f85820d2d0020870b8a010400290e180000001c00000300002d802b8a89270006a598931e142a2a849f1a1e90970189020010118c02813000228000000514202011e0019a0a5c106bb28c87755190edca421db54843bb28887755110ef4a021de54043bb28e857551d0b6ca3a16d547429eaa485af5250a7ca8215d94732baa8e653e548ca7aa9196b50a32d6a12653e540ca7aa8195d94432baa88657a500caf2a0195b94b41b6a96835e53906baa720cf952319eaa463b6548c76aa918dd54e31dba1463b5428c7aea698f5d0d31ea21a63b7424c76a8498f5cc931ea9926376510c67ca990cf55321d6a14433e540867aa810d794c21aea9843ad42086f4a010de54021af298815d53102dca4205b54840bb288817551102eca3985d54730ea98e613f544c278a898754c5309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320d6a1641ad42482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x6a881100603000f395096000072c0004259558e51d0a956394742a99875250a2d6295231a958a548c63565d0a31a5993534c6c56210d31b4580434c785424c931c354d420872942540218b588544c314544c5309558c51483254214520
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x42018090ae730ea4a148572993534c682b90a898a618158d4214520
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
  | 3 => packedAt s3K3 (633+((h/5+packedAt s3K3 (608+(h % 5)*5) 5) % 22)*5) 5
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf1e78f3ffc71ff1f88c70c7fe38ff0f80f1cf
  | 1 => 0xf01f80fce3f818fe3f0f80f8e3c0e7f3b34933
  | 2 => 0xffe000ff03ffe0ffc7f000ff03ff07fc438e3c
  | 4 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1020110004020020000100120082100001045
  | 1 => 0x10c4322a44925160430c86484a425263314912
  | 2 => 0x22014440892402800c90089210940488428228
  | 4 => 0x44481008520200249125220003229021140d80
  | 5 => 0x88916082803494c926ca4ce4980400ca6be000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36150
namespace PEqualNP.Outside.L_meta_36150
open PEqualNP.Outside.L_meta_36150.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0xdab4e21700003d3000000019004c58e343000000000000000014147162f482401000a8105000141200b4687406020000000000054f233a000a12c5c180000000000a52804400000000000000440003e00006000000080020008108080060000081ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa61dd314c37c80986f10130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6186fd0c30dea18617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea10617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea08617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c837e85907b90b20dea1641ed42c835a85907b8cb20f6996417e51c82faa3906fd0720dea0e41ef21c83da43906f90320de206417f548837ea9104fd5220bf2a4417d54882f8a9106f152209e2a4417f53882fca7105f54e20be29c41bf438837a87105f54a20dfa1441bd42882fca3105f54620dfa0c41bd41882fca1106f90220de20441fa30883f261107bc8220fd904417f544837ea8904fd5120bf2a2417d54482f8a8906f151209e2a2417f53482fca6905f54d20be29a41bf434837a86906fd0920f721241bd42483da84906b50920f719241ed32482fea2905f14520dfa0a41bd41483de42907b48520df20241bc40483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c530837e86106f50c20bf29041bf420837a84105f94420fb288417651082faa2107d54420baa8841bf410837a82105f94020df20041bc40083de40107e88020f690041f920082fea9885f95310df2a6213e54c42faa9886f553109eaa6217c54c42fea7885f94f10bea9e217c53c437e87886f50f10bfa96217e52c42faa5885f14b10dfa1621bd42c437e83887d90710dea0e21f541c436a83887d8c710fa98e21f621c43ea43886f90310de206217f548437ea9084fd5210bf2a4217d54842f8a9086f152109e2a4217f53842fca7085f54e10be29c21bf438437a87085fd4a10bf294217d52842f8a5086fd0a10dea14217d518437e83086f50610bf28421be408437881087e8c210fc98421fa20843f241087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53442fca6885f54d10be29a21bf434437a86885fd4910bf292217d52442f8a4886fd0910dea1221bf41443ec82886f50510faa0a21b541443ec62887d4c510fb10a21f5214437c80886f10110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2086fd0410dea08217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xe53886faa710df14e21dfa1c43bd43886faa510efd0a21dea14437e518877e8310ef50621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121df2a2433e54486faa890ef551219eaa2437c54486fea690df94d21bea9a437c534877e8690ef50d21dfa1243bd42487dc6490fb4c921dfa0a43bd41487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21dfa1843bd43086fca410efd0821dea10437e510877e8210ef50421f790843f621087da4210fd48421f2908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037e87206f90e40dea1c81bc43902fca5205f54a40dfa1481be429037a85206f10a40bf28c817d519037e83206f90640dea0c81bc41902fca1206fd0240fda0481bf539037ca7206f54e409ea9c81bc539037ea5206f94a40dea94813d5290378a5206fcca40df19481bd329037865206fd4640df28c81bd519027aa3206f14640df98c81be319037a63206f0c640df90c81be219037a43206f086409f284817f53502f8a6a06fd0d40dea1a817f52502f8a4a06fd0940dea12817f51502f8a2a06fd0540dea0a81fb405037c80a05f95040bf29881de53102bca6205f54c40eea98815d531037e86206f90c40dea1881bc43102fca4207b94840b7290817d52103daa4205b54840dfa1081be421037a84206f10840bf28881f651102eca2205f54440faa888175511037e82206f90440dea0881bc41102fca0206fd0040fd20081bd40103f280206fd4c40df298819e531037aa6204f54c40cea98811d5310378a6206fd4840df29081ae521037aa4204f54840d6a90812d5210378a4206fcc840df19081bd321037864206fd4440df28881b6511037aa2204f54440daa8881355110378a2206fcc440df18881bd311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc37e87987790f30dea1e61dd43cc33a87985f94b30bea9661bf42cc37a859877ccb30ee996617e51cc2faa3986fd0730dea0e61df31cc3ba63986f90330de206617f548c37ea9184fd5230bf2a4617d548c2f8a9186f152309e2a4617d538c37e87186f50e30bf294617d528c37e85186f50a30bf28c617d518c37e83186f50630bf28461be408c378811877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261bf434c3bc86986f50d30eea1a619d434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37e82986f50530ef98
  | 2 => 0xcafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7196fd0e32dea1c657e528cb7e85196f50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132df2a2653e544cafaa8996f551329eaa2657c544cb7e86996f50d32dfa1265bd424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865bf430cb7a86195f94832dfa1065bd420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0ef54f419ea9e83bc53d077ea5a0ef94b41dea96833d52d0778a5a0efccb41df19683bd32d077865a0efd4341df286833e50d077aa1a0ef14341beaa4833d54906fca720df54e41dfa1c83bd43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d419fa9a83be535077aa6a0ef14d41dfa92833f525077ca4a0ef54941de29283bf325077c64a0ef4c941de19283bf515076ea2a0efd4141df28283bd5050778a0a0cf14141bf2a0833e54106fca620df54c41dfa1883bd43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a663bf43cc77a8798df94b31bea9663bf42cc77a8598f7ccb31ee99663bf41cc77a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77e8718ef50e31bf294637d528c77e8518ef50a31bf28c63bf418c77a8318f7cc631fb98c637e508c6faa118dfd5131bf2a263be544c67ca898df55131deaa2633d544c6f8a898efd0d31dea1a637f524c6f8a498efd0931dea1263df324c7ba6498efd0531dea0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf29063ee520c6dca418df54831f6a90636d520c77e8418ef50831bf28863bf410c77a8218f7cc431fb18863dd310c7ea6218f54c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877e8790ef50f21dfa1643bd42c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437
  | 3 => 0x30000040000200c00c0001700c01404000012000020020060000000901011401000010008020030000000000400002c0181a00200000000000000028010040180000602c0240080101c0000080100200401000000000010100060080100000003c02804000000000030000100100400e00000006008000080020040240180100000c05800006008008000000180180000400001000002000000000000080080000200000802000008008070000000000a03a01800002000000000000000100180000202c0080000c004000000020040100402600400805006004008000000080180000400000002000004000010000000200001600c0101602600000001002008010080060140500100001c008030000040a00c0060000480600201c0100001200402000000014008000040180200a004010010020080180180d004008000000060000000a010000040040000000101000a01800006004000008010080000100400001400802000034000000120080000700001400005008008008000000000380600000c0280a004000000040100140880000200002000000008000010000140080001000800006002000010020020000000500000c010000040000000000400001801004014058030000000200000000402002000022fca5a1df54b43bf28e877d51d0efca1a1df54343dfa9687be52d0f7aa5a1cf54b43de29687bf51d0f7ca3a1ef547439ea8e87bc51d0f7ea1a1ef943439f28687bd50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa92873f5250f7ca4a1ef54943de29287bf5150e7ea2a1ef94543dea8a87bc5150f7ea0a1ef94143dea8287bc5050e78a0a1df950439f2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e853d53d0b78a7a16fd4742df28e85bd51d0a7aa3a16f14742dfa8685be50d0a7ca1a16f54342de286857d5490a7aa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a14fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5150a7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050a78a0a15f950429f2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32dfa1665bd42c
  | 4 => 0xb60001000000000003a80006ee00062e7260000000000004ec7ce3e60002ea0000002c40005445d20000000000002ec22031630a07452273400053e4f232035600000000000000000000019e0005b202200069e6441ae0005420000008463c20640000007585c61080004660005780001480000002de0001e400000000053c6220001c600017218a00048a82641a0c87166a06ce0e84d86542b00004c083442879e85800005a80400000a0000000000000000006ea1e83962840fe2026c20cc58426a09850c45c0601101e058a4fc5fc7bc2d62b42823f074c03e1fa14a0006a25b857a6b00a025237083e2a07ea00058672c0005180da7ba03a0007f883c0003be00016200082e0000000000000005920005585c800015c3fe00022200021e0000000000000000000000003980007001dc0000002b20004ae0000000002dc8440004300000001ac0000000000008360ea55c00059800017400000000000051a2a22ca0001ec4426ec4043ec4780003740002802e44fa8145ca24c8206086e81c80005f059c33806a0007ac83a5ec38c7d67d830449c4ca7a443a14600059428e1da3a400c5622084b04f41c21f004c1de7dc0c44e205200031e75e1421b80000000000000004844988566a876463e1284544b25263d22287445e642605c31022458c3b44187860260b866465228c6504cc0000bc4906600000000000005960004360007505c479266a1d018434013241038a00025c59e00023e11455a09200009e6bc48220426c7b67c83240c600045800037c00000030079c06c00004a24e0e60861ba1600102ba35073a67000081000000000060a7d20006040006728282423b029400054c5e45a636280e13463871070a4322f20a229002e6a61b273259a00056a50a6d83880004386c800081a28a00016400000071c00035c00000026e6f62fc2747740003ac23222a51c68004e2460000000000000003641f400000080a2e20000007aa0000000004a43660000006961be41c00076042a00000000076c6cc5ee0001408602bc4e60000000000000000000000002642560000000001d273c34a5d400000040671e3360f600066c20a0000000005fe0000000000000007e23ca47200000000006800000000000000000000e0004f000085248e0f81940000000002be7e00001fc2140007401ce4021780000006125b434836a0000007fc0446c40000004a00007ec1927621a400000078823411e00012c5742480000000005aa8240004446480000000000000007ee0003ce00000076680662060200025a00000000000065c50400000000000000000000000000000083204034610a3907800000000000003280000003cc0000000000007040002f80000c04ba45e0006b244a0000005ba5da226000000000078000000400280000200000001000028008
  | 5 => 0xe0421867d42da0000ac3e841418c00201a0a66b485a7300003f22382600004b450044c12648c00000000000020e0001ea3d60460a43081303ba79865a0007282fa49a6e40007e87f200000024401816634e00000000000007c0003aa4620000003ee7567a202a8407a00000e03300000003920000003f40000005608380000005f447074842231a3f655235a0546927846ca49437200000025000076a0000f000000000000056e0000000000000003801f85884c825e00060028819013c00000000067e00000000077854881200000074e6b84f80003b805855448600000056662a3de5be00820c23a0001886c60320000001380000007b27d00363340000007fa2780000002c041e00035836000065600000072e39a64c0003e00003325a022e0005e00000000000000dc68c46e29c84c75a70c13e1e27061d427252e37617051e00000000045009c4885164161c00624481b43680000ca00000072485e00000080208a31432e0007524da00000000060c82254a4346aa3a233a3dc02019a72010e0000006e60000004d66d00004080006d45d80000000000005822300003da0006300000000004be71800000061e01e84a8507ae2b82a62cc00021c67423c0005760001b60000aa69c8081ee17661a2762f600024a54631200015e7c647a3a000016e00000066200000078e0004000005f25080000d20004760000002a400000043c6d66dc0000000000006767da5cc00000052a05e2aa6c00000003060003182e049e5b032600000000067877266e0000001f200037e18e0000b40000000960000000ce3420008620000ec16a0b60000004b600000000000034400000000000000000008244e0000000000000000002c80007ca00064e3866f017a4d40002925ce10615a2f44920000487a80000f260e6145fa5a230203821a00043e77a00000045a7e600000085440c00011a0000005b60ee1680a80007f04201a800021600000077e00000067a7f617e42400055600055e00000016c0000000002fe1aa0000000004745ea26600036c81629e12a6ac08001c2703f80006fe1986160246d25a40003c42ac00000050e4400000002544b879430c15200012e6185020000000000000002ce3ea00000080c13a0006060040003e25641d806e1b000000000005033e28601482a09015427c0000000004a66943c00007a600000046435e6ae3d05dc7e42ee03c00000073e5e26b600000000063c3e40e20000004e02c64d200053646a0fc15068237a0b20004520000d00001127f46ba00000000000040a0006264e87be8420704ce42e7820160ba32a11c78c71a8000766e22000000d872200062c0000000000004800000000004f60007420001820000002585300de4c27700000004d000000000039400068600079000000000068e54059075c79a0003843
  | 6 => 0x14e0001a000054e29a5140000000000000be6f20000007de3820003c82960007766900003a60005386f861000000074a07a1040c21962e84aa5d003400084e0000002d002812019c0007cc1e60003787b04606400000000000002360003540000000000000000005c25207464ea24000000055081e64a0006285720007025065328300000000000000000000001581bc0940000000000002106fa0000001180007146de5c07fe0000005e84dc0005de00068a2d84a26344e400013638e22c0e40007120006da1a200053a00063a00000000027a4c40d40006665246be0000000003fa02c10200033c0ae09a00000021800000017c00051229870800057c6844bc6322e65f670e00015645636e65e1f646878a6365701a647c4de07277c1cc46c7c453430e1242b64ee08408814c5a84c600000000000082c7c20000000000124a87c04960000060007683fc2627360000000000b05d631c5bc0008186a472a08c0001800000000000000560303b26425802120002f00003527b869857e00052c4fe00000000000047e73839c4ac1d60fa5103c62c26f43d479664600000085c56c00000006600081c0000000000000006582d200010c0f469a0000005f827e40e39e1c400000000041276e6680000005ac2680006e000034c5ae6fc1ca44608e7b411662467c32c75407800007e5680005281fe0008480002a800032268858e00042c0002060000000001440000d62d40000001220003bc3ae61c3d80002a
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x9208433754c42108f58f544423d62d51108f992544423e65151108f58c544423d6215110cd584544423e60151108f180544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423e65d0d108f19743442b561d0d108f995434423c6550d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d0910ad587424423e65509108f195424423e65d0510ae98341442b56490510cd152414423c6550510ae18141442746550510bc18141443376550510cd19541442346550510add8d41442b76250510ecd8141442b46050510ec18141442b06050510ad5923144274654c510ad5913144354534c510ad59221442746548510ad591214436452485108f996404423e6510110a758c40442ad6210110ad58440443b1418c1109e1953044399434c110ec50530443d1314c110ec50620442786548110ea50920443b14148110f848520443b141c4110add92104425e63d50109758f540426e62d50109b58b540423d65950108f58e540423d62950108fd8d540423f62550108fd85540423d61550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c108f992530423d6494c1097596530431e5494c10c7552530431e6494c10c7592530431e5454c10c7551530431e6454c10c7591530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108fd97430423d65d0c10c794f430431d53d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432e6454810cb591520432f4354810cb50d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d52508108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d5250410cd945410423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010a758c400431e5310010c754c40042ad6210010cb948400432d5210010ad584400433554c4010d554f100436552c40109e59610043595384010da54a10042776544010cd55110043555344010d954910043b040440109ed9510043595344010da54910043b34144010
  | 1 => 0x823d61950208fd8d540823f62550208f589540823f61550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c208f992530823d6494c2097596530831e5494c20c7552530831e6494c20c7592530831e5454c20c7551530831e6454c20c7591530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208fd97430823d65d0c20c794f430831d53d0c208fd95430823d6550c20c794d430831d5350c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083374394420cd50e51083374294420cd50a51083365454420cd55151083565354420d554d51083366454420cd59151083374354420cd50d51083374254420cd509510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd545410823f65900208f596400831e5390020c754e40082ad6290020cd946400833551900208fd94400823d6510020a758c400831e5310020c754c40082ad6210020ad58440083365110020cd544400832d54c8020d354f200836551c8020d654e200837151880209bd95200832d5448020d354d20083655148020ea101200827b6548020d654d20083ab4248020dc545200823d63953108f58a54c433661953108fd8d54c423f62553108f99353c423d64d4f108f99253c423d6494f108f99053c423d6414f109b98853c426d6214f108fd9743c423d65d0f10ad58743c423f6550f108f59543c423e64d4b108f59352c423e6494b108f59252c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c42b561d0b108fd9542c423d6550b10cd95141c42b76550710cdd9541c42b76350710add8941c42b46050710ad59231c42b5644c710d514d31c42b56488710ad59121c43645248710a758c40c42ad6210310ad58440c423d63d52108f58b548433561d5210ce983548425e63152109758c548426e62152109b588548429d6315210ab588548431e63152108f58c548431d63152108758c548432e62152108f588548432d62152108b58854843356115210ce980548423e6494e108f592538423f6454e108f191538423e6414e108f590538426e6214e109b588538423e65d0e108f197438423e6550e108f195438431e5350e10c754d438423e6494a108f592528423f6454a108f191528423e6414a108f590528425e6314a109758c528423e65d0a108f197428423e6550a108f195428432e5250a10cb54942842ba60d0610ae18141842b56190210a758c40842ad6210210ad5844084399434c210ea50
  | 2 => 0x4294430cd50a510c3365454430cd551510c3665254430d9549510c3366454430cd591510c3374354430cd50d510c3374254430cd509510c23f65d04308f597410c32e52d0430cb54b410c33651d0430cd547410c23f65504308f595410c32e5250430cb549410c3365150430cd545410c23f65900308f596400c29d6390030cb94a400c32d5290030cd946400c33551900308fd94400c23d6510030a758c400c2ad6210030cb948400c32d5210030ad584400c3365110030cd544400c31d54cc030d354b300c35551cc030da54a300c371518c03097d95300c31d544c030d3549300c355514c030e6101300c27b654c030e6d0d300c369524c030dc545300c23d6395320cb98a54c823d61953208fd8d54c823f61553208f99353c823d64d4f208f99253c823d6494f208f99053c823d6414f209d98453c82756114f208fd9743c823d65d0f20ab58b43c823f6550f208f59543c832e5450b20abd9542c832f6550b20abd8d42c82af6150b20ab18142c82ad648cb20ab59132c834c534cb208f99251c823d64947208fd9741c823d65d0720ab58b41c823f65507208f59541c82ad64c8720ab59121c829d6310320ab58840c82b561103208f58f548832d62d52208f587548833a60d52209798c548825d63152209d98454882756115220a758c54882b56115220c798c548823d6315220c758c548821d6315220cb588548833661152208f584548833561152208d584548833a60152208f992538823d6494e208fd91538823c6454e208f990538823d6414e209d98453882756114e208f997438823c65d0e208f995438823c6550e20c794d438831d5350e20ae98342882b86050a208f992518823d64946208fd91518823c64546208f997418823c6550620cd94541883355150620ab58a408829d6310220ab58840882b56110220e650d308832f54c82208f58f544823d61d51208f992544823e65151208f58c544832d62151208f584544823e6494d208f592534823f6454d208f19153482776154d209d185534823e6414d208f59053482766114d209d584534823e65d0d208f19743482ad62d0d208f995434823c6550d208f99742482ba60d0920ab592424832c54909208f19542482b860509209b19542482e86050920cbd95424832c65509208b19542482af6350920abd8542483ab6050920ab18142483a86050920aa18142482ad648c9209b19532482ad644c920d314d324823e64145208f590514825e63145209758c514823e65d05208f19741482ad62d05208f995414823c6550520ab59321482ad6448520d9145214823e65901208f994404829d6310120ab58840482b56110120ea50a3048278654c120e650d30483a9424c120f24c930483a942c8120abd92204825e63d50209758f540827661d50209d587540823d65950208f58e540
  | 3 => 0x4408f596211031d5388440cb54a211033551884408f595211031d5348440cb549211033551484408f994211023d6508440a798c211029d6308440c754c211032d5208440cd54421103a52108440ae98021102b96008440c794e501031d5394040cb94a501032d5294040cd94650103355194040ce982501039a5394040e654e50103aa5294040ea54a50103b25194040ec546501031e63953308f58a54cc23d61953308fd8954cc23f6155330c795143cc29f6550f30c7d9543cc29f6250f30a7d8543cc29c6050f308f99252cc23d6494b308fd9742cc23d65d0b30a758f42cc23f6550b308f59542cc29d64ccb30a759132cc23e64947308f59251cc23f65d07308f59741cc29d63d07308fd9541cc23d6550730a759331cc29d644c730a758c40cc2ad6210330ad58440cc31d63d52308f58b548c23d61d5230ce983548c26e62152309b588548c27661152309d584548c2ad6215230ad584548c31d6315230cb988548c23d6215230cb588548c22d6215230cd984548c23d6115230cd584548c2356115230ce980548c2ba60d0e30ae181438c23e6494a308f592528c23f6454a308f191528c23e65d0a308f195428c32e5250a30cb549428c23e64946308f592518c23f64546308f191518c23e65d06308f195418c3365150630cd545418c29d6390230a758c408c2ad6210230ad584408c31f54cc2308f58b544c23d61d51308f992544c23e6515130c758c544c23d62151308f584544c23e65d0d30ae983434c29d6490d30c7152434c23c6550d30ae181434c25c6550d30b6181434c31f6550d30c7195434c21c6550d30a7d89434c29f6150d30e6d81434c29c6050d30e6181434c2986050d308f990524c23d64149309d984524c27561149308f997424c23c65d0930a758f424c23e65509308f195424c29d64cc930a7591324c34c524c9308f990514c23d64145309b988514c26d62145308f997414c23c65d0530a758f414c23e65505308f195414c29d64cc530a7591314c354514c5308f996404c23e6510130a758c404c2ad6210130ad584404c39943cc130a7d92304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c23d61950308fd8d540c23d63550308fd89540c23f61550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c23f6550c30c794d430c23e64948308f592520c32e5494830cb552520c32e6494830cb592520c32f4394830cb50e520c32e5454830cb551520c32e6454830cb591520c32f4354830cb50d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c23e64944308f592510c3365494430cd552510c3665294430d954a510c3366494430cd592510c3374394430cd50e510c337
  | 4 => 0xd50951103344254440c794f411031d53d0440cb94b411032d52d0440cd547411023d6590440c754e411032d5290440cd546411031e5350440c754d411032e5250440cb54941103365150440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401031d5350040cb549401033551500409ed9540102ae62d4c40ab58b53102b661d4c40ad58753102ba60d4c40a7596531023f6254c408fd85531031f6554c40c7d89531031e6254c40c7589531031c6254c40c7d85531031e6154c40c7585531031c6154c40c7981531031c6054c40a798c531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae980531029e63d4840a758f521031e53d4840c754f52102b661d4840ad58752102ba60d4840c754e52102ad6594840cbd4e521038e5394840cb54e521038d5394840c354e521031e5354840c754d521023f63548408fd85521032f6554840cbd4d521032e5354840e394d521030e5354840cb54d521038d5354840c354d521032c5354840cbd8d521032e6354840cb58d521032c6354840cbd85521032e6154840cb585521032c6154840cb981521032c6054840a798c521029d6314840c754c52102ae6214840cb54852102b66114840ad58452102ba60148408f997321023d65cc840c754f321032d52cc8408f996321023d658c840c754e321032d528c8408f595321031d534c840cb549321023e650c8408f594321031d530c840cb548321038d320c840ad98432102b5610c840ae98032102b9600c840a798f511029d63d4440c794f511031d53d4440ab98b51102ad62d4440cb94b511032d52d4440ae983511031d5394440cb54a51102b56594440cdd4e51103965394440cd54e51103955394440c554e51103375294440e994a51103355294440e954a51103255294440c794d511031d5354440cb949511032d52544408fd8d511023f6254440cdd9551103375354440cd94d51103965354440c594d51103355354440e554d51103155354440cd14d51103375254440cd94951103a65254440c994951103355254440e954951103255254440cd14951103376354440cd98d51103356354440cd18d51103376254440cd98951103356254440cd18951103373254440cd8c951103353254440cd0c951103366054440cd181511029e6314440a758c511031d5314440ab98851102ad6214440cb54851102b66114440cd54451102ba60144408f997311023d65cc440c754f311032d52cc440cd547311023e658c4408f596311031d538c440cb54a3110335518c4408f595311031d534c440cb5493110335514c4408f994311023d650c440c754c31102ae620c440ab588311032d520c440cd5443110395310c440ae98031102b9600c4408f997211023d65c8440c754f211032d52c8440cd547211023e6588
  | 5 => 0x430863f6550c218f595430871e5350c21c754d430863e64948218f592520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410874d53c8421d554e21086e562884219bd95210874d5348421e9d0521087a541484219dd9521087555348421e9d0921087a54248421b9d9521087676548421e999121087a56448421e995121087a55448421d9d4d21087c65348421d954d21087c55348421d154d21087a74348421e950d210873a5494021ce552500875a5394021d654e50087e12194021ced9250087386494021ced0e50087394394021ced0a50087394294021ced06500873941940218fd91500863c6454021d9485500873a5454021ce551500875a5354021d654d50087e12154021ced9150087386454021ced0d50087394354021ced0950087394254021ced0550087394154021dac8550087722154021da48550087712154021d8485500871d53d0f40cb54b42d033551d0740c794d439031d5350e40cb949429032d5250a40cd94541903355150640ae983539031f5394e408fd89539023f6154e40ab98853902ad6214e40ad98453902b56114e40ae98053902ba60d4a40cbd4a529023f6354a408fd85529029e6314a40a758c52902b66114a40ad58452902ba6014a408f997329023d65cca40c754f329023e658ca408f596329032d528ca408f595329031d534ca40cb549329023e650ca408f594329038d320ca40ad98432902b5610ca40ae98032902b9600ca40ae983519033751946408fd8d519023f6254640a798c519029d6314640ab98851902ad6214640ae980519023e65cc6408f597319031d53cc6408f996319023d658c640cd546319023d654c640c754d3190335514c6408f994319023d650c640ab98831902ad620c640e54c431902ba600c640ae580319023e65c86408f597219032d52c86408f996219023d6588640cd546219023d6548640cb549219033551486408f994219023d6508640a798c219029d6308640e948421902ba6008640ae580219023e65d0d40c7d4d435023e65d0940cbd49425023e65d0540cdd45415031e6454c40c754f431023d6590c40c754e431031e5350c40c754c431034e5394840d354e521032f4394840cb50e521034e5354840d354d521032e6454840cbd0d521032e4354840cb50d521032c4354840c794f421031d53d0840cb54b421023d6590840c754e421032d5290840c794d421031d5350840cb949421031d5310840cb54842103565394440d554e51103665294440d954a51103374394440cd50e51103374294440cd50a51103565354440d554d51103665254440d954951103366454440cdd0d51103364354440cd50d51103344354440cdd0951103364254440c
  | 6 => 0x72e6454831cb591520c72f4354831cb50d520c63f65d08318f597420c69d63d0831cb94b420c72d52d0831ad587420c63f65508318f595420c72e5250831cb549420c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc431b558e310c765528c43197d95310c74d524c431e5d05310c795414c4319dd95310c797434c431e550d310c765524c431b5d95310c757654c431e5991310c795644c431e5951310c795544c431f1949310c755524c431f1549310c745524c431e5d09310c795424c431ce952500c7395494031da94a500c7695294031f44c6500c73b6494031ce192500c73b4394031ce50e500c73b4294031ce50a500c73b4194031ce506500c63f64540318f191500c7553154031ce951500c7395454031da949500c7695254031f44c5500c73b6454031ce191500c73b4354031ce50d500c73b4254031ce509500c73b4154031ce505500c75b3154031dc8c5500c7593154031dc4c5500c75131540318f58e54c863e60953218fd8d54c863c60553218f99353c863d64d4f218f99253c863d6494f218f99053c863d6414f219e98053c86796014f218fd9743c863d65d0f21ad58743c863f6550f218f59543c874c534cb21ab58b41c86af62507218fd9150c863c64543218f58e548863e60952218fd8d548863c60552218f993538863d64d4e218f992538863d6494e218f990538863d6414e219e98053886796014e218fd97438863d65d0e21ab58b438863f6550e218f59543886b561d0a21add854288754534c6218fd91508863c64542219798e544865d6395121a758e544871e63951218f58e544871d63951218758e544863d6295121cb58a544863d6195121cd586544863e60951218fd8d544863f6255121cbd89544863f6155121cdd85544863c60551218f993534863d64d4d218f992534863d6494d218f990534863d6414d219e98053486796014d218fd97434863d65d0d218fd95434863d6550d21c7d4d434871c5350d21ad58742486b761509219b195324874c534c921b918532486ad62d05218fd95414863d6550521abd894148674654c521d514d31486e4624c521f14c9314863e64d41218f593504863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f58e540863e60950218fd8d540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f43086ad62d0c21ad587
  | 7 => 0x294032dc946500cb715194032ced92500cb386494032ced0e500cb394394032ced0a500cb3942940328fd91500ca3c6454032d34c9500cb3a5454032ce551500cbc93254032dc945500cb715154032ced91500cb386454032ced0d500cb394354032ced09500cb394254032d6cc9500cb6a3254032d64c9500cb693254032d24c9500cb1d53d0f41cb54b42d06ae62d4f41ab58b53d06b561d4f418fd8953d063c6054f41ad58453d069e63d4b41a758f52d06b561d4b418fd8d52d063c6054b41ad58452d063e65ccb418f59732d072d52ccb418f99632d063d658cb41c754e32d063d654cb418f99432d063d650cb41c754c32d072d520cb41e34c832d06b6610cb41ad58432d06ba600cb41ae58032d063d63943418f58a50d069e6314341a758c50d06ae6214341ab58850d071d5350e41cb549429071f5350d418f994435072f52509418f994425065e63141419758c505066e62141419b588505063d62d4d418f98353506b56194d41add85535063d63d49418f98352506b56194941add85525063e65cc9418f597325063e658c9418f596325063e654c941add8532506b4614c9418f994325063d650c941e34c832506b6610c941ad58432506ba600c941ae58032506b560d4541a798c505069d6314141ab98850506ad6214141c798c505063d6314141c758c505061d6314141cb988505063d6214141cb588505062d6214141c754f431063f6550c41cb54b421063f65508418fd9541106776550441cd951411063d62953318f98254cc63f62553318f18154cc63e6494b318f59252cc63f65d0b318f59742cc6b561d0b318fd9542cc63d6550b31a758f41cc69f63507318fd9150cc63c64543318f58a548c63e60952318fd89548c63c6055231ad587438c6b76150e318f992528c63d6494a318fd97428c63d65d0a31a758f428c63f6550a318f595428c63f64542318f191508c66e62951319b58a544c6ad62951318f58e544c71d6395131cb98a544c63d6295131cb58a544c62d62951318f586544c73561951318f982544c63f6355131c7d8d544c63f62551318fd85544c73761551318f181544c6b561d0d31add85434c63e64d49318f593524c63e64149318f590524c67a60149319e580524c63d65d09318fd95424c72f5250931cb149424c74c524c931b5185324c69d63d05318fd95414c63d6550531a7d8d414c63e64d41318f593504c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f58a540c63e60950318fd89540c63c60550318f990540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c318fd95430c63e64948318f592520c72e5494831cb552520c72e6494831cb592520c72f4394831cb50e520c72e5454831cb551520c
  | 8 => 0x300003800700a00203a00400a00400000500d00100900200100000103300100000d00500000500800300300000000200cad98752d0eb561d4b438fd8552d0e3c6054b43ab98b51d0ead62d47438fd8951d0e3c60547438f58a50d0e3d6194343ab98850d0ead6214343ad98450d0eb561143439b9885050e6d62141439d9845050e756114143a75835350e3d61d49438f9835250e3d62d45438f9835150eae6214143ab5885050eb66114143ad5845050f2e62141438f5885050f2d62141438b5885050f3661141438f5845050f3561141438d5845050e3f6550c4397d954310f1e5450c43c754f43d0aad62d4f42ad98753d0ab561d4f428fd8553d0a3c6054f42ab58853d0a9e63d4742a758f51d0a3f63547428f18151d0a3d63943428f58650d0a9e6314342a758c50d0ab66114342ad58450d0b1d5350e42c7d4d4350a3e6510d429798c5050a5d63141429d9845050a7561141428f5875350a3e60d4d42ab58a5350aaf6254d42ab5835250a3d63d45428f9835150a9e6314142a758c5050ab66114142ad5845050b1e63141428f58c5050b1d63141428758c5050b3661141428f5845050b3561141428d5845050b1d53d0c428fd954310a3f65508429bd954210b2e54508428f58654cca3e60953328fd8554cca3c6055332a758f42cca9f6350b328f99251cca3d64947328fd9150cca3c64543328f586548ca3e60952328fd85548ca3c6055232ab58b438caaf6250e328f992518ca3d64946328fd91508ca3c64542329d986544ca756195132ad586544ca3d6395132c758e544ca3d6295132cb58a544cb3661951328f586544cb3561951328d586544ca3e60951328fd8d544cb1f63551328fd89544cb2f62551328fd85544ca3c6055132ab58b434caaf6250d32a758f424ca3f65509328f595424ca9f63509328f993514ca3d64d45328f990514ca3d64145329e980514ca7960145328f993504ca3d64d41328f990504ca3d64141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540ca3d61950328f982540ca3f61550328f181540ca3e64150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430ca3f6550c328f992520ca3d64948328f597420ca3f6550832b358e320ca5f654c832e3d09320cb8d424c8329bd95320cb8f434c832e350d320cacf654c832d3d95320cb8e644c832e3591320cb8e544c832e3551320ca3e64944328f592510cb365494432cd552510cbc53294432cd992510cb356494432cdd0e510cb354394432cdd0a510cb354294432d34c9510cb365454432cd551510cbc53254432cd991510cb356454432cdd0d510cb354354432cdd09510cb354254432d5cc9510cb663254432d54c9510cb653254432d14c9510cb3a5494032ce552500cbc93
  | 9 => 0x138b48dbc776000818ee000083c95631810ccc008448692a0001fa992e08ab6c9c3c0904af61f07da3da4f407a4c4be8000d9446edd661ca4a000f001b876600038600079c2ae000000bc8d00c72d10a66aec790da28ea6a8000242e405d89da964ba47f80000001ba6da3ac00000300900002b00000a00b00102100100500000600502600100100d01300a00501f00600100a00900000100d00400000500a00000706302301b00100000600000400500100000200100d00c00200500101800500a00100200900900301700300700200f00300500300000400a00100000400000800100001300002100000200000300300400f00400401a00000200200b00400000100100202000400000000100100001101300100200700101801400400100501300000202300d00200000000402b00000000000500000200002400302a00001800300400600402100800c00300001100d00200d00600100600300300100000000000900a00000200a00d00303205e00100000802200001804e01800200b00000b00000400400700600200700001601001801600001700800500000000800000600200502100400100000100901000200300000b01d00700000002500300403500000200a00300100200c00000400f00200c01701600000400a00200e00800300400001200803e00100b03c00400002900101a00004f01100200000801f00300500400302000002d00300200800300700200601d00401d00000400700100500100900400c00000000001200d00004300200200100200b00000500100100200400406f00500300200400400e00600001301a00500e00300701100301005d03900000600000600100600f00c00300000301304100000200100100100200000d00600600400001100400000200300000900200100000900600400000c00200500900800b00100500200f0040000330000010000000020a600000100000401400301900001e00000600600500800102900100000001400000001801500b00105201001600000700100200005800500100300600600100000000900801300700100300000000200400600100200c01700900000000501300101000601600900300009600300100300400e00800f00000000000e00000700600001000400000300500f00c00000100100400200100d00300a00400500500000000700700500000f02300100300700900c02001201500b00300200200000101500500100200800d01000000001300201000000e00300100500000200100000100400100800900100902c00900200100101100400500001300800e04000300000b00200601600600800200000001100100000001300b00900600101000300301200000d00800200400000001600b00400001200300400000200300000200200000000200f01900000200
  | 10 => 0x88be29400fa9d66ac0000004f2000e66e245ee00073e6be0003f200099623a1f85b600075e49e96c56445219e1881b0d5600000065e000bccaa0e86b685e235235000cd2ee7e9581d056e00000000052000000000000000011c21ec965a0d4a0c6cc60002f653ea82e04484706000ad82b0978000a22d2ca86b0463c11ae34894022a5448c0007a45560000007820006b04fa2f4158e1652e190e2e24e000392000b1a3e83f0eea0006c218e4184e422c2ea7780de4de4e6c246aa796dea27872249400029e658000ca6b124664141c4c860002be27e222000a7e0001f6206422382db24b048e00092400012c9dc00000071a8ee00000016c000efe0580c86ccc92066bfe8100e45406ee862d6a9b440e1dc9ca67a2944243d097058496837ed5432e914e7043c0006364fc0009e8000e7c000ef00ee8d2e06000a88c18f0e562beade4b72c62c3893c514000302074ce8638b069f0dfc454c307ba7ee7f06e466aebc31c0546743561ceefc3c8b7c000000a1a25821c0ca00061e0007846fe95e5943b80001ac234000de08a033a4205326fc0006f6d0601407c8a225496a71c000984ece1806f2e6c00035a5920000000000000009ac2e27b441a21a000000004000ae8000df6b9a4e2c00edc0000000000000002ee842d8a12e60e0ae00080443aa78000458d7277ed5c22e6e801cb6259e76a576ceed041786d20acdf2640b1600000080e00000085800072c9a60000000002a6cce0006f4000884cac16e692d384d887273a724a4e5343060006eaa045983b6046000df8bf4000e88f0a79251c370000a7aae6c2ea80a747d80443be5bc49a0007aeeb0c462a4ed4092b8457034ea6c0e850a496916c7874e1e6bf014ac5a3d2a0266c0009fe000b0c286bca5da0b62f8bb800079e1a4d867e24ac4628a63aeabc66e0b406c0aae8a36455825628c538000b3a0002d2aa2eca2509280002148a81a83381980005c667e0001e4536076008000a94a8e20487e8762ec9447ea000db47acbb0774b5e1865e4000dd0c1204caee560a960005c82d886000047e0008148f0c9a000834000852274d088e68366a0cc4c4eb08d22b4686c4c62c66dec9edc470e0008200005b01f41400001ee1b4264372a8ce80120d783f6e50b7abdcc2a3a6c90000b564be6b62b6d48cb0bb66bae0e7de1e0124d1a010ef4de251a68600aa008388c6b92a0e02e7c8428000ee6738eb28ecb501c2000af81a6cdc000000000990e26d5ea765e089eee431a52c95aa28cf4b60b643e42d4000000f12aa8bb25f49466785ce34a4ae0000000008320000006c620e78c394000000e844cc000ed600036e3265f24a6da04f8000e4ada60003cc000b6ecf8ac8a246349882fe3a060a000a58d0ae5c322f043d664aaa600039a000bda4a2144a30000192e4c000abe0003285d4034
  | 11 => 0x5615c37894a50c5ec78e8b030a8d6e8c4bcdc87fc476b449a4e32bbaa2e7548c8000e1c71887c57ae9e788390000c6a0003d8488aaa000000000000ea42ca524c5e9e65488501f2d8270c0beb3cd90ca80a0d18aeab4ccfe6ce92e8905128080d6ac43425f6ec8a44ba8d3ad365080ce91a9bc16a8bace441e8e0000bd6d6404a000550d504f689268429a6ae00037c0000004ca8b811e000000c0acc872e5a27c24127d40b87705d63ead326c0ddce1eefaaf42304da87400044c1169bac7c00057ea2c70864c000000c3a9a2c8e00000000000001ecba000000d7000000036622000000055ceae2a0000ad61a00180f6da40000000001c8bc0dc626cd440000009d2000cae0000000000006d6000000156ec435cab2078ccaa260000002a282e000d52000000c680d40007e620859028a8009fc0000002c40009aa000e5a000000dca38c3dc4ce54613258aeb48c200032a00077a6e2582336daab94702c6c668b8897200053c00000009402a000be6a46bc6e1a0005064dcbb4a5a5dee10000304ec60f85ca5228da134966232e94e620000f054c64803a000e9acec0000006f07f6032eee0e68e4000e4e000000c74ede33228e59c9fab280002704b80987e0dfeb2008e000ac2e1232495c05e18c2e0eac9c0c140961a29d847471e000000a5e8d8d6c9629d045662e3804ece46e6805cc486e65b844ad6e46000019c9f8c60e4293ec56346b4a9e0dec0000002f0ea6a1caa430c2ba1fc5aeb38042a1072a3c281e408afa86aafe2d60baa62cbced880aaf0248a3ce90cb23fe0e2a5c12aa42400cdeba69820ec62c938c08d5a986de6b8a2aa14e606154a64eb6712618e52c06000118a18ae293aafc090000128a98444000e547145ac1ae0c053a272e48434a3a552cf03b45880000007b03c600040c00058c000000b52e82b90898528e6a112586c10ad04ba5d200008c244daeb323140009be7d08308aa00000013c5d0c28e76d0e758416000000d8c8ded0257463ae6e740734954b5ae28806b100003a276042e5a890ab14b8c8862902ce26e5ea87a39c8dc1c054a55edeeac650479ad9247c4d27a23ce57c45e440acc84e0f2000000dc2c4a906846e36b2c2da000cbe54e000000000948a40cda78038ec3c682becc7eba27bcb7e20084cb668f6406732d8014cd9a7f4a6a5007e48aebc2b0a5a6a7298c1c6614ab017689c4a07fa7282c88b22ac888e748c0d8e6b234ca388fe0dc680c701aa44e7b6b34cb80000b200059a000c5803c55a94e630cd0db608aeecdac0000008e8880c5c45a9f6a70e8eb9e26611078a17c9cea56d4e84aea088ef02d76d9c23e854000be0d20000404c26000c1a000388cd40005026767cea9a6087f2ee216261a654baa5546bcb2656cb42adcada6106c4bc4868c825f8930100aacb023743e025c83a6
  | 12 => 0x76e7046968560004ead165a429675a6265f027a64e1502e60801061e2b9c000ebecf60003b27c4726000742c767100000f4516000b989b08447624aaa9e8d46708223c4000000e18ca2000000ce2af275276c000c7ac88102368d6009a97e0008a4b862de68a6444c8000d9600000000064200000000056a2b817018ae98d4c17a1480000009a8b5c490b6c81aa14902ec20623aaccc69885a7ec6502d07aa000b2ac3e4b49268705ccbeeae0be437add45c07bee2c8242e81681d490c79450e7b26123dee386d0c229b2ce6622eda7860bc4d6922e3edf47c0cfc8cacb48d099804840a13088c46410854481c530a123306dc2469f4ee89d4e729e25c4d3e7166b41b269e3f4aceadea6e8023444eedbad3c52629c48236c580bdeb3e182b2498e4d024c9f2122dda3fc6ec1fe4e0000a68a48000d1ec84000a201601eaa928be42ce56c42ce0bce8ac320ca015e312362000000000000000000000d58a90050d9eb36e5e000024114000ef64928bc00051004e3d4a84a1e000a06b00126dd83481366e022acd296e000f0c6b897c1b642a2402386a2396baceb88f4ba0d7e0c23f800091085e646a2a5660000001de3ca1bc662000b40e00000104df0d7c24ae028c46d83ecdbe00000000005a85c334c36284c02b1e00015a0005c200077201abd0616ed2ea2d680004b2ad221800000062466486454277cebad24ef2d46744b4e1e8d402fab8ee1470069cec099c5ba1d62fc4b6c1eb6a4d4cc2c647c6994292020340dc021625e00072045003ee9c920c94bd8b96cf200083e000000000000c8030ec0eb7010e3ee000de87fe2241ca91c5dc10a000e3c14600046a1ecb78d12e0a252384cd899ab58596e3a2b467c000908e921da628cb60360382c2030000ddec40e6419a0003b0a9c7a6000000980c160009ded98000276d74e7a9740009ec2bc35406438a41c194b18e200000000cc2980fe13aa1681600ed8802ceaa00065c21268c47ae2a000000000b54262b0eae43a80eac52000812882e9669a58e756000a3ec8c36009e26a0005b28280003160000007984720001ccbf85fe95098a00073c000a60000936000ef83580e046c0004489180007a0602572bfa000000000e2228213e3e2268d34912a32ecc4682f29b8202d28d1c25a4a8c442dc6a6d0c33c578c320008267d6bae01635e0828b436a9ae694d2a7360002e400073051e43628089acaaa7c4e89765fcc049c67b82268f8000d3017e4c0a34ab80a80d86a476480caba438470d66000da81422a89a075c8480006669ea0d0a0c072c5091e27c88a9ccb76d62070750c0c5b40a420c0001be000060bbea52000236480b1c000410b826c82889324fe308dce1d2a0acd65be9347dcc2cbfc300aae000cea99e9c865a4020d27e8442ca4a083fa90e4c26f88b66d445cdb826032ced
  | 13 => 0xe0c0000009ee4265e6c206320a606e8fadfa6723988660002283bc000c4c3a48e2000d4202882c20aa500001520007a8bd40000000128ce02631e310960000c8aa8ae7892c00068e7680006607ca0fc432e5852a942aca000000b2e518c340009005e800021000243e09cf06bbc652600f100002b26906209b60062c01660b07484a433e6fa376a36b3008839e9c2dcc95200060497ad7a06a0000000000a2ea870a07e086000000000000000478c54430c66000000ac0cfae30b80000bf61d8068052b22ad45aa8f294c9c474c0405681648ccab487862ab749e48403e6656e603ba00000044660cbd27460c4bf2c1c23cd1463e86ec6e498c9849cd262cc00082adb01745fa4f07cc0da000a4c184e44dd28fc0006ca8960007d200019600074a48a172d84f08
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x904a57118142c82a2b88a699641075cf65d0720c52c5306a91060e635885488306b1ac42a4418558e6115220c4ac5308a91061663584548830ab1ac22a44189589611522086ae232e871043571195438824cb98c0a14412c5c46050a2083ae632a83105187550d30882163aac5a1a412a1c162d0d20932e630284904b1711814248264b98c0a1241385c4605092091ae630284904a57118142482c4b98c0a1241685c46050920954ea302849062a751814248345398c0a12412a5cc6050920d12e63028490489731814248351388c0a12412a5c46050920d42e230284904a1711814248254382c9192410b1d5644c920950e0b2264905457114d3248254382c5a0a412a1c164c8520950e0b2242905457314521482543b28518241461d5434c120950eca126090648654c930482c4ba264982410bdd56290020c1aa6b14801062562546400820eb9eca2004107dd5631002083aed298801041d7654c400830729ac4200418354d621002086eeab08801061653584400830aa9ac2200410d5da5110020c2ac7288801062562944400830ab1aa220041895895110020a52ea2024010589731012008384a988090041685c44048020e42a2202401052975d092008384a9e8490041c8d09514802085ae5b2e878841d73d9742c424ab98c0a0e21295c86050710a8ae429a63885457314921c4318b0cc1aa4218358e6215210c1cc6b10a90860d63588548430b31ac22a4218558d6115210c4cc4b08a908625625845484216b90cba1c210b5c86550e1083ae632e850841d73195428424cb98c0a0c212a5c86050610a30eaa1a610852875509208420eb98c02a2210b5c86015110868eab0e86884b070587434421a3aac3a12212c1c161d0910932e630282884a9721814144268b98c0a0a21385c8605051092ae630282884a57218141442c8b98c0a0a21685c86050510964ea3028288632751814144349398c0a0a212c5cc6050510d22e63028288491731814144351390c0a0a212c5c86050510d42e430282884a1721814144258382c918a210d1d5644c510960e0b2262885457214d3144258382c910a210d1d56448510960e0b2242885457314921442583b28318221461d5434c110960eca0a6088650654c530442c8ba262982212c1d94188110a50eaa1240884b076505204433032a4290221685d1214811086eeab0c8008615535864004312a92c320021075cf651001085ae5b28800843571594400420fbaac620021075da531001083aeca98800842f75588400430729ac4200218354d621001085aed290800860d639484004216bb2a4200218358d5210010c2ca6b088008615535844004313292c220021895496110010a62ea2022008591731011004388a988088021685c84044010e42a4202200853175d051004388a9e8288021c854b4144010
  | 1 => 0x511028ab9ea528881c154e5294440e0ca6a94a2207055354a5110293396a6a8881495cb5354440a2aeb29aa2204367614d511028b398a6a8881499c85354440a4ae429aa2205327014d511028b39ea4a8881455cf5254440a4aeb292a220706539495110382a9ca4a8881c194d5254440e0aa6a92a22043676149511028b398a4a8881455cc5254440a4ce4292a22053270149511030ab18c6a8881499c86354440a4ae431aa2205327018d511028b398c4a8881455cc6254440c4ac4312a22053270189511021b3b064a88810d5d83254440e0a64192a220532700c95110298b8064a8881459cc6054440a2ae6302a220526721815110292b90c0a888107dd95314440c1aa7310a22060d535885110217bb2a4288818398d5214440c1ac6a90a220615539845110312a94c2288818598d5114440c2ac6a88a220626625445110312b12a2288818654e6014440c52a5300a22042d729973110216b94cb188810b5ca650c44085aeb310622060d539883110306a9ac4188810bdd9520c44085aeca906220626625443110312b12a218881455d5310c440c2aca9886220685624c43110382a9262188818654e600c440c52a5300622063151980311030ca9ac0188818a549600c440c62a2b00622069131580311020eb9ccb90881075ce658844083ae7328422041d7598c211020fbb2a610881075d95308440c1cc6a90422060d63548211030b31aa2108818558d5108440a4aea9084220625654842110342b1a4210881c154d2108440c32a73004220629529802110318a8cc0108818654d6008440c52a4b00422063151580211035090ac010881c254d5294040e22a6a8ca020721525465010246b90c0a1e61255c46050f3086ae3b2e859842d72d9741cc30cb1cc1aa4618358e6215230c1ac6b10a91861563984548c312b14c22a4618558d6115230c4cc4b08a91862562584548c254b90c0a1c612c5c46050e3086ae232a851842d72195418c254b90c0a1a612c5c46050d30992e430286984d171181434c246b90c0a1a61255c46050d30b12e4302869859171181434c24d3a8c0a1a61869d46050d30d14e4302869849972181434c344b90c0a1a61225c86050d30d24e2302869849971181434c348b88c0a1a61245c46050d30930e0b1e849849870593324c24c382c899261515c4524c930930e0b1e829849870593314c24c382c898a61515c8514c53083eeab1c801860d6354a400c30ab1aa3200610bdd5621003085aed290801860d63948400c306b1aa4200610ddd56110030c4ca4b08801862552584400c21abb4a2200618558e5110030c4ac5288801861563544400c312b12a220061465d4404c030b12e4202601870952101300c2c8b888098061c4544404c030a32eba1a601870b43549300c389a1aa2980610d5c765d0f2091ae630285
  | 2 => 0xa498863255db424c431e0aa5a126218f0552509310c7a0a9263280634a5c8649403185ae4322a018f12544c5500c788aa262a8063d09493154031e82a498aa018d2972191500c68cb9e84a80634c5c74254031e268298aa018f11414c5500c789a1a62a8063c450d3154031e24e898aa018f11744c5500c789b2262a8063c41913154031e268498aa018f11424c5500c60eb98c0aa643525c0534cb2183ae6302a910d517014d318870731ac52a2438598d619512183ae6302a890c2d72d97434861ab8ecba1a430e1c16550d21a32e029a8690d497014d3248670b80c299243075cf6550521aa2e029a6290ce17018931486a23aa6498a4391195324c52183ae7326a090c1d731815408706a9ac5a18438554d61d0c21e0aa7a0a4210f05535052108782a9e8490843c154d4248421a4aeb3224210d85739912108693baac890843585c35348421a8aeb29a4210f065454d2108782aa2a690843c19d15348421e0ae8a9a4210f066454d2108782b22a690843295db4348421e0aa7a1a4210f055350d21087a0a9a4328043465cc649402183ae6322a010f22544855008790aa242a8043d094d2154021e82a690aa010d19731915008694b9686a80434c5c74354021e468290aa010f21414855008791a1242a8043c85092154021e44e890aa010f21744855008791b2242a8043c81912154021e468690aa010f2143485500861bb8aca9948183595320ca40d0a64b086520689325803290217b92ca98c8185595310c640d0ac4988632069131580319020fb9aca90c81895952108640d0ac690843206a1215802190306b10c4a9881459c46254c40a2ae2312a62051a701895310287390c2a9881435c86154c40c2ac230aa62051a701855310287390c0a9881435c86054c40a2ce2302a620515711815310306a9cc4298818354d6214c40c2aa7308a62061553584531030aa9cc3a90818594d61d4840c2aa6b0ea42052571d4e521029338ea6a9081495c75354840a1aeb29aa42042e7614d5210287398a6a9081499c45354840a4ae229aa42052a7014d5210306b18c6a9081499c46354840a4ae231aa42052a7018d5210287398c2a9081435cc6154840c4ac230aa42052a701855210287398c0a9081435cc6054840a4ce2302a42052571181521020fbb2a6290818354e6214840c1cc6a90a42060d63548521030aa9cc2290818954a6114840c2aa6b08a42062552584521030ca9cc0290810d5c665cc84086ae332c6420435719943210286baa641908183595320c84086aeb3086420615539843210312a94c2190818554d610c840c4aa4b08642068532584321030ca9cc0190818a54a600c840c32a6b006420629525803210344992c0190818354e62d4440c1ca6b16a22060d5358b5110306b1ca5a88818398d52d4440c1ac6a96a22052572d4e
  | 3 => 0x6f00072400169430851058ee000790000000000e4ff9c624a000000003320000000000025c00242000318be0002b4000970a33883410499f00027c0000007e578609d238a761098083841051581216688433a203b41b4e9a3d290444538aa23055d0c9362081c4541b32820246d068210000000e80000000014c272264000ad00000064000000000000004023d4eb88632e5291f00000a7bcb09ac000000001920000007d8f2288000038001b05c000000000000000883d83709c1620428e0021ed286134ff000000000000000006d4c98e0044204120003b65dc1907c1120003803604e000000001740000018e2c0000001684104500000039e52c3c92f0663880400000004010020100800802018020200a0200000800000080000202818020100000200806010000000c0100601000010000000000000040080080000000038180c8020180004806008060000a0200a01800010060100c0001a0081a0080000004008020100801800090120000e0003c008020180c00000028000180001000008100100003800078000000a000100000607002010080300000004000040380200006010000080c028020080c008000502604002000000480c008020000c028020180a0a804008120400006800000000100e00800040020400001024028260000000002000000180a008000000c0000000004004357118152d0e16b90c0a8e878958a6114143c4cc4b08a0a1e25625845050e1ab88c0a9e85075cc6054742c2ac7308a0a1616635845050b0ab1ac2282850d5c4605533286ae2302a91961563986544cb12b14c32a2650d5c4605513286ae3326a09943571181540ca86bacc899065615c6644c832a1eeab226419706544c9510cb82aa264a8865c1d093254432e0a84992a219707434c9510cb82a1a64a8865c19d13254432e0ae8992a219706644c9510cb82b2264a8865d04c95194032a62e2324a01943571191500cb852a264a8065c25513254032e826528aa01974132545500ca98b88c8a8065c2d093254032e1284992a01970b434c9500cb84a1a64a8065c29d13254032e12e8992a01970b644c9500cb8432264a80650b5c86054f4183ae6302a5a0d0d754c832d070aa9ac21968389549610cb41d0a64b0865a0e195358032d0714a92c019683a24c9600cb41962e030a64a0e85325843250744992c0192838358e6214141c1cc6b10a0a0e0d635885050616b90c0aa6630b5c86055231c1ac7314a898e2662586544c616b90c0aa2634a5c05250931a92e02926498cd170185324c616b94c9a82630b5c86055031c1ac6a968418e2552587420c782a968298863c1549414c431e0e86a926218f0543549310c68abacc898863615ca644c431a2eeab226218f0654549310c782aa2a498863c19d1524c431e0ae8a926218f0664549310c782b22
  | 4 => 0xa1cb0985b00019c00011c0004a46a1d8000e90001e0661f80745f8ae8c517e3ac00000280000000002fe898dc135000000000001ca198000000f43648c80006245c980002e61bc000f04925587c0001cc86c8380045e3745e800000000000960ba6d016800000280000001f8000000003cc000000000b077c5598d22c5f4060e3380078000ac3dc594ce92a30c7e4ef000304000d18003480000980039a5400015f01c068000650001840013d318000181dd3763d0c011b422000ee054000000001ea000000d38000000010f01800072000000446000810000b86f04d0003a000000189276890c084034c3d8cd00021c0dc0004f05000000000000000001881860010a8000003a80005f2f4058001200008b83986c1485e0d58001bc3240f83c0000009200045a0009f0003165550820f0fa000cf0ef000000000003220010000000049d2380041460c708001ce7a48d08e2780002d9a03c21f8152322e281cf91fa0146881000042c874000000007ccd780048c000912361885ec118b20001fc000c702e7640011347228800072000000320000a00006780f000000001263ee02c000002d62d8809310c60005798423c334000000000008510c1a22f88780000066c370002ea0001c1eb00005520194000524b522a2b26c4f18b53f6000001b70002480000000000000000000000bb0c0000308000000000f8000000000005700000085c00227056910dd1330a47c0d92282122ed018d4000050fe10b40812ce192c11e0740000004c448b19a50d4270dc954178000bc80014a000000000380080d8a11963b02704908a40c418d24608c4482050004d00021f0008e80000038e90400000000570588013c40ecd723f0060007d0001ee000428f11f200000121000000ba1c10000b8e70000000008803500090c001232560008e800490000001464587c4001b613c000fb23c05e00030093000000cc0d52e416800000000818d69580b20011d80046e00000000000000d5000086000e50001721d0b685500047c80000000000f400029c000d409b2641d469800000000000a9000000001a93fa91400000000358001d400051c00164122000721cc05811846167000434211bd0d6754830871fc0940012932a2102f1d61da1dc221f50002e00019641a000001871fa000f280030a338000003a2000ad80000003400000000000df0003420009680000063c5a0b00520f43d89d0006fca28000008a400000000000000510ae000fa2222a4064000000004140000014c040001b00002509d0004345444a80000037c0000016e838000f300000000190130000000801ae00109000404158a78823ce22c0001100036d060000000000014d0008cc001370005b92500000001800000114780000ca11a000a9a340005988e0000d24a09f8ff0a618800225000508001
  | 5 => 0x6282400022a8701
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x160000000000005e527a488a500000246858784000444a74006a8400180000704e00007c000060908c6e920426463c00006400000000000000000800426c86004c008e6200003014660038321000222e7e82025c000000361e88003400009a00941a561200543e5a967200002c002a0000000c00200e9800000a762800801c00063a00000003050200071302000001050005030000030f01070002010002a05869d13254432b01819d13254032b01811913254032a05854c9610cb41a09854c9600cb4190587991524c431c057654b424c431b01829d13154031b0182191315403191187d093154031905879915348421c057654f4348421b01839d12154021b0183191215402192187d0d2154021c05625c46254c40c05725846154c40c05635c46354840c05735846154840a05854c9610c840a09854c9600c840c05635c86354440c05735886254440c05764c83254440d01325c03254440c0575589310c440a0586549310c440a11854c5600c440e01524c5600c440c057558d2108440a058654d2108440a21854856008440e01534856008440c81729c46050d30c82725c46050d30c81725c46050d30891811c163d0930891811c164cc930891811c1644c930889821c163d0530889821c164cc530889821c1644c530d01525c4404c030d0172544404c030911811d5434c2208a1811c162d0d20c81739c46050920c82735c46050920c81735c460509208a1811c1648c9208a1811c1644c920889831c162d0520889831c164c8520889831c164485208a1811d9428c120908855d1324c1209098754c4048020d01535c44048020d01735444048020909821d5434c210909831d542482108a1821c161d0d10891831c161d0910c81739c86050510c82735c86050510c81735c860505108a1821c1648c5108a1821c1644c510891831c16488510891831c164485108a1821d9418c110910855d1314c110891831d94188110920855d121481109118754c4044010d01535c84044010921875484044010d01735484044010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1074
  | 4 => 1930
  | 3 => 587
  | 2 => 78
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
  | 6 => packedAt s4K6 (880+((h/16+packedAt s4K6 (768+(h % 16)*7) 7) % 99)*7) 7
  | 5 => packedAt s4K5 (32936+((h/358+packedAt s4K5 (28998+(h % 358)*11) 11) % 1713)*12) 12
  | 4 => packedAt s4K4 (81056+((h/643+packedAt s4K4 (73340+(h % 643)*12) 12) % 2317)*12) 12
  | 3 => packedAt s4K3 (30713+((h/195+packedAt s4K3 (28763+(h % 195)*10) 10) % 937)*11) 11
  | 2 => packedAt s4K2 (4888+((h/26+packedAt s4K2 (4680+(h % 26)*8) 8) % 136)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc3cf3f9fff0e38fc7e318f8ffc71c7c784f0cf
  | 1 => 0xfc0fc7e38ff03f1f8fc1f1f1c381f9f99b4333
  | 2 => 0xfff007fc0fffc01ff1fe01fe03fe01fe638c3c
  | 3 => 0xfffff8000fffffe001fffe0003fffe007c0fc0
  | 5 => 0xfffffffff000000001fffffffc0000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x410080010041008000020240104040001045
  | 1 => 0x44221108122090281040909088809091094112
  | 2 => 0x8880a201244402500292012411240124228428
  | 3 => 0x11040052488820012525240022492400540a80
  | 5 => 0xe228b45b00ed349a49f9c9c9380c34357fe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8feeafeeafee8fee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36150
namespace PEqualNP.Outside.L_meta_36150
open PEqualNP.Outside.L_meta_36150.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x407852a0e98b0e067008d3250000227c59530001064a0082800109294800d93009d08f0a2158012691000074b8c4604000e08300704a000080ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x6613d54cc2f8a9986fd0f30ef21e61bd43cc3ba87986750f30bf296617d52cc3be6598774cb30bf28e617d51cc37e83986f50730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7186fd0e30dea1c617e528c2faa5185f94630bea8c61bf418c37a83185f94230ef98461fb308c2fea8985f95130beaa2617c544c37e86987790d30dea1a61dd434c33a86985fd4930be29261df324c3ba64985fd4530be28a61bf414c37a829877cc530ee98a61fb304c3bc60985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30dfa1861bd430c2fca4187b94830b7290617d520c3daa4185b54830bf28861f6510c2eca2185f54430faa886175510c37e82186f50430bf28061df300c3f46018774c030fc980617f54c82fca9905f55320be2a6417f53c82fca7905f54f20be29e41bf43c837a87907b90b20f6a1641ee32c83da65905f94720bea8e41bf41c837a83907bc8720f690e417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c41bf438837a87105f54a20bf28c417d518837e83106f50620bf28441fa40883f281107e8c220fc98441ef20883f641105fd5120dfaa2413f54482fca8905f55120be2a241bc5448278a8905fd4d20bf29a417d53482f8a6906fd0d20dea1a41ee42483da84907b8c920f6992417f51482f8a2906fd0520dea0a41ef21483da42907e90120fca0241fa30483f260907ec8120f7102417f54082fca8106f950209f2a0417d540837aa8104f55020be2a0417f53082fca6107794c20af298417d53083baa6105754c20be29841bf430837a86105f94820bf28841f651082eca2105f54420faa884175510837e82106f50420bf28041ef20083f440107b48020fc90041e920082fea9885f95310df2a6213e54c42faa9886f553109eaa6217c54c42fea7885f94f10bea9e217c53c437e87886f50f10bfa96217e52c42faa5885f14b10dfa0e21f641c437a83887d50710daa0e21f631c43ea63887d88710fa90e217f54842fca9085f55210be2a4217f53842fca7085f54e10be29c21bf438437a87085fd4a10bf294217d52842f8a5085f54610dfa0c21bd41842fca1087e8c210fc98421fa20843f241087dc4210fd884217f54442fca8885f55110be2a2217f53442fca6885f54d10be29a21bf434437a86885fd4910bf292217d52442f8a4886fd0510fb20a21bd41443ea82886d50510fb18a21f531443ec42887d48510fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a82085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5250778a4a0efcc941df19283bd325077864a0efd4541dba8a83bf505077ca0a0ef54141de282837e541067ca820df94c41bea9883bf431077a8620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331dfa1e63bd43cc6fca598df54b31ef99663dd32cc77e8398fd90731dea0e63f541cc76a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77e8718f790e31dea1c63dd438c73a8718df94a31bea94637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c77ca898cf95131beaa263bd544c67aa898df15131dfa1a63bd434c6fea498df14931ef99263dd324c77e8298ef50531fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863bf430c7bc8618ef50c31eea18639d430c6fca418fb94831b7290637d520c7daa418db54831bf28863bf410c7ec8218ef50431faa0863b5410c7be6218fd8c431ee98863f5310c7aa6218df94031fd280637a500c6faa018fe54031bca80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790fb8cb21f699643bf41c877a8390df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710df54e21be29c43bf438877a8710df54a21bf28c43bf41887ec8310ef50621faa0c43b541887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa1a43bd43487dc6490fb4c921dfa0a43f6414877a8290fd50521daa0a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610efd0c21dea18437e52086fca210efd0421dea0843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037e87206f50e40bf294817d529037c85206f10a40bf28c817d519037e83206f50640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40dfa1881bd43102fca4207b94840b7290817d52103daa4205b54840df21081bc42102fca2207d94440bb288817d51103eaa2205d54440dfa0881bd41102fca0206fd0040fd20081bd40103f280205fd5330bf2a661be54cc27ca9985f55330deaa
  | 2 => 0x2008000010070020540000700203000803008000000130020340300c00000807002006000018010100140c0120020040380400800001805000040000060160080080000c09000802000000020020000280b80100000002800bf296877d52d0efca3a1fd94743bb28e877d51d0feaa3a1dd54743bf286877d50d0f7ea5a1ef94b43dea9687bc52d0f7ea3a1ef94743db28e87bd51d0e7aa3a1ed547439aa8e87bc51d0f7ea1a1ef94343dea8687bc50d0efaa921cf55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be28287bf5350f3ea6a1efd4943df29287bd5250f78a4a1efd45439fa8a87be5150f7aa2a1ef14543dfa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf29885de5310abca6215f54c42eea98855d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110beca2215d94442bea8885f55110aeaa2215f94042fd280857a5010afaa0217e54042bca80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665bf43ccbbc87996f50f32eea1e659d43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7196fd0e32dea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1a65de434cb7a86997750d32cea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca41977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41ef29e835e53d06faa7a0f754f41aea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0e794f41dea9e833d53d073aa7a0c754f41de29e83bf52d077ca5a0ef54b41de29683bf32d077c65a0ef4cb41de19683bf50d077ca1a0ef54341de286837d549067aa920df94e41bea9c83bf439077a8720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83be435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0cfd4d41df29a83bd5350778a6a0efd4941df29283b
  | 3 => 0xa6c0015f00000000000000dbc0030711c3b0001ab16ed702091138acbc0005f096000000000000007d20022e7b8310000ac8a400370000cc4cd8002ac8500026630e5ed6f8d338010979b656d60c11c2a83e40648b18b5fe9b4da16d1f26090e8002640000013b0003a41381f5566a59510f4ae70800000000414eb0904e24a10b21a64e809730e10fec610f9480345bd678000008ac001e12724f80031f46c5dc002ef0006240101e1ba628721686aac444a8005641a5470004bc001348005e800031add46a0003297e000750c68c95ce418ab9fa0d85b97883d3b6acd16b032b24a59082024e8b8599722e6579040d10000006d0006969d0819dc41c0d8f483b00e0002821e1b2000001ae0740011281500029537352296000f2832416930b800000067042b5133486ca223e62a2c99e0401f61210c8000003bc911233de000002ed0001e0ca8ed00058c8f0000000000015c58a1d00031210250146000000000112554a664d6517f024000003100d0441029a5284000000000006a800291000000d30000000004c800000000c81cc000000001144888ecbd1750006c8b300015abf17032d184000000ea1142bc001310000000000059280d5200021a7ec372c41ca001b32452c05918b80020033d9f95253e704de2c108e020e8a5a37a5b0e1b612b09251c9e024c2682888b3e6524eaade5129dc22133632001610005200000034500027d66a6c0e02340031c63cd8970b4e2020000e14c67c0017e800586901338184c217932215144085a534c0babd59336726ea50799240f806c851ec4bad05b715a0c8a10001c953a7b4aaac6000b55728003f02a0001f00005747b02e33aa8c4f0876e49094521c0003f8179d723a4113a83515c4e800334000000908002946581196b00013911aa703a000a08005c87680024e1825e0000e021c71800000000001762dc0000003e86a18a5846000e0003b8020006ae4d4580008060000140580a0040080080e008004000040100000000f0020000b00100000400000006000000080020040200d004040008000080000001200c0300200000800403022000000000050000200080001200c000030080180080101201801801006014038000020000c8030000080080100000c0000300a008018090040000000d020048018040020000000b00001c0700a00400804000000028010020000000080001200000801006000008040160a00500a0020080101b000000008040000000000e0020000000100400c000000340040c00300800c020100120440181a0020000180d0000180280100c004008000380100280c0000180f0010000080000900202004000016008068000000300000000a004020010000080080001e0080000000a02c0280000c000030070000000400200001c058020180040000
  | 4 => 0xdc4f20015cab50000008e1761bcda40036a10c000000030a40004e0bb3fac94000002a05c40000000000000218468000d823a5d49f000179000b480000051abec00000212bd80000054c0014b8000020004b12c00000000000196131859ff46e0005c8fc00055000250422000002bc000000002566860008c80023e000000001d6788001cf000c045a1c41e05a400000000d00000005b02b0001d069e8040000000054d0980000002c002ce26871c000330000017b8003080013f000000545a2006346ad800000000ce93298357c000000001f0c21140141d0000b50001480000000057e9280000013a000002a132e000ba19e4a2a89a80003f24540032e6520c538013534000d20006baa1c2307145491c5f0bc128b01991471a81d8c32b109a920dd04f000a3c0032045896d4f24d2860f91203f30ab6d2923d3b20002aa6f18e43000000140d7c0007700000000000162000000a700000000000000645b000000000000299000044001bb5b20000000026cb1cb135a0000000005b0e66840031b0008fdb6336198000ec1ea500da03d2d32402e92e0c81fa1156818e6ac30c1e034000b45b6ae80000000011a0000b0002ac0eaa0c30b1401a41d8d2bb4081700014555a4a93f86b6c842cf58cd000cd4002e30ccdcc00000110c35310003700000032c00005c8113f644000063375b41506802667a0b400000130b2db8925000001759fc478c000034815444837ab72361f89786d000c1534016000be06b0000004e0000004fa001660b661e6bcc40005900006d800486000000000001640009b00067d1888f3ec000f331d3e8000d600000079051a126a86a0000000000014e0005f27dd3c1a04b0000150c44c0298000d8000000000001706515000012e600c900a442000002101222f449a3235a398000000a60001200068e0015a000000000792a9666a4d050001aa6d4db8001ea128ef918444025550b51e8534129de18c15c549f14a874ce5b5339c6d8300ca418014002096bc210002fa0000000003700063c003420000000818c000000141a21be0000000046079d068001069c940a7644e9ace6a0769a000d9800070ce4000926502aca30f768c9ccdfa596b01615d2065e0a1400167142c2589a204960003ca7b092000ad800482001748ff0000016a108000c314900029c000000005040a59d93d4d4abcff12b6b2c90dca63000ae14a9a700000097000000a9400302560000002d71a4000000003900000000062c10d230725fcab94b0f12fa2fd8200041e6c52794f01e00071b0a00000117ae2112af40000000044d6b0e7000c1833930000000df000100899959ca2ca4b4001e3000168460d7000604000003a4000001e861cbc80007b000208000006700014c217510000001f56923392f800000d8d91800056000cc97c50c00145800
  | 5 => 0xee8000000009e0000009e80033033000000039000001770006b6389198
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe54c425d6395310a758e54c431e63953108f58e54c431d63953108758e54c433661953108fd8d54c423e64d4f108f59353c423e6494f108f59253c423e6414f108f59053c426e6214f109b58853c423f65d0f108f59743c42b561d0f108fd9543c423d6550f10c7d4d43c431c5350f108f99352c423d64d4b108f99052c423d6414b109798c52c425d6314b10a758f41c43365450710add9541c43376550710add8d41c43365350710cd14d41c43375250710cd54941c42b5648c710e550e31c42b5644c710d514d31c42b56488710cd55221c433554487109798c548425d63152109b988548426d62152108f992538423d6494e108f990538423d6414e109b988538426d6214e10ad587438431e5350e10c754d438423f6454a108f191528423e6414a108f590528425e6314a109758c528429d63d0610e650d308436852482109798e544425d63951108f992534423d6494d108f990534423d6414d109b988534426d6214d10ad587434431f5350d10c714d434423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c524429d63d0510ad59241442746550510bc18141443376550510cd19541442b76350510cd94d41443345350510cdd4941443355250510ecd8141443b06050510ad5923144395438c5109d19531442b5644c510d514d31442b564885109d19521443b1418c1109e1953044399434c110ec50530443d1314c110ec50620442786548110da14920443b14148110f848520443b141c41109798f540425d63d50109b98b540426d62d50108f596540423d63950108fd8d540423f61550108f585540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530423e6494c108f592530425d6594c10c7952530431d5494c10c7992530431d6494c10c7951530431d5454c10c7991530431d6454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423f65d0c108f597430431e53d0c10c754f43042b561d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432f4354810cb50d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108f992510423d64944108f597410429d63d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb54941043365150410cd553100435553c4010d954b10042796584010d654e100436952840109dd9510043355444010d554d100436552440109ed9510043595344010da54910043b34144010
  | 1 => 0x827661153209d58454c823e6494f208f59253c823e6414f208f59053c82766114f209d58453c82b561d0f20c794d43c831d5350f20e350d32c823e64947208f59251c829d63d0720cd94541c83355150720e950521c825e63152209758c548827661152209d584548823e6494e208f592538823e6414e208f59053882766114e209d58453882b561d0e20c794d438831d5350e208f992518823d6494620a758f41883365150620cd5454188399434c2208f58f544823d61d51208f992544825e63151209758c544827661151209d584544823e6515120a758c54482b56115120c798c544823d6315120c758c544821d6315120cb588544833661151208f584544833561151208d584544833960151208f992534823d6494d208fd91534823c6454d209dd8553482746154d208f990534823d6414d209d98453482756114d208f997434823c65d0d20ad587434823e6550d208f195434831e5350d20c754d434832c54909209b19542482e860509209b195324838d434c920ba181324823e64145208f590514825e63145209758c514823e65d05208f197414829d63d05208f995414823c6550520e950521482e86048520ce15240483aa42901209e19540482e86250120ea5094048278654c120e650d30482e8624c120f24c9304825e63d50209758f540827661d50209d587540823d65950208f58e540823d61950208fd8d540823f61550208f990540825e63150209758c540826e62150209d984540827561150209e980540823e64d4c208f593530827661d4c209d587530823e6494c208f592530825d6594c20c7952530831d5494c20c7992530831d6494c20c7951530831d5454c20c7991530831d6454c208f990530823d6414c209798c530826e6214c209d98453082756114c209e980530823f65d0c208f597430831e53d0c20c754f43082b561d0c208fd95430823d6550c20c794d430831d5350c208f992510823d6494420cd95251083355494420d594e51083555394420cd99251083356494420cdd0e51083354394420cd95151083355454420d594d51083555354420cd99151083356454420cdd0d510833543544208fd97410823d65d0420a758f410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd545410832d54c8020d354f200836551c8020ce55220083595388020ba58a200837151880209bd95200832d5448020d354d200836551480209ed9520083395448020d654d20083715148020bad95200836b6548020ead9120083a86448020dad5120083aa5448020da55120083a95448020ca551200836b5348020f294d20083695348020f254d20083495348020ead0d20083a94348020f894520083695148020f854520083615148020ead0520083a941480209798
  | 2 => 0x6110a40ae580429029d63d0640cd94541903355150640ad587435031f5350d409798c525025d63149409d984525027561149408f997425029d63d0540cdd45415031e6454c40c754f43102b561d0c40c794d431034e5394840d354e521032f4394840cb50e521034e5354840d354d521032f4354840cb50d521023d6590840c754e421032d5290840a758c421031d5310840cb54842102b56110840ae58042103565394440d554e51103665294440d954a51103374394440cd50e51103565354440d554d51103665254440d954951103366454440cdd0d51103354354440cd90951103344254440a758f411031e53d0440c754f411032e52d0440cb54b411033551d0440c794d411031d5350440cb949411032d5250440cd945411031d53d0040cb54b401033551d0040da54a401023f6550040c754d401032d5250040cd545401027b6550040da549401027661953309d58654cc2b56195330c798e54cc33661953308f58654cc33561953308d58654cc23f6155330ad58743cc31e5450f30a7d9543cc31f6550f30a7d8543cc31d4354b30a759332cc31d54ccb30c755132cc23e64947308f59251cc31d43947308fd9741cc23d65d0730a758f41cc23f65507308f59541cc29d64cc730e550731cc29d644c7309b988548c26d62152309d984548c2756115230ad587438c23f6454a308f191528c23e64946308f592518c29d63d0630cd945418c33551506309d986544c2756195130ad587434c29d6490d3097195434c2d86050d30c7d95434c31c6550d30a7d85434c39b6050d30e6181434c31d43d49308f990524c23d64149309d984524c2756114930a7593324c23e64145308f590514c31d43145309b988514c26d6214530a758f414c3375150530cd145414c29d64cc530e5507314c29d644c530d5145314c39943cc1309b98b540c26d62d50309d987540c27561d50308f596540c23d61950308fd8d540c23d63550308fd85540c23e64150309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23d65d0c30ad587430c23f6550c30c794d430c32e5494830cb552520c32f4394830cb50e520c32e5454830cb551520c32f4354830cb50d520c23e64944308f592510c3365494430cd552510c3665294430d954a510c3366494430cd592510c3374394430cd50e510c3365454430cd551510c3665254430d9549510c3366454430cd591510c3374354430cd50d510c23f65d04308f597410c29d63d0430cb94b410c32d52d0430cd947410c33551d04308fd95410c23d6550430cb949410c32d5250430cd945410c3355150430c7553300c34d52cc030d5547300c369528c030dc546300c25f654c030c7551300c34d524c030d5545300c27b654c030e6d0d300c369524c030dc545300c25e63153209758c54c
  | 3 => 0x31da94a500c7695294031ec506500c7d13194031ced0e500c7394394031ced06500c7394194031c750d500c7354154031d54c5500c73a5454031ce551500c7994354031da949500c7695254031ec505500c7d13154031ced0d500c75a4354031ce50d500c7594354031c650d500c73b4154031dc905500c7394154031dc505500c7314154031d6cc5500c7723154031d64c5500c7713154031d44c5500c65e63153219758c54c867a60153219e58054c863e6494f218f59253c863e6414f218f59053c867a6014f219e58053c86b561d0f21c794d43c871d5350f21e350d32c869d63d07218fd9150c863c64543219798e548865d6395221a758e548871e63952218f58e548871d63952218758e548873661952218fd8d548863e64d4e218f593538863e6494e218f592538863e6414e218f590538867a6014e219e580538863f65d0e218f59743886b561d0e218fd95438863d6550e21c7d4d438871c5350e21a758f41887365450621add9541887376550621add8d41887365350621cd14d41886b5648c621e550e31886b5644c621d514d318873541542219798e544865d63951218f992534863d6494d218f990534863d6414d219e98053486796014d21ad587434871f5350d21c714d434866c654c921e350d324869d63d0521ad59241486746550521b918941487376550521cd19541486b76350521cd94d41487345350521e9d8941487a46250521e98c941487a53250521ad5923148795438c5219d19531486b5644c521d514d31487c5324c521e9506214873541d41218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863d63950218fd8d540863e64150219798c540865d63150219d984540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f43086b561d0c218fd95430863d6550c21c794d430871d5350c218f992510863d64944218f597410869d63d0421c794f410871d53d04218fd95410871e5350421c754d41087365150421d354f21087355488421d554e210866f6548421d354d21087a741484219dd9521087355448421d554d210873a5494021ce552500875a5394021d654e500873b4394021ce50e500873b4194021ce506500873a5454021ce551500875a5354021d654d500873b4354021ce50d500873b4154021ce505500876b2154021dc88550087692154021dc485500871d53d0f40ad58743d029d63d0740cd54741d02b561d0e40c794d439031d5350e40a758c42902b5
  | 4 => 0xe58042506d663d05419798c505065d63141419b988505066d6214141cd58753506b56194d41add85535071d5314d41ad58652506b76154941a798c525069d6314941ae98052506b960149418f997325063d65cc941ad98632506b5618c941add8532506b4614c9418f994325063d650c941ad98432506b5610c941ae98032506b9600c941a798f515069d63d4541ad98f515079663d4541a598f515079563d4541ad58b51506b560d4541a798c505069d6314141ab98850506ad6214141c798e541071d6395041c754f43106b561d0c418fd95431069d63d04418fd9541106776550441cd95141107356195331c755332cc71d544cb31a758f41cc7365490731a7d8d41cc6b76550731cdd9541cc7346550731add8d41cc7976350731e518d41cc7355250731e5cc941cc7953250731cd50550cc71d6395231ad587438c71e5490e31add85438c71f6550e31c7195438c69f6150e31e5d85438c7946150e31c750d528c69d63d0631a7593318c73554cc631c750d508c65d63951319d586544c63d6395131c758e544c61d63951318f586544c73561951318d586544c63f6355131c7d8d544c63f6155131cdd85544c6b561d0d31add85434c63e64d49318f593524c63e64149318f590524c67a60149319e580524c71d54cc931c7551324c6d4614c931a758f414c63f65505318f595414c69f6350531cd553314c71d548c5318f993504c63d64d41318f990504c63d64141319b988504c66d62141319b98b540c66d62d50319e983540c67960d50318f596540c71e6395031cd986540c63e64150319b988540c66d62150319e980540c67960150318f992530c63d6494c318f597430c6b561d0c3197596430c69d6490c31b5586430c63f6550c31c7951430c69f6550c31c7d95430c69f6150c31e5985430c7956150c31cb952520c72d5494831e350e520c72f4394831cb50e520c71d4354831cb951520c72d5454831e350d520c72f4354831d390d520c72d4354831d350d520c70d43548318f992510c63d6494431c750e510c63d65d0431a758f410c72e52d0431cb54b410c6756590431ad592410c6d56390431e550e410c76552904318fd95410c72e5250431cb549410c7365450431e590d410c7954350431d9549410c6b76550431cdd95410c6b76350431e598d410c7956350431cd94d410c7a65250431cd549410c7a55250431c9549410c69d64cc431d354b310c79541cc431ad592310c6d5638c431e550e310c765528c43197d95310c69d644c431d3549310c797414c431e5505310c677654c431ad591310c797434c431e550d310c765524c431b5d95310c757654c431b5d91310c796644c431b5591310c795644c431a5591310c796544c431e5551310c7c6524c431d5549310c7c5524c431d1549310c73a5494031ce552500c7994394
  | 5 => 0x4210b1d53508429bd954210b565394442d554e5110b374394442cd50e5110b565354442d554d5110b366454442cdd0d5110b354354442cdd095110b354254442d694e5010b595394042dc9465010b715194042ced0e5010b394394042d694d5010b595354042dc9455010b715154042ced0d5010b394354042ced095010b6a4254042ce5095010b6942540429d98654cca756195332ad58654ccb1e6395332cd98654cca3d6195332cd58654cca3561953328fd8554ccab561d0f32c795143cca9f6550f32c7d9543cca9f6150f328f99251cca3d6494732c750e51ccb1d43543329d984548ca7561152329e980548ca796015232ad587438ca3e64946328f592518ca3f64542328f191508ca7661951329d586544cab561d0d32a7592434ca5c6550d32b3189434cb1f6550d32c7195434cb8f6250d32e3189434ca9f6150d32e350f324ca3e64145328f590514cb1d43145329e980514ca796014532c750f504ca3e64141328f590504ca7661141329d584504ca7661d50329d587540ca7a60d50329e583540ca3d65950328f586540ca3f61550328f990540ca5e63150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430cab561d0c328fd95430cb1e5350c32c7553320ca5f654c832c7551320ca6f654c832e3d0d320ca3e64944328f592510cb365494432cd552510cb366494432cd592510cb374394432cd50e510cb365454432cd551510cb366454432cd591510cb374354432cd50d510cb573254432d98c9510cb553254432d94c9510cb3a5494032ce552500cb725194032dc546500cb3b4394032ce50e500cb3a5454032ce551500cb725154032dc545500cb3b4354032ce50d500cb5b3254032da8c9500cb593254032da4c9500cb1e6454f41c754f43d071d5390f41c794d43d071d5310f41c754f42d071d5390b41c754d42d069e6310b41a758c42d071d5310b41ae98042d06b96010b41ad58753d071f6554f41c7d8953d071e6254f41c758953d071c6254f41c7d8553d071d6154f41c7d8153d071e6054f41c758153d071c6054f41c754c53d06b56114f41a798f52d069d63d4b41c754f52d06b561d4b41c754e52d071d5354b41a798c52d069d6314b41c754c52d06b56114b41ae98052d06b96014b418f99732d063d65ccb41c754f32d071d538cb41c754d32d063e650cb418f59432d071d530cb41ad98432d06b5610cb41ae98032d06b9600cb41a798f50d069d63d4341c754f50d071d5394341c754d50d069e6314341a758c50d071d5314341ab98850d06ad6214341ad587439071d5350e41a758f41906d663d0641ad987435071f5350d41c714d43506b46150d418f994435065e63149419758c525067a60149419e58052506b66190941a798c425069d6310941ad98442506ba6010941a
  | 6 => 0xe8cf8000030020900180c0360080281600600c0180c0060080580001a0900380400c0041c0020200ec320060000000500000004c178130040340200101603c020010000480181400200003000006014038000180000500a00a000000060120000000800c0000100001203c0a807032010050130320300e80407c0080883300207c00004000008020040080240a80a01c040020060140182c00300a014028140300680180f0020240f00300404000012012020030040200000300303e0440100900003003015002028098050200001000008e0000000700e01c058190000440180000a0380480100e0000e0070080300a0000120040000300400007001000000008070020ac008030340000601100400000806016038090010100580080000205c1a80201e000008050120b80081304a0200680a00c000028010080bc020010420201a81105e000020040000fc01800008000038000020000180000200c000100080280b00100200403008008008028040020080f0090300140400600a00413000002000020000000000080700000c01001008024010110000000080f000010070020640580180101602400804050054000120040000000102803800001000054010000240140c0120080340000b0120080100200000c04802010028040060000b80182b0220740200e000030108050080080a8060260180000c1540040082b01204c0000503600c0200200602c0409100803c09803002004010360120400783701e064010050000081100205e0000c01701e0180080400401001004004000028030000040600c02405000004000048010020020001381a00404c0401e00e0100003f00200400000006000038000000200380700202000001cd99151d0eb661d4b43ad58752d0eb66114b43ad58452d0eba6014b43ae58052d0f376554743cdd4951d0f365254743cd54951d0f345254743cd58d51d0f376254743cd98951d0f356254743cd18951d0f376054743cd98151d0f356054743cd18151d0f355114743ad98750d0eb561d4343cd54750d0f355194343cd54550d0eae6214343ab58850d0eb66114343ad58450d0f355114343ad5874390ed661d0e43b59874350e7661149439d5845250e7a60149439e5805250e6e62141439b5885050e7661141439d5845050eb661d4d43ad5875350e9d62d4d43a79875350f9661d4d43a59875350f9561d4d43a75835350eb66114943ad5845250eba6014943ae5805250f355114543ab9885050ead6214143ad9845050eb56114143cd9865410f356195043ad5874310e3f6550c4397d954310f1e5450c43c754f43d0ab561d0f42ad5874390b1e5350e42c754d4390ab561d0d42c7d4d4350a5e63141429758c5050a7661141429d5845050b1e6454c42c754f4310ab561d0c42c794d4310b1d53d08428fd95
  | 7 => 0x9541c626b865a35137987817826800216a308ea8789652200879d09999cf8af21b8170dd8001c98000670ce0fb9189a0a5d26d18faa5a7725c8a29bd11427ba6015b8000002a60d51989a48b102306e80706906b1dca301c72961bf0758021011e304c9362880cd80007b0538001129b31179059e28ba05500025b0f50000891901b61cc2141221fd19200024985e22f9d795288f9ab9f186fa2315b0d08af8001c78c216e9390dca01a430b504d8001048001051f412f097000149a5f15a06790c1cd00009880012b8000000002029dd0000000760f08001d929a0e314e80008d0002768000ec9638148001090000001000f482a83700014600000027d00a29b00018ca7386a8001928398859888001db9110f79bb1228258002560001f01e18a70000199ba0000000c580015c000000050a420000000000990000221a89449520000502778d41f80002a387c154816a66a1d17992b0e58b390f283176831a4f85d1e90001cda5a23e210800000000036146a4f224a6c2900000001d693c9b58001410002381370000a01ad8f89ad04900000016b8001268d1a0705b87ca99aa506c1b3893000000a400001b71b92411700b792590416100000027a08b11918a80019329d21e8bd2920ed0a08000710002671be965a86a5e8000109d495f9d593f0312a9990aac1669f69839f60001cf0909c381aa150b60ec2371bc92a00000017716483306498b8ea201174294a7008c07e80013ba61876a2ba908d71418001e4a4d29fa9394822902e119a679591c505780029582c1af2792270c60000ba8000001719242a40960001ec00014902500002288b8cb88aa320000001511e70002a79c89560410001c20ff2a487d0002550ae0e180000000012600024380024c00000000012e268a001db11b0f18001c589d236a078912280b2891a4e00000015d09b94797d8fd92c1149ec80028a8001679738000ff8be01c8001cb0000000001e880026400000003b8681aa1978000000000000158002348000d98002969831a989f0d207baa110a2330000000840588c890c88482999b0df87f8f9195205a0e0950b30e894a21807211ba17a46a7206999e0de1ae9270001a593d0a99e5a6202818d0000fd11e8d10d88958fe1d11e60dc16e1e1000005a478001e6a2784e0ad95f07d95e0d00000b021300f80000005f0898000000c092daaf150052836a6f80025a8001020000001c118580002e8000f115da118438f200002b9b21c42038001aaa14a520800518ab9da94f8381408540000000ee0002851c289c9bda4d80007e0f58d316c0d5a919441b481d80319120081100891f01505a2aea0c94f2042338001f90b1a7daada638348290218002628000560002340dd24b03421897528101406c8582129811290040000ed80000024189680000011698e0e91ff12
  | 8 => 0x6a0000f81349eaa1aa5129800000000024499480905d800223a310001b2a1f93fa26297a3b05f95500000011c1819538be88317f0f98771fb16918011300c11609411e206a5900f1ca219155a2686d16d80e14726c80b0ab0d29862a0a6e142269a4810e2940019c68c98ef93b20322c0448d91139a694399428389d9ba9de8bb9d60838741bb986a8208f1ed893932a819b88da8f60002aa80024e96a0098001d2a1a1f315184b0000570f2a5829701c0479a304f0ce95e98e8c326810393825d80022117903898483d90d03e1609b18e117491221e1c09350820fa1589450011a00a20000211bfa2229527119b80694a87781291a090066106145a491ee9882659429581cb96a8888fe8638e71b097b2389a18a4a8704a84f8a60c023f9c182c93383b11700026d9151f28cd15a80007000029a8aca5990f9ac94e0001d89f39eb0e385c82a0001d71a29e80618432718a88f000aa7480020da7e020a2da7087298a2509c328287826ea4584081f9da17e83f81880013582f29c93123c8002101a6275272a5405900004a00023a80028e13e1d20ef28029c1d427606f0a80000fb1238620bf20b20f1a409c279a531ce0ca29d97e20614891184190da780000e219580017ca3d8531fe13880005aa2a8120bf9629dda7300010ea3280004980000012f91f8000000978190001d18000000001340001530000001b809e0000001660002170000e783f1e797a9071a52aca39a7b23c1820a7830177a3903a0920001961a8204a4716427408106da630caa3ba8ba8f1808850002890868a39faa6500000d8cc8f304ea9e80026f0cf07a80000013680000008a0de91a80b85200003a94d12499c1f48e02758bb17800c899a55a7f8050689d526a8328aa9509ab0062a71ed0000002a30000001331de0c1a12000000000000000000170930a0faaba8f8002519eb89293c1caa9f1630000b9a44107a241b9a450e522ca289100629430079892a1a60a3622b1ee0640c78668461181030001bc15780024a80006a1ae0f6800125182a610130e984d04682422e28d1281a798525282784c28e8420708ae9c902f9cc8c70cb04ba0a1029c4a5e06b8a40000001f21fc80002380000013996880000005e9ff80488e02d90099aa1c93198f17c20ba2e89aa571e528a2690d39c810808c80000000024c80000028403909e80027c86500000000000023a1210730001b120903e94c0871c00001d82461d30200c682d0b910a9f598996f0c385c2299788e423f0000cc2a287380000019d27e8a51b680028480001e82b14ba021760000719fa0000000bc00000019f17b8d80b81b02809e0aaa1ce8b09f888e85b0db0aa06114b0eb225127a3d101a9b8510880f38002549dc26b20d1e00da13000d191aa688081a2538c929924098c26603228d91d0608b88c500016f
  | 9 => 0x2859df87500000000012001baa02ab04021123189b1d39a20792500308001711b51982889ea14c99f83380009a1f08e60d495c95701f0248fc0e819c97d0ee96b169975a0aa9117325fa8984887f074a8b235a051f11ef01b156a089f71099fdaa92930819ac19a1728ad12090b0000e6921a5c27f00014d96d16804598d8000b21970350440599a1215a488001088000a32ad0e09be225856a8627aa081a70118db96021da3e8f422190b8000000080fa8000b683d19e800128a1b0000c288601d08d9b78fc92d1ef8c800397fa1f0000001e3894aae0289990450bd854a0e8160e4aaf99d8101fb9f791da57a568ac1f517222093e80011580017a0261fc0799d98a18000181b42a8847013a87a2f20c2a20a10d7a2a0a58df0b428c0c41d011c910a5ba1c0600828f712993d84298b184278a161402139df05586304825896227c0c48d68e2959802aa829e222827196a9887a26480024a12c9a3a37a429f99af8b5a0992303586e1e40d60b496c81e0a680009f96180016703c28c9321068001871a903793a22d1fe8000c100e8000001e20000bc8980eb92aa92a4b8b70a91e983c99380021993aa
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x9851671d9543cc21ab88c8a9461325c86050d309a2e2302869851671d95434c2c4b90c0a1a61645c46050d30c1a86b10a29852572145414c30ab20a298a61515c8514c530a4ae3a1ca41852571d0d520c21abb686a88618358e52d0430c1ac6a96821861563947410c30ab1aa3a0861465d7434c030b22e3a1a601870b43549300c389a1aa2980610d5c66494f2083ae7324a39043571992538820eb9cc928c410ddc563d512083ee6b0ea89060d63588544830ab1cc22a2418598d6115120c2ac6b08a89062562584544830cb1ac02a2418a5896015120c62c2b00a89043571992534821ab88cba1a410d5c46550d20838eca9a86905147154d4348264b98c0a1241385c46050920a18eaa1a64904a9741813248270b88c099241075cc65d052083ae632a8290524755052148254ba0c090a41325cc6048520992e631280904e171189404828c3aa86982412a5d0624c1209c2e2312609043571d8d540820eb9ec2aa0410d5c66494c20a2ae3324a61051571991530821ab8ecba18410ddd561d0c20c2ca6b0e861061553587430820eb9cc928841455ce649442086aeda1ca21051573991510821abb686a8841075cf65d042083eeab1e821041d7694f410820ebb2a7a08418558e51d0420c2ac6a8e82105897319120082d0b88c890041525cf5448020ac2e3aa240105297595120082953b2a8900414a1d95448020a56e6aa2401052b715512008294ba6a690041585c75348020a92eb29a40107095494d20083852a2a690041c25515348020e14e8a9a40107097454d2008385b22a690041c21915348020a52eba1a401070953d0d20082d0b8e86900414a5d54348020e12a6a1a40107215494520083a0a9ca290041c89515148020e42a8a8a40107425354520083a0a9aa290041c89d15148020e42e8a8a4010723645452008390322a290041c8d0d5148020e4286a8a401052975d0520082c4b9e8290041c254f4148020e42a3a0a4010529755052008384a9a8290041c85454148020c2ac730ca98850d7214d43c420eb9cc9a9621459ce545071092ae7b2a838851673d9541c421b3b4a6a0e21495c85350710c2ac829a63885457214d31c420eb98c8a94214a5d05248210a92e6292410850d7214d4344268b98c0a0a21385c86050510a2ce7b2a82884367694d4144292b90a6a0a210d1d95250510a28e6a9282885917318141442d0b90c0a0a2185590534c510a8ae429a62886186550d304431832a829822194195314c110b22e898a60885297414920442a4b98a4902212c1d94148110ac0ea90a408841d73d85540421ab8acba18218594d61d0c10c2aa6b0e860852571d0e5204292b8e86a9021075ce649441083aed29e820841d7654f4104306b1ca5a08218358d52d0410a62eba0a200859173d051004388a9e8288021c854b4144010
  | 1 => 0x53d0687390c0a9e83435c86054f41a2ae2302a7a0e196018153d070aa9ac2296838654e6014b41c32a6b00a5a0e155398432d070aa9ac2196838654e600cb41c32a6b0065a0e0d5398850d0706a9ac4286832c5c0614c941c2aa830a6498cd170185324c68bbaac2a1863495c74394831a1eeaa1aa418d2571d0d520c6a2b8c86a906343dc54354831e0ce2a1aa418f057150d520c706b1ca5a08638358d52d0431c2acaa1c8218e456354a410c782a1aa520863c190d5250431e0a86a928218d157598d410c68bbaac6a086389d955250431c4ec6a928218f0663549410c782b1aa4a08638359152cc431e0aa4a0e6218e256454a310c782a1aa51886307dd5644c431c1ac8a926218f0552d05310c782a9282988630ddd5644c431c4ac8a926218f0743549310c782a1aa498863255d3654c431a2aeb3226218d1775591310c64bbaac89886385dd5644c43192aecaa26218e8564949310c70ab22a498863a1591524c431e0ca8a926218f0554549310c723b22a498863c1991524c431c8ac8a926218f0564549310c702b22a498863c250d5294031e42a4a0ca018d91744c6500c7a0a9263280634c5c74394031a32e7a0ca018d15744c5500c68dbaa86a8063c250e5254031e1286a92a018d3375505500c79129282a8063c85494154031b22e898aa018f12544c5500c788aa262a8063d09493154031e82a498aa018d3171d0d500c6a8b8c86a806346dc54354031e24e2a1aa018f117150d500c68cb9e82a8063545ce4154031e228720aa018f1243505500c788a1a82a80634cdcd4154031e24e6a0aa018f1173505500c68cba662a8063c45073154031a62e918aa018f11438c5500c68cba262a8063c4d053154031e228298aa018d31744c5500c789a1a62a8063c450d3154031aa6e898aa018f12744c5500c6a8ba262a8063c45d13154031a22e898aa018c1d7319150c870ab1cc32a443465c05350e21a2ce72a28310c9573d95418868b39ecaa0c430d9da5350621a62e029a8310e156414d31886a8b80a698c43465c05350d21c18caa1a6490cc5731894148670b80c4a0a43459cf655052186ced29a8290d317014d41486c2b98c4a0a43685c06250521a48ea9928290e156414d31486a8b80a698a43511d5324c521d0ac89926290e1653587430870aa9ac3a1843075ce649442183aed29e8210c1d7654f4108692bae8290843615cf4148421e0aa7a0a4210d3171d0e500868cb9e83280434c5c74354021a32e7a0aa010f2341485500868ab8cc8a98818554d61d0c40a4ae3a1ca42052571d0d5210306b1aa4210818554d6110840c4aa4b08842061953580421021abb68728881455ce6454440a2ae6212a22053170109511020ebb4a7a08818358e52d0440c1ac6a96822061563547411030b31ac32a661459c65450f3092ae3b2a87
  | 2 => 0xb496a7baba3481e7800057a0e10000b7288282ee0029e0b8b600110000bc002561222cba1a66b0d4862022a0e4689241e9bc590361197c070008d80000184b59c688a24040180009e328b8001402202c48932002ec3d8004c000ba8000000a7e800692a0002a620974b28f08c060059a81f1cc0110e740943a920000b0910c87e00000292b323e5a2b45485e001280c9560003c0000016a5ca70000000055268310005ba1665a64969e81f95a8aa4a931d6661ea1c1b081a1e708242f91c3e878459a02aab830284850625c1b86d2c8b502a398305c98c8d1d8a2ae07505c8ca4e1baaa4f9b246a9a522788b80262190608806719a580423f28c40aac1508a23800b080e849340008c5e99e128000012c000ee53af0960e881000aca7a650002b266b8ab6292389f8269480000086770b200006b186c211da989782d000a00288a09a080a226000801e60f8000005871000589ae42282110009215c04a707c19230866881fe08ac000000002508717eab9c03ca10000000003400226000504780015a98518003626c978001a0007f000b3ae67b2c4270feb41586e90a069f6510ba462da4f2be541860e166371ce4b9aa1d93a0e92663a6a9094a1c8ae378140327c4d9061d0cc982de79142a18e2821caa586aaf24631900748a6788000000000000000000012a0004c002e49c94c191f2368d05b1b6a3a3c9da0a35892001de00180a8a0cb62549d09624000338005d84e001f44e0f4000000023a9b8000218a720e041240ac2a4430ecaa21aa41126f9143e052a50181404810240e0c01c1e010286406190500c0000000382e09008080003008000000000003421188340c16050102000208100c0b0080000030f818021501864020204008000f0081400040d0141002110100c07028085a000d0000a1400004080300008000001004020b0081400000380c120100010042e21800120013808000c1b8303a050101c122403008134c9c05254743a62e0292a3a1d157318951d0f12b10c4a8e874c9c06254743a62e0312a3a1d157318151d0e93390c0a8e87495c86054743c62c0302a3a1e266254450d0f12b12a228687455c66454c42c2aa6b0e862143576d0e5110a8ab9cc8a88854c5c74394042a62e3a1aa0216166358654cca8b38ca8a1e65255c76550f32a2ce3b2a879943571191508ca62b88c4a1a65325c06250d32a2ce3b2a869958571189434cac4b80c4a1a658650d6014532a1aeba1a641958571d0d320ca1abb686a8865c1d0d3254432a62e3a1ca01953171d0d500cb85a1a64a8065075d66310b41c32a730085a0e195358042d0706b10c4a9e83455c46254f41a34e0312a7a0d1970189
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x5871e0002a3a888854001080100060000940180000b800000094000051c00000240001180000000e500000004641894e48b10000000000a4300260000d4c78a9a006c200007c000050404001020c0000608100c05735886254743c21625c06254743c11735806054743c21725806054743a0586d0d3254432b0181d0d3254032c05625c46254f41c09625c06254f41c09725806054f41c11715806054f41c11545c0614c931d01745493194031d01749493154031d01745493154031c11645c0534c621c11645c0534c521c0475591324c5219058754f4148421b0183d052154021c05645c8514c530b0181d0d524c03091187d0d514c030905811d5434c920905831d54148520911811d5434c12092181dcd544802090983dc55448020b01819d15348020909871915348020b01811915348020d01535c74348020b01839d15148020921871915148020b0183191514802092187d0d51480209098754f4148020d01735474148020c05645c8534c710c05645c8534c510c10655d1314c110891831d941481109118754f4144010d017354b4144010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 884
  | 4 => 1376
  | 3 => 377
  | 2 => 43
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s5K5 (27102+((h/294+packedAt s5K5 (23868+(h % 294)*11) 11) % 1283)*11) 11
  | 4 => packedAt s5K4 (57326+((h/458+packedAt s5K4 (52288+(h % 458)*11) 11) % 1652)*12) 12
  | 3 => packedAt s5K3 (19598+((h/125+packedAt s5K3 (18473+(h % 125)*9) 9) % 453)*10) 10
  | 2 => packedAt s5K2 (2678+((h/14+packedAt s5K2 (2580+(h % 14)*7) 7) % 81)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf7c3cf7e71ff18e3e3f231e38fc738f9c470cf
  | 1 => 0xb9fc0f9f818fe0fc7c7c3e3c0e383f3eda4333
  | 2 => 0x3efff01ffe0fff007f8fc03ff03fc03f238c3c
  | 3 => 0xc0ffffe0000fffff800fffc0003fffc03c0fc0
  | 4 => 0xfffffffff00000000fffffffc000003ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4102020101040400004082010808001045
  | 1 => 0x4244224424124240c0841224248812148a4112
  | 2 => 0x80088008002400090010400900120020008428
  | 3 => 0x1d91040149489080092aa4804124a480340a80
  | 4 => 0x6fe228516100d4d2524f393269808684bf6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8fefafee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36150
namespace PEqualNP.Outside.L_meta_36150
open PEqualNP.Outside.L_meta_36150.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12d50f0b1a6a317110001c00007803660014b11284020000400f10a9ca63e19d2f6e41a2c3629115481d5bb062ccb20815e80289400000491b30060e0d2638b9d4e38146800038000000d080042c1802a0400002ffd500bfe5402ff5500bfc54037fd4c09fe53037f54c09fc5302ffd0c09fe4302ff50c09fc4301ffd48077f5201ff94807fd5201df54807fc5201ffd0807fe4201ff50807fc4201ffcc807fe3201ff4c807fc32037fd4405fe51037f54405fc5102ffd0405fe4102ff50405fc41027fcc405fe31007f4c405fc3101ffc8405fe2101ff48405fc21037fd4003fe50037f54003fc5002ffd0003fe4002ff50003fc40027fcc003fe30007f4c003fc3001ffc8003fe2001ff48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826202ff84131017f8209883bff654c01d7fb2a600eff99530035fcca9803bfd654c01d7eb2a600eff19530035f8ca98037ff644c01b7fb22600dff9913002dfcc898037fd644c01b7eb22600dff1913002df8c898037ff544c01bff2a2600dff5513006ff8a898006ff634c009ffa9a6004ff94d30027bca698013fd534c01deea9a6004ff14d30027fe8698013fe434c009ef21a6004ff50d3006fba8698013fc434c017ffb12600bbfd893005ffcc49800efe624c017feb12600bbf5893005ff8c49800efc624c017ffa92600bdfd493005ffca49802ffd524c017bea92600bff1493005ffe849802ffe424c017fea12600bff10930027fe6498013df324c009ff1926004ff4c93005fba6498013fc324c001ffb0a6000bfd8530067fcc29800afe614c001feb0a600cff18530015f8c29803bff514c019ff28a600eff54530067f8a298037ff414c019ff20a600dff50530067f88298013ff314c009ef98a6004ff8c530027fa6298003dd314c009fe18a600bffc8530067fc429802ffd214c019fe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe6098013fb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ffc813000ffc4098007fa204c003fe902600bfe4813000ff84098007ff104c003ff0826001fe8413000ff82098027ff65440137fb2a2009ff99510035fcca88027fd65440137eb2a2009ff19510035f8ca88023ff64440117fb222008ff9911002dfcc888023fd64440117eb222008ff1911002df8c888023ff5444011ff2a22008ff55110047f8a888003ff63440017fb1a200aff98d10025fcc688003fd63440017eb1a200aff18d10025f8c688027ff5344015ff29a2009ff54d10057f8a688023ff4344015ff21a2008ff50d10057f8868801fff624400f7fb122007ff9891001dfcc48801ffd624400f7eb122007ff1891001df8c48801fff524400fbfa922007ff9491003ffaa48801f7d524400ffe2922007ffd091003ffc848801ffd424400ffe2122007ffcc91003ffc648801ffd324400ffe1922001bfd8510017fea28800bfe5144005fb28a2002ff5451004feaa28800bfc5144005ffa0a2002ff90510017ec828800bfd4144011faa0a2002ff10510017fe628800bfe3144005fb18a2002ff4c510007ea628800bfc3144005ff90a2002ff88510017ec428800bfd214400ffa90a2002ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022007fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xbc644c0cc2a81a20400000230004d0006200000318003b07509920038b105c90424003cced00c32000004d8b0364000284f041110000019c2921c003d8fa350004f0000010e2f8ef0002b1b12e280002109b00000000002649f000004a833000dc054000005c1d8003000000000418001b9054c4004d03832c550791e44d1a0004c000360000000000378002f400000df1749a00124208003205f00116000fd278a718c5316903348184648a4940834cbc38d18064e6184fb29000000004b44400000000ce000c908030001404ac1c34104000e700000120242145b0000000000450744e8fc004002193f4cc580005043489010f400000299223946b4e0983a85e22cbb0002a0006d000a341c0023c39100c70006a0f0000b0000000634407308db390001c4e144128000d6000000000009c002a0b50fcb725137328cd0000d420af12cd8048950f8cf0845945c004f47200000000e21cc000011f238f23c0462ac28144f704c0010c663fcae248c10e800000ba1fc7b000000008c4b0ad0d40011cf124c000000045400000e80000005857310340942d12880000e00c4003540f47000244b3000a92d0b60dca2008fe46d350447a02c00000300001000140c010a80804010080000020000004000102004010001408010203000010c01804050000c1a030003c48040180002000300000000301c0003008000800000000001018040203000000402000081c02020100000028000e030000402040080c00000001002130100800010082002000080825ffb2a6212bfd9531097fcca9881afe654c425feb2a6212bf59531097f8ca9881afc654c423ffb226211bfd913108ffcc898816fe644c423feb226211bf5913108ff8c898816fc644c423ffaa26211ff9513108ffaa898847fc544c4057fb1a6204ffd4d31027fca698813fd534c409fe29a6204ffd0d31027fc8698813fd434c409fe21a6210ffd8931085fec498843fe624c4077f3126210ff58931085fac498843fc624c4077e3126210ffd4931086fea498843fe524c421fea926210df54931087f8a498843ff424c421ff2126210ff50931087f88498813ff324c409ef9926204ff8c931027fa6498843dd324c409fe1926202bfd8531017fea29880bfe514c405fea8a6202ff14531017fe829880bfe414c405fea0a6202ff10531017fe6298813f7314c405ff18a6202f78c531017f8629880bdc314c405fa18a6202f50c531017fe429880bfe214c405fb10a6202ff48531087ea429880bfc214c401ffb026200bfd813107ffcc098806fe604c401feb02620fff1813100df8c09884bff504c41fff2826212ff5413107ff8a098847ff404c41fff2026211ff5013107ff88098813ff304c409ef9826204ff8c131027f86098843ff204c41fff1026210ff4813107ff8409880bff104c405fb8
  | 2 => 0x1a4f9474d73b84e000830000006c000000049c0000123404001c0b9258003ac2e1a10a001410f40043005000a530c6f2207d030770012900000000002fc000740000000000000880000000374da4000025cf54e400114523a4004ec5642cac00078194b20ed2f000142848d125024f89c00000448794c809000f8001211087c2e1260009d180c50010f1f8410005407c000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb705853000ddc764c530016dc764c53000cdc764c530115df754c530115dd754c53010ddf744c53010ddd744c530105df724c530105dd724c5300fedf624c5300fedd624c5300ff5f524c5300ff5d524c530025df714c530027d7714c530007d7614c530016de614c530016dc614c530067d4614c530016d4614c530067d6214c5300ffd5214c530007db704c53000dde704c53000ddc704c53007fd8704c530026df604c530027db604c53007fda204c5300ffd9204c53007fd7104c53007fda104c530024fe76d8d10056de63d8d10004ff75d8d10034fe75d8d10004fd75d8d10034fc75d8d10004ff74d8d1002cfe74d8d10004fd74d8d1002cfc74d8d1007cfd73d8d10056de43d8d10006dd43d8d10004ff72d8d1001cfe72d8d10004fd72d8d1001cfc72d8d100067f52d8d100067d52d8d10006de32d8d10056dc32d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d100f6df31d8d100f6dd31d8d100f6f621d8d10006f521d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d100e6df30d8d100e6dd30d8d100e6fa20d8d10006f920d8d10024ff7658d10056dc6358d100ddf77158d100edfb7058d10004ff7558d10034fe7558d10004fd7558d10034fc7558d10004ff7458d1002cfe7458d10004fd7458d1002cfc7458d100e4ff7358d10006df7358d10004ff7258d1001cfe7258d10004fd7258d1001cfc7258d100067f5258d100067d5258d10056df3258d10006dd3258d100dcff7158d10006f77158d10066f62158d10006f52158d1007cff7058d10006fb7058d1007efa2058d10006f92058d1000df4764c510026f4764c51000cf4764c5100d5f7754c5100d5f5754c5100cdf7744c5100cdf5744c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510057d4634c510026d4634c5100c5f7724c5100c5f5724c5100bef7624c5100bef5624c5100bf77524c5100bf75524c510057d7324c5100bfd5324c510007f3704c51000df6704c51000df4704c51007ff0704c510016f7604c510017f3604c51007fd7304c51007ff2304c51007fd5304c51007ff2204c5100bff1204c510015f8764c110026f8764c110014f8764c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110057d8634c110057da534c1100afd9534c110057da434c1100a7d9434c1100b5fb724c1100b5f9724c11009efb624c11009ef9624c11009f7b524c11009f79524c110057db324c11009fd9324c110007f3714c110015fa714c110015f8714c110067f0714c11000efb614c11000ff3614c110067f2514c1100aff1514c110067f2414c1100a7f1414c110067db314c110067f2314c110067d9314c110057f1314c110007d1314c110067f2214c11009ff1214c110
  | 1 => 0x114005897558a80037c00001380182873b00000005d25d480012289a8a3709b1024f1f05488ce000a5c40d2e238721d000ed6eda001a400006515cb2000032d683600000cc00002345a855c178f8e8702ac78aa003108600318180079002185c7239b0d1e0000208b0700000000002400000880f000ea2a30128501a3d03c68dd180002c901900000e30033d32104d098007e00345667f3887d8474572457ab05326c584542225aa222a0dd98a00a029ce984a8600a55269397e7b3127926db199bdaea712838d4be0917c5e0c6680580d33201cce8c1f9b8a468261e0360405a513e6b72b1c00c82111ca0496c8018c8b30ac93abc1888506a132ad87a5b25b412cb511aecda415784cb41c40399920004ae42e9215ab432d6200d5b0d200020709c00314ac53000e840776f0094a4601b9000516e1f552110000013008000200018000000000201222000180c05078040405000980e282185c060d1a8300202000089403000000413000240204008941c070000002080183004070080c2c020280822210004c1404038102a000102c020000cfe76d81310efd431d813107efa60d8131004ff75d8131034fe75d8131004fd75d8131034fc75d8131004ff74d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d8131004ff72d813101cfe72d8131004fd72d813101cfc72d81310067f52d81310067d52d813111edf32d8131006dd32d8131024fd71d813100cfc71d81310eef621d8131006f521d813107efa30d813107efa10d8131067d4315813107ef86058131014fe76d8530066f661d8530004ff75d8530034fe75d8530004fd75d8530034fc75d8530004ff74d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d8530004ff72d853001cfe72d8530004fd72d853001cfc72d85300067f52d85300067d52d8530126df32d8530006dd32d8530066f641d8530006f541d8530066f631d8530126f531d8530006f721d8530066f421d853000cfe70d8530024fd70d853000cfc70d85300defa20d8530006f920d85300def710d8530066f4615853011df
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x780008800000000000095c00001002b5039b06360003100000290674000000178078e849500000000084880140150d0e6001e00c96a45c00f94405c000002000000d400000dc00020000330201dac4670000000898b1800030006800032013000000000249dc8500000340058000010008086000800200080000004100000010162fa1375d81310045ec26ebb02620687e85dd3604c4010fb0bba6c0988031bdc952d813101e36392a5b026200ec532487604c4010ff0aba6c29801a1f21574d853002c7bc3a83b0a6000ec532c87614c001cd2a4906c298003b24c920d85300077190a41b0a6002ad686d85314c0010ff0aba6c68801a1f21574d8d1002c6fc3a87b1a2000ec6324876344001cd2a4906c688003b28c920d8d100077090a41b1a200087f855d1634400d0f90aba2c6880023be097458d1001c76412e8b1a20008df835c963440011ef02b92c6880031bdc95258d1001e36392a4b1a20038dc874c963440071e90e90ac688003b14c92158d1000c7d43ee0b1a20038f8874816344001cd2a4902c688003b24c92058d100077090a40b1a2004ad686d8d31440037a10e98a608800b7421d314c11000de9432629822001bd0864c53044009da10c98a6088013b4dd9314c110016e93b2629822002dd0764c53044009da0ec98a608800b341d9314c11014de9c2a629822029bd1854c530440517a70898a60880a2f4611314c11013de9c12629822027bd1824c5304404dba6e498a608809b745c9314c11012f69b12629822025ed1624c5304404bea6a498a6088097d4549314c110
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x7868875492058d10
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
  | 8 => 0x94d
  | 9 => 0x94e
  | 10 => 0x94c
  | 11 => 0x9cb
  | 12 => 0x9ca
  | 13 => 0x9cd
  | 14 => 0x9ce
  | 15 => 0xb49
  | 16 => 0xb4b
  | 17 => 0xb4d
  | 18 => 0xb4e
  | 19 => 0x9c953
  | 20 => 0x9c955
  | 21 => 0x9c956
  | 22 => 0x949d3
  | 23 => 0xb4953
  | 24 => 0x94b53
  | 25 => 0x94b55
  | 26 => 0x94b56
  | 27 => 0x16c9
  | 28 => 0x1449
  | 29 => 0x168a
  | 30 => 0x12ca
  | 31 => 0xb49d3
  | 32 => 0x9cb53
  | 33 => 0x9cb55
  | 34 => 0x9cb56
  | 35 => 0x138c
  | 36 => 0x124c
  | 37 => 0xb49c95b
  | 38 => 0xb4949db
  | 39 => 0x9c94b5b
  | 40 => 0x9c94b5d
  | 41 => 0x9c94b5e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 322
  | 6 => 233
  | 5 => 61
  | 4 => 1
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
  | 7 => packedAt gbK7 (12877+((h/107+packedAt gbK7 (11914+(h % 107)*9) 9) % 467)*10) 10
  | 6 => packedAt gbK6 (11877+((h/77+packedAt gbK6 (11184+(h % 77)*9) 9) % 280)*9) 9
  | 5 => packedAt gbK5 (3739+((h/20+packedAt gbK5 (3599+(h % 20)*7) 7) % 127)*7) 7
  | 4 => packedAt gbK4 (71+((h/1+packedAt gbK4 (70+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x18e00c63e3ff231e387e38707e1f0013c470cf
  | 1 => 0x1f00707c7c70c3e3c071c07f8fe7186d1a4333
  | 2 => 0xe0007f807f80fc03ff81ff800ff8218e238c3c
  | 3 => 0x7fff8000fffc0001fffff000c1f03c0fc0
  | 4 => 0xffff80000000fffffffe00000000fe003ff000
  | 5 => 0xffffffffffff0000000000000000ffffc00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x200000809000040810081002000000401045
  | 1 => 0x19051024242241224124402504c618250a4112
  | 2 => 0x2008248049040400940092000910208a008428
  | 3 => 0x1249490008aa480209254a6000c150340a80
  | 4 => 0x4a4300000000f393234c010320424a003f6000
  | 5 => 0x949c7e72724e00000400060c4194b5ff800000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffeeafefafee8fffffeeafefafee8fffffeeafefafee8fffffeeafefafee8fffffeeafefafee8fffffeeafefafee8fffffeeafefafee8fffffeeafefafee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36150
namespace PEqualNP.Outside.L_meta_36150
open PEqualNP.Outside.L_meta_36150.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 16 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 92 := (concat bs1_4_0 (concat bs1_4_32 bs1_4_64))
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
theorem bs2_2_0 : Interval s2Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 8 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_96 : Interval s2Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 102 := (concat (concat bs2_3_0 bs2_3_32) (concat bs2_3_64 bs2_3_96))
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
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_640 : Interval s2Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_704 : Interval s2Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 725 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 (concat bs2_4_192 bs2_4_224)) (concat bs2_4_256 (concat bs2_4_288 bs2_4_320)))) (concat (concat (concat bs2_4_352 (concat bs2_4_384 bs2_4_416)) (concat bs2_4_448 (concat bs2_4_480 bs2_4_512))) (concat (concat bs2_4_544 (concat bs2_4_576 bs2_4_608)) (concat bs2_4_640 (concat bs2_4_672 bs2_4_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 682 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 (concat bs2_5_192 bs2_5_224)) (concat bs2_5_256 (concat bs2_5_288 bs2_5_320)))) (concat (concat (concat bs2_5_352 bs2_5_384) (concat bs2_5_416 (concat bs2_5_448 bs2_5_480))) (concat (concat bs2_5_512 (concat bs2_5_544 bs2_5_576)) (concat bs2_5_608 (concat bs2_5_640 bs2_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_32 : Interval s4Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_64 : Interval s4Atlas 2 64 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 78 := (concat bs4_2_0 (concat bs4_2_32 bs4_2_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_128 : Interval s4Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_160 : Interval s4Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_192 : Interval s4Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_224 : Interval s4Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_256 : Interval s4Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_288 : Interval s4Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_320 : Interval s4Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_352 : Interval s4Atlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_384 : Interval s4Atlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_416 : Interval s4Atlas 3 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_448 : Interval s4Atlas 3 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_480 : Interval s4Atlas 3 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_512 : Interval s4Atlas 3 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_544 : Interval s4Atlas 3 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_576 : Interval s4Atlas 3 576 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 587 := (concat (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96)) (concat (concat bs4_3_128 bs4_3_160) (concat bs4_3_192 (concat bs4_3_224 bs4_3_256)))) (concat (concat (concat bs4_3_288 bs4_3_320) (concat bs4_3_352 (concat bs4_3_384 bs4_3_416))) (concat (concat bs4_3_448 bs4_3_480) (concat bs4_3_512 (concat bs4_3_544 bs4_3_576)))))
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
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_800 : Interval s4Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_832 : Interval s4Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_896 : Interval s4Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_928 : Interval s4Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_992 : Interval s4Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1024 : Interval s4Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1088 : Interval s4Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1120 : Interval s4Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1184 : Interval s4Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1216 : Interval s4Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1280 : Interval s4Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1312 : Interval s4Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1344 : Interval s4Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1376 : Interval s4Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1408 : Interval s4Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1440 : Interval s4Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1472 : Interval s4Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1504 : Interval s4Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1536 : Interval s4Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1568 : Interval s4Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1600 : Interval s4Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1632 : Interval s4Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1664 : Interval s4Atlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1696 : Interval s4Atlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1728 : Interval s4Atlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1760 : Interval s4Atlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1792 : Interval s4Atlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1824 : Interval s4Atlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1856 : Interval s4Atlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1888 : Interval s4Atlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1920 : Interval s4Atlas 4 1920 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1930 := (concat (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat (concat bs4_4_96 bs4_4_128) (concat bs4_4_160 bs4_4_192))) (concat (concat (concat bs4_4_224 bs4_4_256) (concat bs4_4_288 bs4_4_320)) (concat (concat bs4_4_352 bs4_4_384) (concat bs4_4_416 bs4_4_448)))) (concat (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat (concat bs4_4_576 bs4_4_608) (concat bs4_4_640 bs4_4_672))) (concat (concat (concat bs4_4_704 bs4_4_736) (concat bs4_4_768 bs4_4_800)) (concat (concat bs4_4_832 bs4_4_864) (concat bs4_4_896 bs4_4_928))))) (concat (concat (concat (concat bs4_4_960 (concat bs4_4_992 bs4_4_1024)) (concat (concat bs4_4_1056 bs4_4_1088) (concat bs4_4_1120 bs4_4_1152))) (concat (concat (concat bs4_4_1184 bs4_4_1216) (concat bs4_4_1248 bs4_4_1280)) (concat (concat bs4_4_1312 bs4_4_1344) (concat bs4_4_1376 bs4_4_1408)))) (concat (concat (concat (concat bs4_4_1440 bs4_4_1472) (concat bs4_4_1504 bs4_4_1536)) (concat (concat bs4_4_1568 bs4_4_1600) (concat bs4_4_1632 bs4_4_1664))) (concat (concat (concat bs4_4_1696 bs4_4_1728) (concat bs4_4_1760 bs4_4_1792)) (concat (concat bs4_4_1824 bs4_4_1856) (concat bs4_4_1888 bs4_4_1920))))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_832 : Interval s4Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_896 : Interval s4Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_928 : Interval s4Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_960 : Interval s4Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_992 : Interval s4Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_1024 : Interval s4Atlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_1056 : Interval s4Atlas 5 1056 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1074 := (concat (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 bs4_5_224))) (concat (concat (concat bs4_5_256 bs4_5_288) (concat bs4_5_320 bs4_5_352)) (concat (concat bs4_5_384 bs4_5_416) (concat bs4_5_448 (concat bs4_5_480 bs4_5_512))))) (concat (concat (concat (concat bs4_5_544 bs4_5_576) (concat bs4_5_608 bs4_5_640)) (concat (concat bs4_5_672 bs4_5_704) (concat bs4_5_736 bs4_5_768))) (concat (concat (concat bs4_5_800 bs4_5_832) (concat bs4_5_864 bs4_5_896)) (concat (concat bs4_5_928 bs4_5_960) (concat bs4_5_992 (concat bs4_5_1024 bs4_5_1056))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 48 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_32 : Interval s5Atlas 2 32 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 43 := (concat bs5_2_0 bs5_2_32)
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
theorem bs5_3_96 : Interval s5Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_128 : Interval s5Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_160 : Interval s5Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_224 : Interval s5Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_256 : Interval s5Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_288 : Interval s5Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_320 : Interval s5Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_352 : Interval s5Atlas 3 352 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 377 := (concat (concat (concat bs5_3_0 (concat bs5_3_32 bs5_3_64)) (concat bs5_3_96 (concat bs5_3_128 bs5_3_160))) (concat (concat bs5_3_192 (concat bs5_3_224 bs5_3_256)) (concat bs5_3_288 (concat bs5_3_320 bs5_3_352))))
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
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_896 : Interval s5Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_928 : Interval s5Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_992 : Interval s5Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1024 : Interval s5Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1088 : Interval s5Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1120 : Interval s5Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1184 : Interval s5Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1216 : Interval s5Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1280 : Interval s5Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1312 : Interval s5Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1376 := (concat (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)) (concat bs5_4_576 (concat bs5_4_608 bs5_4_640))))) (concat (concat (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 (concat bs5_4_768 bs5_4_800))) (concat (concat bs5_4_832 (concat bs5_4_864 bs5_4_896)) (concat bs5_4_928 (concat bs5_4_960 bs5_4_992)))) (concat (concat (concat bs5_4_1024 bs5_4_1056) (concat bs5_4_1088 (concat bs5_4_1120 bs5_4_1152))) (concat (concat bs5_4_1184 (concat bs5_4_1216 bs5_4_1248)) (concat bs5_4_1280 (concat bs5_4_1312 bs5_4_1344))))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_832 : Interval s5Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 20 := block_range (n:=20) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 884 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat (concat bs5_5_96 bs5_5_128) (concat bs5_5_160 bs5_5_192))) (concat (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)) (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 bs5_5_416)))) (concat (concat (concat bs5_5_448 (concat bs5_5_480 bs5_5_512)) (concat (concat bs5_5_544 bs5_5_576) (concat bs5_5_608 bs5_5_640))) (concat (concat bs5_5_672 (concat bs5_5_704 bs5_5_736)) (concat (concat bs5_5_768 bs5_5_800) (concat bs5_5_832 bs5_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1 := bgb_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 61 := (concat bgb_5_0 bgb_5_32)
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
theorem bgb_6_224 : Interval gbAtlas 6 224 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 233 := (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224)))
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
theorem bgb_7_320 : Interval gbAtlas 7 320 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 322 := (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
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
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 7 zero,inputs.getD 6 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffeeffffffeeffffffeeffffffecfffffeeefffffeeefffffeeafefafee8ffffffeeffffffeeffffffeeffffffecfffffeeefffffeeefffffeeafefafee8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_36150.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.and,[8,6]⟩,⟨.or,[0,2]⟩,⟨.or,[10,3]⟩,⟨.or,[5,7]⟩,⟨.and,[11,12]⟩,⟨.or,[0,1]⟩,⟨.or,[14,7]⟩,⟨.or,[4,5]⟩,⟨.or,[16,6]⟩,⟨.and,[15,17]⟩,⟨.or,[9,13]⟩,⟨.or,[19,18]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_36150

open PEqualNP.Outside.L_meta_36150 in
theorem PEqualNP.Outside.L_meta_36150 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
