import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_26530.Model
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


end PEqualNP.Outside.L_meta_26530.Model

namespace PEqualNP.Outside.L_meta_26530
open PEqualNP.Outside.L_meta_26530.Model
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

def SBf (j : Nat) : Nat := [4, 6, 6, 6, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_26530

namespace PEqualNP.Outside.L_meta_26530
open PEqualNP.Outside.L_meta_26530.Model
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
  | 1 => 0xffffffffffffffffffffffbfcf9ff8fc3ff39f
  | 2 => 0xffffffffffffffffffffffdff3fcff1ff87cf3
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffff40602810250a4185
  | 2 => 0x2089010908912432
  | 3 => 0x150b506a42a52e18
  | 4 => 0xe221ab493064bc0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 30 s0Pos s0Neg, 0xfcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0fcf0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_26530
namespace PEqualNP.Outside.L_meta_26530
open PEqualNP.Outside.L_meta_26530.Model
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
end PEqualNP.Outside.L_meta_26530
namespace PEqualNP.Outside.L_meta_26530
open PEqualNP.Outside.L_meta_26530.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x3830501420083c92cd10000018030728240080bf43de43bd43dd439d43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2859200e81a01e00012222440001c98230a194606090800547552438fa92871f5150e38a0a1c754f429aa8e851d54ccaaaa39947551328ea9e832d52d063aa998d354b318eaa2631d531025aa4204d544408faa4611d540c29aa4185554430
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x5a0000855875250e0d62d4543835885050e156114143
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
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
  | 4 => packedAt s2K4 (297+((h/5+packedAt s2K4 (272+(h % 5)*5) 5) % 21)*6) 6
  | 3 => packedAt s2K3 (602+((h/7+packedAt s2K3 (567+(h % 7)*5) 5) % 26)*6) 6
  | 2 => packedAt s2K2 (155+((h/1+packedAt s2K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x87ffff0ffffc1ff83ffe0fffc1fffc1f9cf3cf
  | 1 => 0xf8783ff0f07fe1ffc707f0f0fe1e1fe3eb4d33
  | 3 => 0xff803fff007ffe1ff807ff00ffe01ffc738e3c
  | 4 => 0x3fffff80001ffff80000ffffe0007c0fc0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80000100000020000008011000220400001045
  | 1 => 0x1212522244a90309434290a252144943294512
  | 3 => 0x2124a4442952103298852a04a5409298528a28
  | 4 => 0x7557388aac1b555cedd18888f999c0c97c0f80
  | 5 => 0x466630ecce63999f36e7ccce311103127fe000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88eeaaeeaaeeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_26530
namespace PEqualNP.Outside.L_meta_26530
open PEqualNP.Outside.L_meta_26530.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1c032840802d8602844480000020bf43bd43bf42bd42bf41bd41df31f631dd31f531d531be40bc40
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x102180050112f5000c338275b43600828ea9e853551d0aaaa718e5d0531caa0a6397434c72a8698e595131caaa26397424c72a8498e54c6408ea98812d521026aa220654c440
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x30500a158a544c61565d0931855953110305524c440
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
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
  | 4 => packedAt s3K4 (228+((h/4+packedAt s3K4 (208+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s3K3 (457+((h/5+packedAt s3K3 (432+(h % 5)*5) 5) % 20)*5) 5
  | 2 => packedAt s3K2 (155+((h/1+packedAt s3K2 (152+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffc7fff8787ff0ff0c3fe1ffe1c3ff0f8cf1cf
  | 1 => 0x87f8f0ff8070ff1ff0387e3c3e03c7f3cb4933
  | 2 => 0x7ff00ffff80ffe1ffc07fc03ffc07fc738e3c
  | 4 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x80400008008001000000804400404100001045
  | 1 => 0x3492299115296831321c3228b20a9263494912
  | 2 => 0x41004222200280024440448104900488128228
  | 4 => 0x1434acc454482a559aad1022392b30216c0d80
  | 5 => 0x6626c887666ccc99ef367933903220ca7fe000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xfafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8fafaeaeafafae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_26530
namespace PEqualNP.Outside.L_meta_26530
open PEqualNP.Outside.L_meta_26530.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x40014e3584046180a424018043bf43bd43bf42bd42df32ee32dd32ed32cd32bf41bd41be40bc40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x354311805001c8005877812b00000010700000a6a9c658f424cb1a849963d0d32c6a1a658e544cb1aa8994754f4196a96838d32d071a64a0e34ca408ea98812d521031a64204d54440
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x400d00a1586544ca0d654cb418359532103053254440
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
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
  | 4 => packedAt s4K4 (228+((h/4+packedAt s4K4 (208+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s4K3 (457+((h/5+packedAt s4K3 (432+(h % 5)*5) 5) % 26)*5) 5
  | 2 => packedAt s4K2 (155+((h/1+packedAt s4K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 2 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 3 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 2 => 0x55112aa222aaa88356445541354094ac628c28
  | 3 => 0x14354cc44a882aa59b5511023992b024740e80
  | 5 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_26530
namespace PEqualNP.Outside.L_meta_26530
open PEqualNP.Outside.L_meta_26530.Model
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
end PEqualNP.Outside.L_meta_26530
namespace PEqualNP.Outside.L_meta_26530
open PEqualNP.Outside.L_meta_26530.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x3a205c0014848c0076000000328e000c6e72561262409028665a740268003000427e4a502a4e1c000016640e0010003e782c066c8800220038000000005e00000086000092008a180060703448584600000000000a26002e804c52000800000000007c000000540082446a361e04243c1a007a00040c1020e00284040800110000880010000001808002ffd500b7f54027f9500bfd54005f55009fc5402ffd4c0b7f5301ff94c0bfd53005f54c07fc53027fd0c07fe43007f50c07fc4302ffd480b7f52017f9480bfd52005f54805fc52027fd0805fe42007f50805fc4201ffcc801df32017f8c801fd3200774c805fc3202ffd440b7f5100ff9440bfd51005f54403fc51027fd0401bf4100ff90401fd41006f50403fc4101ffcc403fe31007f4c403fc31017fc8403fe21007f48403fc2102ffd400bfe50005f9400bfd5002ff1400b7c50027fd0001fe40007f50009fc4001ffcc001fe30007f4c007fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x9a6003f790d30007ba8698002ff624c0057f3126002bf1893005efea4980037d524c007ef9926000f74c930005fec298006fe614c0037e30a600bdfd4530006faa298003bf414c001dea0a6003f7cc530007ba629800eff604c001bf282600bdf1413001ff66098003de304c007ee1826003fe0c130055fecb1001f7f65880013fb2c4005bf99620055facb10016fc658800fbe32c40059f19620005fec910012fe64880017eb244004bf19220056fea9100037d54880017fb1c4003bf98e20005fac71000efc6388015bfa9c4000df54e20015fac51000b7f5288005bea944002f7cca20017ba6510006fe61880017eb0c4001bf18620056fea3100037d5188001dfa0c4000ef50620015fcc11001f7e508800fbe2844000fe90220007f2811000bef2088005fd9044002fe0822004dfeca900037f65480013fb2a4005bf9952004dfaca90016fc6548013be32a40059f19520005fec890003bf64480015fb224004bf99120005fac890012fc6448001de3224004af1912004efea8900037d54480017fb1a4003bf98d20005fac69000efc6348013bfa9a4000df54d20015fec49000b7f5248005f72924002df5492004fdaa4900036d5248005f72124000fb50920017be649000bee3248005ee9924000fb4c9200079a6490002ff61480037f30a4001bf1852004efea2900037d5148001dfa0a4000ef50520017de4290003ed21480057fb024000df9412004ef8a090003fa4048001fca024002fec8120007dc409000bec2048005fc1024008bfd961003efecb080027f658400b7f32c2008bf5961002df8cb0801f7c658400b3e32c2000bfd9210025fcc908002fd64840097e3242008dfd5210006faa908002ff63840077f31c2000bf58e1001df8c7080237f5384001bea9c2000bfd8a10015fcc508002fd62840057e3142008dfd4a10006faa508003df3284001ee9942001bf5861000efea3080077d5184003dfa0c2001ef5061000dfcc10801f7e508400fbe2842000fe8c210007f26108003fa2084001fc9042001fdc421000ff62108007f8108400d7fb2a2000dfd9510004feca88016fe654400d7eb2a2005bf19510036f8ca880167c65440017fb222004bf99110005fac888012fc644400dbfaa22000df55110005fec688003df63440016fb1a2003bf98d10005fac68800efc6344001ee31a2003b718d10036fea6880037d53440017fb122002bf98910005fac48800afc624400dbfa922000df54910007be6488003dd32440037fb0a2001dfd451000feca2880077d514400dfaa8a2000dd5451000f7e8288007f64144003dea0a2000fd505100076a8288007f63144001fa98a2001fd88510007ea4288006ff6044001bf2822006df14110007f46088003f93044001fd1022000fe4811000ff62088003f61044003fa0822001fe04110
  | 1 => 0xbdf3248405f71924202f74c921007da6490803cd32484037fb0a4201dfd452100efaa290807bf4148403fb20a4201ef50521007ea8290803b54148405fb90a4201fb8852100fd84290807f421484017fb024200bf181210aef8a09080bef2048403fb8824207dfd92500a6fcc9280037d64940013eb24a007df1925003efec72804f7e6394001beb1ca0009f58e5003ef8c7280537f4394027bf21ca000df50e5009ef8872801f7f6294025bf314a000df58a50004fac52801f7c6294029bfa14a012df90a50006fa852804b7c4294027bf994a000d7cca50096fc65280037d3294001ae994a012df0ca5003efec3280477e6194001beb0ca0009f5865003ef8c3280537f41940019fa0ca011df90650006fa83280033d4194023be20ca013dfcc65008efc63280037d3194023be18ca012dfc865008efc43280037d2194023be10ca007df9825002cfcc1280177a6094029bfa04a007df1025009efe612801f7c3094025bf904a007df0825008efe212801f7c109401f7fb2c8007dfd9640004fecb20016fe659001f7eb2c8005bf1964003ef8cb200167c65900097eb248004dfd5240026faa92000efe63900017eb1c8003bf18e4007efea7200037d53900057f3148000bf58a40015f8c52003f7f5290001bea948010ef90a40027788520003df3290001ee9948001bf98640005fac320006fc619001fbfa8c8000df546400277e8320003bd41900097f3048007df9424003ef8a120013bf4090009fda048004fe10240075fecaa00037f65500013fb2a8005bf99540075facaa0016fc655001dbe32a80059f19540025fec8a00137f5450009df2a28004df551400777aa8a00033d54500017fb1a8003bf98d4001df8c6a003b7f5350001bea9a8004efd0d400077a86a0002ff62500057f3128002bf18940076fea4a00037d5250009dfa128000ef50940007be64a0003dd32500017fb0a8001bf9854000df8c2a003b7f5150001bea8a8004efd05400077a82a0012ff6050001bf282800edf14140027f680a0003be4050009de2028004fe1014006dfecb1801f7f658c0013fb2c6005bf9963006dfacb18016fc658c00fbe32c60059f19630005fec918012fe648c0017eb246004bf1923006efea9180037d548c0077eb1c6003dfd4e3001efaa71800afe628c0017eb146002bf18a3006efea5180037d528c007ef9946000f74ca3000dfcc318002fd618c0037e30c600ddfd4630006faa318003bf418c001dea0c600cf78c63001fb8631800efe608c00fbf2846007df1423001fbe611800ffb308c007fc184600bbfd9530006feca980027f654c00b7f32a600bbf5953002df8ca9802f7c654c00b3e32a6000bfd9130025fcc898002fd644c0097e322600bdfd5130006faa89800eff634c007bfa9a6003f794d3001efaa69802fdd534c001aea
  | 2 => 0x4102778c5a0873bf52d04399fa96821aef94b410e77aa5a08033d52d0435de296821befccb410073e65a086bbe32d0401de9968200e74cb410d77865a0806bd61d0403dfa8e8201cfd474100f7ca3a0807bd51d04039ea8e8201ef1474100f7e63a0807be31d0403de18e8201efc874100f7c43a0807bc21d0409dfb068204ef983410277ac1a0813bc60d0439dfa86821cef943410e77aa1a0873bc50d04399e286821befcc3410df7861a086bbf20d0435de1068201efc434100f7821a0866ff655040b7f32a8219df9954102cfccaa0866fd6550401beb2a82009f5954102df8caa0806ff6450409bfaa28219efd51410ce7ea8a0813be5450409beaa28219ef551410067aa8a0813bc54504017fb1a8203bf98d4101df8c6a08677f5350401bea9a8204efd0d410c77c86a0803bd4350409de21a8200bfd8941015fcc4a080afc6250433bfa928200df549410277e84a085fbe4250401dea128204ef10941007be64a0803dd32504037fb0a8201dfd454100efaa2a0813f74150403df20a8201ef1054100fe882a0863f73150403fa18a8201fd88541005fec0a0802fc6050433be2828204efd01410277880a0807f71050433dfb2a8219ef995410ce7ccaa0867bd65504019eb2a8219ef195410077ec6a0863be6350401deb1a8218ef18d410cf7ea6a08673f5350431df29a8219ef54d410067aa6a0863bc5350401dfb128217ef989410077ac4a085fbc6250433dfa928219cfd49410bf7ca4a0867bd52504019ea928217ef149410c77e64a08039f325042fdf1928200ef4c9410073a64a085fbc3250403dfb0a8201afd85410276ec2a0807bf51504039fa8a8201ef9454100f7aa2a08073d5150403de28a8201efcc5410c76e62a0807be3150403de18a8201ed0c54100f7e42a0807be2150403db10a8201ef085410077ec0a0803be6050401deb028200ef181410cf7ea0a0867be5050433dea828219ef141410ce78a0a0863bf3050431de1828217efc81410bf7840a0807bf1050403db8828201ef041410b5feca98816fe654c42dbf32a62059f995310b5faca988037d654c4013eb2a6205bf19531005fec898812fe644c4017eb226204bf191310b6fea8988037d544c4037fb1a6203dfd4d3101efaa698802ff624c4057f3126202bf189310b6fea4988037d524c407ef9926200f74c93100dfec2988077f514c403bea8a6201efd053100f7a829880ff7314c403ef18a6201f70c53100fe86298802ff604c4017e3026216df1413101fbe6098807f7104c42b7fb2a4205bf995210aefcca908167e654842b7eb2a4200df59521004faca90816fc65484017fb224204bf99121005fac890812fc644842bbfaa24200df55121005fec69080efe63484017eb1a4203bf18d210aefea6908037d53484037fb124202dfd4921016faa49080
  | 3 => 0xf2166402f750b32017b8859900fdf61cc807ef30e6403f75873201fb8c399097df51cc84bafa8e6423f79473212fbaa39908fdc51cc849efa0e6423f79073211fb8839900bdf21cc805ef10e6402f70873201fbec19900fde60cc807eeb066403f71833212fbea199097de50cc84beea866425f71433212eb8a199093df40cc849ee2066402f7c8332017b8419908fdf10cc847ee0866422bfd953202dfcca9908b7e654c80b3f32a6422bf59532006faca990027d654c80b7e32a6400bfd9132025fcc899002fd644c8097e3226422dfd5132006faa89900aff634c807bfa9a6422f7d4d32116bea69900fde534c807bea9a6422f754d32006baa69900fdc534c843efa1a6403f790d32007ba869900fdc434c8057fb126402dfd4932016faa499087ef424c805f62126403fbcc932017bc649900bdc324c805f61926400bfd853200dfcc299006fc614c845bfa8a6403f7cc532107bc629900fdc314c805f790a6400bfd8132005f8c09908b7c504c807ef9826403f70c132017de409908bdf654c845ef32a6422d799532117baca990035d654c845ee32a6400f7d913210fbcc899003dd644c843ee3226422f7d5132116bea899087de544c845eeaa26400d75513210fb8a89900bdf624c8056fb126403f3d8932017bea49900b5f524c805ef2926402f754932016baa49900bdc524c805efa126421f3d0932017bc849900bdd424c805ee2126402f310932007bec299083de614c801eeb0a6420f718532117bea29908b5f514c841ef28a6422f754532107b8a299087df414c841ef20a6420f710532017be429900bcf214c805ef10a6402f708532007bec099003de604c801eeb026400f718132117bea09908bde504c845eea826422f714132116b8a099087df404c843ee2026402f7c81320179e409900bdc204c841ef8826420f704132006fec8a88027f645443fbf322a200df591510fef8c8a88037f63544013fb1aa21edf98d51006fac6a887b7c635443fbfa1aa21edf90d51006fa86a887b7c4354401bfb12a2009fd89510eefcc4a88037d625443bbe312a21fdfd09510eefc84a88037d425443bbe212a21edfcc951006be64a88777e3254401be992a200d74c9510eef864a88077f61544033fb0aa205ddd855100efe82a88077e4154403be20aa201dfcc55100efc62a88077c3154403bf90aa201df8855100ef842a88037f6054401bf302a200df58151006f8c0a88027c605443fbfa02a21fdf101510f6fe60a887b7c305443bbf902a21ddf0815100efe20a8807771054403be082a204efd97410277ccba08133e65d0409deb2e8204cf5974102778cba0813bf63d0409df31e8204e798f410277ac7a08139d63d0409de31e821cefd4f410e67ea7a086fbe53d0439dea9e8200cf54f410df78a7a0813bf62d0409df3168204ef58b
  | 4 => 0x137c4155065bf98aa830df8c554186f862aa0c77f2155061bf10aa830df08554006fec0aa0037e6055001beb02a800df18154004f8c0aa0137f40550099fa02a804df10154196fe60aa0cb7c3055063bf902a831df08154186fe20aa0c37c1055001bfb22a6009fd915317efcc8a98037d6454c5fbe322a603dfd8d5301cfec6a98175f6354c07bfa1aa603df90d5301ef886a98037f6254c013fb12a62edf98953006fac4a98bb7c6254c5fbfa12a62edf90953176f884a980f7f3254c07af992a603df8c95301ef864a98037f6154c013fb0aa62ddf98553006fac2a98b77c6154c5fbfa0aa62ddf9055316ef882a980f7f3154c07bf18aa62dd78c55301ef862a980f5c3154c5dbf90aa62ddf8855316ef842a98037f6054c01bf302a600df58153006f8c0a98027c6054c5fbfa02a62fdf1015301efe60a980f5f3054c07be182a62edfc8153176f840a98b77f1054c5bbe082a62abfd954302dfccaa18ab7e6550c0b3f32a862abf59543006facaa18027d6550c0b7e32a8603bfd9143026fea8a18137d5450c077fb1a8603dfd4d4301efaa6a1813df4350c07df21a8603ef10d4301fb886a1802ff6250c057f3128602bf18943156fea4a18b3be4250c09de2128603f7cc943005fec2a1806fe6150c037e30a862adfd45430277e82a18afde3150c07ee18a8600bfd8143005f8c0a18ab7c5050c09dfa028603f7cc143006fec8a90027f6454853bf322a400df5915214ef8c8a90037f63548013fb1aa428df98d52006fac6a90a37c6354853bfa1aa428df90d52006fa86a90a37c4354805bfb12a4029fd895202edec4a900b7f4254805bf212a402df10952016fe64a900b7e3254805be192a400dfd8552004fec2a909f7e6154801beb0aa427df1855214efe82a909f7e415484fbe20aa428dfcc55213efc62a909f7c3154805bf90aa402df88552016f842a90037f6054801bf302a400df58152006f8c0a90027c6054853bfa02a429df10152146fe60a90a37c3054805bf902a402dbc8152016f840a909f7f105484fbe082a426bfd954202dfccaa109b7e655080b3f32a8426bf59542006facaa10027d655080b7e32a8402bfd9142026fea8a10137d54508017fb1a8403bf98d4201df8c6a109b7f5350801bea9a8402bfd8942016fea4a100b7d5250809f7a128402ef909420177884a100bec42508017fb0a8401bf9854200df8c2a109b7f5150809dfa0a8400bfd8142005f8c0a109b7c5050809dfa028402fbc814201fbecb9900fde65cc807af32e6403f75973201ebacb9900fdc65cc807efb266403f79933201f3cc99900fdd64cc807ceb266403f71933212fbea9990975f54cc849ef2a66425f755332006baa999093dc54cc8056eb166402f7d4b32016bea59900bde52cc805eea966402d754b32017b8a59900bdf42cc805e
  | 5 => 0x220d68527523328ac68074832e1447903040c66964500944ee71a0003ce2c003275a00080e5a68a65841ac1d64f02402f66621622080e64ac0d27828d46261805887a000049600087617684c3860a80001b85b287452434441057466083600038e11400030a00000c0006c05700c26760000008500e418283418e23800087817e7bc16662248c2e88c414a5e82d03be0b074a5044c85e64da6723c25a000000000049a2ec17c00017211c2446e04b875803c64265e8c26f80c437e8aa7306a21640002704ca0008408064380642e046e76866834a79814243685e4ec00260c59e80810c1b245424286a62005e2da0007e668c5123fa13e75614e0aa2328106d084863a3f613c3b039e67c3641088d226e1365862aa7c82fa0000001ce0005b03da7b835e6483cc00000053063085a47270416c8d03d60008e24488a04ce09a5ac00014c30c0000d000045a4e47e802257e3c873e65c7b400034e78050c2224cc52e70a0020400000100002c0980402e00409016002008018020100000001001000001800000008000050100000000d0100080a00100200c00803000008008180000300000600200816805034004000100000480003d01c054000030060041e8020000200980100c020000180020140100200001c038000280040000100200c0780601e0080200800804c008030140340080a01a0000080701e020000190160040700500e0080200300a098030020040182a80d0300441f0100000ac0b8000020680180e002004000010020000000f0120000081a0020000080c00e0000c80601400c01800000008000340000000500000000c0002500c02c000020080140000600a0080000100801c020000200140a00c0000000180201000402803000024038000000300900001e04c138120140140200108403406000002008000050100180200200001c0f00800401c00004002004010140040000981001606800004000010020030000000100200c0280280a0000040900d02402c0080100c0080380000a00c0100900c0080000e0040140000a00802c050070220380680800a0b0058000040180080901a0040081500600c0304402403c040030020900280002609c000020080000000700201001021012074020000020100000f00000c2080200a0540100600e0140082105a004048030020000300f00a03c0600101007800011008004008390020000080c00c03c018137f64550093fb22a805cfd9154006fec6aa0027f6355065bf31aa800df58d54196f8c6aa0137f4355009bf21aa804df10d54006fec4aa0027f6255063bf312a800df5895418ef8c4aa0137f4255009bf212a831cf90954026f884aa0133c4255065bf992a831df8c95418ef864aa0037f61550013fb0aa830df98554006fac2aa0c37c6155009bfa0aa804cfd0554026fc82aa
  | 6 => 0x62484086fc61a7864a605c74202c00052600000005889400075c0008865ba8804560006022200882e25667ea0000005326645605ca00a0000006365e21386820000007e00006c80001e82ac44e6de81a65009200067e1860005c41920002f00000000005a21da87c80a0c81c231c0000004d81d26a637655a1f80000000004f481607649400030206800047027a00077821453e60642000043e0000000246e80007d200000077000000000004400000000051419c1f609846443c76a6c20003b665850000069a7fe0003dc17481e0007de78a62470c2801024d60000000000006a400000050e81c1ec7061782a02363c00006fa42e7c44a264040a00000080450841a60443a7540004fa1908121fe3aa3540000000003c600064e74e00000011832444a65456a0007928c084a88c1a07f41544ea46246889c0368b41c654e4c66f600055666626c4dc06213251003e69061e1b020e0902d26ae0001462902865aa7a817006619455c48a55809e2b62a862e40e88e19e00082a8be0003e04b03a600023400057a0004f28a859a2ee6000ea8cc00063e0001e035c5b45be6aa00050a5f26a80863503100003e800001c0003ea2d60e01a42e469c2960000d40002cc00067a89200000077e2268227ae4ba05a1c425828e8ae08434049e77a2025e45280f23900a44404604fe05645e4025c06f28325c256e7080f40782fe1be3264800525167ce49c22e73c4746124e04b411a5387be7d435861431a3de82c8567ee1ba00040429a38082823e8da70201666e07a8b000008a1340000b85da68844200060e1ee24c2f80000000001040007c20005784ae20a0007325dc76c2be4321a231808223c0b22126b47ca4aa2f421686e02a14800025c2986166d81983d000014079412841c6785f458e0725bc1fa3a412089a1227e252008e3461aa6742f243036a1965066e617a1566cc6320ec2b455e47a0e88b67a687e4846560be7340001d825631649051e00039c3b800000082400000072226830876e03876627c0ae1124003425c67146522b020c06037066a08c3d81fc5024c227e36005007c55285c42c5ec4523a85d86083bc5fe4d415c7620fa6b689648270e30073648e2e651c1c80004763b46c60003522880b438c00052c1102c84c02288303f86da6d432a1e233442658a0000fc7160005d28a281484e8ba0000002600d83720000706fe58021e6be2665d048800062a3d45980000ce10a69820400012a8c85f85963ba46a35a3ae0a21243222a471e32800086222c1cc5f03ac7280000000002760000004f68ca3780e20000008d82524f889e4b216800e0008c62bc6e21f004a0001de4bc3206ca8e01e437a6f40008b857c69454023a0005948ce0000dc80c6ac4582243827721883960b62643e44a48d677689071283c21810e01e0143e247c8545
  | 7 => 0x3fc0008dc61c0000a03ec6a08728585e000000000000088868467076479a36800026224634c5544867fa0c047e0342ce8bc86c00006a5cc00087015e53a64a0000f688a0962300000000f80003f028286838804e58c00000000684273a83a1dc0003661507dc6ec16a7404a00006ee28c69e1bc1600f08665684b66448445c87e40001b44440ac02e3308260a663c0ee8827f84667501f221a6ba66c83803a2c26ea5621262ea8a433c38424e6e413a0002007882a661076039861879e11632c6bc30e25e77c0003a20000407c62c65820740006f03623c40004c412c6d228a8002ae21c40c7f262c1b60427c04fc72e49222a6921842fc33831e37c7447d62ba1d40cc4122500bc1581065a473800045c0007f047800008024a5b63d21307848203a031468a2ca3567463b22dc00020679c6860008183923f20007aa2740540008643ca5d431200000019a0004d27cc6c41e67105b841672a78c8b249825a83e02800000000000006e0004e65a86b80007d842837400006c54c1a82847b653660a0007744225ee15218a16e51851a7fc72c0000fe6dc3484a82920187180ba5fa8461d064c09c12e0467240128980007b229e6b22d804c4e27002de5ae5768022780003fe41e6b010007e36e29c0480da00042a0007200006d646c5720000007da1c036c4d04066ce53c00074c0001ae5505d60047ba7a40005fc2d40ca54654239465a0206460260000087a272633638a4e854452a59c2b84be0005f65ce56c0000002c40000000007f60007960004240008842b268e26a41887a39a8601ea0005922545de00056454a6282948e43e611e54882e21033e0de0104de78e0000006387b05900003ee0007d003027200071c41400044633a0002a21a600000075e8de0001ca0007ac00001a63418c3f453415a44c0000005ea7ec1f443430
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd645521003c7c75d8e100047f7558e1002c7c7558e1003c7e7654e1003c7c7654e1001e5e6354e100065d6354e1003c7c75d8a100047f7558a1002c7c7558a10004bf7458a10024bc7458a1003c7e7654a1003c7c7654a100166e6254a100066d6254a100065f65cca1012e5c65cca100065f654ca101165c654ca10016ce624ca10006cd624ca1000cf9768c21000759534c21000cf97688210007695248210007c9324821002c7e76d95100047d74d95100047d73d95100047d72d951003c7f71d951008c7d71d951008e3f41d951008e3d41d951003c7e70d951003c7c70d951002c7c75d91100047f755911002c7c7559110004df735911001cdc7359110004ef7259110014ec72591100047e76551100047c76551100263e64551100063d64551101965c635511002c7c75d8d100065f53d8d1001cde76d8d100065f65d8d100065c65d8d100065f75d8d100065c75d8d100065f54d8d100065d54d8d10004dd72d8d100065f52d8d100665f51d8d100665d51d8d100669f41d8d100669d41d8d100065c50d8d100047f7558d1002c7c7558d10064de7618d100065f6518d100065c6518d10005cd7218d100047e7654d100047c7654d100065f6354d1001e5c6354d1016f563154d1002c7c75d89100047f755891002c7c7558910004bf7458910024bc7458910004df735891001cdc73589100047e76549100047c76549100065f63549101465c6354910004de76cc91001cdc76cc9100065f65cc91012e5c65cc910004de764c910004dc764c9100065f654c9101165c654c910016ce624c910006cd624c91002e77765451003574765451002e74765451002c74765451000577745451000577735451000757635451000754635451000577725451000757325451000755325451000773705451003d74705451000770705451000e77605451000f736054510024f476505100057575505101a73754505100073554505100c6d46350510026b77650510026b476505101a73675505100073575505100073765505101a73465505100079763505100c6b663505100c6b463505100079463505100c69463505101a7375350510007355350510006b76250510006b562505101a7375250510007355250510007973250510007953250510007b37050510007b0705051000eb7605051000fb360505101a734505051001cf4764c51000575754c510014f47648510005757548510007c5324851019c7e76941100065f639411009e5c639411000735419411001ed8638c11000771518c110007b1418c110067d2318c11000cf8764c11000759534c11000771514c110007b1414c110007d1314c110007715188110007b1418811000cf87648110007695248110007c93248110007715148110007b14148110007e1214811000cf6768411003d777584110
  | 1 => 0x962003e7a70d962003e6f20d962003c7c75d92200047f755922002c7c755922003c7e765522003c7c76552200263e64552200063d645522003c7c75d8e200047f7558e2002c7c7558e2003c7e7654e2003c7c7654e2001e5e6354e200065d6354e200047f755862002c7c7558620004df735862001cdc735862003c7c765462000e7661546200067561546200063f65d06200e63c65d06200063f65506200ce3c655062000eb66150620006b56150620014f9769022000739545022002c7e76d95200047d74d95200047d73d952003c7f72d95200947d72d95200965f32d95200965d32d95200047d71d952002c7c75d91200063f54d9120024be76d91200063f65d91200063c65d91200063f75d91200063c75d91200063f53d91200863f52d91200863d52d91200869f32d91200869d32d9120004bd71d91200063f51d91200063c50d91200047f755912002c7c7559120084be76191200063f65191200063c6519120005b571191200047e76551200047c76551200063f64551200263c645512018f2e425512002c7c75d8d200047f7558d2002c7c7558d20004bf7458d20024bc7458d20004f77158d2000cf47158d200047e7654d200047c7654d200063f6454d2017e3c6454d2001e5e6354d200065d6354d2002e6f765492004d6c765492002e6c765492002c6c76549200056f74549200072f64549200072c64549200056f73549200056f71549200076b705492003d6c70549200076870549200166f60549200176b6054920024ec76509200056d755092001cec764c9200056d754c92010eac644c9201b74f534c9200074d534c92001ecf764c92001ecc764c9201b74e754c9200074d754c9200074f654c9201b74c654c9200078f644c92010ece644c92010ecc644c9200078c644c92010e8c644c9201b74f544c9200074d544c9201b74f514c920007cb704c920007c8704c920016cf604c920017cb604c9201b74c504c92002c7c75d8520006cd32d85200047e76545200047c76545200063f64545200fe3c64545200074d3254520004be76d0520024bc76d05200063f65d05200e63c65d05200072d52d05200078d32d0520004be7650520004bc76505200063f65505200ce3c65505200072d52505200078d325052000eb6615052000cec76485200056d7548520007a541485201ac7e76941200063f64941200a63c64941200074d3294120026b86490120007695290120087aa4290120007c93290120014f87650120007395450120007695250120007a94250120007c9325012003d6f75881200047d74d96100047d73d96100047d72d961003e7571d961008e3f41d961008e3d41d961003c7e70d961003e7a70d961003e7710d961003c7c75d92100047f755921002c7c755921003c7e765521003c7c76552100263e64552100063
  | 2 => 0x1165c654ca40016ce624ca40006cd624ca400878c424ca400047f755864002c7c7558640004df735864001cdc735864003c7c765464000e76615464000675615464000cbf76506400063f65506400ce3c655064000eb66150640006b5615064002c7e76d954003c7f74d95400a47d74d95400047d73d95400047d72d95400047d71d95400a63f41d954002e3f76551400753c765514002e3c765514002c3c76551400053f73551400053f725514018e3e625514018e3c62551400053f71551400073b705514003d3c70551400073870551400263f60551400273b605514002c7c75d8d400047e7654d400047c7654d4001cbc7650d400053d7550d4002c7c75d89400047e76549400047c7654940014bc76509400053d75509400065f65cc94012e5c65cc9400071d54cc9400065f654c9401165c654c9400071d544c940006cf624c940016cc624c94010f8f424c94002c7c75d854000cbc74d85400063d54d85400047e76545400047c765454000cbc76505400053d75505400063f65505400ce3c6550540006b761505401c47e769414003d3f75901400047d74d963003e5d73d96300047d72d963009e5f32d96300047d71d96300065e31d963009e5c31d963003c7e70d963003e7a70d963003e5f30d963003c7c75d92300047f755923002c7c755923003c7e765523003c7c76552300263e64552300063d64552300047f7558a3002c7c7558a30004bf7458a30024bc7458a3003c7c7654a300166e6254a300066d6254a30014df764ca300065f654ca301165c654ca30016ce624ca30006cd624ca300047f755863002c7c755863003c7c76546300055f735463000e7661546300067561546300063f65d06300e63c65d06300063f65506300ce3c655063000eb66150630006b5615063006794315063002c7e76d95300047d74d953003c7f73d953009c7d73d95300047d72d953009e5f32d95300047d71d953002c7c75d91300047f755913002c7c75591300047e76551300047c765513002e5f7654d3005d5c7654d3002e5c7654d3002c5c7654d300055f7454d300055f7254d300055f7154d3016e5e6154d3016e5c6154d300075b7054d3003d5c7054d30007587054d3001e5f6054d3001f5b6054d30024dc7650d300055d7550d3002c7c75d8930014dc73d89300065d53d89300047e76549300047c7654930014dc764c9300055d754c9300065f654c9301165c654c930006cf624c93002c7c75d85300047e76545300047c76545300063f65d05300e63c65d05300071d53d05300063f65505300ce3c65505300071d5350530006b7615053000eb461505300c797315053000cdc764c5300055d754c5301bc7e769413003d5f758c1300047d74d96200047d73d962003e6d72d96200965f32d96200965d32d96200047d71d962003c7e70d
  | 3 => 0x762505210bf3752505210bf3552505210bf9732505210bfa632505210bf953250521007a532505210078532505211df3450505210bfa7205052102c7e75d81210047d75d8121006cd32d8121006b541d812102c7e75181210047d7518121024be7418121004bd741812101cde7318121004dd731812103e3c64592500047f73592500a63f43592500047f72592500a63f42592500047f71592500a63f415925003c7e705925003c7c705925003e3e405925003e3c40592500047f7458e5009e5e4358e500047f7258e5009e5f3258e500047f7158e5009e5f3158e5003c7e7058e5003c7c7058e5003e5e3058e5003e5c3058e500047d7650e500063d6450e500065d6350e500053f7458a500a53c7458a500047f7458a500063f7458a500043f7458a500063c7458a500047f7358a500966e4258a500966e3258a500047f7158a500966f2158a5003c7e7058a5003c7c7058a5003e6e2058a5003e6c2058a500047d7650a500063d6450a500066d6250a5009e5e76cca5009e5d76cca5009f1e74cca5009f1d74cca500065d64cca500955d72cca500965d62cca501ae5e60cca5012f5a60cca500047d764ca500065d634ca500066d624ca500065e764ca500065d764ca500065d644ca500955f724ca5009f4f724ca500974e624ca500965d624ca500074d624ca500064d624ca501d74f424ca500974c424ca500974f214ca501ae5e604ca501175a604ca500974f204ca500055f735865009d5c73586500047f74586500047f73586500065f73586500045f73586500065c73586500047f72586500065f32586500065d325865008e76415865008e76315865008e76215865003c7e705865003c7c705865003e76105865003e7410586500a63e76d06500a63d76d06500a71e73d06500a71d73d06500063d63d06500063d62d06500071f32d06500071d32d065008d3d71d065008e3d61d065019e3e60d06500e73a60d06500047d76506500063d64506500067561506500063e76506500063d76506500063d63506500063d62506500071f32506500071d325065008d3f71506500a737715065008f36615065008e3d61506500073561506500063561506501cf37315065008f34315065008f36215065019e3e60506500cf3a605065008f3710506500047d764c6500065d634c65000675614c6500047d76486500066d62486500074d324865000675614865000735414865003e3d74d96400047d73d96400047d72d96400063e42d96400a63c42d96400047d71d96400a63f41d964003c7e70d964003e7a70d964003e3f40d96400047f7558e4002c7c7558e4003c7c7654e4001e5e6354e400065d6354e400047f7558a4002c7c7558a4003c7c7654a400053f7454a400166e6254a400066d6254a400065f65cca4012e5c65cca400065f654ca40
  | 4 => 0xc9410071d65cc9411059d72cc9410bf1f52cc9410bf1d52cc9410c79771cc94111f9471cc94111e9f61cc9411279761cc94111f1f51cc94111f1d51cc94111f9621cc9412171c50cc94111f9710cc9410cd3e754c9410053d754c94120f1f534c9410071d534c941005b7714c94100db4714c9410c797314c94110794314c94120f1e754c9410071d754c94120f1e654c9410071d654c94111d9f724c9410c78f724c9410078f624c9410bf8c624c9410bf1f524c9410bf1d524c94100797714c94110794714c9411069f614c94110f97614c9411071f514c9411071d514c9411078f214c94110796214c94120f1c504c9410bf8f204c94110797104c9410cd3e75d81410053d75d81410063d65d81410cd3c75981410053f75581410cd3c75581410063d65581410059f73581410c59c7358141005af72581410bdac72581410cd3e75181410053d75181410c59e73181410059d73181410bdae7218141005ad721814102c7f76595311fd5f73595312057771595310047f74595311fc7f73595310065f73595310047f72595310f65f325953116c7f715953100677715953116e3f415953116e3d415953116e5e315953116e5c315953103c7c70595310f65f305953116e77105953102c7e75d91310047d75d913102c7e75591310047f76551310047d765513102c7e75d89310047d75d8931024be74d8931004bd74d89310047f765493100cdc764c9311165e654c9310065d654c931006cf624c93100dd4714c93102c7e75d81310047d75d813102c7e75181310047d7518131024be7418131004bd7418131014ee7218131004ed721813102c7f76595211ed6f72595211f57771595210047f74595210047f73595211ec7f72595210066f72595210ee5f32595210ee5d325952113c7f715952100677715952113e3f415952113e3d415952103c7c70595210ee6f205952113e77105952102c7e75d91210047d75d912102c7e75591210047f76551210047d76551210063f64551210263c645512102c7e75d8d210047d75d8d2102c7e7558d210047f7654d210047d7654d210065f6354d2101e5c6354d2100cec764c9211e74f534c9210074d534c92101ecf764c92101ecc764c9211e74e754c9210074d754c9211e74e654c9210074d654c92110ece644c92110ecc644c9211e74f544c9210074d544c921007c7714c921107c4714c921016cf614c921017c7614c9211074f514c9211074d514c9211078f414c921107c6414c9211078d414c9211e74c504c921107c7104c921014f476505211df375450521007355450521007c53250521026b77650521026b476505211df3675505210073575505211df3665505210073565505210c6b663505210c6b463505211df375350521007355350521007a772505210bfa4725052100eb7625052100fa
  | 5 => 0x2471c50ccb410e53e754cb410053d754cb4123f1f534cb410071d534cb4110d9f764cb4110d9d764cb4123f1e754cb410071d754cb4110f1e654cb4110f1d654cb410df8f724cb4110f8f624cb410d78c624cb410d71f524cb410d71d524cb411071f514cb411071d514cb411078f214cb4123f1c504cb410d78f204cb4102c7f76595412253f74595412357771595412247f74595410063f74595410047f73595410047f72595410063e42595410fe3c42595411847f715954100677715954103c7c70595410fe3f405954118677105954102e3f765514102e3c76551410053f73551410053f725514118e3e625514118e3c62551410073771551411853d71551411873471551410263f615514102737615514122f3731551411873431551411873621551410053c705514118737105514102c7e75d8d410047d75d8d4100cbd74d8d41024f571d8d410047f7654d410053f7454d410065f6354d4101e5c6354d41005777154d4116f543154d4100cbc7650d410cd3e7550d410053d7550d4100db47150d4115f943150d4102c7e75d89410047d75d894100cbd74d89410047f76549410053f74549410066f62549410166c625494100cbc76509410cd3e75509410053d7550941016ac625094112e5e65cc9410065d65cc9412171f54cc9410071d54cc9411165e654c9410065d654c94120f1f544c9410071d544c941006cf624c941016cc624c94110f8f424c9410bf8c424c94102c7e75d81410047d75d81410063d54d814102c7e75181410047d751814101cde7318141004dd7318141014ee7218141004ed72181412253f76595410ce3f76595410053f73595410053f72595410063e62595410063c62595411853f71595410073771595410053771595411863f61595410ff3761595410073731595411873431595411873621595410053c70595411873710595410cd3e75d8d410053d75d8d4100db671d8d41025b571d8d410c79731d8d410cd3e7558d41005b77158d4115f943158d410053f7654d410053d7654d411fd3f7354d410cf1f7354d410071f6354d410c71c6354d410053f7254d410c71f3254d4116d3f7154d41007377154d41005377154d4116f347154d4116e3f6154d4117f376154d410c7373154d4116f1e3154d4116f1c3154d4116f343154d4116f143154d4116f362154d410053c7054d410c71f3054d4116f371054d410cd3e75d89410053d75d89410cd3e75589410beac6258941005b771589410053f76549410053d76549410053f73549411ed3f72549410cf2f72549410072f62549410bf2c625494113d3f715494113e3f615494114f37615494121f37315494113f34315494113f3621549410053c70549410bf2f205494113f3710549410c69e76cc9410c69d76cc9410c71e75cc9410c71d75cc9412171e65c
  | 6 => 0xf425513218f1e425513218f1c425513218f4c425513218f0c42551320055f715513210f1f415513218f4f21551320055c705513210f1f405513218f4f20551321155e75d85320055d75d85321155e7558532106d461585321155e75d81320055d75d81320065d65d81321155c75981320055f75581321155c75581320065d65581320059f745813210d9c7458132005d77158132105d471581321155e75181320055d751813210d9e74181320059d7418132105d67118132005d571181320fe3e64d91511847d74d91510047d73d91510047d72d915102c7d71d91512263f41d915103c7e70d91512267710d91510e57771591510047d74d8d5116c7d73d8d510f65e43d8d510047d72d8d510f65f32d8d5102c7d71d8d511fe3f41d8d511fe3d41d8d511fe5f31d8d5103c7e70d8d510f65c30d8d511fe7710d8d510f65c6358d5125d777158d510047e7650d510065f6350d510fd3e74d89510053d74d89510063e74d89510047d74d89510063d74d89510043d74d89510047d73d895113c7d72d895102c7d71d89511ee3f41d89511ee3d41d89511ee6f21d895103c7e70d89511ee7710d89512557771589510047e76509510f65e76cc9510f65d76cc9510f71e74cc9510f71d74cc9510065f64cc9511055d72cc9510ee5f62cc95111e5f61cc95112f5761cc95111f5710cc9510047e764c9510065f634c95100577714c95100d74714c9510065e764c9510065d764c9510065f644c95111d5f724c9510f74f724c9510ee5f624c95124f4f424c9510ef4c424c95100757714c95110754714c9511065f614c95111757614c9511074f214c9510ef4f204c95110757104c9510357571981510055f73581510f55c73581510457771581510fd3e74181510053d74181510f55e73181510055d73181510ed6e72181510056d721815103e3e74181510047d741815103e3d74181510043d741815103e5e73181510047d731815103e5d73181510045d731815103e6e72181510047d721815103e6d72181510046d72181510065f32181510065d321815102c7d711815103e75711815119e3f411815119e3d411815103e77101815103e7a101815119e79101815117d3f7654f4117d3d7654f411fd3f7354f410e71f7354f410df1e6354f4117f1d6354f410053f7254f410df1f3254f4116d3f7154f4116e3d6154f4116f1e3154f4116f1c3154f410053c7054f410df1f3054f4114d3f7654b4114d3d7654b410053f7354b4114f1e6354b4114f1d6354b411ed3f7254b410e72f7254b4113d3f7154b4113e3d6154b410053c7054b410d72f2054b410dd9f76ccb410de9e76ccb411259d76ccb410de9d76ccb410049d76ccb410df1e75ccb410df1d75ccb411271e65ccb411271d65ccb410d71f52ccb410d71d52ccb4111f1f51ccb4111f1d51ccb41
  | 7 => 0x855204d6d72981520053f745815214d3c74581520556f725815214d3e74181520053d74181521455e73181520055d731815213d76711815200575711815203e3e74181520047d741815203e3d74181520043d741815203e5e73181520047d731815203e5d73181520045d731815202c7d721815203e6d72181521ae5f32181521ae5d321815203e7671181520047d711815203e75711815200475711815203e6f201815203e7a20181521ae79201815202c7f76595422653f74595422856f72595422647f74595420063f74595420047f735954218c7f72595420066f725954218e3e425954218e3c42595420047f715954214e3f415954203c7c705954214e3f405954218e6f205954202c7e75d8d420047d75d8d420047f7654d4202c7e75d85420047d75d854201cde73d8542004dd73d854202c7e75d81420047d75d814202c7e75181420047d751814201cde7318142004dd731814200cf67118142004f571181421955f76553321955d76553322655f745533212f1f74553321971e64553321971d645533218d5f725533218d5d725533218e5d625533218f1e425533218f1c42553320055f71553321271f41553320055c70553321271f405533202c7f765953226d5f735953227d6f72595320047f745953226c7f73595320065f73595321747f72595320066f72595320047f71595320065e31595321465c315953203c7c70595321465f30595321766f205953202c7e75d91320047d75d9132014dd73d913201ced72d913202c7e75591320047f76551320047d76551320063f64551320263c64551320055f73551320056f725513218f2c425513202e5f7654d3202e5c7654d320055f7454d320074f7254d321755d7254d321774c7254d3201e5f6254d3201f4f6254d322774f4254d321774c4254d320055f7154d3216e5e6154d3216e5c6154d321774f2154d320055c7054d321774f2054d32014dc7650d321155e7550d320055d7550d32015cc7250d321678c4250d3202c7e75d85320047d75d8532014dd73d853202c7e75d81320047d75d81320065d53d813202c7e75181320047d7518132024be7418132004bd741813200cf67118132004f5711813226d5f76595321165f76595320055f74595321755f72595320074f72595320054f72595321765f62595321474f62595320074f42595321774c42595320055f71595320065e61595320065c61595321774f21595320055c70595321774f20595321155e75d91320055d75d9132015ce72d913201dcd72d913210f8f42d91321155e7559132005cf72591321678c42591320055f76551320055d76551322655f74551321171f74551320071f645513210f1c645513218d5f72551320074f72551320054f725513218d5d725513218f4c725513218e5f62551321974f625513210f4
  | 8 => 0x55d731815418d6e72181540056d721815418576711815400575711815402c7d741815403e3d741815403e5e73181540047d731815403e5d73181540045d731815403e6e72181540047d721815403e6d72181540046d72181540063e42181541c63c421815403e7671181540047d711815403e7571181540047571181541c63f411815403e3f401815403e7a40181541c679401815417e3e64d91531947d74d915302c7d73d915329e3f43d91530047d72d915329e5f32d91530047d71d915317e3f41d91530065e31d915329e5c31d915303c7e70d915329e5f30d91532bd5f735915317d3e74d89530053d74d895312e5f63d89530063e74d89530047d74d89530063d74d89530043d74d895312e5f73d895302c7d73d89531765f32d89531766e32d89530047d71d89530065e31d895327e5c31d895303c7e70d895327e5f30d89532b55f73589531165f635895301d5e73d855302d5d73d855316f5631d85530047d74d855302c7d73d855316e5d73d855302c5d73d85530047d72d85532065f32d855316e7641d855316e5e31d855316e7631d855316e5c31d855303c7e70d85532065f30d85532ad5f735855305d5d739815306d5f735815317d3e74181530053d74181531756e72181530056d721815316d76711815300575711815303e3e74181530047d741815303e3d74181530043d741815302c7d731815303e5d731815303e6e72181530047d721815303e6d72181530046d72181531be5f321815303e7671181530047d711815303e7571181530047571181530065e31181531be5c311815303e5f301815303e7a30181531be79301815302c7f765954329d3f74595432a55f735954329c7f74595430063f74595431947f73595430065f73595430047f72595430063e425954317e3c42595431965f32595430047f715954317e3f41595430065e31595431965c315954303c7c705954317e3f40595431965f305954302c7e75d89430047d75d894301cbd74d894302c7e75d85430047d75d8543024dd73d854302c7e75d81430047d75d814302c7e75181430047d7518143014ee7218143004ed721814300cf67118143004f5711814314e3e64d915218c7d74d91520047d73d915214e3f43d915202c7d72d91522663f42d91522665f32d91522665d32d91520047d71d915214e3f41d915203c7e70d915214e3c40d91522666f20d915214e3c64591522956f72591520047d74d8d521747d73d8d5202c7d72d8d5226e5f32d8d520047d71d8d5203c7e70d8d5226e6f20d8d5212d6f7258d520047e7650d520063f6450d521455e73d85520055d73d85520047d74d85520065e73d85520047d73d85520065d73d85520045d73d855202c7d72d85521f65f32d85521f65d32d855213e7621d855203c7e70d85521f66f20d855228d6f725
  | 9 => 0x3644211e59840ca8600600200c010020340040080200200c090000100040800101401807000000054048010080100400905a00c0302b000018030030040000281600409c1102200e00c00032000008180000300180f81602c0e00581400800c058040260000400a00c0040080100c034068000080000000b0080040080700a02c0000301002c018000040140200200c00c0c01700003005804016028010140020240200300001c0180400e0680380200e01c02808000000030030000080000d0020000180c00007c0000700400c00001000008068060300080582b00001c00004000000058000000000580300a000000000200280280800201c018090000040000600a0340300500001004802004080008280020000082300800c0000002e0000a00f0060000000f0140e4070020100100000000e004000050180000e803010038128270040040500002e000050000140280000e0080000a02000c00c0002500c014000020000040500800000c008010240140600d04800428019014070008010140000104e032014140040020140000000a0200000a0000000b0170b20280000000005000001000014018060001a40182204a0001100401600c0f80400a07001000000010040050000740400100a008000280020d8008020000000100802c0800400c00c04c0b00301a00c0200400406c000160140080500000406409004014088110220080000080101800000012002000000010060ac0002a00c01034003024038258040200000100800204c0b0470020100b000008010040030000000101e01a01c000080000040f00c0080040600000e02c1a0070040200080c0000680280c006120010220460640181a0180000580003200007806004038000050220100280a00403c0080603404800801084000000000060080000103202c000070000080480500000c058080000800000d0120080000801e0580002f00a000000000180180080000600c000080a40080200000602c000090000240180e0080000200a02c7d74d8d541965e43d8d540047d72d8d540063e42d8d542a63c42d8d541965f32d8d540047d71d8d542a63f41d8d5403c7e70d8d542a63f40d8d542d53f7458d540253e74d895402d3d74d895418f2e42d895402c7d74d895418e3d74d895402c3d74d89540047d73d895418e3e42d895418e6e42d895418e3c42d895418e6e32d89540047d71d89542863f41d895403c7e70d89542863f40d89542cd3f74589540e63f64d85541955e73d85540055d73d85540e63f74d855402c7d74d85540065e73d85540047d73d85540065d73d85540045d73d85540047d72d85540063e42d85542363c42d85541863f41d85541867641d855403c7e70d85542363f40d85542c53f74585540ce3f64585540753d749815407d3f74581541955e7318154
  | 10 => 0x287eb342da8dc1c01448f006e0008b8bec7904ba0808ca4e47f08d24b41d639294a1907168828f88d41207d42a88227b48527500004209da000926c1214098cae8000732c3400000026271443c69c96892401cbe80009d03c229878033c76c99cc2e0000e012201473863009a816be40ac00077e4c8000522000b6aa6848600000037459a7c20008da21e000000000000c3c00045e000000ac200028e00021c0007fc7ac6e2000c1c3bc3e00164480008f40000260008de0000886da00000000000000089611aa3006c6621ae47c57a7dc04038e000b8e3100000007f442ec4c4741d219a0000000e60004e66927545cc7e0508bd46788883c01301e22360003e2b1680e4765b229e0000ea94054422a0008aa0000002ce51cbf4000b4e76e540b80bf82ea0000d02340084de8666ec0007465a4a3698674202c0000006c27aa096ba0186688178c101e00006b8000ae447e0000008708ce00000023e11660e29c01a362aee00055e0005429e685a3ce8c29e45c81de000c389527a2a466a43e420c460124b1c11c978b321ec9b80008380000000004d223a8b224cc563b439e55295670e8344645369bcb24c0e5f60001666008c4bb2b408b09c6a4ab2c00033827800065e7923947bc4fe6d08cc4c49349f20004f88aca2a9c498224aac462ea4ca3e6b60008e4ad2b6c610a40210000bca70c0121b00000009920820000000000000001768087d21baa66000c182fc1928729ae62a0002326e031c5fa000000b6400028636892200017c9fea8200013e6380002e000000017236e6d86062c68923c8b76880a5a4946324f277879ebc221a554a9439016485494e22ea7a75eb20b382803ac1c68844ae58a2043267b220e4ca0f25fc75a928b142720ce3401080b82f87c4b1e23089cc50068a7e6c4a8a000352000a8ec0053058e48a0002ec64c0d80007045947682203fe13605a00035a5703ba2aa976000000132b9e6049120a80a2000a5695e0005000aab3c6a656e0005d826c5726f491600036a0008324785246fa000a763e6000b0200027c0002f63d697c4e28f64920a40f027651ec4ac2cc427dec280ca2be46800000000000022c0002544328d0aa800038262479a07abda7587fe9a09141621a6748bdc93c08c2520000001b28a23f4a542ca88c826b78588a160005ba000038694000c249f6076bc600033a4580003c4000b922e481c71e5c60007369ca812af27e667056c14883600066a41c6f600000015cbaa000a5072832ca327ce4620007f6000000000932c16470930a5c9b41f47a40504aa3a8bb074061292e642ade154962bd687418e80a07e2f2c366be224ab26f291c806b7a7cc00a6dc848b5484a4b6228a1068609c0485260e8628636c402182a495c29650e71240e89e35640052a5be3b6408a1e0ba2f0a62182c207da8e69
  | 11 => 0xb36698a725929ce2b26684a803a2928003f8af6020348184c2aafc0466e40e25e84f49aa4a05f414c6a82063f23608041f2718b6674e30a42c9fc5684c0000a522825b020257c82849c0be4389e010c1c47561c2000a0a3249882c21046d2bae12e68486e25082e4b225664029a08e5a27ee240af05e0000284000bc000009e710a6a6fc0d6a9a170000af8a3a2a671cc3a19e6824908d64f029085c82a5b600000050cc5211455c0003fc00000019c94cbea000a203cc0008bc6507fa61a8f22a282cc1eb747d8946c548641d4a5e4ec5ceb50b862de5c026e05214e7a85f8112b220000008c0942ab8414bb618a2145464a4654b9c8c66de2d847abbe71a000372334a44876be22fa850726510160c44a844282ba0aeb2a770b4a3028fa900a9200046c06407c7f87d65da38010e01e0003b89c8b56b90846102000000000a7c3f600000000000065c00016c0003b2000ae6c3ea9051a05c000bcc8e80000946f0aa60007ec7e200000044a16aa3c00000097441e3f0030410a344665b87026088b400049855641a0924b832a63c6028a446e4809504ea2c08ec03e25c00089a76a8b6000000c5a1dc3509f067e35882476200097a25e49a3ea2c4796b3a04a1fea800c261ea220ec35ea78ba67e8000774614c48afe316c5e80c4d44c2ac84ee54a73453828a4dc5acbe60181eaaca000402c2260c0001f60002e69d42bcbfe7881be6764d61268e01d024226ab18b0a48e31ab103084ac5740fc652b82b06ad47ba7f26ca0005901bc244c0cbb4446656bfc1b617a8ee8c88e200093e3ec216506ace3967226b2634802518bfa8ba67a8fc000128ac01e668e33658602800094838a53c6f824e76023839a50403c886b284825ca6e8098060b6e434bf27989b6b883b041222637c13a8606607305dc0c474c43e5b430445a70a070c4653aab034ab7073a9666ae0d24bc66c664a4258c79c83c0005801aa2c881e3420000004300005586d400e3148103da91e2d490e45c90600004e40a0002580007a63ae07898a2f4842a2677620a0eea889ea9805a0ab43e84181a888ec08b5834650a78c18c72e00056077244052c0009a8acc00000042a6ea3ee000a60a2457e744a6e8581fab46c5c4965de4b00045bc30c32016e9fa0dc000000a0497072a13c5ae0005620003d084c152404b7e000000bd200067290284e9104e80000000000007c8086000000000a6c4540005025142b014a0008fe99e1b83d22742889383fab5e000ad85f011052e0002e8000ba400000097ec0a990000aa20004f66c663a74a0003d400000000059eb0cb4233208a31827e63eb04b8ab1aae01ca1da0002085203281469ac000680000a2e73c77c5a8000a1432e1d85e2aa0b0086a33e7949f832275c5d200c648bde7e40000846e6944b3e2941803665a63700bc9bac4e04
  | 12 => 0xbe099aab69605d00589cca3823c4daaf4376ad0426958260106bc834c196b989de766a9ca648be2aeaba0001c854e9a6830c329f400000000000090a44e000066aecc140002dc150b5aa0e99600059cac69b092c53e3dcb8c22207235c4fc7003c66228945ea98ebac85681a0f6022ba26903885782642ee6449641942cc2a02461188a6904bf05660246ba898b5c0022b69083a2a0639c36c7a03a069e5968a88141e40c60f887a01034485e0549e851619896ac306aa1ac1388201f80a625a4166fe9eea4eb480a05823be37856a3068ae1a03544ce0da96e1a27be96c564696bf6a58a1aa005763d80b683a7527ca7d031e0005501e8bd04be6a284406a69a15ab449184d05e4000000666b720007ae42200090cb624c60de994436aa410a77a4e00fe37e0002d6b684a649ebbaa482ac2fe9ec73e27ac060003aa5d60000000360e4b120000001b46206a02000c067c0b038c0d40000000000000000000007826ce9a230e6d600000061624891a72c43aabe6b40004840002d00b4aaa000000784000000000862000972330b7c00003468c3127868d8134c2647205e000c04984c58a283643846b000000065a42400027087c00054cb265ec12c9a4000000000b840000000000006c02b85aa000ae2c1a26895ab9a99878a78e4880c8b601ee55abb84564440009c23a69c04a2212adc52800064a1fc840000a986582e268a512000a741000003a4000532000b0e0000007240006188680000000000005f2000000764000000a0846a000afa00066e000a9e5d40005c24d837aa18168c02706000aea0000004521f05ee0328ea8902d28a00001ceb5202e0f40fa17400060a7b6398266000818044a1ca708784cc6ee158bee0009e200012aaae9546cc3ca45092a34ea8ca9688a0000000000007c69d60006740005c40009d21cc000bc40565e6a1264e1883deadaa2c626000a026c86ac7b0abcb0809028c5fe0cc40661c7ea54848cb3062c000000ba89be5349d8b2e0006460740001560007b800000038615e720bce92014230017eb94000a0c4fa7c02b486cbbcb4c0001a4b9670883e00000058402abd806293a44c9b2ad600004c9dcaac6bc0b2
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xb51811c1534c00f0b90cbaa86980961721d53d893003c2e432ea992601ca1c8654f414c0334390ca9a8298002c5e05535053016f0a30aa6a0a600785c865d5314c0010bf06b8ecb1001e0f21d645522003c2e43ac6a9c400787487585518800146b03b2a8310062a520d61506200042fc1ae3b2a4000a2d82d53644800143b0632ec8900028760c75d912000516c10ebb224000a1d83d47644800107d0e286c8900028760c50d91200051ac08a1b224000a1d83194644800186ecab88c8900030d19571191200042ec18ecaa24000c2e421d9544800b0b90eb1aa6900b6952056354d20006163b6c8a924000c2c76191524800164b02322a4900025360f715492000594c20e0a924000b61811c1524800f0d90cbaa849001e1b219754c92003cb4402ea992404ee0c6454d32480014990cbaa649000383191754c920005a4402ea992405ca8e86d913248001c1eca322649000383194644c920005c2c08c89924000a4c865513248043c18c8aa26490003525d7704c920005c4c20e09924000bc1811c132480010bb063b2a2901278319132545200e516432a5a0a4021c8c764cb414800146b03b2a82900668b2195250520006163b2a4a0a4000c8c764c9414800f0d90cbaa42900d7139d932941201d706322652824000b2b8454a4048043d10c899480900130e1d9545012000594c2a84a024002cc8764c94048001e12a899280900020fe1172d961003c1e43ac8aa4200785c8758d538400f0d90eb12a5080029360b654ca1010d46422c4994200083f845cb654400b0790eb22a8880c68b20964551100050ec20cbb1a2000a1d841d763440014ab023aec6880028761352d8d100042f438a1b1a2000a1d84143634400149b04286c688002876106518d1000627b2ae431a2000c4c655c8634400107b083b2a688003158c47654d100041ec20eca922000a4d82d9532440071990eb126488086a3211624c9100062a3b6c6a8a2000c547618d514400168b0431aa2880024d613725451012e2a3b664a8a2000a54864c951440458a8ec992a288002d460c7054510005b0c10e0a8a2007874865d5414400f2e100baa82881178518d54505100051a432eaa0a2000e14635d5414400166100baa828816ea5a1b63505100070bb28c6a0a2000e146518d414400170b0431a82880028d21953505100c70a31aa6a0a20048b487589414403152906b12828810f8518d52505100c54a43664a0a2000a94864c94144001d0ac499282880034c5d77050510005c8c18e0a0a2000ba1821c1414400f0e90cbaa628801e1d219754851019e1b3b2832822039e146350650440016a706a8c6088063a418d418c11001e2c3b2a69822001cb0765053044001e22a6a0a6088002d4615314c110007a0992a29022000f21525052044001f0264a0a4088002d86152148110
  | 1 => 0xb0c382a4a08024760c70549410049ac08e0a928200b1781597325040126f02baa64a090f450c5754c9410058bc0aa6992822dd147154d325040161f04baa64a0802c5e05754c9410068a38aea9928200b0f825953250401c18c4b2a64a0802c5e05654c9412349bc0aebb02821983c875956050401858e4b2ac0a08020f61372595310042ec1eecaa2620085d83dd9524c40149f04b2a64988b7151c5654c93110d47426c4992620085d83dd9544840b07d0fb22a8908020f6137654d2102c2f43ec6a9a4203c4c7654d324840149f0cbaa64908a3131d9754c921005a3c0aea9924200d44715d5324847d68f02b2a649080293e19544c92110f06322a89924204c34765514148405988ec992829097fc1d51325052100782aa264a0a4200a37865d5414843f868ecbaa8290802c9e0975505211ed93c12caa0a4200a378654d4148431c28c6a9a8290806a921932505212ff83a9a64a0a4200f05534c94148431d0f0c9928290883a1219325052110f43bb264a0a4217e84764c941484bfe0d0a9928290803c161532505212ff833aa64a0a4200f05754c941484bfe0cca9928290803c159532505212ff8228264a0a4200e8532507604840183e65ba2c528003074cb7458a500041ec0ee8b14a000a35811d1629400107f08bb265280021de05764ca500050fc22ec994a000a4f825d932940014af02bb2652800293e09644ca502f707a12c8994a03ab0c845893294001c1f08b12652800383211624ca5000527c0ac4994a00085d82dcd619400183e83b9ac32800307507735865000526c10e6b0ca00085e87cc961940010bd0e992c3280020fe1d62d06500048ec3e65a0ca000e0d624cb41940010bf06bb283280021be0976506500050fc1aeca0ca000a2f825d9419400146f02bb283280028de0563506502ef0b98ac6a0ca00083f875894194001c1ac499283280e6c520d61506500070bc1ac2a0ca000e1483585419400146f04b0a832800385cc961506500070a992c2a0ca00083f845d921940010bf06bb24328003135d9324865000722992c290ca000c35765052194001c4ac4a0a4328003c14c941486500042fc1ae3b2c800785c8758d539000f0d90eb12a5200029360b654ca402f706216ca994800787487585519000146b03b2a8320062a520d61506400041fc22e5b2a800085f835c7655000107d0db92a8a00024760f715514000594c10e0aa2800783c865d5435000f0790cbaa84a00968721954cc9401150e432a89928000b0f825513250063c18c4aa264a00720f21d54d854003c1e432eaa0a800083f845cb658c00f0790eb22a91801e1b21d6254a3000526c16ca9946021a8c84589328c00f0e90eb0aa3180028d60765506302ef0a18ecaa0c600083f845cb654c0010bf06b8eca98002476137254d300042f436e2a9a6000
  | 2 => 0x47054d3227686212eaa1a6400b0e84dc9654c801a1d09b92ca99003436137259532004a6c0ee4b2a640094e87d09654c801a1ee9a12ca9908a17a1e61595320052cc00c2b2a640091d841c1654c8012ab02382ca990025360b765513200686216ecaa2640095581dd9544c80129f04bb2a8990034310976551321148f43ec8aa26431b0e84dc9544c863a1d09b92a8990c743613725513200687b26e4aa26468d0c64dc9544c80129b03b92a8991a343d07725513234687a06e4aa2640085d86dc5544c8cfa1885b8aa899002176187055132004a6c10e0aa26466d0c421c1544c8012ab02382a89913e53e0975d853227ca7c12ebb02642285c87595604c8018a8e2b2ac0991968d60674d89510060f992e9b12a200c1d325d3625443907f02ba6c4a88030dc4174d89510041ec24ec992a20587686dc5325440143b093b264a88029360a764c9510062a38aec992a200a4d82d9132544454ad0db8a64a881f0dc41741815103e1a882e8302a20085f825cc605440183e82b98c0a880307505731815103e2b882e6302a207c5a105cc605440f8aa20b98c0a88031644173181510062741ae4302a200c4d835c8605440185e82b90c0a88030b505721815103e33882e4302a207c6a105c8605440f8ca20b90c0a88031a44172181510042ec3e64302a200c1d74cc8605440189ae5990c0a88021761d32181510060eba264302a200c4d724c8605440107b0db92a7a08020f6187054f4100496c10e0a9e8200935811c153d040107b0c382a5a08024760c7054b410049ac08e0a968200c1e855db32d040183b0abb665a080307d4976ccb410060ea92ed9968200c1f515db32d040183aa2bb665a08030714176ccb4100587c12ea996820083e87909655048b62d07b8aa8a08024760c705514100496c10e0aa2820086d82dd953504c9a2863ba2a6a081617a1f6354d4122e8a18aeaa1a820085d83dd9525040b0dd0fb12a4a08c70b189755094100527c12ca9928263e0c42595325040161f04aa264a08c783189544c9410cc1f43cc4b2a8200a3980189655040162d07b8acaa080345a0f71595410068ac1ee2b2a820093582dc5655040126d0f98acaa080345dcf31595410048ec18e0b2a820092d821c1655040125b05bb2a6a08024d6077654d410068a18eeca9a8200937815d95350401a2862bb2a6a086647a1f6354d410041ec36e4a9a8262d1431dc9535045b62d07b8aa6a08b745a0f7154d4116e8ac1ee2a9a8200d1763dc553504c3a28c7b8aa6a08024d60b7154d4130e8b996e2a9a8261d1730dc5535040107b0c382a6a08024b6087054d410049ac08e0a9a8260d14311c1535048d26f02baec4a086265a0f71589410048ec1eeca92820093581dd95250401858c4bb2a4a08024de0576549410049ac0ee6a92821992e87d89525040107
  | 3 => 0x480000073cfb1dd0001e043000000304000b90980000013c1d40001895d0005a8c08004065f10100004e000000010180100400000070040000001000000280a000010000000800000000000000401008060000002c01010000080a000030000500408018020000700800004000000800c0201005000090040d00401008000040400400010000000a000010080000801024000000b0000000402000030080100403000000080a004030000001c08030040000600004004050080100003028020540300c060040100001000000040b00020000010080402c0000c03004050000800003044000040005402004040080100c00008020002d00818000380000600400004060040200526c14e7b0aa800c1f845cf615500183908b9ec2aa00217e0973d85540060e212e7b0aa800c1f415cf615500183a82b9ec2aa00307d0173d855400616212e5b0aa800c1d7390b61550010bf04b98c0aa0030710973181540060fa0ae6302a807c1f405cc605500f83a80b98c0aa0030b109721815400617c22e4302a800c2c845c8605500189d06b90c0aa0031360d721815400617a0ae4302a807c2f405c8605500f8d480b90c0aa01f0b501721815400634a02e4302a80083d87908605500183ae7210c0aa0030b5ca42181540061ba0ae2302a800c36845c4605500186b08b88c0aa0030d90971181540061a212e2302a807c37405c4605500f86a80b88c0aa0028d60674d89530060fc1ae9b12a600c1c835d36254c0183e64ba6c4a9803074c974d89530041fc0ae9b12a600c1c315d36254c0183e60ba6c4a9803150c571d89530060eba463b12a600c1f325d06054c0107f02ba0c0a9803070c5741815303e0f982e8302a607c1d305d06054c0189e64b90c0a980313a0d721815300626c1ae4302a600c4c315c86054c0f89e60b90c0a981f134c172181530062a18ae2302a600c36845c46054c0186b08b88c0a980315e0d71181530062a41ae2302a600c57325c46054c0f8ae60b88c0a981f1c8c1711815303e2a982e2302a600c71305c46054c010bb0f188c0a9803075d2311815300626b9462302a600c55718c46054cd549b0539ec2a909617e0973d85520060fa0ae7b0aa400c1d415cf615480189e40b9ec2a900307cc974181520060e992e8302a40083f815d0605480f85e40ba0c0a901f0e881741815203e16902e8302a400c39205d0605480f89e40b98c0a901f1348173181520061b422e2302a400c35845c460548018ae64b88c0a9003154c9711815203e33902e2302a407c72205c4605480f8ca40b88c0a90031c48171181520042ec1ee2b2a840083d84dd953508010bb0db8aa999002176187055332004a6c10e0aa66400955811c154cc8010eb03bb2a8990160fa1f645513234e86216e6aa2644eb0e84dc9534c80123b08382a6990025560
  | 4 => 0x761c20000009984408037025800054000b014700225c1d0d4000000000d00000000011b3a6634000553107240000002a060501fd4000002e000342000bc94a270000c91c4212460d702c0f25d8c30002ee0000480000007c8c952000000c7184370138df1661aa044000003ae000001aa00005cce0000001945407b0001c4000003be000000cd00000000024284530099a80000f45488b1ba4bc9a90213449cc38001ce4b08f8000164b80b0362bc2b8b4161044160bf0621985ed028000007481d8291221040014e00032c0d9b00085f4239a700066c1e06b0900701f1730a2000a59143763e82e800000784000003e27b44e0681e63904600001c0fc000000000001c80d00000000005000000d580000027ca20660003dc639210000001b90c00017800085000000000420c2000339c334c14c4000001e000000002dc001008000006680009e0001bc8d07d2d24f8d28873a2000fe1fb0be50cc78f40000d0130000000006f8003ea0cc39820000000000000000b40000000044ce5207346414510002ce28400000000000001723680000d1c7200000b78492aa40c49000000418ba1371f220c4c87227a164671a212a1587f165000628ed128248000000001b40a084000000020000000002bc790001664d887120396030fc9d63f400000000000000001b313a348000001882b0e40cf000328000000000005a91d00000074000128000e30ad0006b47a90a000000000001100780000000000000000000000001b70000008780000077000032000444a8800000000000000c800035000000000c10000000006c000256324b6800148654d89970f425891134164690a006e27e2a85e13a0c66f05884617c3f0768e5000434301631f600000000252000fa0932fe3083b14918a764229171cc0743695a0ea064f6000000494000000000000000004a2c0450002022e8000d7398240de80329e3e0ea800000000c6000000000000f00a01dc988c0000000e80000007a0000001b600000000000000a400733e6143499039c084ce81429a3183e116352260001f83647fc0000032c358f987f00000000000000000001e20005ac000e216c00000000000204000003c6000000000007b8ea0000006e8a300200062c0000027256409000358590471e70007ac0013b0002ec820000004484493236c6fcdaa042820d4000a30d80b8fb8a633c0005a0540000005e800000344c88003bc3c4e0000000588f79782e013c2b8003e038cf9158000000000001ec704ab0bf1c22e01c000216000af8ef28a56c9802f000134000000000007497a11e168001230e85c40012d2b8000ff1753d4000559e524c798420001fe0004d9cd35e660ca12a1b23b8699990007810302b000320ed9832d86e4000002a8478000000000188a9890003f4c9800000000000101860c0f
  | 5 => 0xa43780000011a0000000a1041c00004a238714001d80b610cc00001d6000839102a00005b800000000700000000003f153000294000233c8000000000006800015714e00
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1a12ba42409a2a74a83a4e822e5600000032020090007a0000008c006a080000924a1e00960c3400a66c0000000058b2847eae2600201600623868005000002200000e005eb8009ca000725c646e14ac000066aaa4988a947888a230001800065200800a000000004486485a367028601c540024b0b4008e4c003e049e3c2c0000107646007cb600010b020007000004000502000c05000100050000050700010403030004000200503a4b845cf61550014159110973d855400506640425cf61550014259110972d85540050a640425cb615500141591109731815400506640425cc605500142591109721815400509644845c8605500142990211721815400603211835c860550010359810971181540050c640425c4605500141691e0d74d895300503648315d36254c01419900c574d895300511648315c76254c01451900c571d895300407e61748c76254c0140d920c5741815300506640315d06054c0104d980c5721815300512640315c86054c01445920c5711815300605610835c46054c014459220d711815300514640835c46054c01c0b32481741815200710cc9205c4605480130591a1372595320054164684dc9654c80110d9810b76551320054164442dd9544c8015099010b76551320064110981dd9544c80150591109765513200542640425d9544c80110d98d9372551320060310986dc5544c80180c42618705513200641109811c1544c801451901c5764c95100704d05105cc6054401c2341441721815100407660505db32d040140d9214176ccb4100505644505db32d040130592a0f71595410054164a83dc56550401115980c77654d410054164831dd95350401905820c77654d410054464031dd95350401505920c57654d4100544640315d953504018143161b7254d410044566363dc55350401814316187054d41006410c5821c1535040142990189765494100544640715d5325040160990189654c94100550640715d53248463c0476551325052116e81219534c9414840160796615325052121e81219854c94148401607965d5325052131f011d9754c9414840160591211624ca5000581648835854194001c05764c9414865000483a5b82551325000121696e0553505300050564c655c4644800182476604645492000581644645d5324800130994201754c920004d0644805d5324800140d97194644c92000681d95811913248001a0465604644c92018f021d9544c9404800140d941957218d10006111d98218d51440016059218d7550510004c464c805d541440013219220175505100050565c6518d4144001a07656086350510006811958218d414403128498589325051010d2125d624c9414405bc107654d414c110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x30080002611c49601a40090e08a02218851878853040500500b4242306b90c0aa00300584648835c46054c01082d4884c0eecaa26400a4068042607765513200500b422130db8aa899002809a010986dc5544c801402d0884c30e0aa26400a0268042618705513200420b5221302382a899002901a0109811c1544c801082d4b0418eeca9a8200c40609900c77654d4100500b4418b0db92a6a0802811a00c586dc95350401402d1062c30e0a9a8200a04680316187054d4100420b5218b04382a6a0802901a00c5821c15350401402d38cac08c89924000a0169c656086350510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x94e
  | 7 => 0x1
  | 8 => 0x124e
  | 9 => 0x98e
  | 10 => 0x128e
  | 11 => 0x9ce
  | 12 => 0x12ca
  | 13 => 0x12ce
  | 14 => 0xa0e
  | 15 => 0x130e
  | 16 => 0x130b
  | 17 => 0x134a
  | 18 => 0x134b
  | 19 => 0x134c
  | 20 => 0x134d
  | 21 => 0xb0e
  | 22 => 0xb4e
  | 23 => 0xb8b
  | 24 => 0xb8c
  | 25 => 0xb8e
  | 26 => 0x184b
  | 27 => 0x184c
  | 28 => 0x184e
  | 29 => 0xbcb
  | 30 => 0xbcc
  | 31 => 0xbcd
  | 32 => 0xcca
  | 33 => 0xccd
  | 34 => 0xcce
  | 35 => 0x170a
  | 36 => 0x170d
  | 37 => 0x170e
  | 38 => 0xd0e
  | 39 => 0xd4a
  | 40 => 0xd4c
  | 41 => 0xd4d
  | 42 => 0xe8e
  | 43 => 0xe8a
  | 44 => 0xe8b
  | 45 => 0xeca
  | 46 => 0xecb
  | 47 => 0xecd
  | 48 => 0x104a
  | 49 => 0x104b
  | 50 => 0x104c
  | 51 => 0x14a
  | 52 => 0xb8956
  | 53 => 0x14b
  | 54 => 0xcc996
  | 55 => 0x14c
  | 56 => 0x14d
  | 57 => 0xb9354
  | 58 => 0xcd355
  | 59 => 0xb8b16
  | 60 => 0xccb16
  | 61 => 0x1a0a
  | 62 => 0x19cb
  | 63 => 0x1a4a
  | 64 => 0x19cc
  | 65 => 0xccb96
  | 66 => 0x170b96
  | 67 => 0xd4b94
  | 68 => 0x1a8a
  | 69 => 0x104b94
  | 70 => 0x19cd
  | 71 => 0xcd856
  | 72 => 0x171856
  | 73 => 0xccbd5
  | 74 => 0x154e
  | 75 => 0x16ce
  | 76 => 0x1a8b
  | 77 => 0x1a4b
  | 78 => 0xeccd5
  | 79 => 0x1a0c
  | 80 => 0x1a0d
  | 81 => 0x140e
  | 82 => 0x188e
  | 83 => 0x1a8c
  | 84 => 0x1a4d
  | 85 => 0x144e
  | 86 => 0x15ce
  | 87 => 0x18ce
  | 88 => 0x148e
  | 89 => 0x160e
  | 90 => 0x178e
  | 91 => 0xca
  | 92 => 0x10b
  | 93 => 0x134b94
  | 94 => 0x134cd5
  | 95 => 0xccb8b1e
  | 96 => 0x14b94
  | 97 => 0x19cb94
  | 98 => 0x1a0b94
  | 99 => 0xbccd5
  | 100 => 0x1a8b94
  | 101 => 0x140b96
  | 102 => 0x14cd5
  | 103 => 0x19ccd5
  | 104 => 0x1a0cd5
  | 105 => 0x1a4cd5
  | 106 => 0x154cd6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 74
  | 6 => 1139
  | 5 => 1584
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
  | 6 => packedAt gbK6 (46312+((h/379+packedAt gbK6 (42143+(h % 379)*11) 11) % 1367)*12) 12
  | 5 => packedAt gbK5 (81840+((h/528+packedAt gbK5 (76032+(h % 528)*11) 11) % 1901)*12) 12
  | 4 => packedAt gbK4 (32410+((h/173+packedAt gbK4 (30680+(h % 173)*10) 10) % 830)*11) 11
  | 3 => packedAt gbK3 (6828+((h/31+packedAt gbK3 (6580+(h % 31)*8) 8) % 136)*8) 8
  | 2 => packedAt gbK2 (1650+((h/6+packedAt gbK2 (1620+(h % 6)*5) 5) % 25)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe0fff8c183e1c0ff87f03f83f08d278474cf
  | 1 => 0xf07f0f0701fc3e00f0f87fc3fc734ada1a4b33
  | 2 => 0x7ff007fe003fff00ff8003ff8c731c638c3c
  | 3 => 0xff800007ffffc00000fffffc000f83e07c0fc0
  | 4 => 0x7ffffffffff000000000ffc007ff000
  | 5 => 0xfffffff80000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x801100000040401000900080000000801045
  | 1 => 0x10310a1200a43204a20825013061484a0a4112
  | 2 => 0x844aa0215200049200d5008a4b041314208c28
  | 3 => 0xad088045f54a800a04e64ab8090e83a0740e80
  | 4 => 0x8100886a9f3392cce000310102bec005f6000
  | 5 => 0xce7cccf03062103088440c20624fffff000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8fefaeeeafefaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_26530
namespace PEqualNP.Outside.L_meta_26530
open PEqualNP.Outside.L_meta_26530.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 17 := bs2_4_0
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
theorem bs3_4_0 : Interval s3Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 13 := bs3_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 16 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 13 := bs4_4_0
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
theorem bgb_5_1568 : Interval gbAtlas 5 1568 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1584 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))))) (concat (concat (concat (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960))) (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)))) (concat (concat (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)) (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344))) (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
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
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
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
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffeeecfffffffffefaeee8ffffffffffffeeecfefaeeeafefaeee8ffffffffffffeeecfffffffffefaeee8ffffffffffffeeecfefaeeeafefaeee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,32,160)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,32,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_26530.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.or,[6,7]⟩,⟨.and,[8,9]⟩,⟨.and,[2,5]⟩,⟨.and,[1,4]⟩,⟨.or,[0,7]⟩,⟨.or,[4,5]⟩,⟨.or,[14,6]⟩,⟨.and,[13,15]⟩,⟨.or,[10,11]⟩,⟨.or,[17,12]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_26530

open PEqualNP.Outside.L_meta_26530 in
theorem PEqualNP.Outside.L_meta_26530 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
