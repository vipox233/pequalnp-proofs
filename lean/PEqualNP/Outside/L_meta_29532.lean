import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_29532.Model
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


end PEqualNP.Outside.L_meta_29532.Model

namespace PEqualNP.Outside.L_meta_29532
open PEqualNP.Outside.L_meta_29532.Model
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

end PEqualNP.Outside.L_meta_29532

namespace PEqualNP.Outside.L_meta_29532
open PEqualNP.Outside.L_meta_29532.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x354e657212605db7287128e0aa91b6502861f34c44342e356072a4149d1e600007200906002d7b8220132204790095a59804360018000e958066000246422083a7004800706000000c4440a3204180b7290876d5210eeca221dd54443bd28087795010ebca6215754c42bb28885755110af4a0215e54042bb28e657551ccaf4a1195e542329faa2653c544caf4a1a0de54341af29c835d53906dea4a0db14941b7296636d52cc67ca918cf55231bda826378504c67ca810cf55021af298435d53086f4a010de54021bb28e817551d02dca5205b54a40afa9a815c535027ca8184f55030b7290616d520c2eca2185d54430af29e415d53c827ca9104f55220bba8a4174514827ca8084f55010af298215d53042dca4085b54810
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
  | 1 => 0x3e3c1c7f1fffe38e38e0e383f1fff83e2333f3
  | 2 => 0xc03fe07fe3e3fff03f00fc03fe383ffec43c9f
  | 3 => 0x3fff8ffc03fc7fc000fffc7fc03fc107cf1c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x44640a15141040a102860a8904c8894231131
  | 2 => 0x288891428a0640502912844122111528c42486
  | 3 => 0x9511482440c880a6400429185482a285014b18
  | 4 => 0x98018a480880c9348a46001069230309480ec0
  | 5 => 0x20221000931312493498d26200040430b6b000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xffffffc0fcccf0c0ffffffc0fcccf0c0ffffffc0fcccf0c0ffffffc0fcccf0c0ffffffc0fcccf0c0ffffffc0fcccf0c0ffffffc0fcccf0c0ffffffc0fcccf0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_29532
namespace PEqualNP.Outside.L_meta_29532
open PEqualNP.Outside.L_meta_29532.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x30007802400000460098034000002a0051d4c180005441124369c0003c08400568000000000010011080005cc801c0c0005000000000128b000060500a4000001c00000580003800000004400d005001f000000012000010004002000608000040c000ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x51575a5034325354001c00451f2005005900001e38000000254b00003b000c000400004e4152311d44070b36162e12292d193f0f023d010627234d15223a26400e3911001a182837000000002c24214933140d0a102b58084f434a4c481b0047134246302a3e033c17095535562f0508bc0071400601060800004001892a10580002049c0050410815d52d0ebca721db94843b6a9087765110eeaa221de94043bca80875e5410f3ca821f394843aea9087cd5210e9aa421f594443eaa8887da5010fb2a021d794e42aea9c859c4390abea6a15714d42af298855d5310b3886215d94442baa88857a5010af2a0215795332ae2a6655d538ca7ea8994f15132cfaa2655e544cab8a89967151328e2a265cf524cb9c84997350932af298659c43d06f4a1a0de54341af29c835d53906bea6a0d714d41ce21a833e548c67aa918d794f21aea9e437b50486f0a090cf950219eaa0435e53086baa610de94021bca80439c43d02eca3a05d54740af29c815d53902bea6a05714d40ce21a813e548c27aa9185794f20aea9e417751482e8a2904f950209eaa0415e53082baa6105d94420baa88413e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x8320b285004003a6a800000006001825a2c0029269eb8490070a1c000010d03455294443d15495110f495294043d25495010f515154043a35884390b144354442c610d5010a1e6495132c3588544cb166115132c5584544cb1a6015132c6580544cb0c549093293195424ca8d6210f41c610d50d068d6210d418719153c868d6210f40c510d51d028d6210d408719153c83615244010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x508c0001815896115132c12c4b00a89961161580544ca84b9086a8683415c84354740
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
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x878f0f1fc7ffc7e38f1c0c70fc7fc3fe3133cf
  | 2 => 0xf80ff01ff8fff8fc0fe00f80ff8ffc3ec23cf3
  | 3 => 0xfffe3ff0fff1ff0000fff1ff1ffc103cf3c
  | 4 => 0xfff00003fff0001ffffff0001ffe0001fc0fc0
  | 5 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xd0118228544488028505241424124294311145
  | 2 => 0x5222850a28901140a2248884884a828c22492
  | 3 => 0x22444401002200291000812211211101004a28
  | 4 => 0x3300669a1223924da348e0021e48198d540fc0
  | 5 => 0x4408880024cc24924c930e4c80002230abb000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xffffffa0faa0faa0ffffffa0faa0faa0ffffffa0faa0faa0ffffffa0faa0faa0ffffffa0faa0faa0ffffffa0faa0faa0ffffffa0faa0faa0ffffffa0faa0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_29532
namespace PEqualNP.Outside.L_meta_29532
open PEqualNP.Outside.L_meta_29532.Model
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
end PEqualNP.Outside.L_meta_29532
namespace PEqualNP.Outside.L_meta_29532
open PEqualNP.Outside.L_meta_29532.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15a3163c00000009a700282170a78024000c4072024c1f0000e2150446812c00000007432900480202894a994c69500360860044007000000004040300b083102043ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1500102c2d00043320004351542255144a401738260532393c00182825361c000056004845133f461d0b1e0a3a2347090c110d003000075800571a49164202002a4f350812410f3d002e37274d294b00064c312b3b00032144010e5a52003e1b2f341f24194e0000500000005359003214a010a0033c0e1400338243091c044820e000030e00217013e5390e7aa321db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010f72a021d794e42aea9c859c43ccaf4a1995e543329f2a4653d548ca7ea8994f15132ce21a653e53d067aa920d7d4d41ae29a839f5350678a6a0e714d418e29a83b7515067ca820cfd53319e2a6633e548c67aa918e710e31daa0c633f544c678a898ed505319f2a0633d540c7388618db94831b6a90637a500c6f2a018cf952219eaa4437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53902baa7206710f30b7296616d52cc27ca9184f552309faa2613c544c33886984f950209eaa0415e53082baa6105d94420baa8841e9200827ca9884f55310b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1a020b0001600078000030002600000000002e00091800050428e7024801a8a90c0888000b0401010c00f265254443c95495110f315194043ca5495010f315154043a558443ccb184354332a5584434cb0e6214d41c358853507156114d41c698053507196014d41a5584438c69463506318d195414c61d6510c31c310d520c71843540318718d54886956110f30c310d52cc2956110d30d8545200821c6355310
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8c10041445c44354332c0ac4b08a6a0e09625805350708b0ac029a83415c44354b30
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
  | 4 => packedAt s3K4 (2667+((h/30+packedAt s3K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s3K3 (998+((h/8+packedAt s3K3 (950+(h % 8)*6) 6) % 48)*6) 6
  | 2 => packedAt s3K2 (249+((h/1+packedAt s3K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x78f1ffc3f8fc7e3c71c0e3fc7e1c3fe30f70f
  | 1 => 0xf80fe1ffc7fff8fc07e00fc7f8fffc1e4339f3
  | 2 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x50118484921288014304a2094124414c305305
  | 1 => 0x2221009040401080421044208509010412052
  | 2 => 0xa5444912212900368802489092092a81828c28
  | 4 => 0x31004ca081019244d1486000e48c08c4940f80
  | 5 => 0xc6089103364e249b26938f24001033196bf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffe8e8ecece8e8ffffe8e8ecece8e8ffffe8e8ecece8e8ffffe8e8ecece8e8ffffe8e8ecece8e8ffffe8e8ecece8e8ffffe8e8ecece8e8ffffe8e8ecece8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_29532
namespace PEqualNP.Outside.L_meta_29532
open PEqualNP.Outside.L_meta_29532.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x155a70000060000956bcf860e002a33ca08a40060b93000000000580005c012841e9c40240340002400000000110b00000805274000006d500426802c0000000000070a2064a2600000001800003000000401001c0010600000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb00124967c1795c2a77000a42c1c30a08144e000005633001aca8553c800306c0418854251f8986a80240e008072e8d05c6a390240050000009a0007000007e3480060860d1c4006e1196c9e450ca04da67429448c0c030503e3e07848427800000e80021801067b000c8940032000bc0000040841d1d88840661d1944800019a0000020210de0006800581b1b00000133e8b404173811c727f0f1486e53438f0824c00000c00000044000000000ac4400164503d02800005a1889c00583d000c65f3a9cc00762e0040001270000000700070a00060d1901060b000200030104000a09000002000100000217071300080c040201002110bb28c87755190e7ca721cf54a43db28c87b55190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed94443daa8887ba5010e7aa021ee540439ca80873e53d0a7aa1a14f552429e29a85af5250a7ea0a14f950429faa6653c54ccaeca3995d547329f2a4653d548cb5a85194fd51329e2a265ad424ca7ca8194f55032bb2886575510caf4a0195e54032af29c835d53907388798cf952319eaa463b6548c76aa918dd54e31db21c63b4438c76e8518ed50a319faa2633c544c7388698edd5131da2a263d7534c7ae8698ed90d31da21a63d4434c7288698edd0931daa1263d7324c7aa6498dd944319f2a6433d54c867ca810cf55021af298435d53086f4a010de540219f29e813d52d036c63a06d4c7409eaa4813c535027ea4a06d8c540da98a81bb505027ca8204fd53309e2a6617651cc2eaa398754c7309f2a4613d548c37281184fd51309e2a261d5314c37280984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9904f952209eaa4413e544827aa8905dd4520ba28a413e540827aa8105794c20aea98417651082eaa2107a480209f2a4213d548427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x420962202bc8801eb8013380150952000002c0021e3a000001c345a446aca804c94f80502819810b581a32018a028000074e1490000403002e30000000000036000868102340020000100162c181a55865310f255294443c95495110f295294043ca9495010f295254043cc9455010f3151540438e5805350a3960153328b195424ca8d6210f31a658043cc6a56210e31ac580438c68d6210d31a6580434c69664d4d318d996434c6966390d318d994434c6a56210d31ac580434c6c56210d31b4580434c6966510d31c5994434c7866210d31a5588434c7856210d31a1588434c7926010d31a5580434c7916010d31a4580434c6946350931a5193324c694644c931e1509324c62d6214d40c514d315022d6215330c515131cc314544c5308e195404c39131501308718d54482556314520d254d20083615148020
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x900280033000000000204e0041a058a6010d31d04c4b008698e8162580434c648b80c6a1263245c064cc931908eca126498d057214d3150282b90a898e61841953150130
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
  | 4 => packedAt s4K4 (4032+((h/45+packedAt s4K4 (3672+(h % 45)*8) 8) % 180)*9) 9
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s4K2 (456+((h/3+packedAt s4K2 (441+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf1e3c7fc78ffe3f18e3838fe38ff87f10f1cf
  | 1 => 0xfe03f9ff80e3fc7e0fc03f1fc0e3f8f633933
  | 2 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 3 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x41404600421408400840908240830824105045
  | 1 => 0xa20c89489128540860a42910a424930a612912
  | 2 => 0x9110112400a0019100422409402440828228
  | 3 => 0x2404010a010004922229080032288102240d80
  | 5 => 0xc8d82250364d3924dcd273c90041066cdbf000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_29532
namespace PEqualNP.Outside.L_meta_29532
open PEqualNP.Outside.L_meta_29532.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x43e2550d34a12803c5000600851005805582300089d008120c1c9919b2c3c01714bc595521d708000169c26153920600c900014004400b5880001c0157002ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x361e00054860318024132f16800530d0c464182900000000012c66012c064004a0d814da003f8010600228dc587a421080055240fc7c5f389f10a4f3ca08866e10874b83b231888e30270409a15409f8725b14810440a138acd2000015c2e540619cfa41221001c20120702873358e80002248e05e0328834e828049d4d800341bc0000001dc4c251e9903c003d800f0760388d007200000000f2ca1c3e0028194ba001a8b4cc4c1a18ce05608984002e040581600001a80000080002363d00231300002d4a06000406063f010c1f100004120b01004b010a1102000d020100000800010100bb28c87755190e7ca3a14f543429eaa485af5250a78a2a14fd41429f2a0853e548ca7aa9194f950329eaa06576510caeaa2195e94032bca80655e53906baa720e794e41cea9c833d529067ca320cf54241af298835d53106dca420db54841bd2808379501073ca620e754c41d7290833d521075aa420cb548419f28883b65110774a020cf54041dca808339501067ca998cf55331cf2a6639d54cc73e8598e750b31cf20e639c41cc6baa718ed106319faa2633c544c7688298e7d5131ce2a2639f424c73a8498f5d4531eba0a639e414c7388298f510531ca20a635e530c67ca990cf55321d6a16433f5488678a910d794e21aea9c43d5318867ea890cf15121d6a1243d5314867ca810cf55021af298435d53086f4a010de540219ea96813e51d033e63a0674c7409eaa4813f5250278a2a067cc540ce98a81bb505027ca8204f952309eaa4613e540c27aa8185b94830b6a906176510c2eaa2184f953209eaa6413e548827aa9104f951209eaa2415f53482b8a6904f950209eaa0415e53082baa6105d94420baa8841e9200827ea9884f15310af29e215d53c43aa63884f952109eaa421b9408427ea8884f15110ea98a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2e400000a055110031588382d718147d30000c160000781805a347134490b250c3c2093600e870448a804280a2352a0caf4e69880001460810c04c00000008053138e5805150b0e5354841c354d52106956394441ca54a501071a5354041c654d501072a5254041ca549501068d6210731a658041cc6a56210631ac580418c6a56210531ac580414c6946150931a5993514c61e6590531a5986414c61e6510531a3588414c6996010531b1588414c6d16010531a5994414c7166510531e1988414c6956210531e1588414c6856210531e4980414c6956010531e4580414c69160105318e5805488714544c6218b1954248714544c521e1509314862d6214540c5145315023461551209558453483495348020d8545200822d6215310c515131c4314544c5108e19540443913150110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1002300000140100c0038100801245c06150931d02c53008298e8262580414c740b12c020a63445c0544c621a08eaa126290d05721453150282b90a898e21841953150110
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
  | 5 => packedAt s5K5 (864+((h/16+packedAt s5K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (4032+((h/45+packedAt s5K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s5K3 (1996+((h/16+packedAt s5K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s5K2 (456+((h/3+packedAt s5K2 (441+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f87e3c7c7fe3f1c71f1f82387fe3f0dc1cf
  | 1 => 0x1fc7f9fff8071fc7e07e3e3ffc070fc7327933
  | 2 => 0xe007fe03fff81ff8ff803fc03ff80ff8c38e3c
  | 3 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 4 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8280a004410a0840042050490081421404c045
  | 1 => 0x441110408090240820120210a4122482101912
  | 2 => 0x1220089120050014880248209200920430228
  | 3 => 0x4810555224840492b1548004b254a082b80d80
  | 4 => 0x91a4658037269924de6939270060c134efe000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8feecfae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_29532
namespace PEqualNP.Outside.L_meta_29532
open PEqualNP.Outside.L_meta_29532.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826004fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007ff204c003ff1026001fe8813000ff84098007ff104c003ff0826001ff04130007feca90002ff654801dff32a4006bf99520007faca90002fd654801dfe32a4006bf19520007fec890002ff644801bff3224005bf99120007fac890002fd644801bfe3224005bf19120077fea890037fe5448001feaa2400dff15120007fec690002ff6348019ff31a4004bf98d20007fac690002fd6348019fe31a4004bf18d20077fea690033fe5348001fea9a400cff14d2006ffe8690033fe4348001fea1a400cff10d2000dfec49000fff5248007ff2924003ff5492001ff8a49000fff4248007ff2124003ff5092001ff8849000fff3248007ff1924003fb8c92001ffa6490003ed3248007fe1924000ffd8520005fec29002ffe61480057f30a4000ff5852005ff8c29000afc614801dffa8a400bff94520007faa29002ffc514801bffa0a400bff90520007fa829002ffc4148019ff98a400bff8c520007fa629002ffc3148007ff90a4003fbc852001ffc429000ffd2148001f690a4003ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001fe8c12000ffa6090003f93048003fe1824001ffc812001ff64090007fe2048003f71024001ff0812000fd84090007f82048003f41024001ffc412000ffc2090007fa1048003fe0824000ffd9510005feca8802bfe654400d7f32a2000ff59510005faca8802bfc654400d7e32a2000ffd9110005fec888027fe644400b7f3222000ff59110005fac888027fc644400b7e322200affd511004ffca888003fd5444013fe2a22000ffd8d10005fec688023fe63440097f31a2000ff58d10005fac688023fc63440097e31a200affd4d10047fca688003fd5344011fe29a2009ffd0d10047fc8688003fd4344011fe21a2000ffd8910005fec48801ffe62440077f3122000ff58910005fac48801ffc62440077e312200affd491003ffca488003fd524400ffe2922009ffd091003ffc8488003fd424400ffe2122008ffcc91003ffc6488003fd324400ffe1922001bfd8510017fea28800bfe5144005fea8a2002ff14510017fe828800bfe4144005fea0a2002ff10510017fe628800bfe3144005fb18a2002ff4c510007ea628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001fe9011000ffa8088003f94044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xffe4154001fea0aa017ff105500cffe62a805ffe3154001fe98aa017ff0c5500c7fe42a805ffe2154001fe90aa017ff0855000dfec0a8007ff505400dfda82a001ff9415000efca0a8007fc5054003be282a001fe1415000ffe80a8007fe4054003fd202a001ff1015000ffe60a8007fe3054003fd182a001ff0c15000ffe40a8007fe2054003fe102a001ffc415000ffc20a8007fc1054001ffb2a8000bfd95400b7fccaa001afe6550001feb2a8000bf595400b7f8caa001afc65500037fb228005ffd51400b77ea8a0017fe545000bfeaa28005ff1514002f78a8a0003ff63500017fb1a8015ff98d40025fcc6a0003fd635002bfe31a8004bf18d400b7fea6a0057fe5350001fea9a8015ff14d4002ffe86a0017bf435000bff21a8005ff50d400077a86a0017fc4350001ffb128000bfd89400a7fcc4a000efe6250001feb128014ff1894001df8c4a005bff5250029ff2928000ff549400a7f8a4a0017ff425000bdfa128005ff9094002ffa84a0003bd425000bfe2128015ffcc9400a7fc64a0003fd3250029fe1928000ffd8540005fec2a004ffe61500057f30a8000ff5854009ff8c2a000afc615002dffa8a8013ff94540007faa2a004ffc515000bffa0a8005efd054002ffc82a0017fd4150001dea0a8005ff105400affe62a004ffe3150001fe98a8013ff0c5400a7fe42a004ffe2150001fe90a8013ff0854000dfec0a0007ff5050003ff2828001fe9414000ffaa0a0003f95050003fe2828001ffd014002ff680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ff860a0007ff2050003ff1028001ff0814000ffe20a0007fe1050003fd0828001ff04140007feca98002ff654c025ff32a6006bf99530007faca98002fd654c025fe32a6006bf19530007fec898002ff644c023ff3226005bf99130007fac898002fd644c023fe3226005bf19130097fea898047fe544c001feaa26011ff1513000dfec698013ff534c009ff29a6004ff54d30027f8a698013ff434c009ff21a6004ff50d30027f88698003ff624c0017fb126010ff9893001dfcc498003fd624c021fe3126003bf18930097fea498043fe524c001fea926010ff1493008ffe8498043fe424c001fea126010ff10930027fe6498013df324c009ff1926004ff4c930007ba6498013fc324c001ffb0a6000bfd853007ffcc29800afe614c001feb0a600fff18530015f8c29804bff514c01fff28a6000ff5453007ff8a298047ff414c01fff20a6000ff5053007ff88298013ff314c009ef98a6004ff8c530027fa6298003dd314c009fe18a6010ffc853007ffc4298003fd214c01ffe10a6001bfd813000ffea098007fe504c003fd2826001ff54130007f2a098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9
  | 2 => 0x3110ffe8498883fe424c401fea126220ff10931027fe6498813df324c409ff1926204ff4c931007ba6498813fc324c4057fb0a6202ffd4531017fca29880bf6514c405fea8a6200fd54531017f8a29880bff414c443fba0a6202ff90531017fa829880bfc414c405fa20a6202ffcc531027ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff90a6202ff88531017ec429880bfc214c401ffb026200bfd81310fffcc098806fe604c401feb02621fff1813100df8c09888bff504c43fff282621fff1413110ffe809887ffe404c43ffe2026204ffcc131027be6098813fe304c409fe1826220ffc81310fffc409887ffc204c405ff8826202fdc4131017fc209880bfc104c401ffb2a4200bfd95210f7fcca9081afe6548401feb2a4200bf595210f7f8ca9081afc6548401ffb224200bfd91210effcc890816fe6448401feb224200bf591210eff8c890816fc644843dffaa2421dff95121007faa890877fc5448401ffb1a4200bfd8d210e7fcc690812fe6348401feb1a4200bf58d210e7f8c690812fc634843dffa9a421cff94d21007faa690873fc534843bffa1a421cff90d21007fa8690873fc43484057fb124203ffd492101ffca49080ffd5248407fe2924203ffd092101ffc849080fee4248407fea124200fb5092101ff8849080fff3248407ff1924203ff4c92101ff8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017ec629080bfd3148401fa98a4202ff0c521017fe429080ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843dffa82421bff941210dff8a090877ff4048437ff202421bff101210e7fe609086ffe3048437fe1824203ffc812101fde409080ffe2048407fe1024202ffc4121017ee209080bfe1048405fe0824201bfd9550007fec8a8002ff6454035ff322a005bf99150007fac8a806bfc645400b7e322a006ffd5150037fca8a806b7e545400dfeaa2a006ff15150036f8a8a8003ff63540017fb1aa019ff98d50025fcc6a8003fd6354033fe31aa004bf18d50037fea6a801b7f535400dff29aa006ff54d50006faa6a801bfc5354035ffa1aa019ff90d50007fa86a8067fc4354001ffb12a000bfd89500c7fcc4a800efe6254001feb12a018ff1895001df8c4a801bff525400dbfa92a006ff94950037faa4a80037d525400dfe292a01affd09500c7fc84a8003fd4254031fe212a019ffcc9500c7fc64a8003fd3254031fe192a000ffd8550005fec2a805ffe61540057f30aa000ff585500bff8c2a800afc615400dffa8aa006dfd4550037fca2a801bfd5154001bea8aa006ff145500d7fe82a805
  | 3 => 0xfaa2a206dfd5151037fca8a881bfd5454401beaa2a206ff15151007fec6a8802ff6354453ff31aa204bf98d51007fac6a88a7fc63544097e31aa206ffd4d51037fca6a88a77e535440dfea9aa206ff14d51036f8a6a88abff4354453ff21aa200ff50d5114ff886a8803ff62544017fb12a228ff9895101dfcc4a8803fd6254451fe312a203bf18951037fea4a881b7f525440dff292a206ff54951006faa4a881bfc5254455ffa12a228ff90951007fa84a88a3fc4254453ff992a228ff8c951007fa64a88a3fc32544057fb0aa202ffd4551037eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405ffa0aa202ff90551017ec82a880bfc4154405ff98aa202ff8c551017ec62a880bfc3154405ff90aa202ff88551017f842a8803ff60544017fb02a227ff9815100dfcc0a8803fd605444ffe302a201bf18151037fea0a881b7f505440dff282a206ff14151157fe80a889ffe405444ffe202a229ffcc15113ffc60a889ffc3054451ff902a227ff8815113ff840a880bff1054405ff082a202ff04151007fecaa0802ff655044dff32a8206bf99541007facaa0802fd655044dfe32a8206bf19541015fec8a0817ff545040bff2a28205ff5514102ff8a8a0803ff63504017fb1a8225ff98d41025fcc6a0803fd635044bfe31a8204bf18d41137fea6a0897fe5350401fea9a8225ff14d4102ffe86a0817fe435040bfea1a8205ff10d41007fec4a0802ff6250449ff3128203bf98941007fac4a0893fc62504077e3128226ffd4941127fca4a0803fd5250449fe2928205ffd094102f7e84a0817fe425040bfea128200ef5094102ff884a0897ff3250449ff1928200ff4c941127f864a080aff6150405ffa8a8202ff94541017eca2a080bfd5150401faa8a8202ff14541017fe82a0817f74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ffcc541017fc62a080bfc3150405ff90a8202ff88541017f842a0803ff60504017fb028223ff9814100dfcc0a0803fd6050447fe3028201bf18141137fea0a088ffe5050447fe2828205ffd014102f7e80a0817fe405040bfe2028225ffcc14111ffc60a088ffc3050449ff9028223ff8814111ff840a080bff1050405ff0828202ff04141007feca98802ff654c445ff32a6206bf99531007faca98802fd654c445fe32a6206bf19531007fec898802ff644c443ff3226205bf99131007fac898802fd644c443fe3226205bf19131117fea898887fe544c401feaa26221ff15131015fec698813ff534c445efa9a6204ff94d31027faa698813fc534c409ee29a6204ffd0d31027fc8698813de434c409fea1a6200f750d31027f88698803ff624c4017fb126220ff9893101dfcc498803fd624c441fe3126203bf18931117fea498883fe524c401fea926220ff149
  | 4 => 0xffe2154807fe10aa400ffd8152005fec0a90cffe60548037f302a400ff5815219ff8c0a9006fc605480dffa82a406dfd4152037fca0a901bfc505486dffa02a433ff9015219ff880a90d7ff3054867ff182a433ff0c15201ffe40a900ffe2054807fe102a434ffc415219ffc20a90cffc1054801ffb2a8400bfd9542197fccaa101afe6550801feb2a8400bf59542197f8caa101afc65508077fb228405ffd51421977ea8a1017fe545080bfeaa28405ff1514202f78a8a1003ff63508017fb1a8431ff98d42025fcc6a1003fd6350863fe31a8404bf18d42197fea6a10c7fe5350801fea9a8431ff14d4202ffe86a1017bf435080bff21a8405ff50d420077a86a1017fc43508077fb128403ffd494201ffca4a100fee5250807fea928400fb5494201ff8a4a100fff425080bf7a128403ff9094201f7c84a100ffc4250807de2128403fb1094201ffe64a100ffe3250807fe1928400ffd8542005fec2a10c3fe61508057f30a8400ff58542187f8c2a100afc6150865ffa8a8430ff94542187f8a2a1017ff415080bdfa0a8405ff9054202ff882a10c7ff3150861ff18a8430ff0c54201ffe42a100fef2150807ff10a8403ff08542007fec0a1002ff605085fff3028401bf98142007fac0a10bffc60508037e3028432ffd414217ffca0a10bffc505080bffa028405efd014202ffc80a1017fc4050863ff982842fff8c14217ff860a100fff2050807ff1028403ff08142187fe20a10bffe105085ffe0828400ffd9532005feca990bbfe654c80d7f32a6400ff59532005faca990bbfc654c80d7e32a6400ffd9132005fec8990b7fe644c80b7f3226400ff59132005fac8990b7fc644c80b7e322642effd513216ffca899003fd544c85bfe2a26403bfd8d32027fea699013fe534c809fea9a6404ff14d32027fe8699013fe434c809fea1a6404ff10d3201dfec49900fff524c807ff2926403fb9493201ffaa499003ed524c807fe2926403ffd093201ffc849900ffd424c807fe2126403ffcc932027de649900ffe324c807ef1926403ff0c93201fb8649900fec324c801ffb0a6400bfd8532167fcc29900afe614c801feb0a642cff18532015f8c2990bbff514c859ff28a642cff1453216ffe82990b3fe414c859fe20a6404ffcc532027be6299013fe314c809fe18a6403ffc853201ffc429900ffc214c801ffb026400bfd813215ffcc099006fe604c801feb02642bff1813200df8c0990bbff504c857ff282642bff1413216ffe80990affe404c857fe2026404ffcc132027be6099013fe304c809fe1826403ffc813201fde409900ffe204c807fe102642cffc413215ffc20990affc104c8057fb2aa200ffd9151005fec8a8803bf64544015fb22a22aff9915102dfcc8a8803fd6454455fe322a205bf1915100778c8a8816bc645440df
  | 5 => 0xd53027bc86a9813fc4354c01ffb12a600bfd89531effcc4a980efe6254c01feb12a63dff1895301df8c4a981bff5254c0dbfa92a606ff94953037f8a4a98fbff4254c7bff212a63dff10953027fe64a9813fe3254c09fe192a600ffd8553005fec2a98f3fe6154c057f30aa600ff585531e7f8c2a980afc6154c0dffa8aa606ff94553037f8a2a98fbff4154c79ff20aa63cff10553027fe62a9813fe3154c09fe18aa63dffc85531e7fc42a98f3fc2154c01ffb02a600bfd81531dffcc0a9806fe6054c01feb02a63bff1815300df8c0a981bff5054c0dbfa82a606ff94153037f8a0a98fbff4054c77ff202a63bff10153027fe60a9813fe3054c09fe182a63dffc81531dffc40a98effc2054c79ff882a63bff841531dff820a9803ff6550c017fb2a8600dfd9543004fecaa18ebfe6550c0d7f32a8600ff59543005facaa18ebfc6550c0d7e32a8600df19543034f8caa1812ff6450c0bffaa28605ff9514302f7ca8a1817fd5450c01deaa28605ff15143025fec6a1813ff5350c09ff29a8604f794d43027faa6a1803dd5350c09fe29a8604ffd0d4302fbe86a1813fe4350c09df21a8604ff10d430277886a1813dc4350c01ffb128600bfd89431cffcc4a180efe6250c01feb128639ff1894301df8c4a18ebff5250c73ff2928639ff1494302ffe84a1817bf4250c0bff2128605ff10943027fe64a1813fe3250c09fe1928600ffd8543005fec2a18e3fe6150c057f30a8600ff585431c7f8c2a180afc6150c75ffa8a8638ff945431c7f8a2a1817ff4150c0bff20a8638ef9054302ff882a1817bc4150c09ff98a8604f7cc543027fc62a1813fc3150c73ff90a8638ff885431c7f842a1803ff6050c017fb028637ff9814300dfcc0a1803fd6050c6ffe3028601bf181431d7fea0a18dffe5050c6ffe2828605ffd014302f7e80a1817fe4050c0bfe2028604ffcc143027fc60a1813fc3050c73ff9028637ff881431bff840a18e3ff1050c6fff0828637ff0414301dfecaa9003ff64548017fb22a436ff9915202dfcc8a9003fd645486dfe322a405bf19152037fea8a901bfe545486dbf2a2a406ff55152037f8a8a901b7c5454801ffb1aa400bfd8d521affcc6a9012fe6354801feb1aa435ff18d52025f8c6a901bff535480dbfa9aa406ff94d52037faa6a90037d535480dfe29aa436ffd0d521affc86a9003fd435486bfe21aa403bfd895201ffea4a901bef5254807ff292a403df9495201ff8a4a900f7c5254807f6292a403ffd095201ffc84a900fee4254807fe212a403ffcc95201ffc64a900fee3254807fe192a400ffd8552005fec2a90d3fe61548057f30aa400ff585521a7f8c2a900afc615480dffa8aa406dfd4552037fca2a901bfc515486dffa0aa434ff905521a7f882a90d7ff3154869ff18aa434ff0c55201ffe42a9
  | 6 => 0x3b00c064000030120002d800022050040240020080000101600000020000008000000040000d00100c0000080400000c0d0000260000b83a0000400001704e03c068070000740400002400401815004000030060000340282e00a0480800d0000400002000400c00007052014008260000080000500a040038070000280600301a04c020000100b001020066000018000000100000000002c0180f01a004000180600100000201c004010150000040000b0060240b8010000000280409400400800000030008030000100200c000028040030140580305600e0940480000206c00808018000050290080140181f00802c0000100000402801004024000010420000200000000402007002028000030000043780100801403800000008050030000040700d0080100000200c0500282b0080140a00001401c048070180000880f00c07c030270040140880000c080090710020000d81101c03c0600000002002001002000080020020000803700600400001006004068010120080380100600c010030000a80600306a0280380200a0000100400a008030000080140000504c1b01e84700600001010002064030050000040580600200805800020010008010260480780500400001027008008048030020000500000800c00004038008000020000b000001036010000000000000101202604c21821000010020020040040b8010780000600203e000008010040040300600001c0080701e0200400204a0080000600c04c01816ff655500b7fb22a805ffd51540377ea8aa017fe545500bbf2a2a805ff1515402ef8a8aa017bc5455001ffb1aa800bfd8d54217fcc6aa012fe6355001feb1aa842ff18d54025f8c6aa01bff535500dff29aa806ff14d5402ffe86aa017bf435500bff21aa805ff10d54007fec4aa002ff6255083ff312a803bf98954007fac4aa107fc62550077e312a806ffd4954037fca4aa01bfc525500bffa12a805ff9095402ff884aa10bff3255083ff192a841ff0c954007fec2aa002ff6155081ff30aa802bf98554007fac2aa103fc61550057e30aa806ffd4554036fea2aa01bfe515500dfe28aa805ffd055402ffc82aa017fc4155085ff98aa840ff8c554207f862aa107ff2155081ff10aa840ff08554007fec0aa002ff605507fff302a801bf98154007fac0aa0fffc60550037e302a806ffd4154037fca0aa01bfc505500bffa02a805ff9015402ff880aa10bff305507fff182a83fff0c15420ffe40aa0fffe205507ffe102a840ffc41541fffc20aa0fffc10550097fb2aa600ffd9153005fec8a98fbfe6454c0b7f322a600ff591531f7f8c8a9816fc6454c0dffaa2a606ff95153037faa8a981bfc5454c097fb1aa604ffd4d53037bea6a9813fe5354c09bf29aa604ff14d53026f8a6a9813dc5354c09ffa1aa604ff9
  | 7 => 0x4ea951580dd83600823d00000000000008180027a1a3a84800000000014ac70001548002b0a20a8a9be04c00000e8399aa9dc8cd9670000e90e08001810551c5ac62bd8000391db80000013088d0fb82b1fd8bdabf8001a32638ee1b99bc00003b0002a11d3aa81901a100011926f19b84f0000139b80000001a71868e29db14d82da772761ad931a89a860ac18380011119d0000b60b795f2351b51d8264aab2369180002c19cf8d980a80000000000003c8000de0001e323e8001160000002b380007a80022b99d94e9ca2be0b5a5c2721520000000001d4a8ca4a0a320a2871880b2869aac89208b93319917299123827f9dd96ba0d824036ab4a9e93fa620001ab8000db09f0f4a559638040a6a27a5727c150a9819205a000244a701820d50000c10fa000011a7c8002b180028f9fe85d0001240000000002098cfaa48000b808e2082522800000d01bf047280ac0000299a1880000027880024b0f00002540e600009827d8151748002430d607222800000000000002791a98480000006f04f91980016c8c79710000038228d1800141000000000204924800193a650428000000dca4c1c78e198f00029d8000dea37a359189668000000000000002838000ec9481bd21129603120a83e15fa532879c9aa29158000870f88000001220858000f68000001730000001bc8db8000002a782508f13e896800095abd00025e83727e9200cb97c1228a8a32a4d8aa85a80027394f80016a00c00000000f80005da5f80024111b2178a21e22751858d30000088539c900000000019f23e2140002420002139a58528002ba9530ba14924f8001bf89107c82987e0000772c317da988682419d91511ae1e81b59f70f0821938ac493394c2250521762bb81f1f68c018a8840a514b01c0e01809620a09ea2820000000019a287487684e979a2f1cd8b382617f80009025980014705900016f19f97a2332b328884314a8002c90cb0adac38972a30000001f496d80000000000018981d90c069000225a9710a8540a59e08ed988a681560000000bf27b2b990f0660ec0dd08898e9052ae017242a2f82baaf8a70000ce8000d68e38b98010000000002c814f1d18ef2941f61a815b14c8938879c396306a9a90be06ba1001a9d30d78ff8001c18000000f608081122280000e11f02a8000729d9ab72b60500000acaa400000000017e0d4a050001642131a79ab1068129451cb86e1501e40000001e78600f200000002f2a200000027e0ca8001a51d200027789b1fb0342bc1ac25280300180201609c018020020500181a0060a00f08200a030020020020343280100402c0080200a0000000500000800800000004018130020080780000000c008080140080300800e0040081a000000010000000040000001e000008000440402080000201c06801000000008
  | 8 => 0x1a983f83a1088001ae85fac296aa272bf1108d280013980000004080001893f1608a19a40c880022615995e8aba4400003a9de2aa8572881d600f05b9361321091d795385102583ba1225b104a039270ee8af22b25a0f315ca490bd0000dc2471860001e2a0f80020417580000001d212a8c03d1369328e32c9a6590719ca69a6f80024a9a2149847a220778e504d89780019825c8001b7a320000000c39079c690e8708002ac281987a8d1ec91e8f90640000c08658ba93400000005e80000000023c1fe00000000000000014182a0000c98a38ed12799e22e18b96803784693aa97800208a5b8000000220000009961d2ac41f00048a01dc2569ba8f7a0d15880018900000000019307388d91219283ea908001e3aa88eb961140187147996a9180025480006a0001b0a0b1de8f592c1a6a6716990087c08283091d0c501229398400b0e89971b1a2c0e7a57ab78b721084b292a50a729351f79942c220605c1c11e58c1a1e9bb2b685797886128e9752632aa12c84e23a9b615d11f8ea8e7075a4c89a8c900024d1ec0000001cca96a5d0050b88029e492a1541f32b89daa618e4aa1864a6b23004ca9b1b916e00d1ce88c2511cd024abc80000000000023d8480d899e8ae0c712a8000cc9ee00024e09a0000f290419a8f700001990b20ca71ac11d8982816a092ae87b0b50c48001af0961720b48e986883800000012e0a601e85619507d0a8221a119c212b000258a710c604b89994217380029c89520308a0001df00000000011a000010202a76a75894a3892ba0b92eab21d59311629bd9ef9c305c951970a4992096193780017689b800207a3f8000619b1000023058a3f20000028b2362a3a34a170762b424f1c09801f89ee87bacb11ba1603002910e2022ab8402072391cc1989281441559eba438b927f07d815a8289c83d8020b21fc04d0fe9740531141261fa10d1c50cc07f95d8a416e9b49f82018f508c9a19289a00178c31178da87821ba4026613b8bba0126c18e1ed94e134a1d2af0d3a2da45179253991a1b2b290b8711afa8f1ba17f07309182ea40a4b92518328114b8e409e164a2a16f86b29a22883185983508380d8c283388910f86c9d0968a460880558130f118b0161ad17b810893109838942a5a81fa47a0c2b00d71f0854a9f2679001651d500023a1b2aad92186d1571211d42a906e88b2ca10a1bb8b1a4680926a05f0e59082c51be87a04a0801692a58348df11c033051a1e10114d2a6021138194826a481d70bb145a552859660002c080b8002b900000002c02d0aa25908faa98909591f218c84500623984214a0d90fc29ba1f0c205e26d92f0d080c8068fb2a70791a8a151701dd2148b002381a26e27499b0b318a0efa8da5d9b692d18d0071b8a9a93e1030001f40000fd00013b0000002891b407012d8002
  | 9 => 0x2a5116a0f06d8aea62a64113a2483212906323c9fa8d58001231ce0000001e9a7911c9b38000d2000045820000000000000000000000165ac5a3381e03f0058faa0e1239aa12980000025800029100013d00010ca372608668ad0001ff00018d800167a9c00025f0002198000a79cf2a682f80000002880021900002726b8e813591d9c80411771c01c42291301e609fab58f39c480026eaa01ef0001eb2008582920798ca2741a48000182840079ca8ea101a94a3b28ba90112a1da8a0990a915b8509999e11da0a28c80001c8a9e1550000820940499f9a798ff137171981aa09cb2850b6914a2ca2e8df8002c69e92600f99c609d0000000cd09d8609fb80a1ff95a2868440639780898bc843948ab129d0b416b0001448bea0e9959b20001150000e686f8a480000003c0001268d80000928002308da1b700026a86c1e505680009e9f92990d40f801400011313c00010d9e71578000ab27a8670000831d02c8a691fca311569ea96c2be93903282087f02e0850f421822995e1f515281922d0488a98c69978ce29f8989f58861602caa689c70e215c1f125e2932500359d6a7b91024584182c84a9f18c5a70ac787e9a605b1059e180020597ca732ad0000b11430eb24897b0848cf0bc1e89171df8098811029022269aca2a8448fe06212f8718a114618f93d878a6d1f297e94091e22326c8742bb251a069fd2ba21cab517a99c10616d00000018c07527d21f84921c0e12611ed08a9852668af88e93a0f1903977a20000065223a3b80000028e21695a9b02341118d101c99a0fc80000000008681b8000bfa241e6a959f393ca83067ab8143a159d10002781b321a0b08c404622121a8fd94682806289c1a09c2a3199092581b25617d1e
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf71d8910014fe71d891000cfd71d8910014fc71d8910246f631d8910246ef21d8910246ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910236ef20d8910236ed20d891001cff765891003eec625891022df7715891023dfb7058910004ff7558910034fe7558910034fc7558910004ff745891002cfe745891002cfc7458910004ff7358910024fe7358910024fc7358910234ff7258910006ef725891022cff7158910006f7715891005ef631589100dcff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc76549100367e65549100067d6554910006ef625491001eec6254910004ff7650910004fe7650910004fd7650910004fc765091002ebe6450910006bd645091000dfa7050910004ff764c910004fe764c910004fd764c910004fc764c910026de634c910006dd634c910015f6714c91000df4764c510026f4764c51000cf4764c510006f7654c510006f5654c51010ef6644c51010ef4644c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510227d7534c510047d4534c510047d6434c510007d5434c510005f7724c510006f7624c510006f5624c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100fff0704c510016f7604c510017f3604c5100fff2404c5100ffd7304c5100ffd5304c5100fff2204c51000df4764851001ef4764851000cf47648510005f77348510005f57348510006f76348510006f56348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851003fe64248510007e54248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100dff240485100dfe720485100dff220485100dfe52048510015f8765011002ef87650110014f87650110006fb6550110006f9655011000dfb745011000fbb7450110007bb645011002efa645011002ef8645011004fb8645011021fbb545011004fb8545011004fbb4350110007b94350110005fb725011004fbb4250110007b94250110007f37150110015fa7150110015f8715011009ff0715011000efb615011000ff3615011009fbb415011009fb9415011009ff23150110007f1315011009ff22150110007f12150110015f8764811001ef87648110014f87648110005fb7448110005f97448110006fb6348110006f9634811000dfb724811000feb7248110007eb624811001efa624811001ef8624811003fe8624811001ee8624811003fea3248110007e93248110007f37148110015fa7148110015f8714811005ff0714811000efb614811000ff3614811005ff23148110007f1314811005feb214811005ff2214811005fe9214811003ff12148110007e12148110
  | 1 => 0x95102a67f51d95102a67d51d95102a6f631d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102967f50d95102967d50d9510296fa40d9510034ff76595100567c6559510005bf745951004dbc745951028df7715951029dfb7059510294ff75595100067f7559510004ff7459510006bf7459510004bf745951002cfe745951002cfc7459510006bc745951002cbc7459510004ff7359510024fe7359510024fc7359510004ff725951001cfe725951001cfc72595100567f525951028cff7159510006f771595100bef6315951013cff7059510006fb705951013efa405951002cfe76d911004ebe64d9110034fe75d9110004fd75d9110034fc75d911011cfd74d9110006bf54d911004ebc54d9110024fe73d9110004fd73d9110024fc73d911004ebf43d911001cfe72d9110004fd72d911001cfc72d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110286bf41d9110286bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110276bf40d9110276bd40d911002cff765911004ebc645911026df7715911027dfb7059110004ff7559110034fe7559110034fc7559110274ff7459110006bf7459110004ff7359110024fe7359110024fc7359110004ff725911001cfe725911001cfc725911004ebf425911026cff7159110006f7715911011cff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc7655110024fe76d8d10046de63d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d1001cfe72d8d10004fd72d8d1001cfc72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10266df31d8d10266dd31d8d10266f621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10256df30d8d10256dd30d8d10256fa20d8d10024ff7658d10046dc6358d10005ef7258d1003dec7258d1024df77158d1025dfb7058d10004ff7558d10034fe7558d10034fc7558d10004ff7458d1002cfe7458d1002cfc7458d10254ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1001cfe7258d1001cfc7258d10006ec7258d1001cec7258d10046df3258d1024cff7158d10006f77158d1007ef62158d100fcff7058d10006fb7058d100fefa2058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100557c7550d10006bf6450d1002ebc6450d1001cfe76d891003eee62d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d891003eee52d8910006ef32d891003eec32d891000cf
  | 2 => 0x2bcff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d20066df3158d2015cff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200367e6554d200067d6554d201dfe82054d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200757c7550d2002ebe6450d20006bd6450d20006df6350d20026dc6350d201bfe82050d2000dec764c920026ec764c92000cec764c920006ef654c920006ed654c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c920005ef714c920067cf314c920007eb704c92000dee704c92000dec704c92015fe8704c92000de8704c92001eef604c92001feb604c92015fcf304c92015fea304c92015fcd304c92015fea104c920014fe76d852005ef661d852022fe820d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d852005ef651d8520006f741d852005ef441d852005ef621d85202b6f521d852000cfe70d852001cfd70d852000cfc70d852022ef710d852005ef461585202adfb70585200dfe82058520004ff7654520004fe7654520004fc76545200367e65545200067d6554520005bf745452006dbc7454520006f76154520016f4615452013fe82054520004ff7650520004fe7650520004fc765052002ebe6450520006bd645052011fe82050520004ff764c520004fe764c520004fc764c520026de634c520006dd634c52001dee724c520007cd324c520016f6614c52000dfa704c5200ffe8204c52000dec7648520016ec764852000cec7648520006ef6448520006ed6448520005ef7348520005ed734852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005fe63148520007e53148520007eb704852000dee704852000dec70485200dfe8704852000de8704852001eef604852001feb60485200dfea30485200dfe710485200dfea104852001df8764c120026f8764c12001cf8764c120006fb654c120006f9654c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120067d8634c120007eb724c12001dfa724c12001df8724c120087e8724c12001de8724c12000efb624c12000feb624c120087db324c120087ea324c120087d9324c120067e9324c120007c9324c120005fb714c120067db314c120007d9314c120087eb214c120007e9214c120034fe76d95100567e65d951013cfd75d951002cfe74d9510004fd74d951002cfc74d9510024fe73d9510004fd73d9510024fc73d951001cfe72d9510004fd72d951001cfc72d951000cff71d9510014fe71d951000cfd71d9510014fc71d
  | 3 => 0x93154130034fe76d95200767e65d952006dbe74d9520005bd74d9520307e820d952019cfd75d952002cfe74d9520006be74d952002cbe74d9520004fd74d9520006bd74d9520004bd74d952002cfc74d9520024fe73d9520004fd73d9520024fc73d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203167f52d95203167d52d9520316ee32d9520014fe71d9520004fd71d9520014fc71d952001cff70d952001cfd70d95203067f50d95203067d50d9520306fa30d9520034ff76595200767c6559520005df7359520065dc73595202fdef725952030dfb705952019fe82059520304ff75595200067f7559520004ff745952002cfe745952002cfc74595200067e54595200767c5459520004ff7359520006df7359520004df7359520024fe7359520024fc7359520006dc7359520024dc73595200767f53595202fcff7259520006ef72595200c6ee3259520004ff7159520014fe7159520014fc71595200767f515952019cff7059520006fb705952019efa305952002cfe76d91200757e75d91200057d75d912006ebe64d91202e7e820d9120034fe75d91200067e75d91200347e75d9120004fd75d91200067d75d91200047d75d9120034fc75d912017cfd74d9120024fe73d9120004fd73d9120024fc73d912000cff72d912001cfe72d912000cfd72d912001cfc72d91202f6bf42d91202f6bd42d9120014fe71d9120004fd71d9120014fc71d91202f6ef21d912001cff70d912001cfd70d91202e6bf40d91202e6bd40d91202e6fa10d912002cff765912006ebc64591202ddef7259120005f7715912005df471591202edfb705912017fe82059120004ff7559120034fe7559120034fc75591202e4ff7459120006bf7459120006bf545912006ebc5459120004ff7359120024fe7359120024fc735912006ebf43591202dcff7259120006ef7259120004ff7159120006f77159120004f77159120014fe7159120014fc7159120006f47159120014f4715912006ebf41591200a6ef215912017cff7059120006fb705912017efa1059120004ff7655120004fe7655120004fd7655120004fc76551201ffe82055120024fe76d8d20066de63d8d202c7e820d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d20006df53d8d20066dc53d8d20066de43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202d6df32d8d202d6dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d2001cff70d8d2001cfd70d8d202c6df30d8d202c6dd30d8d20024ff7658d20066dc6358d202bdef7258d202cdfb7058d2015fe82058d20004ff7558d20034fe7558d20034fc7558d20004ff7458d2002cfe7458d2002cfc7458d202c4ff7358d20006df7358d20
  | 4 => 0x913001cfe725913001cfc725913008ebf4259130004ff7159130014fe7159130014fc71591300aedf31591301bcff7059130006fb70591301befa5059130004ff7655130004fe7655130004fd7655130004fc765513001cfe76d8930086ee62d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930086ee42d8930086ee32d8930346ed32d8930014fe71d8930004fd71d8930014fc71d8930346df31d8930006ee21d8930086ec21d8930024fd70d89302beef20d8930086ec625893033dfb7058930004ff7654930004fe7654930004fc76549300367e65549300067d655493000dfa7054930004ff7650930004fe7650930004fc765093002ebe6450930006bd6450930006ef625093001eec625093000ddc764c93001edc764c93000cdc764c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c930087ce524c930007cd524c930005df714c930007db704c93000dde704c93000ddc704c93015fd8704c930026df604c930027db604c93015fda504c93015fcf204c93015fda204c930014fe76d853007ef661d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d8530336df32d8530006dd32d853007ef631d8530336f531d8530024fd70d853024efa20d853024ef710d8530005ef7258530085ec725853007ef4615853032dfb7058530004ff7654530004fe7654530004fc76545300067f65545300367c6554530005bf745453008dbc7454530004ff7650530004fe7650530004fc765053000ddc764c530016dc764c53000cdc764c530116de654c530116dc654c530006df644c530006dd644c530005df724c530006df624c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6514c530007d5514c530327d7414c53007fd4414c53007fd6214c530007db704c53000dde704c53000ddc704c5300ffd8704c530026df604c530027db604c5300ffda504c5300ffda204c5300ffd7104c530004ff7648530004fe7648530004fc7648530025de7348530005dd7348530016f66148530007d53148530025f87654130036f87654130024f8765413000dfb755413000f7b75541300077b6554130036fa6554130036f86554130097786554130006fb6454130006f9645413031f7a5454130097785454130007db7354130025fa7354130025f873541300cfd8735413000efb635413000fdb63541300cf7b53541300cf795354130005fb72541300977b52541300077952541300cfdb3254130007d932541300977b51541300077951541300cfdb3154130007d
  | 5 => 0x4ff7654540004fe7654540004fc76545400367e65545400067d6554540005bf745454002dbc74545400b73f545454000dfa705454000dbc7650540016bc765054000cbc76505400b5be75505400b5bc7550540005bf7350540005bf7250540006bf625054002dbf715054002fb77150540007b76150540016be6150540016bc615054009fb4615054009fb65150540007b55150540007bb705054000dbe705054000dbc705054011fb8705054002ebf605054002fbb605054011fba505054011fba1050540004ff764c540004fe764c540004fc764c54002dbe744c540005bd744c540026de634c5400079d434c540006f7614c540016f4614c54010fb7414c540004ff7648540004fe7648540004fc764854002dbe7448540005bd744854001eee6248540007ad424854002df87654140036f8765414002cf8765414000dfb755414000f7b75541400077b6554140036fa6554140036f865541400b7786554140007bb745414002dfa745414002df874541400d7b8745414000efb645414000fbb64541400b7bb54541400d77a54541400d77854541400d7b854541400d7385454140006fb63541400b77b53541400077953541400d7bb4354140007b943541400b77b52541400077952541400d7bb4254140007b94254140005fb71541400b77b51541400077951541400d7bb4154140007b94154140034fe76d95300967e65d95301dcfd75d953002cfe74d9530004fd74d953002cfc74d95300067e54d95300967c54d953000cff73d9530024fe73d953000cfd73d9530024fc73d95303867f53d95303867d53d953001cfe72d9530004fd72d953001cfc72d9530014fe71d9530004fd71d9530014fc71d95300967f51d9530024ff70d9530024fd70d95303767f50d95303767d50d9530034ff76595300967c655953036ddf735953037dfb7059530374ff75595300067f7559530004ff745953002cfe745953002cfc745953036cff7359530006df7359530004ff725953001cfe725953001cfc72595300967f5259530004ff7159530014fe7159530014fc71595301dcff7059530006fb705953002cfe76d913008ebe64d9130034fe75d9130004fd75d9130034fc75d91301bcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d9130366bf43d9130366bd43d913001cfe72d9130004fd72d913001cfc72d9130014fe71d9130004fd71d9130014fc71d9130366df31d9130024ff70d9130024fd70d9130356fa50d9130356bf40d9130356bd40d913002cff76591300057f75591300957c755913008ebc645913034ddf735913035dfb7059130004ff75591300067f75591300047f7559130034fe7559130034fc75591300067c75591300347c7559130354ff7459130006bf745913034cff7359130006df7359130004ff725
  | 6 => 0xf7459540006bf74595400b6bf54595400d67e54595400d67c54595400d6bc5459540004ff7359540024fe7359540024fc73595400d6bf4359540004ff725954001cfe725954001cfc7259540004ff7159540014fe7159540014fc71595400b67f51595401fcff7059540006fb7059540024fe76d8d400aede63d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d400aede43d8d403b6dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d403b6bf42d8d40014fe71d8d40004fd71d8d40014fc71d8d4002cfd70d8d4034efa50d8d4034edf30d8d400057f7558d400b57c7558d400aedc6358d403adfb7058d40004ff7654d40004fe7654d40004fc7654d40005bf7454d4002dbc7454d4000dbc7650d40026bc7650d4000cbc7650d400073f7550d400b5be7550d400b5bc7550d400073c7550d400b53c7550d40006bf6550d40006bd6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400af9c6350d400af9e5350d400079d5350d40005bf7250d40005bf7150d401c6be6150d401c6bc6150d400af9f3150d40007bb7050d4000dbe7050d4000dbc7050d401bfb87050d4002ebf6050d4002fbb6050d401bfba5050d401bfba1050d4001cfe76d89400a6ee62d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940006bf54d89403a6bc54d8940024fe73d8940004fd73d8940024fc73d89403a6bf43d8940006bd43d89400a6ee42d89403a6ed42d8940014fe71d8940004fd71d8940014fc71d89403a6bf41d894002cfd70d89402deef20d89402defa10d89400a6ec6258940005f7715894009df4715894039dfb7058940004ff7654940004fe7654940004fc76549400067f65549400367c6554940005bf745494002dbc74549401b73c545494000dbc765094001ebc765094000cbc76509400b5be75509400b5bc7550940196be6550940196bc6550940005bf7350940006bf635094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400a7ac62509400a7ae5250940007ad5250940005bf71509400a7af2150940007bb705094000dbe705094000dbc705094017fb8705094002ebf605094002fbb605094017fba505094017fba1050940004ff764c940004fe764c940004fc764c94002dbe744c940005bd744c940005fb704c94000df8704c940014fe76d854009ef661d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540024fe73d8540004fd73d8540024fc73d854001cfe72d8540004fd72d854001cfc72d8540396bf42d8540006bd42d854009ef641d8540396f541d854009ef631d8540006f721d854009ef421d854002cfd70d854026ef710d854009ef4615854038dfb7058540
  | 7 => 0x8950004fd71d8950014fc71d89503f67f51d8950034fd70d89502fefa30d89502feef20d8950005df73589500cddc73589500c6ec62589503edfb705895000d7c765495001e7c765495000c7c76549500d57e74549500d57c74549501b67e64549501b67c64549500057f73549500067f63549500357f72549500376f72549500076f625495001e7e625495001e7c62549500c76c62549500c76e42549500c76e32549500057f71549500077b705495000d7e705495000d7c705495019f7870549500367f60549500377b605495019f7a405495019f7a3054950004ff7650950004fe7650950004fc76509500057f75509500357c7550950006bf645095002ebc64509500d73c54509500076d5250950004ff764c950004fe764c950004fc764c9500357e754c9500057d754c95001eee624c9500076d524c950014fe76d85500bef661d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d8550024fe73d8550004fd73d8550024fc73d855001cfe72d8550004fd72d855001cfc72d85503e67f52d85500067d52d85500bef651d85503e6f551d8550034fd70d855028efa40d855028ef710d8550005bf74585500d5bc74585500bef461585503ddfb705855000d7c76545500167c765455000c7c76545500073f74545500d57e74545500d57c74545500073c74545500d53c74545500067f64545500057f735455014e7e635455014e7c63545500057f72545500067f62545500357f71545500377771545500077761545500167e61545500167c61545500bf7461545500bf7641545500bf7631545500077b705455000d7e705455000d7c705455013f7870545500367f60545500377b605455013f7a405455013f7a3054550004ff7650550004fe7650550004fc76505500057f75505500357c7550550007755150550004ff764c550004fe764c550004fc764c5500357e754c5500057d754c550006df634c550026dc634c5501175f534c550016f6614c55000775514c550004ff7648550004fe7648550004fc76485500357e75485500057d7548550005fb704855000df87048550034fe76d95400b67e65d954002dbe74d954000dbd74d95400b73f54d95401fcfd75d954000cff74d954002cfe74d954000cfd74d95403c6bd74d954000cbd74d954002cfc74d95403d67f54d95400b6bf54d95400b63f54d95403d67d54d95403d6bc54d9540024fe73d9540004fd73d9540024fc73d95400067e53d95400b67c53d95403d6bf43d954001cfe72d9540004fd72d954001cfc72d95400b67f52d9540014fe71d9540004fd71d9540014fc71d954002cff70d954002cfd70d95403c67f50d95403c67d50d9540034ff76595400b67c65595403bdbf74595400d73c54595403cdfb70595403c4ff75595400067f75595403bcf
  | 8 => 0xefac54509210efaf4350921007ad4350921007e77150921015ee7150921015ec7150921187e4715092101eef615092101fe76150921187af4150921187ad4150921187e63150921005ef70509210efaf4050921187e7105092101df4764c521026f4764c52101cf4764c521006f7654c521006f5654c52110ef6644c52110ef4644c521015f7734c521017d7734c521007d7634c521026f6634c521026f4634c5210e7d4634c52141fd7534c5210e7d4534c5210e7d6434c521007d5434c521007e7724c52101df6724c52101df4724c521107e4724c521016f7624c521017e7624c521107e6424c521007e5424c521107d7324c521107d5324c521005f7704c5210e7d7304c521107e7204c52100cfe76d81210defa60d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d812101cfd71d812100cfc71d812123ef631d8121006f531d81210defa50d8121006fb30d81210def830d81210defa20d81210defa10d81210def8605812102cfe76d91500357e75d915000d7d75d91500d6be64d91500d73e54d915000cfd75d91503be7d75d915000c7d75d915002cfc75d91500d67e54d91500d6be54d91500d63e54d9150416bd54d91500d67c54d9150024fe73d9150004fd73d9150024fc73d915001cfe72d9150004fd72d915001cfc72d91500d6bf42d9150014fe71d9150004fd71d9150014fc71d91504167f51d9150006be41d91500d6bc41d9150034fd70d91503bebf40d91500d6bc64591500d73c545915040dfb7059150024fe76d8d500cede63d8d5000cfd75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500cede53d8d50406dd53d8d5001cfe72d8d50004fd72d8d5001cfc72d8d504067f52d8d50006de32d8d500cedc32d8d50014fe71d8d50004fd71d8d50014fc71d8d500cedf31d8d50034fd70d8d5036edf30d8d500cedc6358d503fdfb7058d5000d7c7654d500267c7654d5000c7c7654d500d57e7454d500d57c7454d500357f7354d500375f7354d500075f6354d500267e6354d500267c6354d500cf5c6354d500cf5e4354d500057f7254d500057f7154d500077b7054d5000d7e7054d5000d7c7054d501df787054d500367f6054d500377b6054d501df7a4054d501df7a3054d50004ff7650d50004fe7650d50004fc7650d500057f7550d500357c7550d5002ebe6450d500d73e5450d500075d5350d5000dfa7050d5001cfe76d89500c6ee62d895000cfd75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d89500067e54d89503f67c54d8950024fe73d8950004fd73d8950024fc73d89503f67f53d89500067d53d89500c6ee52d89503f6ed52d8950014fe71d
  | 9 => 0xe76d95210f67e65d95211a4fd75d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521004fd73d9521024fc73d9521014ff72d9521014fd72d95214867f52d95214867d52d9521486ee42d952101cff71d952101cfd71d95214767f51d95214767d51d9521476f631d952100cfe70d9521004fd70d952100cfc70d9521034ff76595210f67c6559521005bf74595210edbc745952146def725952147df77159521474ff75595210067f7559521004ff7459521006bf7459521004bf745952102cfe745952102cfc7459521006bc745952102cbc7459521004ff7359521024fe7359521024fc735952146cff7259521006ef7259521146ee42595211a4ff7159521006f771595211a6f63159521004ff705952100cfe705952100cfc70595210f67f505952102cfe76d91210eebe64d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121006bf54d91210eebc54d9121024fe73d9121004fd73d9121024fc73d91210eebf43d9121014ff72d9121014fd72d9121466bf42d9121466bd42d912101cff71d912101cfd71d9121456bf41d9121456bd41d912100cfe70d9121004fd70d912100cfc70d912102cff76591210eebc645912144def725912145df77159121004ff7559121034fe7559121034fc7559121454ff7459121006bf7459121004ff7359121024fe7359121024fc735912144cff7259121006ef7259121184ff7159121006f77159121004ff705912100cfe705912100cfc70591210eebf4059121004ff7655121004fe7655121004fd7655121004fc7655121024fe76d8d210e6de63d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21164fd73d8d21014ff72d8d21014fd72d8d21446df32d8d21446dd32d8d2101cff71d8d2101cfd71d8d21436df31d8d21436dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21446ef20d8d21436f710d8d21024ff7658d210e6dc6358d2142def7258d2143df77158d21005fb7058d210ddf87058d21004ff7558d21034fe7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d21434ff7358d21006df7358d2142cff7258d21006ef7258d21164ff7158d21006f77158d21004ff7058d21006fb7058d21004fb7058d2100cfe7058d2100cfc7058d21006f87058d2100cf87058d210e6df3058d21106ef2058d21166f71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210f57c7550d21006bf6450d2102ebc6450d21015ec765092102eec7650921014ec7650921006ef6550921006ed655092101def745092101faf7450921007af645092102eee645092102eec64509210efac6450921427af5450921
  | 10 => 0x5131015dc7650d3102edc7650d31014dc7650d310075f7550d31115de7550d31115dc7550d310075c7550d311155c7550d31006df6550d31006dd6550d31025df7450d310279f7450d310079f6450d3102ede6450d3102edc6450d3110f9c6450d3110f9e5450d310079d5450d31005df7250d3110f9f4250d31007d77150d31015de7150d31015dc7150d311c7d47150d31026df6150d31027d76150d311c7d65150d3110fd74150d311c79e4150d311c79c4150d311c7d44150d311c7944150d311c7d62150d31005df7050d3110f9f4050d311c7d71050d3101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d8931106ee32d893149eed32d8931024fd71d893142eef21d893100cfe70d8931004fd70d893100cfc70d893149edf30d8931006ee20d8931106ec20d893142ef710d8931106ec6258931495f77158931005fb70589310fdf87058931004ff7654931004fe7654931004fc76549310367e65549310067d6554931005df7354931025dc73549311175f5354931015f67154931004ff7650931004fe7650931004fc765093102ebe6450931006bd6450931025de73509310079d4350931005f77150931015f4715093110fb74150931015dc764c93101edc764c931014dc764c931115de754c931115dc754c931005df744c931005dd744c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c931107cc624c931107ce524c931007cd524c931007d7714c931015de714c931015dc714c931167d4714c931026df614c931027d7614c931167d6514c93148fd7414c931167d4414c931167d6214c931005df704c931107cf204c931167d7104c931025f47654531036f47654531024f47654531015f77554531017777554531007776554531036f66554531036f46554531117746554531007b7745453110df6745453110df47454531007b4745453110db47454531006f76454531006f56454531117775454531007755454531007d77354531025f67354531025f4735453114fd47354531016f76354531017d76354531117d7535453114f76535453114f74535453114fd4535453114f54535453114fd64354531007d54354531005f7725453111777525453100775525453114fd73254531007d53254531005f7705453111777505453114fd7305453100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d813132edf32d8131006dd32d8131024fd71d813125ef621d81310fefa30d8131006fb20d81310fef820d81310fefa10d8131005ef7258131105ec72581310fef86058131034f
  | 11 => 0x137746554541007b7745454102df6745454102df47454541157b47454541016f76454541017b76454541157775454541157755454541006f763545414e7765354541137745354541137775254541007755254541157b74254541007b54254541137775054541157b7405454100cfe76d814111efa60d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d814101cfe72d8141004fd72d814101cfc72d814138ebf42d8141006bd42d814102cfd71d814111efa40d814111efa10d814111ef86058141034fe76d95311167e65d9531025de73d9531015dd73d95311175f53d95311e4fd75d953102cfe74d9531004fd74d953102cfc74d95310067e54d95311167c54d9531014ff73d9531014fd73d95314cedd73d9531014dd73d95314de7f53d9531116df53d95314de7d53d95314dedc53d95314dede43d953101cfe72d9531004fd72d953101cfc72d9531024ff71d9531024fd71d95314ce7f51d95314ce7d51d953100cfe70d9531004fd70d953100cfc70d9531034ff76595311167c6559531005bf745953110dbc74595314c5df735953114f5c53595314d5f771595314ccff75595310067f7559531004ff7459531006bf7459531004bf745953102cfe745953102cfc7459531006bc745953102cbc74595314c4ff7359531006df7359531116df535953114e7e535953114e7c535953114edc535953114ede4359531004ff725953101cfe725953101cfc72595311167f52595311e4ff7159531006f77159531004ff705953100cfe705953100cfc70595311167f505953102cfe76d913110ebe64d9131015f671d9131025f571d913110fb741d9131034fe75d9131004fd75d9131034fc75d91311c4fd74d9131006bf54d913110ebc54d9131014ff73d9131014fd73d91314bebf43d91314bebd43d913101cfe72d9131004fd72d913101cfc72d9131024ff71d9131024fd71d91314bef571d9131024f571d91314aef651d91314aebf41d913110ef741d91314aebd41d91314aef441d913100cfe70d9131004fd70d913100cfc70d913102cff76591310057f75591311157c755913110ebc64591314a5df73591314b5f771591311c7b44159131004ff75591310067f75591310047f7559131034fe7559131034fc75591310067c75591310347c75591314acff7459131006bf74591314a4ff7359131006df7359131004ff725913101cfe725913101cfc725913110ebf42591311c4ff7159131006f771591311c6f6515913110ef741591311c6be41591311c6bc41591311c6f44159131004ff705913100cfe705913100cfc705913110ebf4059131004ff7655131004fe7655131004fd7655131004fc7655131005df7355131025dc7355131005f77155131015f4715
  | 12 => 0xf645095102ebc64509511973f545095101eee62509510076d5250951004ff764c951004fe764c951004fc764c9510057f754c9510357c754c951006bf644c95116ebc644c9510076d524c95100cfe76d8151006bf64d8151006bc64d815113efa60d8151014fd75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d8151024fe73d8151004fd73d8151024fc73d815101cfe72d8151004fd72d815101cfc72d81513de7f52d81510067d52d8151034fd71d815129ef631d815113efa50d815113efa10d8151005bf7458151155bc7458151006bf6458151006bc645815113ef86058151034fe76d95411367e65d9541204fd75d9541014ff74d9541014fd74d95415267f54d95415267d54d9541024fe73d9541004fd73d9541024fc73d95410067e53d95411367c53d954101cfe72d9541004fd72d954101cfc72d95411367f52d954102cff71d954102cfd71d95415167f51d95415167d51d954100cfe70d9541004fd70d954100cfc70d95411367f50d9541034ff76595411367c655954150dbf745954151df77159541514ff75595410067f755954150cff7459541006bf745954150cbf7459541004ff7359541024fe7359541024fc7359541004ff725954101cfe725954101cfc7259541204ff7159541006f77159541004ff705954100cfe705954100cfc7059541024fe76d8d4112ede63d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4112ede43d8d41506dd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d41506bf42d8d4102cfd71d8d414a6f651d8d41506f741d8d414a6be41d8d414a6bc41d8d414a6f441d8d414a6df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41506bf40d8d410057f7558d411357c7558d4112edc6358d414fdf77158d41004ff7654d41004fe7654d41004fc7654d4101cfe76d8941126ee62d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d8941126ee42d89414f6ed42d894102cfd71d894144eef21d894100cfe70d8941004fd70d894100cfc70d89414f6bf40d8941126ec62589414edf77158941004ff7654941004fe7654941004fc76549410067f65549410367c6554941015bc765094101ebc7650941014bc7650941196be6550941196bc6550941006bf635094102dbf725094102faf7250941007af625094101ebe625094101ebc6250941127ac6250941127ae5250941007ad5250941007b77150941015be7150941015bc7150941187b4715094102ebf615094102fb76150941187b65150941187af2150941005bf7050941004ff764c941004fe764c941004fc764c94102df47654541036f4765454102cf47654541015f77554541017777554541007776554541036f66554541036f46554541
  | 13 => 0x9151566bc50d9151006bf30d9151006be30d9151006bc30d9151006bf20d9151006be20d9151006bc20d915150ebf10d915150ebe10d915150ebd10d915150ebc10d9151156bc645915155df7715915150dbe7619151156be76191511573e75191515573d7519151556bf65191511579e73191511579d7319151006be6319151006bc63191510073e531915154f3c5319151157ae7219151157ad7219151006be6219151006bc621915154f3f5219151557b67119151157b57119151556bf611915154fb751191515573e51191515573c5119151557b45119151557b63119151157ba7019151157b97019151006be6019151006bc601915154f3f50191510157c765515102e7c76551510147c76551510357f74551510373f74551510073f645515102e7e645515102e7c64551511573c645515114d7e735515114d7c73551511573f43551510057f72551510077771551510157e71551510157c71551512077471551510367f61551510377761551512077641551512077631551510057f7055151024fe76d8d510357e75d8d510157d75d8d51006bf64d8d51006bc64d8d5114ede63d8d5114f5e53d8d51014fd75d8d514c67d75d8d510147d75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5114e7e53d8d5114ede53d8d51546dd53d8d5114e7c53d8d5101cfe72d8d51004fd72d8d5101cfc72d8d515467f52d8d51034fd71d8d514c6df31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d515467f50d8d51005bf7458d51155bc7458d51006bf6458d51006bc6458d5114edc6358d5114f5c5358d5153df77158d51004ff7650d51004fe7650d51004fc7650d510057f7550d510357c7550d51006bf6450d5102ebc6450d510073d5450d51026de6350d5114f5e5350d51015f67150d511c7b64150d5101cfe76d8951006bf64d8951006bc64d8951146ee62d8951014fd75d895102cfe74d8951004fd74d895102cfc74d8951024fe73d8951004fd73d8951024fc73d8951146ee52d8951536ed52d8951034fd71d895146ef631d895146eef21d895100cfe70d8951004fd70d895100cfc70d89515367f50d8951005bf7458951155bc7458951006bf6458951006bc6458951146ec625895152df771589510157c765495101e7c76549510147c76549510057f74549510073f64549511b67e64549511b67c64549510073c64549511b63c645495114d7e735495114d7c73549510067f63549510357f72549510376f72549510076f625495101e7e625495101e7c62549511476c62549511476e42549511476e32549510077771549510157e71549510157c71549511a77471549510367f61549510377761549511a77641549511a77631549510057f7054951004ff7650951004fe7650951004fc76509510357e75509510057d7550951006b
  | 14 => 0x6ef72591321ceee5259132004ff7159132014fe7159132014fc715913218edf3159132004ff705913200cfe705913200cfc705913216ebf4059132004ff7655132004fe7655132004fd7655132004fc7655132025ec7654932036ec7654932024ec765493201def755493201f6f75549320076f6554932036ee6554932036ec65549321776c6554932006ef6454932006ed645493256f6e54549321776c5454932007cf7354932025ee7354932025ec73549321afcc735493201eef635493201fcf63549321af6f53549321af6d53549321776f51549321afcf3154932005ef70549321776f50549321afcf3054932014fe76d8532166f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532024fd72d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d8532496df30d853243eef20d8532166f46158532005fb705853215df8705853200cfe76d813215efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d8132014fe71d8132004fd71d8132014fc71d813233edf31d813215efa40d813215efa30d813215efa20d8132006fb10d813215ef810d813215ef8605813202cfe76d9151156be64d9151014fd75d9151156be54d9151566bd54d9151024fe73d9151004fd73d9151024fc73d9151156bf43d9151006be43d9151156bc43d915101cfe72d9151004fd72d915101cfc72d9151156bf42d9151006be42d9151156bc42d9151034fd71d915150ebf41d915100cfe70d9151004fd70d915100cfc70d9151156bf40d9151006be40d9151156bc40d9151555be76d915102cbe76d915150f3f75d915150f3c75d9151006be63d9151006bc63d91510073e53d91515673c53d9151006be62d9151006bc62d91515673f52d9151567b771d915150fb471d9151567b751d915150f3e51d915150f3c51d915150fb451d915150fb631d9151006be60d9151006bc60d91515673f50d915150ebf75d9151156be75d915150ebd75d915150ebc75d9151006bf73d9151006be73d9151006bd73d9151006bc73d9151566bf53d9151566be53d9151566bd53d9151566bc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d9151566bf52d9151566be52d9151566bd52d9151566bc52d9151006bf32d9151006be32d9151006bc32d915150ebf71d915150ebe71d915150ebd71d915150ebc71d915150ebf51d915150ebe51d915150ebc51d915150ebf31d915150ebe31d915150ebd31d915150ebc31d915150ebf21d915150ebe21d915150ebd21d915150ebc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d9151566bf50d9151566be50d9151566bd50d
  | 15 => 0xd5350d42007af7250d4201dbe7250d4201dbc7250d421cfac7250d4202ebf6250d4202faf6250d421cfae5250d42005bf7150d421c6be6150d421c6bc6150d4218f9f3150d421cfaf2150d42005bf7050d4202dec7654942036ec765494202cec765494201def755494201f6f75549420076f6554942036ee6554942036ec65549421976c6554942007af745494202dee745494202dec74549421b7ac745494201eef645494201faf6454942197af54549421b76e54549421b76c54549421b7ac54549421b72c5454942006ef63549421976f53549420076d53549421b7af4354942007ad4354942005ef71549421976f51549421b7af41549421976f50549421b7af4054942014fe76d8542186f661d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d8542186f641d8542186f631d8542186f621d854200cfe70d8542004fd70d854200cfc70d85424eebf40d8542006f610d8542186f410d8542186f4615854200cfe76d814217efa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142006bf54d814239ebc54d8142024fe73d8142004fd73d8142024fc73d814239ebf43d8142006bd43d814202cfd72d8142014fe71d8142004fd71d8142014fc71d814239ebf41d81422eeef21d814217efa40d814217efa20d8142005f77158142185f4715814217ef86058142034fe76d95321767e65d95321ecfd75d953202cfe74d9532004fd74d953202cfc74d95320067e54d95321767c54d953201cff73d953201cfd73d95325ae7f53d95325ae7d53d9532024ff72d9532024fd72d953259e7f52d953259e7d52d9532014fe71d9532004fd71d9532014fc71d95321767f51d953200cfe70d9532004fd70d953200cfc70d9532034ff76595321767c6559532595df73595325a5ef725953259cff75595320067f7559532004ff745953202cfe745953202cfc7459532594ff7359532006df73595321ecff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff705953200cfe705953200cfc70595321767f505953202cfe76d913216ebe64d9132034fe75d9132004fd75d9132034fc75d91321ccfd74d913201cff73d913201cfd73d913258ebf43d913258ebd43d9132024ff72d9132024fd72d913257eee52d913257ebf42d913257ebd42d9132014fe71d9132004fd71d9132014fc71d913258edf31d913200cfe70d9132004fd70d913200cfc70d913202cff76591320057f75591321757c755913216ebc6459132575df7359132585ef7259132004ff75591320067f75591320047f7559132034fe7559132034fc75591320067c75591320347c755913257cff7459132006bf7459132574ff7359132006df73591321ccff7259132
  | 16 => 0x4d520075f6354d520267e6354d520267c6354d521af5c6354d521af5e4354d520076f7254d5201d7e7254d5201d7c7254d521ef6c7254d520367f6254d520376f6254d521ef6e4254d521ef6e3254d520057f7154d520057f7054d52004ff7650d52004fe7650d52004fc7650d520057f7550d520357c7550d5202ebe6450d521b73e5450d520075d5350d5201dee7250d52014fe76d85521a6f661d855201cfd75d855202cfe74d8552004fd74d855202cfc74d8552024fe73d8552004fd73d8552024fc73d8552034fd72d855247eee42d85521a6f651d85521a6f621d855200cfe70d8552004fd70d855200cfc70d855252e7f50d8552005bf74585521b5bc74585521a6f4615855200cfe76d815219efa60d815201cfd75d815202cfe74d8152004fd74d815202cfc74d81520067e54d81523ee7c54d8152024fe73d8152004fd73d8152024fc73d81523ee7f53d81520067d53d8152034fd72d815230eee32d8152014fe71d8152004fd71d8152014fc71d81523ee7f51d815219efa50d815219efa20d8152005df73581521addc735815219ef86058152034fe76d95421967e65d954202dbe74d954201dbd74d95421973f54d954220cfd75d954201cff74d954201cfd74d95425cebd74d954201cbd74d95425de7f54d9542196bf54d95421963f54d95425de7d54d95425debc54d9542024fe73d9542004fd73d9542024fc73d95420067e53d95421967c53d95425debf43d954202cff72d954202cfd72d95425ce7f52d95425ce7d52d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542004fd70d954200cfc70d95421967f50d9542034ff76595421967c65595425c5bf74595421b73c54595425d5ef72595425ccff75595420067f75595425c4ff7459542006bf7459542196bf54595421b67e54595421b67c54595421b6bc5459542004ff7359542024fe7359542024fc73595421b6bf435954220cff7259542006ef7259542004ff7159542014fe7159542014fc71595421967f5159542004ff705954200cfe705954200cfc7059542024fe76d8d4218ede63d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d4218ede43d8d425bedd43d8d4202cfd72d8d42576ee52d8d42576df32d8d42014fe71d8d42004fd71d8d42014fc71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d425bebf40d8d420057f7558d421957c7558d4218edc6358d425b5ef7258d42004ff7654d42004fe7654d42004fc7654d42005bf7454d4202dbc7454d4201dbc7650d42026bc7650d4201cbc7650d420073f7550d42195be7550d42195bc7550d420073c7550d421953c7550d42006bf6550d42006bd6550d4202dbf7350d4202f9f7350d420079f6350d42026be6350d42026bc6350d4218f9c6350d4218f9e5350d420079
  | 17 => 0x2179e5355143005bf72551431c5be71551431c5bc71551431d73f51551432179f3155143005bf705514302ddc7654d43036dc7654d4302cdc7654d43025df7554d430275f7554d430075f6554d43036de6554d43036dc6554d431d75c6554d430079f7454d4302dde7454d4302ddc7454d431f79c7454d43026df6454d430279f6454d431f79e5454d431d79d5454d431d75f5254d431f79f4254d43005df7154d436079e4154d431f79c4154d431d75f5054d431f79f4054d4301cfe76d89430067f65d89430067c65d89431ceee62d8943034fe75d8943004fd75d8943034fc75d8943024fd74d894302cfd73d89431ceee42d89431ceee32d8943014fe71d8943004fd71d8943014fc71d8943586df31d894300cfe70d8943004fd70d894300cfc70d89435b6bf40d89430057f75589431d57c75589430067f65589430067c65589431ceec6258943014fe76d85430067f65d85430067c65d854302dbe74d8543025bd74d85431c6f661d85431c7b641d8543034fe75d8543004fd75d8543034fc75d8543024fd74d85431c6bd74d8543024bd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d85434febf42d85431c6be41d85431c6f641d85431c6bc41d85431c6f631d854300cfe70d8543004fd70d854300cfc70d85434febf40d85430057f75585431d57c75585430067f65585430067c65585431c6f461585431c7b4415854300cfe76d81430067f65d81430067c65d81431befa60d8143034fe75d8143004fd75d8143034fc75d8143024fd74d814302cfd73d814301cfe72d8143004fd72d814301cfc72d81433aebf42d8143014fe71d8143004fd71d8143014fc71d814335edf31d81431befa40d81431befa30d81430057f75581431d57c75581430067f65581430067c65581431bef8605814302cfe76d91520357e75d915201d7d75d91521b6be64d91521b73e54d915201cfd75d91525c67d75d915201c7d75d91521b67e54d91521b6be54d91521b63e54d91525febd54d91521b67c54d9152024fe73d9152004fd73d9152024fc73d9152034fd72d91525c6bf42d9152014fe71d9152004fd71d9152014fc71d91525fe7f51d9152006be41d91521b6bc41d915200cfe70d9152004fd70d915200cfc70d91521b6bf40d91521b6bc64591521b73c54591525f5ef7259152024fe76d8d521aede63d8d5201cfd75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521aede53d8d525eedd53d8d52034fd72d8d52596df32d8d52014fe71d8d52004fd71d8d52014fc71d8d521aedf31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d525ee7f50d8d52006de30d8d521aedc30d8d521aedc6358d525e5ef7258d5201d7c7654d520267c7654d5201c7c7654d521b57e7454d521b57c7454d520357f7354d520375f735
  | 18 => 0x86058153034fe76d95431d67e65d9543214fd75d9543024ff74d9543024fd74d95436367f54d95436367d54d954302cff73d954302cfd73d954361e7f53d954361e7d53d954301cfe72d9543004fd72d954301cfc72d95431d67f52d95430067e52d95431d67c52d9543014fe71d9543004fd71d9543014fc71d95431d67f51d95430067e51d95431d67c51d954300cfe70d9543004fd70d954300cfc70d95431d67f50d95430067e50d95431d67c50d95436157e76d95430347e76d954361f3f74d954361f3c74d95436375f73d954361f5c73d95436375f43d954361f3e43d954361f3c43d954361f5c43d95430067e62d95430067c62d95436373f42d95430067e61d95430067c61d95430073e41d95436373c41d954361f5f31d95430067e60d95430067c60d95436373f40d954361e7f74d95436367e74d954361e7d74d954361e7c74d954361e7f73d954361e7e73d954361e7d73d954361e7c73d954361e7f43d954361e7e43d954361e7c43d95430067f72d95430067e72d95430067d72d95430067c72d95436367f42d95436367e42d95436367d42d95436367c42d954361e7f32d954361e7e32d954361e7d32d954361e7c32d95430067f71d95430067e71d95430067d71d95430067c71d95436367f41d95436367e41d95436367d41d95436367c41d954361e7f31d954361e7e31d954361e7d31d954361e7c31d95430067f21d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95436367f40d95436367e40d95436367d40d95436367c40d954361e7f30d954361e7e30d954361e7d30d954361e7c30d95430067f20d95430067e20d95430067c20d95430067f10d95430067e10d95430067c10d9543034ff76595431d67c6559543625bf745954362ddf735954361cff75595430067f7559543624ff7459543006bf7459543214ff7359543006df7359543004ff725954301cfe725954301cfc7259543004ff7159543014fe7159543014fc7159543004ff705954300cfe705954300cfc705954361d7e76195431d67e761954361c7e761954360f3e74195436173d74195436167f64195436175e731954360f5d73195436167f631954360f5f43195436173e43195436173c43195436175c43195431d76e72195431d76d72195430067e62195430067c621954360f3f42195431d77671195431d77571195430067e61195430067c61195430073e411954360f3c41195436175f31195431d77a70195431d77970195430067e60195430067c601954360f3f4019543025bc7655143036bc7655143024bc765514302dbf755514302f3f75551430073f6555143036be6555143036bc65551431d73c65551430079f7355143025be7355143025bc73551432179c735514302ebf635514302f9f6355143
  | 19 => 0x400d001000000a001000806c0000050000038002004000002400c000002002c006002002001400000100000040060000000004000000004000801800100480080100000168000000001024fe76d8d54216de63d8d5402cfd75d8d54034fd74d8d54216de53d8d54216de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54014fe71d8d54004fd71d8d54014fc71d8d54216df31d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54216dc6358d5401cfe76d895420eee62d895402cfd75d8954034fd74d89545f6bf54d89545d67e54d89545d67c54d89545d6bc54d8954024fe73d8954004fd73d8954024fc73d89545d6bf43d895420eee52d895420eee42d8954014fe71d8954004fd71d8954014fc71d89545f67f51d895400cfe70d8954004fd70d895400cfc70d895420eec6258954014fe76d8554206f661d855402cfd75d8554034fd74d8554024fe73d8554004fd73d8554024fc73d855401cfe72d8554004fd72d855401cfc72d8554206f651d8554206f641d8554206f631d855400cfe70d8554004fd70d855400cfc70d8554206f4615855400cfe76d81541fefa60d815402cfd75d8154034fd74d815440ebf54d81543ce7e54d81543ce7c54d81543cebc54d8154024fe73d8154004fd73d8154024fc73d81543cebf43d815401cfe72d8154004fd72d815401cfc72d8154014fe71d8154004fd71d8154014fc71d815440e7f51d81541fefa50d81541fefa40d81541fef8605815402cfe76d91531f6be64d9153024fd75d91531f6be54d9153646bd54d9153034fd73d9153626bf43d915301cfe72d9153004fd72d915301cfc72d91531f6bf42d9153014fe71d9153004fd71d9153014fc71d9153006be41d91531f6bc41d915300cfe70d9153004fd70d915300cfc70d91531f6bf40d91531f6bc645915363ddf735915301cfe76d89531eeee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d89531eeee52d89531eeee32d8953014fe71d8953004fd71d8953014fc71d895300cfe70d8953004fd70d895300cfc70d89535e67f50d89531eeec6258953014fe76d85531e6f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d855353edf53d85534d67e53d85534d67c53d85534d6dc53d85534d6de43d855301cfe72d8553004fd72d855301cfc72d855353e7f52d85531e6f651d85531e6f631d855300cfe70d8553004fd70d855300cfc70d855353e7f50d8553005bf74585531f5bc74585531e6f4615855300cfe76d81531defa60d8153024fd75d815302cfe74d8153004fd74d815302cfc74d8153034fd73d815301cfe72d8153004fd72d815301cfc72d81533fe7f52d8153014fe71d8153004fd71d8153014fc71d81531defa50d81531defa30d81531def
  | 20 => 0x9000000000000000100000010000000000001001000c000004000800800a002002000400000000300100000050078000024000000000000600000000000020210018004000000005800001401600200040000010008004000000000805c0000110000038000005000000c0040060000004006006004000000200100580080000010040000002000009004401600101a0000000021006000801a0010000000000009006800400e000000001c0000010050000000017000800c000004000000000a0010018000000000001802001e00500000080000000018020018001002000400e00a001800000c003002000400c0010008018004000006800000a000004000c0000000018000018000000800800001000780040060120028020002000002000800800600d000c002000002801c006000001000801200000000a001c0000038000006000000800000601200000000020050008000002003005000802a013000001400e02d000005000000300000000000000018004002009003000401200400f0018016000001000c006010003800000000900a000400000000100040000030030010002003002800c0000010078010000003005801001000000380200040170000000002000000003c010007000800000a001000001800200100280140040010010004000004000000800000200700000140010028010002000003000c002003003000000400400300040000090008008004003002800000a001001000000c000000802400e017002802400000000300100040010020004000000002800000c0020008038000005001003801c004000000000c002000000400401800000080620030028008002000000001c0020000000074000007006000800e00f00780000020000050000002001000800001a000003002003c007002800000800300080000020010000040000002000800800800a00c8004026000001800c000001000801400200100700140080010008030006002000003400400d0010020000004000000800200e0028024008002000803400200b00000000060020010034000005003000c012002003800801e00d00200040020180108000000000008001c00000000000200040000010000000000001004800800100780000000000018000016000002802000400600180e000600500000080020000010008000002000801400000000380000040130018004000000001000800a00400000080040000000000002004000000c012000005803801800e002800800600000180100240000010000000003002000c002001000000800400000100000000010008020006000000000000200200180100060000000014030005000801400c0030040004002000002801800800000700100040190000004002000002800400c001001000000400700300040
  | 21 => 0x1bf0000afc0006a700000016ae56653724654e851d0001460324cfc00000002c400058a800000063302331b19fa83500002c866410e4018000b763e64778000000d3b206a4600faa0829689757ee33a0100720c329123090001a80c330001720000b9300000002c800000028cc0001b34f1000000012230d860800095868f0000086d470cb00016eea0702708ec7ae2405d49580f3aa7700000002a630100030940000000000000000a94000000000000034a09e0000ab713800000000000002394c500003f41660c2a66b0000b3c3820002a187b8c1a2330000e10d3400014c0f500000ae31895007d00271a480019b20f84f90980e5e8e900000000000003fe09509c427f183000009448a45b25cc6982a90001a5800100280000120000000000008002001000401800000000180060010018008002000004000000200200000000040010000004000005002000400000100000080000030040004006014001803c0020000008014002000001801000000a00100100100000008000006007000002800a000002001c0000010000004036000000000400c00000080000080060040000004000000800801c00100180880060030000028002013000801000000100500000000020000014000010000000000400000080400060010018000006003000000000800100500080040000000004000000000001c00000b01280040120010008004004001003802800e00000100080060020000000004001001800c0000010048018006002000000400000400080040240040040000002006004801c000005005804002200200180280000000000008002005000000c000001001800001000200880080020040008014000001000800401a002001801000a000000801c000000002000401a0010008004008004002000000c00000700040040040000008000000003800400200000000080140000000020004000000000400600000a0008004000002000800600c003800800c00000000100120000000030006001000800000201900180000020090020000008004000802800800c000000801e00a000000000c0040008000004006001001000c0010068000006000000800c00000f000000400400200500080040000168004000003005001c010004000800000c000001802c002000002000c022002000000001600100600000000020088004000001001801400400000100180000000030010002002002002000c0020000000006000004802c0260000008004002006000800000600b005800c000003000801801400c00080140000000018000000000000000400603300180280000030018010006007000000000200000380000060020040010000005000000400800b0000000016000000000c0060060000000000004000003c02600b00000040000020
  | 22 => 0x3af0ba9859a1ea192fa0000000b5c000077c00000022e000022e000000225914e77261229c886698364a208d78ebb41ad3135498b85139800000017b00010545280000002ef000000000000cc68800035097a400000000001d80007ca43d9e88e945a00f206998001bc5b21cf80000001df807133a43630d12d400097144700002e417057a1ae80000005281700e86798000000130e6cc3ab1dd99aa00067da8acd380000000000d1ec4c000000097400062d8f2c77056e3ef32380f800000000000000f60000000f5200000009f40000002ff800000020c3a90001202cbc00029c08ee7d222325e0b4800020500002907040360000e0e8173f592dd36218b5b52fe146e9952ad28f57c258142600002920001fa8c390d800000011292d49ac00000011546bb62f8000fe4000000333cba4a8f4c59c8c00028d00034f800036a00007c8000119000059998400000005d000000014ea14572e53c3d819510b28c10000000c26a6200000000000001f480000000005658000000000470285529cac005280001f6be44b003944608375929345a5493602900008de347623293c9a8000000000000000054e91a52409cb58b9294000000000000000039400032a000000037080018405cc671b4fc3e01263d799ec7fe0000000000faa69b3e9a2ac3cec3d1658ed18ae0000f580019881411f80c7558832909926ad958000098800056c7260000eec0000001ab820c938642000014c0000005799fbc00000000000018b000041e31fc00037400010dd60c00063b11898246f901625f094ed393cb220d996668000174c000475107aa458148fa368913ca4400041281a892c0312b1b02d7be72a2b2a0011f033418d308800000028480017165570000be8dd286454900001a0bca00014b8ae800012e13a077aa114c78c347721631c3228520c4586248001a8ab90000000026aa0b05c2bd8c78000364327d6e82106919d553b860356297cc000ce762f1d800001af01f02310d496c63893f000000002ea2ec7b6afb1740828000c7944991100c20000612e6590000052f000000000008c064d82a0f56529d70e1c5845f3a99536000e0e4af206eac3420393380006c100027e090409905f31946e486d00000016500005cc0204e30aa20001c6ccc20001581bed196a1321133b159c21812621f000031c0491ec89ac000000028000000058680017e899e00020b00000001ef97447b80000000000dee0004ef1bd0f42c3660f000000000014f80000000001e800d172a7ad00000001269311bc1340cde6c443723cc0e2b830da2b0c23ccf251e06e43ac8dc2b50000eb000018c2d10000ced42b800137e28700000011c6bb027b9bd800000000001d19c8000348965c7866a60002900bde0000eaa0d8000519000171400073c58200004b400000000000000000000
  | 23 => 0x23ed4d49f3000152144a0f04e989d800048c41a1d24e1a49f0000f54ad203866b1bfca344b336a8bf028c1f523f87f11122f11458000c8e89039b256cdfc57a03f31b594e8f7537ade49dc04900000015729b600031f457800000000016ce000363a2700002190000000ef40002bb2b8000093723d924400031f62a000070a2e062980000000000000fd00000006431b9d172a754eb20a06fc4fa0b680000ae6d839b80000000003a8800100e0000000000000000000000027c11400000009f20005078f64000000276a69000000000000000001f4000000000090a0868000000a200000000000000640aaa0000ae3000343455e00000000000004bd5a1119c9fa5671998000000000000000123e95d6880000000000000000095c00000000000000002e396c4a560000000000d8c133012135c84c0005650000000ca6000304cca07ce35e0000ab800256d840cb3241c000112d10e3632bf8fe80000003b6800173a0000002a619689c630827c400099700000000000001a102180007fd421269947e00066a000096294b3c19fd8f4e5d900016d40006c240aa2a0e0a000124aa6c7c893c4982470fc455d054b4296b2b2150b05e956c94f4b5994455c9eb30ba31d6a03082f425a15ce0002d416cc5a052928613701ac5fd69a0000592000216b34c0007843900ba8f7421a64795c000071545a85e01cc01439a8f1c0885af67d1eacbdc2a02ac000080096900025105d67685d587f481839d40d0bd1970a3e50d97416381a02e4a2b46f40003ed93c19de0003601f802208911242cec00000049c01ace440000000000000b78000292029a000439000101c0000001318000000000195800000049300000000000000000f8e62f3400e603385d439c84f177ccda2b0a59910c541603b4ad0368be07fa3f1780ba735680016800000d3800000000059594840000000380000b82a464c480003f000000011c8be479549f1fc57a23a35dd0000000a220000000718000000000000000065680005f20250000794000000691000000033d000000024858941f2a04ebe84e17e928000000002b04b8dbe000162800141c000000111c80601e58800008248681daac91344d280002c4c0007590000d6cc920006890000000cc900000015fab873e18e6c40e9af491938cabe97965aa5b800089406a2f14c1200061612550be7c43c01bf06a0000577224800093f2760dad6700000000cf0b8c80a2c391a03c015b0000760a5e2b55aaa8a59868ac00029113a40002c98000000709357a23019a00048a8e2c00c3624911d113d849a2df93ecd4021c00022c10bcab02441a940001f600019201c2bfb404046d32c29e4458000000000000143818abf10000cd8e0c0c700019d54c2000000204d87c2de1192044128aa70649710000b5e0002b94000
  | 24 => 0xe7cb3d8b1a80008b2678b1cc00000008492d01909942be8e7ca2c6e316a0000d6000000000004c220569b00014061d30001fe42b4bc10002d4800095c0c41f612fcae24028000a641ba00000009006770000bfc000a120000234394ad838d1248a04d130002c000446ce22b0000000909000128800000000000006ac0082249400000c0200000000000000000000e62c19260000101e6e611203c8ef099b0ae95590e81ae3e2aaf4d68d1d3b61ee0520b842610344000000007aa580000000b3ad299ee0004298ea852a0000e820cc0907735cd8994f9a00009b9b5c2ac1c41859df904045d0002b1c0000004770a94000157000262000000003c14e10f2a8b00014358081120002e78aa600000000011c400000033600000000148000f3caea52c9ad86a400002e1bc00000002932e491acb4350bb4f56228b10000f8c00000005b2078f104da00000010748820000000000bd4000148d0b823f51500016e61be4b682140eeb8f0531d783ba94845c247550c4af0000c5c00008f00006c54ae50142518a800097240c92a40000005dc9608000000000000071a00000034219ecb1b03720b40001a41be9fcd32400051824e4d7e94642e99f139a8c229da9f81da19e267add9a6218403c8ab52a02150dc2400fa22810fb8e597dcc825b68fe12820005358000a4a3c40000e9443e84129010200000000000c5400000023b00014cc0000002280ce8000100b1800006b10000000b427f5505000053663e5e2092d72886743e80014380000db3414b3a000596276d9160003dea2fc0002db000000050617158f241d0243e50002860c3844e00000013722646191cb8bba4e03eb8d6533800351b2534cf400d4aa9e4c568875027b35ce52d3c42433cc000107155000136a5b62c5000000000000000004287866871b680001d44330fb59f262712987f8bee0000001375856d02080a3240007b56a100005149a905d0a395129d81c71d4cef203700593980000002b923fc00025767c0000000a780000000000cdc00019d864256807102847c23371d12d6857c8dd5dda3b00000004532840cccd3507c80011b600067296ad31cc8d2372ef4b4c185378ad20d4400013bb25880c3310cd2d94b967814969fdc6b02d500005b8d9263d2f000000000006270d80a8c57100000015e40000000000000000000243c30e0003d6340c87c000000000184c383000109c0009f63d21ba0c4286f2a39c3c0000001f00a4c352ade2bd88f049e2fb6600c29a420000000ca000001b686000135a0004e29b4171a255179860c12043c04c0cbc1b8225158aa40e7a0000262468000b6f000000000006300014d8cd294348f27a80000005130000694000000000000000000029f0000a064a931e0000000000000020c68b17a988c85200000000008e03d834e95dd9bc16c000
  | 25 => 0x422797e60000b5a28c9de1aa000000194282b4fe8fdcbec09f0ceaa9595c66c00000019d2c8c00000000005920002bf000000000027bc000b6b21e80005089fb12ca530a2488a00012fd65c6362aa97094f4297000000000031265000000004860a0271c0000002c4073caa00000afb26400078e0001dfda900ea4f41a900009cc0000d0c000d2000029040000005d0000000001d000000000000000000000008610001c089d41c32189df44100e33550db4f9811a13f2a0000064d5860001a36bd62c72c2d7ca000023a4a081c00040b0fb903071d40e92f00000000000310dfa4321eb00011e20005db9f712285a920f2dc92b403c5e30001076cc73c5a89da52add2171ed11a847d42d176cac8000000202400031e000000000097b00008dd1fa1523eb1ded6405340062d156f8bdc26d97f05328bc2fd1ea0000b7e17b0001340c0c4fc8000794095000131075acbd1839da92ecb5b256024406a67352919c1382a8500000011c886968b8bdd5404cb00001359a400062e04e40a22a40000fccdd62fe00030b99363795828000eb40000001df0880b623ff000000053337680019d665e22b80000000000001a14b6e0005698d004362ce5a72bd461e03250f9a2080a3a85160a45392000488805cf24000256af5525c0005d8a320aa293b07e80018d26403ff87a8000d1f467acb4b583b168b00018e0000000132837615e2520af443a49800025fc00000032d800000000042780000009d0000000106200000031d128a2dc1b983f0cce69958a08bc0001796962e04000c661668000f66000091800038e01357b8000c0caba00000000002030002d18000000043a2553e8428097800000012000000002d20000001f200005ae63580000000004f6826c6ec1a554f8000000bef28408d4ecab4c2c01d981546380a880018aa8d159c89897ba00062180000000002422c3c00051b00000010e248500000000000000001e6c000a9c00009c9304ce02950001924a8d0000000b0600000023e40001d266515cda5cacd0812b20000165512269da48be952a00012c25b83ae9618000c3b1b406f4012000000201121aca3000000000000000020f560237f5550ae500c6e0659035414800068a812c0004c90002f785e01e3648828d7f8c18000000000000030c25d04b060407a1f04cc45755fd278c0003975d900000000005ed00014760000a20a7000000000029a0000a9900005f40000000000000a58acf53b0000e9acbf1f10c004d6763000000041a000137800031835169980002de000300a3d509a12800000017ea0000000000000c1b6081fb9878b6c4399149248beb07d1c0c1967c6343112016800028180000002e60558000000afa1269ad567878c1910a5800064f0001e7d8c6be833708d00000001708188f786936420ba4c7223a116800029
  | 26 => 0xbe81c5c12415a300000002f38cca00023c8000d9e0006018000000000000000000043431698280000000000000bda00001780000000966288000ea00000d10000bc650400015e400000022a80009e438011b09790529f70000000000000000000000087e00014f956445f00016409c22c20000d951009ee2ed00001d017f4e424391d400024e800069e00036919280000000e2871800000004d000000043f55e34686aa00020c0560d6400060780000cccd1000000000000013e32c45c45de3d016f8b0aa6002282200e6d00517000125878746b9cfd3a836e1101d08a980cf10009a94a200025580000000000000001a820001fda18c000a64000117800000042180000003ce62400016fe4731dd34500000ce4758fc87fc1ce0400b4c0000006848000000000000000004c28560b1d6c0000000000898000ad50000f211e00003171ddcd86000499055475c2ab0000000ece0003f38000000ada00023699c453f000106c000b3d018000184633e3fc2c28e82000000000000074e6552115646b894132c2462266d4e510ec000a1a000000007ed382a117a800054e43b2924abcd0b591000060a3b038e0d740003200ef000172c48d0002508328c1c0002e6941249b04103640000003ab8d7115200008b000000000008e2d04000c890000fb15580890a70000c9cce1469aae000000069b8e0800000026ca6f40007fa1e8800122e0004f28600afc0003d280000000000000001020000000000093ca9700007bc000191137183c1b6578078800135c423000000000000000000014ba00035728e0d943c008232ac00000000025c1930d4657811f8fca000089a160654b4b0001b513ba679000187c8c633504534940000003b700004e8c4b0002be0ed226d00007c425600024c939d8947b73158ce15dac7516bb1b98fc4d80cc3068a1e4f546f05085b00bd1c4000000042c2f6027851818f0000000e0294a604919450017c20a0001370c442128104000530541b0fd8c20b500016505ca9a15228789a740e713a99c8db20004671acc00087a00027e800030c2a59e080000002ce00003b400021c30a0b7200000000001d8c7a44d2b04c6a74b56caa8c90e7714acb164902461221a52451200014916795b88883110000000304369a45865c67f0001bd55e200049eac1c44419f1c9b1ec294b9c0db85848d482f244a59015813b5028a695c84cc0ac923d19aba65178001018bea000000000000050000010487d4000057078244c4f0875caa89860000844eea7905d121fc0000005520000454c9549520fc00000000000000004e535ca18000054900000000007c258d23a16246925b0088426c000618995574a00027f8fa951c6f225c800114a000000036000001a5f1998ce56018460000192e697573050c6cc9e4261a1002a881410900013d21815d
  | 27 => 0x921d3135000028f00013780000002f8883a4b630581bd054ae108f84b47a6a0c00000006581a33772ff56fa00002d80000005b03468000bccc4708e8fc5194ba44cc2dc400096767a80005ce95620c80014d207a0b002b42a0644577ad3c47aa8a5dc07fc0002d164800009460004c5000000024a19180000001250002118c82b7058180015d6a4d0f6800118625b0001a110ee3dd3190000000000000000171079a00004e00000003438dc00009b3000000000000000018fc000b68254000000013d5191dbca26ab41290da58425df536a16c8f8c7754600001bc000000197468c000236292d08e0600001f746c26db39823d80009c015c294c6560000000000e584600000bb0116000000141800070b399800000089b0c80ef93864de58f800164c0006982084000000000049d5d2abb6520001a4e48300c8000bf07da5ecaa204ac7df0002110826c524a88000d7c66a00003dcdc438a1340c6c6eea47010925d66600029b93540004c51f7aba0fd22a800005d80ce0004b10e3c384bcc2ada1e0df40000000000000b4951cb20c000000009068427e0002f8905c00033b0000f354b69851aa070000000000010691ced320c493352c60000f61be0fe03534ec82cd004527053800175ea581e48b7c0000001c8ab453002b709512c8000451000341c86a56c6978000000bb500032d800000a0000001a08000365a09c00012100000006320401fc80017a6000229800042eb295f02bb00000005020001016000000000116e9fc23c07840000000001874000bf90cca54c000000269ad7590a13456100000002d219fa5dc000caf5c335102ee56f0002631870bcb4e22ed80000000000000cb00005f610ac0000001e93190a2001f0001bbc0005e10000000000000000000048e0003fa2b7d5aca230000db19e810c1a080000000001071bccd02000470800183ab692cb28c40003a14cf8f18c74990000000000085063e00014749046180000000aa9094800196002d3121cb48c8054481a124ada1b2392a0e0fc63a62d382740008a2000063447c4a600000009704501228eac0c869e58b0000000d1141cb3f89d2cc52a90b11132ab13b822e845600000024d44cec4544c00000000005d9879800000043293056620004730810000b58442825c87239932f86198c40000002f6c0503bc0002d7c7bc000057a5f57da000000303800099100024d000000000017296547284f00000000c4247f0b0174600065c8000e1082e3d700004a2168000000000056b4ff147c00026900000001d2a5f2fdaf0c5647746630c400000003f680000003b70000000b1a0002ee00000007451a6a51c084559061ac7563241f2cdb2cd5424eb11c1b9124ad016008a20000244000000146a52400080002982a70001024f28000184973c0008af392292800000000000013
  | 28 => 0x990000000290868a0f313d1d18416b3768ca57c4e25170002c9c7d62dd19280000000001530b20e207aa4af01ec06c00028290e8542ab33298dbc000c1400000000003c20000000b4400014100ed3aa00013300119dc0000000000000c9332926a8c406ea1bda07cf1a78a5c519c464e6a352d110400000017909b14500000001820000b366451c500000000000000f802230d8042c11c9f50002cd00ea410446a5bca1605500000000005310000bb4000000322a744804881000336c35891325f04b16ccbe616b2d857a08d85f826e800000000000003b67850588000e2200026f8000c0a0000fcaa78000000411000000068e36e2bfc000baa000000069062910b11d00000fe3df0000000b8e59f97d575a3900000aec40453d02d16314e246d177000193a2d93a781404522c665100e49e24665840000138000000246c88a00033e8d7d4f2cc101d0f686ce0004d906b58826bd5532b18000c88103263400048e00000000001fb000000112e45a00019f8f385cd3232a112ae0001a714285666110340000ec2bae00016d000000014318780002ba00000002100005e124cc00014b321a03400010a01e800048200059780000003f600000005c6a34000000000000500012c199800050f16540001dc00000000000005bd99680000000001808e2400039d2eb03361003a01b151aac1f1f380001a60000002dd4ec43b355798c081e47a5c880000005ad24a1058b1e6250581c78022b471651ee443c0005b187e878a0002ec00000009ce00021581a400050eaff800000000019e19fec67039000017635e1d61c4cfd4aad66ea9fc0000000bf2a08a225d70002aace6400029aa5001c01cd62d00016f428f639162ccb25b20000000598a2d065073169a24227a33c000065700000001825fe58c06ac606c5d11632dc000000000000000000000000002740002f20000a2a0000002668000000000199020acba0002a1cb86a7b5680e54be008442a22d005431428e017c7980004da00ad99c8df39c227cd060004768000cc09812a22210a9e0006a1a8843b28b32121a0997692f4c22430626af93b5a768c0e72165f2d4da4c0000000ab186ac054663340bac1153ecac08e328f200000017fe92131d97ac00000059f27fc9c84aa0001efc0000eb077800000000068e29b000025f23880008840001141c9c2d400000007a0f224d24d1973870221325082e47f87b6196874557e70057f0000d5005847a00000000005ab09e45b43894311e6400000022d800000000000000002e60000002f3400000059a800098e8d94b281789e61470542958e2ec565cfa49da5a1b529c8e681c864c49d26640463b600030e80009bb063065566000065480000008ae5649d9022273b2838000c009cf00016e93e02a23c480018de49300033a17000001280e703d2d061
  | 29 => 0xb700027095ae02e05faf240000003a4000000000000000000000005570b1d3ce000468229031c454346000185a5e706f9e5d18c9e6587197000000030629cc0000004291d1cc680005c60000000c2a0000040d560000000cc0000ce60a2800000071f4c99aa552a90b2ea8000a9a3926668df0a946ac3258938a5059a2153020d206ec2be0000ff69750000374dca0006280ff40005e2527000000000017c22749167340002a4cf4c8324948a8d77e0005d0a5e909662c0001f412207160cba3494c68c500012ec64c0005008000808a1400011ac00000000000003502c11232b3074e3a418b2a68ac44902088059852000205a75c00000022caad4000c4f0000000fcc0004aa1a6044e07f217983846200003280006049025991135404c3952e000000063700000000000003f226f80004f8000000000006d3e49a556743a9000000186e6890f98d91938c0d435800000e0005eb80014fa5911cf0e80f4654506bad44a286d65693268f1e18a2f289ec8025bc36f04c06e24213f610c0f9e1cb35baaf990e7e12de9c300002392fca2f49900c030a00001b4c1752ab0bd9d4c2740080000000000001d512560bc00028340006cd00020c0e1469f0000b0c000cdf000299c79ec06000000002a0005f900000000003dd8ec800020900000017a4a4319c83b85c868a1c3a310000b5442a80000000005fb16940d20005b726dd93c0a221024200000cc27b3100dbac6835c13f8b3e2ef608843cb4634b447890c4c6bd85e7a6940b25aa29d00015a822e0000000000000000000000062600021c1
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c8759553480094b906b2aa69001a1fa167650d200043ec2ceca1a400087f855d9434800d0f90abb286900023de057650d200147a40aeca1a4000d6820dd543480091790eb2286900030f1d56450d201c55a40ac8a1a40058de87d8d43480018b8ebb1a86900123b21d654c92000cf4406e299240019ea87dc132480011bf06baec2900123720d75d852002c5f424eca8a40008bd849d951480050f90eb2aa2900030f1d1655452014d2e41acaa8a4000da820dd1514800d1ed0fb0aa2900032d1d361545200343f42ceca0a400087d859d941480051790eb22829000aad205645052000674106ec98a400687e851d931480010fb0a3b262900162fa10764c5200045ec20ec98a4000ce8201d931480051b90eb1a629000a3b21d644852000cf4406e690a40018ec865cd21480033d100b9a42900067aa1f70485200247c43aca98240039ea87dc930480037910e992609000f7221d324c12000ce443a649824001bca864c930480037910c9926090013b2219324c12002765bb2649824003dca764c93048007b90ec9926090013b21d9324c12000765b2a649824000ec9654c9304800179702992609000e7a20b714c120006e4996e298240009e88748530480017930690a6090003f04c5214c12002c5f43ee8b2a2000c3d75d53644400117f08bb2a88800a3d20574d8d1001c7743ee4b1a2000ce872dc1634400117f08bb2a6880162f2117654d1000477c12eca9a20038ec825d9534400d0fd0b3b286880021f6167650d100043fc2aeca1a200687c855d943440011df04bb2868800e3b2097650d100245f43ec8a1a2000c3c75d91434400117f08baec4880162f21175d891000c7d43ee0b1220008bf845d9524400b17908bb2a48800237e0d76549100246e41aeca92200387c87595524406d47908b2aa48800e9b20965549100347743ec4a9220008f7815d942440071790eb2284880023be09764c9100047dc02ec99220038dc8758d32440095ad07b2a62880123d21d654c51010d5a422ca98a2044b548550d3144043d28c8a1a628800378883724c51000763996c498a20048f48758931440031e90cb9a428800e3d21d634851002d5d426caa0220058f887595404400b970eca1a808810ece2154350110004f843a62a022002cf0764c54044001f228698a8088003e850921501100147c432e89022003ae882d8d20440071f10eb1a408800eba209634811001d75436c49022000ae8864c92044001d92c69924088003f04c9314811000df043a429022002de08748520440037c50c90a4088006f8219214811001f70432429022001ae0864852044007dc6ec90a408800b789d92148110016f03b2429022003ee0764852044001bc6e890a4088003785d12148110005f1c1a429022000be1834852044001dc6c690a4088003b858d2148110
  | 1 => 0x501baa86a801a5721d5350d5001c3e42ae9b12a000d5a30dcd5254001c9c65b1aa4a80061fa1b755095001c5f43ec8a12a000c3f75d91425400d2d90ea9284a80db8b191525095000c3e432ea992a00287c855cf615403527d0fba2a2a82870f1db74545500069c386e8a8aa0aac3c761d15154035878e9b22a2a80038d90764545500061e3a6c4a8aa000d3874dc151540030fd0dbaa82a801a5d21d515055000c3e432ea98aa01a93c845d531540051bd0fb1a62a8332cd211514c55014f2a31aa298aa00187c865d5215403527908baa42a80065e20175485500347d436e090aa000a3d8494f655019787eebba2caa00122f21171d8d4000c5f436e8a9a80c193e87dd54350187878edbaa86a00034e1c37550d406161e3b0eaa1a8016c3c75d954350001c3ca7b2a86a00122f21d6550d4002cce43aa6a1a8000d3875dc1435000717908baec4a00028f21543d894001c3f43ecaa9280018be86dd1525000187ecbba2a4a00166b21d52509401971632aa4a128000db210dc542500031790cba264a005a4f215744c94000cdc402e899280058fa86dc132500010ff0ab9ec2a001a1f21573d854000752a1643b0a80058bc841d9515000187ea83b2a2a000a1f21d655454000c5f436e8a8a80019ba80dd1515000b3690ea8a82a00062f219744c5400b49e42ae898a80cab1c8550d3150071d28c2a1a62a00123da1f614c54000c5e432e890a80c9b3a85dd1505003567108a9aa0a005ace21543541400078ca9a86a828006c7876549505003567108a92a0a00172e1d942541400b59c42a84a828000f2952509505003567108a8aa0a005ace215415414000798a8a82a828000c3d74953654c00d0fd0fbaac8980021fe1576551300043fc2ae9b12600687c855d3624c0070f90eb2aa49800e2f21d64509301951e42ac8a126003aac82591424c00b1dd0fb12849800a3720d75d853002c5f424eca8a60008bd849d9514c0050fd0fb2aa2980030f1d365545300156b40ec898a60028dc87591314c0454b90ab22629800372883724c5300076310ec498a6022e5465545314c0c972908a8a62980063721973485300353d42ec8a8260068f887591504c001e92a4992a09801b1e1d9515413031d9c422a2a8260009d8874c5504c0099b0ec98aa098003d45453154130006d4102e9b2a40058bf875d36548001b9041b9aca900028fa1375595200061fba4a8b2a40c3c5c7395165480091bd0fb9aca900035a08175d91200343fc3aebb224000de020dc5644800147d0bba2c8900030fdd7545912050e5a38ea8b2240028f687dc564480010fb0b3b2a8900022f61276551200046fc1aecaa240048dc835d954480011ef02bb2a89000a3d20576551200047bc0ae9b1a40028f4815d3634800b17d093b2a6900022f6127654d200046fc1aeca9a4004
  | 2 => 0x370549510061faa0eca12a20287c865d5425440717d0fb2284a880eaba0b64509511b716322a4a12a2058be84dd9325440117b09bb264a880a1fa1b754c9510061e326ea992a20696c87549325455bc58c8a9264a89e70f1d464d815100c3e42ae9b02a2a18bc86dd1605440117d0fb22c0a88022fa1c64581516a61fbaee8b2a82a18bf845d762504070fd0fb2aa4a08cb8b19552509411565a3b6e8a8a8206a7685d8d515040d8e8eca92a2a08172d1d9425454100792a9284a8a82a18bf845d7605040317908baec0a08030f5d254d95310052ec1ca9b2a62058be87dd1654c40187eea3a2ca988030f5d754d91310055ac0ea9b22620687e87dd5644c401878ebba2c8988021fe1576551310045fc22ecaa262028de86dcd544c4091ed0db8aa898b0a57a1f7550d316362e3b6eaa1a62d3f1441dd5434c5838b8ec3aa8698803551c47550d316978a208eaa1a6222c5c75d95434c401c3ca9b2a86988163721d6550d310068e3aec8a1a620499c87551434c47172902aa28698803551d77150d311c5cb426e2a1a62008bf845d7624c40b17908baec4988021fe1574d89310343e42ae9b12620387c87595524c46d47908b2aa49880a37a1b735493101c5e43ac8a126232a3c85591424c5a36390aa1a84988e3651c543509310247b436e2a1262029d681dd1324c4051b90cba2649888a57215744c931024e643aa49926200acc86549324c401ba621b8264988034d1d36554531554db43ee8a8a62accb476dd1514c5a1e28a7ba2a298aa72d1d87454531006ca398e8a8a62cff14531d1514c443968e9b22a2988038dd5364545310347a43ac8a8a620297487551514c4536a906aa2a298b3ad5a177354531006ca3a6e6a8a62009d48750d514c4456a90aa1aa298887651d143545310078aaa286a8a62cdd3474549514c4536a906a92a29888ad5215325453148eca3a264a8a6200f45524c9514c40117f08baec0988162f21175d81310043fc2ae9b02620687c855d3604c401d9265906c0988162fa1f74595210061ebaea9b2242008bf845d954484031f50fb82c6908033adc87058d210045fc22eca9a42058bc845d953484011f700bb2a6908063e2017654d210343f42ceca1a420087d859d943484010ff0abb2869081a1f2157650d210047dc02eca1a42018f8805d9434840917d0fb2286908030f1d76450d2102d57426caa1242058ec87595424840b958eca1a8490a12cb21543509210256b41eca98a42048f487595314844356908b2a6290a0ed5215434c52110f4a3228698a42009e48750931484055c90ca126290803e150d424c521006f1906e098a42008bf845d7604840b17908baec090803b44c730d81210051ec2c83b22a0008bf845c7635400b17908b8ec6a801a1f2147650d500061f2a0eca1aa00187e86dd543540032f
  | 3 => 0x1b2a8600a75810836550c010fd0e086caa18021f61c10d95436351f42021b2a8600a3d840436550d874bd06086caa18029760c10d95430053741021b2a8600a6d820436550dbf87eebba2caa1b7a8f61262195436952ec1cc232a86dde34419846550c01c68c3208caa1b728f612601954361e1e3b6caaa286c6c5c76d955350c0b33d09b8aa6a1b070f1d065d89430043f43ecab12860087e871956250d8787ae9b2ec2a18038d90765d854360e1f3a0cbb0a86c2c3d741976150d858b8e632ec2a18021fa1f655854369f1a20ecab0a860087e871956150db787ee832ac2a1b070f1d065d814361c3e436eab02860087e87d956050c010fd0e32ac0a18028f61641d91520045fc22e3b1aa4058bc845c7635480187ca83b286a900e1fa1b7550d5201cb7416eaa1aa40695c8754d435480147b0929ecaa136b0fdd7745954201c5f436e8a9a84c193e87dd54350987878edbaa86a10034b1cb7550d426161e3b0eaa1a8432c3c75d954350801c3ca7b2a86a10122f21d6550d4202cce43aa6a1a8400d2c75dc943509b365d0bba2a4a10dacb21153549421959642a86a928400f0d5350d52508010ff0ab9ec2a101a1f21573d85420051e42a87b028400c3d74953654c80d0fd0fbaac8990021fe1576551320353742ec8a9264068ec87591524c8010ff0aba6c09901a1f21574d81320051ec2c85b22a200a3d85903645458d87ced29ec8a8a868f61773d915150d5b408e7b22a2acab5811cf645440195ee5396c8a8ab28fa1472d915150d1ec28e5b22a2008be870cb645440117b0e196c8a8ab28fa1432d91510051ec2865b22a2a1ab6810cb645440156b02196c8a8802aea0032d91510055cc0065b22a200cbb709c3645455947d0a386c8a8a868f61470d91510045f43861b22a2008bd870c3645455947d0a186c8a88028f61430d91510055741061b22a200aad820c3645454356d02186c8a8802ad60430d91510045f43841b22a2008bd87083645455947d0a106c8a88028f61420d91510054f41841b22a200a9d83083645454356d02106c8a8802ad60420d91516c70e29cc6322a2cfab58198c6454401c38c7298c8a8b5e8f61662191516b51ec2cc0322a2a1c3c76d91545454387aebb26c6a88038794f64d8d5160e1f3a8c9b1aa2aac3d751936354555968e2326c6a88022fa1f6458d516870e29ec8b1aa2008be8719163545ab87eea322c6a88031794c7650d510065b208eca1aa20287e86dd5435458d878c9baa86a88122fa1f6450d510061fbaec8a1aa2acc3c75d91435440d2790eaa286a88168f2195450d510061e3b2a8a1aa2bac3c75193625440117d0fb22c4a88022fa1c64589511b61e326e8a92a200d3641dd1525446d47d0db22a4a8a870f1db645495100716316c8a92a2aac3c761915254401c58c9b12a4a88030f19
  | 4 => 0x40012b000611038733da5e400000076000328000000011e11d00034400000000000778ad0ac5612380000063c000594920000000021e000b600000047cf58004900000000002600050800000854790683f42e02219a2145040002600040c001343386a0f80000001b8ec0841a8520761100005404d19531c904001511362002a8000004e0048000000001c0c62e20000000002e190001460000001b8c314a4fc04101000000eb9e00005d8699f7408000000cf3e4000af8000003640000045e000540662386fc281610b42d8579e14626300004d0be0c8598ab2e4618000f600012c4716714e60831238000234000bd0e80f00000006a328848403068ecdc8d027c0006a940044000db92e0000000000d00020c000001ee00000153000000478a0000000769c1000418251c200085914210182001129d1000451089f80005b8001ac21000094800000874180002fe3fc6e2220000000c80015479c0000f000000d01b60008b45a81f2b650cd68e107a7a8b300035c000001423142e400000224184fd994000800a91bb0507a4a71213ba224cb07001445889a0c0de1f46f84134677ce79c92aa1f91210d0743c45220d1d255ce993c23c0fcf60ce000678f29c746e7f0359f100e61c4e020456048e805b20e1ed0e00034c02cd9a420000010f8bb26e1a46da2a2b222c0003419266114a39000000001892d65803d0771dc1811085413c000000751748b8bea1e18a0000f22c028001221900e20010502e218308580fd2da6e8b522724801c0108c110080f00c000200e00c000002000c000f8010000000008008000000000003004000000105400008000440004c0002c0200000008150080600c010000300000004070040601000008000080500405004030000b02c0101803004020040101403004000040300000024040000802001004010040200403010000000200002000000000500805004040000003000008010480100c000000100000014020000003801014020002b050020080200c040040000006000030000701c0100c000080104c080040300000000120040800005038000000f0840300c0400800000070100000c00000040082c00004000000040000d5917f08b8ec6aa31a1fe1573d855461c3fc2ae9b12a6c387f855d36054c0147b09296caa18028f61250d954360e1f3b483b2a8600c6f729cb6550d8d47d08396caa1b0e8f61072d954361d1ec26e3b2a86c3a5e831c76550d8d4bb0638ecaa18021fa1c21d95430043ec3843b2a86c6a3e840876550c0147b0810ecaa1b0e97a0c21d95430052ec1843b2a8600a7a800876550c014f30010ecaa18031edc270d95436351f420e1b2a86c3a3d841c36550c010fd0e106caa18021f61c20d95436351f42041b2a8600a3d840836550d874bd06106caa18029760c20d95430053b4084
  | 5 => 0x9e98b1ae36019a33232714de904104274ea02547a6845a0fe038438979393b686cae1ab446524e21c31cc2c82111847e0380000000a000f30001d60003612027673815000000000000000081e4e00c02f8240ae8000000000b1cc38c3484f8e029800000000000408391702f490d041aa000258da8000ba000000a3000084000450002185b8000008c80017e000000000023c84e8000001c60000000043284c8d20e00c2b0c882b0003908585334e6c4b21353325d4549da08c78c0000019015c7d80000000073a0f0c635878027000160d79f517c0012311b34a7f4b18fc046214668182600007c9a2000868000000003d0350003bc0001c9fe000244490000da06cd20000000006619b006264000000005a40020200019c828000005d0001be00000000000424578001281d000049800000000bd8002640003e1681628611813315c0010b8000008983b000246001048980bc5884a800000000c28e50000d800000000674798001d4604f780047c4d8dc15a3aa0005e1b202011c089d23602fc4604e0008800017300000098800000000001cb000804d480012e00000125000388c4000288000968001ea120a5a0b0929002e08732e7fc6e82d2de528000001020000000029a000da0000a40540000000000000126378090e400003a000001f9052814000de0000011d08a0000008a8cb39a67c0014f1f00004400000000000000000368000000a2310001f424e77000800254000000000001fc7d23448a648000940005950a18d2ee0c5031e222e000a39223e61305302f18e288e510007c7b9019d6018550160433000000d2353ec000278000004443c12c00064d1b1e82ac5e00000028a76
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xe16acea044b92a85e7822904543262e4c6244648d9c02340000e004aa1e00c14324001f229c008145818000016804215600341400071c200700828228a74269d0d65e41d976150c0183441a1f65585431b4c32615350d52509a141d9794f64d8d510060714e87d916354401c16539047650d5160c0f26076551435446dc2476549425454172e45a1075dc5434c5c9916851d3735453114cc52615450d514c4715149755143545310064521d5450d514c45334498549325453171f411d1524c9514c471a848650d424c521715c12554350931484353189854d43541400d4ca26152509505006dc287654942541400d4cc261515055050053c5076545315413070dc4251514c5504c0015899308174d952000568644205d365480011ca9808373595200057064420dcd65480015499308175d912000558644205d764480011e29808371591200057064c20dc56448001549930837550d200055864420dd54348001834811d56450d200060720c7459551480015899308374545200056864420dd151480014c993083764c5200053864420dd931480010e998080764c5200053264c201d931480014e191080764c52000c7225d834853048071c907650d3150110705c4255434c540440072c89858d324811000cb82598348520440072e09858d2148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa00039a114a921d5450d514c40101ad49023aac8a1a40008076a4831d16554520
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
  | 68 => 0xb4956
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
  | 85 => 0x138b
  | 86 => 0x124b
  | 87 => 0x1709
  | 88 => 0x15c9
  | 89 => 0x168b
  | 90 => 0x12cb
  | 91 => 0x1889
  | 92 => 0x1609
  | 93 => 0x180b
  | 94 => 0x130b
  | 95 => 0x1a09
  | 96 => 0x1649
  | 97 => 0x198b
  | 98 => 0x134b
  | 99 => 0xa49d5
  | 100 => 0xb49d5
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
  | 132 => 0xd0b16
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
  | 145 => 0xccb55
  | 146 => 0x154c
  | 147 => 0x140c
  | 148 => 0x18ca
  | 149 => 0x178a
  | 150 => 0x184c
  | 151 => 0x148c
  | 152 => 0x1a4a
  | 153 => 0x17ca
  | 154 => 0x19cc
  | 155 => 0x14cc
  | 156 => 0xbcb94
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
  | 192 => 0xece92
  | 193 => 0x5cd
  | 194 => 0x74c
  | 195 => 0x194c
  | 196 => 0x1a8c
  | 197 => 0x1a4d
  | 198 => 0x17cd
  | 199 => 0x18ce
  | 200 => 0x178e
  | 201 => 0x749
  | 202 => 0xb4a16
  | 203 => 0x1a9951
  | 204 => 0xb4a55
  | 205 => 0xd4b55
  | 206 => 0x5ca
  | 207 => 0x28b56
  | 208 => 0x148b56
  | 209 => 0xd0b56
  | 210 => 0x5cb55
  | 211 => 0x17cb55
  | 212 => 0x1a9952
  | 213 => 0x757d2
  | 214 => 0x74a52
  | 215 => 0x74d52
  | 216 => 0x16c296
  | 217 => 0x74b
  | 218 => 0x1a9953
  | 219 => 0x75494
  | 220 => 0x74a14
  | 221 => 0x1445d5
  | 222 => 0x74d14
  | 223 => 0x1a9954
  | 224 => 0xb4a095e
  | 225 => 0xb4a49dd
  | 226 => 0xd0b4b1e
  | 227 => 0xd4ccb5d
  | 228 => 0x745d2
  | 229 => 0x74294
  | 230 => 0xb45d5
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
  | 6 => packedAt gbK6 (177977+((h/1133+packedAt gbK6 (163248+(h % 1133)*13) 13) % 4939)*13) 13
  | 5 => packedAt gbK5 (36524+((h/195+packedAt gbK5 (34574+(h % 195)*10) 10) % 851)*11) 11
  | 4 => packedAt gbK4 (3456+((h/16+packedAt gbK4 (3360+(h % 16)*6) 6) % 58)*7) 7
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x18e381c7e38e3e3f02383ff83ff0c10f0dc1cf
  | 1 => 0xe0fc01f8fc0fc7c7ffc0383fc1f10633327933
  | 2 => 0xff0001ff1ff007f803ffc03ffe06083cc38e3c
  | 3 => 0xfffffe001ffff80003ffffc000080fc0fc0fc0
  | 4 => 0x1ffffffffc000000000ff000fff000
  | 5 => 0xffffffffe000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x840904120840a0910080d0814c0c10504c045
  | 1 => 0x60a42488440240428a40909281210612101912
  | 2 => 0x91004112091004902095002528060828430228
  | 3 => 0x22290c00162a90004b22a28080280240b80d80
  | 4 => 0x8001bcd2724700303010c4a5000efe000
  | 5 => 0xdcd271e480000000800404063185adbf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffe8feecfae8ffffffe8feecfae8ffffffe8feecfae8ffffffe8feecfae8ffffffe8feecfae8ffffffe8feecfae8ffffffe8feecfae8ffffffe8feecfae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_29532
namespace PEqualNP.Outside.L_meta_29532
open PEqualNP.Outside.L_meta_29532.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 7 zero,inputs.getD 5 zero,inputs.getD 2 zero,inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 3 zero,inputs.getD 1 zero]
def fullWord : Sig := 0xffffffffffffffffffffffe8fffffae8ffffffeefeeefeeeffffffe8feecfae8ffffffffffffffffffffffe8fffffae8ffffffeefeeefeeeffffffe8feecfae8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,16,144)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,16,144)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_29532.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.or,[6,7]⟩,⟨.and,[8,9]⟩,⟨.or,[5,6]⟩,⟨.and,[2,11]⟩,⟨.or,[1,7]⟩,⟨.or,[4,5]⟩,⟨.and,[13,14]⟩,⟨.or,[3,4]⟩,⟨.and,[0,16]⟩,⟨.or,[10,12]⟩,⟨.or,[18,15]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_29532

open PEqualNP.Outside.L_meta_29532 in
theorem PEqualNP.Outside.L_meta_29532 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
