import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_26929.Model
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


end PEqualNP.Outside.L_meta_26929.Model

namespace PEqualNP.Outside.L_meta_26929
open PEqualNP.Outside.L_meta_26929.Model
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

end PEqualNP.Outside.L_meta_26929

namespace PEqualNP.Outside.L_meta_26929
open PEqualNP.Outside.L_meta_26929.Model
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
end PEqualNP.Outside.L_meta_26929
namespace PEqualNP.Outside.L_meta_26929
open PEqualNP.Outside.L_meta_26929.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x383c0324c00b280c01b9400b1d804e7c2a348a8ab42e018a116d510334940990ebdc9100b4000086c00000800385ca460e202093012ac9b33cd810014e86983a0c3848716180000400000061c0000438009b7290876d5210eeca221dd54443bd28087795010ebca6215754c42bb28885755110af4a0215e54042bd286657950ccaeca3195d546329faa2653c544caf4a1a0de54341b7294836d52906bea6a0d714d419f2a0633d540c6dca418db54831bd2806379500c6bca790d754f219f2a4433d54886f6a090de14121bb28e817551d02bca7205754e40b7a92816c52502dca5985b54b309f2a4613d548c2eea2985d145309f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 60
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (731+((h/13+packedAt s1K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s1K4 (1760+((h/20+packedAt s1K4 (1620+(h % 20)*7) 7) % 73)*7) 7
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xe3c7c7f1fe3ff8e38e0e383f1f83ffe61339f
  | 2 => 0xf03f807fe3ffe3f03f00fc03fe3ff83e863cf3
  | 3 => 0x3fff8ffc03fc7fc000fffc7fc03fc107cf1c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x404610c15105400a182a40a0a0490d18611185
  | 2 => 0x288849228a4204502110a449121490a4862432
  | 3 => 0xa511282408c880b4400429185482a285024e18
  | 4 => 0xc40132484080c9268a46001069230309280bc0
  | 5 => 0x8224000931312493498d26200040430d5b000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_26929
namespace PEqualNP.Outside.L_meta_26929
open PEqualNP.Outside.L_meta_26929.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x460000000000000000e8a0c0130000a922200013800080f03105c000561001500001110000ca10000028003800000008251600280520000c0e00d80004c0000000e000000a1a2400c161a7c00000000001e240830304141800000000000c002ff43df43fe43fd43fc43dc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x3b584b0042505607370c1d021343511c2c3e0d321e2b093546183922085730004c190e1703403400385400001b00590100002125002d44002a00004f044d4a0b4e00000027162e000f2824001553523d3100005a49410a122f05363f1f45293355000611231a203a263c1448104700000402f001c2b7080008802680842408011005c186086440d0f5d52d0ebca721db94843b6a9087765110eeaa221de94043bca80875e5410f3ca821f394843aea9087cd5210e9aa421f594443eaa8887da5010fb2a021d794e42aea9c859c4390abea6a15714d42af298855d5310b3886215d94442baa88857a5010af2a0215795332ae2a6655d538ca7ea8994f15132cfaa2655e544cab8a89967151328e2a265cf524cb9c84997350932af298659c43d06f4a1a0de54341af29c835d53906bea6a0d714d41ce21a833e548c67aa918d794f21aea9e437b50486f0a090cf950219eaa0435e53086baa610de94021bca80439c43d02eca3a05d54740af29c815d53902bea6a05714d40ce21a813e548c27aa9185794f20aea9e417751482e8a2904f950209eaa0415e53082baa6105d94420baa88413e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x10a216c0018ea18700a80680b804948008900027a432c980900c22093455294443d15495110f495294043d25495010f515154043a35884390b144354442c610d5010a1e6495132c3588544cb166115132c5584544cb1a6015132c6580544cb0c549093293195424ca8d6210f41c610d50d068d6210d418719153c868d6210f40c510d51d028d6210d408719153c83615244010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x28461815896115132c12c4b00a89961161580544ca84b9086a8683415c84354740
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
  | 5 => packedAt s2K5 (802+((h/14+packedAt s2K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s2K4 (2667+((h/30+packedAt s2K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s2K3 (990+((h/8+packedAt s2K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s2K2 (248+((h/1+packedAt s2K2 (245+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x878f0f1fc7ffc7e38f1c0c70fc7fc3fe3133cf
  | 1 => 0xf80ff01ff8fff8fc0fe00f80ff8ffc3ec23cf3
  | 3 => 0xfffe3ff0fff1ff0000fff1ff1ffc103cf3c
  | 4 => 0xfff00003fff0001ffffff0001ffe0001fc0fc0
  | 5 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xd0118228544488028505241424124294311145
  | 1 => 0x5222850a28901140a2248884884a828c22492
  | 3 => 0x22444401002200291000812211211101004a28
  | 4 => 0x3300669a1223924da348e0021e48198d540fc0
  | 5 => 0x4408880024cc24924c930e4c80002230abb000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffff88ee88ee88ffffff88ee88ee88ffffff88ee88ee88ffffff88ee88ee88ffffff88ee88ee88ffffff88ee88ee88ffffff88ee88ee88ffffff88ee88ee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_26929
namespace PEqualNP.Outside.L_meta_26929
open PEqualNP.Outside.L_meta_26929.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5a2003c000000098a4e00217381401d068c4070024c004c64f805044681005921b0018aa9240001e0094014008550034ac602400071000001040601023080183003ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x50410c3c2622511605174a4e0030000018363e0014000f1c00064500000059001e1349561d4d4411343927000809073f2e0d4b101a470058433a12423d33570b0025000354382b002c37400e2f002d002101310a0252483b4f2835040019321b1f2a5355234c240015002029465a1f0800103061c004000400d043c911102c680041c21c0e1c0210b3e5390e7aa521db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed94443daa8887ba5010f72a021cf94f429eaa4855f5350ab8a6a167d4d429e29a859c5350a38a6a16bd49429f2a0853f54cca78a9994f952329eaa4659c438cb5a85194fd51329e2a265ad424ca7ca8194f55032ce2186576510caeaa2195e94032bca80655e53906baa720e710f31bd286637950cc67ca918cf552319faa2633c544c7388698cf953219eaa6437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53902baa7206710f30bb28e617551cc27ca9184f552309faa2613c544c33886984f953209eaa6417751482e8a2904f950209eaa0415e53082baa6105d94420baa88413e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xb9802a00099ca1640280819e88cc0002c11a0143a400a4821018c500f255294443c95495110f295294043ca5495010f315154043c35885350b166114d42c55845350b1a6014d42c65805350a8d6210e32a318d428ca2c655093287594430cb144354432c610d500ca8d6210f31c610d50cc68d6210d318718d54c868d6210f30c510d51cc28d6210d308718d54c83615244010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x10000084c001815896114d42c12c4b00a6a1611615805350a84b9086a8663415c84354730
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
  | 3 => packedAt s3K3 (990+((h/8+packedAt s3K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (249+((h/1+packedAt s3K2 (245+(h % 1)*4) 4) % 10)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x878f1ffc3c7fc7e38f1c0e3fc70fc3fe30f4cf
  | 1 => 0xf80fe3ffc07ff8fc0fe00fc7f80ffc3ec338f3
  | 2 => 0xffc3fff8fff1ff0000ff8fff1ffc103cf3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xb011888490a288018504a20941224194305445
  | 1 => 0x32251090945010c0a21444288449828c12892
  | 2 => 0x44440212200800321002089012812201028128
  | 4 => 0x110049a088019244a3486000e468088c540ec0
  | 5 => 0x66089203326e249b4c938f2400803331abf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_26929
namespace PEqualNP.Outside.L_meta_26929
open PEqualNP.Outside.L_meta_26929.Model
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
end PEqualNP.Outside.L_meta_26929
namespace PEqualNP.Outside.L_meta_26929
open PEqualNP.Outside.L_meta_26929.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x42bc6802a94499380032e008002c4c04f172274d18048c70c4e00a16143cfa254905a8561d4885a00d85260090300108000018495c14c0670402c0000004ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x302600351a09285171d8d8000a800004a002008a00120007800000109e000000000000c8000064000010e00089103a4d070c4ae74011f00e002717c000026000f64631000b272169c4c000200bcce0000204000000000000007800000000000760a001480000001501a3600000d200000e8106b1800000001300012000800006002c0004e3f24000000000058240000000840000000fc0000080f02a2088c561c298e46429001940a2200000000000000fa0b318600000001dc500000000f20041140dc5d0016c0000369bcbc000000000141e9e8b43e128e0e0610f0dc00350000000000000000000000000830000068561085cea0000000007300000000000210001a3300000001617000000d80096472a8000c86000cc001f0094400003f80000430000000008100402020040403000081000000000e02000000004000040604008040002018080000000040202018000800000000401b7294876d5290ebca7215754e42cf29c859d5390a7ca5214f546429ea84855e5310abaa6215d94442baa88857a5010af2a0216794c42cea98853e5210b5ca4216d944429ea8885b55110a6aa2216e940429ea8085b95010a72a0214f953329eaa6659e54ccb3aa9996790b32ce216655d538cb5885194fd51329e2a265ac424cb3ea8996715132e7a9265cf424cb3c84996710932e6212658c424cabca6194f94b41cf996839d32d067aa1a0cf552419e292839f325073a64a0edd45419fa82833e541067ca918cf552319f2a0633d540c6dca418db54831bd2806379500c67ea990cf15321af29e435d53c879a6590cf952219eaa443b5418867ea890cf15121e699243b5414867ca810cf55021af298435d53086f4a010de540219f296819f32d033a65a04f547409eaa4813c525033e64a0674c9409fa8a81bb505027ca8204f952309eaa4613e540c27aa8185b94830b6a906176510c2eaa2184fd53209e2a6415e53c82baa790734cb209f2a4413d548837281104fd51209e2a241cd324837280904f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa88857d4d10ae29a213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x80e0001699000001a00005803ea9300007108a048c015024422f28a47803c3400c2eb091612951180c018310e9d02e500c000360040026742ab48060118a241000808101820200182a358e5210b165354442c554d5110b315194042c694d5010b195354042cc9455010b315154042a558442cca996010b32a9584428caa96010a32a9584424caa96010932a3993524ca1e6590932a398a424ca1e6510932a5584424ca996010932b1584424cac96010932a3994424cb0e6510932e1984424ca8d6110932e1584424ca856110932e2980424ca8d6010932e2580424ca8960109328e580525070c524c9418e58054c870c544cb21c315132486346550521e14c941486356114940c314932502356115320c315132c830c544c9208e195404838932501208b189544424d6214d10d454d10043615244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x204618400200a001c0c3a05866010932d04c2b00849968161580424ca84b80a499283425c0544cb21c08ca9928290d05711493250282b88a899641821953250120
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
  | 4 => packedAt s5K4 (4077+((h/45+packedAt s5K4 (3672+(h % 45)*9) 9) % 261)*9) 9
  | 3 => packedAt s5K3 (2012+((h/16+packedAt s5K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f878fc7f8fe3f1c71f1c1e3f0fe3f0d34cf
  | 1 => 0x1fc7f80ff8ff1fc7e07e3e01fc7f0fc7323b33
  | 2 => 0xe007fff3ff001ff8ff803ffe3f800ff8c3cc3c
  | 3 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 4 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4300a010422108400810504840904222051045
  | 1 => 0x84210220904030084022221084240504122112
  | 2 => 0x921101001244012480048429022890404c28
  | 3 => 0x890554a24900492b5448024324aa090e80e80
  | 4 => 0xd124660836e49924da793939000cc126bfb000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_26929
namespace PEqualNP.Outside.L_meta_26929
open PEqualNP.Outside.L_meta_26929.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826004fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007ff204c003ff1026001ff0813000ffe2098007fe104c003fd0826001ff04130007feca90002ff654801dff32a4006bf99520007faca90002fd654801dfe32a4006bf19520007fec890002ff644801bff3224005bf99120007fac890002fd644801bfe3224005bf19120077fea890037fe5448001feaa2400dff15120007fec690002ff6348019ff31a4004bf98d20007fac690002fd6348019fe31a4004bf18d20077fea690033fe5348001fea9a400cff14d2006ffe8690033fe4348001fea1a400cff10d2000dfec49000fff5248007ff2924003ff5492001ff8a49000fff4248007ff2124003ff5092001ff8849000fff3248007ff1924003fb8c92001ffa6490003ed3248007fe1924000ffd8520005fec29002ffe61480057f30a4000ff5852005ff8c29000afc614801dffa8a400bff94520007faa29002ffc514801bffa0a400bff90520007fa829002ffc4148019ff98a400bff8c520007fa629002ffc3148007ff90a4003fbc852001ffc429000ffd2148001f690a4003ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001fe9012000ffa8090003f94048003fe2024001ffcc12000ffc6090007fd3048003fe1824001ffc812001ff64090007fe2048003f71024001ff0812000fd84090007f82048003ff8824001ff8412000ff42090007fc1048001ffb2a2000bfd9510057fcca8801afe6544001feb2a2000bf59510057f8ca8801afc6544001ffb222000bfd911004ffcc888016fe6444001feb222000bf5911004ff8c888016fc6444015ffaa22009ff95110007faa888027fc5444001ffb1a2000bfd8d10047fcc688012fe6344001feb1a2000bf58d10047f8c688012fc6344015ffa9a2008ff94d10007faa688023fc5344013ffa1a2008ff90d10007fa8688023fc4344001ffb122000bfd891003ffcc48800efe6244001feb122000bf5891003ff8c48800efc6244015ffa922007ff94910007faa48801ffc5244013ffa122007ff90910007fa848801ffc4244011ff9922007ff8c910007fa648801ffc32440037fb0a2002ffd4510017fca28800bfd5144005fe28a2002ffd0510017fc828800bfd4144005fe20a2002ffcc510017fc628800bf63144005fe98a2000fd4c510017f8628800bff2144005ff10a2002fd88510017fa4288003f52144005fe10a2001bfd811000ffea088007fe5044003fea822001ff1411000ffe8088007fe4044003fea022001ff1011000ffe6088007fe3044003fd1822001ff4c110007f26088007fc3044003ff9022001ff8811000ff44088007fd2044001fc9022001ff0811000ffe208800bfb1044003ff0822001fd8411000ff82088007f41044003fc0822001fc04110
  | 1 => 0xffe4154001fea0aa017ff105500cffe62a805ffe3154001fe98aa017ff0c5500c7fe42a805ffe2154001fe90aa017ff0855000dfec0a8007ff505400dfda82a001ff9415000efca0a8007fc5054003be282a001fe1415000ffe80a8007fe4054003fd202a001ff1015000ffe60a8007fe3054003fd182a001ff0c15000ffe40a8007fe2054003fe102a001ffc415000ffc20a8007fc1054001ffb2a8000bfd95400b7fccaa001afe6550001feb2a8000bf595400b7f8caa001afc65500037fb228005ffd51400b77ea8a0017fe545000bfeaa28005ff1514002f78a8a0003ff63500017fb1a8015ff98d40025fcc6a0003fd635002bfe31a8004bf18d400b7fea6a0057fe5350001fea9a8015ff14d4002ffe86a0017bf435000bff21a8005ff50d400077a86a0017fc4350001ffb128000bfd89400a7fcc4a000efe6250001feb128014ff1894001df8c4a005bff5250029ff2928000ff549400a7f8a4a0017ff425000bdfa128005ff9094002ffa84a0003bd425000bfe2128015ffcc9400a7fc64a0003fd3250029fe1928000ffd8540005fec2a004ffe61500057f30a8000ff5854009ff8c2a000afc615002dffa8a8013ff94540007faa2a004ffc515000bffa0a8005efd054002ffc82a0017fd4150001dea0a8005ff105400affe62a004ffe3150001fe98a8013ff0c5400a7fe42a004ffe2150001fe90a8013ff0854000dfec0a0007ff5050003ff2828001fe9414000ffaa0a0003f95050003fe2828001ffd014002ff680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ff860a0007ff2050003ff1028001fe8814000ff840a0007ff1050003ff0828001ff04140007feca98002ff654c025ff32a6006bf99530007faca98002fd654c025fe32a6006bf19530007fec898002ff644c023ff3226005bf99130007fac898002fd644c023fe3226005bf19130097fea898047fe544c001feaa26011ff1513000dfec698013ff534c009ff29a6004ff54d30027f8a698013ff434c009ff21a6004ff50d30027f88698003ff624c0017fb126010ff9893001dfcc498003fd624c021fe3126003bf18930097fea498043fe524c001fea926010ff1493008ffe8498043fe424c001fea126010ff10930027fe6498013df324c009ff1926004ff4c930007ba6498013fc324c001ffb0a6000bfd853007ffcc29800afe614c001feb0a600fff18530015f8c29804bff514c01fff28a6000ff5453007ff8a298047ff414c01fff20a6000ff5053007ff88298013ff314c009ef98a6004ff8c530027fa6298003dd314c009fe18a6010ffc853007ffc4298003fd214c01ffe10a6001bfd813000ffea098007fe504c003fd2826001ff54130007f2a098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9
  | 2 => 0x31107fca498803fd524c441fe2926221ffd0931107fc8498803fd424c441fe2126204ffcc931027be6498813fe324c409fe9926200f74c931027f8649880aff614c405ffa8a6202ff94531017eca29880bfd514c401faa8a6202ff14531017fe829880bfe414c405fea0a6202ff10531017fe6298813f7314c405ff18a6202f78c531017f8629880bdc314c405fa18a6202ffc8531017fc429880bfc214c401ffb026200bfd81310fffcc098806fe604c401feb02621fff1813100df8c09888bff504c43fff282621fff1413110ffe809887ffe404c43ffe2026204ffcc131027be6098813fe304c409fe1826220ffc81310fffc409887ffc204c405ff8826202fdc4131017fc209880bfc104c401ffb2a4200bfd95210f7fcca9081afe6548401feb2a4200bf595210f7f8ca9081afc6548401ffb224200bfd91210effcc890816fe6448401feb224200bf591210eff8c890816fc644843dffaa2421dff95121007faa890877fc5448401ffb1a4200bfd8d210e7fcc690812fe6348401feb1a4200bf58d210e7f8c690812fc634843dffa9a421cff94d21007faa690873fc534843bffa1a421cff90d21007fa8690873fc43484057fb124203ffd492101ffca49080ffd5248407fe2924203ffd092101ffc849080ffd4248407fe2124203ffcc92101ffc649080fee3248407fe9924200fb4c92101ff8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017ec829080bfd4148401faa0a4202ff10521017fe629080bfe3148405fe98a4202ff0c521017fe429080ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843dffa82421bff941210dff8a090877ff4048437ff202421bff101210e7fe609086ffe3048437fe1824203ffc812101fde409080ffe2048407fe1024202ffc4121017ee209080bfe1048405fe0824201bfd9550007fec8a8002ff6454035ff322a005bf99150007fac8a806bfc645400b7e322a006ffd5150037fca8a806b7e545400dfeaa2a006ff15150036f8a8a8003ff63540017fb1aa019ff98d50025fcc6a8003fd6354033fe31aa004bf18d50037fea6a801b7f535400dff29aa006ff54d50006faa6a801bfc5354035ffa1aa019ff90d50007fa86a8067fc4354001ffb12a000bfd89500c7fcc4a800efe6254001feb12a018ff1895001df8c4a801bff525400dbfa92a006ff94950037faa4a80037d525400dfe292a01affd09500c7fc84a8003fd4254031fe212a019ffcc9500c7fc64a8003fd3254031fe192a000ffd8550005fec2a805ffe61540057f30aa000ff585500bff8c2a800afc615400dffa8aa006dfd4550037fca2a801bfd5154001bea8aa006ff145500d7fe82a805
  | 3 => 0xe322a205bf19151037fea8a881bfe5454455bf2a2a206ff55151037f8a8a881b7c5454401ffb1aa200bfd8d5114ffcc6a8812fe6354401feb1aa229ff18d51025f8c6a881bff535440dbfa9aa206ff94d51037faa6a88037d535440dfe29aa22affd0d5114ffc86a8803fd4354453fe21aa200ffd8951005fec4a88a3fe62544077f312a200ff58951147f8c4a880efc625440dffa92a206dfd4951037fca4a881bfd5254401bea92a206ff14951157fe84a88a3fe4254401fea12a228ff1095114ffe64a88a3fe3254401fe992a228ff0c951015fec2a880bff515440dfba8aa202ff94551016fca2a880bfc5154405be28aa202fd14551017fe82a880bfe4154405fb20aa202ff10551017fe62a880bfe3154405fb18aa202ff0c551017fe42a880bfe2154405fe10aa200ffd8151005fec0a889ffe60544037f302a200ff5815113ff8c0a8806fc605440dffa82a206dfd4151037fca0a881bfc5054455ffa02a227ff9015113ff880a88a7ff305444fff182a227ff0c151147fe40a889ffe205444ffe102a202ffc4151017fc20a880bfc1054401ffb2a8200bfd9541137fccaa081afe6550401feb2a8200bf59541137f8caa081afc65504057fb228205ffd51411377ea8a0817fe545040bfeaa28205ff1514102f78a8a0803ff63504017fb1a8225ff98d41025fcc6a0803fd635044bfe31a8204bf18d41137fea6a0897fe5350401fea9a8225ff14d4102ffe86a0817bf435040bff21a8205ff50d410077a86a0817fc4350401ffb128200bfd8941127fcc4a080efe6250401feb128224ff1894101df8c4a089bff5250449ff2928200ff54941127f8a4a0817ff425040bdfa128205ff9094102ffa84a0803bd425040bfe2128225ffcc941127fc64a0803fd3250449fe1928202bfd8541017fea2a080bfe5150405fb28a8202ff54541007eaa2a080bfc5150405ffa0a8205fdd0541017fc82a080bbe4150405fe20a8202ef10541017e882a080bff3150405ff18a8202ff0c541017fe42a080bfe2150405fb10a8202ff08541007fec0a0802ff6050447ff3028201bf98141007fac0a088ffc60504037e3028226ffd414111ffca0a088ffc505040bffa028205efd014102ffc80a0817fc405044bff9828223ff8c14111ff860a0893ff2050447ff1028223ff08141017fe20a080bfe1050405fe0828200ffd9531005feca9888bfe654c40d7f32a6200ff59531005faca9888bfc654c40d7e32a6200ffd9131005fec898887fe644c40b7f3226200ff59131005fac898887fc644c40b7e3226222ffd513110ffca898803fd544c443fe2a26202bfd8d31027fea698813fe534c409fea9a6204ff14d31027fe8698813fe434c409fea1a6204ff10d31007fec498802ff624c441ff3126203bf98931007fac498883fc624c4077e3126222ffd49
  | 4 => 0xd7ff3154869ff18aa434ff0c55201ffe42a900ffe2154807fe10aa400ffd8152005fec0a90cffe60548037f302a400ff5815219ff8c0a9006fc605480dffa82a406dfd4152037fca0a901bfc505486dffa02a433ff9015219ff880a90d7ff3054867ff182a433ff0c15201ffe40a900ffe2054807fe102a434ffc415219ffc20a90cffc1054801ffb2a8400bfd9542197fccaa101afe6550801feb2a8400bf59542197f8caa101afc65508077fb228405ffd514202ffca8a1017fd545080bfe2a28400ffd8d42005fec6a10c7fe63508097f31a8400ff58d4218ff8c6a1012fc6350865ffa9a8431ff94d42007faa6a10c7fc535080bffa1a8405ff90d4202ffa86a1017fc43508077fb128403ffd494201ffca4a100fee5250807fea928400fb5494201ff8a4a100fff425080bf7a128403ff9094201f7c84a100ffc4250807de2128403fb1094201ffe64a100ffe3250807fe1928400ffd8542005fec2a10c3fe61508057f30a8400ff58542187f8c2a100afc6150865ffa8a8430ff94542187f8a2a1017ff415080bdfa0a8405ff9054202ff882a10c7ff3150861ff18a8430ff0c54201ffe42a100ffe2150807fe10a8400ffd8142005fec0a10bffe60508037f3028400ff5814217ff8c0a1006fc6050865ffa82842fff9414217ff8a0a1017ff405080bdfa028405ff9014202ff880a10c7ff305085fff182842fff0c14201ffe40a100ffe2050807fe1028430ffc414217ffc20a10bffc1050801ffb2a6400bfd9532177fcca9901afe654c801feb2a6400bf59532177f8ca9901afc654c801ffb226400bfd913216ffcc899016fe644c801feb226400bf5913216ff8c899016fc644c85dffaa2642dff95132007faa8990b7fc544c8077fb1a6404ffd4d32177bea699013fe534c809fea9a6404ff14d32027b8a699013ff434c809ff21a6404f790d32027fa8699003dd434c809fe21a6403bfd893201ffea49900ffe524c807f72926403ff54932007daa49900ffc524c807ffa12642dfbd093201ffc849900ffd424c807fe2126403fb1093201ffe6499013ef324c807ff1926403f78c93201ff8649900fdc324c807f61926400ffd8532005fec2990b3fe614c8057f30a6400ff58532167f8c29900afc614c85dffa8a642cff94532167f8a2990b7ff414c859ff20a642cff10532027fe6299013df314c809ff18a6404ff0c53201ffe429900fef214c807ff10a6403ff08532007fec099002ff604c857ff3026401bf98132007fac0990affc604c8037e302642effd413215ffca0990affc504c85bffa02642bff9013215ff88099013ff304c809ef9826404ff8c132027f8609900fff204c807f79026403ff8813201ff840990b3ff104c857ff082642bff04132015fecaa8803ff64544017fb22a22aff9915102dfcc8a8803fd6454455f
  | 5 => 0xd53027bc86a9813fc4354c01ffb12a600bfd89531effcc4a980efe6254c01feb12a63dff1895301df8c4a981bff5254c0dff292a606ff149531f7fe84a98f7fe4254c7bfe212a604ffcc953027fc64a9813fc3254c01ffb0aa600bfd85531e7fcc2a980afe6154c01feb0aa63cff18553015f8c2a981bff5154c0dbfa8aa606ff94553037f8a2a98fbff4154c79ff20aa63cff10553027fe62a9813fe3154c09fe18aa63dffc85531e7fc42a98f3fc2154c01ffb02a600bfd81531dffcc0a9806fe6054c01feb02a63bff1815300df8c0a981bff5054c0dbfa82a606ff94153037f8a0a98fbff4054c77ff202a63bff10153027fe60a9813fe3054c09fe182a63dffc81531dffc40a98effc2054c79ff882a63bff841531dff820a9803ff6550c017fb2a8600dfd9543004fecaa18ebfe6550c0d7f32a8600ff59543005facaa18ebfc6550c0d7e32a8600df19543034f8caa1812ff6450c0bffaa28605ff9514302f7ca8a1817fd5450c01deaa28605ff15143025fec6a1813ff5350c09ff29a8604f794d43027faa6a1803dd5350c09fe29a8604ffd0d4302fbe86a1813fe4350c09df21a8604ff10d430277886a1813dc4350c01ffb128600bfd89431cffcc4a180efe6250c01feb128639ff1894301df8c4a18ebff5250c73ff2928639ff1494302ffe84a1817fe4250c73df2128605ff1094302f7884a1813ff3250c09ef9928604ff8c943027f864a1803ff6150c017fb0a8638ff98543015fcc2a1803fd6150c71fe30a8602bf185431d7fea2a18e3fe5150c71fe28a8605ffd054302f7e82a1817fe4150c0bfe20a8604ffcc543027fc62a1813fc3150c73ff90a8638ff885431c7f842a1803ff6050c017fb028637ff9814300dfcc0a1803fd6050c6ffe3028601bf181431d7fea0a18dffe5050c6ffe2828605ffd014302f7e80a1817fe4050c0bfe2028604ffcc143027fc60a1813fc3050c73ff9028637ff881431bff840a18e3ff1050c6fff0828637ff0414301dfecaa9003ff64548017fb22a400efd91520057ec8a90dbfe645480b7f322a400ff591521b7f8c8a9016fc6454801de322a405af19152037fea8a901b7f545480dff2a2a406ff55152006faa8a901bfc5454801ffb1aa400bfd8d521affcc6a9012fe6354801feb1aa435ff18d52025f8c6a901bff535480dff29aa435df94d52037faa6a901bfc535480dbe29aa436ffd0d521affc86a9003fd435486bfe21aa403bfd895201ffea4a901bef5254807ff292a403df9495201ff8a4a900f7c5254807f6292a403ffd095201ffc84a900fee4254807fe212a403ffcc95201ffc64a900fee3254807fe192a400ffd8552005fec2a90d3fe61548057f30aa400ff585521a7f8c2a900afc615480dffa8aa406dfd4552037fca2a901bfc515486dffa0aa434ff905521a7f882a9
  | 6 => 0x1901200c0000300e00003800022040038230000040000103604c0a8010000000000000a01c1480100a000038090000180a800026000028000000080200a00a0080300c0000501101100a0140881500a0000000b0000340002200601c080040000600000000a008000050ba048020290000001100100401c0280400000c0c02400c0000280500c0a80380f062000018000000080180001201008007020000000180300100000b0200240081500c0040000201400c0900600000002803032008000000060080480a000010080000000880b0050040580182f012084050000021e0008080240080203a00204400002000028000000060040a0010040000000302c0000100000001400007002010000030020000700100800403800000000020040000000200201c0040000601e0700d0060300200700001801c0101b00e0000800e0060c0030170200100380000e070098150000000180700a01c090050020100c001000000198120000000001402600c000010060040480101201c0000102a00c038030000080000503c0240300e00a0001000401604c0100b010024000000140f0000080120000682b002000030020000041200301205004000028008008030100480000801c0000400600804003002008000028000040400003303e008000000000240000203e010008100000000381e000018030230060240400600a0040282204200c0b80e0520000d000004004030090000080a0070340240d8080980440400401c07c01816ff655500b7fb22a805ffd51540377ea8aa017fe545500bbf2a2a805ff1515402ef8a8aa017bc5455001ffb1aa800bfd8d54217fcc6aa012fe6355001feb1aa842ff18d54025f8c6aa01bff535500dff29aa806ff14d5402ffe86aa017bf435500bff21aa805ff10d54007fec4aa002ff6255083ff312a803bf98954007fac4aa107fc62550077e312a806ffd4954036fea4aa01bfe525500dfe292a805ffd095402ffc84aa017fc4255085ff992a841ff8c95420ff864aa003ff61550017fb0aa840ff98554015fcc2aa003fd6155081fe30aa802bf18554037fea2aa01bfe515500dfe28aa805ffd055402ffc82aa017fc4155085ff98aa840ff8c554207f862aa107ff2155081ff10aa840ff08554007fec0aa002ff605507fff302a801bf98154007fac0aa0fffc60550037e302a806ffd4154037fca0aa01bfc505500bffa02a805ff9015402ff880aa10bff305507fff182a83fff0c15420ffe40aa0fffe205507ffe102a840ffc41541fffc20aa0fffc10550097fb2aa600ffd9153005fec8a98fbfe6454c0b7f322a600ff591531f7f8c8a9816fc6454c0dffaa2a606ff95153037faa8a981bfc5454c097fb1aa604ffd4d53037bea6a9813fe5354c09bf29aa604ff14d53026f8a6a9813dc5354c09ffa1aa604ff9
  | 7 => 0x4e83692da950000098000dd9db2c71e000000027a1a2a848000000818150000001bc04c00021ea8b0000001d980f0399a9ab08cd9638000e90002bf8000551c2ac62bd9a20390e080000013082e0fb82b9fd8bd80017e08d2638ee1b91ba2a80001acaa10001d118f26f00000000028984f1a001419c00015b8000000e29d914c1a61d5984a7713199aa860ac0001819102760000b60b78001cd1b4000264aab2348000002c19b7a3300b00026280000003b8d98de00008b91680000020a00000000007aabe22999c8b59c71e314d25b27200000028d06a1d224a1861900a30002870000002ac8b2a9ea3609216f8f48db1331dc16827f8001981241aa80026200025597f02489f11193f0120048a696025727c14f2259fe85a00003e2700000d50fa0c108e0d019127c8002b1ab429029805d0000000002520472098cf8000000000b82080002800002a4800000000280ac0299a168000000000982788f000025427d8e624b0720159719690000d622600000000000018282811a80000000006f04f9199b116e0c78230040000002048d194000029d800042924a4c192a652878000001c48dc8e196a80000018e1630dea358001190000002338000000002838001bb1468002102960319c68ec95c25303d885aa29158001700f880000020a8969220f68000001200000370000000002a788f02589593e273a308dbabd00025d922a7e9790cb8000688a88000870aaa4d85a80000000016680ca988002128000100a2138a3f0000d305da7511b183a5e85380a00014e1c61e21b29bca3ca131a499e1baaba00005297300014f8ba147a4f8002bb1ad07c89102a01c8772c323f97a86828a9d69b49e8a402821f78f081f9498840220522231339ca8e01ea9f714aac48c01890a517c91717d9b889015e8b38a0a5887e1a187487684e976a2d09c1cb02696c00000214580000000000000016a1772c914919e8432b32312c38cb0ad800097000288a238590002a31f501e18800000005410c0a59e3a971b710a8001df8ed800069a682408bf186a7b2b910e8660b98dd2ae0888879050179cf22d82c2af8a724798d9530000e38be0018000000ceac814d8000808ef00006a9a71579c081b0ec15fa941a81f686b80020f1d094b0ff8d79be8000938118f600022080e82b0000d69aa0729d72b5ab685000011f2a421200000017b0d4a050f2160a608ac9a69068000131c886e14e9e49cf8001e800000000000002f8ca9a42481ab113917800277aa225289a86027e2bc063143a598000030040940a0050020140200b0280a4088070080b4030010040102e8000100040080701600000002000078098000000a40401100602c0880b00a000008090060140f008020000018230000a83d81c00000c04816018000008000620000080000400407000000000050
  | 8 => 0xf8d280010f9a8a251de9f42c29670002bf1089a300001913980000015904080003a03a9898002aaa240a1a2fa880aba1115624205b95b1dc9360af00fa440510261d390905710483b246199062a699d50ee89ba291510f315d24925a0bd0dc1321840001e28e3211a0428c972932877a0e94801dac983c127203a6599b90726f84d9a124a9b6800136a200478e50000979d825b8000c38708002448002300001c399700011e8f90c9aac28d86428180005e9ed0c08658ba9341078000ed19d00000018595500000000019500014080002a8a39fe000127a2c00000016498a84693a837a3a2088000002978229f08010001872c425aa568a00000051b99da8f7a0d0008000002a880019207388d91219180029103e9e400000015d9850eb93f9a5a9211d00000020b2c22549d01961dd0f59821af9660c51008829958e89e607c29381292c03114626722a0e7a5785c0b700004b00b935238a0f9f81932508000c1a1c8610000000002b61be175857a729722062aa04e0eaa8f12c95991f9ec8e72b724c8758c926b1e524d0000001f3a96a5c0030b892a9d892a1519c984cab82610e4aa1864a5122e1cc29b1b818100d96b08c2431ca0252bc80023b99d8000001ee8d88000ae0c720c805a7180024e09a0b50f70f29041998480c49ec10b01a2aeac11801d60172090001e180003807b1ae00016f0b49b50a60cc8e992e21080001f05619404b8a821f8691bf12b1d32711dd8c626189994117087d29c80020309509488a09615000011a000010a029c0000275a7680012e92b95f20b9312582b200880023d9bb96da4992095e13785c9738001b0000061a07a5389b000023858a342001bda8bacb2a397d215a41a3687ba4f11ba3d1f91ef040029ab3830a148762022aba071281c91df1978da94283c89c8fe8b927f0b20162828028a41fc23715284d2661c21711141261fa8cc01819f23e1b3a0196b9f88f515a07d90d1a09288710000c310100005307807f8d3a190bba0126c1189ee219a4113499090e22ba4298d0000002af2b28e410ba1b1ae8f116c80009182f23e9f023292517c22686c94a03589e08c86b29a059a8103210018a00e0c283407308902008817624516522828fab00168839ac178811161109838aad9ce259246a0c0548d71f11b19d19d4a9f1d2a3806ea458bb15385586d1618b19212a92ca180a4baa607a10810a05f09326a1380e5ac526780004a080165aa591c0df035000051a1c08b02181392196294b8338271938aa144000285a5514cac080c1f2948ab885e09082da4702c8072a998b80688f8d9045116237842155910a9b9a7a1d21419a26d92f1878d08fc0c20792a716d0fb0b021381aa8e103274a6e02400d0b30ef98880825c9b592d18c1db87029a80000013d9f48000fd00013b0000002890001b3000154a
  | 9 => 0x2a506d8348ae803a63264032a22a3b11c9290001fb0d58000001231cb8002791ea0fa9b20d20000000458208000001cc8000000001620062c5a3181ea0d80003f0001239a912980000000000023500013ca9190c80000006680025f83018c8000079641ff2a68ad0a7a17a9c0000000000000000000290278e8130217135ab500011d9c50000000ea0002270001e697409f8f39bd2a026e9eb9ef9a38411c1058292879800009200882000018a841c18000001581c7a3928c1128990ca25e0a916e9d7a949e0850901a90a8a0ff29e0a2a741c5894049a3c17ea799370b69522a08c81c8060914a2c8f9967a2aac68dfa5f1e99c309d2851988bea6b89d9ff8898cd156a868440639750438bc9fb9472b121b8b41d40001430a4a9d1130000001949150e686f8000000000d800000022e8000928001fa0da1b612680026a9e580009e800056a992278f806c2691f99eb01490d9e78830ab2c893babea7a8671cda2f20e0211fc9b09e10d429f93916895407f0331968f42161f20489f595081995a97f8c6a2b02e8ce15c89887e85b0e20862ca9de2501c41f18852930c5836158a7b90f04a84182d000268a5d2708002c78a9a731059a52059022ad000179a068b11418eb0848001f60cf0bc00000017800a9e91180812439aba24a288fe06212f8719028a113d21a97ba6d1f32ba94491e221074078a6c9ada5193a2b98e12b497799b260169a7d10618e875044a1d84918b21a21e00015728e9038af88e9ed8f188a974a95a66abba21886a398d11112150001af23206500001d01c00000000013c18303d0000bfa3aa222830fca488c4067ab79421fd2781ce9e70461da2188fd828a1f14518f93e99f8b08c885f8002181bf92581ba5617a03
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc42d891000cff71d8910014fe71d891000cfd71d8910014fc71d8910236ef21d8910236ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910226ef20d8910226ed20d891001cff765891003eec625891021df7715891022dfb70589100dff01058910004ff7558910034fe7558910034fc7558910004ff745891002cfe745891002cfc7458910004ff7358910024fe7358910024fc7358910224ff7258910006ef725891003eee325891021cff7158910006f771589100dcff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc76549100367e65549100067d6554910005bf745491004dbc7454910006ef625491001eec625491019ff01054910004ff7650910004fe7650910004fd7650910004fc765091002ebe6450910006bd645091017ff01050910004ff764c910004fe764c910004fd764c910004fc764c910026de634c910006dd634c91001eee624c910006ed624c910015f6714c91000dfa704c91015ff0104c91000df4764c510026f4764c51000cf4764c510006f7654c510006f5654c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510005f7724c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100fff0704c51000df0704c510016f7604c510017f3604c5100ffd7304c5100fff2304c5100ffd5304c5100fff2204c51000df4764851001ef4764851000cf47648510006f76448510006f56448510005f77348510005f57348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851003fe63248510007e53248510007f3704851000df6704851000df470485100dff0704851000df07048510016f76048510017f360485100dff230485100dfe720485100dff220485100dfe52048510015f8764c110026f8764c110014f8764c110006fb654c110006f9654c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110047d8634c110005fb724c110047db324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c110015f0714c11000efb614c11000ff3614c11007fdb314c11007ff2314c11007fd9314c110047f1314c110007d1314c11007ff2214c110007f1214c110015f8764811001ef87648110014f87648110006fb6448110006f96448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811001efa624811001ef8624811003fe8624811003fea3248110007e93248110007f37148110015fa7148110015f8714811005ff07148110015f0714811000efb614811000ff3614811005ff23148110007f1314811005feb214811005ff2214811005fe9214811003ff12148110007e12148110
  | 1 => 0x9510004ff7359510006df7359510004df7359510024fe7359510024fc7359510006dc7359510024dc73595100567f5359510004ff725951001cfe725951001cfc72595100567f525951027cff7159510006f771595100bef6315951013cff7059510006fb705951013efa305951002cfe76d91100557e75d91100057d75d911004ebe64d9110267f010d9110034fe75d91100067e75d91100347e75d9110004fd75d91100067d75d91100047d75d9110034fc75d911011cfd74d9110024fe73d9110004fd73d9110024fc73d911001cfe72d9110004fd72d911001cfc72d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110276bf41d9110276bd41d9110276f621d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110266bf40d9110266bd40d9110266fa20d911002cff765911004ebc6459110005ef725911003dec725911025df7715911026dfb705911011ff01059110004ff7559110034fe7559110034fc7559110264ff7459110006bf7459110006bf545911004ebc5459110004ff7359110024fe7359110024fc735911004ebf4359110004ff7259110006ef7259110004ef725911001cfe725911001cfc7259110006ec725911001cec725911004ebf425911025cff7159110006f7715911009ef6215911011cff7059110006fb705911011efa2059110004ff7655110004fe7655110004fd7655110004fc76551101fff01055110024fe76d8d10046de63d8d10247f010d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d10006df53d8d10046dc53d8d10046de43d8d1001cfe72d8d10004fd72d8d1001cfc72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10256df31d8d10256dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10246df30d8d10246dd30d8d10024ff7658d10046dc6358d1023df77158d1024dfb7058d100fff01058d10004ff7558d10034fe7558d10034fc7558d10004ff7458d1002cfe7458d1002cfc7458d10244ff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d10046df3258d1023cff7158d10006f77158d100fcff7058d10006fb7058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100367e6554d100067d6554d101dff01054d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100557c7550d1002ebe6450d10006bd6450d10006df6350d10026dc6350d101bff01050d1001cfe76d891003eee62d8910227f010d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d891003eee52d8910006ef42d891003ee
  | 2 => 0x16eee644c92016eec644c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c9202b7cf534c920067cc534c920067ce434c920007cd434c920005ef714c920067cf314c920007eb704c92000dee704c92000dec704c92015fe8704c92001eef604c92001feb604c92015fea404c92015fcf304c92015fcd304c92015fea104c920014fe76d852005ef661d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d85202aeee32d8520006ed32d852005ef651d8520006f731d852005ef431d852005ef621d85202aef521d852000cfe70d852001cfd70d852000cfc70d852021ef710d852005ef461585202a5fb7058520004ff7654520004fe7654520004fc76545200367e65545200067d6554520006f76154520016f46154520004ff7650520004fe7650520004fc765052002ebe6450520006bd645052000dfa7050520004ff764c520004fe764c520004fc764c520026de634c520006dd634c52001dee724c520007cd324c52000dec7648520016ec764852000cec7648520005ef7348520005ed7348520006ef6348520006ed634852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005fe64148520007e54148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200dfea40485200dfe710485200dfea104852001df8765012002ef8765012001cf87650120006fb6550120006f9655012000dfb745012000fbb7450120007bb645012002efa645012002ef8645012006fb8645012029fbb545012006fb8545012006fbb4350120007b94350120007eb725012001dfa725012001df872501200a7e8725012000efb625012000feb62501200a7bb42501200a7b942501200a7ea3250120007e93250120005fb715012006fbb4150120007b941501200a7eb2150120007e92150120034fe76d95100567e65d951004dbe74d9510005bd74d9510287f010d951013cfd75d951002cfe74d9510006be74d951002cbe74d9510004fd74d9510006bd74d9510004bd74d951002cfc74d9510024fe73d9510004fd73d9510024fc73d951001cfe72d9510004fd72d951001cfc72d951000cff71d9510014fe71d951000cfd71d9510014fc71d95102967f51d95102967d51d9510296f631d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102867f50d95102867d50d9510286fa30d9510034ff76595100567c6559510005df7359510045dc735951027df7715951028dfb705951013ff01059510284ff75595100067f7559510004ff745951002cfe745951002cfc74595100067e54595100567c545
  | 3 => 0x93154130034fe76d95200767e65d952019cfd75d952002cfe74d9520004fd74d952002cfc74d9520024fe73d9520004fd73d9520024fc73d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203167f52d95203167d52d9520316ee32d9520014fe71d9520004fd71d9520014fc71d952001cff70d952001cfd70d95203067f50d95203067d50d9520306fa40d9520034ff76595200767c6559520005bf745952006dbc74595202fdef725952030dfb7059520304ff75595200067f7559520004ff7459520006bf7459520004bf745952002cfe745952002cfc7459520006bc745952002cbc7459520004ff7359520024fe7359520024fc73595202fcff7259520006ef72595200c6ee3259520004ff7159520014fe7159520014fc71595200767f515952019cff7059520006fb705952019efa405952002cfe76d912006ebe64d9120034fe75d9120004fd75d9120034fc75d912017cfd74d9120006bf54d912006ebc54d9120024fe73d9120004fd73d9120024fc73d912006ebf43d912000cff72d912001cfe72d912000cfd72d912001cfc72d91202f6bf42d91202f6bd42d9120014fe71d9120004fd71d9120014fc71d912001cff70d912001cfd70d91202e6bf40d91202e6bd40d912002cff765912006ebc64591202ddef72591202edfb7059120004ff7559120034fe7559120034fc75591202e4ff7459120006bf7459120004ff7359120024fe7359120024fc73591202dcff7259120006ef7259120004ff7159120014fe7159120014fc715912006ebf415912017cff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc7655120024fe76d8d20066de63d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202d6df32d8d202d6dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d202d6ef21d8d2001cff70d8d2001cfd70d8d202c6df30d8d202c6dd30d8d202c6fa10d8d20024ff7658d20066dc6358d202bdef7258d20005f77158d2005df47158d202cdfb7058d20004ff7558d20034fe7558d20034fc7558d20004ff7458d2002cfe7458d2002cfc7458d202c4ff7358d20006df7358d202bcff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20014fe7158d20014fc7158d20006f47158d20014f47158d20066df3158d20086ef2158d2015cff7058d20006fb7058d2015efa1058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200757c7550d20006bf6450d2002ebc6450d2000dec764c920026ec764c92000cec764c920006ef654c920006ed654c920
  | 4 => 0x913001cfe725913001cfc72591300aedf3259130004ff7159130014fe7159130014fc715913008ebf41591301bcff7059130006fb70591301befa5059130004ff7655130004fe7655130004fd7655130004fc765513001cfe76d8930086ee62d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930086ee32d8930346ed32d8930014fe71d8930004fd71d8930014fc71d8930346df31d8930024fd70d89302beef20d89302befa10d8930086ec6258930005f7715893007df4715893033dfb7058930004ff7654930004fe7654930004fc76549300067f65549300367c6554930005bf745493008dbc7454930004ff7650930004fe7650930004fc765093000ddc764c93001edc764c93000cdc764c930176de654c930176dc654c930006df644c930006dd644c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c930087ce524c930007cd524c930337cf424c930087cc424c930005df714c930087cf214c930007db704c93000dde704c93000ddc704c93015fd8704c930026df604c930027db604c93015fda504c93015fcf204c93015fda104c930014fe76d853007ef661d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d853032edf32d8530006dd32d853007ef641d853007ef631d853032ef531d8530006f721d853007ef421d8530024fd70d853023ef710d853007ef46158530325fb7058530004ff7654530004fe7654530004fc76545300367e65545300067d655453000dfa7054530004ff7650530004fe7650530004fc765053002ebe6450530006bd6450530006f76150530016f4615053000ddc764c530016dc764c53000cdc764c530005df724c530006df624c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6514c530007d5514c530007db704c53000dde704c53000ddc704c5300ffd8704c530026df604c530027db604c5300ffda504c5300ffd7104c5300ffda104c530004ff7648530004fe7648530004fc7648530025de7348530005dd734853001eee6248530007cd3248530025f87654130036f87654130024f8765413000dfb755413000f7b75541300077b6554130036fa6554130036f86554130097786554130006fb6454130006f9645413031f7a5454130097785454130007db7354130025fa7354130025f873541300cfd8735413000efb635413000fdb63541300cf7b53541300cf7953541300977b52541300077952541300cfdb3254130007d93254130005fb71541300977b51541300077951541300cfdb3154130007d
  | 5 => 0x4ff7654540004fe7654540004fc76545400067f65545400367c6554540005bf745454002dbc74545401573c545454000dbc7650540016bc765054000cbc76505400b5be75505400b5bc7550540136be6550540136bc6550540005bf7350540006bf6350540005bf7250540006bf625054002dbf715054002fb77150540007b76150540016be6150540016bc615054009fb4615054009fb65150540007b5515054009fb62150540007bb705054000dbe705054000dbc705054011fb8705054002ebf605054002fbb605054011fba505054011fba2050540004ff764c540004fe764c540004fc764c54002dbe744c540005bd744c540005fb704c54000df8704c540004ff7648540004fe7648540004fc764854002dbe7448540005bd7448540016f66148540007b5414854002df87654140036f8765414002cf8765414000dfb755414000f7b75541400077b6554140036fa6554140036f865541400b7786554140007bb745414002dfa745414002df874541400d7b8745414000efb645414000fbb64541400b7bb54541400d77a54541400d77854541400d7b854541400d7385454140006fb63541400b77b53541400077953541400d7bb4354140007b94354140005fb72541400b77b52541400077952541400d7bb4254140007b942541400b77b51541400077951541400d7bb4154140007b94154140034fe76d95300967e65d95301dcfd75d953002cfe74d9530004fd74d953002cfc74d95300067e54d95300967c54d953000cff73d9530024fe73d953000cfd73d9530024fc73d95303867f53d95303867d53d953001cfe72d9530004fd72d953001cfc72d95300967f52d9530014fe71d9530004fd71d9530014fc71d9530024ff70d9530024fd70d95303767f50d95303767d50d9530034ff76595300967c655953036ddf735953037dfb7059530374ff75595300067f7559530004ff745953002cfe745953002cfc745953036cff7359530006df7359530004ff725953001cfe725953001cfc7259530004ff7159530014fe7159530014fc71595300967f51595301dcff7059530006fb705953002cfe76d913008ebe64d9130034fe75d9130004fd75d9130034fc75d91301bcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d9130366bf43d9130366bd43d913001cfe72d9130004fd72d913001cfc72d9130366df32d9130014fe71d9130004fd71d9130014fc71d9130024ff70d9130024fd70d9130356fa50d9130356bf40d9130356bd40d913002cff76591300057f75591300957c755913008ebc645913034ddf735913035dfb7059130004ff75591300067f75591300047f7559130034fe7559130034fc75591300067c75591300347c7559130354ff7459130006bf745913034cff7359130006df7359130004ff725
  | 6 => 0xf7459540006bf74595400b6bf54595400d67e54595400d67c54595400d6bc5459540004ff7359540024fe7359540024fc73595400d6bf4359540004ff725954001cfe725954001cfc72595400b67f5259540004ff7159540014fe7159540014fc71595401fcff7059540006fb7059540024fe76d8d400aede63d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d400aede43d8d403b6dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40014fe71d8d40004fd71d8d40014fc71d8d403b6bf41d8d4002cfd70d8d4034efa50d8d4034edf30d8d400057f7558d400b57c7558d400aedc6358d403adfb7058d40004ff7654d40004fe7654d40004fc7654d40005bf7454d4002dbc7454d4000dbc7650d40026bc7650d4000cbc7650d400073f7550d400b5be7550d400b5bc7550d400073c7550d400b53c7550d40006bf6550d40006bd6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400af9c6350d400af9e5350d400079d5350d40005bf7250d401cebe6250d401cebc6250d400af9f3250d40005bf7150d40007bb7050d4000dbe7050d4000dbc7050d401bfb87050d4002ebf6050d4002fbb6050d401bfba5050d401bfba2050d4001cfe76d89400a6ee62d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89400a6ee42d89403a6ed42d89400a6ee32d8940014fe71d8940004fd71d8940014fc71d89403a6bf41d8940006ee21d89400a6ec21d894002cfd70d89402deef20d89400a6ec625894039dfb7058940004ff7654940004fe7654940004fc76549400367e65549400067d6554940005bf745494002dbc74549400b73f545494000dfa705494000dbc765094001ebc765094000cbc76509400b5be75509400b5bc7550940005bf735094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400a7ac62509400a7ae5250940007ad5250940005bf7150940007bb705094000dbe705094000dbc705094017fb8705094002ebf605094002fbb605094017fba505094017fba2050940004ff764c940004fe764c940004fc764c94002dbe744c940005bd744c940026de634c9400079d434c940006ef624c94001eec624c94016faf424c940014fe76d854009ef661d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540006bf54d8540396bc54d8540024fe73d8540004fd73d8540024fc73d8540396bf43d8540006bd43d854001cfe72d8540004fd72d854001cfc72d8540396bf42d8540006bd42d854009ef641d8540396f541d854002cfd70d854025efa20d854025ef710d8540005ef72585400a5ec725854009ef4615854038dfb7058540
  | 7 => 0x89502fefa40d89502feef20d8950005bf74589500d5bc74589500c6ec62589503edfb705895000d7c765495001e7c765495000c7c76549500073f74549500d57e74549500d57c74549500073c74549500d53c74549500067f64549500057f73549501ae7e63549501ae7c63549500357f72549500376f72549500076f625495001e7e625495001e7c62549500c76c62549500c76e42549500c76e32549500057f71549500077b705495000d7e705495000d7c705495019f7870549500367f60549500377b605495019f7a405495019f7a3054950004ff7650950004fe7650950004fc76509500057f75509500357c75509500076d5250950004ff764c950004fe764c950004fc764c9500357e754c9500057d754c950006df634c950026dc634c9501775f534c95001eee624c9500076d524c950014fe76d85500bef661d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d85500067e54d85503e67c54d8550024fe73d8550004fd73d8550024fc73d85503e67f53d85500067d53d855001cfe72d8550004fd72d855001cfc72d85503e67f52d85500067d52d85500bef651d85503e6f551d8550034fd70d855027efa30d855027ef710d8550005df73585500cddc73585500bef461585503ddfb705855000d7c76545500167c765455000c7c76545500d57e74545500d57c74545501567e64545501567c64545500057f73545500067f63545500057f72545500067f62545500357f71545500377771545500077761545500167e61545500167c61545500bf7461545500bf7641545500bf7631545500077b705455000d7e705455000d7c705455013f7870545500367f60545500377b605455013f7a405455013f7a3054550004ff7650550004fe7650550004fc76505500057f75505500357c7550550006bf645055002ebc64505500d73c5450550007755150550004ff764c550004fe764c550004fc764c5500357e754c5500057d754c550016f6614c55000775514c550004ff7648550004fe7648550004fc76485500357e75485500057d7548550005fb704855000df87048550034fe76d95400b67e65d954002dbe74d954000dbd74d95400b73f54d95401fcfd75d954000cff74d954002cfe74d954000cfd74d95403c6bd74d954000cbd74d954002cfc74d95403d67f54d95400b6bf54d95400b63f54d95403d67d54d95403d6bc54d9540024fe73d9540004fd73d9540024fc73d95400067e53d95400b67c53d95403d6bf43d954001cfe72d9540004fd72d954001cfc72d9540014fe71d9540004fd71d9540014fc71d95400b67f51d954002cff70d954002cfd70d95403c67f50d95403c67d50d9540034ff76595400b67c65595403bdbf74595400d73c54595403cdfb70595403c4ff75595400067f75595403bcf
  | 8 => 0xe7cc634c921427cf534c9210e7cc534c9210e7ce434c921007cd434c921007e7714c921015ee714c921015ec714c921167e4714c92101eef614c92101fe7614c921167e6414c921167cf314c921167cd314c921005ef704c9210e7cf304c921167e7104c92101df4765052102ef4765052101cf47650521006f76550521006f56550521015f77450521017b77450521007b7645052102ef6645052102ef464505210efb4645052141fb754505210efb454505210efb74350521007b54350521007e7725052101df6725052101df47250521127e47250521016f76250521017e76250521127b74250521127b54250521127e63250521007e53250521005f770505210efb74050521127e7205052100cfe76d81210defa60d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d81212a6ee32d8121006ed32d812101cfd71d812100cfc71d81210defa50d8121006fb30d81210def830d81210defa20d81210defa10d81210def8605812102cfe76d91500357e75d915000d7d75d91500d6be64d91500d73e54d915000cfd75d91503be7d75d915000c7d75d915002cfc75d91500d67e54d91500d6be54d91500d63e54d9150416bd54d91500d67c54d9150024fe73d9150004fd73d9150024fc73d915001cfe72d9150004fd72d915001cfc72d91504167f52d9150006be42d91500d6bc42d9150014fe71d9150004fd71d9150014fc71d91500d6bf41d9150034fd70d91503bebf40d91500d6bc64591500d73c545915040dfb7059150024fe76d8d500cede63d8d5000cfd75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500cede53d8d50406dd53d8d5001cfe72d8d50004fd72d8d5001cfc72d8d500cedf32d8d50014fe71d8d50004fd71d8d50014fc71d8d504067f51d8d50006de31d8d500cedc31d8d50034fd70d8d5036edf30d8d500cedc6358d503fdfb7058d5000d7c7654d500267c7654d5000c7c7654d500d57e7454d500d57c7454d500357f7354d500375f7354d500075f6354d500267e6354d500267c6354d500cf5c6354d500cf5e4354d500057f7254d500057f7154d500077b7054d5000d7e7054d5000d7c7054d501df787054d500367f6054d500377b6054d501df7a4054d501df7a3054d50004ff7650d50004fe7650d50004fc7650d500057f7550d500357c7550d5002ebe6450d500d73e5450d500075d5350d5000dfa7050d5001cfe76d89500c6ee62d895000cfd75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d8950024fe73d8950004fd73d8950024fc73d89500c6ee52d89503f6ed52d8950014fe71d8950004fd71d8950014fc71d89503f67f51d8950034fd70d
  | 9 => 0xe76d95210f67e65d95211a4fd75d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521004fd73d9521024fc73d9521014ff72d9521014fd72d95214867f52d95214867d52d9521486ee32d952101cff71d952101cfd71d95214767f51d95214767d51d9521476f641d952100cfe70d9521004fd70d952100cfc70d9521034ff76595210f67c6559521005bf74595210edbc745952146def725952147df77159521474ff75595210067f7559521004ff7459521006bf7459521004bf745952102cfe745952102cfc7459521006bc745952102cbc7459521004ff7359521024fe7359521024fc735952146cff7259521006ef7259521146ee32595211a4ff7159521006f771595211a6f64159521004ff705952100cfe705952100cfc70595210f67f505952102cfe76d91210eebe64d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121006bf54d91210eebc54d9121024fe73d9121004fd73d9121024fc73d91210eebf43d9121014ff72d9121014fd72d9121466bf42d9121466bd42d912101cff71d912101cfd71d9121456bf41d9121456bd41d912100cfe70d9121004fd70d912100cfc70d912102cff76591210eebc645912144def725912145df77159121004ff7559121034fe7559121034fc7559121454ff7459121006bf7459121004ff7359121024fe7359121024fc735912144cff7259121006ef7259121184ff7159121006f77159121004ff705912100cfe705912100cfc70591210eebf4059121004ff7655121004fe7655121004fd7655121004fc7655121024fe76d8d210e6de63d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21164fd73d8d21014ff72d8d21014fd72d8d21446df32d8d21446dd32d8d2101cff71d8d2101cfd71d8d21436df31d8d21436dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21446ef20d8d21436f710d8d21024ff7658d210e6dc6358d2142def7258d2143df77158d21005fb7058d210ddf87058d21004ff7558d21034fe7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d21434ff7358d21006df7358d2142cff7258d21006ef7258d21164ff7158d21006f77158d21004ff7058d21006fb7058d21004fb7058d2100cfe7058d2100cfc7058d21006f87058d2100cf87058d210e6df3058d21106ef2058d21166f71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210f57c7550d21006bf6450d2102ebc6450d21015ec764c921026ec764c921014ec764c921006ef654c921006ed654c92116eee644c92116eec644c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c921
  | 10 => 0x95311e4ff7159531006f77159531004ff705953100cfe705953100cfc70595311167f505953102cfe76d913110ebe64d9131034fe75d9131004fd75d9131034fc75d91311c4fd74d9131014ff73d9131014fd73d91314c6bf43d91314c6bd43d913101cfe72d9131004fd72d913101cfc72d91314c6df32d9131024ff71d9131024fd71d91314b6f651d91314b6bf41d91314b6bd41d913100cfe70d9131004fd70d913100cfc70d913102cff76591310057f75591311157c755913110ebc64591314addf73591314bdf77159131004ff75591310067f75591310047f7559131034fe7559131034fc75591310067c75591310347c75591314b4ff7459131006bf74591314acff7359131006df7359131004ff725913101cfe725913101cfc725913112edf32591311c4ff7159131006f771591311c6f65159131004ff705913100cfe705913100cfc705913110ebf4059131004ff7655131004fe7655131004fd7655131004fc765513101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d8931106ee32d89314a6ed32d8931024fd71d893142eef21d893100cfe70d8931004fd70d893100cfc70d89314a6df30d893142ef710d8931106ec625893149df77158931005fb70589310fdf87058931004ff7654931004fe7654931004fc76549310067f65549310367c6554931005bf745493110dbc7454931004ff7650931004fe7650931004fc7650931015dc764c93101edc764c931014dc764c931176de654c931176dc654c931006df644c931006dd644c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c931107cc624c931107ce524c931007cd524c931497cf424c931107cc424c931007d7714c931015de714c931015dc714c931167d4714c931026df614c931027d7614c931167d6514c931167cf214c931005df704c931107cf204c931167d7104c931025f47654531036f47654531024f47654531015f77554531017777554531007776554531036f66554531036f46554531117746554531006f76454531006f5645453148f765454531117745454531007d77354531025f67354531025f4735453114fd47354531016f76354531017d7635453114f77535453114f75535453111777525453100775525453114fd73254531007d53254531005f7705453111777505453114fd7305453100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d8131326df32d8131006dd32d8131024fd71d81310fefa40d81310fefa30d8131006fb20d81310fef820d81310fefa10d81310fef86058131034f
  | 11 => 0x1cebe6250d411cebc6250d4112f9f3250d41007b77150d41015be7150d41015bc7150d411c7b47150d4102ebf6150d4102fb76150d411c7b65150d411c7b62150d41005bf7050d4101cfe76d8941126ee62d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d8941126ee42d89414f6ed42d8941126ee32d894102cfd71d894144eef21d894100cfe70d8941004fd70d894100cfc70d89414f6bf40d8941006ee20d8941126ec20d8941126ec62589414edf77158941004ff7654941004fe7654941004fc76549410367e65549410067d6554941005bf745494102dbc74549411373f5454941015f67154941015bc765094101ebc7650941014bc7650941135be7550941135bc7550941005bf735094102dbf725094102faf7250941007af625094101ebe625094101ebc6250941127ac6250941127ae5250941007ad5250941007b77150941015be7150941015bc7150941187b4715094102ebf615094102fb76150941187b65150941187b62150941005bf7050941004ff764c941004fe764c941004fc764c94102dbe744c941005bd744c941026de634c9410079d434c941006ef624c94101eec624c94116faf424c94102df47654541036f4765454102cf47654541015f77554541017777554541007776554541036f66554541036f46554541137746554541007b7745454102df6745454102df47454541157b47454541016f76454541017b76454541137b75454541157765454541157745454541157b45454541157345454541006f76354541137775354541007755354541157b74354541007b54354541005f77254541137775254541007755254541157b74254541007b54254541137775054541157b7405454100cfe76d814111efa60d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141006bf54d814138ebc54d8141024fe73d8141004fd73d8141024fc73d814138ebf43d8141006bd43d814101cfe72d8141004fd72d814101cfc72d814138ebf42d8141006bd42d814102cfd71d814126ef621d814111efa40d814111efa10d8141005ef7258141125ec725814111ef86058141034fe76d95311167e65d95311e4fd75d953102cfe74d9531004fd74d953102cfc74d95310067e54d95311167c54d9531014ff73d9531014fd73d95314e67f53d95314e67d53d953101cfe72d9531004fd72d953101cfc72d95311167f52d9531024ff71d9531024fd71d95314d67f51d95314d67d51d953100cfe70d9531004fd70d953100cfc70d9531034ff76595311167c65595314cddf73595314ddf771595314d4ff75595310067f7559531004ff745953102cfe745953102cfc74595314ccff7359531006df7359531004ff725953101cfe725953101cfc725
  | 12 => 0xe74549511557c74549510073c74549511553c74549510067f64549510057f73549511ae7e63549511ae7c63549510357f72549510376f72549510076f625495101e7e625495101e7c62549511476c62549511476e42549511476e32549510077771549510157e71549510157c71549511a77471549510367f61549510377761549511a77641549511a77631549510057f7054951004ff7650951004fe7650951004fc76509510057f75509510357c75509510076d5250951004ff764c951004fe764c951004fc764c9510357e754c9510057d754c951006df634c951026dc634c9511775f534c95101eee624c9510076d524c95100cfe76d815113efa60d8151014fd75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d81510067e54d81513de7c54d8151024fe73d8151004fd73d8151024fc73d81513de7f53d81510067d53d815101cfe72d8151004fd72d815101cfc72d81513de7f52d81510067d52d8151034fd71d815128ef631d815113efa50d815113efa10d8151005df735815114ddc735815113ef86058151034fe76d95411367e65d954102dbe74d9541015bd74d95411373f54d9541204fd75d9541014ff74d9541014fd74d9541516bd74d9541014bd74d95415267f54d9541136bf54d95411363f54d95415267d54d9541526bc54d9541024fe73d9541004fd73d9541024fc73d95410067e53d95411367c53d9541526bf43d954101cfe72d9541004fd72d954101cfc72d954102cff71d954102cfd71d95415167f51d95415167d51d954100cfe70d9541004fd70d954100cfc70d95411367f50d9541034ff76595411367c655954150dbf74595411573c545954151df77159541514ff75595410067f755954150cff7459541006bf7459541136bf54595411567e54595411567c5459541156bc5459541004ff7359541024fe7359541024fc7359541156bf4359541004ff725954101cfe725954101cfc72595411367f5259541204ff7159541006f77159541004ff705954100cfe705954100cfc7059541024fe76d8d4112ede63d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4112ede43d8d41506dd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4102cfd71d8d414aef651d8d414aedf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41506bf40d8d410057f7558d411357c7558d4112edc6358d414fdf77158d41004ff7654d41004fe7654d41004fc7654d41005bf7454d4102dbc7454d41015bc7650d41026bc7650d41014bc7650d410073f7550d41135be7550d41135bc7550d410073c7550d411353c7550d41006bf6550d41006bd6550d4102dbf7350d4102f9f7350d410079f6350d41026be6350d41026bc6350d4112f9c6350d4112f9e5350d410079d5350d41005bf7250d41
  | 13 => 0x49321afcc735493201eef635493201fcf6354932177cf53549321af6e53549321af6c53549321afcc53549321af4c53549321afce4354932007cd4354932005ef71549321776f51549321afcf3154932005ef70549321776f50549321afcf3054932014fe76d8532166f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532024fd72d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d853249edf30d853243eef20d8532006f610d8532166f410d8532166f46158532005fb705853215df8705853200cfe76d813215efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d8132014fe71d8132004fd71d8132014fc71d813233edf31d81322ceef21d813215efa30d813215efa20d8132006fb10d813215ef810d8132005f77158132165f4715813215ef8605813202cfe76d91510357e75d91510157d75d9151156be64d91511573e54d9151014fd75d915150e7d75d91510147d75d91511567e54d9151156be54d91511563e54d9151556bd54d91511567c54d9151024fe73d9151004fd73d9151024fc73d915101cfe72d9151004fd72d915101cfc72d91515567f52d9151006be42d9151156bc42d9151034fd71d915150ebf41d915100cfe70d9151004fd70d915100cfc70d9151156bf40d9151156bc64591511573c545915154df77159151024fe76d8d5114ede63d8d51014fd75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5114ede53d8d51546dd53d8d5101cfe72d8d51004fd72d8d5101cfc72d8d5114edf32d8d51034fd71d8d514cedf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d515467f50d8d51006de30d8d5114edc30d8d5114edc6358d5153df77158d510157c7654d510267c7654d510147c7654d511557e7454d511557c7454d510357f7354d510375f7354d510075f6354d510267e6354d510267c6354d5114f5c6354d5114f5e4354d510057f7254d51007777154d510157e7154d510157c7154d511e7747154d510367f6154d51037776154d511e7764154d511e7763154d510057f7054d51004ff7650d51004fe7650d51004fc7650d510057f7550d510357c7550d5102ebe6450d511573e5450d510075d5350d51015f67150d5101cfe76d8951146ee62d8951014fd75d895102cfe74d8951004fd74d895102cfc74d8951024fe73d8951004fd73d8951024fc73d8951146ee52d8951536ed52d8951034fd71d895146ef641d895146eef21d895100cfe70d8951004fd70d895100cfc70d89515367f50d8951005bf7458951155bc7458951146ec625895152df771589510157c765495101e7c76549510147c76549510073f74549511557
  | 14 => 0x24ff72d9532024fd72d95325867f52d95325867d52d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d9532034ff76595321767c6559532005bf745953216dbc745953257ddf73595321af5c535953258def7259532584ff75595320067f7559532004ff7459532006bf7459532004bf745953202cfe745953202cfc7459532006bc745953202cbc745953257cff7359532006df7359532176df53595321ae7e53595321ae7c53595321aedc53595321aede43595321ecff7259532006ef7259532004ff7159532014fe7159532014fc71595321767f5159532004ff705953200cfe705953200cfc70595321767f505953202cfe76d913216ebe64d913201dee72d9132025ed72d913216faf42d9132034fe75d9132004fd75d9132034fc75d91321ccfd74d9132006bf54d913216ebc54d913201cff73d913201cfd73d9132576bf43d9132576bd43d9132024ff72d9132024fd72d9132576ed72d9132024ed72d9132566ee52d9132566bf42d913216eef42d9132566bd42d9132566ec42d9132014fe71d9132004fd71d9132014fc71d913200cfe70d9132004fd70d913200cfc70d913202cff76591320057f75591321757c755913216ebc645913255ddf735913256def72591321cfac4259132004ff75591320067f75591320047f7559132034fe7559132034fc75591320067c75591320347c7559132564ff7459132006bf745913255cff7359132006df73591321ccff7259132006ef72591321ceee525913216eef42591321cebe42591321cebc42591321ceec4259132004ff7159132014fe7159132014fc715913216ebf4159132004ff705913200cfe705913200cfc705913216ebf4059132004ff7655132004fe7655132004fd7655132004fc7655132005df7355132025dc7355132005ef725513201dec725513201ddc7650d3202edc7650d3201cdc7650d320075f7550d32175de7550d32175dc7550d320075c7550d321755c7550d32006df6550d32006dd6550d32025df7450d320279f7450d320079f6450d3202ede6450d3202edc6450d3216f9c6450d3216f9e5450d320079d5450d32007cf7250d3201dde7250d3201ddc7250d321cfcc7250d32026df6250d32027cf6250d321cfce5250d3216fcf4250d321cf9e4250d321cf9c4250d321cfcc4250d321cf8c4250d32005df7150d3216f9f4150d321cfcf2150d32005df7050d3216f9f4050d321cfcf2050d32025ec7654932036ec7654932024ec765493201def755493201f6f75549320076f6554932036ee6554932036ec65549321776c6554932007af745493216dee745493216dec7454932007ac745493216dac7454932006ef6454932006ed64549321776f54549320076d5454932007cf7354932025ee7354932025ec735
  | 15 => 0xe74d8152004fd74d815202cfc74d8152024fe73d8152004fd73d8152024fc73d8152034fd72d815230eee32d8152014fe71d8152004fd71d8152014fc71d81523ee7f51d815219efa50d815219efa20d8152005bf74581521b5bc7458152006bf6458152006bc645815219ef86058152034fe76d95421967e65d954220cfd75d954201cff74d954201cfd74d95425ce7f54d95425ce7d54d9542024fe73d9542004fd73d9542024fc73d95420067e53d95421967c53d954202cff72d954202cfd72d95425be7f52d95425be7d52d9542014fe71d9542004fd71d9542014fc71d95421967f51d954200cfe70d9542004fd70d954200cfc70d95421967f50d9542034ff76595421967c65595425b5bf74595425c5ef72595425bcff75595420067f75595425b4ff7459542006bf74595425b4bf7459542004ff7359542024fe7359542024fc735954220cff7259542006ef7259542004ff7159542014fe7159542014fc7159542004ff705954200cfe705954200cfc7059542024fe76d8d4218ede63d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d4218ede43d8d425aedd43d8d4202cfd72d8d4255eee52d8d425aeef42d8d4255ebe42d8d4255ebc42d8d4255eec42d8d4255edf32d8d42014fe71d8d42004fd71d8d42014fc71d8d425aebf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d425aebf40d8d420057f7558d421957c7558d4218edc6358d425a5ef7258d42004ff7654d42004fe7654d42004fc7654d4202dec7654942036ec765494202cec765494201def755494201f6f75549420076f6554942036ee6554942036ec65549421976c6554942007af745494202dee745494202dec74549421b7ac745494201eef645494201faf64549421b76f54549421b76d5454942006ef635494259f6e53549421976c53549421976f51549421b7af41549421976f50549421b7af4054942014fe76d8542186f661d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d8542186f641d8542186f621d854200cfe70d8542004fd70d854200cfc70d85424eebf40d8542186f4615854200cfe76d814217efa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d814202cfd72d8142014fe71d8142004fd71d8142014fc71d814239ebf41d814217efa40d814217efa20d814217ef86058142034fe76d95321767e65d9532025de73d953201ddd73d95321775f53d95321ecfd75d953202cfe74d9532004fd74d953202cfc74d95320067e54d95321767c54d953201cff73d953201cfd73d9532586dd73d953201cdd73d95325967f53d9532176df53d95325967d53d9532596dc53d9532596de43d9532
  | 16 => 0x91525b6bd72d91525b6bc72d91525b6bf52d91525b6be52d91525b6bc52d91525b6bf32d91525b6be32d91525b6bd32d91525b6bc32d9152006bf71d9152006be71d9152006bd71d9152006bc71d91525febf51d91525febe51d91525febd51d91525febc51d9152006bf31d9152006be31d9152006bc31d91525b6bf21d91525b6be21d91525b6bd21d91525b6bc21d9152006bf70d9152006be70d9152006bd70d9152006bc70d91525febf50d91525febe50d91525febd50d91525febc50d9152006bf30d9152006be30d9152006bc30d91525b6bf20d91525b6be20d91525b6bd20d91525b6bc20d9152006bf10d9152006be10d9152006bc10d91521b6bc64591525f5ef72591525b5be76191521b6be76191521b73e75191525ef3d75191525eebf65191521b79e73191521b79d7319152006be6319152006bc63191520073e53191525e73c53191525efae72191521b7ad72191525eebf62191525e7af52191525ef3e52191525ef3c52191525efac52191525efae32191521b7b671191521b7b57119152006be6119152006bc61191525e73f51191521b7ba70191521b7b97019152006be6019152006bc60191525e73f501915201d7c765515202e7c765515201c7c76551520357f74551520373f74551520073f645515202e7e645515202e7c64551521b73c64551521ad7e73551521ad7c73551521b73f43551520076f725515201d7e725515201d7c725515220f6c72551520367f62551520376f625515220f6e425515220f6e32551520057f71551520057f7055152024fe76d8d520357e75d8d5201d7d75d8d52006bf64d8d52006bc64d8d521aede63d8d521af5e53d8d5201cfd75d8d5257e7d75d8d5201c7d75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521ae7e53d8d521aede53d8d525dedd53d8d521ae7c53d8d52034fd72d8d5257edf32d8d52014fe71d8d52004fd71d8d52014fc71d8d525de7f51d8d5200cfe70d8d52004fd70d8d5200cfc70d8d525de7f50d8d52005bf7458d521b5bc7458d52006bf6458d52006bc6458d521aedc6358d521af5c5358d525d5ef7258d52004ff7650d52004fe7650d52004fc7650d520057f7550d520357c7550d52006bf6450d5202ebc6450d520073d5450d52026de6350d521af5e5350d5201dee7250d521cfae4250d52014fe76d8552006bf64d8552006bc64d85521a6f661d855201cfd75d855202cfe74d8552004fd74d855202cfc74d8552024fe73d8552004fd73d8552024fc73d8552034fd72d855247eee32d85521a6f651d85521a6f621d855200cfe70d8552004fd70d855200cfc70d855252e7f50d8552005bf74585521b5bc7458552006bf6458552006bc64585521a6f4615855200cfe76d8152006bf64d8152006bc64d815219efa60d815201cfd75d815202cf
  | 17 => 0x2179e53551431cdbe72551431cdbc72551431d73f52551432179f3255143005bf7155143005bf705514302ddc7654d43036dc7654d4302cdc7654d43025df7554d430275f7554d430075f6554d43036de6554d43036dc6554d431d75c6554d430079f7454d4302dde7454d4302ddc7454d431f79c7454d43026df6454d430279f6454d431f79e5454d431d79d5454d43005df7254d436079e4254d431f79c4254d431d75f5154d431f79f4154d431d75f5054d431f79f4054d4301cfe76d89430067f65d89430067c65d894302dbe74d8943025bd74d89431ceee62d89431cfae42d8943034fe75d8943004fd75d8943034fc75d8943024fd74d89431cebd74d8943024bd74d894302cfd73d89431cebe42d89431ceee42d89431cebc42d89431ceee32d8943014fe71d8943004fd71d8943014fc71d89435a6bf41d894300cfe70d8943004fd70d894300cfc70d89435a6bf40d89430057f75589431d57c75589430067f65589430067c65589431ceec62589431cfac4258943014fe76d85430067f65d85430067c65d85431c6f661d8543034fe75d8543004fd75d8543034fc75d8543024fd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d85434bedf32d85431c6f641d85431c6f631d854300cfe70d8543004fd70d854300cfc70d85434febf40d85430057f75585431d57c75585430067f65585430067c65585431c6f4615854300cfe76d81430067f65d81430067c65d81431befa60d8143034fe75d8143004fd75d8143034fc75d8143024fd74d814302cfd73d814301cfe72d8143004fd72d814301cfc72d814335edf32d8143014fe71d8143004fd71d8143014fc71d81433aebf41d81431befa40d81431befa30d81430057f75581431d57c75581430067f65581430067c65581431bef8605814302cfe76d91521b6be64d915201cfd75d91521b6be54d91525febd54d9152024fe73d9152004fd73d9152024fc73d91521b6bf43d9152006be43d91521b6bc43d9152034fd72d91525b6bf42d9152014fe71d9152004fd71d9152014fc71d91521b6bf41d9152006be41d91521b6bc41d915200cfe70d9152004fd70d915200cfc70d91521b6bf40d9152006be40d91521b6bc40d91525edbe76d915202cbe76d91525b73f75d91525b73c75d9152006be63d9152006bc63d91520073e53d91525ff3c53d91525ffaf72d91525b7ac72d91525ffaf52d91525b73e52d91525b73c52d91525b7ac52d91525b7ae32d9152006be61d9152006bc61d91525ff3f51d9152006be60d9152006bc60d91525ff3f50d91525b6bf75d91521b6be75d91525b6bd75d91525b6bc75d9152006bf73d9152006be73d9152006bd73d9152006bc73d91525febf53d91525febe53d91525febd53d91525febc53d91525b6bf72d91525b6be72d
  | 18 => 0x86058153034fe76d95431d67e65d9543214fd75d9543024ff74d9543024fd74d95436367f54d95436367d54d954302cff73d954302cfd73d954361e7f53d954361e7d53d954301cfe72d9543004fd72d954301cfc72d95431d67f52d95430067e52d95431d67c52d9543014fe71d9543004fd71d9543014fc71d95431d67f51d95430067e51d95431d67c51d954300cfe70d9543004fd70d954300cfc70d95431d67f50d95430067e50d95431d67c50d95436157e76d95430347e76d954361f3f74d954361f3c74d95436375f73d954361f5c73d95436375f43d954361f3e43d954361f3c43d954361f5c43d95430067e62d95430067c62d95430073e42d95436373c42d954361f5f32d95430067e61d95430067c61d95436373f41d95430067e60d95430067c60d95436373f40d954361e7f74d95436367e74d954361e7d74d954361e7c74d954361e7f73d954361e7e73d954361e7d73d954361e7c73d954361e7f43d954361e7e43d954361e7c43d95430067f72d95430067e72d95430067d72d95430067c72d95436367f42d95436367e42d95436367d42d95436367c42d954361e7f32d954361e7e32d954361e7d32d954361e7c32d95430067f71d95430067e71d95430067d71d95430067c71d95436367f41d95436367e41d95436367d41d95436367c41d954361e7f31d954361e7e31d954361e7d31d954361e7c31d95430067f21d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95436367f40d95436367e40d95436367d40d95436367c40d954361e7f30d954361e7e30d954361e7d30d954361e7c30d95430067f20d95430067e20d95430067c20d95430067f10d95430067e10d95430067c10d9543034ff76595431d67c6559543625bf745954362ddf735954361cff75595430067f7559543624ff7459543006bf7459543214ff7359543006df7359543004ff725954301cfe725954301cfc7259543004ff7159543014fe7159543014fc7159543004ff705954300cfe705954300cfc705954361d7e76195431d67e761954361c7e761954360f3e74195436173d74195436167f64195436175e731954360f5d73195436167f631954360f5f43195436173e43195436173c43195436175c43195431d76e72195431d76d72195430067e62195430067c62195430073e421954360f3c42195436175f32195431d77671195431d77571195430067e61195430067c611954360f3f41195431d77a70195431d77970195430067e60195430067c601954360f3f4019543025bc7655143036bc7655143024bc765514302dbf755514302f3f75551430073f6555143036be6555143036bc65551431d73c65551430079f7355143025be7355143025bc73551432179c735514302ebf635514302f9f6355143
  | 19 => 0x5e00100000280120010008040000001000001000000400080040020010000000002006000007000c00200180140000010028008004002000800800400100080880160000018020000000024fe76d8d54216de63d8d5402cfd75d8d54034fd74d8d54216de53d8d54216de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54216df32d8d54014fe71d8d54004fd71d8d54014fc71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54216dc6358d5401cfe76d895420eee62d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d895420eee52d895420eee42d895420eee32d8954014fe71d8954004fd71d8954014fc71d895400cfe70d8954004fd70d895400cfc70d895420eec6258954014fe76d8554206f661d855402cfd75d8554034fd74d855454ebf54d855451e7e54d855451e7c54d855451ebc54d8554024fe73d8554004fd73d8554024fc73d855451ebf43d855401cfe72d8554004fd72d855401cfc72d855454e7f52d8554206f651d8554206f641d855400cfe70d8554004fd70d855400cfc70d8554206f4615855400cfe76d81541fefa60d815402cfd75d8154034fd74d815440ebf54d81543ce7e54d81543ce7c54d81543cebc54d8154024fe73d8154004fd73d8154024fc73d81543cebf43d815401cfe72d8154004fd72d815401cfc72d815440e7f52d8154014fe71d8154004fd71d8154014fc71d81541fefa50d81541fefa40d81541fef8605815402cfe76d91531f6be64d9153024fd75d91531f6be54d9153646bd54d9153034fd73d9153626bf43d915301cfe72d9153004fd72d915301cfc72d9153006be42d91531f6bc42d9153014fe71d9153004fd71d9153014fc71d91531f6bf41d915300cfe70d9153004fd70d915300cfc70d91531f6bf40d91531f6bc645915363ddf735915301cfe76d89531eeee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d89535d6df53d895358e7e53d895358e7c53d895358edc53d895358ede43d89531eeee52d89531eeee32d8953014fe71d8953004fd71d8953014fc71d89535d67f51d895300cfe70d8953004fd70d895300cfc70d89535d67f50d8953005bf74589531f5bc74589531eeec6258953014fe76d85531e6f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d855301cfe72d8553004fd72d855301cfc72d85531e6f651d85531e6f631d855300cfe70d8553004fd70d855300cfc70d855353e7f50d85531e6f4615855300cfe76d81531defa60d8153024fd75d815302cfe74d8153004fd74d815302cfc74d8153034fd73d815301cfe72d8153004fd72d815301cfc72d8153014fe71d8153004fd71d8153014fc71d81533fe7f51d81531defa50d81531defa30d81531def
  | 20 => 0x780040000000008010002000003800001c001018002c000000006802c0060050000030000000002802800200000000000340010000010022000004000000602d000000800a000005000003001100300240060020058014002007002802c00200d0010000000004000003c022006000001000800400b0000006004002000800000500600000100010028008016000006800000400c001801000200200000040000050030000000000001800c0000070008028000011001800c02c0010008000002000004800000200a0058000010003001800c00000100000280080020020010020002000000001000200180180120010008030002000005800001a0060038000002000000000400c00000000000020020038000012005000002000000100880840040060060000002000003800400a00900600000000030000000030001005001c00000100300000040040000004004003001000001e00000580080060060000008004005000001c002002000000003c004000000c00000000200040060080048014006001001800800800c00000000040000080004002000000000400200200380100000000070000002001003000400200700180000080000000004006002000800400e00c0000008002001001802800200600180040020000000010004001002000000e00000000280000050020000022001001001400200100000080040070000000000002006800c000002002003800a01100180140000010048000000009000002c006000002801000a000000002c0060010000024002000004000c000000000804001801a001001800a00a0008004026003000001000002100700080060010030008000000000800000a003003801c00600100000040140010000004000000000002800e001008000000000200f001800600000280040020040020000000001001800000c00a00180200060040048000010001016802801c0000010024004001003000800c01100180180020020000000012011006800401400f006800000000e004000c000004000000400a00100000040060120070000000005000001000e00b0010000012003002800004a00a013800400000000100040020000008020008000000800000200800100040040000020010000002001800401e0000048008000000000002000000000000040060040048028000000002001000a001001000000000300a0010000000000800c01801200000000000000008004002001000801000000000000100000030010000000006000802c0000000020000006002003000c00000a000003c0020000080024000000000801800a00600080080000000008008000000000000c02400200000000020000000000000001000802400000000f800400000e0008014004000000000000400f005001000000900300000
  | 21 => 0x17ca1d8000000057ea9e2aa00000005660000000a3c5e028b86c944ccfc0000000000cfd0bf0000000335515ad24162c6c3d21fbc0001192dd800102600046518cc7c600061981e4f5e9ac5fb89b43c6d3b000186400040d309350067600059a94b8b90b9300000000001cd301a5543060000d1b48c00000009901096ec9e8000351cc367f90000001356b7c5b934804a22544441580000a2e3a805ac5fac25000000000000000000000000003c70000500a4534a00000000002cc08180000005e580013be27b3140930cd669616818540005410000828a8a3d40000a7c3b80f85001a6934060d01200e0d306311a497519a88d84c91c5cb880ad131abc8f72b6d2079ea09be2851a6012491630244c15480002a905b2540002001000000c0090000000008002000000800c000001800000e000001800000400000580140080000000000004001000000c00e001001000c0200010000000008005001003800401700f802c002000000000000800000680040060050008004000000003800800800400b000000a006002001000000000000b000a00000180000020000018000000001006800000c00e0000004000000007007c00200500100000000030070000004002006004c002016000000402800300000000060000000000000005004804000a003001003001800c0010018000000000000400a0030000000000005001805c00400a000000400600000f801000600000380040020000028048000000000003000000000500500000020000014008000001002801a004000800c00400f004000000000f000800800a000000001800e0010028028000012000802000a000000800c0160000040008006001002002c0020000010018028000001800000a00b0010044000000001000000400900080080000060010000002000008000400000f00300180000000010004000001001800000c010000001400200900180040000090060000008001003000001200100000300100050000000004016006000c01800100000000000030000014006008002000c00400b0010004008006000000000000200400000000080000004004003004800800a001005000000c00a0028004008001000000400000300800080020060020000000009001800401600b00300180020020000020000008007803000e00400280000020000008000002002002800c0000000020028008000001000000200000a0004000001002000400e000000000400a001002803c0160040050018000003003000402400b004800c0000010000000024000007805000200b008800c0000010008000000006000004c000005000000400a0000000000000004000800000a001001000000e0010070014002004000000401400900000380060000048008000001002000802000a00000000000030
  | 22 => 0x3af000185937cad4687800000002c0fe000000045c000000024c0000000000000c245151cb8cea87c64a00017180005dfb135414000000000000041913f000032a000000000000007214d80000002f60001a84b4034400000000001c3000215c00000059e202c4063bf30d2ab400000043800703aa43948092d4000c00499a8e83b20004e19ae15da00000000000000000000000b8000046d2a0ce6491767da760d38ccf1e59a3c00000062600009743b862d95b8dfe000000000000078003c000191c0f600000000000000000cb000084800008b00008ef5070000ba6c5f0b09dd005613848e1820b445fe3c8abd097040a37b91dc0cc7ca5a70f557305d65732fe0000a2868d960480abe14f715700000001fb000089abe44fba43c0009752e906490f436a35ca900000a1e5629e6198e0000001c2c5280000002be400000000004a00000000003301a7a00000000d105e53d152209d72e75b0001950000000000184c000000000000000000008700014b800000005340000004600f9c0000a552800000004d10718001a5e7f1125aaa89a80fc02892748de5f81ca283468e000000000030200062324e12e8af32349295540bfc0000f90ff0ca8000000000085336a00018405cc34d8ffda7c75a09a99ec000ce30000830eee00061e8000bf494e165b15c7660001039c387dca540a28c70eea3280a3243400000065600000002b60000eec93608062c190800000000001486ae00054110e8f2a000000000000000000000000000001ba2a4902ec7669c91890ce6ec000290c94e74c5ed2908c0a66805b91d4000c1211825b8fb88e82b19e1c92c0002919c480c8c0b6052f7da44b8e00011758fa2f418cb088f585652830001a5000036320fc0006dc5e181641a455b62494bc77a26c0c113a07f89b60a495d0772ad51c323cd4aa45818482e1224d454c6a6bcc78c9f019202150cb900172ca96080003ce0725292000118a5f4000ce70001c818bcb660150f6108ca8b27e00017f60001c0a2743140c800008a98e200063ca1dc0bab053702e64000000000000033e0000da83d5232a1f0001be8e381270f22f0194a00f1baac38b08c344cc133961840735f80000000002410dc98ca00055782610b831306081f4e048490000000e0a2b137726e115a00011d10a54c60a03308a3c2ac858000135812231b0000000000b02000181c7b29020002fd0fca000000174547cc3600000000006ea0001b94ea8c1e55900000000000002a6572a0001e833346f08e236119bc62e44204925f09a08e4034b3c96d61d20972e2cbe284a4c1a94cf188bc2b52b483de9f60000fc8282809416b3b12540000000001186baf27b9b9d9c800000001b8d4c6041e180016106912cba7e40000000f700000005183f8170c00000000000000002695b52d500006a73048
  | 23 => 0x13c00018800023a40000004e78000a98993076800000048c00000016066f95bba1ac93e20e3f73340ad251b17a8578000c6d259a89164a04e10c9b34c8e0004391bc400047f02401e994e4ee15e289d6bab7e000000000092100015e80000005af0000bbaae200000000001f711d9b14e6a576000256400047b2d092440000000000c7870a00062a2dd0000000643250c9f42dd0001b694580004f0314cfbe37e000226c0000001fa80000000003d9800000000000000000009b40000000000123000055d68e97b00013e54024ed0792420000000000000102411847b083400000053b18040000004e42b2190200019b00000600000000ac0000d0d0002b40000547000000097a5670000000000000000000000095c0000001a2000000012b800018452d8000b8e0002d88000000000000135d8261473622ce91b8ca639490b4ca0000000112832600035d29bcabc0022cc9dc0afe107211913962c0000000d8c0000001fd000173a9d90001841968000498808519ca492f380012d2b5a1a102145cc7a940e80000de1994b89e7c9620006660000000cd900bad400006c03e416d40006f80cf29300008d0000065d1ce78400000000009ba00034284b461707d19447c22af4b182a00000000002b28b5018d0001370b6600006b1ffda683040001790000ad93bdb32ca480001718000e7a04340115c0000c8f00a0390866cfa0bf800078e5af44b9d60e102a5000000080000000027040002e45d533b804440c10e0bc13f01bd1ce9af8f9a00065c223c6f45d02e480002384f03bd0b24000000439adf4000ac40328000e1478200000002ca4c600028100000004cf9f0509c00000000008cc00032b0001536acd000000000000000000000005610000000c5e3970002e9d772cd500034c0a84c0701ba3a914000000000017760003e7000000052200001a033610155a17040009bf5c02d487461c44ff80bc42454b0c8162800074b2391e5c000bb75e527318fe000000258071800000000000008cf693b2b800000010200000000000002aa44360005078cf4000a3800f9c7d04893202b04cc5f04060a1128103200016280000000c754b9121366d2c1da90598fc84320e2d6400090600017f0e320000000d6da24000000157c00041f48c10780006ef1cd9da4bd2649546138000087500025c00008045c6a0d81a8c2c4c1337492a73b57bb2d46a0a7d43c1718ed687649f8000b0e5300000dac9d8ac110d11943fa17315a86ac00000000027599821f111300013fa0002c980007160000001ef4d5a86e4b2001800000027dab940003622df8000d407bb00022480006a5000038000020f5970001682000244992000086d095a0d41960004f100017e2000000000066e000119262943a0cc0498d68f8c00061f1f1000000000017085b64202a201b4000
  | 24 => 0xec84678b1cc000894000044896800052c8b7819a5132be8e7d9d66ae36b0b51a6c0000000000000224000000134e0003d280017781ed00000003507b100005c8000a7559880c41165330e999dd02000017d854d36eafc24000d83ca70400029b5a264920002a3c0004565a6800094400000000000000001ab23d4f3cd216010020db27c22261bd4fa2af60ba97c982e4c066e000087a73359697b81de8ff09c8a5c0000003b02164000d1e359000083a4c23b61fb566c728588a91c00072f41480019ee01e27e8ea85382730002e6c5906cf023800000055a0a5877c2dc3075b40000fa600042f8000e72a57000000173c8c90b7800000019d42a81d0a72000000142881c00060200002406b42aba9e918400040733480003e0000285c000000000000000005c4419b840009bb5c9224d16cad12951da800075140aaa61a7873f0002ac416a4da3c58e690cc4260002f3400000000020c80000004ebac602c65270fd000095e0840849c780e600044d057cf98000000000039608e18a23e9042ad8315146542c94f00016097a48655db19f0952aa40001af402cd081c6b3d8000b701be8000fcc7994ef20d0ff63c449d0a2437688e0d283a90002ad29e28d53167a143200016f6075591800099e2370e8800000077300020717dc5296412ba9440b175b7289442039611f000074a514290902000000000011d80000001888000d9200035799d0000000110318000000000000000009ae17422940008445998a8972884242d306cec6d050e78971290c8b55a967554a72400027105b036f0c49f145163e2577a284000c3200000008a47a348626f10184dd33d27b4e2c92438898f8006cf34280d64e92900007043c29e61c02607596400c56688aa80005b65808fac0002b467c800000018f00026f5a1c58c000000000000013108d851062700000000006d210e800071cc2b420841030075e6a10a452140004f98a5528a1f56811cd09cc986006335c00000000015c91da00013333e000000000000017705d81920e887bc568578828400033851799d857c8bd000228d6340004daa230cccd3507c80000008bb07816ad9ca6f21900000b48b1f35106996c000037132595c08ee199800000046e0000000d8e2d52a4b234c7a000000000189c3601ac200cb960002b88001502d032ff800000000059f000000095e00023e0eb21a70001d58db63845390fed64e996132188584c6fb425b498a943dd2bd8a687ac25f193a57d4222520e332f80003060000000000d0c000006c50eb15489ae3c000930000023c5de44004b837400032f5770001482000025890c000b780000ac80002e700014dd70e000334a5888ce0000000d2810400000000016c86d14e98000c0c9aa178b1e146621423827ac21868b31190bd10c41366f2cc00000000002500aeeb4c000
  | 25 => 0x12fcc46800027780010360000148000fc899d44480003748ab04f800195e66c0000000000c8c6748000b2400000028c556e4bf1769424000ae70c5a784a1e0004b389a1336636000000045a86c0cc156459e29e17d0000000ca018700007e202300007a5268c9900016200001770001219a90abb0739d191aa73a000000127295b00000006869fa5d023ec00000000000d5a4a000352000000000058d800000000000000006d80002a413a80001de00034701c2738355261d46e64d4ae8000000bcf000000152a12a5df104008c7c938390d00fc0003e58fb00000004f80328de083940b1094fd08064662ca400077d538a3e55fe43701d16a4ac8cc43a1a6417f49d43ae8cad1688302ef80008fa0000bd9ef0000000000000063a4bc00004f91d67365c400349b6535509aa9d7026fd5ec8a8170624e0b5000113c8a617934b5208ad31a926647940940000eb4ce672642f0c0c9884ac0000ca85e6c0c04819c000092c66d000000000068b046d08a4cb00000000003f40a833280a0379442ab758b81b400030b99366de17c8a9ce340000001cdc8880003d50000cbc534000000000000022b8a600000000001a14b6e0005340000000000185800150a2ce4e380006809da1d400007689362568000000b225e720280005430000000f5655558005f18d264000034901fe7f45d82ad8b584a468a80018e03b00bb00009941d415e9a2000023c0001260000000000196c0000001b9800000093d0000000fd631f00000018e82d933383f8d3200000031980000005c4800153a87b16680019a60130d61d703c4000543900c0000000000000000825111142010c7864702d7d32842e5f18000260c6b3fe8000000b3d0000000b5c0002c0047c0000004b2826c2200001bb000038419a4589414e421695b62b08e440a90003154000bef62180004e486331c21357b64843012a5800051c2428000000000584800000000000009f4e9cce000029340000000000000000c9200000011b20006992988f3658300015cd65ebe90f634a54b09ce08316e12da00000026c00005fd0128000000b3b2c30028e3a3686519ec187600000032452e62b900020601aa37f65923dcf640ba3dbaa401489cb09d88080000000002f7899204a3da028c79cc160002c1c000618000099c0000f43b38580cc40002ba80012ac9785d88000000bd75b9a7d400000015180000000000ad80014c2000511292800094b0002bf945a00053232f40000000000bf00003df00014b44f40000000c280000000000d4445c000000239569e8230000000000a8a0000000eda00000030f0f28c1000011257d6ae907d9bd819e84f5fa8000d0c50122a02cc64a5f4300345cd660000001d1158e11512e8a7400064f68f9d498c6be800019b8ede639126b1a8ec400017109255fa0000301a4c2c
  | 26 => 0x96b8a4790001a301a0000199578e00023c979400000000000000009f24d0800000000031680018060005ba80000002f700000018a209500000004228c713825dca165024b615e47000002ee265c0007e22790000bbc000000000000000043086fc00019c292a0dd1a445f4b31640a7e36542ea5c85844de06303996a20000000d3d6ce0000f0927126a64a36500003c00000002345152d1a04d00000004430000000000000000000000035560780002e0cc900032c4b0a8aa4cd1d4cf3460b2f080005bea1c14133fc10e5be4ee0000aa000013aa50516e36d000034447e06b000087c00055150912ac000d414a6800000000059597b400033122f000000081e0000001a0200000034508e6c481dd0001768b841f98b4c7fc0000f401f0000d0900000000000000000000e3628c00000018f65ea1220000000a6a00015000009e71e418b8d8216d4bf169875c2ab4659518e460003c6800104000045d33884d4b6f0001088bf2ac9000000000033e000308c000aa86552a509ca66d0001f7461a43f0d9aa4c00000049b80000000000000001a7003d00000000008514f50001688a071ae8c040003233830001a1610a000270172c48d0fd820436cc1c5cd000107c49a06c800135a12c03f800024a35c5868000000000000000159e0000b325bd91208800019387d4ce145980000004b600034dc00038349400000004d900015f8f4c80d0000000eae00000010a80000db3e180007a200013c978c9fe4e3524127841600030783b800000048aa61036257842d8000000a10000000143600000000007809ef00032ac2426ac453b260f12d4653f91f8000122408a61505c0890002318cf2b39366187c210b2c231b4a808a72a59309fc000c4b0000000e4a27811404e820400024c9361510c4a19c87d98dcc7516b939d8f81b80ac94308304f50003060c560c045f000000043221f00000007f60d789bd1bcc091430e2013c0004918a4d87e5312161ff000004063087fd3a20b42ca311000067210082eda740e542b03c53fc0004581ac400000000000000000002a78000e7843b2ce0c203e60002dcb0a17a000000003a54dc000528b1e800048744018d4b3c72d00000018b2461148000090200000000f00008fc14c8000dfc6cb3111dfc65c67f54e1b986001bc3f48bb8482a701c9a2102c41d052f05f400046a245277515e1542660a840009a90b8976d74c000000123d19044f3eda6257d45895400000782a064aa00016a61f04d2061c2e87485d11dd8e62558119a1818347d80002d5c00024764aa0680000000000000ed05f527120e000098c0001a4800054d55180000008c544593f82946b73f01955862ba560c8fa147e2400002600dc6000000036194201a389998d5b6c97451201d2ae16c0001a5c98683c4b085689107c71b324697508820d
  | 27 => 0x170a9094938980a3eb610002f556284240338700fc6be253a0f4d36212f25b949800013f02d80017040000001a34b6000000000016386445d222b07e0c47000026494600009682b0f70000000288c00007600005e99ea16853f2ed44a60000001ed99202d14c419044b626b10f17ed6685ec4a89a116321341048a49416a7b5782d615eaa913a0800000000000000010a43da0000000000632000000040a0000a60dc0bb26870001a00e9a91e0000000c7e9ca51d80000000005718d18000c771b492a0e569e52880984bee9d2610b2b50620000a71f3c00047c00019754c000050491b015677e00033c06c26d338c00016aaa14495800111a2b800000000000002300228e282e902aa0500005030d800019b600057d00000003be553000000000055580017fc7d4000000103e0004970000000d2b0002c841ee779241a8f0032781652112c000c5220b8994fb400035e2f587140000001bcc000a0255e0000daaa7824b845098a66a28d13554f278f1bb8aa07da31a0308e3caba0180ee9bb578a0004f8a15000000037a00492d61581ee06f8836c830000d4d7fa52b00000014321db19e0f346a800021094e099a00000006a4000b631042414f2c94651e82c8f5cb6516e000014c6eb1e484dc7228795d70bb14cc2b700012c9690453305341c00056c5a510e00000005d9b2d9a0800000001dc0160000989f7800000018c34cd56017801f115579800005f2d144723f95f029f0f7c8994d40000000140000000000099c23c080000061d0dc8001534bf9000000067ec85269971400000056b05214a42d243a1ba4adecb04883510ef8bc428030e0000b0b013807525e00000000000006585f6319000050d1e910c40000000000000000000000000000000000008bc00000000029cc6823164e6845d9e89e4460800000000037229acd02ae460e96581b89793ec80007420001e30000c740002f5b0c1206826000221d3e8000000000124071507e95b40001363121e140a6464478ad6c0007f20001c343983a62530275626cce0d6800000000000005e4aac2c425ca45000069e0000eac000d113f989219845da4730000000a9f274a2717a872c00021fc4e887e622800000028e5d9000000000009e0001188a773fa80018c4223420025800043c1cc1304000aba32faf600120001de00007b600000002b8be6bed000000181c0004a980000005ca0002acc7f03cf3882be05808ec0000001884ba30002b5cfce00065c8000ad6b9c0002c780000000002688000520190800000000000000000007306618c300000003c9800177a000000000000000000000000000000208edd5440001a6832563ad2e00000013d859b1278001a00c0136b97c121c25800023589d6cb30008c14a500000b21024e94000000173c2aa8913861f8405a9525eea8215
  | 28 => 0x68ca7ec68a000079962c4560005601458cfa00013e1fdd6d20000002ab05b4026000194c30a1f4000000000000000000007d20001b700000003c20100001614000000000007226e0000000000942145000000800067680000000000001948c402773a299c4e8437b193242d9266a350c02f00004450001b7430c000000275557e00022832280004120001b40ecc0000e5023132a11655e80000e2000000090800005449f21bcf408622992d70fa464517504f41544045f800003904be2ea8000000ae156e00005ac0004928001792cd600000012ec73e05800003f000000000000000000000000d902135d49a3940a0001f78000000000314800069000011c04008e8bdc3b22a105d62e500014f8576c9d0f588840b4bac2c728a472046d5470000000ace00001340002c612332889e2000000000000009c000000088eada1af8f5d460cbf1b3800123600048e80000006bb620a95844ac8824700000000000000000f740000000000cfc74f00000012d487d22d2458b9a21828387f8c3c28d0310accfae61100016d10d4adf3232eb53842ba000000000011100000000000003e0190c00003b08989540003f72f32ae000000000000005c09e9000000000a4410fc80000885a72582718b2a1da00000000000000000000cb400045a800021aacc0818000000b7a0001b0cff40d35d5b07c8220001f2ad183288a823d18c00000005c89ac000049400000008340000578044c4a3b216516b447aade1e288556c40000000000d3a00000020b138ab4b0000000dd0cfe49d80000005d703500006bc3ac000085cf2000051b19e13029d00f3a8e58ce00018a9438000c7229b00019b0b794699634598296000037ccb25b200031696fe00012b276c00000005e93d0000657550a63966e0ce0f303105fe1c700032dc00000047f00018ba91100000019741510000000a2400000016952981523eb042c3227fe1e62bb072a00051929940000004152258cc82160e08c4010600002f9a0d98c8bf28e8000000660000247c000d430000000aa61f2434000112a6820003320856be7187b2f16ac7094e49c9c0008ae0002a240009470920ab186ac053819390df8cbb3bc0000000000000233555c63b5ff9d940000ec5f300000000004d193841d000000012a800080100034744e22452c791c46521962231c3c17200000006847044a14839348ebe5ce0ae000000032d546800046a00002b87a855ca4f35400000000000000a0400000041d000000038959900008b697a00000011b600028a8000e020005e3000117286902f131c0004f3000000014eabe50aae7d6841ce32600001c453a00034c51fa3b646a000124c39961d000157294a00032a54b489000000011be49308ea4f158c9682822ba18de5ba3a000018acb430d233a00000000000e7133cd060
  | 29 => 0x8e301980014d892d0612f080000005b8800000000000000000000000000f983180004450b1c35c95a34630a985a7d0452000000065c0000000000c803060000000c144140000c6800000000000006ab0080cc00000005c300000005e8000000101e0003df9aa548c3920ae8000a58cc56731538000b101be192c00025e2183020dbe0002be17d8f4e59a6280378000cef5a00cc92fe3fd36c297c00000050622057746900002c488047ec0002c9054ca445d08a1104400059f80011647000000000c587720db92ec0001c500026940009b90000c4823c25923595883ae0002f7a9747484155258b046684901d380018520000002bec00040b22c80fcfaac4f4ac0c89434143000251086ad3f4781e2800000003d8bf80508e131ba6988a208d5942c18000c394f31e212520000000000c1c3a900000009f000034a9e8958606c61b8000d1276e20a0d9000ec9c606800000000051a280c740b0f1cf06a931ec9a2889d541aea67094af44b2283335a9b38802a4e0a2278c6e25bc3c910d8e8e77164380010761052de9e0c85025044fb0bd08e0c306d1320c2800060a86399d4c2746e800000069f000000000034e4d90a0c17e0000001fa800079d3d680000e0cdf0000000000c063b080551ae8b8161afc94420001138b8532280500000000000000000ce8f6a3b134517897820631c3b2788d0bf62d183ad0569fc59c2488452aeb00023d09ec0a2620034107a59f60889d80006b62d504680004275e9895c6960005e431a00b087100029a4a7624a00000000000000000000c4c0000002130
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8bc845d76148001d8a6598ec29000a1f21d65545201551e422caa8a4002a7481595514800d1ed0fb0aa29000a2f21d64505200146e43ac698a40018ec865cd21480051d90eb1a4290016aea13655012002c7c43acaa024005cb87650d40480a76710aa1a80900027a21d325012001e743b264a024000f89434c94048001f428290a80900036c04174d951002c5fc3ae9b2a2000dd010dcd654400147d09baaca880030fdd2545951061e2e39ca8b2a20048de87dcd6544001ae020baec88801a1fe1d75d9110006f0086e4b222000a3e85dd1644400187eebaa2c8882db2b1cb545911001c7743ee4b22200087d859d9544400117b093b2a88800237e0d76551100246e41aecaa220008ef825d954440071d904bb2a8880023be0974d8d1001c76412e9b1a20058be849d9534400117b093b2a68800237e0d7654d100243e43acaa9a2004a5c83595534400d0fd0b3b286880021f6167650d100043fc2aeca1a200687c855d943440011df04bb2868800e3b2097650d10006b8086eaa1a20048bc875914344001878eab2286880e6ab2096450d1002c6f43ec6a1a2000c5c75d8d43440011bf06baec4880123720d75d891000c7d43ee0b1220058be849d9524400117b093b2a4880022fe11765491002c5e422eca9220008df835d952440091b906bb2a48800e1f21d65549100061e3a2caa922035a5c835955244001b6021ba2a48801a3ba1f6254910006563a6c4a92200687e859d942440010fb0b3b284880023be09765091001c5e43ac8a122003aac8259142440019e021bb264880023de05764c9100047dc02ec992200687e851d932440010fb0a3b264880162fa10764c9100045ec20ec9922000cf0101d932440071b90eb1a64880123b21d624c9100247a43aca98a20019f080dc931440033e50fb82628800e3d21d644851000cf8406e690a20018f4865cd21440033e100b9a42880067ca1f70485100247c43aca98220029f081dc930440053e50fb8a6088006f421d314c110016e843a6298220019d0874c530440037a50c98a6088006f4219314c11002768432629822004ed3764c53044005ba4ec98a608800b741d9314c110027683b2629822000ed3654c53044001da2ca98a6088002f4e09314c110006e9b926298220009f08748530440017a30690a6088003f04c9214c11001c7c43ac890220029f081dcd20440051f10cb9a408800a7c2057348110014f943ee290220009f0874c52044001ba2e698a4088003f04c9314811000df043a429022002de08748520440033c10e90a4088006f8a19214811000df0432429022003ee0864852044007dc6ec90a408800b789d92148110016f03b2429022003ee0764852044001dc6c890a4088003b85912148110005f1c1a429022000be1834852044001bc6e690a4088003785cd2148110
  | 1 => 0x501baa86a801a5721d5350d5001c3e42ae7b12a01a93e87dd1525416d878edba2a4a80034e1c374549505ee1e3b0e8a92a01ac3c74d915254001c5c85b22a4a80034e1d3705495000c3f436eaa12a00696c8754942540030f90cbaa64a806a4f211754c95001c6f43ec6992a0ccb2c84549325406bc98c6a9264a800a1f21574d85500051e422a5b0aa000d5a30dcd5154001cac63b1aa2a80061fa1b75505500145f43ec8a0aa000c3f75d91415400d2e90ea8a82a80ab8d191515055000c3e432ea98aa00187c865d5215403527908baa42a80065e20175485500347d436e090aa000a3d8494f655019787eebba2caa00122f21172d8d4000c5f436e8a9a80c193e87dd54350187878edbaa86a00034e1c37550d406161e3b0eaa1a8016c3c75d954350001c3ca7b2a86a00122f21d6550d4002cce43aa6a1a8000d3875dc143500010ff0ab9ec4a001a1f21573d894002c5e420eca928000c3f541d952500070f90eb2aa4a00062fa1b745494000cdd406e8a9280059ac8754942500031790cba264a005a4f215744c9406558e42a869928039e8c6250d32500091dd0fb1264a000a2f21175d85400051e42a87b0a800287e87d95515000317d0dba2a2a00030fd977454540006d5106e4a0a8000ea621d89415000b3690ea8a82a009b8d195515054000c5e432e898a801693c855d1315000337100ba262a00163ea1b704c54000c5e432e890a80c9b3a85dd1505003567108a9aa0a005ace21543541400078ca9a86a82801ab3884549505002d6710aa12a0a0003ca54942541400363c3b2a2a82801ab3884545505000b970eca0aa0a005ace215415414000798a8a82a828000c3d74953654c00d0fd0fbaac8980021fe15765513001c6e41aebb1260058be849d9524c00117b093b2a49800e1fa1f65549300061e3a6caa926003ace82d91324c0071b90eb2264980ba97215644c9301772632aa49926066b8c84549324c001ba421b8a64980021fe1574d85300343e42ae9b0a6000ec532c87614c0050f90eb2aa29800a2f21d64505301351e42ac8a0a6002ab481591414c00b1ed0fb0a82980063721973485300353d42ec8a8260068f887591504c00d8f0eca92a09818ece2115254130004ec43a64a826004cd8764c9504c001e92a4992a098003d4545315413002c5f43ee8b2a4000c3d75d53644800117f08bb2a89000e3b20974d8d200147b43ee2b1a4000cf071dc1634800117f08bb2a6900162f2117654d200047bc0aeca9a40028f4815d9534800d0fd0b3b286900021f6167650d200043fc2aeca1a400687c855d943480011ef02bb2869000a3d2057650d200245f43ec8a1a4000c3c75d91434800959d07b2a64900123b21d654c92016d56422ca9924056b4c8550d324805bd18c8a1a649000378843714c9200045fc22ebb0a4005
  | 2 => 0xc745493269786298e8a92642dcac74d91524c801c5ea9b22a49901a3b21d645493201cb643aa8a926435b4c83551524c9a369d0bb9aa499003631d37354932004e643a86a92642eb4c8550d524c85bb18e8a1aa499003c355143549320045fc22ebb0a64058bc845d7614c8010ff0aba6c29901a1f21574d85320045fc22ebb0264058bc845d7604c8010ff0aba6c09901a1f21574d81320051ec2c85b22a2008bf845cb635440b17908b96c6a88030f9507650d510143f436eaa1aa20297681dd5435440d2b90ea9a86a88aa4fa1f74549515b61e3b6e8a92a200d3471dd1525457b878ec3a2a4a88ab0f1d3645495100717216c8a92a200d3474dc552544050fd0dbaa84a881a5b21d52509510143e432ea992a22a93c845d532544071bd0fb1a64a8b42cb211524c9511af2631aa4992a20187c855d3605440147908a96c0a88028f61253d954167e1fbaee8b2a82028be86dd1535058327d0fbaa86a0b0f0f1db7550d410069a38eeaa1a82c2c3c761d5435044d878ebb2a86a08038794f6550d410245e43acaa1a820599c8754d4350401a68ebb8a86a08021fe1573d89410343e42ae7b128200c3f541d952504070f90eb2aa4a080a2fa1b7454941014db40ee8a9282059ac8754942504051790cba264a089a4f215744c9416758e42a869928239e8c6250d32504091dd0fb1264a0b36cda1774545411559a422a6a8a8226b348550d5150401e2aa6a1aa2a08aacd21152545411359a42a84a8a8200f2552509515040317908baec0a08028f21543d81410061eba4a9b2a620687e87dd5644c4010ff0abb2a8988162fa1276549310045ec24eca92620387e87d95524c401878e9b2aa49880eb3a0b644c93101c6e43ac8992622ea5c85591324c45dc98caa926498a4ae3211524c931006e9886e09926206a7685d91514c40d1e90eb22a29881b1d1d9525453148d9a422a4a8a62009d4874c9514c4099a8ec992a298803d154932545310043fc2ae9b02620687c855d3604c401d9265906c0988162fa1f74595210061ebaea9b2242008bf845d954484031f50fb82c6908033cdc47058d210045fc22eca9a42058bc845d953484011f700bb2a6908063e2017654d210343f42ceca1a420087d859d943484010ff0abb2869081a1f2157650d210047dc02eca1a42018f8805d9434840917d0fb2286908030f1d76450d210256741eca99242048ec87595324845b55908b2a6490a12d3215434c92116f46322869924200de310dc1324840b56d09b2a82908163d21d655052102e5a3b286a0a4283b348550d41484013c90e992829080f391d93250521007c2a1a64a0a42008bf845d7604840b17908baec090803b24cb30d81210051ec2c85b22a0008bf845cb635400b17908b96c6a801a1f2147650d500061f2a0eca1aa00187e86dd543540032f
  | 3 => 0x1b2a8600a75810836550c010fd0e086caa18021f61c10d95436351f42021b2a8600a3d840436550d874bd06086caa18029760c10d95430053741021b2a8600a6d820436550dbf87eebba2caa1b529760e62195436f716214c432a8600e2c629086550dbb47b09308caa1b728f612601954361e1e3b6caaa286c6c5c76d955350c0b33d09b92a6a1b0f0f5d365d894300717216cbb1286c1c3e741976250d8587ae832ec4a1b0b171cc65d89430043f43ecab1286d5e2c42d956250c010fd0e32ac4a1b6f0fdd0655894360e1e3a0cbb0a860087e87d956150c010fd0e32ac2a1b070f1d065d814361c3e436eab02860087e87d956050c010fd0e32ac0a18028f61641d91520051ec2c81b22a4c6c3e7694f645496d47b0bb9ec8a92daaba0873d91525fd56c10e7b22a400cb7719c7645497f47d0a38ec8a92da8f61471d91520045f43863b22a4008bd870c7645497f47d0a18ec8a90028f61431d91525b55741063b22a400aad820c764548015750018ec8a9002ae60031d91520065db84e1b22a4bfa3e851c3645496d47b0a386c8a90022fa1c30d91520045ec3861b22a4bfa3e850c3645480147b0a186c8a92daaba0830d915200556c1061b22a400ab6810c3645480156b02186c8a90022fa1c10d91520045ec3821b22a4bfa3e85043645480147b0a086c8a9002a7a0c10d91520054ec1821b22a4b6aae82043645480155b04086c8a936b8714e631915269556c14c6322a400e1c6394c64549b347b0b308c8a93628f61660191525b61e3b6c8aa2a4b6c3d75d936354801c3ca7b26c6a93070f9d464d8d525ee1eba8c9b1aa4bdcac72193635480117d0fb22c6a934f8714f6458d520045f438c8b1aa4d7c3f7519163548018bca63b286a90032b9087650d5201c3f436eaa1aa4c6c3c64dd5435480917d0fb2286a90030fdd76450d525fe1e3aec8a1aa40693c87551435480b4790caa286a90030f1d95450d5251e1e3a8c9b0aa4008be87d91615480117d0e322c2a91e70f1d464d81525b45e436e8b02a4008be87d91605480117d0e322c0a935b0fdd774595421b6563b6e8a928406a6e85d8d525096d17f08baec2a12da2fe1175d81420061eba4a9b2a6400a5d83953654c80b17d0fba2ca990030fdd474595320061ebaea9b226400aad82d53644c80d0fd0fbaac8990030f1d774591320043fc2aecaa264008bf845d9544c8071bd0db9aa8990123ba1b7255132614af43eeaa1a64c6c5c76dd5434c9abe1885baa8699307171d87550d32006a6390eaa1a64d4f0c421d5434c85d8b8ebb2a8699003879536550d3202c6e43acaa1a6400d1c75d91434c8093390eaa286990e6e32095450d32006a63aee4a1a6439b8e84dc9434c801a58e9b2aa4992f66ba1f74549325fe563b6e8a9264d3f0c53dd1524c979958ec3a2a499003631c
  | 4 => 0xec02528c00002a2803a6f4ee9b73fe91c162431ee000000002d6000260e61e0194d70000000002480019e0006a23015e0c8001091de08c0021e43e40c000002b87e0961f223c84cbe8b00fe60c5515d0a85607580b16c664f80f41ae06d22a1a0764d4729cb34e000ad1be234828cd0bc0f24641687e0004e8350003c26a8000cb2907b400246156000ef8632fe5811f1e33b879c000003a67b85d07822e0f0829c8180628000733ac4286f8b70ce000000000008d90b0002dc171030901f6850bc0b43168e8df81f2927285009b3222f90b8002804b4718000000ac0000000023c750dd0004d8fc8754422388920f3de8400499f3ee000a1a0d2ce8445da0b3208601c000226000f6000112001159a400025c000c833a564358f24720006184a444410000074401b0000db0000ccb20000960001a8000007a8f4972000000f20e20005ec00002000000001b6000000000002d8000000000000000000000000000086126000178000000010da1d000000e48000008b40010d03c4700993340005c18000336000941852f2748001d50000009a116000000460000906c0c392002c4f4aa0002ee000000d6366578001a2236159208d313e2602f968202764b094b0ee088f992a4680000c9824700001a207284559138000000a84898c3f4621029bc0003f1191972ec798000313762986913b0001608600033c29d170a94665440021218e268458dc0248111208401a104f423130c4c0958693d63e45a9731580a0841c148441d1600000000000000020340001c1200008000000000d0000101c04008000380000c00004070041901c0a0040700008030000000000c05028030500200000008010001100805010060000a02801000000080a00c02178080480000c010c8090080002c0900c0700800018000340701c040000e030090300200c0602406044040440001c02018110000000812014060000b00001020000140600c060100603002004000040101c1a0280d03c000000e0040000802004140000003c0a000080180d008000600700801054010040100809008000000301801008020200001404000020040301c01000070000b004010100200c09000010400502d7f17f08b96c6aa31a1fe1573d895461c3fc2ae9b0aa6c387f855d36054c0147b0928ecaa18028f61250d954360e1f3b485b2a86c3a3d84dcb6550d874bd06396caa1b1a9760c72d95430063bb8ce3b2a86c6a3e841c76550d8747b0838ecaa18021fa1c21d95430043ec3843b2a86c6a3e840876550c0147b0810ecaa1b0e97a0c21d95430052ec1843b2a8600a7a800876550c014f30010ecaa18031edc270d95436351f420e1b2a86c3a3d841c36550c010fd0e106caa18021f61c20d95436351f42041b2a8600a3d840836550d874bd06106caa18029760c20d95430053b4084
  | 5 => 0x5e262594079fc17a3a04406219a309241b82de0009491f08e16c229d029a6bc528460064087682721e0501b83e32a0003e0420001d80001c00038000000000804540c90c26a4279fd0005b4be09d02200000050148900e30a128a0fc9912739c1c00600400021c2705242a00056836000460268fd39a1103923b1e65a8c21743621bc41000000000d08812cc4bc000081e2318001e044c48c00074000000e6001270600589a529856c1700e24c28c6f07a1a0000368830004744c9ad01451c000003b6648a900027e2cccb00003457c13000294444000151ce168911c22ae5d44f000438650000511fc0192220e4048305c0683ec3146c1da0746e85700036a454830bf388228389001fe4902ea351aa090000000000004a8d12e03a4c48c41640f4d41e231a000000000000009c9fb1f4000aa9b42420007c1a34784f84b14e0005c44e0e11c8368001414320847707b41014d1289214458800000000924000000008f4d5800182510e8800000000001f14060009b800000000ef0000006803e80041215c2189402071cc090b1006380022a0000007b15321c0000000038a8a42c8ce0006601c9143ea3291192e0c0000e78660003b11b800372794371502c663c101f42f4000000002d27501488519864c9286445e5f8001c31b2670eb88d1727f82a91000053c7a8003640011f93c000000001ac3806982000003000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8000061100011a0000002b48949800049383382942d32a81160000e9e58014800000797006802e0098022000069f0800800001839800000000000580005000136bc7210a54000120e001070a0008c040010000040886ad0b65e42d976250c0182c42a1f655894369d0765e53d93635480181c53a1f6458d520070394e421d9435498303c981d95450d5272e43a1075dc9434c9c990e851d373549321acc32615450d524c87350c9755143549320064321d5450d524c8553149854d4354541154c926152509515046bc4476549325453171dc1251524c9514c473c847650d3250521715c1255434c941484353189854d43541400d4ca2615250950500353309854541541401570c1d951505505006bc4876549325413070dc2251524c9504c073c887650d3250120705c2255434c940480015919304174d951000568648105d365440011d29804373595100057064810dcd65440015519304175d911000558648105d764440011e29804372591100057064c10dc96444001551930437550d100055864810dd5434400182c821d56450d100060720c7459552440015919304374549100056864810dd152440014d193043764c9100053864810dd932440010f198040764c9100053464c101d932440014e192040764c91000c7425d8348530440051d0985cd314811000c7825d8348520440051e0985cd2148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x110039a10ca921d5450d524c801016d49043aac8a1a20008076a4831d16554910
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
  | 67 => 0x1549
  | 68 => 0x1409
  | 69 => 0x150a
  | 70 => 0x128a
  | 71 => 0x16c9
  | 72 => 0x1449
  | 73 => 0x168a
  | 74 => 0x12ca
  | 75 => 0x1849
  | 76 => 0x1489
  | 77 => 0x180a
  | 78 => 0x130a
  | 79 => 0x19c9
  | 80 => 0x14c9
  | 81 => 0x198a
  | 82 => 0x134a
  | 83 => 0xa0996
  | 84 => 0x138b
  | 85 => 0x124b
  | 86 => 0xcc996
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
  | 100 => 0x138c
  | 101 => 0x124c
  | 102 => 0xcc9d5
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
  | 131 => 0xb8b16
  | 132 => 0xccb16
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
  | 145 => 0xbcb55
  | 146 => 0xccb55
  | 147 => 0x154c
  | 148 => 0x140c
  | 149 => 0x18ca
  | 150 => 0x178a
  | 151 => 0x184c
  | 152 => 0x148c
  | 153 => 0x1a4a
  | 154 => 0x17ca
  | 155 => 0x19cc
  | 156 => 0x14cc
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
  | 169 => 0x184e
  | 170 => 0x148e
  | 171 => 0x18cb
  | 172 => 0x178b
  | 173 => 0x188c
  | 174 => 0x160c
  | 175 => 0x1a4b
  | 176 => 0x17cb
  | 177 => 0x1a0c
  | 178 => 0x164c
  | 179 => 0xd4d14
  | 180 => 0x170d
  | 181 => 0x15cd
  | 182 => 0x1a8b
  | 183 => 0x194b
  | 184 => 0x1a0d
  | 185 => 0x164d
  | 186 => 0x170e
  | 187 => 0x15ce
  | 188 => 0x40e
  | 189 => 0x74b
  | 190 => 0x188e
  | 191 => 0x160e
  | 192 => 0xece93
  | 193 => 0x5cd
  | 194 => 0x74c
  | 195 => 0x194c
  | 196 => 0x1a8c
  | 197 => 0x1a4d
  | 198 => 0x17cd
  | 199 => 0x18ce
  | 200 => 0x178e
  | 201 => 0x749
  | 202 => 0xcca16
  | 203 => 0x1a9951
  | 204 => 0xcca55
  | 205 => 0x74a
  | 206 => 0xccb96
  | 207 => 0x1a9952
  | 208 => 0xccbd5
  | 209 => 0x5cb
  | 210 => 0x40cd6
  | 211 => 0x160cd6
  | 212 => 0x5ccd5
  | 213 => 0x17ccd5
  | 214 => 0x1a9953
  | 215 => 0x757d3
  | 216 => 0x74a53
  | 217 => 0x74bd3
  | 218 => 0x170416
  | 219 => 0x75614
  | 220 => 0x74a14
  | 221 => 0x74b94
  | 222 => 0x15c5d5
  | 223 => 0x1a9954
  | 224 => 0xcca099e
  | 225 => 0xcca49dd
  | 226 => 0xccb8b1e
  | 227 => 0xccbcb5d
  | 228 => 0x745d3
  | 229 => 0x74414
  | 230 => 0xcc5d5
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
  | 5 => packedAt gbK5 (36524+((h/195+packedAt gbK5 (34574+(h % 195)*10) 10) % 774)*11) 11
  | 4 => packedAt gbK4 (3472+((h/16+packedAt gbK4 (3360+(h % 16)*7) 7) % 82)*7) 7
  | 3 => packedAt gbK3 (245+((h/1+packedAt gbK3 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1c6381c7e38e3e381e3f07f83ff0c10f0d34cf
  | 1 => 0xe07c01f8fc0fc7c01fc7f83fc1f30233323b33
  | 2 => 0xff8001ff1ff007ffe3f8003ffe040c3cc3cc3c
  | 3 => 0xfffffe001ffff80003ffffc000080fc0fc0fc0
  | 4 => 0x1ffffffffc000000000ff000fff000
  | 5 => 0xffffffffe000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x820904121020a088409050818a0c105051045
  | 1 => 0x40442088480444410842a01301430212122112
  | 2 => 0xb480451204900094429010a4a4040c28404c28
  | 3 => 0x25090c0016a890024324528084080440e80e80
  | 4 => 0x8001b4f27239000630108695000bfb000
  | 5 => 0xda7271e480000004000084063186abbf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffe8fef8eee8ffffffe8fef8eee8ffffffe8fef8eee8ffffffe8fef8eee8ffffffe8fef8eee8ffffffe8fef8eee8ffffffe8fef8eee8ffffffe8fef8eee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_26929
namespace PEqualNP.Outside.L_meta_26929
open PEqualNP.Outside.L_meta_26929.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 60 := (concat bs1_4_0 bs1_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 40 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 3 zero,inputs.getD 2 zero,inputs.getD 6 zero,inputs.getD 7 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 0 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xffffffeaffffeeeaffffffe8ffffeee8ffffffeaffffeeeaffffffe8fef8eee8ffffffeaffffeeeaffffffe8ffffeee8ffffffeaffffeeeaffffffe8fef8eee8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_26929.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[8,3]⟩,⟨.or,[9,4]⟩,⟨.and,[10,7]⟩,⟨.or,[2,5]⟩,⟨.and,[12,6]⟩,⟨.or,[0,1]⟩,⟨.or,[5,6]⟩,⟨.and,[14,15]⟩,⟨.and,[0,4]⟩,⟨.or,[11,13]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_26929

open PEqualNP.Outside.L_meta_26929 in
theorem PEqualNP.Outside.L_meta_26929 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
