import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_32882.Model
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


end PEqualNP.Outside.L_meta_32882.Model

namespace PEqualNP.Outside.L_meta_32882
open PEqualNP.Outside.L_meta_32882.Model
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

def SBf (j : Nat) : Nat := [7, 8, 7, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_32882

namespace PEqualNP.Outside.L_meta_32882
open PEqualNP.Outside.L_meta_32882.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2424e8d1c00f062ea40234a6822a2604008561521900005003e08610406141106553943684022005930f00005873804300018400018304f241ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x530a0e4f2b0015002113352800003e015800540f00020c48003025002e003d474129081f07560300003300102c55262419573c37431d120d34444b32364a2d18453f00405017062038002f005204091e1a14314c4923002a0051393a1b115a421c0b5900224e460027003b054d160e020808d02286010000281063828b200c10000141800600090033e5390e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110f6aa221ee940439ea8087b95010e72a021d794e42aea9c859c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a655e53906baa720e710f31b7296636d52cc67ca918cf552319faa2633c544c7388698cf950219eaa0435e53086baa610f948421bd2804379500867ca7a04f55240afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f950409faa6613c54cc27ca9184f55230ce21c61b9408c27ea8984f15130dca02613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a4413d54882eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9084f55210b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x24000b8e00001c09a280b30788a8602802241462600030000400002001648000004010903255254443ca9495010f295254043cc9455010f315154043a658043ccb144354732a6580434ca996010f31c310d52cc6996010d31d8485500870e6214d40c358853503166114d40c558453503196014d40a6580438c29863502308e195404c21d6510c30c310d520c31443544308718d548821c6355210
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc0500081445c04354732a12e021aa598e05625845350304b12c029a81845856014d40
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
  | 4 => packedAt s0K4 (2667+((h/30+packedAt s0K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s0K2 (249+((h/1+packedAt s0K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 2 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x40118004220208008204820901304088105045
  | 2 => 0x52228891414810a0521244248449414612512
  | 3 => 0xaa444512412900354802489092092941828a28
  | 4 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_32882
namespace PEqualNP.Outside.L_meta_32882
open PEqualNP.Outside.L_meta_32882.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xa81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630bea8c617e508c3f481187e50230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3be6298774c530fd20261f9404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec82887d50510fb18a21f531443ec42887d48510fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ee21e657e51ccbeca3995d94732bea8e65f551ccaeaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a89977d0d32ee21a65ee424cbda84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83be43d077887a0df94b41f7296836e52d06faa5a0fb54b41b6a9683bf42d077a85a0df94341bea86837d54906fca720f794e41af29c837d53907baa720d754e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f7d0f31ee21e637e52cc7dca598db94b31bea9663ed52cc6daa598f7ccb31ee996637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf294637d528c6fca318fd90631faa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7b88698dfd4931be29263df324c7ba6498fd90531faa0a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fd90721faa0e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887dc8510fb50a21f719443ed32886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821f721043ed42087dc6410fb4c821bf28843f641087ea8210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9
  | 2 => 0x2c465c00000000000001ee2d60001800054c658000f2224488000000005a0c70820de00000000378605200e9220991388ba4526c8cd1be06a124001f004a000e01000002d8e506818a4151a8a400007cdb8c20c4000000000000000018b1fc7e80d16d000000ef1132f40000009a1ac5dd2693a1980000021402e00000125544000000000009a8e98002ec000000f50001a4d2a210002f1258002500009fa7b0a835d2403c00089c7e000176540000002843f446800268a800007600ca08c41e85207f94f0d94fc9a43580000057400137000000980000802143f97c000000001d00640015288c000001018000820003f00032a03906000000468221ad00000041800000108000e23ba0000003701a4e0360da0007100000036a9e508800000270001da39c040011a30000000000051e9f08885d000000002a449e71d440530b488c708a22ca000a611b2549b4e08092c01910592b444798fd8005500d8fb156000001378910005d0002a100045000000000000d9970000824000f01a84f07d80003c42d1c8b8000000000df0000000004740e278c9800000000000004b628cbf8c40003e400285074404000004140acc20514927f0ab80010c5247a0de0c24208189513a19cde99e0000180000100500401c00801010018038010000000280b0020040280001c0040180400000400000006014008010000140080100400000001004000000030140080000500c018000000120140280102600c0280400000c0280500802c000000060000000000a0280080a00000000806004000000030000000000400400404000002010010020000080000100805002800004008000000000040780000200400803006004048030020180080500a0180080100a0100000500a008000010080000280500003c000010100000300000200c0000400a0000200900a0000280000600c02801008028000030000000580100c03000801006008000000080000100100e0000380400000401806002000008000000280100000403c000030000000200000201400002000000000000060140300f0000040100100a002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443fb28887765110efaa221fd54443baa88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85be43d0b7887a15f94742fb28e857651d0afaa3a17d54742baa8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857
  | 3 => 0x1f8b92a8000599e94e00000000000000000000482000000c63aa000000000003a8000dd000000000000001d530a2a000000000e8000000000e5000000600001a67e40023a12e0004b28045c000ea0735227484511d40a5a43a1a20003d8000005342b4000030002d00006a2cc000001f10100013a022000000001630006a00023c31e0ec002783700000c1360ac8340020e3c88bc4400000a398870000007847c29c00000000131052a290d9a935e0fc3180034c9b12ba1e0168cce6a8c2de98c831ec00004c81000450000000000000000001b36827c7fa1c01487400109000000000000000008fa924ca0bc002061a06ec000003485c4498162bc000002450000000014546c00000224458000e58004640e0000000ca0004580004e45507a13240a1c270aa00000000000000000850000008f4000000005b047800000000000002ea001189233b04f4fb87c1d6170f914f0005193a8a122c000000000002d400000460000e425e0007bc280003845001728d42e79cbd8211500001e8cb0686652315a090944259ea232880ff9c50009d86a800000000788002a6000d7283000644ca0e74e4a61301470c02c400a0152a25000000000000000000002c02a879000204000200e46fc979e32180000001c46e4eced8002b00002313e286001298004862fc000003142ac0007b0000007700033a36cb09a0000000001861949e90900049c498290b72c8000001cf000974002a70002bc0013221a7cc0000019e571448d24e62607227d23c77caaa68000000000b2062a05040110000000022b000000c49c30000012a29600056c638f7432338000d85466e41204a53ea647188e38c0002616a26605026800000000000000001e000167000000f28000004a476800000000448002e4a5c00000000410689ab054a19000a54b26c4dd0ac00067c00000120000d80ae1361c438000186000001790003cd29000000000198cd29a09800178000000f01dc0ae4840000020e00076000000000000a700060d458000000000029400097c92226000548420a01f48f90a8bd0000011c0004840648b94109e91c330000001653b95f000510c90000000001c800536789472563e8894000000009b800234046764000002a20006083e0000000e94a0006614980023052c93a020004b4000040000a12c05e0004b80026b0002a40024c476000001a7000000002554ce9280027f45a0005f1802727d4001d1000000000000f4248368800000014e8000000008e244398a110b099000000001350fa66ce48004a00000900043e114db0e010e371330072907ac060c9000aa400000000640aca0400000016800430000bf18c3ae61cb981500003d0d0003380b0f685b00017c9617d000000370ef000000c11fd21e000530430003202c0772dc8400000000000000000000000d5
  | 4 => 0x29c7592d18d358970d09f84c4615
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x514823d64145209798c514825d6314520cd99051483356414520d598c51483556314520d990851483654214520d98c851483653214520dc580514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020b9185200836551480209ed95200837151480209798f54c425d63d53109b98a54c426d62953108f99353c423d64d4f109b98a53c426d6294f108f99052c423d6414b109798c52c425d6314b10b558e41c42b5648c710d914921c425f63552109718d548425e63152109758c548426e62152109b588548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e6414a108f590528425e6314a109758c52843675208610bc58021843e02188210bc18520843e321482109b98a544426d629511097d8d544425c63551109bd89544426c62551109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109b98a524427761549108f990524423d64149109798c524425d63149109b994524432e6414910cb590524434e6314910d358c52443656114910da58052442d56390510d914a41442746550510d914941442b5648c510d914a3144274654c510d914931442766588510d914a21442746548510d914921443685288110f888620442786548110f8485204436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109e980520427565c8410cd553210435553c8410d954b21042756508410cd55021043555308410d954821042f16008410cd553100435553c4010d954b10042796584010da54a10042776544010cd55110043555344010b9189100436552440109ed9510043695244010
  | 1 => 0x873a5454021ce551500875a5354021d654d50087e12154021da90950087694254021da8c950087693254021dc90550087714154021dc8c550087713154021dac8550087722154021da48550087712154021d8485500865e6394b409758e52d02b561d0b409798e51d025d6394740ab58b41d02b96010e409dd8552902746154a409bd89519026c62546409b988535026d6214d409d98453502756114d40d3988535034d6214d40d598453503556114d40d6580535023e65d0d40c714f435031c5350d40c714f42502b561d0940c714d425031c53d0540ab58b415031c5350540c714e405023d6590c40c754e431031d5310c40ae580431034e5394840d354e521034e5354840d354d521032e4354840cb10d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103364354440cd10d511031d53d0040cb54b401033551d0040d654e401023f6550040a718d401031d5350040cb549401033551500409ed95401035953500409b98854cc26d62153309d98454cc2756115330c715143cc23e6494b308f59252cc2d561ccb308f99251cc23d6494730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b6580438c2776154a309d185528c26f62546309b189518c3984390230b618d408c39b43502308f992544c25f63551309b988544c26d62151309d984544c27561151308f994544c31d6315130cb988544c32d6215130cd984544c3356115130ce580544c25e6590d30c7152434c25c6550d30c7151434c31c54cc930b5587324c31c544c930c7153314c2cd62cc530c7151314c3385490130e690e404c2786550130e650d404c31c548c1309b98b540c26d62d50309d987540c27561d50308f596540c31c63550308f990540c25e63150309b988540c26d62150309d984540c27561150309e980540c25d65d0c30c7553430c25d6510c30c7550430c2d96010c30cb952520c32d5494830cb951520c32d5454830d3d0d520c34c4354830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430c7553300c34d52cc030d5547300c339548c03097d95300c29c644c030c7551300c34d524c030d5545300c27b654c030ce551300c25e63d53209758f54c827661953209d58654c823e64d4f208f59353c82766194f209d58653c82cd6390b20ab59232c825f63552209718d548825e63152209758c548827661152209d584548823f6454e208f191538823e6414e208f59053882766114e209d58453882e960086209d9865448275619512097d8d544825c63551209dd85544827461551209d98653482756194d208fd91534823c6454d209dd8553482746154d20b358e424826c6550920ab592324826c654c9208f99
  | 2 => 0x6494732cd59251ccb574354732d510d51cca7661952329d586548cb2e6295232cd986548cb356195232cb951428cb1e54cca32b9987328ca7661951329d586544ca5e65d0d32c7550434cace6210d32b5584434cad96010d32b398e424ca6c6550932e310d424cae661cc932a7992324ca3e64141328f590504ca7661141329d584504ca5e63d50329b988540ca7661150329d584540ca7a60150329e580540ca3e64948328f592520ca5f654c8329bd95320cb1d5310f41ab58843d06b96010f419798e52d065d6394b41d398e52d074d6394b41cb90d52d072c4354b41cb94942d066e6294e419b58a539074e6294e41d358a53907566194e41c794f41906e662d0641ab58843506b66110d41ae58043506b661d0941b998b415069e63905419798c505065d63141419b988505066d62141418fd95411067765504419b98b54cc66d62d53319b98854cc66d62153319e98054cc6796015331c755043cc6cd6210f31b658043cc63e6494b318f59252cc72e6494b31cb59252cc74f4354b31d310d52cc74e524cb319b98a548c66d6295231cb98a548c72d6295231cd986548c7365450631c7953318c6e662cc6319b98a544c66d629513197997434c71d5410d31b3588434c6d66110d31b6580434c6d661cc931b598e414c6746550531e510d414c6e662cc531a7992314c63e64141318f590504c66e62141319b588504c65e63d50319b988540c66d62150319d984540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c65e63d53219758f54c863e64d4f218f59353c86d56390721ad59231c865e63d52219758f548863e64d4e218f59353886cd6390a21ab592328865e63d51219758f544866d62951219d586544863e64d4d218f593534866d6294d219d586534863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d6595021cb98a540873661950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a53087566194c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530866d6590821b358e420874d5390821b9586420872e5450821d354d420866d658c821ab592320872d548c821b9586320872d544c821d394d32086756590421b558e41087555390421b958a41087365450421d554d41087a542504219d59631086b5648c421cd55231086e5628c421cd5513108756534c421f14c931086e562884219bd9521086776548421b9d9521087676548421b9d9121086e56448421e995121087a55448421b9d8d21086e56348421f194d21087c55348421b9181210873a5494021ce552500875a5394021d654e50087e12194021d9485500
  | 3 => 0x5061c2000b3c3f99200000c000dc490001449223ca6d80002e11a2591c00025a305388580d68f8119130449bc4b8f7000b1d0998212070c390000006647906c4fe0808b924282000cda5d1960000000e000af800166000000000660000007ca8f2045593200000075c000000005d0368781a687c00260024000002341aa000001273002b0e81db2340b4fe84a07e000dda9d3206b4440ca3169d95616726c01879908000988f902655e0a4000b90008b4289af0b62e0be22f406758638be3644446690f0c60010280023cb042a914576000fba7d00041038a244ae318b91be2027ed100f45225005a9e626452d1314e4ee5cc049d40509e4ec2b80ce3f8ac8ed1861943218d062a183b92334aa147a8ff0007ac83a2115aa40038db03a108c49381002a04584043c63892a32534554e50e953e33c7d85e27c23d0e9f62b61f00817b4b0a64a208522a0e8412352148b95aa50240674fd2bd4a698c1ea2c554010000040801402000070280c01807044000ac0a0b40004004040290000500800034000000a2480d00c040080007c00130181d42d12000034060040a0180800c29020000200f01c7b0981e03001000040080b01c050040700c00000000040102003000000000a01801104040000408c260140a010010100a104080901a034090000a01c07014000040001003000060080204404000050700602c140080705409000210302c0040000002014030c4021840000806158030080700c0004001084010040c00c050400f04c0c004000cc0000c0b008010202f0001b014010e00500c080181200c000100604c0001c3e02c000000306c4d020050101a04000074320340308c0000c01044fa01c3403c1f00c0101407004030000d018000140000002020010000300442030000504f00a7661d49439d5875250e6e62d45439b58b5150e6e62141439b5885050e7661141439d5845050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9f6150c43a71814310f8d4394843e350d5210f954394443d994a5110f655294443e550d5110f665254443d95495110f994394043da94a5010f695294043dc9465010f715194043c750d5010f994354043da9495010f695254043dc9455010f715154043ced0d5010f5a4354043ce50d5010f594354043c650d5010f1d5310f42ad58443d0ab96010f429798e51d0a5d6394742d598e51d0b556394742cd90d51d0b3443547429d9865390a756194e42d398a5390b566194e42d55865390b1e53d0a42b99874290aae6210d42ad5844350ab96010d42b99874250a9e63909429798c5050a5d63141429d9845050a7561141428fd954210a6f65508429d98754cca7561d53329d98454cca7561153329e98054cca796015332c755043ccad56110f32b658043cca3e64947328f59251ccb36
  | 4 => 0x4f1432baae4869f44a48f4570f03c47353521b0b8a80bea611dc6f497ac401889cda8492385850113d29442d2897a20c53d2309d0fa6c4588b03de9f0690fd09a5d55426e5802e91e0320563a8431ea2d67155f805096054952a4242b18b20612200295b9c1298938120934243691b20d0a4b346606e002804238503f28cc4725a494b50e719f51a350c3abc4d85c54b21048837c4a225098790a1245000aa5592ba1bc000550004968ece900015e0686492c2789d45e03638eb08d226d3386d1470fc2b8658ef1814d29cc1f0004849ec3d0004be17d341c8000001692c904a8e4988001a26e8932590007649fa2228a3392004f16c7a50a013144971582810c4430bcab30002656524f48e58c999782c46c03025551028d140750ba82c34984206000d602f04e315670002505d8eaa291c403cb612950e0012a0ef2a2084fe17006aa943da9726a000e4a5e000000000a61d02c8c60000002cd619a70ac3e90b89b00047c000a43ea425530e60584e52689c0003940021a102524001980ecb14151582c064d03800000000e00000000000022328c5a81e1cb0d44008dab43f0380ca8d80680007c0004d6569418dd1c8364cf118370a4953a804ca63cd5a1c0005b8a6a0a56c688ca03330c05156818456230959bc08ca2cd49d31c26813827e4860003a00006e0000c8004322fd002ae03c6200f8d74e42dcf01974740005d8f108a00102000000b30611df2dea30bf11d1c6138bba950b2771030000f29d0dc800508301451cc2d00011b8002a6644ff0000004c0001373fe668b487335c768001c4000854240000047194c2115a6341070a90768247b23f1084ecd185702ea88af93a2ca21cd31bf08610497216000000761b353c2acab8003dc0c13d13430a000000e7306958f99e7224628d5154036b202a1160007b1412670167748c8003c23ace88384b6070002300887a0001f10000000000028e0005a0005621f84c00000000004000000a8c0016d00000000000342aad5080036e14c5ea0f5a00356889f498a4cd40390d0520508a01240000000000000000000000a50000890000450c29b0009e0f18005380004a8002a401052a49000b2c2d000114000001f04cc359041cf02c1c08710514e5404d0c400000000091000001209ed4543200015e0de000bf80000020c000000008c
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xbe488444b0b6947058347eae72921eb2124cc62000262c3e30000a00a06e5200c42e005c0000c854a88c40168e02000018385e9c009a9e287c36902a00983c80bca41cc27406869632101a24aa04824aba7800a28a004288a6140022006c46ca00b8000000b4007600647a6a62c00eac66685a080c503a60004e561800f0106000940e0408402341231a3c3000004285000000a0059118021a4ab8ec4a1887235cb6150c4391ae43028621c95711814310f82a1aa4a8887c250e5254043e1286a92a021f11439455010f88a1aa2a8087461d94354043a36e4a1aa021d1b7150d5010f0ca9ac021e854c5c04354742c32a8b0087995517010d51ccb0caa2c021a65615c44350932b12e021a84996195358043d0694b8086a9683865516010f31a92e021aa598e1954580434c6c2b9086a0a63645c04350531e0aa6a128210f05544c93108662b9ec890843295d36348421e0aa8a9a4210ca5741812108662b98c090843c89512154021e42a890aa010f425348550087a0a9a42a8043525ce4254021ac2e3212a010d29748c950086b0b8c64a8043545ce4154021ac2e520aa010f21425055008698ba462a8043585ca3154021e826498aa010d607648550086b1ba242a8043585d12154021ac6e690aa010d61734855008722b12c229a81925896014d40ca2c2b00a6a061453587425030629ac5a0a814a5c04354840a62e021aa22060c63549401030a31aa2a008186d516010e30934eda1a811862562584544c30cb1ac02a2618a5896015130c62c2b00a89861454587324c3062a2c598a61469d64390130c30caa1a809861954580430c2a4b8086a9061545c04354430838ecaa2601860c64549300c30a322a298061855916314520a8ae7210a290525748c85148318b22c028a419458d6014520c52a8b004210649535802108312aa0c2900419154c6148020cc6a4b0043084e276c852084306b22c6292218a5916014910c92c6b00a488661615805244322b18a520a2189590528c510ac4eb10c4088660654852044318aa2c0108219454d6008410cc2a4b004208625541891004322a98c488021191d95244010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x8c00004200e600a00909821d94354043911811d9435404391181dc9435404390982dc54354043921841d92154021941831d9215402194183dd1215402192184dcd2154021
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (6+((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s1K6 (731+((h/13+packedAt s1K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s1K5 (20911+((h/227+packedAt s1K5 (18414+(h % 227)*11) 11) % 1089)*11) 11
  | 4 => packedAt s1K4 (29960+((h/241+packedAt s1K4 (27550+(h % 241)*10) 10) % 871)*11) 11
  | 3 => packedAt s1K3 (5236+((h/34+packedAt s1K3 (4998+(h % 34)*7) 7) % 123)*8) 8
  | 2 => packedAt s1K2 (488+((h/2+packedAt s1K2 (480+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 2 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 3 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 2 => 0xc4148944492854085064292124849286314512
  | 3 => 0x1a912289244a801ac80524849212530c28a28
  | 4 => 0x488c032520240c92352918000e498192540f80
  | 5 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0fffffaaafaaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_32882
namespace PEqualNP.Outside.L_meta_32882
open PEqualNP.Outside.L_meta_32882.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2018f0056000153071401002cb02320000000006054a24b8f1a8c9130e000000000000147c18000000000000e8000010241045080009c00454000003450da252987008206001800030202000c100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1b080005968006a98e888a9b90232289a0a2121fa1910ca59f131eac02818010802923ad929c9627a104801914800a2b000f0028952400272d178b118000000d00001702001a8024838b9a0107a68c0f801880958407000e261d94182b9c09002ca51d031e0d93a02a060519802aa80093021018004141011060002002468c020468b04040870004593b7294876d5290edca421db54843bb28887755110ef4a021de54043bb28e857551d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290656e52d06daa5a0eb94b41d6a9683ae32d075a65a0cf55241d719283ad325076ea2a0cf95041b7296636d52cc79a6598cf952319eaa463b5418c79a6498ed505319f2a0633d540c6dca418db54831bd2806379500c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af298815d53102dca4205b54840bb288817551102dca5985b54b30e6996613f544c278a898734c9309f2a0613d540c2dca4185b54830bb2886175510c27ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a83885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xf1800000889081456000e401a75985180808d586548caa56195232a3993534cac56110d32b2580434ca4d6394b41a358e52d062d658cb41a998b51507853250531c554d410873141540218d584544c30c544c9309358c52443245250510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x99090ae3326a6994857398b5150682b88a899261415cc5250510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
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
  | 4 => packedAt s2K4 (2694+((h/30+packedAt s2K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s2K3 (633+((h/5+packedAt s2K3 (608+(h % 5)*5) 5) % 24)*5) 5
  | 2 => packedAt s2K2 (199+((h/1+packedAt s2K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf3c78f3ffc7c7f1f8c470c7fe3f1f0f80f4cf
  | 1 => 0xf03f80fc63f9f8fe3f0780f8e3c7e7f1934b33
  | 3 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 4 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1040110004008020000100120090100001045
  | 1 => 0x10882222049101404204844848428241114112
  | 3 => 0x22035449492492a00dc80a92129054ac628c28
  | 4 => 0x44111009120080249151220003245024240e80
  | 5 => 0x88a26082403524c926a64ce4980080c95be000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88ffffeeaaeeeeee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_32882
namespace PEqualNP.Outside.L_meta_32882
open PEqualNP.Outside.L_meta_32882.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xaa500009801e280284c782170aac01f062441c001cc23000068120450a92c743000049000000002200501194e0060036a8700486800b0010404004a003002203040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8c586200b67a72002c220000000000001c00004400004c00001e3a6a000050005a880070003400001800a6a84e00000000a40000520090000000ac000c206400000000040000000000001000a200688e38606c007c5600006e0046ae322e00001412000600660000b4000084000078005400000000004a000000000000b00074762a00b2002800080000000000008a0000000a009200005c02005ea03c000000000e98009c0000269400869a9e0000000000960024000048003e001a000000000000aa30407e000080160000004200820036000000000500000402000002000000000100050000010001000000000001000800b7294876d5290edca421db54843bb28887755110ef4a021de54043bb28e857551d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290656e52d06daa5a0eb94b41d6a9683ae32d075a65a0cf55241d719283ad325076ea2a0cf95041b7296636d52cc79a6598cf952319eaa463b5418c79a6498ed505319f2a0633d540c6dca418db54831bd2806379500c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af298815d53102dca4205b54840bb288817551102dca5985b54b30e6996613f544c278a898734c9309f2a0613d540c2dca4185b54830bb2886175510c27ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a83885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8d02c08280c00000778020501c3600490000308028d586548caa56195232a3993534cac56110d32b2580434ca4d6394b41a358e52d062d658cb41a998b51507853250531c554d410873141540218d584544c30c544c9309358c52443245250510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x10d0090ae3326a6994857398b5150682b88a899261415cc5250510
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
  | 4 => packedAt s3K4 (2724+((h/30+packedAt s3K4 (2484+(h % 30)*8) 8) % 213)*8) 8
  | 3 => packedAt s3K3 (633+((h/5+packedAt s3K3 (608+(h % 5)*5) 5) % 28)*5) 5
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf3c78f3ffc7c7f1f8c470c7fe3f1f0f80f4cf
  | 1 => 0xf03f80fc63f9f8fe3f0780f8e3c7e7f1934b33
  | 2 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 4 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1040110004008020000100120090100001045
  | 1 => 0x10882222049101404204844848428241114112
  | 2 => 0x22035449492492a00dc80a92129054ac628c28
  | 4 => 0x44111009120080249151220003245024240e80
  | 5 => 0x88a26082403524c926a64ce4980080c95be000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8ffffeaeaeeeee8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_32882
namespace PEqualNP.Outside.L_meta_32882
open PEqualNP.Outside.L_meta_32882.Model
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
end PEqualNP.Outside.L_meta_32882
namespace PEqualNP.Outside.L_meta_32882
open PEqualNP.Outside.L_meta_32882.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x4009000630004855201080264078a063401f4a8c01c1c88d0022000142e1c9013c8151d1864002169ca8800995800058d80500800c22800462ce082041ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x6613d54cc2f8a9986fd0f30ef21e61bd43cc3ba87986750f30bf296617d52cc37e85986f50b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7186fd0e30dea1c617e528c2faa5186fd0a30dea14617e518c2faa3185f94230ef98461fb308c2fea8985f95130beaa2617c544c37e86987790d30dea1a61dd434c33a86985fd4930be29261bf424c37a849877cc930ee992617f514c2f8a29877cc530ee98a61fb304c3bc60985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30dfa1861bd430c2fca4187b94830b7290617d520c3daa4185b54830dfa1061bd420c2fca2187d94430bb288617d510c3eaa2185d54430bf28061df300c3f46018774c030fc980617f54c82fca9906f953209f2a6417d54c837aa9904f55320be2a6417f53c82fca7905f54f20be29e41bf43c837a87906fd0b20f721641bd42c83da85906b50b20f719641ed32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837e87106f50e20bea9441bf428837a85105f94620bea8c417e50883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e86906f50d20dfa1241ee424837a84907b50920d6a1241ee32483da64905fd4520be28a41ef21483da42907e8c120fc98241fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6106fd0c20dea18417e520837e84106f50820bf28841f651082eca2105f54420faa88417551082fca0107bc8020fd10041ed20083f240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7886fd0f10dea1e217f52c42fca5885f54b10be29621bf42c437a85887d90710faa0e21f631c43ea63887d88710fa90e217f54842fca9085f55210be2a4217f53842fca7085f54e10be29c21bf438437a87085fd4a10bf294217d52842f8a5086fd0a10dea14217d51842fca1087e90210fca0421fa30843f261087e88210fc90421f710843f621085fd5110dfaa2213f54442fca8885f55110be2a221bc5444278a8885fd4d10bf29a217d53442f8a6886fd0d10dea1a217f52442fca4885f54910be29221bf424437a84887d90510faa0a21f631443ea62887d88510fa90a21fa40443f280887e8c110fc98221fa20443f240887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be29821bf430437a86085fd4810bf29021ee52042dca4085f54810f6a90216d52042f8a4086fd0810dea10217e51042fca0087dc4010fd08021f510043f220087c44010
  | 1 => 0xe50906faa120dfd4d41be29a83bf435077a86a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077e8620ef50c41bf29083ee52106dca420df54841f6a90836d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50107f4a020de94041bea8083f950106f2a020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998efd0f31ef21e63bd43cc7ba8798e750f31bf296637d52cc77e8598ef50b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63bf438c77a8718df94a31bea9463bf428c77a8518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131dfa1a63de434c77a8698f750d31cea1a637f524c6f8a498efd0931dea1263df324c7ba6498fdcc531ef18a637f504c6f8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31dfa1863bd430c6fca418fb94831b7290637d520c7daa418db54831dfa1063bd420c6fca218f7cc431fb18863dd310c7ea6218df94031fd280637a500c6faa018fe54031bca80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790efd0b21f721643bd42c87da8590eb50b21f719643ed32c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21dfa1c43bd43886faa510efd0a21dea14437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa1a43bd434877e8490fb90921dea1243ed424875a8490fb8c921f699243f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610efd0c21dea18437e520877e8410ef50821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037e87206f50e40bf294817d529037e85206f50a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40dfa1881bd43102fca4207b94840b7290817d52103daa4205b54840dfa1081bd42102fca2207d94440bb288817d51103eaa2205d54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a661be54cc27ca9985f55330deaa
  | 2 => 0x20000000200000c0100200000c008000040000001200a0100880c0000080601500400c0000900c0200700200001400002004008000010000180100e0260100100000400000800000030048000000000301900c00002000bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0f7ea5a1ef94b43d729687bd52d0e7aa5a1eb54b4396a9687bc52d0f7ea3a1ef94743dea8e87bc51d0f7ea1a1ef94343dea8687bc50d0efaa921cf55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be28287bf5350f3ea6a1efd49439fa9287be5250f7aa4a1ef14943dfa8a87be5150f7aa2a1ef14543dfa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0bbca7a15794f42bea9e85dd53d0abaa7a16fd0f42df21e85bd43d0b7887a15f94742bea8e857e50d0afaa1a16fd4f42df29e859e53d0b7aa7a14f54f42cea9e851d53d0b78a7a16fd4742df28e85bd51d0b78a3a16fd4342df28685bd50d0b78a1a15f552429eaa4857e5390afaa7216fd0e42dea1c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f90d42dea1a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142dfa9a853f5350b7ca6a16f54d42de29a85bf5250b5ea4a16fd4542df28a85bd5150b78a2a16fd4142df28285bd5050b78a0a15f950429f2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32dfa1665ee42ccb7a85997b50b32d6a16657e51ccafaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cb7e87197790e32dea1c65dd438cb3a87195f94a32dfa1465bd428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cb7ca8994f95132beaa265bd544ca7aa8995f15132dfa1a65bd434cb7e84996f50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6196fd0c32ef21865bd430cbba86196750c32bf29065bf420cbdc84196f50832f6a1065ad420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41dfa1c83bd43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837
  | 3 => 0x64a0015e15f50e354000002282c9361a71203b0239ab276ad429b5c000cbce100000000000000000000000fa19e17800117000cc43480000066cc48002ac7e4002510005ed5300037a7b95f0436c2dac0018b0909d08b00056c6080d226368b687c8002645b4b40284966ec74b2a21e9593b8204b26fcd200039c748a430f00000082a126447ec3fa0e124a8d503010365bc00000272000941e100085c0013e4445dc002d200061c0f8e2006be06e98a3b00004bb086aa9f94780007a000002540e000032aba0d4001a58383d4418c686c2fcb50eb8d72ae5b8660413e69fd0f03f3964a4939594082c10fade2e4578109da19a5cc6d1035de29917a5b062c28f40064126b8002150b05098701607800176a1a2968512ba02000d481a0d91ccc5cb82476a2cf0ce14415e21d09afe5d8138cd0461f690890a11000481230811de000002d00007a40016332a0008f000000000ae29a0463b43b0835f25015f8003520017bb263260014f8132fe00000000000440001fe0de0000000000000000000000001120000003204c9aa000c6d650000007d00022c2f46c91b975224000b30005822b0c832d0002f4000001d400000131000000000006c45494f10d2d2000fe0005320000023a1c6000001bc3a0324000fe000001461492c0230002963805b0e89be6008f8ac2a124c2342c8003de0244d2273c012899abb4bca5c00000000c084eb45000b59510000e623c0030503ad7c002c2462000d2b65298000003430000a87f81960ea603333e1447ada50221e69499029b6cc4889b87c0001908536c038d003595a69c00156a8d4de000aa8003e42a4000322ba0000021634c000001ec6982707b24a466675b82c66680c0a191d3a6224001db06e970b58565f4828821cc32c13ca50000489010c9d60000000000003cb1473a492822f00010e3860015c80059e0a4bc2b20e20005d9611803600007d0003b98a0006ae4d40280000700a01c0880d0000040080d00e02800807002024000060000000300200a004000010080000000000200c0000500000000801000000010020000b00000000001c14001000034000000060240000000e0080000000201800813008004018030020040100501a0000402900c000000000000040002800a00006001002004000020020140b8000220000080701602c000000040240380d0000140000000000000000000010010010000040100301a00c000040000000000100600400808014010010100000000000b00600c00006034000030020020280101500a0880400d00401403004000014000010020000000301000c000000020340580400000400802002018008000100180100000401c0000000601c000000000140280400000004800012010028000020100180200001409800000008010030020140000
  | 4 => 0xdc504001458000000008e000000da5688042ec894440003ec000000de168c7c000000005c4a805a59ada800289000000002655928a8d81012f2aa800000000b60002102120000000200000135a452480004c000258000000001880007e054000b9911ae23f0550000006500000024f00000000119000a45a111f1d6001898ab000000e41e2000b70589c100000078000000cfc000000007e8e48000000000000041aac00034f4c403000000268710000003b20d40018400000133953000000a88000000000033a00013000344000a4d418f8306001708151d00011f8a10005a852800528000003181360000000032e000ba04233c001a800000081c281150000cd908b565cd75368144e4add992410e8acd0e8b728ea544b0b90aa8f06803e30c8f43c000000d91383090ae9213e80064e00000045088754c28004a08b92c09e62417400000410d8c860000f212c000c215c2a00024e00000000000000a94039910000018e0000000000029c5e0000092b126c000b10006d0001ad0000ea9e1821a1000aad1826918ab2d859d4634bf00007a166cd9b718e6ac409728006521015203617ca9d8184d186dbc9291a0ee8ac002cc000a20952fd0d041c072903fa000001456c018c000004d09e4633355e8c4485ac40da2291b3730000000013f000000dc000658c30800cb03000174b3701aad00002767a0bc2e0006da000001234720000012f3ea8b5670004c6a108db480fc000002db5c000039253000b5c0b8001a40009c2f657a000d78d400099800000146a74000db46800000000000184f8000000000cfac7000244003063ca0018c80000029000000000000f235400068d370b64be680001ac000000b20bf05a29c000d6000000000003b860138ac81c8254ca20c0166a00009335a001738b80000017580000016c12800324149a3a80402000792750000019980036e000000001ea3440000001444d3b0c13bc77c8c00829a17da99ed61a000e50265706d8339b538e8140008631e000000005020004f8396bc62008b415523d0d118c5c673c0002b1be00191800442798000000000004283a4ba71903200450251a6b245dcce47b93a514870a31b34aa6e85525a6b018000a8e62a7fd7d8a048859c0000068c860000004c8b4c002320a24207e95b4d4bc95624d000b900000000090c00229058cec001f74f6ba97992b63c5389e80025ca14000006b2000dc800000594002dd4f8000002af000000000000005f53d0ca09233901a3b5b29cd602df1e20017fa0b1746c52614f0200007080000000045ae8586a48003672223955722038acac37130000000000005e22098b0000004b5431e30c48d40021b00034c0018111c000000003ce0017a87b0000000037141e20000338000000001f1108664638005aad258ea3805cdc800000000000be000
  | 5 => 0x1e2b4002613bac409e33039a00154000330000000000000ec000001c0d6d300
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2528423d6494a108f990528423d6414a109798c528425d6314a10a758f428432e5250a10cb5494284399434c210ea509208423d63d51108f58b544423e64951109798c544425d63151109b988544426d62151108f994544429d6315110ab588544431e63151108f58c544431d63151108758c544432e62151108f588544432d62151108b58854443356115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423e65d0d108f19743442ad62d0d108f995434423c6550d10c794d434431d5350d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d0910a758f424423e65509108f195424432e5250910cb549424433454905109d19541442f060505109d1953144395434c510bc18131442746548510e950921442f06048510ce15240443b241901109e19540442f06150110ec5054044278654c110e650d30442f0614c110f44c530442786548110ea50920442f06148110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f58e540423d62950108fd8d540423f62550108f990540425e63150109758c540426e62150109b588540427661150109e980540423e64d4c108f593530426e62d4c109b58b530423e6494c108f592530425d6594c10c7952530431d5494c10c7992530431d6494c10c7951530431d5454c10c7991530431d6454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423f65d0c108f597430431e53d0c10c754f43042ad62d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432e6454810cb591520432f4354810cb50d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810a758f420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb549420433554c4010d554f100436552c40109e59610043395484010d654e10043695284010bc58610042776544010cd55110043555344010d9549100427b6544010ce55110043595344010da54910042f36544010dcd9510043b36444010ec19110043735444010ec95110043715444010ec55110043315444010dcd4d10043d25344010dc54d10043d15344010d454d10043b34344010ec50d10043735244010f894910043715244010f854910043615244010ecd0910043b14244010
  | 1 => 0x829d6395320c798e54c823d6395320c758e54c821d6395320cb98a54c823f63553208f99353c823d64d4f208f99253c823d6494f208f99053c823d6414f209d98453c82756114f208fd9743c823d65d0f20ab58b43c823f6550f208f59543c831f5350f20c714d43c829d63d0b20cb95142c82af6550b20cbd9542c82af6350b20cb94d42c832c5350b20ab59232c838d438cb20ab59132c834c534cb20cb50951c82ad64c8720cb55321c832d54487209798c548825d63152209d984548827561152208f992538823d6494e208f990538823d6414e209d98453882756114e20ab58b438831e5350e20c754d438829d63d0a208fd91518823c6454620e650d308825e63951209758e544823e6494d208f592534823e6414d208f59053482766114d209d58453482ad62d0d20c7d4d434831c5350d20a758f42482ad64909209b19542482e86050920cbd95424832c6550920abd8d424832e5350920cb14d42483ab6050920ea18142482ad648c920e350e324826c654c920ab591324834c534c920cb50b514823e64145208f590514825e63145209758c51482ad64c8520ea50a3048278654c120e650d30483a9424c120f24c930483a942c81209798f540825d63d50209d987540827561d50208f596540823d63950208fd8d540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530823e6494c208f592530825d6594c20c7952530831d5494c20c7992530831d6494c20c7951530831d5454c20c7991530831d6454c208f990530823d6414c209798c530826e6214c209d98453082756114c209e980530823f65d0c208f597430831e53d0c20c754f43082ad62d0c208fd95430823d6550c20c794d430831d5350c208f992520823d64948208f597420829d63d0820c794f420831d53d08208fd95420831e5350820c754d420832e5250820cd95251083355494420d594e51083555394420cdd0e51083354394420cdd0a51083354294420cd95151083355454420d594d51083555354420cdd0d51083354354420cdd0951083354254420cb553200834d53c8020d954720083595388020dc546200826f6548020cb551200834d5348020d9545200827b6548020d654d20083ab4248020dc545200825e63153109758c54c426e62153109b58854c423e6494f108f59253c423e6414f108f59053c426e6214f109b58853c42ad62d0f10c794d43c431d5350f108f99252c423d6494b108f99052c423d6414b109798c52c425d6314b10a758f42c432e5250b10cb54942c4395434c710e950921c425e63152109758c548426e62152109b588548423e6494e108f592538423e6414e108f590538426e6214e109b58853842ad62d0e10c794d438431d5350e108f99
  | 2 => 0x5250a40cb549429029d6310640ab58841902b96010640ab58b435031f5350d40a758f425032f52509409798c515025d63145409b988515026d62145408f997415031e6454c40c754f43102ad62d0c40c794d431034e5394840d354e521032f4394840cb50e521034e5354840d354d521032e6454840cbd0d521032d4354840a758f421031e53d0840c754f421032d52d0840c794d421031d5350840cb94942103565394440d554e51103665294440d954a51103374394440cd50e51103374294440cd50a51103565354440d554d51103665254440d954951103374354440cd50d51103374254440cd509511023d6590440c754e411032d5290440cd546411029d6310440c754c41102ad6210440cb54841103355110440ae580411031d53d0040cb54b401033551d0040dc546401023f6550040c754d401032d5250040cd545401027b6550040dc545401026e62953309b58a54cc2ad6295330c798e54cc32e62953308f58a54cc32d62953308b58a54cc23f6255330ab58b43cc31e5450f30a7d9543cc31f6550f30a7d8943cc23e6494b308f59252cc31d4394b308fd9742cc23d65d0b30a758f42cc23f6550b308f59542cc29d64ccb30e350b32cc29d644cb30c750d51cc29d64cc730c755331cc31d544c7309b988548c26d62152309d984548c2756115230ab58b438c23e6494a308f592528c29d63d0a30cb949428c32d5250a308fd91518c23c64546309b98a544c26d6295130ab58b434c29d6490d3097195434c2d86050d30c7d95434c31c6550d30a7d89434c39b6050d30e6181434c23e64149308f590524c31d43149309d984524c2756114930a758f424c32f5250930cb149424c29d64cc930e350b324c29d644c930d3149324c31d43d45308f990514c23d64145309b988514c26d6214530a7593314c39943cc1309b98b540c26d62d50309d987540c27561d50308f596540c23d62950308fd8d540c23d63550308fd89540c23e64150309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23d65d0c30ab58b430c23f6550c30c794d430c23e64948308f592520c32e5494830cb552520c32e6494830cb592520c32f4394830cb50e520c32e5454830cb551520c32e6454830cb591520c32f4354830cb50d520c23f65d08308f597420c29d63d0830cb94b420c32d52d08308fd95420c23d6550830cb949420c32d5250830cd952510c3355494430d994a510c3655294430cdd0e510c3354394430cdd0a510c3354294430cd951510c3355454430d9949510c3655254430cdd0d510c3354354430cdd09510c3354254430c7553300c34d52cc030d5547300c369528c030dc546300c25f654c030c7551300c34d524c030d5545300c27b654c030e6d0d300c369524c030dc545300c25e63953209758e54c
  | 3 => 0x8318fd95420c63d6550831cb949420c72d5250831c7553310c74d52cc431d954a310c65f654c431c7551310c74d524c4319dd95310c797434c431d9549310c73a5494031ce552500c76a5294031da54a500c73b4394031ce50e500c73b4294031ce50a500c73a5454031ce551500c76a5254031da549500c73b4354031ce50d500c73b4254031ce509500c75b3154031dc8c5500c7593154031dc4c5500c65e63953219758e54c869d6395321c798e54c863d6395321c758e54c861d6395321cb98a54c863f63553218f99353c863d64d4f218f99253c863d6494f218f99053c863d6414f219e98053c86796014f218fd9743c863d65d0f21ab58b43c863f6550f218f59543c871f5350f21c714d43c869d63d0b21cb95142c86af6550b21cbd9542c86af6350b21cb94d42c872c5350b21ab59232c878d438cb21ab59132c874c534cb21cb50950c865e63152219758c548867a60152219e580548863e6494e218f592538863e6414e218f590538867a6014e219e58053886ad62d0e21c794d438871d5350e21a758f4288795434c6218fd91508863c64542219798e544865d63951218f992534863d6494d218f990534863d6414d219e98053486796014d21ab58b434871f5350d21c714d434869d63d0921ab592424866c6550921b9185424872f6550921cb19542486af6350921cb94d424872c5350921e9d8542487a46150921ab592324878d438c9219b19532486ad644c921d314d32487a5428c5219d1953148795434c521e950931487c5324c521e950b214872d42d41218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863d63950218fd8d540863e64150219798c540865d63150219b988540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f43086ad62d0c218fd95430863d6550c21c794d430871d5350c218f992520863d64948218f597420869d63d0821c794f420871d53d08218fd95420871e5350821c754d420872e5250821cb553210874d53c8421d554e210866f6548421cb551210874d53484219dd9521087555348421e9d09210873a5494021ce552500875a5394021d654e500873b4394021ce50e500873b4294021ce50a500873a5454021ce551500875a5354021d654d500873b4354021ce50d500873b4254021ce509500876b2154021dc88550087692154021dc485500871d53d0f40ab58b43d029d63d0b40cb54b42d02ad62d0e40c794d439031d5350e40a758f429032e
  | 4 => 0x550d510cb374254432d9909510cb354254432d9509510cb254254432d5cc9510cb663254432d54c9510cb653254432d14c9510cb3a5494032ce552500cb994394032ea50a500cbc93294032dc946500cb715194032ced0e500cb394394032ced0a500cb394294032c750d500cb2d4254032d34c9500cb3a5454032ce551500cb994354032ea509500cbc93254032dc945500cb715154032ced0d500cb5a4354032ce50d500cb594354032c650d500cb3b4254032da909500cb394254032da509500cb294254032d6cc9500cb6a3254032d64c9500cb693254032d24c9500cb1d53d0f41ab58b43d069d63d0b41cb54b42d06ad62d0e41c794d439071d5350e41a758f429072e5250a41cb54942906ad62d0d41c7d4d435069d63d0941cbd49425065e63141419758c505066e62141419b588505071e6454c41c754f43106ad62d0c41c794d431074e5394841d354e521072f4394841cb50e521074e5354841d354d521072e6454841cbd0d521072d4354841a758f421071e53d0841c754f421072d52d0841c794d421071d5350841cb949421071d53d0441cb54b411063f6550441c754d411072d52504419dd95411075a5394041d654e501076a5294041da54a501073b4394041ce50e501073b4294041ce50a501075a5354041d654d501076a5254041da549501073b4354041ce50d501073b4254041ce509501073b4154041dc90550107394154041dc505501066e62953319b58a54cc6ad6295331c798e54cc72e62953318f58a54cc72d62953318b58a54cc63f6255331ab58b43cc71e5450f31a7d9543cc71f6550f31a7d8943cc63e6494b318f59252cc71d4394b318fd9742cc63d65d0b31a758f42cc63f6550b318f59542cc69d64ccb31e350b32cc69d644cb31c750d50cc66e62152319b588548c67a60152319e580548c6ad62d0e318f992528c63d6494a31a758f428c72e5250a31cb549428c63f64542318f191508c66e62951319b58a544c6ad62d0d31a7592434c65c6550d31b5185434c71f6550d31c7195434c69f6250d31e5d85434c7946150d318f990524c63d6414931c750c524c67a60149319e580524c69d63d0931cbd49424c72c5250931a7593324c78d42cc931a7591324c74c524c931e550f314c71d43d41318f990504c63d64141319b988504c66d62141319b98b540c66d62d50319e983540c67960d50318f596540c63d62950318fd89540c63e64150319798c540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c31ab58b430c63f6550c31c794d430c63e64948318f592520c72e5494831cb552520c72e6494831cb592520c72f4394831cb50e520c72e5454831cb551520c72e6454831cb591520c72f4354831cb50d520c63f65d08318f597420c69d63d0831cb94b420c72d52d0
  | 5 => 0x53d0b1d5314f42ab58853d0a9e63d4742a758f51d0b1d53d4742c754e51d0b1d5354742a798c51d0a9d6314742c754c51d0aba6014742ae58051d0a9e63d4342a758f50d0b1d53d4342c754e50d0b1d5354342a798c50d0a9d6314342c754c50d0ab66114342ad58450d0aad62d0e42c754d4390a9d63d0a42b398f4290aae62d0d42c7d4d4350b1c5350d42ab1894350a3e6510d42b398f4250a5e63145429758c5150a7a60145429e5805150a5e63141429758c5050a7661141429d5845050b2d62d4d42ab58a5350aaf6254d42c754c5350a9e63d4942a758f5250aae63d4942e398f5250a8e63d4942e358f5250aad61d4942ab5835250a9e6314542a758c5150aba6014542ae5805150a9e6314142a758c5050ab66114142ad5845050b1e6395042c758e5410b1d53d0c42ab58b4310a3f6550c42a758f4210a3f65508429bd954210b2e5450842cb58a54cca9d63d0b32cb95242cca9f6350b32abd9542ccb2f6550b32cb19542ccaaf6350b32e3d8d42ccb8c6350b32cb50951ccb2d4254332c758e548caad62d0e32c7952438caaf6250e32c7d95438cb1c6550e32a7d89438cb8f6250e32e3189438ca9d63d0a32a7593328cb2d54cca32c750d518cb1d43542329758e544ca6d62951328f58e544cb1d63951328758e544ca3d6295132cb58a544ca2d62951328fd8d544cb1f63551328fd89544cb2f6255132ab58b434caaf6250d32a758f424ca3f65509328f595424ca9f6350932cb553324cb1d548c9328f993514ca3d64d45328f990514ca3d64145329e980514ca7960145328f993504ca3d64d41328f990504ca3d64141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540cb1e6395032cb98a540ca3e64150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430caad62d0c3297596430ca9d6490c32b358a430ca3f6550c32c7951430ca9f6550c32c7d95430ca9f6250c32e3989430cb8d6250c328f992520ca3d6494832c750e520ca3d65d0832a758f420ca6d6590832ab592420cacd6390832e350e420ca3f6550832cb951420cb8e4350832e350d420caaf6550832cbd95420caaf6350832e398d420cb8d6350832cb94d420ca9d64cc832e350b320caad648c832b358e320cb8d438c83297d95320ca9d644c832e3d09320cb8d424c8329bd95320caad644c832e3d0d320cb8d434c832b3d95320cb4f654c832b3d91320cb8e644c832b3591320cb8d644c832a3591320cb8e544c832e3551320cb365494432cd552510cb954394432e950a510cbc53294432cdd0e510cb354394432cdd0a510cb354294432c750d510cb2d4254432d34c9510cb365454432cd551510cb954354432e9509510cbc53254432cdd0d510cb564354432cd50d510cb554354432c
  | 6 => 0xda868030050380040382809c0000182b00209c00003044024008160080040580e0240001680204c000060080000080a0230060000a81902c07c0081400600c0500601200003800000014010060260100401200604400000048000008010000400380d03a0100380e0200080080002605c0000400601c0300c06e0980100303c02002000016008008020180200481c00001c0400000a010068060240080080b0240001100f0040000000000405400000014000028110100040200202c0080000100200007803012020000000000280200001c00c13801006004008520000000880000004c018000100940200200000000018006004020020060a000800008000000030000001d806004000018010020000080000601c0c803000028078010160000000c0000101180c01e0001f02300401c02800006014000000060280e0010000040300b01e00c0000a0080b4000120000000000d0020000100700c0480080e034000008020060001000900a0180000000003c0281700e0000380700400c0100100002803801006034010080060140181900c000088010260201202100001c040030000040300900604c1400b0000b40000600a0841000400a000030000060240200a00203c000010260080380102c054030010100000280601a0040300600c028000000060040e0000100140b00f0020040c008002010028390000040000201200000001034000008050060080200203801c010020020000101100e04c008010000000080a00000006000000000028250400040480501a0440b80b00c01001800018028018080080100580c00a03c050060a4000120000000280b007004024000030061281200a00605c018000000000002702200002000cb99152d0f2f6554b43cb58d52d0f2f6154b43cb98552d0f2d6154b43cb18552d0f2f6054b43cb98152d0f2d6054b43cb18152d0f2d5214b43ab98b51d0ead62d4743cb54b51d0f2d5294743cb54951d0eae6214743ab58851d0f2d5214743ae98051d0eb96014743ab98b50d0ead62d4343cb54b50d0f2d5294343cb54950d0eae6214343ab58850d0f2d5214343ad98450d0eb56114343ab58b4390ece62d0e43b398b4350e6e62145439b5885150e7a60145439e5805150e6e62141439b5885050e7661141439d5845050eae62d4d43ab58b5350e9e62d4d43e398b5350e8e62d4d43e358b5350e9d61d4d43a75835350f2d5214943ab9885150ead6214543ae9805150eb96014543ab9885050ead6214143ad9845050eb56114143cb98a5410f2d6295043ab58b4310e3f6550c4397d954310f1e5450c43c799153d0b1d53d0f42c754e43d0b1e5350f42c754c43d0aad62d4f42c7d9553d0b1f6254f42c758953d0b1f6154f42c798553d0b1d6154f42c718553d0b1f6054f42c798153d0b1d6054f42c7181
  | 7 => 0x1d3872a8988013786308787b80280002586d0b484e9cd8531542560ae1960dda8d16502524790c9151ff8fb9cc9899a0063a4486010f9a503c0a60000e900029f00010e8d71498190d1a6b2592329359a1832270a14a2c0b29bc0c48b500d8c40b086a15b882a3218a00001697a87122300918b0540790572001c328c0ba89392227588a1b99c28f5077076279a772512629201529060fe07e105a8880016e8b215b00009b139000238204800022800246904a2400000012e13027daa5a698dc800018a7d2038001538001749bc819a619930000550ee99c1459f69e32811558000000f494e8e6143821a7789c909163800285a369bb1ed00028b9feaa929b06b03a028a138900000061190468001d82aa9110ab0f79ec886a08a7612295c0689c1a028bd8ea932a9e00000983489d2a425686e10e064144a8703111f12e8249e6891a718d092686d8e89a3aac883046066a1f0000e826c9cf2220e013ea950000d52948000408d307d25ea420002900750000ab9549351d30000b30682a30000000001368a3800208206a539b00000ef9000001dc0000000000000970000001a88af00ba678851798000cb97008b0ba0001238001041ce96100018b8000000002921c48bc1a99cc0fa1790748a401c8298002880001848e69eb127a4616598380000026500026316695f80026d9b70b41ec1b58002830b88b70e4873806a801e004209487a8e597403d9b1a9388c04c1b2a3f12a1afa8216480584900213ba6892400fa1c9c5a020232a71ac27e948250a2022e8cd0bb23194900120099a0c7aaba750d683b80020522d89fa8517185388b89a0318341e99751b824408d9512a50d408381f21310d8fd8c204f94a13327f0ad29a11b0e30f09ba8001d0a3d9c821780087c92d249aa290280000023e0950a126a22ca1900011e10a967aaa04880014780000027389592b9b08000000001292550000c600002b8002140ae8000000000d9a181aaa269ae24b80000002611611d80027b233a968001831870a2823a3b0bf9f800022d00005a91c9fa8ecaa099791490a0f38bf1d51860390e215f0001f9a6600025b2588fd0f920d89916e1a70001078de2379298998001de2ad88e2091f79b391e8371a20d88120dc22524ea4a2111f1a4f8cf0ac9c11cfa5195e17308401b814a849e91db87f1501012429f400023123426680008a80000017c92f07004815d92c83e1770000000d79f121f80018d9ba0ef1e88001ef03b0f101605214fa0a15706f1e10000d20000002700f896c02226e0718a09d210b239a0c95a100884a28259a839bfa941a08f582c9ae9fb14410390f1f727e00e81d14f0dd24b0f18608858018b5a71220838255a4a83088928e93ca6a9178aa00022e010181021042800216800199a9300019387404c9050e2956a621ee9d7996a1592
  | 8 => 0xc20648f81ca11319d0b98000d4a959672099a10000001f5260a3aa4d88984d000000075a7911817f25b8000f9a5299b0981531588d607ea6eaa784b80025c99297c1800002300b11c881b21195500880001a28b17b0ed96b92a8001ed80300d1578e994111b8001d884e1f4a8da570c015819016d9472492079690001aa25f1fb8d5a8a8d9097a8c9869888930001f02a000007d9ab29719821ea411520a49b48da854a5e14e11c06c9e218a96a2102ab00a8458f281729d160a1b05910213825d849a7ca451fd8c90559c70f023b8bd2ae15ea4001ea019e797d97680011994083001308880c09119fa9d9288b387994a96a81f91a07c25a21297b9560cb0ce85d0c518195922922999b80399e07f8000a811424c1e60000f621c22a280aa980006700029a8478df8000c39e0800221a1da418000c595a8000000002638b60001de8398001df9ca80000000000011680005191d03ea8a23ca818002af82f8c6aaf04f0111518ee02e8ce04120b06513d2271ee00486b97e8079be82790b8001852691f9159a2b80000000027c0000001739a60000fb0ec0001b6a9c0000002a10002989918000000a020f061a722358000c09311e51489778181119912991628500000000709388000001b881e0561bd00022b11580029123729802805e99099412f9d19b40001272501c500000009ba9613fa4ca5405d8908081a90a184a9e38001070001660001e19762531a49170e10000000c71821af1dc97f8e70448000cc1d70000780000c105998091a83fa8f0a727899da0e1e485a0961640eb1949188a90000000f32610c30860001c61d58000001dd81386c06f9248001418002580820001c994d1988ca97d0cca1d1360001fc92b0118de86600028627b89d9508128000000002520001430000b8130a8e00b2ad1d9800000170a8400026f00011380018f9d40c80969be0000679b78002248001f39ac9c40ff94280012080019917e0002a1a6ba4828f93c06216300021e07a1fe110057a010a518ca600b19b3248a0a9aba0e8ad84da1628786a8000509d68331a303f0201ea85e03685812504b0698ff069210841982a2f8050c1a459318000001a68000f68329e28001399f20a79ff09200007685f856a7305f010a548e403c9082059890d009e94c22620f9d1168a6413e08ca5d29ca2384721b8000f219707b1d00bba6c1338001920001b513b0a20000cf9da84a20700010180000000010c1fa00000002f0000d81b926fa0b88720600023080a0000000000c280000000003a8a89211c0a9b94b80016f0ed00023882b00000000000021980019ea6d1b100011225a8001ef80027f8db1da1780929450881d294b16fa2f0fe8000b682d86e98e0000b00940001f88290000359bba2aa9ea4f29780424d2289a82782351c01ad9fd00000023a0000bc8da
  | 9 => 0x264a7a18580009a8000be1882a8a25a670ea20313d8402470389e70af8fc0c88808d12331e809e13419f02a8e18e789f0e0a22877aa394c83381400026599517594d9699f0a1a85c02e1c91df0eba72909a7415c82680017118f0b782a0001eb9cd1a58000ac25f9729ea0c980023c0001468001d618792816b12196816007885296d00001d9d90000438000d38000001088001e5a120a69d4a43aa603d0db8002998f400008f0000df1a28e380025c00019a8faa1a0000b90612210721cb9cb134a3905b25782c00000f0be9c38fca188000378000000000000989420000158242a48ca18420c00001c19597223d2a800010300023f93708107311fa90800035020a9f80023600c9bd8000a5858a27aae8000a99e40001bf1ce0002409b2081aa218c0000002892431260270f72ac00010d11085b85100014008f96224e0cda0d1c6a91a3e93f00e1c78000151230361f60000001db282862a0405c88ea151788001a78179128000441f316c8aa88d26829282d0d299c94618eaa692c000043161906a7a93a2749f59ad17a1fc0a31b613223495d01a9dd00718d09c1259a4276a170450001f28e506593a9
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x9850e72d9543cc216b90c8a8c61325c86050d309a2e2302869850e72d95434c2c4b90c0a1a61645c46050d30c2a86b08a49852571149424c306b20a499261515c4524c93085aeda1aa41860d6394b420c306b1aa5a1061495cb4394430a2ae7a14a21852572d0d510c28ab9e84a8861465d7434c030b12e5a1a601870b43549300c389a1aa2980618358e6295320a2ae229a879050e7395142c8246b9ecaa1641439cf6550b2085ced29a85905257114d42c8306b20a699641515c4534cb2083ae6322a3105157114d4348264b98c0a1241385c46050920a1ce7b2a849042e7694d4248292b88a6a1241625cc6050920b42e2302849060d6414d32482a2b88a69924186195434c120c50caa126090648654c930482c4ba26498241075cf625502085ae4b2e861060e5358b4308306a9ac5a1841075ce649482083aed29e841041d7654f4208292b968728841455cf4294420a4ae5a1aa21051573d095108294bae8490041625cf4248020e12a7a124010723425452008216b94c929e21075ce6494b1085ae5324a70841d739925284217b92c7aa22107dcd62d5110c1ac7310a88860e635885444306b1ac42a2218558d6115110c4ac4b08a888619635805444314b12c02a2218c585601511085ae5324a68842d721974344216b90caa1a21071d95350d10a18e4a9a868841d73992524420eb98cba1221075cc6550910858eca92848850c735494244268b98c0a0a21385c86050510a28eaa1a62884b1741813144270b90c098a21491d54248510962e830242884d1731812144268b98c2a0221385c86150110a30eaa1a60884b1741853044270b90c2982214a1d54248110962e830a40884d1731852044216b96c6aa021075cf625501085ae5324a60850d729925304286b94c8a98210b5cb65d0c1085eeab16860860e5358b4304306a9ac5a1821075ce6494810a1ae7324a40842d76d0e5204286b9cc8a90210b5db435481083ae7b2e840841f7558f420420ebb4a7a1021075d953d0810c1ac7296840860d6354b42042c8b98c888021685c86444010aa2e7aa2200856172d511004298baca8880214c9d95444010a60ecaa22008533735511004299b92a8880214c5d35344010ac2e5a9a20085517594d1004388aa4a688021c49515344010e22a8a9a20087127454d1004388ba2a688021c4d915344010e20c8a9a200853175d0d1004388a9e8688021685cb4344010a62eaa1a20087115350d1004298ba6a488021545cf5244010ac2eb29220087215494910043a0a9ca488021c89515244010e42a8a9220087425354910043a0a9aa488021c89d15244010e42e8a922008723645491004390322a488021c8d0d5244010e4286a92200853175d0910042c8b9e8488021c454f4244010e42a5a122008531755091004388a9a8488021c85494244010
  | 1 => 0x510cb832a264a8865c15513254432a4ae5a1aa2195457290d510ca8bb9286a8865c19c94354432e0ae4a1aa21951573d09510caa2b9c84a8865c150e4254432e0c86a12a21970543509510ca93b9a84a8865c19cd4254432e0ae6a12a21951574cc9510cb82a1664a8865495d23254432e0a87192a219515744c9510cb83a1264a8865c15093254432a4ae8992a219707434c9510cb82a1a64a886551dd13254432e0ce8992a219545744c9510cb82ba264a8865415d13254432b12e8994a01971143546500cb90a12a328065d04c95194032a52e5a1ca01951973d0a500ca86ba264a806546dd54354032a56eaa12a019589744c9500cb852a264a8065c25513254032e228728aa01972142945500cba0994a2a8065c450d5154032e4284a8aa01974132545500ca94b9686a8065525ca4354032a36e4a1aa01970a7250d500cb84b9286a8065465cf4254032a92e7212a01970943909500cb8521a84a8065c250d4254032a56e6a12a01970a73509500cb84b9a84a8065465d33254032e1285992a019529748c9500cb84a1c64a8065465d13254032e1684992a019709424c9500ca94ba264a8065c2d0d3254032e1286992a01954b744c9500cb853a264a8065525d13254032e12e8992a019509744c9500ca86b94c8a98838354d62d0c4185aeda1ca420d0d73991521060ebb4a7a10838358d52d0841a52e5a1ca020d1973d0a5010694b9686a8083465cf4254041c1cc6b14a998d0e7295143cc646b96caa1e63439cb6550f3185ae4322a118cc572185434c668b80c2a1a63439cb6550d31b0ae430a8698d9170185434c70ca1ac0292634a5c05250931c1ac82926498d4970149324c616bb686a90638358e52d0831c1ac6a968418d1575d0d310c6c2b968698863c1d0d524c431a52e5a1ca018d1973d0a500c694b9686a8063465cf4254031e268698aa018e0d6398a54c868cb80a6a1e43439ce5450b2191ae7b2a8590d0e73d9542c86173b4a6a16434a5c05350b21c1ac829a6590d497014d32c860eb98c8a8443465c05350d2198ae630a8490ce170185424868739ecaa12430b9da5350921a52e029a8490d857318542486d0b80c2a124383590534c921a92e029a6490e146550d314871232a8498a4391195324c521b0ae89926290e0e5358b4308706a9ac5a1843075ce649482183aed29e8410c1d7654f4208692bae8490843615cf4248421e0aa7a124210d2972d0e500868cb9e85280434a5cb4354021a32e7a12a010f23424855008686b94c8a98818354d62d0c4085aeda1ca42050d73991521020ebb4a7a10818358d52d0840a4ae5a1ca22051573d0a5110292b9686a8881455cf4254440c1aa6b10822060d63548411030ab1aa220881895895110440c32a6b00822062952580411030731ac52a661439ca5450f3091ae5b2a87
  | 2 => 0xf4000003054000000444000007e000005cc0000000000000ac00000004180001400224000d000000c5591561f4001e92600000000004b0b9000293f400449334acb300000568000000000015330953cc6627cbc000ca518b60ec2200000310a8000000000c0004100000028801a40000000000230c49a238004156a09ca22280000000001484d4000000700000218000005d1f1180000017c644b8550011f0000000153000cd0e0000a000540000b8b8118704683615c000004516800000970000024000000000f49b0000e4c972000000014241c8200012000f602c4b33800300004852807000370000003a000b03e0fb38d6c24811000be2b4530016f598320f0d8410fc0d400000164517533c005785b55400000f20000028c00000000003f5dc48398a715800580215c094354000000000000000e800000000c348c590000054545000004f0ac000000dc992dcea170004bc6f1a0004f8f73840000000000000002d000521116550485000001e0d9000da19d62001172a4c951c652787f43800000000000000000000753f88d000a6101100015f0680200006000d2184185b8d70000022c0044c00001192c8004a8ed205680014d1ec0053000000334b4543c000550623bcbb28000000934ec0056c0034d4b258000000029000000000004a00000000885b40000000000004e1490015c490423a4e5511714e4f1000031e53021c6a479675d8f50bd780903e0511d4346d494bf000e4309631cc0000000000004dc005494331d0a46c00000001c4741d94a00116488981ad00408ba1353a02158025612ac5e42c8f4a4250c1092b8011804e10d36140d62742a2bcb4010008020000004002000080080006802000380500a000020000000000040040000800006010000080001000008020000200004038000080a018100180200000028020c0020000000800000000080c008060001a028000180e010120300004006000000080603804060100780c020020282005802000140000800838008160185000014010020000c04800038000080401004000020080a0000000019435cc6154b43c4ac230aa5a1d2a7018552d0e94b80c2a9687435cc6054b43a4ce2302a5a1d257118152d0f14b00c0a96878a54a6014743c52a4b00a3a1e255298450d0f12a92c228687435c86154f42c2ac230aa7a151a7018553d0a8cb80c2a9e85435c86054f42a2ce2302a7a15157118153d0b0cb00c0a9e858654e6014742c32a6b00a3a16155398450d0b0aa9ac22868543dd56250c32c1acaa1c841950d7598d420ca87baac6a106507dd5644c83285eeab22641948d74d95320ca86bacc89906543dd5644c83291eeab22641960f75591320ca46bb2a899065615d13294432a4ae5a1ca21951573d0a510ca86ba264a886545dd54354432a4eeaa12a219585744c9
  | 3 => 0x1d36d150006338800480df2c410470003e8cb5740f53c842f4e71c84f3e45101000000474f50c000000b00003400000d1285694200055d311306c0008c2a8d0000eb0000005c00000390001e31800001340010f5acee0001b49c0000019161594fc6e20c00098dd2d4e00000000013294ff40c000009c000ec001740000035049000de404c800020538910000007c7700
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1e0102a00006a8240048b2c4c0193018000020c000008470c0020d004c9001e145428200002000000a002e70e91004001f4e8c0000094380526d10000100018126080010008000c05735846154b43c21615c06154b43c09735806054b43c21715806054b43c05725846154f42c11615c06154f42c09725806054f42c11715806054f42b01844c95194032b01844ca5154032b01844c95154032c09645c0524c93190587d0d524c431b0182d0d3154031c09645c0534cb21c09645c0534c921c04655d1324c5219058754f4248421b0183d092154021c05645c4524c93090987d0d524c030b0182d0d514c030c05645c4534cb20c05645c4534c920c08655d1324c1209098754f4248020b0183d095148020905821d5434c510905831d54248510909821d5434c110909831d5424811092182dcd544401091183dc95444010b01829d15344010911871915344010b01821915344010d01535cb4344010b01839d15244010921871915244010b0183191524401092187d0d52440109118754f4244010d017354b4244010
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (27102+((h/294+packedAt s5K5 (23868+(h % 294)*11) 11) % 1283)*11) 11
  | 4 => packedAt s5K4 (57326+((h/458+packedAt s5K4 (52288+(h % 458)*11) 11) % 1652)*12) 12
  | 3 => packedAt s5K3 (19723+((h/125+packedAt s5K3 (18473+(h % 125)*10) 10) % 601)*10) 10
  | 2 => packedAt s5K2 (2678+((h/14+packedAt s5K2 (2580+(h % 14)*7) 7) % 68)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x77c3de7e7c7f1c63e3f311e3f1c71cf9c530cf
  | 1 => 0xbbfc1f9f9f8fe07c7c7c1e3c7e381f3e4ac333
  | 2 => 0x3cffe01fe00fff807f8fe03f803fe03fb30c3c
  | 3 => 0xc0ffffe0000fffff800fffc0003fffc03c0fc0
  | 4 => 0xfffffffff00000000fffffffc000003ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4202008100840400004090010408001045
  | 1 => 0x40404001201008080020420080810004112
  | 2 => 0xc1488148092448094015202904924025130428
  | 3 => 0x1e91080152489040092a5480092492802c0a80
  | 4 => 0xefe211515800da52524f99324d80c2853fa000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_32882
namespace PEqualNP.Outside.L_meta_32882
open PEqualNP.Outside.L_meta_32882.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12454f12967a3178f428dc2c00d40000001c8012890006c0402b3c2c0283218fb06e21a2e36485334c1c83b06000322a0002d289cbba1ac42803a60e04263889a520698a011830000240cc0006081800c00a0002ffd500bfe5402ff5500bfc54037fd4c09fe53037f54c09fc5302ffd0c09fe4302ff50c09fc43037fd4807fe52037f54807fc5202ffd0807fe4202ff50807fc42027fcc807fe32007f4c807fc32017fd44057f51017f94405fd51015f54405fc51017fd0405fe41017f50405fc41017fcc405fe31017f4c405fc31017fc8405fe21017f48405fc21037fd4003fe50037f54003fc5002ffd0003fe4002ff50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10017f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826410ff4413207ff8209903bff654c01d7fb2a600eff99530035fcca9803bfd654c01d7eb2a600eff19530035f8ca98037ff644c01b7fb22600dff9913002dfcc898037fd644c01b7eb22600dff1913002df8c898037ff544c01bff2a2600dff5513006ff8a898006ff634c009ffa9a6004ff94d30027bca698013fd534c01deea9a6004ff14d30027fe8698013fe434c009ef21a6004ff50d3006fba8698013fc434c001ffb126000bfd8930067fcc49800efe624c001feb12600cff1893001df8c49803bff524c019ff292600eff54930067f8a498037ff424c019ff212600dff50930067f88498013ff324c009ef9926004ff8c930027fa6498003dd324c009fe192600bffd853005dfec29802ffe614c0057f30a600bff5853005dfac29802ffc614c0057e30a600bffd453005efea29802ffe514c017fea8a600bdf5453005ff8a29802fff414c017ff20a600bff5053005ff88298013ff314c009ef98a6004ff8c530027fa629802fdd314c009fe18a600bffc853005ffc429802ffd214c017fe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe6098013fb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ffc813000ffc4098007fa204c003fe1026001ffc413000ffc2098007fa104c003fe882600bfe4413000ff82098027ff65480137fb2a4009ff99520035fcca90027fd65480137eb2a4009ff19520035f8ca90023ff64480117fb224008ff9912002dfcc890023fd64480117eb224008ff1912002df8c890023ff5448011ff2a24008ff55120047f8a890003ff63480017fb1a400aff98d20025fcc690003fd63480017eb1a400aff18d20025f8c690027ff5348015ff29a4009ff54d20057f8a690023ff4348015ff21a4008ff50d20057f88690006ff6248007ffa924003ff9492001fdca49000ffd5248013f6a924003ff1492001ffe849000ffe4248007f72124003ff50920047da849000ffc4248007ff9924003ff8c92001fdc649000ffd3248001f69924003ff0c92003ffec29001eff614800fff30a4002bf9852003ffac29001efd614800ffe30a4002bf1852003ffea29001f7f514800fff28a4007ff5452003efaa29001ffc514800fffa0a4007ff9052003ffa829001ffc414800fff98a4007ff8c52003ffa629001ffc3148007ff90a4003fbc852001ffc429000ffd214800ff690a4003ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001fe8c12000ffa6090003f93048003fe1824001ffc812001ff64090007fe2048003f71024001ff0812000fd84090007f82048003ff8824001ff8412000ff42090007fd104800ffc8824001ff04120
  | 1 => 0x14364692b3e411000131e8f3418af300ac0014030c7623429278ff000fa48c1e40541068b61f930338914bc26450000b00015c950cc043bd3a0ac000f8740b93b1a42f00023120ec0ec003c0000e000000c720d330004642456264594c84a19454200351f40903c142e86421c0d030961cd0d3444e0082a144104312d2e01f2703928503104d81bd3d261194f0930dc2417025228d54d8203809b124882ac5d4a8074dca332c9f00d2623ca52c400000c133ceb160004c4e6000b51b4c44907b0602d49c664b11e364d42ecf7204b01a83f038783b47146c012fd1f02cfb17c8b37c303f4b32f4672409225c003a40000000000a9184001686b09c0045915000b2000002743c29910324fc00072000c847400000003840000050001112dd200000a000d200017214001310f000f643800048000005e268004112944900134003d0790f4424d0520006e1c0f54d419000cd10cea0743a0840031800054a24b8081809400031114e7000a811cde1a125330e43e00000000000d62113e44c622b4c21fcbc4fcb946102291051dc7c13c4036d1c280d7329083b82234c4437432314551b0d041cbe000000001c45c0042cfe488e242828368050102c10031201428230080000080000c0a061182c0e100002c000702800160900018080b1981c18000107c4a13090182a031981406050900000050000400020188016000180c3e33130401003000900202068400603000000206000142221050000c000604c000800818220d0982000000000c02050380c25ffb2a6412bfd9532097fcca9901afe654c825feb2a6412bf59532097f8ca9901afc654c823ffb226411bfd913208ffcc899016fe644c823feb226411bf5913208ff8c899016fc644c823ffaa26411ff9513208ffaa899047fc544c8077fb1a6404ffd4d32027fca699013fd534c809fe29a6404ffd0d32027fc8699013fd434c809fe21a6403bfd893201ffea49900ffe524c807fea926403ff1493201ffe849900ffe424c807fea126403ff1093201ffe6499013ef324c807ff1926403f78c93201ff8649900fdc324c807f61926403f30c932087fec299042ff614c821ff30a6402bf98532087fac299042fd614c821fe30a6402bf18532087fea2990437f514c821ff28a6410ff54532086faa299043fc514c821ffa0a6410ff90532087fa8299043fc414c809ff98a6404f7cc532027fc6299013fd314c821ee98a6404ff0c53201ffe429900fef214c807ff10a6403ff48532087da429900ffc214c801ffb026400bfd813207ffcc099006fe604c801feb02640fff1813200df8c09904bff504c81fff2826412ff5413207ff8a099047ff404c81fff2026411ff5013207ff88099013ff304c809ef9826404ff8c132027f8609900fff204c807f79026403ff8813201ff84099043ff104c81fff0
  | 2 => 0x218aa4e0342b88c238630005348475000f10581b0188229ce838d392d05b000003944b000dc000004a0003c8890
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb705893000ddc764c93001edc764c93000cdc764c930115df754c930115dd754c93010ddf744c93010ddd744c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930067cc624c93001ecc624c930105df714c930105dd714c9300fedf614c9300fedd614c9300ff5f514c9300ff5d514c930067cf214c9300ffcd214c930007db704c93000dde704c93000ddc704c93007fd8704c930026df604c930027db604c93007fcf204c93007fda204c93007fda104c9300ffd9104c930024fe76d8d20056de63d8d20004ff75d8d20034fe75d8d20004fd75d8d20034fc75d8d20004ff74d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2007cfd73d8d20056de43d8d20006dd43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d200f6df32d8d200f6dd32d8d20004ff71d8d20014fe71d8d20004fd71d8d20014fc71d8d200067f51d8d200067d51d8d20006de31d8d20056dc31d8d200f6ef21d8d20006ed21d8d2001cff70d8d2000cfe70d8d2001cfd70d8d2000cfc70d8d200e6df30d8d200e6dd30d8d200e6fa10d8d20006f910d8d20024ff7658d20056dc6358d200ddef7258d200edfb7058d20004ff7558d20034fe7558d20004fd7558d20034fc7558d20004ff7458d2002cfe7458d20004fd7458d2002cfc7458d200e4ff7358d20006df7358d200dcff7258d20006ef7258d20004ff7158d20014fe7158d20004fd7158d20014fc7158d200067f5158d200067d5158d20056df3158d20006dd3158d20066ef2158d20006ed2158d2007cff7058d20006fb7058d2007efa1058d20006f91058d2000dec764c920026ec764c92000cec764c9200d5ef754c9200d5ed754c9200cdef744c9200cded744c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920057cc634c920026cc634c9200c5ef714c9200c5ed714c9200beef614c9200beed614c9200bf6f514c9200bf6d514c920057cf314c9200bfcd314c920007eb704c92000dee704c92000dec704c92007fe8704c92001eef604c92001feb604c92007fcf304c92007fea304c92007fcd304c92007fea104c9200bfe9104c92001df8764c120026f8764c12001cf8764c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120057d8634c120057da534c1200b7d9534c120057da434c1200afd9434c120007eb724c12001dfa724c12001df8724c120067e8724c12000efb624c12000feb624c120067ea524c1200b7e9524c120067ea424c1200afe9424c120067db324c120067ea324c120067d9324c120057e9324c120007c9324c1200a5fb714c1200a5f9714c12009efb614c12009ef9614c12009f7b514c12009f79514c120057db314c12009fd9314c120067eb214c12009fe9214c120
  | 1 => 0x7f661540000000000062528007a00248000063680000061128000000228013000002497200001487e00000016c7c68b1400002e80000823db71081b730000094001dc000c2b0015e9f690c4000005998484655000009e002553a5e091a4f2bb672257a0000099642967b6106006395c0a724700000320012da6a70000000001b2fc006f00000000000064fa8c6200098ab0022800e10000000dd001cc000000000000000144d00438af838000013400000019c000000000000000024b000002043000431b000ca0990c8e2100000001d0032c00000008800a8208349c0000001ca00000000000000000000530000000002c1683c000018440000000000000414800000002800000000000002b00000000183c080000000002c801c6d65ab7c000007800a6a3000000000000e0002000000000000000da0000001421700000000046b20720000005ce1654854006e1600000000000000004d8004e00002e000003200000003ab8000000036404000000000001b98068e200354000000000b800088b8ca000022c006b0020000000000000000037800000000000033b00000002d028009a03a5c00a2118cd9a2a6ba45a800603253800000a000ae74368004800000000000000002d250ac0000001511070000e860001f00000960014000000000186000023c00443d1a966004800000c14297d0e99002818c5b00001620000001789356ae8007421068fcdb0000000000013c3e000000000001a80000b71d8005e0e3c000000072000000180000020500802000000404010000000000181000030080002010080800000100002030000c00000000000000000004000000000000100406070000c0003000040000000080203020040a0100000020102014000100cfe76d81320efcc32d813207efa60d8132004ff75d8132034fe75d8132004fd75d8132034fc75d8132004ff74d813202cfe74d8132004fd74d813202cfc74d813201cfd73d813200cfc73d8132024fd72d813200cfc72d8132004ff71d8132014fe71d8132004fd71d8132014fc71d81320067f51d81320067d51d813211edf31d8132006dd31d81320eeef21d8132006ed21d813207efa30d813207efa20d8132067cc325813207ef8605813201cfe76d8930066ee62d8930004ff75d8930034fe75d8930004fd75d8930034fc75d8930004ff74d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930066ee42d8930006ed42d8930066ee32d8930126ed32d8930004ff71d8930014fe71d8930004fd71d8930014fc71d89300067f51d89300067d51d8930126df31d8930006dd31d8930006ee21d8930066ec21d893000cfe70d8930024fd70d893000cfc70d89300deef20d89300defa10d8930006f910d8930066ec625893011df
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9006003856c940a00b000000e4d8e00f01a61e088130c0001a6c0121400d0b8b00b402500c508d3a013a238000b560a802e1001b914030b3b0a78c800e019955e0091f08e94a30808400030000200060000c0014100020010162fa1375d81320045ec26ebb02640687e85dd3604c8010fb0bba6c0990031ddc551d81320163a38aa3b026400ec531487604c8010ff0aba6c49801a1f21574d893002c77c3a85b126000ec531887624c001ce2a2886c498003b44c510d89300077110a21b126003ace86d89324c0010ff0aba6c69001a1f21574d8d2002c6fc3a87b1a4000ec6314876348001ce2a2886c690003b48c510d8d200077090a21b1a400087f855d1634800d0f90aba2c6900023de057458d200147a40ae8b1a40008df835c563480011df04b8ac6900031ddc55158d200163a38aa2b1a40028dc874c563480051d90e90ac690003b14c52158d2000c7d43ee0b1a40028f8874416348001ce2a2882c690003b44c51058d200077090a20b1a4004ace86d8d32480037910e992609000f7221d324c12000de5432649824001bc8864c93048009d910c9926090013b2dd9324c12001ee53b2649824003dc8764c93048009d90ec992609000f321d9324c12014de5c2a649824029bc9854c930480517970899260900a2f2611324c12013de5c0a649824027bc9814c9304804db96e2992609009b725c5324c12012f65b0a649824025ec9614c9304804be96a29926090097d2545324c120
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x5870875451058d20
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x98a
  | 8 => 0x98d
  | 9 => 0x98e
  | 10 => 0x98c
  | 11 => 0x9ca
  | 12 => 0x9cb
  | 13 => 0x9cd
  | 14 => 0x9ce
  | 15 => 0xcc9
  | 16 => 0xcca
  | 17 => 0xccd
  | 18 => 0xcce
  | 19 => 0x9c992
  | 20 => 0x989d2
  | 21 => 0x9c995
  | 22 => 0x9c996
  | 23 => 0xcc992
  | 24 => 0x98cd2
  | 25 => 0x98cd5
  | 26 => 0x98cd6
  | 27 => 0x1709
  | 28 => 0x15c9
  | 29 => 0x168b
  | 30 => 0x12cb
  | 31 => 0xcc9d2
  | 32 => 0x9ccd2
  | 33 => 0x9ccd5
  | 34 => 0x9ccd6
  | 35 => 0x150c
  | 36 => 0x128c
  | 37 => 0xcc9c99a
  | 38 => 0xcc989da
  | 39 => 0x9c98cda
  | 40 => 0x9c98cdd
  | 41 => 0x9c98cde
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
  | 7 => packedAt gbK7 (12877+((h/107+packedAt gbK7 (11914+(h % 107)*9) 9) % 387)*10) 10
  | 6 => packedAt gbK6 (11877+((h/77+packedAt gbK6 (11184+(h % 77)*9) 9) % 492)*9) 9
  | 5 => packedAt gbK5 (3739+((h/20+packedAt gbK5 (3599+(h % 20)*7) 7) % 81)*7) 7
  | 4 => packedAt gbK4 (71+((h/1+packedAt gbK4 (70+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x88e00c63e3ff311e3f0e38387e1f0013c530cf
  | 1 => 0xf00707c7c70c1e3c7f1c03f8fe3086d0ac333
  | 2 => 0xf0007f807f80fe03f801ffc00ffc318e330c3c
  | 3 => 0x7fff8000fffc0001fffff000c1f03c0fc0
  | 4 => 0xffff80000000fffffffe00000000fe003ff000
  | 5 => 0xffffffffffff0000000000000000ffffc00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x200000809000040900080802000000401045
  | 1 => 0x9041024242200204280401204820825004112
  | 2 => 0x9009248049045202902492800958308a130428
  | 3 => 0x1249490008a548004925256000c1502c0a80
  | 4 => 0xa24300000000f993246c0181204852003fa000
  | 5 => 0x4c9c7e72724e0000008006064192adff800000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8fffffeeafeeefee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_32882
namespace PEqualNP.Outside.L_meta_32882
open PEqualNP.Outside.L_meta_32882.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 8 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_96 : Interval s1Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 102 := (concat (concat bs1_3_0 bs1_3_32) (concat bs1_3_64 bs1_3_96))
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
theorem bs1_4_128 : Interval s1Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_160 : Interval s1Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_224 : Interval s1Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_256 : Interval s1Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_320 : Interval s1Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_352 : Interval s1Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_416 : Interval s1Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_448 : Interval s1Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_512 : Interval s1Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_544 : Interval s1Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_576 : Interval s1Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_608 : Interval s1Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_640 : Interval s1Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_672 : Interval s1Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_704 : Interval s1Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 725 := (concat (concat (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128))) (concat (concat bs1_4_160 (concat bs1_4_192 bs1_4_224)) (concat bs1_4_256 (concat bs1_4_288 bs1_4_320)))) (concat (concat (concat bs1_4_352 (concat bs1_4_384 bs1_4_416)) (concat bs1_4_448 (concat bs1_4_480 bs1_4_512))) (concat (concat bs1_4_544 (concat bs1_4_576 bs1_4_608)) (concat bs1_4_640 (concat bs1_4_672 bs1_4_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_64 : Interval s1Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_128 : Interval s1Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_160 : Interval s1Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_224 : Interval s1Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_256 : Interval s1Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_320 : Interval s1Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_352 : Interval s1Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_416 : Interval s1Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_448 : Interval s1Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_512 : Interval s1Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_544 : Interval s1Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_608 : Interval s1Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_640 : Interval s1Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_672 : Interval s1Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 682 := (concat (concat (concat (concat bs1_5_0 bs1_5_32) (concat bs1_5_64 (concat bs1_5_96 bs1_5_128))) (concat (concat bs1_5_160 (concat bs1_5_192 bs1_5_224)) (concat bs1_5_256 (concat bs1_5_288 bs1_5_320)))) (concat (concat (concat bs1_5_352 bs1_5_384) (concat bs1_5_416 (concat bs1_5_448 bs1_5_480))) (concat (concat bs1_5_512 (concat bs1_5_544 bs1_5_576)) (concat bs1_5_608 (concat bs1_5_640 bs1_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_32 : Interval s1Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 40 := (concat bs1_6_0 bs1_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
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
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
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
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 6 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 2 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffafffefff8fffffefafefefef8fffffffafffefff8fffffeeafeeefee8fffffffafffefff8fffffefafefefef8fffffffafffefff8fffffeeafeeefee8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,4,68),(inputs.getD 7 zero,4,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,4,68),(inputs.getD 7 zero,4,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_32882.Model.Repr at out
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

def mono : List Gate := [⟨.and,[5,7]⟩,⟨.or,[3,4]⟩,⟨.and,[9,6]⟩,⟨.or,[0,2]⟩,⟨.or,[5,7]⟩,⟨.and,[11,12]⟩,⟨.or,[0,1]⟩,⟨.or,[14,7]⟩,⟨.or,[4,6]⟩,⟨.and,[15,16]⟩,⟨.or,[8,10]⟩,⟨.or,[18,13]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_32882

open PEqualNP.Outside.L_meta_32882 in
theorem PEqualNP.Outside.L_meta_32882 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
