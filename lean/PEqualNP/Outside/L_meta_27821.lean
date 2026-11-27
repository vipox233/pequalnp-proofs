import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_27821.Model
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


end PEqualNP.Outside.L_meta_27821.Model

namespace PEqualNP.Outside.L_meta_27821
open PEqualNP.Outside.L_meta_27821.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_27821

namespace PEqualNP.Outside.L_meta_27821
open PEqualNP.Outside.L_meta_27821.Model
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
end PEqualNP.Outside.L_meta_27821
namespace PEqualNP.Outside.L_meta_27821
open PEqualNP.Outside.L_meta_27821.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x30007802400000460098036000000000a8a521800000411243a9c0003e08400000158000000010011080005cd001c0018050000000001280160060500a8000001c0000058e003c00026004400d0050020000000012640008002002000608000000c000ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x18300008ac00014c000028006c8878fc0048000000903444c858000d4464009964f931540070cc00840000113400003c55388c0159153c40000148015c0000c40000dc0100000000f4391c040000c000145168007401205d50bd4068d52908006000d8004d601cb4e0b87c24b0ecd0a8a02c20e89d24f0a4000095190d2c011000800104e4000a001c0220040a2e0c12001a02001e0e000804000210040e021c0006113e5390e7aa321db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010f72a021d794e42aea9c859c43ccaf4a1995e543329f2a4653d548ca7ea8994f15132ce21a653e53d067aa920d7d4d41ae29a839f5350678a6a0e714d418e29a83b7515067ca820cfd53319e2a6633e548c67aa918e710e31daa0c633f544c678a898ed505319f2a0633d540c7388618db94831b6a90637a500c6f2a018cf952219eaa4437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53902baa7206710f30b7296616d52cc27ca9184f552309faa2613c544c33886984f950209eaa0415e53082baa6105d94420baa8841e9200827ca9884f55310b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2e51a2241a6030020b0439240c000a0a62a71609e00088c30488c237265254443c95495110f315194043ca5495010f315154043a558443ccb184354332a5584434cb0e6214d41c358853507156114d41c698053507196014d41a5584438c69463506318d195414c61d6510c31c310d520c71843540318718d54886956110f30c310d52cc2956110d30d8545200821c6355310
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x40c0010801445c44354332c0ac4b08a6a0e09625805350708b0ac029a83415c44354b30
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
  | 4 => packedAt s1K4 (2697+((h/30+packedAt s1K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s1K3 (990+((h/8+packedAt s1K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 10)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x78f1ffc3f8fc7e3c71c0e3fc7e1c3fe30f70f
  | 2 => 0xf80fe1ffc7fff8fc07e00fc7f8fffc1e4339f3
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x50118484921288014304a2094124414c305305
  | 2 => 0x2221009040401080421044208509010412052
  | 3 => 0xa5444912212900368802489092092a81828c28
  | 4 => 0x31004ca081019244d1486000e48c08c4940f80
  | 5 => 0xc6089103364e249b26938f24001033196bf000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_27821
namespace PEqualNP.Outside.L_meta_27821
open PEqualNP.Outside.L_meta_27821.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x84600200df43be43bc43dc439c43
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x11484c1800211e5390f1ca421e354843cb28887955110f34a021e654043
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x4203055254443c25495010f115154043
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 5
  | 3 => 7
  | 2 => 3
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
  | 4 => packedAt s2K4 (84+((h/1+packedAt s2K4 (80+(h % 1)*4) 4) % 9)*4) 4
  | 3 => packedAt s2K3 (197+((h/2+packedAt s2K3 (189+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s2K2 (116+((h/1+packedAt s2K2 (114+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf8f0fff0fffe3f0f1e380e3fe3fe0ffc30f3cf
  | 1 => 0xff0fff0fffc7f01fc00fc7fc7ff07cc33cf3
  | 3 => 0xfff0fff0fff8ffe0000ff8ff8fff8303cf3c
  | 4 => 0xff0000ffff0000fffffff000fff00003fc0fc0
  | 5 => 0xffffff00000000ffffffffff00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1182212442440050a09220920920528305145
  | 1 => 0x5222842428480850144244424424a050c12492
  | 3 => 0xa4444848829001aa2004889089094a03028a28
  | 4 => 0x30066682221c92334690e000f2406319540fc0
  | 5 => 0xc088880ccce124cc99270f2400018c62abf000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_27821
namespace PEqualNP.Outside.L_meta_27821
open PEqualNP.Outside.L_meta_27821.Model
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
end PEqualNP.Outside.L_meta_27821
namespace PEqualNP.Outside.L_meta_27821
open PEqualNP.Outside.L_meta_27821.Model
def s4K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1c300b00a9001250800a8ae59a1000009a000000000e7989060000a8003004040006fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8040000000241e040081c0e04028000c0d0280404000c000020f010080c2600808001002020020abe41ccaf50732be40ccaf50332bd438caf90a32df328cbbcca32be418caf50632be408caf50232ef324cb78c932bf414caf10532bf404caf10132be430caf90832df320cbb8c832dd320cbb4c832cd320caf90432f6410cad90432bd410cbd50432b5410caf90032fa400cae90032bd400cbe50032b9400caf90b31bd42cc77ccb31dd32cc6f90331bd40cc6f50e31be428c6f50a31be418c77cc631f7318c6f90231bd408c6fd0931bc424c77cc931dd324c7dcc531de314c6fd0131bc404c6f90c31be420c7b90831ae420c6f50831ed420c6b50831be410c77cc431f6310c774c431f5310c754c431be400c7e90031ba400c6f50031f9400c6e50031bf43c86f90f21bd43c86f10f21ee32c87b4cb21be40c86f50321bf43886f90e21bd43886f10e21bd42886f90621f631887d4c621ef21887dc8621be40886f50221bf43486f90d21bd43486f10d21ee32487b4c921f631487d4c521f721487b88521bf40486f10121bf43086f90c21de43086790c21bd43087750c219d43086f10c21be42086f90421ef21087d88421ed21087d48421e521086f90021fa40086e90021bd40087e50021b940086f90b30bd42cc37ccb30dd32cc2f90730bd41cc37cc730dd31cc2f50e30be428c2f50a30be418c2f50630be408c37cc230fb308c2fd0930bc424c37cc930dd324c2fd0530bc414c37cc530dd314c3ecc130de304c2f90c30be420c3b90830ae420c2f50830ed420c2b50830be410c3d90430b6410c2f50430f5410c2d50430be400c37cc030fa300c374c030f9300c364c030bf43c82f90f20bd43c82f10f20ee32c83b4cb20be41c82f50720ef21c83b48720bf43882f90e20bd43882f10e20bd42882f90620bd41882f90220fa30883e4c220ef20883ec8220bf43482f90d20bd43482f10d20ee32483b4c920bf41482f10520ef21483b48520fa30483e4c120fb20483b88120bf43082f90c20de43082790c20bd43083750c209d43082f10c20be42082f90420f641082d90420bd41083d50420b541082f90020ef20083e88020ed20083e48020e920082fd0f10be43c42f50f10bc43c42fd0b10be42c42f50b10bc42c43d8c710f531c43d88710f521c42fd0e10be43842f50e10bc43842fd0a10be42842f50a10bc42842f50610be40843e8c210f930843e88210f920843dc4210fb10842fd0d10be43442f50d10bc43442fd0910be42442f50910bc42443d8c510f531443d88510f521443e8c110f930443e88110f920443ec4110f610442fd0c10be43043790c109e43042f50c10dd43042750c10bc43042fd0810be42043b90810ae42042f50810ed42042b50810bc42042f90410be40043dc4010fa10043d44010f910043c44010
  | 1 => 0x989a000d49584c731d4000200000000000359be000f8790fc321c42300019116050627c9a658924571967f87e000000d0a00019c4b9541e2460015a1d9c8962540f9800001a00136001228904000000001b85a0003a86c0a1081e8503081e2520c6c0226f22a6e84e500f2111c21a9da2aa367f1a83b12a4c97a0000000244801d0758588823a81100000d87e0005c23c521e036992838ce5818e2c12080966868482902c668f4530f0000001d10a11a5000178610a800068001dc340000011e2e800002282e03c922065d9f0000007a88a430845b810630bc261ae00150001e212a14000002ba4c73a348c836438327d1ec389a47a23e90816629527e82a51988841d20014a5b1280e09e508b209000000006c830650fe8291800198001022d000860000021e00208948de0000004808001c65123093800329f64f0dc418040008e1b80044056798006080007186060521680c240020016a1805c8b0543b9646d9aa2099e641122980039800199264c1347611a0ba122d93e000960013a001b4218f67b8003ea1c17974560ac8e25a2fa4a000e8539de0380000000109c08892c01a2e3317e001560009c00138728c66b2265f072000000280000000000004511c5c8000007c00000000000003a0000000000301a23100000000000d200070381a03915e2208028800859040024000092008080001000101a030200800040100802090000802030000406090203000000080002000002404010000400070f030040801800020c06808041500064060701820081108014
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x63b13150031c898a8018ce94043c8672a021e438c434cb219d2808710ce54043887288698c433b5050d219c2828690ce9404348672a021a432c544c921c621a6490d91453248668a898a4394434c521b22926290f14c9314863ca6202431d53101219d2868610ce543430863aa9218431e5310c21972908610cd9444308674a021843395010c21c6a1e4210e550e21086caa5108432f5448421c6a1a4210cdd51210872a8690843675448421d3aa24210e9d0d210878c8690843a54348421e2a1a4210e150d21087348720043994390021f090c8010e9485400873486a0043994350021f090a8010eac85400876442a0043a92150021d890a8010e8485400866ca221261355110930c6212649856141324c25ca420a612d5210530ca20a629856141314c34c8520861a54290430d3212821869509410c31a85980619541cc030aca9c60186a50a300c36283180611f544c030c6a12601865505300c276a898061a9424c030d8a0a601856d51300c336a898061ca424c030cca12601872509300c3128498061d2414c030cca0a601874505300c3228298061365110f209aa8887906310d32c826ca221c41355110e20cc21a61104dd454348268a2a1a41365110d209aa8886904b1513248318869924168504c9208f29882904754c41483488290a416850485209c2a260906610d30482d0a498241c9324c1209b28e86104d547430823aa9218411e5310c209729086104d944430826aa2218413a5010c20cb21c82106550e410832c86a0841954350420c6a1e40106950720083328710041695288020d8a0c40104bd51200831a8690041a541480209daa240106650d200836282900416b5448020d5aa240106ad0d20083948690041a94348020e4a1a40106250d20083c48290041a94148020f0a0a401068505200825ca421e212d5210f108f29885884754c42c43288698e21a442487109729087084b548438423ca6214211d5310a10cc21a61086a109208425ea4a1a212c5250d109729086884b548434423ea6a12211c53509108f29884884754c4244268a898a2194434c510b828262884d15121443488490a217050485109c2a260886610d30442e0a298221d1314c1109c2a240886a10920442e0a290221e121481109729686084b54b430423aa9218211e5310c109729086084b548430426ca2218213a5010c108f29e84084754f420425aa9210218e4390810c6a1c84086390d420431a86a10211e53108108ea9884084b948420426ca2210213a5010810caa1e20086950b1004272a908021994384010d4a1420085c546100426ea888021954344010d2a1220084ed5110043328688021a94244010b9aa220086cd5110043668688021d24344010d8a1a20087450d10043228688021b34244010f121220086c50910043c28488021a14244010
  | 1 => 0x2c0a8498a65f8346c8d80f98811000002162510e321d21b800359aa591c2300e81f97c3b2188098a2317a8106467800608fe000000006c61a1253a1a241ee3704a381fa290382497800000479021f1e87a9b4001e46980000000009cc5282c001c84f0ac00120078c26c22a000002c8000000083930341fe258604c99041042061de0003a6b0d27d8ce4d22c0490a5b962001e2570405c0008990c1582403196001724520036912540ea0b8007593e5782041800889d0000a24d9a84a15a000460001a83138001c61e8b8229da0a8a0149f48299408848461ba3781635198000807c8141c12a6f0b43b9c4268880d8b65109e1a008671565081c3da28780aa4b110150265821e700841384c5a8003e9ce038ca3918c89146000005503c3112268000818623f1ca6e0f8001ae001d80017653116400ba00152040784e91a688f27b08202948820cc691dc00158170e27980000030000741a8bc6d8000011c3c0500a2100c89c5999a871808808e500e664872639081d866219743d0067e1680000000000750000000000214611f031898168be5b12e001fc2b8000005e16004491be030343631080200c4702820321c0080800000002406060081c000202010180b010080601000440011010000e04000080406000080000088100e06008600004008100412080300c140001c000d0083c14020000002000180c260e000042a0a048002c000000c080000ce940414ca72a020a653651101329aa8880995354e320ca3ea8990652f544c832a7aa2641963d51320cb8a65208658d3250432e2992821965cc9410cb4c64a0865953250432d29928219614c9410cb926520065b24190032d8a0c8019634c9400cb9264a0065b24150032d8a0a801966cc9400cb5464a0065993250032d49928019624c9400ca74a021263395010931c62126498d5145324c65ca4202632d5210131c6a166218d554e310c74a85188631f544c431c6a126218cdd51310c74a849886357544c431cbaa26218f1909310c72a8498863c5424c431c2a126218ea90a400c7528520063d13190031ca98a8018ea909400c75284a0063d13150031cd98a8018ec8c5400c73262a
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x59019811b0f8c00000880161700020d8e9589000b00181100000800002000001e9e07989200000000000d049a108b80001280000e0f1c80001787138601941d06830a80001c11949f000020801f9a8c9900001b9d80150000040016930080038982850000000a00000000040020e04080060c08602105800614084e04c94190032e04ca4150032e04c94150032a2580424c93194580514c931e05093190031e09093150031e05093150031a2580434cb21a4580434c621a2580434c92198580514c921a4580434c52198580524c521a1191324c521c1151324c521a85834348421a15924348421e050d2190021e090d2150021e050d2150021a1584424c93094584504c930a1588414c53092588504c530e050a414c030e0909414c030e0509414c030a1584434cb20a4584434c220a1584434c92098584504c920a158c41485209258c5048520a4584434c12098584524c120a2191324c120c2151324c120a85874348020a25924348020e050e4148020e090d4148020e050d4148020a1588434c710a158c4248710a2588434c210a258c4248210a1588434c51098588504c510a158c42485109458c5048510a2588434c11098588514c110a4191314c110c4151314c110a258c42481109458c5148110a81912148110c81512148110a858b4344010a45924344010a458f4244010a85924244010e050e4244010e090d4244010e050d4244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*4) 4
  | 5 => packedAt s4K5 (i*15) 15
  | 4 => packedAt s4K4 (i*26) 26
  | 3 => packedAt s4K3 (i*37) 37
  | 2 => packedAt s4K2 (i*48) 48
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (5+((h/1+packedAt s4K6 (4+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (408+((h/8+packedAt s4K5 (360+(h % 8)*6) 6) % 37)*6) 6
  | 4 => packedAt s4K4 (8752+((h/100+packedAt s4K4 (7852+(h % 100)*9) 9) % 399)*10) 10
  | 3 => packedAt s4K3 (11160+((h/93+packedAt s4K3 (10323+(h % 93)*9) 9) % 335)*10) 10
  | 2 => packedAt s4K2 (3322+((h/22+packedAt s4K2 (3168+(h % 22)*7) 7) % 105)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffdfd273c777b0cf
  | 1 => 0xffffffffffffffffffffffffefe39cf87bd333
  | 2 => 0x77fc1f3f83ec3c
  | 3 => 0x7bffe03ffc0fc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffa0448401108045
  | 1 => 0x10882108210112
  | 2 => 0x9014052020428
  | 3 => 0x6000aa4400a80
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 15 s4Pos s4Neg, 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_27821
namespace PEqualNP.Outside.L_meta_27821
open PEqualNP.Outside.L_meta_27821.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x547004c8c48038bd3862ead0005404f1d58b8d05049110c4a00c96003d42100b4594101c51f364c0105260904063488000186745013c8d0000400030dcff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa617c514c37e82986f50530ef98a61dd314c37e80986f50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6186fd0c30dea18617e520c3dca4185b94830bea9061ed520c2daa4186f90830de210617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea08617e500c37e80186f50030ef98061fa300c3ba60187e4c030ec980617f54c837ea9904fd5320bf2a6417d54c82f8a9906f153209e2a6417f53c82fca7905f54f20be29e41bf43c837a87906f90b20de21641ee32c83da65905f94720bea8e41bf41c837a83907bc8720f690e41bf40c837a81905fd5220bf2a441be548827ca9105f55220deaa4413d54882f8a9105fd4e20bf29c417d53882f8a7106fd0e20dea1c417d528837c85106f10a20bf28c417d518837e83106f50620bf28441bf40883f481106f50220fca0441b940883f461107e4c220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea6905f94d20bea9a417c534837e86906f50d20df21241bc42483dc64907b4c920bfa8a417c514837e82906f50520f790a41ed214837e80907e90120dea0241f9404837280907e8c120fc98241fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6106fd0c20dea18417e520837c84106f10820bf28841f651082eca2105f54420faa884175510837e82106f50420bf28041bf400837a80107bc8020fd10041ed20083f240105fd5310bf2a621be54c427ca9885f55310deaa6213d54c42f8a9885fd4f10bf29e217d53c42f8a7886fd0f10dea1e217f52c42fca5885f54b10be29621be42c437885886fd0710dea0e21f631c43ea63887d88710fa90e21bf40c437a81885fd5210bf2a421be548427ca9085f55210deaa4213d54842f8a9085fd4e10bf29c217d53842f8a7086fd0e10dea1c217f52842fca5085f54a10be29421be428437885085f54610dfa0c21bd41842fca1086fd0210dea0421fa30843f261087e88210fc90421f710843f621085fd5110bf2a221be544427ca8885f55110deaa2213d54442f8a8885fd4d10bf29a217d53442f8a6886fd0d10dea1a217f52442fca4885f54910be29221be424437884886fd0510dea0a21f631443ea62887d88510fa90a21bf404437a80887e8c110fc98221fa20443f240887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be29821bf430437a86085fd4810bf29021ee52042dca4085f54810f6a90216d52042f8a4086f90810de210217e510437e82086f50410bf28021bf400437a80087dc4010fd08021f510043f220087c44010
  | 1 => 0xc54c8778a990cf15321bfa9e437e53c86faa790df14f21dfa1e43bd43c877c8590ef10b21f719643ed32c877e8390ef50721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c538877e8710ef50e21bea9443be42887788510df94621dfa0c43f6418877a8310fd50621daa0c43f631887ea6310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21bf29a437d53486f8a690efd0d21dea1a43be42487788490fb8c921f699243bf41487ec8290ef50521faa0a43b541487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21dfa1843bd43086fca410ef90821de210437e510877e8210ef50421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40dfa1e81be43d037a87a06f10f40bf296817d52d037e85a06f90b40dea1681bc42d02fca3a05f54740dfa0e81be41d037a83a06f10740dfa9e81be53d037aa7a04f54f40de29e81bf52d037ca5a04f94b40dea9681bc52d037e65a06f8cb40de99681bc32d037ea3a06f94740dea8e813d51d0378a3a06fcc740df18e81bd31d037863a06fc8740df10e81bd21d037843a05f552409eaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c535037e86a06f90d40dea1a81bc43502fea4a05f14940dfa1281be425037a84a06f10940bfa8a817c515037e82a06f90540dea0a81bc41503f680a06f90140dfa9a813f535037ca6a06f54d40de29a81bf525037ca4a06f54940de292813c525037e64a06f8c940de99281bc325037ea2a04fd4540df28a81bd5150378a2a06fcc540df18a81bd315037862a06fc8540df10a81bd215037842a06fd4140dda82817e541027ca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330dfa1e61bd43cc2fca5985f54b30df21661bc42cc3be6598774cb30bf28e617d51cc37e83986f50730ef98e61dd31cc37e81986f50330bfaa4617e548c37ca9184f95230beaa461bd548c27aa9185f15230bea9c61bf438c37a87185f94a30bea9461be428c37885185f94630bea8c61bf418c37a83185f94230dfa0461bd408c3be61187ecc230bfaa2617e544c37ca8984f95130beaa261bd544c27aa8985f15130dfa1a61bd434c2fea4985f14930df21261bc424c3be6498774c930bfa8
  | 2 => 0xb78a2216fd4042df28085ba5010b7aa0214f54042dca8085395010b78a0215fd5332bf2a665be54cca7ca9995f55332deaa6653d54ccaf8a9996fd0f32ef21e65bd43ccbba87996750f32df21665bc42ccafca3995f54732bf286657d50ccafea9196fd52329faa4657e548cafaa9195f15232de2a4653c548cafaa7196fd0e32dea1c657e528cb7c85196f10a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cb7e86997790d32dea1a65dd434cb3a86996f90932de21265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca4196f90832de21065df320cbdc6419774c832f6990657e510cbeca2195d94432bea8865f5510caeaa2195f94032fd280657a500cafaa0197e54032bca80657e53d06faa7a0efd0f41df21e83bd43d077887a0df94b41bea9683bf42d077c85a0ef50b41de216837e50d06faa1a0efd4f41df29e83bd53d067aa7a0ef14f41dfa9683be52d067ca5a0ef54b41de29683bf32d077c65a0ef4cb41de19683bf50d077ca1a0ef543419ea8683bc50d06faa920cf55241bf29c837d539077e8720ef50e41bf294837d529077c8520ef10a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41df21a83bd435077886a0dfd4941be29283bf425077c84a0ef50941de21283f7415077c82a0dfd4141be28283bf535067ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc5250678a4a0efcc941df19283bd325077864a0efd4541dba8a83bf505067ea0a0ef94141dea8283bc50506fca820cf95041bf298837d531077e8620ef50c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998efd0f31dea1e637e52cc6faa598ef90b31de21663df32cc7ba6598efd0731dea0e637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31dfa1c63bd438c6fca518df54a31df21463bc428c6fca318efd0631dea0c63df318c7ee6318df94231bea84637f544c6fca898ef951319f2a2637d544c77aa898cf55131be2a263bf434c77a8698dfd4931be29263be424c7788498f7cc931ee99263bf414c77a8298fdcc531ef18a637f504c6f8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31dfa1863bd430c6fca418fb94831b7290637d520c7daa418db54831df21063bc420c6fca218efd0431dea0863df310c7ec6218f74c431fa98863d5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa643bf54c867ea990df95321beaa6437
  | 3 => 0x40460000003a0020000300100201009804002000010010000001400b0040000500a03200802007006000000060040081900001400016804000000098010020480000500001815801008004040080000200180000a02801835036090048010020140180b060004008150120080a0210000540004a002008000070000000002400a010030030040000f0040180e00800000000000817004000060000000400002100000007819004000098780220280200000c0180480901805c0000208602c0301f018030008090300080c001000040080050000242800800812c03801004034040020080400780900003c0380000600000007000000018380060000000000403c0381200003405003006004018820100400280400000001800006048010010000000002703e000340050020140080d0180282080601a0741b00e036030000410a20000000b01a03c05002000010000010060380000001c00000803050074020010020040100a00e098088090020cc06801002004000120000100504c050178008150020a0000010a80040000300202400011004024020020001300002801e098038090280742b01b0020240300f00000822806052030000000140100681400e0480b80100e00400807000004020060080001f802034002fca5a1df54b43bf28e877d51d0efca1a1df54343dfa9687be52d0e7ca5a1ef54b43de29687bf51d0f7ca3a1ef547439ea8e87bc51d0f7ea1a1ef94343dea86873d50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa9287be5250f7aa4a1ef149439e29287bf5150e7ea2a1ef94543dea8a87bc5150f7ea0a1cfd4143df28287bd5050f78a0a1df950439f2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216fd0e42df21c85bd4390b7887215f94a42dfa1485ef4290afca3215f54642bf284857d5090b7ea7216f94e42dea9c853d5390b78a7214f94a42dfa8c85be5190b7aa3214f54642de28c85bf5090b7ca1216f542429ea8485bc5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6216fd0c42df21885bd4310b7886215f94842dfa1085ee4210b7a84217b50842bf28885f65110aeca2215f54442faa8885755110afca0217e94042bd280857d5010bf2a0215e54042dfa9885be5310b3ca6216f54c429ea98859d5310a3aa6216f14c42df290853e5210b5ca4216fd4442df28885b65110b7aa2214f54442daa888535511
  | 4 => 0xf00980003c445e4f20007040002ec0001cc2f609a49a6b658800019a00064a5700001d21223760000003ea3f47341c873a00053a1fc0003ac09200000000007213a0000001284aa2d062e0000ce0be6203700485b80ca20227657450662872847a4f41a043c00056c53474a40039811e2500003365d40007a24625261c45de00046065400062600036076811a7d63907b00d25380000004765f456417c27200000238a0ea1f00000007b800007450278600054472600000059e0004ca0002b65e045c6500004846000007c65a40006c857a0006e67aa7086765405d27a03c83ec0c661a37279e2325aa2ee06a2d424833058a1de79820c00019600040e36678a09600000021011c0b80220a47480fa03858634402e32a09462206828035461e3142145fc08077a4b68001ea2ac5a80000187c400e15871800024429c7b228a82414200075000081a33c35631c5821e000000000008e00000c79443e5843087144c00040267fe15e1a21b62b03fe56e1041900002a826c84200000000007c0007a60ec10e40a18600027c0007204a88027ca3b282008c0ee00042c08a0c04f00000000f64e60006525680001f400039c0006664da0000000000000000000000000000004a200000000000000000000000000078c4b20002ca00000023c0000442785083fa00039200000038263240825e62c5204d82ea54869800066e7746c276e7900003e22da33817e48c0b484e36c1f25ea2fc7dc0008140540004a47ea0004406f440c0000000565227bc00023600071a64621e1ae00008257204044e7448345a05bc73684815243050a03c6aa0b045005044835022a6d81607702cc0163683800d61e86f23da45a3528266d243817836e0bc02450049668e2e876a49479671009c10a53047e6d613044a5c411866a30048225234a5ca1d46d421c5044722426f05e80d801222e1b26685b45f82a41a613233e7d06722663fc4fc52a4bc4e03f268a5f00c827e59c5e600023e5d87327be4e867e85c6c046868c4986120e409e69a54e4e47f01a41c085a74e74267001c26253e48a06637c7924e20dc0b24b82540000c420a63c5ac7f45c22843dc6f65b25d66d04ce5be8460520d45ba7560782c884046a7ee67a65861041435a71e0005cc00065681e00000060a51e5da6cc6fe4ec1406140a85f600070e4cc0006187b45f200026a02012658e51c6ee59624a0007643e800056a2281460002de0001c64b06b22123584a659a0001b07060000001fa0003aa00019e0000283d00000005181e60000004027845785662746e464c4ba00039482a0002202c61760b60620002704f84ae0423c00006604103ba5c63a00001482641dc60c0004a019c3f82f07468541f632c16275c4585924060000900002e20002c23260260400200e036010000000800a00001e004000000
  | 5 => 0x2b42b235c0ae7e07b600070200086200047820e0000006ae3b480473063829a1447666482ae1006900000f200053c5a60000000e21aa00000072a0008183d225a3ae5b08165100000000000002d634007e1be85230c0fc64e25c3ee0e08503f60005c858c6bc1200000000008602a61ce4fa11215c00042462a82c4126e007030e2260d042072e1d001e68851a16c6e22d23884c62301946b034202c7540585943623461923b66ec4184545367f83744fe5982a21ca29618879a0a20100f86ac00881c24c1d616a37e3cc49c5dc7780343167828066de1bc4c230648662415a28e1e21741c28566427803343242687ce4ea05a56251427a21834c0003282c42e42043d62467247e62fa2900000006b43860000006a61103c61086dc00054a4565b618e3484d00003ce4642347c21843b04f65fa19833a4de6860ac7a841e6be2ba00068475e00079c00020000039a7f22bc01a60e7e429432e54200041644683a7580302dc00014c0004520000004c450c1806440007a44803180a000000012e1506a46ea00004e2a041a14e0001060007ac00000031038400063a39e2d874c3a20c22860ba1e400081200077e7167400000000000000005ec30a3be49e00034e2be4d600000042200069c6a255800000000000000071c8381027c849255661649000054c6640000006ce00000015470c84a1ec78e2081da2828224d47e863666214a32066c63e67c00007672200026082e84c12c8440cc00022c5ce5548361b881017000080e75a1a85524260066a86087da03e15625829804a2f441c44c16426e24e80a5906405327ba1165800000008321d85603bc63000010c5ee6a00004dc00000070a29e52c83c52e2e60f01fe0de6922fe00a5280aa48e3d804683e7ec43683044477c8582067fc7006c457655c68201455e5121f821a3a637837a4ac7ae2921ba6342380f416e85e24043242a0a647033203a31a12a6b80e661c5c05164884044c831e47c5a243446c05e5e21723e438c18a36a7f669428c0324b41ac3644282166046f87605241367c013857c69611438e0007fa46e04c43a0da0e84742c01ee2243126800007d42aa23a0605463c212455a5507386062887d27cc5ae5fe07a2e017a73e6ca3de06c4be73c65a6e867816880c7de6fc4422ce2b82f80880363e04d272c30413c3ca4ee2f20007527880006022561b47126fa2223968283e665e06413e6da50e7d83227e257e5e480865c3a818c6ba6c642e76208635e0000843a476c6743b806e13477205c0003025d018200002a0fe3d477616646669e3
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd544423c62551108fd85544433761551108fd81544433b60551108f993534423d64d4d108f992534423d6494d108f990534423d6414d109b988534426d6214d108fd97434423d65d0d108fd95434423d6550d10c7d4d434431c5350d108f993524423d64d49108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108fd96424423d6590910ad58642442b960909108fd94424423d6510910a758c42442b56110910ae58042442b960d0510aed814144274654c510d514d31442f0604c510cd55221442746548510cd55121442f06048510ad587404423f65501108f59540442b761501109e1953044358534c110bc18530443d1314c110ce55220442786548110ce55120442f06148110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f58e540423e62950108fd8d540423c62550108fd85540423d61550108fd81540423d60550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530423e6494c108f592530425d6594c10c7952530431d5494c10c7992530431d6494c10c7951530431d5454c10c7991530431d6454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423f65d0c108f597430431e53d0c10c754f43042b561d0c10ae583430423f6550c108f595430431e5350c10c754d430423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cbd92520432c6494810cbd0e520432d43948108fd91520423c6454810cb951520432d5454810d394d520434d5354810cbd91520432c6454810cbd0d520432d43548108f990520423d64148109798c520425d63148109b988520427661148109e980520423f65908108f596420431e5390810c754e420432e5290810cb54a420423f65108108f594420429d6310810c794c420431d5310810cb948420432d5210810ad58442042b960108108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d52504108f992500423d64940108f597400431e53d0010c754f400432e52d0010cb54b400423f6550010c794d400431d5350010cb949400432d5250010d554f100436552c40109e59610043595384010da54a10042f161840109dd9510043555344010d954910043b34044010ec501100427b6544010d654d10043695244010ecd0510043b14144010bcd9510043736544010ec99110043b16444010ec95110043b15444010dcd4d10043d25344010dc54d10043d15344010d454d10043b34344010ec50d10043735244010f894910043715244010f854910043615244010ec90910043b04244010
  | 1 => 0x83ab2150120ea48540482b9648c1209e19530482b9644c120d614d30483c9324c120aed9320483a940881209798f540825d63d50209d987540827561d50208f596540823d63950208f586540823f63550208fd85540823e64150209798c540825d63150209d984540827561150209e980540823e64d4c208f593530827661d4c209d587530823e6494c208f592530825d6594c20c7952530831d5494c20c7992530831d6494c20c7951530831d5454c20c7991530831d6454c208f990530823d6414c209798c530826e6214c209d98453082756114c209e980530823f65d0c208f597430831e53d0c20c754f430823f6550c208f595430831e5350c20c754d430823f65908208f596420831e5390820c754e42082b960908208fd94420823d6510820a758c420831e5310820c754c42082b56110820ae580420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083374394420cd50e51083364294420cd10a51083365454420cd55151083565354420d554d51083366454420cd59151083374354420cd50d51083364254420cd109510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd545410823e64940208f592500823d65d0020c794f400831d53d0020cd947400833551d00208fd95400831e5350020c754d40083365150020cd545400833a5050020d354f200836551c8020ce55220083595388020dc546200826f6548020d354d20083655148020ead01200827b6548020ce55120083595348020ea109200837151480208f58e54c423e62953108fd8d54c423c62553108f99353c423d64d4f108f99253c423d6494f108f99053c423d6414f109b98853c426d6214f108fd9743c423d65d0f10ae58343c423f6550f108f59543c423e64d4b108f59352c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c423f6590b108f59642c42b56190b108fd9442c423d6510b10a758c42c42b56110b10ae58042c4354534c710cd55221c43355448710ad58740c42b761503108f58e548423e62952108fd8d548423c62552108f993538423d64d4e108f992538423d6494e108f990538423d6414e109b988538426d6214e108fd97438423d65d0e10ad587438423f6550e108f595438423e64d4a108f593528423f6454a108f191528423e6414a108f590528425e6314a109758c528423f6590a108f59642842b96090a108fd94428423d6510a10a758c42842b56110a10ae58042842b960d0610aed814184358534c210ce552208433954482109798e544425d6395110a758e544431e63951108f58e544431d63951108758e544423e62951108f586544433561951108f582544433960951108fd8
  | 2 => 0x5454430d9949510c3655254430cd991510c3356454430cdd0d510c3354354430cd909510c33442544308fd97410c23d65d0430a758f410c32e52d0430cb54b410c33651d0430cd547410c2b960d04308fd95410c23d6550430cb949410c32d5250430cd945410c33551504308f992500c23d64940308f597400c32e52d0030cb54b400c33651d0030cd547400c23f6550030cb949400c32d5250030cd945400c3355150030d354b300c35551cc030b658e300c369528c030dc546300c25f654c030d3549300c355514c030e6d01300c399404c0309ed95300c39b434c030e650d300c369524c030dc545300c2db654c030d6d95300c39a644c030e6591300c39a544c030e6551300c3ca524c030d6549300c3c9524c030d2549300c39a424c030e6109300c3d2514c030d6545300c3d1514c030d4545300c39b414c030e6505300c23d63d5320cb98b54c823d61d5320ce58354c825e63153209758c54c827661153209d58454c829d6315320ad58454c831e63153208f58c54c831d63153208758c54c832e6215320cd98454c823d6115320cd58454c82356115320ce58054c823e6494f208f59253c823f6454f208f19153c823e6414f208f59053c82766114f209d58453c823e65d0f208f19743c823e6550f208f19543c831e5350f20c754d43c82b96090b20a758c42c82b56110b20ae58042c838d434cb208f99251c823d64947208fd9151c823c64547208f99741c823c6550720cd94541c83355150720e950521c82ae62d0320ab18940c823d63952208f586548833a60952208fd8d548823f61552208f993538823d64d4e208f992538823d6494e208f990538823d6414e209d98453882756114e208fd97438823d65d0e20ae583438823f6550e208f595438829d6310a20ad58442882b96010a208f992518823d64946208fd97418823d65d0620ae583418823f65506208f595418833a5450220aed95408833b6550220aed8d40882b86250220aed8540882b9648c220ae5913088358534c220aed93208823d63d51208f587544823e64951208f994544823d63151208f988544823c62151208f584544833960151208f992534823d6494d208fd91534823c6454d209dd8553482746154d208f990534823d6414d209d98453482756114d208f997434823c65d0d20ae583434823e6550d208f195434823e65909208f994424829d6310920ad584424826c654c920e350d324823e64145208f590514825e63145209758c514823e65d05208f19741482b960d05208f995414823c6550520e9505214823e65d0120ab98b40482b96490120ce152404823c6550120ab18940482786550120ba189404833b6550120ae195404833865501208e19540482bb6350120ead8940482b86250120ea18940482a86250120ea8c940483a93250120aed85404
  | 3 => 0x9408f997325023d65cc9408f19632502ba608c940ae582325023f654c9408f195325023e650c9408f59432502b6610c940ad58432502ba600c940ae580325023d63d45408f98b51502b96094540aed81515023e65cc5408f597315023e658c5408f596315023e654c540aed8131502b8604c5408f994315023d650c540ab98831502ad620c540e54c431502ba600c540ae580315023c65c8540ae98321502b960c85408f996215023d65885408fd95215023c65485408f994215023d6508540a798c215029d6308540ae98021502b96008540ae58b505031d53d0c408fd95431023d6590840a758c421032e5210840ad58442102b96010840cd547411023f65504408fd95401027b6550040ce951401023e62953308f58654cc23c62553308fd8554cc23f6454b308f19152cc23f6590b308f59642cc29d6390b308fd9442cc23d6510b30a758c42cc2b56110b30ae58042cc31d54ccb30c755132cc23e64947308f59251cc23f65d07308f59741cc2b960d07308fd9541cc23d6550730a758f40cc29f63503308f98a548c23d61952308f189548c23f6155230ae583438c2bb6050e308fd91528c23c6454a308fd96428c23d6590a30ae582428c23f6510a308f594428c29d6310a30ad584428c2b96010a308f992518c23d64946308fd97418c23d65d0630a758f418c23f65506308f595418c27661951309d586544c2b561951308f58e544c31d63951308f98a544c33661951308f586544c33561951308d586544c23d6095130ce582544c23f6355130c7d8d544c23c62551308fd85544c23f6055130ced81544c2b960d0d30aed81434c23e64d49308f593524c23e64149308f590524c27661149309d584524c23d6590930a758e424c2b960909308f594424c29d6310930ad584424c2b96010930c7553324c31d544c930b6181324c23e64d45308f593514c23e64145308f590514c26e62145309b588514c23d65d05308fd95414c3375150530cd145414c354514c530b6181314c29d63d01308fd95404c23d6550130a7d8d404c26e62d50309b58b540c27661d50309d587540c23d65950308f98a540c23d61950308fd8d540c23d63550308f189540c23f61550308f990540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23d65d0c308fd95430c32e5494830cb552520c32f6494830cb192520c32f4394830cb50e520c23f64548308f191520c32e5454830cb551520c32f6454830cb191520c32f4354830cb50d520c23f65908308f596420c32e5290830cb54a420c23f65108308f594420c29d6310830cb948420c32d5210830ad584420c2b960108308f992510c23d6494430cd952510c3355494430d994a510c3655294430cd992510c3356494430cdd0e510c3354394430cd90a510c3344294430cd951510c335
  | 4 => 0x798f540865d63d50219e983540867960d50218f596540863d63950218f582540863f63550218fd81540863e64150219798c540865d63150219d984540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f430863f6550c218f595430871e5350c21c754d430863f65908218f596420871e5390821c754e42086b561908218fd94420863d6510821a758c420871e5310821c754c42086b56110821ae580420863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d41087365150421d354f21087355488421d554e210866f6548421d354d21087a741484219dd9521087355448421d554d21087a442484218f992500863d6494021ce95250087395494021d694e50087595394021ce99250087396494021ced0e50087394394021ce90a50087384294021ced0650087394194021ce95150087395454021d694d50087595354021ce99150087396454021ced0d50087394354021ce90950087384254021ced0550087394154021dac8550087722154021da48550087712154021c754f43d029e6310b40a758c42d032e5210b40ad98442d02b56110b40cd54741d02b661d4f40ad58753d02b960d4f408f18953d023f6154f40ae58053d02b960d4b408f58e52d023d6194b40a798c52d029d6314b40ad98452d02b56114b40ae58052d023e65ccb408f59732d031d53ccb408fd9632d023f654cb408f19532d031d534cb408f99432d023d650cb40ad98432d02b5610cb40ae98032d02b9600cb40a798f51d029d63d4740ae58351d023f63547408f18951d02b960147408f99731d023d65cc740cd54731d023e658c7408f59631d031d538c7408f59531d023e650c7408f59431d031d530c740ab98831d02ad620c740cd54431d0395310c740ae98031d02b9600c7408fd9721d023e65887408f59621d033551887408fd9521d023c6548740cd54521d023e65087408f59421d029e6308740a758c21d02ba6008740ae58021d031d5350e40cb94a429029d6310a40ad58442902b96010a40cd545419031f5350d408f994435025e63149409758c525027661149409d584525023e65d0940cb14a42502ba6090940a798c425029d6310940ad98442502b56110940ae980425033751505408f994415023e62d4d408f58753502b96094d40aed8153502b96094940aed81525029e6314940a758c52502b66114940ad584525031e63149408f58c525031d63149408758c525033661149408f584525033561149408d58452503396014
  | 5 => 0x520c72f4354831cb50d520c63f65908318f596420c72e5290831cb54a420c63f65108318f594420c69d6310831cb948420c72d5210831ad584420c6b960108318f992510c63d64944318f597410c72e52d0431cb54b410c63f6550431cb949410c72d5250431d354b310c6d5638c431d954a310c65f654c431d3549310c797414c431e5505310c677654c431e5d0d310c795434c431d9549310c6d7654c431d5d95310c796644c431e5591310c796544c431e5551310c7c6524c431d5549310c7c5524c431d1549310c796424c431e5109310c63e64940318f592500c73a5494031ce552500c76a5294031da54a500c7d13194031ce992500c7396494031ced0e500c7394394031ce90a500c7384294031ced06500c7394194031d54c5500c73a5454031ce551500c76a5254031da549500c7d13154031ce991500c7396454031ced0d500c7394354031ce909500c7384254031ced05500c7394154031d6cc5500c7723154031d64c5500c7713154031d44c5500c63d63d5321cb98b54c873561d53218f58354c865e63153219758c54c867a60153219e58054c869d6315321ae58054c871e63153218f58c54c871d63153218758c54c872e6215321cd58454c873a60153218f58054c873960153218e58054c863e6494f218f59253c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c863e65d0f218f19743c863e6550f218f19543c871e5350f21c754d43c86b56190b21a758c42c86b56110b21ae58042c878d434cb21ab98b41c86ac62507218f99250c863d64943218fd9150c863c64543218f58e548873661952218f582548863f63552218fd81548863e64d4e218f593538863e6494e218f592538863e6414e218f590538867a6014e219e580538863f65d0e218f59743886b561d0e218fd95438863d6550e21a758c42886b56110a21ae58042887365450621add9541887376550621add8d41886b46250621add8141886b5648c621ad5913188754534c621add93218863e64942218f592508863d63d51218f583544863e64951218f994544863d6315121cd584544863d60151218f992534863d6494d218fd91534863c6454d219ed8153486786054d218f990534863d6414d219e98053486796014d218f997434863c65d0d21ad587434863e6550d218f195434863e65909218f994424869d6310921ae580424866c654c921e350d324863e65d0521ab98b41486b56490521cd152414863c6550521ab18941486746550521b918941487376550521ad195414873465505218d19541486b76350521e9d8941486b46250521e918941486a46250521e98c941487a53250521add8141486b5648c5219d19531486b5644c521d514d31487c5324c521add9321487a541885218f990504863d64141219798c504865d63141219
  | 6 => 0xb693254032c754f43d069e6310b41a758c42d072e5210b41ae98042d06b96010b41ad58753d06ba60d4f41ae58353d063c6254f418fd8153d06b56114f41ad58752d063d6394b418f58252d069e6314b41a758c52d06b56114b41ae98052d06b96014b418f99732d063d65ccb41c754f32d063f658cb418fd9532d063c654cb41c754d32d063e650cb418f59432d06b6610cb41ad58432d06ba600cb41ae58032d069e63d4341a758f50d063f63543418f18950d071d5350e41cb94a429069d6310a41ad58442906b96010a41c7d4d435063e6510d419798c525065d63149419e980525067960149418f997425072c5290941ad986425069e6310941a758c42506b66110941ae98042506b960109418f98b535063d60d4d41ad58653506b76154d41ad58652506b76154941a798c525069d6314941ae98052506b96014941c798c525063d6314941c758c525061d6314941cd584525073a60149418f580525073960149418e580525063e65cc9418f597325063c658c941ad98632506b5618c9418fd95325063c654c9418f994325063d650c941ad98432506b5610c941ae98032506b9600c941ad58b515063d63d41418f98b505071d53d0c418fd95431063d6590841a758c421072e5210841ad58442106b960108418fd9541106776550441cd951411063e62953318f58254cc63c62553318fd8154cc63f6454b318f19152cc63f6590b318f59642cc69d6390b318fd9442cc63d6510b31a758c42cc6b56110b31ae58042cc71d54ccb31c755132cc69d63d0731a7d8d41cc63e64943318f59250cc63e62952318f582548c63c62552318fd81548c6b561d0e31add85438c63f6454a318f191528c63f6590a318f596428c6b56190a318fd94428c63d6510a31a758c428c6b56110a31ae580428c63e64942318f592508c67a60951319e582544c6b960951318f58e544c71d63951318f98a544c63d6195131cd586544c73a60951318f582544c73960951318e582544c63f6355131c7d8d544c63c62551318fd85544c73761551318fd81544c6b561d0d31add85434c63e64d49318f593524c63e64149318f590524c67a60149319e580524c63d6590931a758e424c6b561909318f594424c69d6310931ad584424c6b96010931c7553324c71d544c931b5185324c69d63d05318fd95414c63d6550531a7d8d414c63e64d41318f593504c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f98a540c63d60950318f189540c63f60550318f990540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c318fd95430c72e5494831cb552520c72f6494831cb192520c72f4394831cb50e520c63f64548318f191520c72e5454831cb551520c72f6454831cb191
  | 7 => 0x194042c794d5010b1d5354042cd9455010b3551540428fd8d5010a3f6154042ced955010b3b5354042ce94d5010b9a5354042c694d5010b395354042e654d5010b195354042ce14d5010b3a5254042ea9495010b3b5154042ce9455010bb25154042cc9455010b395154042ec5455010b315154042ce1455010b3b6354042ce98d5010b396354042ce18d5010b3a6254042ced855010b3a6154042ce5855010b386154042a798c5010a9d6314042c754c5010ab66114042ad5845010b355114042ae9805010b395014042c798e54cca3d61953328f58254cca3f61553328fd8154ccb1e5450f32a7d9543ccb1f6550f32a718943cca9f6150f32a7d8143cca9d6310b32ad58442ccab96010b328f99251cca3d64947328f99250cca3d6494332c758f548cb2e62d52328f587548ca3d60d52329d984548ca7561152329e980548ca796015232ad584548cab96015232c758c548cb2e6215232cd984548ca3d6115232cd584548ca356115232ce980548ca3d6015232ce580548ca396015232ab98b438caac6250e32a758e428ca9d6310a32ad584428cab96010a32c7d53328ca3e64946328f592518ca3f64546328f191518ca3e64942328f592508ca3f64542328f191508ca3d61d51328f583544ca3e64951328f994544cb1d63151328f584544ca3d60151328f997434caae62d0d32a7592434cb1c5490d328f195434caac6250d3297195434cacc6250d32c7d95434cb1c6550d3287195434cb8f6250d32a7189434cb8c6250d32a3189434ca9f6150d32a7d81434ca3e65909328f994424ca9d6310932ad584424cab96010932e350f324ca9f648c9328f990514ca3d64145329e980514ca7960145328f990504ca3d64141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540ca3d61950328f582540ca3f61550328fd81540ca3e64150329798c540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca3d65d0c328fd95430cb1e5350c328fd96420ca3d6590832a758e420ca3f65108328f594420ca9d6310832ad584420cab96010832c7553320ca5f654c832c7551320cb8c424c8329bd95320cb8f434c8328f992510ca3d6494432cd952510cb355494432cd992510cb356494432cdd0e510cb354394432cd90a510cb344294432cd951510cb355454432cd991510cb356454432cdd0d510cb354354432cd909510cb344254432d5cc9510cb663254432d54c9510cb6532544328f992500ca3d6494032ce952500cb395494032dc946500cb715194032ce992500cb396494032ced0e500cb394394032ce90a500cb384294032ce951500cb395454032dc945500cb715154032ce991500cb396454032ced0d500cb394354032ce909500cb384254032d6cc9500cb6a3254032d64c9500c
  | 8 => 0x600900500500000800e00500b0010e100500100300b00700903e01c00b00001200800700700000500e00000f0030078f58652d0e3d6094b43ad98452d0eb56114b43ae98052d0eb96014b43ae98351d0eb960d47438f18951d0e3f6054743ad98750d0eb561d43438f18950d0e3f61543439d9845250e7561149439e9805250e796014943a758b5350eb66114943ad5845250eba6014943ae5805250f3661149438f5845250f3561149438d5845250f3a60149438f5805250f3960149438e5805250e3e62d45438f5835150e3e62d41438f5875050e3f6550c4397d954310f1e5450c43c754f43d0b1e5350e42c754d4390aae62d4e42c7d4e5390a3f6154e428fd815390aae6214e42ad9845390ab56114e42ae9805390ab96014e42cdd465190a3f63546428fd815190a9e6314642a758c5190aba6014642ae5805190b3b50942428fd8d5090a3f6154242a798c5090a9d6314242ad9845090ab561142428f9974350b1f5350d42c79915310b1d53d0c428f5964310b1d5390c42c794d4310b1d5310c42c754f4210a3f6550842c754d4210a6f6550842d594e5110b555394442cdd0e5110b354394442d594d5110b555354442cd9915110b374354442cd90d5110b354354442cd10d5110b374254442cd5095110b5a5394042d654e5010b725194042dc5465010b3b4394042ce50e5010b5a5354042d654d5010b725154042dc5455010b3a6454042ced0d5010b3a4354042ce50d5010b384354042ced095010b394254042ab98b5310ab661d4c42ad5875310aba60d4c42ae5835310a9d6594c428fd855310a3f6054c42c7d955310b1e6254c42c71895310b1f6154c42c79855310b1d6154c42c71855310b1f6054c42c79815310b1d6054c42c71815310a9e6314c42c754c5310aae6214c42ad9845310ab56114c42ae9805310ab96014c42c794e5210b1d5394842cb98a5210b8e5394842e354e5210a9e63d4442a758f5110b1e53d4442c754f5110aba60d4442ae5835110b1d5394442ad5965110b375394442e594e5110b355394442e554e5110b155394442cd94a5110ba65294442c794d5110b1d53544428fd8d5110a3f6054442cdd955110b375354442cd94d5110b965354442c594d5110b355354442e554d5110b155354442cd14d5110b365254442e99495110b376354442cd98d5110b356354442cd18d5110b366254442cdd815110b366054442cd5815110b346054442a798c5110a9d6314442c754c5110ab66114442cd5445110aba6014442ae5805110a9e63d4042a758f5010b1e53d4042c754f5010ab661d4042ad5875010b3651d4042cd5475010b1d5394042cd5465010ab96594042ced4e5010b9a5394042ce54e5010b995394042c654e5010b3a5294042ea94a5010b3b5194042ec9465010b395194042ec5465010b315
  | 9 => 0xcba3482a4eda29670234ec9ad48a6a13e5f214c7baccaac4d8cdc44a4692d6e4089faa46000ac292a1f0e16d84330d86368486074e40bf00886520001704decda754000b58000000dee23a2e00000009580000006ba000de80003c44663a2000c34e4224a4583a85b858278800700200300800700100600200100705100001004000000200c00301100100400b00d00000500100100200a01300800000500701300400101000500c00800000100c00303700100002800f00702e00300000100302f00500b00300000500300000200100100300600600000700000601b00400900a00100200900d00000100100000300000200000900000200c03d00b00002d00404003200200300900100e00901600600400000400100000102100601001803b00600100000e00300000a00700402200101300300800700700000000200002200300c00c00005601600100000000000e00101500301b00400200000c00200200800300302400002701301300b00302f00001100100000100a00200200500101700900300300201000c02400000102b00100200301300000002500200000000400b00300000f00d00400a00000600e00000100902500001200001802300300300100100102a00b00000000200200100100100100100300300300600100800400400100400000f00302800000700500c00000d00902000700200000300000201800200100900a00400800000900000401e00200500200a00100f00d00100103500200300600000000100200000b00100501500b00000e00900000800000900000400600000300000800100400500001200000100b00c00c02b00200000700300100102100000200400000100000e00000000a00502b00000000101600600300b00e02f00400900003300b00e00003f01b00e00700a00e00000000c00000900000c00f00900800600000400200100300400000001f00400500700100400b00301000900300000400100b00500c02600101202300000100900000000000900000d00300000000100004200300000600200100301300001300001900000600100000f00100700800000100100000100000000600900100400000800b00201000000900000003301300300200201c00800e00300000100501700201200100400400300400400100900900000000300100200101000f00400600000e00001300000600000000100a00500102600201500300200b00701001b00100201102800000000000000900600800a00c00900000400100701a00300900600202201a00401300700700200700000300300000601001400200000002300000800401401900000f01e00400000000000100300000b00000901b00001100200000301100000d00001000300000500000200600500f00204400303b02700000b00000000102000600100
  | 10 => 0x824da13007071848e000b6880ae0c244c101a09747783dea3cb38554aca51215857247c97c846c14aa4000e540000005ae0008640005920000946fe20e000566eea6b24f663626a98e22006e000c9418a00034494a9f000012e000db47c2000714480ba430cc6e45c3802e6b940cc2c89f49220000928ea8bc996000a3600000000033e00030438a7e4648a86334a7803ed5661200091400000054276446c7e28085e0a1060a4d470686671202c980976c2e84c000e2064a1785460004ac42600000051e0000005f8b9804803097200016e0000ae0009821bae26dfaae00000004f8000728ce835481ce2400000039c000654858ae431c0acbc49b08f43d60000000003be9b2a505802f4cf000081a000bc03e0602a90732b7c000bc6000516e9a0000009a611c0009c66668e4000d2a234b288e242e0007e87820ee6f80000005d6c50028c8ae5c2a270a43c906be200007cab800058e8aed047d41049327ce99284889c0006c448889a4e6b70c0e00000012a45017ec0000028063e1c2a1c3325249d80003c000023836460edd0a28526000c3a23c5849ee4e03ccd742609d49cebf821e404e3c8f081e2ecb4468c6e2576a4246edba66cb8cde00007800009eae28138000d1cd92bbc3c88188ca83e7a2e1a0000000005689fc5f6ac68ba64217cd4461e62cb50cb064e51c204454c28cfedce66a55ac9c8d0316b0e3e2d1259eb52c98af65a6420000ca8704da28f8ee832c836606950cf47bc0006be28eb342c23c26b4c56108cbe0004ca0b0b3c00084a6dee4ce2e00000017418cbba6689541540001820e6920000b9ce125184e45c0ec0472af4eac8c4000c5aae243a86c49ed80cbcaaa24253a7da26269c47672e00097867e0000004ecbb6000cde68622eee6ae8a7e4a8ad44c280073e0b2aec4be51ae062fc11238c5600008a612ccc2156ad624ee08a1e956000020af292eab60f65306ae000000000000352b9a000000abe0000003060002d655e310bdc510b0a3a0d3c7feafa378bf6d6074ed2e1ec13cc72066e84e62440c662580006bc70021c86011a5ec9a0c4ea4e61ae6438e0646a098c35ec36cc4baa0ecda8d6a0006e088a792826a3047ed720002caacca0889400091c0000008c6c46050d7c000000af80001ea41ea56d5ebd42e2ee05aca06d002aa7dcee27604a626c95c0001b2bca0463f206a202dd20005744bc90024677ee7c690198aae86adda69ee56084b2e0d6d7a3f67729beb1044af06284eb65902b68804901fe2089c04c0b3a7b2000e8c9e0000000362000326e1c24041420ab6ea0a34027aa6259c8f25eebd8000136e74c429e89b8c12122dc2c2c9160000005f4210000000b600000000000009ca000000bd20003ead9e74c7b41e29a458a1aa0001a4000000640000d3a7b0000000ad2b782eede6b4c56e68a
  | 11 => 0x80d8646b063ec68832239eb882be9ac2b27f4b00e7e5320ce4ce8a2058d288c03f006c0380140561a645aaa8698c749b68da0004ae00000032e8de000c38540000924b9e1c4bcef08d4cd8a78c41c60c4c8b5e0008e8844e38cdca022a6000000b92852c644520001fa2dcdec0000005aa0000009e40002acb08e6699ed4a0003926708ce0000e0b96e9ee0a1c6a80912c884242f62566760bc7a852ea2ee46000df4d880000001a83a68ec0debb496a9aadead6665ce8e5e624c26456a9600002b087a842db0a4a07a00018e000e6c000ec200057a62ac580000000006b8c187aa49400000000079425e5f0628000000000edeaa61864fccb6376a48a923b2890ba067237ee808dc770b2c4cc740afc08617ab8069ab0c2907ded96970c767f8b8a83a72a2887e63d4c70a68da4d647a6412e3009a3201cc3600f0302e92d58b76e6ed5c01cec8ebef0cb4e528eb2e00d1e994a7696605e1d8dca83837227c1e0d784b6b04c60eb816820cd109f607680685ada090a8aac48d2401649cc160405226949309ecb18cace8a92600842204ea0c6786d076e49a5dcb6c9ae79cb6a6f69521c802ed308cc04c01e2b448c73a266c7ce8833670ee4441aa004823da80eaee6c0068be00722ce2da3feb206b0dfe0a06e81508864b0eee882106b5aea8000ef6856cec6dcd1694840c00000052cadacea000a3846275a25c000a3e000e365963b481063cb5cc6cc4c19cb8e9187845a896e418c5c7aea146200783e44d02e83aa55c0a4e4a93cd4037c5b0d207f65b287e45e31e56289e42c38419a0828a0a32cc89088785d834c92ceba000e3205ccce080aa09d6e0e942766d7eb54000ed000012426ed2c1fce98252c1a9d257c00094e000cb443602a6eed0a00c498df2342dbe6802725706344b80dc3188b68c2632c02b74ca0eca0feed2a3a09c27ef02534ab4000a40bee00000012893eaea8acc441484f4000000eaab16a5c14419443899833ad5a4ee872e7206208ace45c42d274476aa2ac68a9ec84022f0473c77a2c64b40da7c06145d4d4ecee00000021a42ab1a3bc00000075c44c0000000005b6c4ac960d040edae1ac5ca000a2229a1007b677c6aae3a9cc4eabcc0f876cba8e18bda0003129bc02601a0363caf12052370006bf46647200000f273825414e000dc6e4e49203a11ead02ae9a8cf21f81ee7be4649e28149a25be4a296c1d0b483503945fa102514444660346618a2cb7ad8e824db832a6a8658a740fa6d82c46567264ba3ee03c000d9ab468d4e5edf0160a5e000556ea6000a96812a12180b24110cb8b621a2876caa000746ed60a6ba68021d600050ca6cf0e854ccc3fcd903087acb1c3b86c650680c6b68fe4aae78b3e9906acd08ef84f25941667220007a459a00028a67ae0489677415ccd299a934a26b147109443880f4a
  | 12 => 0x60400000082a91a054efc44e7e000000068e22a5209c40008c8c820e8a54ec4efa0006f2a640007561ce7cabfe4100a8d9c8620005cc5a26a28b25de5d090c898b4232837adaa90ee4843225084021817640a28c29e1b8c1cd6c7c68205ce3e84682148880000008a889200006072c3a4b72b30e0215ea16850828b22eced42ca61460ba000874d68c06a6e2a80b46e670c7ccd065fc0e400071a0be000bea7c8000e52a5a0000009babc8ebca7218858616a0443d871600097a41625a8e66ea216b122fa830548cae968ef471caf0e5abfa65a23674819e1200000001bef10b02132c8e3ace1e65ebd00002fed027fc1d400030091e09ea1a0008223fa83c00033c9de0008e08fc7581841f478ace0000cc6000a88164270a0e0003d010e90264c3c634a226eb4c625ba62e2980000008b06f4d266d67d00007b80003d20009360000009da3e60000000002c083422c00036a000bb8366804cfc83230e00e6380001b4dacc0aa449649e61161debaeabcc8095aacee6000023e13a222a8ed4615a46073039a1e65dac3262466254e7c4bc204a56c0000005c2552ad8644000e2c7422740004c40c2e7a7ec6a4bb230a5c8232000400500aa20000001b00c03f40008d6ed4790e96a18000396c1ebac36e87c000000b7e390282406dde4e20007088b471e7d8cf86cea94a9c00099c00257e82ea7c7ea0000007340000007d6d822d0a60000d0e000000000000000682db6000df8e22dc095ebec3b6b6423079610c79ade45a02b848a2d8538988c24bde07eae6938e502246c279ea70a341404fe9f214a4841d25640fc5887fa610be4114ce63f861cf000ea8fab40358724118a2431ac3c674a7a22803458c43ecb24a02cc0009fe7621620009d0ab02de75eade910000448a9a84eaba000c528a46a6ea21ca0007360004d80001dcd144424c688eb66c9e000000000ee400053ec7a6daa8c2769c2f0adbcef24d2cd6000b90dfc16ce94000b865b4e3e1f6000000000000000d708b86fcc86e9c50a946a666081ae004c2a000010904000db297e0000003b0aac000d942782ba776000000d326fa496afe0d46840c488c6cc00094cea4000402000b2a550e689b4d34a4c4dc0d2456df6bbeb82c22478ef0bfc1f254cd188d2c040005c6000000ecc6e45365fe5021e817200000029c000000b360c6986000000000000a9885e428126000d1ad226c8bb0d3600000066e000000d54dd682c598d76b84ea0000000000000ac00001bc0004d6000386c6ac262929840908be7eebf2a20000000024c92c5ede20000000005a494086e60000000085c000cfa0005eaa04870470e145e2e9033808e000c900000000000000000000000001c0000b56dd40000000003560e2dcc4e8e86dc82a0ba252a200e82000d3ec7e2125e876803215219646a1422d401850
  | 13 => 0xc80000000000001b64308f68ee7a00001e4e6a0aa1da00000010a7f254a0b8042eb067c000a52504b327986ecc3e4b2cf6c8c000d62000dd8578696be8ca44fa000750c0c0000a200078e000d3863a3144f07f0000000d52b1e0003cebd62942f02bc7520000002f2eaeefe0004746d474a0b6626cd4000ca22863823dc544a58e702e4000000000000a84ac8268d50000000e2a00098a9dc5bcc20928c4000036cddce582f8da6edc00047acc0e10cd06d209800000078653c0969f89c808c8845d20000caeec558000a8a374868434e76e34000616962ec6d0cbe6000000ab235c62235aadc206ce200081663050eb4a012b2665093a00032400000000013400024805a6ca2eac54000c788d800000ac086f04461901927d2cd85e4398ed83aed980003bac30
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x9048d7318940c8252b88c4a06410d5c765d0e2083ae7b2e8310499731894088258b88c4a0441545c4534c22083ae6310a890438755834348254392c1a1a41431d5434c920950e4b068290524755052148246b98c4a0241295c46250120992e631280904e171189404824cb98c4a02412c5c46250120b12e631280905a17118940482553a8c4a02418a9d46250120d14e631280904a9731894048344b98c4a0241225cc6250120d44e231280904a9711894048350b88c4a0241285c46250120950ed19280904a8764c940482543b642a02412a1d92150120950e4b246090438755913048254392c898241545c4534c120a90ea9926090689644c9304821dbaac1210418654d609082083ae7b28841041f7558c420820ebb4a621041075d9531082086eeab08841061653584420830aa9ac2210418694d6010820c32a6b0084104357610a510828ab9885288414c5c04294420a62e1212a210515731095108298b8084a88414a5d74048020e12a7a02401072151d012008294ba88490041625cc4248020e12a621240105a1711092008390212a290041075cc625531083ae7b2885885457214d31c4292392a890e21075cc625521083ae7b2885085497214d3084294392a8904218598d6195110c34c6b04a88841d73189544421ab8ecba1a210e5c365d0d10858e4b2a868850d7214d434420eb9cc9a922107dcd659091083ae7b28848843571d94424421cb86ca21221515c8534c5109c2e43026288434765512144292392a890a21345cc604851083ae7b2a80885497214d3044270b90c298221541d5314c110ca0ca98a6088438765512044294392a890221345cc6148110e42a890a408841d73189540430aa9ac3a18218654d60d0c10a1ae6324a40841d731915204286b98c8a9021495c74354810a52e1a1aa40841d73d94420421ab8aca210210e5c1651081083eeab18840841d7694c420420ebb2a6210218358e5210810c1ac6a90840861653584420430aa9ac221021899496110810c4aa4b08840861a53580420430ca9ac0210218a9496010810c52a4b00840871153d011004390a968088021c454d4044010e42a4a02200871153d051004390a968288021c454d4144010e42a4a0a20085317599110042c8b9cc8880214cdd56444010ac2e5a9a20085517594d10043892a2a688021c45515344010e24e8a9a20087117454d1004389322a688021c45915344010962eda1a200871153d0d1004388a9a8688021545cf5244010ac2eb29220087415394910043912a2a488021c85515244010e84a6a922008741535491004391ba2a488021c81d15244010e44c8a922008721645491004391a1aa488021c850d5244010a62eb2122008711539091004390a9484880212c5d84244010a62ea2122008591731091004388a988488021c85484244010
  | 1 => 0x3248646b98c4a0a432a5c0625052198ae63128290ce170189414864ab98c4a0a432c5c06250521b0ae63128290da17018941486533a8c4a0a43899d46250521d0ce63128290ca5731894148742b98c4a0a43215cc6250521d44e03128290ca5701894148750b80c4a0a43285c06250521948ed1928290ca4764c94148652392c918a430d1d5644c521948e4b226290d517014d31486a23aa6498a43a1591324c52186eeab0c8410e1553586420860eb9eca2104307dd5631082183aed2988410c1d7654c420870b29ac2210438554d6110821876eab008410e1a53580420870ca9ac021043495d74148421e0aa7a0a4210d257510921086c2b988490843c154c4248421b42e02124210c397610a500868cb9885280434c5c44294021a62e3212a010d19731095008698b8884a8043c8d052154021e408490aa010c357118953d021ab8ccb99681431c9534cb4083ae6312a3a060d5358831d0312b12a218e81455d5310c740d0ac498863a06195358031d0318a8ac018e81a44c5600c74083ae732c43a05247254521d030ab1cc2292818598d6114940c2ac6b08a4a061a63580525030cb1ac0292818c9856014940c62c2b00a4a0435711963250254b90c098a81a1589310c540d2262b0062a041d731972150306b1ca42108189949611084086ae2312a99843571d9442cc286392a8996610d5c4625523086ae3b28851861563986544c31930ac12a2610d5c4625513086ae3326a49843771596424c286392a899261345c4604c930a4ae428a829854572145314c264b90c098a610d5c46255030a4ae2324a41843571191520c292b88c8a90610d5c76510830c1ac7290841860d63548420c21bbaac221061899496110830c4aa4b08841862a52580420c314a92c0210610d5d84294430a2ae6214a2185317010a510c21abb084a8861455cc4254430a62e0212a21860d6354b410c30ab1aa3a08618a54960d0430c62a2b06821870952d01300c388a8e8098061c2549404c030e22a2a02601870b43549300c384a1aa498061c4d0d514c030e2286a8a601851975991300c2c8b8cc89806146dd5644c030e14a8a92601870954549300c385ba2a498061c21d1524c030e14c8a92601870964549300c28cbac8498061c254a424c030932ec212601851975109300c384a908498061645c4424c030e82a528a601871254545300c388aa2a298061d0949514c030e82a4a8a601871274545300c388ba2a298061c4991514c030e22c8a8a601871242545300c388212a298061265db414c030e12a5a0a601871151d05300c384a928298061c4545414c030c54c4b06a9906156398454c830b31ac22a6418558d6115320c34c6b00a9906196358054c831930ac02a6418c585601532086ae232e87904357119543c82863aa8699641075cc6550720a48eaa0a43
  | 2 => 0xc6a8085469cc6154042a32e630aa02152a721855010b18b08c2a808507dd95314042c2aa7308a021615535845010a1bbb2a2280858598d5114042c2ac6a88a021619539805010b18a8cc0280858698d5014042c32c6a80a021632615405010b18b0aa028085255c46250f32932e0312879960d6398b548cb0ab1cc22a4658558d6115232c32c7300a91963161980548cb0cb1ac02a4658c9856015232c62c2b00a9194a571189438ca54b80c4a1c65295c46250d32952e031286994c571189434ca64b80c4a1a65255c46250d32932e0312869958571189434cac4b80c4a1a65239d46250d32c1cea312869968671189434ca46b88c4a1a65a15c46250d3290ae2312869968a70189434ca46b80c4a1a65a25c06250d32912e0312869941f7558e420ca1bbaac2210650edd56010832a1aea212641958571109320cac4b808499065435d7434c83286aec214a2195157310a510ca98b808528865455ce4254432a2ae6212a21953170109510cb8221264a8865c1d0d3254432872ec214a0195197310a500ca98b888528065465ce4254032a32e6212a01953171109500cb8421264a8065c2d0d3254032872e0312a7a0c397099732d0686392a699683075cc6254341c2cc6b08a4a0e1563584525070cb1cc0292838c5866014941c34c6b00a4a0e19635805250718b0ac0292830e5c0658c941c1ac72908420e2a52580421061cb80c4aa6630e5c36510b31a18e4aa26598c3970189548c61cb86ca214638658e6095131c62c3304a898c3970189544c61cb84c9a92630edc16590931a18e4aa26498cd170185324c61cb80c4aa0634a5c06494831872e0322a418d2970191520c61cb86ca210638358e5210831c1ac6a908418e2652584420c712a92c2210630edd56010831c54a4b008418e2952580420c782a968298863c1549414c431e0e86a926218f0543549310c68abacc898863645c2644c431a2eeab226218f0654549310c782aa2a498863c1dd1524c431e08e8a926218f0664549310c782b22a498863455d6424c431e0aa52126218c9576109310c68aba88498863c1548424c431b22e02126218f41524c6500c61cbb08528063465cc4294031a62e2214a018f12544c5500c788aa262a8063d09493154031e82a498aa018c3976109500c68cb9884a80634c5c44254031e268298aa018f11414c5500c789a1a62a8063c450d3154031e24e898aa018f11744c5500c78932262a8063c45913154031e248498aa018f10424c5500c713312c3aa6438598d6115321c2ac6b08a990e196398054c8718b0cc02a6438698d6015321c32c6b00a990e316158054c861cb80cba1e430e5c06550f21a18eaa1a6590c8d7318941c8654b80c4a0e430e5c365d0e2192ae63128310cb17018941886a8b80a698c430d1d561d0d21948e4b0e8690d0c7550d
  | 3 => 0x4f2082c4358000000012511e0ba3d81b1cd0a40a5218c94508e48097d41a000fd1373be0000f9b70267c020000250000fb800278540a4000234000bc8cd0000001915a1fa4c1209e53ea6b8001e628e388c49b33d66991e90f0fa800621841fc7381d83e2a20e8b097011a6347d24944c06ce28001942dc330cc33c67c4e1c10001108b1920985d8ee22a2662ec529581d64185b05500e339010300004f90324401e1d01315227a4d82b9cf1f65cc5705a182000000790de000daa421b089cdf9e11e0588a58814206e0288000244086b8930446451a831050000001f209c384129ee44800000091116318560b210041472a2e418534a19f11c6570f7a3035216402866000000480200004008020280e01808010040083600000000120280c00000008080200a0686a0000a00800008440000e00000000081001e0a850038000080009054000040080e018080f0201886a04816008000201a0301e038c208800000060082a09024138120087001000000020f00e00000000520c01e0000a018be008001389c0680001808038000600a0c8141700a0181404804008140101000000028160e8440000002800000020000a0181801810008080282e000100b00007800078020000000012000240d80a0080c00802000000601a0002a0100e000000101e0a0040482006808010180300e060000001000c397018951d0e1ab88c4a86878c5866014943c64c2b00a4a1e31615805250e8b388c4a9885455c46254c42a34e0312a621519701895310a87390c2a9885855846154c42a34e030aa621519701855310a87390c0a9885459c46054c42a2ae2302a621619601815310b0aa9cc2298858554d6114c42c32a7300a621619535805310b0ca9cc1a88858694d60d4442c32a6b06a22153170d4e5110a99386a6a88854c5c35354442a2aeb29aa2214367614d5110a8b398a6a8885499c85354442a64e029aa2215317014d5110b82a9ca4a88858558c6354442a4ce431aa2215327018d5110a98b80c6a8885459cc6054442a2ae6302a221526721815110b18b00c0a888507dd95314442c2aa7308a221616635445110b0ab1aa2288858654e6014442c62a3300a221619535805110b18a8ac0288858554e61d4042c2ca6b0ea021615535875010b0ab1ca3a80858598d51d4042c2ac6a8ea02153171d4e5010a8cb9ea328085c454e5194042e24a6a8ca021711535465010a9938ea6a80854c5c75354042a32eb29aa02143a7614d5010a8d398a6a80854a9c85354042a64e229aa0215317114d5010b84a9ca4a8085469cf5154042a32e7a8aa021531759455010b8929ca2a8085c454e5154042e24a6a8aa021711535455010b91292a2a80850e9d85154042a34e628aa021519731455010a99388a2a80858658c6354042a54e431aa0215327118d5010a98b88
  | 4 => 0x5e8b889b0ee665008884100bd179aa12809ce000325e2bcf60a740813cf49c3018510d12450006581c11713a000f103f0960012406c0ca0010aa191be05c3a9da01c430af23730a8e1091ba1a03fcda000038484eca0a3fa000ed8000004b000168000010108000004e45c00014c000438782221c87780026458cd898e0821600012328c72cb3800196564d789e152000ab01023a858000f421455c9f8980c48703203c2da344e80bc25c7d0369073c00b8bc0c5330438001e724e71cce23107a5c8d38e023e8943e15f146668cb9d434674c800ea2fe918e223b1c81f84a85b01a27cc50000326047b8cf0000000088c2560011694a364000001bb452140610b92d40011e0000bc0b0500f2000000558000047f0001fe24c000ba9220163c48e1bd000000ca8002280008586742e000ef0002a81c0b49d80002b40002d1d0530f69a543c000249d7000000001860007d850a470006d800233348300e492d22a4c4370002205ed0e80033649484800132000bf1ab0007e4001d208e744158d511c00000000328000ce9c62ba63c000000002e8000c83d00011f0d313400022a0e46c0000a9ad3402ccc58000e6240be0ec1da82c618342aa8806906300c4a421814304000a01492e83e0ff86a18e6f91115b0003b80422b3727e03404612c150d807104082400005274420e10a20302090c076310128a7000270000000692404d0428861e6791098004641087a8003508d0418b5318754ee924394000c1a3f06e684451bc0145acc3800066000b781d40e000001e317c2d1019ea0000004221b0c00001a80000087cf98241602f4a11132a683cb61412245988c1030004ec479651ac044448001544d47c90d000369108e940a0586a0000c23746f0e70468b10d04d0007308d87a000000d623a4800e4bb9d63201584b9640b888cc98000a63645f87f28a4643d9fb4280a8731601483702f8fc2dc120049801500786d8923908440012a034000001
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x48d0015801c228010168d8b001b80250000041b1d858018810000001a05000013a30ba09600000600198880190182971a93182411899e078700082583a106a480000a9c800f9100000c1d00a61f1fa1831223a6800000001092800c80178000148e0015090a2000000e9e800000001400220200000f0000000002001400402182820000000000410110003800004003c11615c06154c42c11715806054c42c11635c06354442c11735806054442c11635c46354042c11735846154042c81719c06250d32c82715c06250d32c81715c06250d32b01801093254432b01811093254032909801c9534cb41909801c9544cb31909801c9544c931b01801d1524c431b0180991524c431c0576548424c431d01525c0424c431a11869d13154031911871093154031a11861093154031909801d5434cb218a1801c961d0d21c81739c06250521c82735c06250521c81735c062505218a1801da32505218a1801c9648c5218a1801c9644c521a0485591324c5219058754c4248421d01535c04248421b01831092154021905811c9534cb40c0575589310c740a11854c5600c740905831c95148740905811c9544cb30905811c9544c930b01811d1524c030b0181991524c030c0976548424c030d01525c4424c03091187991514c03091187109514c030a1186109514c030c097654b414c030c1176547414c030905811d5434cb20905831d541487208a1811c960d0d20889831c960d0520c81739c46250120c82735c46250120c81735c462501208a1811da3250120889831db21501208a1811c9648c1208a1811c9644c120a0885591324c1209098754c4248020d01535c44248020b01831095148020905831c95448710909831c95448210905831c95448510909831c95448110920875512148110a20865512148110911879915344010c117654f4344010b01831d15244010b01839915244010a2186d0d52440109118754c4244010c117654c4244010c21765484244010d01735484244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1074
  | 4 => 1930
  | 3 => 587
  | 2 => 78
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
  | 6 => packedAt s5K6 (864+((h/16+packedAt s5K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (32936+((h/358+packedAt s5K5 (28998+(h % 358)*11) 11) % 1289)*12) 12
  | 4 => packedAt s5K4 (81056+((h/643+packedAt s5K4 (73340+(h % 643)*12) 12) % 2317)*12) 12
  | 3 => packedAt s5K3 (30713+((h/195+packedAt s5K3 (28763+(h % 195)*10) 10) % 705)*11) 11
  | 2 => packedAt s5K2 (4862+((h/26+packedAt s5K2 (4680+(h % 26)*7) 7) % 124)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc3c79f8e3f1c78fc7e638f8e1c738fcf8d30cf
  | 1 => 0xfc07e7f03fe07f1f8f83f1f01f83f1f3b23333
  | 2 => 0xfff807ffcfff801ff1fc01ffe3fc01fc43cc3c
  | 3 => 0xfffff8000fffffe001fffe0003fffe007c0fc0
  | 4 => 0xfffffffff000000001fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4050c0a0410891088020828244108449051045
  | 1 => 0x842111048241203010811110888120a2122112
  | 2 => 0x8800200040002400204002401200100004428
  | 3 => 0x1102004928904001254a2401024a4800680a80
  | 4 => 0xe234546c20da749a49f3c9c9d0086c2b7fb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8fef8fee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_27821
namespace PEqualNP.Outside.L_meta_27821
open PEqualNP.Outside.L_meta_27821.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x5824719000c62400800004400a1d3cb58063658d2a4afd4002441f024cd4505002079776dcf8470f402364343a10200a9100f00315201a004ecd59c720003a0001b0b5c000005e4c0181100080013c800821400c800004a00121090002ffd5009fe54025f9500bfd54027f150097c5402ffd4c07fe5302ff54c07fc53027fd0c07fe43007f50c07fc4302ffd480b7f5202ff9480bfd52005f5480bfc52027fd0801fe42007f50809fc4201ffcc801fe32007f4c807fc3202ffd4405fe5102ff54405fc51027fd0405fe41007f50405fc4101ffcc405fe31007f4c405fc31007fc8405fe21007f48405fc2102ffd4003fe5002ff54003fc50027fd0003fe40007f50003fc4001ffcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x64001ffc432000ffc2190007fc10c801bffb2a400dbfd952006ffcca90016fe654801bfeb2a400dbf5952006ff8ca90016fc6548001ffb224000bfd9120067fcc890012fe6448001feb224000bf59120067f8c890012fc644801bffaa2400cff95120066fca890037fd5448019fe2a2400cdf15120007fec690002ff6348017ff31a4003bf98d20007fac690002fd6348017fe31a4003bf18d2006ffea69002ffe534801bfea9a400bff14d20067fe869002ffe4348001fea1a400bff10d2000dfec490037ff524801bbfa924009ff9492006ffaa4900037d5248013fe292400cffd092004ffc8490003fd4248013fe212400bffcc92004ffc6490003ee3248001fe9924000fb4c92004ff86490003ff61480017fb0a400aff98520015fcc290003fd6148015fe30a4002bf1852006ffea29002bfe514801bfea8a400aff14520067fe829002bfe4148001fea0a400aff1052005ffe629002bfe3148001fe98a400aff0c52004ffe4290003ef2148015ff10a4000ff48520007da4290027fc21480037fb024001ffd412000ffca090007fd5048003fe2824001ffd012000ffc8090007fa4048003fea024000fe5012000ff88090007ff3048003ff1824001fe8c12000ffa6090003f93048003fe1824001ffc812004ff64090007fe2048003f71024001ff0812000fd84090007f82048003ff8824001ff8412000ff42090007fc1048011ffb2a2008bfd9510047fcca88016fe6544011feb2a2008bf59510047f8ca88016fc6544001ffb222000bfd911003ffcc888012fe6444001feb222000bf5911003ff8c888012fc6444011ffaa22007ff9511003efca888023fd544400ffe2a22007df15110007fec688002ff634400dff31a2003bf98d10007fac688002fd634400dfe31a2003bf18d10047fea68801bfe5344011fea9a2006ff14d1003ffe868801bfe4344001fea1a2006ff10d10007fec488002ff6244001ff3122009bf98910007fac488002fd6244001fe3122009bf18910047fea4880237f5244011ff2922008ff54910006faa488023fc524400fffa122000ff90910007fa848801ffc424400dff9922000ff8c910007fa648801bfc32440037fb0a2002ffd4510017fca28800bfd5144005fe28a2002ffd0510017fc828800bfd4144005fe20a2002ffcc510017fc628800bf63144005fe98a2000fd4c510017f8628800bff2144005ff10a2002fd88510017fa4288003f52144005fe10a2001bfd811000ffea088007fe5044003fea822001ff1411000ffe8088007fe4044003fea022001ff1011000ffe6088007fe3044003fd1822001ff4c110007f26088007fc3044003ff9022001ff8811000ff44088007fd2044001fc9022001ff0811000ffe208800bfb1044003ff0822001fd8411000ff82088007f41044003fc0822001fc04110
  | 1 => 0x7f95050003fe2828001ffd0140027f680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ff860a0007fe2050003fd1028001ff0814000ffe20a0007fe1050003fe0828014ffd95300a5feca98053fe654c00b7f32a6014ff595300a5faca98053fc654c00b7e32a6000ffd9130005fec89804ffe644c0097f3226000ff59130005fac89804ffc644c0097e3226014ffd513009ffca89804f7e544c029feaa26013ff1513009ef8a898006ff634c007ffa9a6003ff94d3001ffaa69800ffc534c007ffa1a6003ff90d3001ffa869800ffc434c001ffb126000bfd8930007fcc498003fd624c001fe3126009bf189300a7fea4980537f524c029ff2926014ff54930006faa498053fc524c027ffa126000ff90930007fa849804ffc424c007ff9926003f7cc93001ffc649800ffd324c001ee9926003ff0c930007fec298002ff614c025ff30a6002bf98530007fac29804bfc614c0057e30a6014ffd4530097fca298053fd514c025fe28a6013ffd0530097fc8298003fd414c025fe20a6003ffcc53001fbe629800ffe314c007fe98a6000f74c53001ff86298003ff214c025ff10a6000ff48530097f84298006ff604c003ffa826001ff9413000ffaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826003fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007d8304c003ff1026001fe8813000ff84098007ff104c003ff0826001fe8413000ff82098027ff65c80137fb2e4009ff9972002dfccb900277e65c800b3f32e4009ff5972008dfacb900277d65c80013eb2e4009ff1972004df8cb90027ff64c80137fb264009ff99320025fcc990027fd64c80017eb264009ff1932004df8c990047ff54c8021ff2a64010df9532008ffaa990043fc54c8021be2a64009ffd8f2004dfec790027fe63c80077f31e4009ff58f20005fac790027fc63c80137e31e4011ffd4f2007ffca790047fd53c801ffe29e4010ffd0f2007ffc8790003fd43c801ffe21e4001bf98b2004ffea5900277f52c8013ff2964009ff54b2004efaa590027fc52c8013ffa164009ff90b2004ffa8590027fc42c8013ff9964009ff8cb2004fdc6590027fd32c8001f69964009ff0cb2004ffec390027fe61c80057f30e4009ff58720005fac390027fc61c80057e30e4011ffd4720077fca390047fd51c801dfe28e4010ffd0720077fc8390003fd41c801dfe20e400fffcc720077fc6390003fd31c801dfe18e4009ffc872004fde4390027fe21c8013fe90e4000fb4872004ff84390006fd60c8003ffa864001ff9432000ffaa190007fc50c8003ffa064001ff9032000ffa8190007fc40c8003ff9864001ff8c32000ffa6190007fc30c8003ff1064001fb8832000ff44190007fc20c8003f61
  | 2 => 0x21017f8639080bfe21c8405f710e4202fd88721017f8439080bec21c8413ffb064209ff9832100dfcc190827fd60c84017eb064209ff1832100df8c19087fff50c8439ff286421fff543210e7f8a19087bff40c8439ff206421cff103210effe6190873fe30c8439fe1864209ff8832104ff8419080bff10c8405ff0864202ff043210dffeca9086eff6548437ff32a4205bf995210dffaca9086efd6548437fe32a4205bf19521007fec890802ff6448435ff3224204bf99121007fac890802fd6448435fe3224204bf191210dffea89086bfe5448435bf2a2421bff551210d7f8a89086b7c5448401ffb1a4200bfd8d210cffcc69080efe6348401feb1a4200bf58d210cff8c69080efc6348437ffa9a4219ff94d210dffaa690867fc5348435ffa1a4219ff90d21007fa8690867fc43484057fb12421bffd49210defea490827fe5248437fea924200df5492104ff8a49086bff4248413ff2124200ff5092104ff88490867ff3248413ff1924200fb8c921007fa6490803ed3248413fe1924202bfd8521017fea29080bfe5148405fea8a4202ff14521017fe829080bfe4148405fb20a4202ff50521007ea829080bfc4148405ff98a4202ff8c521017ec629080bfd3148401fa98a4202ff0c521017fe4290827f72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec090863fe60484037f3024200ff581210c7f8c090806fc6048437ffa824218ff941210dffaa090863fc5048435ffa024218ff901210c7f88090867ff3048431ff1824218ff0c1210c7fc4090827fc2048405ff8824202fdc4121017fc209080bfc104842bffb2a8015bfd9540006fecaa00027f655002bff32a8005bf995400affacaa0056fd655002bfe32a8005bf195400aef8caa00167c65500037fb228004ffd51400af7ea8a0013fe5450009bf2a28004ff55140027f8a8a00137c5450009de2a28004cf15140007fec6a0002ff635002fff31a8003bf98d40007fac6a005ffc63500077e31a8015ffd4d400bffca6a0057fd535002ffe29a8004ffd0d400277e86a0013fe4350009fea1a8000ef50d40027f886a0003ff62500017fb128000ff98940007fac4a0003fc62500137e3128015ffd49400aefea4a0057fe525002bfea928000df549400aff8a4a0013ff4250009dfa128004ff90940027fa84a0003bd4250009fe2128017ffcc940007fc64a0003fd325002ffe1928000ffd8540005fec2a005bfe61500057f30a8000ff585400b7f8c2a000afc615002bffa8a8016ff945400affaa2a005bfc5150009ffa0a8004efd0540027fc82a0013fd4150001dea0a8004ff105400bffe62a005bfe3150001fe98a8016ff0c540007fe42a005bfe2150001fe90a8016ff0854000dfec0a0007ff5050003ff2828001fe9414000ffaa0a005
  | 3 => 0xe2928204ffd09410277e84a0813fe4250409fea128200ef50941027f884a0893ff3250401ff1928200ff4c941127f864a080aff6150405ffa8a8202ff94541017eca2a080bfd515044bfaa8a8202ff14541017fe82a0813f74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ffcc541017fc62a080bfc3150405ff10a8202fd88541017f842a0803ff60504017fb028223ff9814100dfcc0a0803fd6050447fe3028201bf1814112ffea0a088ffe505044bfea828223ff14141027fe80a0813bf4050409ff2028204ff10141127fe60a088ffe3050447fe1828223ff8814111ff840a080bff1050405ff0828202ff04141117feca9888aff654c445ff32a6205bf99531117faca9888afd654c445fe32a6205bf19531007fec898802ff644c443ff3226204bf99131007fac898802fd644c443fe3226204bf19131117fea898887fe544c443bf2a26222ff5513110ff8a8988877c544c4057fb1a6203ffd4d3101ffca69880ffd534c407fe29a6203ffd0d3101ffc869880ffd434c407fe21a6200ffd8931005fec498803fe624c401feb126200ff1893104df8c49888bff524c445bfa926222ff94931117faa4988037d524c445fe2926221ffd0931007fc8498803fd424c443fe2126203ffcc93101fbe649880ffe324c407fe9926200f74c93101ff8649880aff614c405ffa8a6202ff94531017faa29880bfc514c405ffa0a6202ff90531017fa829880bfc414c405ff98a6203fdcc531017fc629880bde314c405fe18a6202f70c531017e8629880bd4314c405ff10a6202fd88531017f84298803ff604c4017fb026220ff9813100dfcc098803fd604c441fe3026201bf18131117fea098883fe504c445fea826220ff1413110ffe8098883fe404c441fe2026203ffcc13101fbe609880ffe304c407fe1826220ff88131107f8409880bff104c405fb8826202ff84131017f82098827ff65c84137fb2e4209ff9972102dfccb908277e65c840b3f32e4209ff597210fdfacb908277d65c84013eb2e4209ff1972104df8cb90827ff64c84137fb264209ff99321025fcc990827fd64c84017eb264209ff1932104df8c99087fff54c843dff2a6421edf953210fffaa99087bfc54c843dbe2a64209ffd8f2104dfec790827fe63c84077f31e4209ff58f21005fac790827fc63c84137e31e421fffd4f210effca79087ffd53c843bfe29e421effd0f210effc8790803fd43c843bfe21e4202bf98b2104ffea5908277f52c8413ff2964209ff54b2104efaa590827fc52c8413ffa164209ff90b2104ffa8590827fc42c8413ff9964209ff8cb2104fdc6590827fd32c8401f69964209ff0cb21015fac39080bff51c8405ff28e4202ff54721017f8a39080bff41c8405ff20e4202ff50721017f8839080bff31c8405ff18e4202ff4c7
  | 4 => 0x12fe648c813feb246400bf5923204ff8c919026fc648c85bffaa4642cff95232166fca9190b7fd548c859fe2a4642cdf1523201dfac71900fff538c807ff29c6403ff54e3201ff8a71900fff438c807ff21c6403ff50e3201ff88719026fe628c813ffa946409dfd4a3204ffca519027fd528c813bea946409ff14a3204ffe8519027fe428c813fea146409ff10a3204ffe6519027df328c807f79946409ff0ca3204fd86519027ff618c813ff30c6402bf9863204ffac319002fd618c813fe30c6402bf1863216ffea3190affe518c85bfea8c642bff14632167fe83190affe418c857fe20c6403ffcc63201ffc631900ffc318c813ff10c6409ff0863204ffec119027fe608c8037f3046409ff58232005fac119027fc608c8037e304642dffd4232157fca1190b7fd508c855fe284642cffd0232157fc81190abfc408c807ff9846403ff8c23201ff86119027fe208c813fe104642bffc4232157fc21190abfc108c853ffb2a6429bfd953214ffcca99016fe654c853feb2a6429bf5953214ff8ca99016fc654c801ffb226400bfd9132147fcc899012fe644c801feb226400bf59132147f8c899012fc644c853ffaa26428ff95132146fca8990a7fd544c851fe2a26428df1513204dfec69900fff534c807ff29a6403ff54d3201ff8a69900fff434c807ff21a6403f790d3201ffa8699003dd434c807fe21a6403bfd893214ffea4990a77f524c813ff2926429ff54932006faa499027fc524c851ffa126409ff90932007fa8499027fc424c807ff9926403fbcc93204ffc6499027de324c813fe1926409f70c93201fd86499003ff614c8017fb0a6427ff98532015fcc299003fd614c84ffe30a6402bf1853214ffea29909ffe514c853fea8a6427ff14532147fe829909ffe414c84ffe20a6403ffcc53201fbe629900ffe314c807fe18a6427ff8853204ff84299003ff604c8017fb026426ff9813200dfcc099003fd604c84dfe3026401bf1813214ffea09909bfe504c853fea826426ff14132147fe809909bfe404c84dfe2026403ffcc13201fbe609900ffe304c807fe1826426ff8813204ff8409909fff104c84dff0826426ff0413212ffecaa0896ff6550401bfb2a82009fd954112ffccaa0816fe655044bfeb2a8225bf5954112ff8caa0816fc655044bbe32a82059f19541015fec8a0813ff545044bdfaa28204ff95141026fca8a0813fd5450409fe2a28204df1514102778a8a08133c5450401ffb1a8200bfd8d41127fcc6a080efe6350401feb1a8224ff18d4101df8c6a0897ff5350449ff29a8225ff54d41127f8a6a0813ff4350409dfa1a8204ff90d41027fa86a0803bd4350409fe21a8200ffd8941005fec4a0803fe6250401feb128200ff1894104df8c4a0897ff525044bbfa928225ff9494112ffaa4a08037d525044bf
  | 5 => 0x8152006fac0a90db7c6054873bfa02a436df901521b6f880a90e37f305486dbf182a436df0c1521b6fc40a90277c205486fbf882a436df841521b6f820a9027ff65908137fb2c8409ff9964202dfccb210277e659080b3f32c8409ff596421adfacb210277d65908013eb2c8409ff1964204df8cb21012fd6490809ffaa48435efd5242027fca9210137e5490809feaa48404ff15242026f8a921013bc54908099e2a48409ffd8e4204ffcc72100efe6390813feb1c8400bf58e4204ff8c721026fc639086bffa9c8434ff94e421affaa7210d3fc5390809ffa1c8404ff90e42027fa8721013fc43908137f3148409ffd4a4204efea521027fe5290813f72948409ff54a4204efaa5210d7ed5290801b6a948409ff14a4204ffe8521027bf4290809f7a148409ff10a4204fd88521027ff3290813fe1948409ffd864204ffcc32100afe6190813feb0c8400bf5864204ff8c32100afc619086bffa8c8433ff946421affaa3210cffc5190809ffa0c8404ff90642027f883210d3ff3190867ff18c8433ff0c64204ffc4321027fc2190813ffb048409ff9824200dfcc121027fd60908017eb048409ff1824200df8c1210d7ff5090865ff2848435ff54242197f8a121013ff4090809ff2048404ff102421a7fe61210cbfe3090865fe1848409ff8824204ff841210cfff1090865ff0848432ff0424218ffecaa10c6ff6550801bfb2a84009fd954218ffccaa1016fe6550863feb2a8431bf5954218ff8caa1016fc6550863be32a84059f1954204dfec8a1013ff5450809ff2a28404df95142027faa8a1013fc5450809be2a28400ffd8d42005fec6a10c3fe63508077f31a8400ff58d42187f8c6a100efc6350863ffa9a8430ff94d4218ffaa6a10c3fc5350809ffa1a8404efd0d42027fc86a1013fd4350801dea1a8404ff10d42025fec4a10c7ff5250863bfa928409ff9494218fdca4a10c7fd5250801bea928431fb54942006daa4a1027fc5250809ffa128404fbd094204ffc84a1027be4250813fe2128409ef10942027d884a10c3ff3250813fe1928400ffd8542005fec2a10bffe61508057f30a8400ff5854217ff8c2a100afc6150863ffa8a842fff9454218ffaa2a10bffc5150809ffa0a8404efd0542027fc82a1013fc4150861ff98a842fff8c54217ff862a10bffe2150813fe10a8400ffd8142005fec0a10bbfe60508037f3028400ff58142177f8c0a1006fc6050863ffa82842eff9414218ffaa0a10bbfc5050809ffa028404efd0142027fc80a1013fc4050861ff982842eff8c142177f860a10bbfe2050813fe102842fffc4142177fc20a10bbfc1050813ffb2c6409bfd963204ffccb19016fe658c813bf32c64059f9963204ffacb190b6fd658c813beb2c64009f5963204ff8cb19026fc658c813ffb246409bfd923204ffcc919
  | 6 => 0x3006004004000130000000101102800c0c80000000c008030020080100002a01800016000020020000080040000a016010140090240000b81100003c018060160000100001400402800020000000010000002500500a0080101d00401002800000004060270020080d00400412002806000044060000140040300100e000070000060340000300202801000034004008050200000780100c12005017000004080010000280000400e0140d80301e0740181901e01c030070260080a80000205402003002000020040d40340300000802c010030460080380000e0380000a0000080201c0000540083f01000c02012000028080000000000400e0200080000101a01800800048000010000000340001200800006039024040190110020340900000a020020020000140400700e0000600000201c018050320240380008c00c0805803e0000080c002000088000060a40002c0060340b80a02a0500600001a030018000100780e0000ea0340203c002070028010320180481c00c00009000022098000020320080100700c04c0080200e0080001800200479ffb2a863cbfd9543006fecaa18027f6550c79ff32a8605bf995431e7facaa18f2fd6550c79fe32a8605bf195431e6f8caa18167c6550c077fb228604ffd51431e77ea8a1813fe5450c09bf2a28604ff55143027f8a8a18137c5450c09de2a28604cf1514301dfec6a180fff5350c07ff29a8603f794d4301ffaa6a18f3dd5350c07fe29a8603ffd0d43027be86a180ffe4350c07df21a8603ff10d4301f7886a180fdc4350c01ffb128600bfd8943007fcc4a1803fd6250c01fe3128609bf189431e7fea4a18f37f5250c79ff292863cff549431e7f8a4a1813ff4250c09dfa128604ff1094301ffe64a180fdf3250c07fe1928600ffd8543005fec2a18effe6150c057f30a8600ff585431dff8c2a180afc6150c79ffa8a863bff945431e7faa2a18effc5150c09ffa0a8604efd0543027fc82a1813fc4150c07ff98a8603ff8c54301ff862a18effe2150c77fe10a8600ffd8143005fec0a18ebfe6050c037f3028600ff581431d7f8c0a1806fc6050c79ffa82863aff941431e7faa0a18ebfc5050c09ffa028604efd0143027fc80a1813fc4050c07ff9828603ff8c14301ff860a18ebfe2050c75fe102863bffc41431d7fc20a18ebfc1050c01bfb22a400cfd91521cefcc8a90127e6454801beb22a439df19152024f8c8a90033c64548091e322a400dfd8d521c6fcc6a90037d6354871be31aa439dfd0d521c6fc86a90037d4354871be21aa405dfd895202cfec4a90176f6254873bfa12a409df109521c6fe64a90277c3254801bfb0aa437df98552006fac2a90df7c6154873bfa0aa437df905521bef882a90e37f315486fbf18aa437df0c5521befc42a90277c2154801bfb02a436df9
  | 7 => 0x1e50000012c75af5034772e62e00df21a50516806e5310000000000000000004641782b21120005424135213f74cb08c5512c22a836e2aa2b90d300051c0990002f20cf2262af37004f33f08423231508528b41a02904d0e300043b3330004a54c656a0002f848759b0005720e81753a859e2bb2972c90002c424a00036c0131611ba52829f5a90d900000046a1f228840b3000572ea55d2625015320000a21930000802d741c07536346c47532944a1c60000000001860003fe24722d00043e0bc0635301d92a12301343b33fd4cc43c38e3cd0074663c92d60fa00027f3b455859a49f4d859823f04b44300043433d16000033743942e1e20000003820da4853f85401711ef00000008f42f30350945e51726d1a62bf0f116501406839444c4b644518f0b05600e92df41e4c826e55e49e1910242f62360cb0870fe0ea5344e54ba00000046139b00049a0004245150004d32a94261070003672d10c60001a41512662eb3070004782712ec0795b251e4ea1370420004fc08a00c4f80001241015970000001cb0e055a5790004091062a64120b80300000b100035452600006b00000014600029e0000ba0cd0000003473b62950a739105d35f38a5a85223e113a0a90ae38803f2cc4c018d1734af1f92752d457d0c858858b1993ad3ed0f41a019d4a322c53f25d0d63bf03c45216e1fa58c43315255434831f13606c25b45d09023a45b44f3f24764900002552f100047c2103e250021120349b34248d1c229811521e5160ec09842331809f30a3d72054dd2c55aa4f91c73be3df3eb37b5394953623da4163d314b31b4a03d12ee40432c09a1cc4320e22f33861491df2725184ed0860740ef31612b2772e525f00004a3c10643f44f321916c4fe3a200926119800027927a5962f70000001164b705448834a1be4722291262590274bb00010c1e048f49710e3c811d1834ac1130323d600013e5703192bc58100029b1a72ba39f4f514a21f30e47f3ca4d51800a83110393253442004ef12d11f23504801500058612706f0000f53b53ab00000059400000007c4d400a00c000078000180080500100402c0a01203601c03808000004018130980040100f0000000000200800c0500000001c0802f0000100180101c00801003000008030010000700a819008000018040080000204f0020040402b006000030070040300000000a014050000000040300001e028078240000480b8000200000001d004044008000100000280200c0600180701c0b8020030c80080080102a0280e0080120080000200e02c0a8010060440080f000034000290000300080c0140200100f00600801804000000000040020000400000001c038000320000080e0060080b00e00411c0101300803c0e8520080000380605a0200500000e000000010000180680b0020080
  | 8 => 0x830001f72c30003e31324ab0001485140000032065ac0721c417e51a0e101f55600000010031a00000016f58f3e04e70b60005671d200000008e2e42961544220921d32572c83560171ce37f0f002e53804557734656120e01812e14e23d4bd3410a330929a5a71d00bd56219c1170512ab11854c0005b135e05f0b44983520001892d53511400041ac1bb32f4020ac20f1140ee0003b950700028a00000047021737549c08100021d0002a544e0004530000002ac1033e90000003170004d935800000045c4f62010000000004673e404100044b00024f4741664493c23cf41d1dc0a64793d54fa4d10003494b342000000053344714359538d1552b645a4314b83dd4350220961de38555549d11b2cb4c30f315c4da4c94994914bf3e83e509e5915112203ff0773a74a64f253616a2e11da00058903d01a0003230001564fb4150f700000056436a2d300010821608d5b52851cd45955b2145022704144b54a84364ad47b00e3d405a4f04942ff28221548927d1a21114f701d26c5a40d730b34028e08911906707359356d4822ae0020e75851413f92fe01e5131f056c23c03e3c63145044dc36604c0c70c532103458a5844f141b4841c534b33403b54629003618544034c29459957b4e246510b46f0002ce0a03a10003990000000000000000000462210be15e13802d0935ae04e05c2020aa4002be2222415a60fb02359d4074e40000000005ad0001584c700056f1fe00054b4d01813040000000001701020881ff42d00040c5240c20ab00048e5763f13bb5290a40000003c000019500000014d3533385691a502f00039022b50e2743f300015b5595780191d52601c84380083c40004ae1b73d800a45618229c0dd59c1f65634b94ee3db1f80003d233a0c018e17a0001a327c29139d4811b515a40f0f21770b549212a51b1d637905632b3781b134e23300017f00054e5a112c2a053c3c34053b75833dc14c25e52c26828632001c32d0352762db48a2f93452cf2521971904e10f80702871ab10f22415f52f35706220c42827812f39637307d59f0110000004a117200038c00030113b2f40d020d3121690332dd1c95750001f400021c3e748616d0ed0002da36d11022f19f10900031c00038736f02c26a23b16b3760ad0004064d74b11571b40004550002ef0001472492533131bc00f52336539e0003980005824512500001213893a942a25a07b35a50824b00013152d41000d3ae50f4250003600830001fc41100011a1280000b33640000000002340000001fd0003e61ae02525c00000000000000000017954d32209c00000006a0003de0000002891d12b12401443680004a747e3800db0000d54a905841734300000034d00046953d51d0472080003b85a21e83311ed2420e43b21763a42812234df3fb09539313f0002642931ee
  | 9 => 0x4ec44831e1f14e036940300032e2832fd3270fd0690000a500000021b0004eb4580000000001b200039a00033035500000000000054a0003d000000037a0ff2dc0de3060973d92434b00eb4c11aa27e1920313a52651b030842c28d3772d007a18c44426b35d04302b4b259208207858e25400047a4e84465b35734212b80602e32ed28f4572124b448b3502de2510001622cd2fc1d40911741042131ad33e53747d0522844801e353a00000051000000000000000017d40d4db0000000000003c710d52a00018a3fa0005120000000003322bd00019b3100c420915357e00052e0004de0002270bf0004713840591b628055049300000053b1fb58d1883f606d4085a510a05b02142944247356e5a357f35b1f32a251f5252183a60fc4010c300000000030d36b2580000d44d20000005480001b30003365ab0285663742630372ca02638f40e1671335745710004a22382b30bb3810003f01ca3052450b930f09400000052b2b01420554543612f53ba33c42b4d622e0c11c10651a950d01b25640a24e0000380ce1bf4c507e2a35650f60d23fc50a4ff45044d37d0000000000000000000003cc30c5b046328c0001b84682fb19a52700019619e1b91295191cf04437e4273a03350002b73aa2070062485a026f05e0500710490d80001a11940003ec48c1233c500015d3ee32a4962d910541800043d0b70a14ca0004aa0d154f0004e600000000054400023e3b00000000001640002282d820a00000043a4e93bc07f17b0000004bc46b2fa20b2990000000004f40000002a40002ad0405060050121392f055c18411e0f93392440001205573950001355534a41500000761593ce30217c2b50003260001c33ea06129235900059000b0e51d81ec3284cd44103a5b43713971d73af23139c09d33b2c00530ca5874193b102016309b1e62e81bd3a31a837c26735c08b0000000000002a75200000000105471ea2d22b453518b4300c92690dc1874621af0160b21e713011c57c38b46041f2041e955f50c1c023934f0af56b0e624c23729d56831d2e21e154337253e2e73bd4c406643713c3ef3ac46d1454831252733240cc46e2c143f57a5801eb5411e41dd2464fd3922255493cb1db13d54514f0005521f500024d4be45f4c250b00002a2e900000022a0002c61224e33f54cf27b4ce3
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x67190910005f5719091000dfa7090910005f97090910197f01090910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100457c7550910026be6450910006bd64509100076d5250910177f0105091004cff768c910004fe768c910004fd768c91004cfc768c9100457e758c9100057d758c910006df638c91001edc638c91004eee628c910006ed628c910015f6718c910005f5718c91000dfa708c910005f9708c910157f0108c910004ff764c910004fe764c910004fd764c910004fc764c91001ede634c910006dd634c91004eee624c910006ed624c910015f6714c91000dfa704c910137f0104c91000df4764c51001ef4764c51000cf4764c51022776544c51022774544c510015f7734c510017d7734c510007d7634c51001ef6634c51001ef4634c510037d4634c51001ed4634c510005f7724c510006f7624c510006f5624c51021f77524c51000775524c510037d7324c510007d5324c510007f3704c51000df6704c51000df4704c510107f0704c51000df0704c510016f7604c510017f3604c510107d7304c510107f2304c510107d5304c510107f2204c51000df4764851004ef4764851000cf47648510006f76448510006f56448510217765448510217745448510005f77348510005f57348510006f76348510006f56348510015f77248510017e77248510007e7624851004ef6624851004ef46248510007e4624851020f775248510007755248510007e63248510007e53248510007f3704851000df6704851000df470485100c7f0704851000df07048510016f76048510017f360485100c7f230485100c7e720485100c7f220485100c7e52048510015f8764c11001ef8764c110014f8764c1102077a544c11020778544c11000dfb734c11000fdb734c110007db634c11001efa634c11001ef8634c110037d8634c11001ed8634c110005fb724c110006fb624c110006f9624c1101ff7b524c11000779524c110037db324c110007d9324c110007f3714c110015fa714c110015f8714c110097f0714c110015f0714c11000efb614c11000ff3614c110097db314c110097f2314c110097d9314c110037f1314c110007d1314c110097f2214c110007f1214c110015f8764811004ef87648110014f87648110006fb6448110006f964481101f77a54481101f7785448110005fb7348110005f97348110006fb6348110006f9634811000dfb724811000feb7248110007eb624811004efa624811004ef86248110007e862481101ef7b5248110007795248110007ea3248110007e93248110007f37148110015fa7148110015f87148110057f07148110015f0714811000efb614811000ff36148110057f23148110007f13148110057eb2148110057f22148110057e92148110007f12148110007e12148110
  | 1 => 0x8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10266df31d8d10266dd31d8d10266f621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10256df30d8d10256dd30d8d10256fa20d8d1001cff7658d10036dc6358d1024df77158d1025dfb7058d10107f01058d10004ff7558d1002cfe7558d10004fd7558d1002cfc7558d10004ff7458d10024fe7458d10024fc7458d100067e5458d100067c5458d10254ff7358d10006df7358d10004ff7258d1004cfc7258d100067f5258d10036df3258d1024cff7158d10006f77158d10096f62158d10104ff7058d10006fb7058d10106fa2058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100457c7550d10026be6450d10006bd6450d1003f3c5450d10006df6350d1001edc6350d101d7f01050d1004cfe76d891023ff010d8910004ff75d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d89100067e54d89100067c54d891001cfe73d8910004fd73d891001cfc73d89100067f52d891000cff71d8910014fe71d891000cfd71d8910014fc71d8910246f631d8910246ef21d8910246ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891023efa30d891023eef20d891023eed20d89100c4fd76989100457e75989100057d7598910006ef62989100c5f57198910055f970989100e7f0109891004cff7658910005df7358910035dc73589100e5f77158910075fb70589100c7f01058910004ff755891002cfe7558910004fd755891002cfc7558910004ff7458910024fe7458910024fc74589100067e54589100067c5458910004ff7358910006df7358910004df735891001cfe735891001cfc7358910006dc735891001cdc7358910006ef72589100067f52589100e4ff7158910006f77158910056f631589100c4ff7058910006fb70589100c6fa305891023cfe76189100457e75189100057d751891003dbe7418910005bd7418910035de7318910005dd731891004eee6218910006ed6218910237f010189100067f76549100067e76549100067d76549100067c76549100073f745491003d7e745491003d7c74549100073c745491003d3c74549100067f64549101ce7e64549100067d64549101ce7c64549100067f63549101c67e63549100067d63549101c67c635491022d7f72549100476f72549100067f625491004e7e62549100067d625491004e7c62549101b67f61549101bf7631549101bf7621549101b67f60549101b77a30549101b77a20549101bf7b10549101b77610549101b77410549101b77810549101b770105491004cff7690910004fe7690910004fd769091004cfc76909100457e75909100057d759091003f3c54909100076d5290910015f
  | 2 => 0xdec70485200c7e8704852004eef604852004feb60485200c7ea40485200c7ea30485200c7e710485200c7ea104852004df87650120026f8765012004cf876501200077b755012029f78755012029efb655012029ef9655012000dfb745012000fbb7450120007bb6450120026fa6450120026f86450120067b8645012029fbb54501200677a5450120067785450120067b85450120067385450120005fb7350120067bb4350120007b94350120007eb725012004dfa725012004df87250120007e8725012004de8725012000efb625012000feb625012029f7b5250120007795250120067bb4250120007b94250120007ea3250120007e93250120005fb7150120067bb4150120007b94150120007eb2150120007e9215012004df8764c12001ef8764c12004cf8764c120005fb744c120005f9744c1202977a544c12029778544c12000dfb734c12000fdb734c120007db634c12001efa634c12001ef8634c12005fd8634c12001ed8634c120007eb724c12004dfa724c12004df8724c120007e8724c12000efb624c12000feb624c12028f7b524c12000779524c12005fdb324c12005fea324c120007d9324c12005fe9324c120007c9324c120005fb714c120006fb614c12005fdb314c120007d9314c120007eb214c120007e9214c120024fe76d91100457e75d91100057d75d911003ebe64d9110277f010d9110004ff75d911002cfe75d91100067e75d911002c7e75d9110004fd75d91100067d75d91100047d75d911002cfc75d911011cfd74d911003e7e54d911003e7c54d911001cfe73d9110004fd73d911001cfc73d911004cfe72d9110004fd72d91100067f52d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110286bf41d9110286bd41d9110286f621d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110276bf40d9110276bd40d9110276fa20d9110024ff76591100057f75591100457c755911003ebc645911003f3c545911026df7715911027dfb705911011ff01059110004ff75591100067f75591100047f755911002cfe7559110004fd755911002cfc75591100067c755911002c7c7559110274ff7459110006bf7459110006bf545911003e7e545911003e7c545911003ebc545911003e3c5459110004ff735911001cfe735911001cfc735911003ebf4359110004ff725911004cfc72591100067f525911003ebf425911026cff7159110006f771591100b6f6215911011cff7059110006fb705911011efa205911001cfe76d8d10036de63d8d10257f010d8d10004ff75d8d1002cfe75d8d10004fd75d8d1002cfc75d8d10024fe74d8d10004fd74d8d10024fc74d8d100067e54d8d100067c54d8d10104fd73d8d10036de43d8d1004cfe72d8d10004fd72d8d100067f52d8d10036dc32d
  | 3 => 0x820549201b77a1054920024ff765092000cfe7650920174fd765092000cfc76509200057f755092006d7c7550920006bf6450920026bc64509200076d5250920005fb705092000df870509202d5ee768c92004eee768c92004f6e758c92004f6d758c9202cf6e548c9202cf6c548c920135ed738c92001eee638c92001eec638c920005ed718c92004feb708c92000dee708c92000dec708c92004fe8708c92004eef608c92004feb608c920157ea408c920157ea308c920157ea108c92001cff764c92000cfe764c920134fd764c92000cfc764c920006df634c92001edc634c9202c76f524c9200076d524c92004fcc324c920005fb704c92000df8704c92004fe8204c92000dec764c92001eec764c92000cec764c9202bf6e544c9202bf6c544c92004def734c92004fcf734c920007cf634c92001eee634c92001eec634c92005fcc634c92005fce434c920007cd434c920005ef714c92005fcf314c920007eb704c92000dee704c92000dec704c920137e8704c92004eef604c92004feb604c920137ea404c920137cf304c920137ea304c920137cd304c920137ea104c920014fe76d8520056f661d8520004ff75d852002cfe75d8520004fd75d852002cfc75d8520024fe74d8520004fd74d8520024fc74d85200067e54d85200067c54d852001cfe73d8520004fd73d852001cfc73d852000cfd72d8520014fc72d85200067f52d85200067d52d8520006ee32d8520006ed32d8520006f731d8520056f431d8520056f621d852000cfe70d852004cfd70d852000cfc70d85200e6fa30d85200e6f710d8520005df735852005ddc7358520056f46158520004ff7650520004fe7650520004fc76505200057f755052006d7c7550520026be6450520006bd64505200673c545052000dfa7050520004ff764c520004fe764c520004fc764c52001ede634c520006dd634c520007cd324c520016f6614c520057d4314c52000dfa704c520235ee76c852004eee76c852004f6e75c852004f6d75c85202b76e54c85202b76c54c852004def73c8520005ed73c8520006ef63c8520006ed63c85200c5ed71c8520016ee61c8520016ec61c852004feb70c852000dee70c852000dec70c852004fe870c852004eef60c852004feb60c85200e7ea40c85200e7ea30c85200e7ea10c852000cfc76485202af6f52485200076d5248520006f76148520016f4614852004fe42148520005fb704852000df8704852004fe8204852000dec7648520016ec764852000cec76485202a76e54485202a76c5448520005ef7348520005ed7348520006ef6348520006ed634852004def714852004fe77148520007e76148520016ee6148520016ec6148520057e46148520057e64148520007e54148520057e63148520007e53148520007eb704852000dee7048520
  | 4 => 0x8720016ec614872004fe46148720077e64148720007e54148720077e63148720007e5314872000dee704872000dec70487200c7e71048720024fe76d912006d7e75d91200057d75d9120066be64d91200673c54d9120004ff75d912002cfe75d91200067e75d912002c7e75d9120004fd75d91200067d75d91200047d75d912002cfc75d9120006bf54d91200667e54d91200667c54d9120066bc54d91200663c54d912001cfe73d9120004fd73d912001cfc73d912004cfe72d912000cfd72d912004cfc72d91200067f52d9120066bf42d9120014fe71d9120004fd71d9120014fc71d912004cff70d912004cfd70d9120196bf40d9120196bd40d91200057f755912006d7c7559120066bc64591202e5ef7259120004ff75591200067f75591200047f755912002cfe7559120004fd755912002cfc75591200067c755912002c7c7559120194ff7459120006bf74591200667e54591200667c5459120004ff735912001cfe735912001cfc7359120066bf43591202e4ff7259120006ef72591200067f5259120004ff7159120014fe7159120014fc7159120066bf4159120174ff7059120006fb705912001cfe76d8d2005ede63d8d20004ff75d8d2002cfe75d8d20004fd75d8d2002cfc75d8d20024fe74d8d20004fd74d8d20024fc74d8d200067e54d8d200067c54d8d2004cfe72d8d2000cfd72d8d2004cfc72d8d200067f52d8d2005edf32d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d2005edc31d8d2004cff70d8d2004cfd70d8d20156df30d8d20156dd30d8d20156fa10d8d2005edc6358d202ddef7258d20005f77158d20055f47158d20004ff7558d2002cfe7558d20004fd7558d2002cfc7558d20004ff7458d20024fe7458d20024fc7458d200067e5458d200067c5458d20154ff7358d20006df7358d202dcff7258d20006ef7258d200067f5258d20004ff7158d20006f77158d20004f77158d20014fe7158d20014fc7158d20006f47158d20014f47158d2005edf3158d20134ff7058d20006fb7058d20136fa1058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d2006d7c7550d20026be6450d20006bd6450d200673c5450d2000dfa7050d2002e7f76549201b67e76549201b67d765492002e7c76549200073f74549200657e74549200657c74549200073c74549200653c74549200067f64549201ce7e64549200067d64549201ce7c64549200067f63549201c67e63549200067d63549201c67c635492004d7f725492006f6f725492004e7f625492004f6e425492004f6e32549201be7e61549201be7c615492004f6f21549200077b70549201b778705492004e7f60549201b77a40549201b77a305492004f7b20549201b76e205492004f6c205492004f78205492004f6
  | 5 => 0x1b67d40597201b67c40597201b67f30597201b67e30597201b67d30597201b67c305972004e7f205972004e7e205972004e7d205972004e7c20597201b67f10597201b67e10597201b67d10597201b67c1059720004ff75593200067f75593200047f755932002cfe7559320004fd755932002cfc75593200067c755932002c7c755932004ebf74593200867e54593200867c5459320004ff735932001cfe735932001cfc7359320086bf435932004cff725932000cfe725932004cfd725932000cfc725932004e7f525932004e7d525932004ebe425932004ebc4259320004ff7159320014fe7159320014fc7159320086bf4159320176bf4059320176bd405932004efa205932004ef92059320004ff7558f2002cfe7558f20004fd7558f2002cfc7558f20004ff7458f20024fe7458f20024fc7458f200067e5458f200067c5458f2004edf7358f2007ede4358f2004cff7258f2000cfe7258f2004cfd7258f2000cfc7258f2004e7f5258f2004e7d5258f2004ede3258f2004edc3258f20004ff7158f20014fe7158f20014fc7158f2007edf3158f2004eef2158f20136df3058f20136dd3058f2004efa2058f2004ef92058f20004ff7650f2004cfe7650f20004fd7650f2004cfc7650f200057f7550f2008d7c7550f201e67e6550f200067d6550f20026be6450f20006bd6450f200873c5450f2001ede6350f20006dd6350f2004def764cb20306ef764cb2004f6e654cb2004f6d654cb202ff6e544cb202ff6c544cb2004fcf734cb2004fcf634cb2001eee634cb2004eec634cb2004fcc634cb2007fce434cb20007cd434cb20005ef714cb2007fcf314cb2000dee704cb2000dec704cb20137cf304cb20137cd304cb20004ff755872002cfe7558720004fd755872002cfc7558720004ff7458720024fe7458720024fc74587200067e54587200067c5458720004ff735872001cfe735872001cfc735872000cfe7258720014fd725872000cfc725872004e7f525872004e7d525872004eee3258720006ed325872004ef77158720076f64158720076f6315872004ef7215872004ef4215872004efa205872004ef920587200c6f71058720004ff7650720004fd765072004cfc76507200057f755072008d7c755072012e7e65507200067d6550720026be6450720006bd64507200873c5450720016f66150720006f56150720004ff764c720004fd764c72004cfc764c7201167e654c7200067d654c72001ede634c720006dd634c72004dee724c720007cd324c720016f6614c720006f5614c720077d4314c720005fb704c72000df8704c72004def76487202f6ef764872004f6e654872004f6d65487202ef6e54487202ef6c5448720005ef7348720005ed734872004eef6348720006ed634872004fe7714872004fe76148720016ee614
  | 6 => 0xe6450930006bd64509300076d5250930177d8305093000ddc764c93004edc764c93000cdc764c930006df644c930006dd644c9303375e544c9303375c544c93001ddf724c93001fcf724c930007cf624c93004ede624c93004edc624c930007cc624c93032f5f524c9300075d524c930005df714c930007db704c93000dde704c93000ddc704c930137d8704c93000dd8704c93001edf604c93001fdb604c930137da204c930137da104c930014fe76d8530096f661d853024fd830d8530004ff75d853002cfe75d8530004fd75d853002cfc75d8530024fe74d8530004fd74d8530024fc74d85300067e54d85300067c54d853000cfd73d8530014fc73d853004cfe72d8530004fd72d85300067f52d85300067d52d8530326df32d8530006dd32d8530096f641d8530096f631d8530326f531d8530096f421d853001cfd70d853024efa20d853024ef710d8530096f4615853031dfb7058530107d83058530004ff7650530004fe7650530004fc76505300057f75505300a57c7550530026be6450530006bd645053009f3c5450530006f76150530016f4615053011fd8305053000ddc764c530016dc764c53000cdc764c5303175e544c5303175c544c530005df724c530006df624c53030f5f524c5300075d524c53001ddf714c53001fd7714c530007d7614c530016de614c530016dc614c530097d4614c530016d4614c530097d6214c530007db704c53000dde704c53000ddc704c530107d8704c53000dd8704c53001edf604c53001fdb604c530107da204c530107d7104c530107da104c530004fe76c8530004fd76c853004cfc76c85300a57e75c85300057d75c853001dde73c8530005dd73c853004eee62c8530007cd32c8530006f761c8530016f461c853000dfa70c8530005f970c85300e7d830c8530004ff7648530004fe7648530004fc764853001dde7348530005dd7348530007cd3248530016f66148530007d5314853000dfa70485300c7d830485300067f74597200063f74597200067e74597200247e74597200067d74597200067c74597200247c74597200063c74597200243c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067e43597200067c435972004e7f725972004c7f725972004e7e725972004e7d725972004c7d725972004e7c725972004e7f425972004e7e425972004e7d425972004e7c425972004e7f325972004e7e325972004e7d325972004e7c32597200067f71597200067e71597200067d71597200067c71597200067f41597200067e41597200067c41597200067f31597200067e31597200067c315972004e7f215972004e7e215972004e7d215972004e7c21597201b67f70597201b67e70597201b67d70597201b67c70597201b67f40597201b67e4059720
  | 7 => 0x8540005f970c8540004ff7648540004fe7648540004fc76485400067f65485400de7c6548540025be7448540005bd74485400d73c5448540016f66148540007b54148540024fe76d91300a57e75d91300057d75d913009ebe64d913034fd830d9130004ff75d913002cfe75d91300067e75d913002c7e75d9130004fd75d91300067d75d91300047d75d913002cfc75d91301d4fd74d913009e7e54d913009e7c54d913000cff73d913001cfe73d913000cfd73d913001cfc73d913035ebf43d913035ebd43d913004cfe72d9130004fd72d91300067f52d913035edf32d9130014fe71d9130004fd71d9130014fc71d913001cff70d913001cfd70d913034ebf40d913034ebd40d913034efa20d9130024ff76591300057f75591300a57c755913009ebc645913009f3c5459130345df7359130355fb70591301d7d83059130004ff75591300067f75591300047f755913002cfe7559130004fd755913002cfc75591300067c755913002c7c755913034cff7459130006bf7459130006bf545913009e7e545913009e7c545913009ebc545913009e3c5459130344ff7359130006df7359130004ff725913004cfc72591300067f525913009ebf42591300bedf3259130004ff7159130014fe7159130014fc715913009ebf41591301d4ff7059130006fb70591301d6fa205913004cfe76d89302dfd830d8930004ff75d893002cfe75d8930004fd75d893002cfc75d8930024fe74d8930004fd74d8930024fc74d89300067e54d89300067c54d893000cfd73d89300067f52d893033eee32d893033eed32d8930014fe71d8930004fd71d8930014fc71d893033edf31d893001cfd70d89302deef20d89302defa10d89300a57e75989300057d7598930006ef629893005df97098930157d83098930005f77158930095f4715893007dfb7058930137d830589300a57e75189300057d751893009dbe7418930005bd741893004eee6218930006ed6218930095f67118930005f571189302d7d830189300067f76549300067e76549300067d76549300067c76549300073f745493009d7e745493009d7c74549300073c745493009d3c74549300067f64549301ce7e64549300067d64549301ce7c64549301b67f635493022d7f72549300a76f72549300067f625493004e7e625493004e7c62549301c75f32549301be7e61549301be7c61549301c75f31549301b67f60549301c77b30549301b75e30549301b75c30549301b77830549301b75830549301b77a20549301b77a1054930004fe7690930004fd769093004cfc76909300a57e75909300057d759093009f3c549093001dde7390930005dd73909300076d529093000dfa7090930005f97090930197d83090930004ff7650930004fe7650930004fc76509300057f75509300a57c7550930026b
  | 8 => 0xaf6f72549400067f625494004e7e625494004e7c62549401cf3f42549401cf6e42549401cf6d42549401be7e61549401be7c61549401cf3f41549401b77a70549400077970549401b67f60549401cf7b40549401b73e40549401b73c40549401b77840549401b77a205494000dbc765094004ebc765094000cbc76509400073f75509400adbe75509400adbc755094037f3c75509400ad3c75509400073f655094037f3c6550940005bf7350940006bf6350940025bf7250940027af7250940007af625094004ebe625094004ebc6250940007ac625094037f3f525094037fae52509400073d525094037fad52509400072d5250940005bf7150940007bb705094000dbe705094000dbc7050940177b87050940026bf6050940027bb6050940177ba505094037fb95050940177ba2050940004fe768c940004fd768c94004cfc768c9400ad7e758c9400057d758c9400067f658c94016e7c658c940025be748c940005bd748c9401673c548c94000dfa708c940005f9708c940004ff764c940004fe764c940004fc764c9400067f654c94014e7c654c940025be744c940005bd744c9401473c544c94001ede634c9400079d434c940014fe76d85400067f65d85400067c65d85403773c54d85400b6f661d8540004ff75d854002cfe75d8540004fd75d854002cfc75d854000cfd74d8540014fc74d8540006bf54d85403767e54d85403767c54d8540376bc54d85403763c54d854001cfe73d8540004fd73d854001cfc73d8540376bf43d8540006bd43d854004cfe72d8540004fd72d85400067f52d85400067d52d8540376bf42d8540006bd42d85400b6f641d8540376f541d8540024fd70d854026efa20d854026ef710d85400057f75585400ad7c75585400067f65585400067c655854003f3c54585400b6f4615854036dfb705854000dbc7650540016bc765054000cbc76505400073f75505400adbe75505400adbc75505403673c75505400ad3c75505400073f655054012ebe655054012ebc65505403673c655054012e3c6550540005bf7350540006bf6350540005bf7250540006bf62505403673f52505400073d5250540025bf7150540027b77150540007b76150540016be6150540016bc61505400b7b461505400b7b65150540367b551505400b7b62150540007bb705054000dbe705054000dbc705054011fb87050540026bf6050540027bb605054011fba5050540367b9505054011fba2050540004ff764c540004fe764c540004fc764c5400067f654c5401167c654c540025be744c540005bd744c54010f3c544c5400b7d4314c540005fb704c54000df8704c540004fe76c8540004fd76c854004cfc76c85400ad7e75c85400057d75c85400067f65c85400fe7c65c8540025be74c8540005bd74c85400f73c54c854000dfa70c
  | 9 => 0xe41d95403b67d41d95403b67c41d95400067f31d95400067e31d95400067c31d95400067e21d95400067c21d95403ae7f70d95403ae7e70d95403ae7d70d95403ae7c70d95403ae7f40d95403ae7e40d95403ae7d40d95403ae7c40d95403ae7f30d95403ae7e30d95403ae7d30d95403ae7c30d95403ae7f20d95403ae7e20d95403ae7d20d95403ae7c20d95403ae7f10d95403ae7e10d95403ae7d10d95403ae7c10d954001cfe76d8d400067f65d8d400067c65d8d403a73c54d8d400bede63d8d40004ff75d8d4002cfe75d8d40004fd75d8d4002cfc75d8d4000cfd74d8d4001cfc74d8d40006bf54d8d403a67e54d8d403a67c54d8d403a6bc54d8d403a63c54d8d400bede43d8d403a6dd43d8d4004cfe72d8d40004fd72d8d400067f52d8d403a6bf42d8d40014fe71d8d40004fd71d8d40014fc71d8d403a6bf41d8d40024fd70d8d40346df30d8d40346fa20d8d400057f7558d400ad7c7558d400067f6558d400067c6558d4009f3c5458d400bedc6358d4039dfb7058d4000dbc7650d4001ebc7650d4000cbc7650d400073f7550d400adbe7550d400adbc7550d403973c7550d400ad3c7550d400073f6550d401e6be6550d401e6bc6550d403973c6550d401e63c6550d40025bf7350d400279f7350d400079f6350d4001ebe6350d4001ebc6350d400bf9c6350d400bf9e5350d403979d5350d40005bf7250d403973f5250d400bf9f3250d40005bf7150d40007bb7050d4000dbe7050d4000dbc7050d401d7b87050d40026bf6050d40027bb6050d401d7ba5050d40397b95050d401d7ba2050d4004cfe76d89400ad7c75d89400067f65d89400067c65d894038f3c54d8940004ff75d89400067f75d894002cfe75d8940004fd75d894002cfc75d89400067c75d894002c7c75d894000cfd74d894038e7e54d894038e7c54d894001cfe73d8940004fd73d894001cfc73d894038ebf43d8940006bd43d89400067f52d894038eee42d894038eed42d8940014fe71d8940004fd71d8940014fc71d894038ebf41d8940024fd70d89402e6ef20d89400ad7e75989400057d75989400067f65989400067c65989400873c5498940006ef6298940065f970989400057f75589400ad7c75589400067f65589400067c65589400673c5458940085fb70589400ad7e75189400057d75189400067f65189400067c65189403873c54189400bdde7318940005dd731894004eee6218940006ed62189400b5f67118940005f571189400067f76549400057e76549400067e76549400047e76549400067d76549400057c76549400067c76549400047c76549400073f74549400257e74549400257c74549401cf3c74549400253c74549401b67f64549400067f63549401c67e63549401c67c63549401cf3f43549400073d435494022d7f7254940
  | 10 => 0xc921007cf634c92101eee634c92101eec634c9210cfcc634c9210cfce434c921007cd434c921007e7714c921015ee714c921015ec714c92113fe4714c92104eef614c92104fe7614c92113fe6414c92113fcf314c92113fe6314c92113fcd314c921005ef704c9210cfcf304c92113fe7104c92104df47650521026f4765052104cf476505210077775505213d77475505213d6f765505213d6f56550521015f77450521017b77450521007b76450521026f66450521026f464505210d7b464505213d7b754505210d77654505210d77454505210d7b454505210d7345450521005f773505210d7b74350521007b54350521007e7725052104df6725052104df47250521007e4725052104de47250521016f76250521017e762505213d77752505210077552505210d7b74250521007b54250521007e63250521007e53250521005f770505210d7b7405052104df4764c52101ef4764c52104cf4764c521005f7744c521005f5744c5213cf76544c5213cf74544c521015f7734c521017d7734c521007d7634c52101ef6634c52101ef4634c5210cfd4634c52101ed4634c521007e7724c52104df6724c52104df4724c521007e4724c521016f7624c521017e7624c5213c777524c52100775524c5210cfd7324c5210cfe6324c521007d5324c5210cfe5324c521007c5324c521005f7704c5210cfd7304c52100cfe76d81210c6fa60d8121004ff75d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d81210067e54d81210067c54d812101cfe73d8121004fd73d812101cfc73d8121014fd72d812100cfc72d81210067f52d81210067d52d8121006ee32d8121006ed32d812104cfd71d812100cfc71d8121076f631d8121006f531d8121006fb30d81210c6f830d81210c6fa20d81210c6fa10d8121005df73581210cddc73581210c6f860581213bd7e76d95400ae7e76d954002c7e76d95400257e74d95403b73e74d95400253e74d95403af3d74d95400257c74d95400067e63d95400067c63d95403b73f43d95400057d72d95403b73f42d95400067e61d95400067c61d95403b73f41d95403b77b70d95403af7870d95403b77b40d95403af3e40d95403af3c40d95403af7840d95403af7a20d95403ae7f74d95403b67e74d95400247e74d95403b63e74d95403ae7d74d95403ae3d74d95403ae7c74d95400247c74d95400067f73d95400067e73d95400067d73d95400067c73d95403b67f43d95403b67e43d95403b67d43d95403b67c43d95400067f72d95400067e72d95400067d72d95400047d72d95400067c72d95403b67f42d95403b67e42d95403b67d42d95403b67c42d95400067f32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95403b67f41d95403b67
  | 11 => 0x47f755912102cfe7559121004fd755912102cfc75591210067c755912102c7c755912119cff7459121006bf74591210d67e54591210d67c5459121004ff735912101cfe735912101cfc73591210d6bf4359121404ff7259121006ef72591210067f525912117cff7159121006f77159121004ff705912100cfe705912100cfc70591210d6bf405912101cfe76d8d210cede63d8d21004ff75d8d2102cfe75d8d21004fd75d8d2102cfc75d8d21024fe74d8d21004fd74d8d21024fc74d8d210067e54d8d210067c54d8d21014fd72d8d210067f52d8d210cedf32d8d2104cff71d8d2104cfd71d8d2115edf31d8d2115edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d210cedc30d8d2115ef710d8d210cedc6358d213fdef7258d21005fb7058d210c5f87058d21004ff7558d2102cfe7558d21004fd7558d2102cfc7558d21004ff7458d21024fe7458d21024fc7458d210067e5458d210067c5458d2115cff7358d21006df7358d213fcff7258d21006ef7258d210067f5258d2113cff7158d21006f77158d21004ff7058d21006fb7058d21004fb7058d2100cfe7058d2100cfc7058d21006f87058d2100cf87058d210cedf3058d2113ef71058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210dd7c7550d21026be6450d21006bd6450d210d73c5450d21015f67150d2102e7f76549211be7e76549211be7d765492102e7c76549210073f74549210d57e74549210d57c74549210073c74549210d53c74549210067f64549211ce7e64549210067d64549211ce7c64549210067f63549211c67e63549210067d63549211c67c635492104d7f72549210df6f725492104e7f625492104f6e425492104f6e32549210077771549211bf74715492104e7f61549211bf7641549211bf76315492104f7721549211bf6e215492104f6c215492104f74215492104f6421549211b67e60549211b67c605492104f6f20549211bf771054921024ff7650921014fe765092117cfd7650921014fc76509210057f75509210dd7c7550921006bf6450921026bc64509210076d5250921005f77150921015f471509213f5ee768c92104eee768c92104f6e758c92104f6d758c9213ef6e548c9213ef6c548c92113ded738c92101eee638c92101eec638c92104fe7718c921015ee718c921015ec718c92104fe4718c92104eef618c92104fe7618c92115fe6418c92115fe6318c921005ed708c92115fe7108c92101cff764c921014fe764c92113cfd764c921014fc764c921006df634c92101edc634c9213e76f524c9210076d524c92104fcc324c921005f7714c921015f4714c92104fe4214c921015ec764c92101eec764c921014ec764c9213df6e544c9213df6c544c92104def734c92104fcf734
  | 12 => 0xd215972104e7c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067e40597210067c40597210067f30597210067e30597210067c305972104e7f205972104e7e205972104e7d205972104e7c20597211be7f10597211be7e10597211be7d10597211be7c1059721004ff75593210067f75593210047f755932102cfe7559321004fd755932102cfc75593210067c755932102c7c755932104ebf74593210f67e54593210f67c5459321004ff735932101cfe735932101cfc73593210f6bf4359321014fe7259321014fc725932104e7f525932104e7d525932104ebe425932104ebc425932117ebf415932117ebd415932104ef6215932104ef52159321004ff705932100cfe705932100cfc70593210f6bf4059321004ff7558f2102cfe7558f21004fd7558f2102cfc7558f21004ff7458f21024fe7458f21024fc7458f210067e5458f210067c5458f2104edf7358f210eede4358f21014fe7258f21014fc7258f2104e7f5258f2104e7d5258f2104ede3258f2104edc3258f2113edf3158f2113edd3158f2104ef62158f2104ef52158f21004ff7058f2100cfe7058f2100cfc7058f210eedf3058f2104eef2058f21004ff7650f2104cfe7650f21004fd7650f2104cfc7650f210057f7550f210fd7c7550f211e67e6550f210067d6550f21026be6450f21006bd6450f210f73c5450f2101ede6350f21006dd6350f2104def764cb21416ef764cb2104f6e654cb2104f6d654cb2140f6e544cb2140f6c544cb2104fcf734cb2104fcf634cb2101eee634cb2104eec634cb2104fcc634cb210efce434cb21007cd434cb21015ee714cb21015ec714cb2113fcf314cb2113fcd314cb21005ef704cb210efcf304cb21004ff755832102cfe7558321004fd755832102cfc7558321004ff7458321024fe7458321024fc74583210067e54583210067c5458321004ff735832101cfe735832101cfc7358321014fe725832100cfd7258321014fc725832104e7f525832104e7d525832104eee3258321006ed325832104ef6215832104ef5215832104efb70583210e6fa40583210e6fa305832104efb205832104ef820583210e6fa1058321024fe76d91210dd7e75d91210057d75d91210d6be64d91210d73c54d9121004ff75d912102cfe75d91210067e75d912102c7e75d9121004fd75d91210067d75d91210047d75d912102cfc75d9121006bf54d91210d67e54d91210d67c54d91210d6bc54d91210d63c54d912101cfe73d9121004fd73d912101cfc73d9121014fd72d91210067f52d91210d6bf42d912104cff71d912104cfd71d912119ebf41d912119ebd41d912100cfe70d9121004fd70d912100cfc70d91210057f75591210dd7c75591210d6bc6459121405ef7259121004ff75591210067f7559121
  | 13 => 0x893100cfe70d8931004fd70d893100cfc70d8931436df30d89313fef710d89311157e75989310057d7598931006ef62989310cdf5719893115fd431989310edf7715893113fd43158931005fb7058931105f870589311157e75189310057d751893110dbe7418931005bd741893104eee6218931006ed62189313f7d43118931105fa7018931005f970189310067f76549310067e76549310067d76549310067c76549310073f745493110d7e745493110d7c74549310073c745493110d3c74549310067f64549311ce7e64549310067d64549311ce7c64549311be7f635493142d7f72549311176f72549310067f625493104e7e625493104e7c62549311c75f32549311be7f61549311c77731549311bf5e31549311bf5c31549311bf7431549311bf5431549311bf7621549311b67e60549311b67c60549311c75f30549311bf771054931004fe7690931004fd769093104cfc76909311157e75909310057d759093110f3c549093101dde7390931005dd73909310076d5290931015f67190931005f5719093119fd43190931004ff7650931004fe7650931004fc76509310057f75509311157c7550931026be6450931006bd64509310076d525093117fd43150931015dc764c93104edc764c931014dc764c931006df644c931006dd644c9314275e544c9314275c544c93101ddf724c93101fcf724c931007cf624c93104ede624c93104edc624c931007cc624c93141f5f524c9310075d524c931007d7714c931015de714c931015dc714c93113fd4714c931015d4714c93101edf614c93101fd7614c93113fd6214c931005df704c93113fd7104c93100cfe76d813125fd431d8131106fa60d8131004ff75d813102cfe75d8131004fd75d813102cfc75d8131024fe74d8131004fd74d8131024fc74d81310067e54d81310067c54d8131014fd73d813100cfc73d813104cfe72d8131004fd72d81310067f52d81310067d52d813131edf32d8131006dd32d813101cfd71d813125ef621d8131106fa40d8131106fa30d8131106f820d8131106fa10d8131097d43158131106f860581310067f74597210063f74597210067e74597210247e74597210067d74597210067c74597210247c74597210063c74597210243c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067e43597210067c435972104e7f725972104e7e725972104e7d725972104e7c725972104e7f425972104e7e425972104e7d425972104e7c425972104e7f325972104e7e325972104e7d325972104e7c32597211be7f71597211be7e71597211be7d71597211be7c71597211be7f41597211be7e41597211be7d41597211be7c41597211be7f31597211be7e31597211be7d31597211be7c315972104e7f215972104e7e215972104e7
  | 14 => 0x12d3c75509410073f655094145f3c6550941005bf7350941006bf6350941025bf7250941027af7250941007af625094104ebe625094104ebc6250941007ac625094145f3f525094145fae52509410073d525094145fad52509410072d5250941007b77150941015be7150941015bc715094117fb47150941026bf6150941027b7615094117fb6515094145fb5515094117fb62150941005bf7050941004fe768c941004fd768c94104cfc768c94112d7e758c9410057d758c9410067f658c94116e7c658c941025be748c941005bd748c9411673c548c941015f6718c941005f5718c941004ff764c941004fe764c941004fc764c9410067f654c94114e7c654c941025be744c941005bd744c9411473c544c94101ede634c9410079d434c94100cfe76d81410067f65d81410067c65d814136f3c54d814111efa60d8141004ff75d814102cfe75d8141004fd75d814102cfc75d8141014fd74d814100cfc74d8141006bf54d814136e7e54d814136e7c54d814136ebc54d814136e3c54d814101cfe73d8141004fd73d814101cfc73d814136ebf43d8141006bd43d814104cfe72d8141004fd72d81410067f52d81410067d52d814136ebf42d8141006bd42d8141024fd71d814127ef621d814111efa40d814111efa10d81410057f755814112d7c75581410067f65581410067c655814103f3c545814111ef86058141024fe76d91311157e75d91310057d75d913110ebe64d9131447d431d9131004ff75d913102cfe75d91310067e75d913102c7e75d9131004fd75d91310067d75d91310047d75d913102cfc75d91311dcfd74d913110e7e54d913110e7c54d9131014ff73d9131014fd73d9131456bf43d9131456bd43d913104cfe72d9131004fd72d91310067f52d9131456df32d913101cff71d913101cfd71d9131446bf41d9131446bd41d9131446f621d913100cfe70d9131004fd70d913100cfc70d9131024ff76591310057f75591311157c755913110ebc645913110f3c545913143ddf735913144df771591311dfd43159131004ff75591310067f75591310047f755913102cfe7559131004fd755913102cfc75591310067c755913102c7c7559131444ff7459131006bf7459131006bf545913110e7e545913110e7c545913110ebc545913110e3c545913143cff7359131006df7359131004ff725913104cfc72591310067f525913110ebf4259131126df32591311dcff7159131006f771591311def62159131004ff705913100cfe705913100cfc705913110ebf405913104cfe76d89313ffd431d8931004ff75d893102cfe75d8931004fd75d893102cfc75d8931024fe74d8931004fd74d8931024fc74d89310067e54d89310067c54d8931014fd73d89310067f52d8931436ee32d8931436ed32d893101cfd71d89313feef21d
  | 15 => 0xf10d954148e7e10d954148e7d10d954148e7c10d954101cfe76d8d410067f65d8d410067c65d8d414873c54d8d41126de63d8d41004ff75d8d4102cfe75d8d41004fd75d8d4102cfc75d8d41014fd74d8d41006bf54d8d414867e54d8d414867c54d8d41486bc54d8d414863c54d8d41126de43d8d41486dd43d8d4104cfe72d8d41004fd72d8d410067f52d8d41486bf42d8d41024fd71d8d4143edf31d8d4143ef621d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41486bf40d8d410057f7558d4112d7c7558d410067f6558d410067c6558d4110f3c5458d41126dc6358d4147df77158d41015bc7650d4101ebc7650d41014bc7650d410073f7550d4112dbe7550d4112dbc7550d414773c7550d4112d3c7550d410073f6550d411e6be6550d411e6bc6550d414773c6550d411e63c6550d41025bf7350d410279f7350d410079f6350d4101ebe6350d4101ebc6350d411279c6350d411279e5350d414779d5350d41005bf7250d414773f5250d411279f3250d41007b77150d41015be7150d41015bc7150d411dfb47150d41026bf6150d41027b76150d411dfb65150d41477b55150d411dfb62150d41005bf7050d4104cfe76d894112d7c75d89410067f65d89410067c65d894146f3c54d8941004ff75d89410067f75d894102cfe75d8941004fd75d894102cfc75d89410067c75d894102c7c75d8941014fd74d894146e7e54d894146e7c54d894101cfe73d8941004fd73d894101cfc73d894146ebf43d8941006bd43d89410067f52d894146eee42d894146eed42d8941024fd71d8941406ef21d894100cfe70d8941004fd70d894100cfc70d894146ebf40d894112d7e75989410057d75989410067f65989410067c65989410f73c5498941006ef62989410d5f571989410057f755894112d7c75589410067f65589410067c65589410d73c54589410f5f7715894112d7e75189410057d75189410067f65189410067c65189414673c5418941125de7318941005dd731894104eee6218941006ed621894111dfa7018941005f970189410067f76549410057e76549410067e76549410047e76549410067d76549410057c76549410067c76549410047c76549410073f74549410257e74549410257c74549411cf3c74549410253c74549411be7f64549410067f63549411c67e63549411c67c63549411cf3f43549410073d435494142d7f725494112f6f72549410067f625494104e7e625494104e7c62549411cf3f42549411cf6e42549411cf6d42549411bf7671549410077571549411be7f61549411cf7741549411bf3e41549411bf3c41549411bf7441549411bf7621549411b67e60549411b67c60549411cf3f4054941015bc765094104ebc7650941014bc76509410073f755094112dbe755094112dbc755094145f3c7550941
  | 16 => 0x49321457c74549320073c74549321453c74549320067f64549321ce7e64549320067d64549321ce7c64549320075f73549321c75c735493204e7f63549321c75e43549320075d435493204d7f725493214f6f725493204e7f625493204f6e42549321c76f325493204f5e325493204f5c325493204f6c325493204f4c32549321be7e61549321be7c61549321c75f315493204f6f21549321b67e60549321b67c60549321c75f305493204f6f2054932024ff765093201cfe7650932184fd765093201cfc76509320057f755093214d7c7550932006bf6450932026bc6450932005df735093201ddc73509320079d43509320076d5250932014fe76d853213ef661d8532004ff75d853202cfe75d8532004fd75d853202cfc75d8532024fe74d8532004fd74d8532024fc74d85320067e54d85320067c54d853204cfd73d853201cfd72d85320067f52d85320067d52d853213ef631d853213ef621d853200cfe70d8532004fd70d853200cfc70d85320eedf30d8532006f610d853213ef410d853213ef46158532005fb7058532135f8705853200cfe76d8132136fa60d8132004ff75d813202cfe75d8132004fd75d813202cfc75d8132024fe74d8132004fd74d8132024fc74d81320067e54d81320067c54d813204cfd73d813201cfd72d81320067f52d81320067d52d8132014fe71d8132004fd71d8132014fc71d813207edf31d8132136fa30d8132136fa20d8132006fb10d8132136f810d8132005f7715813213df47158132136f8605813249d7e76d954112e7e76d954102c7e76d95410257e74d95414973e74d95410253e74d954148f3d74d95410257c74d95410067e63d95410067c63d95414973f43d95410057d72d95414973f42d95414977771d954148f7471d95414977741d954148f3e41d954148f3c41d954148f7441d954148f7621d95410067e60d95410067c60d95414973f40d954148e7f74d95414967e74d95414963e74d954148e7d74d954148e3d74d954148e7c74d95410067f73d95410067e73d95410067d73d95410067c73d95414967f43d95414967e43d95414967d43d95414967c43d95410067f72d95410067e72d95410067d72d95410047d72d95410067c72d95414967f42d95414967e42d95414967d42d95414967c42d95410067f32d95410067c32d954148e7f71d954148e7e71d954148e7d71d954148e7c71d954148e7f41d954148e7e41d954148e7d41d954148e7c41d954148e7f31d954148e7e31d954148e7d31d954148e7c31d954148e7f21d954148e7e21d954148e7d21d954148e7c21d95410067f70d95410067e70d95410067d70d95410067c70d95414967f40d95414967e40d95414967d40d95414967c40d95410067f30d95410067e30d95410067c30d95410067e20d95410067c20d954148e7
  | 17 => 0x2cfc75592320067c755923202c7c755923204ebf74592321667e54592321667c5459232186bf4359232186bd435923204cfe725923204cfc725923204e7f525923204e7d525923204ebe425923204ebc425923204edf325923204edd3259232004ff7159232014fe7159232014fc7159232166bf4159232004ff705923200cfe705923200cfc7059232166bf4059232004ff755863202cfe7558632004fd755863202cfc7558632004ff7458632024fe7458632024fc74586320067e54586320067c545863204cfe725863204cfc725863204e7f525863204e7d525863204edf325863204edd325863204ef7715863215ef6415863215ef6315863204ef7215863204ef42158632004ff705863200cfe705863200cfc705863204eef205863215ef71058632004ff755823202cfe7558232004fd755823202cfc7558232004ff7458232024fe7458232024fc74582320067e54582320067c545823204cfe725823204cfc725823204e7f525823204e7d525823204edf325823204edd3258232004ff7158232014fe7158232014fc715823204eef215823204efb7058232156fa4058232156fa305823204efb205823204ef82058232156fa1058232024fe76d913214d7e75d91320057d75d9132146be64d91321473c54d9132004ff75d913202cfe75d91320067e75d913202c7e75d9132004fd75d91320067d75d91320047d75d913202cfc75d9132006bf54d91321467e54d91321467c54d9132146bc54d91321463c54d913204cff73d913204cfd73d91321a6bf43d91321a6bd43d913201cfd72d91320067f52d9132146bf42d9132014fe71d9132004fd71d9132014fc71d913200cfe70d9132004fd70d913200cfc70d91320057f755913214d7c7559132146bc64591324adef7259132004ff75591320067f75591320047f755913202cfe7559132004fd755913202cfc75591320067c755913202c7c75591321a4ff7459132006bf74591321467e54591321467c5459132184ff7359132006df73591324acff7259132006ef72591320067f5259132004ff7159132014fe7159132014fc7159132146bf4159132004ff705913200cfe705913200cfc7059132146bf405913204ddc7650d32026dc7650d3204cdc7650d320075f7550d324a75c7550d324a6df6550d324a6dd6550d3201ddf7450d3201f9f7450d320079f6450d32026de6450d32026dc6450d321479c6450d324a79f5450d321475e5450d321475c5450d321479c5450d321471c5450d32007cf7250d3204dde7250d3204ddc7250d32007cc7250d3204dcc7250d3201edf6250d3201fcf6250d324a75f5250d321479f4250d32005df7150d321479f4150d32005df7050d321479f4050d3202e7f76549321c67e76549321c67d765493202e7c76549320073f74549321457e745
  | 18 => 0xc73549420076f63549424c76e63549420076d63549424c76c63549421cf6f43549421cf2f43549421cf6e43549421cf6d43549420072d43549421cf6c43549420076f71549424bf6e71549420076d71549424bf6c71549424bf6e61549424bf6c61549421cf6f41549421cf2f41549421cf6e41549421cf6c41549424c76f31549424bf6e31549424bf6c31549420076f70549424b76e70549420076d70549424b76c70549424b76e60549424b76c60549421cf6f40549421cf2f40549421cf6e40549421cf6c40549424c76f30549424b76e30549424b76c30549424bf6f10549424b76e10549424b76c1054942014fe76d85420067f65d85420067c65d85420076d52d854217ef661d8542004ff75d854202cfe75d8542004fd75d854202cfc75d854204cfd74d85420f67e54d85420f67c54d854201cfe73d8542004fd73d854201cfc73d85420f6bf43d8542006bd43d8542024fd72d85420067f52d85420067d52d854217ef641d854217ef621d854200cfe70d8542004fd70d854200cfc70d85420f6bf40d85420057f755854218d7c75585420067f65585420067c65585420076d525854217ef4615854200cfe76d81420067f65d81420067c65d81420076d52d8142176fa60d8142004ff75d814202cfe75d8142004fd75d814202cfc75d814204cfd74d81420867e54d81420867c54d814201cfe73d8142004fd73d814201cfc73d8142086bf43d8142006bd43d8142024fd72d81420067f52d81420067d52d8142014fe71d8142004fd71d8142014fc71d8142086bf41d8142176fa40d8142176fa20d81420057f755814218d7c75581420067f65581420067c65581420076d5258142176f860581420067f74596320063f74596320067e74596320247e74596320067d74596320067c74596320247c74596320063c74596320243c74596321c67f73596321c67e73596321c67d73596321c67c73596321c67f43596321c67e43596321c67d43596321c67c435963204e7f725963204e7e725963204e7d725963204e7c725963204e7f425963204e7e425963204e7d425963204e7c425963204e7f325963204e7e325963204e7d325963204e7c32596320067f71596320067e71596320067d71596320067c71596320067f41596320067e41596320067c41596321c67f31596321c67e31596321c67d31596321c67c315963204e7f215963204e7e215963204e7d215963204e7c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067c40596321c67f30596321c67e30596321c67d30596321c67c305963204e7f205963204e7e205963204e7d205963204e7c20596320067f10596320067e10596320067c1059632004ff75592320067f75592320047f755923202cfe7559232004fd7559232
  | 19 => 0x95420067e73d95420067d73d95420067c73d95424e67f43d95424e67e43d95424e67d43d95424e67c43d95424e67f72d95424de7e72d95424e67d72d95420247d72d95424de7c72d95424e67f42d95424de7e42d95424e67d42d95424de7c42d95420067f32d95424de7e32d95424de7c32d95420067f71d95420067e71d95420067d71d95420067c71d95424e67f41d95424e67e41d95424e67d41d95424e67c41d95420067f31d95420067e31d95420067c31d95424de7f21d95420067e21d95424de7c21d95420067f70d95420067e70d95420067d70d95420067c70d95424e67f40d95424e67e40d95424e67d40d95424e67c40d95420067f30d95420067e30d95420067c30d95424de7f20d95420067e20d95424de7c20d95420067f10d95420067e10d95420067c10d954201cfe76d8d420067f65d8d420067c65d8d42186de63d8d42004ff75d8d4202cfe75d8d42004fd75d8d4202cfc75d8d4204cfd74d8d421667e54d8d421667c54d8d42186de43d8d42166dd43d8d42024fd72d8d420067f52d8d42186df32d8d42014fe71d8d42004fd71d8d42014fc71d8d42166bf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42166bf40d8d420057f7558d4218d7c7558d420067f6558d420067c6558d42186dc6358d424d5ef7258d4204dbc7650d4201ebc7650d4204cbc7650d420073f7550d424cf3c7550d420073f6550d421e6be6550d421e6bc6550d424cf3c6550d421e63c6550d42025bf7350d420279f7350d420079f6350d4201ebe6350d4201ebc6350d421879c6350d421879e5350d424cf9d5350d42007af7250d4204dbe7250d4204dbc7250d42007ac7250d42026bf6250d42027af6250d424cf3f5250d424cfae5250d424cfad5250d421879f3250d42005bf7150d42005bf7050d4202e7f76549421ce7e76549420247e76549421ce7d76549420257c765494202e7c76549420247c76549420073f74549420257e74549420257c74549421cf3c74549420253c745494204e7f64549420067f63549421c67e63549421c67c63549421cf3f43549420073d435494204d7f725494218f6f725494204e7f62549421cf6f425494204f3e425494204f3c425494204f6c42549424c76f325494204f6e325494204f6c32549421be7e61549421be7c61549421cf3f415494204f6f21549424bf6e215494204f6c21549421b67e60549421b67c60549421cf3f405494204f6f20549424b76e205494204f6c205494218f6f765494202e6f76549421cf6c76549420256c765494202e6c76549420246c76549421cf6f74549420072f74549421cf6e74549420256e74549421cf6d74549421cf6c74549420256c74549421cf2c745494204f6f645494204e6f645494204f2f64549420076f73549424c76e73549420076d73549424c76
  | 20 => 0x4e7f205964204e7e205964204e7d205964204e7c20596420067f10596420067e10596420067c1059642004ff7558e4202cfe7558e42004fd7558e4202cfc7558e42006bf5458e421467e5458e421467c5458e42146bc5458e421463c5458e4204edf7358e421a6de4358e42146dd4358e4204cfe7258e4204cfc7258e4204e7f5258e4204e7d5258e4204ebf4258e4204ebd4258e4204ede3258e4204edc3258e42004ff7158e42014fe7158e42014fc7158e421a6df3158e42004ff7058e4200cfe7058e4200cfc7058e421a6df3058e4204f6f7654a4204d6f7654a4250e6f7654a421cf6f7454a421af2f7454a421cf6e7454a420256e7454a421cf6d7454a421cf6c7454a420256c7454a421cf2c7454a420252c7454a421ce6d6454a420076f7354a425076e7354a420076d7354a425076c7354a4204f6f6354a4204f6e6354a4204f6d6354a4204f6c6354a421cf6f4354a421cf6e4354a421cf6d4354a421cf6c4354a420076f7154a424ff6e7154a420076d7154a424ff6c7154a4204f6f6154a4204f6e6154a4204f6d6154a4204f6c6154a421cf6f4154a421cf6e4154a421cf6c4154a425076f3154a424ff6e3154a424ff6c3154a420076f7054a424f76e7054a420076d7054a424f76c7054a4204f6f6054a4204f6e6054a4204f6d6054a4204f6c6054a421cf6f4054a421cf6e4054a421cf6c4054a425076f3054a424f76e3054a424f76c3054a424ff6f1054a424f76e1054a424f76c1054a42004ff755864202cfe7558642004fd755864202cfc7558642006bf54586420d67e54586420d67c54586420d6bc54586420d63c5458642004ff735864201cfe735864201cfc735864204cfe725864204cfc725864204e7f525864204e7d525864204ebf425864204ebd425864204ef7715864219ef6415864219ef6315864204ef7215864204ef42158642004ff705864200cfe705864200cfc705864219ef71058642004ff755824202cfe7558242004fd755824202cfc7558242006bf54582420667e54582420667c5458242066bc54582420663c5458242004ff735824201cfe735824201cfc735824204cfe725824204cfc725824204e7f525824204e7d525824204ebf425824204ebd4258242004ff7158242014fe7158242014fc715824204efb7058242196fa4058242196fa305824204efb205824204ef82058242196fa10582424ed7e76d954218e7e76d954202c7e76d95420257e74d95420257c74d95420067e63d95420067c63d95424e73f43d95424e76f72d95420257d72d95424e76c72d95424e76f42d95424df3e42d95424df3c42d95424e76c42d95420067e61d95420067c61d95424e73f41d95420067e60d95420067c60d95424e73f40d95424de7f74d95424e67e74d95424e67d74d95424e67c74d95420067f73d
  | 21 => 0xe7050d521b57c7050d521cf3f4050d521bd7e76d85521cd7e74d85520057d74d85521cd7c74d85520073f64d85520067e64d85520067c64d85520073c64d85520063c64d85521c57e73d85520057d73d85521c57c73d85520067f63d85520067d63d855204d7e72d855202d7d72d85520fe7f62d85520ff6f62d85521be7e61d85521bf7661d85521be7c61d85521bf7621d85521b57e70d85520057d70d85521b57c70d85520057f74585520073f74585520053f74585521cd7e74585521cd7c74585520073c74585521cd3c74585520073f64585520067e64585520067c64585520073c64585520063c64585520057f73585521c57e73585521c57c73585520067f63585520067d635855251d7f72585520076f725855251d6f72585520de7f62585520df6f62585521bd7f71585520077761585521be7e61585521be7c61585521bf7461585521bf7641585520057f70585521b57e70585521b57c70585521b57e76d81521cd7e74d81520057d74d81521cd7c74d81520073f64d81520067e64d81520067c64d81520073c64d81520063c64d81521c57e73d81520057d73d81521c57c73d81520067f63d81520067d63d815204d7e72d815202d7d72d815208e7f62d815208f6f62d81521bd7e71d81520057d71d81521bd7c71d81520067f61d81520067d61d81521b67e60d81521b77a60d81521b67c60d81521b77a20d81520057f74581520073f74581520053f74581521cd7e74581521cd7c74581520073c74581521cd3c74581520073f64581520067e64581520067c64581520073c64581520063c64581520057f73581521c57e73581521c57c73581520067f63581520067d63581525157f72581520076f72581525156f725815206e7f625815206f6f62581520057f71581521bd7e71581521bd7c71581520067f61581520067d61581521b57f70581520077b60581521b67e60581521b67c60581521b77860581521b77a40581521ce7f74596421ae3f74596421ce7e74596421ce7d74596421ce7c74596421ce3c74596420067f73596420067e73596420067d73596420067c73596421ce7f43596421ce7e43596421ce7d43596421ce7c435964204e7f725964204e7e725964204e7d725964204e7c725964204e7f425964204e7e425964204e7d425964204e7c425964204e7f325964204e7e325964204e7d325964204e7c32596420067f71596420067e71596420067d71596420067c71596421ce7f41596421ce7e41596421ce7d41596421ce7c41596420067f31596420067e31596420067c315964204e7f215964204e7e215964204e7d215964204e7c21596420067f70596420067e70596420067d70596420067c70596421ce7f40596421ce7e40596421ce7d40596421ce7c40596420067f30596420067e30596420067c3059642
  | 22 => 0x915254f3f20d91520073e20d915254f3c20d91520073f10d91520073e10d91520073c10d91521cd7f74591520073f64591521ce7e64591521ce7c64591521cf3c64591521ce3c64591520057f73591521c57e73591521c57c73591525457f72591520076f72591525456f725915218e7f625915218f6f62591520057f71591521bd7e71591521bd7c71591520057f70591521b57e70591521b57c70591521cf3e76191521ad3e76191521ce3e76191521cf3f73191521cf3e73191521cf1e73191521cf3d73191521cf1d73191521cf3c73191520073e63191520063e63191520073c63191520063c63191521cf3f72191525373e72191521cf3d72191521cf2d72191525373c721915250f3f621915253e3f621915250f2f62191520073f32191525373e32191525373c32191521cf3f71191521cf3e71191521cf3671191521cf3d71191521cf3571191521cf3c71191520073e61191520063e61191520073c61191520063c61191520073f31191520073e31191520073c31191525373f21191520073e21191525373c21191521cf3f70191521cf3e70191521cf3a70191521cf3d70191521cf3970191521cf3c70191520073e60191520063e60191520073c60191520063c60191520073f30191520073e30191520073c30191525373f20191520073e20191525373c20191520073f10191520073e10191520073c10191521c57e76d8d521cd7e74d8d520057d74d8d521cd7c74d8d520073f64d8d520067e64d8d520067c64d8d520073c64d8d520063c64d8d521c67e63d8d521c75e63d8d521c67c63d8d5204d7e72d8d5202d7d72d8d5216e7f62d8d5216f6f62d8d521c75f32d8d521bd7e71d8d520057d71d8d521bd7c71d8d521b57e70d8d520057d70d8d521b57c70d8d520057f7458d520073f7458d520053f7458d521cd7e7458d521cd7c7458d520073c7458d521cd3c7458d520073f6458d520067e6458d520067c6458d520073c6458d520063c6458d521c57f7358d520075f6358d521c67e6358d521c67c6358d521c75c6358d521c75e4358d5252d7f7258d520076f7258d5252d6f7258d5214e7f6258d5214f6f6258d520057f7158d521bd7e7158d521bd7c7158d520057f7058d521b57e7058d521b57c7058d520057f7650d520067f7650d520047f7650d520057e7650d520057d7650d520057c7650d520067c7650d520047c7650d521c57f7450d520073f6450d520267e6450d520267c6450d521cf3c6450d520263c6450d521c57f7350d521c75e6350d520075d6350d521cf5f4350d521c73e4350d521c73c4350d521c75c4350d520057f7250d5204d7e7250d5204d7c7250d525267f6250d521e76f6250d521cf3f4250d521c75f3250d520057f7150d521bd7e7150d521bd7c7150d521cf3f4150d520057f7050d521b57
  | 23 => 0x4d67e54d89434d67c54d8943024fd73d89430067f52d89434d6ee42d89434aeee32d8943014fe71d8943004fd71d8943014fc71d89434d6bf41d894300cfe70d8943004fd70d894300cfc70d89434d6bf40d89431e57e75989430057d75989430067f65989430067c65989431673c5498943006ef62989430057f75589431e57c75589430067f65589430067c65589431473c54589431e57e75189430057d75189430067f65189430067c65189435573c541894304eee6218943006ed62189431ddf67118943005f571189431d5fa7018943005f97018943014fe76d85430067f65d85430067c65d854347f3c54d85431def661d8543004ff75d854302cfe75d8543004fd75d854302cfc75d854301cfd74d8543006bf54d854347e7e54d854347e7c54d854347ebc54d854347e3c54d8543024fd73d854304cfe72d8543004fd72d85430067f52d854347ebf42d854344edf32d85431def641d85431def631d854300cfe70d8543004fd70d854300cfc70d854347ebf40d85430057f75585431e57c75585430067f65585430067c655854310f3c54585431def4615854300cfe76d81430067f65d81430067c65d814339f3c54d81431d6fa60d8143004ff75d814302cfe75d8143004fd75d814302cfc75d814301cfd74d8143006bf54d814339e7e54d814339e7c54d814339ebc54d814339e3c54d8143024fd73d814304cfe72d8143004fd72d81430067f52d814339ebf42d8143356df32d8143014fe71d8143004fd71d8143014fc71d814339ebf41d81431d6fa40d81431d6fa30d81430057f75581431e57c75581430067f65581430067c655814309f3c54581431d6f860581431cd7e76d91520247e76d91521ce7e64d91521cf3e64d91521ce7c64d91521c57e73d91520057d73d91521c57c73d91521cf3f43d91520073e43d91521cf3c43d91521af6f72d915204d7e72d915202d7d72d91521ae7f62d91521af6f62d91521cf3f42d91521bd7e71d91520057d71d91521bd7c71d91521cf3f41d91520073e41d91521cf3c41d91521b57e70d91520057d70d91521b57c70d91521cf3f40d91520073e40d91521cf3c40d91521cd3e76d91520243e76d91520073f73d91520073e73d91520073d73d91520073c73d91520073e63d91520073c63d91521af3f72d91521af2f72d915254f3e72d91521af3d72d915254f3c72d91521af3f62d91521ae3f62d91521af2f62d91520073f32d915254f3e32d915254f3c32d91520073f71d91520073e71d91520073d71d91520073c71d91520073e61d91520073c61d91520073f31d91520073e31d91520073c31d915254f3f21d91520073e21d915254f3c21d91520073f70d91520073e70d91520073d70d91520073c70d91520073e60d91520073c60d91520073f30d91520073e30d91520073c30d
  | 24 => 0x28008000001000000402500380180080000000014036036001001400e000001000002e014003801c054001001801000000d00080100020070000008002002011800000000000b8088002001000003400400101c80400040000008040038001000800000400b000000001a00000100300020000038024016009003002002000600280040040120098020038009000000000001300c8008000005017004400000200000000000050018004018002004003402400000280000140030010058006012000000804800400080240000000020010000000000000000400000580100020000058000046001002000c000002000801c00401a007800000c000000002400c001000001c01400000000000120030000050000002004800000000000100000000020000094000000002000c004000002000404e007000800402200b008800001c000005800803e00000000380040130008008002000001800400000800000280020010038000006001000000000000000c800400a002003805c08801c006800401a00001a000000000000180280000030018004000002005004800400000b800001e0060028008008003004800802c001001800c0100010048000000001000000000a000001800000000456d7e76d95431e67e76d954302c7e76d95430257e74d95435673e74d95430253e74d954355f3d74d95430257c74d95435675f73d954355f5c73d95435675f43d954355f3e43d954355f3c43d954355f5c43d95430057d72d95435673f42d954355f5f32d95430067e61d95430067c61d95435673f41d95430067e60d95430067c60d95435673f40d954355e7f74d95435667e74d95435663e74d954355e7d74d954355e3d74d954355e7c74d954355e7f73d954355e7e73d954355e7d73d954355e7c73d954355e7f43d954355e7e43d954355e7d43d954355e7c43d95430067f72d95430067e72d95430067d72d95430047d72d95430067c72d95435667f42d95435667e42d95435667d42d95435667c42d954355e7f32d954355e7e32d954355e7d32d954355e7c32d95430067f71d95430067e71d95430067d71d95430067c71d95435667f41d95435667e41d95435667d41d95435667c41d954355e7f31d954355e7e31d954355e7d31d954355e7c31d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95435667f40d95435667e40d95435667d40d95435667c40d954355e7f30d954355e7e30d954355e7d30d954355e7c30d95430067e20d95430067c20d95430067f10d95430067e10d95430067c10d954304cfe76d89431e57c75d89430067f65d89430067c65d89434d73c54d8943004ff75d89430067f75d894302cfe75d8943004fd75d894302cfc75d89430067c75d894302c7c75d894301cfd74d8943
  | 25 => 0x7008c0000310000068006008002000000a002004800000000000000100000090010024022001000800800a00c000801c02400a001000801400000c000c00000000a800400a0020000044000004000800000000600080000000000000004004020001000400e01300180080060020040058004000001000001400400100080040000008000000003000000c0080010008008020004010800c00000001c8008002000000001800400d001002800a00000a80880140010000000000005007000000c001000000000e003003801c008000003800000400a009801c0080010008018016002001000c01e002001000000800e00000540000070058008016000007001c020000007800c02a00200080b003a011001000000e00200000080040080048020002009007803400200a009004c00a005005000c0060070040004002017000800803a0110010038014001000000400600000100040000080030000000001000000c03a0150000000000022003005000600e01080300000030008000002005006802800c0000000000008002002000002000000180100000120010008004002004000c008001002001c00a000000800000e0030000010000000005009800a000001801001200400100000020000088000020001000003801400300000a4002004000001c000011006800000e0070020008012028000000c000005002002001000300000300040000008040000000001000c0080110008014000003001800000c000002002c002008002800c024000003800000600500480100000040008008014001007000400e00001600000020030018004000001000800800a001001801000a001001001c000008000800802e000000000001e0000068004000000003000000e005001000000e00d000000000000d00c000400c00000300bc0000060018038006003003000400000000180040000000048054008005010000803e00700000600020000150014002006000000000400300380680080010000004006003005001c0000020038068018000000809c0060020038048006001000800400c00b00080000000000020014036005000001c02e00600180000360040028000000005000007000400300e000002802300000080020030000008042002001000002c001000800800000600b00100000050058000000000004002c07a012004800400c013000001000a0170000008020000002802000c024001801c006000004800801a01100200200260050008020000005000800c00400400000400100030008000008000002800000000b002004400e008008006c0600020030004000007004002800200000000140000000000004002000006002000400000801040000000000000006003004805400600100e0028000006000000c0000040010048010001000
  | 26 => 0x4f65ab000053a8000000053c00015604d49a94000038244b989403480e0000147e0e780003d200007ce07fe714000000000003b601da4b209fc28b8a682959fd8768871813f12a87b51e4c16607d40000a482091f981470ae42260a5079f04fa32882ca4f28db6335948259a80002db0000000128a0001e5666e80000000000000000035c12e22a31770000046e4e1930e1ae95aa3d4924c6b80e7400008380001366000000000017aa5ae00005dea026316818a00e81fa3de000001e80006ee9d000000200001800021300002a71d8204b0d8e6e805ea41d800045e98cc7b600003a19c9e00000003ba994234b0d100008000014009000001c00c00000000340ae0000020028032000000001000c0080000000002000006000c00200200d000800a00400280100160000030018006004000800c00a00300000040080000018000034003000000002200100080080060000028088010004001800400000300100040000060010004000000001004000400100480280060010010008002001000000000001e000001000e00800c800000a0050020010000014001800401a00101a805c014009000001400000100200000000280000000000000000000802600300c000002800000c001800400000000080620000008008000010003002000a0110000000002001007002000c015001000000400a0000000000000002000c00000100000680000020070010016001000002400a003000805c000000019800401800000a0014002009001800000e00700200040000010000010010002001000000400d0008044008000001800004a00a0040020004002006001000001f000000400400200080000000030010020010000003000400200900000000040010008008026000004803001400000580200000000078008008001000800c01e0020020000000000013001001e00300c0010000000002006c00800000580280040090008004000002003800000200000c800000a0020000000006000001800802a000000001000800100e001401202b000000c02600300280040020000000000004001002800003e007002800c00801a017800c004000001803802e007000801c006002008001c00200a00080000060000020054022001002000c00800100000040000030050008008005006800c004004000000000a000009800c0180030020014000000006800800000b008001403e01700680000000000090000006009004802c00000000100080060400030004008006000002c000011008000001a0050010004000003000000c0120000020000006000006801400a0010080020010006001006800000200000000080000050004000003007004c01200600c812c004004000005c00400c0028004010001000001c00200200080080060000008000000007001800800
  | 27 => 0x1e08cf60959bfc4191c7631a03107d11a2021882ac48c0dc2264a02e4ef15a85bb078a000000000000007a581660000000000000041200001f800003dc000034112f80001b5e10e947c3471d2074a8000000060426b0dd2798800075c9e04761800032c8e1a7fa0000452000000000002af0000000000e000019c4a515581449a7000000001781c003d7080460d000017e000016e9c1e132000000015f27539cf430a8000000000000017001db02fc7b7810e0001eb400000000000000000000023c82320001b9c08181766d380004ff800041f800079995da2431fc43f11ad023b0ce8284078e5d1a09a43b00002ab0aa63e81884073909660f98a83450000000155a00000004f497540f4954044315780201b5882ea09072118a426c8bda2e400487470fb0467817a4d10a6a102821061e961e7c900004ee01d400011120000418023950611c8e9000009862c812d610c061e3b9848c56706ca56b94f06118c0a57b9c5c2a498ac4b9198c26a077e3ae0eb60001892787800009980003e1800001584705f316ee19f128648a800000005bc12d8b5c1b10000111192265580002fe0000000000012714420001f784bb031400008e45748f540000bb20001082000000000000006fb9f7e7bd00281329dba5530ca05391e1676b97b85b68000000069a22090926ff8000000001a3ae87766521af054a000051e14261861d1a00015bc53f11d47479790000080a0ed204c617806605e0464172a03c6d59fd63fa02161ce8aa007a8e6e1e6800040486d80000b1c7a30d5a2b680000fd06d618a8dec14080f245d8c421d212cc0a20e066bd9c8a13c86f00b6117e2d116426fd99c258219ea00005ee18989521da14cc014076e00016e0000000072c00005d8800074c1e6c1e19e340001802000104c2cc1cc48201b046828f5612996840f603ec1c00ac20000000702800004483704e787ae090800062e80006e3192858800000e6093201710dc17900000f8142c6790000000000028609e8000155461000000b20088000000046e800029f11ac0da0d7844282125ff120c193009e69e90ce04210264da152c3340e0c0490450653165c80d95343231e022891b8072980004b40000559000027b87b0000000075899a429b8000000000041b800038a9140000000051c00001c720b41a01ee626e182e0000d2a0379e105861b246de098a7ac0000000000000019be4a6000000000000dd0a585c9800000002460000c7400000001d891bc0ad9b4c79f88122211c260001a2e0b180007019a9600012520000000000138a0000c5400012fc5f1000009d15160000f645369bdc31019020980cb44c982506d50000000143200004da00000000000d2e3e7188a0000ea000009fa0000000352800032680000000b565629f1e00018aa2c218081641342000081a5609
  | 28 => 0x98604b1818e65f0ba62f481d20c59fce093087a000191a24e0c6e03710fa6340702000170e55380001ca8bd615c80be00000007288000000000033b000047e1e1a58504e05b900004de800000019466b680005709f6c00006c8788185c5b899f44dc80c4804800070f07465fe80000000eec7e6903a00016980df10042b49198462816c36b14d871480003d3984244e00000000da400000002950000171800000014360000000000117400016d028c892429696f414b8c123c9818c2331938550855436e0000232000000000005f01c5400001b20098000565005410a011a67d89cc0d59ad845c99c002e053623b80000001a3878c9d8c0531a900001bbc1491d0400015ac2e388161ab00001c68000000000013700763d1199000000000000000000000000019e06420000000000035a00000000f6077d00001010ad05521b084ca9d7674d8a3800000005840518502800031199165411b2e5920de6277991038211782488d5e1e598bc3ca0f2a69c94e25dc80004ee8f96042834002b00004fa800000014c2000000007a00000000000000000040200007ca08e05b200000000000000012a000000075f814e7c2094279e0a2806000001a61f32000000062d1c8624411a664000005ed830c0001c6c3b503ea0000000000000048600007af047e0001fe6000000016b086a198027a293000034298861f782bc78209f0257000010680ba01005620c70e022bd111a31c08262cb027843f806200012a034c9eea2409b8a55b841e5eb0a883148c9622012de6299b7c2b3204252a9da00000ff24ba800045c1af43e515c00e1800073b88be58187c24c80000000000000000001758000000000000016b20000000000000000000007ca878478300000d21756000151005d20107ff0c8474207103a6000000000002b50bd03a5800010500002729978258863410a9e2c000099e58c89303be0e4e3a495e067a000049f912810b9ab253408a453184d40c392fa303072037800642411da400000000001fc616b86307e4163c43998ca47c131400006a25cc1fe4137801847b8d1e40d07166e09a2c00017247061b446d40ece6c51a304d191080169e9a000000000014c000000006f680006db000000019a26f90bc2078a09868216be69a8b063cc1dd010813f63a780000001a3e60e0000488945600000006570b460000eae0001a600001136000160a6aa01a00000160478000068e864055c8f9a26384d21f000002ac90b627f81c055a129e33c000063d8000549800015b1f7a032881e5f79a160001c9835f0d8a64a9f6471392102b1943448191ea16f90c6689102e56c8d64487095406a8b4241806fa09f86ee02504a075996a029c1fb41c38d7e6730756045863c41b0032638954a41f0cce81205662bb844a6ea0a904b49986820860282815327828cbe
  | 29 => 0xc77f08a07659f3050382cc234000052c002c05280000d82092021040600019880001f02094998046501b87e99b2847d80003a3060c2798000350127a0000000778841c0000000000000035880000aa800069280000000000000000000000000001b3406c000019607a04c18000000000000003645599a7c38b8b7c0d4839a6970000000063e22e800007700000000a620001f1a00016c464310747f6828a64e88ca00015e64f8800000010c20000c8e00019bc5c11d7a0b6800004417ee4478cea1569832045192610f0fcc00000000001d0600000000000000000017c2021bec0000000548888a27419761278f9061b9ac61399e0e1cb204474a0f6a4951fa272516fe7dd057850c1626465800062b800012e800000000000de80002080eaa432146678e176e0ba038e16392ee1b98f626c69f76000160017d12d43ef01e0000118833883025b61f0400001360001bcc6ec1a92000016400005b4000179c0e296aa2bb00006d49a763981b620ea1dc40971d683b69b664941cf814508fc02c9a3400017f020d800069600000001cd672c80000000dee7f28bb8790903e3ea8a4400000006e1000000006f2224000000017c27cf0b6a2c980000cb0000000196678000004f706a61d285100000000710000070e12725ec80006ad800071a03be5911734000000058d9890000022016782e4153126435c800000f80003b21f181340c4a7d3881847e9fd00cd000060e85306e480006a8000037f916e0000b527fc19820000fa400001f000014a082a9ce26d29d145e300005c700000001c446798000000000024605b8000095e38f9faa4f00d2612b15980ae94f200000000001ba61a4000046186860001958000000000011d02171e52000190a00000000001fd4000a0ac7041e6019506e200009ec472153600000a42ef000006f151e00017b40000000331895a1e900001d49cd21979224631907037784921e0000000001e61c79c0211d105825114d471916706451220058800072e1f665ad0000000039c00010d058e800003602d07dc923a49b8c7663602346920dd425297220f082b87b71d120e480000000cd82ab9d440001cca07f029c6e393c67fe0db272006627b00b243fe00005b388b000000002f000000001a564918fb403b963847702283721d3c32f0d3c6bb9bce0000dbe7b3955c2a580000da938e000072200009c25900c86140022200008fa0790000539800042280000000000417a04e000123c6f5209468a9c586f88e2c2f51f0628515ca391802e4289324802143c6fc9a2800000006f6052c1af85e8131942456390843a98eca11f01be38109e47cd191230593a038d0c3c36988101c313a445f18a210e00004e58b762b5950e2300d5c79a00000000bfc0000a743b08b365d780005100a041af1f4826c08b600009a066c05b0191
  | 30 => 0x91cda81599f26471d500ff97c81ed08644589c4c2f99e5431e9bfa2ea00000000ebe000000000000000001f840001c340001c3676e00000000fa648f82903bd00006e1800071783c45bc12262ad85766eb83e61139c4819991a068991a23cb864a7a61b60139180c0d79bde5a4026a5d9153c13d08b81fc89a20b103b84e012000001dbe0000a3a396800065295a60000484389999c00000003dda0064d893ac7b1169e00000001bd96242fb99d476b0cba607819e19d9c7c000000023a8000000000081a95be000066a000208467880000090f204c78af23c580001fa912a581000075915904fc00007a280000b99e0670e9ed000003425be0f022ac0cb63f898060c98f580c80f065270e121428d16705164a68001ca000000022786e03e389f222b88000ef0fc0000000076d000057c000000016c2287118479d875a6b218b240c0ea837d93fa2821d4c000000000018d61ea0bec000104030d032e15480007d097480000000000121200000008198000113209c431131200015920001bc85b291e814f80bc1e78bce5ab92ca2978ed0000000000000006a7820c09893c86280ee4168805876d89aa77a0da081e962c00000003d9800000000000000b220d400000001cf233480004ed800051697881bb04428119b383c20c3252d1ad23ee1aaa0000072685006e7ff93ae75e1df85a5979e40a91ae6938e761c981967718e681ba80007c7000004b97945de129c66d00001ff1d2e000000000000005e685846f01df066480002b2000028304ec0000000000120a000000023197e40000358222015e45980007398b38217800027d81b6000000024180000ba800000015dc01f1b9e77500a2498a06822313d445480005fc9a52440989800000002651ccc6169b5a1101fdc5310a8268c8daa69b80001731be60000f0408a813800008920398a347d280001dc83aa4a98422000172c3ad0846000000000017862cf8000000009a61c0f4c0000446390800000000000000d660118eb018b85f62998000000136c00000004cd1aba1770b1075b000079c80000001ecc00000006b592da000118260f1bf84ed0254266956c2fe800002d85942d40cae0f596560000a4600000040219f0a45a95d00410efa48204aa00013de00000003d0820847994160000f5057109f413e00007620f985c68000000000000008f804c8d7659d00007728e3a0000000000149810d000034a094c2aa00000000e0051b12d83e78bb41fa10de56812485558b7a3580d923560e5612c99b26a908f02c103307d60678825987e4ef9d7c4af13e880ea0160c10a407ae84ce297203e6f487fa35b8db011e164e10d950a167167e5ce9944470845a2e891240001a50320170a3b0000052e04d879214507030f8c79b8c920ee800063e81ee51604584ff0e50100113079617ca65401c
  | 31 => 0x841ec911c00001de80d011e47909c45730ea460d886c70c908e60a0380577810646499185ad914e000091675c036665680000051f621b48f6e7b68000005973e478800000004602c6000071f8cfe1619402518800068d849031604b84278e5e7769d741d900005c517400001dee3ce80000aa000003a096e29482c025187d200000004b3905646a1602000000065398b08078000000000000002fe73e9de66868c0609b0b7462014720c014ba59d82a200009982339c5a6d09016122000000018e6000000000012f43bb8fbe15a80b45d6069669513484cb9c907128000097800000000000c908d86d705081040cdc4e219ec0f30fa82d68e10305108075a8a1a07614087ce9a4405f874e525824e0001c9c4fd20300001f12000000010200000000d54000074c731968c0001f8c4c880000000e4040e000000000000001cc8092800000017f42eb800056d0d46298000000000000000c440000000690800001a93ec0320344071000005400003970000605823c22b1350000000000002ce0001ec63c6080e17380006f180001ac853278504c462780002fa80000001d4a691800013a19b8000099c2d5100025e178e18d800000000000000d8200000002e600000000f3808f88b44b11e5a0f689d82ae11ec6728822184949e5f4180e6c407c8000175000000006ae04825400fe402599980078000261031a000202c50e204a0001b6473c13aa1ed80001d800001d78000047196065d1274608993425f18ce51a80001f18efe2d80d9c06e8b9e02b95ce562058a5a017a0157036c3c7179676496a616492b04d9000031209bc6811b400cc9c0e1e20cda3630b92259084e08b11da6a2800000013ce000101c4570a0a00000004ae9f2628488520cf9f864c007f06a8920e513187c2b80da26e21e4615ba0a402a924a6ee00004290b4832b107a81d8c3a15c00ec00006aa2cf0a8039f8f0a58a17847cb8cf25bd80003d6968a67c0d2050717c635d10780f8921a386009800000000000d9850400000bc827600010a640a06c636695c80dc89d265ba0046c0208c1a10c5e70b9f96371990e1fd133c32a8df215813c255100602050c5c43898201cb8b0e792811864804c0000092e0ff0b5873082485338cf8227182605a948e6cc070600000006129ebe0000b6400003b264f0384534800000000000a69c920249b485c600000e888f423105b63f40f8829d908673f00008071eb280a800023080006e580005321e362d790bc770876a00008a870f8bc62b703120cd995259785a8346000000011b45c417684f9000014e11580001a1c0341f6066a18ea56e18686761f94476041653d02d612c1d9a03d98e443b8d305f99906318903241a8e945e984fe1df004e43f0c3625c85ec6f28bc81048fdc1be010221f0bbe3bf05443021d400b788f656587d865
  | 32 => 0x8e83c64c315807aa0b3403e16fc4e4000032a1bb23001e265ff96c07e700002ae8e641620c6056d99407ef9dc80879e40264098803305407fe9eec4c418d205499c8065068e49e10ba195882c2990dc4797801c596083458a956232e1b747a89cac3a70b844de16d211d86ce4d00fec7df199665c999e70c1fb82a8952467496540001d3a53e01c8000000022599fa5a9169400009f82c31fbc66b0000000000000000003f388d242d0e1464c12ae30a04c252980007bf101800011f47a2097a6e600000001a6600000000001c4681b0d0627515a400002026ed800038f00001418000000199a0000dfc031910005701ae6f107ce2169f00000144a0001a4c38280004d600000001c567910ace567800008e93f206896cc6771e6400010d41f114067ec82e01d400007a50fd2457897e2d29ade6c09d0262f800072080004a11742071902419b98d44a88e1e0db968230f87f80ca891a25d9308522a0a839e130a2018a9e5ba8cc82a2902c1c905aa3d781581839fa841898dc00003d419218e85fa8454778007059c8abe5219c6600002300000b121eb1f4054a94484ab019a7be89001f880a8000156a28882b06bb1e8e7c580000000000000091c3331baa4ea04624a081a43b18e0e0a7933050a800003c09085a21c284280ee0000141a43a897058680000001404745853a4851a5e07b1ee871b9c88000196c7059aea000193e2480948237800005580003882074000000000005c474f9f2000000000000000000000005b800000000001f90d6c0001d900d308d600017325611d3846406280000c8a0b88b823f5000000003ae7fb1fae81b86060000a7a6011f680860e526b0096c68494a40000b4038a202211a9a100000a7e18e983055c1dea3d009a600000000401bac0001cea44b0ab4033927621504f058d189a00000004cf8fb67b2000057900000ad02c26b5000010f800002085e65110000000178020c00000000000809025a44810aa2bd9a1e4a4114c60b1d2279404a427598f857b101e5fe084a2a609667350ae22c28c2e810022480e096050500003c00d5072d0e3200003de000000021200002428ef27a81bf0000079c5ca8d884bf90f2619945e7bb8cc4563184449c12665e28d3800009b4365864465f9c607da8f367ec1ca418285f27e78b0200012f21ce067a46700002aa9eae2fd80006050a027ed861678896d4449821c000000036f077a7a1000051a000072b800005680003ff061c52408e65e0997a1ee13760b48ffe0fe80000001cdc00018744a900000001af200002a470b0ad800010d80001cde2e90c880521f8209119aa3af116817789287e90a7206185583a204245da9a860000c9878f924200000006a3800033b86dc606167a0e99abc2858d0c1ac03f24d8096838c0f7e7ee8226822013e2bf0b2a5540f822dc0e
  | 33 => 0x70a0000000000000049b000022a931a35300000000de200000007e2865a2288bdc5d30000000064200000002e30936062048e63810226da8f806889f7081705b2000196a4d588bc3198da844880000001b0c0000fc281900000e500000000000520188257e934a414960c2cc8e447d1972e00000004a300005d98dd648b0b8a6838000339830851500001dc163082d90e8000000047298764cd894e6cf00747461e1c25417284938cc25fd80000eb00000ce068c63c8000269119a29e0a062ca1492000031e247800074d000039280003209dc06f41d603f680000f216f2000000053812c005183065d49b180001896000092a66997dc07400000000e6a03e85d0365171e42b1c8e545000000005040bb8f4a1c50f8439f00002f312e80f9037e676985003d00005c486383988b9680a00001a9131638904a27939800000114a21a1d52229800052680003140c4c8050fde4bd80000001e2a616025800012b424f80006d18e9a69913e6000000000d0000085000000000001e997e848b9a8c67f97207a707bc1fb18b852f80003ac8d1251d82fa15d000000000005df8e8000000003a298fc1e3118040192965a383220001d842e19b0a00011f208d857c0000000000000000009ae39b166e000000008b8dca00000000000000762848a00019a02bf800004a000004c1ea615e80003040fa22351cbe48d143e00000006a719fc0001b720000dd000018c40000126000068a17c05480e3201a00000003d1929259991600ce9ab028a9d3200000000000582497800000000007d706d40000edc000207028f000076789122fd0a6c62d9ae2332845656895307db8670147981c000000057887ca0001dfe00000004a39a8400000000001d8e55e86822008b1e1a49d0e00000006c8800037e00002929eaa0000d56000000043900000000fe66b280000001b1c7b0800030900004330000313910e8029c6a82c0d9057e104a40300b00301d807e200007fc8000000108800000002cb80001b0a06033000000609c784cc9b942770f8a17f8a00023092c00000003bd9a8881e00001699ae60000ae800000000000be200000000001fcc00000002b294b2125800075214640000000000180a4ec8000000139800000003dc800079e82f80000000630800001b021a1578000707000059680000000000000000058f80ea5d80a2074b1b90339000047199c62e512be24e9a4049602f467400003509ef20d707a204d045c0d295b0000108c0148b9a3c480004b70c2200000000000ac0324109a74291d263b90d646c84bc6479e7400000fe5061c24185042c0000bde3251fc81cc81f617495767eb1a9a0000f1e0001db0718800005c00da5f59f9250e800047398541d01e125be9c083cd00003dd19b645580000000be02be84f6051186a219800036b800000006a87
  | 34 => 0x17504804f68bf22ce87be4df800057d8f68151939c2dc96780001dd23b484b40001af863780004ce95d84e0886e000000028f8a3600016643038cb04d39da83fb94a81ba13c400007364ac951c598800014a00000fd80000d88000419800000000000001fc021f87921b7883e61495181f4010c585800073600c260a800000000005379f8e0000d6a3ee80003c50000000000044f00003b780000001e86000109452b9e8206404680000790000000054080005cf1c2000001c20000542000000032984d639200006c98000237000000013925d28dcc80014b672d80003df14dc57a94ee327151a00003785b19eac30115206ef913471d0b686c5818447100005ee9c9a35380d663b17a261b1d940fb942e1198e821c4873426d80006271cec00010906cb1ef86cc91c07b293280000000385898000009e255f04cc0000f3c327800001088564519c1214a813c00000007e00dce0000000000020463000001a793f80001b3a000000080815d41bd07ba1ca08b241081420001a06675800a00010980e2000000000000a812e6039090e2768000575803c0d5000065784323fd12f037600006f58ce011200a61261b760b70000725877465c0de47a78b1a00000002e217d45f80f240a1125600011044a20000000060871c873e1bf101464b937c7ad9ed2308053417691104111e70265935c18b088e31a8a4e0ab8a1e09c153e24f0df472a99ee20c82ec59b132c1ad9a3c665000000000000a38e580000000083800000014201488000459198a307000046e18882a19144283800000d8fd82b1000000000006b0800051e8000000000076710f669880005e494ec7890e7a823827280c8b666b384be1f3195425615ba00020547d500007b91be0000175a7c8800009b99ce525047a60400002c50000211000052897e200007ee2df8fe01ab8a8e79702982a90dea37e817237c1dcc6fa828c48a02a6522106820a8d4800000007e8004a0000624000000000005e200003f07a4002a52f118c37a057e5181f565719702000000051d1f5000000007f480000000000584800031f08280000ddc176000036d153819f80005b590be00017981b680003068f1a4f585c23a895f40000000757000000000000000000000000073a00007ae000039c1f5a59f0d9e5b993847cf86b870a90542100000000016800011fe0000000000182453293d048d882e65a00383ab0f225f38556121940043e12e03e480003fd800073916dc61c9ba482188763db0860125000021c20ae7a49f0e000113233f0000827833c3fc000049f000004e800009f00003c4177c00001f84139f5206a140c4ad8000757929a56180000000fb26b3000044500004e8800000015fe7340000000000006606c075b9142434923207c969200004ae41700006611ee21de16506c78c02000000046c0
  | 35 => 0x1d54583933819a05506be83181680b160000be447300001d51b3e6410cde1a811d63888d3a1e51cf646d81ac00000004c702388030fea000125a7bc1b7038706b4000000c0ed800000008782d898f44540068250075c207186210080004d500000000000255800000010ca7cd8f7a3158a26393169a1720fc87771a9803f028620303dc0000000149a0b80001afc41407da00011180000000000008a0bc16a200000000b513ee0f38fc601112446c380001d10000587000059317762a511a421c8000000096a76a87d60000d4417017d200004a80000376000000040f142200009c67f080004c61b362ec12603610000658829671c00005c2065c77782941cf1d421b300007a90d5228c061046f8a9a16014e834d8ed607f94d67231b2a542093449a01545210bf01f717d869b035a6f09fe25518baa7108dda71e9f1074419ae76c8b0063208e27300264749142800020507f80bfe2160e8e43d16227fb800030600004e688e857a12385b78a2c5eb800013887aa27000e26c80000000000000000005c300000001a0c79a800078a152e2d38620199174414597a845501921a51a7421d0688000159a4040d7a06984266ab04527089a5a7d79dbc3eb012278600005db07666ad049a402800047f0ee800010b86e8935e23f8ffa0131706245173864902be3b3050e5c58c642b79efe41c800051ba062680a00e3350a8472a0ef01f99a8264d9de41cc12c273f800000003a01539df630b0fd673380d4000000058b89ba0a012166121b686e6800055f9d980000d8600002b210313045a1800042c000000011aa1038000000126a61e00000000000000105a38e07080000dc000000000000000000000081497364ec111600016e8193800081ca0a259a0d223b8800019b09be504800016913a62bc000000014ac000000034220a6395205a514913a0000b78000000082c9e3c77e8974438208a3468c6c39c800030e0d3400009ea6bf80a073807f6000000000002402f60000000050c1869aa678b9d56000003051197b081609c8000120433e845e000026801780905e90f3e6159f1442b916c0d38000000000000010f063c08da2f28d024270be84569be85230fca7fa97da441800044f812063680124f8000077c80000001f0c2909ae40a49ae820e95fc8179dce0000d804d69ff46db8c7200018124f601d667e1fde41188427561ff6002145c0fa1e804da89ce66392405078f0c3eba0180001b7a70680000001036000000000008940e400006b700006711864263000000000000001b1207d054a5138f3217f1ac45af10204dc13024e507985980c7e61392aa17e807e1b903d03290e6622683f82e81a787281574166900e36e8b6e0001ed664b1dec1591da6613032834f975c2219ee02499374623007854e92800089a68309a07e15a08500001d26
  | 36 => 0x9c800830a677883c19d118e6fd12b8623874272f1a181941dd82f1058c4d317742ee820a11b051a53e814049716a800411de2d310025ef1b7e5ef99325ae87042be028213b9c0400013cc2b9a07c38d8c1e0001ef618c8622775938c6a015525d38bb62608c784369aae59192020f286fe42a0ec42e01d5a2e700003cb0cf4000065213a9f4c00014fe06d0d2469f86d02ba8f0e557869c40683a44db86726ed10b20f0150c5fb16b01d61e301659d46743000063f9f2c0e5965230c0d0e6af83b0180151272e80206c18346000121e0bd969c27810c02eb181a3400520000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c855d942440011bf06bb2848800e3720d7650910006b8086eaa1220098bc875914244001878eab22848801e5b21d52509101cf17322a4a122000e2d64549424412dec020a9284880263ba0a768c91003c9e422eb1922000d70105d6324400759906b1464880063d219718c91000cf8402e319220028f8865c232440053e102b8464880033c043764c9100046fc1aec99220008f7815d932440011f700bb264880161fa14764c9100043ec28ec99220048be841d9324400117b083b264880033c040764c91004c6e43ac699220038ec8758932440075ad0db1a62880067c203724c51001d6a41ec498a20038f48758931440075a906b1262880db1d1d9524c5102259a422a498a2038e5463549314406dae0e0a926288002b5219324c51000762b126498a20019f287dc131440131e90eb2242882cf8d151644851004d72412c890a20019f080dcd2144001ba461b9a42880063d219734851000cf8402e690a20098f48758d214400178b0631242880271d1d952485102159a422a490a2009e6462549214406dae0e0a924288003b1d8e3248510005f0c046490a2000ec5634c921440033e50fb82428800eb6a1b634c110014f840ee49822003ad883d8930440071f10eb12608800eb620d624c1101be3c3b2a49822040b38845493044071cb0c6a9260880df5c1c5524c1100056c432649822000ec9624c930440053e50fb8a6088006f421d314c110016e843a6298220019d0874c530440037a50c98a6088006f4219314c11001f68432629822001ad0864c53044007da6ec98a608800b749d9314c110016e83b2629822003ed0764c530440059a0ec98a60882cbd4951314c110597a82a2629822000bd3824c53044001ba6e498a6088003b4d89314c11000768b126298220b1f53524c53044001ea2a498a60880027c21d214c110005e8c1a429822000fc13248530440131f10eb2240882c38e151644811004d74412c890220029f081dcd2044001ba463b9a408800a3e2197348110014f840ae690220098f88758d20440017930631240880271e1d952481101f59c422a49022009e6862549204406fae0e2a924088003b2d8e3248110005f0c0c649022000ec9634c920440053e50fb8a40880027c21d3148110006e8b9a629022000fc1324c520440033e10e90a4088006bc2192148110016783b2429022009ee062485204415fec6a490a4088003d8549214811000df043a429022002de08748520440033c10e90a4088006f8a19214811000df0432429022009ee0864852044013dc6ec90a408800b789d92148110016f03b2429022009ee0764852044001dc6c890a4088003b85912148110577b12a24290220aef605448520440017c70690a4088002f860d2148110006f1b9a429022000de1734852044001dc6c690a4088003b858d2148110
  | 1 => 0x265b8a609000eb620f614c12000764996c29824000ed331d8530480015b10c98a6090002f260f214c120006f1b8e429824000bc9834853048001f826290a60900035c04175d91100043ec3cebb22200587f875d764440010ff04baec8880161fe1f52d91100043ec3ea5b222000d7010dd5644400b0fd0fbaac8880121fa1375591100061f426eab222000c3d84dd564440090f909baac8880021f60b75591100043f438eab222000a3e85dd1644400117d0faa2c88801e8fa1754591100061e2a6e6b22200087e87d49644400b0f90fa92c88801e8f21352591105af1a2a6e2b2220b4e3854dc1644400917d09baec6880022f61375d8d100043fc2ae9b1a200587c855d3634400987ce82a6c6880030f5d054d8d1000536c10a9b1a20048be84dd5634400117b09baac6880161fa177458d100043ec2ee8b1a2004c3e7415163440014db042a2c6880030f1537650d1002c3f42ceca1a200087d859d943440010ff0abb286880161f2157650d100061e2a2eca1a20008ef825d943440131d904bb286880035c0437550d1001c5e43ac8a1a203ca3c855914344001878eab22868800ea720d6450d100246f43ec6a1a2000e1c54d8d434400917d09baec4880022f61375d89100043fc2ae9b12200587c855d3624400987ce82a6c4880030f5d054d891000536c10a9b12200793c845d66244001ae020bacc4880037404373589100045fc22eab1220048bc845d562440011bf06baac48800e3720d755891002c3f42ee8b12200087d85dd162441578b8e72a2c4880030fdd054589100261e3a0a8b1220adc5c7315162440014db042a2c48800e37a1f73589100062f2a6e6b122000c5c54dcd62440018bee7a92c488293171cf52589100066a39ee2b1220018fa87dc162440019b0e7b82c4880035c0417518910006d8082e83122009cce625cc6244001ba020b98c4880023be1d621891000666b9ac43122039a3e849d9524400147b093b2a4880029b60a76549100051fc22eca922039a3c845d952440014bf06bb2a4880e29720d765491000537c12eca92200793e87dd15244001e6021ba2a4880030fdd874549100061f3b0e8a922000c3d761d15244001878ec3a2a488003cc04074549100043f43ec8a92200087d87d91524400f878e9b22a4880021fe1d64549100043e43ac8a922007c3c745915244001878e9b1aa4880030f1d1635491000537c12c6a922009a6c8258d5244001878e9b12a4880030f1d162549100052fc1ac4a922038a5c835895244001878a8bb4848800237e0d769091001c6e41aed2122000d70105d6424400f65908a94848827bd8041529091000c7a432e32122042d34545c642440033e100b8c848800a3e21970909101f69c2a2e121220029f0815c2424400b0fd0b3b284880021f61676509100043fc2aeca122005
  | 2 => 0x27650d200043fc2aeca1a400587c855d943480011ef02bb2869000a3d2057650d200061e2a0eca1a40038bc8759143480794790ab22869029a4fa1f745492054f94106e8a9240a1c3f761d1524817b87cec3a2a4902f30f5d8745492050e1e3b0e8a924000d38701d1524814de50403a2a4902861fa1f64549201b43ec3ec8a92400cc3c74d9152480134d905b22a4900021fe1d645492002c3e43ac8a92400cc3c745915248001878e9b1aa4900030f1d163549200053bc0ac6a924037a748158d52480134f50db82a4900034e1d3705492004db5416e0a924000c3c75d9142480192d90ea9284900db1b1d9525092000717b22a4a124036d6870549424806d8d8eca92649015ecb211524c9201c72631aa49924036d687054932480015990ca1a649015fc3151434c920006f1086e299240008bf845d7614800917908baec2900021fe1574d852002c3e42ae9b0a4004c3c7415361480014db042a6c2900028f21152d85200076299663b0a400587e859d941480010fb0b3b282900030f15276505200061e2a0eca0a40028bc87591414804b4790ab228290003350c6764c52002c3f428ec98a400087d851d9314800917d083b262900022f610764c5200066a188ec98a40028dc8758d31480055a902b1a629000ab920563c85201b6363b2a490a4054b2c84549214806fcc8c2a9242900db5a1c15248520006e5186e690a40018ec865cd2148001d8c63b1a429000a3b21d6348520005724328290a4054f24545052148001d8ac698a42901db1e1db75501203bd9d426eaa024053b3a85d914048177a70a9b9a809014ece215435012004cf543ee4a0240baf2854dc94048001ad6ea39280900035a1d472501205cf942a0e4a024000bc9831c940480017c30239280900025e21d525012004e3c3b2a4a02400cb38845494048013ad0e4a9280900066e21d425012004e5c3b284a024053b38855094048013b50e4a128090003ca549425012004cf443c64a024059f28548c940480013d10e992809015fca1513250120007c4a1a64a0240b8d3854dc540480a76710aa0a80900267a21f21501202b7942a642a0240009e88748540480a9e50a890a8090003e8505215012004c7c432e89824052d38545d130480133d104ba2609000eb6a1b634c120005f0c08e49824009c787654930480a567108a9260900e39618d524c12004eb4392a498240019d8874c930480035b10c9926090027361d9324c12004ee43926498240b7f4b524c93048001e92a49926090006f221d324c12004ee443a649824001bca864c930480037910c992609000fb2219324c12000d64432649824003ecb764c93048013b94ec9926090027721d9324c12001f643b2649824000dcb744c93048001b92e899260902dbd2951324c1205b7a42a2649824000bcb814c93048001b9
  | 3 => 0x6b2e400087e8790d65c80010fb0f21acb900130f1d243597200261e3a086b2e4009a6e8210d65c80014db0421acb900030f1d371597200051f424e2b2e4000a3d849c565c8001878e938acb900269ba0a715972060536c14e2b2e4000a3f845c565c800147908b8acb900030f1d171597200061e3a0e2b2e4004c3c74d0565c80010fd0f20acb900021f61e41597200261e3a482b2e4004c3c7410565c80134dd0420acb900029b608415972047e1e3a662b2e4090c3c748c565c80010fd0e18acb900021f61c31597200051f42062b2e4000a3d840c565c817f878e818acb900269ba08315972000536c1062b2e4036a7a800c565c80014f30018acb900161fa1f75593200243fc16eab26400487d82dd564c815317f08baac99026e1fa1c75593205361fba0eab264010a6d821d564c800117f08baac7900122f2117558f2002c3f42ee8b1e400087d85dd163c800187ee82a2c7900130f1d05458f2000536c10a8b1e400587c85dd943c80010ff0abb287900161f2157650f200043ec36eaa1e400087e8759543c80010f90eb2a87900128f2116550f2004c5e43ac8a1e403ca3c8559143c80131b90eb1a8790003871516350f2004d6643286996405ff0c5450d32c800117f08baac3900122f211755872002c3f42ee8b0e400087d85dd161c800187ee82a2c3900130f1d0545872000536c10a8b0e400587c85dd941c80010ff0abb283900161f21576507200043ec36eaa0e400087e8759541c80010f90eb2a83900128f21165507200145e43ac8a0e4025a3c8559141c80131e90eb0a83900038d151615072000c77416ec98e4021a3c8459531c8001ca862b2a639000a3721d634c7200156a40ac698e40098f48758531c80075a906b0a6390003b14c9614c720006e4996e098e40019e8805cd21c80135c90ca0a4390177c9151414872000762b1a6290e4000be3804c521c80010fb0f3aec8902fa9b60a75d912002c3fc3aebb224000c3f845d7644800187908baec8901161fe0975d91200651f42ea9b224000c3d75d536448001878a8b9ec8900161fe1f52d91200043ec3ea5b22400ca3c84d4b6448001878a8b8ec8900161fa1f75591200045fc22eab22400087e871d56448001878ebba2c8900021fa1f525912002c3e43ea4b2240008bf845d7634800917908baec6900021fe1574d8d2002c3e42ae9b1a4004c3c7415363480014db042a6c6900022fe117558d200245e422eab1a40008f7815d563480051e902baac6900161fa177458d200043ec2ee8b1a4091c7471951634800187ee82a2c6900130f1d05458d2000536c10a8b1a4093c7471151634810b8e8e3a92c69000a3da1f7158d200063b2a6e2b1a4000c7454dc563480018eea5b8ac69000335dcc7158d200067838ee0b1a400587e859d943480010fb0b3b286900030f15
  | 4 => 0x24c00147f08bb2a4980e68f211765493000537c12eca926000a77815d9524c06f4e902bb2a49804e4fa1f74549300078c186e8a926000c3f761d1524c00187cec3a2a4980030f5d874549300061e3b0e8a926000f18301d1524c0010fd0fb22a4980021f61f645493009e1e3a6c8a92600087f87591524c0010f90eb22a49804f0f1d164549300061e3a6c4a926000c3c545da424c0011ef02bb4849800a3d2057690930006ac182eb21260018dc865ce424c0cda38a8b9c849800676201739093009d96422a5212609ef483054a424c0131f10cb8484983134e151709093001cec41ae1212600587e859d9424c0010fb0b3b28498003560c3755093004c5e43ac8a126000c3c75591424c0272d90ea9284980e78b991525093000716b22a4a126096f4830549424c0131b90eb22649830f87151644c93004d66412c89926000bc581189324c0138b8eca92649819ac7211524c93004f26312a49926036d5870549324c0033b101b8a649800374843714c93000ced43ee099260048be84dd7614c00117b09baec2980021fe1574d853002c3e42ae9b0a6004c3e74153614c00187ae82a6c2980029b60854d85300051e422a5b0a6000c3c54dd9414c00b0fd0b3b282980021f6167650530006ac186eaa0a60028bc87591414c04b4790ab2282980030f1d564505300247b43ec2a0a6000e3454d85414c0033b101b92629800ab5207624c5301b62e3b2a498a6062b1c84549314c06fca8c2a9262980db561c1524c5300156b436c298a60019da87dc1314c0051dd053b6429804e4f21175c8530006ac182eb90a60018dc865cf214c0033b100b9e4298003b14cb61c853004c7c432e190a60039d8835c3214c001b9264b864298003360c3764853002c3f428ec90a600087d851d9214c00917d083b242980022f61076485300066c180ec90a60018dc865cd214c0033b100b9a4298003351d931485300243f43ee8b2e400483e87dd165c815387ee5ba2cb902a70f5cb74597205351f424e8b2e400487f875d165c800987ce83a2cb900030f5d074597200052f418e8b2e4000a5d831d165c80134dd043a2cb900469b60874597200053b408e8b2e4000a75811d165c806d4f5003a2cb900029e600745972054d1f438e8b2e4000c3e871d165c8001c3d063a2cb900038760c745972053717410e8b2e4000e2d821d165c814d87ee43a2cb9029b0f9c874597205361eb90e8b2e40a6c3c721d165c8001c6d023a2cb900038d60474597200071d400e8b2e4000e39801d165c800187ee03a2cb901db0f9c074597200061eb80e8b2e40c2c3c701d165c8001878e9b9acb900028fa1273597200051ec24e6b2e4000c3c749cd65c80134dd0539acb903069b60a73597200051fc22e6b2e4000a3c845cd65c8001878e8b9acb900030f1d073597200261e3a68
  | 5 => 0x124f21d52509400051e432a4a128009c3c76549425012de5440a9284a00574be1d52509400259743aa4a128004b2c875494250073a590ea9284a00124b21d525094000717c32a4a128000b2e8654942500016590ca9284a00038b219525094004f17bb2a4a128009e2c765494250001c5ec6a9284a025bcaa01525094000794c02a4a128096f28705494250073c5ec0a9284a00e7cad8152509400069c3aee0a128000f2952dc1425000b0f90b3b464a00021fe15768c94002c3e42aed192800087c865d6325000927908bac64a00021fe1f658c9400043ec3ecb19280018bc865d2325002b2790aba464a00263e219708c9400069c2a2e1192800587e85dd932500010fb0bbb264a00030f153764c9400061e2a0ec99280018bc865d1325002b2790aba264a025387195434c9406161e3a0cbb0a80018bd84dd76150001878a9baec2a000a2f21175d85403751f42ea9b0a8000c3c545cf61500014790aa1ec2a01ba8f21352d85403751e422a5b0a8000a3c8550b6150001c5aa4a16c2a00161fa1b75585403ac3e436eab0a800493e84dd561500010fd0fb2ac2a00021fa1c655854064c9f43eeaa0a80c8a3e86dd54150123878edbaa82a031e4fa1f65505406151f436caa0a8075c3c76d954150001878cbb9a82a00030f1d763505400ac9e42ee4a0a8025a3c85d8941500012790ea9282a00028f21952505401b61e3b2a4a0a8000e3465d854150001a70ebb8282a00161fa17764c5400043ec2eec98a8000c3c549d93150001ca863b2a62a00062f219744c5400ac9e42ae898a8000c3c655d131500091f50db8262a00034e153704c54002c3e42ced90a800087f855db215000b0f90abb642a00021f21975c85400249e422eb90a800087f87d9721500010fb0fb2e42a00062f21974c85400ac9e42ae990a80098f8865c32150001a70a8b8642a00161fa1776485400043ec2eec90a8000c3c54dd92150001878a83b242a00062f21974485400ac9e42ae890a807ae34655052150001ab060baec8980021f61e75d913002c3fc3aebb22600087f825d7644c00b0ff0fa96c8980021f61f52d9130006ac186eab22600587e87dd5644c00187d09baac8980030f61375591300043ec16eab22600087e871d5644c00147d0bba2c8980022fa1f545913009d1f42ea8b2260c6e1c54dcd644c0010fd0fa92c8980161f21f525913009d1e426a4b226000c3c54dc5644c18bc70a9b82c8980122fa1375d89300045ec26ebb12600087f855d3624c00b0f90aba6c4980130f9d054d89300061eba0a9b126000a6d82153624c02727908bacc498003560c17598930006e8186e2b126000d58305d4624c001b3060ba0c4980023be1d621893004e73312e23126000ce5625c4624c001ba060b88c4980e68fa1276549300051ec24eca926000a6d829d95
  | 6 => 0xad1ec20e7b2a8076a3e84dcb65500eb47b09b96caa00030f5d372d95405361f3a4e5b2a8000c3d745cb65500090fd08b96caa00121f21172d95403b51f420e5b2a8075a3d841cb655014d87ce8396caa000297a0c72d95400052ec18e5b2a8000a76811cb65500014eb02396caa01d69ea0072d95403b53cc00e5b2a800087e870cb65500010fb0e196caa01da8fa1032d95400051ec2065b2a8000a76810cb65500014eb02196caa01d69ea0032d95400053cc0065b2a8076a3e84dc765500eb47b09b8ecaa00030f9d171d95403b51f420e3b2a8075a3d841c765500010fd0e18ecaa00021f61c31d95403b51f42063b2a8000a3d840c765500014dd0418ecaa00029b60831d95403ad3d40063b2a8000a79800c765500010fd0e10ecaa00021f61c21d95403b51f42043b2a8000a3d8408765500014bd0610ecaa00029760c21d95403ad3d40043b2a8000a79800876550185878e832ec6a00062f61375d8d400061e2a6ebb1a80038bc845d763500e947d0baa6c6a01d28f21352d8d400061e2a2e3b1a800087e87d9563500010fd0e32ac6a033a4fa1f7550d4066d1f436eaa1a80abc3c76dd5435019927d0fb2a86a030a8fa1b6550d403ae1e3b6caa1a8000e1c63d954350001c38cbb1a86a00564f2177250d400061e32ee2a1a8000d3875dc1435000917d09baec4a00062f61375d894000536c16ebb128000a6d821d762500010ff0ab9ec4a00161f21573d89401e61e3aa87b12800087f855c7625000b0f90ab8ec4a029a8f21065989400043f43ecab12800087e87195625019787ee832ac4a00561f61f65189400062f39eca3128000a6d82d9462500018ece3b28c4a029a8f21065189403be1eba0ca3128000c5e7319462500014db04328c4a00031d9c465189406163cb80ca3128000c5f655cc62500018b8cab98c4a000347151731894000477c3ac43128000c77655c462500018e8cab88c4a00034d15171189400061e3a6eca92800087e869d952500014db053b2a4a00030fa1276549400061ec24eca928000c6d829d952500018dc853b2a4a00031b50a76549400051fc22eca928000c3c745d952500014df04bb2a4a029a8f21076549400061fc20eca92800487c841d95250001879083b2a4a00120f21076549400061fa18eca928000c3f421d952500018dc843b2a4a00031b50876549400061fa08eca928000c7a801d952500018f3003b2a4a00030f90076549400061e200eca928000c7a201d9525000927d0fba2a4a00da8fa1b74549400061e3b6e8a928074c3c74d8d52500012790ea1aa4a00da8f21943549400061e3b286a928071c3c74d8952500734f10cb82a4a00034e1d17054940655b5c12e0a92809d93e87dd54250137878edbaa84a00024fa1f65509403ae1e3b6caa128000c3c75d8d425000165b0a31284a
  | 7 => 0xbc845d763484010ff0aba6c6908161f21574d8d210261e3a0a9b1a4200a6d82153634840117f08baac6908122f2117558d210047dc02eab1a42018f8805d5634840b0fd0bba2c6908021f6177458d213ae3c384a8b1a4200c3f741516348409878e82a2c6908029b6085458d213be3c380a8b1a4245c7870d4963484031f50fb82c6908031e9537058d210063c2a6e0b1a4200c7b52dc163484019b6e6382c6908033cdc47058d2102c3f42ceca1a420087d859d94348401878a93b286908021fe157650d2102c3e42aeca1a42008fb805d943484031f100bb286908030f1507650d2101c5e43ac8a1a423ca3c85591434854d27d0fba2a490aa7c9087745492150e1fbb0e8a9242d6c3e761d152485ab87aec3a2a490a870f1d874549210069a388e8a9242a6f24211d152485430fd0fb22a4908de1f61f64549210d61e3a6c8a92420087f87591524840b0f90eb22a49086b0f1d164549210061e3a6c6a924200c3c7458d52484014f700b1aa4908da9e20163549210069a3a6e2a924209b6682dc55248401878ebb22849086a5b21d52509211be363b2a4a124200e2f64549424846fac8e2a9284908df1b1d9524c9213dd96422a49924238e4c63549324846fac8e2a926490802b3219434c9213df862a2869924200de310dc132485258e8edbaa8290a4ecda1375505213d59b42ec8a0a42d4d3454dcd41484f56690aa1a829082679a1f725052169f922a6e4a0a4200d67751c94148401ac8ea3928290b4bc91507250521005e2c18e4a0a4200be1801c941484012e90ea9282908271d1d952505210d59a422a4a0a4209d647254941484053690ea1282908272d1d942505213d59a42a84a0a4209da4725094148401e4aa4a1282908267921e32505213ef922a464a0a42009e4874c941484f7e48a89928290803e150d325052168e9a2a6e0a0a42098f4865d131484f3a68a8ba2629082679209744c52101d6b436c698a4200be1801c931484138e8eca9262909e6cd211524c5211c72a31aa498a4209d647254931484053a90e992629080ab5219324c52104e6a3b26498a4209dc4724c931485a1e8ea49926290803d1549324c521015e243a6498a4209dc4874c9314840578d0c992629080af1219324c52101f624326498a4202ac4864c93148407d8eec9926290827719d9324c52104ee23b26498a4203ec4764c93148401b8ee89926290803715d1324c52167fa32a26498a42cff44544c9314840178f009926290803714cb704c5210045fc22ebb0242048bc845d760484010ff0aba6c0908161f21574d81210261e3a0a9b024200a6d82153604840147908a96c09080f351cd31d81210076299263b024200ec932cc36048401da263986c0908124fa1172d95403b51f426e7b2a8075a3d84dcf655000187ce8b9ecaa01da8fa1073d95403
  | 8 => 0x9baec0988022f61375d81310043fc2ae9b02620587c855d3604c40987ce82a6c0988030f5d054d813100536c10a9b026200a3c8454b604c4090fd0fba2cb908120fa1f745972154e1fb96e8b2e42a9c3d72dd165c854d47d093a2cb908121fe1d74597210261f3a0e8b2e4200c3d741d165c84014bd063a2cb908029760c745972104d37410e8b2e421fa6d821d165c846f4ed023a2cb908029d60474597210053d400e8b2e4200a79801d165c855347d0e3a2cb908030fa1c74597210070f418e8b2e4200e1d831d165c854dc5d043a2cb908038b60874597215361fb90e8b2e42a6c3e721d165c854d87ae43a2cb90a9b0f1c874597210071b408e8b2e4200e35811d165c840187ee23a2cb90a4b0f9c474597210061eb88e8b2e42c9c3c711d165c8401c75003a2cb908038e60074597210061e3a6e6b2e4200a3e849cd65c840147b0939acb908030f1d2735972104d37414e6b2e42daa6d829cd65c840147f08b9acb908028f21173597210061e3a2e6b2e4200c3c741cd65c8409878e9a1acb908021fa1e43597210043ec3c86b2e4204c3c7490d65c8409878e821acb908269ba08435972100536c1086b2e4200c3c74dc165c840147d09382cb908028f61270597210061e3a4e0b2e4209a6e829c165c85b34db05382cb908028fe1170597210051e422e0b2e4200c3c745c165c8401878e8382cb908130f1d340597210043f43c80b2e420087d8790165c8409878e9202cb908130f1d0405972104d3741080b2e4200a6d8210165c84e7878e9982cb909d30f1d230597210043f43860b2e420087d870c165c840147d08182cb908028f61030597216c61e3a060b2e4209a6e820c165c84014db04182cb908de9da0430597210053ac0860b2e420587e87dd564c855317f08baac990a6e1fa1c75593215361fba0eab26421ea6d821d564c840117f08baac7908122f2117558f2102c3f42ee8b1e420087d85dd163c840187ee82a2c7908130f1d05458f2100536c10a8b1e420587c85dd943c84010ff0abb287908161f2157650f210043ec36eaa1e420087e8759543c84010f90eb2a87908128f2116550f2104c5e43ac8a1e423ca3c8559143c84131b90eb1a8790803871516350f2104d66432869964281f0c5450d32c840117f08baac1908122f211755832102c3f42ee8b06420087d85dd160c840187ee82a2c1908130f1d0545832100536c10a8b06420087d879d764485af4db053aec8908161fe1d75d91210061fc22ebb224200c3c845d7644850b0ff04baec89086a8fa1754d91210061ebaea9b224200c3c545cf644840b0ff0fa96c8908021f61f52d91210d51e426a5b224200c3c545c3644840b0fd0fbaac8908022fe1175591210043f438eab224200c3c75dd164484010fd0fa92c8908161f21f52591210045fc22ebb1a42048
  | 9 => 0x525094100597432a4a128200b2c865494250401c590ca9284a08278bdd9525094104f163b2a4a128200e2f63549425052fe4d02a9284a0803c960552509414bf9238aa4a128239e2f615494250473e4ec2a9284a08034d1d7715094100792a96e2a12820587c859da32504010ff0abb464a08161f215768c9410043e432eb192820493c845d632504010ff0fb2c64a08021f61f658c9410145e432e9192822593c855d232504131e90cb8c64a08034d151718c94102c3f42eec992820087d85dd93250401878a9bb264a08030f150764c9410145e432e8992822593c855d13250529c38caa1a64a0b270f1d065d81410145ec26ebb028200c3c54dd7605040317908baec0a09b68fa1754d81410061e2a2e7b028200a3c8550f60504db47909a96c0a09b68f21152d81410051e42a85b028200e2d5250b605040b0fd0dbaac0a0a461f21b75581410249f426eab02820087e87d9560504010fd0e32ac0a0803550c575d91310043ec3cebb22620587f875d7644c4010ff04baec8988161fe1f52d91310043ec3ea5b226200d5431dd5644c40b0fd0fbaac8988030fa1375591310061ec26eab22620087d82dd5644c4010fd0e3aac8988028fa1774591310045f43ea8b226221a3e85d51644c5bdc38a9b9ac8988021fa1f525913102c3e43ea4b226221a3c84d49644c5bbc68a9b8ac8988030f15370591310245f426ebb1262008bd84dd7624c4010ff0aba6c4988161f21574d89310261f3a0a9b126200c3d74153624c4014db042a6c4988864f2117598931006aa18aeb3126200dd031dc1624c401aa862ba8c498803650c5741893100477c3ac43126209cea625c0624c4019d2c4b80c498803740c570189311cd1f424eca926200a3d849d9524c4014db053b2a4988028fe1176549311cd1e422eca926200a6f825d9524c4014f700bb2a4988da9e201765493110c9f43ee8a926200f1431dd1524c40187eec3a2a4988030f9d874549310061ebb0e8a926200c3c761d1524c401e28623a2a4988021fa1f64549310043ec3ec8a926221c3c74d91524c4010ff0eb22a4988021f21d645493110e1e3a2c8a926200c3c74d89524c401878a8bb484988023ee01769093100c7c402ed2126200d54315d6424c4051b90cb9c8498a13471517390931014ea40ae72126221b2c8454a424c53fe8862a9484988263d21971909316e69a2a2e321262039d4835c6424c40b0fd0b3b284988021f6167650931006aa18eeaa1262098bc87591424c401878eab2284988865b21d52509311cf17322a4a126200e2d64549424c52fe8862a9284988263721d644c9316df0e2a2c89926209acc82591324c401793003126498827171d9524c9314258e422a49926209e4c62549324c46faa8e2a92649880a75a1f714c931014ea40ee09926200dd310dc1324c40917d
  | 10 => 0xb2a8200c3d74dcb655054d87ce9396caa08030f5d172d95414951f420e5b2a8291a3d841cb655054d87ce8396caa080297a0c72d95410052ec18e5b2a8291a76811cb65505254eb02396caa08029ea0072d95410053cc00e5b2a820087e870cb65504010fb0e196caa0a4a8fa1032d95410051ec2065b2a8291a76810cb65504014eb02196caa08029ea0032d95410053cc0065b2a8292a3e84dc3655052347b09b86caa08030f9d170d95414951f420e1b2a8291a3d841c365504010fd0e186caa08021f61c30d95414951f42061b2a8200a3d840c365504014dd04186caa08029b60830d954148d3b40861b2a8200a75810c365504010fd0e106caa08021f61c20d95414951f42041b2a8200a3d8408365504014bd06106caa08029760c20d954148d3b40841b2a8200a75810836550593878e832ec6a080a2f61375d8d410061e2a6ebb1a8290a3e85d53635052147909a96c6a08030f15170d8d410043f43ecab1a820087e87195635059d27d0fbaa86a0b8a8fa1b7550d4155e1e3b6eaa1a82e193e87d95435059347d0db2a86a0a470f1db6550d410070e31ecaa1a8200e1c65d8d435044b2790bb9286a08034d1d77150d410061e32ee0a1a82028bd84dd762504014db05baec4a08029b60875d89410043fc2ae7b12820587c855cf6250479878eaa1ec4a08021fe1570d894102c3e42ae1b1282a6a3c8419662504010fd0fb2ac4a08021fa1c65589417061fba0cab12822587d87d9462504018bce7b28c4a08029b60b65189410063d386ca31282a6a3c84194625052787ae8328c4a0803179cc651894100536c10ca31282c9c757119462504018f4e0328c4a080317d9573189410062e32ae63128200d1c545cc62504011df0eb10c4a08031ed9570189410063c32ae03128200d38545c06250401878e9bb2a4a08021fa1a765494100536c14eca928200c3e849d9525040187b093b2a4a08031b60a765494100637214eca928200c6d429d9525040147f08bb2a4a08030f1d1765494100537c12eca928200c3f841d95250401879083b2a4a08030fd0c76549410061fa10eca928200c6e421d952504018da843b2a4a08031da0476549410063ac08eca928200c3e411d95250401878823b2a4a08031d88476549410061fa00eca92820493e87dd1525046f47d0dba2a4a08030f1db74549414861e3a6c6a92820093c8750d525046f4790ca1aa4a08030f1d9435494146e1e3a6c4a928239a74865c55250401a68e8b8aa4a0b7ed9e0971549414ec9f43eeaa12829bc3c76dd5425040127d0fb2a84a0a470f1db65509410061e3aec6a128200b2d8518942504092790ea9284a08028f219525094104e1e3b2a4a128297f2621549425044ba5f0ea9284a0812cba1d52509410259643aa4a128239d2c8754942504092590ea9284a08038be19
  | 11 => 0x8c801878e8b8acb190030f1d071596320261e3a682b2c640087e87905658c8010fb0f20acb190130f1d241596320261e3a082b2c6409a6e82105658c8014db0420acb190030f1d370596320051f424e0b2c6400a3d849c1658c801878e9382cb190269ba0a705963275d36c14e0b2c6400a3f845c1658c80147908b82cb190030f1d170596320061e3a0e0b2c6404c3c74d01658c8010fd0f202cb190021f61e40596320261e3a480b2c6404c3c74101658c8134dd04202cb190029b608405963236e1e3a620b2c646ec3c74841658c8010fd0e082cb190021f61c10596320051f42020b2c6400a3d84041658c9d5878e8082cb190e297a0c10596320052ec1820b2c6409a6e82041658c8014db04082cb190161fa1f755923254c5fc22eab24649b87e871d5648c94d87ee83aac9190b29b60875592320045fc22eab0c64048bc845d5618c80b0fd0bba2c3190021f61774586320061fba0a8b0c6404c3c74151618c8014db042a2c3190022fe1175582320245e422eab04640587e85dd1608c8010fb0bba2c1190030fdd054582320261e3a0a8b046400a6d82151608c8010fb0f3aec8993a69b60a75d913202c3fc3aebb226400c3f845d7644c80187908baec8992921fe0975d91321451f42ea9b226400c3d75d53644c80b0ff0fa96c8990021f61f52d91321451e426a5b226400c3c545c7644c801878a8b86c8990161fa1f75591320045fc22eab22640087e871d5644c801878ebba2c8990021fa1f525913202c3e43ea4b2264acc5c76dd5434c95b63d09baa8699252c7a176450d3204ce743ee4a1a64e8f0c54dc9434c801a9eea3928699003531d47250d3273f862a0e4a1a6400bc5811c9434c80179300392869939b471537150d3272e8e2a6e0a1a64a693e87dd1524c953e1865ba2a4992870fdd874549327261f3b0e8a9264e3c3d761d1524c943878ec3a2a499003471cc745493253786190e8a9264a187e87d91524c8710fb0fb22a4990a30f1d364549320043fc3ac8a92640587c87591524c851878e8b22a499003471d3735493204da7416e6a92640095c8750d524c8134b90ca1aa4990a3471d1435493204da641286a926400c3c75d91424c8133390ea1a8499026a721943509324a68e3aa86a126409b8c8250d424c8512d90ea9284990e31b1d9525093200717b22a4a126438d4c73549424c801e1a86a9284990022fe1175d85320245e422ebb0a640087f855d3614c80b0f90aba6c2990130f1d054d853200536c10a9b0a6400a3c8454b614c80117f08baec0990122f21175d81320043fc2ae9b02640587c855d3604c809878e82a6c0990029b60854d81320051e422a5b02640493e845cb655052547d09b9ecaa0a468f61373d95410061f3a2e7b2a8292a3e841cf655052347b0839ecaa0a4a8fa1372d954148d1ec26e5
  | 12 => 0x28fa1b7550d4255e1e3b6eaa1a849da3e86d954350937878edb2a86a10038718f6550d420070e32ec6a1a8400b2d851c94350801878cbb8a86a10030f1977050d420249f43ee8a928439c3c76dd15250859878e9b1aa4a10e69b60b63549420049e43a86a928409a3c8650d5250809878eca1aa4a1263c3cc943549421cd9743ee8a928439d2e87dd1525081365d0dba2a4a1026cb21b745494254f16436e8a928435e2f76dd15250873a5cedba2a4a10e74b1db74549421cf163b6e8a928439c2c76dd1525080165b07ba2a4a1002cb607745494200596c06e8a92842dc6c76dcd525087365909b9aa4a10029be1973549421cd36432e6a928429c6c765cd525080165f08b9aa4a10e6cb2117354942166363b6c6a92840096f8758d52508632d90eb1aa4a10a31b1d9635494276f2631ac6a928400d2f8750d525080165d0ea1aa4a1002cb21d43549420069643a86a928409b2e8650d52508136590ca1aa4a10f38bdd94354942026973b286a928404d2c7650d5250873c58eca1aa4a10130b1d943549421cd97c1a86a928439f0f8350d5250931e1ce6a1aa4a1003c35cd435494200787b1a86a928498f0c6350d525080165f02a1aa4a1002cbe0143549420fe363b6e2a928439b2c84dc552508014df0cb8aa4a10e69b21971549420de363b2e2a928400b2f845c5525087365908b8aa4a10471b1db70549421cd96426e0a928400a6f865c152508734d90cb82a4a10371b1d9705494200597c22e0a928439b2c845c1525094d87ee832ec2a12770f1d065d85420f536432a5b0a841ea3c8454b61508738dae4a96c2a10021fa1f65585420043f438cab0a843196c8754961508354d90ca92c2a125f9918552585425361fba0cbb02849dc3c7419760508214d90ca96c0a10428f21152d81421ce36b92a5b02840587e86dd560509370f90dbaac0a10021fa1f65581420043f438cab02843196c8754960508194d90ca92c0a125b9a18152581420243f43ee8b2c640483e87dd1658c95387ee5ba2cb192a70f5cb74596325351f424e8b2c640487f875d1658c80987ce83a2cb190030f5d074596321c52f418e8b2c6400a5d831d1658c8134dd043a2cb190b69b60874596320053b408e8b2c6400a75811d1658c8014f5003a2cb190029e600745963254d1f438e8b2c6400c3e871d1658c801c3d063a2cb190038760c74596320061fb98e8b2c64acc3e731d1658c80187ae63a2cb1933b0f1cc745963253717410e8b2c6400e2d821d1658c94d87ee43a2cb1929b0f9c874596325361eb90e8b2c64a6c3c721d1658c801c6d023a2cb190038d60474596320071d400e8b2c6400e39801d1658c801878e9b8acb190028fa1271596320051ec24e2b2c6400c3c749c5658c8134dd0538acb193b29b60a71596320051fc22e2b2c6400a3c845c565
  | 13 => 0x61fba0c8b02a404c3e741916054809878e8322c0a90029760c64581520053ac08c8b02a436a7a801916054801c7480322c0a90024fa1c64581525ee97b90c8b02a400a3e87191605480187d0e322c0a900387a0c64581520070ec18c8b02a400c3e731916054801878e6322c0a92f38b60864581525ee1fb90c8b02a400e36811916054801c6b02322c0a90030f9c464581520061e388c8b02a400e3a801916054801c7300322c0a93bf0fdc064581520061e326e6b02a400c3c74d8d605486d0f90eb1ac0a90028f21163581520061e3a2c6b02a400d2f74dc96054801a58e9b92c0a90038b19372581520061e326e2b02a400c3c74d85605486d0f90eb0ac0a90028f21161581520061e3a2c2b02a400e3864d8160549ddad6e5b02c0a90030f1d373596421cd1f424e6b2c8400a3d849cd659080147f08b9acb210e68f21173596420061e3a6e2b2c8439a3e849c5659080147b0938acb210028fe1171596421cd1e422e2b2c840087e870c565908010fb0e18acb210e68fa1031596420051ec2062b2c8409a6e820c565908014db0418acb210029ea0031596420053cc0062b2c8400c3c74dc1659087347d09382cb210028f61270596420051fc22e0b2c8439a3c845c165908010fd0e182cb210021f61c30596421cd1f42060b2c8400a3d840c165908134dd04182cb210029b60830596420053b40860b2c8400a75810c165908010fd0e082cb210021f61c10596421cd1f42020b2c8400a3d8404165908014bd06082cb210029760c105964204d3741020b2c8400a6d820416590801878a8baac72129a8fa175458e420061e2a6e2b1c8400c3c54dc16390801a58e9b9aa5210029be197354a4200597c22e6a948439b2c845cd5290801a58e8b9aa5210034b1d37154a4200537c32e2a948400b2f845c5529087365908b8aa5210034b1d17154a42006963a6e0a948400a6f865c1529080165f08b82a5210e6cb2117054a42006963a2e0a948400c3c545d5619094d47d0baa2c3210030f15373586420061e2a6e0b0c8400c3c545d5609094d47d0baa2c1210030f15373582420061e2a6e2b04849ca3e841cf655093747b0839ecaa12728fa1071d95424dd1ec20e3b2a840087e870c765508010fb0e18ecaa12728fa1031d95420051ec2063b2a849ba6e820c765508014db0418ecaa10029ea0031d95420053cc0063b2a849ca3e841c3655093747b08386caa10021fa1c30d95420043ec3861b2a849ca3e840c3655080147b08186caa126e9ba0830d954200536c1061b2a8400a76810c365508014eb02186caa10021fa1c10d95420043ec3821b2a849ca3e84043655080147b08086caa100297a0c10d95420052ec1821b2a849ba6e8204365508014db04086caa129b0fdd065d8d424ee1e3a0cbb1a840087e87d9563508010fd0e32ac6a1
  | 14 => 0xf825d9435480187f083b286a90030f2107650d520062f418eca1aa400c5d831d9435480187c863b286a90030f10c7650d520061fa10eca1aa400c6e421d943548018da843b286a900317cc87650d520061fa08eca1aa400c3f401d9435487127d0fb2286a90128fa1b6450d520061e3b6c8a1aa438b1e83d9143548732b90eb1a86a9003871916350d527b5a7c12c6a1aa49ac3c64dc9435491f878c9b8a86a91cf0f1937050d520071b30ec9b0aa43787d87193615480987ce8326c2a90030f5d064d85520052ec18c9b0aa437a768119361548014f300326c2a93d70f9d864d85520261fc38c9b0aa400c3d8719361548098790e326c2a900387a0c64d85520070ec18c9b0aa400c3e731936154801878e6326c2a93cf8b60864d85525361f390c9b0aa4a1c3d72193615494d878e4326c2a90038da0464d85520071ac08c9b0aa400e36211936154801c7500326c2a90038e60064d85520061f380c9b0aa400c3c701936154801878c8b9ec2a90de1f61f63d85520051e422c7b0aa400c3c645c3615487327d0fba2c2a90030f61b745855200697c16e8b0aa400c3f62dd16154801a5ec5ba2c2a90030fdd874585520049f43ec8b0aa4f4d2f72d916154809878e9322c2a90030fdd064585520261f3a0c8b0aa404c3c7419161548014bb06322c2a90de9da0464585520071b208c8b0aa400a7980191615480127d0e322c2a935b4bdc864585520051f438c8b0aa400c3e871916154801c3d06322c2a90038760c64585520061f398c8b0aa400c3c7319161549abc5b04322c2a935b0fdc864585520071b408c8b0aa400e358119161549e787ee2322c2a90038ea0064585520071cc00c8b0aa400c3e701916154801878e0322c2a90030f19373585520061e3a6c6b0aa43787c8758d615480147908b1ac2a90030f1d1635855200697ba6e4b0aa400d2c74dc96154801c58c9b92c2a90038d1936158552796b3b96c2b0aa400c3c64dc16154801c74c1b26c0a90da1f61c64d81520261f3a0c9b02a400c3d7419360548014bb06326c0a90029d60464d81521b53d400c9b02a4f1c3e76193605480987f0e326c0a90030f61c64d81520261e438c9b02a400e1e831936054801c3b06326c0a90030f9cc64d81520061e398c9b02a4efe2d82193605494d87ce4326c0a92870f5c864d81525361e390c9b02a400e36811936054801c6b02326c0a90030f9c464d81520061e388c9b02a400e3a801936054801c7300326c0a90038e88064d81520061e322e7b02a43687d87d8f605480147908b1ec0a90030f19171d81521b43ec3ec3b02a400a3c84587605487327d0fba2c0a90030f61b745815254c9e436e8b02a400d2f82dd1605480187ec5ba2c0a90034bd8b74581520061fbb0e8b02a40093e87d9160549e1a5ee5b22c0a90130f1d2645815200
  | 15 => 0x3108c8a92f2cb60a60191520051ec3cc0322a400c3d87980645480147d07300c8a90028f60e60191520070f39cc0322a400e1d73980645497947b05300c8a90038b60a601915200717394c0322a4fce2d72980645480147d03300c8a90028f60660191520071b38cc0322a400e35719806454801c74e1300c8a90038e5c260191520051fc38c0322a400a3e83180645480147b06300c8a9003879cc60191520070eb98c0322a400e2e7218064549f7c5ae4300c8a90028fa0460191520051ec08c0322a400e36711806454801c6ae2300c8a90038ea0060191520071d380c0322a400e3970180645480147d0d980c8a90028f61b30191520051f43460322a400a3d868c0645487327d0e180c8a90024f61c30191520051fc3060322a400a3e860c0645480147b0c180c8a90028f21830191525359741060322a400b2d820c0645480166d02180c8a9002cd604301915250d1e43440322a400e3860880645480147d0d880c8a90028f61b10191520051f43420322a400a3d86840645487327d0e080c8a90024f61c10191520051fc3020322a400a3e86040645480147b0c080c8a90028f21810191520058f41820322a400b1d83040645494d65d04080c8a9002cb60810191520070f31ec9b1aa43887d87193635480987ce8326c6a90030f5d064d8d521c52f418c9b1aa400a758119363548014f300326c6a93eb0f9d864d8d520261fc38c9b1aa400c3d8719363548098790e326c6a900387a0c64d8d520070ec18c9b1aa4f8e2d82193635494d87ce4326c6a92870f5c864d8d525361e390c9b1aa400e1f321936354801c6d02326c6a90038d60464d8d520061f388c9b1aa400c3c711936354801c7500326c6a90038e60064d8d520061f380c9b1aa400c3c701936354801878c8b8ec6a90030f19170d8d521cc9f43ee8b1aa400c3d86dd16354801a5f05ba2c6a90030fd8b7458d5200697b16e8b1aa400c3f761d1635480127d0fb22c6a93e74bdcb6458d520261e3a4c8b1aa400c3f74191635480987ce8322c6a90130f1d06458d521c52f418c8b1aa400e1e4319163548014eb02322c6a90029e6006458d520049f438c8b1aa4e4d2f72191635480147d0e322c6a90030fa1c6458d520070f418c8b1aa400e1d8319163549f187ee6322c6a938f8b6086458d527261fb90c8b1aa400e36811916354801c6b02322c6a90030f9c46458d520061e388c8b1aa400e3a801916354801c7300322c6a90030f9c06458d520061e380c8b1aa400e1c64d8d6354801a5ee9b92c6a90034b1d37258d5200716326e4b1aa4f7d4f73dc96354801878c9b8ac6a90030f1937058d52004b6c16eca1aa400c3e84dd9435480187b09bb286a90031b60b7650d5200637216eca1aa40087e869d94354801878c93b286a90024fe117650d520061e322eca1aa40096
  | 16 => 0x1d915254d97414e3b22a504b2d829c7645480187cecb8ec8a93d2cbe0971d915254d96412e3b22a400d2f725c7645480147d0c38ec8a9412cb60a61d915247e1f3b663b22a490c3e768c7645480127d0e18ec8a90024f61c31d91520051f43063b22a400a3d860c7645497f87cec18ec8a92a6cba0831d915200596c1063b22a400b3a800c764548016730018ec8a929b0f9da21d915200697b96e1b22a400c3e769c3645495365d05386c8a940ecb60a70d91520061f3b2e1b22a4f0b2f825c3645495365904b86c8a90034bdc970d91520051f430e1b22a503b2d8298364548e787ced986c8a91d30f9da30d91520049f43861b22a40093d870c3645480147d0c186c8a90028f61830d91526c61f3b061b22a4a9b2e820c3645480165b04186c8a9002cda0430d91520059ac0861b22a4a6c3e7688364548db87ced886c8a91bb0f9da10d91520049f43821b22a40093d87043645480147d0c086c8a90028f61810d91527561f3b021b22a400b1e83043645480163b06086c8a92a6cba0810d915200596c1021b22a439a3e86d916454801878c9b9ac8a940b4bdd3725915280f16326e4b22a400c3c64dc56454801878c9b82c8a938ecb60a63191520051ec3cc6322a400c3d8798c6454801c3ce7318c8a9003875ce631915271d1ec14c6322a400e2d8298c6454801c5ce5318c8a94038b5ca63191520051f40cc6322a400a3d8198c6454801c6ce3318c8a90038d5c663191520051f404c6322a400a3d8098c6454801c74e1318c8a90038e5c263191520051fc38c6322a400e1e8318c6454801c3ce6318c8a9003875cc631915200717390c6322a4ffe2d7218c645480147d02318c8a90028f60463191520071b388c6322a400e357118c645480147d00318c8a90028f60063191520071d380c6322a400e397018c64549434790d990c8a90038718f32191526ad96c14c2322a400a3d87984645480187b0f308c8a90028fa0e61191520051ec1cc2322a400e1e739846454801c3ae7308c8a93568f60a611915200716c14c2322a400e2e7298464549fdc5ae5308c8a90038d9c661191520071ab8cc2322a400a3e80984645480147b01308c8a90038e9c261191520071cb84c2322a400a3f87184645480147d06308c8a90028f60c61191520070f398c2322a400e1d731846454801c5ce4308c8a93f78b5c861191520071b408c2322a400e36711846454801c6ae2308c8a90028fa0061191520051ec00c2322a400e3a701846454801c72e0308c8a90028fa1b31191520051ec3662322a400a3e868c4645480147b0d188c8a90e64fa1c31191520049ec3862322a400a3f860c4645480147d0c188c8a90028f61831191520051e43062322a4a6b2e820c4645480165b04188c8a9002cea0031191520059cc0062322a4a1a3c868846454801c68c
  | 17 => 0x400801005405000001402000801400800008002800401002000800001400803401808c02c0000180040a000000c02c0000e003014c05000800c00000400002800001400000006c00000001000000401000001003400801807c01800802800800800000000006801c00000000002400006402800800c00800400c00001400c0927d08b96caa1ab28fa1372d954355d1ec26e5b2a8600c3d74dcb6550d4d87ce9396caa18030f5d172d95435651f420e5b2a86aba3d841cb6550d4d87ce8396caa1aae97a0c72d95435652ec18e5b2a8600a76811cb6550c014eb02396caa18029ea0072d95430053cc00e5b2a86aca3e84dc76550d5747b09b8ecaa18030f9d171d95435651f420e3b2a86aba3d841c76550c010fd0e10ecaa18021f61c21d95435651f42043b2a8600a3d840876550d574bd0610ecaa18029760c21d95430053d40043b2a8600a79800876550d5947d09b86caa1aae8f61370d95430061f3a2e1b2a86aca3e841c36550d5747b08386caa18021fa1c20d95430043ec3841b2a86aca3e840836550c0147b08106caa1aae97a0c20d95430052ec1841b2a8600a76810836550c014eb02106caa18021fa1c10d95430043ec3821b2a86aca3e840436550c0147b08086caa1aae97a0c10d95430052ec1821b2a8600a6e820436550c014db04086caa180e2f61375d894300536c16ebb128600a6d821d76250c010ff0ab8ec4a18161f21571d89430043fc2ae1b12860587c855c36250d4d4790832cc4a18021fa1f65589430043f438cab128706c3f741956250c790fb0fb28c4a18029b60b65189430063b38eca3128600c7a70d946250d4d47908328c4a1ab70f5d065189436762eb98ca3128600a6d821946250c018ece2328c4a18031e9c0651894300477c3ac43128600c77655c46250c018e8cab88c4a18034d15171189430063db2ae03128600c78655c06250c01a70a8b80c4a1b3b0f1d065d854301c5ec26ebb0a8600c3c54dd76150d1f47d0baa6c2a1a3e8f21352d85430061e2a2e1b0a860087e87d956150c010fd0e32ac2a1b3b0f1d065d814301c5ec26ebb028600c3c54dd76050ce747d0baa6c0a19ce8f21352d81430061e2a2e3b02860587e86dd56050d570f90dbaac0a18124fa1375581430043f43ecab02860087e871956050d4b2df04b9ec8a90265b20973d91520051ec3487b22a404c3e7690f64549472df04b8ec8a90265b20971d91520051ec3483b22a404c3e7690764549452df04b86c8a90265b20970d91520051ec3481b22a404c3e769036454801a5ee5b9ec8a90030f9da73d91520068fb9ce7b22a4a9b2e829cf6454a0b65b0539ec8a90030f9d973d91527cd97c12e7b22a4a9b2c825cf6454801a5ee4b9ec8a90028fa1873d915282d96c14c7b22a4a6c3e76ccb6454801a5ee5b8ec8a90030f9da7
  | 18 => 0x4005c05c00005000c09003c01802800402401801400001000c07400801c01c0040440400000000100500bc0040080140a800801002001000c01000003807c00400800800002c01c0c800002000c00000401c04000400c0040540000300380000140200000000000d402c00001c00000400802c02c00400402001c00001400801c0a002006c00800400000004c00c0080340000b40a400001801805801809809c00005400000005406000801c00000409402000004807801401004001000c0240000000180340a800003000000c00003c0cc01800400009401802807000800001c00000400c00800401409401000c0000500000b000400c09c01c02400c0400100080500880040180340d804004800c00000800c00800000800c03400004801400000809000010009c00001006800001401803805401801c00400000c03800000c02002400400808800400800001007801800000000c00802800000404c03803000000802801400400c00c0000a400000800c00400400005c00c03c02001c02c01c01800003802007801010401001004c00401c0000200280000200000ac00400000800000000400800803802400000000405802000c0000100000180300040480100180680a80dc02005002801401801001400007003808400000400402800c0000bc00c00801800c0200100040c800400400000000004000000007407001000400003401002c00802400003401000403401c0dc03000c01c0a000c03802c03c05800400008805807000400800400001403003000000402802c00803000c00814001000000c0a004400000800400006c00009800000c00401404c00001401012404805801000403400001801800c0100180080f400800000402009c00001c00829808800001c00400003002400400803c01c00400c02400001002c00400800000400c00001402400001003c07c01007c04801402000c02402c0f40a801008c01c0040000740000040a801401000c0140c80000140000100900e400801c06000004000000c03000001c00400802000000009400000002005400001001001003400000c00400000000002c00400802403c0dc01800000000c00000000403401404007403800c05c00c00000001c0e400803002c04409c0000040000000000080d001400c00001802008401800001802000000806802400000806802000002000008002401c07c0000300ec03c01800400800402000001c06006c16800004403800802000400003801c00c05800000c0a401c01403c00400000001800000403400402c02000407c01000000c0ac01c0080440040280280200940000d401400801800005801000808800c00403803c02c01000c03803003c00001805c00c00400400001000000406800c01400800c000004018008008004080084004000078020
  | 19 => 0x6da00000023a400c3b6110077c000000000033000000000000007b06371cc00007b24793d7916c28a641000000000000026ca1280005ec0ba0b5c8d204c3d300000005be00015d800000011a079816600d00019f91829a14ad07c01365eb48f225cac0759456023d1465342c39ef401896a2d68aa80b24412462060e907d326b905078c1ad1a38b7cb700000000684c2a8894a6a0ec8464d20001084bea85c0141b10a8833e16995c8606000196a41c46e9610441e9042062d106102c90c24d185000012883a1838e440029933dc1dd459a83727d904525623f3ae99e448a125298171cbee01e468a14076000047982ec3522ab2259a08a8e03143d10f50f02c717024981f080c276048439c7d71d58a10d0c06e19c14200389134ab82b029414903696c46d47fe000120816c79b4759bd133837632606506a446241898713086fc169159cf9a3790e40d5c7284f94a911100000004d7865cec061647c0fd821c3750000ad46c09a32b8115c02409a00d8fa4c16492396864877a9050aa853c1e810700390a477c000395162c1cc0001f815e53402de427046c7b8177143033c0ee69a458a60426e99b2831c3489235000005cc6be7230001bc000065f47e80013586e60c38000eca95f3a61684d9853a35c8e2d1ee88f084955868221446e9adcb5000007f80003ec92a4b497012780a62e6000025060509ea2384c694c170941d2886ac250188852847625788f08cc04e00023591b67bb49c8e8c83a93800c000057e00042b91682f432311182910d04e03bc9fe40000002008af80440da12217688544d03ea98a4e806471628f903a273313899344027ac0a8970c41427a2140028b5e0003769fc4f440e017e800000000005894306406d100000000004b106ca6a033a7320000000f228ec000128c072464025947067a2f042886c017a58f00880010788a61c4a1502680003bb0ffcd6200027406d0fc43aa0c78ab0188460191000000000032a80000002591c40fa0f8a16d1c903445b246e3a492b420036f3af04151fc7973378fd4bfc70019d94b42fc7fa30111f46e878935786585b05c61dd0bf89c638f29c81d934e2f513a8df800097245f83ecb4856903d00004dc15b3f020a064224b38f0a0c69c7ad3fe88a423a8ed37e800007699942b1cbc9a88123f488640584b00000000c8659e1b421a899885e000252cfba1710001a3800081c0000000d2099d2630000e4000044117082b800025e880ce4a0003ec80010040001eb9cc0bb22611fe9ed0652976365000116667632414f86b23a11cd8d9ce5c12b3e0002c01401401800805003c00c08800803805000001c06c00801800000000001c01800002400006401000c01c02401002c00800814c00001801c08802c0f404c00c00000004400801001c0180140040340680240000100100000
  | 20 => 0xa2a10000f908a73b6895c6a800032c1bd800000000013e000051f11d01d4a1275a000014808887e307028ca1e21a47e03400005f10000b6800062503780000006683940d78cc800043ba658b4a41008fa69000000000010b00006703330000da000000000009080aa07ca2a800000024e875cb5c31a0eb0a700000003fe00012bc8bd34285ed2a6714235823405e20614c0000fa4127000000020c0001801b482403b40b200005022cc28507fc75294f1680b2073c81621f80008ac85920280010b00004779e54b2a4cf3510e649528e323d22f8000000445174440865a29b83f899296d41c94692fa00012a039cc4e4fc43e85c87a847849e977d0646b62ba8c648a07110a59a612403ce000000121e6013eb0fd004696b00200000002a744d86710aa2e737900000002523a880009c2511000125816e00047200000001e32a6800114800000000012ea15e3b600008685824c6200d1063e34032074ea442d1f9235c0000001e207bc27499217895ec0003b1000209c00063500012cc16a0000b3157502a88600003f05d06913d19514db258548f80000ac26224411cc00074e0002000cc495d466915000072743793150681683699ed40005f300011ecbd00871219f1000015f0000000ca200001e958c0009ae4be080115c34b2d9124d2c65cb0c81e207da95835aa360aca1cd3d28fe8af0000000238047c4f3240917000006c3668a301ba79c20721b126e000000122c00026915e94cc4702c643a8dc882636e38e91300169ab33ea0940006c30da8a085920971361928efa30f2dc8a2074e2050ca9250c6c0b21a01b252424a6171260c0ba4fa1c116349865711568a593346bd1108fe06309681e199086ba3a233d21200b661a2279ad12088963141ab8f1c4033710eb4d783311529610cd23b804596044fe1b70400d34cf65ce02a8180a0007b1401531310524000075435e4333c803ad1b27173ee02c02460000460a2d2a022b4301d6c1aa17c06c1c1530065e0001d2c000978017061000094847316e800081b23a000065846c033800072e0000000000dd80bf20ba4c868c6381b08d303bc9893c61bd45266eb09f9cc4e386ab0c481788b28e149f9fd8726495079a3400a60c828a98e488e6cf306a440b7e03e3f91b80e3021821ca5711ea10b2de18408aa5640ed9ea40842644178a8407473e026979849088849400d867e0af2d48854ecc37b3bc02ac6901dc04105a4fc611e24f21a44586961d28bccf348ea18483384d48452b41034a367aa41819fd17453f3c7837889a00002004ec9d68103549bc521600344d103c72c56b3b1129456e3353b595f0ab849730195b4ea670600016691400001a28000fa264b221a08c28200000007a00663714578000f9600025100640cc84040701449844fd00017152de23d19e195c8806e5145000
  | 21 => 0x8a765623e08014f3e0291950bac00000027a86e8ba02e4000132cd845f602280005aa03000015290104e90451d5cf0a31125096808d47be0000f7c00052a23fa324b9e87c40f17885f21e10001feca8600004c1e782de65c098249d05400045a2198d3e66d48b98b02b22e62f3981c1e092c4ba015c1ca26739a000038c2110e19a9c04c8a90001a347c22d4410902404895100000003d647220b18e844e00019ca25400000021e1c10c4650d290953cd900004c59c88ec267c000106d32a5cd0001f3c0009304c508e4b901f4000000000004f17b9dbc9ee1bf0001c2c000000000000112600015e0000fa06ef07401ac00000046000008c21031c383b423460600004c918a00021f21049721cb41aa27c0002733b38f68a086310001878c800001f991d487668410917c08008e21c50978e8a7581ad1408e4882b0b394e00003b749d0710f00000423205025a801344a0d896800017b24891903c8000000026c1fa3271ea000098f1e297f41a649128b8dcc60a6e14a495543f659b4860ff0bac1d00d0178cf865731598c351781293bf1a5ce9e41f06097e455c4a40dd848800066347a24b8af462444c082c000852389967c8b03bc0328b582182db0000cd0d541aa42d1d1c79a00029404c45882021b21ba0bc225a00014bcb1c2221521ab52e07e14771994cee0001ce9ce526276a12895210e81b904e9cf4492146291945812a7070002678fe069d3358fac738838243a1b47486c5488837024c1570c997ecf8e21f35d8904d1627d38721341d89851650000f9803200000f02dc00030a000079e4d53aa0ac865c63e3f40874e0410f00025645c63c200025c45e83b320a96400fe3b9212160c0347f8000060c7ee5bb0c506f0ce4000000000000026f0001bdc0000d60db136000016a18b0c091940002010ff92306d73818e38a8c81913000000006190000df002e5190001a6ca4e630000032c65e0002da030068462e23e23e50e66452129edc18e81343b00012f60fd0000000f2c5ab49b000000061f0000000f26000421127c7f654924c81c40008a20c7231896a6d413b12f034a4060979958c000000fa95f88e20143e526982ec0641f2937400072900021b80000000cd218c5503044380c406c40000c081600c417500008580005a2246800035c0100b108cd19e28d37480000c20ef09200004f89732ee835d09e0000f51498c36982000027c5700003ef000000000000008791085f20d1a21400000045c8000c2600048c80000001c1023000090a50327800240000002ff95383640d40ed00000005a621c1780aa2085000086c6d65130000000000844000000088a88d0dc1754dba73b0cc04a80005e43f39f68170000000191000000000009ed1b86b81f797500005d700000000000a836080000005990000c18f0c0a111900001a47b
  | 22 => 0x9040380000003a00000000b944e640b879c4e008e00000012044421a21eb924877f18a0dfd0ca6813591c24a3a80d1aa8ba89640f71180764b1891535202491b43b50000cace183cb46a16c00004a80fe089918e7812480054d805803d99b5928233243200000003123231e086a229d414800023016b34a2284fb67550f68314ca04a701c0244a808430de85111ca5292eda2648de60c46709e044a01326b0000b664c000004205744770e39b388940000cd80010fe99732da0b80546db1549068e10186379a4d09e45200e924205448242fa0bb85803582b514d473e69e27f8b950e219e2c8872448c289120104857232845b9f18aa03ea2fd0600000955000155cdf60003090324dfc0f60001a312cc04a05a25e42ac6e70868da4602135275108069e09c44f1a80b581402970000c127210721fb0a243bb3f31ae8e7869214797791187193f2250ca168de00019b842e10a00004643c81a70000000a2830b000185c0000000000000b2400048088b4f283db0001d04f1474200000010223d638a800000048e000237c0004484b1069027c8051040ea01e22350000d940007770001598e0215a00000009e877321aa6887a245d0000a1d16400000011780007eb3bd0df485666a1938f3110255814295491aa2b40ac23e80108ad4a50c380b40000001224b6e00034a9fa8ef61cf4439d10ab47f32ba0f54d4a933377150477e7b23ae10291701c01260d583f21a80249e647f20681768ec893838626702a4c4263b1d72438d8e12e4c31e8020882d0168b092382f21298a6c0e09b12aa09545760832f696580425612e21d40c643ee42f8e0d24a6a61e39f24e3e2fb0bfa0684ac3c027b0e5525a42225d901045e2f82130b7427860a0a907b8b6a68720620112ac83d31005748a25dc2ca1c3c99431f2ec2590a626e324c16f534a99f308800004031e31a0688c103153891a84ba663317796a8e7e3de08e251c95823b05c81205320a536f0a8c6e07f728f199ca582cb2ce96240008920001afc6d835c0f492a8b929452771d7c4b60002c4000104465236d0ad923428e042102066e3af3498d9890626509618bca568b00000c3000000017d1ed837c2d14c71310f1a3172ce0abc59c8b50d9a330c544ab3ec000000034939581a400083e21787946f00ee37d000064a86b2b71964ab67433c922509b66b036fa03c0000004659ce84385ee218014004e2dc134044c22a0003ba0a7c7ba67300019c52360ae35f00006a64b80000d8d16c5a74a30000cf01ac39304080004190aa1fb471a000344000020201d24da4003fa71a0000bf10e41f70000c6c53c8f6424a3c43220002a5800052e00000022ac000593000074cf9c33001580003e697f2cc1ec4fca7c2189800000000026d1be4412385044862ca0a0000001a0000038c00010609744b704987
  | 23 => 0x9900ba00700008a456f0651cdc0000003ce8bb0ca658a29e981044883f33099b00001f1351937c19a1d84bd00007c411030c1b9000017023380006b670a0399a3cc9257d46112d90ce17900014952c00000000ac48da133000000008e0a24480458ba469909c0970bf81603b40e00abe185075093c00082007d156400095b000000103e0001e90534f4e7ef483109d2ca3e63b21ffc83c4be29b0de89a63d044e217483887b3b910c84ba7a121d1874bd220700007292120994a01c58fa83c139a8a4800038103c227509864f4c681c802c03f3a3071400000003e0bfc0000000b298f40007b92d19e60284000021800120625033a01a92d8336000234c0003ec1f3a61c0008e7363000000074d247800029c05c01a0000cc05f80000a804da0e914a9da4edc000000000000072c05e1b70a643430ff015045c0f21608750df04de11501f4daa00000012007e25970000000f7e57713ca5f800033a0000c9803e60f4c826c09824d12b60b0c0006cb0bc038c0009143a500000006ff03a000000063c32e9228c567b00129dc493424745d90d88fc1f20d583087580e13c38d2836271b06f9df00000811f020250660000501ba806a0be0318834000553107829c00009e1188928d380000000000a2000f00000003c011123182b4f164e539b20b0f56161287066449c18249f13b4d145c11e525b80822130710f2515029a26688a11f643149494f03c4000000067c2240003b1a47400000007a8908ca827e49d98981b63331cd00012a87f4000045c00094204b0620f7832422f81f846c0004489a0c63814301b9acc0006d84a7202c0005224791370522586429817d1867100c616d914a2a60001fd525e0004d693f85d2000232858d1880002788a4000000033a85f44e89aa00004e400051840515fd11600012c1d583f026b0f6212c00014c1c2051c0004c700000007a65e500022010c46a8167800000000047fa4d400008600017a82d800206309dc0000794b3a428f084bf2299dc108e5ef0a9a6603ba25f43c89c8fdc4e22af11a0c7e18d4d4a65061042e1d323a10c200015823482281484bb940488c9162739f7c0000003c193bc0001a61bb800012073825710dc41c2664c8854104c407227030d1e090d2720c750b6912238000039800049180000003
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1465921537158d200050b648549d9434814d839801507650d200060d2047458d524800183474e0563549205364aa0874dc1524801982c87d915250920006831508650d324800142d9215276505205360e600541d941480014c5920c6764c52000534640319d931480010d5980c4764c52000531648311d931480014d1900c4764c520006891508650521480054c49758d31485205354a250751c9404800194b7560c7250120006521d5831c94048001b085460c725012000658dd5811c94048001960756047250120006c8151811c940480193289854942501200054a25d5250940480139288754942501200064a150874c940480019285421d215012004e5221d524c9304806da4886549324c12004f121d9524c9304816d70894549324c12004c72261744c930480134c8965d1324c12084f42151744c930480032c89660d214c1200055464c105d764440015619204175d91100055464c10dd564440015619204375591100050b64854dcd644400982e7460854d8d100060b5d182153634400982e746085458d100050b64854dd9434400142d921517650d105360b208545d94344001551930437550d100055864810dd5434400981e871536350d100058364854d8d434400982e7460854d89100060b5d18215362442119308404175989100055464c105d6624400156192041759891000474a6010dcd62440015c19204373589100060bdd182151624400184c7360854589100051364854dcd624400155193041751891000558648105d4624400159193041741891000568648105d062440011d198041731891000570648105cc6244211932870437454910005c464c10dd1524400172192043745491000507e4d761d1524400141c935d87454910004cc660101d15244001711930407454910005c8648101d1524400903c9421d64549105360b2087458d524400182c74e0963549100060720c74589524400181c74e0d62549100050b648545da424400181c54e0d76909100055464c105d642440015619204175909100055464c10dd5424400156192043755091003e0b21d64549424421193084041758c9100055464c105d6324400156192041758c9100053464c10dd932440014e192043764c9100043c660101d932440014d193040764c91000538648101d932440072c498589324c51001cb2261624c930440072d098589314c11001d3425d624c5304406d95087549314c1101b694219524c5304406fc5076549314c110595c4251524c530440031d09760d214c11000cb42598348530440051d0985cd314811001534259734c5204406d96087549214811004e98219524852044013c60765492148110575c82515248520440132e098591214811004d3825d64485204420fe2054591214811000c7825d8348520440051e0985cd2148110
  | 1 => 0x50764c841d952500014359121076549400050ea40841d9525000982c8490876549400051a64a801d9525000142d9210076549400040f2607650d5250009838861d170549400054664c745c15250001531911d170549405340f25c86549425000182c87e1952509400244ba5e86549425000182c8721952509403a60b21f6354942502199288760152509401cd8a2598054942500215289754b70509400240fa5387d96325000983886151708c9400054a648545c2325000142d92153764c9405360760c541d9325000142d9215173d85403748b2615250b615000103c9721952505400050b648549d93150001645920c7654c5400059464031d95315000983a86153704c5400054a64854dc1315000903e94e1f65c85400260e218545c321500015299215170c85400050b64854dd9215014d83581150764854000552648305d7644c001551910c175d91300055264830dd5644c001551910c375591300050b64854dc5644c00982e7460854d89300060b5d182153624c217918840c1759893000552648305d6624c001551910c1759893000474a6030dc5624c0015c1920c3715893000552648305d4624c001551910c1751893000562648305d0624c001591910c1741893000474660305c4624c0015c1920c1711893085e46a1c30dd1524c001709920c37454930005c464430dd1524c001437915d874549300050d245761d1524c001319980c07454930005c2648301d1524c001711910c074549300050b648545da424c00183454e05769093000552648305d6424c001551910c175909300055264830dd5424c001551910c3755093009e0b21d64549424c00982e7460854d85300060b5d182153614c00142d9215376505300055264830dd5414c001551910c375505300260da1c54d85414c00162592153615053085e46210305d7214c001549920c175c853000554644305d7214c0014c9920c376485300053464430dd9214c0010d9980c0764853000532648301d9214c0014d1910c07648530026071d2831d165c800981c7460c74597200260d1d2811d165c80098347460474597200260e1d1801d165c800182e8760874597200068360d821d165c8001a1583604745972000689609811d165c8001a198360074597200068a609801d165c8001a318160074597205360ba08749cd65c814d82e821d271597200240f251870c565c800903c97a1031597200040f25d840c565c800182c7460831597200060e1d1800c565c800182f746085458f200260721c5458d43c800160d921516350f200060bdd18215161c800903c9421d65507200260d21c5458541c8001625921516150720856852103159531c8001645920c5654c720005946403159531c800142d9215173d91200050b648545c7644800182f746085458d20006191c5821516348
  | 2 => 0x40142d9210476549410040f2607650d5250409834861d171549410054564c745c55250401531901d171549415340f25c86549425040182c87e1952509410244ba5e86549425040182c8721952509414860b21f63549425061d9248760552509411cd8925981549425043d5249754b71509410260d218545c6325040152592151718c9410050b64854dd9325054d81d83150764c9410050b648545cf60504db22c9854942d814100551648315d7644c401551900c575d91310055164831dd5644c401551900c775591310050b64854dc1644c40982e7460854d89310060b5d182153624c615914840c5759893100551648315d6624c401551900c5759893100474a6031dc1624c4015c1920c7705893100551648315d4624c401551900c5751893100561648315d0624c401591900c5741893100474660315c0624c4015c1920c5701893185645a1c31dd1524c401705920c77454931005c464031dd1524c40143b905d874549310050e241761d1524c401315980c47454931005c1648311d1524c401711900c474549310050b648545da424c40183854e01769093100551648315d6424c401551900c575909310055164831dd5424c401551900c7755093110e0b21d64549424c40982e7460854d81310060b5d182153604c40981c74a0c7459721026071d1831d165c84098347460474597210260e1d2801d165c84098387460074597210060ba1d821d165c8401a0d8360874597210068560d811d165c8401a258260474597210068660d801d165c8401a298260074597210068c605801d165c854d82e821d273597215360ba08749c165c840903c9461c30597210240f25e840c165c840103c9761030597210060b1d1820c165c84018347460430597210060bdd18215163c840981c871516350f21005836485458d43c840182f7460854583210050b648545cf644840142d9215170d91210060bdd1821516348401868706085458d210051a64854dc1634840142d921527650d215360d604541d94348401838801d163549210060e1d38058d524854d926821d371549210d60b21f645494248401a0c54219434c92153549250751c941484019477560c7250521006511d5831c94148401b045460c725052100658dd5801c94148401960756007250521006c8151801c941484353249854942505210054925d52509414841392487549425052100649150874c9414841394487549324c5211be91219524c93148413c4476549324c52167dc1251524c931484131c4985d1324c52104d31259744c9314861bd04545d1324c5215340fe6174dcb655014d81e7460c72d95405360d9d1811cb655000142d9215171d8d400060b5d182194625000144d92195731894000543648545cc625000146592195711894000549648545c4625000906f9850a765494
  | 3 => 0x525350ba4a7319361548018358760464d85520068560d811936154801a258260464d85520260e21d801936154801a198360064d85520068a609801936154801a318160064d8552026071d18319161548098387460064585520060b60a87191615480943491a1c6458552006836098319161548018368760464585520068560d811916154801a258260464585520068660d801916154801a298260064585520068c60580191615480903c981d163585520050da5c64d85615480981c8760c64d81520068360983193605480903e989cc64d81525350ba4a7319360548098348760464d81520068560d811936054801a258260464d81520240fa6271193605494d42e929c464d81520060e61d801936054801a198360064d81520068a609801936054801a318160064d8152026071d18319160548098347460464581520060b60a87191605480943890a1c645815200683609831916054801a158360464581520068960981191605480183a8760064581520068660d801916054801a298260064581520068c60580191605480903c981d163581520240f26074585605480143a9719360581520050b64854dc5639080142d921537058e420050b64854dcd619080142d9215370586420050b64854dcd609080142d9215371582425340f2588750d525080182c7660f74549420060b1d981dd1525080182c7660374549420060b1db845cd525080942e96e1d43549420060b1da8750d525080182c7621d43549421ccc32617350d5250a1fc0c765cd4354942167031db6350d525091f82c76e05435494239e0b1db8050d525080182c76e1171549420060b1db845c1525080981c7460c74596320260d1d2811d1658c8098347460474596320260e1d2801d1658c8098387460074596320060ba1d821d1658c801a0d8360874596320068560d811d1658c801a258260474596320068660d801d1658c801a298260074596320068c605801d1658c94d82e821d271596325360ba08749c1658c80903c9461c10596320240f25e84041658c80103c976101059632006071d183041658c80182c7460810596320060bdd182151618c80182f7460854582320050b648545c7644c80142d9215170d913253543250751c9434c801947756047250d32006511d5811c9434c801b04546047250d3200652dd5801c9434c801948756007250d32006c2151801c9434c94d90e821d373549321460b21f64549424c80130c9850d525093204d4325d43549424c85190c8750d52509325340fe6174dcb655054d81e7460c72d95415360e9d1801cb655040142d9215170d8d410060b5d182194625040144d92195731894100543648545cc62504014699219570189410054a648545c0625040141d9321076549410050da44841d952504014399021076549410051964a811d9525
  | 4 => 0x5480982c829d971d91520060b9d9820c7645480183a76a0031d91520060e9d9800c7645480982e829da70d91520260b20a765c3645480182e7660830d91520060d9da810c364548018367660430d9152006079da83043645480181e7660c10d91520060b9d982043645480182d7261e63191520060761e7398c6454801c0d725ce63191520060d61d7198c6454801c15735c66319152007095c97198c6454801839875c26319152007065cd7098c6454801c29725c263191520070c5c57098c6454a2560d92a0c6319152007035c97318c6454801c15735c46319152007095c97118c6454801c19735c063191520070a5c97018c6454801c31715c063191520060b5c987984645480181d875ce6119152007035c9739846454801835879c66119152007055cd719846454801c25725c661191520060e61d709846454801c19735c261191520070a5c9709846454801c31715c26119152007035c9731846454a2362592a046119152007055cd711846454801c25725c46119152007065cd701846454801c29725c061191520070c5c570184645480103d97e1831191520048b64b860c4645480123a90e1831191520048e643860c4645480123a9021831191520048e640860c4645494322c9660831191520060b5c987980645480181d875ce6019152007035c9739806454801835875c66019152007055cd719806454801c25725c660191520060e61e709806454801c19735c260191520070a5c9709806454801c31715c26019152007035c9731806454801c15735c46019152007095c9711806454a2162992a006019152007065cd701806454801c29725c060191520070c5c570180645480103d97e1830191520048b64b860c0645480123691e1830191520048d647860c064548012369121830191520048d644860c0645494322c9660830191520040f65f86040645480121e93e1810191520048764f86040645480122d92e18101915200487a4c86040645480121d93218101915250c8b25982040645480181d8760c64d8d52006836098319363548098348760464d8d520068560d811936354801a258260464d8d520260e21d801936354801a198360064d8d520068a609801936354801a318160064d8d520260d1d1811916354809838746006458d520250724e87191635480182d82a1c6458d5200607a1d831916354801a0d8260c6458d520068560d811916354801a25826046458d520068660d801916354801a29826006458d520068c60580191635480141e971936358d5200507a4c841d94354801435912107650d520050e640841d9435480144d92a0c7650d520050b648431d9435480181e831db6450d520260721c6458d4354801615911916350d52005866406458d435480981c8760c64d85520068360983193615480903e989cc64d85
  | 5 => 0x2c0014e03200092a2847a00000000396230bd8b33a80d073a4b11e61c4595812e0004900724456cfd89b0ca00000000000000000000000004500000009c001630000008e8ce486810d11f2000760471dd49241c5101320c3702188d1d46581f0000000006117f1e6840790004a00002d80033400000000000000000000000008d8a700033400000000000730000000000003c1580000e0000100007f0310bc000160001a2000439dc0d00e415000000490da1432684d8000000000010404e1528180d05237a374eb0763409180e8002103ec369a7174284001d337c3c10e1032cc6ac7e0411c0314001d90a27b8170002843d4f98000002dce000034c0303784613e0243080045c888ed1cc0003791890e0f4260a09f40001fc001d04741c0f08c81928991a9162d0678a3a2a3c8600000370000007b00002c100a897e36e4cc000000001540000021a21400000480628e320b0000480021f2502e4e10ef000340f48002e48040007933e548001fa3f00004d17c000224991951001d46da3e25248c2e800000128000003180009a86e096390a820d000000ba80006a000000000002200000003c8080000000000000140000000eba160141108f19442a204a28a43de0946787317a0011913f3fe000f420f000000e28000c06a90980f000000b011c000000f58222ac7f88f8470646bcc08001e2000cc902000000880c609804002a4807a66d221db126034a496b4a60809313e0008ec0015f29a0005f8d60000000004f000001029b237806cd42090be6e0000004ac0000023f1622707496a1945b8dd0000001f4b28002b8520001ec31c0001797308a2ec4f0da1a6018761f01980b52a80045e5785a8000008b035252050000000000600000000060140f0000001c000040000c0200006000000000204c03054000080501800000060040b000030000000c0600006038010080700810000030080000011010000000200400014030000f0080000400000000080500001010030000902c1a00c0001c1300c190140500006040000000802000000000080d008000100501c000100500805028120040200806000020000200801000070000105800064060140a01c000040200c060000601804000010180803c020000d018000000600c08008030040400401008010100100c00014090040400800000030240a0040806c00000010040600004000080180800c030000b020005340fe6174dcb6550d4d8367460472d95435360e9d1801cb6550c0182d74608651894300519648655c46250c015259215171189430051a648655c06250c015299215170189430050b648545c36150c0142d9215171d81430040fe5d8690f645480103f9761a41d91520040fe5d86903645480982e829da73d91520064360b739cf645480982c829d973d91520260ba0a769c764
  | 6 => 0x2470f06d8000001607347594f0c44049d23330888c618f91a8008bb0002f27891b8000b00000006b2da5bcab8a30009500216114a6ec7e8ad0001a4ef80012c6490ea45358964000001dc0000024f234725108000a87d4000c701c000000d80003b4e505c000430a98000000004117d000000bb93800000000000000618ad1f600014c1f9d128c000000ab2a88e4dfa27434684000000001c81b1e5056574530000006c41d9200927dc0000026e4490c0003a43d12c0aa2140011015903e00000000000830e186442295c858f70000008b8ae38e9289800000059c000180007a8121710162a00014b066210a607e1ca2800886724255431a0309a4608485a3041409c86c4842f8109a42c881cba0c435c4ec6017800273c002511f008cb61de16c20c951880e2400a51b31683a000000000000000000002180009000079cc88e215e0003a18b25a848330d50847b4719a33c037c0000000064000162000000c1927000000000001ae00000000000894180030008b40000000000126a1732e000001fc1824b11a0b8052159159140006a48880025e5c0d2800000264b480022a000000004006e4241440000010d8003fa15c0018d0000000000043c6710a1ad49c8640000004c000958771c25e86c8003e2000971f931e0002c8172260e800236000000000381787385913d0000003da30000755120fa2328a4f19984706c0e41894786149e000000000da8003cc0000019d02a0008224113a43c9887c0003480a193382828001051222500000041c3fc0000012a000e224c000000000000003
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4ca492a000001e1200017000088b346d3800000a9800ac3a4448431340312800028fa80074a00004000000347190000000000ce232c0000010147840200100000000280000400004001840c0418000501b45418edb2286a901300d931d88750d525094d08653930a1aa4a126404c05219931d1715494102604b224390ca9284a080310484648315d6624c4018884232018aeb3126200c41a1d920c774549310062250ec8063ba2a498802829a2153805da424c40101cd49003a2c6a9242a6c8164454219434c921534249504baa4a128290a9b10593150874c9414840980c433263a2e0a928004c0c219911d17054940026053204390ca9284a001302a8664854dc1315000188442324182eb3126000c44211910c175989300062150ec9061ba2a4980031128764430dd1524c001412d10a9c0aed2126004c09a1d92153615053000621108c9060bae429800311084644305d7214c0019024232418aca98e4000c84211900c5654c72000406b52408e8b1aa49029b209901508650d324814d910c80a84328290a40a684a2a0975494250120536213262a10e992809029b1219115087485404814d016543242a2eca1a2004c03a1d921536350d1000622108c9820bacc48800312084648105d6624400188943b26086e8a922000c48a1d92043745491000403b52418e8b12a48800280da2153835da424400188842326082eb1922000c4821192041758c910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x3
  | 10 => 0x98a
  | 11 => 0x98c
  | 12 => 0x98d
  | 13 => 0x98e
  | 14 => 0x150a
  | 15 => 0x150c
  | 16 => 0x150d
  | 17 => 0x150e
  | 18 => 0x9ca
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0xa0e
  | 22 => 0xa0a
  | 23 => 0xa0c
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x1549
  | 29 => 0x154c
  | 30 => 0x154d
  | 31 => 0x154e
  | 32 => 0xb49
  | 33 => 0xb4d
  | 34 => 0xb4e
  | 35 => 0xb89
  | 36 => 0xb8c
  | 37 => 0xb8e
  | 38 => 0xcc9
  | 39 => 0xcca
  | 40 => 0xccd
  | 41 => 0xcce
  | 42 => 0x15c9
  | 43 => 0x15ca
  | 44 => 0x15cd
  | 45 => 0x15ce
  | 46 => 0xd09
  | 47 => 0xd0a
  | 48 => 0xd0c
  | 49 => 0xd0e
  | 50 => 0x1609
  | 51 => 0x160a
  | 52 => 0x160c
  | 53 => 0x160e
  | 54 => 0xd49
  | 55 => 0xd4a
  | 56 => 0xd4c
  | 57 => 0xd4d
  | 58 => 0xe89
  | 59 => 0xe8a
  | 60 => 0xe8e
  | 61 => 0x98956
  | 62 => 0x98955
  | 63 => 0x9c956
  | 64 => 0x9c955
  | 65 => 0xb0956
  | 66 => 0xb0955
  | 67 => 0xb4956
  | 68 => 0xb4955
  | 69 => 0x1a09
  | 70 => 0x209
  | 71 => 0x1409
  | 72 => 0x128a
  | 73 => 0x16c9
  | 74 => 0x1449
  | 75 => 0x168a
  | 76 => 0x12ca
  | 77 => 0x1849
  | 78 => 0x1489
  | 79 => 0x180a
  | 80 => 0x130a
  | 81 => 0x9c996
  | 82 => 0x9c995
  | 83 => 0xa0996
  | 84 => 0xb0995
  | 85 => 0xb0996
  | 86 => 0x154995
  | 87 => 0xcc995
  | 88 => 0xcc996
  | 89 => 0x15c995
  | 90 => 0x3c9
  | 91 => 0x1709
  | 92 => 0x1889
  | 93 => 0xb1515
  | 94 => 0x8a
  | 95 => 0xcd515
  | 96 => 0x8c
  | 97 => 0xb49d6
  | 98 => 0xb49d5
  | 99 => 0x138c
  | 100 => 0x124c
  | 101 => 0xcc9d6
  | 102 => 0xcc9d5
  | 103 => 0x128c
  | 104 => 0x18c9
  | 105 => 0x1789
  | 106 => 0x180c
  | 107 => 0x130c
  | 108 => 0xb8a16
  | 109 => 0x138d
  | 110 => 0x124d
  | 111 => 0xd0a16
  | 112 => 0x8d
  | 113 => 0x128d
  | 114 => 0xe8a16
  | 115 => 0x168d
  | 116 => 0x12cd
  | 117 => 0x1949
  | 118 => 0x134d
  | 119 => 0x749
  | 120 => 0xb4b16
  | 121 => 0xb4b15
  | 122 => 0xb8b16
  | 123 => 0xccb15
  | 124 => 0xccb16
  | 125 => 0x15cb15
  | 126 => 0x3ca
  | 127 => 0x170a
  | 128 => 0x188a
  | 129 => 0xcd555
  | 130 => 0x20c
  | 131 => 0xccb56
  | 132 => 0xccb55
  | 133 => 0x1a0a
  | 134 => 0x140c
  | 135 => 0x18ca
  | 136 => 0x178a
  | 137 => 0x184c
  | 138 => 0x148c
  | 139 => 0xd0b96
  | 140 => 0x20d
  | 141 => 0x140d
  | 142 => 0xe8b96
  | 143 => 0x16cd
  | 144 => 0x144d
  | 145 => 0x194a
  | 146 => 0x14cd
  | 147 => 0x74a
  | 148 => 0xe8cd6
  | 149 => 0x188c
  | 150 => 0xd4d11
  | 151 => 0xd4d12
  | 152 => 0xd4d14
  | 153 => 0xe8d16
  | 154 => 0x170d
  | 155 => 0x194b
  | 156 => 0x164d
  | 157 => 0x44d
  | 158 => 0xd5611
  | 159 => 0xd5612
  | 160 => 0xd5614
  | 161 => 0x40e
  | 162 => 0x128e
  | 163 => 0x140e
  | 164 => 0x1a0c
  | 165 => 0x170e
  | 166 => 0x74b
  | 167 => 0x1a0d
  | 168 => 0x188e
  | 169 => 0x1a8b
  | 170 => 0x3cd
  | 171 => 0x194c
  | 172 => 0x17cd
  | 173 => 0x74c
  | 174 => 0xb09895d
  | 175 => 0xb09895e
  | 176 => 0x94995
  | 177 => 0xb49c95e
  | 178 => 0xb49c95d
  | 179 => 0x94b15
  | 180 => 0x138955
  | 181 => 0x124955
  | 182 => 0xcc9c99d
  | 183 => 0xcc9c99e
  | 184 => 0x124995
  | 185 => 0x8995
  | 186 => 0x128995
  | 187 => 0x12c995
  | 188 => 0x40996
  | 189 => 0x41296
  | 190 => 0x160d51
  | 191 => 0x24d
  | 192 => 0x150b16
  | 193 => 0x150cd6
  | 194 => 0x14d
  | 195 => 0x9ccd5
  | 196 => 0x989d5
  | 197 => 0x1689d5
  | 198 => 0x12c9d5
  | 199 => 0xa0752
  | 200 => 0xb8751
  | 201 => 0x2cd
  | 202 => 0xa1296
  | 203 => 0x75611
  | 204 => 0xa0754
  | 205 => 0xe8751
  | 206 => 0x5cd
  | 207 => 0xccb4b1d
  | 208 => 0xccb4b1e
  | 209 => 0x138b15
  | 210 => 0x20b15
  | 211 => 0x140b15
  | 212 => 0x144b15
  | 213 => 0x40b16
  | 214 => 0x41416
  | 215 => 0x160d52
  | 216 => 0xcd
  | 217 => 0x154996
  | 218 => 0x154cd6
  | 219 => 0xb4cd5
  | 220 => 0xb0b55
  | 221 => 0x16cb55
  | 222 => 0x144b55
  | 223 => 0xb9416
  | 224 => 0x75612
  | 225 => 0xb8754
  | 226 => 0xe8752
  | 227 => 0x40cd6
  | 228 => 0x41716
  | 229 => 0x168cd5
  | 230 => 0x16ccd5
  | 231 => 0x3ccd5
  | 232 => 0x170cd5
  | 233 => 0x160d54
  | 234 => 0x4d
  | 235 => 0x15c996
  | 236 => 0x15cb16
  | 237 => 0xd0d54
  | 238 => 0x151296
  | 239 => 0x41516
  | 240 => 0x161296
  | 241 => 0x40096
  | 242 => 0x155416
  | 243 => 0x41556
  | 244 => 0x161416
  | 245 => 0x40216
  | 246 => 0xe9716
  | 247 => 0x1715d6
  | 248 => 0x415d6
  | 249 => 0x161716
  | 250 => 0x403d6
  | 251 => 0x8416
  | 252 => 0x128416
  | 253 => 0x20416
  | 254 => 0x140416
  | 255 => 0x3c416
  | 256 => 0x170416
  | 257 => 0x1a0d55
  | 258 => 0x189616
  | 259 => 0x160996
  | 260 => 0x160b16
  | 261 => 0x160cd6
  | 262 => 0x75614
  | 263 => 0x94b099d
  | 264 => 0x4955
  | 265 => 0x9ccc99d
  | 266 => 0x24b55
  | 267 => 0xc9d5
  | 268 => 0x98a16
  | 269 => 0xb4ccb1d
  | 270 => 0xb0b96
  | 271 => 0xcce96
  | 272 => 0x84099e
  | 273 => 0x2040b1e
  | 274 => 0x3c40cde
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1462
  | 6 => 4190
  | 5 => 2482
  | 4 => 602
  | 3 => 44
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (59451+((h/487+packedAt gbK7 (54094+(h % 487)*11) 11) % 1755)*12) 12
  | 6 => packedAt gbK6 (219268+((h/1396+packedAt gbK6 (201120+(h % 1396)*13) 13) % 5531)*14) 14
  | 5 => packedAt gbK5 (156362+((h/827+packedAt gbK5 (146438+(h % 827)*12) 12) % 2979)*13) 13
  | 4 => packedAt gbK4 (44140+((h/200+packedAt gbK4 (42140+(h % 200)*10) 10) % 874)*11) 11
  | 3 => packedAt gbK3 (3662+((h/14+packedAt gbK3 (3564+(h % 14)*7) 7) % 75)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x38e3f1f98e3e3838e1c1fe1ff060678d30cf
  | 1 => 0x1c0fc7e3e0fc7c03f01fe0fe1f18199b23333
  | 2 => 0x1ff007fc7f007ffc7fe000ffe02061e43cc3c
  | 3 => 0x1ffff8007fff80007fffff0000c07e07c0fc0
  | 4 => 0xfe00000007fffffff8000000000ff8007ff000
  | 5 => 0xfffffffff800000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2408209048820a08882040a20ca06022851045
  | 1 => 0x484044221204444111009404c1418089122112
  | 2 => 0x80910044801000940248000910020214004428
  | 3 => 0x112289000528900204952940000c0540680a80
  | 4 => 0x1c00000007cf2723a0040c604464a8007fb000
  | 5 => 0xe1fcf2792000000400183181998b57ff800000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffee8fef8fee8fffffee8fef8fee8fffffee8fef8fee8fffffee8fef8fee8fffffee8fef8fee8fffffee8fef8fee8fffffee8fef8fee8fffffee8fef8fee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_27821
namespace PEqualNP.Outside.L_meta_27821
open PEqualNP.Outside.L_meta_27821.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 7 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 5 := bs2_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_32 : Interval s4Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_64 : Interval s4Atlas 2 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 66 := (concat bs4_2_0 (concat bs4_2_32 bs4_2_64))
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
theorem bs4_3_256 : Interval s4Atlas 3 256 23 := block_range (n:=23) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 279 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96)) (concat (concat bs4_3_128 bs4_3_160) (concat bs4_3_192 (concat bs4_3_224 bs4_3_256))))
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
theorem bs4_4_288 : Interval s4Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 302 := (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 24 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_32 : Interval s5Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_64 : Interval s5Atlas 2 64 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 78 := (concat bs5_2_0 (concat bs5_2_32 bs5_2_64))
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
theorem bs5_3_352 : Interval s5Atlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_384 : Interval s5Atlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_416 : Interval s5Atlas 3 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_448 : Interval s5Atlas 3 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_480 : Interval s5Atlas 3 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_512 : Interval s5Atlas 3 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_544 : Interval s5Atlas 3 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_576 : Interval s5Atlas 3 576 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 587 := (concat (concat (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96)) (concat (concat bs5_3_128 bs5_3_160) (concat bs5_3_192 (concat bs5_3_224 bs5_3_256)))) (concat (concat (concat bs5_3_288 bs5_3_320) (concat bs5_3_352 (concat bs5_3_384 bs5_3_416))) (concat (concat bs5_3_448 bs5_3_480) (concat bs5_3_512 (concat bs5_3_544 bs5_3_576)))))
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1376 : Interval s5Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1408 : Interval s5Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1440 : Interval s5Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1472 : Interval s5Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1504 : Interval s5Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1536 : Interval s5Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1568 : Interval s5Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1600 : Interval s5Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1632 : Interval s5Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1664 : Interval s5Atlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1696 : Interval s5Atlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1728 : Interval s5Atlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1760 : Interval s5Atlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1792 : Interval s5Atlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1824 : Interval s5Atlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1856 : Interval s5Atlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1888 : Interval s5Atlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1920 : Interval s5Atlas 4 1920 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1930 := (concat (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448)))) (concat (concat (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)) (concat (concat bs5_4_576 bs5_4_608) (concat bs5_4_640 bs5_4_672))) (concat (concat (concat bs5_4_704 bs5_4_736) (concat bs5_4_768 bs5_4_800)) (concat (concat bs5_4_832 bs5_4_864) (concat bs5_4_896 bs5_4_928))))) (concat (concat (concat (concat bs5_4_960 (concat bs5_4_992 bs5_4_1024)) (concat (concat bs5_4_1056 bs5_4_1088) (concat bs5_4_1120 bs5_4_1152))) (concat (concat (concat bs5_4_1184 bs5_4_1216) (concat bs5_4_1248 bs5_4_1280)) (concat (concat bs5_4_1312 bs5_4_1344) (concat bs5_4_1376 bs5_4_1408)))) (concat (concat (concat (concat bs5_4_1440 bs5_4_1472) (concat bs5_4_1504 bs5_4_1536)) (concat (concat bs5_4_1568 bs5_4_1600) (concat bs5_4_1632 bs5_4_1664))) (concat (concat (concat bs5_4_1696 bs5_4_1728) (concat bs5_4_1760 bs5_4_1792)) (concat (concat bs5_4_1824 bs5_4_1856) (concat bs5_4_1888 bs5_4_1920))))))
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
theorem bs5_5_864 : Interval s5Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_896 : Interval s5Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_928 : Interval s5Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_992 : Interval s5Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1024 : Interval s5Atlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1056 : Interval s5Atlas 5 1056 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1074 := (concat (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 bs5_5_224))) (concat (concat (concat bs5_5_256 bs5_5_288) (concat bs5_5_320 bs5_5_352)) (concat (concat bs5_5_384 bs5_5_416) (concat bs5_5_448 (concat bs5_5_480 bs5_5_512))))) (concat (concat (concat (concat bs5_5_544 bs5_5_576) (concat bs5_5_608 bs5_5_640)) (concat (concat bs5_5_672 bs5_5_704) (concat bs5_5_736 bs5_5_768))) (concat (concat (concat bs5_5_800 bs5_5_832) (concat bs5_5_864 bs5_5_896)) (concat (concat bs5_5_928 bs5_5_960) (concat bs5_5_992 (concat bs5_5_1024 bs5_5_1056))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 48 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 44 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 602 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 (concat bgb_4_384 bgb_4_416))) (concat (concat bgb_4_448 bgb_4_480) (concat bgb_4_512 (concat bgb_4_544 bgb_4_576)))))
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
theorem bgb_5_1568 : Interval gbAtlas 5 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1600 : Interval gbAtlas 5 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1664 : Interval gbAtlas 5 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1696 : Interval gbAtlas 5 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1760 : Interval gbAtlas 5 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1792 : Interval gbAtlas 5 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1856 : Interval gbAtlas 5 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1888 : Interval gbAtlas 5 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1952 : Interval gbAtlas 5 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1984 : Interval gbAtlas 5 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2048 : Interval gbAtlas 5 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2080 : Interval gbAtlas 5 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2144 : Interval gbAtlas 5 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2176 : Interval gbAtlas 5 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2240 : Interval gbAtlas 5 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2272 : Interval gbAtlas 5 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2336 : Interval gbAtlas 5 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2368 : Interval gbAtlas 5 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2432 : Interval gbAtlas 5 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2464 : Interval gbAtlas 5 2464 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2482 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)))) (concat (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)))))) (concat (concat (concat (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344)) (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824))))) (concat (concat (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)))) (concat (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)))))))
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
theorem bgb_6_4160 : Interval gbAtlas 6 4160 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4190 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))))) (concat (concat (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560)))) (concat (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816))) (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)))))) (concat (concat (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360))) (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)))) (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)) (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))))))))
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
theorem bgb_7_1440 : Interval gbAtlas 7 1440 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1462 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 (concat bgb_7_384 bgb_7_416)) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))) (concat (concat bgb_7_544 (concat bgb_7_576 bgb_7_608)) (concat bgb_7_640 (concat bgb_7_672 bgb_7_704))))) (concat (concat (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864))) (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))) (concat (concat (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)) (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248))) (concat (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344)) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 7 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffeeefffffeeefffffeeafffffeeafffffeeefefefeeefffffee8fef8fee8fffffeeefffffeeefffffeeafffffeeafffffeeefefefeeefffffee8fef8fee8
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
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_27821.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,6]⟩,⟨.and,[8,7]⟩,⟨.or,[0,3]⟩,⟨.or,[10,4]⟩,⟨.or,[6,7]⟩,⟨.and,[11,12]⟩,⟨.or,[0,1]⟩,⟨.or,[14,2]⟩,⟨.and,[15,5]⟩,⟨.and,[0,4]⟩,⟨.or,[9,13]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_27821

open PEqualNP.Outside.L_meta_27821 in
theorem PEqualNP.Outside.L_meta_27821 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
