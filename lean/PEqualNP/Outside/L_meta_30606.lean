import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_30606.Model
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


end PEqualNP.Outside.L_meta_30606.Model

namespace PEqualNP.Outside.L_meta_30606
open PEqualNP.Outside.L_meta_30606.Model
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

end PEqualNP.Outside.L_meta_30606

namespace PEqualNP.Outside.L_meta_30606
open PEqualNP.Outside.L_meta_30606.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xacf12003101654500094e702262604280002001b000c5a94208700446928a22554003a00c24465cc903e186871e30300064100524102d248ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4a3a092a512e003552021e360d2801074144211512002f245a2b58573932160003372d4e0000001b554829000000044f452718533b13460a00002500001c0f003342003c19231d0e08222c1700474c591f05103f4031380c004d54503d304b3e11340020000b492656061400431a073cd41870a0008706182800a58003080000900042a200043b3117651d0eeaa3a1d794c42aea9885ad4210aeca2215d54442bd28085795010aeca3195d54632af29e835d53d06dca520db54a41afa9a835c53506bca318d7542319f2a0633d540c6dca418db54831bd2806379500c73ca818e755031e729063cd520c6bca218f594431eb20863d5410c7b4a018d754031eca806359500c6bca790d754f219f2a4433d54887a86310d7d4d21ae29a43d431486bca7205754e40b7a92816c52502bca6205754c40b7290816d52102eca2205d54440af28e615d538c2eea2985d14530eba8a615c514c3a8a2985514530eda82615e530c2bca7105754e209faa2413c544827ca8104f55020af298415d53082eca2105d54420afa9e215c53c42bca7085754e10ea18c21d930842bea6885714d10ec982213e540427aa8085794c10aea98216e52042daa408750c410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x24100c0651682c00201270e00aa0cba26a6010000a980000087871801c004103294254042c3551520c6c56290431c6951500c7195454031d2949500c7495254031d4905500c7514154031c555031886d1600c621b458031486546154e40c5990514c3156414530d1988514c3456214530d4580514c2546154e20b458031842d0614c210961953044255650c410c55503104345520c410
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc8000104001505ca4154031c22a8b006310e0564588514c308b22c028a61905896014530
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
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s0K2 (249+((h/1+packedAt s0K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfe3f1ffc3fc7fe1c71f1c1ff8fc0ffe18739f
  | 2 => 0xf1fc01e3fc7ff8fe07e3e01c3f1ffe1e664cf3
  | 3 => 0x1fffe03ff807f1ff803ffe03fe00fe1878f1c
  | 4 => 0xfe000003ffff801ffffc00003ffff001f80fe0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x40204280480090004104040490244288081185
  | 2 => 0x284124449128410a0223214909092454264432
  | 3 => 0xa488a04901192026880148c02a40a944828e18
  | 4 => 0xc41ac9922a503255d5480282b492c189d80bc0
  | 5 => 0x9130100326244992692931300030011756000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffcffccfcf0ccc0fffcffccfcf0ccc0fffcffccfcf0ccc0fffcffccfcf0ccc0fffcffccfcf0ccc0fffcffccfcf0ccc0fffcffccfcf0ccc0fffcffccfcf0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_30606
namespace PEqualNP.Outside.L_meta_30606
open PEqualNP.Outside.L_meta_30606.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x340088028000004800a8038000000000b80141800000491a63aa00003e084000001580000068100110800064d801e4000352000000001380002c60500a8000001c00000612a23c00000004c00e0058020000000012000000000002000608000000c001ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x2900384a000200470f000028002300005106094f565305102d00003b4c1e43312459001a3f1f2100042e520b002c1700261246000000390719363e3525000100450d2a034e30421815204d552754004100500a370000321b000000083c3d40165a0e481d3a1c114b140022445849002b34000013332f570c00010200205321c78500001010000005080050c0e00000004ca100b6e5290edaa521cf94a429ea84855e5310abaa6215d94442baa88857a5010af2a0216794c42cea98853e5210b5ca4216d94442daa8885ba5010a7aa0216e540429ca80853e54cca7aa9996b10a32bb28c6575518ca7ea8994f15132d6212656e52906daa520cf950319eaa0636e520c6daa418f54c431bd2806379500c6bca790d754f21d6216433e548867aa910cfd51219e2a243ac424867ca5a04f55240b7a92816c525035ea4a04f14940d6292812c5250376a0a04f950409f2a4613d548c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ea9904f153209f2a4413d548835885106e502209faa2413c544837280904f950209eaa0415e53082baa6106b10820bb2884175510827ca9084f55210afa9a215c534427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x91601c61a1b0b8a42609422000e312004aa2b00a00780008b01851033155354442c694d5010b195354042cc9455010b315154042aa580428cb244254632aa580424cb513154031c354c42c86a96010b21aa580424870e6314940c358c52503266114940c9584525032960149408b189548c2a96010a20aa189408823865501208b594420830d5310820c9109510822c6255210
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x1008040c0001485c04254632c12a6b008590e05635845250304b1ac029281885856014940
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
  | 4 => packedAt s1K4 (2667+((h/30+packedAt s1K4 (2457+(h % 30)*7) 7) % 121)*8) 8
  | 3 => packedAt s1K3 (990+((h/8+packedAt s1K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfe1f1fc7fe3ffe1c71f8e07c7e0fffe19327f
  | 2 => 0xf1fe01ff87fc78fe07e3f007f8ff0e1e663d93
  | 3 => 0x1fffe3ff8007f1ff803fff8ff000fe187ce1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80280204210420008105024101204308091025
  | 2 => 0x2840a4891240c10a02229092484a0454262492
  | 3 => 0x6484609010c910264800a430d20628c4824e18
  | 4 => 0x441549224480125554480120a494a081d00b40
  | 5 => 0x8919810367126499a79349c40018c1197db000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_30606
namespace PEqualNP.Outside.L_meta_30606
open PEqualNP.Outside.L_meta_30606.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x70094006080001448b4ca9065802c420140e0a0001f5c0091a562088f38a910b02001263a5c69b5e4c49014551a018793803038a040040147001c0008c100ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x84e419280704e7c00a100000001885e00100000000150000000020190e3c00000e2173500000443610c7c00000d400483e8dc6c452a18068530700000000f04c4c85210a48200290000000000000000001940039001e8b86f2f80070001f850ea0c000001077001e0f6252599c586b40128d0231707480003c80000690000074490da0c2a000f98400000000034320016c005a2a9b90466181d89c12011c0e64c3f8341e00168000a002301c00222ea18ac0000000000b0000cda000c1900059199d07a0015a04fc57120009e0005058b00028934625e0882420631d91c5002030004000a000d0402070100040200000002020a030002000e01070500020603030000002a01080702000701bd286877950d0ebca7215754e42af298855d5310aeca2215d54442bd28085795010abaa3995794332aea9c65cf524cabea2995714132af298655e53906baa720d794c41aea98836e52106daa420de94041bca80835d52cc6bca198d754e31afa9263d7514c6b8a098d794c31af29e435d53c86bca710d754e219faa2433c54486bca690d754d219f2a0433d54086bca610d754c21f2908437a50086f2a010d794f40aea9e819e53d033aa7a067ccb40ce996819f31d033a63a04f55240afa9a815c535033ea6a06714d40cf992819d325033e62a0674c540dda82813e541037281984f952309eaa4619e548c33aa9185754a30aea8c615e508c33e811867502309f2a0613d540c2dca4185b54830bb2886175510c37280186795030ceaa061ce520c2baa4187354830a6a9061d6510c2baa2187554430aaa88615e500c3b4a01867d0030ed200619d400c3b280186650030af29e415d53c839a65904f952209eaa4415f53882b8a7106e50220afa9a415c534839a64906e501209f2a0413d54082bca6105754c20bb288417551082bca7885754f10ea98e213e548427aa90857d4e10ae29c21b940842bea6885714d10ea98a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x5051697203819e369c011000000708000311a0058c38a40004c4d21640280303400015106000000941013e0000054b800946ac30032bc0001e00292427402c440a00a01001440006080060c0820095584504ca4d62141318e58054486586054d21c955121087612154021a61813250298604c540a698f50503295250030cc545400c30e5454830c3551520c3455294430c5951510c3155454430d1949510c3455254430a6592500c21d65d0030c354b400c31551d0030a6592400c3495290030d4546400c21f6550030c3549400c3155150030d2549400c3515150030a6d95400c31b6550030e2949400c3195250030e2549400c3095250030e4945400c3195150030e4545400c311515003095584538831853502209319532483185350120e24c9404824d6214e10c614d4084254654c510c614d40443913150110
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x13080038d05200067245c4604c940912e430262a070152945400c381292a2a0061c05495150030a22e229a8110508754c94048284b90a6a0421441d53150110
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s2K5 (864+((h/16+packedAt s2K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s2K4 (4032+((h/45+packedAt s2K4 (3672+(h % 45)*8) 8) % 198)*9) 9
  | 3 => packedAt s2K3 (2012+((h/16+packedAt s2K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s2K2 (453+((h/3+packedAt s2K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1e3f838e3cfffe3f1c71e3870c7ffe3f0e43cf
  | 1 => 0x1fc7fc0fff0f1fc7e07e3c07ff8e0fc7307d33
  | 3 => 0xe007fff03ff01ff8ff803ff80ff00ff8c38e3c
  | 4 => 0xfff800003fffe000ffffc0000ffff000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8300a01044441040082060a140128224064045
  | 1 => 0x44110824082024082012040224842482101512
  | 3 => 0xa21100900248014480091009204910408a28
  | 4 => 0x48b05b4d22aa0c92f5548050ae496192f80f80
  | 5 => 0x9104620802cc91249a693264c0018024af6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffeeffcceeaaee88ffeeffcceeaaee88ffeeffcceeaaee88ffeeffcceeaaee88ffeeffcceeaaee88ffeeffcceeaaee88ffeeffcceeaaee88ffeeffcceeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_30606
namespace PEqualNP.Outside.L_meta_30606
open PEqualNP.Outside.L_meta_30606.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x63860a8d1e0002500680802258a021664da2108c4a03e0051d549d7a6483838000b4f130648b8558a0000421158c000171052000002d4204700498b0c9004ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1241800942d0684c2c720e8b042273b8fc300e3301c022500000005a001e83268428009e843c028001e2b8b8b6382f80cec334302cd20000188646338174f6301792c6e6f04068b8003294ce60021080d41c37120fc15001b09839221e4786700050fa82188248e522898082280d978ac40061fc9a02001840055000d87c1f13138000f321f052003a1b40c00001607a002a1c40a461a88cb2241d9ac0811408000000000e80000228d05600400008622080a90e490b9d4a00416011300010102054f090101030700090b051f000002010106090002090b00000a010a0900050a0006080800bb28c87755190e7ca3a14f543429eaa485af5250a78a2a14fd41429f2a0853e548ca7aa9194f950329eaa06576510caeaa2195e94032bca80655e53906baa720e794e41cea9c833d529067ca320cf54241af298835d53106dca420db54841bd2808379501073ca620e754c41d7290833d521075aa420cb548419f28883b65110774a020cf54041dca808339501067ca998cf55331cf2a6639d54cc73e8598e750b31cf20e639c41cc6baa718ed106319faa2633c544c7688298e7d5131ce2a2639f424c73a8498f5d4531eba0a639e414c7388298f510531ca20a635e530c67ca990cf55321d6a16433f5488678a910d794e21aea9c43d5318867ea890cf15121d6a1243d5314867ca810cf55021af298435d53086f4a010de540219ea96813e51d033e63a0674c7409eaa4813f5250278a2a067cc540ce98a81bb505027ca8204f952309eaa4613e540c27aa8185b94830b6a906176510c2eaa2184f953209eaa6413e548827aa9104f951209eaa2415f53482b8a6904f950209eaa0415e53082baa6105d94420baa8841e9200827ea9884f15310af29e215d53c43aa63884f952109eaa421b9408427ea8884f15110ea98a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x906891000a0000000000000011426800000b00000a54c9e4eb87304030980560001f00940002e6c012001c00b043c006502802638bcb0030a4180088d10000c40802000000000169d540000000060458d020c080102000006001028e5805150b0e5354841c354d52106956394441ca54a501071a5354041c654d501072a5254041ca549501068d6210731a658041cc6a56210631ac580418c6a56210531ac580414c6946150931a5993514c61e6590531a5986414c61e6510531a3588414c6996010531b1588414c6d16010531a5994414c7166510531e1988414c6956210531e1588414c6856210531e4980414c6956010531e4580414c69160105318e5805488714544c6218b1954248714544c521e1509314862d6214540c5145315023461551209558453483495348020d8545200822d6215310c515131c4314544c5108e19540443913150110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x200081000a038003320401245c06150931d02c53008298e8262580414c740b12c020a63445c0544c621a08eaa126290d05721453150282b90a898e21841953150110
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
  | 3 => packedAt s3K3 (2012+((h/16+packedAt s3K3 (1900+(h % 16)*7) 7) % 88)*7) 7
  | 2 => packedAt s3K2 (453+((h/3+packedAt s3K2 (441+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1e3f87e3c7c7fe3f1c71f1f82387fe3f0dc1cf
  | 1 => 0x1fc7f9fff8071fc7e07e3e3ffc070fc7327933
  | 2 => 0xe007fe03fff81ff8ff803fc03ff80ff8c38e3c
  | 4 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8280a004410a0840042050490081421404c045
  | 1 => 0x441110408090240820120210a4122482101912
  | 2 => 0x1220089120050014880248209200920430228
  | 4 => 0x4810555224840492b1548004b254a082b80d80
  | 5 => 0x91a4658037269924de6939270060c134efe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefeececfafae8e8fefeececfafae8e8fefeececfafae8e8fefeececfafae8e8fefeececfafae8e8fefeececfafae8e8fefeececfafae8e8fefeececfafae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_30606
namespace PEqualNP.Outside.L_meta_30606
open PEqualNP.Outside.L_meta_30606.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x9200000000c000142e7400b00015804ea401c0430828483c18a369402200200112a84d160a1151f00980181a78007008cc8940000131c3c0040018100001000003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x901432727eac74922a0000625a0c0000280000201c00000000000036b400a20000002e54520060a400a888040000447600025e00003a985c00005600000000002c22a638004800b0b26e4c4e468a3e1a7a7c709a009400b60000588000008c00080eae3412000616309c7850006aaa3c00866c00101e269e008218000066000084002442400000008e0096680000000a4aa0640a00050e010004000001031100000100010303040400030400000102000db7294876d5290edca421db54843bb28887755110ef4a021de54043bd286857950d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290655e53106baa620db94841b6a90837a50106f2a020db94b31b6a9663cd32cc67ea898cf15131e6992633e540c67aa818db94831b6a90637a500c6f2a018cf950219eaa0435e53086baa610de94021bca80436e52d02daa5a06b94b40d6a9681ae32d035a65a04f55240d719281ad3250376a0a04f95040b7296616d52cc39a65984f952309eaa461b9408c39a64986e501309f2a0613d540c2dca4185b54830bb2886175510c37281904f952209eaa4413e540827aa8105794c20aea98417651082eaa2106e500209f2a4213d548437281085bd4910b629221b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x780826354b094090000000100199c001c6080008e582548caa96095232a3993534cac56110d32b2580434ca396015131c3151324c64d6394b40a358e52d022d658cb40aa98b50503893250130c654d400833151500209358c52443285250110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x990912e1326a69950970151324c644b9cc5a8281425cc5250110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
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
  | 4 => packedAt s4K4 (2724+((h/30+packedAt s4K4 (2484+(h % 30)*8) 8) % 147)*8) 8
  | 3 => packedAt s4K3 (633+((h/5+packedAt s4K3 (608+(h % 5)*5) 5) % 28)*5) 5
  | 2 => packedAt s4K2 (199+((h/1+packedAt s4K2 (196+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf3c38f1e3cfc7f1f9c470c7e23f3f1f91c4cf
  | 1 => 0xf03fc0fe7ff1f8fe3e0780f8ffc7c7e1827b33
  | 2 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 3 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x185011804450842008414412809210910c045
  | 1 => 0x10080220008001004000800840420200001112
  | 2 => 0x2202b445492892a00f480a92129094d4630c28
  | 3 => 0x44109005120080249251220003249044240e80
  | 5 => 0x88a32088402d24c925a64ce4980020995be000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffecffeceee8eee8ffecffeceee8eee8ffecffeceee8eee8ffecffeceee8eee8ffecffeceee8eee8ffecffeceee8eee8ffecffeceee8eee8ffecffeceee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_30606
namespace PEqualNP.Outside.L_meta_30606
open PEqualNP.Outside.L_meta_30606.Model
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
end PEqualNP.Outside.L_meta_30606
namespace PEqualNP.Outside.L_meta_30606
open PEqualNP.Outside.L_meta_30606.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x340018e364460948a15a15e000165c00327300001c26c012c00f88140a290370821c8f328de3a7e74034021c6aa4a5d4bd24b5a800001b1f00cc01e4c01da200005b170c801500000002d0000080001c0051a08c010e080850620880037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0401bf41017f90401fd41006f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd40017f5000ff94001fd50005f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a400eff19520035f8ca90003ff64480017fb224000efd91200057ec890037fe644800b7f3224000ff59120005fac890037fc644800b7e3224000ef1912002d78c89003bff544801bff2a24000ff5512006ff8a890003ff63480017fb1a400cff98d20025fcc690003fd63480017eb1a400cff18d20025f8c69003bff5348019ff29a4000ff54d20067f8a690037ff4348019ff21a4000ff50d20067f88690006ff6248007ffa924003ff9492001ffaa49000ffc5248007ffa124003ff9092001fdc849000ffd4248001f6a124003ff1092001ffe649000ffe3248007f71924003ff4c920007da649000ffc3248001ffb0a4000bfd852005ffcc29000afe6148001feb0a400bff18520015f8c29003bff5148017ff28a4000ff5452005ff8a290037ff4148001dfa0a400bff90520007fa8290003bd4148017fe20a400cffcc52005ffc6290003fd3148017fe18a4003ffc852001fde429000ffe2148007fe90a4000fb4852001ff84290006ff6048003ffa824001dfd412000ffca090007fd5048003bea824001ff1412000ffe8090007fe4048003fd2024001ff50120007f28090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9024003fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007ff1048003ff0824001fe8412000ff82090003ff65440017fb2a200aff99510035fcca88003fd65440017eb2a200aff19510035f8ca88003ff64440017fb222009ff9911002dfcc888003fd64440017eb222009ff1911002df8c88802bff5444013ff2a22000ff5511004ff8a888003ff63440017fb1a2008ff98d10025fcc688003fd63440017eb1a2008ff18d10025f8c68802bff5344011ff29a2000ff54d10047f8a688027ff4344011ff21a2000ff50d10047f88688003ff62440017fb122007ff9891001dfcc488003fd62440017eb122007ff1891001df8c48802bff524400fff2922000ff5491003ff8a488027ff424400fff2122000ff5091003ff88488023ff324400fff1922000ff4c91003ff86488006ff6144005ffa8a2002ff94510017faa28800bfc5144005ffa0a2002efd0510017fc828800bf64144005fea0a2002ef50510007ea8288003b54144005fe20a2002ffcc510017fc628800bf63144005fe98a2000fd4c510017f8628800bff2144005ff10a2002fd88510017fa4288003f52144005fe10a2001bfd811000ffea0880077f5044003ff2822001fe9411000ffaa0880077d5044001fca822000de5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x77a3054003be182a001dfc815000efc40a80077c2054003bf882a001df8415000ef420a80077c1054001ffb2a8000bfd95400b7fccaa001afe6550001feb2a8000bf595400b7f8caa001afc65500037fb228005ffd514002ffca8a0017fd545000bfe2a28000ffd8d40005fec6a0057fe63500097f31a8000ff58d400aff8c6a0012fc635002dffa9a8015ff94d40007faa6a0057fc535000bffa1a8005efd0d4002ffc86a0017fd4350001dea1a8005ff10d40007fec4a0002ff6250029ff3128003bf98940007fac4a0053fc62500077e3128016ffd49400a7fca4a0003fd5250029fe2928005ffd094002f7e84a0017fe425000bfea128000ef5094002ff884a0057ff3250029ff1928000ff4c9400a7f864a0003ff61500017fb0a8013ff98540015fcc2a0003fd6150027fe30a8002bf185400b7fea2a004ffe5150001fea8a8013ff1454002ffe82a0017bf415000bff20a8005ff505400077a82a0017fc415002bff98a8013ff8c540007fa62a004ffc3150029ff90a8013ff88540007fa42a004ffc21500037fb028001ffd414000efea0a0007fe5050003fea828001df5414000ff8a0a0007ff405000bfda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffe60a0007fe3050003fe1828001ffc814000ffc40a0007fa2050003fe1028001ffc414000ffc20a0007fc1050001ffb2a6000bfd9530097fcca9801afe654c001feb2a6000bf59530097f8ca9801afc654c001ffb226000bfd913008ffcc898016fe644c001feb226000bf5913008ff8c898016fc644c025ffaa26011ff95130007faa898047fc544c0037fb1a6004ffd4d30027fca698013fd534c009fe29a6004ffd0d30027fc8698013de434c009fea1a6000f750d30027f88698003ff624c0017fb126010ff9893001dfcc498003fd624c021fe3126003bf18930097fea498043fe524c001fea926010ff1493008ffe8498043fe424c001fea126010ff10930027fe6498013df324c009ff1926004ff4c930007ba6498013fc324c001ffb0a6000bfd853007ffcc29800afe614c001feb0a600fff18530015f8c29804bff514c01fff28a6000ff5453007ff8a298047ff414c001dfa0a600fff90530007fa8298003bd414c01ffe20a6004ffcc530027be6298013fe314c009fe98a6000f74c530027f86298043ff214c01fff10a6000ff4853007ff84298006ff604c003ffa826001dfd413000ffca098007fa504c003fea826001df54130007f2a09800379504c003fe2826001ffd013000ffc8098007fd404c003fe2026001ffcc130027f66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff9026001ff8813000ff84098007ff104c003ff0826001fe8413000ff82098003ff65480017fb2a400eff99520035fcca90003fd65480017eb
  | 2 => 0x2101fde409080ffe2048407fe1024202ffc4121017ee209080bfe1048405fe0824206dfd9350036fcc9a801b7d64d400dbe326a006dfd8f50036fcc7a801b7d63d400dbe31ea01edfd0f500eefc87a80037d43d403bbe21ea006dfd8b50036fcc5a801b7d62d400dbe316a01edfd0b500e6fc85a80037d42d4039be216a01ddfccb500e6fc65a80037d32d4039be196a006dfd8750036fcc3a801b7d61d400dbe30ea01edfd07500067e83a806f7e41d4001bea0ea000cf507500def883a80777f31d4037bf18ea000df4c7500def863a80737f21d4037bf10ea000df487500def843a80067d60d4003bfa06a001df9035000ef881a80077f30d4003bf186a001df0c35000efe41a80077e20d4003be106a001dfc435000efc21a80077c10d40037fb2aa000ffd9150005fec8a806bfe645400b7f322a000ff591500d7f8c8a8016fc645400dffaa2a006dfd5150037fca8a806b7e545400dfeaa2a000df55150037f8a8a801b7c5454001ffb1aa000bfd8d500cffcc6a8012fe6354001feb1aa019ff18d50025f8c6a801bff535400dbfa9aa006ff94d500cefca6a801bfd5354001bea9aa006ff14d50036f8a6a806bff4354033ff21aa000ff50d500cff886a8003ff62540017fb12a018ff9895001dfcc4a8003fd6254031fe312a003bf18950037fea4a801b7f525400dff292a018df94950037faa4a80037d525400dfe292a006df149500d7fe84a8063fe4254001fea12a018ff109500cffe64a8063fe3254001fe992a018ff0c950007fec2a8002ff615402fff30aa002bf98550007fac2a805ffc61540057e30aa006ffd4550036fea2a801bfe515402fbf28aa006ff54550006faa2a801bfc515400dbe28aa01affd05500077e82a805ffe4154001fea0aa000ef505500bff882a8067ff315402fff18aa000ff4c5500bff862a8063ff215402fff10aa000ff485500bff842a8006ff6054003ffa82a006fed415000ffca0a80077e5054003fe282a001df1415000ff0a0a8007ff4054003ff202a001ff1015000ffe60a8007fe3054003fd182a001ff0c15000ffe40a8007fe2054003fe102a001ffc415000ffc20a8007fa1054003fe082a000dfd91500d6fcc8a80037d6454035be322a000dfd8d500cefcc6a80037d6354033be31aa01adfd0d500cefc86a80037d4354033be21aa000dfd89500c6fcc4a80037d6254031be312a01adfd09500c6fc84a80037d4254031be212a019dfcc9500c6fc64a80037d3254031be192a000dfd85500befcc2a80037d615402fbe30aa01adfd05500067e82a805f7e4154001bea0aa000cf505500bef882a80677f315402fbf18aa000df4c5500bef862a80637f215402fbf10aa000df485500bef842a80077f60540033fb02a006ded815000efe80a80077e4054003be202a001dfcc15000efc60a800
  | 3 => 0xf98a8202ef8c5410177862a080bbf2150405df10a8202ed885410177842a0803bf605044fdf3028200ef5814113f78c0a08abbf505044fdf2828227ef1414114f7e60a089fbe305044fde1828228efc814113f7c40a089fbc2050405df8828202edc41410177c20a080bbc1050401ffb2a6200bfd9531006feca988027f654c44dff32a6206bf99531007faca98802fd654c44dfe32a6206bf19531006f8ca9881a7c654c401ffb226200bfd913112ffcc898816fe644c401feb226200bf5913112ff8c898816fc644c44dffaa26225ff95131007faa898897fc544c4057fb1a6204ffd4d31027fca698813de534c409fea9a6200f754d31027f8a698813ff434c409ff21a6204ff50d31027f88698803ff624c4017fb126224ff9893101dfcc498803fd624c449fe3126203bf18931137fea498893fe524c401fea926224ff1493112ffe8498893fe424c401fea126224ff10931027fe6498813df324c409ff1926204ff4c931007ba6498813fc324c4057fb0a6202ffd4531017fca29880bf6514c405fea8a6200fd54531017f8a29880bff414c405dfa0a6202ff90531017fa829880bbd414c405fe20a6202ffcc531027ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff90a6202ff88531017f84298803ff604c4017fb026223ff9813100dfcc098803fd604c447fe3026201bf18131137fea09888ffe504c447fe2826225ffd013111ffc809888ffc404c409ff9826204f7cc131027fc6098813fc304c449ff9026223ff8813111ff8409880bff104c405fb8826202ff84131017f82098803ff65484017fb2a4222ff99521035fcca90803fd65484017eb2a4222ff19521035f8ca90803ff64484017fb224221ff9912102dfcc890803fd64484017eb224221ff1912102df8c89088bff5448443ff2a24200ff5512110ff8a890803ff63484017fb1a4220ff98d21025fcc690803fd63484017eb1a4220ff18d21025f8c69088bff5348441ff29a4200ff54d21107f8a690887ff4348441ff21a4200ff50d21107f8869080aff6248407ffa924203ff9492101fdca49080ffd5248401f6a924203ff1492101ffe849080ffe4248407fea124203ff1092101ffe649080ffe3248407f71924203ff4c921007da649080ffc32484057fb0a4202ffd4521017fca29080bfd5148405fe28a4202ffd05210177e829080bfe4148405fb20a4202ff505210177a8290803f54148401daa0a4202ff10521017fe629080bfe3148405fe98a4202ff0c521017fe429080ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec09087ffe60484037f3024200ff581210fff8c090806fc6048445ffa82421fff941210fff8a090887ff404843fff202421fff10121107fe609087ffe304843ffe1824203ffc81
  | 4 => 0x80b7c5154405fa28aa202ffd0551017fc82a880bfc4154405ff98aa202ff8c551017ec62a880bfc3154405ff90aa202ff88551017f842a8803ff60544017fb02a22fff9815100dfcc0a8803fd605445ffe302a201bf18151037fea0a881b7f505440dff282a206ff14151197fe80a88bffe405445ffe202a231ffcc15117ffc60a88bffc3054461ff902a22fff8815117ff840a880bff1054405ff082a202ff0415102f7ecba0817be65d040bdeb2e8205ef1974102f7ec7a0817be63d040bdeb1e8205ef18f411777ea7a08b7be53d0401dea9e822def14f4102f7ec5a0817be62d040bdeb168205ef18b411777ea5a08b3be52d0401dea96822cef14b4116f7e65a08b3be32d0401de996822cef0cb410157ac3a080bbf51d0405df28e8202ef5474101778a3a080bbf31d0405df18e8202ef0c7410177e43a080bbe21d0405de10e8205efd834102f7cc1a0817bd60d040bde306822eefd434115f7ca1a08afbc50d045bdf986822bef8c34115f7861a08b3bf20d0457df106822bef083410177e21a080bbe10d0405de0868200ffd9541005fecaa08abfe655040d7f32a8200ff59541005facaa08abfc655040d7e32a8202bfd914102ffea8a08abbf545040bff2a28205ef9514102ffaa8a0803bd545040bfe2a28205ef15141007fec6a0802ff6350453ff31a8204bf98d41007fac6a08a7fc63504097e31a822affd4d4114ffca6a0803fd5350453fe29a8205ffd0d4102f7e86a0817fe4350453df21a8205ff50d410077a86a0817fc435040bde21a8200ffd8941005fec4a08a3fe62504077f3128200ff58941147f8c4a080efc6250455ffa928228ff94941007faa4a08a3fc525040bffa128205efd094102ffc84a08a3be425040bfea128200ef5094102ff884a0817bc4250453ff9928228ff8c941007fa64a08a3fc32504057fb0a8202ffd4541017fca2a080bfd5150405fe28a8202ffd054102fee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff98a8202ff8c541017f862a080bff2150405ff10a8202fd88541017f842a0803ff60504017fb028227ff9814100dfcc0a0803fd605044ffe3028201bf18141157fea0a089ffe505044ffe2828205ffd014102f7e80a0817fe405044fdf2028205ff1014102f7880a08a7ff305044fff1828227ff0c141147fe40a089ffe205044ffe1028202ffc4141017ee20a080bfe1050405fe0828200efd95411577ccaa0803bd6550455de32a8200efd8d4114f7cc6a0803bd6350453de31a822aefd4d4114f7ca6a0803bd5350453de29a8200efd89411477cc4a0803bd6250451de312822aefd49411477ca4a0803bd5250451de2928229efcc9411477c64a0803bd3250451de1928202efd85410157ec2a0817b76150405dfa8a8202ef945410177aa2a080bbc5150405d
  | 5 => 0x8d421d7fea6a10e7fe5350801fea9a8439ff14d4202ffe86a1017fe435080bfea1a8405ff10d4201dfec4a100fff5250807ff2928403ff5494201ff8a4a100fff425080bf7a128403ff9094201f7c84a100ffc4250807de2128403fb1094201ffe64a100ffe3250807fe1928400ffd8542005fec2a10e3fe61508057f30a8400ff585421c7f8c2a100afc6150875ffa8a8438ff945421c7f8a2a1017ff415080bdfa0a8405ff9054202ff882a10e7ff3150871ff18a8438ff0c54201ffe42a100ffe2150807fe10a8400ffd8142005fec0a10dffe60508037f3028400ff581421bff8c0a1006fc6050875ffa828437ff941421bff8a0a1017ff405080bdfa028405ff9014202ff880a10e7ff305086fff1828437ff0c14201ffe40a100fef2050807ff1028403ff081421c7fe20a10dffe105086ffe0828400ffd9532005feca990dbfe654c80d7f32a6400ff59532005faca990dbfc654c80d7e32a6400ffd9132005fec8990d7fe644c80b7f3226400ff59132005fac8990d7fc644c80b7e3226436ffd51321affca899003fd544c86bfe2a26403bfd8d32027fea6990dbdf534c809ff29a6404ff54d32027f8a699013dc534c809ffa1a6404ff90d32027bc8699013fd434c801eea1a6404ff10d3201dfec49900fff524c807ff2926403fb9493201ffaa499003ed524c807fe2926403ffd09321afde849900ffe424c807fea126403ff1093201fd8849900fff324c809f79926403ff8c93201fbc649900ffc324c807ee1926403fb0c932007fec299002ff614c869ff30a6402bf98532007fac2990d3fc614c8057e30a6436ffd45321a7fca2990d3fc514c86bffa0a6434ff905321a7f88299013ff314c809ef98a6404ff8c532027f8629900fff214c807f790a6403ff8853201ff84299003ff604c8017fb026433ff9813200dfcc099003fd604c867fe3026401bf181321b7fea0990cffe504c867fe2826435ffd013219ffc80990cffc404c809ff9826404f7cc132027fc6099013fc304c807ff9026403fbc813201ffc409900ffc204c869ff8826433ff8413219ff8209900aff6554401ffb22a200bfd9151197fcc8a8816fe6454401feb22a232ff1915102df8c8a881bff545440dff2a2a206ff55151037f8a8a8803ff63544017fb1aa231ff98d51025fcc6a8803fd6354463fe31aa204bf18d51037fea6a881b7f535440dff29aa206ff54d51006faa6a881bfc5354465ffa1aa231ff90d51007fa86a88c7fc4354401ffb12a200bfd8951187fcc4a880efe6254401feb12a230ff1895101df8c4a881bff525440dbfa92a206ff94951037faa4a88037d525440dfe292a232ffd0951187fc84a8803fd4254461fe212a231ffcc951187fc64a8803fd3254461fe192a202bfd8551017fea2a881bf75154405ff28aa202df94551017f8a2a8
  | 6 => 0x17fb02a643ff9815300dfcc0a9803fd6054c87fe302a601bf18153037fea0a981b7f5054c0dff282a606ff14153237fe80a990ffe4054c87fe202a604ffcc153027fc60a9813fc3054c8bff902a643ff8815321ff840a9913ff1054c87ff082a643ff04153007fecaa1802ff6550c85ff32a8606bf99543007facaa1802fd6550c85fe32a8606bf19543025fec8a1817ff5450c0bff2a28605ef9514302ffaa8a1803bd5450c0bfe2a28604bfd8d43027fea6a1813fe5350c09fea9a8604ff14d43027fe86a1817df4350c09ff21a8604ef90d43027f886a1813bc4350c09ee21a8600ffd8943005fec4a1907fe6250c077f3128600ff5894320ff8c4a180efc6250c85ffa928641ff9494320ff8a4a1817ff4250c0bff2128641ef9094302ff884a1817bc4250c09ff9928604f7cc943027fc64a1813fc3250c01ffb0a8600bfd8543207fcc2a180afe6150c01feb0a8640ff18543015f8c2a190bff5150c81ff28a8640ff1454302ffe82a1817bf4150c0bff20a8605ff10543027fe62a1813fe3150c09fe18a8641ffc8543207fc42a1903fc2150c01ffb028600bfd81431fffcc0a1806fe6050c01feb02863fff1814300df8c0a190bff5050c7fff282863fff1414302ffe80a1817bf4050c0bff2028605ff10143027fe60a1813df3050c09ff1828604ff0c14320ffe40a18fffe2050c7ffe1028640ffc41431fffc20a18fffc1050c077fb2aa400ffd9152005fec8a90fbfe645480b7f322a400ff591521f7f8c8a9016fc645480dffaa2a406dfd5152037fca8a901bfd5454801beaa2a406ff15152007fec6a9002ff635487bff31aa404bf98d52007fac6a90f7fc63548097e31aa406ffd4d52037fca6a90f77e535480dfea9aa406ff14d52036f8a6a90fbff435487bff21aa400ff50d521eff886a900eff6254807ffa92a406fbd495201ffca4a900f7e5254807fe292a403df1495201fd8a4a900fff4254807ff212a403ff1095201ffe64a900ffe3254807f7192a403ff0c952007fec2a9002ff6154879ff30aa402bf98552007fac2a90f3fc61548057e30aa406ffd4552036fea2a901bfe515480dfe28aa43effd05521e7fc82a90f3fc415487bff98aa43cff8c5521e7f862a900fff2154807f790aa403ff8855201ff842a9003ff60548017fb02a43bff9815200dfcc0a9003fd6054877fe302a401bf18152037fea0a901b7f505480dff282a406ff141521f7fe80a90effe4054877fe202a43dffcc1521dffc60a90effc3054807ff902a403ff8815201ff840a90f3ff1054877ff082a43bff04152007fecaa1002ff6550875ff32a8406bf99542007facaa1002fd6550875fe32a8406bf1954201dfec8a1017ff545080bff2a28405ff5514202ff8a8a1003ff63508017fb1a8439ff98d42025fcc6a1003fd6350873fe31a8404bf1
  | 7 => 0x82a0080080480001007402000002034088030120080080800600400004004004010020020040380301600c0702906a0000280000803c0000000a0101d00e000000018090000000000000c0100000500c0000583e0040040001102a00400000010014000010060000480c00a0000282900002c0b014002024008360000080580001600c0400f0140000080106c0040c80400204408001006004018130000000080f0000000083e0040040280600800000017002080090050160040180709600802002000004008010020001182502a0cc0000300a0540087e004000088000300000100000000c020050020000000004e0540e00000402c0a00004002c0b003006004040010060140000002a0000101b0260300181100a08c030040440040c01000000400016002000040000280000000c00c0140080000000801807002008020060080201000200a0243100001401c0002801200000001008054028160040000900f0000b00b7fb2aa805bfd915402ffea8aa01bbf545500bff2a2a805df9515402ff8a8aa0177c545500bde2a2a800ffd8d54005fec6aa12bfe63550097f31aa800ff58d54257f8c6aa012fc635500dffa9aa806ff94d54037f8a6aa017ff435500bdfa1aa805ff90d5402ff886aa003ff62550017fb12a849ff9895401dfcc4aa003fd6255093fe312a803bf18954037fea4aa01b7f525500dff292a806ff1495402ffe84aa017fe425500bfe212a84affcc95424ffc64aa127fc3255001ffb0aa800bfd8554247fcc2aa00afe6155001feb0aa848ff18554015f8c2aa01bff515500dff28aa806ff1455402ffe82aa017bf415500bff20aa805ff10554257fe62aa123fe3155091fe18aa849ffc8554247fc42aa123fc2155001ffb02a800bfd815423ffcc0aa006fe6055001feb02a847ff1815400df8c0aa01bff505500dbfa82a806ff94154037f8a0aa017ff405500bff202a805ff10154257fe60aa11ffe305508ffe182a849ffc815423ffc40aa11ffc2055091ff882a847ff8415423ff820aa012ff6554c01ffb22a600bfd9153237fcc8a9816fe6454c01feb22a646ff1915302df8c8a981bff5454c0dff2a2a606ff55153037f8a8a9812ff6354c09ffa9aa606f7d4d53027fca6a98137e5354c09fe29aa604df14d53027b8a6a9813ff4354c09ff21aa604ff10d53007fec4a9802ff6254c8bff312a603bf98953007fac4a9917fc6254c077e312a606ffd4953037fca4a981bfc5254c8dffa12a645ff9095322ff884a9813ff3254c09ff192a604ff0c953007fec2a9802ff6154c89ff30aa602bf98553007fac2a9913fc6154c057e30aa606ffd4553036fea2a981bfe5154c0dfe28aa646ffd0553227fc82a9913fc4154c09ff98aa604f7cc553027fc62a9813fc3154c8bff90aa644ff88553227f842a9803ff6054c0
  | 8 => 0xac0000001b290d29fa5c9a3a39b42317195a0192caa080000030b2f7109aef31123003c84a10d8342cda918e1b2ba0a05fb1312a8002ce229297b3e06e2a8b20105a06a1806f9e39e91bba731969b7ac81269c889f2f0b360e72ed89925827da2c92095f80011188497494e09da52951a6db2787d1530000e42e30001a5112a139979621dc88f92919318e80003218d20e0f032f91411e9c60fe1d997b93d31880017b000090a14a032589b40869ceb14800212800287a788f68002fc1060001319138001651079c0a7c8d73121c50a38d4adb8cab2407c0002f80db99a8cf9088dd06d09193fa098eead5a2aaa7200992815037871a492b0a2d1b191002903d0850cc8000ad9bb0ef2e28002c01d91f0abf9cc8000f423380032c00008d0312821fc8d425189507f3300bc28c00021c8001ad27fa562ce800000340317947b499728002c1b4b9918019942752a60000001ac9c2b2522f80027e0288ea1fda6baf10000cba599841603198d629babdb0d00026a0000002c3a3c8ff05f20587790b18124c86a8001012b6175a038002628001d49541b48f59d580006719502f0000003219251a7088910800215247ab6a5bb14197000300aa980029e0000000fc0000be08e0002de0000001000002e6812a573339f60af0b432a80013407885e800000343b3900b0000912f5a43a4082c0001132bf00022ba7c0d800008f24e8178f49ab2df04727133a28a12382200021f0c50000002fa80017000014c80000004900000cb309862be9eb329a94a208df2a480028529415f1c315892ba983409301a28a900734a34624f80526333e8f100015580026cab024d0000002e900c00400200c0480801c0240000200601409811006008108000200180980900e010118020000000000000000000008006008008080120100080007600400004034018008150000000503d0200200581f05211c00000000000000070000140000400002c0b80600002807808006000200020100200481c00206002800010000030060000080880601a0000100802c0080000b03c0000400a00204c0380004a048008010000a4008040040040080000a01001013016008000000020ec0b80200000c07007000028000000000040e8080200a8008020300dc0200102e02c0280000e048048090300101202900001401018000000000030020300280200e01c2d80200600c018000200100000500801c0000000401800800006000000040080380200b00000800016058000020010000080800400201c03805002004040000280000000a0060000c826006004008050320000100502006c05800000000048030220000001e00a0040e80600004c0300100a0540180400000000008002008028020100080280101e00c0180003e0140c82e0000340002200210c020050760080703700c000
  | 9 => 0xb87313b0df996225313a07133106a93a921352688870658a31de92e98a9550701b01bdaaa9b88ca0278ae32e27200a885abb2d91cd115299a6e1bd1d182820e8d78000c3a690cb10e8000001770b69c101603807b0000002a22eab389c718a2198629a880009000017f8ab8002d18000a0a24a682e80090ef8000bc8002b82390002cc99a30900005400017780033c2ff8000000000c819c0002dd0001038003342b88228c5acd0430fb0000000ce00002a88180000005e31900000018884c19fac617daee87714598b8e885da450d6b470000708001d32738000111ac285ac68000f880000015129c10325215280f93a8b2308acfb352d32fd8001262e584080028db1cab32639e9ac58e59f691e1f2b0500008118724c1c90000e927917aa0d85c33d9228001ae8ec0001db87386080009a96b1c00000000002f6325aa69f706b00017300000a0a48c629d8a28ed0000aca9100016e0d8ad033b12302330f286a9a0000002389440000000468060aa058ae1a64276941aba8000000001e40001ea2b49c7b238ee0e79d68d92df8b61ed0002762a11d10ae8159b628c96aa3c0190e60141ee0000002b500000028e9fe9e622a0000000001da8000002d8a258048ea8420001471be9af00020c1439898002410000002c9a4305c9218021cf1fd2e7825336b4786ba6780003eb4b0000970000001858a780025580022c34880001eb4eaf9076a6d1568c09e8000149b1b00004ba72a60a881f1a5f2b719f134ab41fe32a2202b78d22381538a68002482368c92bd306b062dc94f33d2c32d28002ae95b1a48be80005290a8001670000690001d61eb9d3a0a8e0aeb1aaaab80011d00013280027b9bf2ac0eb1f53210030571bc03ab1ba6220caa914109a28e1288a80de88c19ea2280025d055a90167a4581a8000e00b996fadc22400000023f00009e9c68000002d0818af20000b831a91c9cf8001fa8eda4f00021d8001792a505229f1e88000000000f3b0403623e0c18002cc1cd8002a19fa23185981fad80000998001e50d000c1462a002580003b07517caed2ad98816eb490001822da9da2c431f274b3700034800004f089800235ab180015a28899d1b72fb30800034c827198b4197384d8f28001720b51a691a813800257902b0db448d5a349572743019639cb008aa80ab13f0c7a0b32c853080937a442bca178fd165a9cac285825b24191594b9649e20fd90b8d9a7a11813e05d07a11a0d10941271b82e424b0389240cd15da27064a4e1891bc892a5f8e22b2a4287ba8baa434d15ba70a6132898514886e8130298b48038c71f80a884a896240023b1084004823b179a210000dc80006a00022e1402ab2ec34133f0002819399408001cc33116102d88a80013828612d2828639c429693c8a590f27f1c834698cb3497822f1de2f1b2f1628
  | 10 => 0x2af9ff09ca8d00000006987a8921420da04d337b0c80009b1188002fe166800326a16a61aa58f91af90907c8bb0eb85508799b86301c0fa800335a1e8000c020d0428548001fc0949751248002f6a5a0741bf800056ae10000002f981e1608099191dc0a22500002779f78a414e8d0a3f800169a652c218325c06d8e81e2aaf0ad16a342800000248aa38002872c89599322898da8000ff9a30002541868c6b3cad7b0e8c31ff9480209431e4a6690f9f4aeb850aec99113c1429ae07113714db029d50000001b08338000000561468002548e6b1fa8f0000002140001681e69be2da1a59d407580000031196c9ca9312d212592b07d80004121d33293b8000000eca3717680032300032931c237a462db24a29b1e125e1a031e23421122686c89d05a0e99762bba50800096950a800000001e3000315a8109f80028400027a8000122deb458042f0000181831a1c0002f39298c98418b3b0101c99e0e38bb8ddb320820a611c26f32733819da082fba321f318c0309ea8d391ba0223aa7822b01183e11db24ad61b98fcae9b432f280026f80000f2469b330ab1a1689df8bf28396d98080014c0002568798e31168cf21f9050002960b1959305af4271999098954a121e1a079d02e006c2d10978db3001a188400005134e0aa92f8fbad515cac12001848cc0499520000f30001ad9b92600668069aa03c0001b12ca848b1d9368780001c4a3d03a0000000ba92001b9e58029838000000002360002f78000930002e49a7a8ab03a3300001092a0460b300014900009b80021ab4aa5dac0b221008000000001630198000b89619d70002539ab8ce80012d82ea0624982b0260b58000002d6a2601487e8002cb00013d8bd80003f1b58000000001998000219900002991690af80ba5317e9a60500c4a4734502a0ba0cdaf4acba3e8000b2a04a170b0b0f80da958479d819cb1606107901b2ae23daee25aaf5117a1894a2fe98b1e004e02ba698078a98f980580015e2e3a2d80000013a0000080001f884b2a7893b4db0980080015c2b381712e228895874a9d2ef800000000111138904b4419480004405b2350001c3919ad48600391640241ec1a9a1630a00017c1802f88832b584512c0f232d800000053a759f5b1009800000002e00000002c83d8a51a12191efafc83f92808393e84f872add8002c4a8b1788f790cb12a281ce0000000002950000000a19f917106500000e86f0b11583168001df000067ac500014d2d38000002830001fb8f18002ac88e80008b8349d78003318000000002ea17d23103680002f8d2935a10af322e9fb1ee9dd0002ad13098f1db03ba658000c232b0640002b11f22222510002fd00000018d861ac930c2700002fa2b9a0b96b8f82bc34c0001579e72aa10814a845ad71d29f42be2c79123180e28329f12c727d21
  | 11 => 0xf09d08e500032e9f011619200027b13396d1eda0915d2cf2d99ec92204382d144a6c2029a40688a11f9b229ba82485ba928de00030e16f0002972e532d2e701d13900032088b10c1a922321b00030731d2ca16614f9742a280016c1b39c9a0f13611f9279ef0d19908893032ff1938f710226b0352132b9232a23a7e8f51c18720e109e2118169c5a3b8b705183020400e0803398d314b03714515ea891ca22781f2908c117f29ea79a0100033f8c4230b3a87e2593079dd95aa1e12f3282e0a1597a26e8101b53330c29b6a4b98e0202102a31879e08681cb9d8a5508d84ca9326708c8fa03323a3260bd0b79b20359d226624229880d06610a0b01018882b220f82101a0762d428fa4a8b930b9a21170010579f38001e7a1a19b2e60a70180dc07fa29a44a84982800304907221b1e90e26a8bf8a02e881d9c21501980001a08622ba00025ea648000591210e480009c33b9042e218f88600031500029aa08a05000302000082a8097091b02695617184497e0f60fea771ba08a11491f05a8c88d504e8001a824d839800
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb72541100577b525411025f7a5254110007795254110057785254110007f37154110015fa7154110015f871541100bff0715411000efb615411000ff361541100bf7b51541100bf7a51541100bf7951541100bf7851541100bfbb41541100bff241541100bfb94154110007f14154110007b141541100bff23154110007f131541100bff22154110007f121541100577b76541100367b76541100bf7876541100367876541100077b745411026f7a745411000779745411026f7874541100077b645411026f7a645411000779645411026f7864541100077b73541102677a73541100077973541102677873541100077b63541100067b63541102677a635411000779635411000679635411026778635411026f7b43541102677a43541100077943541102677843541100077b725411025f7a725411000779725411025f7872541100077b625411025f7a625411000779625411025f78625411026f7b425411025f7a425411000779425411025f7842541102677b325411025f7a325411000779325411025f7832541100bf7b71541100077371541100bf7a71541100bf7971541100bf7871541100bf70715411000f7b615411000e7b615411000f7361541100bf7b41541100bf3b41541100bf7a41541100bf7241541100bf7941541100bf3941541100077141541100073141541100bf7841541100bf7b31541100bf7a31541100bf7231541100bf7931541100077131541100bf7831541100bf7b21541100bf7a21541100bf7221541100bf7921541100077121541100bf782154110015f8764c110026f8764c110014f8764c110005fb754c110005f9754c110006fb654c110006f9654c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110047d8634c110047da434c110007d9434c110005fb724c110047db324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c11000efb614c11000ff3614c11007fbb414c11007ff2414c11007fb9414c110007f1414c110007b1414c11007fdb314c11007ff2314c11007fd9314c110047f1314c110007d1314c11007ff2214c110007f1214c110015f8764811001ef87648110014f87648110005fb7548110005f97548110007bb7448110007b87448110006fb6448110006f96448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811001efa624811001ef8624811003fe8624811003fea4248110007e9424811003fea3248110007e93248110007f37148110015fa7148110015f8714811005ff0714811000efb614811000ff3614811005fbb414811005ff2414811005fb94148110007f14148110007b1414811005ff23148110007f1314811005feb214811005ff2214811005fe9214811003ff12148110007e12148110
  | 1 => 0x510007b5425051004fb44250510007f3705051000df6705051000df4705051013ff07050510016f76050510017f3605051013f77505051013ff2505051013f75505051013fb7405051013fb6405051013fb5405051013fb4405051013ff2305051013ff2205051004fb7765051002eb7765051013fb4765051002eb47650510007b77550510287b67550510007b57550510287b47550510007b76550510287b66550510007b56550510287b46550510007b7735051027fb67350510007b5735051027fb47350510007b7635051027fb66350510007b5635051027fb46350510287b7535051027fb65350510007b5535051027fb45350510007b77250510277b67250510007b57250510277b47250510007b76250510006b76250510277b66250510007b56250510006b56250510277b46250510287b75250510277b65250510007b55250510277b4525051027fb73250510277b63250510007b53250510277b4325051013fb77050510007b3705051013fb6705051013fb5705051013fb4705051013fb07050510017b76050510016b76050510017b3605051013fb7505051013f37505051013fb6505051013fb2505051013fb5505051013f35505051013fb4505051013fb7305051013fb6305051013fb2305051013fb5305051013fb4305051013fb7205051013fb6205051013fb2205051013fb5205051013fb4205051000df4764c510026f4764c51000cf4764c51000777754c51000774754c510006f7654c510006f5654c510005f7744c510005f5744c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510047d6534c510007d5534c510005f7724c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c51011ff0704c510016f7604c510017f3604c51011f77504c51011ff2504c51011f75504c51011fd7304c51011ff2304c51011fd5304c51011ff2204c51000df4764851001ef4764851000cf47648510005f77448510005f57448510006f76448510006f56448510005f77348510005f57348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851003fe65248510007e5524851003fe63248510007e53248510007f3704851000df6704851000df470485100fff07048510016f76048510017f360485100ff7750485100fff250485100ff7550485100fff230485100ffe720485100fff220485100ffe52048510015f87654110036f87654110014f8765411000dfb755411000f7b75541100077b6554110036fa6554110036f865541100577865541100577b545411026f7a5454110007795454110057785454110005fb7354110006fb6354110006f963541100577b53541102677a5354110007795354110057785354110005f
  | 2 => 0xcff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d102c6bf41d8d102c6bd41d8d102c6df31d8d102c6dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d102b67f50d8d102b6fa50d8d102b67d50d8d102b6df30d8d102b6dd30d8d10024ff7658d100057f7558d100557c7558d10046dc6358d102adf77158d102bdfb7058d10004ff7558d100067f7558d100047f7558d10034fe7558d10034fc7558d100067c7558d100347c7558d10004ff7458d1002cfe7458d1002cfc7458d102b4ff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d10046df3258d102acff7158d10006f77158d1007ebf4158d1007ebd4158d1011cff7058d10006fb7058d1011e7f5058d1011efa5058d1011e7d5058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100367e6554d100067d6554d1000dfa7054d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1002ebe6450d10006bd6450d10015f67150d1001cfe76d891003eee62d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100fcfd72d8910006ef42d891003eec42d891000cff71d8910014fe71d891000cfd71d8910014fc71d89102a6bf41d89102a6f641d89102a6bd41d89102a6ef21d89102a6ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d89102967f50d89102967d50d8910296ef20d8910296ed20d891001cff7658910005bf745891004dbc745891003eec625891028df7715891029dfb7058910004ff7558910034fe7558910034fc7558910004ff7458910006bf7458910004bf745891002cfe745891002cfc7458910006bc745891002cbc7458910004ff7358910024fe7358910024fc7358910294ff7258910006ef725891003eee325891028cff7158910006f7715891005ebf415891005ef6415891005ebd41589100fcff7058910006fb70589100fe7f50589100fe7d5058910004ff7654910004fe7654910004fd7654910004fc76549100367e65549100067d655491000dfa7054910004ff7650910004fe7650910004fd7650910004fc765091002ebe6450910006bd6450910015f67150910004ff764c910004fe764c910004fd764c910004fc764c910026de634c910006dd634c91001eee624c910006ed624c910015f6714c91000dfa704c91000df4765051002ef4765051000cf47650510015f77450510017b77450510007b7645051002ef6645051002ef4645051004fb46450510287b7545051004fb65450510007b5545051004fb45450510005f7735051004fb7435051027fb64350510007b5435051004fb44350510005f77250510006f76250510006f5625051004fb74250510277b6425
  | 3 => 0xa645012002ef8645012006fb8645012006fbb4350120007b94350120007eb725012001dfa725012001df872501200a7e8725012000efb625012000feb62501200a7bb42501200a7ea42501200a7b9425012006fe94250120007a942501200a7ea3250120007e93250120005fb715012006fbb4150120007b941501200a7eb2150120007e92150120034fe76d95100567e65d951017cfd75d951002cfe74d9510004fd74d951002cfc74d9510024fe73d9510004fd73d9510024fc73d95100067e53d95100567c53d951001cfe72d9510004fd72d951001cfc72d951000cff71d9510014fe71d951000cfd71d9510014fc71d95102f67f51d95102f67d51d95102f6bf41d95102f6bd41d95102f6f631d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102ee7f50d95102ee7d50d95102eefa30d9510034ff76595100567c6559510005df7359510045dc73595102e5f771595100ddfb70595102ecff75595100067f7559510004ff745951002cfe745951002cfc7459510004ff7359510006df7359510004df7359510024fe7359510024fc7359510006dc7359510024dc73595100567f5359510004ff725951001cfe725951001cfc72595100567f52595102e4ff7159510006f771595100be7e51595100be7c51595100bebf41595100bebd41595100bef6315951017cff7059510006fb705951017e7f505951017e7d505951017efa305951002cfe76d911004ebe64d9110034fe75d9110004fd75d9110034fc75d911013cfd74d9110024fe73d9110004fd73d9110024fc73d911001cfe72d9110004fd72d911001cfc72d9110006be42d911004ebc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102debf41d91102debd41d91102def621d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91102ce7f50d91102ce7d50d91102cebf40d91102cebd40d91102cefa20d911002cff765911004ebc6459110005ef725911003dec725911015df771591102d5fb7059110004ff7559110034fe7559110034fc75591102ccff7459110006bf7459110004ff7359110024fe7359110024fc735911004ebf4359110004ff7259110006ef7259110004ef725911001cfe725911001cfc7259110006ec725911001cec725911004ebf425911015cff7159110006f7715911009ebf415911013ebd415911009ef6215911013cff7059110006fb705911013e7f505911013e7d505911013ebe405911013ebc405911013efa2059110004ff7655110004fe7655110004fd7655110004fc7655110024fe76d8d10046de63d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d1011cfd73d8d10006df53d8d10046dc53d8d1001cfe72d8d10004fd72d8d1001cfc72d8d10
  | 4 => 0x8520024fc73d852000cfd72d8520014fc72d8520306ee32d8520006ed32d852005ef621d8520306f521d852000cfe70d852001cfd70d852000cfc70d852028e7f50d852028e7d50d852028ef710d8520005bf745852006dbc7458520006bf6458520006bc645852005ef461585202fdfb7058520004ff7654520004fe7654520004fc76545200367e65545200067d6554520006bf6454520196bc645452002ebf76d0520005be76d052006ebe76d0520004be76d052006ebd76d052006dbc76d052002ebc76d052002cbc76d0520006bf65d0520176be65d0520006bd65d0520176bc65d0520006bf63d052016ebe63d0520006bd63d052016ebc63d0520167ae72d052006fad72d052015ebf62d0520167ae32d0520007ad32d052013dbd71d052005ebf61d0520016be61d0520016bc61d052005faf21d052015fba70d052006fb970d052015ebf60d052015f3f50d052015f3d50d0520167bb20d052015fae20d052015fac20d052015fb820d052015fba10d0520004ff7650520004fe7650520004fc7650520006bf645052002ebe6450520006bd645052002ebc645052001dee7250520147ae4250520007ad4250520016f6615052000dfa705052013fba4050520006bf7650520005be7650520006be7650520004be7650520006bd7650520005bc7650520006bc7650520004bc7650520006bf6550520156be6550520006bd6550520156bc6550520006bf635052014ebe6350520006bd635052014ebc6350520147ae7250520007ad725052013ebf6250520147ae3250520007ad325052015dbf715052006fb7715052005ebf6150520016be615052005fb66150520016b66150520007b56150520016bc615052005faf215052005fb62150520147b5215052013fba7050520007b9705052013ebf605052013f3f505052013f3d5050520147bb205052013fae205052013fac205052013fb8205052013fb7105052013fba1050520004ff764c520004fe764c520004fc764c5200057f754c5200757c754c520006bf644c52012ebc644c520026de634c520006dd634c52001dee724c520007cd324c52000dec7648520016ec764852000cec7648520006ef6548520006ed6548520005ef7448520005ed7448520007af6448520007ac6448520005ef7348520005ed7348520006ef6348520006ed634852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005faf414852005fe6414852005fad4148520007e54148520007a54148520007eb704852000dee704852000dec70485200ffe8704852001eef604852001feb60485200ff6f50485200ff6d50485200ffea40485200ffe710485200ffea104852001df8765012002ef8765012001cf8765012000dfb745012000fbb7450120007bb645012002ef
  | 5 => 0x33fbb2019120337ae2019120337ac2019120337b82019120337ba1019120004ff7655120004fe7655120004fd7655120004fc76551200367e65551200067d6555120006bf645512002ebc6455120024fe76d8d200757e75d8d200057d75d8d20006bf64d8d20006bc64d8d20066de63d8d20034fe75d8d200067e75d8d200347e75d8d20004fd75d8d200067d75d8d200047d75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2019cfd73d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d2032edf32d8d2032edd32d8d20014fe71d8d20004fd71d8d20014fc71d8d2032eef21d8d2001cff70d8d2001cfd70d8d2031e7f50d8d2031e7d50d8d2031edf30d8d2031edd30d8d2031efa10d8d20024ff7658d20005bf7458d2006dbc7458d20006bf6458d20006bc6458d20066dc6358d20315ef7258d20325fb7058d20004ff7558d20034fe7558d20034fc7558d20004ff7458d20006bf7458d20004bf7458d2002cfe7458d2002cfc7458d20006bc7458d2002cbc7458d2031cff7358d20006df7358d20066de4358d20314ff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d20066df3158d20086ef2158d2019cff7058d20006fb7058d2019e7f5058d2019e7d5058d2019efa1058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20006bf6454d20236bc6454d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d2002ebc6450d20026de6350d20006dd6350d2001dee7250d2020fae4250d2000dec765092002eec765092000cec765092001def745092001faf7450920007af645092002eee645092002eec645092006fac6450920005ef7350920005ef715092006faf4150920007eb705092000dee705092000dec70509201bfe8705092001eef605092001feb60509201bf6f50509201bf6d50509201bfaf40509201bfea40509201bfad40509201bfea105092000dec764c920026ec764c92000cec764c920006ef654c920006ed654c920005ef744c920005ed744c920007af644c9201aeee644c9201aeec644c920007ac644c9201aeac644c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c92030fcf534c920067cc534c920067ce434c920007cd434c920005ef714c920067cf314c920007eb704c92000dee704c92000dec704c92019fe8704c92000de8704c92001eef604c92001feb604c92019f6f504c92019f6d504c92019fea404c92019fcf304c92019fcd304c92019fea104c920014fe76d8520006bf64d8520006bc64d852005ef661d8520034fe75d8520004fd75d8520034fc75d8520006bf74d852002cfe74d8520004fd74d852002cfc74d8520006bc74d8520024fe73d8520004fd73d
  | 6 => 0xb70595201de7f50595201de7d50595201defa105952002cfe76d912006ebe64d9120034fe75d9120004fd75d9120034fc75d91201bcfd74d9120006bf54d912006ebe54d912006ebc54d9120024fe73d9120004fd73d9120024fc73d912006ebf43d9120006be43d912006ebc43d912000cff72d912001cfe72d912000cfd72d912001cfc72d912035ebf42d912035ebd42d9120014fe71d9120004fd71d9120014fc71d912006ebf41d9120006be41d912006ebc41d912001cff70d912001cfd70d91203467f50d91203467d50d9120346bf40d9120346bd40d9120335be76d912002cbe76d9120006bf65d9120006be65d9120006bd65d9120006bc65d9120006be63d9120006bc63d9120347af72d9120347ac72d912035fae32d9120005bd71d9120006be61d9120006bc61d912035faf21d912035fbb70d9120347b870d91203473f50d91203473d50d912035fbb20d9120347ae20d9120347ac20d9120347b820d9120347ba10d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bc53d9120346bf72d912035ebe72d9120346bd72d9120346bc72d912035ebf52d912035ebe52d912035ebd52d912035ebc52d912035ebf32d912035ebe32d912035ebd32d912035ebc32d9120006bf71d9120006be71d9120006bd71d9120004bd71d9120006bc71d9120006bf51d9120006be51d9120006bc51d9120006bf31d9120006be31d9120006bc31d912035ebf21d912035ebe21d912035ebd21d912035ebc21d9120346bf70d9120346be70d9120346bd70d9120346bc70d9120346bf50d91203463f50d9120346be50d9120346bd50d91203463d50d9120346bc50d9120346bf30d9120346be30d9120346bd30d9120346bc30d9120346bf20d9120346be20d9120346bc20d9120346bf10d9120346be10d9120346bd10d9120346bc10d912002cff765912006ebc645912034def7259120355fb7059120004ff7559120034fe7559120034fc7559120344ff7459120006bf7459120004ff7359120024fe7359120024fc735912034cff7259120006ef7259120004ff7159120014fe7159120014fc715912006ebf41591201bcff7059120006fb70591201be7f50591201be7d5059120345be761912006ebe7619120344be761912006f3e751912006f3d7519120006bf6519120006be6519120006bd6519120006bc651912006f9e731912006f9d7319120006be6319120006bc631912033fae7219120337ad7219120336bf621912033fae321912006fb67119120005bd711912006fb57119120005b57119120006be6119120006bc611912033faf2119120337ba701912033fb97019120336bf60191203373f50191203373d5019120
  | 7 => 0x8530007cd3248530007b54148530025f87654130036f87654130024f8765413000dfb755413000f7b75541300077b6554130036fa6554130036f865541300977865541300977b545413038f7a5454130007795454130097785454130007db7354130025fa7354130025f873541300cfd8735413000efb635413000fdb63541300cf7b53541300cf7a53541300cf7953541300cf7853541300cfda4354130007d943541300977b52541303877a52541300077952541300977852541300cfdb3254130007d93254130005fb7154130006fb61541300977b515413037f7a5154130007795154130097785154130007bb4154130007b941541300cfdb3154130007d931541300977b76541300367b76541300cf7876541300367876541300077b745413038f7a745413000779745413038f7874541300077b645413038f7a645413000779645413038f7864541300cf7b73541300075b73541300cf7a73541300cf7973541300cf7873541300cf58735413000f7b635413000e7b635413000f5b63541300cf7b43541300cf7a43541300cf5a43541300cf7943541300075943541300cf7843541300077b72541303877a72541300077972541303877872541300077b62541303877a625413000779625413038778625413038f7b42541303877a42541300077942541303877842541300cf7b32541300cf5b32541300cf7a32541300cf7932541300075932541300cf7832541300077b715413037f7a715413000779715413037f7871541300077b61541300067b615413037f7a615413000779615413037f78615413038f7b41541300073b415413037f7a415413000779415413000739415413037f7841541300cf7b31541300cf5b31541300cf7a31541300cf7931541300075931541300cf7831541303877b215413037f7a215413000779215413037f782154130034fe76d95200767e65d95201dcfd75d952002cfe74d9520004fd74d952002cfc74d9520024fe73d9520004fd73d9520024fc73d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203767f52d95203767d52d9520376ee32d9520014fe71d9520004fd71d9520014fc71d9520376ef21d952001cff70d952001cfd70d952036e7f50d952036e7d50d952036efa10d9520034ff76595200767c6559520005bf745952006dbc7459520365ef72595200e5fb705952036cff75595200067f7559520004ff7459520006bf7459520004bf745952002cfe745952002cfc7459520006bc745952002cbc74595200767f5459520004ff7359520024fe7359520024fc73595200067e53595200767c5359520364ff7259520006ef72595200c67e52595200c67c52595200c6ee3259520004ff7159520014fe7159520014fc71595200767f51595200c6ef21595201dcff7059520006f
  | 8 => 0x1b6dc654c930005df744c930005dd744c930006df644c930006dd644c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c930087ce524c930007cd524c9303a7cf424c930087cc424c930005df714c930087cf214c930007db704c93000dde704c93000ddc704c93019fd8704c930026df604c930027db604c93019f5f504c93019fda504c93019f5d504c93019fcf204c93019fda104c930014fe76d853007ef661d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d853039edf32d8530006dd32d853007ef631d853039ef531d8530024fd70d85302ae7f50d85302aefa50d85302ae7d50d85302aef710d85300057f75585300957c755853007ef46158530395fb7058530004ff7654530004fe7654530004fc76545300367e65545300067d655453000dfa705453002ebf76d053008ebe76d053008ebd76d053002ebc76d0530006bf65d0530176be65d0530006bd65d0530176bc65d053016f9e73d053008f9d73d053015ebf63d0530006bf62d0530166be62d0530166bc62d053016f9f32d05300079d32d053013dbd71d053007ebf61d0530016be61d0530016bc61d053007f9f31d053015ebf60d053015f3f50d053015fba50d053015f3d50d053016fbb30d053015f9e30d053015f9c30d053015fb830d053015fba10d0530004ff7650530004fe7650530004fc7650530006bf645053002ebe6450530006bd645053002ebc6450530025de735053014f9e43505300079d4350530006bf7650530006be7650530006bd7650530006bc7650530006bf6550530156be6550530006bd6550530156bc655053014f9e73505300079d735053013ebf6350530006bf6250530146be6250530146bc625053014f9f32505300079d325053015dbf715053008fb7715053007ebf6150530016be6150530016bc615053007f9f315053007fb6215053013ebf605053013f3f505053013fba505053013f3d505053014fbb305053013f9e305053013f9c305053013fb8305053013fb7105053013fba105053000ddc764c530016dc764c53000cdc764c5300075f754c5300075c754c530006df654c530006dd654c530005df744c530005dd744c530005df724c530006df624c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6514c530007d5514c53007f9f414c53007f9d414c530007db704c53000dde704c53000ddc704c53011fd8704c530026df604c530027db604c53011f5f504c53011fda504c53011f5d504c53011fd7104c53011fda104c530004ff7648530004fe7648530004fc7648530025de7348530005dd734853001eee624
  | 9 => 0xc74d953000cff73d9530024fe73d953000cfd73d9530024fc73d95303f67f53d95303f67d53d953001cfe72d9530004fd72d953001cfc72d95300967f52d9530014fe71d9530004fd71d9530014fc71d95300067e51d95300967c51d95303f6df31d9530024ff70d9530024fd70d95303ee7f50d95303ee7d50d95303eefa10d9530034ff76595300967c65595303e5df73595300edfb70595303ecff75595300067f7559530004ff745953002cfe745953002cfc74595303e4ff7359530006df73595300ce7e53595300ce7c5359530004ff725953001cfe725953001cfc7259530004ff7159530014fe7159530014fc71595300967f51595300cedf315953021cff7059530006fb705953021e7f505953021e7d505953021efa105953002cfe76d913008ebe64d9130034fe75d9130004fd75d9130034fc75d91301fcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d91303debf43d91303debd43d913001cfe72d9130004fd72d913001cfc72d9130006be42d913008ebc42d91303dedf32d9130014fe71d9130004fd71d9130014fc71d913008ebf41d9130024ff70d9130024fd70d91303ce7f50d91303ce7d50d91303cebf40d91303cebd40d913002cff765913008ebc64591303c5df73591303d5fb7059130004ff7559130034fe7559130034fc75591303ccff7459130006bf74591303c4ff7359130006df7359130004ff725913001cfe725913001cfc72591300aedf3259130004ff7159130014fe7159130014fc715913008ebf41591301fcff7059130006fb70591301fe7f50591301fe7d5059130004ff7655130004fe7655130004fd7655130004fc765513000ddc7650d3002edc7650d3000cdc7650d30025df7450d300279f7450d300079f6450d3002ede6450d3002edc6450d3008f9c6450d3008f9e5450d300079d5450d30005df7250d303bf9e4250d3008f9c4250d30005df7150d3008f9f4150d30007db7050d3000dde7050d3000ddc7050d301ffd87050d30026df6050d30027db6050d301ff5f5050d301ffda5050d301ff5d5050d301ff9f4050d301ff9d4050d301ffda1050d3001cfe76d8930086ee62d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d89303b6de43d8930006dd43d8930086ee32d89303b6ed32d8930014fe71d8930004fd71d8930014fc71d89303b6df31d8930024fd70d89303167f50d89303167d50d8930316ef20d8930316fa10d8930005bf745893008dbc7458930086ec62589303adfb7058930004ff7654930004fe7654930004fc76549300067f65549300367c6554930004ff7650930004fe7650930004fc7650930025de735093000ddc764c93001edc764c93000cdc764c9301b6de654c930
  | 10 => 0xd400af9c6350d40005bf7250d4020ebe6250d4020ebc6250d400af9f3250d40005bf7150d40007bb7050d4000dbe7050d4000dbc7050d401ffb87050d4002ebf6050d4002fbb6050d401ff3f5050d401ff3d5050d401ff9f3050d401ffba2050d4001cfe76d89400a6ee62d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89400a6ee52d89400a6ee42d8940416ed42d89400a6ee32d8940014fe71d8940004fd71d8940014fc71d8940416bf41d8940006ee21d89400a6ec21d894002cfd70d894034e7f50d894034e7d50d894034eef20d89400a6ec625894040dfb7058940004ff7654940004fe7654940004fc76549400367e65549400067d6554940006ef625494001eec625494000dbc765094001ebc765094000cbc7650940005bf735094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400a7ac6250940005bf7150940007bb705094000dbe705094000dbc70509401bfb8705094002ebf605094002fbb60509401bf3f50509401bf3d50509401bfaf20509401bfba2050940004ff764c940004fe764c940004fc764c94002dbe744c940005bd744c940026de634c9400079d434c940006ef624c94001eec624c9401afaf424c940014fe76d854009ef661d8540034fe75d8540004fd75d8540034fc75d854015ebf74d854000cfd74d8540014fc74d8540014bc74d8540024fe73d8540004fd73d8540024fc73d8540406bf43d8540006bd43d854001cfe72d8540004fd72d854001cfc72d8540406bf42d8540006bd42d854015ebf41d854009ef641d8540406f541d854002cfd70d854015e7f50d854015e7d50d854015ebe40d854015ebc40d854015efa20d854015ef710d8540005ef72585400a5ec725854009ef461585403fdfb7058540004ff7654540004fe7654540004fc765454013ebe765054000dbc7650540016bc765054000cbc7650540006bf6550540156be6550540006bd6550540156bc6550540005bf7350540006bf635054014ebe635054014ebc6350540005bf7250540006bf6250540146be6250540146bc625054002dbf715054002fb7715054009ebf6150540007b76150540006b76150540016be6150540016bc615054009fb4615054009fb62150540007bb705054000dbe705054000dbc705054013fb8705054002ebf605054002fbb605054013f3f505054013f3d505054013fba205054013fb71050540004ff764c540004fe764c540004fc764c5400057f754c5400b57c754c54002dbe744c540005bd744c540004ff7648540004fe7648540004fc764854002dbe7448540005bd7448540016f66148540007b54148540034fe76d95300967e65d953021cfd75d953002cfe74d9530004fd74d953002cf
  | 11 => 0x13f3f205055013f3e205055013f3c205055013f3f105055013f37105055013f3e105055013f3a105055013f3d105055013f3c10505500057f764c5500067f764c5500047f764c5500057e764c5500057d764c5500057c764c5500067c764c5500047c764c5500057f744c5500d57e744c5500057d744c5500d57c744c5502b57f734c5500cf5e634c5500075d634c5500057f724c5500c57e724c5500c57c724c5500cf5f324c5500075d324c5502ad7f714c5500bf76614c55000775614c5500bf3f414c5500bf3d414c5500cf77314c5500bf5e314c5500bf5c314c5500bf74314c55011d7f704c55000d7e704c55011f7a704c55000d7a704c55000779704c55000d7c704c55011e7f604c5501377b604c55011f5f304c55011f7a304c55011f77104c55011f7a104c5500057f76485500057e76485500057d76485500057c76485500057f74485500d57e74485500057d74485500d57c74485500057f73485500cd7e73485500057d73485500cd7c73485502957f72485500c76e62485500076d62485500c76e32485500076d324855028d7f71485500bf3f41485500bf7641485500bf3d41485500077541485500073541485500c77721485500bf6e21485500bf6c21485500bf7421485500fd7f704855000d7e704855000d7c70485500fe7f60485501177b60485500ff7a30485500ff6f20485500ff7710485500ff7a1048550034fe76d95400b67e65d954023cfd75d954000cff74d954002cfe74d954000cfd74d954002cfc74d954043e7f54d954043e7d54d9540024fe73d9540004fd73d9540024fc73d954043ebf43d954001cfe72d9540004fd72d954001cfc72d9540014fe71d9540004fd71d9540014fc71d954043ebf41d954002cff70d954002cfd70d95404367f50d95404367d50d9540034ff76595400b67c655954042dbf74595400f5fb7059540434ff75595400067f755954042cff7459540006bf74595400d67e54595400d67c5459540004ff7359540024fe7359540024fc73595400d6bf4359540004ff725954001cfe725954001cfc72595400b67f5259540004ff7159540014fe7159540014fc71595400d6bf415954023cff7059540006fb705954023e7f505954023e7d5059540024fe76d8d400aede63d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d400aede43d8d40426dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40014fe71d8d40004fd71d8d40014fc71d8d40426bf41d8d4002cfd70d8d403c67f50d8d403c67d50d8d403c6df30d8d400aedc6358d4041dfb7058d40004ff7654d40004fe7654d40004fc7654d4000dbc7650d40026bc7650d4000cbc7650d40006bf6550d40006bd6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc635
  | 12 => 0xe74585500d57c74585500057f73585500075f73585500055f73585500cd7e73585500cd7c73585500075c73585500cd5c73585500067f63585500067d63585500057f72585500c57e72585500c57c72585500067f62585500067d62585502e57f71585500077761585500be7e61585500be7c61585500bf7461585500bf76315855017d7f70585500077b70585500057b70585500577b605855017f7a305855017f7a10585500d73f76d05500d73e76d05500d73d76d05500d73c76d05500d73f73d05500d73e73d05500d73d73d05500d73c73d05500073f63d055045f3e63d05500073d63d055045f3c63d05500d73f72d05500d73e72d05500d73d72d05500d73c72d05500073f62d05504573e62d05500073d62d05504573c62d055045f3f32d05504573e32d05500073d32d05504573c32d055013d3d71d05500bf3f61d05500bf3e61d05500bf3d61d05500bf3c61d05500bf3f31d05500bf3e31d05500bf3c31d05500bf3f21d05500bf3e21d05500bf3c21d055015f3f70d055015f3e70d055015f3d70d055015f3c70d055015f3f60d055015e3f60d05501773b60d055015f3f30d055015f3e30d055015f3a30d055015f3c30d055015f3f20d055015f3e20d055015f3c20d055015f3f10d055015f3e10d055015f3a10d055015f3d10d055015f3c10d05500057f76505500057e76505500057d76505500057c76505502cd7f74505500073f64505500d73e64505500073d64505500d73c64505500057f73505500cd7e73505500cd7c73505500d73f435055044f3e43505500073d43505500d73c43505500057f72505500c57e72505500c57c72505500d73f42505504473e42505500073d42505500d73c425055015d7f71505500d77741505500bf3e41505500bf3c41505500bf7441505500bf76215055013d7f705055000d7e705055000d7c705055013e7f60505501577b605055013f3f405055013f3e405055013f3c405055013f7a305055013f77105055013f7a10505500073f76505500073e76505500073d76505500073c76505500073f735055044f3e73505500073d735055044f3c73505500073f635055044f3e63505500073d635055044f3c63505500073f72505504473e72505500073d72505504473c72505500073f62505504473e62505500073d62505504473c625055044f3f32505504473e32505500073d32505504473c32505500bf3f715055015d3f71505500d73771505500bf3f61505500bf3e61505500bf3d61505500bf3c61505500bf3f31505500bf3e31505500bf3c31505500bf3f21505500bf3e21505500bf3621505500bf3c215055013f3f705055013f3e705055013f3d705055013f3c705055013f3f605055013e3f60505501573b605055013f3f305055013f3e305055013f3a305055013f3c3050550
  | 13 => 0xd5048f3e4250d500d73c4250d500cf5f3250d500057f7150d500bd7e7150d500bd7c7150d500d73f4150d501fd7f7050d5000d7e7050d5000d7c7050d501fe7f6050d502177b6050d501ff3f4050d501ff5f3050d501ff7a3050d501ff7a1050d504857e76d89500d57e74d89500057d74d89500d57c74d89500067f64d89500067d64d89500cd7e73d89500057d73d89500cd7c73d89500067e63d89500067c63d89500c67e62d89500c76e62d89500c67c62d89500bd7e71d89500057d71d89500bd7c71d89500357f70d895000d7e70d89500357d70d895000d7c70d89503667f60d895047f7b60d89503677a30d89503676f20d89503676d20d89503677a10d895036d7f76589500057f74589500073f74589500053f74589500d57e74589500d57c74589500073c74589500d53c74589500067f64589500067d64589500057f73589500cd7e73589500cd7c73589500067e63589500067c63589503657f72589500076f62589500c67e62589500c67c62589500c76c62589500c76e32589500057f71589500bd7e71589500bd7c71589500c76f21589501dd7f70589500077b70589500057b70589500777b60589501df7a30589501df7a10589500057f76509500057e76509500057d76509500057c76509503457f74509500057f73509500cd7e73509500cd7c735095034d7f72509500d76f42509500c73e42509500c73c42509500c76c42509500057f71509500bd7e71509500bd7c71509500d73f41509501bd7f70509500077b70509500057b705095000d7e705095000d7c70509501bf78705095000d7870509501be7f60509501d77b60509501bf3f40509501bf7a30509501bf6f20509501bf7a10509500057f764c9500057e764c9500057d764c9500057c764c9500057f744c9500d57e744c9500057d744c9500d57c744c95031d7f734c9500075f634c9500cf5c634c9500cf5e434c9500075d434c9503157f724c9500c76e624c9500076d624c9504776f424c9500c76c424c9500cf6f324c9500c75e324c9500c75c324c9500c76c324c9500057f714c9500bd7e714c9500bd7c714c9500cf5f314c9500c76f214c95019d7f704c95000d7e704c95000d7c704c95019e7f604c9501b77b604c95019f5f304c95019f7a304c95019f6f204c95019f7a104c95046d7e76d85500d57e74d85500057d74d85500d57c74d85500cd7e73d85500057d73d85500cd7c73d85500067f63d85500067d63d85500c57e72d85500057d72d85500c57c72d85500067f62d85500067d62d85500be7e61d85500bf7661d85500be7c61d85500357f70d85504677b70d855000d7e70d85500357d70d855000d7c70d85502e67f60d85504677b60d85502e77a30d85502e77710d85502e77a10d85502e77510d85502ed7f76585500057f74585500d57
  | 14 => 0x6bf635055014ebe635055014ebc63505501573f535055044f3e53505500073d53505501573c5350550006bf6250550146be6250550146bc62505501573f52505504473e52505500073d52505501573c525055015dbf71505500d7b771505500bebf6150550016be6150550016bc61505500bf3f51505500bf3e51505500bf3d51505500bf3c51505500bfb6215055013ebf6050550157bb505055013f3e505055013f3c505055013fb8505055013fba305055013fb7105055013fba1050550004ff764c550004fe764c550004fc764c5500057f754c5500357e754c5500057d754c5500357c754c550026de634c5500cf5e534c5500075d534c550016f6614c5500bf76514c55000775514c55000dfa704c550004ff7648550004fe7648550004fc76485500057f75485500357e75485500057d75485500357c754855001eee62485500c76e52485500076d5248550007b541485504ad7e76d91500d67e64d91500d73e64d91500d67c64d91500cd7e73d91500057d73d91500cd7c73d91500c57e72d91500057d72d91500c57c72d91500073e42d91500d73c42d91500bd7e71d91500057d71d91500bd7c71d91500d73f41d91500357f70d915000d7e70d91500357d70d915000d7c70d915042e7f60d91504a77b60d915042f3f40d915042f3d40d915042f7a30d915042f7a10d91504357f765915042d7f74591500073f64591500d67e64591500d67c64591500d73c64591500057f73591500cd7e73591500cd7c73591500d73f43591500057f72591500c57e72591500c57c72591500057f71591500bd7e71591500bd7c71591500d73f415915023d7f70591500077b70591500057b70591500b77b605915023f7a305915023f7a105915049d7e76d8d500d57e74d8d500057d74d8d500d57c74d8d500ce7e63d8d500cf5e63d8d500ce7c63d8d500c57e72d8d500057d72d8d500c57c72d8d500cf5f32d8d500bd7e71d8d500057d71d8d500bd7c71d8d500075e31d8d500cf5c31d8d500357f70d8d504977b70d8d5000d7e70d8d500357d70d8d5000d7c70d8d503e67f60d8d504977b60d8d503e75f30d8d503e77a30d8d503e75d30d8d503e77a10d8d503ed7f7658d500057f7458d500d57e7458d500d57c7458d503e57f7358d500075f6358d500ce7e6358d500ce7c6358d500cf5c6358d500ce5c6358d500057f7258d500c57e7258d500c57c7258d500057f7158d500bd7e7158d500bd7c7158d500cf5f3158d5021d7f7058d500077b7058d500057b7058d500977b6058d5021f7a3058d5021f7a1058d500057f7650d500057e7650d500057d7650d500057c7650d503cd7f7450d500d73e6450d500073d6450d503c57f7350d500d75f4350d500cf3e4350d500cf3c4350d500cf5c4350d500057f7250d500c57e7250d500c57c725
  | 15 => 0xf64549500057f73549500cd7e73549500cd7c73549501ee7e63549501ee7c63549500357f72549500376f72549500076f625495001e7e625495001e7c62549500c76c62549500c76e32549500057f71549500bd7e71549500bd7c71549500c76f21549500077b705495000d7e705495000d7c70549501df7870549500367f60549500377b60549501df7a30549501df7a1054950004ff7650950004fe7650950004fc76509500057f75509500357e75509500057d75509500357c7550950005fb705095000df87050950004ff764c950004fe764c950004fc764c9500057f754c9500357e754c9500057d754c9500357c754c950006df634c950026dc634c9501b75f534c9500cf5c534c95001eee624c9500c76e524c9500076d524c950014fe76d85500357e75d855000d7d75d85500bef661d85500bf7651d855000cfd75d85502e67d75d855000c7d75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d8550024fe73d8550004fd73d8550024fc73d85504667f53d85500067d53d855001cfe72d8550004fd72d855001cfc72d85504667f52d85500067d52d85500be7e51d85500bef651d8550466f551d85500be7c51d8550034fd70d85502e6fa30d85502e6f710d8550005df73585500cddc73585500bef461585504b5fb705855000d7c76545500167c765455000c7c76545500057f74545500d57e74545500d57c74545500057f73545500cd7e73545500cd7c73545500067f63545500057f72545500c57e72545500c57c72545500067f62545500357f71545500377771545500077761545500167e61545500167c61545500bf7461545500bf7631545500077b705455000d7e705455000d7c705455017f7870545500367f60545500377b605455017f7a305455017f7a105455002ebf76d05500d6be76d05500d6bd76d055002ebc76d05500d73f75d05500d73e75d05500d73d75d05500d73c75d055015ebf65d0550006bf63d055016ebe63d055016ebc63d05501773f53d055045f3e53d05500073d53d05501773c53d0550006bf62d0550166be62d0550166bc62d05501773f52d05504573e52d05500073d52d05501773c52d055013dbd71d05500bebf61d0550016be61d0550016bc61d05500bf3f51d05500bf3e51d05500bf3d51d05500bf3c51d055015ebf60d0550177bb50d055015f3e50d055015f3c50d055015fb850d055015fba30d055015fba10d0550004ff7650550004fe7650550004fc76505500057f75505500357e75505500057d75505500357c7550550006bf645055002ebe645055002ebc64505501573f54505500d73e54505500073d54505500d73c5450550006bf7650550006be7650550006bd7650550006bc76505500073f75505501573e75505500073d75505501573c755055013ebf6550550
  | 16 => 0x87500fe7d60487500ff6f20487500ff77104875002cfe76d91500357e75d915000d7d75d91500d6be64d91500d73e54d915000cfd75d915042e7d75d915000c7d75d915002cfc75d91500d67e54d91500d6be54d91504a6bd54d91500d67c54d9150024fe73d9150004fd73d9150024fc73d915001cfe72d9150004fd72d915001cfc72d91504a67f52d9150006be42d91500d6bc42d9150014fe71d9150004fd71d9150014fc71d91500d6bf41d9150034fd70d915042ebf40d91500d6bc64591504cdfb705915000d7c765515002e7c765515000c7c76551500357f74551500373f74551500073f645515002e7e645515002e7c64551500d73c64551500057f73551500cd7e73551500cd7c73551500d73f43551500057f72551500c57e72551500c57c72551500057f71551500bd7e71551500bd7c71551500d73f41551500077b705515000d7e705515000d7c705515023f7870551500367f60551500377b605515023f7a305515023f7a1055150024fe76d8d500357e75d8d5000d7d75d8d500cede63d8d500cf5e53d8d5000cfd75d8d503e67d75d8d5000c7d75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500ce7e53d8d500cede53d8d50496dd53d8d500ce7c53d8d5001cfe72d8d50004fd72d8d5001cfc72d8d500cedf32d8d50014fe71d8d50004fd71d8d50014fc71d8d504967f51d8d50006de31d8d500cedc31d8d50034fd70d8d503e6df30d8d503e6fa10d8d500cedc6358d504c5fb7058d5000d7c7654d500267c7654d5000c7c7654d500057f7454d500d57e7454d500d57c7454d500357f7354d500375f7354d500075f6354d500267e6354d500267c6354d500cf5c6354d500265c6354d500057f7254d500c57e7254d500c57c7254d500057f7154d500bd7e7154d500bd7c7154d500cf5f3154d500077b7054d5000d7e7054d5000d7c7054d5021f787054d500367f6054d500377b6054d5021f7a3054d5021f7a1054d50004ff7650d50004fe7650d50004fc7650d500057f7550d500357e7550d500057d7550d500357c7550d5002ebe6450d500d73e5450d500073d5450d5001cfe76d89500357e75d895000d7d75d89500c6ee62d89500c76e52d895000cfd75d89503667d75d895000c7d75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d895047e7f54d89500067d54d8950024fe73d8950004fd73d8950024fc73d89500067e53d895047e7c53d89500c67e52d89500c6ee52d895047eed52d89500c67c52d8950014fe71d8950004fd71d8950014fc71d895047e7f51d8950034fd70d8950366ef20d8950366fa10d8950005bf74589500d5bc74589500c6ec62589504bdfb705895000d7c765495001e7c765495000c7c76549500057f74549500d57e74549500d57c74549500067
  | 17 => 0xdf3f21d07500df3e21d07500df3c21d075015f3f70d075015f3e70d075015f3d70d075015f3c70d075015f3f30d075015f3e30d075015f3c30d075015f3f20d075015f3e20d075015f3c20d075015f3f10d075015f3e10d075015f3d10d075015f3c10d07501557f76507500357e76507501557d76507500357c76507502cd7f74507501573f64507500f73e64507501573d64507500f73c64507500057f73507500ed7e73507500ed7c73507500f73f43507504df3e43507500073d43507500f73c43507500057f72507500e57e72507500e57c72507500f73f42507504d73e42507500073d42507500f73c425075015d7f71507500f77741507500df3e41507500df3c41507500df7441507500df76215075013d7f705075000d7e705075000d7c705075013e7d605075013f3f405075013f3e405075013f3c405075013f7710507501573f76507501573e76507501573d76507501573c76507500073f73507504df3e73507500073d73507504df3c73507501573f63507501573e63507501573d63507501573c63507500073f72507504d73e72507500073d72507504d73c72507501573f62507501573e62507501573d62507501573c62507504df3f32507504d73e32507500073d32507504d73c32507500df3f71507500f73771507500df3f61507500df3e61507500df3d61507500df3c61507500df3f31507500df3e31507500df3c31507500df3f21507500df3e21507500df3621507500df3c215075013f3f705075013f3e705075013f3d705075013f3c705075013f3f305075013f3e305075013f3c305075013f3f205075013f3e205075013f3c205075013f3f105075013f37105075013f3e105075013f3d105075013f3c10507501357f764c7500067f764c7500047f764c7500357e764c7501357d764c7500357c764c7501367c764c7500347c764c7500057f744c7500f57e744c7500057d744c7500f57c744c7502b57f734c7500ef5e634c7501375d634c7500057f724c7500e57e724c7500e57c724c7500ef5f324c7500075d324c7502ad7f714c7500df76614c75013775614c7500df3f414c7500df3d414c7500ef77314c7500df5e314c7500df5c314c7500df74314c75011d7f704c75000d7e704c75000d7c704c75011e7d604c75011f5f304c75011f77104c7501157f76487500357e76487501157d76487500357c76487500057f74487500f57e74487500057d74487500f57c74487500057f73487500ed7e73487500057d73487500ed7c73487502957f72487500e76e62487501176d62487500e76e32487500076d324875028d7f71487500df3f41487500df7641487500df3d41487500077541487500073541487500e77721487500df6e21487500df6c21487500df7421487500fd7f704875000d7e704875000d7c704
  | 18 => 0x65250521147a65250521147b55250521007a55250521147b45250521147b73250521147b63250521147a63250521147b53250521007a53250521147b43250521007b77050521507b67050521007b57050521507b47050521507b66050521507b46050521517b75050521507b65050521507b4505052150fb73050521507b63050521507b43050521147b72050521147a72050521147b62050521147b4205052100cfe76d8121007b541d81210fefa60d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d81212feee32d8121006ed32d812101cfd71d812100cfc71d812129ebf41d812129ef641d812129ebd41d8121006f541d8121006b541d81210fefa20d81210fefa10d8121005bf745812110dbc7458121007b541581210fef860581212157f7650f500357e7650f502157d7650f500357c7650f503cd7f7450f500f73e6450f502173d6450f503c57f7350f500f75f4350f500ef3e4350f500ef3c4350f500ef5c4350f500057f7250f500e57e7250f500e57c7250f504ff3e4250f500f73c4250f500ef5f3250f500057f7150f500dd7e7150f500dd7c7150f500f73f4150f501fd7f7050f5000d7e7050f5000d7c7050f501fe7d6050f501ff3f4050f501ff5f3050f501d57f7650b500357e7650b501d57d7650b500357c7650b503457f7450b500057f7350b500ed7e7350b500ed7c7350b5034d7f7250b500f76f4250b500e73e4250b500e73c4250b500e76c4250b500057f7150b500dd7e7150b500dd7c7150b500f73f4150b501bd7f7050b5000d7e7050b5000d7c7050b501be7d6050b501bf3f4050b501bf6f2050b501b57f764cb500357e764cb501b57d764cb500357c764cb500057f744cb500f57e744cb500057d744cb500f57c744cb5031d7f734cb501b75f634cb500ef5c634cb500ef5e434cb500075d434cb503157f724cb500e76e624cb501b76d624cb504f76f424cb500e76c424cb500ef6f324cb500e75e324cb500e75c324cb500e76c324cb500057f714cb500dd7e714cb500dd7c714cb500ef5f314cb500e76f214cb5019d7f704cb5000d7e704cb5000d7c704cb5019e7d604cb5019f5f304cb5019f6f204cb500f73f76d07500f73e76d07500f73d76d07500f73c76d07500f73f73d07500f73e73d07500f73d73d07500f73c73d07501773f63d07501773e63d07501773d63d07501773c63d07500f73f72d07500f73e72d07500f73d72d07500f73c72d07501773f62d07501773e62d07501773d62d07501773c62d07504ef3f32d07504e73e32d07500073d32d07504e73c32d07500df3f61d07500df3e61d07500df3d61d07500df3c61d07500df3f31d07500df3e31d07500df3c31d0750
  | 19 => 0x8d2153df77158d21004ff7558d210067f7558d210047f7558d21034fe7558d21034fc7558d210067c7558d210347c7558d21004ff7458d2102cfe7458d2102cfc7458d21534ff7358d21006df7358d2152cff7258d21006ef7258d21126ee5258d211a4ff7158d21006f77158d211a6bf4158d211a6bd4158d21004ff7058d2100cfe7058d2100cfc7058d21106df3058d21126ef2058d211a6f71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d2101dee7254d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2102ebc6450d21015ec7654921036ec7654921014ec765492101def755492101f6f75549210076f6554921036ee6554921036ec65549211176c65549211176f54549210076d5454921005ef7354921006ef6354921006ed63549215276e53549211176c5354921007e77154921015ee7154921015ec71549211e7e4715492101eef615492101fe761549211e76f51549211e76d51549211e7af41549211e7e641549211e7ad4154921005ef70549211176f50549211e7e71054921015ec764c921026ec764c921014ec764c921005ef754c921005ed754c921006ef654c921006ed654c9211aeee644c9211aeec644c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c921107cc634c92151fcf534c921107cc534c921107ce434c921007cd434c921007e7714c921015ee714c921015ec714c9211a7e4714c92101eef614c92101fe7614c9211a7af414c9211a7e6414c9211a7ad414c9211a7cf314c9211a7cd314c921005ef704c921107cf304c9211a7e7104c92101df4765052102ef4765052101cf47650521015f77450521017b77450521007b7645052102ef6645052102ef4645052110fb46450521517b7545052110fb65450521007b5545052110fb4545052110fb7435052150fb64350521007b5435052110fb44350521007e7725052101df6725052101df47250521147e47250521016f76250521017e76250521147e65250521007e55250521147b74250521147b64250521147b54250521147b44250521147e63250521007e53250521005f7705052110fb74050521507b6405052110fb44050521147e7205052110fb7765052102eb77650521147b4765052102eb47650521007b77550521517b67550521007b57550521517b47550521007b76550521517b66550521007b56550521517b46550521007b7735052150fb67350521007b5735052150fb47350521007b7635052150fb66350521007b5635052150fb46350521517b7535052150fb65350521007b5535052150fb45350521147b77250521007a77250521147b67250521147b57250521147b47250521147a47250521017b76250521016b76250521017a76250521147b75250521147b
  | 20 => 0x755535453113777525453100775525453118fd73254531007d53254531005f7705453113777505453118fd7305453100cfe76d81310067f65d81310067c65d813111efa60d81310067f75d8131034fe75d8131004fd75d8131034fc75d81310067c75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d8131396df32d8131006dd32d8131024fd71d81312bebf41d81312bebd41d813111efa30d813111efa10d81310057f75581311357c75581310067f65581310067c655813111ef86058131034fe76d95211167e65d95211e4fd75d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521004fd73d9521024fc73d95210067e53d95211167c53d9521014ff72d9521014fd72d952157e7f52d952157e7d52d952157eee32d952101cff71d952101cfd71d952156e7f51d952156e7d51d952156ebf41d952156ebd41d952100cfe70d9521004fd70d952100cfc70d95211167f50d9521034ff76595211167c6559521565ef7259521575f7715952156cff75595210067f7559521004ff745952102cfe745952102cfc7459521004ff7359521024fe7359521024fc7359521564ff7259521006ef7259521186ee32595211e4ff7159521006f771595211e6bf41595211e6bd4159521004ff705952100cfe705952100cfc70595211167f505952102cfe76d912110ebe64d9121034fe75d9121004fd75d9121034fc75d91211c4fd74d9121024fe73d9121004fd73d9121024fc73d912110ebf43d9121014ff72d9121014fd72d912155ebf42d912155ebd42d912101cff71d912101cfd71d9121556bf41d9121556bd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d912110ebc40d912155eef20d9121556f710d912102cff765912110ebc645912154def7259121165f77159121004ff7559121034fe7559121034fc7559121554ff7459121006bf7459121004ff7359121024fe7359121024fc735912154cff7259121006ef7259121146be4259121146bc42591211c4ff7159121006f771591211c6bf41591211c6bd4159121004ff705912100cfe705912100cfc705912110ebf4059121146ef20591211c6f71059121004ff7655121004fe7655121004fd7655121004fc7655121024fe76d8d21106de63d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d211a4fd73d8d21014ff72d8d21014fd72d8d21546ee52d8d21546df32d8d21546dd32d8d2101cff71d8d2101cfd71d8d21536bf41d8d21536bd41d8d21536df31d8d21536dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21546ef20d8d21536f710d8d21024ff7658d210057f7558d211157c7558d21106dc6358d2152def725
  | 21 => 0xf75591311357c75591310067f65591310067c655913112ebc645913159ddf735913116df77159131004ff75591310067f75591310047f7559131034fe7559131034fc75591310067c75591310347c75591315a4ff7459131006bf745913112ebe545913159cff7359131006df735913114ebe435913114ebc4359131004ff725913101cfe725913101cfc7259131006be425913112ebc425913114edf3259131204ff7159131006f77159131206bf4159131206bd4159131004ff705913100cfe705913100cfc705913112ebf405913114edf3059131206f71059131004ff7655131004fe7655131004fd7655131004fc76551310067f65551310367c655513102ebe6455131006bd6455131015dc7654d31036dc7654d31014dc7654d31025df7554d310275f7554d310075f6554d31036de6554d31036dc6554d311375c6554d31005df7254d31007d77154d31015de7154d31015dc7154d31227d47154d31026df6154d31027d76154d312275f5154d31227d65154d312275d5154d312279f4154d312279d4154d31005df7054d311375f5054d31227d71054d3101cfe76d89310067f65d89310067c65d893112dbe74d8931005bd74d8931126ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931006be74d893102cbe74d8931004fd74d8931006bd74d8931004bd74d893102cfc74d8931014fd73d8931126ee32d8931596ed32d8931024fd71d893152ebf41d893152ebd41d893152eef21d893100cfe70d8931004fd70d893100cfc70d8931596df30d893152ef710d89310057f75589311357c75589310067f65589310067c6558931126ec625893158df77158931004ff7654931004fe7654931004fc76549310067f65549310367c6554931025de73549311ef5e535493101eee6254931004ff7650931004fe7650931004fc76509310067f65509311d67c6550931015dc764c93101edc764c931014dc764c931005df754c931005dd754c9310075f654c9311b6de654c9311b6dc654c9310075c654c9311b65c654c931006df644c931006dd644c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c931127cc624c931127ce524c931007cd524c931587cf424c931127cc424c931007d7714c931015de714c931015dc714c9311a7d4714c931015d4714c931026df614c931027d7614c9311a7d6514c9311a79f414c9311a79d414c9311a7cf214c931005df704c931127cf204c9311a7d7104c931025f47654531036f47654531024f47654531015f77554531017777554531007776554531036f66554531036f46554531137746554531007d77354531025f67354531025f4735453118fd47354531016f76354531017d7635453118f77535453118fd6535453118f755354531137d55354531
  | 22 => 0x95315c67d51d95315c6bf41d95315c6bd41d953100cfe70d9531004fd70d953100cfc70d95311367f50d95310067e50d95311367c50d95315b57e76d95310347e76d95310067e64d95310067c64d95315c75f73d95315c75c73d95310067e62d95310067c62d95315df5f32d95315df7771d95315c77471d95315c73f41d95315c73d41d95315df7731d95315c75e31d95315c75c31d95315c77431d95310057d70d95310067e60d95310067c60d95315df5f30d95315c77710d95310067f74d95310067e74d95310067d74d95310067c74d95315c67f73d95315de7e73d95315c67d73d95315c67c73d95315de7f43d95315de7e43d95315de7d43d95315de7c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067c42d95315de7f32d95315de7e32d95315de7d32d95315de7c32d95315c67f71d95315c67e71d95315c67d71d95315c67c71d95315c67f41d95315c63f41d95315c67e41d95315c67d41d95315c63d41d95315c67c41d95315c67f31d95315c67e31d95315c67c31d95315c67f21d95315c67e21d95315c67d21d95315c67c21d95310067f70d95310067e70d95310067d70d95310047d70d95310067c70d95310067f40d95310067e40d95310067c40d95315de7f30d95315de7e30d95315de7d30d95315de7c30d95310067f20d95310067e20d95310067c20d95315c67f10d95315c67e10d95315c67d10d95315c67c10d9531034ff76595311367c65595315cddf73595315d5f771595315c4ff75595310067f7559531004ff745953102cfe745953102cfc74595315ccff7359531006df7359531004ff725953101cfe725953101cfc7259531224ff7159531006f77159531226bf4159531226bd4159531004ff705953100cfe705953100cfc70595311367f50595315c57e76195311367e76195315c47e76195311373e74195311373d74195310067e64195310067c64195315bf5e73195315b75d73195315b67f63195311376e72195311376d72195310067e62195310067c62195315bf5f32195315b77671195315bf7571195315b67f61195315b73f41195315b73d41195315bf7731195315b75e31195315b75c31195315b77431195311377a70195310057d70195311377970195310057970195310067e60195310067c60195315bf5f30195315b777101953102cfe76d91310067f65d91310067c65d913112ebe64d9131034fe75d9131004fd75d9131034fc75d9131204fd74d9131014ff73d9131014fd73d91315aebf43d91315aebd43d913101cfe72d9131004fd72d913101cfc72d91315aedf32d9131024ff71d9131024fd71d91315a6bf41d91315a6bd41d913100cfe70d9131004fd70d913100cfc70d91315aedf30d91315a6f710d913102cff76591310057
  | 23 => 0x7ae20d8941147ac20d894154fb710d8941555bf7658941005bf7558941155be7558941155bc7558941005bf735894114dbe735894114dbc735894154dbf7258941007af6258941146be6258941146bc6258941147ac6258941146ac62589411c5bf7158941007b77158941005b7715894110fb761589411c7b62158941005bf705894113dbe705894113dbc7058941147af20589411c7b71058941005bf7654941005be7654941005bd7654941005bc765494156dbf75549411573e65549410073d6554941005bf735494114dbe735494114dbc73549415ef3e53549411573c5354941565bf7254941157af52549411473e52549411473c5254941147ac5254941147ae32549411e5bf7154941015be7154941015bc71549411e6bf61549411f7b761549411e73f51549411e73d51549411e7af21549411e7b62154941005bf705494113dbe705494113dbc70549411573f50549411e7b71054941005bf764c941005be764c941005bd764c941005bc764c941005bf754c941155be754c941005bd754c941155bc754c941535bf734c94114f9e634c9410079d634c9415e79f534c94114f9c534c94152dbf724c941007af624c941147ac624c941147ae524c941007ad524c94114faf324c9411479e324c9411479c324c941147ac324c9411a5bf714c941015be714c941015bc714c9411a6bf614c9411afb7614c9411a79f314c9411a7af214c9411a7b6214c941005bf704c94113dbe704c94113dbc704c94114f9f304c941147af204c9411a7b7104c94113dbe76d8141155be75d8141005bd75d8141155bc75d814114dbe73d8141005bd73d814114dbc73d8141006bf63d8141006bd63d8141145be72d8141005bd72d8141145bc72d8141006bf62d8141006bd62d814102dbf71d81413ffb771d8141015be71d814102dbd71d8141015bc71d81412d6bf61d81413ffb761d81412d7b621d814113ebe60d814113fba60d814113ebc60d814113fb710d814113fba10d81412d7b910d8141005bf7558141155be7558141155bc7558141005bf735814114dbe735814114dbc7358141006bf6358141006bd6358141005bf7258141007af7258141005af7258141145be7258141145bc7258141007ac7258141145ac7258141006bf6258141006bd6258141007b7715814104fb7615814109fb6215814113dbf7058141007bb605814113ebe605814113ebc605814113fb8605814113fba205814113fb71058141034fe76d95311367e65d9531224fd75d953102cfe74d9531004fd74d953102cfc74d95311367f54d95310067e54d95311367c54d9531014ff73d9531014fd73d95315de7f53d95315de7d53d953101cfe72d9531004fd72d953101cfc72d95311367f52d95310067e52d95311367c52d9531024ff71d9531024fd71d95315c67f51d
  | 24 => 0xe40d814113efa40d814113ebc40d814113efa10d8141005ef7258141145ec725814113ef8605814162dbe76d9541245bd75d9541156be65d95411573e65d9541156bc65d954114dbe73d9541005bd73d954114dbc73d95410073e53d95411573c53d9541145be72d9541005bd72d9541145bc72d954102dbf71d9541015be71d954102dbd71d9541015bc71d9541616bf61d9541627b761d95416173f51d95416173d51d9541617b621d954113dbe70d9541005bd70d954113dbc70d95411573f50d9541617b710d954161dbf7659541615bf75595410073f6559541156be6559541156bc65595411573c6559541005bf735954114dbe735954114dbc7359541005bf7259541145be7259541145bc72595411573f5259541245bf7159541007b77159541005b77159541246bf6159541197b76159541247b62159541005bf705954113dbe705954113dbc70595411573f5059541247b7105954160dbe76d8d41155be75d8d41005bd75d8d41155bc75d8d41006bf65d8d41006bd65d8d4114ebe63d8d4114f9e63d8d4114ebc63d8d41145be72d8d41005bd72d8d41145bc72d8d41006be62d8d41006bc62d8d4102dbf71d8d41015be71d8d4102dbd71d8d41015bc71d8d4159ebf61d8d41607b761d8d4159f9f31d8d4159f9d31d8d4159fb621d8d4113dbe70d8d41005bd70d8d4113dbc70d8d4159fb710d8d415a5bf7658d41005bf7558d410073f7558d410053f7558d41155be7558d41155bc7558d410073c7558d411553c7558d41006bf6558d41006bd6558d4159dbf7358d410079f6358d4114ebe6358d4114ebc6358d4114f9c6358d41005bf7258d41145be7258d41145bc7258d41006be6258d41006bc6258d4114f9f3258d41205bf7158d41007b77158d41005b77158d4112fb76158d41207b62158d41005bf7058d4113dbe7058d4113dbc7058d4114f9f3058d41207b71058d41005bf7654d41005be7654d41005bd7654d41005bc7654d415c5bf7554d415cdbf7354d411579f5354d4114f3e5354d4114f3c5354d4114f9c5354d41005bf7254d41145be7254d41145bc7254d41225bf7154d41007b77154d41005b77154d41015be7154d41015bc7154d41227b47154d41015b47154d41226bf6154d41237b76154d412273f5154d412273d5154d412279f3154d41227b62154d41005bf7054d4113dbe7054d4113dbc7054d411573f5054d41227b71054d415fdbe76d8941155be75d8941005bd75d8941155bc75d894114dbe73d8941005bd73d894114dbc73d8941146be62d8941147ae62d8941146bc62d8941147ae32d894102dbf71d89415f7b771d8941015be71d894102dbd71d8941015bc71d894154ebf61d89415f7b761d894154faf21d894154fb621d894154fad21d894113dbe70d8941005bd70d894113dbc70d8941
  | 25 => 0x8d41606be54d8d41006bd54d8d4114ebe43d8d4114ede43d8d41606dd43d8d4114ebc43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d41006be42d8d41606bc42d8d4102cfd71d8d4159edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41606bf40d8d4159ef710d8d410057f7558d411557c7558d4114edc6358d4163df77158d41004ff7654d41004fe7654d41004fc7654d41005bf7454d4102dbe7454d4102dbc7454d41005f77154d41015f47154d41015bc7650d41026bc7650d41014bc7650d41005bf7550d41155be7550d41005bd7550d41155bc7550d41006bf6550d41006bd6550d4102dbf7350d4102f9f7350d410079f6350d41026be6350d41026bc6350d4114f9c6350d41005bf7250d41145be7250d41145bc7250d4120ebe6250d4120ebc6250d4114f9f3250d41007b77150d41015be7150d41015bc7150d41207b47150d4102ebf6150d4102fb76150d41207b62150d41005bf7050d4113dbe7050d4113dbc7050d4114f9f3050d41207b71050d4101cfe76d894102dbe74d8941015bd74d8941146ee62d8941147ae42d8941034fe75d8941004fd75d8941034fc75d8941014fd74d894154ebd74d8941014bd74d8941024fe73d8941004fd73d8941024fc73d8941146be42d8941146ee42d89415f6ed42d8941146bc42d8941146ee32d894102cfd71d894154eef21d894100cfe70d8941004fd70d894100cfc70d89415f6bf40d8941006ee20d8941146ec20d894154ef710d8941146ec6258941635f77158941004ff7654941004fe7654941004fc76549410367e65549410067d6554941005bf745494102dbe745494102dbc74549411573f54549410073d5454941015bc765094101ebc7650941014bc7650941005bf7550941155be7550941005bd7550941155bc7550941005bf735094114dbe735094114dbc735094102dbf725094102faf7250941007af625094101ebe625094101ebc6250941147ac625094101eac6250941007b77150941015be7150941015bc71509411c7b4715094102ebf615094102fb761509411c7b62150941005bf705094113dbe705094113dbc7050941147af20509411c7b71050941004ff764c941004fe764c941004fc764c941005bf744c94102dbe744c941005bd744c94102dbc744c941026de634c94114f9e434c9410079d434c941006ef624c94101eec624c9411afaf424c941147ac424c94100cfe76d814102dbe74d8141015bd74d814113efa60d814113fba40d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814113ebd74d8141014bd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d81413febf43d8141006bd43d814101cfe72d8141004fd72d814101cfc72d81413febf42d8141006bd42d814102cfd71d81412d6f621d814113eb
  | 26 => 0x16f9c5354f41005bf7254f41165be7254f41165bc7254f41225bf7154f41015be7154f41015bc7154f41226bd6154f412273f5154f412273d5154f412279f3154f41005bf7054f4115dbe7054f4115dbc7054f411773f5054f411f5bf7654b4102dbe7654b411f5bd7654b4102dbc7654b4156dbf7554b411f73e6554b411f73d6554b41005bf7354b4116dbe7354b4116dbc7354b416573e5354b411773c5354b41565bf7254b41177af5254b411673e5254b411673c5254b41167ac5254b41167ae3254b411e5bf7154b41015be7154b41015bc7154b411e6bd6154b411e73f5154b411e73d5154b411e7af2154b41005bf7054b4115dbe7054b4115dbc7054b411773f5054b411adbf764cb4102dbe764cb411adbd764cb4102dbc764cb41005bf754cb41175be754cb41005bd754cb41175bc754cb41535bf734cb4116f9e634cb411af9d634cb4164f9f534cb4116f9c534cb4152dbf724cb411afaf624cb41167ac624cb41167ae524cb41007ad524cb4116faf324cb411679e324cb411679c324cb41167ac324cb411a5bf714cb41015be714cb41015bc714cb411a6bd614cb411a79f314cb411a7af214cb41005bf704cb4115dbe704cb4115dbc704cb4116f9f304cb41167af204cb41034fe76d95411567e65d954102dbe74d9541015bd74d95411573f54d9541244fd75d9541014ff74d9541014fd74d9541616bd74d9541014bd74d95416267f54d9541156bf54d95416267d54d9541626bc54d9541024fe73d9541004fd73d9541024fc73d95410067e53d95411567c53d9541626bf43d954101cfe72d9541004fd72d954101cfc72d954102cff71d954102cfd71d95416167f51d95416167d51d954100cfe70d9541004fd70d954100cfc70d95411567f50d9541034ff76595411567c655954161dbf7459541645f77159541614ff75595410067f755954161cff7459541006bf7459541156bf5459541196bc5459541004ff7359541024fe7359541024fc7359541196bf4359541004ff725954101cfe725954101cfc72595411567f5259541244ff7159541006f77159541004ff705954100cfe705954100cfc70595411567f5059541015bc7655141036bc7655141014bc765514102dbf755514102f3f75551410073f6555141036be6555141036bc65551411573c6555141005bf735514114dbe735514114dbc7355141005bf7255141145be7255141145bc72551411573f5255141007b77155141015be7155141015bc7155141247b4715514102ebf615514102fb76155141247b62155141005bf705514113dbe705514113dbc70551411573f5055141247b71055141024fe76d8d4102dbe74d8d41015bd74d8d4114ede63d8d4114f9e43d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4159ebd74d8d41014bd74d
  | 27 => 0xa20d8132005bf74581321adbc745813219ef8605813202cfe76d9151196be64d9151014fd75d9151196be54d915167ebd54d9151024fe73d9151004fd73d9151024fc73d915101cfe72d9151004fd72d915101cfc72d915167e7f52d9151034fd71d915161ebf41d915100cfe70d9151004fd70d915100cfc70d915167e7f50d9151196bc6459151175f77159151024fe76d8d5118ede63d8d51014fd75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5118ede53d8d51676dd53d8d5118ede43d8d5101cfe72d8d51004fd72d8d5101cfc72d8d5118edf32d8d51034fd71d8d515cebf41d8d515cebd41d8d515cedf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d516767f50d8d51006de30d8d5118edc30d8d5118edc6358d5166df77158d510157c7654d510267c7654d510147c7654d510357f7354d510375f7354d510075f6354d510267e6354d510267c6354d5118f5c6354d510057f7254d51007777154d510157e7154d510157c7154d51227747154d510367f6154d51037776154d512275f3154d51227763154d510057f7054d51004ff7650d51004fe7650d51004fc7650d5102ebe6450d51006df6350d51026dc6350d5101cfe76d8951186ee62d8951014fd75d895102cfe74d8951004fd74d895102cfc74d8951024fe73d8951004fd73d8951024fc73d8951186ee52d8951666ed52d8951034fd71d8951566bf41d8951566bd41d8951566ef21d895100cfe70d8951004fd70d895100cfc70d89516667f50d8951186ec625895165df771589510157c765495101e7c76549510147c76549510067f64549510057f73549511ee7e63549511ee7c63549510357f72549510376f72549510076f625495101e7e625495101e7c62549511876c62549511876e32549510077771549510157e71549510157c71549511e77471549510367f61549510377761549511e77631549511e76f21549510057f7054951004ff7650951004fe7650951004fc7650951004ff764c951004fe764c951004fc764c9510357e754c9510057d754c951006df634c951026dc634c9511b75f534c95101eee624c9510076d524c95100cfe76d815117efa60d81510de7f75d8151014fd75d815100cfc75d815100c7c75d815102cfe74d8151004fd74d815102cfc74d8151024fe73d8151004fd73d8151024fc73d81514b67f53d81510067d53d815101cfe72d8151004fd72d815101cfc72d81514b67f52d81510067d52d8151034fd71d81510de7e51d81510de7c51d81510debf41d81510debd41d81510def631d815117e7f50d815117efa50d815117efa10d8151005df735815118ddc735815117ef86058151235bf7654f4102dbe7654f41235bd7654f4102dbc7654f415c5bf7554f415cdbf7354f411779f5354f4116f3e5354f4116f3c5354f41
  | 28 => 0x91321aebe64d913201dee72d9132025ed72d91321afaf42d9132034fe75d9132004fd75d9132034fc75d913220cfd74d913201cff73d913201cfd73d913269ebf43d913269ebd43d9132024ff72d9132024fd72d913269eed72d9132024ed72d913268ebf42d91321aeef42d913268ebd42d913268eec42d9132014fe71d9132004fd71d9132014fc71d91321aebf41d913200cfe70d9132004fd70d913200cfc70d9132006be40d91321aebc40d913269edf30d913268eef20d913202cff76591321aebc6459132685df7359132695ef725913220fac4259132004ff7559132034fe7559132034fc755913268cff7459132006bf7459132684ff7359132006df735913220cff7259132006ef72591321aeef425913220ebe425913220ebc425913220eec4259132004ff7159132014fe7159132014fc71591321aebf4159132004ff705913200cfe705913200cfc70591321aebf40591321cedf305913220eef2059132004ff7655132004fe7655132004fd7655132004fc7655132005df7355132025dc7355132005ef725513201dec725513201ddc7650d3202edc7650d3201cdc7650d321b5de7550d321b5dc7550d32025df7450d320279f7450d320079f6450d3202ede6450d3202edc6450d321af9c6450d321af9e5450d320079d5450d32007cf7250d3201dde7250d3201ddc7250d3220fcc7250d32026df6250d32027cf6250d3220fce5250d321afcf4250d3220f9e4250d3220f9c4250d3220fcc4250d3220f8c4250d32005df7150d321af9f4150d3220fcf2150d32005df7050d321af9f4050d3220fcf2050d32025ec7654932036ec7654932024ec765493201def755493201f6f75549320076f6554932036ee6554932036ec65549321b76c65549321adee74549321adec74549321b76f54549320076d5454932007cf7354932025ee7354932025ec73549321efcc735493201eef635493201fcf63549321b7cf53549321ef6e53549321ef6c53549321efcc53549321ef4c53549321efce4354932007cd4354932005ef71549321b76f51549321efcf3154932005ef70549321b76f50549321efcf3054932014fe76d85321a6f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532024fd72d853253eee52d8532006ed52d85321a6f631d85321a6f621d853200cfe70d8532004fd70d853200cfc70d853258edf30d853253eef20d85320057f75585321b57c75585321a6f4615853200cfe76d813219efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d81323aede43d8132006dd43d8132024fd72d8132014fe71d8132004fd71d8132014fc71d81323aedf31d8132326ef21d813219efa30d813219ef
  | 29 => 0x1d67e65d954224cfd75d954201cff74d954201cfd74d95426ee7f54d95426ee7d54d9542024fe73d9542004fd73d9542024fc73d954202cff72d954202cfd72d95426de7f52d95426de7d52d9542014fe71d9542004fd71d9542014fc71d95426eebf41d954200cfe70d9542004fd70d954200cfc70d95421d67f50d9542034ff76595421d67c65595426d5bf74595426e5ef72595426dcff75595420067f75595426d4ff7459542006bf7459542004ff7359542024fe7359542024fc735954224cff7259542006ef7259542004ff7159542014fe7159542014fc71595421f6bf4159542004ff705954200cfe705954200cfc70595421d67f5059542024fe76d8d421cede63d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d421cede43d8d426cedd43d8d4202cfd72d8d426ceef42d8d42686be42d8d42686bc42d8d42686ec42d8d42686df32d8d42014fe71d8d42004fd71d8d42014fc71d8d426cebf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d426cebf40d8d42686ef20d8d421cedc6358d426c5ef7258d42004ff7654d42004fe7654d42004fc7654d42014fe76d85421c6f661d8542034fe75d8542004fd75d8542034fc75d8542166bf74d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d8542166be42d8542166bc42d85421c6bf41d85421c6f641d85421c6f621d854200cfe70d8542004fd70d854200cfc70d8542636bf40d8542166ef20d85421c6f4615854200cfe76d81421befa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d814202cfd72d8142014fe71d8142004fd71d8142014fc71d814240ebf41d81421befa50d81421befa40d81421befa20d81421bef86058142034fe76d95321b67e65d9532025de73d953201ddd73d95321b75f53d953222cfd75d953202cfe74d9532004fd74d953202cfc74d953201cff73d953201cfd73d95326aedd73d953201cdd73d95326be7f53d95321b6df53d95326be7d53d95326bedc53d9532024ff72d9532024fd72d95326ae7f52d95326ae7d52d9532014fe71d9532004fd71d9532014fc71d95320067e51d95321b67c51d95326bedf31d95326aeef21d953200cfe70d9532004fd70d953200cfc70d95321b67f50d9532034ff76595321b67c65595326a5df73595321ef5c53595326b5ef72595326acff75595320067f7559532004ff745953202cfe745953202cfc74595326a4ff7359532006df73595321b6df53595321ee7e53595321ee7c53595321eedc535953222cff7259532006ef7259532004ff7159532014fe7159532014fc71595321b67f51595321eedf315953222eef2159532004ff705953200cfe705953200cfc70595321b67f505953202cfe76d
  | 30 => 0xe54d8543006bd54d854302cfd73d854316ebe43d854316ebc43d854301cfe72d8543004fd72d854301cfc72d8543006be42d854363ebc42d854316edf32d8543206bf41d8543206f641d8543206f631d854300cfe70d8543004fd70d854300cfc70d854363ebf40d854316edf30d85430057f75585432157c7558543206f4615854300cfe76d81431fefa60d8143034fe75d8143004fd75d8143034fc75d8143024fd74d814302cfd73d814301cfe72d8143004fd72d814301cfc72d81433d6df32d8143014fe71d8143004fd71d8143014fc71d814341ebf41d81431fefa40d81431fefa30d81431fef8605814302cfe76d91521f6be64d915201cfd75d91521f6be54d915270ebd54d9152024fe73d9152004fd73d9152024fc73d91521f6bf43d9152034fd72d91526d6bf42d9152014fe71d9152004fd71d9152014fc71d91521f6bf41d915200cfe70d9152004fd70d915200cfc70d915270e7f50d9152006be40d91521f6bc40d91521f6bc6459152705ef725915201d7c765515202e7c765515201c7c76551520357f74551520373f74551520073f645515202e7e645515202e7c64551521f73c64551521ed7e73551521ed7c73551521f73f43551520076f725515201d7e725515201d7c725515224f6c72551520367f62551520376f625515224f6e32551520057f71551521f73f415515224f6f21551520057f7055152024fe76d8d520357e75d8d5201d7d75d8d521eede63d8d521ef5e53d8d5201cfd75d8d526a67d75d8d5201c7d75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521ee7e53d8d521eede53d8d526fedd53d8d521ee7c53d8d52034fd72d8d526a6df32d8d52014fe71d8d52004fd71d8d52014fc71d8d526fe7f51d8d526a6ef21d8d5200cfe70d8d52004fd70d8d5200cfc70d8d526fe7f50d8d521eedc6358d521ef5c5358d526f5ef7258d52004ff7650d52004fe7650d52004fc7650d520057f7550d520357c7550d52006bf6450d5202ebc6450d520073d5450d52014fe76d85521e6f661d855201cfd75d855202cfe74d8552004fd74d855202cfc74d8552024fe73d8552004fd73d8552024fc73d8552034fd72d8552576ee32d85521e6f651d85521e6f621d855200cfe70d8552004fd70d855200cfc70d855265e7f50d85521e6f4615855200cfe76d81521defa60d81520e67f75d815201cfd75d815202cfe74d8152004fd74d815202cfc74d81524be7f54d81520067d54d8152024fe73d8152004fd73d8152024fc73d81520067e53d81524be7c53d8152034fd72d81520e67e52d81520e67c52d81520e6ee32d8152014fe71d8152004fd71d8152014fc71d81524be7f51d81520e6ef21d81521de7f50d81521defa50d81521defa20d8152005bf74581521f5bc74581521def86058152034fe76d9542
  | 31 => 0x915300cfc70d915373e7f50d9153236bc6459153735df735915301cfe76d895322eee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d89536f6df53d89536b67e53d89536b67c53d89536b6dc53d895322eee52d895322eee32d8953014fe71d8953004fd71d8953014fc71d89536f67f51d89536b6df31d895300cfe70d8953004fd70d895300cfc70d89536f67f50d895322eec6258953014fe76d8553226f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d855301cfe72d8553004fd72d855301cfc72d8553226f651d8553226f641d8553226f631d855300cfe70d8553004fd70d855300cfc70d855366e7f50d8553226f4615855300cfe76d815321efa60d81530ee7f75d8153024fd75d815302cfe74d8153004fd74d815302cfc74d8153034fd73d81530ee7e53d81530ee7c53d815301cfe72d8153004fd72d815301cfc72d8153014fe71d8153004fd71d8153014fc71d81534c67f51d81530eedf31d815321e7f50d815321efa50d815321efa30d815321ef86058153034fe76d95432167e65d9543254fd75d9543024ff74d9543024fd74d954372e7f54d954372e7d54d954302cff73d954302cfd73d954371e7f53d954371e7d53d954301cfe72d9543004fd72d954301cfc72d95432167f52d9543014fe71d9543004fd71d9543014fc71d95430067e51d95432167c51d954372ebf41d954300cfe70d9543004fd70d954300cfc70d95432167f50d9543034ff76595432167c6559543715bf7459543725df735954371cff75595430067f7559543714ff7459543006bf7459543254ff7359543006df7359543004ff725954301cfe725954301cfc7259543004ff7159543014fe7159543014fc7159543236bf4159543004ff705954300cfe705954300cfc70595432167f5059543025bc7655143036bc7655143024bc765514302dbf755514302f3f75551430073f6555143036be6555143036bc65551432173c65551430079f7355143025be7355143025bc73551432579c735514302ebf635514302f9f635514320dbe725514320dbc72551432173f52551432579f3255143005bf7155143005bf70551432173f50551432579f305514301cfe76d894302dbe74d8943025bd74d894320eee62d894320fae42d8943034fe75d8943004fd75d8943034fc75d8943024fd74d894320ebd74d8943024bd74d894302cfd73d894320ebe42d894320eee42d894320ebc42d894320eee32d8943014fe71d8943004fd71d8943014fc71d89436c6bf41d894300cfe70d8943004fd70d894300cfc70d89436c6bf40d8943696df30d894320eec625894320fac4258943014fe76d8543206f661d8543034fe75d8543004fd75d8543034fc75d854316ebf74d8543024fd74d854363eb
  | 32 => 0x4009000800400c003002802802600a000000c00a00500f801800000901f0008002001002800c00401400080000000010000008006001005806c00a00a000001c002000009804c0120030000008014007001800800600e00200440000000030000010003000000000200100100000140000048000000000000000000001d000000000000600580040140020030004014000000000c000006000003400200900100040080030000010000000000003400000000000000060000010010000002002806c0000000010004000005002802000c007002803c00c0000020000004000000003c01602800c800801400000000040020030000044000000006000001c00000c8038002002006000400600000700040020000000018004004001802c004001000000401000000b00040060020050000000030001000402000b00000240000030028008008002003000400a001000000c00a004000800400000300480000060140008024000001000801000400400200000000270000004008006000001800a007002801000c004000004800402f000000402e004000000c002004000000c008004000002c004005024fe76d8d54256de63d8d5402cfd75d8d54034fd74d8d54256de53d8d54256de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54256df32d8d54014fe71d8d54004fd71d8d54014fc71d8d54726bf41d8d5400cfe70d8d54004fd70d8d5400cfc70d8d547367f50d8d54256dc6358d5401cfe76d895424eee62d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d895424eee52d895424eee42d895424eee32d8954014fe71d8954004fd71d8954014fc71d89546e6bf41d895400cfe70d8954004fd70d895400cfc70d89547067f50d895424eec6258954014fe76d8554246f661d855402cfd75d8554176bf74d8554034fd74d8554176bf54d8554646bc54d8554024fe73d8554004fd73d8554024fc73d8554646bf43d855401cfe72d8554004fd72d855401cfc72d85541767f52d8554246f651d8554246bf41d8554246f641d855400cfe70d8554004fd70d855400cfc70d85541767f50d8554246f4615855400cfe76d815423efa60d81540f67f75d815402cfd75d8154034fd74d81540f67e54d81540f67c54d8154024fe73d8154004fd73d8154024fc73d81540f6bf43d815401cfe72d8154004fd72d815401cfc72d81544ce7f52d8154014fe71d8154004fd71d8154014fc71d81540f6bf41d815423e7f50d815423efa50d815423efa40d815423ef8605815402cfe76d9153236be64d9153024fd75d9153236be54d915373ebd54d9153034fd73d9153716bf43d915301cfe72d9153004fd72d915301cfc72d9153014fe71d9153004fd71d9153014fc71d9153236bf41d915300cfe70d9153004fd70d
  | 33 => 0x10008000002000001800000e02200180440220020000000000007002805800000a004000800e000005800400400a00200080060120020044002009001800001000300a800000c007000000401200000000000000060000000010003000001c000000002801c002000001000c038006002000001c007003002000602b005801c002007000800400600c000010c00c000002800800200000a800c000001002804400602200000380020030040000004003006000c00000200e000c00a008006802400400100a0000008002000000c00a0010020004004023000800800e0010048094004001000800402a002002800404e0010000000004002000000400a00d002800c0020360018020002001000000000400c0000000008003018000004e000000005c000002001000800400200b0004000002005801003200000080480020040008000002001000801c00e024000801c00800800780100120050010000004002000000000001d00b00040020080008000008005003000c0000100008008012016004001000400b000003c0180020000004002000000800000c00a001000c01200d000003000000701e8058000004001801401400e000000400a00b005002c00000d00180040000030098004002000000000801400a0008028002007001004800201a0000058000003000000800c01e000000802e013003802400204b001002c000005000000c00200000400140000030048004014008001001403400000280240000020000018078001006800400c00000b000800000700600000100080020004000013008000000800200200600080130048010008005002002c00400200500100000000060018002000000000c004000004000001200600a00000040000020024000001003000001402d002802c004005009800000c0010070000012020000000000a03f00000040160040000008002018000002400000100000280100030000004022000001000800e00000b800000c001003000400e018001000801e000001802c012003003000c01e00a013801800c003008802001a0000008004002008005804002a000000000c00000500300000020050008008000001000000002c00200e000801000b00080000000080008008002000000001400e00000000040120020010004000015003000000c00100280240000000008058000003000001000c003001001c00e0000050000000001000801000e001001001400200000100000000060008000004000008800401c04f00000100000250018034000000005804000400500180100040020008028004007001801400e003000801c0060160010000022000001801000601c00000480120010008004010000002805c034001000800002c0030008070002009000800000400100800180020070038014004003000000
  | 34 => 0x6003000000002c000005800000600100080480000000000000010001000001002c00000500000080060098000016021000800401801400c80140340040038014000000002800001a0010008010006001000800000000a0018000000004001001c0160070040000000006004001400200d003800802e008010000000200b002000000c00f00000100120010000010002000013000c00801f00000000020010120008002002000001400400100200cc022001000800c0020150058000004001000000000802b0020000000002002001801000500000080060000030030040000000000001000c0018004000001002000003e0010090088012024000001c0000150020000006001006806800e01500000140080310008000000002005000400000201200080020150068024004007001801400800000180740260100058000016005008801800200a00300040d2002000000000e001000001000000400b8000000002008000000000000080000040020000008060004000000c00400100080e80000070020054004006002800c00a0010038074006001004005c00a0000008074004006000801c00000600000000080010010008002001000002000400000000d0018007000001006a002002800c022002004000001c0030008008004010000800c014018001002000401a00080140420000000000008002001000800a000009001800400100600000020010008000006000000006c000009007000000c00e000800000401800180000000000080040034008005006c0000000048018034005000000000e00100000000020060040000006007000801000c00d001000001e003004001800e00c0018000000001002800400e00100000180040010020004002006002000404a0040008028010003002000400000100000280000180060030002000002809c000002000800400200300a800c00800b00000000000060040020016015000801c0000070000008000001000003c00800c000002001a002002800400800f011001400200400f0078000002000800c00a00c000000401c0000000000006000000000402e002000000800400300b800000800b000002400000d0040004000004001000c03a000004001802a00300e0028004000000802001201200300200000020018000000000005800c00e004001800c000005001000c006001000001c000001000001c000015002000000000f000000000a00f002807c00e0130030014000001000804400e001000000401200300f801800a001000002400600200180000140090000020004002001001800000700d001000000700a8004018007001000800a00f0058014000000001800000a0050010024000000000800800a000005800400000e000004c01a00000000480000010048018000009011000000000
  | 35 => 0xc0002e612ca0000f99000000006b4f4a48a52fc00001f75009441000000015fc00032700001c2804149d451a0000f404a4123f157908118bd4044d74c3a04311250bf0a1c56c027c1d506f35301012499142750e10933b715012a94e6b512c8c345e86bb122153507e46d8519899f0c852a400006a300000001748a1f4a80c2446a44fd2f695222a2c0002d8c00000000002e1c0002b782232890f131a2d102013518900000000000abd1b54000129c4e000000002a440003e00af856780001ba13bb03f400012bc5242de52bb000008b32640000000000000000000000000b2cca227ed1b526f881817740004184000222d1ed03c87f235f4ae710a40000e3558a472c0001a3ce273054a8d47e128b0d0c96a4b153033ce8ee300011e30000000157426c00000960000c07000011d00001763ec853015a80000000b030af0a2d05c13f54c9481e08b00002d3885c029875133ad0cd07247bc28104143bd4ab103e100e47c00000560c0f26300000cfc67f00000002f187f0333894555f41bd4ef02260620000174d14a4384a9b000105b2e58aa711dcf3714f4cc503c4000370496b2cd40005414ae10f70000000039e000000000000002fb11284bc1485013c58813a049d1b7842108dc000175497d000111c00013ac08d410a0001506445cd2b4f780000c9800d0008000010001000001c00602800a000000000a001000802000800080040040030050014002002003000402e000000000802600100000200020030018000000004004001400000000000080220050020000000002000000c004001005800c00400400280000100000028000000001002002000e0040000004008002000800c004000002800000c002000000800000800d000c01400f003000c0140040000000000013003001801600f0038008000001001800800600e001006c00a0000010024000002000800c0020010008008000002000800400201a00180140060010008000028002001001400e014003802800a00000300040040060038008058002009002801e000005000c00600d000001800401a002000800200d001000000200000a001c00200000e80000140070000008000007000001800401a00000000020000008018008001000005000a00b0040004000008001001c0040000030000000000004801c00a0050008004082000000000000200b004000000000001280000000140030058000001002801400200000b001800400000300600040030000000014001000000400000f000000c0080010000000006000002800801600c000000402200c000800000000e00000180000000010038010006001005000e000001000402400100380080060030058060000001004000c008003018800000c0050018000000002002000800000500c800400000b000000803c00000980
  | 36 => 0x4436d09900002a10000e8332a878521cc31e0b753f947a482a29eccb044cd4a01a5445b3ac4f7f00005172bc80b00000bb624840002da00002f086290000000000091d2db40690e1101a54948cc2dd510451c846703350601da523b5288ba0423c0000000f0c1be4f0245b80004f7c14e0554000028c00000008b92a6400341d85bb4dc924c3d40e4e2c7d49700000000001183000000017d40002a0cbf7023400017a0dc22edcbf2000000016cd13f2b8d20709044e41ed0211090929711280003b287e501d0d5a2ce8dc0000050644b8c174b3c00022c402500000002774b914be83f8000000000801903ad40002e1800000000003d1c000000000000000002bb000000014d52d2809e000000700007aa264128700004f2152c000000109a000069d196c892000155d0000000151c85e09d00000000d150000a1134c114832692ac018400000000001fd000028c526510e473a53051bb4e1d0f20000000000063600000001f1800023cccb700000001448bfd00005fa000000000000000000000000000000003d9000150e00000002340000290000038510c91a4c4db569c051448c4150000864440c6ad49a532900005274d2c2380000b7200010340d4c00000000ac4e7c00000000001e740000f808f6000145606d09fc4c686bf2d18ea6137c84613480000000fd542a4000000038500012be51347de000060e3710cc803cc838185c47d000116f40b46461dd44cd5224e984940c410b685b030706494a2000000002301f583b237443f605d45ad231826a01c83e800000001ca079550f82974838f0d00015a2000139a08a0d8c365800039b0000489d07d2da801705c474c00005b8063d0b3191c6620790000000099c106cc4300000000000e8824d4000000000000013c33360000108c63531a800000e00001580e9a000000001994cc390028200011884ba03d02b200002704b15000000044240001308e311f9061d25940003b3d4b84475298000105c0000000009000024489d309cc75e2808a88241c68634a00001fe400054215000000000000027a0000a8c31487363060086431ca7300000001fb40001ddc00050549d8089d268163558900001034d04b770000a1b4ff11fe000063d2abc7180aac7b0480517122084f14b9908e261c558210400000005953d681fe0000d464a5057300014ea369129c46f89b2000000040340003ef0000449c0000000340000000009800004cbc00028b0369513912f23c400000000000000000000000000004a800003b742f8f150000e3e25b000008e89a1034000000009f40000000011d32d297528e2084beb412800000011c400000002de0c2b3220fd6000031f00000003430f813094bbe00000003550a7e1e3800025e41b6441400055e8a130000ea50e940000000a0e313d3af3fed5580000c7f060
  | 37 => 0x109a34c610271e5c13426340003b080003e8815241ec00000000000ad4e5a00004004d8c000000107f000000016c4fea07d4ba80bdc924042413e3715462000096400000003a84a7954b03ab24800000394249288ca411b2800052cd00009c908d56b517b32f8b6e334ce800e6c6db36cd48b24e87d41854f212010ad60c803db11307d506713550000000532d3860bd133e012cc294a8c2de45540001878974554c0701c4c0a54b8141c4f2400016e824c00000000ba500330c40ee28cc00000000000000000061c28f06a8000000082d111073f0a1895c568000000000000000bed488405e1b3937300012931098dd8000100f2e84916000128f0000c5e413c5640000c3f44e4d50000039d1058cf500003490d151ae0000f9a0000b88399800028f132b09540004cdc00002cc0003ddc0153f8cea9297039302f9376293c000000000045d400000000000000df20000a250fec29a0000f6600000000000a09290c9a2464102b44f85ef000086854a0c7e4a0c00004e061b21b827b0e3c3ec55fc0351b00b1d3849469204874e47d07002230bb342803bf000040a1f894ca3db000031b93fa07d0c583b2cbf4393c75040440003a3c0d200002bf107103c000065950b40000000000000139300000002ba037524500000438000000000000015b700000003d151c1000000015a505200009e936c4e950b5118717501e62fc0208337c2b8534c35e2ce4b804d140bd3fb104916911a439c4e1f2bf14630000bcb03646ef1dec71943280d706c8e300e04add37746454e6cf482a715751edd28632e0fb8350073e4f08aef0944b6f2c911df13787ec00002d8367d5441db80001288c7b00002f146787e021f4d0a0cf4a4633754f400010212108d3b3a7084c482c00007800002de80002f2000000000000000be31bf12261b4cdae1c34a9a4f44398399c0002531527452400054a80004660000000017235d8c4d000136f4ff40000000e38000000000000004c2c00056c4f0800004d052209af219c0004c8c96d00003b509dc878177c4c3000000053f8b7343980000d98f635014933227c4680a90a8a0174a7615f461803a94871a580000000b5a3e3c000394c9494dd4502000000000004b6000000040d800000010d21b50000502c8e125c4cc6267828c4ecc0012044ad055c127d06445912f84000000069e1760f463928e5541000003620f2608f8000000000025ece6d00000000000bdf0000544468080c4eb40001de40001124000000000013f82f3340829c0a0cc0a49e4b532188a213d4c9913f4d26e4ced56a30155514ee8d9433a10804f9033824b841a04b12c431e93c80c30cf41d8d046153125800014a800014841668000000091026ed1643cf953700680002e6d09e4ce0a8000000004a7500a4f2c38700008bc000065a2c650e3000008
  | 38 => 0x3c37e507229a83f44c9d38e00000000000833000000033a9172360cad3025c3a04f5800007fc0000fe80c6000000053ec70529e00db010078b11d800010ec74928c0b5519490f53a7cb4500011e02534532209c0002460c125634a56391437f0000d521f7d1362e300c250d80002f5c00000010dc00015984978395492c9f342b4000374d36647fc35553ac491184881d000030150780004e540003cbc1d4000000000000003adc5a00000000000000042ed54e15702fb24d953f0000cfa000011512a40001fa908300000000d3400000010d9563c53a14ccbba4b8d21030d48ba00000ff1a1d3d556bd41d3a2cd6108c852f1689194000113d434c97f0dd8e5d4ea000027d4fc040a159100000004f4c2d533bc0001929335383d455000059d44b0656078c82c0cd400008bc4e94224f97215c00007743fc48f000007708c10ff90392764c3d52088084c084c9342070623a8110530885b0bd95410ed09ae000000010405de00003a120f8e1e13c017a046c000000065012b48c448d88f93af89da000034e4bdc51f12245b53514ab65428508321cd6f50d0cb92c6137c000000000006c61f4546c0028d6616f41ba29f4ff419a41f20f9ce8514f0280009cd8f0e9cb0133908af0000000410d2ed00014b90cf8196466400051785214f190ba4599384231ca0f537448d1ac016318ec55634a400035ec93e2708896226c66b28a0fe2000014655b458a4d7893d00015902ec411109a4192000000000000002a0800000005f404f000000012601388ff23c711e1304c00015ac000000055f540c985041cde24140fb12040e393cac0004ba4f9e36751d11e044ba487936b4390fa9067c50546040000000abc33f45702fc4e5700002893e449d506bc0ef4614a8e1fcc1a700002b22d84dbc55647ae0000d7c1c105a90000ec004e525f40d545b3f212d915c540a07c503b00000001d2d47b20f508a43f92350000def0d3ce2d1494b310cb5197364448a00010cc1e4513a20bcf8600000005170ce300014de1cc122812ecde61720b3d340cdca03511743dd8ab901b0028335076a4f352763e9ced443c14a6076833334694a75490d8e0c2d4481b2042e0e7c370504003f35d1560535c3604c704c131b43051e1815c05694b4115c855560021d347005222291122f3d22d39e52b430b93465524a592424e742a04a452d413283a788eb42415641f2cbd63d3c21f03051a83920d7e48d01e528bd29252042900e9802e493d2dd0b210c040895770c3495e44300001f08c8c00010ec451133c0f38d6705dd23d52dc34c43b93883fa40004700266559521b21f1154374810005891b1000133d368c03e2b1cef1000000000000000a9c00000000000000000035847f0b913a536e48c80000b1e51b845006284270000bef00008ce084800045b126c4ce910854
  | 39 => 0xe480d81c8cfda10d000020b82db1a14c08000154d1c0827814c4b3e41a400000000003a900c9163c03100012bf15b0b0c16392a51a5c00000000001684a1e178528a00008d30000d5c00000000000000000000000007b305980002b7115e45a86281e9c0002eac00030d09724be000000007880000000000000000014ec05913ed530cd2420ecba60aa83eb54844fa53cc67e248c8430adc983048093c3f2552e506d3e0000071c000012820d816f00011c64f88aee0dbc9c019e4000000000054640000010f3d4e246df0a04507282c440189009d1d195a6523cc7d0c8c1d332a14bd000073500000000a4c000000000000010a646bc73340c10c50800d0936054730d88daf1718c8d50183ca02e000000005f1099d0700000d6a00005202ee051355ac8ca4b50509000108638b0d902464000143d2401d0400039a405b2f0c21951f52cb000108809e40c012dd2ef09b85844d28d8553213db0ab50e21e78ada4f1117e250c75d3dbc9001fed3ee4db094b30807d321a545805f05a72ba4562429c4ac52acb592d040ab32ac4c73730625265d3a6330030839a12cd01894082ee45493d5d1a132742ba5315576361c65121c53ec1ad549f351c5b94f3c9663b213e733f150d4d5854300007c44565420558c0001168479034d3e93bb4b4d1880f0f51a800000000004904000263cfcb4b20b843cc87274b5c99a04b86da0000d8a477860f4de000000009b003800002bb40003b88e2900010f61c944c600008c0380098955a480a296000005a55842c384b9004880001bc20c0d74df5520d4b223e13d053f40002d3d0fd2fcc0004a010b4000000017c117c15680000fe4c1b38751c5373545037507f6024c0000000765254107156394d800004ec3b54f5853c05cd098c13f0a1ceb23b0535c532538a5528000170cf72491440f302c08e1e8552f1c3829425e87ba2fe043e1cd0a4710d8895308c9f047c935f24551eb2ab8b6b353cd411a61574073ca6f4168a7f0bb406338d4e7f40314e51f8d16710f090425114c73ab8b28148c23954f8c4428000000e0ccda19d48ad3ed4a8613107143fd818d3ed907405400003da4aa830303e2000018b162cfc14ef4f102df51924da81021509498076c0262f70000095c1c31aa09622674d494ec80003e1c8e60d2d2910000ecd1e28a64195c28e0c2909b00013a3072c00000004aa4dc531e41a858c1ba94164ec001d18a906e48c4000000064039413e33fe04bc1120ccd2a906c4213c0cb000049303a036d28f8306075c63a42c046a4b9c2150000e8900000000001534345c0943fe437b51d0000297ce222b7cf163c0492612500000fc0fe44fc800028ec54e1859212000000000000004a140003e540002e0ce412c292e505000af24e146702fcead0000000000000000012b148280003e6d17700000
  | 40 => 0x39d22f468c03103e629b02141efc74317ac7373c2c50c188cdb24bc94dc26d03133ae80003754d070000e362a7c3cf120cab521283cd18f10e71e0140e003000000009ba3c6089a000000053e13574d4d4752ce000000000004df40000000cb4306800050f12ee01944cf0ee03500de446310d40d1535882b0000fe017b4000565c0000000000000151300000000000d231a7c00000008cf000000000000004e3400000010264bb01a4000028a526c8e40d20de30c48b67491956e21611b843a45663ffd1bf2080e7b2a8c3ee18b81eb561809a3d7447b488c425000087000000000000e6f00000003344000334000000013e1030d37a01ec95233546be07880001ca8a693b693f001e4ece04d51d529500005094428117cbc14fd915a25513f1171d5991360a60425ce7535e8ce6291146d4534fd100000001d70a3d36a0d274df80000c3c00036240001bd40003f712424a9d47a00011b700000005508000138c3a951f0ec553c8000380c4014a2423c1dbd56c10748a902d48fd35101d10948986000013b2054a72000100446c83670df00002bc0f1f3e7131232850a42dd8000235514e5044b0d3a6cae620c46d135e122a00000000000e073b2400015a045546004e708b4000501c0004acc00015d159517807014b78ad73e8400000003fd42d810d52c433a0a7400000013971e405d0430c0000e5113231ad3fb4cd88fb00004330000e86232c6911f99196000145727dc29143593b639f934f56a47080f0c4d5454122b35210ab4e493643c6c4d11fad21523f8b710d282c12b148a62cfc664225ce8e3e2d3810c6c84835747c056081ed49107381e69453206c95620c08561d4d24e18b11ca0740c9f531915c50b85cb00d8642279cbf948b11ba52e8d102e5454546b003b189d35a5130c94407832841bc74a19c4d730d8c65e2ffc6730f5cb81350cdc6182c6c1391825b3c482be042ccfb538142900010dd43c45cf0f5008c54a54e304bc8ab2d2c4d60000d982c84a493fa02d74db850d310906400002f9419800021944da25ccf5e2e41516000000012910eb00006f41ea00003c1c000485889026b42fe0000000000131000000002cc80004becfaf00000000e690c12c687bd44ec1a90000b493908000227921c46acc8a0000000428d25102d92d51bc4fcd0d68f6d1540e3b00000003d706b1000115f419c0003f9c62b2aa800041e800013fcb5c11c8e6300000003e1110b37ccf9d00006bc1d6c3c809414be05cc1c5447d18e275cace0000dea1eacb8b0000265000159c000000000000ba4cb8be227c519303b40004ea542b40dc57812cd08c000005410e025947f4dd600000aa548cbd82cac0000000c5b4dd01253e3112b04f43d10000cbb37c4000503c0e71e4928411146b221c82bd516903f1f7490e47bd0b220913331b5820b3
  | 41 => 0x4a880003140000135cee838211aa0fa8dab3f180000000000445476600000004c7c0000000b82050400011b000000000000dc857a0000f22000117f0000a70303800000004530000000000000022f81c8000038600000000f04c392e50fbf10dc4a042849f200000000000984000101b00000002e3d20839d926d15bc03706ec77c000000006382c545083a44104aba528cc9b2f9501426c549d3384fee1e31106023c0004ed0f94468800021840a43e0853f15d8f332acc8932c492392d0c83a32a5056085888f04500000000e2a0000caf260800038e94ee10f502432fcf6b13a86f81f3400026544ae42a80005060a8f20350a251652ce00008d43d300001ee0000457534000013fe1788efe02c40000000000000000055580000a600000001315369c00000006fd0c8954f068cd424a68d703afc00005f94ce323c97c3aacf041a885724b24aff272d1ea48e813300002a50000fa6470d3b54f1c00028d00002cb0e8a0000000000000000006a6547400000007ff364c0e9473c23f4a5463200002a63170b7e435000034fd1d0000020223dcdfa3924da117ec6a52638dcb40400503f1c00000000001e084e139f095d1704fe11938000405d35016d0683000000000000003c38eef544911b00012c3000000000000001a3825f3bd000000000004e3cf2541d55933634e514ffcb890000720463c0003594cff3c6537b175c00000002cd000000006789253b0c5fc184c00000000001c40000000000e0f0119d00005860eb0000381840500000000618641000000021a82af4380a6d20f000022643a81b24bc500011110de815f51a0528202509c00004d311e0c86500cd221d3c0003f3912a2e88e8137b438200004410918147316442b1dfc00027254e100000004ab952b382453856ac0095000d3d2f507b136fd1c9000153c3c0c00020944030000000194cce90ddcdec3b94c452be4ca443a064d0000077020488500000000000000000130f00010f42138000243000003ec342289c6cd11d40003410000539887b0cc8da517cd28c2dd0b4051455b506ac91a56cd0621c7c5924ea8aeb28e48d737ac0003d8503a4f280003c2903210c800018440004fa864c26592521a0032c07340000000000000000000013a20000000000006a1d08e4b000000048454260000e2837f123843f00003978de507315540bfcd62352d56600000f71fbd3304fac6650d480000ef000000011ce10c415d3b9c178000037d00014a14670b05000000022dcfb90000153000072611b4baa0e38a2925e000050bc0000001454000000048bd08700000004cb00001a080000be12050cf10981dd0b4837b80000c9cfed3dd40000000000386408755c52f3000053e07cc4f32f4c23125d55a1002009f24c40000000c810d7cb3342d502343090ef000000000007441d49
  | 42 => 0xc0000c1c5d100008ac0e58000000071600015b61d888f23f7c0001d6000027ad4c40000cb244c000028ac0004d0d0d134d8000000000037d854a0000000545070315187670a78875000080f12944843b5d3ab1b940003bec000278c551000032a2a893d2373d47625d8000242c15e3af53d718b44f94d4890a06c40f92d895a50d19579244c74048c0dc902b912d4cd09e2187000027e800045608225530d8b03f8000247044b00012ea4c74f4144500531a9cb52346c6740000dfe053533f2660197000107c329887900000002628fd7000000041382f23950fac14b8412385937f245d30c31d88aa000151b287478f00007dc0000709494d1f5087026f1e4c670051400020d4d5342449c4298c262000000000c04ca00002c019a8bbd00006902df12f41a10b2d34140001cac0000b4d370000118b53fc96900005f6000077e56b0f3b17dd16239652821c902c300000002beccae000000000340002b34000269c514000032f36653040000ffe0000c26047d30647645cc45a0622000000040a45032d60ed154c4cad52d4000000104438551bd07bc69b1cec0003215557000000000010852f448da01cc8b63960000205000056d0000050800003d8f880000bd900000002f3400000000001c2c0000d6127000011242a78c6c00e95a800015070000000433c52c3f484ab2c70a4c0b94402324cdc300003f100000002fb80003c00cf7110c00048740462d50b3c20a0ee1048445819b4fdb04dcd2e00a425a0228ffa13504ed45b44193a3000000000003a0800036e09c6427c1160b3106d2c3d13c51c45ea307c4b811e884752c002f0a2d30131d435c550ce603b5911949e80a83f312e400012634794efc05ec000000000031695623130e130000e0a3a1000034e15471200193000016b3b7c38955f87cc2e640002fe8f7419b05b600005b709f85351118c022b00a77524c0e21cc938c00000000c006102b4400000cc21e4b1c6a9114459732780002698db739952332954a3f44e098b5630e5c3a40000000079c0108c5544390c80a8000035fcb693acc8fa0b480004b04000000000007102df000000034e4f0900011d6000038a00000005248000450c2291c884dd0b44e924f70c5435e40002c5115300008dc322527f0f8c06700015b2276c8370000000277000046b47c1000072d0000000000115700000002e90b9e1f281a24d080003b807a23304563180400000003c94e91496396d43548080000000b640000fc42a840001f400003d9cc0d0d580000000fca0000c5f00012430dad46030784951534e6a4efc8c92f243e1017c54025000001ee4da93ed078916b925700000ad0000000228800056200002aa53e5208c55208ac4973eac499469cef821d9033365c850256895912610313958ab000002064294b5f0aa00763e90a9550a0000
  | 43 => 0x446800014e4b4430a93d4296d2671794b2600000b246441bf0c113914f0400047b0ac354ecf853b1c000000000000002c420c914b35b510134f8a0a24bc6e4182406413b86c20c380cc0000e254bfc00000000001a514e718c471e000000040b800000000004ca85810000000000000000000000498854000039903c03b6104505f34dc0004f994d126e49cd4a34000379c5af00009de00000001fc400000012ab0000908000009c155c33923fc3d80000e470000dff35800003e8123e54780000778000476948c0000dba1c540003d34000118012b49ec000369866752294d931e15404f7400004c06d9281c5a51a80000556c0002ae000000000003aec04c000000b0000c8304c40000000ee9220c0001fd46764f682881f384624f012b601f057e3c788cd067401032c4d570ea8cb620592ba2380ef03ac0ed31728b29435445d0000a1401b4f900fc84eb2f800004518c6f542c3ed07b0d4d2a4089c00014800000e05333d5a4255c67c39908b206040004e0d4fa36b4000389057b48100005264000416400005240001ed815400000000000e332b54d5b2f10b2e1460d720000000552d0c62a1c00052a81e10d10c7400002251bf80001abc00030880990cc000018107a530dc1614014cf33a5c0000000f5443e86b35570fbe051065c382c60622a01231b1c5dc34d00001e98c0129e8e964ee000018351c726b07d74bf4056000059600000210c0920f010c7843a9d0922c1800030d80c5290883f318400017f4000000000043a80000694db60000000000004e093c5f8000000000010770ba84be25082842eb4c630ab000019b8315121400051dc0000000feb224400037e095507e87552ebd49500010f319ec0001738d2501f901d06609283c5c96f4c5800000000005444000000048e2b18c49166cdf705a8d4a253924710788ec1190eb800000000000368048800000003370000cde0ad86434120efd0ca400000009c300000000b84c284ab40003cc01b814a47e953880000160a050000ff01ad04f712047711504cf149c800025602e3486400030f130e00001b5539105800006391258ab24d24098311c00023a13190be91fa20991823a747c7000000000001190d1c18c066c3c6000087e227400004152dc2f7800039342d648604692e1400000005671bed4a53edc24826ccdb43c90e6e02e544646c12d0357cbe83df48d947485944fa00a0144081907080dd2cd06ee00000000000b8a0bacbb438403ba312800042b8c1639cc1d23ff539c0000a3a0610000319400000009ed55ed1631e0c285421000051fc0dc4ac05da10c11dc21493621ab80003ce40000000000479c41800000000000000000070f092c00000000000000df0000093f000141a3910eec3d2c4b0065000000010fb0f540ec0000e93043cdfd197d2a842540c8251
  | 44 => 0x693be0220faa3b48000000000000000000000000004c77a1268b3621d00113aa92f14250953335c0570d50c4650e80004de40001714000239446149f07f80000f712d1c1c64b180000000b0251900002d313f40c7037e14b4f4e33483640a88361237cc8b30bcb2f3b6c0a1296934e2d98f2017090163ca0e8d38840002218ebc35592373b652c21ec89df47740480000000000000049580000000a890fcc000517d1e6052c69933949cc0000000496400014ec0001cb80004c9000011395480000000000000012c4409154c00000011d83eec0002b4860803f06c533b4ac12d7800000013823e8c88e02402581a2143b4d203c51b3d5b808f40000000c69000065516fc1e950500003c1956720149050a7c27f0e8cef92eb00002ef03ae0c24c68056c05549cc3314a040003d5400023b911809c544f52b502a0001380000104d0000adb4d34299147077d167c000000000000014ac082800022040000000000274873111cc61a1974ec626040000c5c1363df15784aa89510000aca199848f329c00000014cf00000000000c70389814a0000e990f4849b00002c231dc0000000f7000013210000000000114c50cc24d000000051000002a7438b0f900000000c3e0000000130020326e1140557c243377cbf63ae53cc183054f25f85802f400004594c840000599000099b484c9610000d0e48243342a4c2ca3a1c90d2b3c422000155204c8668161481c475c51e24088fc3ca95552e9d4d40a8c761278024e2b647bb309c2b30e44b5d0f2cd2a1e811c2448013a3cb0a7515509fe1fb936d443428d22ec336192c75717644820050000480d255205c000355400006680000000000000000054e92da463400046d00003fcccc30000b2508b87210000ae233b000000009c500011db55bd21a000046e439400000011700000fba05b439c27d80001b2c000000000034e949c385c00028986d72e743c400000001dc80003bfcf642aecf2950e51cd376c7293948000073800013701fc1ff0a4849291f315b94db28e0f273f749e44ddd0cb00009a81c7401b1090da055786f254e00000000000000000000000824e794323cf000042f442c0000802566c00000000000f94e78000000042e4a5043786dd1899509185086d412c6e9146cfd94da03d649c4f051ea4a1505640000000000086800056680050470f6a2721078081c00043b4bfb14dd0654894bd2411cdd92ab4f36005958b142c43f1194d3c00000000b40a6e1ae43ad1d145823da0ba300002c740f486b00002470b64711108009137ed45d000127440e08e24b4c000407c80b252800000011b63784000000000000010ac2114a5e0001116180c1ea44851474750d6c24e4ca000d0b5615840004d44dac4c980004e2c9a42c202ee09011132f903c21cb0ac429c522054706e72180bbf000000
  | 45 => 0xc503783ff19dc4c545149ab000044d00013b90000aa03f0873d5184fd81ad8d1d00000000000d644d80000026c00041e4c6708d80d50001398176c3713610b6c1b48e0d33111cc0398de41ab10153e94268083440d3b10ae03f994522f013313244f4316f87d94060a0817fcfbd2360c3b083c07123480e150c4205000134c564800046107174fbc23b0000c2c22d4d682ec897000010734aa505d0ab8221240c63027e4f6e00014f717b84b20001122000040b00002a90000a973dcc18513f06bd09b46ff1e642922b303be30101fb000025c0bc0c062750f1a3d248e700009ca000040e298812a35c41ae4c8918607600000000000000110042dcd9a00000000000f2e0000000000126b32cc0000000000000000000007a3000000050308d12bd9573315c3112aac1b9409543041507be191000053f130d0000fef1b3050007a0318259c2530bd4261211000000000004934af40000d2f2a5811e0c680001d7cff73d6c32b49dcfae357888455148de003c7da4e801a1006092c37802e03530000271d2484bac1ca44c54492600988091400039e948e34b543f00000000000abe031d057214c1510e3000016780bb43692240000000000130a000000053400002ea400000005590ebc02a1e605bc229d52621dc1a8007c00000006543689409101c00000002132eecd324064a4d30242331e346b84d64ff510205c053491261d806d021fc3b3288953d54cc8ef36f4d182818b7b3ad891f050c1c1075403926800002c8c0b700007a41be8e5f2f300004eb907e19e07f752bc1f04a6c00038fce1b00009303bdcea24130f791f84b0027386050a6c34111bd21f1db14423654e615454df44668218062489853693c544404713294afa26d810450890020bf4e7727a11a545a50f85674a2011f8e2e06dc6f74d604ce26a45893238e2026f11373cc53b1000004407d8a4e31e4ac231cc7d212f49340000f510e206c315dd4914080cc22d088a10bbca1930b54bb000000029ac000107c1a03b30000249cd200e4117800011520764000000020e0000f11246c53406f09a51bb04f51278a18441c000000114f0000ac9000008533d859c00008e305e55300b99447121800038ad51721bd2062bcc5551d1c660029c00039c87af2945347000036a2f7432412d03dd402d1e228b80000b88075164cc972ba85d60000a37508d0424950117008c05c1410abf00000fa48880cf13e041317b001c18cc456510c31622248a4325411200c863e294c941113d49400015504adc67a36ec6e20000270000119f1b700ca000126a4b88d924fcc000193c0000000000000000000000001520000220103e000042d00010680890000196029552fc4c84b0003d0b24d5900000004ce400018dc000000000000000a90000000414d1fb4be4e023988b651ff955a085cd9e54
  | 46 => 0xe694a4000000015f0000435d35b000000000000003aa000012fc1ac258c8490eeccdb332400053c400015b548d1864778000111e0000b9f000000008a94ef51112bd3de035b00010b1000149e16a8000000033b46304ef1eb011a21e82dc3804d130f7c000418d5ae1a8452a3d5816525a0bfe097400000010ff1b80000000000000000000000a0c00012cc34b05e717e420951c07fd0000a171108000000071200003745114dd727f400001a15aa06ccbfc0000e3d0c40fad0000f9f000000000001804c152b500007c3105ca322e941274cc947922943cc33e460a20a4eb400000000000bdb00011c8000000042e07c800000000fa4fd000000001adc0004d840005034a2a32d52f50000d9c29f0a03200c66301ac04932f09602fd4dc71da000038600004c44000346477612d4a1a2a1400000000000000000000000014040002f2857524453a706552d100011e82175594000074d4c80d63037c00026fd5852949161218d1ee00000022c442101dc05e62f994371030887558400007b919535b85190000bea161cf8900000003e34d33504910a3bc85831f9c68d09d505e497429625194df479150c485000000003bd4f64cd604a4eaf3b6073c086c5900000e1c00000000000dd004b525a0de03f73d7c85100012610000c4b24ac00000010af000000003d45ac45e40002adc68a3e60ee42651151052091e1170ddc38bd20d3b78bb00000b7044d486c000000000000000000f3547d80000000a6700002cf4004b0b3458ae400011734988b370b1925c17c800000012df568caf724b41243a4549000012781454b2a388c35123a50d041b025e2cec0000000e343050c3348004f40000d0654600000254d014a647643d104cc142863f1198c662c81424179110f5218e3722e105540bc24a19bc8dd19f534400001fd433943d11492bc23142b02d6cd7542a142a40b0bce314cd7701f49e5285807f3ec06483bb83de122d36523c045e27e00004c6cd26496c0000ec40000000000000000038c85ab31c800019c9308040400000014ae547c8941b98a6133f849005b879b2c5800045f400012308b31f147394c00f341800000504c00019849aa00012a614451d3422ca84243d3d80000b7f256cedd000000023d4118000142c00014bc00000000000bd53f0c000404c922000000000000002c400001a0406e00002bb069817d0000000000000016a0e7000000004e148b022340000000ca302d0000128ce4c3370f961284d803364ea309ac000053cc640000afe00014cd2220f3f456cf422418a923d646212c4cd860000ed03ba8d694e5850e00013ce2c240000e5cdb500009e654e4000132cc5d0d5c00000000f4001918a228047c00000000bb0aa651bc00000012b800003b016982ce543d2a127a87d83f3c000000000048300001fe89ef4ae4f
  | 47 => 0x55b1c1c8db5064929042084007003733decad805b0a35039126642091a326dc9ff402400000006ed00014010000276000129e00005c455f04543720b270000b5100000000000c0000000ce000000001681df00000002e48748366c000000000018e0000000093747c44f6000077300001d6338900700000000000000000000000006a433809d04da4000485c22210a800000006e10fd4db013ec8591e7cae534c4c1939f415730849e1000046b055927e136550253d4f834e514f655c8f7e0ee4380081000038682b445ac3143a8017f00008bf304078707e0aac4e40dde20391a6466c02d2c108b4012832e14755813240dce407049c0000d1e339cb9c05d07c916c80e300010d84b6000000000000000d2100008ae0000365000000054c85a352a50bf47dc16000000000000a943ecc9cf0000bc73be89b523580001eb40003b980000418c1d0000cbd2840af50000ef6292c1b0020cf624abd4e94d50c382fa499314585653188b9705a02e80000e3c33e000029943a20001536331cc9618d06ba011431d30c800008d07560000807381001900007e800010450164c56000000043e4000071c94f2d5c42f344400034014b60000fd44b6c000000052b00000004e646f6000000000011341bc06023ab081f5658daa09502640ac472f4d9c0000000d0f42740000000a363c74000283526f48b8c82266406000003193ff000032b036c00003ef30c07960088000551871a02894170000be70000000000020100015873ce0c515128a660f4c0003de90f700b0492000000017f81be26f45c9000080633c0e430001249121c0002e4c81a37a4a68000095f000000025200000000000217cb8e000036e3100d3546e449f3bccf2d00010962c88d1433b90510c0cad4000061f45d93070000c111a68000000000051e03920000f233248c6000004e500000bc11d085a0000a983e38c710000000088014c000000000006070f1c0003e28244148952d16614210958cf2000112929d0f605440000507cd1253b4cba00008342cc10062bf493201e93a117a400027b04063d489d1149876b2ad158333310082c5ca01567cc984a7c4a651f816742f10c44b48bae11c000055a08011a252f61aa929600005363434bb546cd3f73e4cc48332c7db2134c4e0000af15480f140000b6000013f8228c6921db400053e4ff100009d6347cc7c0000dda2e340001b8ca12356000000006eb0000d5100000002c6c0eb240440401e0866204ce114c4cc033f78eeb4c2435900005791d64000450402b00002e7000106b47f00004b587cf5268e0e0001314000000035ad1562c1d317000000000000001aac8ed00007b51d6871b000008045800004ac8000383096e13985e33f9409210e8199000027d212ca4a00008f400000002b2c000332946b264800003682b91c314652
  | 48 => 0x4bf818225dc00027b8dbe0078de80c940003608000295c69c47e4e9446f1232044d0df00000000224f6532014e81e5000023083da4b8492a3ea01e7116483924ecd0b111cd4e4edc
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf30825055044001e66e4a0aa0883a3cc9c9415411000798b9282a8220e8f30725055044001e66c4a0aa0883a3cc989415411000798b1282a8220e8f306250550441d3e6664a0aa0883a3cc8c941541100079899282a8220e8f30325055044001ae70e98aa088002dca1d3154110005b843a62a822000d70874c550440036e50c98aa088006dc2193154110005b9c2262a822000b71844c550440ad6e70698aa08805fd4e0d3154110267a939a62a822000f51734c55044001ea6c698aa088133d418d3154110005b9c1262a82204cf53324c55044001ea26498aa088002dca1d2154110005b843a42a822001b728648550440036e10c90aa088002dce112154110005b8c2242a822000b738348550440016e30690aa08814adce0921541100bfb1c1242a82204bf62724855044001ec2e490aa088003d8d89215411025fb031242a82204bf62324855044001ec26490aa08800a3e219754c1100247c43aca982204ff92435053044001f2286a0a60880036ce1d414c110006d843a829822002db2765053044005b60eca0a60880036cdd5414c110006d8baa82982204ff92835053044001f2306a0a608809f6cdcd414c11013fc9b9a829822000f9363505304409ff20c6a0a60880036cdc9414c11027fc9992829822000f913250530440037a10e98a608800b7421d314c11000de9432629822001bd0864c53044009da10c98a6088013b4dd9314c110016e93b2629822002dd0764c53044009da0ec98a6088003d4e15314c110007a842a629822000dd3754c53044001ba2ea98a6088003b4d95314c11000768b2a629822000bd3844c530440017a30898a6088002f4e09314c110006e9b92629822000bd1834853044001f826490a608800a3e219754811035e5c3b6e89022067cb8761d12044001763023a24088003aa90b644811001c7c43ac8902200097985dcd20440051f10cb9a4088003aa59142481100057443264902204efa2425052044001f4284a0a40880036ce1d4148110005d943a829022000bb0875052044001b610ea0a408800b6c9d94148110016d83b2829022000db3755052044001b62eaa0a40880036cdcd4148110006d8b9a82902204efa2825052044001f4304a0a408809f6cdc9414811013fd1b92829022000fa362505204409df40c4a0a408813be88c94148110007d0992829022000dd1734c52044001f826498a4088006f821d2148110016f043a429022001be28648520440037c10c90a408800fb8219214811001f71bb2429022002de2764852044005bc0ec90a408800fb81d92148110006f1baa429022000de17548520440017c70890a4088002f86112148110007d1ba2429022000fa0744852044001dc6c890a4088003b85912148110005f1c1a429022000be1834852044001bc6e690a4088003785cd2148110
  | 1 => 0x6eaa0aa08809fccdd5415411000799b2a82a822050f30655055044001b66e6a0aa088143ccd4d415411074f9929a82a822000f315350550440a1e60a6a0aa0880036cdc9415411028799a9282a8220e8f32525055044001e62a4a0aa088143cc1494154110267a929a62a822000f51534c55044097ec4a490aa088003d854921541100bdb840ee8a822000a7b865d1504402f4f10cba2a088002dce0574541100bdb840ae8a8220efe386459150440016d704b22a08812eda209645411015db9c0ac8a822017b7081dcd5044001ea463b9aa0880029ee1973541100bd3c432e6a82204cd58735cd50440016e702b9aa08805edc20573541107753d43ec6a822092a7887d8d50440474f307b1aa08800396dcf63541107672c39ec6a822001a7b81d8d50440034f303b1aa0883b78ed07635411076f1ca0ec6a8220ede5b31d8d50441dbcb263b1aa0880025ee1d6354110054bc43ac6a822055b738158d50440018f70eb1aa08801a9ea1d63541100353c43ac6a822000c788758d504400d0f10eb1aa08815a9ee0d63541100072dc1ac6a8220ece5b3258d50440ab4f702b1aa0880039ce05635411075f1da0ac6a8220ebe394158d504402f6e502a1aa08805edc20772541100053dc32e4a822017a78865c9504400167708b92a088136ce2117254110005b9c0ae4a822017b70815c9504400167708b12a088136ce211625411075734312c4a822051b738158950440014f70ca12a0880029e21942541100bdb940a84a822000e59634c9504402f6e502992a088236dca1f71541100beb943ee2a822001b7286dc550440036e10db8aa08805f5c9db71541100beb83b6e2a822000b7184dc550440016e307b8aa0880035cdcf7154110006b8b9ee2a822000b7182dc55044001ae6e5b8aa0880035c5cb7154110005b943a82a822000b708750550440036e50ca0aa088006dc21941541102cdb9c2282a822017f33845055044001e66e8a0aa088137cc9d1415411000798ba282a82204df30745055044001e66c8a0aa088137cc1914154110005b9c1a82a82204df334350550441d3e6486a0aa088003cc50d415411026f9821a82a822000b7382505504409be6684a0aa0883a3cc909415411000798a1282a82204df30425055044001e670ea0aa088003cca1d415411000798c3a82a822000f3087505504409be670ca0aa08809fcca19415411013f98c3282a822027f308650550440a1e66eca0aa08805fcc9d941541100bf98bb282a822017f30765055044001e6706a0aa0883a7cca0d415411000798c1a82a8220e9f30835055044001e66e6a0aa0883a7cc9cd415411000798b9a82a8220e9f30735055044001e66c6a0aa0883a7cc98d415411000798b1a82a8220e9f30635055044001e6704a0aa0883a3cca09415411000798c1282a8220e8
  | 2 => 0x774589100061fa86e8b122000c3d50dd16244001958e9b92c4880063ea1f70589100045fc22eca9220058bc845d952440011bf06bb2a4880123720d765491001c3e43acaa92203da5c83595524400117f08bb284880023be09765091001c5e43ac8a122003aac8259142440010ff0abb2648801a1f215764c9100045fc22ec99220058bc845d9324400d0fd0a3b264880021f614764c91002c5f420ec99220008bd841d932440071b90eb1a64880da97215634c9100247643ac49922035aac84589324400536b09b9a828800a6d6137250510006f1106e4a0a2005ab684d894144001d4e85b1282883c7a910b625051002c7a43ac4a0a2027bb080dd5414400156f0cbaa828809ead2197550510005d9c02eaa0a2027bb0805d541441ebc6ccbb2a82883d78d1956550510005cbc1acaa0a204fb9483595414403776700b2a828809eec20373505100055bc32e6a0a2027ab4865cd414400166f0ab9a8288142cd2157350510005d9c02e6a0a2027bb0805cd414400166f0ab1a8288142cd21563505107a74a31ac6a0a2057bb38058d414400156f0ca9a8288002ad219535051013dd9402a6a0a2027bb080dc94144001f4441b928288002ade19725051013d5a432e4a0a204eda4725c9414400176700b92828809eec201725051079d5b43ec4a0a20beab487d89414401756b05b128288003a9dcb625051078f52396c4a0a2002ab780d89414400556b01b1282883cb8dd4362505107971aa86c4a0a20f2ea720d8941441e5d4a41b1282880026de1d625051004cda43ac4a0a2053bb380589414400196f0eb128288016ada1d625051002d5a43ac4a0a2000cb487589414400b1690eb128288152ade09625051000753c12c4a0a20f1ea63258941440a756f00b128288003ace0162505107871ba82c4a0a20f0e3550589414404f76500a928288003a9589325051013dd940264a0a2027bb287dc1414404fb650fb82828800aeca1b7050510015d8436e0a0a2027db276dc1414404fb60edb828288002ec6177050510005d8c1ee0a0a2000db373dc14144001b62e7b828288002ec60b7050510006d9b96e0a0a2000db172dc141441778e8edbaa62882df1d1d8754c510005b8c00ea98a2000e5653d9531440091e90eb2a62880063d219744c5100072ab2aa698a20009b584dc931440015a90c99262880063d219744851001c7a43ac890a20018f4865cd21440032f30bb9aa088003748c773541100353d42ec6a822000e5b53d8d50441d9cb0a7b1aa08801a3e21d635411000cbcc2ee4a8220009f08750550440a1e66a8a0aa088137cc951415411000798aa282a82204df30545055044001b670ea0aa0880036c21d4154110016d93b282a822002db0765055044001e670aa0aa088143cca15415411000798c2a82a822050f3085505504404fb6
  | 3 => 0xca0a4000cb5211d94148001975003b282900032e60076505200061fa80eca0a4000c3d501d9414800195c403b282900032b08076505200065b880eca0a4000cba101d9414800196a203b282900032e44076505200155b40ecaa0a4000ab581d95414800117f0eb2a82900022f21d65505201551f42ec6a0a4000a3d85d8d414800556d03b1a8290002ad60763505200045fc3ac6a0a40008bc8758d414804f5590cb9282900032b1d97250520005d3c0ae4a0a4027aac864c94148001958ec992829009eea201325052006cda43ac2a0a4000cb47658541481ed76700b0a82900a2ae2197050520006d4b92e0a0a40058be84dd9314800117b09bb2629001a1fa16764c5200043ec2cec98a4000c3c64dd5314800187eebb2262900030f1d7644c5200146e43ac698a4002ad48158d31480c3a98ea99262902c3a3191324c5200147643aca90a4000daa40dd121480031d90cba242901a32b1db6448520336563b0c890a4000ba58119121480031d90cb9a42900067a201734852000536c2ec690a40028ec8758d2148141f4480a0a4290003a9e194148520005d34328290a4000ba4865052148001d490ca0a429000ba9dd94148520017523b28290a4000ea7655052148001d4acaa0a4290003a9d8d414852000752b1a8290a40a0fa2805052148001f4300a0a4290283e81c1414852029f53b028290a4028fa3605052148141e4ea0a0a4290283c95414148520007d0a0ee090a406bcb876d91404800b970eca1a8090006ea21d425012001ed443a84a024001baa8650940480037510ca128090017aa219425012002f55bb284a024003daa765094048007b50eca128090017aa1d94250120005d5c1a84a024000bab8150940480013d10e992809000f3a1d93250120005d4c2264a024000f89434c94048001b5285b8a80900172e1d94150120006d9b8a82a024000ba9844854048001f428290a80900035654373595100246f43ee6b2a2000c9f41dcd654400193a83b9aca8800317d4373595100062ea86e6b2a2000c5f751cd6544001b4a83b92c88800e3ba1f725911000657a0ee4b222000cad41dc964440018dea1b92c8880031b543725911000657ba0e4b2220008df835d954440091b906bb2a8880023be09765511001c76412ecaa220008ef825d363440071d904ba6c6880022fe1172d8d1002c5e422e5b1a200687e87dd5634400187e83baac6880030f5077558d100043fc06eab1a200087d80dd563440018b8ebb9ac6880021fe157654d100046fc1aeca9a200487c8759553440094b906b2aa6880021fe157650d100343e42aeca1a20008ef825d943440071d904bb286880122f21d6450d1020d56412c8a1a20008df835d762440091b906baec4880021fe1573d89100343e42ae7b1220058be87dd1624400117f03ba2c4880022f60
  | 4 => 0x44810396ec0b88c8900034dd4171191200069aa82e23224000db3205c46448001b4c40b88c890003690817119120006d8102e23224000cb571984644800147d0a308c8900028f61461191200054f418c23224000a9d83184644800196ae2308c8900022fe11765512002c3e43acaaa240068be87d91544800187cebb26c6900030f5d764d8d200061f3a8c9b1a4000c3d7519363480cf958e4326c690002ad60464d8d207cd3cc04ebb1a400687f875d763480018de42baec6900721fe0175d8d200c43ec02ebb1a4000c7a105d763480071d904ba6c6900022fa1f6458d200045f438c8b1a4000ab581191634800b17d0fba2c6900022f6077458d200061fa86e8b1a4000c3d50dd1634800b17d09bb2a6900022f6137654d200043ec2ceca9a40008bf845d9534800b17908bb2a6900023de057654d200147a40aeca9a400687e859d943480010fb0b3b286900022fe117650d2000657210eca1a40048be87d91434800b1b90eb1a86901a32b1db64509200256741eca99240048ec87595324806b55908b2a64903e39314d654c9201ae56326e899240019e880dd13248001b5481ba264900063b219744c92000cf4402e89924067aae86d9132480d1958edb2264901a36a1c3644c920336563b0c89924000ba58119132480cdb50e03226490186d3a17634c92000746326c69924035e8c6450d32480033d101b8a64900067aa1f704c9200045fc22ebb0a40058bc845d7614800156b03ba6c290002ad60474d85200045fc22e7b0a40058bc845cf61480d11790dba2c2900022fa1f64585200045f438c8b0a40f7caf72191614800b17d09bb2a2900022f61376545200143e43acaa8a4002a7481595514800195e433b682900032b48676d05200061fa84eda0a4000c3d509db4148001974213b682900032e44276d05200045fc3acba0a40058bc87597414805d47d0bb1e82900028f61763d05200045fc3ac7a0a40058bc8758f41480575590c99682900d72b1d932d052015dd440265a0a400687e851d941480010fb0a3b282900162f21076505200246f418eca0a40008dd831d9414800195c843b282900032e90076505200145f43ec8a0a4002ab681d9141480051790eb228290016ab2194250520006563b284a0a40008be869d9414800196cc33b28290002ad60676505200065ac0ceca0a4000cb6219d9414800196a433b282900030fd4276505200061ea84eca0a4000cb7109d9414800156f02bb282900aa8fa1476505200051ec28eca0a4029a9e831d9414800153b063b282900030fa1476505200061ec28eca0a4000c9e831d9414800193b063b282900032ba08765052000656c10eca0a4000cae321d9414800b17f023b282900032da04765052002c5ec08eca0a4000cb5811d9414800195e423b282900032d884765052000656908e
  | 5 => 0x8002d6e0d71541300cdac41ae2a826000d5b735c5504c1fd4f50fb0aa0982329e21f615413000d3cc1ec2a8260fde5b32d85504c001cb265b0aa0983af9c8c761541307ef3898ec2a82600097b87585504c0252f10eb0aa09815ad6e0d61541301771dbb682a82602ee3876d05504c117e3507a0aa0981c7c660f41541300078db9e82a82608bf1873d05504c057c76c7a0aa0980afc6d8f415413045f8d99682a826000f1932d05504c04f67303a0aa0981bf8ed87415413037f8d98e82a826019b5a83505504c113e3486a0aa098003c650d41541301571dbb282a82602ae3876505504c113e3506a0aa098003c660d41541300078db9a82a826089f1873505504c04fc76c6a0aa09809fc6d8d415413044f8d99282a826000f1932505504c05767702a0aa0981c7cce05415413037f1db0a82a82606ff1b31505504c0dfe6442a0aa09800356e1d3154130005ad43a62a826000b58874c5504c001ab10e98aa098006d6a19315413000dac43262a826000b5b844c5504c0016b30898aa098002d6e0931541302adadc0a62a826019f53814c5504c0dfea4e298aa098003d45c53154130007a9b0a62a82606ff50614c5504c0dfe368298aa0981bfc650531541300cdad41a42a826000b5983485504c001e926490aa098003cc505215413002c5f43ee8b2a40008bd81dd1654800187ea1ba2ca900030f543745952006c5ec38c3b224000a3e85187644800147b0a30ec890002a7a0c61d91200054ec18c3b224000cb571187644800147d0bb9ec8900028f61773d912035d57410e7b224068aad821cf644800117d0e29ec8900022f61c53d912035d57410a7b224000aad8214f644800156d0229ec890002ad60453d91203455d400a7b224000ab98014f644800196ee338ec8900030fd4171d91200061ea82e3b224000a3e851c7644800147b0a38ec890002a7a0c71d91200054ec18e3b22406baae821c764480d155b0438ec8901a2aea0071d912035d5cc00e3b2240008be87947644800117b0f28ec8900022fa1c51d91200045ec38a3b224000a9e83147644800153b0628ec8901aeaba0851d912000556c10a3b224068aba8014764480015730028ec8900022fa1e31d91200045ec3c63b2240008be870c7644800117b0e18ec8900028fa1431d91200051ec2863b22406baae820c7644800155b0418ec8901a2aea0031d91200055cc0063b2240028bc84dc5644800117b0f328c8903f2ab60a65191207dd5cc04ca32240008bf8759464481f555b05318c89000369c857119120006d9082e23224000cb6865c4644800196ecab88c8900032d99571191200065ab2ae23224000cb4655c4644800196cc6b88c8900032d18d7119120006d3412e23224000da5825c4644810596ec4b88c890003698c97119120006d9402e23224000db1805c46
  | 6 => 0x4656316e4a0a8000daa20dc94150001d4c43b1282a000aad21f61505400055ac16c2a0a8005ab780d85415000b56b01b0a82a0413ac1c361505408271ba86c2a0a8104e3550d854150209d6441b0a82a000aaea1b705054000759b0ee0a0a800687e859d931500010fb0b3b262a00062f219744c54000cdc402e898a80018bc865d1215000196ceca0a42a0012676137250d3001c6e41aebb126005c9e7450f624c0070fd0fb2aa4980127360b744c93000c6e432e89926003ace82d91324c207d1885b22649800e3721d644c9301b72632aa499260008bf845cb614c00b17908b96c29800a1f21d655453015d4e43265a0a60028be87d91414c0051790eb228298016a721943505300055ac0ceca0a6000a3f855d9414c0554790abb28298002abe09765053014556412eca0a6000ab7815d9414c00156f02b2a829800aad205655053013d4e432e6a0a6000b97815cd414c04f5390c99282982e3171db754c5305b62e3b0ea98a6000b59801d5314c001caca3b2a629800a3721d654c53000c6e432e898a600099d84dc9314c001caacaa8a6298006372197348530147533128290a6000f8532505214c0e3e34a8a1aa098003c655143541300363c3b2a4a826004cd8764c9504c0e1e94a4992a098003d2549325413000cbcc2ee2a826006a7a85d85504c05b970eda0aa0980a72e1d9415413037fa928a62a826000f51514c5504c0336b107ba2a0980029ee1974541300cd3c432e8a826000b5b835d1504c0336b106ba2a09840b8e19164541303c5adc1ac8a826093b5a87dcd504c033ab50fb9aa098006d6a1b735413000dac436e6a826019d5a76dcd504c033ab0edb9aa098002d66137354130005acc16e6a826000b5981dcd504c0016b50ea1aa098002d621d435413000dad43286a826001b588650d504c0f36b708a1aa098067c6e11435413038f8d3a286a826000f197450d504c001e36c8a1aa0981c7c61914354130005adc1286a826101f1a4250d504c0e3e3084a1aa098002d6e05435413038f8da0a86a82608fc7876dc9504c0336b107b92a0980029ee1972541300cd3c432e4a82600ec78765c9504c00167708b92a0981c6ce2117254130005adc1ae4a826019b58835c9504c00167708b12a0981c6ce211625413031dadc1ac4a826100e6862589504c0014f70ca12a0980029e21942541300cdad41a84a826000b5a874c9504c0016b10e992a098006d6a19325413000dac43264a826036e5b764c9504c033cb0ec992a098002d6e113254130005acc2264a826062b5b824c9504c033e9704992a0981c3d29c93254130007a4b9264a826000f4b624c9504c0e1e90c4992a0983ffd2d093254130387a421264a826000b5b814c9504c0e1e9642992a098066d620f7154130006adb9ee2a826000a7b865c5504c0334f10cb8aa09
  | 7 => 0x3f76d91415402f2790eb2282a8002cee0164505500bc9ec26e6a0aa01793c8750d415402f27b09b9282a805e4f21d42505500c69639284a0aa000b3b80509415404f67100a1282a8002ce60376505500061fbb4eca0aa000b35819d9415400163f06bb282a8226c720d765055000597c12eca0aa088b2c825d9415400166f02bb282a8002cee0176505500051fc32e6a0aa000a3c865cd415400166f02b9a82a84178718d63505500059bc0ac6a0aa017b348158d415400167700b1a82a82234b1c972505500059bc0ae4a0aa000b3b805c9415404f67100b9282a80024fe1d62505500049e43ac4a0aa000b3b8058941540012f301bb262a80031e9c3764c5500061fa0eec98aa000c3d41dd931540018f301bb262a80031e8c3764c5500063d086ec98aa00087e869d931540012f700bb262a806a4fa10764c5500049ec20ec98aa01896e821d931540012db043b262a80030fa10764c5500061ec20ec98aa000c5e831d931540018bb063b262a80031ba08764c55000636c10ec98aa000c5f321d931540018ed023b262a80031d604764c5500061fa08ec98aa000c3d411d931540018bc623b262a8003170c4764c5500343fc00ec98aa000c7a801d9315400d0fb003b262a80031e600764c5500062f980ec98aa000c7a301d931540018ba603b262a80031e4c0764c5500063b880ec98aa000c7a101d931540018ea203b262a80031e440764c55000cbd406e898aa00097980dd131540010ff0cba262a80021f219744c5500bcae43ac698aa000c5c7658d31540016b700b1a62a806a4fa13724c5500049ec26e498aa00197a80dc931540012f301b9262a805e5721d324c5500062e3b26498aa017b54814c931540332e90eb0a62a80039558d614c550005b9c02c298aa026a78865c131540018f0ecb8262a80025e60376485500049fc22ec90aa01a93c845d921540012bf06bb242a80665720d7648550004bdc02ec90aa00097b805d121540032f100ba242a80021fe1973485500043e432e690aa01796c8758921540016d700b1242a805e5b21d32485500c4ba43a8290aa01ad37875052154035a690ea0a42a8003c9e094148550447924128290aa017d3772505215402fe4ee4a0a42a8223c9989414855000792b128290aa088f26325052154001e4a64a0a42a82834ddc141485500df1bb028290aa0a2f33605052154141e6460a0a42a8283c9c8141485503445fc22e5b1a80048bc845cb63500071dd05bb2a6a00023b60b7654d400245e43acaa1a80668be86dc943500070f90eb2aa4a001a3ba1f625494000c5e432e89928041e8c6250d32500091dd0fb1264a000a2f21175d85400145e422e7b0a802b8bc8750f61500d117f08b96c2a000a2f21172d854015c5e43a85b0a80028bc87595415000156f02b2a82a019a2fa1b72505401
  | 8 => 0xc4a0a42a8223c9949414855000792a928290aa000a3d8690b6454001a76c9b82c8a842f4e1937059150004bcc1ee0b22a10bd3b43dc164540012f303b82c8a842f4ed0770591504ccbdc02e9b1aa001978805d3635400127f08b96c6a806a4f21172d8d504bcbdc02e5b1aa001978805cb635412d2f700b8ec6a80065e20171d8d50005acc0463b1aa019a5e86d8d63540018b8c7b92c6a842b9618f7058d50034bdc1ee0b1aa00697983dc16354001ab6c7b82c6a842b5618f7058d50004bcc0ee0b1aa10ad5b31dc163540012f301bb286a80025ee017650d500cc9e43ac8a1aa000b3b80591435403327b09b9286a80621f61f64d89500c43ec38c7b12a000a3d8418f62540018bae631ec4a80029d60463d89500d49f43ee8b12a00093d81dd16254001a76c1ba2c4a80034e8c374589500069d086e8b12a01ac3c74d9162540310f90eb22c4a80028f61063589500c537410c6b12a000a758118d62540032f101b8ac4a80034edd370589500069c3a6e0b12a00097983dc16254001ad6c5b82c4a84275a18b705895084eb5196e0b12a00097981dc16254213ad643b82c4a80025e6037650950004bdc02eca12a00197880dcd425405727909b8a84a80065e203715095000cbd43ee0a12a00697a86dc1425400d2f10db8284a80025e60f7050950004bcc0ee0a12a108d3b41dc142540012f301bb264a80024fe11764c9500d49e422ec992a000c5c635d932540012ef02bb264a805e5d205764c950004bdc02ec992a01996d82dd132540012f700ba264a80065e201744c9500c4af43ec6992a01895c8750d3254123e1884a1a64a80665b21d624c95047596422c4992a000e4c6358932540016d700b1264a82665ee0174d855000cbc402e9b0aa09897b805cf61540032f100b9ec2a805e1f61f63d85500043fc3ac7b0aa019c5c7358f615400127f08b96c2a806a4f21172d85504bcbdc02e5b0aa001978805cb615402f0fb0fb16c2a80065e20373585500ccaf43ee6b0aa000d1f41dcd6154001a3a83b9ac2a800356e037358550006ac406e6b0aa000d5b60dcd6154001ab421b9ac2a800317dd873585500043f43ec6b0aa019c5c73d8d6154001cac63b1ac2a805e1f21d63585500ce2e39ac6b0aa000c5c73d89615402f0f90eb12c2a8003171cd62585500bd3a40ac4b0aa000d5b73dc16154001ab0e7b82c2a80065ea1b705855000cbc436e0b0aa00097983dc1615400d2f703b82c2a801a5e6077058550006b9b0ee0b0aa107d7061dc1615420fa7683b82c2a841f4e507705855083eb918ee0b0aa106e1c6358f415400167700b1e82a80024fe1d62d05500d49e43ac5a0aa000b3b8058b41540012f301bb282a800257e0d76505500ccae41aeca0aa00096f825d941540312d904bb282a80025ee0176505500bc9f43ec8a0aa000c
  | 9 => 0x3250521005d3c0264a0a42a1f87304c9414845174905b82829080369dcb70505211455a432e0a0a4200ba7825c1414845174904b82829080369dc970505210043fc2ae7b02420687c855cf604840b96ce8a0ec090c332de1d41d81213fe5a43a83b024202cb57250760485edd4c64a0ec090803a94c941d81215075910283b0242219b48750560484a9b4ee4a0ac0908764f6137250f5015c9e426e2a16a01d96d82dd132d40392b90ea1a65a827fc3109434cb500dc9ec26e6a0ea01b93c8750d41d403727b09b9283a806e4f21d42507500e69639284a0ea000a3f865cd41d40554790cb9a83a8002cde0573507504d696392e4a0ea000b37815c941d400187e83bb263a80030f507764c7500062f986ec98ea000c5d30dd931d40018ee21bb263a80031d443764c7500043fc32e898ea00687c865d131d403d27d09b9263a80024f613724c7500dcae43a6498ea036c5c764c931d40376a90299263a80021fe1973487500343e432e690ea01b96c874c921d40392e90ea0a43a807b4de1d41487500f69a43a8290ea000f278250521d4135e4904a0a43a806f4ddc941487500df93b928290ea09af266250521d4145e4ac4a0a43a826bc98c94148750007929928290ea0a0d377050521d402fc6ac0a0a43a8283c9c8141487500051ec2c85b22a0008bf845cb635400b17908b96c6a801297a1b6354d506b62e31ee4a9aa00187e86dd543540030f90cbaa86a801a4f21d5450d5001c3e42ae7b12a01ac3c74d9152540030fd0dbaa84a80061f219755095000cbc402eaa12a0068fa86dc142540030fd0dbaa64a80625760f754c95000c3e432ea992a03dc5c635d532540071bd0fb1a64a801a5b21d524c9501ef2631aa4992a0b787f8754f61540098b8e6a9ec2a80022fe1172d855002c5e422e5b0aa000d5a30dcd515416d0fd0fb1aa2a8067171cf63545500072b18ec6a8aa02ba3d85d8f41540574790ca9e82a80b78718d53d055015d1ec2ec5a0aa02ba3c8654b41540030fd0dbaa82a805e4f613755055000c3e432eaa0aa0028be87d91415404f47b0bb2282a80030fdd764505500349e43aa8a0aa005a3c86551415400156b033b282a8002a7e0d765055014d4e41aeca0aa000aaf825d9415405155904bb282a809e8fa1b75505500061f3b6eaa0aa027a3c865d5415400166f02baa82a809e8f617635055013d1e432a6a0aa029e1c6354d415400166f02a9a82a805ecd205535055013d1ec2ec4a0aa027a3c86549415400d0f90a3b262a80162fa10764c5500045ec20ec98aa000c5e531d931540071dd043b262a80023b608764c5500063b288ec98aa00187e86dd531540032f501baa62a80061f219754c550034ae43aa698aa000c5c7654d315400d2e90ea8a62a80061fa1b754855000c3e432ea90aa00696c875492154051d4c
  | 10 => 0xa126236c5c65dd5324c4053a903baa649880355947754c9310146e432ea99262029d4815d5324c56f4bd0db2a6498ae3171db654c9315c6aa38eca99262b6c5c76195324c56daa8e232a6498802d6600654c93101d67416c899262038dc87591324c46d4b90ab226498c4fa3109644c9310072632ec499262b0b8e84d89324c46dc98caa92649880a75a1f714c931014ea40ee099262bbc7476d95514c4056a90ea9aa2988135521d5354531015ab432a6a8a6202b548654d514c40dca90ca9aa29881b95dd95354531026ab3b2a6a8a6204d547654d514c40dca8eca9aa298802d5e095354531005abc02a6a8a6206c7476549514c4013a90e992a298813351d93254531005aac2a64a8a6200f45524c9514c401aaaa7b82a2988029e60375d81310053cc00ebb02620087f855d3604c40d0f90aba6c0988021fe1572d81310343e42ae5b0262b887c86dd5604c4010fd0fb2ac0988021fa1c65581318962fb98cab02620187c85dc1654840d0fd0fbaac6908030fd077558d210061ea0eeab1a420087d80dd563484010ff0abb2a6908021fe157650d210343e42aeca1a42008fb805d943484031f100bb286908122fa1f6450d2101cb6c2ee6a924206a6e85d8d524840d1d90eb1aa49080e7360f754c92101476432ea9924204ace83d953248623c98a7b2a64908123b21d654c9211af46322869924205cb47650d4148545e4ea8a928290803c9551525052101e723b264a0a42a1f86434c94148401f0a86992829080a6d6137050521145d2416eaa0a4200ab7865d541484515690cbaa8290802e9e097550521145d2412eaa0a4310e3665d954148621c68cab2a8290ab2e9e0965505216065a3b6e6a0a4228ba482dcd414840156f0cb9a82908a2ad219735052112e5a3b2e6a0a4200b37855cd41485456690ab9a8290802e9e097350521145d2412e6a0a4200b378558d41485456690ab1a8290c3fa518d635052152dd3c12c6a0a4200ab78654d41484015690ca9a82908a2e9a0953505215fdd343ee4a0a4228da687dc9414840574d0db92829080ae921b7250521146d33b6e4a0a4228da476dc9414840174b0bb928290802e960f7250521005d2c06e4a0a4200ba68754941484017490ea92829080ae9a195250521015d2432a4a0a42adba7855494148451e4f0aa928290a8bc99d5525052100792baaa4a0a4200f27655494148545e48caa928290802e9e0d52505218779329aa4a0a42a2f2453549414840174f00a928290a8bc9d415250521005d343a64a0a4200ba4874c9414840574d0c992829080ae921932505211af53bb264a0a4228ea4764c9414840174f0a9928290802e96153250521535d3c1a64a0a4228f87834c94148543f0ce69928290803e15cd3250521007c3b1a64a0a42a1f84634c9414861bf0ea69928290a87e114d
  | 11 => 0x5040536902b9ec0a089e2f61f63d8141634dbc0ae5b0282029b4815cb605044f17b0fb16c0a08022fe1d62d814114656392c5b028200cac72d8d605044f1790eb1ac0a08032b1c9635814113d5c402c6b0282029b481dc9605045135d0fb92c0a080369e077258141006d240ee4b028200da761dc96050401a5ea1b92c0a08034b5437258141006d3886e4b028200caf761c9605040117d0fb12c0a08a32b1cb625814100755106c4b0282278bc875896050451958e4b12c0a080369dcb7158141006d2396e2b02822687d87183654c40147d08306ca988028f61060d953100537410c1b2a6200a6d82183654c4018f2e0306ca988028fa1372d95310051ec26e5b2a62bba5e831cb654c5714bb06396ca988021fa1c42d95310043ec3885b2a62bba5e8310b654c4014bb06216ca98ae29da0442d95310053ac0885b2a6200a7a8010b654c4014f300216ca988031edc270d95310061fa0ae1b2a6200c3d415c3654c40147d08386ca988028f61070d95315dd2f418e1b2a62b8a5d831c3654c4014dd04386ca988029b60870d95315c53b408e1b2a62bba75811c3654c4010fd0f206ca988021f61e40d95310043f43881b2a620087d87103654c5774bd06206ca988029760c40d95310053741081b2a6200a6d82103654c5714ed02206ca988029d60440d95310043f43c41b2a620087d87883654c4010fd0e106ca988021f61c20d95310051f42041b2a6200a3d84083654c5774bd06106ca988029760c20d95315c53b40841b2a6200a7581083654c62f4bb07320ca98c5a9d60664195318ad2ec1cc432a6200d5b305c0654c401ae620b80ca988031ea1970195310063d322e032a6200c78645c0654c401ab506b80ca988035660d70195316763db1ae032a6200c7a625c0654c4018f0c4b80ca9880356cc97019531006b940ae032a6200d71815c0654c59b8f6c2b80ca988034ed0570195310069ca0ae032a6200d73315c0654c401ab462b80ca98803560c57019531006b818ae032a6200c7970980654c40147d08300ca988028f610601953100537410c032a6200a6d82180654c4018f2e0300ca988029e60065d91310043f43ecab22620087e87195644c4014f30032ac89881a1fa1f75591310061fa0eeab226200c3d41dd5644c4010fb01baac8988021fe15765513102c3f43ecaaa262068bc87591544c5718b8edb2aa6988030f9d365d89310061f3a0cbb1262b7c5c73197624c4014f30032ec4988030fd9574d89310061e32ae9b126314ab5819d3624c40b17f0eba6c4988b62fe0574d893114c5ec0ae9b126200c9f305d3624c40196e20ba6c4988021fa1f65589310043f438cab126200a7980195624c40b17d093b2a4988022f61276549310062f298eca92620387e87d95524c40d0fd0bbb284988021f61776509310045ec24ec
  | 12 => 0xdad321543549321aec63a286a926400f0d5450d524ca39a98a7b82a4990022fe1170d853202c5e422e1b0a640087f855c7604c80d0f90ab8ec09901637a1f6350d515c43fc2ae7b12a2b687e86dcd52544091bd07bb284a88023760f76509510143e432ea992a2038de87d8d325447bc98c6a9264a88061f21574d81515c43fc2ae7b02a20187c855cf60544370f90ea9ec0a88061f21572d81510dc3e43aa5b02a22c93d85dcd52d045933b07baa65a08b66b21d524cb416578629aa49968200a3d8494f655040517d0dba2a6a08163da1b7154d410145e432eaa1a82029b4815d54350455878ebb2a86a08122f21d6550d410043fc2ae7b12820687c855cf62504070f90eb2aa4a080a2fa1b745494102c9e43aa8a9282028bc865d542505a1958c5b9a84a080eaba1b62509410145f436e899282299ad82dd132504051790cba264a09072b189744c94102cce43a869928241e8c6250d32504091dd0fb1264a08021fe1573d81410343e42ae7b0282678bf8750b6050407958e4a16c0a08028f61a53d95410069bb2ee2b2a831bd3465dc5655040136b05b8acaa0c6f4dd4b7159541004dac06e2b2a831bd3750dc5655045317b0fb2ec6a08a62f61c62d8d410051ec28c5b1a8200cad7218b635040157300316c6a08aa4fa1f7558d410069bb0eeab1a8200d3621dd5635040127b01baac6a08034dc437558d411561e3aecab1a82298bc87595635040147b0a312c6a08a6a7a0c6258d410055cc00c4b1a8200d3775dc56350401a68ebb8ac6a080365d8f7158d418d6ca31ee2b1a82009b582dc56350635b2e65b8ac6a08026d6037158d418d6cb986e2b1a82009b581dd9535040136f02bb2a6a080a6d2077254d41014db43ee2a9a82059b686dc5535040b3690db8aa6a08026d60b7154d41004dac06e2a9a8319d3750dc5535040536903b82a6a0b226de0575d8941014da40aebb12820093f855cf62504552790ab9ec4a0b1e6de0573d8941014da40ae7b1282809b7815c3625040536902b86c4a0802e960620d894100656316e6b128228aae86d896250631d48c5b8ac4a08166de0b715894102cdac16e2b128200da762dc56250631b48c5b8ac4a08026d60371589418c6d3906e2b1282029b481dc1625040136b03bb2a4a08026de0576549411449e43acaa928200b3781595525045127b0bb9aa4a089e4f2177054941004dac0eec992820093f855d932504552790abb264a08032b189764c941004dbc0aec99282009bb805d9325044f37100bb264a08a26760f754c941004dbc0aea99282029b4815d532504513390eb1a64a0af2c7215634c94100746312c69928200b978158d325045335d0fb1264a08a66b21d524c9415ef8629aa499282c89b7815d7605040536902baec0a08024fe1573d81411549e42ae7b0282c79b7815cf60
  | 13 => 0x800200400002400e00600200800400200200800e00200000000000000000400002800000000c00800005c00400800401600a00000000401e01003000600000c01a02800e00800200600000800800000000000e00600000200001000001c02200801000200001200e00600a00002200000003000400e01600e01800801600200000201a00601200000400800200400200000800000003c0120020060040a801600000200600600c02a04600202c03000001c00600602000001a00400000a00600000c00c00002000001600c05000c01201800c00c00801000200601200000000001800a01000000001600001000000401600000201400200000000000e00000000000004000c00202800405800800200201200a00800000001400400000a00201200000802a00800000200000402000207600200a00201200001401c00000000000401a00402600200000000600001a00000a00000400400600c00600000a00000601000200200000400200000002602a00401400000e00200400a00000000002201200200600200a00200e00000600002a02000000201e00400800605c00403e00600000200200003200203e00000400200200200402801201803800201400400a00600600200000200000600200601600601a00a00002200405401200400000400c01800400c01c00203400400802401000201c00600601800000000400000400a00000004000600200200e01201201e00000000001601e01a00800600000404200200400600000800600401600000c00000400a00000200a00c01600200603600000001600000000c00600600001e00600800e00000e00200c00a02600000400000600600000a01203e00001c00002400000000600c02c00000600002802600000600000400401c00000202201200600400002800600000000400000000200602801c05801600a02200003200c00002000800a00000002201400001200400e00200800200000e00002e00201800400200000800400000000200200000000001800000200601600001200203c01400c00000200000201200e00600000000400000400000800e00000400000202200600001a00002200600000400200600000000000000002800404400000001800000000800603801400200000000a00002cbb87f855c76054c5b1790eaa6c2a18032b10972d85430043fc2ae3b02860687c855c76050c070fd0dbaa86a90122fa1f6450d520349e43aa8a1aa405a3c86551435480117f08b86c2a90162f21170d85520e43e43aa9b02a400c5c535cf60548030f90ab8ec0a91ae2fe1170d85420145e422e1b0a84038de86dcd544c8091dd0db92a8990126721d5450d3220dc6412a8a1a6441b8e84dc9434ca3db1885b8a869900e5b21d54549321eda641aa8a92651db4e85dcd524c8013990ea1aa499
  | 14 => 0x858d00000000014b4001c84ea4ba000000000ced4d60000975b9120d9c42740003d9a154d0bf928c0d00017655cc001739a0078d9a8e0141c0012382cc000000000000000bfd668000001bb5780624c6482c96948877192c7e5804d783bda240755dc6a1aa00011bd01990400000196d6e80000100000000000018b0a1c9480885e0000d71c3c000000dad645944be400169c00174514c93db20270bd0e3000061c4ac9d09a8278d147e00000011100017600006d800000182dc340011212d0000000c50e519347b036471cec9578000ca58f9c2c0000005800680000003297a400000038846c0000000009ed39d90d2b89c09c80000014613444344fcbf00005015899c0ff05594959f49780000013fd6143159d15818cc70c88d3a5bed585b1d38140d458000928000b9c00057c8a40006bc000000001628fa9bd8ce096000000000000108400103c00104c001bb800158d921498000000568c2db0cbec0003ccaa0ce86d40000016c0000000114000000000000000001ae0cb5af09d4fe40002d52a0000aa561841d3288446800000000001c0000001c00708000000f180019d96a000000195000000099ce480010900000b0868001a640006b84640015c082400062c00070438c740e15afd1d4f3d66d5e83b4d9c3991d80a49006d044d8598a88ad30866409c239870a183484a42180000006c4c74ff51181f456cab40c4c205a8b94758e95954ad4efcec0448eb4abd1d03f0c904e17d82f15a44110b1b74e0c83080420c001410491a5801c43ca6800149d2f0f41b24001b3d8ed6e4020bc869d0e0a50000000b68f798c00000009500015c40012840019404b40001ccca97c13313f4890e690382e05f55c80006994fc000f51161869748e793c116c3d00ecf28c40e4dc0c094b89420df0a597980003454ac00100490d154baccf80019600000001a000000087597083884c4401c4001770000b783347f97880000000015a8000da40140007b80000010dc000000cd9014000000e6c0014ed9757241058600006f4620000000000f380004819a07008fcf7ce99ab8251a2c4c4000000c68208e9000000155cd65818000000d88000000fe0001b4cf740000004bd6d18e8000ae962c0009f03dd5e15f91e0000e040018a00008e0c6000000000024434c00000118000127c3e5af40008d80605ac684000d41a48650000000000808d4c00000157c000001b5dbc8001c780008bc000c45010a3c8701a8660000000000e598c8001a60addb10f682b01813ac170ef80011250e80006c0000000f70ca1aed56c4cdbe46901b400000096c00600a05e03000600400a01000000400202000000600800400200000600000000805000201a01000601c00600e00002400e00401801e00604601000203601400400000c00400000803200600200600003601a
  | 15 => 0x573400000137d1511c932563cb840004e40000012900000000000000007c8001ad93f038485cad1c30d8029c000a2498db8db81a8cb5c79db68258000f14000dd8ecc001ad0000cb0001785c88001ae4000c850a4341469620658c01b6d9d4b0cc6c9acb140000011fd0f836c894000000755098000000000d100010245553d40005a1ab03185f0c3c7ad84099054578c001184000c7000019cb3d880538cdd94da782908b89bc26c00051d91d5f581c1dc001b44fadaa93b0000ab1aa59780000008d0ee8000000c0db54000534000e8072d0680003e81097c5130d2c001abc51400000121025cd314dd5043a03689a494568152435cd01ba96019001f964d7ed0ecd281b97f10f4b1c61440d1c4801b300009b13a0000bd583126994830d5605ec0018fc934000924c0559830017db2c000d8400152c00040067daace646281e0984acce7c000000000000000000001630001570001b7c0013edacd44cb98135c39454154ae00012cc450c34c540000009947a8c19b09520ba9919708eb1715bf80b55bcf84b60261b9d550c30204714cbcc49318a5d671964d591945c950960d555178a956f5bb083c200001b3567d00c0000000015444f199c210001c2400109c0000000000008605180010740004ecb4c45400156457915cec5bc03ed4254155d45b400109526c0000017ac0000009fd6e0528000780000c15475190c08fb4b8cf5c9a10fc408c7cebcc98da11ecd240000007118ac000000d382990210d9204000000000000000b20000564000000bc52985740019cc000c94000a34645b853040188d54192e0679a81990d5d6557cd0f0bdcf1065c3fc1400011989e4188185218174001135b88e842ed1ad0a93e8edd9e5c7413828cf60cecdecc11a18311b942a40000000016f00811f9814000000000001175248d6c7989312450708f153c0fc1d9a99398dd4ac43c4654afd5587a494c61995c0017694e439c1640019b41bcd180000292c833d8513b58d86c80011440008e80014c19881ec00042959c00000090400000000011c001379b000000000007280011f533c7d8000d9400121d391568000000e5c0001b0001bf0be0001779c48f8db40aec001690c9d8f1bd00000008100000000016394c884039457189ce70268001a3047c2401947bc00000025585d9998c4a7d350df40016999dc000000e88550231c957d0a744c1c198a4a0ce082b4a409e854c128070b8072535c5e8001301310001984ba49200011e4a6d8880010299385b844408d54cc582acb34a4415d08da2046818d8dd2ac880eb8bd8f1d91400000165c8dd2dc914ab92e88f47212582a113d604359909b05c280000014a4000ef048c0004a8694fbd9284f504174003800161d835374638000000bf4000001c1c00117c37cf9800097c908000001358dc52ec0000005
  | 16 => 0x288fd52352300000000018e09c50d55b94f0b443c1bfc000145530c78c293f923c3c8bb4a1512853c000000af5c6d1b1bf5a1143cde0821704850cf4748f89260fc4848f9d7504056514656bc280f9414cd985bc000000fa14e14f4001c4ca4c0004840004e88a06897bd47842d4a80017a0000f58d554cc000000001228e18119c69a6c3a4ddca04e3ca280016754040006705200000010c5c7c81d1c00003b0cfc7b593ca2ca80879c6400076c000ad9c917e54317940006cc14800549138412c9587f5c5c858000db4000000000000000000000d68000001058d3c0f9274000a8566180c00000000132cde51e9c5423c0001244580014d8000b24000001a7c00094074cf2d2e5820000590000414a995005c1c443907752a910c3ad9ac0003f4a6147db181916a8b3910413d8b80015a13d86dc508a799bc26537107c000f20000000dc80016102e8b7000142c0005940012800016fc000ea86a400091c2240c0e9c2a8000248e44000fccb2d5b4a48324ee00011692bc0000a0b10ff827d2d8784ae500936883415106c0f03b858d1897d59a40000d40017e01ada503a96586b40b8a00000fa57c8000d7c0014e8fb924000048878983c058000035078000a90098424a8c7c1bbd109be13cc49459880c0000e489d980430000a206f00005fc980ce4001a85a34000df80017907348e5641b700e16088890ac0000016ad6b000168cbc04d9278001101a90a08024fb02e5b510d15185a4000001800dccf540018f4e1c00104901c64d549ae8d8db9832c50c0003780000017316b534049dba536d4296951b863da3800007da3d84c000001a706303f8e5477887d5e4d50000aa81988290640000000000d9b492551cd8b5ad53a80002280646fc00068cbb12c05d40002c000000122d02c0000009dd7dd3c96c4001894cf0eecf48000000169b58b040000016d80000013c5139a0d86d4b138d54002d48073c000fc11a0001924588dfd270000000de98480002c800120822c00131d2f53bd03438000029400177dbcc898d440002bc00174d4a03095f00485b0648000e60ed08f800000060d29d2fd19c32186400000146c8c8001ab40007d4054000dbd634000d495d0000000aac10151c2b8a38001a74000cc4ed9898918f642148ec6109b58757e9a0518d15914847540800000075ce395104b1af8000000d90fd1c50000d094397f50b881573c5492b4041251ac9b788cc45da692657545dcc39bc452c4d13e4361c5997d9587396d575d3613b84980cd7212a49cd5eda1d930a30dd0bccb559e0db1031689c606354d4001a9cc800017b005c938000ea07500007f14f8e2c2c5a287d15358781200018850b53393e0b7dac0f80b197a80000446e4b587dd529140cad6ecb6ccc0001a45bdd79c001838000000d0c00000191171c001c048c40017b
  | 17 => 0x14440000019ec4a12001e54b8e291640009f83041d1759bd43e0000000000cd0af05e4001700d7539587c674000fe80000006ac0bc000e400000005f945d2b11b5c980005602fc9d80010005d08654019c8050608370a89844b41a4c6eca9c3d55adb380000011f0dc0000000c5c2d80012940ad2f94c47cc000000b000dc7e9a4021c0001fd224bbd349c080000010c0221710000668c4c92c7440016b80003500013215380007956c80000000001a55fc338000d340010e5054910da98287180018d5590000000000000000b30000510000ee530c59cb293d16798bc0842d1774d054846a8999448cc9c8d808f0cccd12c9f42f84190cd76c03d48c06cb080019b0a54b48ffdc10ac8fc8f04ac170c4b86b01e8cd55d9ba013172c7c4000000f91334000f01bad855c140000000018e40000091a9574001824d1c000db8ef4c88f6c00000098816caf85c400000000117000007855d060e243319f08a9b61add2c55156f80011dc965b6411125c7fd9690c84dc7319f8000fdd6cc8559b9c8121598d088438a70524f4511400095c5d9729a957184600000008b44c9a080009b8c8cfd83549e031ca65435a5cd2076004c0a810c6e07914bd8917f96481c90a0530e20160001c416641f1a89c20884e8c2f477cead45105d440e34fed34d388284001b28c1d0bcf34479470b747a0600764e1086d7fca104f86f9044b90090f242896a4f3131588d994000640000970f4c000bb80008c1220000cb8b658108191a56253645cc0c90815b10503742dd11d9fc7686e9b140f59e93dc000f0800066d6dc9540000001582352d48b0e75a556853547ec1786044d40e8be824dc71be97b8c2550c1d454003000124c471ac5594504b50420000000001
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x241c3360541711912000469660205c464480014a69608171191200056164c205c46448001d215008171191200046c660205c464480014b29608171191200060da15711846448001835855c4611912000625a0d711846448001895835c461191200040f6627519363481f7439909d464d8d200060d9d58119363480018357560464d8d20006291d98119132480019a070604644c92000683a1464d8d324800168591193634c92000728485109db414800181d8560c76505206ce29606321d941480018368560476505200060d615811d941480018968360476505200062560d811d941480018a58260476505200062660d801d941480018a98260076505200062c605801d9414803d83581d4076505200d60d605501d941480014a59188076505200042b660201d9414800148d93080765052000529644201d94148001c295008076505200070cd41101d94148001ca12144076505200062a200764c941480010b6981d9615052000629e087658541480518a8865c970505200050d64464dd53148001439901d7644c520006291d9811912148001625952194148520005a164c86505214800162595d8d4148520145a82598050521480031a897611325012020f221d9434c94048001b1150e0d655051002c2da638758941440018a487e0962505101ad2925d624c941440013339560f70505100061c1d9801d5314400945497595534c51000495654864c9314404f53097615415411013d4c65773505504404f53195dc94154110006c850782591504400d07a98e1d63541100061621f8358d504406d4589758d3254110004cce5182dc5504402f330985d141541100bccc65383505504402f33194e0941541100064ce1e8750550440016339661d4154110005c4e4d8750550441d37109361d4154110005c8e498750550441d17209261d41541100054ce5d8350550440015309760d41541100058ce5973505504402f630965cd41541108ff441cd7350550440015339758d41541102854c25d63505504400163396609415411013d8c2598250550441d1b20826094154110004cce61725055044001330985c94154110004cce6162505504409b330985894154110004cc650874c550440013619221d315411000654e0c874c550440011709761131541100bcd4261734c55044001950875cd3154110004cc653824c550440032709661121541100bcd82617248550440054b0965d5414c11013d6425d83505304400139194e09314c1100062c1d9811d120440074a8975914248110004aa650864c920440019a37221d41481100054c6548750520440015919321d41481100046c26175505204400153195dcd414811013d6825d8250520440019a087609414811001534259734c520440016c0964c9314811000cb825983485204400156195dcd2148110
  | 1 => 0x25000008a24640a400d52c9580062068000100000000203000020e008040000000081001000140001008180400000040002000040600000200001000040004000040405020000604010001200008000002038040204008200000018080c0000000000000529644425cb6150c014a99010972d854300515644535cf60548014599014d73d81521ecc32615450d524c88350c9755143549320062a5c98018b63504014a99018b73589410052a640625d932504018a880189764c941005836546258d325040168990189634c9410062a2007258d60504018aa8788362581410051664e645c0654c40147191991701953100516a5a835c0654c4014599398970195310065460d815c0654c643c3361505701953100456660315c0654c40145a960c5701953100552648315c0654c401d11410c570195310045c660315c0654c401472960c570195310060ea1170180654c401839845c060195310061aa0970180654c401869825c060195310040f66274197624c62d435919d065d89310060e9d180197624c4014399019574d8931006161d980195324c40195071600654c93100683a1065d89324c40164990197624c9310145525d854c9514c47bc4476549325453120f211d9434c941484013279560f7250521144c926175549414845132595e0d5250521144e164f854c941484052a4966153250521144e1261734c94148627c84765cd325052186dc1255734c941484518a486dc97050521007144c110dd931d40014559118f7258d50006155cd8118f62540014559118d764c95000615204635d9325400160d9418d624c95000591644635893254001856878c763585500061520473589615400182d84608764c5506f616603321d9315400185583604764c55000619609811d9315405d83980d04764c5501560e601411d93154001459908c4764c55000417660311d9315400144d920c4764c55000705504311d93154001459900c4764c5500060ea11801d9315400183984600764c5500061660d801d9315400186a82600764c5500061a609801d9315400187181600764c550007144c1101d93154001c3341440764c55000615204764c931540338548758d614c5500041ea60765c1315400185b831d9704c550005c8e4162505215400185876600754c5301ef121d9524c9504c00131b9460b73541300ccc62617450d504c03331994e0943541300ccd264b844c9504c0032589661132541300ccd2261724c9504c1f1c48765c932541307fdc2251724c9504c03385886dcd7154130005c4e4583505504c0013199421d3154130004d2648874c5504c00131994e0931541300ccd4261714c5504c001f013250521541300052964a655c464480014b19099571191200052964a635c464480014a696a09711912000668609805c46448
  | 2 => 0x120d423001f00000631516e0000000c000001b400003b17c320003810a0735e3588ed716801760000000f400000000000000c000b60023186cf0006c0000001700000110000000000f00000508015a8f289b800000000000b000000ca82000000000000013600003105c0000278000018b4000000015400345c80074000004800002500198000000000000000150280025c263700000207f591c800420189956ca500ec00004d148ea41258000000048010000059697a0003000000026801020061000f2a4000016a00000009c00000000000060018200002a40000000000058668012a005a000d83d64805068800000d200000d8001d1527c00da160000000000000000002e80000002880000040000000000000000000000000001f4003f688000000000000000380085ea30000130d20005db232001ac009369800005e4e000000e1ca74008d0000080000f80000150000000db6280000004a3717c006380098b145264e8840000000aa2b80066200000000ae428e1ba00002bc001a00338000000174381133000000a001ec00002180028000000000003f2cda8000000092bf158008cac490003000659848800438000071318000035298012c000f1e14a8b000001e0000000c8000000000865c13c00000029cb6680b00000d810a4000c037a9800001f000008e448000000000144e7733a440000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x20148189aeb047aa41a88002800071648a3003881a43b8211802000622330a0862b80ca9880350192504315c0654c401418d0ce8c00cbb1262008546a471600654c93100441b53420cbb126498c5aa05a1a1065d89324c4019054232032ec49926200c05661410c4764c55000680b24a08623b262a800341141640311d9315400102ad49023b26498aa000a14680811d9324c55000624330a8040b88c89000350193540205c46448001418d04eac08c9b1a40008686a470604644c92000441b53428c9b1a64903eea09a0a1464d8d324800190342b22326c69924000c0a66150080765052000681326a80403b2829000342191540201d94148001054d49003b264a0a4000a28684801d93250520
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x200005201b1a1190197624c931005201b0a1591193634c920
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
  | 27 => 0x198a
  | 28 => 0x198b
  | 29 => 0x198c
  | 30 => 0x198d
  | 31 => 0xb09
  | 32 => 0xb0c
  | 33 => 0xb0d
  | 34 => 0xb0e
  | 35 => 0xb49
  | 36 => 0xb4b
  | 37 => 0xb4d
  | 38 => 0xb4e
  | 39 => 0xb89
  | 40 => 0xb8b
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x1849
  | 44 => 0x184b
  | 45 => 0x184c
  | 46 => 0x184e
  | 47 => 0xbc9
  | 48 => 0xbcb
  | 49 => 0xbcc
  | 50 => 0xbcd
  | 51 => 0xcc9
  | 52 => 0xcca
  | 53 => 0xccd
  | 54 => 0xcce
  | 55 => 0xd09
  | 56 => 0xd0a
  | 57 => 0xd0c
  | 58 => 0xd0e
  | 59 => 0xd49
  | 60 => 0xd4a
  | 61 => 0xd4c
  | 62 => 0xd4d
  | 63 => 0xe89
  | 64 => 0xe8a
  | 65 => 0xe8b
  | 66 => 0xe8e
  | 67 => 0xec9
  | 68 => 0xeca
  | 69 => 0xecb
  | 70 => 0xecd
  | 71 => 0x1049
  | 72 => 0x104a
  | 73 => 0x104b
  | 74 => 0x104c
  | 75 => 0xa4953
  | 76 => 0xa4954
  | 77 => 0xa4955
  | 78 => 0xb8953
  | 79 => 0xb8954
  | 80 => 0xb8956
  | 81 => 0x1549
  | 82 => 0x1409
  | 83 => 0x150a
  | 84 => 0x128a
  | 85 => 0x16c9
  | 86 => 0x1449
  | 87 => 0x168a
  | 88 => 0x12ca
  | 89 => 0x1489
  | 90 => 0x180a
  | 91 => 0x130a
  | 92 => 0x19c9
  | 93 => 0x14c9
  | 94 => 0x134a
  | 95 => 0x138b
  | 96 => 0x124b
  | 97 => 0xcc996
  | 98 => 0x1709
  | 99 => 0x15c9
  | 100 => 0x168b
  | 101 => 0x12cb
  | 102 => 0x409
  | 103 => 0x10b
  | 104 => 0x1609
  | 105 => 0x1889
  | 106 => 0x180b
  | 107 => 0x130b
  | 108 => 0x1a09
  | 109 => 0x1649
  | 110 => 0x134b
  | 111 => 0xa49d2
  | 112 => 0xa49d3
  | 113 => 0xa49d5
  | 114 => 0x138c
  | 115 => 0x124c
  | 116 => 0xcc9d5
  | 117 => 0x150c
  | 118 => 0x128c
  | 119 => 0xe89d3
  | 120 => 0x18c9
  | 121 => 0x1789
  | 122 => 0x180c
  | 123 => 0x130c
  | 124 => 0x1a49
  | 125 => 0x17c9
  | 126 => 0x134c
  | 127 => 0x138d
  | 128 => 0x124d
  | 129 => 0x150d
  | 130 => 0x128d
  | 131 => 0x168d
  | 132 => 0x12cd
  | 133 => 0x1a89
  | 134 => 0x1949
  | 135 => 0x134d
  | 136 => 0xb8a53
  | 137 => 0xb8a54
  | 138 => 0x184a53
  | 139 => 0x184a54
  | 140 => 0x124e
  | 141 => 0x2c9
  | 142 => 0xcca55
  | 143 => 0x128e
  | 144 => 0x449
  | 145 => 0xe8a53
  | 146 => 0x12ce
  | 147 => 0x5c9
  | 148 => 0x130e
  | 149 => 0x749
  | 150 => 0x138e
  | 151 => 0x150e
  | 152 => 0x168e
  | 153 => 0x180e
  | 154 => 0xb9993
  | 155 => 0xb9994
  | 156 => 0x185993
  | 157 => 0x185994
  | 158 => 0xcd995
  | 159 => 0xe9993
  | 160 => 0xb8b11
  | 161 => 0xb8b14
  | 162 => 0xb8b16
  | 163 => 0xccb16
  | 164 => 0xd4b14
  | 165 => 0x170a
  | 166 => 0x15ca
  | 167 => 0x16cb
  | 168 => 0x144b
  | 169 => 0x188a
  | 170 => 0x160a
  | 171 => 0x148b
  | 172 => 0x1a0a
  | 173 => 0x164a
  | 174 => 0x19cb
  | 175 => 0x14cb
  | 176 => 0xccb55
  | 177 => 0x154c
  | 178 => 0x140c
  | 179 => 0x18ca
  | 180 => 0x178a
  | 181 => 0x148c
  | 182 => 0x5ca
  | 183 => 0x2cc
  | 184 => 0x17ca
  | 185 => 0x1a4a
  | 186 => 0x19cc
  | 187 => 0x14cc
  | 188 => 0xccb96
  | 189 => 0xd4b94
  | 190 => 0x140d
  | 191 => 0x40a
  | 192 => 0x144d
  | 193 => 0x58a
  | 194 => 0x194a
  | 195 => 0x1a8a
  | 196 => 0x14cd
  | 197 => 0x74a
  | 198 => 0x154d
  | 199 => 0x16cd
  | 200 => 0x19cd
  | 201 => 0xcd856
  | 202 => 0xd5854
  | 203 => 0x154e
  | 204 => 0x140e
  | 205 => 0x16ce
  | 206 => 0x144e
  | 207 => 0x148e
  | 208 => 0x18cb
  | 209 => 0x178b
  | 210 => 0x188c
  | 211 => 0x160c
  | 212 => 0x1a4b
  | 213 => 0x17cb
  | 214 => 0x1a0c
  | 215 => 0x164c
  | 216 => 0x170d
  | 217 => 0x15cd
  | 218 => 0x1a8b
  | 219 => 0x194b
  | 220 => 0x1a0d
  | 221 => 0x164d
  | 222 => 0x170e
  | 223 => 0x15ce
  | 224 => 0x188e
  | 225 => 0x160e
  | 226 => 0x1a8c
  | 227 => 0x194c
  | 228 => 0x1a4d
  | 229 => 0x17cd
  | 230 => 0x18ce
  | 231 => 0x178e
  | 232 => 0xb8a495b
  | 233 => 0xb8a495c
  | 234 => 0x94a53
  | 235 => 0x9ca52
  | 236 => 0x94a54
  | 237 => 0x12ca52
  | 238 => 0xce
  | 239 => 0x94a55
  | 240 => 0xb0b91
  | 241 => 0x94b93
  | 242 => 0x140b91
  | 243 => 0x20d
  | 244 => 0x94b94
  | 245 => 0x94b96
  | 246 => 0xb9393
  | 247 => 0x41411
  | 248 => 0x98cd6
  | 249 => 0x12ca53
  | 250 => 0x40cd1
  | 251 => 0x10a53
  | 252 => 0x40d51
  | 253 => 0x124a54
  | 254 => 0x4e
  | 255 => 0xcca49dd
  | 256 => 0x9ca53
  | 257 => 0xe8a49db
  | 258 => 0x9ca55
  | 259 => 0x9ccd5
  | 260 => 0x184b91
  | 261 => 0xa4b94
  | 262 => 0xa5854
  | 263 => 0x198a52
  | 264 => 0x150a55
  | 265 => 0x198a53
  | 266 => 0x198a54
  | 267 => 0x198a55
  | 268 => 0x4d
  | 269 => 0xccb8b1e
  | 270 => 0xd4b8b1c
  | 271 => 0xb0b94
  | 272 => 0xb0b96
  | 273 => 0xb0cd6
  | 274 => 0x5d2d2
  | 275 => 0xb4cd5
  | 276 => 0x140b94
  | 277 => 0x5ccd2
  | 278 => 0x2cb94
  | 279 => 0x5ce92
  | 280 => 0x184b93
  | 281 => 0x16cb96
  | 282 => 0x184b94
  | 283 => 0x184b96
  | 284 => 0x150cd6
  | 285 => 0x5cb
  | 286 => 0x16ccd5
  | 287 => 0xa4b895c
  | 288 => 0xa5515
  | 289 => 0xb96d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1694
  | 6 => 5561
  | 5 => 1831
  | 4 => 222
  | 3 => 24
  | 2 => 2
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (68882+((h/564+packedAt gbK7 (62678+(h % 564)*11) 11) % 2033)*12) 12
  | 6 => packedAt gbK6 (291017+((h/1853+packedAt gbK6 (266928+(h % 1853)*13) 13) % 7341)*14) 14
  | 5 => packedAt gbK5 (115349+((h/610+packedAt gbK5 (108029+(h % 610)*12) 12) % 2417)*12) 12
  | 4 => packedAt gbK4 (16206+((h/74+packedAt gbK4 (15540+(h % 74)*9) 9) % 469)*9) 9
  | 3 => packedAt gbK3 (1984+((h/8+packedAt gbK3 (1944+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt gbK2 (186+((h/1+packedAt gbK2 (184+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7388e063f00c63c703fe3f0fe1fc0c8e0474cf
  | 1 => 0x8c0f007c7ff07c780383c7f0fe1c30139a4b33
  | 2 => 0xff0007f807f807ffc03f800ffe0c31c638c3c
  | 3 => 0xfffff80007fff800003ffff000303e07c0fc0
  | 4 => 0xf0000000007ffffffffc00000003fc007ff000
  | 5 => 0xffffffffff800000000000000003ffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x110824209200008100a0090820900486001045
  | 1 => 0x800100042120244811084240480810008a4112
  | 2 => 0xe900949041480124802902295404318208c28
  | 3 => 0x4a24300005d4900281324a604410120740e80
  | 4 => 0x20001200096a7264b25800c4080bb8005f6000
  | 5 => 0x4b4c9c724e000000c06000081192eedf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffeffecfefaeee8fffeffecfefaeee8fffeffecfefaeee8fffeffecfefaeee8fffeffecfefaeee8fffeffecfefaeee8fffeffecfefaeee8fffeffecfefaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_30606
namespace PEqualNP.Outside.L_meta_30606
open PEqualNP.Outside.L_meta_30606.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 9 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 50 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_128 : Interval s2Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 136 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := (concat bs2_5_0 bs2_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 16 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 92 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 24 := bgb_3_0
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
theorem bgb_4_192 : Interval gbAtlas 4 192 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 222 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_1824 : Interval gbAtlas 5 1824 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1831 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344)))) (concat (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824))))))
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
theorem bgb_6_5536 : Interval gbAtlas 6 5536 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5561 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)))) (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152))) (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)))))) (concat (concat (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)))) (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))) (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208))) (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)))) (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))))))) (concat (concat (concat (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))) (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)))) (concat (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232))) (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424))))) (concat (concat (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584))) (concat (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680)) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)))) (concat (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936))) (concat (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032)) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)))))) (concat (concat (concat (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288))) (concat (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384)) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)))) (concat (concat (concat bgb_6_4512 bgb_6_4544) (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640))) (concat (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736)) (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832))))) (concat (concat (concat (concat bgb_6_4864 bgb_6_4896) (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992))) (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184)))) (concat (concat (concat bgb_6_5216 bgb_6_5248) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))) (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536))))))))
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
theorem bgb_7_1664 : Interval gbAtlas 7 1664 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1694 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
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
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffeeeeffffffecffffeeecfffffffffefaeeeafffeffecfefaeee8ffffffffffffeeeeffffffecffffeeecfffffffffefaeeeafffeffecfefaeee8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_30606.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,4]⟩,⟨.and,[8,7]⟩,⟨.and,[2,6]⟩,⟨.or,[2,3]⟩,⟨.or,[11,6]⟩,⟨.or,[5,7]⟩,⟨.and,[12,13]⟩,⟨.or,[0,1]⟩,⟨.or,[4,6]⟩,⟨.and,[15,16]⟩,⟨.or,[9,10]⟩,⟨.or,[18,14]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_30606

open PEqualNP.Outside.L_meta_30606 in
theorem PEqualNP.Outside.L_meta_30606 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
