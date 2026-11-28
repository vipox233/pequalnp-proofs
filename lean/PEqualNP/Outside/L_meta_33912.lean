import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_33912.Model
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


end PEqualNP.Outside.L_meta_33912.Model

namespace PEqualNP.Outside.L_meta_33912
open PEqualNP.Outside.L_meta_33912.Model
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

def SBf (j : Nat) : Nat := [8, 7, 7, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_33912

namespace PEqualNP.Outside.L_meta_33912
open PEqualNP.Outside.L_meta_33912.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630bea8c617e508c3f481187e50230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3be6298774c530fd20261f9404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec82887d50510fb18a21f531443ec42887d48510fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ee21e657e51ccbeca3995d94732bea8e65f551ccaeaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a89977d0d32ee21a65ee424cbda84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83be43d077887a0df94b41f7296836e52d06faa5a0fb54b41b6a9683bf42d077a85a0df94341bea86837d54906fca720f794e41af29c837d53907baa720d754e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f7d0f31ee21e637e52cc7dca598db94b31bea9663ed52cc6daa598f7ccb31ee996637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf294637d528c6fca318fd90631faa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7b88698dfd4931be29263df324c7ba6498fd90531faa0a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fd90721faa0e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887dc8510fb50a21f719443ed32886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821f721043ed42087dc6410fb4c821bf28843f641087ea8210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9
  | 2 => 0x260000d1338000000013fa2d3000007a000394744000000007d40e256000504000005087307124453a7250b139098158408b90005b8cd8000004a4000004a0000a20cc36c00000266408000001eb05e87c2daa90002d525159320414bf2183ae61ca58d00d07c88411a0005cc0006517a498701ed434000ce0232745f400000242300000100dc7f4631824f253414000420264000f31d4000000d7354350090002c43c09203f32e2e15316b0007b80000014e9ec001964c0000000000001e8500762d000000018000638270fe4806f0002644e27fd3e0e630237c869b237c7c00011338000000000000000000890000000007746a0002400001c000642a54fc7e887000000000088000be00075a4d0e2778308822ee084a189b0000010a0001ba14000000000a880026a3a60000024b22e5d8599a8442694000000ba01400000000000000fd4905e80014900000113950220000db8001961342a8005400014118810ca4149a693d01794f0003fc000000f22ba000000001b6000000002f8000001d0000000000000000940000040600000000000000ca800418000988f935a1b01887f000000740000a4000000003ba0000010a00000000000422308da83d02c0004e075000000d19ce0000000000080100401c0680200004c0180200200004803000004008000020000200100800803806010008008000000000000100200400000016000008000020180080100e000010000020240280300000c00800000014020040000100200200001c0000701a00c000010500000180a0420000180a00802c00002004000030000040000300000200800804004000018020000000180000e0080180900a000008000040100180300c018010020020180000100204c050010060040380101602803800000000010000000080100000c01003001006000010020060240080000200c048060080000100100001800000000000000050000180080000200c000010000040180101400800009000000020030040000180100200c050000000000000400c00c020010040000000702c0000280200e02c00800000036fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443fb28887765110efaa221fd54443baa88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85be43d0b7887a15f94742fb28e857651d0afaa3a17d54742baa8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857
  | 3 => 0x590000000000028849e71c0022328e000400000000000009a22a3ecb29c1416000fd800000aa0ab2224de1ecb00ed3ec000ba0000004bd50800366000ec890000824000002e0000000003cc0d892a39074000890000f04590390c0c064c20979000000000b101096c0017f0ae2e80020012aa145600005a0009419a3088280018b3f8000248b70701989fa6e04055cde80033c334218e74b4634d61a12987e12e23f30a538f49544c4758000001aa9c0788e90de839208004da230000de3aa000550000000007b0000004f027a6115e00087927000a6ce925f1442d8000001a2008000005000009b22e02a6880006a06e395489d440a7e4000000005a42300a4744b0001460c80000008d0009d0b304417c0b800000264664000a80000000000031e004b18000009e0000000000006210900000000000000000f222f00048cf08740000000029c00098c7f8004d86a5451af0004d0d301400095d0f23315a3901aa8c2de734001ec0008a0000040000cc6c0000120ed3d1b400e3840000023a874000000000011d8874ca0c8251bb40c2acd200014c06c4a11402e000000c92e29146915e0008d80000025a001162240000000000046472c9127d0000000000000083d09a87000000000000000000000012e0005723d0000000f91e2d8000000582ea20c00231000404ec03e0009d4149f707253c0f0700001a4000004600012f21c0007201500000079cf790445400050a2951a30c67217384944f29112f69187706238a5682d0002065140000044000000276000000529ea17800c35a8335c9542e2723220001815308480483a983280014a80017e000000003700000000004e150000005344f4df8003c61f8a112a0008dc001583b647c00100000000002530000000000048600000000314000000001a6674679400f85840024e340000c32120008f000289000368b21cf10a000490a354e974390f718e2d13420d1140000595c4e6370000793be7cc9700000086c00155000480002814100000000052c0012a022492001158d631870c000002b6a9062a19532418c48bb0002a48e1b9080718778000004ccb52a353e14c8d888000000000000000007186300059c368000000000000000000033972000a5c0000036200000000000a18d594800067d4925937416400000000000068000000000794a058068d80000000000000016012c980003b45e0000fc27c7704e8003c000000252000000000fa00060d459370a2000001a70004ec7aa9444c11c458134844aca921547c8e00309608a4d46080000091c000000000013b80c03a000af8243245b40013844a0644fa8e130408f11f400024c0000013c7c48c8ec1948d0a880000000000091000000001980002106c800404000000002301f5358004b00007c0001480001e00011c00039a4c00000000
  | 4 => 0x1c400042d478000000ac0000000023c
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x514823d64145209798c514825d6314520cd99051483356414520d598c51483556314520d990851483654214520d98c851483653214520dc580514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020b9185200836551480209ed95200837151480209798f54c425d63d53109b98a54c426d62953108f99353c423d64d4f109b98a53c426d6294f108f99052c423d6414b109798c52c425d6314b10b558e41c42b5648c710d914921c425f63552109718d548425e63152109758c548426e62152109b588548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e6414a108f590528425e6314a109758c52843675208610bc58021843e02188210bc18520843e321482109b98a544426d629511097d8d544425c63551109bd89544426c62551109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109b98a524427761549108f990524423d64149109798c524425d63149109b994524432e6414910cb590524434e6314910d358c52443656114910da58052442d56390510d914a41442746550510d914941442b5648c510d914a3144274654c510d914931442766588510d914a21442746548510d914921443685288110f888620442786548110f8485204436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109e980520427565c8410cd553210435553c8410d954b21042756508410cd55021043555308410d954821042f16008410cd553100435553c4010d954b10042796584010da54a10042776544010cd55110043555344010b9189100436552440109ed9510043695244010
  | 1 => 0x873a5454021ce551500875a5354021d654d50087e12154021da90950087694254021da8c950087693254021dc90550087714154021dc8c550087713154021dac8550087722154021da48550087712154021d8485500865e6394b409758e52d02b561d0b409798e51d025d6394740ab58b41d02b96010e409dd8552902746154a409bd89519026c62546409b988535026d6214d409d98453502756114d40d3988535034d6214d40d598453503556114d40d6580535023e65d0d40c714f435031c5350d40c714f42502b561d0940c714d425031c53d0540ab58b415031c5350540c714e405023d6590c40c754e431031d5310c40ae580431034e5394840d354e521034e5354840d354d521032e4354840cb10d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103364354440cd10d511031d53d0040cb54b401033551d0040d654e401023f6550040a718d401031d5350040cb549401033551500409ed95401035953500409b98854cc26d62153309d98454cc2756115330c715143cc23e6494b308f59252cc2d561ccb308f99251cc23d6494730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b6580438c2776154a309d185528c26f62546309b189518c3984390230b618d408c39b43502308f992544c25f63551309b988544c26d62151309d984544c27561151308f994544c31d6315130cb988544c32d6215130cd984544c3356115130ce580544c25e6590d30c7152434c25c6550d30c7151434c31c54cc930b5587324c31c544c930c7153314c2cd62cc530c7151314c3385490130e690e404c2786550130e650d404c31c548c1309b98b540c26d62d50309d987540c27561d50308f596540c31c63550308f990540c25e63150309b988540c26d62150309d984540c27561150309e980540c25d65d0c30c7553430c25d6510c30c7550430c2d96010c30cb952520c32d5494830cb951520c32d5454830d3d0d520c34c4354830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430c7553300c34d52cc030d5547300c339548c03097d95300c29c644c030c7551300c34d524c030d5545300c27b654c030ce551300c25e63d53209758f54c827661953209d58654c823e64d4f208f59353c82766194f209d58653c82cd6390b20ab59232c825f63552209718d548825e63152209758c548827661152209d584548823f6454e208f191538823e6414e208f59053882766114e209d58453882e960086209d9865448275619512097d8d544825c63551209dd85544827461551209d98653482756194d208fd91534823c6454d209dd8553482746154d20b358e424826c6550920ab592324826c654c9208f99
  | 2 => 0x6494732cd59251ccb574354732d510d51cca7661952329d586548cb2e6295232cd986548cb356195232cb951428cb1e54cca32b9987328ca7661951329d586544ca5e65d0d32c7550434cace6210d32b5584434cad96010d32b398e424ca6c6550932e310d424cae661cc932a7992324ca3e64141328f590504ca7661141329d584504ca5e63d50329b988540ca7661150329d584540ca7a60150329e580540ca3e64948328f592520ca5f654c8329bd95320cb1d5310f41ab58843d06b96010f419798e52d065d6394b41d398e52d074d6394b41cb90d52d072c4354b41cb94942d066e6294e419b58a539074e6294e41d358a53907566194e41c794f41906e662d0641ab58843506b66110d41ae58043506b661d0941b998b415069e63905419798c505065d63141419b988505066d62141418fd95411067765504419b98b54cc66d62d53319b98854cc66d62153319e98054cc6796015331c755043cc6cd6210f31b658043cc63e6494b318f59252cc72e6494b31cb59252cc74f4354b31d310d52cc74e524cb319b98a548c66d6295231cb98a548c72d6295231cd986548c7365450631c7953318c6e662cc6319b98a544c66d629513197997434c71d5410d31b3588434c6d66110d31b6580434c6d661cc931b598e414c6746550531e510d414c6e662cc531a7992314c63e64141318f590504c66e62141319b588504c65e63d50319b988540c66d62150319d984540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c65e63d53219758f54c863e64d4f218f59353c86d56390721ad59231c865e63d52219758f548863e64d4e218f59353886cd6390a21ab592328865e63d51219758f544866d62951219d586544863e64d4d218f593534866d6294d219d586534863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d6595021cb98a540873661950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a53087566194c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530866d6590821b358e420874d5390821b9586420872e5450821d354d420866d658c821ab592320872d548c821b9586320872d544c821d394d32086756590421b558e41087555390421b958a41087365450421d554d41087a542504219d59631086b5648c421cd55231086e5628c421cd5513108756534c421f14c931086e562884219bd9521086776548421b9d9521087676548421b9d9121086e56448421e995121087a55448421b9d8d21086e56348421f194d21087c55348421b9181210873a5494021ce552500875a5394021d654e50087e12194021d9485500
  | 3 => 0x40027f0000000017d1902200003315c154000001f8978469810001e488822332ae8d60b657c000001184269900000030e87ceb8004c017443a341527409e8d13b6540b824d0c6218ab0a0000a750a8ec2ce69cfd0313fa19081840000030598000006ed5e1594c4084600002bead0000fa3082388a0000008b4002033ac1680000013c294d993040a270d5800582678a707a56c3b5122770044a4001f717639156a792cc5b5100e055c3a8f31f22f28992c2913a88bc16a850ea3d8ec1a95a00ac28046520428710142c6a18740360140f42b8e919a6592b8913264d8831724420ecd119031c9b9190be22a068ef09f48e14c0029f23e194d00000009d00006d1ba8d43da480005114a8aa15a1b88009a45c000679534a094c2f85931e9f5161e25287d81a0c40cc9ad1ea6306e040161cd4a41205815d35c984971bd2505a83b2991c209cdf0b82168096222705c7d09aabd394589351a63dea80119eb30c0101900402020080040200c0600814038000240a0000b04805010030080c014290081f000010142500c10008000000106c510000902401010080000008401008020780402019068030440c000060001b010030001005815034060540600000000120281406c04000010040500c06000010004c00c0203c04058190080500c030180000c1b004010080c02c00054050601e00405000080040000402000120002c01800008000001801009010030142a004000080200c000240200001068000180100c010200500001004020040002003028000001801402000030001d01018000020000000c060b8030040607c12010120280201c07038000001000410000040d80f044000d80202804004380000403c13074000400001c01000050140c0040400802004030041300809000060ca7661d49439d5875250e6e62d45439b58b5150e6e62141439b5885050e7661141439d5845050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9f6150c43a71814310f8d4394843e350d5210f954394443d994a5110f655294443e550d5110f665254443d95495110f994394043da94a5010f695294043dc9465010f715194043c750d5010f994354043da9495010f695254043dc9455010f715154043ced0d5010f5a4354043ce50d5010f594354043c650d5010f1d5310f42ad58443d0ab96010f429798e51d0a5d6394742d598e51d0b556394742cd90d51d0b3443547429d9865390a756194e42d398a5390b566194e42d55865390b1e53d0a42b99874290aae6210d42ad5844350ab96010d42b99874250a9e63909429798c5050a5d63141429d9845050a7561141428fd954210a6f65508429d98754cca7561d53329d98454cca7561153329e98054cca796015332c755043ccad56110f32b658043cca3e64947328f59251ccb36
  | 4 => 0xd18434f85244d8c738a24d1993b000318462bf11e9446f07816a421521ce58c6a91e13e3187042e2a80e280558a4e4240780000008e350c52362080182080441a92871ad41b65d04b800000b00921ed14c9112d0004ecab03e9f5420000000003420000590c552001229893c80009692b0003987a1a820e7a862ac22365d53aa1e4e61786609451c7480026938e2140ea424d04bcb0a7b00062cb8a5f472b256900d0526e8ea8da4ca6d52c9d9428000c18000006141f882038a95111511744a94085122e044aa800000b28002883900012797748092cc4123112201140963d29990e8070005943920b0001886b8c92584151491d000970b5a871649506715b048b0c000003923ec002174aa264ca0cb186a24000183648fc3586021e1fca403a1144c4290000003ad0d800000001538001ac000130000000010d1c051a00103921000a98dc0002ec0146c0002960007e94c2de4cc340004466bc0015a05e3287286a3f0440e5ace0063d557800000000399162c8478002830d2a494014a0a86b40010903e000001910000000000000082800249000a2c0023e00074c002700b64686aa2b09c4e50027e362124de00132e7805e0c11ee864000384860f80a9df0000007380e4e4000a08170ee000872840c2731020ac514a5d0316c3b80003f0a3148b30929420247f87984534a8dc26a3a1de6354c26d2f40006f9ff422000211b93880002583c1f254800182412a88e31455a60000019a0e0550ab8a1130654df97b53400089aaa4383c437ac51e04813d000368600000a81f03654f0000004087f9ec59a4f02b1f34ac79c0007c5904dcfd8f2000000000321dc9b133a8242c3400013a2d2660279da28c435180003d0744102bb000000f09583604d05113f4980e4fc9b70365f00404424ea8c91000168ad44eacf3dc204ceab85a24041520f06053cae0165265cd5baa10005fd2d9380008391291901e0013c2b200022c1415e1626706101333e860559921201d0891dd0b0a70b71cf59666c7f06c00078c00160000820000004764c9461f000019c6e1f128e0254b22a29a0005f9681a6a6c0004a556ac15c84c348065061c20005e0000b9124000002712866d85ea312fc50159a6f1080000000048c470001e50000012089506a8e12e80051e000000b758e7f0418af1a429ce192600009
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1d8013ae11022fa4a5a88f29049e000021898c0016802305802c282b10ae841700008a0c82802d980b179180141a800318a406001d0183af2ca78da699250e011e8031aa30228688802019a1299c32a7122d1b1280002aaba615803200090fa38010001480002200050787310000000a8d1b80000000309f960e9f001c800b8800001a1300209501000540000000408082000300408001424040c4c0c040868400c00005400101800024ab8ec4a1887235cb6150c4391ae43028621c95711814310f82a1aa4a8887c250e5254043e1286a92a021f11439455010f88a1aa2a8087461d94354043a36e4a1aa021d1b7150d5010f0ca9ac021e854c5c04354742c32a8b0087995517010d51ccb0caa2c021a65615c44350932b12e021a84996195358043d0694b8086a9683865516010f31a92e021aa598e1954580434c6c2b9086a0a63645c04350531e0aa6a128210f05544c93108662b9ec890843295d36348421e0aa8a9a4210ca5741812108662b98c090843c89512154021e42a890aa010f425348550087a0a9a42a8043525ce4254021ac2e3212a010d29748c950086b0b8c64a8043545ce4154021ac2e520aa010f21425055008698ba462a8043585ca3154021e826498aa010d607648550086b1ba242a8043585d12154021ac6e690aa010d61734855008722b12c229a81925896014d40ca2c2b00a6a061453587425030629ac5a0a814a5c04354840a62e021aa22060c63549401030a31aa2a008186d516010e30934eda1a811862562584544c30cb1ac02a2618a5896015130c62c2b00a89861454587324c3062a2c598a61469d64390130c30caa1a809861954580430c2a4b8086a9061545c04354430838ecaa2601860c64549300c30a322a298061855916314520a8ae7210a290525748c85148318b22c028a419458d6014520c52a8b004210649535802108312aa0c2900419154c6148020cc6a4b0043084e276c852084306b22c6292218a5916014910c92c6b00a488661615805244322b18a520a2189590528c510ac4eb10c4088660654852044318aa2c0108219454d6008410cc2a4b004208625541891004322a98c488021191d95244010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x84a0000200006ec30909821d94354043911811d9435404391181dc9435404390982dc54354043921841d92154021941831d9215402194183dd1215402192184dcd2154021
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s0K6 (731+((h/13+packedAt s0K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s0K5 (20911+((h/227+packedAt s0K5 (18414+(h % 227)*11) 11) % 1089)*11) 11
  | 4 => packedAt s0K4 (29960+((h/241+packedAt s0K4 (27550+(h % 241)*10) 10) % 871)*11) 11
  | 3 => packedAt s0K3 (5270+((h/34+packedAt s0K3 (4998+(h % 34)*8) 8) % 135)*8) 8
  | 2 => packedAt s0K2 (488+((h/2+packedAt s0K2 (480+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 2 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 3 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2004400040000400000800480120800001045
  | 2 => 0xc4148944492854085064292124849286314512
  | 3 => 0x1a912289244a801ac80524849212530c28a28
  | 4 => 0x488c032520240c92352918000e498192540f80
  | 5 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfffffcccfcccfcc0fffffcccfcccfcc0fffffcccfcccfcc0fffffcccfcccfcc0fffffcccfcccfcc0fffffcccfcccfcc0fffffcccfcccfcc0fffffcccfcccfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_33912
namespace PEqualNP.Outside.L_meta_33912
open PEqualNP.Outside.L_meta_33912.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x340088028000004600a8038000000000ba9141800000491243a9c0003e084000001580000068100110800064d901e0c00050000000001280002c60500a8000001c00000600003c00026004c00e0058020000000012000010000002000608000000c000ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x594a0c551e281b2f3c3733002154044445343632490f29083f2d43404c27382318170322525000000e1553310726190a5a42120905165100002b010646004e00393a4d112c1a004b004f003b200000001d2a3e000b1f580d0010000000020048351347003d41142e30561c25245704002ca040000285100000216080020c1c00312085800648132013e5390e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110f6aa221ee940439ea8087b95010e72a021d794e42aea9c859c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a655e53906baa720e710f31b7296636d52cc67ca918cf552319faa2633c544c7388698cf950219eaa0435e53086baa610f948421bd2804379500867ca7a04f55240afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f950409faa6613c54cc27ca9184f55230ce21c61b9408c27ea8984f15130dca02613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a4413d54882eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9084f55210b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1640452603030e000706a800000202004ac28200000000090000001e62e0006a2a0d0000400000b255254443ca9495010f295254043cc9455010f315154043a658043ccb144354732a6580434ca996010f31c310d52cc6996010d31d8485500870e6214d40c358853503166114d40c558453503196014d40a6580438c29863502308e195404c21d6510c30c310d520c31443544308718d548821c6355210
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x4800c01001445c04354732a12e021aa598e05625845350304b12c029a81845856014d40
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
  | 3 => packedAt s1K3 (998+((h/8+packedAt s1K3 (950+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 2 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 2 => 0x52228891414810a0521244248449414612512
  | 3 => 0xaa444512412900354802489092092941828a28
  | 4 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_33912
namespace PEqualNP.Outside.L_meta_33912
open PEqualNP.Outside.L_meta_33912.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2418f2b0000b8244694010000c0b00000004a8c6050024c911c00a00001c0000000180007c515000000000000003a00024004d0801a9c804540101b1058e005298780800e0018000002031008180ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x7c123eae0000289c1c1a5e36007a82703006000046680204580c8092664c0a002600000086603a985264006a325000566e000000000000485c00000000429610a81600b400b2888a4e242c9e00545a00906200004400000000009a00a2000e003800004a74181eb0a6221440b6ac208ea40076a08434aa72787e942a088c00003c2e00006c00030000090d0103090104080100030206020401020001040200000c020201b7294876d5290edca421db54843bb28887755110ef4a021de54043bd286857950d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290655e53106baa620db94841b6a90837a50106f2a020db94b31b6a9663cd32cc67ea898cf15131e6992633e540c67aa818db94831b6a90637a500c6f2a018cf950219eaa0435e53086baa610de94021bca80436e52d02daa5a06b94b40d6a9681ae32d035a65a04f55240d719281ad3250376a0a04f95040b7296616d52cc39a65984f952309eaa461b9408c39a64986e501309f2a0613d540c2dca4185b54830bb2886175510c37281904f952209eaa4413e540827aa8105794c20aea98417651082eaa2106e500209f2a4213d548437281085bd4910b629221b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8b01d090280608180101c0181a07940008408e582548caa96095232a3993534cac56110d32b2580434ca396015131c3151324c64d6394b40a358e52d022d658cb40aa98b50503893250130c654d400833151500209358c52443285250110
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x8001800800912e1326a69950970151324c644b9cc5a8281425cc5250110
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
  | 4 => packedAt s2K4 (2724+((h/30+packedAt s2K4 (2484+(h % 30)*8) 8) % 134)*8) 8
  | 3 => packedAt s2K3 (633+((h/5+packedAt s2K3 (608+(h % 5)*5) 5) % 24)*5) 5
  | 2 => packedAt s2K2 (200+((h/1+packedAt s2K2 (196+(h % 1)*4) 4) % 13)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf3c38f1e3cfc7f1f9c470c7e23f3f1f91c4cf
  | 1 => 0xf03fc0fe7ff1f8fe3e0780f8ffc7c7e1827b33
  | 3 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 4 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x185011804450842008414412809210910c045
  | 1 => 0x10080220008001004000800840420200001112
  | 3 => 0x2202b445492892a00f480a92129094d4630c28
  | 4 => 0x44109005120080249251220003249044240e80
  | 5 => 0x88a32088402d24c925a64ce4980020995be000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffeecceeeeee88ffffeecceeeeee88ffffeecceeeeee88ffffeecceeeeee88ffffeecceeeeee88ffffeecceeeeee88ffffeecceeeeee88ffffeecceeeeee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_33912
namespace PEqualNP.Outside.L_meta_33912
open PEqualNP.Outside.L_meta_33912.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xba50000a8022280284c782190aac69f0024403001cd230000701244d0a93074300005100000000222c001004e0060038a8790486c00b0010404004a003003200040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x96762a0066728c829e4e56443e1600840000001a00ae64001000009c40460000ac1400004c00000000006802420000125e5800903ca000282000007ab200000000340054005000000000a8780e926a000000a20000002c000030946c523a5a008000002e38080618360060700000008a00000a00000000880024009a00b48600003200b0485c6e001caa4a000000b67e260000000000982200a68e620000000004001e00000c00007c0000a40000740000010903000a0600000b000002020900000205000002000000020300020101b7294876d5290edca421db54843bb28887755110ef4a021de54043bd286857950d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290655e53106baa620db94841b6a90837a50106f2a020db94b31b6a9663cd32cc67ea898cf15131e6992633e540c67aa818db94831b6a90637a500c6f2a018cf950219eaa0435e53086baa610de94021bca80436e52d02daa5a06b94b40d6a9681ae32d035a65a04f55240d719281ad3250376a0a04f95040b7296616d52cc39a65984f952309eaa461b9408c39a64986e501309f2a0613d540c2dca4185b54830bb2886175510c37281904f952209eaa4413e540827aa8105794c20aea98417651082eaa2106e500209f2a4213d548437281085bd4910b629221b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xd4a1e0309440018772c011940515008e582548caa96095232a3993534cac56110d32b2580434ca396015131c3151324c64d6394b40a358e52d022d658cb40aa98b50503893250130c654d400833151500209358c52443285250110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x221800912e1326a69950970151324c644b9cc5a8281425cc5250110
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
  | 4 => packedAt s3K4 (2724+((h/30+packedAt s3K4 (2484+(h % 30)*8) 8) % 177)*8) 8
  | 3 => packedAt s3K3 (633+((h/5+packedAt s3K3 (608+(h % 5)*5) 5) % 20)*5) 5
  | 2 => packedAt s3K2 (200+((h/1+packedAt s3K2 (196+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf3c38f1e3cfc7f1f9c470c7e23f3f1f91c4cf
  | 1 => 0xf03fc0fe7ff1f8fe3e0780f8ffc7c7e1827b33
  | 2 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 4 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x185011804450842008414412809210910c045
  | 1 => 0x10080220008001004000800840420200001112
  | 2 => 0x2202b445492892a00f480a92129094d4630c28
  | 4 => 0x44109005120080249251220003249044240e80
  | 5 => 0x88a32088402d24c925a64ce4980020995be000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffececeeeee8e8ffffececeeeee8e8ffffececeeeee8e8ffffececeeeee8e8ffffececeeeee8e8ffffececeeeee8e8ffffececeeeee8e8ffffececeeeee8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_33912
namespace PEqualNP.Outside.L_meta_33912
open PEqualNP.Outside.L_meta_33912.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2a000000600009546d7860e002a33ca0fa4225c0130000000565800000016a51e9c40240340042400000000110b0000080527001a0064000426172c3a00000000050e2000a260000000180000280000000100140010600001ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa617c514c37c82986f10530ef98a61dd314c37e80986f50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6186fd0c30dea18617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea10617e510c3eca2185d94430bea8861f5510c2eaa2186f90430de208617e500c37e80186f50030ef98061fa300c3ba60187e4c030ec980617f54c82fca9906f953209f2a6417d54c837aa9904f55320be2a6417f53c82fca7905f54f20be29e41bf43c837a87906fd0b20dea1641ee32c83da65905f94720bea8e41be41c837883907bc8720f690e41bf40c837a81905fd5220bf2a441be548827ca9105f55220deaa4413d54882f8a9105fd4e20bf29c417d53882f8a7106fd0e20dea1c417d528837e85106f50a20bf28c417d518837c83106f10620bf28441bf408837a81107e8c220fc98441ef20883f641105fd5120bf2a241be544827ca8905f55120deaa2413d54482f8a8905fd4d20bf29a417d53482f8a6906fd0d20dea1a41bf424837a84907b8c920f6992417f51482f8a2906f90520de20a41ef21483da42906fd0120dea0241fa30483f260907ec8120f7102417f54082fca8106f950209f2a0417d540837aa8104f55020be2a0417f53082fca6107794c20af298417d53083baa6105754c20be29841bf430837a86105f94820dfa1041bd42082fca2107d94420bb288417d51083eaa2105d54420df20841bc41082fca0106fd0020dea0041ef20083f440107b48020fc90041e920082fea9886fd53109faa6217e54c42faa9885f15310de2a6213c54c42fea7885f94f10bea9e217c53c437e87886f50f10bfa96217e52c42faa5885f14b10dfa1621bd42c437c83886f10710fb18e21f531c43ec43887d48710dfa0621bd40c42fea9085f95210df2a4213e54842faa9086f552109eaa4217c54842fea7085f94e10bea9c217c538437e87086f50e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3086f90610de20c217e508437e81087e90210dea0421f9408437281087e8c210fc98421fa20843f241087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53442fca6885f54d10be29a21bf434437a86885fd4910bf292217d52442f8a4886fd0910dea1221be414437882887d8c510fa98a21f621443ea42886fd0110fd20221bd40443f280886e50110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2086f90410de208217e500437e80086f50010fb88021fa10043ea20087e44010
  | 1 => 0xd54c867aa990df15321bfa9e437e53c86faa790df14f21dfa1e43bd43c877e8590fb90b21dea1643ed42c875a8590fb8cb21f699643be41c87788390df94321bea86437f548877ea910cfd5221bf2a4437d54886f8a910ef152219e2a4437f53886fca710df54e21be29c43bf438877a8710df54a21dfa1443bd42886fca310ef90621de20c43f631887ea6310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21bf29a437d53486f8a690efd0d21dea1a43bf42487dc8490ef50921f6a1243ad42487dc6490fb4c921df20a43bc41487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21dfa1843bd43086fca410efd0821dea10437e510877c8210ef10421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40dfa1e81be43d037a87a06f10f40bf296817d52d037e85a06f90b40dea1681bc42d02fca3a05f54740dfa0e81be41d037a83a06f10740dfa9e81be53d037aa7a04f54f40de29e81bf52d037ca5a06f54b409ea9681bc52d037e65a06f8cb40de99681bc32d037ea3a06f947409f28e81bd51d0378a3a06fcc740df18e81bd31d037863a06fc8740df10e81bd21d037843a05f552409eaa4817e53902faa7206fd0e40dea1c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f90d40dea1a81bc43502fea4a05f14940dfa1281be425037a84a06f10940bfa8a817c515037e82a06f90540dea0a81bc41503f680a06f90140dfa9a813f535037ca6a06f54d40de29a81bf525027ea4a06f94940dea9281bc525037e64a06f8c940de99281bc325037ea2a06f94540dea8a81bc5150278a2a06fcc540df18a81bd315037862a06fc8540df10a81bd215037842a06fd4140dda82817e541027ca8205f94c40bea9881bf431037a86205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330dfa1e61bd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28e617d51cc37c83986f10730ef98e61dd31cc37e81986f50330bfaa4617e548c37ca9184f95230beaa461bd548c27aa9185f15230bea9c61bf438c37a87185f94a30bea9461bf428c37a85185f94630bea8c61be418c37883185f94230dfa0461bd408c3be61187ecc230bfaa2617e544c37ca8984f95130beaa261bd544c27aa8985f15130dfa1a61bd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8
  | 2 => 0xcafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7196fd0e32dea1c657e528cb7e85196f50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132df2a2653e544cafaa8996f551329eaa2657c544cb7e86996f50d32dfa1265bd424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865bf430cb7a86195f94832dfa1065bd420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41dfa1c83be439077a8720ef10e41bf294837d529077e8520ef90a41dea1483bc42906fca320efd0641fba0c837e50906faa120efd4e41df29c83bd539067aa720ef14e41dfa9483be529077aa520cf54a41de29483bf329077c6520ef4ca41de194833e519077ea120ef94241dea84833d5090778a120dfd4d41be29a83bf435077a86a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077e8620ef90c41dea1883bc43106fca420fb94841b7290837d52107daa420db54841dfa1083be421077a8420ef10841bf28883bf41107ec8220ef50441faa08837e50107f4a020de94041bea8083f950106f2a020efd4c41df298839e531077aa620cf54c41cea98831d5310778a620efd4841df29083ae521077aa420cf54841d6a90832d5210778a420efcc841df19083bd32107786420ef944419f28883b6511077ea020ef94041dd28083bd501067aa020ee540419ca8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc77e8798f790f31dea1e63dd43cc73a8798df94b31bea9663bf42cc77a8598f7ccb31ee99663be41cc7788398df94331bea86637f548c77ea918cfd5231bf2a4637d548c6f8a918ef152319e2a4637d538c77e8718ef50e31bf294637d528c77e8518ef50a31bf28c63be418c7788318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898efd0d31ef21a63bd434c7ba8698e750d31bfa92637c524c77e8498ef50931ef99263dd324c77c8298ef10531fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863bf430c77a8618df94831f7290636e520c6faa418fb54831b6a9063bf420c77a8418df94431df20863bc410c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c877ca990cf95321beaa643b
  | 3 => 0x100080300500e0000200200801000008014000068040000540000000a00c01000000020000080000040000000a038008020020001680000001000001000008010000220400000200c0000082200e03c00001000004018000080500000100000c018000020000000200400800013000000008020020040680400a00c038010020080980300800001001008000048000160000100800e0040000200001000800006008078020000040180100000400008010000028060000240100000000c0080800200c01000002014000000060040000402c00003809000014008010000080000a0100100000200000c030030000000080000400c0002c0000000b0060140140101c00200c0080101200c0000100003c0100201200c0781700000001000000020008000000040080001601c00001000000028040000040000300c0000000000201c0080300c004030000020000100300801400806000000010010020300080200002000000008034000020060140000900003c0700d0000280100000400001004000000010020020000200200001c00001006004020000000080000000c0000080000000400003000014010040100100000500000000000002000000000000000280200600402806014000008080000140201b000002fca5a1df54b43bf28e877d51d0efca1a1df54343dfa9687be52d0f7aa5a1cf54b43de29687bf51d0f7ca3a1cf94743dea8e87bc51d0f7ea1a1ef94343dea86873d50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa92873f5250f7ca4a1ef54943de29287bf5150f7ca2a1ef54543de28a873c5150f7ea0a1cfd4143df28287bd5050f78a0a1df950439f2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e853d53d0b78a7a16fd4742df28e853e51d0b7aa3a16f14742dfa8685be50d0b7aa1a14f54342de286857d5490a7aa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a14fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5150b7ca2a16f54542de28a853c5150b7ea0a14fd4142df28285bd5050b78a0a15f950429f2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32dfa1665bd42c
  | 4 => 0x2060000000006ee6563280000007ce7267fc4b80000000002d600000000006050e2b60005fa2a400000000000000a4ec0742d87340004be0005f848800050800000000000019a33200000000002269e5883cc50c00000000000054400000014a5e27560004260001a85ce0000000002cc5481740001e031050611400018656205e2160003ea8266ce7162a66a06ea79e00048a4503da5a28348585343480000008040000000001e40a45ba6c27bc35226255427630c1f80d233e09841c2c80e01c610c0660a61064de5282704d603a74c4c81f003e28c14c0fe6a258e0a06b024a16654a5ac72c7ea00055a5da7f64e229200049e4527ba83e16435400000000000082e0000000005a000000021a55e15e37e5e45800004700000001da60c0000003ba00045c3560000000007001d82a00000000004740000000008443f000000031a0000000000008360000001765680002740000000003960002944e40003724024383823b00006ec0000000002d08142440002bc8205e60d60004c66e83080007ac83a4c014804c3427d67d846200c33a7a41d62b047675c5d256436628062c0000e81be0000000000007640ca7dc0524ae59a7601441b41fe00000000000044a45a6a866e47812a3e84148560004f03b800022000028621c0623927863d67440260be55c56a0c200027e48e1260003f80000000007505660000005e03f611679200000025413425a3ca1807c800052e00056e09e23609238e4486bc3ae1fa7b600041834000000026400000079c8108480000000000005aa1b604a16224608600000067861273a2ec7d200000000000000000000000000032e82838600066480e5762f22827101ae70a5163f22de23a13602e00063c5c86a67326d853a3044d40000000006c83605f006a81a71c00077400000023e00e6f663200022a26600000000068204e2220000000006460000004e60001ea5e82ce80a0000000000000003de00000046a6963ec0006cc1ba2f47626300000003bc76c0001420008600002ae4b20000000004a200000000000000024e25c12000000073c2e85fe0000000f671e0003840000000000000002000000d40000004320007e20000002520000000000000004bc2100000000006040000008520f80001900007400000000001f200020c7e00000001ce1a25d458a3806c42e60000000007b404418a7fe46643c7ec1a000000022c59c7ee0007883be00012e57e24000000063e0000000000008240004043aa0008063260006487660000000006220000000000000000000004d00000000000400000000006680000000008322e434a10a0007f80000000000000007800001d25c200000070454240a5124806b200041e3ac0c600000000059000021e0000060080000000001c0080600a02001800008008008
  | 5 => 0x420002c60b27d401a00000085a0ac3706b41881827300023d20000a840c47a2301284cc4563a037600000020400000000000000004613200079800032c6e40007285a600023c0007e811001800000046000030600000042207c0003747a25268400e602a7547a000033c56059600000031600066c34c8380005306ca0002b200000069200051c18e2f87480544307843e400037800000000000076a0000f000024853e0000000005be1ee0000002fe00000033600000025600000000000013e00000081200077800000000074e0000006b84c465200039e00044c20236853213a00052a51e5d62841843122320326c60000000000360000007fa7d00000003580000000000003e00002ee0000000000000002185c072e00036a26c5fc57068c0e200084c0000001de0004e822628e30e75a1aa42e5106401d070c1401727061bc4f844e3d464c09c2fa4e00000cc0684084103021b000000026a7240005ae85e5b40000008220000006140001945d008a0204a05143f46aa7206383643dc3881dc0007186e66580000000000000000000000000006d46d02985522280000000000000000000000004847ae60800001e84a85067a0000000000002be1b223400054664421469c61e1e680800017800000000000000024200000016043a00036249a00000078e0000000000000007c60000000000000000000000005a82960006d60005c46dc11e0000003fc18c0007da0005ea4f406429c0000002121ca5980ae4a446458600053600000067c6762506c039a1e80ea3b44347720ba1a416e0960bc0000d82e000000016c0000000ec00000000000086200047c0000000000002e20005ec08240e00064e0000000000000000004a86f000030056c5ee0380000005f63fa15c3a67ca45804857243e0f200032a61677a0000007e63fe0000001d40007aa5b200041a8540003c611c61a00058c00000016a0007f03200000ee3e220e00077e3e67f400000052419267e7940000006360007580000000000001a600000044225e00010412c8162902f62b86ac08001c00037a2686fe6d25b840057457a29e0003c064a0005b647e1cc06c3224d813000015461c24c0244ce0000000000000000000002c001080c1ac06e13c00000400000000065c36c4920de0905d805000001400015600073e00082a27c00069400046c26e0007a60002f06ae0006b600003c7e442400060a0000002da0000000000000000004ac50049839815242a36e38a0fc5222fc4540b841266a0007f21120006ba7be0000000003c200000049478c6260708420007826e24b471a01672239c8025c60c00000766346541f600045e35c0000000000002a83a45584464c217e1c47423144fa7a80e47703383a260049662e00034e05868600079000050a27a00068e00075e10079a0000000
  | 6 => 0x15000060e00051800000063a0d06f219c0c42880000000000007de0002d40007766900005020000000006f834461874a0c810800019607a5f403484e1e20282785ca2c24201221980007b057c0006707cc0005f200000000000022e0000007464b64dc28a0dc0000005204ea51a2386284d24fc81e00083000000070210e00000052c5de31e0002aa00049c00000009446e15a4901b80000006fa00000011a2086de0005dc0000003184a680071461034646830a22400033465e2ca4b013871268a00019e3d86660005046500000b00004ee1026da0da0006be48200000037c00000002c70e0000000b417000000000000000043639409a5bc00032454c60668466017a65a7082d21584160000001ec4281c84405400004aa0723a80847c478a4fe08842c0004ba2ac77c57814e05a66200048c00000082c7c20000000000120000000007c000000076800000005c5a40060b673660200000800059281872a00008c0007b855020a00005667203017c62a3304ca3506a46982dc12454e0000000fa4f679685c6424444864722b435a7384da0000a26f467483c39053c2722ba00000000025800081c0ce3b60000000003c469a31c0f40000002c40000002a23c835e1c06fc00000000076e3ce0000aa2600006e05825562ea5841c259e40608e7b211800068053875207807e0006240008460001684f21f429a0005946880000000003ee1fc00038c5b05cc0000000001460000006200000003b23d000000
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x920842bb64c42108f58f544423d62d51108f992544423e65151108f58c544423d62151108f984544423c6115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423e65d0d108f19743442b960d0d108f995434423c6550d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d0910ae583424423e65509108f195424423e65905108f994414429d6310510ab5884144274654c510e550d31442746548510e9509214423e65d0110ad98740442b96490110ce152404423c6550110ad18540442786550110bc185404433b6550110ae195404433865501108e19540442bb6350110aed8940443b36150110ae18540443b06150110ac18540443b23150110ec4c540443b22150110ec48540442b9648c1109e19530442b9644c110d614d30443d1314c110ae59220442786548110ae59120443685248110f848520442bb64c4110ec502104425e63d50109758f540426e62d50109b58b540423d65950108f58e540423d62950108fd8d540423f62550108fd81540423d60550108f990540425e63150109758c540426e62150109b588540427a60150108f993530423d64d4c109b98b530426d62d4c108f992530423d6494c1097596530431e5494c10c7552530431e6494c10c7592530431e5454c10c7551530431e6454c10c7591530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108fd97430423d65d0c10c794f430431d53d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432e6454810cb591520432f4354810cb50d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d52508108fd96410423d6590410c794e410431d5390410cb94a410432d5290410ae582410423f65104108f594410429d6310410c794c410431d5310410ab588410432e5210410cb54841042b960104108f992500423d64940108f597400431e53d0010c754f400432e52d0010cb54b400423f6550010c794d400431d5350010cb949400432d5250010ce941400435553c4010d954b10042796584010ce55210043595384010da54a10042776544010d554d10043655244010ecd01100427b6544010ce55110043595344010da54910043b04144010
  | 1 => 0x831e6494c20c7592530831e5454c20c7551530831e6454c20c7591530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208fd97430823d65d0c20c794f430831d53d0c20ab58b43082b960d0c208fd95430823d6550c20c794d430831d5350c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cd95251083355494420d594e51083555394420cdd9251083346494420cdd0e51083354394420cdd0a510833542944208fd91510823c6454420cd95151083355454420d594d51083555354420cdd9151083346454420cdd0d51083354354420cdd09510833542544208fd96410823d6590420c794e410831d5390420cd946410833551904208fd94410823d6510420a758c410831e5310420c754c41082ad6210420cd94441083355110420ae580410823e64940208f592500823d65d0020c794f400831d53d0020cd947400833551d00208fd95400831e5350020c754d40083365150020cd545400834d53c8020d954720083595388020ba58a200837151880209bd95200834d5348020d954520083ab4048020ea501200827b6548020d654d20083ab4248020ea50920083715148020bad95200836b6548020ea99120083a96448020ea95120083a95448020dad4d20083ca5348020da54d20083c95348020d254d20083ab4348020ea50d20083e25148020da54520083e15148020d854520083aa4148020ea105200823d63d53108f58b54c433661d5310ce58354c425e63153109758c54c426e62153109b58854c429d6315310ab58854c431e63153108f58c54c431d63153108758c54c432e62153108f58854c432d62153108b58854c43366115310ce58054c423e6494f108f59253c423f6454f108f19153c423e6414f108f59053c426e6214f109b58853c423e65d0f108f19743c423e6550f108f19543c431e5350f10c754d43c423e6494b108f59252c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c423e65d0b108f19742c423e6550b108f19542c432e5250b10cb54942c42b96090710a758c41c42ad6210710ae58041c4395434c710e950921c42b661d0310ad18540c423d63952108f58a548433a60952108fd8d548423f62552108f993538423d64d4e108f992538423d6494e108f990538423d6414e109b988538426d6214e108fd97438423d65d0e10ae583438423f6550e108f595438423e64d4a108f593528423e6494a108f592528423e6414a108f590528425e6314a109758c528423f65d0a108f59742842b960d0a108fd95428423d6550a10a758c41842ad6210610ae580418433a5450210aed95408433b6550210aed8d40842bb6250210ae18540842b9648c210ae5913084358534c210ae59220842b96448210da14
  | 2 => 0x5254430d9549510c3376454430cd191510c3374354430cd50d510c3374254430cd509510c23f65904308f596410c32e5290430cb54a410c3365190430cd546410c23f65104308f594410c29d6310430ab588410c32e5210430cb548410c3365110430cd544410c2b960104308f992500c23d64940308f597400c32e52d0030cb54b400c33651d0030cd547400c23f6550030cb949400c32d5250030cd945400c3355150030d354b300c35551cc030b658e300c369528c030dc546300c25f654c030d3549300c355514c030e6d01300c399404c0309ed95300c39b434c030e650d300c369524c030dc545300c2db654c030d6d95300c39a644c030e6591300c39a544c030e6551300c3ca524c030d6549300c3c9524c030d2549300c39b424c030e6509300c3d2514c030d6545300c3d1514c030d4545300c39a414c030e6105300c23d63953208f98654c823f63553208f18554c823e64d4f208f59353c823e6494f208f59253c823e6414f208f59053c82766114f209d58453c823f65d0f208f59743c82b960d0f208fd9543c823d6550f20d314d32c823f64547208f19151c823f65907208f59641c82ad62907208fd9441c823d6510720a758c41c82ad6210720ae58041c832d54c8720cb55121c82ad62d0320abd8940c823d63952208f986548823f63552208f185548823e64d4e208f593538823e6494e208f592538823e6414e208f59053882766114e209d584538823f65d0e208f59743882ad62d0e208fd95438823d6550e20ae58342882bb6050a208fd91518823c64546208fd96418823d6590620ae582418823f65106208f594418829d6310620ab58841882b96010620d614d308825e63951209758e544829d6395120c798e544823d6395120c758e544821d63951208f58a544832d62951208f986544823d6095120ce582544823f63551208fd89544832f62551208f185544823f6055120ced81544823e64d4d208f593534823e6494d208f592534823e6414d208f59053482766114d209d584534823f65d0d208f597434823f6550d208f595434831f5350d20c714d43482b960d0920aed81424826c654c920d314d32482e8604c9208f993514823d64d45208f990514823d64145209798c514825d63145208f59641482ad6290520ae582414823d6510520a758c41482ad6210520ae580414832d54c8520cb55121482e86048520ab58b404823f65501208f59540482af62501209e1953048358534c120ba18930483c9324c1209798f540825d63d50209d987540827561d50208f596540823d63950208f986540823f63550208fd89540823d62550208f185540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c208f992530823d6494c2097596530831e5494c20c7552530
  | 3 => 0x940ad58432502ba600c940ae58032502b96094540aed81515029e6314540a758c51502ae6214540ab588515031e63145408f58c515031d63145408758c515032e62145408f588515032d62145408b588515033960145408f997315023d65cc5408f19631502ba608c540ae582315023f654c5408f195315023e650c5408f59431502ae620c540ab58831502ba600c540ae580315023e65c85408f597215023c6588540ae98221502b960885408fd95215023c65485408f994215023d6508540a798c215029d6308540ae98021502b96008540ae587505031d53d0c408fd95431032d52d08408fd95421023d6590440a758c41102ad6210440cd94441102b960104408fd95401027b6550040ce951401023d62953308f98654cc23f62553308f18554cc23e6494b308f59252cc23f65d0b308f59742cc2b960d0b308fd9542cc23d6550b308fd9151cc23c64547308fd9641cc23d6590730a758e41cc23f65107308f59441cc29d6310730ab58841cc2b96010730c755331cc31d544c730a758f40cc29f63503308f58a548c23e61952308fd89548c23c6155230ae583438c2bb6050e308f992528c23d6494a308fd97428c23d65d0a30a758f428c23f6550a308f595428c23f64546308f191518c23f65906308f596418c2b960906308fd94418c23d6510630a758c418c2ad6210630ae580418c26e62951309b58a544c2ad62951308f58e544c31d6395130cb98a544c23d6295130cb58a544c22d62951308f986544c23d6095130ce582544c23f6355130c7d8d544c23f62551308f185544c23f6055130ced81544c2b960d0d30aed81434c23e64d49308f593524c23e64149308f590524c27661149309d584524c23d65d09308fd95424c32f5250930cb149424c34c524c930b6181324c23e64d45308f593514c23e64145308f590514c26e62145309b588514c23d6590530a758e414c2b960905308f594414c29d6310530ab588414c2b96010530c7553314c31d544c530b6181314c29d63d01308fd95404c23d6550130a7d8d404c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c23e61950308fd8d540c23d63550308fd89540c23c61550308f990540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23d65d0c308fd95430c23e64948308f592520c32e5494830cb552520c32e6494830cb592520c32f4394830cb50e520c32e5454830cb551520c32e6454830cb591520c32f4354830cb50d520c23f65d08308f597420c29d63d0830cb94b420c32d52d0830ae583420c23f65508308f595420c32e5250830cb549420c3365494430cd552510c3665294430d954a510c3376494430cd192510c3374394430cd50e510c3374294430cd50a510c23f64544308f191510c3365454430cd551510c366
  | 4 => 0x798f540865d63d50219e983540867960d50218f596540863d63950218f582540863f63550218fd81540863e64150219798c540865d63150219b988540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f430863f6550c218f595430871e5350c21c754d430863e64948218f592520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420872e52508218fd96410863d6590421c794e410871d5390421ab58a410863f65104218f594410869d6310421c794c410871d5310421ab58841086b96010421cb553210874d53c8421d554e210866f6548421cb551210874d5348421e910521086776548421d554d21087a742484218f992500863d6494021ce95250087395494021d694e50087595394021ce99250087396494021ced0e50087394394021ced0a50087394294021ce90650087384194021ce95150087395454021d694d50087595354021ce99150087396454021ced0d50087394354021ced0950087394254021ce90550087384154021dac8550087722154021da48550087712154021c754f43d032d52d0b40a798c41d029d6310740ab98841d02ad6210740cd94441d02ae62d4f40ab58b53d02b960d4f408fd8953d023c6154f40ae58053d029e63d4b40a758f52d02b960d4b408fd8d52d023c6154b40ae58052d023e65ccb408f59732d032d52ccb408f99632d023d658cb40c754e32d023d654cb408f99432d023d650cb40c754c32d032d520cb40e34c832d02b6610cb40ad58432d02ba600cb40ae58032d02b960d47408f58e51d023d6294740a798c51d029d6314740ab98851d02ad6214740ae58051d023e65cc7408f59731d031d53cc7408fd9631d023f654c7408f19531d031d534c7408f99431d023d650c740ab98831d02ad620c740ae98031d02b9600c7408f99721d023d65c8740cb54b21d023f65887408fd9521d023c6548740cb54921d023e65087408f59421d029e6308740a758c21d02ba6008740ae58021d031d5350e40cb54942903365190640a758c41902ad6210640ae580419031f5350d408f994435032f52509408f994425025e63145409758c515026e62145409b588515023e65d0540cd14641502ba6090540a798c415029d6310540ab98841502ad6210540ae980415023d62d4d408f98753502b96094d40aed81535023d63d49408f98752502b96094940aed81525023e65cc9408f597325023e658c9408f596325023e654c940aed8132502b8604c9408f994325023d650c940e34c832502b6610c
  | 5 => 0x530c63d6494c318f597430c63f6550c31c794d430c63e64948318f592520c72e5494831cb552520c72e6494831cb592520c72f4394831cb50e520c72e5454831cb551520c72e6454831cb591520c72f4354831cb50d520c63f65d08318f597420c72e52d0831cb54b420c63f65508318f595420c72e5250831cb549420c63f65904318f596410c69d6390431cb94a410c72d52904318fd94410c63d6510431a758c410c6ad6210431cb948410c72d5210431ae580410c71d54cc431d354b310c765528c43197d95310c71d544c431d3549310c794414c4319dd95310c797434c431d9549310c63e64940318f592500c73a5494031ce552500c76a5294031da54a500c73a6494031ce592500c73b4394031ce50e500c73b4294031ce50a500c73a4194031ce106500c73a5454031ce551500c76a5254031da549500c73a6454031ce591500c73b4354031ce50d500c73b4254031ce509500c73a4154031ce105500c75b3154031dc8c5500c7593154031dc4c5500c63d6395321cb98a54c863d60953218fd8d54c863f60553218f99353c863d64d4f218f99253c863d6494f218f99053c863d6414f219e98053c86796014f218fd9743c863d65d0f21ab58b43c863f6550f218f59543c872e5450b21abd9542c872f6550b21abd8d42c86ac6150b21abd8142c86ad648cb21ab59132c874c534cb21a758c41c86ad6210721ae58041c863e64943218f59250c863d63d5221cb58b548873661d52218f583548865e63152219758c548867a60152219e580548869d6315221ae580548871e63152218f58c548871d63152218758c548872d6215221cd984548873a60152218f580548873960152218e580548863e6494e218f592538863f6454e218f191538863e6414e218f590538867a6014e219e580538863e65d0e218f197438863e6550e218f195438871e5350e21c754d43886b661d0a21ad18542886ad6290621a758c41886ad6210621ae5804188795434c621cbd53218863e64942218f592508863f64542218f191508863d63d51218f583544863e64951218f994544863d6315121cb588544863d60151218f992534863d6494d218fd91534863c6454d219ed8153486786054d218f990534863d6414d219e98053486796014d218f997434863c65d0d21ab58b434863e6550d218f195434863e65d0921ad98742486ad6490921cb152424863c6550921ad185424866c6550921b9185424872f6550921cb195424862c6550921abd8d42487a76150921ab18542487a46150921a918542486af6050921ab592324866c654c921ab591324874c534c9218f996414863e6510521a758c41486ad6210521ae58041487a5428c5219d1953148795434c521e950931487c5324c521e950b21486af64885218f990504863d64141219798c504865d63141219
  | 6 => 0x71d534c841cb549321063e650c8418f594321071d530c841cb548321078d320c841ad98432106b5610c841ae98032106b9600c841c794e511071d5394441cb94a511072d5294441cd98651107965394441e554e51107a65294441e954a511069e63d4041a758f501071e53d4041c754f50106ae62d4041ab58b501072e52d4041cb54b501071d5394041cb54a50106b96594041ced4e501079a5394041ce54e50107995394041c654e501073b5294041ea94a50107395294041ea54a50107295294041ce94650107b25194041c794d501071d5354041cb949501072d52540418fd8d501063f6254041ced95501073b5354041ce94d501079a5354041c694d50107395354041e654d50107195354041ce14d501073b5254041ce94950107aa5254041ca94950107395254041ea54950107295254041ce149501073a5154041ec945501073b6354041ce98d50107396354041ce18d501073b6254041ce98950107396254041ce189501073b3254041ce8c950107393254041ce0c9501073a6154041a798c501069d6314041c754c50106ae6214041ab588501072d5214041ae98050107395014041c798e54cc63d62953318f58254cc63f62553318fd8154cc71e5450f31a7d9543cc71f6550f31a7d8943cc69c6150f31a7d8143cc63e6494b318f59252cc63f65d0b318f59742cc69d63d0b318fd9542cc63d6550b31a759332cc69d644cb31a758c41cc6ad6210731ae58041cc63e64943318f59250cc71d63d52318f58b548c73661d52318f583548c66e62152319b588548c67a60152319e580548c6ad6215231ae580548c71d6315231cb988548c63d6215231cb588548c62d6215231cd984548c73a60152318f580548c73960152318e580548c6b661d0e31ad185438c63e6494a318f592528c63f6454a318f191528c63e65d0a318f195428c72e5250a31cb549428c69d6390631a758c418c6ad6210631ae580418c71f54cc6318f992508c63d64942318fd91508c63c64542318f58b544c63d60d51318f992544c63e6515131c758c544c63d62151318f580544c63e65d0d31ad987434c69d6490d31c7152434c63c6550d31ad185434c65c6550d31b5185434c71f6550d31c7195434c61c6550d31a7d89434c7976150d31a7185434c7946150d31a5185434c69f6050d318f990524c63d64149319e980524c67960149318f997424c63c65d0931a758f424c63e65509318f195424c69d64cc931a7591324c74c524c9318f996414c63e6510531a758c414c6ad6210531ae580414c79543cc531a7d92314c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f58a540c63d60950318fd89540c63f60550318f990540c65e63150319b988540c66d62150319e980540c67960150318f992
  | 7 => 0x494032ce552500cbc93294032dc946500cb715194032ce992500cb396494032ced0e500cb394394032ced0a500cb394294032d34c9500cb3a5454032ce551500cbc93254032dc945500cb715154032ce991500cb396454032ced0d500cb394354032ced09500cb394254032d6cc9500cb6a3254032d64c9500cb693254032d24c9500cb1d53d0f41cb54b42d071e5350e41c754d439072e5250a41cb54942906b661d4e41c7d4e539063f6254e418fd8153906ae6214e41ab58853906b66114e41ae98053906b96014e41ad987529072f5294a418fd8d529063f6054a41a798c529069d6314a41ad98452906ba6014a41ae580529063e65cca418f597329071d53cca418f996329063d658ca41cb54a329063d654ca41c754d329072d524ca418f994329063d650ca41e34c832906b6610ca41ad58432906ba600ca41ae580329073b50942418fd8d509063f6254241a798c509069d6314241ab98850906ad62142418f997435071f5350d418f997425072f5250941c7991531071d53d0c418f596431071d5390c41c794d431071d5310c41d394e521074d5394841cbd0e521072d4394841d394d521074d5354841cb991521072f4354841cb90d521072d4354841cb10d521071e53d0841c754f421072d52d08418f596421071d5390841cb54a421071e5350841c754d421072e5250841c754c421072d5210841c754f411072d52d04418fd95411071d5350441cb54941106776550441d694e50107595394041da94a50107695294041ced0e50107394394041ced0a50107394294041d694d50107595354041da94950107695254041ce991501073b4354041ce90d50107394354041ce10d501073b4254041ce90950107394254041ce109501073b4154041ce50550106ae62d4c41ab58b53106b661d4c41ae98353106b960d4c41a7596531063f6254c418fd81531071f6554c41c7d89531071e6254c41c7589531071c6254c41c7985531071c6154c41c7d81531071e6054c41c7581531071c6054c41a798c531071d5314c41ab98853106ad6214c41ad98453106ba6014c41ae580531069e63d4841a758f521071e53d4841c754f52106b661d4841ae98352106b960d4841c754e52106ad6594841cbd4e521078e5394841cb54e521078d5394841c354e521071e5354841c754d521063f63548418fd81521072f6554841cbd4d521072e5354841e394d521070e5354841cb54d521078d5354841c354d521072c5354841cbd8d521072e6354841cb58d521072c6354841cb985521072c6154841cbd81521072e6054841cb581521072c6054841a798c521069d6314841c754c52106ae6214841cb54852106b66114841ae98052106b960148418f997321063d65cc841c754f321072d52cc8418f996321063d658c841c754e321072d528c8418f5953210
  | 8 => 0x200000000b004005002003000000003007018000001002001000001000009003002000005006000000003000000004004ae98352d0eb960d4b438f18552d0e3f6054b438f58a51d0e3d6094743ab98851d0ead6214743ae98051d0eb96014743ab98b50d0ead62d43438fd8950d0e3c61543439b9885150e6d62145439e9805150e796014543a75875350e3e61d49438f5835250eae6214543ab5885150eba6014543ae5805150f2e62145438f5885150f2d62145438b5885150f3a60145438f5805150f3960145438e5805150e3d62d41438f9875050e3f6550c4397d954310f1e5450c43c754f43d0aad62d4f42ae98353d0ab960d4f428f18553d0a3f6054f42ab58853d0a3d63947428f58251d0a9e6314742a758c51d0aba6014742ae58051d0a9e63d4342a758f50d0a3f63543428f18550d0b1d5350e42c7d4d4350a3e6510d429798c5150a5d63145429e9805150a7960145428f9875350a3d60d4d42ab58a5350aaf6254d42ab5875250a9e6314542a758c5150aba6014542ae5805150b1e63145428f58c5150b1d63145428758c5150b3a60145428f5805150b3960145428e5805150a3d63d41428f9875050b1d53d0c428fd954310a3f65508429bd954210b2e54508428f98654cca3d60953328f18554cca3f6055332a758f42cca9f6350b328fd9151cca3c64547328f99250cca3d64943328f986548ca3d60952328f185548ca3f6055232ab58b438caaf6250e328fd91518ca3c64546328f992508ca3d64942329e982544ca796095132ae582544ca3d6395132c758e544ca3d6295132cb58a544ca3e6195132ce982544ca3d6095132ce582544ca3960951328fd8d544cb1f63551328fd89544cb2f62551328f185544ca3f6055132ab58b434caaf6250d32a758f424ca3f65509328f595424ca9f63509328f993514ca3d64d45328f990514ca3d64145329e980514ca7960145328f993504ca3d64d41328f990504ca3d64141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540ca3e61950328f582540ca3c61550328fd81540ca3e64150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430ca3f6550c328f992520ca3d64948328f597420ca3f6550832b358e320ca5f654c832e3d09320cb8d424c8329bd95320cb8f434c832e350d320cacf654c832d3d95320cb8e644c832e3591320cb8e544c832e3551320cb365494432cd552510cbc53294432cdd92510cb346494432cdd0e510cb354394432cdd0a510cb3542944328fd91510ca3c6454432d34c9510cb365454432cd551510cbc53254432cdd91510cb346454432cdd0d510cb354354432cdd09510cb354254432d5cc9510cb663254432d54c9510cb653254432d14c9510ca3e64940328f592500cb3a5
  | 9 => 0x30278cd0c6b61300000005de2120001e08e2000000000000000d88bb2e4c2746fe000518000000000c76e54e6653c000000000e38000bec0000002fab580a828eaf62646d2052c1a9da77c000eb003e000bfc2d03cc95417c20200036c00000000031c000000000c84ccc00000000000100100100000700400400000000000200400000000000100000200100000a00a00000000800900100200000000000100000200000000200a00800100100200200000100000900000a00300000100000600300000000200300400000100800000b00000000000100500000100600700000200000f00100200100200100400000b00000500000200300000000100300600100000200700000000100000500300000200a00000000300000201c00400000800100300100000100100000c00300000100100100a00200700c00400000000000000a00a00000c00800900200100300400000600400000000900200000600200100100000000c00000001400300300200000700300200000100500100300000000200000100000c00300100000200100100500100600100600000000000100000c00400a00000200700200000700300000500300300000200200500800000100300100100000000100600500100200000600000200000000b00000800000000200700100100600100000800200800000400000000000000101500800200000a00200200f00200e00000700000c00200000000000000501200000000000200200100100300000001100200400200100000000600000600001900300100100000100600600000100300000000000300000800100000400200000300000600900300000100100000100e01200000500500900000000000200200000000100200500000000300700000000600200300b00300000200200300800000a00600900100000100900500000800000000300500400100000000500200000200700100300500f00000300000100300000200100000100d00000000400100000c00600000000600302400200000000200100000100300400000000200100000200000000000000400100e00200500a00200100000000000100000400000000100e00000c00000100300200100000100d00600000300100300000200300100200500c00c00000000000000001700200200000100000000100200000100100100000100600300100200000700100001600500000000000100100000800100100000500000000700000200000000100300300000800200000100000200100000600600200300000100000100800500a00f00100300100200200100000300100200100000200500800000100100500000400100100700c00100100000600000200000000300500500000000300400000400000000300a00a00000100600500000000000000400
  | 10 => 0x1e1a42361ace28c36010862000a300006a44143ea0a00001560008cce3cad8866570900afe00000087800061a0007dad800009e0baea1eb4448807e000000000752b90000000624000e221ba066cd6000000000016e9a968000000000000000eb4000000d6aea858453a00000000050e19800000037a0009280000004001da9ec22a000a2cdb60009cc000a9a95a000000000b3ad845cc0004c60c20009a8972a1200080e0005fc4720ca2d4e94000a34000c0087220c182802df07e2486536a38be400092c5feb8c6b8b0600084a62ccf062e0000000002b02c8d10000a9212c000000334cf24fa0924560000f800058e08ea88b9a000f0600000069eb1ed90680796000b2c94a9aa00056e7ca00094c000196f04a060004bc8b439400000000018600000000074a0000003b6baa000000000cd80005b6000000000000000000000828000300be0d4a0007580008acafc000000000748000000000688b2e29200054a4c447ed8ea24a6c000a9000000052a000000000000bb43380009e4390f0e63c99c2e80fe0000000000008ba0c40006e800069abc2000000516000ea60009fc6f2c9c088dfc346000000c1e000b5c000134000000000aa40006f8000000000000cde0000006a6412000000c5c0000000006ba9ee00000001a16c000a6eeec3600005863b439e8a000000000024400000034e8863268a8498cf883a65a87ab66aa0000000e400005f06200000000000002d8308000000000000d7086a0005fa000e06490de4000000322000000000df2000a1a44ac5a0568d84080684fec32b76d8221a000000000000000000bd421625a1040980001fc43a000c606daba0000c12d440006d686e000cd00009fe8b261638e000000046000382e6c9f6ca47843c08b6000bba000100000000000b9e114000914330000000000836a3a00010208a00000075e00000089a0000008debc0000252b94000000e84000000000dca0001d2d488ec11848ca70b1a0003acac6626bde18a436d14d7e1f000000097e59e0ac64a256000000cca000000aac4b0c7c0000006cea6800065c26ad640b882aef20000002dc000000a3edbccda912af48301620000000000000000000006e00000000003fcb68960e6a0d4a2a000d9ef120000004060000005caece8080005dc000e320009a2a623646e600072e4b4c6a00000013806e3524f009a000284c624603a4000000000d2c678ed8000aa8c38792000000084d260009080000001d48c80000000000001bc0000000008f444600046cc98000000000030000d04000000376e3ad52e78000794000000a26c260000005eeb86000000000000ce00008820008f00008e6c54de249e83400015e00a6ac0005d85e69c2caa8128b0000000dfab728f6000000000000000e8c000000000000534cae0000000000000009de
  | 11 => 0xa4287e3e06100008ca1f400014c0004f65a200e0004dea2e8dcbd62ce83c0000000000000000005f8000e000004d2000c4c926ee48144f486cba2776cec35cb56000916000ca6ce800000000000000000000000092e27e00033a7e60000003bac083e400000000070a552000000efe4626fccc6000000000ac015c0001f8000000000000ca0000336506d9a640000eb64e62621d07f63f80002ba000000000b160008420000000000003789f8000e763f00006b2cfc000e5082c56ca1ce980004e433c0000004a00000002ee7ea0002e2e140001d6000eee22e4f27ceb8ae30d3a60247471843e32e000000000c2a10a00000000000037ce361740000000000007540b4000000000276000000798000682058ce20000002c20001260000000006460ba0000000000d60000dc96610e00069cc9eae212072a6a8398b880f2a86a36f0c00000000030eaa22e0000b6a57e20a98c08c000ed20000009c89eabf2000dccf083ca2800004e25d078a0001360240005b4036ef0000ac4242cfe0004c27be9621408520000002720000008f2e649ae4684322a82f2730b3c00000074e944cbe4ee00056442e73a634000cf4e0e000d560000ea000000000000164348000cb00005a605ae3eb24430606790000d3c310188340b7a0e2b300b0a14bee99a4a6e04e600009a0ab0000ed41e253898e000000000000db45228f8000000000a967cc6126f4000a0cc6e97a75609c81a000000000bdc192b0c044614e962a492a958e7e0000e00007c076019400052cb704a8e9c39611a000bb60001b62b4422ae497c000000000726000000368000000000000000a4e000d34000000000692000000000bda99e6d8000000000668304654000000d6c0009b8bf8bb09d40000000c8000060000208000d0800045a3922d63e650a1800001e4ebee1000064c7b28e00820000000003f420ecf60aad7c8ae0008c0dd8cc2e20e58aae1ae6cc7e049c3daa445406c6000c68286000150970a5aab8000e1aad207c6c48580006c2c6630a79e5f60004585da922f0a51c424148d62184000000e52e46abe93288a000000000874000c5e898b14d86000000270d324500009e24cc998152000ad6230000358a4c19a6de6dc894a52000e4a980ee6c3caf260a89e25e29e8261729f4bb8824bc8ea0d3863226e8eea5871aa8224ec0e4ca8160000009e62545b800000000000000023e000000000b1c3208e8000c2c000dee00085e00000000055ec7237e33e7dcdd67420e88604b6850c2878e5040007f4064000766000b32000000ef8546dba0000000000000006cac0abce2f00008bcaec00005c0000000000000009fa2280000000001f200077e52618c0000000000002380000380000cc008000bfa0000002c40000000000000000fa000000000000d2a4c875cb6e6720d07706
  | 12 => 0x8a2e6e206c6c000990b98950312c505bee44a780001eac14c8a5f419c2b27fe4d882200000000000000000065eafa00000000000014a6567089d603ab808d46aed92d287d23e88fa49a3d01c244007a7e8a600007c2e26354d7a96a00084678200039c2c03fa04e00000000001edda0960a466c000e16716da4b0e4a4000b4867e0000000000007ae00000064e000c803b05a00000008d27a400018e89c79c84054e548000ec0000000000c8c67a838520db8000592666a940000006c82900000009827043a8444dc4000b280a25281a2c3ee724f8000ab2e24442496454a5e1a828868cace4524ea03c6580004dcac25e2d12000000232000598a80000aca00063e788c348c20003ae698804000000000000b20000000be2000000d1685aad00000000000000006ecc7a942d18000000600000000b22000a540000001127640000022aa00080076c72c5b00003720000003b87003c4dc2222b7e2cc5744e81cc00c000000774b34000000000000d6051000073c0000000000001220be6ee84c63adea000aee00000088e38015a1060001c80000000006a0000000a9e0008920005ce094ef600093002ec52000000000426ed048a062c0c000324b38000a4800000035e240b74000000686000b3e0000000000000005080009f0000000d9c0001580000000000002fc000000b7c000e2c0009dcae8650eb8028cb825c652404c965f200061c2ecd5c9ceeea000048c0434cee000000000006a000c30000000000166154000000000000670000000000b3655867c2500001b4a10434772000000000000eca5d45720000000006d4000000000050234d0e00000016e000000000ec659aa02a0a08000000031e000d208a4000000b78000cb441c832c407b60e60320009d00eedb068a000c900000000000000009c4e342decd244e4800000004645e43d8a8421c7120000000f492000030c00090a9b617038a16852466e0000ae000000000000a3c98a020000000a72000000eac1e600000085cd4090684eb64040c22000034000a160009be73e00083eb1858c3440003a0acc000dec60412a7bc00042a000178000000be846613e0900003be70c000000000000dac0000000000007a6578000000000000cbc0bc0004820000e40001be0000000006d0c20b603dc40e0001de848aeadb2000dc60007f800029600000032c0000000000003168be4d6aba50cb0a000550ad4e5c0001fe95cdc85d2076adc000e8200002200088c000aa6d0a4166c096e00057c4d454c000ac800000080a00000080c00013a4d0ba82a2bc4ada0000000007b4000a740000000000000000000000000003c82a0a7c23a7a87f2902000c18000eaa000964b4a0003dee9ec460000000040000007ec57a5326629f2d1e3a2ab40008d04ce116ddedbe000a2000047000000017e00
  | 13 => 0xd8ef4a00000000da8000b4e0004fc000000c82370000c06000e420000000000000003741907ac56a000000d682a6b960000000000000007ee000000ea2e8ad4cc7e5907b0dd297416a7023ce9b23a6b8274c41eb120f0cb69a67620007c4000c94000000a40000000b8e4e01c08ea00062210c000000edc000c2e0000000006480003ec000000b9c386d96000000306514d8a246a0894e428000b46000000000000de81eea04000000952a0e3fe0006302ca000d3e96c72272812e0000004dadf8006000000000000ae600000000000026c0007320007de2f45a81e814200001828a0008e491e7e4eaeddcc487780b600071000039a09ea760000000005965c04106963d4108c3a6841249189960000008ce00000029cb923181c6484df62bc46e000d0287ce7ce5a6ea000000000000d8c000000000000000000000000de00000003c6b620000000009d8000e5ea46026da0810cc090e000bd00009ba2ea0000005544c0a289886aaea4014000000a18dfe1b293c0002262102e69c081e6b07d40000002780000009b0dd4e4e000a22c88a8aa9c2acc1c000b5ae5656690c7ba0000003bc000000e920b2000000074000000934000000000e746e40008fca8ed24000b04daa0005acc9a0ec6440007fc000000d30ade000bea2240000008180000000000002da00000000051e3427aa00000098600042c00093ebd26b416028c870a7aba6e2a1d80005b2dc02045c6282c740a649468ea6a34a62a258e68c16c9259c91aae06606288847b8e08a984be448d783f6000ec8b5414edf48642ae4ac27c00024a0003d67d08aa000ca27c63c2e7066460ec4e000ec2e0a9785c8e8871c81c1f600056006c0006742483f235a0008684762148b80000001a60de000a64a506be000000d5a82e910000000cba0007f0000e7a00000054466a0000000000007c8c56ee2c640005e0000c7847a4ae21e5d6a66218cc8d5e1ece621b8c0200040cd742fe820d4e2b858227acc4bf4000b087460008966940000f6d2e000b02bbe0000005a42c60000000000007388a600036600000095e4aae908c65e84a202a46a35600036a00000023c0c029a00000017ac4a41a000000636a8c000200aaa8d60000000000000000005c400000036e000890000000000000000efc110000d980000000000000005123625769e8384144736000ed69c6d502f6000b5055622c1a01c4000b0079a000638946cd4cac2668da0000fc24c000000a5cab694876845c000eba000000ecc0000005aeeb243819eb2613c54205e9925bac440da000000b842d272444c3d2efa0000009bc04c924b429ca08600002c76e2e4420cea76a000ba4cb20005ec000daed3631a000854000d943880d2000da20000000d8e1e0003b2c10b4c880d1c000b5e95600055a9b42f8580cce000530132c86000
  | 14 => 0x6a200091c7d8d46b6c58ab2ae1858860c2606f601cf000000004b20000009d28065aa00059404a00053e706000000c4270e0002be3aa856000000000000618da65bc000000bac328072e1211c1aa994af811edd040a4ecbca51ad6e5009ace8675a000d22042676000012ee8d1a000e484bad541b000000038cc8ee1c000000000000000de6176be600007000000097674493a904d428febf0940936714000ce6000e02000128750000000a326bce80000000000000000ce4000000000000642af06f043cbfe7d6dce00052ec24abcbf67a20ce98477a1ced0032a55c6082943320001dcd58780d72cdc0003146e25c293847c0000000000000005026fa2200005680001ca5eaedebc6d66cfa00048e000a7eb10146f02b52f10e0c49273445e478418d763e2740c58000000a562b6c70000ca8a4a000d060c60000000000000004b8000000000000000000ebc2987fa0000000000003ee00071e000268e2ee8e4029a40000007a08c4bcc0006900008761fa000000844786054cee000000000562ec4350000b40000000000888720000000000000bbceda000078000000000000000b
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x905157114d43482a2b88a699241385c4604c92083ae7326a29041f73596414829238aa890a41325cc604852083ae7b2a80905517114d3048270b88c498241521d5324c120c90ca992609041d731855408306a9ac5a18418654d60d0c20a2ae6324a21041d73191510828ab98c8a8841495cb4354420a62e1a1aa21041d73d94410820fbaac620841075da531042083aeca98821060e535884108306a9ac4208418558e5110420c4ac52888210615635444108312b12a2208418694d6010420c32a6b008210632515804108318a8ac020841c254f4048020e42a3a024010709535012008390a8a8090041c254f4248020e12a6a124010723425452008390a12a2900414a5d66448020b12e7322401052b7559120082b0b8ea690041525d65348020e14a8a9a40107095454d20083853a2a690041c25d15348020e14c8a9a40107096454d2008254bb68690041c254f4348020e12a6a1a40107415394520083912a2a290041c85515148020e84a6a8a4010741535452008391ba2a290041c81d15148020e44c8a8a4010721645452008391a1aa290041c850d5148020a52eb20a4010709539052008390a8c82900412a5d84148020a52ea20a4010589731052008384a988290041c85444148020c64c2b06a98860d6398854c430731ac42a6218358d6215310c34c6b00a9886196358054c4315312c02a6218a589601531085ae432e878842d7219543c420eb98cba1621075cc6550b10a28eaa1a63885247550921c424ab98c2a0621295c8615031085ae5b2e870841d73d97428424cb98c2a04212a5c86150210a92e429a610854973149208420eb98c22a2210b5c86115110870eab0686884b071583434421c3aac1a12212c1c560d0910a28eaa1a628852475509214424ab98c2a0221295c861501109a2e630a80884e172185404424cb98c2a02212a5c86150110b22e630a80885a17218540442593a8c2a02218c9d46150110d24e630a80884b1731854044348b98c2a0221245cc6150110d44e430a80884b1721854044350b90c2a0221285c86150110960ed18a80884b0764c540442583b442a02212c1d92150110960e2b24608843875591304425838ac898221525c8534c110aa0ea98a6088691644c5304425838ac9102210e1d56448110960e2b2240885497314920442b03aa4290221a85912148110876eab048208619535824104314a92c120821075cf651041085ae5b28820843970594410420fbaac620821075da531041083aeca98820842f75588410430729ac4208218354d621041085aed290820860d639484104216bb2a4208218358d5210410c34a6b008208619535804104315292c0208218a5496010410a62eba02200871153d011004390a9680880214c5d44144010b22e620a20087115310510042d0b908288021c85484144010
  | 1 => 0x4248658b80c2a1243315cc61509219c2e030a8490c8d731854248654b80c2a1243615cc6150921b42e030a8490ca67518542487133a8c2a1243a19cc615092194ae630a8490e85731854248642b98c2a1243a89c0615092194ae030a8490ea1701854248650b80c2a1243291c5648c921858eab226490ca47159132486a4b80a699243291d9428c521a28eaa1a6290ca476509314872232a6498a43615d1324c52185eeab148210e0d5358a410860eb9eca2084307dd5631042183aed2988210c1d7654c410870729ac4208438354d6210421876eab008210e1a53580410870ca9ac020843495d44148421b0ae620a4210f055310521086d0b808290843495d74248421e0aa7a124210c3976106500868cb9883280434a5c84194021a52e520aa010d19731055008694b9082a8043c81052154021e468490aa010c2d7218553d020eb98c2a9681435d5320cb40c2aa6b0865a06255258432d0342992c2196818654d600cb40c52a4b0065a06893258032d0216b94cb98e81451c5534c74083ae732e43a05247154921d0258b88c099281a14c9610c940d1264b0064a060d63988515030731ac428a818358d6214540c34c6b00a2a0619635805150315312c028a818a589601454085ae432c62a041d73196215030ab1ca2208818958a511044085ae430aa99842d72d9441cc28a38aa898e610b5c8615523085ae5b28831860d6398a544c315312c12a2610b5c86155130a4ae2292849854571149324c268b88c0992610b5ca64d453085ee4b2c829851471551314c264b90c098a610b5c86155030c1ac6a96841862952583420c292b90c9288610b5c86454430a4ae4322a21851573d09510c298b8684a88610b5cb651043085eeab10821842d76948410c306b1ca4208610b5d95210430c1ac6a90821861563944410c312b14a2208618558d5110430c4ac4a88821862a52580410c314a92c0208618c9456010430c62a2b00821870952d01300c388a8e8098061c2549404c030e22a2a02601870b43549300c384a1aa498061c4d0d514c030e2286a8a601851975991300c2c4b94c89806146dd5644c030e14a8a92601870954549300c3853a2a498061c25d1524c030e14c8a92601870964549300c24cbb68498061c254b424c030e12a4a12601874152945300c3892a2a298061c4551514c030e84a4a8a601874152545300c389ba2a298061c41d1514c030e24c8a8a601871164545300c389a12a298061c4509514c030a32eb20a601870952905300c388a8c8298061265d8414c030a32ea20a601858972105300c384a908298061c4544414c03083ae630aa9905457114d32c820eb9eca20e41491c5544872083ae630aa91041d73d9441882a8b88a6984418398d6295120c34c6b04a89041d731855448216b96cba1a410e5c365d0d20868e2b2a86
  | 2 => 0xc2a9083439cc6054841a1ae6302a420d26711815210714b00c0a908307dd95314841c1aa7310a420e0e635485210706b1aa4290838554e6114841c32a7300a420e2952980521070ca9ac0290838a5496014841872e132e6420c3970996321061cb84ca19083435d5320c841c1aca9906420e15539843210712a94c2190838554d610c841c4aa4b086420e8532584321061cbacc0190838654e600c841c52a53006420e19535803210714a92c019083a24c9600c841e0aa6a94a220e0d5398b501070729ac5a80838354d62d4041c1ac7296a020e0e6354b5010706b1aa5a80834a5cb5394041a32e7a94a020f095394a501078529aa528083c254d5294041a54e5a9aa020d2972d4d501068cbaca6a80830e9d85354041a34e629aa020d2a7214d5010694b90a6a80834c9c45354041a34e7a92a020d1973d495010694baca4a8083c294e5254041e12a7292a020f0a535495010784a9aa4a80830e9d85254041a34e6292a020d19731495010695390a4a80834c9c45254041e22a728aa020f2152945501070cb18c6a80834a9c86354041a52e431aa020d327118d501068d398c4a8083465cc6254041c52c4312a020d3271189501061d3b064a80830e5d83254041e1264192a020d32710c95010698b8864a808307dd95314041c1aa7310a020e0d535885010617bb2a4280838398d5214041c1ac6a90a020e19539805010714a94c0280838698d5014041c32c6a80a020e2a625405010714b12a028083235c86150f31932e030a8798c3970d9742cc70ab1cc3aa4638358e6215231c1ac6b10a918e1963980548c714b14c02a4638658d6015231c54c4b00a918e2962580548c652b90c2a1c632c5c06150e31872e032a8518ca572185434c658b80c2a1a63315c86150d319a2e030a8698c8d72185434c64cb80c2a1a63615c86150d31b22e030a8698c9675185434c70b3a8c2a1a63a19c86150d3192ae430a8698e8572185434c642b90c2a1a63a49c06150d3192ae030a8698e9170185434c648b80c2a1a63251c563d0931928e2b266498c9471591324c6a4b80a49926307dd56390431c1ac6a948218c2f75588410c616bb4a4208638358e5210431c1ac6a908218c3b75580410c715292c0208638a5496010431a2aea20a6218d8572105310c782a908298863645c0414c431a2aeba1a6218f0743549310c61cbb08328063465cc4194031a52e420ca018d1973905500c68cb9882a80634a5c84154031e208298aa018f13434c5500c61cb86cba1e43235cc6150b21952e030a8590d497014d32c8712b14c3aa4438398d6215221c1ac6b10a910e19639805488714b14c02a4438698d6015221c32c6b00a910e2962580548861cb80cba1c430e5c06550e2192ae630a8510cb170185428868a3aa8698c430b1d562d0d21948e2b168690c9573185
  | 3 => 0xf900018000097800000000cba4443e0001e90336c000ba800000000000000006791a0fe17e0000021a0000000697300000002800414000000000000010380000001c000000005c4000ce12824c000a72f000000000000000001ff0006500000015e0004d8002700bc0024a0c8299008f83c42588d1270000000005d2ac000000000ac21000231000808e5000000000b08000200000000000076800000258000fa16d2c8000a498a024624ea1701da354721d037e4cc0014a3f8000000000000000007118845886000256000c194d08c000e380011259c000a827c738000b10084180000029c000000050040000180000f00600801002006000000030060040080100000c0000000001000800000004018000080040000e0020040480001a028020010060000380000000005800000008000000000080000800200003000000008000020000000000a00001c000000040600100000200404007002000028030040000000000001c028000000000080200001003801008020010000000180000000000c00003006008018010000000000101c0000000200200005802004000000000020000000100001000804002000000000060000000000001c01803010014050010080040000300e0300000200000000008000010000000020100000000000c000000000300080100600002001000000004397018552d0e16b90c2a86878a58a6014543c54c4b00a2a1e29625805150e1cb80c2a9e85075cc6154342c32c7300a2a161a635805150b0cb1ac028a850e5c06155332872e030aa91961963982544cb14b14c12a2650e5c06155132872e1326a29943970185540ca86bacc899065625c2644c832a1eeab22641953170192510ca1cb80c8a8865c19513254432e0aa8992a21953170191510cb83a1264a8865c15093254432e0e86992a219705434c9510cb833a264a8865c15d13254432e0ec8992a219704644c9510cba0992a328065c29513254032e12a8992a01974132945500cba0992a2a8065c2d093254032e1284992a01970b434c9500cb84a1a64a8065c29d13254032e12e8992a01970a644c9500cb84b2264a80650edc1654ca41c1aca9906520e85325843290744992c019483835886254c41a2ce2312a620d1a70189531068cb80c4a9883439c86154c41a1ae430aa620d1a70185531068cb80c2a9883439c86054c41a1ae4302a620d1671181531070cb00c0a98838354e6214c41c1aa6b10a620e1953980531070ca9ac0298838654e60d4841c34a6b06a420e19535835210694b86a7290834a9c35354841a52e1a9aa420d0d7594d52106173b0a6a9083439cc5354841a4ce229aa420d2a7014d5210694b80a6a90838358c6354841a4ce231aa420d2a7018d5210694b80c6a9083439cc6154841a1ae630aa420d2a701855210694b80
  | 4 => 0xa000000000002520000000021c0000000024c0007e0222c600000000124000d12260000000000000011d1ba0500052c0000000062cd28ba000000c62182fc88442800000530c10000003a80008c0fc0000022c492168002080000005720b00013c00000000000000000a66ac0006b426000eda1147400000000000000000000007a4000000622a44080042e3200000c00015c001b3000000df00000046c0000026a18039a47000000000001e62e40003c148000f39111e8000e6800000870000002b884050800000000000861700006c000000000000b60d43fc6686838a780000ee0ca000000010001249c8003e000000000000000000000000000000000000095000000000000bd000574000082144a0af8e11100000000031e000b00001ca3583a80000033cf50184760000011f0d80eca81194821886f800000880ad972000830690001ae00090000000000c99403de000000002a24603e9de35e6a4000001d26ec528000dc45400000000918000000007709b1040002a80000010e510560000866689822b000000098000002000009500000063800000350cd8000000006f000000670628000000000004436030c001c600000000107098000ac000000000000000000000021d1c60000ba2837a208e4000000864489b90007d8eb0001e21985980000000c0003647283c001e5000000be1772fa73000000000000d200027a5788e8000006040019517818c00000000504000e23327e0b7000470000c40f630e1c0fe8c93ba31880027346000ab9eb3e289091000000000000250003801c1e63863749e16a0000000000000048400000000308088000000002a90d2a41280000019439c0002e0000008580022654c000000ec0000a8003da17cb799831c0005907f03a6350200044a1e8780000286403a0dc2866451709e0006000000000000000000000104000000003302281b20a000001b1000424000000007086d800000000d6a221380011f0bb42478c5580000000015a1b0000005f00000000027000324000001cf00003c000000000002d9ec000000000002d2000001cb2f20005ba3f3a20005191e06014000000000340bf89f0000007e93f2b40002f072004000c304036a160ff0064120b48089002c0011ea0e4464d000000000000118000b8000fc88307e0000000024600000000000000da2000000000000000080c000000006c80000035c000000003c20cd191a0370754071a81b4280e017616a5990691432c000000342380800021e0648b4eb8000904b83da16204000ec8000545b01080000069c0000004c0000013b33e89c65a360000003680000000014000000000000690004c89b878084001218972e807c05a482c40000000042a0e8000001f655056800000000000000000000000016802400000220365211fa37400000000
  | 5 => 0x34c5140d000284000001aa0ee000001250001f0000001ea0000000000000000000000704000000000000017b00051c4e80036e761178f20000000004d22434ca41d200015000000000684000f9000000f2000000000000000000d40000000000000059000000740000007cc000eb0000dc2880000012d1a88b0f20787319d0007d4879590006b0000000000001223c2627dc1480000026047a061600000000045219cc21240008c04c800000000969e8000000000000003e81f0c10000000008e0000002900048a0b0510390001bc001650000010a0ec0000000000000026868a2a2aa000000f70005a00017a22e71045000000000b580000000000000000420e9800000000ef8000000000000029e7b87781930a4e92000028c6f1198003f6724000000001840e000000000468
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1ba68b978f000084180007019093241fa0230e02002605099d00048399161f0a8c8f80150d25000c228024881a811400069b1592000e989987a096971a100b001e0014801c93891c00000588800300118006000021000023a1801d800da5929e82a200110a0000000332082871c0000200840800000603020818a0408086b01809d13254432b01801913254432a09869d13254032c09625c06254c41c09725806054c41c09635c06354841c09735806054841a05854c9610c841a09854c9600c841c09635c86354041c09735886254041c09764c83254041d01325c43254041c81729c06150d31c82725c06150d31c81725c06150d31891801c563d0931891801c564cc931891801c5644c931d01525c0414c431b01821053154031911801d5434c6218a1801c562d0d21c81739c06150921c82735c06150921c81735c061509218a1801c5648c9218a1801c5644c9218a1801d9428c521904855d1324c5219058754c4148421d01535c04148421b01831052154021a05854c9610cb40a09854c9600cb40905821c5534c740905831c55248740905821c5544c730905821c5544c53090987991524c030c097654b424c030b01821d1514c030b0182991514c030a1186d09514c03090987548414c030c0976548414c030c1176544414c030d0172544414c030905831c55448720905831c55448520909879915348020c097654f4348020b01831d15148020b01839915148020a2186d0d51480209098754c4148020c097654c4148020c21765444148020d01735444148020905821d5434c710905831d542487108a1821c560d0d10891831c560d0910c81739c86150110c82735c86150110c81735c861501108a1821da3150110891831da21501108a1821c5648c1108a1821c5644c110a1085591314c110891831c56488110891831c56448110a208559121481109118754c4144010d01535c84144010921875484144010d01735484144010
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
  | 6 => packedAt s4K6 (880+((h/16+packedAt s4K6 (768+(h % 16)*7) 7) % 90)*7) 7
  | 5 => packedAt s4K5 (32936+((h/358+packedAt s4K5 (28998+(h % 358)*11) 11) % 1713)*12) 12
  | 4 => packedAt s4K4 (81056+((h/643+packedAt s4K4 (73340+(h % 643)*12) 12) % 3082)*12) 12
  | 3 => packedAt s4K3 (30908+((h/195+packedAt s4K3 (28763+(h % 195)*11) 11) % 1133)*11) 11
  | 2 => packedAt s4K2 (4862+((h/26+packedAt s4K2 (4680+(h % 26)*7) 7) % 103)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc3cf1f8f8f1e38fc7e718f8fc071cfcf8dc0cf
  | 1 => 0xfc0fe7f3ffe03f1f8f81f1f1ff81f1f1927333
  | 2 => 0xfff007fc0fffc01ff1fe01fe03fe01fe638c3c
  | 3 => 0xfffff8000fffffe001fffe0003fffe007c0fc0
  | 5 => 0xfffffffff000000001fffffffc0000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x406140a011045108801082824810444504c045
  | 1 => 0x4020100020080201000101080808080001112
  | 2 => 0x888092012448025002a2012411240128230428
  | 3 => 0x1104004a489020012545240022492800580a80
  | 5 => 0xe228d46b00dd349a49f9c9c9380c2c2d7fe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_33912
namespace PEqualNP.Outside.L_meta_33912
open PEqualNP.Outside.L_meta_33912.Model
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
end PEqualNP.Outside.L_meta_33912
namespace PEqualNP.Outside.L_meta_33912
open PEqualNP.Outside.L_meta_33912.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d243179f00b1c3100d4e200000022128c00a1e057390000da80e192306e21a363a515804c845bb0601d322e0022d2c9c99866408804a68f192a39e805218341020604000280c4800c08800264c18002ffd500bfe5402ff5500bfc54037fd4c09fe53037f54c09fc5302ffd0c09fe4302ff50c09fc43037fd4807fe52037f54807fc5202ffd0807fe4202ff50807fc42027fcc807fe32007f4c807fc32037fd4405fe51037f54405fc5102ffd0405fe4102ff50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc2100ffd40037f5000ff94003fd5000df54003fc5000ffd0003fe4000ff50003fc4000ffcc003fe3000ff4c003fc3000ffc8003fe2000ff48003fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x82640fff4413207ff8209903bff654c41d7fb2a620eff99531035fcca9883bfd654c41d7eb2a620eff19531035f8ca98837ff644c41b7fb22620dff9913102dfcc898837fd644c41b7eb22620dff1913102df8c898837ff544c41bff2a2620dff5513106ff8a89880aff634c409ffa9a6204ff94d31027bca698813fd534c41deea9a6204ff14d31027fe8698813fe434c409ef21a6204ff50d3106fba8698813fc434c401ffb126200bfd8931067fcc49880efe624c401feb12620cff1893101df8c49883bff524c419ff292620eff54931067f8a498837ff424c419ff212620dff50931067f88498813ff324c409ef9926204ff8c931027fa6498803dd324c409fe1926202bfd8531017fea29880bfe514c405fea8a6202ff14531017fe829880bfe414c405fea0a6202ff10531017fe6298813f7314c405ff18a6202f78c531017f8629880bdc314c405fa18a6202ffc8531017fc429880bf6214c405fe10a620bffd813105dfec09882ffe604c4037f302620bff5813105dfac09882ffc604c4037e302620bffd413105efea09882ffe504c417fea82620bdf5413105ff8a09882fff404c417ff202620bff5013105ff88098813ff304c409ef9826204ff8c131027fa609882fdd304c409fe182620bffc813105ffc409882ffd204c417fe1026202ffc4131017ee209880bfe104c405fe882620bfd44131017f82098827ff65484137fb2a4209ff99521035fcca90827fd65484137eb2a4209ff19521035f8ca90823ff64484117fb224208ff9912102dfcc890823fd64484117eb224208ff1912102df8c890823ff5448411ff2a24208ff55121047f8a890803ff63484017fb1a420aff98d21025fcc690803fd63484017eb1a420aff18d21025f8c690827ff5348415ff29a4209ff54d21057f8a690823ff4348415ff21a4208ff50d21057f8869080aff6248407ffa924203ff9492101fdca49080ffd5248413f6a924203ff1492101ffe849080ffe4248407f72124203ff50921047da849080ffc4248407ff9924203ff8c92101fdc649080ffd3248401f69924203ff0c921015fec29080bff5148405ff28a4202ff54521017f8a29080bff4148405ff20a4202ff50521017f8829080bff3148405ff18a4202fd8c521017fa6290803f53148405fe18a4202ffc852101fee429080bfe2148405f710a4202ff08521017d8429080bf4214840fffb024207bfd812103ffcc090806fe604840ffeb024207bf5812103ff8c090806fc604840fffa824207dfd412103ffca09081ffd504840fbea824207ff1412103ffe809081ffe404840ffea024207ff1012103ffe609081ffe304840ffe9824207ff0c12101ffe409080fef2048407ff1024203ff4812103fda409080ffc2048405ff8824202fdc4121017fc209080bfd104840ffa8824202ff04121
  | 1 => 0x700032510001381c12a4c48e3753e4d8f80c0001045e2152d0f88612093150b54181e0c48401400380cf488a91a00601c000001a41c00284de29800244df2ec43000d51185a4482e12d0431c6647c0c224613e5210a00f000000000030925394723a8004000000000144000402f3acdc0749d001053292b1ac8b008ab000b1100b40009e1d13a000000000043400474381d400254b94c917000c13342c04d032b91a1f9352c00026c0d3b8d90c800420ba3a4793d400000940007f39c3c31800039390253f31000138db270e8388394641f444004dc004a000000710cc00000a506cac45844360000011348000404e400109330003ec0b2dc8f34400208d3189401f4e6000000a4001bc000009f1ec003e8001f0230002500000149240000030c002a1181b077108004b011000bf000ec000000011e00000340004cc00020d612400000a048c631b50e4f08a4ece12bc0017c001542211c78000191e88d0a8001a4570b4000604d000973d1270000000000000000d4140004a3cd02000c513cef114f6000000008c2b50b2000000000000000007600000000204a400000ff000b214c000100000000000b33dc0000036170ce000120fc060102404000005408000180402090082000020a00402050e00400170002c040e050000014018081001000480002008000c07000040a01000100809000041605028000a0004014000d0200c00060005006000000002000080408000000402050781c1c000000800000080000021100000060800802010180025ffb2a6412bfd9532097fcca9901afe654c825feb2a6412bf59532097f8ca9901afc654c823ffb226411bfd913208ffcc899016fe644c823feb226411bf5913208ff8c899016fc644c823ffaa26411ff9513208ffaa899047fc544c8077fb1a6404ffd4d32027fca699013fd534c809fe29a6404ffd0d32027fc8699013fd434c809fe21a6403bfd893201ffea49900ffe524c807fea926403ff1493201ffe849900ffe424c807fea126403ff1093201ffe6499013ef324c807ff1926403f78c93201ff8649900fdc324c807f61926403f30c932007fec299002ff614c821ff30a6402bf98532007fac299043fc614c8057e30a6412ffd4532087fca29904bfd514c821fe28a6411ffd0532087fc8299047fd414c821fe20a6404ffcc532027be6299013fe314c809fe18a6403ffc853201fde429900ffe214c807fe10a640fffd813207dfec09903ffe604c8037f302640fff5813207dfac09903ffc604c8037e302640fffd413207efea09903ffe504c81ffea82640fdf5413207ff8a09903fff404c81fff202640fff5013207ff88099013ff304c809ef9826404ff8c132027fa609903fdd304c809fe1826403ffc813201fde409900ffe204c807fe902640ffb4813201ff8409903fff104c81fff0
  | 2 => 0x258003f09250488000001650c21cb83b4be19d2f0f42720c990011b000003684c4543a000a4288000000000000001260006500000174c0190000dc0000001000d2180004c016000170003b1b86a1cc151593d240f10705828c00350bd428c82050f3c8983c026000244503416c002680035cb60002b2a8cb029343f4003f8e3000002f0a74b800000000005000000084034
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x77158931015dc764c93101edc764c931014dc764c931115df754c931115dd754c93110ddf744c93110ddd744c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c931067cc624c93101ecc624c931007d7714c931015de714c931015dc714c931087d4714c931026df614c931027d7614c931087cf214c931087d6214c931105df704c931105dd704c9310fedf604c9310fedd604c9310ff5f504c9310ff5d504c931067cf204c9310ffcd204c931087d7104c9310ffd5104c931024fe76d8d21056de63d8d21004ff75d8d21034fe75d8d21004fd75d8d21034fc75d8d21004ff74d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21084fd73d8d21056de43d8d21006dd43d8d21014ff72d8d2101cfe72d8d21014fd72d8d2101cfc72d8d210f6df32d8d210f6dd32d8d2101cff71d8d21014fe71d8d2101cfd71d8d21014fc71d8d210e6df31d8d210e6dd31d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210067f50d8d210067d50d8d21006de30d8d21056dc30d8d210f6ef20d8d21006ed20d8d210e6f710d8d21006f510d8d21024ff7658d21056dc6358d210ddef7258d210edf77158d21004ff7558d21034fe7558d21004fd7558d21034fc7558d21004ff7458d2102cfe7458d21004fd7458d2102cfc7458d210e4ff7358d21006df7358d210dcff7258d21006ef7258d21084ff7158d21006f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d210067f5058d210067d5058d21056df3058d21006dd3058d21066ef2058d21006ed2058d21086f71058d21006f51058d21015ec764c921026ec764c921014ec764c9210d5ef754c9210d5ed754c9210cdef744c9210cded744c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c921057cc634c921026cc634c921007e7714c921015ee714c921015ec714c921087e4714c92101eef614c92101fe7614c921087cf314c921087e6314c921087cd314c9210c5ef704c9210c5ed704c9210beef604c9210beed604c9210bf6f504c9210bf6d504c921057cf304c9210bfcd304c921087e7104c9210bfe5104c92101df4764c521026f4764c52101cf4764c521015f7734c521017d7734c521007d7634c521026f6634c521026f4634c521057d4634c521057d6534c5210b7d5534c521057d6434c5210afd5434c521007e7724c52101df6724c52101df4724c521067e4724c521016f7624c521017e7624c521067e6524c5210b7e5524c521067e6424c5210afe5424c521067d7324c521067e6324c521067d5324c521057e5324c521007c5324c5210a5f7704c5210a5f5704c52109ef7604c52109ef5604c52109f77504c52109f75504c521057d7304c52109fd5304c521067e7204c52109fe5204c521
  | 1 => 0xa72600ac325e272c182514a33194881b1a51a900209414432c0f922cd000891640001f818650013c0083268b400b55781c0000730000000000010a006f8014a99648008aa8000001e544c0e000ad002d89295401bcea6d721491e5351800f2100b87c78e04b801bc16000911c003c000003338b514ca200368641434384f8845d2cd18001f8dda05f10af44cbc6c319641a6784db2595c1fc82d13526cccdd62800ba00558bd02b74391138000029cb6181d8005c000891c003972878009f4f184006c6e1f4aabe090540073000017650231ecd6e2000a53431412d0c0020e80cc8a4140e8007731b081c7425b6d0ce35f931a6701eae4028a0499dceae100c0b4933d06d40d56392924d255020dc892bb20ac2700001ae00031899cac4e8b152962e1080000620006ae82432cecc311b5816a10e2c4680d000a805008540001040242801028004a350300400030081008120007400040a0001a00070100a030580000040287c1600070000400018080601050000200080001e020000006050100c0c3a0184c02050982014080206c0604014fe76d85320efcc32d8532086f661d8532004ff75d8532034fe75d8532004fd75d8532034fc75d8532004ff74d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532014fc73d8532024fd72d8532014fc72d8532086f631d8532086f621d8532004ff70d853200cfe70d8532004fd70d853200cfc70d85320067f50d85320067d50d853211edf30d8532006dd30d85320eeef20d8532006ed20d8532067cc3258532086f4615853201cfe76d8931066ee62d8931004ff75d8931034fe75d8931004fd75d8931034fc75d8931004ff74d893102cfe74d8931004fd74d893102cfc74d8931014fd73d893101cfc73d8931066ee42d8931006ed42d8931066ee32d8931126ed32d8931014fe71d8931024fd71d8931014fc71d89310deef21d8931004ff70d893100cfe70d8931004fd70d893100cfc70d89310067f50d89310067d50d8931126df30d8931006dd30d8931006ee20d8931066ec20d89310def710d8931006f510d8931066ec625893111df
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x162528c40005c00000147802d66e8c89709c03b44dceb41a68fb242387a424ac18846300100005e20164c0000ea021736714800c00aaa0045c8260d9a980a5932f020020d100c4c0060c007970000003043000162fa1375d85320045ec26ebb0a640687e85dd3614c8010fb0bba6c2990031edc150d853200e3c382a1b0a6400ec930483614c8010ff0aba6c49881a1f21574d893102c77c3a85b126200ec930883624c401ce2a0886c498803b44c110d89310077110221b126203ace86d89324c4010ff0aba6c69081a1f21574d8d2102c6fc3a87b1a4200eca304836348401ce2a0886c690803b48c110d8d210077090221b1a420087f855d1634840d0f90aba2c6908023ee017458d2100c7c402e8b1a42018f687dc563484011bf06b82c6908023be097058d210063db82a0b1a4201c787054163484031b90e982c6908063b21d2058d210076498240b1a42018f4874416348401ce2a0882c690803b44c11058d210077090220b1a4204ace86d8d32484057890e992629080f7121d324c521015e34326498a4202bc4864c93148409d890c9926290813b1dd9324c52101ee33b26498a4203dc4764c93148409d88ec992629080f311d9324c52114de3c2a6498a4229bc5854c9314845178f0899262908a2f1611324c52113de3c026498a4227bc5804c9314844db8ee0992629089b715c1324c52112f63b026498a4225ec5604c9314844be8ea09926290897d1541324c521
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x3870875411058d21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0xb09
  | 8 => 0xb0d
  | 9 => 0xb0e
  | 10 => 0xb0c
  | 11 => 0xb49
  | 12 => 0xb4b
  | 13 => 0xb4d
  | 14 => 0xb4e
  | 15 => 0xcc9
  | 16 => 0xcca
  | 17 => 0xccd
  | 18 => 0xcce
  | 19 => 0xb4b11
  | 20 => 0xb0b51
  | 21 => 0xb4b15
  | 22 => 0xb4b16
  | 23 => 0xccb11
  | 24 => 0xb0cd1
  | 25 => 0xb0cd5
  | 26 => 0xb0cd6
  | 27 => 0x170a
  | 28 => 0x15ca
  | 29 => 0x16cb
  | 30 => 0x144b
  | 31 => 0xccb51
  | 32 => 0xb4cd1
  | 33 => 0xb4cd5
  | 34 => 0xb4cd6
  | 35 => 0x154c
  | 36 => 0x140c
  | 37 => 0xccb4b19
  | 38 => 0xccb0b59
  | 39 => 0xb4b0cd9
  | 40 => 0xb4b0cdd
  | 41 => 0xb4b0cde
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
  | 5 => packedAt gbK5 (3739+((h/20+packedAt gbK5 (3599+(h % 20)*7) 7) % 74)*7) 7
  | 4 => packedAt gbK4 (71+((h/1+packedAt gbK4 (70+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x88e01c63e3f0311e3f1e3838fe3f08370530cf
  | 1 => 0xf00607c7c7fc1e3c7e1c03f0fc30049cac333
  | 2 => 0xf0007f807f80fe03f801ffc00ffc318e330c3c
  | 3 => 0x7fff8000fffc0001fffff000c1f03c0fc0
  | 4 => 0xffff80000000fffffffe00000000fe003ff000
  | 5 => 0xffffffffffff0000000000000000ffffc00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8240420a09200040910080842120813001045
  | 1 => 0x1000004042000204200401004000000404112
  | 2 => 0x90092880490452029044928009a8308c130428
  | 3 => 0x1251490008a54800892526a000c1602c0a80
  | 4 => 0xa24300000000f99324cc0182208852003fa000
  | 5 => 0x4c9c7e72724e000000100604c132adff800000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffeecfeeefee8fffffeecfeeefee8fffffeecfeeefee8fffffeecfeeefee8fffffeecfeeefee8fffffeecfeeefee8fffffeecfeeefee8fffffeecfeeefee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_33912
namespace PEqualNP.Outside.L_meta_33912
open PEqualNP.Outside.L_meta_33912.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 8 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_64 : Interval s0Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 102 := (concat (concat bs0_3_0 bs0_3_32) (concat bs0_3_64 bs0_3_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_224 : Interval s0Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_256 : Interval s0Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_320 : Interval s0Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_352 : Interval s0Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_416 : Interval s0Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_448 : Interval s0Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_512 : Interval s0Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_544 : Interval s0Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_608 : Interval s0Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_640 : Interval s0Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_704 : Interval s0Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 725 := (concat (concat (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128))) (concat (concat bs0_4_160 (concat bs0_4_192 bs0_4_224)) (concat bs0_4_256 (concat bs0_4_288 bs0_4_320)))) (concat (concat (concat bs0_4_352 (concat bs0_4_384 bs0_4_416)) (concat bs0_4_448 (concat bs0_4_480 bs0_4_512))) (concat (concat bs0_4_544 (concat bs0_4_576 bs0_4_608)) (concat bs0_4_640 (concat bs0_4_672 bs0_4_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_64 : Interval s0Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_128 : Interval s0Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_160 : Interval s0Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_224 : Interval s0Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_256 : Interval s0Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_320 : Interval s0Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_352 : Interval s0Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_416 : Interval s0Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_448 : Interval s0Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_512 : Interval s0Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_544 : Interval s0Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_608 : Interval s0Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_640 : Interval s0Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 682 := (concat (concat (concat (concat bs0_5_0 bs0_5_32) (concat bs0_5_64 (concat bs0_5_96 bs0_5_128))) (concat (concat bs0_5_160 (concat bs0_5_192 bs0_5_224)) (concat bs0_5_256 (concat bs0_5_288 bs0_5_320)))) (concat (concat (concat bs0_5_352 bs0_5_384) (concat bs0_5_416 (concat bs0_5_448 bs0_5_480))) (concat (concat bs0_5_512 (concat bs0_5_544 bs0_5_576)) (concat bs0_5_608 (concat bs0_5_640 bs0_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 40 := (concat bs0_6_0 bs0_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
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
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffefffffffafffffeeefeeefeeafffffffefffffffafffffeecfeeefee8fffffffefffffffafffffeeefeeefeeafffffffefffffffafffffeecfeeefee8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_33912.Model.Repr at out
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

def mono : List Gate := [⟨.or,[6,1]⟩,⟨.or,[6,5]⟩,⟨.or,[7,9]⟩,⟨.or,[0,3]⟩,⟨.or,[1,11]⟩,⟨.or,[2,9]⟩,⟨.and,[0,3]⟩,⟨.and,[7,13]⟩,⟨.and,[4,8]⟩,⟨.and,[10,12]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_33912

open PEqualNP.Outside.L_meta_33912 in
theorem PEqualNP.Outside.L_meta_33912 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
