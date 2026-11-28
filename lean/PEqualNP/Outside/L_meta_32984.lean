import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_32984.Model
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


end PEqualNP.Outside.L_meta_32984.Model

namespace PEqualNP.Outside.L_meta_32984
open PEqualNP.Outside.L_meta_32984.Model
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

end PEqualNP.Outside.L_meta_32984

namespace PEqualNP.Outside.L_meta_32984
open PEqualNP.Outside.L_meta_32984.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xa403156006ba5c0001a4c14012000000026d0000003c0190c000337288bb5380002f5800000066168c36a15004000b0b0244007102518a3ced8367084a806e00000009c22500c8a003e0000000007103a00024040000000000c000000400002240020218f01bd286877950d0edca521db54a43bba8a87745150ebca6215754c42bb28885755110af4a0215e540429f2a6653d54ccaeca3195d54632bda826578504cabca620d754c41b7290836d52106f4a020de540419f2a0633d540c6dca418db54831bd2806379500c6bca790d754f21bd2844379508867ea890cf15121af29e815d53d02eca3205d54640b7a92816c525027ca8184f55030b7290616d520c2eca2185d544309f2a0413d54082bca6105754c20bb288417551082dca5885b54b109f2a4213d54842bea6885714d10
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
  | 4 => packedAt s0K4 (1760+((h/20+packedAt s0K4 (1620+(h % 20)*7) 7) % 96)*7) 7
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3f83e38f1ff8ff8e38fc707071f83ffe34c33f
  | 2 => 0xc7fc03ffe0ff1c703f1f807ffe3fc1c048fdcc
  | 3 => 0x7fffc0fff001fffc01fff807fc001ff8f0e0f
  | 4 => 0xf800000fffffe07fffe000007ffffe01f00ff0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x90a844114a411004183414151048946414c115
  | 2 => 0x9108c90246102090090c81233211848c08554c
  | 3 => 0x22118124043248324009230264830918890e0a
  | 4 => 0x2053124890a0096aa2400a0849262811e00aa0
  | 5 => 0x462020098c4924d34924c4c0004302176a000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00fffcfff0fcfccc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_32984
namespace PEqualNP.Outside.L_meta_32984
open PEqualNP.Outside.L_meta_32984.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x340078026000004800a8038000000000b80141802600411a53aa00003e084000001580000000122110800064d801c0000352000000001380002c60528a8000001c00000600003c00000004910d0058020000000012000000000002000608000000c000ff43fe43fd43fc43ff42ef42fe42fd42fc42ec42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x30320000394028311c1a08073f043b43482c0010031f092955492656474a46421e53000c052e340e3d00000a58361b4c37572f4d0f2135240011384f0100001400125425592a00000000005a3a1d3e195216182b0000450000204400064115510b3c224e0d02272d334b5023171319041048502046030038b1806080000074200164438026240040b7a50d0ef2a1a1db94a43b6a94876f5250ed8a4a1db54742b7294855e5310abaa6215d94442baa88857a5010af2a0215b95042d72a085ce5310b9aa6216bd0c42d6a1885e65110adaa2217954442b2a8885ea5010bd2a0214f953329eaa6656e52906daa520eb10a41b7a92836c52506bca620d754c41b7290836d52107588420de94041bca80836e528c6daa518ded4131bc282633e540c67aa818db94831b6a90637a500c6f2a018db95321b62a6436d528867ea890cf15121d7aa2436e54486d8a890eb15121962a243e751487cc8290f950521b7290435e53d02baa7a06b10b40b7294816d52902dea4a05b14940d6212813e540c27aa8185b94830b6a906176510c2eaa218764c0309f2a4413d54882dca5885b54b10afa9a215c534427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x81621c1a802a6007b0880480b8050000000000c00001a000380980000004b0000029000000000000008090300200000002a960d0c42d194d5110b455354442c9d0d5110b254354442d85465010b495354042d85455010aa56110a41c354c421072842540418b191528c62e6495121c398c544870d6315121c9584544872a6015121ca5805448724549052199195414870d5310b40a958442d02a56110940d4545300c22c6454b10
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc0049001485c34354442c0ac6b08a890e09635805448710b0ac02a2438154d6110b40
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
  | 3 => packedAt s1K3 (998+((h/8+packedAt s1K3 (950+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 12)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfe0f1e3c7fe3fe3c63f1c0e1c7e1ffe36433f
  | 2 => 0xf1ff01fff87fc7fc07c7e00fff8fe0fe487ccf
  | 3 => 0x1fffe03ff80071ff807fff01ff000e18f8f0c
  | 4 => 0xfe000003fffff81ffff800001fffff01f00ff0
  | 5 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x842a024452244401420d052284120a34164115
  | 2 => 0x2040248081080804004220444884404808144a
  | 3 => 0x6c8660c9111c922cc80348e05d20c68c8a8f0c
  | 4 => 0x4814c9122450025a9490028112499401e00aa0
  | 5 => 0x81188100266124932724930980011811756000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffafff0fafaa0a0fffafff0fafaa0a0fffafff0fafaa0a0fffafff0fafaa0a0fffafff0fafaa0a0fffafff0fafaa0a0fffafff0fafaa0a0fffafff0fafaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_32984
namespace PEqualNP.Outside.L_meta_32984
open PEqualNP.Outside.L_meta_32984.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1c52340802c008a0000111f3a1c019005001b009d51a00301250c391a100540041e00590305d426480000a5620f12000c9890a0810410c0004100050206ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2b00525547000e211e013056001c093c1a23143b41133932080c4a2f003527000a1f02544d572e3d2500004b1b385024161d4546484f0740332a03580f0b12005100360022313f001510492917000d4c00065a0000003e0400345937182d432c002005283a114e19424453260000041010000605043c48102d828d2c082001a20404023838b056e5290edaa521cf94a429ea8c855e5310abaa6215d94442baa88857a5010af2a0216794c42cea98853e5210b5ca4216d944429ea8885b55110a6aa2216e94042dca80853e54cca7aa9996b10a32bd2846579508ca7ea8994f15132d6212653e52d067aa920dbd4941b629283af5250678a4a0eb149419629283b7515067ca820cf952319eaa4637b504c6f0a098cf950319eaa0636e520c6daa418de94031bca80633f54c8678a990cf952219eaa443ac428876a8310cfd51219e2a243b5414867ca810cf55021af298435d53087588410de94021bca80436e52902daa5204f950309eaa0616e520c2daa4185d94430baa8861d9300c2bca7905754f20d6216413e548827aa9104fd51209e2a241ac424827ca9884f55310afa9a215c534427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x280800200c1098060c39e00068050048002e196900700a028ac02a1010860430000b165354442c554d5110b315194042c654d5010b315154042a9584428cb284254232a9584424cb0e6314941c358c52507256114941ca980525072960149418b189548c6a56110a21a9189418863465505218b594420870d5310821ca1095008751514c030c354c42c82a56110b20a9584424822c6255310
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x268401485c44254232c0ac6b08a4a0e09635805250710b0ac0292838154d6110b20
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
  | 0 => 0x1fe0f1fc3fe3f8e3c71f8e07c7e1fe1e1b3673
  | 1 => 0xe1ff01ffc7fc7ffc07e3f007f8fe0ffe64399f
  | 3 => 0x1fffe3ff8007f1ff803fff8ff000fe187ce1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x842a028491442101410582514120a24c0b1231
  | 1 => 0x104044090200c0080222108208480510242086
  | 3 => 0x4c86209080c91024c800a430d20468c4814e18
  | 4 => 0x4814a9222480125694480120a4954081d00d40
  | 5 => 0x9118c1033712649b279349c4001981197eb000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffeeff88eeeecc88ffeeff88eeeecc88ffeeff88eeeecc88ffeeff88eeeecc88ffeeff88eeeecc88ffeeff88eeeecc88ffeeff88eeeecc88ffeeff88eeeecc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_32984
namespace PEqualNP.Outside.L_meta_32984
open PEqualNP.Outside.L_meta_32984.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x46657281e3528026bc0801cac10b3c68c16102489b400051c000000044003ac54541974e5029d4c909103e1060052010865a18000340008200b1412c4006ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x110003000000e6000200078000014800000c00000002c898e425000009a324299c365342000f64c0e0000e45158008c0b000009e760e84cfa00418b4da001c170a0751f800900000000420c00000124921800d400000000000000001e310900000002d000f0860a800ae6f1a800003d0f9f0c05500958000031038fe00199d0102e1c9b8685800018966b00204d8360100052413c8b0008220000ca19028004e000018c0000308ec3c030b800745f00198f43711178000038800480a0a17450643f059007725138e047100bc462a34a1c2254080687c000680084512d800d00d01000000000003000002010000070802040603000002090c05080901000004050004001301070110030207009f296873d50d0e7aa921e7d4d439e292873f5050e7ca821dd94642baa8c853d5390a7ca5216d94642daa8c853d5090abca6215754c42bb28885755110af4a0215e54042cf298853d5310b3aa6214754c429f29085ae5210b6ca2216d54442dd280853d5010b72a0214e540429f2a6653d54ccb3a87994fd52329e2a46576518caeaa3194fd51329e2a2659d434ca7ca8194f55032bb2886575510caf4a0195e54032b7294836d529067ca998cf553319f2a0633d540c6dca418db54831bd2806379500c7588590cf952219eaa443b6548876aa910edd0e21daa1c4375528876c8510ed10a219faa2433c54487588490edd5121da2a243b7434876a8690f9d4921f3a1243b642487688490f910921d221243e632487ca6490dd944219ea9e813e52d036c43a06d487409eaa4813f5350278a4a06d88540da90a81bb505027ca8204f953309eaa6613e548c27aa9184f951309eaa26177514c2e8a2984f950309eaa0616e520c2daa4185d94430baa8861d9300c27ea9904f15320bb28e417551c83ca43904f952209eaa441b9408827ea8904f15120f290a41b9404827ca8104f55020af298415d53082eca2105d544209f2a4213d548427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x400e920a1d1864a40599000c600340179338a4c0d58c072700ac4000084b0f1201680144551e3e800006290a81086ca2800897174c00d41008065018008000a0128e5805250ea56194842c554e5110b155354442c654e5010b1a5354042c654d5010b325154042cc5455010a39601523287195434ca8d6310b21aa58042c86956310a21ac580428868d6310921aa58042486a46250d21a999352486366590921a998a42486366510921a558c42486b16010921b158c42486e16010921a999442487266510921e198c42486a56310921e158c42486856310921e898042486a56010921e858042486a16010921a919232486a4644c921e150d324861d6314940c9149215022c625513099588514c349524c030d4545300c21d6315320c915121c832454485208e19540483a12150120
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xa80106039801100005285c06250d21d02c73008490e82635804248740b1ac021243285c0648c921908eca1a6490d05731492150282b98a890e41881952150120
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
  | 4 => packedAt s3K4 (4032+((h/45+packedAt s3K4 (3672+(h % 45)*8) 8) % 198)*9) 9
  | 3 => packedAt s3K3 (1996+((h/16+packedAt s3K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s3K2 (453+((h/3+packedAt s3K2 (441+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf1f8f1fc78f8fff18e3f1c1e38e1fff19307f
  | 1 => 0xfe7f01ff80ff1c7e0fc7e01fc0fe38f663993
  | 2 => 0xf007ffe3fff001f8ff007ffe3ff003f087ce1c
  | 4 => 0xfff80003fffffe00ffff80003ffffc00f80fe0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4180a020421210800820a048408208c4091025
  | 1 => 0xa25106489125030860445214a424c12a262892
  | 2 => 0x20420209010124012100148429204222024a18
  | 4 => 0x4004892240800129289002012491000d00540
  | 5 => 0xc8946c10364e49a4dcf269390041984cfdb000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefef8f8fefea8a8fefef8f8fefea8a8fefef8f8fefea8a8fefef8f8fefea8a8fefef8f8fefea8a8fefef8f8fefea8a8fefef8f8fefea8a8fefef8f8fefea8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_32984
namespace PEqualNP.Outside.L_meta_32984
open PEqualNP.Outside.L_meta_32984.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x80d820e506381a380196a7119e069421f30013002e00eb066c40055c54b0000ec00b100433254a45112000780340000000dc022000002f6801c804e4dd005a90480000000056000126c010a858020c90204001040a002810a140810018404b7290876d5210eeca221dd54443bd28087795010ebca6215754c42bb28885755110af4a0215e54042bd286657950ccaeca3195d546329faa2653c544caf4a1a0de54341b7294836d52906bea6a0d714d419f2a0633d540c6dca418db54831bd2806379500c6bca790d754f219f2a4433d54886f6a090de14121bb28e817551d02bca7205754e40b7a92816c52502dca5985b54b309f2a4613d548c2eea2985d145309f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 60
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (731+((h/13+packedAt s4K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s4K4 (1760+((h/20+packedAt s4K4 (1620+(h % 20)*7) 7) % 88)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe3c7c7f1fe3ff8e38e0e383f1f83ffe61339f
  | 1 => 0xf03f807fe3ffe3f03f00fc03fe3ff83e863cf3
  | 2 => 0x3fff8ffc03fc7fc000fffc7fc03fc107cf1c
  | 3 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x404610c15105400a182a40a0a0490d18611185
  | 1 => 0x288849228a4204502110a449121490a4862432
  | 2 => 0xa511282408c880b4400429185482a285024e18
  | 3 => 0xc40132484080c9268a46001069230309280bc0
  | 5 => 0x8224000931312493498d26200040430d5b000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfff8fff8eca8eca8fff8fff8eca8eca8fff8fff8eca8eca8fff8fff8eca8eca8fff8fff8eca8eca8fff8fff8eca8eca8fff8fff8eca8eca8fff8fff8eca8eca8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_32984
namespace PEqualNP.Outside.L_meta_32984
open PEqualNP.Outside.L_meta_32984.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x272c700002e28c003e014863c6912b540532d1265002227520e2abc79b424118000a0688241c98b280002e580000506942001840324a3920c3002000040100ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x63431a47c0f0d19c8e123d0b4007e14144f2170e09412753b828dc1b2b9d8220008020d8813e128bc00000740a0d181cc9a1f1092c665f20900a866388f0e85b36984000e001c07a5840098ac141c800a05d001e09c4c038c47e320b000b400241ec006a0004c002f21a1d04000100000000020d083a018000000020180000000d0186b05800000023110a4220012446551b0e00037299c8fa2a2c9fc8a2c158b83218328ecc81e100d4d027300909e6f3105402852e108521d0900030016140001053d060003000602010800200207030529020c1002380422020000020a17000000010032aeaa4875e5190ebaa121e7d5143ae28a875f5050ebca621d794f42aea9e855e5310abaa6215d94442baa88857a5010af2a0215d94632baa8c655e53d06baa7a0e750f41b7294836d52906bea6a0d714d41cea1a835e53106baa620db94841b6a90837a50106f2a020db94a31b6a94635f548c6baa918f394a31e6a94635e518c6baa118cf950319eaa0636e520c6daa418de94031bca80635f540c73ca818d755031ceaa0631d540c79ca418f354831af28863d6510c7b4a018d754031eca806359500c6bca790d754f21e729e43cd53c879c8790f350f21e718e43cc31c86daa510f50c621afa9a435c53487a86290f3d4d21e629a43ce434879a8690f9d4521f320a43e541487ce6290f38c521e618a43e431487886290db94821af29e815d53d02bca7205754e40b7a92816c52502bca6205754c40b7290816d52102eca2205d54440dca00815f54cc2baa9985794730e790e61cd21cc2baa71857d5130aeaa2615c514c39e42987348530eda82615e530c2bca7105754e209f2a0413d54082bca6105754c20bb288417551082bea7885714f10b7296216d52c43ca43885794e10aea9c21d930842bea6885714d10f290a21d9304427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x121b003451d5ea57002c4c28b1e558a7020d19724656841c25800040000000000114a8800038a86084c8031a008400000415803e780075801414301a343000c18b020a001820800e00965805150e5960d503187596540c70d5494831c3551520c6c56294431c6552500c71a5454031c6551500c74a5254031d2549500c68d640c721b258031c8695640c621b45803188695640c521b458031486c46150d21b198f51486c46350521e150d414864e658c521b1986314864e650c521a359031486c9600c521a959031486e1600c521b19943148746650c521b1d903148786640c521b15903148785640c521a159031487c2600c521b158031487c1600c521b058031486656114940ca5494010331515004095185544c21d6414530d1145214c21d6414f10d114d21c434453485109619530443c1214c110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc0010a03840810ce01305c06150d21982e1b206290c85769903148740b24c018a43a0991600c521d02c8b006290d0574145214c282ba0a690e2190195214c110
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
  | 3 => packedAt s5K3 (2012+((h/16+packedAt s5K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e1f8f8f1fc7f1ff1c63c70e3f1f83ff18339f
  | 1 => 0x1fe7f00fe3f8ffc7e07c780fc7e3ff8724ccf3
  | 2 => 0xe007fff003ff01f8ff807ff007fc03f8c70f1c
  | 3 => 0xfff8000003fffe00ffff800007fffc00f80fe0
  | 4 => 0xfffffffffc000000fffffffff8000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x828082142050028004208102120490a4081185
  | 1 => 0x44410122048220082004482481210912044432
  | 2 => 0x41522502490265016880526085482a52450e18
  | 3 => 0x89906e4c9234c192dd6900c136927064f80bc0
  | 4 => 0x10044808002488249252248920004000b2a000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8fefeeca8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_32984
namespace PEqualNP.Outside.L_meta_32984
open PEqualNP.Outside.L_meta_32984.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826004fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007ff204c003ff1026001ff0813000ffe2098007fe104c003fd0826001ff04130007feca90002ff654801dff32a4006bf99520007faca90002fd654801dfe32a4006bf19520007fec890002ff644801bff3224005bf99120007fac890002fd644801bfe3224005bf19120077fea890037fe5448001feaa2400dff15120007fec690002ff6348019ff31a4004bf98d20007fac690002fd6348019fe31a4004bf18d20077fea690033fe5348001fea9a400cff14d2006ffe8690033fe4348001fea1a400cff10d2000dfec49000fff5248007ff2924003ff5492001ff8a49000fff4248007ff2124003fb9092001ffa8490003ed4248007fe2124003ffcc92001ffc649000ffd3248007fe1924000ffd8520005fec29002ffe61480057f30a4000ff5852005ff8c29000afc614801dffa8a400bff94520007faa29002ffc514801bffa0a400bff90520007fa829002ffc4148019ff98a400bff8c520007fa629002ffc3148007ff90a4003fbc852001ffc429000ffd2148001f690a4003ff0852000dfec090007ff5048003ff2824001fe9412000ffaa090003f95048003fe2824001ffd012000ffc8090007fa4048003fea024000fe5012000ff88090007ff3048003ff1824001ff4c12000ff86090007ff2048007fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffe2090007fe1048003fe0824000ffd9510005feca8802bfe654400d7f32a2000ff59510005faca8802bfc654400d7e32a2000ffd9110005fec888027fe644400b7f3222000ff59110005fac888027fc644400b7e322200affd511004ffca888003fd5444013fe2a22000ffd8d10005fec688023fe63440097f31a2000ff58d10005fac688023fc63440097e31a200affd4d10047fca688003fd5344011fe29a2009ffd0d10047fc8688003fd4344011fe21a2000ffd8910005fec48801ffe62440077f3122000ff58910005fac48801ffc62440077e312200affd491003ffca488003fd524400ffe2922009ffd091003ffc8488003fd424400ffe2122008ffcc91003ffc6488003fd324400ffe1922001bfd8510017fea28800bfe5144005fea8a2002ff14510017fe828800bfe4144005fb20a2002ff50510007ea828800bfc4144005ff98a2002ff8c510017fa628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001fe9011000ffa8088003f94044003fe2022001ffcc11000ffc6088007fa3044003fe9822000fe4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xffe4154001fea0aa017ff105500cffe62a805ffe3154001fe98aa017ff0c5500c7fe42a805ffe2154001fe90aa017ff0855000dfec0a8007ff505400dfda82a001ff9415000efca0a8007fc5054003be282a001fe1415000ffe80a8007fe4054003fe202a001ffcc15000ffc60a8007fa3054003fe182a001ffc815000ffc40a8007fa2054003fe102a001ffc415000ffc20a8007fc1054001ffb2a8000bfd95400b7fccaa001afe6550001feb2a8000bf595400b7f8caa001afc65500037fb228005ffd514002ffca8a0017fd545000bfe2a28000ffd8d40005fec6a0057fe63500097f31a8000ff58d400aff8c6a0012fc635002dffa9a8015ff94d40007faa6a0057fc535000bffa1a8005ff90d4002ffa86a0017fc4350001ffb128000bfd89400a7fcc4a000efe6250001feb128014ff1894001df8c4a005bff5250029ff2928000ff549400a7f8a4a0017ff425000bdfa128005ff9094002ffa84a0003bd425000bfe2128015ffcc9400a7fc64a0003fd3250029fe1928000ffd8540005fec2a004ffe61500057f30a8000ff5854009ff8c2a000afc615002dffa8a8013ff94540007faa2a004ffc515000bffa0a8005efd054002ffc82a0017fd4150001dea0a8005ff105400affe62a004ffe3150001fe98a8013ff0c5400a7fe42a004ffe2150001fe90a8013ff0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a0007ff405000bfda028001ff9014000f7c80a0007fc4050003de2028001fe1014000f7080a0007ff3050003ff1828001ff0c14000ffe40a0007fe2050003fd1028001ff0814000ffe20a0007fe1050003fd0828001ff04140007feca98002ff654c025ff32a6006bf99530007faca98002fd654c025fe32a6006bf19530007fec898002ff644c023ff3226005bf99130007fac898002fd644c023fe3226005bf19130097fea898047fe544c001feaa26011ff1513000dfec698013ff534c025efa9a6004ff94d30027faa698013fc534c009ee29a6004ffd0d30027fc8698013de434c009fea1a6000f750d30027f88698003ff624c0017fb126010ff9893001dfcc498003fd624c021fe3126003bf18930097fea498043fe524c001fea926010ff1493008ffe8498043fe424c001fea126010ff10930027fe6498013df324c009ff1926004ff4c930007ba6498013fc324c001ffb0a6000bfd853007ffcc29800afe614c001feb0a600fff18530015f8c29804bff514c01fff28a6000ff5453007ff8a298047ff414c01fff20a6000ff5053007ff88298013ff314c009ef98a6004ff8c530027fa6298003dd314c009fe18a6010ffc853007ffc4298003fd214c01ffe10a6001bfd813000ffea098007fe504c003fd2826001ff54130007f2a098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9
  | 2 => 0x31007fa8498883fc424c409ff9926204ff8c931027fa6498813fc324c4057fb0a6202ffd4531017fca29880bf6514c405fea8a6200fd54531017f8a29880bff414c405ff20a6202ff50531017f8829880bff314c409fb98a6202ff8c531017bc629880bfc314c405ee18a6202fd0c531017fe429880bfe214c405fe10a6200ffd8131005fec09887ffe604c4037f3026200ff581310fff8c098806fc604c445ffa82621fff941310fff8a098887ff404c43fff202621fff10131027fe6098813df304c409ff1826204ff0c131107fe409887ffe204c43ffe1026202ffc4131017fc209880bfc104c401ffb2a4200bfd95210f7fcca9081afe6548401feb2a4200bf595210f7f8ca9081afc6548401ffb224200bfd91210effcc890816fe6448401feb224200bf591210eff8c890816fc644843dffaa2421dff95121007faa890877fc5448401ffb1a4200bfd8d210e7fcc690812fe6348401feb1a4200bf58d210e7f8c690812fc634843dffa9a421cff94d21007faa690873fc534843bffa1a421cff90d21007fa8690873fc43484057fb124203ffd49210f7dea49080ffe5248407fea924203ff1492101fd8a49080fff4248407ff2124203fb9092101ffa8490803ed4248407fe2124203ffcc92101ffc649080fee3248407fe9924200fb4c92101ff8649080aff6148405ffa8a4202ff94521017eca29080bfd5148401faa8a4202ff14521017fe829080bfe4148405fb20a4202ff50521007ea829080bfc4148405ff98a421cfdcc521017fc629080bfd3148405fe18a4202fd0c521017fe429080ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843dffa82421bff941210dff8a090877ff4048437ff202421bff101210e7fe609086ffe3048437fe1824203ffc812101fde409080ffe2048407fe1024202ffc4121017ee209080bfe1048405fe0824201bfd9550007fec8a8002ff6454035ff322a005bf99150007fac8a806bfc645400b7e322a006ffd5150036fea8a801bfe545400dfeaa2a000df55150037f8a8a8003ff63540017fb1aa019ff98d50025fcc6a8003fd6354033fe31aa004bf18d50037fea6a801bfe5354033bf29aa006ff54d50037f8a6a801b7c5354035ffa1aa019ff90d50007fa86a8067fc4354001ffb12a000bfd89500c7fcc4a800efe6254001feb12a018ff1895001df8c4a801bff525400dbfa92a006ff94950037faa4a80037d525400dfe292a01affd09500c7fc84a8003fd4254031fe212a019ffcc9500c7fc64a8003fd3254031fe192a000ffd8550005fec2a805ffe61540057f30aa000ff585500bff8c2a800afc615400dffa8aa006dfd4550037fca2a801bfd5154001bea8aa006ff145500d7fe82a805
  | 3 => 0xeaa2a206ff15151007fec6a8802ff6354401efb1aa200b7d8d5114ffcc6a8812fe6354401feb1aa229ff18d51025f8c6a8803dc63544096e31aa206ffd4d51036fea6a881bfe535440dfea9aa200df54d51037f8a6a88abff4354453ff21aa200ff50d5114ff886a8803ff62544017fb12a228ff9895101dfcc4a8803fd6254451fe312a203bf18951037fea4a881bfe5254451bf292a206ff54951037f8a4a881b7c5254455ffa12a228ff90951007fa84a88a3fc4254453ff992a228ff8c951007fa64a88a3fc32544057fb0aa202ffd4551037eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405ffa0aa202ff90551017f882a880bff3154405ff18aa202fd8c551017f862a880bff2154405ff10aa202fd88551017f842a8803ff60544017fb02a227ff9815100dfcc0a8803fd605444ffe302a201bf18151037fea0a881b7f505440dff282a206ff14151157fe80a889ffe405444ffe202a229ffcc15113ffc60a889ffc3054451ff902a227ff8815113ff840a880bff1054405ff082a202ff04151007fecaa0802ff655044dff32a8206bf99541007facaa0802fd655044dfe32a8206bf19541015fec8a0817ff545040bff2a28205ff5514102ff8a8a0803ff63504017fb1a8225ff98d41025fcc6a0803fd635044bfe31a8204bf18d41137fea6a0897fe5350401fea9a8225ff14d4102ffe86a0817bf435040bff21a8205ff50d410077a86a0817fc4350401ffb128200bfd8941127fcc4a080efe6250401feb128224ff1894101df8c4a089bff5250449ff2928200ff54941127f8a4a0817ff425040bff2128205ff5094102ff884a0897ff3250449ff1928200ff4c941127f864a080aff6150405ffa8a8202ff94541017faa2a080bfc5150405ffa0a8205fdd0541017fc82a080bbe4150405fe20a8202ef10541017e882a080bff3150405ff18a8202ff0c541017fe42a080bfe2150405fb10a8202ff08541007fec0a0802ff6050447ff3028201bf98141007fac0a088ffc60504037e3028226ffd414111ffca0a088ffc505040bffa028205efd014102ffc80a0817fc405044bff9828223ff8c14111ff860a0893ff2050447ff1028223ff08141017fe20a080bf71050405ff0828202ff04141007feca98802ff654c445ff32a6206bf99531007faca98802fd654c445fe32a6206bf19531007fec898802ff644c443ff3226205bf99131007fac898802fd644c443fe3226205bf19131117fea898887fe544c401feaa26221ff15131015fec698813ff534c409ff29a6204ff54d31027f8a698813ff434c409ff21a6204f790d31027fa8698803dd434c409fe21a6200ffd8931005fec498883fe624c4077f3126200ff58931107f8c49880efc624c445ffa926220ff94931007faa498883fc524c443ffa126220ff909
  | 4 => 0x6fe6054801feb02a433ff1815200df8c0a901bff505480dbfa82a406ff94152037f8a0a90dbff4054867ff202a433ff101521affe60a90cffe3054867fe182a403ffc815201ffc40a900ffc2054869ff882a433ff8415219ff820a9003ff65508017fb2a8432ff99542035fccaa1003fd65508017eb2a8432ff19542035f8caa100eff645080bffaa28405ff9514202f7ca8a1017fd5450801deaa28405ff15142007fec6a1002ff6350863ff31a8404bf98d42007fac6a10c7fc63508097e31a8432ffd4d4218ffca6a1003fd5350863fe29a8405ffd0d4202ffc86a1017fd435080bfe21a8403bfd894201ffea4a100ffe5250807fea928403ff1494201ffe84a1017ef4250807ff2128403ef9094201ff884a100fbc4250807f62128403ffcc94201ffc64a100ffc3250801ffb0a8400bfd8542187fcc2a100afe6150801feb0a8430ff18542015f8c2a10cbff5150861ff28a8430ff1454202ffe82a1017fe415080bfe20a8431ffcc542187fc62a10c3fc3150807ff90a8403fbc854201ffc42a100ffc2150801ffb028400bfd814217ffcc0a1006fe6050801feb02842fff1814200df8c0a10cbff505085fff282842fff1414202ffe80a1017bf405080bff2028405ff1014218ffe60a10bffe305085ffe1828403ffc814201fde40a100ffe2050807fe1028430ffc414217ffc20a10bffc1050801ffb2a6400bfd9532006feca990027f654c85dff32a6406bf99532007faca99002fd654c85dfe32a6406bf19532006f8ca9901a7c654c801ffb226400bfd913216ffcc899016fe644c801feb226400bf5913216ff8c899016fc644c85dffaa2642dff95132007faa8990b7fc544c8077fb1a6404ffd4d32027fca699013de534c809fea9a6400f754d32027f8a699013ff434c809ff21a6404f790d32027fa8699003dd434c809fe21a6403bfd893201ffea49900ffe524c807f72926403ff54932007daa49900ffc524c807ffa126403ff9093201ffa849900ffc424c807ff9926404fbcc93201ffc649900fde324c807fe1926403f70c93201fd86499003ff614c8017fb0a642cff98532015fcc299003fd614c859fe30a6402bf18532177fea2990b3fe514c859fe28a642dffd0532167fc82990b3fc414c809ff98a6404ff8c532167bc6299013fc314c809ee18a6403ffc853201fde429900ffe214c807fe10a6400ffd8132005fec0990affe604c8037f3026400ff5813215ff8c099006fc604c85dffa82642bff9413215ff8a0990b7ff404c857ff202642bff10132027fe6099013df304c809ff1826404ff0c13201ffe409900ffe204c807fe102642cffc413215ffc20990affc104c8057fb2aa200ffd9151005fec8a88abfe645440b7f322a200ff59151157f8c8a8816fc645440dffaa2a206dfd5151037fca8a881bfd5454401b
  | 5 => 0x4d53027f8a6a98137c5354c09ee29aa604ffd0d53027fc86a9813fc4354c01ffb12a600bfd89531effcc4a980efe6254c01feb12a63dff1895301df8c4a981bff5254c0dff292a606ff149531f7fe84a98f7fe4254c7bfe212a604ffcc953027be64a9813fe3254c09fe192a600ffd8553005fec2a98f3fe6154c057f30aa600ff585531e7f8c2a980afc6154c0dffa8aa606dfd4553037fca2a981bfc5154c7dffa0aa63cff905531e7f882a9813ff3154c09ff18aa604ff0c5531effe42a98f3fe2154c79fe10aa600ffd8153005fec0a98effe6054c037f302a600ff581531dff8c0a9806fc6054c0dffa82a606ff94153037f8a0a98fbff4054c77ff202a63bff10153027fe60a9813fe3054c09fe182a63dffc81531dffc40a98effc2054c79ff882a63bff841531dff820a9803ff6550c017fb2a863aff99543035fccaa1803fd6550c017eb2a863aff19543035f8caa1812ff6450c0bffaa28605ff9514302f7ca8a1817fd5450c01deaa28605ff15143025fec6a1813ff5350c75efa9a8604ff94d43027faa6a1813fc5350c09ee29a8604ffd0d4302fbe86a1813fe4350c09df21a8604ff10d430277886a1813dc4350c01ffb128600bfd89431cffcc4a180efe6250c01feb128639ff1894301df8c4a18ebff5250c73ff2928639ff1494302ffe84a1817fe4250c0bfe2128604ffcc943027be64a1813fe3250c09fe1928600ffd8543005fec2a18e3fe6150c057f30a8600ff585431c7f8c2a180afc6150c75ffa8a8638ff945431c7f8a2a1817ff4150c0bdfa0a8605ff9054302ff882a1813ff3150c09ef98a8604ff8c543027f862a18e7ff2150c71ff10a8638ff08543007fec0a1802ff6050c6fff3028601bf98143007fac0a18dffc6050c037e302863affd41431bffca0a18dffc5050c0bffa028605ff9014302ff880a1813ff3050c09ef9828604ff8c143027f860a18e7ff2050c6fff1028637ff081431c7fe20a18dffe1050c6ffe0828603bfd9552007fec8a9002ff645486dff322a405bf99152007fac8a90dbfc645480b7e322a406ffd5152036fea8a901bfe545480dfeaa2a400df55152037f8a8a9003ff63548017fb1aa435ff98d52025fcc6a9003fd635486bfe31aa404bf18d52037fea6a901bfe535480dfea9aa406ff14d521b7fe86a90d7fe4354801fea1aa435ff10d5201dfec4a900fff525480df7a92a403ff9495201efca4a900ffc5254807be292a403fb1495201ffe84a900ffe4254807fe212a403ffcc95201ffc64a900fee3254807fe192a400ffd8552005fec2a90d3fe61548057f30aa400ff585521a7f8c2a900afc615480dffa8aa406ff94552037f8a2a90dbff4154869ff20aa434ff105521affe62a90d3fe3154869fe18aa403ffc855201ffc42a900ffc2154801ffb02a400bfd815219ffcc0a9
  | 6 => 0x1100a060000030160002c0000160540604d0020180000105009c0b00a0000080000001200c0e801008000078140000180e00003a0000980500000810002010068000000060301981600a0080280c00a024000120000d00001900601c0a0010020bc0000001a00c000000000e40080200000800005002014038170000100d00c010000040040140940101b004000018000000100a0060040480280f0200040000e00c010000070000280200500c0240000100e01c0300b00200000803046008018000020281e0010000000d00000000c0d8030000bc0182b02c018038000020a4008080000080a8420040240880a00e03000001000004028010060000004e00000001003004014000010020540000302a0100f0020080080080000000001801010000078000080140781d06e0000282400801c1c0000060540181800400009800012004018070080140200001405c0203e0020002f0250040180000a000034018010000000000200000008027050000000000280140c8010120080400104600c0380300000c000050400280680000a0000000402607c008040000100481102418c0200400000021004006054030080000041a803016058008020700040080700000c0780300a00000001008040038020080000280000804c0000b024020078000240e400015000024000160000100500100c04c0780d0120080580200000402800044020040020480000780100400808000000014080070000240400200a0400300401404c05816ff655500b7fb22a805ffd51540377ea8aa017fe545500bbf2a2a805ff1515402ef8a8aa017bc5455001ffb1aa800bfd8d54217fcc6aa012fe6355001feb1aa842ff18d54025f8c6aa01bff535500dff29aa842df94d54037f8a6aa01b7c535500bffa1aa805efd0d5402ffc86aa017fc4355001ffb12a800bfd895420ffcc4aa00efe6255001feb12a841ff1895401df8c4aa01bff525500dbfa92a806ff94954037f8a4aa017ff425500bdfa12a805ff9095402ff884aa10bff3255083ff192a841ff0c954007fec2aa002ff6155081ff30aa802bf98554007fac2aa103fc61550057e30aa806ffd4554036fea2aa01bfe515500dfe28aa805ffd055402ffc82aa017fc4155085ff98aa840ff8c554207f862aa107ff2155081ff10aa840ff08554007fec0aa002ff605507fff302a801bf98154007fac0aa0fffc60550037e302a806ffd4154036fea0aa01bfe505500dfe282a805ffd015402ffc80aa017fc4055085ff982a83fff8c1541fff860aa107ff205507fff102a83fff08154207fe20aa0fffe105507ffe082a804bfd9553007fec8a9802ff6454c7dff322a605bf99153007fac8a98fbfc6454c0b7e322a606ffd5153037fca8a981bfd5454c0dfe2a2a604bfd8d53027fea6a981bdf5354c09ff29aa604df9
  | 7 => 0x4f8358dd9102930080000000000001e20f2a782821a39dc00000000001408180e8001bf2c722328880004c0000000389ab2aeabe9678000e90002c60cd8551c52bc88e1800380000000e093429e8fb82b202a639a31bb8001a10ee0002870400001d41bd11daa599026f0000000000001ad91c01280019b80014e8000e29dbac08002761b81869351a72838ae00018391119d80aa750b995f02d9b61d88b82a923811b2648000000000000000001ba0000d983a8de0000002b18000001188002bd1f107a94fa2e19e0b79c99e5a8aa5c2720000001530001d524a88b80000028486a18829c0940f4991239800136aaaa7d8b49de16c173a560000002629990471810db0000240a21128001428a896427a257a5280000022a05a00003d2700000d51518c20fa00019227a9abaaf80028e29585d26c8d08000522b2a0e0d00000000ba08fa0c80027e0000000002a20150002bf29721b16d0002768720f00f124ba548000e612827b89a0510000000d600000000022aa9b00002791e18480000386f04f11c8000000001b20001720002090d2143800000022928800000193a6500024c8001670dc96e8e184280018f0000dea3900011b800237000000000149a810001be1c91c7213a940310ec89895fa5383ca852a01178000000f88858001261740000f680000000000020e8001240000872a50250911418000978dbabc00025e83627ca160cba348688aa926a4e0ac85a97b00000015096a80c2b900005380000f8a50842418089e405da7411e9858d31b39bfa5f9aa9c89e3a169bda3f0bc07719f8002880000528f09ea9541520001ae00007cac4a960930298518002c317c9cd0681b89d99b6a4297e90e1fc1a58001fba4214d021a2793717627f8c118a97f8e014c01f0a711916201c259aba1158a383f07e09e9a287487684e8002310001cd8260000000019ec97989200013c0432b12a0ac3a860b586994ba352c90cb0590af8000990a780014916e0001701f988e90c01d98980010a98e90f2282188001e18ed8000002681568000bba792b78542950000dd0662ac088a43017188a3182baad8a90000000000000e38000011050bf9502c80ce8000878ef1d20001fb15b01a9a980016386ba9206a8ec2128d79ac14d9a80ff9c18001d38110f60f222500e0000d68ca8808729da2b40d4ab502a895aa180000021597d0002099231649e69a78f9906a618001cb06e1510aea0008c1ea02f0000001a51cea9fa53119a4e9d283403214700023e09d0000b0abb2a2a7c25a80100b00404c018080280900200b0001301700401c03001003004000078000060180081305a00002002000024090000000380180102a0900580200a03c008050020080a00f004000000030000e40800f0040040000d01e0000080000a0000980000400004802000000020
  | 8 => 0x29e91d683e908a299e08002c299a018abe0000000000000391108b10501de9421a426ea148c8959a288a496093d0ada44839a8595e85b89e04080f02585706293590490915c93983a0eea478000001b524980022d9d82a8a8a01d1ed8bf0dc1e4800154a12208a5b2c998600020826580014a83b21512b0001360e31e500026fa6999d24b1a225c847a248778e504d8999b990713a0c4a340000000000708001c600027f1079980642aa28b12285e8001879f00c18658bc9378000c980000000000000023d80020300013e02a1440000220a60000ed12b98b80019619e80404683696880020d1dca8d8000001588008002572c41f488f0a300025b9bc800189210800000000000163000073a8f11319283d8002a61e60000001611870eb9431932902551e81968000001df1c11a68f59301d31b0a918c610088287c12116a18422e8118e78e8a0aa670b919725803080000004b21329480b1389fc85c25128c8c29941ed23c0eaa21061114978857a7284e2b4aa82c19759308c915d2b59b70e71efa4d075a6b09ca4d9239550028909e725d23229f00d1f812e0ba9cc2b69db2620e484c8649d929888c96f1bb1832519cf19f2459cc824abb80023e8000001f28480d8a718b00c792ea4f0000000f709c0000b70f300000007b21010410b182019ac0000000016a0daac8c58cc8a819a8370b68001c20000e98002141321af12f01e8561950000aa00006917304b8002712240c68a189b94493287d29a0972078981749df9528001c091d275810207096a5916280712f9fdab005ca0f1349d61c32401b11beac2274a4a12496193b28917197680009d861a0c00020487602305882925000007ba3791f88a21a24400027d2a11c4a3a03f9f32cb11f1ef0302b223fa06aa997f21823a998a0120b9460fe9e112c0bb03b89f015a801fd07d9cba4395604d0021751b591612a1ff0cc017a1d8b42408da96fa660f515da0610d1a192c9a00780c405300011a80007f8bda54191a05a6c0711f221e1380d3a2b00023024523690eaad1afab090b893a1f98e0599b288b24102e88d88392927e9f42978e40a09709d4a8d06b0160318210891bc18b00d8c383381fa2c86c88814ca4696916517919c2ab9d59ad2480108549098378730bd25a2ae20f9f50d70f1a4c29c8559000cf09513ba3b9829d105f06d157125165aa686e8b3aca24716690800910a2b8a6a0e5901267aa387a04a080169aa317e0df0349200122209259d7994ac50ac14e0269f705083318ca55a83092abfac100b94f02d2b714799b02c2488918052a71592a7a9911184511823b0420fb0d91cf8d122180005e26d9331030c3005a178792a49a89f18b21dd8fc01a217273a5d82380c8b50ef98a00694b1b793118d28b9baa981711319411f90fd0001dd13e8002868701b40000001582
  | 9 => 0x22706d80300026411500006306026312d1ff8d59271d01ce0000002771ec1209b30000d28458000200002358000000000000000002c596601e21100483e0fa9279aa12da58a8f8000000000e814000010ca3880006680000016818d8000060000a9a60a9980021c2a40af02f800027028813a039391a4a9da1b8f81ee921a6b9c78410001f5879a2b8001e88a29770f3ab39c026e0001f38000001c38582909728000001ca2050182818079c4199901a30a3ca5f2899139da8ca15b8ab09b0ea2879e284f8821b4a829c829b8a5860955896049a8ea778ff13a8b89169808c81caa928df8cd29e22f1ebac6a842600f91c589f8438c00000a020096b80029a95a08984406397822020423294a2af0000b60be80014680a00006f8000001170a68e6ac88002118001958d80000000000949fe0000da1b926a9fe8a11e78000001ee056a968000f781310d93f11406c0ad1600002789b188d1578830671d080002e20187f0d416c8209e993c832a9d2bd84885b0f421aa2c0851fa15381915e1818c722f9978ce0001d70002690e20862ca9c6a50a911f609aa331f683515c27990f8ab84182cac7a6884aa7092a8be140a0a1059a617ba5e07e9e02ab1020b31450eb0cf9fa8848149a900027317a8098000000a42259aca2d11a0fe062133871a4627b122102a1f17d9f788107426d1481e32b82b9878a521eb19c8752b317a15aa1996d84910613da9398c2220e124921e84488aaba9f0a668b1890222a2908697798f86523620b261103a3d28c2192260d19b018500001c81b8000fd8001120001908000c0a2683c2808fc800202067ab614593f9f89d18c5000233a1d1a08282239488000460000000b29ae85fa1c96b12981b25697c1c
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910236fa40d8910236ef20d8910236ed20d891001cff7658910005bf745891004dbc745891003eec625891022df7715891023dfb7058910004ff7558910034fe7558910034fc7558910004ff7458910006bf7458910004bf745891002cfe745891002cfc7458910006bc745891002cbc7458910004ff7358910024fe7358910024fc7358910234ff7258910006ef725891003eee425891022cff7158910006f7715891005ef641589100dcff7058910006fb70589100defa4058910004ff7654910004fe7654910004fd7654910004fc7654910004ff7650910004fe7650910004fd7650910004fc765091001eee6250910006ed6250910015f67150910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100557c754c910006df634c910026dc634c91000df4765051002ef4765051000cf47650510015f77450510017b77450510007b7645051002ef6645051002ef4645051004fb4645051004fb74350510007b54350510005f77250510006f76250510006f56250510007f3705051000df6705051000df4705051011ff07050510016f76050510017f3605051011fb7405051011ff2405051011fb5405051011ff2305051000df4764851001ef4764851000cf47648510006f76548510006f56548510005f77448510005f57448510006f76448510006f564485100e6f663485100e6f46348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe46248510227e7524851003fe4524851003fe64248510007e5424851003fe63248510007e53248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100dff240485100dff230485100dfe720485100dfe52048510015f8765011002ef87650110014f8765011000dfb745011000fbb7450110007bb645011002efa645011002ef8645011004fb8645011002eb86450110005fb7350110006fb6250110006f9625011004fbb4250110007b94250110007f37150110015fa7150110015f8715011009ff0715011000efb615011000ff3615011009fbb415011009ff2415011009fb9415011004ff14150110007b1415011009ff22150110007f12150110015f8764c110026f8764c110014f8764c110006fb654c110006f9654c110005fb744c110005f9744c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110047d8634c11021fdb534c110047d8534c110047da434c110007d9434c110047db324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c11000efb614c11000ff3614c11007ff2414c110007f1414c11007fdb314c11007fd9314c11007ff2214c110007f1214c110
  | 1 => 0x95102a67f51d95102a67d51d95102a6f621d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102967f50d95102967d50d9510296fa30d9510034ff76595100567c6559510005df7359510045dc735951028df7715951029dfb7059510294ff75595100067f7559510004ff745951002cfe745951002cfc74595100567f5459510004ff7359510006df7359510004df7359510024fe7359510024fc7359510006dc7359510024dc7359510004ff725951001cfe725951001cfc725951028cff7159510006f771595100bef6215951013cff7059510006fb705951013efa305951002cfe76d911004ebe64d9110034fe75d9110004fd75d9110034fc75d911011cfd74d911004ebe54d9110024fe73d9110004fd73d9110024fc73d911001cfe72d9110004fd72d911001cfc72d9110006be42d911004ebc42d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110286bf41d9110286bd41d9110286f621d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110276bf40d9110276bd40d911002cff765911004ebc645911026df7715911027dfb7059110004ff7559110034fe7559110034fc7559110274ff7459110006bf7459110004ff7359110024fe7359110024fc7359110004ff725911001cfe725911001cfc725911026cff7159110006f7715911009ef6215911011cff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc76551100367e65551100067d6555110006bf645511002ebc6455110024fe76d8d10046de63d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d10006df53d8d10046dc53d8d1001cfe72d8d10004fd72d8d1001cfc72d8d10046df32d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10266df31d8d10266dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10256df30d8d10256dd30d8d10024ff7658d10046dc6358d1024df77158d1025dfb7058d10004ff7558d10034fe7558d10034fc7558d10004ff7458d1002cfe7458d1002cfc7458d10254ff7358d10006df7358d10046de4358d10004ff7258d1001cfe7258d1001cfc7258d1024cff7158d10006f77158d100fcff7058d10006fb7058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10026de6350d10006dd6350d1000dfa7050d1001cfe76d891003eee62d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d891000cff71d8910014fe71d891000cfd71d8910014fc71d8910246f641d8910246ef21d8910246e
  | 2 => 0x26de6350d20006dd6350d2000dec765092002eec765092000cec765092001def745092001faf7450920007af645092002eee645092002eec645092006fac645092006fae5450920007ad5450920005ef7150920007eb705092000dee705092000dec705092017fe8705092001eef605092001feb605092017fea505092017faf405092017fea405092017fad4050920014fe76d852005ef661d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d85202c6ee42d8520006ed42d852005ef621d85202c6f521d852000cfe70d852001cfd70d852000cfc70d852022efa40d852022ef710d8520005bf745852006dbc745852005ef461585202bdfb7058520004ff7654520004fe7654520004fc76545200067f65545200367c6554520005df7354520065dc7354520004ff7650520004fe7650520004fc765052001dee7250520016f66150520004ff764c520004fe764c520004fc764c52000dec7648520016ec764852000cec76485200f6ee65485200f6ec6548520005ef7448520005ed7448520006ef6448520006ed6448520006ef6348520006ed634852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005fe65148520007e5514852005fe64148520007e541485202b7e7314852005fe43148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200dfea50485200dfea40485200dfe7104852001df87654120036f8765412001cf8765412000dfb755412000f7b75541200077b6554120036fa6554120036f86554120077786554120005fb74541200777b5454120007795454120006fb6354120006f963541202af7a5354120077785354120007eb725412001dfa725412001df872541200c7e8725412000efb625412000feb62541200c77b52541200c77952541200c7ea4254120007e942541200777b51541200077951541200c7eb2154120007e9215412001df8765012002ef8765012001cf87650120005fb7550120005f9755012000dfb745012000fbb7450120007bb645012002efa645012002ef8645012006fb8645012002eb86450120007eb725012001dfa725012001df872501200a7e8725012000efb625012000feb62501200a7bb42501200a7ea42501200a7b9425012006fe94250120007a94250120006fb615012006fbb4150120007b941501200a7eb2150120007e92150120034fe76d95100567e65d951013cfd75d951002cfe74d9510004fd74d951002cfc74d9510024fe73d9510004fd73d9510024fc73d951001cfe72d9510004fd72d951001cfc72d951000cff71d9510014fe71d951000cfd71d9510014fc71d
  | 3 => 0x94354130006fb62541300977b52541300077952541300cfdb3254130007d93254130005fb71541300977b51541300077951541300cfdb3154130007d93154130034fe76d95200767e65d952019cfd75d952002cfe74d9520004fd74d952002cfc74d9520024fe73d9520004fd73d9520024fc73d95200067e53d95200767c53d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203267f52d95203267d52d9520014fe71d9520004fd71d9520014fc71d95200767f51d952001cff70d952001cfd70d95203167f50d95203167d50d9520034ff76595200767c655952030def725952031dfb7059520314ff75595200067f7559520004ff745952002cfe745952002cfc74595200767f5459520004ff7359520024fe7359520024fc735952030cff7259520006ef7259520004ff7159520014fe7159520014fc715952019cff7059520006fb705952002cfe76d912006ebe64d9120034fe75d9120004fd75d9120034fc75d912017cfd74d9120024fe73d9120004fd73d9120024fc73d912006ebf43d912000cff72d912001cfe72d912000cfd72d912001cfc72d9120306bf42d9120306bd42d9120014fe71d9120004fd71d9120014fc71d9120006be41d912006ebc41d9120306ef21d912001cff70d912001cfd70d91202f6bf40d91202f6bd40d912002cff765912006ebc64591202edef72591202fdfb7059120004ff7559120034fe7559120034fc75591202f4ff7459120006bf7459120004ff7359120024fe7359120024fc73591202ecff7259120006ef7259120004ff7159120014fe7159120014fc71591200a6ef215912017cff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc76551200367e65551200067d655512000dfa7055120024fe76d8d20066de63d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202e6df32d8d202e6dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d202e6ef21d8d2001cff70d8d2001cfd70d8d202d6fa50d8d202d6df30d8d202d6dd30d8d20024ff7658d200057f7558d200757c7558d20066dc6358d202cdef7258d202ddfb7058d20004ff7558d200067f7558d200047f7558d20034fe7558d20034fc7558d200067c7558d200347c7558d20004ff7458d2002cfe7458d2002cfc7458d202d4ff7358d20006df7358d20066de4358d202ccff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d20086ef2158d2015cff7058d20006fb7058d2015efa5058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d2002ebc6450d20
  | 4 => 0xd301bfda5050d301bfda1050d3001cfe76d8930086ee62d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930346de43d8930006dd43d8930086ee32d8930346ed32d8930014fe71d8930004fd71d8930014fc71d8930024fd70d89302cefa50d89302ceef20d89300057f75589300957c7558930086ec625893033dfb7058930004ff7654930004fe7654930004fc7654930005df7354930025dc7354930004ff7650930004fe7650930004fc7650930025de7350930005fb705093000df8705093000ddc764c93001edc764c93000cdc764c9300075f754c930095de754c930095dc754c9300075c754c9300955c754c930006df654c930006dd654c930005df744c930005dd744c930006df644c930006dd644c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c930087ce524c930007cd524c930005df714c930166de614c930166dc614c930087cf214c930007db704c93000dde704c93000ddc704c93015fd8704c930026df604c930027db604c93015fda504c93015fda104c930014fe76d853007ef661d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d8530336de43d8530006dd43d853001cfe72d8530004fd72d853001cfc72d8530006f741d853007ef441d853007ef631d8530336f531d853007ef621d8530024fd70d853024ef710d853007ef4615853032dfb7058530004ff7654530004fe7654530004fc76545300367e65545300067d6554530005df7354530025dc73545300975f535453000dfa7054530004ff7650530004fe7650530004fc765053002ebe6450530006bd6450530025de73505300079d435053000ddc764c530016dc764c53000cdc764c530095de754c530095dc754c530005df744c530005dd744c530006df644c530006dd644c530005df724c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6514c530007d5514c530007db704c53000dde704c53000ddc704c5300ffd8704c530026df604c530027db604c5300ffda504c5300ffda104c530004ff7648530004fe7648530004fc7648530025de7348530005dd734853001eee6248530007cd3248530006f76148530016f461485300e7d73148530025f87654130036f87654130024f8765413000dfb755413000f7b75541300077b6554130036fa6554130036f865541300977865541300977b5454130007795454130007db7354130025fa7354130025f873541300cfd8735413000efb635413000fdb6354130097db53541300cf7a53541300cf7853541300cfd853541300cf5853541300cfda4354130007d
  | 5 => 0x2ebf605054002fbb605054011fba205054011fb7105054011fba1050540004ff764c540004fe764c540004fc764c540026de634c5400ffb8404c540004ff7648540004fe7648540004fc764854002dbe7448540005bd744854001eee6248540007ad4248540016f66148540007b5414854000dfa70485400dfb84048540034fe76d95300967e65d9530025de73d953000ddd73d95300975f53d95301dcfd75d953002cfe74d9530004fd74d953002cfc74d95300967f54d953000cff73d9530024fe73d953000cfd73d9530376dd73d953000cdd73d9530024fc73d95303867f53d9530096df53d95303867d53d9530386dc53d953001cfe72d9530004fd72d953001cfc72d95300067e52d95300967c52d9530386df32d9530014fe71d9530004fd71d9530014fc71d9530024ff70d9530024fd70d95303767f50d95303767d50d9530034ff76595300967c655953036ddf73595300cf5c535953037dfb7059530374ff75595300067f7559530004ff745953002cfe745953002cfc745953036cff7359530006df7359530096df53595300ce7e53595300ce7c53595300cedc5359530004ff725953001cfe725953001cfc72595300cedf3259530004ff7159530014fe7159530014fc71595300967f51595301dcff7059530006fb705953002cfe76d913008ebe64d9130034fe75d9130004fd75d9130034fc75d91301bcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d9130006df53d9130366dc53d9130366bf43d9130366bd43d913001cfe72d9130004fd72d913001cfc72d9130366df32d9130014fe71d9130004fd71d9130014fc71d9130366df31d9130024ff70d9130024fd70d9130356bf40d9130356bd40d9130356fa10d913002cff765913008ebc645913034ddf7359130005f7715913007df4715913035dfb7059130004ff7559130034fe7559130034fc7559130354ff7459130006bf745913034cff7359130006df7359130006df53591300aedc5359130004ff725913001cfe725913001cfc72591300aedf3259130004ff7159130006f77159130004f77159130014fe7159130014fc7159130006f47159130014f4715913008ebf41591300aedf31591301bcff7059130006fb70591301befa1059130004ff7655130004fe7655130004fd7655130004fc76551300067f65551300367c6555130005df7355130025dc73551302175c535513000ddc7650d3002edc7650d3000cdc7650d30095de7550d30095dc7550d301d6de6550d301d6dc6550d30025df7450d300279f7450d300079f6450d3002ede6450d3002edc6450d3008f9c6450d3008f9e5450d300079d5450d30005df7250d30005df7150d3008f9f4150d30007db7050d3000dde7050d3000ddc7050d301bfd87050d30026df6050d30027db605
  | 6 => 0xf7459540006bf7459540004ff7359540024fe7359540024fc73595400067e53595400b67c5359540004ff7259540006ef7259540004ef725954001cfe725954001cfc7259540006ec725954001cec72595400b67f52595400d6bf4259540004ff7159540014fe7159540014fc71595400b67f51595401fcff7059540006fb70595401fefa2059540024fe76d8d400b57e75d8d400057d75d8d400aede63d8d4034fb840d8d40034fe75d8d400067e75d8d400347e75d8d40004fd75d8d400067d75d8d400047d75d8d40034fc75d8d4000cfd74d8d40024fc74d8d400aede43d8d403b6dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40014fe71d8d40004fd71d8d40014fc71d8d403b6bf41d8d4002cfd70d8d4034edf30d8d4034efa10d8d400aedc6358d40005f77158d4009df47158d403adfb7058d401bfb84058d40004ff7654d40004fe7654d40004fc7654d401dfb84054d4001cfe76d89400a6ee62d89402efb840d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d8940006ef52d89400a6ec52d89400a6ee42d89403a6ed42d89400a6ee32d8940014fe71d8940004fd71d8940014fc71d894002cfd70d89402eeef20d89400a6ec625894039dfb705894017fb84058940004ff7654940004fe7654940004fc76549400367e65549400067d655494019fb8405494000dbc765094001ebc765094000cbc7650940006bf6550940006bd655094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400a7ac6250940005bf71509400a7af2150940007bb705094000dbe705094000dbc705094017fb8705094000db8705094002ebf605094002fbb605094017faf205094017fba205094017fba1050940004ff764c940004fe764c940004fc764c9400057f754c9400b57c754c940026de634c940006ef624c94001eec624c94015fb8404c940014fe76d854009ef661d854026fb840d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540024fe73d8540004fd73d8540024fc73d854001cfe72d8540004fd72d854001cfc72d854009ef651d854009ef641d8540396f541d8540006f731d854009ef431d854002cfd70d854026ef710d854009ef4615854038dfb705854011fb84058540004ff7654540004fe7654540004fc76545400367e65545400067d6554540005df73545400addc7354540006f76154540016f4615454013fb8405454000dbc7650540016bc765054000cbc7650540006bf6350540005bf725054002dbf715054002fb77150540007b76150540016be6150540016bc615054009fb4615054009fb62150540007bb705054000dbe705054000dbc705054011fb8705054000db87050540
  | 7 => 0x8950004fd73d8950024fc73d89500c6ee52d89503f6ed52d8950006ef42d89500c6ec42d8950014fe71d8950004fd71d8950014fc71d89500c6ef21d8950034fd70d895030eef20d89500c6ec62589503edfb705895000d7c765495001e7c765495000c7c76549500057f74549500067f64549500cd7e73549500cd7c73549500357f72549500376f72549500076f625495001e7e625495001e7c62549500c76c62549500c76e32549500057f71549500077b705495000d7e705495000d7c705495019f7870549500367f60549500377b605495019f7a305495019f7a2054950004ff7650950004fe7650950004fc76509500357e75509500057d755095002ebe64509500073d5450950004ff764c950004fe764c950004fc764c9500057f754c9500357c754c950026de634c9500cf5e534c9500076d524c95000dfa704c950014fe76d85500bef661d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d85503e67f54d85500067d54d8550024fe73d8550004fd73d8550024fc73d855001cfe72d8550004fd72d855001cfc72d85500bef651d85503e6f551d8550034fd70d855028efa30d855028ef710d8550005df73585500cddc73585500bef461585503ddfb705855000d7c76545500167c765455000c7c76545500057f74545500067f64545500075f73545500cd7e73545500cd7c73545500075c73545500cd5c73545500067f63545500057f72545501467e62545501467c62545500357f71545500377771545500077761545500167e61545500167c61545500bf7461545500bf7631545500bf7621545500077b705455000d7e705455000d7c705455013f7870545500367f60545500377b605455013f7a305455013f7a2054550004ff7650550004fe7650550004fc76505500357e75505500057d7550550005fb705055000df87050550004ff764c550004fe764c550004fc764c5500057f754c5500357c754c55000775514c550004ff7648550004fe7648550004fc76485500357e75485500057d7548550006ef624855001eec62485500f76f5248550016f66148550007755148550034fe76d95400b67e65d95400adde73d9540005dd73d95403c7b840d95401fcfd75d954000cff74d954002cfe74d954000cfd74d954002cfc74d95403d67f54d95403d67d54d9540024fe73d9540006de73d9540024de73d9540004fd73d9540006dd73d9540004dd73d9540024fc73d954001cfe72d9540004fd72d954001cfc72d95403d6bf42d9540014fe71d9540004fd71d9540014fc71d954002cff70d954002cfd70d95403c67f50d95403c67d50d95403c6fa20d9540034ff76595400b67c65595403bdbf7459540005ef72595400a5ec72595403cdfb70595401ffb840595403c4ff75595400067f75595403bcf
  | 8 => 0x16f76254521017e762545210f7e75254521147765254521147745254521147e45254521147645254521147e64254521007e54254521147e63254521007e53254521005f770545210f7775054521147e7205452101df4765052102ef4765052101cf47650521005f77550521005f57550521015f77450521017b77450521007b7645052102ef6645052102ef464505210efb464505210e5f673505210e5f473505210efb74350521007b54350521007e7725052101df6725052101df47250521127e47250521016f76250521017e7625052141fe75250521127e45250521127e642505210efe54250521127e63250521007e53250521005f770505210efb74050521127e7205052100cfe76d81210defa60d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d81212beee42d8121006ed42d812101cfd71d812100cfc71d812123ef641d8121006f541d8121006fb40d81210def840d81210defa20d81210defa10d8121005bf74581210edbc74581210def8605812102cfe76d91500d6be64d915000cfd75d915002cfc75d91500d6be54d9150416bd54d9150024fe73d9150004fd73d9150024fc73d91500067e53d91504167c53d915001cfe72d9150004fd72d915001cfc72d91504167f52d9150014fe71d9150004fd71d9150014fc71d91504167f51d9150034fd70d91503bebf40d91503befa20d91500d6bc6459150005ef72591500c5ec725915040dfb705915000d7c765515002e7c765515000c7c76551500357f74551500373f74551500073f645515002e7e645515002e7c64551500d73c64551500cd7e73551500cd7c73551502167e63551502167c63551500d73f43551500057f72551500d73f42551500057f71551500077b705515000d7e705515000d7c70551501ff7870551500367f60551500377b60551501ff7a30551501ff7a2055150024fe76d8d500357e75d8d5000d7d75d8d500cede63d8d500cf5e53d8d5000cfd75d8d5036e7d75d8d5000c7d75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500ce7e53d8d500cede53d8d50406dd53d8d500ce7c53d8d500cede43d8d5001cfe72d8d50004fd72d8d5001cfc72d8d50014fe71d8d50004fd71d8d50014fc71d8d504067f51d8d50006de31d8d500cedc31d8d50034fd70d8d5036edf30d8d500cedc6358d500cf5c5358d503fdfb7058d50004ff7650d50004fe7650d50004fc7650d500057f7550d500357c7550d500073d5450d50006df6350d50026dc6350d500cf5c5350d5001cfe76d89500c6ee62d895000cfd75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d89503f67f54d89500067d54d8950024fe73d
  | 9 => 0xe76d8d210e6de63d8d21015f671d8d2101df571d8d210e7d731d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21164fd73d8d21006df53d8d210e6dc53d8d21014ff72d8d21014fd72d8d21446df32d8d21446dd32d8d2101cff71d8d2101cfd71d8d21446f571d8d2101cf571d8d21436f651d8d21436df31d8d210e6f731d8d21436dd31d8d21436f431d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21024ff7658d210057f7558d210f57c7558d210e6dc6358d2142def7258d2143df77158d21167d43158d21004ff7558d210067f7558d210047f7558d21034fe7558d21034fc7558d210067c7558d210347c7558d21004ff7458d2102cfe7458d2102cfc7458d21434ff7358d21006df7358d210e6de4358d2142cff7258d21006ef7258d21164ff7158d21006f77158d21166f65158d210e6f73158d21166de3158d21166dc3158d21166f43158d21004ff7058d2100cfe7058d2100cfc7058d210e6df3058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21005ef7254d2101dec7254d21005f77154d21015f47154d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21026de6350d21006dd6350d2101dee7250d21005f77150d21015f47150d210e7d73150d21015ec765092102eec7650921014ec76509210f5ee75509210f5ec755092101def745092101faf7450921007af645092102eee645092102eec64509210efac64509210efae5450921007ad5450921005ef7350921007e77150921015ee7150921015ec7150921187e4715092101eef615092101fe76150921187e65150921187e64150921427e73150921187e43150921005ef70509210efaf4050921187e71050921015ec764c921026ec764c921014ec764c9210076f754c9210f5ee754c9210f5ec754c9210076c754c9210f56c754c921006ef654c921006ed654c921005ef744c921005ed744c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c9210e7cc634c9210e7ce534c921007cd534c9210e7ce434c921007cd434c921007e7714c921015ee714c921015ec714c921167e4714c92101eef614c92101fe7614c921167e6514c921167e6414c9210e7e7314c921167ce314c921167cc314c921167e4314c921167c4314c921005ef704c9210e7cf304c921167e7104c92101df47654521036f4765452101cf47654521015f77554521017777554521007776554521036f66554521036f465545210f7746554521005f774545210f7775454521007755454521007d773545210e5f673545210e5f47354521007d473545210e5d47354521006f76354521006f563545210f7775354521007755354521007e7725452101df6725452101df47254521147e47254521
  | 10 => 0x931025f47654531036f47654531024f47654531015f77554531017777554531007776554531036f66554531036f46554531117746554531117775454531007755454531007d77354531025f67354531025f4735453114fd47354531016f76354531017d7635453114f77535453114f75535453114fd64354531007d54354531006f7625453148f76525453111774525453111777505453114fd7305453100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813132ede43d8131006dd43d813101cfe72d8131004fd72d813101cfc72d8131024fd71d81310fefa30d81310fefa10d81310fef86058131034fe76d95210f67e65d952101dee72d9521015ed72d95210f76f52d95211a4fd75d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521004fd73d9521024fc73d95210067e53d95210f67c53d9521014ff72d9521014fd72d9521476ed72d9521014ed72d95214867f52d95210f6ef52d95214867d52d9521486ec52d9521486ee32d952101cff71d952101cfd71d95214767f51d95214767d51d952100cfe70d9521004fd70d952100cfc70d9521034ff76595210f67c6559521005df73595210e5dc735952146def72595211476c525952147df77159521474ff75595210067f7559521004ff745952102cfe745952102cfc74595210f67f5459521004ff7359521006df7359521004df7359521024fe7359521024fc7359521006dc7359521024dc735952146cff7259521006ef72595210f6ef52595211467e52595211467c5259521146ec5259521146ee32595211a4ff7159521006f77159521004ff705952100cfe705952100cfc70595210f67f505952102cfe76d91210eebe64d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121024fe73d9121004fd73d9121024fc73d9121014ff72d9121014fd72d9121466bf42d9121466bd42d912101cff71d912101cfd71d9121456bf41d9121456bd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d91210eebc40d9121466ef20d9121456f710d912102cff76591210eebc645912144def725912145df77159121005fb70591210ddf87059121004ff7559121034fe7559121034fc7559121454ff7459121006bf7459121004ff7359121024fe7359121024fc735912144cff7259121006ef7259121184ff7159121006f77159121004ff7059121006fb7059121004fb705912100cfe705912100cfc7059121006f8705912100cf870591210eebf4059121126ef2059121186f71059121004ff7655121004fe7655121004fd7655121004fc76551210367e65551210067d6555121005ef725512101dec72551210f76f5255121015f67155121024f
  | 11 => 0x26dc634c9410079d434c94100cfe76d814111efa60d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d814101cfe72d8141004fd72d814101cfc72d814102cfd71d814127ef621d814111efa50d814111efa40d8141006fb20d814111ef820d814111efa10d814111ef86058141034fe76d95311167e65d95311e4fd75d953102cfe74d9531004fd74d953102cfc74d95311167f54d9531014ff73d9531014fd73d95314de7f53d95314de7d53d953101cfe72d9531004fd72d953101cfc72d95310067e52d95311167c52d9531024ff71d9531024fd71d95314ce7f51d95314ce7d51d953100cfe70d9531004fd70d953100cfc70d95311167f50d9531034ff76595311167c65595314c5df73595314d5f771595314ccff75595310067f7559531004ff745953102cfe745953102cfc74595314c4ff7359531006df73595314c4df7359531004ff725953101cfe725953101cfc72595311e4ff7159531006f77159531004ff705953100cfe705953100cfc705953102cfe76d913110ebe64d9131034fe75d9131004fd75d9131034fc75d91311c4fd74d9131014ff73d9131014fd73d91314bebf43d91314bebd43d913101cfe72d9131004fd72d913101cfc72d9131024ff71d9131024fd71d91314aebf41d91314aebd41d913100cfe70d9131004fd70d913100cfc70d91314bedf30d913102cff765913110ebc64591314a5df73591314b5f77159131004ff7559131034fe7559131034fc75591314acff7459131006bf74591314a4ff7359131006df7359131004ff725913101cfe725913101cfc72591311c4ff7159131006f77159131004ff705913100cfe705913100cfc705913112edf3059131004ff7655131004fe7655131004fd7655131004fc76551310067f65551310367c6555131015dc7650d3102edc7650d31014dc7650d311d6de6550d311d6dc6550d31025df7450d310279f7450d310079f6450d3102ede6450d3102edc6450d3110f9c6450d3110f9e5450d310079d5450d31007d77150d31015de7150d31015dc7150d311c7d47150d31026df6150d31027d76150d311c7d65150d311c79f4150d311c79d4150d31005df7050d3101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d893149ede43d8931006dd43d8931106ee32d893149eed32d8931024fd71d893142ef651d893149ef731d893142ede31d893142edc31d893142ef431d893142eef21d893100cfe70d8931004fd70d893100cfc70d893149edf30d89310057f75589311157c7558931106ec6258931495f77158931004ff7654931004fe7654931004fc7654931004ff7650931004fe7650931004fc765
  | 12 => 0xd5450951006df635095118edc6350951004ff764c951004fe764c951004fc764c9510057f754c9510357c754c951006df634c951026dc634c9510075d534c95101eee624c9511476e524c951015f6714c951167d6314c95100cfe76d8151006df63d8151006dc63d815113efa60d8151014fd75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d81513de7f54d81510067d54d8151024fe73d8151004fd73d8151024fc73d815101cfe72d8151004fd72d815101cfc72d8151034fd71d815129ef621d815113efa50d815113efa10d8151005df735815114ddc7358151006df6358151006dc635815113ef86058151034fe76d95411367e65d9541204fd75d9541014ff74d9541014fd74d95415267f54d95415267d54d9541024fe73d9541004fd73d9541024fc73d9541526bf43d954101cfe72d9541004fd72d954101cfc72d954102cff71d954102cfd71d95415167f51d95415167d51d9541516f621d954100cfe70d9541004fd70d954100cfc70d9541034ff76595411367c655954150dbf7459541005df735954112ddc735954151df77159541514ff75595410067f755954150cff7459541006bf7459541004ff7359541006df7359541004df7359541024fe7359541024fc7359541006dc7359541024dc7359541156bf4359541004ff725954101cfe725954101cfc7259541204ff7159541006f77159541206f62159541004ff705954100cfe705954100cfc70595411367f5059541024fe76d8d4112ede63d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d41006df53d8d4112edc53d8d4112ede43d8d41506dd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4112edf32d8d4102cfd71d8d414a6df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d4112edc6358d414fdf77158d41004ff7654d41004fe7654d41004fc7654d41015bc7650d41026bc7650d41014bc7650d41006bf6550d41006bd6550d4102dbf7350d4102f9f7350d410079f6350d41026be6350d41026bc6350d4112f9c6350d414f79f5350d4112f9c5350d4112f9f3250d41007b77150d41015be7150d41015bc7150d411c7b47150d4102ebf6150d4102fb76150d411c79f3150d411c7b62150d41005bf7050d4112f9f3050d411c7b71050d4101cfe76d8941126ee62d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d8941126ee42d89414eeed42d894102cfd71d894144eef21d894100cfe70d8941004fd70d894100cfc70d89414eebf40d894144ef710d8941126ec62589414e5f77158941005fb705894111df87058941004ff7654941004fe7654941004fc7654941004ff764c941004fe764c941004fc764c9410057f754c9411357c754c941006df634c941
  | 13 => 0x8d51557d751d8d514c75e51d8d514c75c51d8d514c7d451d8d514c7d621d8d51006de60d8d51006dc60d8d515575f50d8d514c6df75d8d5114ede75d8d514c6dd75d8d514c6dc75d8d51006df74d8d51006de74d8d51006dd74d8d51006dc74d8d51556df54d8d51556de54d8d51556dd54d8d51556dc54d8d51006df72d8d51006de72d8d51006dd72d8d51006dc72d8d51556df52d8d51556de52d8d51556dd52d8d51556dc52d8d51006df42d8d51006de42d8d51006dc42d8d514c6df71d8d514c6de71d8d514c6dd71d8d514c6dc71d8d514c6df51d8d514c6de51d8d514c6dc51d8d514c6df41d8d514c6de41d8d514c6dd41d8d514c6dc41d8d514c6df21d8d514c6de21d8d514c6dd21d8d514c6dc21d8d51006df70d8d51006de70d8d51006dd70d8d51006dc70d8d51556df50d8d51556de50d8d51556dd50d8d51556dc50d8d51006df40d8d51006de40d8d51006dc40d8d51006df20d8d51006de20d8d51006dc20d8d514c6df10d8d514c6de10d8d514c6dd10d8d514c6dc10d8d5114edc6358d5154df77158d514c5de7618d5114ede7618d5114f5e7518d515475d7518d51546df6518d5114f9e7418d5114f9d7418d51006df6418d51006de6418d51006dd6418d51006dc6418d5153f5f5418d510075d5418d5114fce7218d5114fcd7218d51006de6218d51006dc6218d510075e5218d5153f5c5218d51547d67118d5114fd57118d51546df6118d5153fd75118d515475e5118d515475c5118d51547d45118d51547d62118d5114fda7018d5114fd97018d51006de6018d51006dc6018d5153f5f5018d510157c7654d510267c7654d510147c7654d510057f7454d510357f7354d510375f7354d510075f6354d510267e6354d510267c6354d5114f5c6354d511457e7254d511457c7254d5114f5f3254d51007777154d510157e7154d510157c7154d511e7747154d510367f6154d51037776154d511e7763154d511e7762154d510057f7054d51004ff7650d51004fe7650d51004fc7650d510357e7550d510057d7550d5102ebe6450d510073d5450d51006df6350d51026dc6350d511d75f5350d5101cfe76d89510357e75d89510157d75d8951006df63d8951006dc63d8951146ee62d89511476e52d8951014fd75d895146e7d75d89510147d75d895102cfe74d8951004fd74d895102cfc74d89515367f54d89510067d54d8951024fe73d8951004fd73d8951024fc73d89511467e52d8951146ee52d8951536ed52d89511467c52d8951034fd71d895146eef21d895100cfe70d8951004fd70d895100cfc70d89515367f50d8951005df735895114ddc7358951006df6358951006dc6358951146ec62589511476c525895152df77158951004ff7650951004fe7650951004fc76509510057f75509510357c75509510073
  | 14 => 0x24ec765493201def755493201f6f75549320076f6554932036ee6554932036ec65549321776c65549321776f54549320076d5454932007cf7354932025ee7354932025ec73549321afcc735493201eef635493201fcf63549321afce5354932177cd53549321afce4354932007cd4354932005ef715493256fce31549321afcc31549321776f50549321afcf3054932014fe76d85320067f65d85320067c65d8532025de73d853201ddd73d8532166f661d8532167d631d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532166dd73d853201cdd73d8532496de43d8532006dd43d8532024fd72d8532166de31d8532166f631d8532166dc31d8532166f621d853200cfe70d8532004fd70d853200cfc70d8532496df30d85320057f75585321757c75585320067f65585320067c6558532166f46158532167d4315853200cfe76d81320067f65d81320067c65d813215efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d813233ede43d8132006dd43d8132024fd72d8132014fe71d8132004fd71d8132014fc71d81322deef21d813215efa30d813215efa20d81320057f75581321757c75581320067f65581320067c655813215ef8605813202cfe76d9151156be64d9151014fd75d9151156be54d9151566bd54d9151024fe73d9151004fd73d9151024fc73d915101cfe72d9151004fd72d915101cfc72d9151034fd71d915150ebf41d915150ef621d915100cfe70d9151004fd70d915100cfc70d91515667f50d9151156bc6459151005df735915114ddc735915155df771591510157c765515102e7c76551510147c76551510357f74551510373f74551510073f645515102e7e645515102e7c64551511573c64551510057f73551512167e63551512167c63551512165c63551511573f43551511457e72551511457c72551511573f42551510077771551510157e71551510157c71551512077471551510367f61551510377761551512077631551512077621551510057f7055151024fe76d8d5114ede63d8d51014fd75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5114ede53d8d51556dd53d8d51006df43d8d5114ede43d8d5114edc43d8d5101cfe72d8d51004fd72d8d5101cfc72d8d5114edf32d8d51006de32d8d5114edc32d8d51034fd71d8d514c6df31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d5114edf30d8d51006de30d8d5114edc30d8d51545de76d8d51024de76d8d514c75f75d8d514c75c75d8d51006df64d8d51006de64d8d51006dd64d8d51006dc64d8d515575f54d8d510075d54d8d51006de62d8d51006dc62d8d510075e52d8d515575c52d8d51557d771d8d514c7d471d
  | 15 => 0xc20d95320067f10d95320067e10d95320067c10d9532034ff76595321767c65595325addf73595325b5ef72595325a4ff75595320067f7559532004ff745953202cfe745953202cfc74595325acff7359532006df73595321ecff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff705953200cfe705953200cfc70595325a57e76195321767e76195325a47e76195321773e74195321773d74195320067e64195320067c64195325975e731953259f5d731953259e7f63195325975e431953259f6e72195325976d721953259e7f62195325976f321953259f5e321953259f5c321953259f6c32195321777671195321777571195320067e61195320067c61195320075e31195325975c311953259f6f21195321777a70195321777970195320067e60195320067c60195325975f301953202cfe76d91320067f65d91320067c65d913216ebe64d9132034fe75d9132004fd75d9132034fc75d91321ccfd74d913201cff73d913201cfd73d913258ebf43d913258ebd43d9132024ff72d9132024fd72d913257ebf42d913257ebd42d9132014fe71d9132004fd71d9132014fc71d913257eef21d913200cfe70d9132004fd70d913200cfc70d913258edf30d913202cff76591320057f75591321757c75591320067f65591320067c655913216ebc6459132575df7359132585ef7259132004ff75591320067f75591320047f7559132034fe7559132034fc75591320067c75591320347c755913257cff7459132006bf745913216ebe5459132574ff7359132006df73591321ccff7259132006ef7259132004ff7159132014fe7159132014fc71591321ceef2159132004ff705913200cfe705913200cfc705913218edf3059132004ff7655132004fe7655132004fd7655132004fc76551320067f65551320367c655513202ebe6455132006bd6455132025de73551322175e535513201ddc7654d32036dc7654d3201cdc7654d32025df7554d320275f7554d320075f6554d32036de6554d32036dc6554d321775c6554d32005df7454d32007cf7254d3201dde7254d3201ddc7254d321efcc7254d32026df6254d32027cf6254d321efce5254d32165de7154d32165dc7154d321775f5154d321efcf2154d32005df7054d3201ddc7650d3202edc7650d3201cdc7650d32005df7550d32005dd7550d320075f6550d321d6de6550d321d6dc6550d320075c6550d321d65c6550d32025df7450d320279f7450d320079f6450d3202ede6450d3202edc6450d3216f9c6450d3216f9e5450d320079d5450d32007cf7250d3201dde7250d3201ddc7250d321cfcc7250d32026df6250d32027cf6250d321cfce5250d32165de7150d32165dc7150d3216f9f4150d321cfcf2150d32005df7050d32025ec7654932036ec7654932
  | 16 => 0x51421973f505514220faf2055142024fe76d8d4218ede63d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d425cebe54d8d42006bd54d8d4218ede43d8d425cedd43d8d4202cfd72d8d42576df32d8d42014fe71d8d42004fd71d8d42014fc71d8d42576ef21d8d4200cfe70d8d42004fd70d8d4200cfc70d8d420057f7558d421957c7558d4218edc6358d425c5ef7258d42004ff7654d42004fe7654d42004fc7654d42014fe76d8542186f661d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d8542186f641d8542186f621d854200cfe70d8542004fd70d854200cfc70d85424e6bf40d854245eef20d8542186f46158542005fb705854217df8705854200cfe76d814217efa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d814202cfd72d8142014fe71d8142004fd71d8142014fc71d81422feef21d814217efa40d814217efa30d814217efa20d8142006fb10d814217ef810d814217ef86058142034fe76d95321767e65d95321ecfd75d953202cfe74d9532004fd74d953202cfc74d95321767f54d95320067e54d95321767c54d953201cff73d953201cfd73d95325be7f53d95325be7d53d9532024ff72d9532024fd72d95325a67f52d95325a67d52d9532014fe71d9532004fd71d9532014fc71d95321767f51d95320067e51d95321767c51d953200cfe70d9532004fd70d953200cfc70d95321767f50d95320067e50d95321767c50d953259d7e76d95320347e76d95320067e64d95320067c64d95325a75f73d95325a75c73d95325bf5e43d95325bf6f72d95325a76c72d95325bf6f32d95325a75e32d95325a75c32d95325a76c32d95320067e61d95320067c61d95320075e31d95325bf5c31d95325a76f21d95320067e60d95320067c60d95325bf5f30d95320067f74d95320067e74d95320067d74d95320067c74d95325a67f73d95325be7e73d95325a67d73d95325a67c73d95325be7f43d95325be7e43d95325be7d43d95325be7c43d95325a67f72d95325a67e72d95325a67d72d95325a67c72d95325a67f42d95325a67e42d95325a67d42d95325a67c42d95325a67f32d95325a67e32d95325a67c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067c41d95325be7f31d95325be7e31d95325be7d31d95325be7c31d95325a67f21d95325a67e21d95325a67d21d95325a67c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067c40d95325be7f30d95325be7e30d95325be7d30d95325be7c30d95325a67f20d95325a67e20d95325a67d20d95325a67
  | 17 => 0x4fd73d9152024fc73d9152034fd72d91525debf42d9152014fe71d9152004fd71d9152014fc71d915200cfe70d9152004fd70d915200cfc70d91526167f50d91521b6bc645915260def725915201d7c765515202e7c765515201c7c76551520357f74551520373f74551520073f645515202e7e645515202e7c64551521b73c64551522167e63551522167c63551521b73f43551520076f725515201d7e725515201d7c725515220f6c72551520367f62551520376f625515220f3f425515220f6e32551520057f7055152024fe76d8d521aede63d8d5201cfd75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521aede53d8d52606dd53d8d521aede43d8d52034fd72d8d525aedf32d8d52014fe71d8d52004fd71d8d52014fc71d8d52006de31d8d521aedc31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d521aedf30d8d521aedc6358d525fdef7258d52004ff7650d52004fe7650d52004fc7650d520073d5450d52006df6350d52026dc6350d52014fe76d85521a6f661d855201cfd75d855202cfe74d8552004fd74d855202cfc74d855252e7f54d85520067d54d8552024fe73d8552004fd73d8552024fc73d8552034fd72d855252eef52d855247e7e52d855247e7c52d855247eec52d855247eee32d85521a6f651d85521a6f621d855200cfe70d8552004fd70d855200cfc70d855252e7f50d8552005df73585521addc73585521a6f4615855200cfe76d815219efa60d815201cfd75d815202cfe74d8152004fd74d815202cfc74d81523ee7f54d81520067d54d8152024fe73d8152004fd73d8152024fc73d8152034fd72d8152014fe71d8152004fd71d8152014fc71d815219efa50d815219efa20d815219ef86058152034fe76d95421967e65d954220cfd75d954201cff74d954201cfd74d95425f67f54d95425f67d54d9542024fe73d9542004fd73d9542024fc73d95420067e53d95421967c53d954202cff72d954202cfd72d95425e67f52d95425e67d52d9542014fe71d9542004fd71d9542014fc71d95421967f51d954200cfe70d9542004fd70d954200cfc70d9542034ff76595421967c65595425ddbf74595425edef72595425e4ff75595420067f75595425dcff7459542006bf7459542004ff7359542024fe7359542024fc735954220cff7259542006ef7259542004ff7159542014fe7159542014fc7159542004ff705954200cfe705954200cfc70595421967f505954201dbc7655142036bc765514201cbc765514202dbf755514202f3f75551420073f6555142036be6555142036bc65551421973c65551425d73e53551421973c5355142007af725514201dbe725514201dbc725514220fac725514202ebf625514202faf625514220f3f525514220f3d52551421973f515514220faf2155142005bf705
  | 18 => 0xc74d8153034fd73d81533fedf53d815337e7e53d815337e7c53d815337edc53d815301cfe72d8153004fd72d815301cfc72d815337edf32d8153014fe71d8153004fd71d8153014fc71d81533fe7f51d81531defa50d81531defa30d81531def86058153034fe76d95431d67e65d9543025de73d954302ddd73d95431d75f53d9543214fd75d9543024ff74d9543024fd74d95436367f54d95436367d54d954302cff73d954302cfd73d9543636dd73d954302cdd73d95436267f53d95431d6df53d95436267d53d9543626dc53d954301cfe72d9543004fd72d954301cfc72d95430067e52d95431d67c52d9543626df32d9543014fe71d9543004fd71d9543014fc71d954300cfe70d9543004fd70d954300cfc70d95431d67f50d9543034ff76595431d67c655954361dbf745954362ddf73595432175c5359543624ff75595430067f755954361cff7459543006bf7459543214ff7359543006df73595431d6df53595432167e53595432167c5359543216dc5359543004ff725954301cfe725954301cfc7259543216df3259543004ff7159543014fe7159543014fc71595431d67f5159543004ff705954300cfe705954300cfc7059543025bc7655143036bc7655143024bc765514302dbf755514302f3f75551430073f6555143036be6555143036bc65551431d73c65551430079f7355143025be7355143025bc73551432179c735514302ebf635514302f9f63551431d79f53551432173e53551432173c53551432179c53551432171c53551431d73f52551432179f3255143005bf71551431d73f51551432179f31551431d73f50551432179f305514301cfe76d89431ceee62d8943034fe75d8943004fd75d8943034fc75d8943024fd74d89435c6be54d8943006bd54d894302cfd73d89431ceee42d89431ceee32d8943014fe71d8943004fd71d8943014fc71d894300cfe70d8943004fd70d894300cfc70d8943586df30d89430057f75589431d57c75589431ceec6258943014fe76d85431c6f661d8543034fe75d8543004fd75d8543034fc75d8543024fd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d85431c6f641d85431c6f631d85431c6f621d854300cfe70d8543004fd70d854300cfc70d85434b6df30d8543006f610d85431c6f410d85431c6f4615854300cfe76d81431befa60d8143034fe75d8143004fd75d8143034fc75d8143024fd74d814302cfd73d8143006df53d814335edc53d814301cfe72d8143004fd72d814301cfc72d814335edf32d8143014fe71d8143004fd71d8143014fc71d81433aebf41d814335edf31d81431befa40d81431befa30d8143005f771581431c5f471581431bef8605814302cfe76d91521b6be64d915201cfd75d91521b6be54d9152616bd54d9152024fe73d9152
  | 19 => 0x1c00a005000800000400000000040020000000000002003000005000400000600240000010018000046002001000800000d0038000006000000000400200d0028018000005001000000400100400140100020010008004001001800c002001024fe76d8d540357e75d8d5402d7d75d8d54216de63d8d542175e53d8d5402cfd75d8d542167d75d8d5402c7d75d8d54034fd74d8d542167e53d8d54216de53d8d542167c53d8d54216de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54014fe71d8d54004fd71d8d54014fc71d8d5463e7f51d8d54006de31d8d54216dc31d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54216df30d8d54216dc6358d542175c5358d5401cfe76d895420eee62d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d895420eee52d895420eee42d8954014fe71d8954004fd71d8954014fc71d895420eef21d895400cfe70d8954004fd70d895400cfc70d895460e7f50d8954006ee20d895420eec20d895420eec6258954014fe76d8554206f661d855402cfd75d8554034fd74d8554024fe73d8554004fd73d8554024fc73d855451ebf43d855401cfe72d8554004fd72d855401cfc72d8554206f651d8554206f641d855400cfe70d8554004fd70d855400cfc70d855455e7f50d8554005df7358554215dc7358554206f4615855400cfe76d81541fefa60d815402cfd75d8154034fd74d8154024fe73d8154004fd73d8154024fc73d81540067e53d815440e7c53d815401cfe72d8154004fd72d815401cfc72d815440e7f52d81543cebf42d8154014fe71d8154004fd71d8154014fc71d815440e7f51d81541fefa50d81541fefa40d8154005ef725815420dec72581541fef8605815402cfe76d91531f6be64d9153024fd75d91531f6be54d9153646bd54d9153034fd73d9153646df53d915361e7e53d915361e7c53d915361edc53d915361ebf43d915301cfe72d9153004fd72d915301cfc72d915361edf32d9153014fe71d9153004fd71d9153014fc71d91536467f51d915300cfe70d9153004fd70d915300cfc70d91531f6bc645915363ddf735915301cfe76d89531eeee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d89531eeee52d89531eeee32d8953014fe71d8953004fd71d8953014fc71d89531eeef21d895300cfe70d8953004fd70d895300cfc70d89531eeec6258953014fe76d85531e6f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d855301cfe72d8553004fd72d855301cfc72d85531e6f651d85531e6f631d85531e6f621d855300cfe70d8553004fd70d855300cfc70d85531e6f4615855300cfe76d81531defa60d8153024fd75d815302cfe74d8153004fd74d815302cf
  | 20 => 0xc00600001380000020080008014000003001000000a000000800800c00e0050000004003000000c00600000000000040060020000000000003000000600c002000001c002000801800400100080000040000008000004000000800400000200100000060000020000002001000800c0140100000000010000006800400000100180140020000020010004001000000400800000000040020010000010002000001000000200100000000000010080010000001000800c0040030008000002000004802800c001000800c000000000003c00c00100000040060000000014004001000800000c000001000000000100000100000020010030000004001000000e00800000000060000008004000004000000000a000000801800000c003801800000800000000020000000000000001001800c00600200680040140000008004000001007000c0000010000004000000000000c000000001802000200100500000000010000004000000000000000400400f00080040010000000006005002000c004001001800c01400600000040000000070010002000001804000800600200280080090028000004000000801000a000004002c0000000000000002003000000401e0020000000004002000000000000000000000020010048020002002000000c008000003800800e000000800400000100000000060000000014000002000000000a005001000800000100080380040010048000008001000800400000a000000400200100480000040000080048008000000000c006000000000400600700080040040040000000010001000800001400100c00140100000010008006002002002c0060000020014000001004000000801c00080000120000040008000000000800400800500100000000000020010002002000000000000600580000000000008000000003000801401c000000801001a005002002800a0050010000002004000002c004003001001c00200000100040020010020000000000000801c0040040000000002000001800400000000080140060060008000002004000800000400000000000000010008000004000002800c0060000000004002004001800000400000100040000020008000006000000000001400700080000000010008004000004000000400000100000000040000018024004000000000402a00100100000020030078000020000001000400200000080000000020000018000002000000800600200000000020000010008004000000000800000400100040000000000000000000002800400e00800180000020000000004006000000000400400000000140060000058008006001000001800e01200100080000010000004000005000000c004004003000400000100000000000020028000006004000000800000
  | 21 => 0xcc79d16a16846f600000024c00000000000b5c0000ce1468000e608905210001104c3100027e40000000000cb00003d60bd8000000388641800000000000005702580004e000000000000000000000000202000056ed3153d0fcc00000000000011cc000000325c05c6d421d8d9c00000049c28b8000b530000e400000000e400000000002e8b4a195e00000000003ea2724041514494a3204e000159e00000002140007220000000000000296000096c7516288784000b6e0a733453600000002c8468c0006888160eb855e0a4b2ad0b43eb2de000188088600010f40000991698ed4e4e00004d8000ea60000002ccc000245345190c000a890e0b2840c214f00003fc00071842b28440005670dfacd428200033b8000000000000013c00012a0000000000000000000000069300034acb8c000000002e009000001000e000000000000200400280080040000000000000015000000000401400000000000010018004004005000000c00c001001000c0020000018004000000005801800400100000000040000070000000000000001000a0030000004036000000000000000000000000020000020008000000000801c02c001003000c00e006000800c000000003000c00c0080010000000002001000800200b000000000200000180200020030000008000001001000c00e0040000008000009000000000400000180100020020000014000009003801c01a001000001c008001000800400000b0020020002000000800800000b0000004004000000001000c005001800000400200180180000080058000000001000002000a003003000000000b000001800a00600000040160010018000000001000000c00200200000000000000088000028000000000c000000000002c00800200000200040030060008000000000800c0000000020008002001000000000000100200080060000000000000005000000800400c0038000002000000000400000300000180020000008008016000001800000000000000140100040008004000000000002000c00500000040020050008040002001000803800800900000080000000000000006008000801000000000100000040040000004004000000002000000100180080000000000000008004001800000200e00300040000020058000008000000000800000500400000020000028004004000000800400200400100000000010000000014001000000000c012002000000000b000800000200100000140000050000014002000000000000000b000000000e002000000c018000000000c00400300100040040020030008000001000000000000000000000020000018000000003000000400e00000000100000060010004010000000800000c00000200000000010000000002002000800c00200300000
  | 22 => 0x137000101800000000005ec5c41718bb56c462703e8b1800026a000167c1ce8f858900017e426b2d8b16944a00000000012dc000000085c21200000013243e841664e89cc00061161400007aea59000000169200015f88b00002b224c8ed1174bcc6818000000a1e5b501213300000000000c946ca0f530746567f72211b6cb2cb5100008a0f00571172b1e000056500000000000002d3a6640008f500028ecfc400054700000002d000012c8000afa00000013fa000000104c00000045f203ce1800000030200000000618b040009aa57280005600000cc08f80006c9000000141a3876649494a26431000000000000000000000001754b2150d34c6420000000000000000000000000000003a80000000000de18460000ce800000000000007880000002178001a4800000000003a48cb499971c4a06a736c18a850e6016a200000000003cd0000000959000182024e9e40c500002847912168b713ae000000043c8020000000df4d6600062280000006e350e976c8e4c2c2df000000000000018b83f40000000000000cac0000000f8802f0000000000c9b10080000000000001ca485424127780004e0b6400008fcd063b30000000000000000000082440700006881c40c40002994000c5837e8dfc13c1be000000000034500000004da0000c71b48c6800000000013b015f0612d7c76400057500019ba2053a6066824683e07b008531a00000000000001b320ba550000000000287d4ae0051620000e9ecdf0001fa411600069f02811ca0000002bd026071f5c42fc4d022a72488b7c0005012408b6072200064aae4800000000031c000000023c80000000000000000000cc20000001398c0b0000f380008df49100008fe6aa25402114460965349de15528c73a00250986000000127000000000000000000361d6805c00024600000016187b050d15d83c0737000000000000066900000009e3471000132e0000001964000ae72e833a8134b3a17d88492e24274c220500002814a480000000002d2165035caca3c40000c200002beb11d06e48e60380000008dc0000001572c350001888852000000000000003e00000458b65d9000000000023800029e1828067152153c0ee00000000000000003f420cc000000000008000000067600005469194a889a51947546870000000c7e0cb80000009a459b80006ba7165beadb00000000000000000396000000000000000002a80007cc00000000008240001704b449e21f1079c0000005fc8000e5000000000016c68d740f18980002f412b242009492b3be30e52ecaeb00026883006350e5b3ac682d1600033680005565641c480000000000000000000000000000067b0b929fc00000053100000000000000fe4a2244d00000000004bc0000000c2a000000121800000055914688
  | 23 => 0x7fb00012918440000000bf0000af249f00000b60005af146000000010c05806de9b50002aa8a50b4a0f8000000000000000000000001d800000000000000000000b1f00000000004e35d384f400000000000018a800000000018bc0002789ce4000a1858eb24823000000000008721d000003a50a400021721c4000000410a67d4860000000000a24000000000086a344646ab856087072b9ab04a129e86a11f14cb056c26918ccfc60000002e1c4ea00000000000000002e91f515e64e26910000bc04db000000166c9f70000000000000000000000000032d05e800000000000000008221790f50b9c00000000015f6000000000000000000000003e200010400001a215a000000000000000011cc5e000029080006100000001d5800013917fa3bc3ac8ed0000000a5664d15c92cd2ea8a2000007c000a8c0002f8d96214c32f052c8da0005060000384000429ab993e6aec0000000dc40000319a2559c000241291c00000055580000007680002fa5218a9d694800161a89c0368001426904000038449804300621ec1005ef0001338ae877b2f105e436019e36b32d93f883c00000007f85c50001ad800000000033c51c800000000019e800000015057ec0000003260f5a80d000000000053a00032a8f5202c0920000000ca845a00000000000000ca80e00000000e29388d144e100017ae00000023ac00022e0002484fce0005518c1980200000000000003930001bac8e847b3f29a98de6a5e34780000003a6000000000090738080000008ce519800000000000000001a4ad20450b089dc05d3ec8f10f0cc115ae85f43c878a3a0838c00049228c8000cd4000000000000000000000719045532f300000000680002bb4000d19673156c000000547a8991ec71c02f04f8b92b0000c1564000a4400033dc0000003a6890c000bbd000000122e0000000000000000000151c0000004e400019089825b999e851c0001638ce0000987097000000000000012f8000c1f11207c80008b60002ed800001d1af0a3d228a3500000e82680002da00015363e95f41bf935ac3750c80005b400019fb1496acab142a83b09f26b109a87ad1b68236638459652c68492800189aa0e3d529d13700f82720b8000000010b000000040b0000000a806071c0a17000084f5978c34000bbe000133da200000000000ac04c252a057921683200023a00004fd0000380de213a1a802ec97e0235139268000ba200002c80004610002244000000000000000059700000000000001deabf000054200000000000000002a292126dc0000000000cd805f800178a92e54caf7c0000000778000000254000000000039e00020ac0000005d800007562e212d000133676c0000000b3c0000001fe9a5c00010d80000000002f38a2c00000000017a000000029c82b400090a0
  | 24 => 0xe2a90500011d400000052405b1098000503afec47ac4c4e32e7894295d0003184000000149206400047053418f58e600041e80017dc000510131800068b421b3a0c7e00000000013a2000000299d290ce9000000000000000000000000002d31800adc0002f28b0c35e00001380c11060005ce17916760005ab8000df8000299a4340008a808a9b00294a7526883f14e23a5000259493aac30112a5c00017300000003c60002c60f986e000000000000007975a6800048ec040001f84fb40000000000000bfa34d00000000000000000000a401908000000ce1000000008e000000000000061c0002c8c0000000002e380007a33af21140006f433c8000e3c000000000159200000000017520001e906800003390ff0f3c60e0006070724cec000000000069c00000024a517800000015a0000d3308684991c600035f800000006f0fc00000007ba00009440000000000000000d3c5cda650deac2400002f40006ff0000000b721e635684b46201834a1ac5cfa698b45292ed0747b35bb0aa974c62c0001b413c075a00021986d26662bd0c6d3400002aa80019f8000000106c0000000a2859cdda4d6000000000091e1bd00008b80002b1928c0001c527f219ca0e0000000000bc20003eb80000000005ad9eb94b400029483eca4600000000008449fb3791c90000c5c6051549866a3d00006f180c85419300000003945b3ac6cdca64f4f7a0fc81cca053e14b40006503f3323c39860957880007e2b0b00000000000004c0ad304120a73cc986c532000000000093ece034930008807f842e9ef000000007a8000fd60002878000000000632000178e8ac0002c1d3c25ea0630f18f7281804e892cee23bf48d93e000000000000000004a519a00000000000000000000bec2cda18d02258a5a794d01742bd63ba1084f400000000000000000003390afe0004bea38568aa7d5dc1b78ce8c9000000015de0005fe000179c0882d18000000000000000000000065221fc0008f100007fc00074600000000006240000000fe60002db8001a4ab2a59c15e40005640001f48000a53000000000081700000000000000000000aeeb770002fa84a4000000000000000000000006c60003da0a0c0007f602885e000079c018b03c0001b22dfa1cc55855a54a8000a6c0000fc8a944cac601b000000007902668c88f4e0d400034680005ff4bf21895ec2155e782b0c88ca300000007c20006338048000bf500000000000004458000fc054458b00000001ec46a80000002800d60000000b27000000158e0003b680019dc00061f8000b8428852e31880003b90ed800007a1884802c1484200000005f967238e00700013580000001a000006320c885601923ff50300004ec0001e400000000340aa0001988498000335039a000000349c
  | 25 => 0x40009dd00022ac0000000f780012bc00029da3fc000d063119e908582bc0ac91d800000000100000000002f8b0d95c87005e10a68d708bd14f9f2800000058a94b800018b12423dc000bcb0000000b540003dbb3015fcd051542cf483a70466800000000005aa000000000059a30b9a460002fa80015a80004afa958b6c0001ac00000006bd4ed1e38e6c937329024cbbc16d3a39e997169700002a812a01473fa9be40000000001d8000000065e000039cb9801ab108000000000000101c59d0d500000000000002b709bcb283c780000000000000000000a4d4518000000000000000000000028a00013d8000000000042600000000009960000470001a404d054b0e498f29db5d7975407e94f101a9c89be4b722d8c9498acb9495121c89c45746984d82cc00000000000007ee000000000018f58a1c740000002660c440000000002da4cc600000000010be000000000043476b25328147062ab00000000000004e700000000005248000000d260002448000b7a17480000000000000000000c7b000000192c000548b47137e3ee1b9800000000000000000000000001a1400000000000019f2bc63caa5c8f0245a0000cd8f420003868000338aff13383f823e00000000000000000001fa8000000662800139eca261509350d66ee645a35828007c46421a4b5826800002880000001ac8284d5e06551b1fc4000aaf0000000abe00000014f0000000000000000000056b000000000013e0655820b8a0d180011c000000002d193c0000002a4c00000000000000004ca291136087400034801b803200068fb330000000000000120261e63a0ccc00009800028e122a000656b06800065f54a0001a70a080b530a53a40001ed9af002a0000000000000000000000092c0002340000000000643b07991800000028e42101a9462a2c4b1e2ee000000000000064492280009f1397114000000000000018b200000000015dc000255800111800005713d00000001ee00002e80000000d0c0001b600000000005e3040a6d15381f70002588000af500007f400000010e8e1400035b30f96380003c100023448ca00038518596da000000000000000000022380000005f828dd3a82b40000d5c6da82921422e19f0c855022e8c0b811b18201c849ebe1024b22818043400000000003e729780012e827e2fb0000a989fa6028395876a0905b3388fe85081848b9013ebe667f1a8138ab5819f10500284ec5ea00013140000058000a7c0000002a2c00063c0000fe155064100000000009e900785dc000a505960d5400000039d00013644204502dac5e62c9000000000000049e0219732b7f5d895b565a0004ec853400040800021c80006d300028f097249000026cc4f0bac00000000006a90000068590a521900000000c6f00015707be0006808f24ff2000
  | 26 => 0x364212c200289000000059c00037b291800080305c8000944000000314162253f0002e452060002fd89755f23681a9afdc0ac1d100000011766542c1a55c09651700000016aa32f56aa1dcbfc00000022980005914c8000036a00000000001e03be000000000000000032c8460662000000000000000001800000004b5976000000019719a0a1a0000000000b3400000006f400049e44f2364a600000002ecc0002ba35d2c0400000000016d46be717000000cdd27963b287554c00003ef0bc400000053baedd03470900000003b00000001a7ce0400064d000000000000004fc00073d0002ffc250c7d50780015ee00001200000005a53cd98dc0007db14808100001b10000000000000000000000000000000014d600000011e00000000000000000d0400000002280004a580000000003d000019006dd06f098551a000000000088e8b0000000059603800001ecdee00063b0ea061e00000000000000003143158ecc7190000040ab090f4e3914c2e20000000658e340000000d840008060000000a16d3d55717c800000000010617ca00000000000000000002e0cfd808c14315d43bcc4f3780ad943869e31c16ad53e7b21ee96204de1940000000b0007906d1b3530c00048e92e00009e551f04ccfba03318a8001a6c0000001f409b820a0149728540a31684147400000012c8c38b9a48f16e8000892000000207129820200003a170a33000001080009ed1510a4c17c00025e8000000bfd55d8000d3000039080010d843c5ce80008462140531a347e4c32657092563449500000002ba000115a9900000000000000000c48343a86c000b3248308dc000000000082d60450a58480000000001f18000000a2800023e97a60000001dfcd7276a00000012b8bb961c2a996a0cb318a263d97c60e27fb14d50640900006a0898b9006aaad119ec093dd9af8b0e4ac08287a091a2f83b999140006a43621541054000091000000028438880000003c365a000000000000000000000005000000000595099000000020e00000000005860f48000000d1b0000000000376536000136e00000000005eac4e0002eeceb6cbb0000f0000032313180000000624c700006980000001dd80000000000000000d1e0001dc80009280002a048ee3740b2836c1cc0000001ee00001025278f443ec74b06c80000000000000000f8caad43b00000d800032e000000000000019e0000000000000000067d0000c680000004248d5863c0000000c00908a7b2dd1f048faae32d900018d21116158f4c34c0444cf000080ccc63570000000000000000000000000006400001623eb17215fabbf30794800000000a400000000005f200008148f04b000008c60003370fec00060a333800045a0000720000f9c3fa0001545222a4b00008f00000000000000e8800652d97b
  | 27 => 0x263081e0000002f595d0000000333957400015480019fed300000f6400000034ca5e0000000282000055eca54231848000000493274c00000030300000000000002b6d9ec4620000000a000000000000e1000047e80008d804135433ec9ca0524250000dae000000000059444f22aa4d17783bb00000000006d9000000044e0000c69efc2182790ab264502000056d0a44b047ac22b339c00000000000000008f200000000000004bfa8ad4f20000001db846a66b0682e850c000017e80005aa000000199557c6cc000047400097a00000000ae9ab23d000000000000003f4000c410001b3d10838c0001f002d6723000031c00007312f9e2c9e425c68122a4696b8c5148000000a700002b8835600044c8000bbe48949923cc000000635a7d8ffa2eb66a80018d43aa0002df963c80b00000019b64051d12c1984a8754ef90fcdc00000002fb4e9c0000000000000d3b00000000000000000b9c000000000000000091007b82c0f9aacd2782e7da26b7b3952220cc80003be80000000000000000000b130000000d0400053783c80005d73c98000c30bd20000000f6a1043b832c00000002d980000007c908e00000009443db0000f300000000001648d2d2b903286f8bdc1571de409c00049eacc44b69ee000002019e53500000002023ba53b0d9892800006280000005374001b540000004d2b4b00000001118000000abc18e0000000000400800000039831f225d5f088700019c416699a2f4a6481ba0006388000000000000000128298540280000001cf0001b080001b747495740000004098000000ab800000000003c50001d84e0a00000014151480000000000000403270000000022519a8a84000a9e02c91f838800000000001820001bc80000000004d38004bf20000000d90678a122c09ba9794000306111000092c47d800000037700000000001ca41a00000000005ecb4e91800000002080980129000000147ea14339000000000041d8e8c0f05bd2fe9cfda7200000000019ac00005185854aa61349f8ff8000000111305522664e6609c3d1e800021b24d98ca00020f1c0da6e00000010680000005209fbd1bab95026a9b40006843a2800000084e3e38f9012499615687ec000640000000063a000000000070c00000000000000000002a9c00048503d0000000c9c0002ed40007490ef8000fc888a5870000000000281911405a00000000019da4711c2000000000031029a800000000000000000000000c080002740000000fa2d2a3688d50be0000298ab7400037100000002200000000000000977000172c00000000000000000000000df800000000000017c400018500018047921920cb4c92b71000000000088d0000000c6c76930b932079400000004940007df15aae683da1e50002c400000000001c6c00000
  | 28 => 0x1d1d4aa94bb8000000264c0001a500001a400000006b800000000028729300000000000000000000000000000000000007b80000001690000000000000000000000000000000007a200013b4ca213100000000000000001a200000000000000000097000095583200015880010140004372eb4000000000033000000066ba7c8000000000000000095533f8b300002e86068000000ad70002d6800050c667a1d03e643e4b4000000000046f023c0000005f5a3b8a92000000000000024e00000002ae00000000000006c500000000009e727a8bf8ad445d0000000c98000000000000000044aa2d40000000000a58fdab4700023e400000000000000000000000c14c5e5a941280299260000000000112000686b239050be021995e00000000dd21f40008d82eb34249186751e12ea94209a94e58000000b2b0000001a8657c62b851800000000000010fca9a65380006dc00044a00007bc07f14e0000820ac0501000068e000000000000000060daa8884800000006040000004e497740000000000000000b784a010000004ae0000000b0a0000000000b60a21103069d6b20000000000d442de0b7155cfb806a07a2f6d21c00000002e00000000000000f1260350580004520001410000000000119000023281d13da7fc0004e76668000ece0002e0219000019f07d0000000a9017c8000f8631f0000000738000346198000065300d8000000000000000000083600000010b000000000015b200015980005d43b130d2da11364c1000071c0000001d602d52d20004e69d8c2a0467000270c8825480282b816447142182804570720393000000000021281d115e00000000000003cb4608000000000000000052a0002e1ae34d689662b312a97a229d4b9884518846401d8cc99e0c270cd874c74e3a068386308a810b14b8000d8264736d00012b089f00b0e555665fc43d00013829834209b84ba815357815bc04a1d71ed00008be46a5a1966030cca600480006847d800000018f8d18076800043e000000000000000000032e80002d91a4800000000027e0000d9600000000010723bc000268c440000057a1a82fe00000000000000f341a80000000bc00024d40005bb5da16bc8f848831d800000000004aad10d6a00064300000000002939de9a1800000021c05c20000002799272000000223d6cc30300010dd9eac205ca02c472e1823f92cfc0000005168000e7c91a000187400059000005bc6020000000001a5e000000310cad60003cf80007b07106108418a54cbf24ba0b07008512b831e800000027b27f8bf0759000000079ac3c000304c0000001f299f800023300013a47e80000000000000c9f00012a400000002a800059e0000002f600009ba5ff000082ad171ad0000000000540000000078c3bf13dc69a12108b800000000000000
  | 29 => 0x654cba6555e1b0f898e0cd2fba5f0000037000000000032800020985ee000000000000096f0000001678ad10541b0cb24000318a2b592800020cb2f453c593000000124e36b0000130f1a1ad00012d4000a883ba2ab1638b40000000000091600680000000001a7821cb5c0000000000000000000000000000000000014c68150002b419fa0000359e943808980001d7c0000000001ef423c23400020e038c000000099161e07e0b48f418c63120c9000133a0003a42e18000000000000102c602356000030800059294792b469521c0208bb4000194ad0800000000002914606391c5b1b510000000000000007c800005542a43ae22580012da0000b4000000005a1d780001f200026a93a1024b3000009dc0000dc00000000000000000ce800000068a800000000048e0d20a9c0005d40000b9849300026b8a3669c0b81cc8d2c4b40000edc00000009788a80009f500001d528ab181b519f07ea733234aaf535ecc33c38000000c1769f800000013b00014f4f2846f000000165c9b934da2490de6e867d0cdd16e000000000000000064414987ee000000000000000000000001dc0000001a84dbe0005c9800000000000000000000000000001704d3245caf78000aa400000000001441b613ec8042e618c00012760005661d90580ac40c9920c0000004661885062b460001148000000000000148a000625800000000000026d800000055f80002349476719ff80009bd1dc0000b3800000004f04320000001ff13e0b20000007800075200008401a60000dc81186ca39a000017c00000000031b1606ca969080000000001ba80000000000002194000000000000000000032b848101200000000011b40005e0000118c00050a800158a72c2218000000000000000000095666530d00002390000c9d61400060e217867a00012b8000e0c0003abb19800023a4ce16a00001bb65a8a6c936151306800000045800000012a415b67791293e895b0002e3c0009b12c692819ca5ec593000000000066c80000002984bd800125a40c00000007484590002140000b6f048134d2040004ea858cdc813839286648a22004e81cc4a040005052c2071200061311ac000c3022f30bc000a4e000000172c00052880016ea0005dd00000003ed0000000e76506000000170867300000000000004341a1800000000026f9154adf000000000000000003600008895c013991924b00000a14d8c74a40f8000a7063a4bc8e75102c4a0000000f04802000000000000000014700000000001ffd06013718b80000000000000e6d3760000003204c56000000000000027d00020bc0004dd000000000000047e2f7440ec0c69a0001748000000218400000000000000000001668e84000ac613312bc3b45544752a10054acb423b3700a6694000000000072d5a70000000d
  | 30 => 0x777000300d79a0001f40000000d4007580000000660001c4c00006400000000006fa3e780000000000002528a940002c232dc6260d64682ad99e4bf35e2087974a00000000012ce0000001a8c00000061d0000cb600000012b515c0000098764dd800000013a80000003e580007d8bae00029600000005e4000000000001e1eacc964320001dd5458b6539c000007200000000000000004c000019225ad0000ff4000362000000128c2362158000e680000001bbd13a6e642c800000000054c0f3000026c00000000003994988000000000000000076c0000000000f080000002e804884f314500014cc000000000000084400000001068bf63f870c000a24198922cac2352000000094e630312951800017c000210058a84d387098046200000000000000000000001a00000000037c5acbc95178c651a882d208afe00002bb624a68400000043cb0f54743726a08000900b7000000017827c21f7a6244380001461bec000000574b4d4b9ea033df0000000aa1000135cbe800053f00007d45f30000001134783000000129a5245b0a1e014a00000009c58be000000000000000000006d000000000027700006bb2c58624000000000000000000000020b811a00000019a57ce893330a1211641b829900000005d300018152840c853733cd246b5c00000008c0bab42da5847c00001f8000000066c000000000092f6231e140000005cbb378000c160002f40d6ed0b1532984d60a9260c343d2d834032b09fd4ba92000000000000000000000704143000000000069739e16e0bd68d200000006b825817d326483e66d000258c0000000002adc0000000000000f50000000069000000026c8000e5e00000000018e46ab2fd0000000c1220680000000000001f5478e1645a92779696743237209cdf010e66995880000003d88000000a160002a140006b200018100000001858000d4a8ec1c680acd22cb862e98643b82ef51503c45d8b7400000980000004fc000073e00046102a400000000030b4c9020f0001c2c00000000000017640004f50000000000000272800003200005d8000b604508c58c281125112fd103651020e02dd56a8071a8a54c4800cb12980000000002cc92c49c22be36700000002210000000000a870001098eaa0000000000ce072b25d000030a00022300016320005be0774226a176372e25702045558152c0000003a100000008964a7247d504000492000000076f26d2b4c00000066408980008b300021f0000c7500027ad3100001068000000a865a0a29c000000000000000000019d8000000b3e00000000000400000000ea0c553ac000045e9185f781d800e0282bf19191ce000000061d1fc29402a00000000005bca6f1a244fa2c4800047625e000147c0000000958000000000000001000060b56f00000000000002
  | 31 => 0x16d81c47aa76252f80016e4a340000000000ad800013ac4187af00000002145ee1c7840c000c440d08000af656928a8000c520ab0001b9c0001d400007f00000000001120e6a107048b32c000000000000000000000018b400034a00000007ec0003470988cde9d62a680014e686d1688000f3c5a049d000000030c5ea94590aeac24429d7400000000000009a8a4a68500013500002622d20fe080400000011860001212334000bda3639a752d4
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb5a85dcd504c0099b0eca1aa09804ad621543541300078caa286a826019b5883549504c0256b10a992a098003d254932541300cdac41aa2a826012b58854c5504c001ea2a298aa0980021fe1573d91200343e42ae7b2240008ef825d9544800b0f90eb2aa89001a1fa1f7558d200043fc2aeca9a400087f855d9434800d0f90abb286900023de057650d200147a40aeca1a40048be87d91434800b1b90eb1a86900ea972156350d2001476412ebb0a40048de839d951480011bb073b2a29000a1fa1f65545200062e39ecaa8a4000daa40dd121480031d90cba24290003a990764485200147643ac890a4002ae681d8d21480051d90eb1a429007a9b21563485200f73232aa290a4056bc483545214800d4f50bb1aa09001a3e21d635412000794aa284a824006c787654550480ab6b106a8aa0900027a21d215412001e743b242a824000f615148550480071f10cbaa8090016aea1b645012000dd443a84a024003da88750940480037550ca128090006ea219425012002f5443284a024001aa886509404800bd56eca12809000f6a9d9425012001ed43b284a024005ea8765094048001b56eaa1280900036a5d54250120005d5c0a84a024005ab884d854048001d5285b0a8090002ae2194150120005d4c2242a024000fa14148540480091bd0fb9aca8800237e0d75d91100246e41aebb2220008df835d954440091b906bb2a8880023be09765511001c76412ecaa2200587c8759554440854b906b2aa88801a2fa1f64551100046fc1aeca9a20008f7815d9434400b1b90eb1a868800a3d20573d891002c5f43ee8b1220018fa87dc16244001970e9b82c4880022fe11765491002c5e422eca9220008df835d952440091b906bb2a4880022fe1176509100047dc02eca1220058ec87589424400d0fd0b3b264880021f616764c9100043fc2aec992200687c855d9324400117f08bb264880162f211764c91001c6f43ec69922000c5c75d8d324400b1e90eb12828800eb9a0b654851001c7a43aca90a201cad4835952144001b6481ba242880063d219744851000753216c890a20038f48759121440896c90a9924288073b118d324851002d5d436c8a022005ab884d89404400b1f10eb128088016ae21162501100055c43284a022000ea96250940440037610ea0a808800b6c21d415011000dd943282a022001bb086505404400bd610ca0a8088006ac219415011002f59bb282a022002db2765054044005b60eca0a8088017ac1d94150110006d9b9a82a022000bb3825054044001d66c4a0a8088003ac5894150110005d8c2242a022000fa14248540440095b507b2a60880123e21d654c1100147c432e89822004cd8764c930440876b10a99260880036c5d1414c110007c8a1a8298220009f08748530440059e0ec90a6088003f04c9214c110
  | 1 => 0x90ca1a8290a0ed921532505210e6e239a64a0a4200f85434c94148401bc641b82829080237e0d75d81210246e41aebb02420087f855cf604840d0f90ab9ec090803aa50b40d812100758a0e81b02420587c855cf6454001ad441b92a8a80061fa1b7550d500349e43aa8a1aa042e1c63551435400b1bd0fb1a86a80029b61742d895000716aa685b12a0008df835c762540091b906b8ec4a80061f21975509500343e428ec992a000c5e531d932540030fd0dbaa64a801a5b21d524c9500143e42ae5b0aa000c5c73d9151540332bd0fb9aa2a8263171db73545505462e3b0e6a8aa019c5c73d8d5154001cac63b1aa2a8003561cf705455000c3e432eaa0aa01995c835d5415400d1f50db8282a80061fa1b754c550034ba43aa298aa00187c865d521540332b906baa42a800a3ba1f6248550665aa41aa290aa028e64625452154001b3080b9ecaa001237e1d73d9540006d4206e4b2a8000a5e83dd5655019787eebba2caa02d31b1ca535954001c7743ee4b2a8000d38405d7635000d0ff0ebaec6a00036c1037158d400043ec2ceca9a80008f7815cf62500051e902b9ec4a001237a0e76549400046ec1ceca92800387c8759552500071790eb2a84a00066e203715094000cdd43ee0a12800687e859d932500010fb0b3b264a00034e103754c9400247743ec49928000c6c75d8932500011df04baec2a000e3b20975d85400246f41ceca8a80008dd839d951500050f90eb2aa2a0003171cd655454014536412caa8a8000d9840dcd515000d1ed0fb0aa2a0003351cf615454000cdc406e4a0a80019ba87dc1415000d0fd0b3b262a00021f616764c5400065c206ec90a800687e851d921500010fb0a3b242a001237a0c76485400046ec18ec90a8000cb8401d921500031790cba242a00066e20174485400246e41aebb226000a5e85dcd644c0011bd0fa9ac898263351c753591300147b43ee2b2260008ef825d9544c0071d904bb2a8980023de0576551300147a40aecaa2600587e87d95544c0031bd0db9aa8980126721d5450d301d70e32aa8a1a6000dd210dc5434c0071b906b8ec49800637a1b73549300247d436e0a1260b295e87dd5324c1698b8edbaa64982cf171d8754c9300962e3aeca9926000e4e52d95324c0071b90eb2a649800637219744c930094ae42ae89926000c5c75d91324c0071b90eb226498003171d5644c9301656a40ac899260049cc87549324c001ab0ebb8264980021fe1572d85300343e42ae5b0a6000e9543d07614c0091b9063b2a29800317d4c76545300143e43acaa8a60018de86dcd514c0051790eb22829800637219744c5300146e43ac898a60049d487545314c0031b90cb9a429804a572157348530655a642a6490a602cec4614c9214c0071ed0fb0a429801b1e1d954541300cdac41aa8a8260c9
  | 2 => 0x15418d516bf26294c431aa2cead5819886354401c98c5290c6a8b5a976166018d514c62e3b6c6a9aa200c5f531d943544050f90cbaa86a890b8718d5450d5102c6f43ec6a1aa298c5d75d8f6254401c9ca5b1ec4a8acb179d463d89515462eba8c7b12a2a8cd47118f62544011bd0fb1ac4a880237a1c63589516ae2fba8c6b12a2048de83dd942544011bb07bb284a880a1fa1b75509510062e31eeaa12a20693c875514254575c38c6aa284a88031b948764c9510066b188ec992a20287e86dd5325456f8b8c7baa64a880e37a1f634c9515562e3aec6992a20695c8754d32544094b90ca9a64a8803171d9534c95137e2e3a8c7b02a20187c855cf60545311b90db9ac0a880237a1f63581510046f438c6b02a2d4c3f75dd165504091bd0fb9acaa0812a7a0f6550d410245e43acaa1a820687e859d932504010fb0b3b264a080e37a1f634c9410062e3aec69928204a9c8650d325053da38eaa1a64a080237e0d75d81410246e41aebb0282988df835d7644c4011bf06bb2a8988161fa1f65551311d70e32aa8a1a6206c7476551514c4539a8edb9aa298813351d943545310078aaa286a8a6206a7685d89514c5311bf06baec0988063720d75d813100536c14a7b2a42048de87dcd65484018beea39aca9080237e0d75d91210246e41aebb22420087f855cf644840d0f90ab9ec8908063ea1f70591210065dba0e0b2242008df835d954484091b906bb2a8908023ee01765512100c7c402ecaa2420587c8759554484854b906b2aa89080a3ba1b72551210343f43eeab1a4200c5c75dcd63484010ff0abb2a69080237e0d7654d2101477436e4a9a42038f686dc553484010ff0abb2869081a1f2157650d210047dc02eca1a42018f8805d9434840b1b90eb1a86908ea972156350d2101c7b436e2a1a42039ac8755142484015590caa2849080a79a077350921006f1886e0a1242b396e87dd5324856f8d8edbaa6490b4fd10c7754c921596363b0ea9924200d64711d532485a5e88623aa649087b1b1d7654c9210072729eca99242048ec8759532484051d90cba2649087a5b215744c921006a63aec699242039cc8754d324845978902a9a6490b47531d5434c921165e240a869924200d6475dc5324845978d07b8a6490803551cf6554521686aa39aa8a8a4228b648255151485513ad0fb9aa290aab351db735452167fa2296e6a8a42a7cd4761cd5148401b88e439aa290b3bd114873545210e66a39ec6a8a4200e5753d8d514840d1e90eb1aa29080a5d21d5354521145b2412a6a8a42cdb6685dc95148401b88e7b92a29087ad9215425452100792aa284a8a4284dc47350951484013c90e992a29087ad921532545210e6e239a64a8a4200f45534c951484073cd05baa829080e3d21975505210e4ea41aeaa0a42029b48750d414840156
  | 3 => 0x9032000060080c00004030480080e03806028120000800024020100100a01800008df835c762550091b906b8ec4aa2aa37e0d71d89535bc3fc2ae5b0aa600c6d7294b6550dbd87eebba2caa190ac7a1773551430043fc2ae5b0a860687c855cb6150d690ff0ab9ec8a910b8718d5450d5202c6f43ec6a1aa4b487f855cf60549bb87eebba2caa101b0f9d554d8d420043fc2ae7b02840687c855cf605080187ae92a6ca990029760e54d95325962f3b463b2a6400c3d741d3654c96f4bd063a6ca992d29760c74d95325a52ec1ee3b2a64b4a6e821c7654c96f4db0438eca990021fa1c41d95320043ec3883b2a64b7a5e83107654c8014bb0620eca992d29ba0841d953200536c1083b2a6400a7a80107654c8014f30020eca992de97a0c70d95325a52ec18e1b2a640087e87103654c8010fb0e206ca992de97a0c40d95320052ec1881b2a64b4a6e82103654c8014db04206ca990029da0440d95320053ac0881b2a640087e87043654c8010fb0e086ca990028fa1010d95320051ec2021b2a64b7a5e83043654c8014bb06086ca992d29ba0810d953200536c1021b2a64dca5d83990654c9a54db05308ca9936f950c661195320072a30c6232a64daa5d83980654c9658b8e632ec8990021fa1f65591320043f438cab22640687e87dd5644c8010ff0abb2a8990031794c765513202c3f43ecaaa264068bc87591544c9698b8edb2aa6990eb171977550d32006a7296eaa1a64038dc865d5434c9654bd0db2a86992d3171db6550d3259e2e3b0caa1a6400e1c65d91434c875c38caaa28699003171977050d325be363b6caa926406c6c76551524c809998eca1aa499003c35514354932024e741ee2a9264b4c5d73d97614c9658bce632ec2992cf175cc65d853259e36390cbb0a640087e87d95614c8010fd0e32ac29936717dcc65585325962e398cbb0264b487c86dd5604c8010fd0fb2ac0990021fa1c65581322162e31ee6aa2a200d5631dcd54544018b8c7b82a8a88029761743d8d514c52e432a9b1aa242c5e76553635456f8bced296c6a8aaa97a1474d8d514c52ec28e9b1aa298a5d85dcb63545315ad02396c6a8aaab560472d8d510046f43885b1aa2008dd8710b63545554bd0a216c6a88029761442d8d514c56b40885b1aa200ad58110b63544015b500216c6a8802b660042d8d515552f428e1b1aa298a5d851c363544011bd0e206c6a88023761c40d8d515552f42881b1aa200a5d85103635440159d04206c6a8802b360840d8d514c56b40881b1aa200ad58110363544011bd0e106c6a88023761c20d8d515552f42841b1aa200a5d85083635440153d08106c6a8802a761020d8d514c56b40841b1aa200ad58108363544011bb0f320c6a8b62976166418d510046fc3ac831aa2c3a5e8519063545514b90caa0c6a880387d9
  | 4 => 0x98001ae8742b845174404ba0781280005a88900e4fc9084a36a70cb382e0006280807c06c398399df2383347c8003fa000000001902b8ad80017c61c000000000003f8002a45bc000000002fc00000244279068712f658c759093ac00000000178000c70000000004e99b000000ff000000000001120000000021e0000000000029e000001f01b2000000003103400000015e0000000000033c000e7000000dc1ea3c67e400201000000be0ad378000778000007f00d98934a2203b8002200380005239623d1200000050c0010832a000e702c290344318002521d4749033ae0001681e07232ce20f70264442898f00000000000000000000c521e0287180c000760829d0404000d8000166175028430d6000928f82601a400220000000648df16802c7520922c0f45b20c1182881f179000724001692c8004128403a60000a1043ba26c8b936362000001573a2000a98980000006a960306058ca1a828a0000013e0004900019d0cc2040005f3b683c470370904d4b9177226438dd87d000264931eb2d05782d9ec31665ca20930607708c0541e2798030ed0ec7bc918b03f4684519c23c21a06f1d435e0003c9800bc000b30ec25a5f4a310a0006acc099a16e110b597000030c002000846e47e00033c71c00000216000268e50007a40000023625d090004385b80017f390001030b236e730c806d1b00000008d000130001000007940001c19c6700015601e000090002806a8001a238c000e08000004e0a889f1fe51c110590f65b02580537405452a1109c4bd108490dc0010a00038a0002d0004060006d9540001601a0fb292084cc0bd000210b09930de0ed07003152098459ed08c0000021b120734610000003585580014e618cc88a1ba88cae0271d00007d0562340000003a000000bc13326e648f121009e5a8000850620a00217518c07d0c0551fa1f8cb035282764000d40ce000a60003dc184939de1ea104d91ac1880910517e06686879800000418df0f43f60009d9a60042c4158001725e8ac98c0006340b81a00068d0a83c2c47801c1f62be7fc401ad1384a8de9a93ce4d07111e140024701d529a1c09c8001b8248db047000208709f5308305059021987c4ac107274064960913e4034550ee2280c8f412e000000fb800008070000780a0100e0102403802060000a800000140282600808008060180400018000000281600004160020000400800008080580c000520080e0080e008320a0120182a040160400c04002000000d8000003a048000000002000008000100000806000140300201814000060a01800002008020180800014020020200a000000000000000020180900000000000060082c0780000000020080580200002058300000c00028000000480a020040380a028020282e000020480002800008040000201800
  | 5 => 0x218281282960fcf21910001b00000000085cd00f00b81904d02034e888da1203a44ac8c81812c3689e0fe33e864089c027a194fc00000000112a042ec390fa2161940a4c115518e000868ac0e81c87b15005e574f98c000034c000b80006b8a517123e690d9a07264290001422b4284000d243e2a0001bf0a63c83508321802053062000074c28003b4000300950005b5040000004c51307a10e5940011529c2ec001cf0460001517323a729
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x6812093644f1200a402b143c9861010f81002c2a82e8528c005471a00a91904c01114005800004606804e70c873a00305409338b00e148140217031d95450d524c801c46528c4764c951594172607654d3254485c1476551435453172651a0c75dc532485c7946851cf7254521144c92615450951485c5d04735514254521144d1261534c951484595449754d32545210065121d534c951484595849750d325052170ec1215434c941484015899210173d954000564644405cf65500011aa9810372595400056864440dc965500015299210175d8d400054c644405d763500011b2981037158d400056864840dc5635000152992103754c9400054c64440dd5325000184c821cd65545400056264840dcd51500015919110373545400052a64840dd921500014b19110376485400042e660401d921500014a99210076485400052c644401d92150001854811d5644c9300ccc62615450d504c085c187655143541300ccd2261524c9504c033350985453154130147181d95148550481c174093545215412000caa25984485404800b2a898589425011002cac2616250540440032b0966112150110167301d93248530441bf740954c9214c110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80040396144a921d534c95148401026d490439acaa8a80008156a4811d5644c930
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
  | 67 => 0x9c956
  | 68 => 0xb0956
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
  | 85 => 0xa4994
  | 86 => 0xb0994
  | 87 => 0x138b
  | 88 => 0x124b
  | 89 => 0x1709
  | 90 => 0x15c9
  | 91 => 0x168b
  | 92 => 0x12cb
  | 93 => 0x1889
  | 94 => 0x1609
  | 95 => 0x180b
  | 96 => 0x130b
  | 97 => 0x1a09
  | 98 => 0x1649
  | 99 => 0x198b
  | 100 => 0x134b
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
  | 131 => 0xb8b16
  | 132 => 0xd0b14
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
  | 145 => 0xbcb53
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
  | 156 => 0x154d
  | 157 => 0x140d
  | 158 => 0xe8b96
  | 159 => 0x16cd
  | 160 => 0x144d
  | 161 => 0x1a8a
  | 162 => 0x194a
  | 163 => 0x19cd
  | 164 => 0x14cd
  | 165 => 0x154e
  | 166 => 0x140e
  | 167 => 0x24e
  | 168 => 0x5ca
  | 169 => 0x16ce
  | 170 => 0x144e
  | 171 => 0x184e
  | 172 => 0x148e
  | 173 => 0xd4cd2
  | 174 => 0x18cb
  | 175 => 0x178b
  | 176 => 0x188c
  | 177 => 0x160c
  | 178 => 0x44c
  | 179 => 0x5cb
  | 180 => 0x17cb
  | 181 => 0x1a4b
  | 182 => 0x1a0c
  | 183 => 0x164c
  | 184 => 0x170d
  | 185 => 0x15cd
  | 186 => 0x104d14
  | 187 => 0x1a8b
  | 188 => 0x194b
  | 189 => 0x1a0d
  | 190 => 0x164d
  | 191 => 0x170e
  | 192 => 0x15ce
  | 193 => 0x188e
  | 194 => 0x160e
  | 195 => 0x1a8c
  | 196 => 0x194c
  | 197 => 0x1a4d
  | 198 => 0x17cd
  | 199 => 0x18ce
  | 200 => 0x178e
  | 201 => 0x5c9
  | 202 => 0xb09d6
  | 203 => 0x1a9951
  | 204 => 0xb0a54
  | 205 => 0x44a
  | 206 => 0x24b16
  | 207 => 0x144b16
  | 208 => 0x104b14
  | 209 => 0xe8b16
  | 210 => 0x44b14
  | 211 => 0x164b14
  | 212 => 0x1a9952
  | 213 => 0x5d652
  | 214 => 0x5ca52
  | 215 => 0x154256
  | 216 => 0x5d052
  | 217 => 0x5d453
  | 218 => 0x5c9d3
  | 219 => 0x140454
  | 220 => 0x5ce93
  | 221 => 0x1a9953
  | 222 => 0x1a9954
  | 223 => 0xb09c95e
  | 224 => 0xb0a499c
  | 225 => 0xe8b8b1e
  | 226 => 0x104d0b1c
  | 227 => 0x5c452
  | 228 => 0x5c253
  | 229 => 0xb0454
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1431
  | 6 => 3397
  | 5 => 551
  | 4 => 44
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
  | 6 => packedAt gbK6 (177772+((h/1132+packedAt gbK6 (163056+(h % 1132)*13) 13) % 5967)*13) 13
  | 5 => packedAt gbK5 (34339+((h/183+packedAt gbK5 (32509+(h % 183)*10) 10) % 728)*11) 11
  | 4 => packedAt gbK4 (3164+((h/14+packedAt gbK4 (3080+(h % 14)*6) 6) % 53)*7) 7
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x71c071c0e38c78e0e0ff1f81fff0661318339f
  | 1 => 0x7e007e00fc0f8f00ff07e3ffc1f1886324ccf3
  | 2 => 0x80007fff1ff00fff0007fc01fe02107cc70f1c
  | 3 => 0xffff80001ffff0000007fffe000c1f80f80fe0
  | 4 => 0x1ffffffffff80000000fe000fff000
  | 5 => 0xffffffffe000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x30492048208410202052048868c02611081185
  | 1 => 0x42105212440089024a01214485208862044432
  | 2 => 0x800214860d100a460205481514201024450e18
  | 3 => 0x148700041bad200c0436923818441280f80bc0
  | 4 => 0x240020124a449894a00020000f4000b2a000
  | 5 => 0x693869388000001018c00040218bed5b000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffefff8fefeeca8fffefff8fefeeca8fffefff8fefeeca8fffefff8fefeeca8fffefff8fefeeca8fffefff8fefeeca8fffefff8fefeeca8fffefff8fefeeca8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_32984
namespace PEqualNP.Outside.L_meta_32984
open PEqualNP.Outside.L_meta_32984.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 60 := (concat bs4_4_0 bs4_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 40 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bgb_4_32 : Interval gbAtlas 4 32 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 44 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_544 : Interval gbAtlas 5 544 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 551 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)))))
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
theorem bgb_6_3392 : Interval gbAtlas 6 3392 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3397 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)))))) (concat (concat (concat (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528))))) (concat (concat (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)))) (concat (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 16, 20),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 32, 40),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 0 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 6 zero]
def fullWord : Sig := 0xfffffffffffffffffffffffffefeeca8fffefffefffefffefffefff8fefeeca8fffffffffffffffffffffffffefeeca8fffefffefffefffefffefff8fefeeca8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,32,160)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,32,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_32984.Model.Repr at out
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

def mono : List Gate := [⟨.or,[7,6]⟩,⟨.or,[7,5]⟩,⟨.or,[4,9]⟩,⟨.or,[6,10]⟩,⟨.or,[3,10]⟩,⟨.or,[3,2]⟩,⟨.and,[13,8]⟩,⟨.and,[0,12]⟩,⟨.and,[11,1]⟩,⟨.and,[9,4]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_32984

open PEqualNP.Outside.L_meta_32984 in
theorem PEqualNP.Outside.L_meta_32984 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
