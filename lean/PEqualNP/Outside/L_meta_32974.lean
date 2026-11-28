import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_32974.Model
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


end PEqualNP.Outside.L_meta_32974.Model

namespace PEqualNP.Outside.L_meta_32974
open PEqualNP.Outside.L_meta_32974.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_32974

namespace PEqualNP.Outside.L_meta_32974
open PEqualNP.Outside.L_meta_32974.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1042300f731de31dc31f431d431
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40001508d8006156518c72ca818e555031e329063c5520c7a4a018f454031
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xa03055454831c4551500c7415254031
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
  | 4 => packedAt s0K4 (83+((h/1+packedAt s0K4 (80+(h % 1)*3) 3) % 8)*4) 4
  | 3 => packedAt s0K3 (197+((h/2+packedAt s0K3 (189+(h % 2)*4) 4) % 12)*4) 4
  | 2 => packedAt s0K2 (116+((h/1+packedAt s0K2 (114+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfe1fc7ff07fc7f0e3c7e383ffc7e03fc30f3cf
  | 2 => 0x1fe0078ff87ff8f03f8fc0383f8fff80ccccfc
  | 3 => 0x1ffff80fff807fffc00fffc03ff003ff0f0f0f
  | 4 => 0xe000000fffff80fffff000003ffffc03f00ff0
  | 5 => 0xfffffff0000000ffffffffffc0000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x42428a01310090020c120809941228a81051c5
  | 2 => 0x4449911253284150148e42928c8499184cc45c
  | 3 => 0x88850124021920344004918029205251050e0a
  | 4 => 0x81962648a45032aea920050532496063b00ba0
  | 5 => 0x11180400c46244c93249262600018002eaa000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_32974
namespace PEqualNP.Outside.L_meta_32974
open PEqualNP.Outside.L_meta_32974.Model
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
end PEqualNP.Outside.L_meta_32974
namespace PEqualNP.Outside.L_meta_32974
open PEqualNP.Outside.L_meta_32974.Model
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
end PEqualNP.Outside.L_meta_32974
namespace PEqualNP.Outside.L_meta_32974
open PEqualNP.Outside.L_meta_32974.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5a500000280000a8a0a10d1956800031a213072424da90000023304c7010000e9f00843004e5110000a8b0000700003c4062404007912e00008008000b081184148ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa0000060700001b00234c00000058362e125215004722103c3d1904240916311a4e3944034500550f000842591e1c3b00002a002d1437212c5a4d1f4134292b0e28330d003f17534a38574b2600001300004000000050200b32003e0046305149250000000c350056011d4843050002112f180027003a4f5400020403802080810038803008418004100020018100180000101765190eeaa321dd94642baa8c853e540ca7aa819734c832bb2886575510caf4a0195e540329f28c833d50906bca620d754c41b7290836d52106f4a020de54041cf298839d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331b7294636d528c7688318cfd51319e2a263b4414c67ca990cf55321af29c435d53887688310cfd51219e2a243b4414867ca3a04f55240bba8a8174515036ea2a04f14540da28a81345150376a0a04f950409f2a4613d548c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca9104f55220afa9a415c534827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f55210da20c21b9408427ea8884f15110dca02213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1e400a0a0040b0300018480700506800380a9a0008a49aeb162070812030060f493254032c354d521071a5354041c654d501072a5254041ca54950107255210631ac580418c6b16010531c554c41886b16010621ac58041487166314540c558c51503266214540c9588515033160145408d185548c2346155220ac58041842b061502108e19540442356510410c554c41043255210410
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x81040c1885496010631c22a6b008310e05635885150308b1ac028a81885896014540
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
  | 4 => packedAt s3K4 (2667+((h/30+packedAt s3K4 (2457+(h % 30)*7) 7) % 121)*8) 8
  | 3 => packedAt s3K3 (998+((h/8+packedAt s3K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s3K2 (249+((h/1+packedAt s3K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 1 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 2 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4028004410502000420502480101429008c025
  | 1 => 0x24448c080c88910601209086c832244c221c92
  | 2 => 0xa88094912409402a8802a41252500944870518
  | 4 => 0x41529224820125515480024a4a4a009700ac0
  | 5 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefeececfafaa8a8fefeececfafaa8a8fefeececfafaa8a8fefeececfafaa8a8fefeececfafaa8a8fefeececfafaa8a8fefeececfafaa8a8fefeececfafaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_32974
namespace PEqualNP.Outside.L_meta_32974
open PEqualNP.Outside.L_meta_32974.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2d0610ca900acc123a9c02a002d7801e208804400e0002b802c005cd824c40f1a0c4c38000812151c3460a128d41f2c94a210a0002435881c08401c8b801c3ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20ee20fd20fc20ec20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1615174d254008610600189d8c60b3e990cc43281b81256051a09265079004087368d06a2206968b602310bc6c81138e83421169090c101904c8a6a0397cde73159387a3f171e478412c0e46e852a898601b25144000001800107c001d40071001101c0000000ae000c85108003800024002913ce41e0012cfe46260a070063398000000017000000b8b000051d810001c2f0942a8036120001f238f8a6613a0a4460c2c800f07700000d64d088903a003f1ec6682001e8001f05002d010b0000082f0018000717050502031b060404051c0200030b0202011e02030b0b050107074b000100b7294876d5290edca421db54843bb28887755110ef4a021de54043bd286857950d0adaa7195b54632b728465cf534cadea2995b14132b7290656e52906daa520d794c41aea98836e52106daa420de94041bca80836e52cc6daa598db94a31b6a94633f544c678a898cf950319eaa0636e520c6daa418f54c431bd2806379500c6dea790db54f21b7286436d52886dea690db54d21f3a8a436c50486dca410db94b40b6a9681ae52d035aa5a06b8cb40d699681af21d035a43a04f55240b7a92816c525035ea4a06b14940d719281ad325035e42a06b48540dda82813e54102dca5985b54b30e6996613e548c27aa9186e50230b7a92616c524c39a64986e501309f2a0613d540c2dca4185b54830bb2886175510c37281904f952209eaa441ae548835aa9105bd4e20b6a9c416d51882dca1106bd0220d6a04413e540827aa8105794c20aea98417651082eaa2106e50020d72a041ad54082dea6107394c20b6a9841cd530829aa6107994420b6a8841e551082caa2105b94020f528041af40083d480106b50020f4a0041a940082dca5885b54b10f290e213e548427aa9085bd4a10b629421b940842dea4885b14910f290a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3a000242e2961c56098046214000500152628646872020b0e5e2c9800c00f9b02a50800068aa30001709309c02206b4f111e486204a48060310408002c10441300199584504ca396015131c5551310c75131540319a181534864d6314121aa18132502a86048540aa98b50503285250130e24c9404c3195350020cc545400826561d4c2093596530830e5454c20c355153083455394420c995151083255454420d194d51083455354420aa592500822d65d0020c354f400832551d0020aa59240083495390020d8546400822f6550020c354d40083255150020d254d40083615150020aad95400832b6550020cad4d400838a5350020ca54d40083895350020c254d40083a25150020ca54540083a15150020c8545400824d6314a10ca14940842646548510ca14940443a12150110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x6001100104c5380341285c4604c940912e630242a052171d4d4008284baca6a0041c054e5150020e04a6a8a8010701535454008284b98a4a0421481d52150110
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
  | 3 => packedAt s4K3 (1996+((h/16+packedAt s4K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e0e3c7e3cff1fff1c470e3f0c7e3fff21c27f
  | 1 => 0x1ff03f8fff0fe3c7e0780fc7ff8fc707067d93
  | 2 => 0xe0003ff03ff003f8ff800ff80ff007f8c78e1c
  | 3 => 0xffffc0003ffffc00fffff0000ffff800f80fe0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8280460044482100084144094012214420c025
  | 1 => 0x44208824082204082008024224848212021492
  | 2 => 0x416d116c92a64a81f480aa90ad2194b2c70e18
  | 3 => 0x844014120040092451220000a491020480b40
  | 5 => 0x9188220802c893249a64cd24c00020c4b5e000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffecffeceea8eea8ffecffeceea8eea8ffecffeceea8eea8ffecffeceea8eea8ffecffeceea8eea8ffecffeceea8eea8ffecffeceea8eea8ffecffeceea8eea8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_32974
namespace PEqualNP.Outside.L_meta_32974
open PEqualNP.Outside.L_meta_32974.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa817c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885105f94620bea8c417e50883f481107e50220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea6905f94d20bea9a417c53483dc84907b50920f719241ed32482fea2905f14520f790a41ed21483f480907e50120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bd0820f6210417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dcc610fa18c217e50843f461087e4c210fb88421fb10842fea8885f95110beaa2217c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4885f94910bea92217c52443ec82887d50510fb18a21f531443ec42887d48510fd18221f930443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f731043e862085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5310abaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210b5a84215f94442fb28885765110afaa2217d54442baa88857e5010bf4a0215e94042bea8085f95010af2a0215fd5332bf2a665be54cca7ca9995f55332deaa6653d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cafca5197bd0a32f621465df328cbde65195f94632fb28c6576518cafaa3197d54632baa8c657e508cafaa1195fd5132bf2a2657d544caf8a8997790d32eea1a65ef424cbd884997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41ef29e835e53d06faa7a0f754f41aea9e83bf43d077a87a0df94b41bea9683be42d077885a0df94341bea86837d54906fca720df54e41bf29483ee52906dca520df54a41f6a94836d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077a86a0dfd4941be29283be425077884a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31bea9663f641cc7ea8398df94331bea86637f548c6fca918df55231be2a4637d538c7bc8718f750e31bf294637d528c7be6518f74ca31bf28c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a2637f524c6f8a498fdcc531ef18a637f504c6f8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31ef21863dd430c6fca418fb94831b7290637d520c7daa418db54831ef99063dd320c6fca218fd90431faa0863df310c7ec6218f74c431fa98863d5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510df94621fb20c43f541887ee6310fd0c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f7a1243ec42487dc6490fb4c921fb20a43f541487ee6290fd0c521fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40bea9481be429037885205f94640bea8c817e509037e81207ed0240bfa9
  | 2 => 0x8b0004b45505e000904001b900000000000000000000f60500008e932398000000cc238a8000000000000ec000000168731eb000000a61dd31a9480000014052923a692e2a580015d3a453cbc8003ec88c0012f0006a1518980009e91600000013000157106080df0122b251800000000200749f300064c838003e8969508000000008c87b5500000029f000000000004760004485f000440d281c47c468000004ec0009380b4101d47f9e94121a4c29d930c2ecbe0001ce810001fa0004206f000370000000000000000014400c0001a9151ea1340011724ca352c000000a253198a13c0006c254000000c2000000000571ce54c74c0020716c158ed85133a35c53a3911c770328f142e268001313900200011108a0cd1e14d0c23190d80032a3c1191452d67449c01941c2dd2b9e84566213999030468937a2a5265054f234144000000003a00000000029c000000002403d0ba800000000000000b8078ef99e0001c0411563960000000026c1ac000000006c4201c319a01c4b8380000012f0004441b81b17e32c1b46d27110a400002742a63553a80019246d13a0f2c89a8bb2164fc9e45f9ae45a0005c1622842ccfe1611380f125090000000001240007287e9540000014d0d051e000001ec2b65b88c00007c000000670120010a0e0036000078004f00040001004000010680100c000040a030010100600026010000040600c0201c0500811004080080000c00000000000b0000e000070080100c010040100c000080a000030080b00c0005c0000c00020040280700c070000400800004040300000003070000441200003000090400200c0300001054010040700400000000140001809058010000203c02010000742700000020020100003c010080400800000000480a0000201821000080480100400014090040000002004030000000800050020180003011064020580b0000001400004000080600c0001417000000000000004014040001201c000140201c0000c00014090080200407020040080000400014010000802400000000040300017034160000200c020280004001006fca5a1df54b43bf28e87f651d0eeca3a1df54743faa8e877551d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf29487ee5290edca521df54a43f6a94876d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216fd0e42dea1c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885d
  | 3 => 0xc7128788000000002b4001434700009c96000097c0028547471400000462384000000003940000041a4480f8004489212314b2a2600221091e62f13683a51833d280c31587f82d8994d83e8001b3000034000000ee20469858360088001ad02a15460a20330975438843ac6dcd496c4cc718651e10003dd21255000000d300025ca20ea8601963a90d28b0087bc5a9b41a44e81506216005c95a4943c43082158004a449e027124a50001490000008f9f70006fc000003f6000000005360413b999000084590ec0000012701300000000000430000488881746f47420100057c710003e40006c800000a281e8744c860c7e00021613cf52560fa000b99e00001383f82f0f2724f6800400750b80f217c99d27a8412657000096000044d014008214d220ee000000000003bc000001662060003327c0003140c0001b600148072000428001aa000438000000000000027f00000135a3f37661c7c93f0007b9140640000003f2030002ad341b50007680009f0004841180343e0000000000059c0e80033600138000000a7495000552140000050003b4161a70004342a18f000a5d0600000082c000002a01200021908c320d21774a2704c900e28e9c90a89d0000c40022f2de2553295e2525c82c97f38e0004399f3e279c00000000668000f80007e4e00001ba000a92992f60006f8520849eceb8324146c9510a90002d11b0a122c5a8912830345a4fa9340564dd0e10f35e554361cf10c1e82496d51c2bc182330005d06b18e06e0000000035800000068000230de0001fc000238783fe0ed0926e1842981f800328000e693b3c8000b180000078c000000000000026100068c000003e000110a81000000000e40000b88329c0940011a8d431896d4c13000071000039000670fc0b10e200108000000000000000008b92697d00009552a9526a000121e620a000052a402c5a13102927a708bd1330003bc001ba0c66d8d08e344c8743e0b93fa28c0015a096964c5a5c000000000004a6000002804261bc350ce1d6000468004520302b800000a19410c440a0009f00000090c0a00000079445245404000540000008dc60000000520940002580000027d04c84400034312294d58001481cc5ea60002370000d10008f4001780000002e800000451258002ca3ec3b10146010c8f2a730244c001231369009280044a0014900032200047997000001031020000b5260
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5424832c5450920cb15232482e5618c9209b195324832c544c920cb15321482cd63c8520cb15121483385490120ea90a40482786550120ea509404832c54881209798f540825d63d50209d987540827561d50208f596540832c62550208f990540825e63150209758c540826e62150209d984540827561150209e980540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c530826e6214c209d98453082756114c209b597420832d54d0820d354f420826d6510820cb550420834d5310820ba58042083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083674254420d9109510832d54c8020d354f200836551c8020ce552200826f6548020ab191200832d5448020d354d200836551480209ed95200833954480209b98b54c426d62d53109798e54c425d63953108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b109798e52c425d6394b10b958a41c4354534c710ad59221c426f62552109b189548425e63152109758c548426e62152109b588548423e6414e108f590538426e6214e109b588538423f6454a108f191528423e6414a108f590528425e6314a109758c5284357530c610bc58031843d0318c210bc18530843d3314c2109798e544425d639511097d8d544425c63551109bd89544426c62551109798e53442776154d108f990534423d6414d109b988534426d6214d1097994534431e6414d10c7590534434e6214d10d358853443556114d10d6580534425e63949109758e524423f64549108f191524425f63549109718d52443545390510b958a41442746550510d514d4144276658c510d514e3144274654c510d514d31442b56488510d514e21442746548510d514d2144358538c110f48c63044278654c110f44c5304435453841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d5185530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520427565cc410cd553310435553cc410d954b3104275650c410cd5503104355530c410d954831042f1600c410cd553100435553c4010d954b10042796584010d654e10042776544010cd55110042d46344010d554d100436552440109ed9510043595344010
  | 1 => 0x866e62d50219798c540865d63150219d984540867a60150219e580540867661d4c218f990530863d6414c219b988530867a6014c219e580530865e63948219758e520863e64944218f592510866f65484219dd95210866e6294f409b58a53d02b561d0f409b98a51d026d6294740a758f41d02776154e409d18553902b96010a4097d8d519025c6354640ad587435025e63149409758c525027661149409d584525034e6314940d358c525032f4314940cb50c52503666114940d9584525036960149408f997425032c52d0940cb149425029d63d0540cb14b415032c5250540cb14a405034e5394840d354e521034e5354840d354d521023d6590840c754e421032d5290840c754c421032d5210840ae58042103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103364254440cd109511031d53d0040cb54b401033551d0040da54a401023f6550040c754d40102ac6250040cb549401033551500409ed95401036952500409b98b54cc26d62d53309d98654cc2756195330b358a43cc2766194b309d58652cc29d64ccb309bd89548c26c62552309b988548c26d62152309d984548c27561152308fd91528c23c6454a30b6580318c27661951309d586544c26f62551309b189544c27761551309d185544c2cd6290d3097195434c29d64cc9308f990514c23d64145309b988514c26d6214530cd990514c3356414530d590c514c3554314530d9988514c3656214530d5cc8514c3553214530dc580514c25e65cc530d5147314c354514c530d5146304c26e62d50309b58b540c27661d50309d587540c23d65950308f990540c25e63150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c365525443097596310c31d548c430d354a310c355518c430c7550310c34d520c430d5544310c2d9600c430c7553300c34d52cc030d5547300c371518c03097d95300c31d544c030d3549300c2d4614c030d5545300c27b654c030dc545300c25e63153209758c54c827661153209d58454c827661d4f209d58753c823e6494f208f59253c832c5450b20b958632c823e64947208f59251c82cd63c87209798c548825d63152209d984548827561152209dd8553882746154e208f990538823d6414e209d98453882756114e20cbd5042882e96010a2097d8d518825c6354620ea10a40882e86250220ead09408823e64951209bd89544825e63151209758c544827661151209d584544823e6515120c798c544831d6315120cb58854483366115120cd584544833960151208f992534823d6494d208fd91534823c6454d209dd8553482746154d209b996424832c54909209b19
  | 2 => 0x6015232cb550428cae56110a32ba580428caae64cca328f992518ca3d6494632cd992518cb356494632d5cca518cb674254632d9109518ca7661951329d586544cace6290d3297195434ca6e65d0932cb550424cace6310932e350c424cae56110932ba580424caae64cc932b5986324ca3e64141328f590504ca7661141329d584504ca6e62d50329798c540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca5f654c8329bd95320ca6e6294f419b58a53d074e6294f41d358a53d071e5350f41c754e42d069d6310b41c754c42d072d5210b41ae58042d065e6394a419758e529074e6394a41d358e52907666194a41cb94b41906d663d0641ad987435069d6310941ad98442506b96010941b598f41506ae62905419798c505065d63141419b988505066d62141418fd95411067765504419b98b54cc66d62d5331b958a41cc66e62d52319b58b548c6cd6290e31a7593328c66e62d51319b58b544c65d63951319d586544c63e64d49318f593524c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d6595031c798e540c73661950318f990540c66e62150319b588540c67a60150319e580540c65d6590c31b358a430c6d56190c31c7951430c72e5494831cb552520c7666194831cb951520c72d5454831d390d520c74d4354831a7593320c71d54cc831b5587320c71d544c831d3949320c6756590431b558e410c6e56290431d954a410c7365450431e550d410c7655250431b558e310c65f654c4319dd95310c6d7654c431d5d95310c6d7644c431b5591310c796544c431e5551310c6d7624c431f1949310c7c5524c431b5181310c73a5494031ce552500c76a5294031da54a500c7d13194031d54c5500c73a5454031ce551500c76a5254031da549500c7d13154031d690d500c7594354031d6cc9500c7593254031dc905500c7714154031d6cc5500c7723154031d64c5500c7713154031d44c5500c65e63d53219758f54c865e63153219758c54c867a60153219e58054c863e6494f218f59253c871e6494f21c759253c874e6294f21d354f42c872d5410b21b358c42c874d5310b21ba58042c874e534cb219798e548865d6395221c798e548871d6395221cd986548863e64d4e218f593538863e6414e218f590538867a6014e219e58053887365450621cd55331886b5640c621cd5503188755530c621bc580318872e54c8621b598f218865e63951219758e544863e6494d218f592534866e65d0921cb55042486cd6310921b998442486e96010921b9986324866c654c921b998a41486746550521e9109414867665cc521ad5903148755530c521b998831487c5320c521bc58031486d663c8521ab992214863e64141218f590504865e63141219758c504
  | 3 => 0x4c90642e47983e21c000000618000006d000000000628a08bb4a85c00024e168958ff8004680d8000e6000000000000000d0001f725a06c240002fc00000000000910ac851546464f480007c0000f0000000000000027e00000208000160001d839c278758f62a01dc338e1348170fd1b7000000001685967450516c336844c30004080009811716c4244c9671ba0c919abf0e835d0a9252409005309c4e80dc9c1850000007e0000e49180015e1da448051cb0ec8840004a4d0964d713149a784402885288b0e28000002c8001460000008292a000000c724c0460015e808000051538001ac000eb00009c00000066026b4d5b91d000ac81580033e905378001943dc0000059e5ed469750e20014f26b0ac9b4e51df5a41fcfa9a145e0007293b416001190dc4f800046073000b10e1a1a0008a91d8000008746c1844d27500000136aaa9338e215c001400000486e545843428000ec80028e3d0102b652601c04010010181b000000500900415078000300700004000010000100000000010080001802008020100b014010040000000000010080600c010040200010000060000008c0101c0b01c0701402044060040a0000800c0000803018020000700c000500301c00048040041c000030040a0340800c020040400002000000002400401024000380500001004050040001003000230f00600c050041801c1100c0100405000010440100809018000500416c01014010000b01c0a00c0b03401030260080b00c0202000000000140a02c00000000080000c1a00804038000080000c070440a0000800c2b00c080000d010010000200c070000c024290101806c410200300c1000410020000040000012000020000001817000030401d00001010000180806c0001c0301813004000026e62947439b58a51d0f666294743d958a51d0ed661d0e439d9865290e756194a43cbd0e5290f666194a43d95865290ed661d0d43ab98a4350e6e62141439b5885050e7661141439d5845050e3f6550c4397d954310eb561d0e429d9875350a7561d4d429798f5150a5d63d45429798c5050a5d63141429d9845050a756114142d398a5310aad62d0c42ad5874310b1e5350c42ab5924210a3f65508429bd954210aaf6550842cbd954210aaf6350842e394d4210b8d5350842abd854210aac6050842d594e5110b555394442e950a5110b565354442d554d5110ba54254442cdd0d5110b354354442d694e5010b595394042ea50a5010b725194042dc5465010b2d4254042d694d5010b595354042ea5095010b725154042dc5455010b3b4354042ce50d5010b3b4254042da9095010b394254042da5095010b2942540429d98654cca756195332c798e54ccb366195332cd58654ccb1e5450f329d987548ca7561d52329d984548ca7561152329e980548ca79
  | 4 => 0x1223c63c8001390120000b82855c888b71ba09e1753300f08e014b10d13ae7ec4183a2be91c000004f40000aa790a603091aa52989cc26ac75080f158a512ec3c4408c93c8430a10e921e4d07e8b9000250c40b52221e14e0d554c83d4a97f28696d61a290546ec65a5d31a6a0f6050066234d68df578000ac1dc32aa24cb8600003d5450000000002000012e774000002a2aece42be5849b800062294000f52990ea8f40000037e0483615d2882dc7d1713a46692f28542eaa54c0e0156169470d03de1ecf599d59c570939fe4fc0006f28326c00055216126a6c211893f80e5229772908c08117c0ca7316889d000824f9acd544ab0a281a0326a87829a25227c5394e3f23180028241821020a27058070640001a8a4097000000000d1000170000cb21e3a61f8000000962189200000039c0000000026000000000000610f8000038b317841aa7d252240006c401800228b28ef0000006d8000ba2e62080000011280cb48003e8418000002362bcd28000222412fa31140440d82c00524284d2182748a05887059073c0016118ea1cf886105c111509370707680000000055400000000604002a04e4000000004f60bc00000000558c110b00000047a430420000000000000000000000a18248001a428c0018f000000001d543e61cb50001fc000e805b21a56c000ea1f65e4c8a604262b03583b47c0354b00234c735169082587b45f8f30deac10d9a04ee52c26000338988742b804e001000300005b4c800012a6f4762503e44ad488041c6284a786834e6cc521c20d440429135000994000004c6984232784e22cc628cd5482206712f116000de00002000000000000000000001804850cac65740002ca2e208000c180022a814ba19406aa051023c49000000000000664000005a09c0001c70007d800000000000000002c6114001b819e3bc002b5238948d78004ea600000a818293c99006356b04000002de0001f926000000b20002a4074002a80007112d13e364150569c11dc0003c8000000008c1db0005f45e000122000b01130003300f8a50000002f2970f40b4cc128234248112120009f400000402368000000da0003e9e23528ac6ca6a00034ce02af0000005f00037cb249e0003d08402fab423caac9e93300041d3209b2d6391490db2ca7e129acc1fe5504b0f9016780c59c947092d2a800160000000000c6215569f003067818a07000a74471c600068c8f86e3269fd12a350aa5e96a23f00055d1b9033dc000f28690ae8991d1490002f443a424b8ae5360253180991b0c402c001119fd07a8e4f38071528188708a518acd4791629a9d8a020e2b495c512c5358400a9a024b092
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x56345a4cae249a2a4600a400603c0094b45e32a0c82e0e30a6827220869266448a36509626120010b288746ac2520000ca003aac000000bc00b648bec6628402009e007c006e0000163e988c084e00a81e224a0c00c0041400000a1a00b0767090541cbab8a2425818c438787e28006c2c8e5c40649c7a06aa80680804203080000106b000a220000016001001c00201180c881161c083001252b8ec6a1085235cf615084291ae630284214a5711814210b82a9a84a8885c294d4254042e12a6a12a021721429455010b90a12a2a80854a5cb4354042a62e3a1aa021528765095010a95b9a84a80854adc54254042c52a8b00851956170109518cb42a1ac2212658a5516010932d1286b0084996195358042d0714a92c021683c150d525043198ae5b226218c9574d89310c782aa2a498863255d0604c43198ae43026218f12544c5500c788aa262a8063d09493154031e82a498aa018d497290d500c6a8b8c86a8063465d33254031aa2e3992a018d5173905500c6b0b9482a8063c450d4154031aa0ec98aa018d53744c5500c6a8ba262a806354dc93154031c52a8b008590e495358042c8718aa2c018c439454d600c621c52a8b008490d857310941486d0b8084a0a43a1591320c521ca2a6b006290ec1325803148692b8e86292819158d6114940c92c6b00a4a0661615805250306b18a5a0a818654d6010840a62e0212a22060d531894010312312a2a0081515ca4314530c4ac8b10a29851574cc8514c318b22c028a61985896014530c32a8b00621864952580310c30aaa0c29806191548614c030c56a8b0085104aa76d09408830ab1ac22a2418658d6015120c52c4b00a8906316158054483122a2c3192418315163c8520a54eb2148090628655094048314aa2c0210419254d6010820ac2e0212a21042c765512008306322a690041891915148020ca6a6b0063084d276cc53084306b22c429a21865916014d10c92c4b00a68865161580534432229ac520a21855905388510aa4eb18c6088650654c53044318aa2c0188219454d600c410cc2a4b0062086155418d100422a3b2a6880219118d5244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2ec0684a00000909831d94254042921811d9425404292181dcd425404290983dc54254042911841d93154031941821d9315403194182dd1315403191184dc93154031
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
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
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (20684+((h/227+packedAt s5K5 (18414+(h % 227)*10) 10) % 990)*11) 11
  | 4 => packedAt s5K4 (29960+((h/241+packedAt s5K4 (27550+(h % 241)*10) 10) % 958)*11) 11
  | 3 => packedAt s5K3 (5236+((h/34+packedAt s5K3 (4998+(h % 34)*7) 7) % 123)*8) 8
  | 2 => packedAt s5K2 (488+((h/2+packedAt s5K2 (480+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f8f8ffc7f8fff0c63e383fc7e0fff08727f
  | 1 => 0x1fc7f00e3f8ff1c7f07c7c038f8ff1c7364d93
  | 2 => 0xe007fff03ff001f8ff807ffc0ff001f8c78e1c
  | 3 => 0xfff800003ffffe00ffff80000ffffe00f80fe0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2008010040010000000808080120040001025
  | 1 => 0xc4a1052449250308502464292484a096164492
  | 2 => 0x4192230490232481348029180d206532428e18
  | 3 => 0x9106a49224a0092ad4900504a494c20e80b40
  | 4 => 0x90244c08034c4924ca72526260018804bd6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_32974
namespace PEqualNP.Outside.L_meta_32974
open PEqualNP.Outside.L_meta_32974.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d243179f00b1c3100d4e200000022128c00a1e057390000da80e192306e21a363a515804c845bb0601d322e0022d2c9c99866408804a68f192a39e805218341020604000280c4800c08800264c18002ffd5009fe5402ff55009fc5402ffd4c07fe5302ff54c07fc53027fd0c07fe43007f50c07fc4302ffd4805fe5202ff54805fc52027fd0805fe42007f50805fc4201ffcc805fe32007f4c805fc3202ffd4403fe5102ff54403fc51027fd0403fe41007f50403fc4101ffcc403fe31007f4c403fc31017fc8403fe21007f48403fc2102ffd400b7f5002ff9400bfd50005f5400bfc50027fd0001fe40007f50009fc4001ffcc001fe30007f4c007fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24006ff08120037d8409000bf8204801fff8824006ff04120037fecb0801aff658400dff32c2005bf99610036fccb080167e658400dfeb2c200bbf59610036facb080027d658400dfe32c2006bf19610037fec90801aff648400dff3242004bf99210037fac908002fd648400dfe3242006bf1921005ffea90803bfe5484017feaa4200eff15210037fec70801aff638400dff31c2003bf98e10037fac708002fd638400dfe31c2006bf18e1005ffea708037fe5384017fea9c200dff14e10077fe8708037fe4384001fea1c200dff10e10037fec50801aff628400dff3142002bf98a10037fac508002fd628400dfe3142006bf18a1005ffea508033fe5284017fea94200cff14a10077fe8508033fe4284001fea14200cff10a1006ffe6508033fe3284001fe994200cff0ca1000dfac308007ff5184003ff28c2001ff5461000ff8a308007ff4184003ff20c2001ff5061000ff88308007ff3184003ff18c2001ff4c61000ff86308007ff2184003ff10c2001ff4861000ff8430801afe608400dffa842006dfd4210037fca10801bfa508400dfea842006df5421005ff2a10800379508400dfe2842006ffd0210037fc810801bfd408400dfe2042006ffcc210037fc610801bfa308400dfe9842000fe4c210037f8610801bff208400dff1042006ff48210037f8410801bff108400dfb8842001fec4210037f8210801bf81084015ffb2a200abfd9510057fcca88016fe6544015feb2a200abf59510057f8ca88016fc6544001ffb222000bfd911004ffcc888012fe6444001feb222000bf5911004ff8c888012fc6444015ffaa22009ff95110057faa888027fc5444001ffb1a2000bfd8d10047fcc68800efe6344001feb1a2000bf58d10047f8c68800efc6344015ffa9a2008ff94d10057faa688023fc5344013ffa1a2008ff90d10007fa8688023fc4344001ffb122000bfd891003ffcc48800afe6244001feb122000bf5891003ff8c48800afc6244015ffa922007ff94910057faa48801ffc5244013ffa122007ff90910007fa848801ffc4244011ff9922007ff8c910007fa648801ffc324400d7fb0a2001ffd451000ffca288007fd5144003fe28a2001ffd051000ffc8288007f64144003fea0a2000fd5051000ff88288007ff3144003ff18a2001fd8c51000ffa6288003f53144003fe18a2001ffc851000ffc4288007f62144003fe90a2000fd4851000ff84288006ff6044015ffa82200adfd4110037fca08802bfa5044015fea822000df54110057f2a08800379504400dfe2822009ffd0110037fc8088003fd404400dfe2022008ffcc110037fc6088003fa3044001fe9822000fe4c110037f8608801fff204400dff1022000ff48110037f84088007ff1044003fd8822006ff84110037ec208801bfc104400dfa0822001fe04110
  | 1 => 0x379504c00dfe2826019ffd0130037fc8098003fd404c00dfe2026003ffcc13001ff6609801bfe304c00def1826006ff0c130037b8609800ff8304c031ff9026006ff081300bffe209801bfc104c00dffb2c4006bfd9620037fccb10016fe658800dbf32c40059f99620037facb1005afd658800dbeb2c40009f59620037f8cb1001afc658800dffb244006bfd9220037fcc910012fe648800dfeb244000bf59220037f8c91001afc648802dffaa44015ff952200b7faa910057fc548800dffb1c4006bfd8e20037fcc71000efe638800dfeb1c4000bf58e20037f8c71001afc638802dffa9c4014ff94e200b7faa710053fc538802bffa1c4014ff90e20007fa8710053fc43880057eb144002ffd4a20017fca51000bfd5288005fe2944002ffd0a200afde851000bfe4288005fea144002ff10a20017d8851000bff3288005ff1944002ff4ca20017f8651001bff618800dff30c4001bf98620037fac310002fd618800dfe30c4006bf186200b7fea31004ffe518802dfea8c4013ff146200affe831004ffe4188001fea0c4013ff106200a7fe631004ffe3188001fe98c4013ff0c620017fe431000bfe2188005fe90c4002ff08620035fcc11001bff508800dbfa844006ff94220037faa11001b7d508800dfe2844006ffd0220037fc811001bfa408800dfea044000fe50220037f8811001bff308800dff1844006ff4c220037f8611001bff208800df79044002fec8220037f8411001bf8208800dff8844006ff04220097feca9004aff6548025ff32a4005bf99520097faca9004afd6548025fe32a4005bf19520007fec890002ff6448001dfb224000afd912008ffcc890012fe6448001feb224000bf5912008ff8c890012fc6448001de3224004af19120097fea890047fe5448025feaa24011ff15120007fec690002ff6348021ff31a4003bf98d20007fac690002fd6348021fe31a4003bf18d20097fea690043fe5348025fea9a4010ff14d2008ffe8690043fe4348001fea1a4010ff10d20035fec49000bff5248005ff2924002ff54920017f8a49000bff4248005ff2124002fb90920017fa8490003ed4248005fe2124002ffcc920017fc649000bee3248005fe9924000fb4c920017f86490003ff61480017fb0a400fff9852000dfcc290003fd614801ffe30a4001bf18520097fea29003ffe5148025fea8a400fff1452008ffe829003ffe4148001fea0a400fff10520087fe629003ffe3148001fe98a400fff0c520017fe429000bef2148005ff10a4002ff48520007da429000bfc21480057fb024012ffd4120096fea09001bfe5048025fea824000df54120037f8a090047ff404800dff2024000fe90120007fa8090003f9404800dfe2024010ffcc120037fc6090003fd304800dfe1824002ffc8120017f6409001bfe204800df71
  | 2 => 0x40117fea2a007ffe5150045fea8a801fff14540027fe82a0013bf4150009ff20a8004ff505400077a82a0013fc4150043ff98a801fff8c540007fa62a007ffc3150041ff90a801fff88540007fa42a007ffc21500097fb028022ffd4140116fea0a001bfe5050045fea828000df54140037f8a0a0013ff4050009fda028006ff901400377c80a001bfc405000dde2028004fe1014010ffe60a001bfc3050041ff9028006ff081400fffe20a001bfc105000dffb2c6006bfd9630037fccb18016fe658c00dbf32c60059f99630037facb1806efd658c00dbeb2c60009f59630037f8cb1801afc658c00dffb246006bfd9230037fcc918012fe648c00dfeb246000bf59230037f8c91801afc648c037ffaa4601eff952300dffaa91807bfc548c0077eb1c6003ffd4e3001ffca71800ffd538c007fe29c6003ffd0e3001ffc871800ffd438c007fe21c6006ffd8a30037fcc51800afe628c00dfeb146000bf58a30037f8c51801afc628c037ffa94601dff94a300dffaa518077fc528c03dffa14601dff90a30007fa8518077fc428c007ff9946003ff8ca3001ffa651800ffc328c00dffb0c6006ff9863000dfcc31801bfd618c0017eb0c6006ff18630035f8c31806fff518c039ff28c601bff546300e7f8a31807bff418c039ff20c6000ff506300e7f8831800fff318c007ff18c6003ff4c63001ff86318077ff218c039ff10c6000ff486300e7f8431801afe608c00dffa846006dfd4230037fca11801bfa508c00dfea846006df542300dff2a11800379508c00dfe2846006ffd0230037fc811801bfd408c00dfe2046006ffcc230037be611800ffb308c00dfe1846006fe0c230037fe411801bfc208c00dff8846006ff042300d7feca9806aff654c035ff32a6005bf995300d7faca9806afd654c035fe32a6005bf19530007fec898002ff644c033ff3226004bf99130007fac898002fd644c033fe3226004bf191300d7fea898067fe544c035feaa26019ff15130035fec69800fff534c007ff29a6003ff54d3001ff8a69800fff434c007ff21a6003f790d3001ffa8698003dd434c007fe21a6000ffd8930005fec498063fe624c0057f3126000ff589300c7f8c49800afc624c035ffa926018ff949300d7faa498063fc524c033ffa126018ff90930007fa8498063fc424c007ff9926003f7cc93001ffc649800ffd324c001ee9926003ff0c930007fec298002ff614c02fff30a6001bf98530007fac29805ffc614c0037e30a601affd45300bffca29806bfd514c02ffe28a6019ffd05300bffc8298003fd414c02ffe20a6003ffcc53001fbe629800ffe314c007fe98a6000f74c53001ff86298063ff214c02fff10a6000ff485300bff8429800eff604c035ffa82601adfd4130037fca09806bfa504c035fea826000df541300d7f2a09800
  | 3 => 0xfa82422ddfd412116ffca0908b7fd504845bfe282422cffd0121167f880908afff3048457fe1824202ffc8121017de409080bfc2048403ff8824201fdc412100ff820908037f6454055bf322a000df59150156f8c8a80037f6354053bf31aa000df58d5014ef8c6a80ab7f4354053bf21aa000df50d5014ef886a80037f6254051bf312a000df58950146f8c4a80ab7f4254051bf212a000df50950146f884a80a77f3254051bf192a000df4c950146f864a80037f615404fbf30aa000df5855013ef8c2a80ab7f415404fbf20aa000df5055013ef882a80a77f315404fbf18aa000df4c55013ef862a80a37f215404fbf10aa000df4855013ef842a80177f605400b3fb02a005ded8150156fe80a801b7c4054053bf982a006df0c150146fe40a801b7c205404fbf882a006df04150037fecb2001aff659000dff32c8005bf99640036fccb200167e659000dfeb2c8026bf59640036facb200027d659000dfe32c8006bf19640025fac920013ff5490009ff2a48004ff55240027f8a92001bff639000dff31c8003bf98e40037fac720002fd639000dfe31c8006bf18e40137fea720097fe539004dfea9c8025ff14e40027fe8720013fe4390009fea1c8004ff10e40037fec52001bfe62900057f3148006ff58a40005fac52001bfc629000d7e3148026ffd4a40127fca52009bfd5290049fe2948004ffd0a40027fc8520093be4290009fea148004ff10a40027788520097ff3290049ff1948000ff4ca40127f8652001bff619000dff30c8001bf98640037fac320002fd619000dfe30c8006bf18640137fea32008ffe519004dfea8c8023ff14640027fe8320013fe4190009fea0c8004ff1064012ffe632008ffe3190001fe98c8023ff0c640127fe432008ffe2190001fe90c8023ff08640035fcc12001bff509000dbfa848006ff94240037faa12001b7d509000dfe2848006ffd02400377e8120013fb409000dfe2048006fe10240037fe612001bfc309000dff9048006ff08240037fe212001bfc1090045ffb2a8022bfd9540117fccaa0016fe6550045feb2a8022bf59540117f8caa0016fc655000d7fb228004ffd5140027fca8a0013fd5450009fe2a28000ffd8d40005fec6a0087fe63500077f31a8000ff58d4010ff8c6a000efc6350045ffa9a8021ff94d40117faa6a0087fc5350009ffa1a8004efd0d40027fc86a0013fd4350001dea1a8004ff10d40007fec4a0002ff6250001f7b128000bbd8940107fcc4a000afe6250001feb128020ff18940015f8c4a0003ec6250005763128022ffd4940107fca4a008bfd5250041fe2928004ffd09400277e84a0013fe4250009fea128000ef50940027f884a0087ff3250041ff1928000ff4c940107f864a0003ff61500017fb0a801fff9854000dfcc2a0003fd615003ffe30a8001bf185
  | 4 => 0x8c7fc32504037fb0a8201ffd454100ffca2a0807fd5150403fe28a8201ffd0541027ee82a0807fe4150403df20a8201ff1054100f7882a0807f44150403ff98a8201ff8c54100ff862a0807ff2150403ff10a8201fd8854100ff842a0803ff60504017fb028200ff98141007fac0a0803fc605040d7e3028233ffd414119efea0a08cffe5050467fea828233ff14141027fe80a0813bf4050409fe2028232ffcc141197f860a08c7ff2050463fe1028201ffc414100fee20a0807fc1050461ffb2a6230bfd9531006feca988027f654c461ff32a6205bf99531187faca988c2fd654c461fe32a6205bf19531186f8ca988167c654c401ffb226200bfd913117ffcc898812fe644c401feb226200bf5913117ff8c898812fc644c461ffaa2622fff95131187faa8988bffc544c4037fb1a6203ffd4d3101ffca69880fde534c407fea9a6230f754d3101ff8a69880fff434c407ff21a6203ff50d3101ff88698803ff624c4017fb12622eff98931015fcc498803fd624c45dfe3126202bf18931187fea4988bbfe524c461fea92622eff1493117ffe84988bbfe424c401fea12622eff1093101ffe649880ffe324c407fe9926203ff0c93100dfec298807ff514c403ff28a6201fd9453100ffaa2988c3f5514c403fe28a6201ffd053100ffc8298807fd414c403fe20a6201ffcc53101fee6298807fe314c403ef18a6201ff0c53100fb86298807f4314c403ea18a6201ffc853100ffc4298807fc214c401ffb026200bfd8131007fcc098803fd604c401fe3026206bf18131187fea0988c37f504c461ff2826230ff54131187f8a0988bfff404c45ffe2026203ffcc13101fbe609880ffc304c45dff902622eff0813100ffe2098807f7104c403fe082622dffd952116dfeca908b7fe654840b7f32a422dff5952116dfaca908b7fc654840b7e32a4200ffd9121005fec8908b3fe64484097f3224200ff59121005fac8908b3fc64484097e322422dffd5121167fca8908b7fd5448459fe2a24200ffd8d21005fec6908affe63484077f31a4200ff58d21005fac6908affc63484077e31a422dffd4d2115ffca6908b7fd5348457fe29a422cffd0d2115ffc8690803fd4348457fe21a4201bfd8921017fea49080bfe5248405f72924202ff5492116fdaa49080bfc5248405ffa12422cfbd0921017fc849080bfd4248405fe2124202fb10921017fe649080bfe3248405f71924202ff4c921007da649080bfc32484037fb0a4201ffd452100ffca290807fd5148403fe28a4201ffd052100ffc8290807f64148403fea0a4200fd5052100ff88290807ff3148403ff18a4201ff4c52100ff86290807ff2148405fb90a4201ff8852100fdc4290807fc2148403f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c09081afc604845bf
  | 5 => 0x9142027fea8a1013fe5450809feaa28404ff15142007fec6a1002ff6350871ff31a8403bf98d42007fac6a10e3fc63508077e31a8439ffd4d421c7fca6a10e7fd5350871fe29a8404ffd0d42027fc86a1013fd4350809fe21a8402bfd8942017fea4a100bfe5250805fea928402ff14942017fe84a1013ef4250805ff2128402ef90942017f884a100bbc4250805f62128402eb10942017fe64a100bfe3250805fe1928400ffd8542005fec2a10dffe61508037f30a8400ff585421bff8c2a1006fc6150873ffa8a8437ff945421cffaa2a10dffc5150809ffa0a8404ff90542027f882a10e3ff315086fff18a8437ff0c542017fe42a100bfe2150805fe10a8400ffd8142005fec0a1003fe6050801feb028400ff18142035f8c0a10e7ff5050873bfa828439ff941421cffaa0a10e7fc5050809ffa028404efd0142027f880a10e3ff3050871fe1828402ffc8142017de40a100bfc205086fff8828437ff041421b7feca990daff654c86dff32a6405bf995321b7faca990dafd654c86dfe32a6405bf19532007fec899002ff644c86bff3226404bf99132007fac899002fd644c86bfe3226404bf191321b7fea8990d7fe544c86dfeaa26435ff15132015fec69900fff534c807ff29a6403ff54d3201ff8a69900fff434c807ff21a6403f790d3201ffa8699003dd434c807fe21a6402bfd8932017fea49900bfe524c805f72926402ff549321b7daa49900bfc524c805ffa126435fbd0932017fc849900bfd424c805fe2126402fb10932017fe649900fef324c805ff1926402f78c932017f8649900bdc324c805f61926400ffd8532005fec2990d3fe614c8037f30a6400ff585321a7f8c299006fc614c86dffa8a6434ff945321b7faa2990d3fc514c86bffa0a6434ff905321a7f8829900fff314c807ff18a6403ff0c532017fe429900bef214c805ff10a6402ff08532007fec099002ff604c801ff3026400ff58132007f8c09901afc604c86dffa826436dfd41321b7fca0990dbfd504c86dfe2826435ffd01321aff8809900fff304c807ef9826403ff0c132017fe409900bef204c805fe1026434ffc41321a7f820990cfff65504677fb2a8233ff9954102dfccaa08cffd65504677eb2a8233ff1954102df8caa0806ff6450409ffaa28204ff951410277ca8a0813fd5450467deaa28204ff15141007fec6a0802ff6350465ff31a8203bf98d41007fac6a08cbfc63504077e31a8233ffd4d41197fca6a08cffd5350465fe29a8204ffd0d410277e86a0813fe4350409fea1a8200ef50d41027f886a0803ff62504017fb128231ff98941015fcc4a0803fd6250463fe3128202bf1894119ffea4a08c7fe5250467fea928231ff14941027fe84a0813fe4250463df2128204ff50941027f884a0813bc4250465ff9928231ff8c941007fa64a0
  | 6 => 0x2c000150100240000e0000040080d0020100000400600c0080706400c000000020b80000f02400400001008004018000040100080003c0280308701607c0400b00c18c00000004024060030020100080000404c0303100001c038000000000200715000408000018000028240080300000a0000000380100400800814028008010000000141580900803c0002100200c05001008000050050160180700500a0240100f00800400802000018000050021940400000602c008000000140580102a1340000600403c0380400a0600100a0020000000000008c0281a0202480180300c0000100a03a0000100000a0040f015000008028000020000c80000002c00813010024020090000240a80700403807001024004010000040300100100201c0480a000014000000280000280201000404800064010050000120c40700002e0980000600000011800010008000200020000080201c038010010000000180701200400009024004000000000840380800200c01001012008080040080200081f014014000020460000181002a000018050000080000400004c008070042d8000000220080104301c000008000020000e00f008024028030080381282002e000028000000000000200401400074002040000040020000b00d0040380800401e0540d0080000000c08201200c0102a0020080380e0081180182f01204c0001a00a0080080f004000000050000141101100001c028430060700100101e000000030000500080000400016001004004008060e61280300000a0000300500e02c79ffb2a863cbfd95431e7fccaa1816fe6550c79feb2a863cbf595431e7f8caa1816fc6550c077fb228604ffd5143027fca8a1813be5450c09feaa2863cef55143027f8a8a180eff6350c07ffa9a8603ff94d4301ffaa6a180ffc5350c07ffa1a8604f7d0d4301ffc86a180fbe4350c07fe21a8603ef10d4301fb886a1803ff6250c017fb12863bff98943015fcc4a1803fd6250c77fe3128602bf189431e7fea4a18effe5250c79fea92863bff14943027fe84a1813fe4250c77df2128604ff109430277884a180fff3250c07ef9928603ff8c94301ff864a1803ff6150c017fb0a863aff9854300dfcc2a1803fd6150c75fe30a8601bf185431e7fea2a18ebfe5150c79fea8a863aff14543027fe82a1813bf4150c09ff20a8604ff1054301ffe62a180ffe3150c07fe18a863bffc85431d7fc42a18ebfc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028606bf181431e7fea0a18f37f5050c79ff282863cff541431e7f8a0a1813ff4050c09dfa028604ff1014301ffe60a180fdf3050c07fe182863bffc81431dff840a18ebff1050c75fe0828639ffd95421cdfecaa10e7fe655080b7f32a8439ff595421cdfacaa10e7fc655080b7e32a8402bfd
  | 7 => 0x4d116e0003ca00000000014409d33a1fa29d3380000003803d720046100031650d0000002f40001a426430500010f3774a349338e1f606841f2891d95865170eb4130902dc4c63e94d050814c1f33a043b0bc0001242bc4b90000fd20745d55b2b906f36355e28317b26500002459157f05f36416b0a906c41c4fc0002753f810243c29c2c71ee1870d006730c0000000000f40002e81c101c2b405241253300000012200035f00000000a0000580003d50ea4e11fd0c73f30790002c14115744dc37a1151cd49812f13558700047f0001d64242f209a0f62bd02c1940000001480b52f33184c222100031200022e0d91f21e216c0dc53800031446b00022d0510004422ba1294374fa34c0000200005491fc1bf23f1171a648c1102c646804d1510c253f5030003fe42e08a48f2fc14e0d74de0000a800038204b0004040001ec52a0004ac37449642100036c30813d00927d3d822c2842603d13ce3933ba58b44711e2104021005690650462ca07e0005412ff3ac4700c647938851934632a25956411334513f20901d5062980003c107c28e00454300041846c3500001551755903b41e805b2610dd0f20002ec0004692c90004564fb00500000000024c0002a31b25721653a853e40502b34454a5731b515d11a3c43342c242b0000d655a3a61b02360002824b616a00025632809e47a03a3e200047658000000018800027943805a0003da08154200031e0bb2f501b2fa56a24d0fe2ea58836815405657a0940004480ff00000037500019517a0001bc4f145700053b2183b650b1161c232711c14742609925c1202ab53a0000004ab00008c4e830a00055d1453c056c48508009b0b654827a3871b132c4651365605661a14921492b34781d700039932e3b50a21af21a1760c343600052400008602e04058a4cf17d4dd4a23ee0720e93e12760734a12ae00020100051e04900000f00041d10b37357b5580000004a90005203d40111680002fe52518400052900b0003e83e60003be4641ea00009f00004300017955654e5304d63f533c0f85120ba10a0a42af37c52d2404872d145e2042023305782304df28020c01815c42510804521d48156519f4f444b0b23394f20633a242f49756f09722824a2d931d1bd3ae28542807a3c94312eb38a1801cc2171280a12683953331ca56336d4f61a30002442350552e536f2124af15b5551de30d4164744ff1663794bc0f53d956225724b55729e1344b135121c01e1313e50a73210001013b01c94cc26955c5134f01671a04c425d00057e57908b00052c22255f0003610004190001823c706b00002c0000c00600c0005e042010008040000940601600a00005830000000038050020340580006e00002011008014040010000440180700007846802034000000310281700000508a0200004701a0
  | 8 => 0x95370003760000001ab2a10002c000018b00014a0d52293f927f0000030000005854cb3b74c549c2901964ae1e14e413946043312a3433961a808e0384c32ce2c433d2b01e60154302a64661405812342cc08812731c29632206002d1901894c852b4861810c828726c37f0761f520b1db29b57d36e3ff27e1d13de4221854a43e403327346f02110e0ac1321191e31834a51ae19d0ca43205d4544d84da51650745925005049a5675222470e35054b84463410b722a0143eb2a41f00e543427403c2b10bf0b115a3ec0e101a13b39f44d2e32a91e05471931ba4bd0b30d44072ef35718e1c31e940b26d0063712160f35762a22ee23700708944f5684b305e57c19933240148238907530006639110658e1055541cf23b1f40ec52e47d03914654511425e2384d403e07116450c2921d038f18a3b92ed2bb0f13dd2943e71f745a0db3fb2240c13203ab1785834754c13702781f14a03f42a500e1922d64ea18d04c0e842d2fd00023c0313b842c39b0001580000933b317107025f2c503b2130005280000000000000be0002b70003ef0c026e0003664550000003371e545c00036a3690005820002ac2860a000056e32b3c31b74ec5261d850e00051425836b4b23971dc4ee04144923d08711b0002f73c849d34226f01f27b46a3193c639e1122062a71254a72f829125400000017f0161ed3df2521bb2d34584f329358d14f1c706400000000038d5273a700000000003554000014d2b802f0fb0ed53d0300002be3e343f50424e0003bf00019c39a57514b0000fa3251724c031f1985231d500049922514245f04a41e10d32904e0a64ed0002fb00000049b51500029f00035e00052f20f3fd00025b07b18c24f0001c53a32a827c37e00026235c07707d0f922f0ab4d90002db4db4f54e544a4e638c1560af1d228a32d25a38b0000130d800044c17003d42332f0004e73bd02824200003600000013800050f00000046700045226315246d3a500000000051833e00022343a0002f62df0cf16f34d4e01265024630c530601708449f4940003013b20251e72e10e23983a900000002651f0003ad1fb43e2081a554b00000034745b0001032f100153148b4d50000001214030000000480000003e04ce2b20000004200002d558c3533d64f800046228822600029539d2e70002e944324806b0aa3cd5102ad3af13a0ae00031a0423923bc2e000000055302355251b00054412e30f2672663071574f90000df0004ca4c72193262150ce30e0321b30bd34b1c60440003313a11634831044103db3831620000003f02d05091c02aa29a5002d82d70000002cf1740000e753540a0000000620c400c5010001ad0d10000000000e400040851100016d06144130208551d30944e1a705403f0085210924954aa161472000000137091000000000539220
  | 9 => 0x3483f212b31b1771860cd0823780000001aa4e23c54eb21140d0690001414840000002c834058920a0000951da00031741a1cb02235a13c11819b0962b54d224140600000056b24628131506d3650b000000033b00028d13e0000001dd15317c0b400028c35530313305300002a4143360001731ef0192532f92a03351d44f705926a0b923951a1c82331f85772de48e2b60293245322e655100000000007f19e0001602434400000374ad26b0004e900057128b2142724270000a340c3520003d00000001a23040e609c23a3130000000cc0000000002f00f70000000000000000271fe4352274d700244535d0ef47e24949108310c08f5614b53d34513603234bf0004443114390000e02992d23b13dc37254f54d21e50a3544535362e41b600048035800015e0000005590003f648d3861231b438537d2310000470001df2971693ea4a84000000b82323942bf00037b00d00000000019a34e2c34901974cd2511a904f51c2cd03443d3cf00025535927011f56d00042a4bb33f3f108d06e0000000004d30d300000038430b11d3bb40f0000001910003d209817e4b449e0de4880004294891b90002453672cb0000003fa41534947b2710000002dd1eb0004b012d21b2774501ce34a1091ff15041748a07846e1d30f00c923e05c2da4b73cc35b47310720300057020d3cb4be0570000a528f2050740004fe4e31c439c22b21f3810003623f71f95343c20da18f3100fc4ef01220e3904a61b80cb4c91ac1433fc3aa41b0ad54c01006a4fd3a43ed1e458f5501be11153c54640e0ee2e234f15f4ba2d43564770005840000d200012c47c1594711304
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa30541100377830541102177b20541100377a205411003778205411013f7b10541100377610541100377410541100377810541100577b765411002e7b765411013f78765411002e7876541100077b74541102277a74541100077974541102277874541100077b64541102277a64541100077964541102277864541100077b735411021f7a735411000779735411021f7873541100077b63541100067b635411021f7a635411000779635411000679635411021f7863541102277b435411021f7a435411000779435411021f7843541100077b72541102177a72541100077972541102177872541100077b62541102177a62541100077962541102177862541102277b42541102177a425411000779425411021778425411021f7b32541102177a325411000779325411021778325411013f7b715411000773715411013f7a715411013f79715411013f78715411013f7071541100377b61541100367b615411003773615411013f7b415411013f7a415411013f72415411013f79415411000771415411013f78415411013f7b315411013f7a315411013f72315411013f79315411000771315411013f78315411013f7b215411013f7a215411013f72215411013f79215411000771215411013f782154110024ff765011000cfe76501100fcfd765011000cfc7650110006bf6450110026bc6450110005ef725011003dec7250110005f7715011000df47150110007b5415011000779505011020dfa768c110036fa768c110035fb758c1100377a758c110205f9758c11003779758c11000579758c1101fefb658c1101fef9658c1100bdf9738c11001efa638c11001ef8638c110037f3718c11000dfa718c110035f8718c110037f0718c110036fb618c110037f3618c1100e7f2418c110007f1418c1100e7f2318c110047f1318c1100e7f2218c110007f1218c11001cff764c11000cfe764c1100bcfd764c11000cfc764c110006df634c11001edc634c110005f7714c11000df4714c110007d5314c1101ef7b504c11000779504c110037d8304c110037f0104c11000df8764c11001ef8764c11000cf8764c1101f5fb754c1101f5f9754c1101eefb654c1101eef9654c110035fb734c110037db734c110007db634c11001efa634c11001ef8634c110047d8634c110047da434c110007d9434c110047db324c110007d9324c110007f3714c11000dfa714c11000df8714c1100bff0714c110036fb614c110037f3614c1100bff2414c110007f1414c1100bfdb314c1100bff2314c1100bfd9314c110047f1314c110007d1314c1100bff2214c110007f1214c110014ff764811000cfe764811007cfd764811000cfc7648110005bf744811004dbc7448110006ef6248110016ec6248110005f7714811000df47148110007e52148110007795048110
  | 1 => 0x891000cfc71d891009ef641d891009eef21d891009eed21d8910034fe70d891000cfd70d8910034fc70d89100067f50d891003eef20d8910005bf745891004dbc745891003eec6258910255fb7058910004ff755891002cfe7558910004fd755891002cfc7558910004ff7458910006bf7458910004bf7458910024fe7458910024fc7458910006bc7458910024bc7458910004ff735891001cfe735891001cfc735891009cff7258910006ef725891003eee325891007cff7158910006f7715891007ef64158910254ff7058910006fb70589100067f5058910004ff7650910004fe7650910004fd7650910004fc765091003fac425091000df67150910004ff764c910004fe764c910004fd764c910004fc764c910016ee624c910006ed624c91000df6714c910035f47650510026f47650510034f4765051000df7745051000fb77450510007b76450510026f66450510026f4645051004fb4645051004fb65450510247b55450510005f7735051004fb74350510007b54350510005f77250510006f76250510006f5625051024fb6425051004fb44250510007f37050510035f67050510035f47050510007f0705051000ef7605051000ff36050510247775050510247f25050510247f1505051004fb74050510035f4764c51001ef4764c510034f4764c51000777754c51023f74754c51023ef7654c51023ef5654c510005f7744c510005f5744c51000df7734c51000fd7734c510007d7634c51001ef6634c51001ef4634c510047d4634c51001ed4634c510047d6534c51023fd5534c510005f7724c510007f3704c510035f6704c510035f4704c510007f0704c51000ef7604c51000ff3604c51023f77504c51023ff2504c51023ff1504c510047d7304c510035f47648510016f47648510034f47648510005f77448510005f57448510006f76448510006f56448510005f77348510005f5734851000df7724851000fe77248510007e76248510016f66248510016f4624851003fe4624851003fe6524851022fe55248510237e7424851003fe4424851003fe63248510007e53248510007f37048510035f67048510035f47048510007f0704851000ef7604851000ff3604851022f77504851022ff2504851022ff1504851003fe7204851002e7f765411013e7e765411013e7d765411002e7c76541100067f64541101567e64541100067d64541101567c64541100067f635411014e7e63541100067d635411014e7c63541100067f62541101467e62541100067d62541101467c625411000777715411013f7471541100367f615411013f76415411000775415411013f76315411000775315411013f7621541100077521541100357f70541100577b70541100367f60541102277b40541100377a405411003778405411021f7b30541100377
  | 2 => 0x28778325421013f7b715421013f7a715421013f79715421013f78715421013e79615421013f7b415421013f7a415421013f79415421013f78415421013f7b315421013f7a315421013f79315421013f78315421013f7b215421013f7a215421013f79215421013f782154210035fb764c21027efb764c210275fb754c210275f9754c210036fb654c2100377a654c21026ef9654c21003779654c21000679654c210037db734c210037db634c21001efa634c210036f8634c210037d8634c21006fda434c210007d9434c21006fdb324c210007d9324c21000dfa714c21000df8714c2100bfdb314c2100bfd9314c210024fe76d911004ebe64d9110004ff75d911002cfe75d9110004fd75d911002cfc75d911001cfe73d9110004fd73d911001cfc73d9110014fe72d9110004fd72d9110014fc72d9110006be42d911004ebc42d9110034ff71d911000cfe71d9110034fd71d911000cfc71d911011ebf41d911011ebd41d911011ef621d9110034fe70d911000cfd70d9110034fc70d91100067f50d911004ebf40d911004ebc6459110005ef725911003dec7259110265fb7059110004ff755911002cfe7559110004fd755911002cfc755911011cff7459110006bf7459110004ff735911001cfe735911001cfc735911004ebf4359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec72591100fcff7159110006f771591100fef62159110264ff7059110006fb70591100067f505911001cfe76d8d10046de63d8d10004ff75d8d1002cfe75d8d10004fd75d8d1002cfc75d8d10024fe74d8d10004fd74d8d10024fc74d8d10006df53d8d10046dc53d8d10014fe72d8d10004fd72d8d10014fc72d8d10034ff71d8d1000cfe71d8d10034fd71d8d1000cfc71d8d100e6df31d8d100e6dd31d8d10034fe70d8d1000cfd70d8d10034fc70d8d100067f50d8d10006fa50d8d10006f950d8d10046df30d8d100057f7558d100557c7558d10046dc6358d1025dfb7058d10004ff7558d100067f7558d100047f7558d1002cfe7558d10004fd7558d1002cfc7558d100067c7558d1002c7c7558d10004ff7458d10024fe7458d10024fc7458d100e4ff7358d10006df7358d10004ff7258d10014fe7258d10014fc7258d100bcff7158d10006f77158d1025cff7058d10006fb7058d100067f5058d10006fa5058d10006f95058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10026be6450d10006bd6450d1000df67150d10014fe76d891003eee62d8910004ff75d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d891001cfe73d8910004fd73d891001cfc73d8910006ef42d891003eec42d8910034ff71d891000cfe71d8910034fd71d
  | 3 => 0xd40596100367c40596100367f30596100367e30596100367a30596100367d30596100367c30596100367f20596100367e20596100367d20596100367c20596100367f10596100367e10596100367d10596100367c1059610004ff755921002cfe7559210004fd755921002cfc7559210036bf7459210004ff735921001cfe735921001cfc7359210076bf4359210004ff7259210006ef7259210004ef7259210014fe7259210014fc7259210006ec7259210014ec7259210076bf42592100febf41592100febd4159210034ff7059210034fe7059210034fd7059210034fc70592100367f50592100367d5059210036be4059210036bc4059210036f71059210036f51059210004ff7558e1002cfe7558e10004fd7558e1002cfc7558e10004ff7458e10024fe7458e10024fc7458e10036df7358e1006ede4358e10004ff7258e10014fe7258e10014fc7258e1006edf3258e100bedf3158e100bedd3158e10034ff7058e10034fe7058e10034fd7058e10034fc7058e100367f5058e10036fa5058e100367d5058e10006f95058e10036de3058e10036dc3058e10036f71058e10036f51058e10004ff7650e10034fe7650e10004fd7650e10034fc7650e101e67e6550e100067d6550e10026be6450e10006bd6450e1001ede6350e10006dd6350e10004ff7558a1002cfe7558a10004fd7558a1002cfc7558a10004ff7458a10006bf7458a10004bf7458a10024fe7458a10024fc7458a10006bc7458a10024bc7458a10004ff7358a1001cfe7358a1001cfc7358a10036ef7258a10066ee4258a10066ee3258a1007eef2158a1007eed2158a10034ff7058a10034fe7058a10034fd7058a10034fc7058a100367f5058a100367d5058a10036ee2058a10036ec2058a10036f71058a10036f51058a10004ff7650a10034fe7650a10004fd7650a10034fc7650a101ce7e6550a100067d6550a10026be6450a10006bd6450a10016ee6250a10006ed6250a10067ac4250a10004ff764ca10034fe764ca10004fd764ca10034fc764ca101b67e654ca100067d654ca1001ede634ca10006dd634ca10016ee624ca10006ed624ca100377b76542100357b765421029e7b76542100077b74542102977a74542100077974542102977874542100377b64542100377a64542100377964542100377864542100077b735421028f7a735421000779735421028f7873542100377b63542100367b63542100377a63542100377963542100067963542100377863542102977b435421028f7a435421000779435421028f7843542100077b72542102877a72542100077972542102877872542100377b62542100377a62542100377962542100377862542102977b42542102877a425421000779425421028778425421028f7b32542102877a3254210007793254210
  | 4 => 0x8520007eb7048520035ee7048520035ec7048520007e87048520016ef6048520017eb60485202b76f504852007fe7104852002e7f76541201467e76541201467d765412002e7c76541200067f64541200073f64541200063f64541201567e64541200067d64541201567c64541200073c64541201563c64541200067f635412014e7e63541200067d635412014e7c63541200076f72541201476c72541200367f62541201476e42541200076d42541201476e32541200076d32541200067f615412013e7e615412013e7c61541201476f21541200076d21541200357f70541200977b70541200367f60541200377a40541200377a30541201477b20541200376e20541200376c20541200377820541200376820541200377a10541202adfa7690120036fa76901200377a7590120037797590120105f97490120127bb6490120026fa6490120026f8649012008fb86490120026b86490120037eb7290120015fa7290120035f87290120037e87290120036fb6290120037eb6290120127ba4290120127ea4290120127aa429012008fe94290120127b84290120127ea3290120007e93290120127eb2190120007e92190120024ff7650120014fe7650120104fd7650120014fc7650120006bf6450120026bc6450120005ef7250120015ec7250120007ad42501202a77b5050120007795050120037b84050120037e82050120015f87650120026f87650120014f87650120035fb7450120037bb7450120007bb6450120026fa6450120026f8645012008fb8645012008fbb4350120007b94350120007eb7250120015fa7250120015f87250120107e87250120036fb6250120037eb6250120107bb4250120107ea4250120107b9425012008fe94250120007a94250120107ea3250120007e9325012008fbb4150120007b94150120107eb2150120007e9215012001cff764c120014fe764c1200c4fd764c120014fc764c120006bf644c1200cebc644c120006df634c12001edc634c120005ef724c120015ec724c120007cd324c12000779504c1200067f74596100067e74596100067d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f42596100067e42596100067c42596100067f32596100067e32596100067c325961013e7f715961013e7e715961013e7d715961013e7c715961013e7f415961013e7e415961013e7d415961013e7c415961013e7f315961013e7e315961013e7d315961013e7c315961013e7f215961013e7e215961013e7d215961013e7c21596100367f70596100347f70596100367e70596100367d70596100347d70596100367c70596100367f40596100367e40596100367
  | 5 => 0x34fd72d8d20014fc72d8d200eedf32d8d200eedd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d200eeef21d8d20014fd70d8d200067f50d8d20086df30d8d20005bf7458d2008dbc7458d20006bf6458d20006bc6458d20086dc6358d202d5fb7058d20004ff7558d2002cfe7558d20004fd7558d2002cfc7558d20004ff7458d20006bf7458d20004bf7458d20024fe7458d20024fc7458d20006bc7458d20024bc7458d200ecff7358d20006df7358d20086de4358d200c4ff7258d20006ef7258d20004ff7158d2000cfe7158d2000cfc7158d200c6ef2158d202d4ff7058d20006fb7058d200067f5058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d20026bc6450d2001ede6350d20006dd6350d20015ee7250d201dfae4250d20035ec7650920026ec7650920034ec7650920015ef7450920017af7450920007af6450920026ee6450920026ec645092008fac6450920026ac6450920005ef7350920005ef7150920007eb7050920035ee7050920035ec7050920007e87050920016ef6050920017eb60509202cf6f505092008faf4050920035ec764c92001eec764c920034ec764c9202c6ef654c9202c6ed654c920005ef744c920005ed744c920007af644c9201aeee644c9201aeec644c920007ac644c9201aeac644c920015ef734c920017cf734c920007cf634c92001eee634c92001eec634c920087cc634c920087ce434c920007cd434c920005ef714c920007eb704c920035ee704c920035ec704c920007e8704c920016ef604c920017eb604c9202c76f504c920087cf304c92000cfe76d8520006bf64d8520006bc64d852007ef661d8520004ff75d852002cfe75d8520004fd75d852002cfc75d8520024fe74d8520004fd74d8520024fc74d852001cfe73d8520004fd73d852001cfc73d8520034fd72d852000cfc72d8520066ee32d8520006ed32d852007ef621d8520066f521d8520034fe70d8520014fd70d8520034fc70d85200067f50d852007ef710d8520005bf745852008dbc7458520006bf6458520006bc645852007ef461585202bdfb7058520004ff7650520004fe7650520004fc7650520006bf6450520026bc6450520015ee725052018fae425052000ef66150520004ff764c520004fe764c520004fc764c5200057f754c5200957c754c520006bf644c52017ebc644c520015ee724c52007fd4314c520035ec764852000eec7648520034ec76485202b6ef65485202b6ed6548520005ef7448520005ed7448520007af6448520166ee6448520166ec6448520007ac6448520166ac6448520005ef7348520005ed7348520006ef6348520006ed6348520015ef7148520017e77148520007e7614852000eee614852000eec614852007fe4614852007fe64148520007e5414
  | 6 => 0xe76d912008ebe64d9120004ff75d912002cfe75d9120004fd75d912002cfc75d9120006bf54d912008ebe54d9120006bd54d912008ebc54d912001cfe73d9120004fd73d912001cfc73d912008ebf43d9120006be43d912008ebc43d9120034ff72d9120014fe72d9120034fd72d9120014fc72d9120126bf42d9120126bd42d912000cfe71d9120004fd71d912000cfc71d912008ebf41d9120006be41d912008ebc41d9120014fd70d91200067f50d912008ebf40d91202adbe76d9120024be76d9120006bf65d9120006be65d9120006bd65d9120006bc65d9120006be63d9120006bc63d91202efaf72d9120127ac72d9120127ae32d9120006be61d9120006bc61d9120127af21d9120127bb70d91200073f50d9120127bb20d91202efae20d91202efac20d9120127b820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d91202eebf72d9120126be72d9120126bd72d9120126bc72d9120126bf52d9120126be52d9120126bd52d9120126bc52d9120126bf32d9120126be32d9120126bd32d9120126bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006be31d9120006bc31d9120126bf21d9120126be21d9120126bd21d9120126bc21d9120126bf70d91202eebe70d9120126bd70d91202eebc70d9120006bf50d91200063f50d91202eebe50d9120006bd50d91202eebc50d9120006bf30d91202eebe30d91202eebc30d9120126bf20d91202eebe20d91202eebc20d9120006bf10d91202eebe10d91202eebc10d912008ebc64591202e5fb7059120004ff755912002cfe7559120004fd755912002cfc7559120124ff7459120006bf7459120004ff735912001cfe735912001cfc7359120104ff7259120006ef72591200acef7259120004ff715912000cfe715912000cfc71591202e4ff7059120006fb70591200067f5059120125be761912008ebe7619120124be761912008f3e751912008f3d7519120006bf6519120006be6519120006bd6519120006bc651912008f9e731912008f9d7319120006be6319120006bc63191202afae721912008fad72191202debf62191202deaf62191202afae321912008fb6711912008fb57119120006be6119120006bc61191202afaf21191202afb970191202aebf60191200073f50191202afbb20191202dfae20191202dfac20191202afb8201912001cfe76d8d20006bf64d8d20006bc64d8d20086de63d8d20004ff75d8d2002cfe75d8d20004fd75d8d2002cfc75d8d20024fe74d8d20004fd74d8d20024fc74d8d20034ff72d8d20014fe72d8d20
  | 7 => 0x96200067d71596200067c71596200067f41596200067e41596200067c41596200067f31596200067e31596200067c31596201467f21596201467e21596201467d21596201467c21596200367f70596200367e70596200367d70596200367c70596200367f40596200367e40596200367d40596200367c40596200367f30596200367e30596200367d30596200367c30596200367f20596200367e20596200367d20596200367c20596200367f10596200367e10596200367d10596200367c1059620004ff755922002cfe7559220004fd755922002cfc7559220036bf7459220004ff735922001cfe735922001cfc73592200aebf43592200aeef7259220106bf42592200aeef4259220106bd4259220106ec4259220004ff715922000cfe715922000cfc71592200aebf4159220034fe7059220034fc70592200367f50592200367d5059220036be4059220036bc4059220036ef2059220036ed2059220004ff7558e2002cfe7558e20004fd7558e2002cfc7558e20004ff7458e20024fe7458e20024fc7458e20036df7358e200a6de4358e20006ef4258e200c6ec4258e200c6df3258e200c6dd3258e20004ff7158e2000cfe7158e2000cfc7158e200a6df3158e20034fe7058e20034fc7058e200367f5058e200367d5058e20036de3058e20036dc3058e20036ef2058e20036ed2058e20004ff7650e20034fe7650e20004fd7650e20034fc7650e201e67e6550e200067d6550e20026be6450e20006bd6450e2001ede6350e20006dd6350e20005ef7250e20015ec7250e201dfac4250e20004ff755862002cfe7558620004fd755862002cfc7558620004ff7458620024fe7458620024fc7458620004ff735862001cfe735862001cfc7358620006ef425862003eec4258620036f7715862009ef6415862009ef6315862009ef6215862003ef52158620034ff7058620034fe7058620034fd7058620034fc70586200367f50586200367d5058620036ef2058620036ed2058620036f61058620036f41058620004ff7650620004fd7650620034fc765062019e7e65506200067d6550620026be6450620006bd6450620005ef7250620015ec725062018fac425062000ef66150620006f56150620004ff764c620004fd764c620034fc764c6200057f754c6200b57c754c6201867e654c6200067d654c62001ede634c620006dd634c62000ef6614c620006f5614c62009fd4314c620035fb76502202f6fb76502200377a6550220037796550220037bb7450220037bb6450220026fa6450220036f86450220037b864502200afbb4350220007b943502200afeb7250220015fa7250220015f87250220107e87250220015e87250220107bb42502200afeb42502200afab4250220107b94250220107e842502200afbb4150220007b94150220024f
  | 8 => 0x5df724c53001ddf714c53001fd7714c530007d7614c53000ede614c53000edc614c5300bfd4614c53000ed4614c5300bfd6514c530317d5514c530007db704c530035de704c530035dc704c530007d8704c53001edf604c53001fdb604c5303175f504c530317da504c530317d9504c5300bfd7104c530004ff7648530004fe7648530004fc764853001dde7348530005dd7348530016ee6248530007cd324853002e7f765413014e7e765413014e7d765413002e7c76541300067f64541301567e64541300067d64541301567c64541300075f735413014f5c73541300367f635413014f5e43541300075d43541300067f62541301467e62541301467c625413014f5f32541300075d32541300067f615413013e7e615413013e7c615413014f5f31541300075d31541300357f70541300d77b70541300367f605413030f7b40541300377a405413003778405413014f7b30541300375e30541300375c30541300377830541303077b20541300377a20541300377820541302ff7b10541300377a10541300377810541300d77b765413002e7b765413014f78765413002e7876541300077b745413030f7a745413000779745413030f7874541300077b645413030f7a645413000779645413030f78645413014f7b73541300075b735413014f7a735413014f79735413014f78735413014f5873541300377b63541300367b63541300375b635413014f7b435413014f7a435413014f5a435413014f79435413000759435413014f7843541300077b72541303077a72541300077972541303077872541300077b62541303077a625413000779625413030778625413030f7b42541303077a425413000779425413030778425413014f7b325413014f5b325413014f7a325413014f79325413000759325413014f7832541300077b71541302ff7a71541300077971541302ff7871541300077b61541300067b61541302ff7a61541300077961541302ff78615413030f7b41541302ff7a41541300077941541302ff78415413014f7b315413014f5b315413014f7a315413014f79315413000759315413014f7831541303077b21541302ff7a21541300077921541302ff782154130024ff765013001cfe765013010cfd765013001cfc7650130006bf6450130026bc6450130005df735013001ddc73501300079d4350130005ef72501300c5ec72501300077950501300067f74596200067e74596200067d74596200067c74596200067f73596200067e73596200067d73596200067c73596200067f43596200067e43596200067c43596201467f72596201467e72596201467d72596201467c72596201467f42596201467e42596201467d42596201467c42596201467f32596201467e32596201467d32596201467c32596200067f71596200067e715
  | 9 => 0xf43d913012ebd43d9130014fe72d9130004fd72d9130014fc72d9130006be42d91300cebc42d913012edf32d913000cfe71d9130004fd71d913000cfc71d913001cfd70d91300067f50d91300cebf40d91300cebc6459130005ef72591300c5ec725913034dfb7059130004ff755913002cfe7559130004fd755913002cfc755913012cff7459130006bf745913010cff7359130006df7359130004ff7259130006ef7259130004ef7259130014fe7259130014fc7259130006ec7259130014ec725913010edf3259130004ff715913000cfe715913000cfc71591300cebf415913034cff7059130006fb70591300067f5059130035dc7650d30026dc7650d30034dc7650d3001ddf7450d3001f9f7450d300079f6450d30026de6450d30026dc6450d300cf9c6450d300cf9e5450d3033f9d5450d30005df7250d303479e4250d300cf9c4250d30005df7150d300cf9f4150d30007db7050d30035de7050d30035dc7050d30007d87050d3001edf6050d3001fdb6050d3033f5f5050d3033fda5050d3033fd95050d300cf9f4050d30014fe76d89300c6ee62d8930004ff75d893002cfe75d8930004fd75d893002cfc75d8930024fe74d8930004fd74d8930024fc74d8930034fd73d8930014fc73d89300a6de43d8930006dd43d8930006ef42d89300c6ec42d89300c6ee32d89300a6ed32d893000cfe71d8930004fd71d893000cfc71d893001cfd70d89300067f50d89300c6ef20d8930005bf74589300cdbc74589300c6ec6258930335fb7058930004ff7650930004fe7650930004fc765093001dde73509300c7ac4250930035dc764c930016dc764c930034dc764c930005df744c930005dd744c930006df644c930006dd644c93001ddf724c93001fcf724c930007cf624c930016de624c930016dc624c9300c7cc624c9300c7ce524c930327cd524c93032fcf424c9300c7cc424c930005df714c9300c7cf214c930007db704c930035de704c930035dc704c930007d8704c93001edf604c93001fdb604c9303275f504c930327da504c930327d9504c9300c7cf204c93000cfe76d85300bef661d8530004ff75d853002cfe75d8530004fd75d853002cfc75d8530024fe74d8530004fd74d8530024fc74d8530034fd73d853000cfc73d8530014fe72d8530004fd72d8530014fc72d8530006f751d85300bef451d85300bef631d853006ef531d853001cfd70d85300067f50d8530006fa50d8530006f950d85300bef710d85300057f75585300d57c75585300bef4615853031dfb7058530004ff7650530004fe7650530004fc7650530026be6450530006bd645053001dde73505300079d4350530035dc764c53000edc764c530034dc764c5300075f754c5303175c754c530316df654c530316dd654c530005df744c530005dd744c530
  | 10 => 0x9230036bf745923010ebf435923010ebd4359230004ff7259230006ef7259230004ef7259230014fe7259230014fc7259230006ec7259230014ec72592300f6bf4259230004ff715923000cfe715923000cfc71592300f6bf4159230034fe7059230034fc70592300367f50592300367d5059230036be4059230036bc4059230036df3059230036dd3059230004ff7558a3002cfe7558a30004fd7558a3002cfc7558a30004ff7458a30006bf7458a30004bf7458a30024fe7458a30024fc7458a30006bc7458a30024bc7458a30036ef7258a300eeee4258a300eeee3258a30086ed3258a30004ff7158a3000cfe7158a3000cfc7158a300eeef2158a30034fe7058a30034fc7058a300367f5058a300367d5058a30036df3058a30036dd3058a30036ee2058a30036ec2058a30004ff7650a30004fd7650a30034fc7650a301ce7e6550a300067d6550a30026be6450a30006bd6450a30016ee6250a30006ed6250a300efac4250a30004ff755863002cfe7558630004fd755863002cfc7558630004ff7458630024fe7458630024fc7458630004ff7258630014fe7258630014fc7258630036f771586300e6f641586300e6f63158630046f531586300e6f62158630034fe7058630034fc70586300367f5058630036fa50586300367d5058630006f95058630036df3058630036dd3058630036f61058630036f41058630004ff7650630004fd7650630034fc765063019e7e65506300067d6550630026be6450630006bd645063000ef66150630006f56150630004ff7648630004fd7648630034fc764863016e7e65486300067d6548630016ee6248630006ed624863000ef66148630006f561486300377b76542300357b765423036e7b76542300077b74542303677a74542300077974542303677874542300377b64542300377a645423003779645423003778645423014f7b735423014f7a735423014f79735423014f78735423014e79635423014f7b435423014f7a435423014f79435423014f7843542300077b725423035f7a725423000779725423035f7872542300377b62542300377a62542300377962542300377862542303677b425423035f7a425423000779425423035f78425423014f7b325423014f7a325423014f79325423014f7832542300077b71542303577a71542300077971542303577871542300377b61542300377a61542300377961542300067961542300377861542303677b41542303577a415423000779415423035778415423014f7b315423014f7a315423014f79315423014f78315423035f7b21542303577a2154230007792154230357782154230024fe76d91300cebe64d9130004ff75d913002cfe75d9130004fd75d913002cfc75d9130034ff73d913001cfe73d9130034fd73d913001cfc73d913012eb
  | 11 => 0x2cfe75d8540004fd75d854002cfc75d8540034fd74d854000cfc74d854001cfe73d8540004fd73d854001cfc73d8540076bf43d8540006bd43d8540014fe72d8540004fd72d8540014fc72d85400fef641d8540076f541d8540024fd70d85400067f50d85400fef710d8540005ef7258540105ec7258540006ef6258540006ec62585400fef4615854037dfb7058540035bc765054000ebc7650540034bc7650540376bf6550540376bd6550540005bf7350540006bf6350540005bf7250540007af625054018ebe625054018ebc6250540007ac625054018eac6250540025bf7150540027b77150540007b7615054000ebe615054000ebc61505400ffb461505400ffb62150540007bb7050540035be7050540035bc7050540007b87050540026bf6050540027bb60505403773f50505400ffb71050540004ff764c540004fe764c540004fc764c5400057f754c5401157c754c540025be744c540005bd744c540006ef624c540176ec624c5400ffd4314c540004ff7648540004fe7648540004fc7648540025be7448540005bd7448540006ef6248540016ec6248540167af424854000ef66148540007b5414854002e7f76541401567e76541401567d765414002e7c76541400073f74541401573c74541400367f64541400067f635414014e7e635414014e7c63541401573f43541400073d43541400067f62541400076f62541400066f62541401467e62541401467c62541400076c62541401466c62541401573f42541400073d42541400067f615414013e7e615414013e7c61541401573f41541400073d41541400357f70541401177b70541400367f60541401577b40541400373e40541400373c40541400377840541400373840541400377a30541400377a20541400377a10541400067f74596300067e74596300067d74596300067c745963014e7f735963014e7e735963014e7d735963014e7c735963014e7f435963014e7e435963014e7d435963014e7c43596300067f72596300067e72596300067d72596300067c72596300067f42596300067e42596300067c425963014e7f325963014e7e325963014e7d325963014e7c32596300067f71596300067e71596300067d71596300067c71596300067f41596300067e41596300067c415963014e7f315963014e7e315963014e7d315963014e7c31596300067f21596300067e21596300067c21596300367f70596300367e70596300367d70596300367c70596300367f40596300367e40596300367d40596300367c40596300367f30596300367e30596300367d30596300367c30596300367f20596300367e20596300367d20596300367c20596300367f10596300367e10596300367a10596300367d10596300367c1059630004ff755923002cfe7559230004fd755923002cfc755
  | 12 => 0xd74d8940014fc74d894001cfe73d8940004fd73d894001cfc73d8940006ef52d8940106ee52d8940006ed52d8940106ec52d8940106ee42d89400aeed42d8940006ef32d8940106ee32d8940106ec32d894000cfe71d8940004fd71d894000cfc71d8940106ef21d8940006ee21d8940106ec21d8940024fd70d89400067f50d8940106ef20d8940105ee76d8940014ee76d8940006ef65d8940006ee65d8940006ed65d8940006ec65d8940397af74d89400afac74d8940006ef63d8940006ee63d8940006ed63d8940006ec63d89400afaf43d8940007ad43d8940006ee61d8940006ec61d89400afaf41d89400afeb70d89400076f50d89400afeb40d8940397ae40d8940397ac40d89400afe840d8940006ef75d8940006ee75d8940006ed75d8940006ec75d8940396ef74d8940106ee74d89400aeec74d89400aeef54d89400aeee54d89400aeed54d89400aeec54d8940006ef73d8940006ee73d8940006ed73d8940006ec73d8940006ef53d8940006ee53d8940006ed53d8940006ec53d89400aeef43d89400aeee43d89400aeed43d89400aeec43d8940006ef71d8940006ee71d8940006ed71d8940006ec71d8940006ef51d8940006ee51d8940006ed51d8940006ec51d89400aeef41d89400aeee41d89400aeed41d89400aeec41d8940006ef31d8940006ee31d8940006ec31d89400aeef70d8940396ee70d89400aeed70d8940396ec70d8940006ef50d89400066f50d8940396ee50d8940006ed50d8940396ec50d89400aeef40d8940396ee40d8940396ec40d8940006ef30d8940396ee30d8940396ec30d8940006ef10d8940396ee10d8940396ec10d8940106ec625894038dfb70589400adee7618940106ee76189401076e75189401076d7518940006ef6518940006ee6518940006ed6518940006ec6518940107ae7418940107ad74189402deef64189402deaf6418940107ce7318940107cd7318940006ef6318940006ee6318940006ed6318940006ec63189402f7af4318940007ad4318940107e67118940107e57118940006ee6118940006ec61189402f7af4118940107e970189402e6ef60189400076f50189402f7eb40189402dfae40189402dfac40189402f7e84018940035bc7650940016bc7650940034bc7650940005bf7350940025bf7250940027af7250940007af6250940016be6250940016bc6250940107ac6250940016ac6250940005bf7150940007bb7050940035be7050940035bc7050940007b87050940026bf6050940027bb60509403873f5050940107af2050940004ff764c940004fe764c940004fc764c940025be744c940005bd744c94001ede634c9400079d434c940006ef624c940016ec624c9401afaf424c94000cfe76d8540006ef62d8540006ec62d85400fef661d8540004ff75d8540
  | 13 => 0x96400367f10596400367e10596400367d10596400367c1059640004ff7558e4002cfe7558e40004fd7558e4002cfc7558e40036df7358e4012ede4358e400cedd4358e40004ff7258e40014fe7258e40014fc7258e40006be4258e400cebc4258e4012edf3258e40004ff7158e4000cfe7158e4000cfc7158e4012edf3158e40034fe7058e40034fc7058e400367f5058e400367d5058e40036bf4058e40036bd4058e40036de3058e40036dc3058e40004ff7558a4002cfe7558a40004fd7558a4002cfc7558a40004ff7358a4001cfe7358a4001cfc7358a40036ef7258a40126be4258a40126ee4258a4008eed4258a40126bc4258a40126ee3258a40004ff7158a4000cfe7158a4000cfc7158a40126ef2158a40034fe7058a40034fc7058a400367f5058a400367d5058a40036bf4058a40036bd4058a40036ee2058a40036ec2058a40004ff764ca40004fd764ca40034fc764ca401b67e654ca400067d654ca40005bf744ca40025bc744ca4001ede634ca40006dd634ca40016ee624ca40006ed624ca40127ac424ca40004ff755864002cfe7558640004fd755864002cfc7558640004ff735864001cfe735864001cfc7358640004ff7258640014fe7258640014fc7258640006be425864004ebc4258640036f7715864011ef6415864004ef5415864011ef6315864011ef62158640034fe7058640034fc70586400367f50586400367d5058640036bf4058640036bd4058640036f61058640036f41058640004ff764c640004fd764c640034fc764c6400057f754c6401357c754c6401867e654c6400067d654c64001ede634c640006dd634c64000ef6614c640006f5614c64011fd4314c640004ff7648640004fd7648640034fc764864016e7e65486400067d6548640005bf7448640025bc7448640016ee6248640006ed6248640127ac424864000ef66148640006f5614864001cfe76d8d4010ede63d8d40004ff75d8d4002cfe75d8d40004fd75d8d4002cfc75d8d40034fd74d8d4001cfc74d8d4010ede43d8d400f6dd43d8d40014fe72d8d40004fd72d8d40014fc72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d400f6bf41d8d40024fd70d8d400067f50d8d4010edf30d8d4010edc6358d40005ef7258d40105ec7258d403a5fb7058d40035bc7650d4001ebc7650d40034bc7650d4039ebf6550d4039ebd6550d40025bf7350d400279f7350d400079f6350d4001ebe6350d4001ebc6350d4010f9c6350d40005bf7250d401debe6250d401debc6250d401deac6250d4010f9f3250d40005bf7150d40007bb7050d40035be7050d40035bc7050d40007b87050d40026bf6050d40027bb6050d4039f3f5050d4010f9f3050d40014fe76d8940106ee62d8940004ff75d894002cfe75d8940004fd75d894002cfc75d8940034f
  | 14 => 0x14d7c73585500075c735855014d5c73585500067f63585500067d63585500057f72585501457e72585501457c725855013d7f715855000777615855013e7e615855013e7c615855013f74615855013e74615855013f7631585503c57f70585500077b70585503c57b70585500567f60585500577b60585500057f76505500057e76505500057d76505500057c765055013d7f74505501573e64505500073d64505500057f735055014d7e735055014d7c73505501573f43505500073d43505500057f72505501457e72505501457c72505503bf3e42505501573c425055013d7f715055015777415055013f3e415055013f3c415055013f74415055013f7621505500057f70505500357e70505500357c70505503ae7f605055019f7b60505501573f405055013f7710505500057f764c5500067f764c5500047f764c5500057e764c5500057d764c5500057c764c5500067c764c5500047c764c5500057f744c5501557e744c5500057d744c5501557c744c55013d7f734c55014f5e634c5500075d634c5500057f724c5501457e724c5501457c724c55013d7f714c55013f76614c55000775614c55014f77314c55013f5e314c55013f5c314c55013f74314c55013f54314c5500057f704c5500357e704c5500077a704c55000779704c5500357c704c5503ae7f604c5501877b604c55014f5f304c55013f77104c5500057f76485500057e76485500057d76485500057c76485500057f74485501557e74485500057d74485501557c74485500057f734855014d7e73485500057d734855014d7c734855013d7f72485501476e62485500076d62485503b76f42485501476c42485501476e32485500076d324855013d7f714855013f76414855000775414855014777214855013f6e214855013f6c214855013f7421485500057f70485500357e70485500357c70485503ae7f604855016f7b60485501476f204855013f7710485501567f74596401567e74596401567d74596401567c74596400067f73596400067e73596400067d73596400067c73596401567f43596401567e43596401567d43596401567c43596400067f72596400067e72596400067d72596400067c72596401567f42596401567e42596401567d42596401567c42596400067f32596400067e32596400067c32596400067f71596400067e71596400067d71596400067c71596401567f41596401567e41596401567d41596401567c41596400067f31596400067e31596400067c31596400067f21596400067e21596400067c21596400367f70596400367e70596400367d70596400367c70596400367f40596400367e40596400367d40596400367c40596400367f30596400367e30596400367d30596400367c30596400367f20596400367e20596400367d20596400367c205
  | 15 => 0xb7058d503f57b7058d500d67f6058d500d77b6058d500057f7650d500057e7650d500057d7650d500057c7650d5014d7f7450d501573e6450d500073d6450d5014d7f7350d501575f4350d5014f3e4350d5014f3c4350d5014f5c4350d500057f7250d501457e7250d501457c7250d503ef3e4250d501573c4250d5014f5f3250d500057f7150d5013d7e7150d5013d7c7150d501573f4150d500057f7050d500357e7050d500357c7050d503e67f6050d501e77b6050d501573f4050d5014f5f3050d501457e76d89501557e74d89500057d74d89501557c74d89500067f64d89500067d64d895014d7e73d89500057d73d895014d7c73d89501467e62d89501476e62d89501467c62d89500076f42d89501476c42d895013d7e71d89500057d71d895013d7c71d89500357e70d895002d7d70d89500b67f60d89500b77b60d89501476f20d89500057f74589500073f74589500053f74589501557e74589501557c74589500073c74589501553c74589500067f64589500067d64589500057f735895014d7e735895014d7c73589501457f72589500076f62589501467e62589501467c62589501476c62589501476e32589500057f715895013d7e715895013d7c71589501476f21589503dd7f70589500077b70589503dd7b70589500967f60589500977b60589500057f76509500057e76509500057d76509500057c76509501457f74509500057f735095014d7e735095014d7c73509501457f72509501576f42509501473e42509501473c42509501476c42509501472c42509500057f715095013d7e715095013d7c71509500057f70509500077b70509500057b70509500357e70509500357c70509500077870509500357870509503ce7f60509501cf7b60509501573f40509501476f20509500057f764c9500057e764c9500057d764c9500057c764c9500057f744c9501557e744c9500057d744c9501557c744c9501457f734c95014f5e434c9500075d434c9501457f724c9501476e624c9500076d624c9503d76f424c9501476c424c95014f6f324c9501475e324c9501475c324c9501476c324c9500057f714c95013d7e714c95013d7c714c9501476f214c9500057f704c9500357e704c9500357c704c9503ce7f604c9501b77b604c95014f5f304c9501476f204c95013d7e76d85501557e74d85500057d74d85501557c74d855014d7e73d85500057d73d855014d7c73d85500067f63d85500067d63d85501457e72d85500057d72d85501457c72d855013e7e61d855013f7661d855013e7c61d85500077731d855013f7431d855005f7b70d85500357e70d855002d7d70d855005e7f60d855005f7b60d855013f7710d85500057f74585501557e74585501557c74585500057f73585500075f73585500055f735855014d7e7358550
  | 16 => 0xc921007cf634c92101eee634c92101eec634c92115fcc634c92115fce434c921007cd434c921007e7714c92100dee714c92100dec714c9211a7e4714c921016ef614c921017e7614c9211a7e6414c921005ef704c92140f6f504c92115fcf304c9211a7e7104c921015f47650521026f47650521014f4765052100df7745052100fb77450521007b76450521026f66450521026f46450521167b46450521167b65450521407b55450521167b74350521007b54350521007e77250521015f67250521015f4725052118fe4725052100ef7625052100fe7625052118fe65250521407e55250521167e7425052118fb6425052118fb4425052118fe4425052118fa4425052118fe63250521007e53250521005f77050521407775050521167b7405052118fe72050521034fe76d8121004ff75d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d812101cfe73d8121004fd73d812101cfc73d812100cfd72d81212beee32d8121006ed32d8121014fd71d8121256f641d8121006f541d81210067f50d81212befa20d8121256fa10d812116d7e75981210057d7598121006fb6098121005bf7458121165bc745812116d7e75181210057d7518121165be7418121005bd741812115dde7318121005dd7318121036fa6018121006f960181211557e76d91501567e64d91501573e64d91501563e64d91501567c64d915014d7e73d91500057d73d915014d7c73d91501457e72d91500057d72d91501457c72d91500073e42d91501573c42d915013d7e71d91500057d71d915013d7c71d91500357e70d915002d7d70d91501367f60d91501377b60d91501573f40d91501557f74591500073f64591501567e64591501567c64591501573c64591500057f735915014d7e735915014d7c73591501573f43591500057f72591500076f72591500056f72591501457e72591501457c72591500076c72591501456c72591500057f715915013d7e715915013d7c71591501573f41591503fd7f70591500077b70591503fd7b70591501167f60591501177b605915014d7e76d8d501557e74d8d500057d74d8d501557c74d8d5014e7e63d8d5014f5e63d8d5014e7c63d8d501457e72d8d500057d72d8d501457c72d8d5013d7e71d8d500057d71d8d5013d7c71d8d500075e31d8d5014f5c31d8d500df7b70d8d500357e70d8d5002d7d70d8d500de7f60d8d500df7b60d8d5014f5f30d8d500057f7458d501557e7458d501557c7458d5014d7f7358d500075f6358d5014e7e6358d5014e7c6358d5014f5c6358d5014e5c6358d500057f7258d501457e7258d501457c7258d500057f7158d50007777158d50005777158d5013d7e7158d5013d7c7158d50007747158d5013d747158d5014f5f3158d503f57f7058d500077
  | 17 => 0x4fd72d8131014fc72d813101cfd71d81310067f50d813131efa30d813125efa10d81311857e75981310057d75981310067f65981310067c65981310e7d43198131006fb60981310057f75581311857c75581310067f65581310067c65581310bfd431581311857e75181310057d75181310067f65181310067c651813117dbe7418131005bd7418131175ee7218131005ed721813120fd43118131036fa6018131006f96018131024fe76d9121166be64d9121015ee72d912100ded72d9121167af42d9121004ff75d912102cfe75d9121004fd75d912102cfc75d91211bcfd74d912101cfe73d9121004fd73d912101cfc73d9121166bf43d912100cff72d912100cfd72d9121446ed72d912100ced72d9121456bf42d9121166ef42d9121456bd42d9121456ec42d9121014ff71d9121014fd71d9121446bf41d9121446bd41d9121034fe70d9121004fd70d91210067f50d9121166bc40d9121456ef20d9121446f710d9121024ff7659121166bc645912143def725912118fac425912144df77159121004ff755912102cfe7559121004fd755912102cfc7559121444ff7459121006bf7459121004ff735912101cfe735912101cfc735912143cff7259121006ef7259121166ef425912118ebe425912118ebc425912118eec425912118eac42591211bcff7159121006f77159121004ff7059121034fc70591210067f5059121166bf405912118eef20591211bef7105912101cfe76d8d2115ede63d8d21004ff75d8d2102cfe75d8d21004fd75d8d2102cfc75d8d21024fe74d8d21004fd74d8d21024fc74d8d211a4fd73d8d2100cff72d8d2100cfd72d8d21436ee52d8d21006ed52d8d21006ef42d8d21436ec42d8d21436df32d8d21436dd32d8d21014ff71d8d21014fd71d8d21426df31d8d21426dd31d8d21034fe70d8d21004fd70d8d210067f50d8d21436ef20d8d21426f710d8d2101cff7658d210057f7558d2116d7c7558d2115edc6358d2141def7258d2142df77158d21004ff7558d210067f7558d210047f7558d2102cfe7558d21004fd7558d2102cfc7558d210067c7558d2102c7c7558d21004ff7458d21024fe7458d21024fc7458d21424ff7358d21006df7358d2141cff7258d21006ef7258d21176ee5258d21006ed5258d21006ef4258d21176ec4258d211a4ff7158d21006f77158d21004ff7058d21034fc7058d210067f5058d2115edf3058d21176ef2058d211a6f71058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21026bc6450d21005ef7250d21015ec7250d211dfac4250d2100dec764c92101eec764c92100cec764c921415ef754c921415ed754c92140eef654c92140eed654c921165ee744c921165ec744c9211aeee644c9211aeec644c921015ef734c921017cf734
  | 18 => 0xf72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067c42d95314967f32d95314967e32d95314967d32d95314967c32d953148e7f71d953148e7e71d953148e7d71d953148e7c71d953148e7f41d953148e7e41d953148e7d41d953148e7c41d953148e7f31d953148e7e31d953148e7d31d953148e7c31d953148e7f21d953148e7e21d953148e7d21d953148e7c21d95310067f70d95310067e70d95310067d70d95310047d70d95310067c70d95310067f40d95310067c40d95314967f30d95314967e30d95314967d30d95314967c30d95310067f20d95310067c20d953148e7f10d953148e7e10d953148e7d10d953148e7c10d9531024fe76d91310067f65d91310067c65d913117ebe64d9131175ee72d9131005ed72d9131477d431d9131004ff75d913102cfe75d9131004fd75d913102cfc75d91311d4fd74d913100cff73d913100cfd73d9131486bf43d9131486bd43d9131014fe72d9131006ee72d9131014ee72d9131004fd72d9131006ed72d9131004ed72d9131014fc72d913101cff71d913101cfd71d9131476bf41d9131476bd41d9131034fe70d9131004fd70d91310067f50d9131486df30d9131476f710d9131024ff76591310057f75591311857c75591310067f65591310067c655913117ebc645913146ddf735913147df771591311d7d43159131004ff75591310067f75591310047f755913102cfe7559131004fd755913102cfc75591310067c755913102c7c7559131474ff7459131006bf745913117ebe5459131006bd545913146cff7359131006df7359131004ff7259131014fe7259131014fc7259131006be425913117ebc42591311d4ff7159131006f77159131004ff7059131034fc70591310067f505913117ebf4059131196df30591311d6f71059131014fe76d89310067f65d89310067c65d893117dbe74d8931005bd74d8931176ee62d893141fd431d8931004ff75d893102cfe75d8931004fd75d893102cfc75d8931024fe74d8931006be74d8931024be74d8931004fd74d8931006bd74d8931004bd74d8931024fc74d893100cfd73d8931176ee32d8931466ed32d893101cfd71d893141eef21d8931034fe70d8931004fd70d89310067f50d8931466df30d893141ef710d89310057f75589311857c75589310067f65589310067c6558931176ec625893145df771589311a7d43158931004ff7650931004fe7650931004fc76509310067f65509311ce7c6550931177ac42509311bfd43150931034fe76d81311857c75d81310067f65d81310067c65d813125fd431d8131004ff75d81310067f75d813102cfe75d8131004fd75d813102cfc75d81310067c75d813102c7c75d8131024fe74d8131004fd74d8131024fc74d813100cfd73d8131014fe72d8131
  | 19 => 0x8132006fb6098132005bf74581321adbc74581321b57e75181320057d75181321adbe7418132005bd74181321a5f67118132005f57118132036fa6018132006f9601813201cfe76d8d41196de63d8d41004ff75d8d4102cfe75d8d41004fd75d8d4102cfc75d8d4100cfd74d8d414cebe54d8d41006bd54d8d41196de43d8d414cedd43d8d41014fe72d8d41004fd72d8d41014fc72d8d41006be42d8d414cebc42d8d41024fd71d8d4146edf31d8d41034fe70d8d41004fd70d8d410067f50d8d414cebf40d8d4146ef710d8d410057f7558d4119d7c7558d41196dc6358d414c5f77158d4100dbc7650d4101ebc7650d4100cbc7650d414bdbf7550d414bdbd7550d414b6bf6550d414b6bd6550d41025bf7350d410279f7350d410079f6350d4101ebe6350d4101ebc6350d411979c6350d4118dbe7250d4118dbc7250d411debe6250d411debc6250d411979f3250d41007b77150d4100dbe7150d4100dbc7150d411d7b47150d41026bf6150d41027b76150d411d7b62150d41005bf7050d414b73f5050d411979f3050d411d7b71050d41014fe76d8941025be74d894100dbd74d894118eee62d894118fae42d8941004ff75d894102cfe75d8941004fd75d894102cfc75d894100cfd74d894143ebd74d894100cbd74d894101cfe73d8941004fd73d894101cfc73d894118ebe42d894118eee42d89414aeed42d894118ebc42d894118eee32d8941024fd71d894143eef21d8941034fe70d8941004fd70d89410067f50d89414aebf40d894118eec20d894143ef710d894118eec625894118fac42589414a5f77158941004ff764c941004fe764c941004fc764c941005bf744c941025bc744c9410079d434c941006ef624c941016ec624c94118fac424c941034fe76d8141004ff75d814102cfe75d8141004fd75d814102cfc75d814100cfd74d814101cfe73d8141004fd73d814101cfc73d814137ebf43d8141006bd43d8141014fe72d8141004fd72d8141014fc72d8141024fd71d8141266f621d81410067f50d814137efa40d8141266fa10d814119d7e75981410057d7598141006fb6098141005ef725814118dec725814119d7e75181410057d7518141195de7318141005dd731814118dee7218141005ed7218141036fa6018141006f9601814149d7e76d95311867e76d953102c7e76d95310067e64d95310067c64d953148f5f73d953148f5c73d95310067e62d95310067c62d95314977771d953148f7471d95314977731d953148f5e31d953148f5c31d953148f7431d953148f5431d95310057d70d95314975f30d953148f7710d95310067f74d95310067e74d95310067d74d95310067c74d953148e7f73d95314967e73d953148e7d73d953148e7c73d95314967f43d95314967e43d95314967d43d95314967c43d95310067
  | 20 => 0x2cfe75d8142004fd75d814202cfc75d8142014fd74d814201cfe73d8142004fd73d814201cfc73d8142024fd72d814200cfe71d8142004fd71d814200cfc71d81420067f50d8142006fa50d8142006f950d814238efa40d81422e6fa20d81421cd7e75981420057d75981422eebf6498142396ef6298142127ac4298142006fb6098142107ac42581421cd7e75181420057d75181422eebf64181421c5de7318142005dd7318142396ef62181422afac42181421bdf67118142005f57118142036fa6018142006f96018142024fe76d91321aebe64d9132015ee72d913201ded72d91321afaf42d9132004ff75d913202cfe75d9132004fd75d913202cfc75d91321dcfd74d9132014ff73d9132014fd73d91324f6bf43d91324f6bd43d913201cff72d913201cfd72d91324f6ed72d913201ced72d91324e6bf42d91321aeef42d91324e6bd42d91324e6ec42d913200cfe71d9132004fd71d913200cfc71d91321aebf41d9132034fe70d9132004fd70d91320067f50d91321aebc40d91324f6df30d91324e6ef20d9132024ff76591321aebc64591324dddf73591324edef72591321dfac4259132004ff755913202cfe7559132004fd755913202cfc75591324e4ff7459132006bf74591324dcff7359132006df73591321dcff7259132006ef72591321aeef42591321debe42591321debc42591321deec42591321deac4259132004ff715913200cfe715913200cfc7159132004ff7059132034fc70591320067f50591321aebf40591321c6df30591321deef2059132015dc7650d32026dc7650d32014dc7650d3201ddf7450d3201f9f7450d320079f6450d32026de6450d32026dc6450d321af9c6450d321af9e5450d324d79d5450d32007cf7250d32015de7250d32015dc7250d321dfcc7250d3201edf6250d3201fcf6250d321dfce5250d324d7cd5250d321afcf4250d321df9e4250d321df9c4250d321dfcc4250d321df8c4250d321af9f4150d321dfcf2150d32005df7050d324d75f5050d321af9f4050d321dfcf2050d3200cfe76d85321a6f661d8532004ff75d853202cfe75d8532004fd75d853202cfc75d8532024fe74d8532004fd74d8532024fc74d8532014fd73d853201cfd72d853242eee52d8532006ed52d8532006ef42d853242eec42d85321a6f631d85321a6f621d8532034fe70d8532004fd70d85320067f50d853245edf30d853242eef20d85320057f75585321b57c75585321a6f46158532034fe76d8132004ff75d813202cfe75d8132004fd75d813202cfc75d8132024fe74d8132004fd74d8132024fc74d8132014fd73d8132336de43d8132006dd43d813201cfd72d813200cfe71d8132004fd71d813200cfc71d81322d6ef21d81320067f50d8132336fa30d81322d6fa20d81321b57e75981320057d759
  | 21 => 0xe00a000000c0000070008008002000001000c0000040028004006001002000c0100000000028002000001800000c0000068070006008000001800200500000000000000000014002000000000000200a001000400000000680000260010000030000007000000800000000100200020080068000000001001001c000001000800000400b0020000000000000000400000000000000140010008004000001001800c0160140038004008000014fe76d8943025be74d894301dbd74d89431deee62d89431dfae42d8943004ff75d894302cfe75d8943004fd75d894302cfc75d894301cfd74d89431debd74d894301cbd74d8943024fd73d89431debe42d89431deee42d89431debc42d89431deee32d894300cfe71d8943004fd71d894300cfc71d89431deef21d8943034fe70d8943004fd70d89430067f50d89434febf40d89434eedf30d89431deec20d89431deec62589431dfac425894300cfe76d85431d6f661d8543004ff75d854302cfe75d8543004fd75d854302cfc75d854301cfd74d85434c6be54d8543006bd54d8543024fd73d8543014fe72d8543004fd72d8543014fc72d8543006be42d85434c6bc42d85431d6f641d85431d6f631d8543034fe70d8543004fd70d85430067f50d85434c6bf40d854347edf30d85430057f75585431e57c75585431d6f46158543034fe76d8143004ff75d814302cfe75d8143004fd75d814302cfc75d814301cfd74d8143024fd73d8143014fe72d8143004fd72d8143014fc72d814334edf32d814300cfe71d8143004fd71d814300cfc71d81433a6bf41d81430067f50d81433a6fa40d814334efa30d81431e57e75981430057d7598143006fb6098143005ef72581431ddec72581431e57e75181430057d75181431ddee7218143005ed72181431d5f67118143005f57118143036fa6018143006f9601814301cfe76d8d421c6de63d8d424dfac42d8d42004ff75d8d4202cfe75d8d42004fd75d8d4202cfc75d8d42014fd74d8d421c6de43d8d42506dd43d8d42024fd72d8d42506ef42d8d424debe42d8d424debc42d8d424deec42d8d424deac42d8d424dedf32d8d4200cfe71d8d42004fd71d8d4200cfc71d8d42034fe70d8d42004fd70d8d420067f50d8d42506bf40d8d424deef20d8d421c6dc6358d424fdef7258d421dfac4258d4200cfe76d854244fac42d85421bef661d8542004ff75d854202cfe75d8542004fd75d854202cfc75d8542014fd74d854201cfe73d8542004fd73d854201cfc73d8542024fd72d85424a6ef42d854244ebe42d854244ebc42d854244eec42d854244eac42d85421bef641d85421bef621d8542034fe70d8542004fd70d85420067f50d85424a6bf40d854244eef20d854218fac42585421bef46158542034fe76d81422e7ac42d8142004ff75d8142
  | 22 => 0x8014000017000800000201700180000200080000000000002000000000e0000000004004006000000c00200400300140140000000000000004007000400e003000802000c000000000c00800800180000000080040000000000001000000000000080040020040080008000008003800401600300480000000000000004004006000000c000002004001800e0060000000006004004000800000500000480000000000000008000003801001c001002000801a00200080080020070000010002008000800000000500180000060070000000000003001800400c0010040000000008000000c0060020000024028001000000000c0060010020004001006800800800000180240140000060020008005000000400c000000000c0340100000004000007000000000000000180280080050018004000000000000400c00300000000080020000004000007002000000a00000000340060020008000002002001000000e00b000000c01401300080040020020010018006000004800800000000000500000030000004000001002800401400400280000020000048014002004002800c006002001801400c000001000400600100080000000000048000002001002803400000100200000000000000000008008000800000a009005000400a000002801000000100000000100010020000000000000801c00200100c000400600800080040000000050018000000000000400201d00000000020000000000000000000800c00c0010038010022000001800800e0020000000006004002805800000200080180040000098000000001005001000000100000040000000098004000003000000000200300180140000000000000000001002800000000c0000000004003000801800000c0010000016005004000400400400080040040000000000014000002800000a001003000000200100080140000000000000002000000800c000004003000400a002000805800c00000180300000180088020004001003000c0220000000040004002001000c00000d000000400c000000000400000500280140040020038000000000000000800000300000040000000018014000000007001401c008000002c004000008005801800200080100000000030000008001000003c000000000000000a000000000000200100080a0014008000005400c0000018008004000000000000a0020008000004007001000800000000100b80000040070000000001002000c0040000010004000003000000000000c000000c0000000028000002000006801000000e0048004002000000801800200d0008004016002000000001400400480080020020008000006001005800c03e00100080100000010010004000001000000400c0020000000000001000802000a0010000008
  | 23 => 0x800000072317a2ed8000a2039d8000000c2200003e00001c400031f55a627b0002884b22c212d1800116a4c200013c91a476d00003901f28482ca347dc90bc23a2b4f40fe07d16827582520000000000be8000000325c00033c4bb1cd9972a502818000a1406b0fe000000000000037980008ca32f80000007d6000000000094200000015b4b0e5b1b97cf84000000148c64400026237aca266d42e1b8fc00015c6c78001b1823000003dd34c0693638000000000079800000098f56cb628000000000345800000000000000000000000000008002001400000200400180240070020004000006000806400600300000000000000000010018001004800400c00a0008068006005000001c000000001000000200000400000040000038000000010003001800000000300000000010010008008000000000000200000100000020020008008004000000005c012003001000400000000000280180090010000002001000000400600c000800000201300000040500040000000008000004001c000000000801000000000200000060010028004002005000000800400e002001c0000080018000004007000800400200f000000c00c0020018004006003000000c00a0000020000004008005001c00c0000008070000000000000400c00100080000040000010004000000000000000e00000500000000020020000002000000000c0120000000018000002001800001a00300800000000010008004000003000000400a00000100140000000000014010008002000000000c0050000008004000800001400100000000060040000000008002001001800400300280400320040038000000001002802c000001000000800e0010000028026002004800c000002000000000200200400040020030000008000000000000400a000000000400400100100040040010010018006001002000800a00000080100060000008000000001000000c006001000800000400000080100000030000018004002002000000c00500000000000100050004008007000800c0060000030008022004000001800801300b802800a00400080000000000000008000001000800800800d0010004002001002803000000200100000000040000004000002001001c0240010008008014001000002c0020040000000002001000004000200b0028010002000000000000400500000080000000008000000004005000001a00200100080160080020000008000000000002a00600200000060010040000000000006002c018002000000000c0050040038000002001800000a00200400000060030040000002003000000400600000300000000060000024004005000000000c002001000800a00400080000040090000000002001000800c00e001008800400a001001800000a000
  | 24 => 0xd660000000000c2d000159462e0000002270000bee423ab9cd7e8bc3e6afcc1cab55000000000000054900007de64300000001eacba0001aa93f20d40cc927527aab6719b8904f8d711f436a4a302f60e882993be00000014310d40004ad07c40008d10001d88000a780001dece5e7f2350155802c35611d800000000074080000000006268000000510334053504c00000000000007180000ad5586000702008c48a79754a27a4d707c06310134000de80ed89c45222ad67a0000b2e84f53b80000ac00053998800000001848000cb4000574800000000000000015c6d101a880015cc8d300023a80003fb0002d740000000002701628000200851453e35b4c235ac00000024d0000000000000000000000000022c11c4000000000119a10500006c034867800000000000006a380000000006e515281dc80d32a00017b800000016fc5fadd86c90000e18bdf4e282e40000ef49aa5c4862000000000000045262c000121a00000000009ec00000036fc7f2dde0c980009a80f166881a00000001c496ac02e00039f2aad49a0002e300016ce3ff00000013767161578001c9e20901c984453a68a000276d20294753436205f000030f99a485e3aa0001f6520a01d6b180000000724d40b754460000000cd9ba4a44075800133a551000000039ccf60000001d105153591e9ccecabe0002edd9ee69353090acd2ce2b0ef9a7d5523b92d483a5200a055f628b09200000000d9914c8c704907f9c000003e2a6ac4880003d48000000000439818c0003540000000000ad460380010240000000000fb460801f125000074a62f0000b9471c0000f740003801391f3c99cd2e1ec0454e4e0000c41974d92000434000161e0dc2659530bb86f92d8850d63c73560900000000005cd8a3192a00014c80000004c51d3994828c0e72740001738c2000017608a862b3181458000c5600000018505a500016e4ae490e00022bd7e000005a00000000000000000000aa4000109400000000000018be2e30002bf427c8010aa8734f8636f54100000009320000000b6074931e2d9800010952c37040000006e62c5400000000020e4a4800051f00003b400000016900000003cfa7100f600000000ac00000064180016a203500034e0ad28144e7a8c40c856b517332c000c442f92ac800000048e91e80005e60000b397106980000000a7c0000000000000a1f000287046c00050b0085852cb4513a0219a6cee00aaecd70a5e10001e312588a96c0b9384d42df45c03fd8d63f317480000002dc00038853c00000000000dde000602800000033f3b280009bcc9c0cb80000528df3bb8001b1c000000000000000000012a1046000000000183a0000001ef8000b105310000b748a50240445374bba4fb34183160000e4055da640001e380000004f550d8000c1a000179
  | 25 => 0xe000000000041c31680ae33700031dc00000000030780000002ceaa2800000000000000006880002100d080000001d2d3b000058d800022400000000000000000002cf00000003ae80019be00026e8000000996291127992c9b86cb00006380000002b280002230000ec4f26a172758f5d4322420002b047aa97c1660000e86091485000000078b52b00000002a1000045c000cb50000e8816aac206104404d8a8c30c3670dd216665e1f9cf2a75567fabbc7ec5896e00f097c60005468a29c380794bc10c19c2540182395d37c5521628fb15e00000003590018e7600030c16b80004ca22fcc920001129dad16ee6216a9d6930ede51deaa41ae0b5b0d7911d7020004da8b9d5be491048000000058a24000000cc8760dd2f680008a000026050a0000000000000074e1cc80000000003542dbc0000000000694000b9000000010b600025e04940002ea5e2a5395624ba0002464a90d3c0000000000005479012969642669013b8f34e434da0f3dbd28160e080000007e91aca169c10d522619358028d6a264800171e0000001130618a48000268c000b616ceaa39cb2df1102964000000000000000000002110001474000000000186c0000000ed84c000000000000000000002fc947a84400010f899a6395fc3474fae2b01110000f8e0000002691a32d460899b400000006481ee45900000002c047ee21211b8000000b6800027500000006a80f240006a70000000fc4e3a1f8827cdd053b15e3a14cd4000332b84037e04900000000000c71bbb3e000000000001cc1d881d00000000006dd000000000040d00008340848e9221b880000a1d0000000520c1f08f8d15b6a2bb67634704dc00900028cc00000000005751f4cbf60800000000000001509cb80000000001c840000000000000d6d0002bd169e00024f93b4f1253536c2f50000000000000000075600002780008a818415d400063a0000000000000000151c0000000000564abecd00001170000a0421f8000c6e000000225400048e000000000027046b80000005310000344af2c0c00000012da6b422580000006740000000000d5407a0e9107c86b4111d41ca2887232000004a41932132f810256829339a4bc81ef201ace593c000579800000000066d02f11cec5d0000000c38c6347c0001266d3b043800135ed2f0000000000a9e000000000000000039c174e0000000000000a672c40b6d76892b35b00011048133d9000000042c4a18000000bb53718000000967000104c000e0c637ae78000d5161c96f02a0b1827c8000fe6ca13870ded96c50e0000001836065000202caba000000000035600044c33a800000068792c43f09362efb2ed8841b72570ed0bba6956c38001af000060c85d400058e0001a940004680000001c0e0000000f180008ad255800100ce28149a04000
  | 26 => 0x2df00000001c00ec1a84000caf5a91068efebfe27a000000000000011419900003562e94e36be250932b000000041402b09608706d98000000af20000f649f0c0d53600018660000c6b3c98109ea0000000000a2209c8001b9c3b020a885c5da0000000001822000000000000000000016309d27c4217374c00000000000000000003120000000cfe00000004261a70000f4949440a39d1e90000afe000037cf460000000000d36d9a2f2800000000058c8000000cf50000000ac0191000179c0000ad26427994e879e6fd8001a2256c57a800000000b495000000015a0001ec400000000000000000000000000000000000000000025700024f090e000000000000000000000000000000780000000000000020cb32cd642a800000071500035b0000000000000103e0000000000000ba605f001000000032b9e08e3c3124fd8000bf200023e2a648ced7b0000000000dae2db80980002b800000010fa0004680da0df60532d41f8d06294c0002c30000bce033ae38c622fa43d94f4000e3e23912a9b76d2771380000001630412705c6a96e4eea190f0ada255984e10c0bf45eb02f43d47751a71c5dae67ef65591149e0d76705252c000ca03c21b0c470000639074cb424201298001944a4e4ae051d9821d93798c29ba09b64f60000c6a000000188800000017224d129e0000002930fa88e04ee0a81c4a0004f6b99c000000000267c27ee8b0000000a540000002c454042e174180004fa0f229435740000006420000000af102800010ca0000002d2162402c4f2a3189a6bb14ce00000008591a1a4a000041e41586e4000604202a784f98156000245c00096471605e4000b3e0000f800000000000fd000000000000008766f620938a800021a1608001c6200021e00018ae20b43c21046889fe49086c9428a932bdb5dc000ccd0000000e6001a00037dc5a262561588cd7ee0000b935d03f2d4e3700000000daa0002d69686c0f3898000000db443880000006d6237800184c1e6000000000000000000000000000002d24000778000000000000039f8001d088ff6d3a15c0a4629360092c67c00000029bd89400064481751b0da8645ac75baae1e0000001b480000002c185ca5b34ab930457488e1b08eb465058600006605a85d730599b56a800070d8fd40000000000000000afc0000001ce80000000000000000000000000000000000000000000002de5680000000000070a96f52f24e00000000eea5780003fa0001514e7a0006869301a0e0000002d5d0dc00017fa5200005f6000062400030651c23d916683a1f2a544976e6e0002aec49e43a32380017527011f083f42f0819000000125ed390002d9456e76f441800000000017915f51563b856000000000000001f717fecaa115227c000c680002de009800032
  | 27 => 0x177641d000000000000060b9f6d63e87205c23c1226164665388d172a8b000000080e11d0001c08000335121a4795dc0aa475ac984f237361724b91361d4709b6f82ca00014430941c4000000331471c52025eb0b12385da730236cf2072e00000c560e00000036e08be000000000000039c000000000000000019c988a25d0000001aa67af50801c0c76000000000118000057581508da25a1f180044621c94c613880000000001dc9b600000df01700000004c1000112200000000000000004c69f940002b30000000e449800000000b54b470001400000902000000000000000000000006f84930000000e5a7070000000483000020000000000002b8a96a7c5d634082c0e3c5f507f584eafb00002ec0001d658e0904f360001c884a90bc6ee0ee1d0966200004a8000a5e75e2b9914d9d04100c8010cc3a60029c2af007421b1d48654d043331929e0d02ae631c537f5bba94520c31e0d90000234800011209d00000001300007378d890f2a9a4e98e817bc802509852468023413a2bb51c20c53032b2cdc2e384039ff488266200000000000003731b94bd00000000844000000284000008a3841b580014c60001a9380dcf00000000001218000000000000000000004c0966000472800164270d00000008d800000028a4000000000203000000061900000000000001b700000000002fe8a8c82715f94d998e1b52d700015380d82b500000000006ad0001b9a59f72f33748000003f08000ff26ad3e536d800057151aafed10000056780000000002e39a000005872248ff98740073a028793d600000000019480001b000e00007ae0000001bc0000001b1c14a20000001030000e1240228301f622c000000132600072ab8189980003ba1424b360005e5aea0000ded3e32f65c3a000000000048c9590001a7157ebab568000000000000000003701e811f1cdc000099338b42900a433106249400000018d88fcb9831d000105000002f640831846493b1cb90a05de5cd0441d0400000000005bc000078000000039821e000355400000038c823c0f4000130867c6da68c36b988da82a1569fa49c4ee94d0ca0f98d1e22151a0291bb49bc42b1bac000e73000000190e0c1282800000000061b9dc42507a0000393463282019e80000004346818000734d4d33ab3cc0000000540000ef266e64708f40006e74b813640000000000e600000001970000000c4000000009cc0000000000f56ced0e104dc0040000000f7c000ae20000000b84e7b0de81bc7905306be00000508333df9899ad2a083ac0d1894400029294cc00024e08798a1412b98675959000000000004980000000000000ebe3bc5d70338000000000000000081e000246159a00800032280005b808a15b9a3c28e000000000049c4d92b700000000c500007660000e180000
  | 28 => 0x94c3d4046945c7946593b7241c62246b61f0ea1d14bc95a0aaf553064f0d633a5128a394678e7c204c916d62c899f81e36fe153400040900f23b47a212000001dc0007ff2f4800040c950102360904a60e33f00000000003408000000371000000049a9f7543800000000067882c9b841f76e40000e70d4f14a998d4f600022a800000000000036c459aa52367aa54f427bb2c79b445860000000001ad0000006adfc6be7f610500005887e65d68a1c0000006e887d9c2a0000001af845600063f16bc00071d00f800096e67c4989d1164600057caff4000d863298615934c3400000cc0403390001be80bc0004e914e80000000000001354cfd0001af4546c4f58b146cde083270c9765096a2607d22c8fe200000022d8000b0b1aa80000009ef05b95680005a76c490a9ab81b34dbb8159500000000b2c00080f25c8000000d4b00c000025a4a71d0800000000000011787ac72900018a96f400000022310364a500009d4f7a81c000118c00000064985c1478e4a7330000e9a61000000000000006c28000fbce09508b560fbe1a84e123f4000ddb00016980d8b894262501626000000000131c0000000001b468ac00034200000000000000efa000000000000030f2b6ba3182600000000000000000a60000e7800000000005e0000000000000000000039f8f384db6a28aa490a00000000000000000000d1da54000000000000002d0a41e74c4eb746b126899c6e2f18c174169a7574b3371c000c66099ad14e56d800000680000d3000016802bc38b0000cac000000000000000000011688d59b600000019216da28b00000004f08585f8b21800055e2ae000000000028a2410f440002fe0cc40004fb4aa000081ea2d00000005560005971a1c9aa00014494a40008dc0000000b6c700176125892a0000002ec8c2e0746fc00008949205c12bd8b6a2ee1f4aa58fe8bb03ca15bc190d5f16f0000000dbc0000de922a499460800000055000037fc8ee2e650380000000001ae00011860000000000c140000e38bf000003d2aa1711042c4c0f81714e209900001d216be48f67035fc626dd43bd1e4827447d69b295c00011b0000000d5e000000000000096200012200009526328ae4394000087000000000011400000006b70000000000000000251070c1e1658000000000059dac800001362ba39d5a5abe656aa2d0ea400000024480005eb0c7899c5940fc00010c800002400001f0174ad600035119aa00000000000006580c6379c000dba00000003a000041624a4d2200016b00008f2e185c623f9b3cb4628cb91466400024980005240002bc2b7865a0e30000000000000000000143016800000000000003f028d96dc8cc4cda7d400000032883480008970000000000cbd14da061740b2a03b0d34fdc119636000042a0713fa80015b60000
  | 29 => 0x5fab7e800000004d800000083f5e88001804bcf40b800168472d0000000000000045b4d40000003daa96482c0003b522a8cc08a42c200017940000001d8553e000000338958a00016019ecd44a5a43ba6607887cb73d0e54000000000000000000033d000172c0000000e31b42b4e5fe0000000aa5000021800093a0002680000c473f62dc40009e2142000000000031b12a42005f8708b0c53e496a3db8d2cf30a7a5eaa379bc41e43f8181d8dac245f5b148000b4a49fa184e9e985000000000000034f000091a64d000000108c000000185000000018180000000000002459ca4000417aa155c88ee72380000004e01bf000132a0000000000be0000000147d41c0000000d9000000073400000000005a81e59d0c8494ebac2499400000037bc58c5773b30000000a7100000019921960003650f3288a26825ec00000042f8000000e0f000071800091171b86684c4d012838dd4cc8dc502f80004929681c0b83400094656e95893722da58207b549200047a37108367c8019000000000000007d40002d2453af6c26ab3551285f570c4713819848278c7f00031c40000415dea3bc00029e000068c000e65000000141aa6a000385000000000000000001440001da098ee7d000077912638d0519af10c6307426b0bd688ba419d91380000003e99225590000259000000000039200007203e766c0a9cbbc2293598dc02b0b6b36a81b5134aa36822558000a7f0e90b890d8be028eb1447d49e700000004323bf0000000026000000000000086701d80003e400000000000000000000000000be518f80012169755d184b80003ab00000002963691d31b7c00000000015989d8000000000000000000014e454c0002be21d0000b363b9b0f0aaa6b93698001c820002f783549fa8ce10ea43c4b29722a9b8f40c431a38405b5b204426cd8dfcf4c51e156011c000532000265c1c2ca5000000000000000000d961a00000009b58f80000000001c920000000000000e7c2e0000188c00000000000000cf4468c980000002eb050400000053580640000004d48b257ba0d05ec1ccd78204e000000006edf06dcabe8c8acae46422200000003ff000000025e383959ccee0001e7080865845a00003d800000000000000000000000001bea00000000000000000003071078aea0000a69d1adf427f980c65400000000000001d50000000000aae5390000cfa000532a308d9aac60001cc52f208e4bb800005c00064fab390860006f18000198b1a086800000039406026c472c000343153d1620004b600007fa0000000000000000000219800012b000373c000cc341e816d13ad916c6a090000000484a2788ae000000056d1e200000000013140000000608ba20004b5b0040000005c9849c000000309a13875800000025e800000044219c154eaa836f0ec8
  | 30 => 0x6398000000e775488001b0800000900002d800060580000000006a4000000000021180000000000d517f8d1226f35824f80007fb0f38000d84000128308c0142b600000000000000000000ae0c546fb000000090852e8f0462ae46050ada9012633000089d716c6916ca0dc822000522999c0000003c003280000006d5b275b5ac8511ca7640005045c200000004290000000a5c0000000714d34a1a17880000002f70000001248d9731faf309b409310b17b000000010000001ac0003a61cd16b0486042140400000054400015b05e23d810dd4b6c645c8800138640654487b0bf4000055b984e145833e901b81407910002734eb83636948898e4a9f42e597d4b9e1b100022f93b4000365842819633457000002a42856cc2d799b8cd70000001c0400002580000002a54c195247061326f08000d4c9a13b217551ee1e94428fc800000040d2cb07e0c6e0000001a1600026b8001cd80001fe096cf82030228acf401e75b0001fa8fba47855680000000b02c12a180003de0000000000000000053939600000000004a2c5046c85e84d69c8058b2340000002d68794bb600000000000000000000d74000a6e5e01fb4afc7fa00e000000000058000017140000002a84c807ac5019284f6600000000000006380002f0c01c9f80000a19b6e00020e0000ed80000000000000534000000148660511e00000000003b48000000388249000058451a0000000c5e00000016b1bae27e3589e34a0400000028c8562c7655d3300faaca7240b930c1278e3a9829d38ce8061c0e1c0001fb00028040000000001854f1005818f00000000000000ef800033a16c000118a00037f2bfd3fea4161d80000007860b980018900000000000a5a0000000000000b7751d8001a9400048d9b196f8cd400036bc0000000bf827000000022c014400000000000a8ba859600026494d2e0132a800134a7b60000001cd6be70000288000b925c68684000d2300000000000003902c95bb83ee2ac23cd4169fd0002ca01bc00012f8eed6e05bb00000000000000000f6c00000000035f8000c4e0b72a5ce3e00057ba9700008751b500008c2bb800003f8b2a2eb69f000092ec7a4018000000000000000166e0005829bf162e00000000010f40006beb9a9540cce57612d49f400020117486480000000001146000272000041c00000019994604b62380001aac0000000001392d5b11700011b46c159d00011acb87131b9012aa1cb0001b65c680000000000a2223a09780000003cb000000000088131700000000000002e898b600000028a94c8b9d00000000000000f9b52497ea0a000323c00058b0000001910a2b0000000b34c9b286966105a07e6050000f0ec0055a00009ce00026900007d677c4d3833482e00052a161506868e0000000efc0001880000d749f3
  | 31 => 0x945d2a00000e56000000000000000000000000000000e480003c30dd8d7898c00054d80003086c55be84116c866f33585c4c948d55231ea182a9e80001ea81b2000059a325a985d32c9b39465e0001d28aa800000007680000007fc00032080007d149c9d8c118378000000126029c6b092b0e7233067d02fd984d4368aaf40000000000000196626400000000000000000001ca64af0b3800196229434a0000870000213a2840005924b480003523216922da400000047201809de4a0673a58d73ec1a0e7800000081100027904b00000002d640000001d713c4000aa6133000111e00000037e40000000c70214f9c563096000000000045da93d0d25571240164000c800000d28000000000000000055900003696d8dd60000f713660000000001a28e7232f186493600062180000004d11419f248c0b2906b80000004df4be82680000002312b300000004480b4c00c43967306b97ec48416ba1f87f07d802aac086d825229e1120000dc673c8d21c2e5e000036f40000000000c082841f402d38b52942c76a019e564864e0000000000b800002ee400000028e1111bc80000000000152b27000000000000063380000000005ab0000000ac4295b5d449858d6bc8000d769106ff28fc000b0a00000000009d00db2f9059eaaf1b71bd0be60005de0f3436800000005290fea405cc948400000044912280000006b700000005061a81c24000b95000000030000000000013a20000000001a180000000000c96000000000086c0000000000f78097000000148400000000000005ed0002f1c00096553c80400000000000000a8228147a80000000c40000950088d330000000000ab05331bdd496000091800146e00000039900000004f184f4e2800052f895800044f027b951b1699900016f4000408000067800000000000006020000002619a4cc3d21097ec0000000001d1c000ac71e29859112cad0000000a24a0f140036c0000001a09e95a2ee29698800000070442e16897349fa66790100000004c58000504d2b000150c0001015cbadf925a0000000648000df20001d180001210a7800023068b15a142c000000000000000086f000000000000000007b889a58069116d06009b017d90b51f870f564b940b9c00033980016c0e2200000002d20003281ee93e260c56934616a65b240520a400000000013606fa899625b59c7986b5256a40d8f6e826461fdc4fe0000740001bdc00000000002686f5000069833ad6f5368000000d570000a6105c0004310f407c416b6591538afe00012ab9c40000000000000000d3725c3a1d5f017b326346906a2bd0001c14000d591bb0dd0cb68ae44b2ad55060000002ccc8ac0000000000d2e0006021705b407210a88000bd4c0e013ac0c000ccc400000000060148d1fe0000000000000148e00034900f
  | 32 => 0x14fa00008b2f1800072c00000000000000001bf5a12327000331800000017cb019a000004b000000003a34ef0000216a28182943d946bbf1e0000030c11a6af38696eabbe53f2b4400048b08611d80000005f68000b92000415000000047300031d0f70a2453005508f647460b00000009bf0000000000bc44bfa8000000006cf80018eac18252000000000000000009300003d6b34931243547400002c49ac1b2a730000d2c72d80004804be4f82f5c000e301ad1e059f6b2f31f26213aa00000004c5854dea08429548ca4e33e800014ea3141c1348400034f0be00018aae0b5ca00019c80006ca8000cc200053b0000000000000000000000000038587260000001604000000000000000041f10427380000e600013dc000000388b5816e60611a131a8f14d3a5bb26b41a60003893379292e1f10e06f028099e43e27b938e6f159a26b81ba69047cb2996c40006b921518c000008f09a11a8923103b0507749ca1919b900002201080890000000270958414a11c31080000006e231a054c0000000003265bd8d0544580000005760001b6cab6c0909d8000000754057acc0000b2d00026f400000030da3748cc70b0003a251c684a3752cac00052742e80003066a45e402d9930d0e2350000c820000000d5c73a3b70d680019f200023f0de59e0dd9000000000000019000011f643d27980003aeb380001a0c000ae500000000000004bf14b00000000000000a6e97326e0001b8671a0000000ea2bf968da5d18b800030f0a589fc00000039757c2aaa10f800000045b03517dd5580002120928c88e6d220314d0a40000000000000ae100009a400030d37914fc07e0001cd8000000000393000000093700000000000004ac1b11c7259c45e8000000000443111800000002300000002a861f8001c64d2871d8000af4a70000061cbdc00015f3665a6800047638b812ce7f2cf38d800000033605d08ba4590fd000081cddf0001bb4c7a0c36c19bfc42800007500002d46ae000000055c20f630aae0000000000000000000009107fc0008532fea6680000000000805b4aa9d3bb247d282dc955cb72d502ba11b380000002760000ed4068d7a01115100003530bb9aac564000677b9100006da0001b28302000139b165cb0706008800000007534e99192ba00036612d17d0d420002dec00048c31637cc03690647303259704ea4210e785fc5ff23f825061683612e0380dd83e455b8a5d7d21e21872f4851e4fc0001f90000699174178c000a846899b488dc84519c1dc17de1eb0bb32a551e99133f8419c964cf0000001882851354a0c03448cb2058f4c000000000000000000000000002be00017a800048e0000000000cac08a59f886114416100000000002650000001b4c00051780005447285840d600004a35510000000d934b0b2492bec4
  | 33 => 0xc340003f598c800000023a80007dacb727292080000003da000175e34c146b6c8000b834a98d240003af0f00000000c030000c58ec0c941c78b81244000662000033800013d359400060f3950a90f1e00000000000000006892dc8000bcd0bf000000000000008bc080d2548a256c3360000002ea9c4c00000000004060000000000000bd35032b5d9b286d1be00018f2ae83010ca47b40003991d9c20e00000018b400000000000000000003519b38eb200061a9a14b900003f42310000b4c000000000000008197c4000000000000000000000020ec00012400000000000004070000000a535990000d1a00000027f06e4000000000000000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa7b865c9504404f4f10cb92a088002cee1172541102259c422e4a822000b73815c9504404f6e102b92a088002cee1162541102259c422c4a8220a5e686258950440014f70ca12a0880029e21942541102179421284a822027b7281509504404f6e502992a08809edca1f715411013eb943ee2a822006b7286dc5504400d6e10db8aa08809f5c9db715411013eb83b6e2a822000b7184dc550440016e307b8aa0880035cdcf7154110006b8b9ee2a822000b7182dc550440016e50ea0aa088002dc21d4154110035b943282a822006b7086505504404f6e708a0aa08809fcce114154110227993a282a822000f31745055044001e66c8a0aa088113cc1914154110005b9c1a82a822044f33435055044001e6286a0aa088002dce0941541105279921282a822044f30425055044001ae70e98aa088002dca1d3154110005b843a62a822000d70874c5504400d6e50c98aa08801adc2193154110005b9c2262a822000b71844c5504404f6e70698aa08809fd4e0d315411021fa939a62a822000f51734c55044001ea6c698aa08810fd418d3154110005b9c1262a822000b728748550440016e10e90aa08801adca192154110035b843242a822000b738448550440016e30890aa088002dce0d2154110005b8c1a42a822027b7382485504404fec70490aa08810bd89c92154110007b0b9242a822000f63624855044085ec0c490aa08828fd8d092154110217b021242a822042f62324855044001ec26490aa0880032b1cb6450110034da43a82a022006ab4865054044093b48e4a0a808801aec201415011013e3c3b2a0a02202ae38645414044001ad6e4a82808810b5a1c95050110006b9b8aa0a022000f31415414044001ae702bac60880035c205758c1100363db0aeb1822006d73615d63044001ae482bac608810f5c8c5758c11021eb898aeb1822000d72215d63044001ae2eaa0c60880035c5d5218c110034ea43a629822006ad4864c530440039a8ec98a608801af4201314c11050fa9a8262982205fc7976541304404f8f0eca82608800396d8d504c110006b9b8aa09822000f51315413044001f2286a0a608801af421d314c11000ee843a629822006bd2864c5304400d7a10c98a608800fb4219314c11001f69bb2629822001dd2764c53044003ba0ec98a608800fb41d9314c11000e683b2629822000f53854c53044143ea10a98a608828b74dd5314c110516e8baa6298220a1ed3654c53044143da2ca98a6088002f4e11314c110005e8c22629822000bd3824c530440017a30690a6088003f04c9214c110006563a6c490220068f686dc5204400d3c90e90a408801ab92192148110236d23a2429022006be080485204404f8f0eca8240880034edd150481102269c3a2a09022028e68625412044001ae6e2a824088003d84855048110
  | 1 => 0x106b2a610801b1edcd654c2100372db9aca9842000e5a435953084001cb664b2a610817f96cc5654c2102ff2c98aca9842000e596550d3084001cb2ca992610800237e0d755911001c6e41aeab2220008ef825d564440051d904baac88800a3ba1f725911000657ba0e4b222000c6f72d4164440f38d8e5a82c8880023be0974d8d1001476412e9b1a20008bf845cb634400917908b96c6880171e9d550d8d100072da9aa1b1a2043e5853543634400b0fd0fbaac68800237e0d7558d100047bc0aeab1a200087e871d563440018b8ebb9ac6880031d1d77158d100043f43ea0b1a200587c87d41634400b8f0eb282c6880163e21d5058d100043fc2aeca1a200587c855d943440011df04bb2868800a3b2097650d1001c5e43ac8a1a203baac82591434400117f08baac4880122f21175589100046fc1aeab1220038dc835d5624400917d0fba2c4880032b1d372589100061fba6a0b1220abc3c74d416244001958853b284880022fe11765091000477c12eca122000cac421d942440010ff0abb264880161f215764c9100045fc22ec99220048bc845d932440071d90eb1264880d6ab211624c91000cdac26e4a0a2004ab684d894144155d4885b1282880123d21d6250510005b8c28e0a0a2000bd1831c141441258e8edbaa628824b9518f754c510004f2c16e898a20068f4865d131440075ad0db1a62880026d613724c510005b8c28e098a20019e582dd1214400d1e90cba2428812769109744851001573416c890a20a9ea442d9121440051e90eb22428801a3d2197348510005b8c28e090a2000bd1831c1214404f4f301b22a0882a38ed03645411000537c12c8a822028a6c82591504404f4f301b1aa08801a9e20363541100043fc3ac6a82200587c8758d504404f4f301b12a0880028fe1162541101551e422c4a822006a7686dc5504400d4e90ca0aa088113ccd014154110004ba43a62a822006a74864c55044053ca8c698aa08810fd4cc131541100353a43242a822042f6320485504404f6e103ba2a0880029ee19745411013d3c432e8a822000b6b825d150440856d104ba2a088002dce05745411013db840ae8a8220a8e3a64d915044151c70c8b22a088002dae096454110215b4412c8a822027b7081dcd5044001ea463b9aa0880029ee19735411013d3c432e6a822043d58735cd50440016e702b9aa08809edc205735411036d3d43ec6a82201ba7887d8d5044001cb6e7b1aa08829f961cf63541100353dc0ec6a822006a7981d8d504414dcb663b1aa08829b964c76354110004bdc3ac6a82200a9788758d50440018f70eb1aa0880169ea1d635411002d3c43ac6a822000c788758d504400b0f10eb1aa0881aa9ee0d63541100072dc1ac6a82205fa7b8158d5044001ce702b1aa08809edca05435411013db840ee4a822000
  | 2 => 0xd42501200355643284a024002cac76509404800d75100a1280902bbcad4142501201463c3b2a0a02402ae38645414048051ad0e4a828090003ca50950501201265c3b6c8a024004cb87650d40480419d0edb92809001aea21d4250120016d443a84a024006baa86509404800d7510ca128090013aa219425012002755bb284a024002daa765094048005b50eca128090013aa1d94250120016543b284a024000bab83509404800175702a12809000b3a1d93250120005d4c2264a024000f89434c94048009970eca0a809000b3a1d92150120005d4c2242a024000fa1414854048001958c9b92609001a7321d324c12003566432649824065e8c644c9304800d7910099260900a31e1d9504c1200071db22a09824061e38645413048001cb6c6a8260900a35a1c9504c120007a4992a09824000c3f749d165840014df04ba2cb080029b20974596100353d404e6b2c204ea79809cd65840014ef02b9acb0809e9d20573596100051f420e6b2c2000a3d841cd65840018bae639acb080029ba08735961000536c10e6b2c2027a76811cd65840014eb0239acb0801a9ea00735961005d3cc00e6b2c2000a6e8290d65840014db0521acb0801a9ea0243596100053cc0486b2c2006a7a8010d65840014f30021acb080028fe1172596100051e422e4b2c200087e8710965840010fb0e212cb0800297a0c42596100052ec1884b2c2027a768110965840014eb02212cb0801a9ea0042596100053cc0084b2c2000a3e84cc9658400147b09992cb0801a9ea0332596100053cc0664b2c2006a7a800c965840014f300192cb080023be09755921001476412eab2420028ee87dc964840e58dea1b92c9081cb1b543725921039673886e4b242072ce510dc964840b795ee8392c9080171e9d55058e1000477c12eca1c20028ec825d9438400d1790eb2287080eeab2096450e100346e43ac6a1c20008bf845d5628400917908baac5080122fa1f7458a102ee1fa86e8b14205dc3d50dd162840bb96e21ba2c5081772d4437458a102de57b90e8b14205d8bf845d942840e51df04bb285080038b1096550a100345e43ac8a142002aac82591428400d1d90eb128508012ab2116250a100045fc22ec99420048bc845d9328400d1b90eb1a650801a3b21d624ca101ad56422c49942000a7b865d150840016d704ba2a108142da20974542100053dc32e6a842051d58735cd50840016e702b9aa10809edc20573542100053d43ac6a842051a788758d508400dcb706b1aa10800396dcd635421056f2c39ac6a8420ade5a4358d508415bcb664b1aa1082b396cc563542105672c98ac6a842000e596350d50840014f70cb92a108002cee1172542102959c422e4a842000a7b86509508400d4f10ca12a108143ca10942542100072cb1a64a842000e5b835953084001cb
  | 3 => 0x7b22405daad821cf644800117d0e29ec8900022f61c53d912012557410a7b224000aad8214f644800156d0229ec890002ad60453d91202ed5d400a7b224000ab98014f644804955d0438ec890176ab60871d91200045f438a3b2240008bd87147644800153d0628ec890002a760c51d912012557410a3b224000aad8214764480bb5750028ec890002ae60051d91200045f43863b2240008bd870c7644800147d0a18ec8900028f61431d91201255741063b224000aad820c764480bb5750018ec890002ae60031d91200045fc22eab2240008ef825d564480e58dee5a82c8900022f61e651912000556c14ca32240afab980994644800117f0eb28c890002abe09651912000556c14c63224000aad8298464480b7c5ec5a80c8901572b1c864d8d2039477c12e9b1a40028ec825d3634800117d0fb22c6900022fa1c6458d200045fc22eab1a40048bc845d563480011ef02baac6900063d2057558d200245f43ee8b1a4000cac74dc9634800187ee9a82c6902af0f1d35058d200045fc22eca1a40008ef825d9434800195c843b2869000e2fa1f6450d200246e43ac6a1a4004aae86d9142480bb958edb2284902832b19373509204a656326e2a12405ddab741c142480b71dd0dba264900d72b193744c92003476432e89924035cac645d132480ab55d0db2264901772b1db644c9202de573b0c8992405bcac761913248001d18c9b1a64900d7a3191434c92000656326e29924000ba9841c132480ab958e4326c2900063b20974d85202ec5e436e8b0a40008be87d91614800117d0e322c2900122f210765052000657210eca0a40018be87d91414800917d09bb262900022f613764c52002c3f42cec98a400087d859d93148001878c9baa62900030fdd7644c5200061e3aec898a4000e9431d9131480b71dd0dba242900b32b193744852003476432e890a402ccac645d121480ab55d0db2242901772b1db64485202de573b0c890a405bcac761912148001958c9b9a429001a3b219734852000656322e690a40069e8805cd21480031d90eb1a42900b2ab211634852000752326c290a402cea464505214800175308382429016e8fa1b64541202ef94106c8a82405dc3f70d915048001c76e1b22a0901778e8c364541202ef1d086c8a824072a6f8259150481614f700b22a0901768fa1864541202df17b10c8a8240afe3b6019150480b7e5040322a0900028fe1163541201551e422c6a824000e2c64dc9504800d6d501b92a09001a9b21942541201571632284a824006b6880509504800d4d90c992a0901eb8b1913254120035b440264a824006a7880d85504800d4d90c90aa0901db8b1912154120035b440242a824000bab844ca404806bd50c89948090002eae11219012016754322432024024cac72d91404802b958c9b92809001a6b21
  | 4 => 0x4c0016b10e992a09801ad6a193254130035ac43264a826000b5b844c9504c0016b308992a0980a6d6e09325413014fa5c1264a826060f4a724c9504c001e92e4992a098003d2d893254130307a431264a8260b3f4b424c9504c0c1e9084992a098002d6e053254130307a590a64a826029b5883dc5504c001ab6e7b8aa098003d4cc771541300053dc32e2a826029a78865c5504c0016b706b8aa0980a6d620d7154130006adb9ae2a82605fd70715c5504c0a74f50fb0aa09802e9e21f61541300353cc1ec2a826000e7371d85504c159ce0e3b0aa0982b39c8c7615413056f3898ec2a82600097b87585504c0352f10eb0aa0980a6d6a0d41541300078ca1a82a826000d5b874c5504c0016b50e98aa098002d621d3154130006ac43a62a826006b5a864c5504c00d6b10c98aa098002d6e113154130005acc2262a826000b5b824c5504c0536b70298aa0980a7d4e0531541302ffa938a62a826000f51714c5504c001ea6c298aa09817fd4185315413014dad41a42a826000b5983485504c001e926490aa0980032b1cb6450130034ce43a86a026006a9c8650d404c0d1b18e4a1a809801ae6201435013014e3c3b2a0a02602ae3864541404c001ab6e6a828098003c650d5050130006b5b92a0a026060d6872541404c00187ee93a2cb1001a9ea0274596205953cc04e8b2c4000a6f825d165880514d904ba2cb100029de0573596200053a40ae6b2c4000a3e841cd658800147b0839acb10003175cc735962014537410e6b2c4000a6d821cd65880014ed0239acb100029d60473596200353d400e6b2c4016a79801cd65880514dd0521acb100029b60a43596200353d40086b2c4000a798010d65880014bf06b8acb100029720d71596200051f420e2b2c4000a3d841c565880014bd0638acb100029760c715962014537410e2b2c4000a6d821c565880018eae238acb1001a9ea0071596200b53cc00e2b2c4028a6e8290565880014db0520acb1001a9ea0041596200053cc0082b2c400087e870c565880010fb0e18acb100028fa1031596200051ec2062b2c4028a6e820c565880014db0418acb1001a9ea0031596200053cc0062b2c40008f7815d563880031e902baac7100032b10b7458e200345e43ac8a1c40068dc8758d4388163d1884b1a871000237e0d755862001c6e41aeab0c4000cac42dd1618800d1790eb22831001a3d21d615062055752212c2a0c400587c85dd931880010ff0abb263100161f215764c6200043ec36ea98c400087e8759531880010f90eb2a6310003950c5654c6200346e43ac698c4001ad48158d318800d1e90eb0a631000eb520d614c620005d5c1286a04403bda87250d408800175704a0a81100c76a1c941502200061ebaea9b2240058bf8755364480b787ceda86c8900030f5d475d912012557410e
  | 5 => 0x80171e9d5505863000477c12eca0c60028ec825d9418c00d1790eb2283180c6ab20964506300347a43ac2a0c60008bf845d9218c00917908bb2431801a3b21d624863016556422c490c60068f487585218c0014f70cba2a118002dae09745423035db4412e8a846000a7b865c9508c00167708b92a1181b2ce21172542300053dc3284a846006a7886509508c0d7e5084a12a1180029ee197154230005adc1ae2a846029b58835c5508c0d5ae0e2b8aa1180029ea1d61542303553c43ac2a846006e7381585508c001ce6e2b0aa11829b9c1c561542305373920ac2a8460a6e7231585508c14fce262b0aa11829b9c885615423000738b0a82a846000e7161485508c0011df04baac89800a3b20975591300047bc0aeab2260018f4815d5644c0051dd0fb92c8980032bdd0725913000637b96a0b226079c6c72d41644c00733b09b928698002d66147050d30005e8c08e0a1a6004c9e7450f624c0d1d1884a1ec4980032b10a765093000656210eca1260039cd82dd1324c00d1b90cba264981a363109744c93001567416c899260b7e8c42d91324c0051b90eb226498002d6614704c930005e8c08e099260008ef825d3614c0051d904ba6c2980022fe1172d85300245e422e5b0a6005c7a75543614c001ce6a2a86c29817f9c14550d853000c5e43ac8a0a6031aac82591414c1238b8edbaa629824795187754c530004e6c16e898a60068dc865d1314c00133b09b926298006b5a1b614c530005acc28e098a60068dc865cd214c0534f301b22a0982db8ed03645413000537c12c8a826028a6c82591504c00d4b90ca1aa098187c6d01435413014d3cc06c4a826006a5c864c9504c0c1e9640992a0980a69e6036154130004ae43a62a826006a5c864c5504c04fca8c298aa09817fd4c41315413014dac41ee8a826000a7b865d1504c0534f10cba2a098002d6e0d745413014dac41ae8a826000b6b825d1504c0c16d104ba2a0982db8e99364541305b71c322c8a826000b6b82591504c0c16d104b22a0980a6d6a1f735413014ead43ee6a826006b5a86dcd504c00d6b10db9aa0980a7569db735413014eac3b6e6a826000b5984dcd504c0016b305b9aa098002d66077354130005ad43a86a826000b588750d504c00d6b50ca1aa09801ad6219435413014dadc2286a826029f1b8450d504c0c3e34e8a1aa098003c65d143541300078db2286a826061f186450d504c0016b704a1aa0982d7c6909435413030f8c21286a826000b5b8150d504c0c3e3682a1aa0980a6d620f72541300053dc32e4a826029a78865c9504c00167708b92a098186ce2117254130005adc1ae4a826029b58835c9504c00167708b12a098186ce21162541305a734312c4a826000a7b86509504c0014f10ca12a0980a6d6a0d42541303079421284a826000b5a874c95
  | 6 => 0xad5742063b128000aad840c762500e55d50018ec4a0002ba60031d894000476c3cca3128000aad8499462501715d301328c4a00023be1d651894000557c22ca31280008ed8798c625000155b09318c4a00023be1d63189404dd57420c6312805baae8650c62500b75590ca18c4a0003a3d8d431894000556c24c2312805be2f64d406250137958c5b9a84a000aaba1b6250940396563b6c4a128089cac62dc542500e5b56e438284a00032bd08764c9400345e432e8992803bcac625d13250077d18c4a1a64a000e3ba1f624c94044e563a0c5b0a80018bc845cb61500e51d90db92c2a00023ba1f625854000477438c4b0a8000cac62dcd41500b717d0db9282a00c72b18b725054018d57436c4a0a8072cac76d8941500b795cec31282a016f2b1d8625054000752316c2a0a8000ba9821c141500051dd05bb262a00023b60b764c54002c3f42cec98a800087d859d931500018d8c5baa62a001a2f219744c54000656312e898a80069b8805d131500018deebb1262a00031b1d7624c5400076218ec498a80028ec821d9215000195e843b242a001a2f219744854018e56312e890a80018ee87d892150063d48c4a0a42a00ab0f9db745414000716316e8a828006b3a80dd1505000d4790ca1aa0a01f78b18943541400359c40286a82805ba6e86d8950500e5e5081b12a0a00039adc3625414039735186c4a828072e6a10d8950500b7c5ec8312a0a02c39ad8062541402df94200c4a828006a3c865095050051c58c4a12a0a001ace20142541400351e43282a828077e2c62505505000d67100a0aa0a00030fdd2745963000537c12e8b2c6000a6c825d1658c00147f08b92cb180028f21172596300043f43884b2c600087d87109658c0534bd06212cb180029760c42596300053b40884b2c6000a7581109658c00d4f500212cb180029e60042596300353d404e2b2c603fa79809c5658c0014bf06b8acb180a69720d71596300051f420e2b2c6000a3d841c5658c0534bd0638acb180029760c715963000537410e2b2c6000a6d821c5658c0018eae238acb1801a9ea0071596300dd3cc00e2b2c6000a6e82905658c0014db0520acb1801a9ea0241596300053cc0482b2c6006a7a80105658c0014f30020acb180028fa1221596300051ec2442b2c6006a7a80885658c0014f30110acb1801a9ea0021596300053cc0042b2c60008ef825d5648c0051d904baac91800a3ba1f725923039637a86e4b246072c6d50dc9648c0e599e61b92c9181cb334c372592302de57ba0e4b2460008bf845d5628c00917908baac5180122fa1f7458a302ee1fa86e8b14605dc3d50dd1628c0bb93e61ba2c518177274c37458a302de57b90e8b14605d8bf845d9428c001c5884b2a851801a2f21d6450a3001556412c8a1460068ec87589428c00955908b12851
  | 7 => 0x7a80dd131540012f301ba262a80021fe19744c5500043e432e898aa02795c8758d31540018b8ecb1a62a809ed5205634c5505e5adc02c698aa02a93e84dc9315400127b09b9262a801a5ea03724c550004bcc06e498aa0299748758531540018e8ecb0a62a80a6d520d614c5500072ab1ac298aa0bbb738058531540018f6ed38262a80031e1da704c550537a818ce098aa030a78865c131540018f0ecb8262a82b3d40c5704c550004bcc06ec90aa00093f845d9215405527908bb242a800257e0d764855014cae41aec90aa00097b805d9215404f2db05ba242a81df4b1097448550004bdc02e890aa006978805d121540010ff0cb9a42a80021f219734855013cb643ac490aa076b2c8458921541756d700b1242a809e5b21d3248550144ba43a8290aa077f244250521540014ef02b9acb200029d20573596401551f420e6b2c8000a3d841cd65900018bae639acb200029ba08735964000536c10e6b2c8000a76811cd65900014eb0239acb2001a9ea0073596401353cc00e6b2c8006a7a809c965901734f301392cb200028fe1172596401551e422e4b2c802aa3e84cc9659000147b09992cb2001a9ea0032596400053cc0064b2c8000a5f835c565900014b906b8acb200aa8fa1071596400051ec20e2b2c8000a5e831c565900014bb0638acb200029ba08715964000536c10e2b2c8000c75711c5659000d4f50038acb2009a9e60071596400043f43862b2c800087d870c5659005547d0818acb200028f61031596400053741062b2c8000a6d820c5659000d4f50018acb200029e60031596401551f42442b2c8000a3d84885659000d4f50010acb200029e60021596400047bc0aeab1c80018f4815d5639000195885b92c72001a3721d634ca405bf46212c699480068ec8758932900011bf06baac32000e3720d755864000656216e4b0c800587c85dd931900010ff0abb263200161f215764c6400043ec36ea98c800087e8759531900010f90eb2a6320003950c5654c6400346e43ac698c8001ad48158d319000d1e90eb0a632000eb520d614c6400347643ac490c80068f4875852190153d4884b0a432000e2f21172d8d402dc5f436e4a1a803bcac62dc94350001958c5b8a86a0002ea6087050d4002c77c3aa5b128072aac8650f625007795ceca1ec4a016f1b9db50d89400ad57420e7b128072aad841cf62500011dd0e29ec4a00023b61c53d89400ad57420a7b128000aad8414f62500015cd0229ec4a0002b960453d894039575400a7b128000ae98014f625002b55d0838ec4a01caab61071d894000477438a3b1280008ed87147625002b55d0828ec4a0002ab61051d894000567418a3b128000acd8314762500e55d50028ec4a0002ba60051d89400047743863b1280008ed870c762500014dd0a18ec4a00029b61431d89400
  | 8 => 0x4b2286a8316cee016450d5014c9ec26e4a1aa02887d87d93625405587ce9b26c4a80038b10b64d895014536412c9b12a000a6d86d0b625405527d0fba2c4a80030fd8374589500069db06e8b12a02ac3c74d9162540510f90eb22c4a80034b1d362589500069dba6e0b12a000d3874dc16254189ad6e5b82c4a80025e603765095000696214eca12a00093f845d942540012df04bb284a80025ee01765095000696210eca12a0c3d2c42dcd4254185a5885b8a84a801a5ea1f705095060f94216e0a12a00597a86dc1425400b2f10db8284a80025e60f7050950004bcc0ee0a12a05dd3b741c142540016b30638284a81cb5adc8705095057f94210e0a12a000b71811c142540012f301bb264a80024fe11764c9501549e422ec992a000977815d9325404f2e902bb264a80025ee01764c95014cb6c16e8992a07dd2c425d132540012f700ba264a801a5e201744c950144ae43a86992a07df0c4250d32540532d90eb1264a81eacb211624c950605b5c02c4992a00096f825d361540512d904ba6c2a81fe5ee0174d8550034bc402e9b0aa07e97b805cf615400d2f100b9ec2a809e1f61f63d85500072a18ec7b0aa00087f8758f61540538b8e6b1ec2a809e9d20563d85500049fc22e5b0aa02a93c845cb61540f72f700b96c2a801a5e20172d85500072ab1e63b0aa000b7180cc761540532bd0fb9ac2a8003951877358550006adc06e6b0aa000c5f60dcd6154001ab6c1b9ac2a8003568437358550006ac886e6b0aa000c5f761cd6154001ca8c239ac2a80021fa1f635855014e2e39ec6b0aa027a7481d8d6154001cac63b1ac2a809e1f21d635855014e2e39ac6b0aa027a748158d615404f4ed0db0ac2a8003551cf6158550006adb9ee0b0aa000d5873dc1615417fae6e3b82c2a82fb9c1877058550004bcc06eca0aa00095f835d941540532b906bb282a80025be097650550144b6412eca0aa00097b805d9415404f2790eb2282a81decb20964505505ed9dc02c8a0aa02793c8750d415404f27b09b9282a80025e603764c5500072a18eec98aa000c7980dd931540018f461bb262a80031e843764c5500043f434ec98aa000d54319d931540012bf06bb262a80025de05764c550004bdc02ec98aa02a93e841d9315400127b083b262a80a25ba08764c550004b6c10ec98aa000d54311d93154001ca8623b262a80030fa10764c5500061ec20ec98aa000c5e831d931540018bb063b262a80031ba08764c55000636c10ec98aa000c76811d931540018eb023b262a80031dcc4764c5500062f188ec98aa000c5c311d931540018e8623b262a8003150c4764c5500063cc00ec98aa000c5f301d931540018f4603b262a80031e4c0764c5500063b880ec98aa000c7a101d931540018f2203b262a80a25ba0b744c550004b6c16e898aa0069
  | 9 => 0x745913102c5e43aa8b22620087e87d41644c40b0f90fa82c8988030f9d365d89310061f3a0cbb1262d1e5431197624c4014f30032ec4988030fd9574d89310061e32ae9b126200d94315d3624c40917d09baec4988022f61375d89310245fc3ae9b126200c9f305d3624c40196e20ba6c498aaf0f9d350d89310061eba6a1b126200d5431dd5624c4010fd0fb2ac4988021fa1c65589316872a188cab126200a7980195624c40b0fd0bbb284988021f617765093100656216eca1262008bd849d9424c401c5885b2a84988029e60375d81310053cc00ebb02620087f855d3604c40b0f90aba6c0988021fe1572d813102c3e42ae5b026200d54315d6604c59fca86232cc0988029e600659813102c3f436eab02629187c86dd5604c401aa863baac0988021fa1f65581310043f438cab0262cfc5f73195604c59d8eee232ac098803550c575181310363d302ea302623087d87d94604c40187ce9b28c0988031b9cb65181310053cc06ca3026200c3e74194604c5278bae6328c0988031b9c8651813166e3ab88ca30262cce5431194604c4014f300328c0988030fd9574181310061e32ae83026200d94315d0604c4018decab90c0988031b1957218131006e218ae430262008fb87580604c4018f2eab00c0988063b60b75d91213ae36b96a1b224200cac42dcd644846355d09b92c890b2fa910b715912165716216a0b2242028f581dd7634840195884ba6c6908161fa1f7558d210043ec06eab1a420087e871d5634840155d09b92c6908163b21d5258d210047743e84b1a420087e87d41634840b0f90fa82c6908021fe157650d2102c3e42aeca1a4200cac425d943484011f700bb2869081a3e2017650d2101c5f43ec8a1a42018ee86dc943484053990ea1a64908d7a3191434c9210265a3b286a0a4231ba48250d414859374d09b92829080b391d93250521165d242264a0a4200f85434c941484010ff0ab9ec0908161f21573d81210047dc3ac03024200a3d8690b64540512dd0fb92c8a80031bd837259150006b5b06e4b22a000d2f741c96454191a76e9b82c8a80035adcb7059150006b4396e0b22a00096f825d363540512d904ba6c6a81fe5ee0174d8d50034bc402e9b1aa00093f845cb635405527908b96c6a81ee5ee0172d8d50034bc402e5b1aa07897b805c7635400d2f100b8ec6a8002d660231d8d5014d2f436c6b1aa02797687dc56354001ca8c7b8ac6a80035ce037158d500063bb06e2b1aa000d7360dc56354001ae461b8ac6a80035c4c37158d500063bbb0e2b1aa000d57731c56354001ca8c638ac6a831f56dcf7058d506372c31ee0b1aa000d7371dc16354001ae0e3b82c6a80025e6037650d50004b7c12eca1aa02896c825d943540012ef02bb286a809e5d2057650d50004bdc02eca1aa02993c8759143540fb659
  | 10 => 0x17000046004338060040342900900e05c0000f00e00001002048014058020140000000002601803006008000000170000080d00707a0100000300e00c01000024000040140080140080f0460202080001e0a8058010160000280300402c0a001000004050250380000004e0000000200103c014008000040280000000c0500180600000c0280802e060048330061200500503400401000010000050290040280001100400002002010010048020000080101a0020040d00c0020100717b09baec4a19f30f5d350d89430246ec1eebb0a8600cac425cb6150c010ff0ab8ec0a18161f21571d81430047dc3ac030286018f681dd763508011eb03baec6a10032b10971d8d426bf16216a1b1a84038de83dd761508011bb07baec2a10032b10973d85426b716216a1b0a84058fb875436050801a5884bacc0a101b1e18175981420063cbaec13028400d2c425d460508bb93ec8b98c0a11cb33d897318142006c6212e6302845dcb7645c460508e59cec4b88c0a10036910971181420047dc3ac0302845dabb8458060508e55d704b00c0a100e3b60b75d91323e636b96a1b2264d5e8c42dcd644c87755d09b92c8990032b10b71591326a716216a0b22643bb8e84dc9434c8051bb07baec2990032b10974d85320043fc2ae3b02640587c855c7604c8011f70eb00c0990123d60775d8d4100656212e5b1a82018bd84dd762504eb87ae9a86c4a08062fa1b744c941024ce43a86992823be8c6250d32504071dd0fb1264a08021fe1573d814102c3e42ae7b0282008fb875806050401aa862b86ca988029ba0b74d953100536c16e9b2a6200c3d741d3654c40147d09b96ca988028f61372d95310043f43885b2a620087d8710b654c5254bd06216ca988029760c42d953148d3b40885b2a6200a758110b654c4014f500216ca988029e60042d95310063db84e1b2a6200a3e841c3654c40147b08386ca98a4a97a0c70d953148d2ec18e1b2a6200a6e821c3654c4014db04386ca98a469da0470d95314953ac08e1b2a620087e87103654c4010fb0e206ca98a4a97a0c40d95310052ec1881b2a6200a6e82103654c4014db04206ca98a469da0440d95310053ac0881b2a620087e87083654c4010fb0e106ca988028fa1020d95310051ec2041b2a6292a5e83083654c4014bb06106ca98a469da0420d95310053ac0841b2a6200c6e72d97644c4018dce432ec898b4f950c465d91310053cc00cbb226200c6f655cb644c4018d8cab96c898803710c572d913101477416ebb2262008ed82dd7644c4051df0eb96c89880333cc172d913100673882e5b226279c6e72d43644c4018dae5a86c898803550c775591310043f43ecab22620087e87195644c5a5ca86232ac8988029e600655913102c3f43eeab22620087d80dd5644c4010fd0e3aac898802aba0b
  | 11 => 0x5018f26d1b10592c2127a40a612289292001ca1b605f1fc0001c923b8e32948000612e09250b609501391e9fa1a922f8caa4e0c417e9bc849a740001bf0839202d012aa709882629901ad9138002591dc14a00011c820800243903acd0002be9238002058a497f116a880822b69218651a4a1e03015380b14301b1e000006d85c022229a448a78269a400003c9ba1cc2a9a6910495b0000ab8fa83589097c1400631561632aa22b04401580027711f86b21b0002369fb8ea90506e8d41f71509958c70db1d721f0d6a41a78a9508e91c1329c31df21b84a2e4ab72c99720ac88d048a782580c69ea8cc99d0ec27b00020e9678001540638001f018e21c107aba12726004c9e5ac5a7f271abb172a8e17dabc23b0000790a023c00016dae78001eb971895a67ab60001198000f69c08002d2896ae026881216f2039bb28880000024424d98211400002e8f19f51eb26fae613819f0ed18c1680092c10000750000ad96a2830f492e98e8e600000026f2aea10149ad709c99d9aca3517480000010d80016a9d99f20d0a6aab78992d69e096e13000025b898ae10001cdac700000012c0000da8000002de82b800139a9a04588a0002e80332ea8cb8000281f28fb85203b0dbaac00000015f881800038aae1ce94c222ad99bea731002671520002c80002ad9a089d1320002e40f7a5093ba4b8d01108e98000d822a2b40b180000008f8000508f70a888c06c00d003002000010000180300003f0020280180e00000000804002024080020042f402002004000038380000bc0380e002038028020000240080101200c0600200000c008000001100000c0000180080c034000008030020900a0030780080480100002000011004028018110001380001a000034000010000c000000008014010050000000300300800402003000008050000000040003f0000bc0400304400c000040000101d01e0000140080000800803000004048030040400400902605200009802000000000000040040180500802c000010000000081d0000300180b00805c1b00500000001800000028018220280200b811002000008020220041100100200c018000020340d00000a04c0000a05e000078000080380606c0060080300503e0d400009000000030040000000000000203400004004018010000080700286100e0080000000201800802000060398020000000100d00c000000060040040200000604c010090020040600000c000028460120040a03800a0500200000600c0180a0120180180000c07000805006004048000000000000300405406006040030000050000940300e058004000020100140180200007c000000200101f00100000001804040014020000260000a00300000c0580002e0a00200101c0000483c01402c010280000340000009c0501e800004004
  | 12 => 0x49a72c791b9802cb8001770001781668000000d2a378e40362381f797d02d1812829d795793c0f80e82b30002bb90a07d2cda3421a8d51d1a531e80ec8fa17b92d0252339741911da8c080fa120e2a7500700022d0000000002ec00015d80009712881500010f00000026c8002640a3a4200193b29da7280005e0d20002c88c52ba96b861a4a2188002848000001c880d0000000cd93a8b22088ca0002030f89429d02cea4900027a9069ff09a90b92da9784f2e1a55a5287291a245a178b88e8a28206a852e32c91e30ee2e8abf03f1a89f409b9c41bb9a82a2a2480003720c0001bd9e6a2619e8002eb9511972b491184da7592b1fca5a9b88000001cca469418af84e2970002a423e9d92220e21752811e90002840a900015c2839de8060002968002890000b11ab89b0af0c2ab5800290816a390000000002050cf9d08000000878000000699bc0002008002619a12659868f9a59a360000931830dc9ac1179af80020985a09420700016e8469efa8b800100abc8f129f1ec2b096d03217a1caa49ae2831a0d8110002219dd0000bf9280000b40000600fc22f22e00020113380010c1979758e021800004783281c14a8001221dc80022e8ff11b29a8f300028e8ac0002090001fd10f8e49ae9481e388e2d798cad62c4a40281a921ce23997aaa4847038022a1412698a83102a0c0149181ab91e40be004018a5780f2479939891cb21d1d4a9118d04f8000df18f85e83b9f69518dea1610603405c80000000024eaab0000000000000000002a880003796299b07a966068855a5a1230000000a80c813880000000008f1920f58b4aafa2c02c0000002879528101872a910a8000001a3ad58ea0000001cf9c180018507b92e02e26491710e1762990000730002319240001a28a2000000000000000187a25aeb29b25d8000000002c513689993c8002941cd14b96c0c20402ad0bc82d97927d8538c88141f9a1194f9e70000bf13091d8428b583d04a8f92c28b0a2c9918738cf122ae72b011d01fada93f1c51ffaa204b272201992a8023e2c1a0b17000da10a049c6ab1093aeeaabaaca8a888161a19020009a1382894214e01d0068eb10801a85a968ad32918051b3883229227ae223481613e8248d724c22704c0a99d303389d891260a1fa268a129e2240842d4878889a061860dfa1690184325e95689c1f616b07a10d2a09d3a3f01a13e0cc2de28a1aaace0cb2dc2132dd1d111e02181985486e0949609a01989c819901718a0298001c708baa12e5000045231075aca0d385b00895720b969aa680012a029164a899260d7ad89f80002c407b004a6ea632cf05613d0c58001010000002410981b026b0000000519b92bd9dd9b820a03c26215ead3a9f8e689190b19c13329882b0769e2084a86945a0f1a61162df2e69c107f23305d21c82f0
  | 13 => 0x171000208184aa72d20001c60da1f094ea238711af17f9181a300c0a09a21090ef1a988b0410680828511150fb00002c80017309f1de0271e1a1129ea778aa1feaa58be92124719a9f31f5ad0880a500001ea11896924b04d0002c399baa300012080023223a80006780007607729c1591d42c609a0c99c02a50001c58000030000002ca8002761e4a0e0ba84e9ee1d80178f615e2d90cd0e79fe1b0a7f80008da90064937a652e39baa6d9db00026380a20d00023a2b89aa27d22d92b9360ad25729623fadb0231808961ed0001450578210001b48928001e5007aaa81c95b8d32a7a3d29829386713a00002a800000202161196a551a500000017380004ba8fa7e1bd143a0a8a18de1799b7a0c8481641ab2a00bd9c79149d28e50000001dba8c8b38588000001789a68001d61d680026600006ba9c81909007fad40f206685701e8390002ed963a1e8d880c80014780014ca7c28d1e981f1318000001d20001030000002ee00027b8001908010d126a0b70ae2e900021580a8fd24f8000001b58008001fd8000000000bb8871c21f1aed0b01070b81b21c4abe0000000c30000000000038001408002ea0001598000000c6000148a02adf9020059600002519941be2680449cb85baa60ab0530261d5a04102860ad528b19f97e07022b8000eb9f90660e7108ac3002a6e2480859ee8b990426c0239120778810000001962cc82f8000000130000629980dd26ba871999b70fd8a59709192ec80003f8000b3220a1500000004919e11100000025c0000000129d517b03e0fe154a2527487994d0308c19470022da00002405f8b50000001651ae0aea32a30ac0a7a0ce95328c1888b9207ac68a695ca8f0109f12bf8ffa669e88e0a461ef0149671f894f125a489558e189e9cf08aa7103a2769f39340fe8ef92981da5497695a8002d18d1add864000065846041a202370fca999469391948bb182a2309f81e20fa9303690e9b28868001e60a713d8892429930278d90001d88001ec80024f1b306f0000aa8000ba0001b527ca3da589c28d58000000d98000000749448e11311a18e583483eab99e78000398978002701e10000e913508606f99ca5ca8d8568780b2ab387c17783da4aa6986cac025396cab195895a25f1df80ea4d1158a504383aacb2e9a8087085415f1098080421550f3a5e28621a24cab280000b935a798f41bf8c122a8000bd23009211280000001800025d0dc105a792148f50001c98000000001ed87c8bc00018b93701b80000012f8a31a78850c929b8c798dad10720001410001621da09e071a210002510002af0ee9b196f97c9440001951ad1b691aadb9500e38620000000ed800000285a9d0888c3a5693f85d9fa80000000000000000014d80010c9a58002a3a928f01348a4183a430a28f08001fb2bd000282059a198d
  | 14 => 0x12c87412486a00000018407e0002170000000000002388551102d82a827e811a129132b2052ab50000002cfae594621d9c39b40dd8000d60002738c488015d1859580002dca450a606d2359f491f025858040a5f87e8b792f16587da5206918b2b808ca5419a1e2a562cc0b6800000295aa194b1b98000f2a3ca5b06a80000e1898ce035
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1454935c471596400061560d711c565900014a99010b7258e400052a64042dc96190001255980c5654c6400061521c315953190001651900c5654c6402de2a200625d13150001469901d7624c5400059165431d8931500016c1900c7624c5402de8aa0062dd15050001855835c471596300058a64042595428c0014a99010a76509302de2360c421d9424c0014a990108765093000615184874c5504c00134b926137354130004c6e5182dcd504c053318985d143541305adc22497450d504c05331994e0943541300068a10886509504c05334992e11325413003496259844c9504c16bb0842611325413014cd2261724c9504c167708945c9325413014e1621b735c5504c0013199421d3154130004d2648874c5504c0019538121d3154130004d264b844c5504c00131994e09315413014cd4261714c5504c001950875c5315413014d94259714c5504c00d6189650d50501305af421c943541404c001454915cc7359620006155cd811cd6588001454935c471596200061560d711c565880014a99010b7458e200052a64042dd16188001255980c5654c6200061521c315953188001651900c5654c6202dc6aa5f8250d40880b71aa97e0941502200050e64075d913148001615950c7644c520005a464031d9131480b78a88019173485202de8aa0064dc950480b72aa96e1132901202dcaaa5b84486404800d5289750950501200358a259425414048051c287650950501204de2a1db8350940481138a876e0542501201de2a1d9844c94048077c887650d325012018e2a1d9844854048063ca07650521501200355225d325413048167e08644c9504c120006155cd811cd6584001629901096550a10005866508359530840016499220d654c210005946448359530840016499290d654c210005866533259530840014a99010a76509102de29604421d942440014a99010876509100061518c874c5504400b07a98e1d63541100061621f8358d504400187087e0563541100068a10886509504400136392613715411013d1c25973dc550440013339460b715411013ccc261745055044149720925d1415411013ccc6538250550440013319421d3154110004d8648874c550440019538321d3154110004d864b844c5504404f350985cd31541100065421d734c5504404f650965cd3154110004cc653824c5504404f36192e1121541100349c259844855044149b2042611215411013cd8261724855044147720945c921541100358c259415414044149d207250550501100054c650815d6304400155193205758c11000558648815d6304400156192905758c1100054c652215d63044001350984c5504c11013f141d9315413044123c5076e15314c110004f064b844c5304400139194e09314c11003598259215412044147d20744855048110
  | 1 => 0x10055464031dd5644c401a503160065591310040f66274197624c40183a7460065d8931006940c580197624c4014399019574d893100545654315d3624c401c14650c574d893100564640315d3624c401156980c775589310055464031dd5624c401a503160065589310052a64042dd9424c4016299010b655093100455660315d6604c401551900c57598131006940c580196604c401156980c775581310055464031dd5604c401155980c5751813100554640315d4604c40183a746006518131006165cd80194604c40186a7260065181310061c5c580194604c40143990195741813100545654315d0604c401c14650c5741813100564640315d0604c40146990195721813100551654315c8604c401c44650c5721813100570640315c8604c4014a99010b73591210052a640425d363484014a9901097650d212de2a200425d943484633849850d32505211df211d9434c941484012569818f7158d5000515a5b731c563540012559818c7158d500058a64042d9362540015299010a76509500054a640421d942540b79288010876509502ee46dd1831c142540e594b7260c7050950006c2109831c142540bb93374604705095039658dc9811c14254001b204260470509500059464031d8f61540012579858f31d855000515e5d63cc7615400125698187735855000495660611cd6154001456978c7635855000615a1e31d8d6154001856861cf615855000495a6031dd93154001651900c7764c55000515658319d93154001551900c6764c55000455660311d93154001455960c4764c55000554640311d93154001255980c4764c55000594640311d931541b1a51800c4764c5500060b611821d9315400185583604764c5500051c643311d93154001456918c4764c55000516642311d9315400105d980c4764c55000516640311d93154001075980c4764c5500051c640311d93154001457980c4764c55000615a60311d93154001455980c4764c55000615660311d93154001055980c4764c55000705a50311d93154001c15940c4764c55000705a10311d93154001c15840c4764c55000711a48311d93154001c45920c4764c55000711a08311d93154001c45820c4764c55000714a40311d93154001455900c4764c55000714640311d93154001451900c4764c5500060ea11801d9315400183984600764c5500061660d801d9315400186a82600764c5500061a609801d9315400187181600764c550007140c5801d93154001c50318c0764c5500051524f101d93154001c5031840764c550006152047658d3154001854831d9614c55013c9526163585315404f4549758d614c55014e1521d635853154001c50311da704c5500041ea60765c1315400185b831d9704c5500061ce04765c13154001454915cc7359640006155cd811cd6590
  | 2 => 0x98623280000007e37900000986d6c00000006000191d950003e800000000001c89b69889560328064002c2cb1000256180088e706aa400000022c0017000011a89293cc007236915c0400031da858000007acb6519c34210018400152ab5c0c4d248e5aa85253999c53003a98ab770bb8cc3e0003c96cf002b800f400255b4fe001b00042690ed727c23221e456300d000430007d8c83000a1140000269d6240037000a46f8b800ad16a31786a081ec305a41001320000000ba484e240f0f0061bcd2385f00000d9562fc00c23a00000b47d25c001117a950c0a0a000005f003dd5efb2a1cdc4e827a752677000c410b55d000006e718740000000000000002cc0000518000000001a000b86e8011cec00081da003f8000000728018035139c456ef7b0109c7950815b60000001d263510d92400238014e96641ac388420945fa26663e40eaa608014009000002c000000000006b004fc5b3a80066d000000240005ac9302a64a98e0f84880128f51d0380000000fc00000000052b100360ae0043a3c009e66a04b83c2f07800375daf400d1001e800020027cc8f100001602302416050080404140000000030180c000104820140009804020000800020e010101a0304000000100018040000030040003020000300038000101018020a000200001020001800008040a01030083a0d00018000100028100403800020200004014a99010972d85430052a640425c763508014a99010973d85420054a640425d660508b7c286010975981420054a640425d4605080158990109731814200568640425c460508014a99010b71591320052a640425d3614c8014a99010972d8d4100455a60315c3654c401551900c570d95310041b66272197644c40186a7260065d9131006940c580197644c4014699019572d913100551654315cb644c401c44650c572d913100570640315cb644c401156980c7755913
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa8b801900000018000700001d040c8b16848e97801f9b8c19958d1400018d948e2085069c950892161311080f8f100782989c09010580171f109d808302001a0a1e8020001a83802113a1919b1e00099286010e00090022c145840800711360190008012812dc8514cc8084bacc0a1002251a90c580197644c401222d48ca18ae5b226200b10680650c572d9131006880cac8062b96c898802251a90c580195644c401128d4862c00cbb1262009056a4650c574d89310058234032862ba6c49880341065640315d3624c401128d4862c00cab1262008946a431600659813100482b5232862ba0c09880341065640315d0604c401222d48ca18ae43026200d10195900c572181312dc15150c8084bb2869096e12ba8640429d94254001128d4320188ec98aa000914683980c4764c55000602d48cc0623b262a8003015a4660311d9315400182351330188ec98aa000c11689980c4764c5500060a340cc0623b262a800301598a50311d9315400180acc328188ec98aa000c05662840c4764c55000602b30c20623b262a800304598a48311d93154001822cc324188ec98aa000d01651920c4764c55000608b31410623b262a800304598608311d93154001c02c2304188ec98aa000c14662900c4764c5500060a330c80623b262a800341294640311d93154001a08ca320188ec98aa000d10a49900c4764c55000688324c80623b262a8002453a8640311d93154001a0942320188ec98aa000d04611900c4764c55000688504c80623b262a800344182640311d93154001228d4862c00ec98aa000a146a031600764c5500070230818b003b262a8003841820c5801d93154001428d4063180ec98aa000a146a031840764c5500048a352188ed38262a8002851a80c4769c1315400102ad490e18aca98c8000c1421d900c5654c6402de11306c80843b2849816f2099310886509504c0014295370243a62a826000c14258875c531541300040ab5243862b2a6310003050876403159531880b7850c0b20210eca1220008156a46321d31541102de443222110ca12a088002852a6e0c874c550440018284b10eb9a62a822000c141d8984c5504c110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xe24608ac000003004441ba195900c572d9131004411ba195900c574d8931006005a4689980c4764c550006011a4681980c4764c550006041a2681980c4764c55000700184609900c4764c550006011a961031600764c550006041a960831600764c550
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x1
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x124e
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124d
  | 15 => 0x98a
  | 16 => 0x98c
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128a
  | 20 => 0x128c
  | 21 => 0x128d
  | 22 => 0x128e
  | 23 => 0x9ca
  | 24 => 0x9cb
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12ce
  | 28 => 0x12ca
  | 29 => 0x12cb
  | 30 => 0x12cd
  | 31 => 0xa0a
  | 32 => 0xa0b
  | 33 => 0xa0c
  | 34 => 0xa0e
  | 35 => 0x130a
  | 36 => 0x130b
  | 37 => 0x130c
  | 38 => 0x130e
  | 39 => 0xa4a
  | 40 => 0xa4b
  | 41 => 0xa4c
  | 42 => 0xa4d
  | 43 => 0xb0c
  | 44 => 0xb0d
  | 45 => 0xb0e
  | 46 => 0xb4b
  | 47 => 0xb4d
  | 48 => 0xb4e
  | 49 => 0xb8b
  | 50 => 0xb8c
  | 51 => 0xb8e
  | 52 => 0xcca
  | 53 => 0xccd
  | 54 => 0xcce
  | 55 => 0xd0a
  | 56 => 0xd0c
  | 57 => 0xd0e
  | 58 => 0xe8a
  | 59 => 0xe8b
  | 60 => 0xe8e
  | 61 => 0x9c956
  | 62 => 0x949d6
  | 63 => 0x12c956
  | 64 => 0x952d6
  | 65 => 0xca
  | 66 => 0xa4953
  | 67 => 0xa4954
  | 68 => 0xa4955
  | 69 => 0xb0956
  | 70 => 0xb0955
  | 71 => 0xb4956
  | 72 => 0xb8956
  | 73 => 0xb8953
  | 74 => 0x150a
  | 75 => 0x168a
  | 76 => 0x180a
  | 77 => 0x9d256
  | 78 => 0x1249d6
  | 79 => 0x4c
  | 80 => 0xa5253
  | 81 => 0xa5254
  | 82 => 0xa5255
  | 83 => 0x4e
  | 84 => 0xa0996
  | 85 => 0x10b
  | 86 => 0xb0996
  | 87 => 0x138b
  | 88 => 0xcc996
  | 89 => 0xd0996
  | 90 => 0x168b
  | 91 => 0x409
  | 92 => 0x180b
  | 93 => 0x1609
  | 94 => 0x8d
  | 95 => 0xa49d2
  | 96 => 0xa49d3
  | 97 => 0xa49d5
  | 98 => 0xb49d6
  | 99 => 0x138c
  | 100 => 0xcc9d6
  | 101 => 0xcc9d5
  | 102 => 0x150c
  | 103 => 0xe89d6
  | 104 => 0xe89d3
  | 105 => 0x180c
  | 106 => 0xa52d2
  | 107 => 0xa52d3
  | 108 => 0xa52d5
  | 109 => 0xce
  | 110 => 0xb8a16
  | 111 => 0x138d
  | 112 => 0xd0a16
  | 113 => 0x150d
  | 114 => 0x1889
  | 115 => 0xe8a16
  | 116 => 0x168d
  | 117 => 0x198a
  | 118 => 0xb0a55
  | 119 => 0xb8a53
  | 120 => 0x138e
  | 121 => 0x198b
  | 122 => 0xcca55
  | 123 => 0x150e
  | 124 => 0x198c
  | 125 => 0xe8a53
  | 126 => 0x168e
  | 127 => 0x180e
  | 128 => 0xb8b16
  | 129 => 0xccb16
  | 130 => 0xb0cd6
  | 131 => 0x170a
  | 132 => 0x15ca
  | 133 => 0x16cb
  | 134 => 0x144b
  | 135 => 0x188a
  | 136 => 0x160a
  | 137 => 0x184b
  | 138 => 0x148b
  | 139 => 0x154c
  | 140 => 0x140c
  | 141 => 0x18ca
  | 142 => 0x178a
  | 143 => 0x184c
  | 144 => 0x148c
  | 145 => 0x17ca
  | 146 => 0x14cc
  | 147 => 0x5ca
  | 148 => 0x154d
  | 149 => 0x140d
  | 150 => 0xe8b96
  | 151 => 0xb8e96
  | 152 => 0x16cd
  | 153 => 0x144d
  | 154 => 0xe8cd6
  | 155 => 0x18cb
  | 156 => 0x178b
  | 157 => 0x188c
  | 158 => 0x160c
  | 159 => 0x170d
  | 160 => 0x15cd
  | 161 => 0xb49c95e
  | 162 => 0xb4949de
  | 163 => 0xb0a495d
  | 164 => 0xb8a495b
  | 165 => 0x94a53
  | 166 => 0x12ca52
  | 167 => 0x94a54
  | 168 => 0x94a55
  | 169 => 0x94b15
  | 170 => 0x94b93
  | 171 => 0x198d
  | 172 => 0x9ca52
  | 173 => 0x124a54
  | 174 => 0xd0a099e
  | 175 => 0x10a53
  | 176 => 0xa5813
  | 177 => 0x9ce93
  | 178 => 0x128a16
  | 179 => 0xcca49dd
  | 180 => 0x9ca53
  | 181 => 0xe8a49db
  | 182 => 0x9ca55
  | 183 => 0x9ccd5
  | 184 => 0x8a55
  | 185 => 0x130996
  | 186 => 0xb1516
  | 187 => 0xb5396
  | 188 => 0xb5696
  | 189 => 0xb9816
  | 190 => 0x198a52
  | 191 => 0x139256
  | 192 => 0xcd516
  | 193 => 0x180a53
  | 194 => 0x184a53
  | 195 => 0x18ca53
  | 196 => 0x151296
  | 197 => 0xe9816
  | 198 => 0x198a54
  | 199 => 0x1692d6
  | 200 => 0x181316
  | 201 => 0x40a
  | 202 => 0x198b93
  | 203 => 0x184b93
  | 204 => 0x5c0d2
  | 205 => 0x2cc
  | 206 => 0x2d254
  | 207 => 0x5d2d2
  | 208 => 0x5ccd2
  | 209 => 0x5d712
  | 210 => 0x5ce92
  | 211 => 0x5d792
  | 212 => 0x198e93
  | 213 => 0x18ce93
  | 214 => 0x199853
  | 215 => 0x1998d3
  | 216 => 0x24b56
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1426
  | 6 => 3726
  | 5 => 1502
  | 4 => 255
  | 3 => 68
  | 2 => 8
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (57987+((h/475+packedAt gbK7 (52762+(h % 475)*11) 11) % 1712)*12) 12
  | 6 => packedAt gbK6 (194994+((h/1242+packedAt gbK6 (178848+(h % 1242)*13) 13) % 5951)*13) 13
  | 5 => packedAt gbK5 (94118+((h/500+packedAt gbK5 (88618+(h % 500)*11) 11) % 1803)*12) 12
  | 4 => packedAt gbK4 (18615+((h/85+packedAt gbK4 (17850+(h % 85)*9) 9) % 370)*9) 9
  | 3 => packedAt gbK3 (5662+((h/22+packedAt gbK3 (5508+(h % 22)*7) 7) % 82)*8) 8
  | 2 => packedAt gbK2 (744+((h/2+packedAt gbK2 (736+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc47038fc00c63e380ffc7e0ffff0321c08727f
  | 1 => 0x7803f1fff07c7c00e0f8ff0e0f0c067364d93
  | 2 => 0xf8003fe00ff807fff00ff000ff030c78c78e1c
  | 3 => 0xffffc0000ffff800000fffff000c0f80f80fe0
  | 4 => 0xffffffffff00000000ff000fff000
  | 5 => 0xfffffffff000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8412102480000808028012082880120c001025
  | 1 => 0x80090865024640a42484a042604021164492
  | 2 => 0x4804aa4123480292600d206296210c70428e18
  | 3 => 0x512180000ad49001404a494604040480e80b40
  | 4 => 0x900024ca7252589600184004ee000bd6000
  | 5 => 0xa64e34938000000601800008188bbb5e000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffeffecfefaeea8fffeffecfefaeea8fffeffecfefaeea8fffeffecfefaeea8fffeffecfefaeea8fffeffecfefaeea8fffeffecfefaeea8fffeffecfefaeea8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_32974
namespace PEqualNP.Outside.L_meta_32974
open PEqualNP.Outside.L_meta_32974.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs5_2_0 : Interval s5Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 8 := bs5_2_0
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
theorem bs5_3_96 : Interval s5Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 102 := (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96))
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
theorem bs5_4_704 : Interval s5Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 725 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 (concat bs5_4_192 bs5_4_224)) (concat bs5_4_256 (concat bs5_4_288 bs5_4_320)))) (concat (concat (concat bs5_4_352 (concat bs5_4_384 bs5_4_416)) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512))) (concat (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)) (concat bs5_4_640 (concat bs5_4_672 bs5_4_704)))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 682 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 bs5_5_384) (concat bs5_5_416 (concat bs5_5_448 bs5_5_480))) (concat (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)) (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 8 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 68 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_224 : Interval gbAtlas 4 224 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 255 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224)))
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
theorem bgb_5_1472 : Interval gbAtlas 5 1472 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1502 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))))))
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
theorem bgb_6_3712 : Interval gbAtlas 6 3712 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3726 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)))))) (concat (concat (concat (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496))) (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))) (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456))) (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584)) (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712)))))))
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
theorem bgb_7_1408 : Interval gbAtlas 7 1408 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1426 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672))))) (concat (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832))) (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))) (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 16, 20),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero]
def fullWord : Sig := 0xffffffffffffffffffffffecffffeea8fffffffffefefefefffeffecfefaeea8ffffffffffffffffffffffecffffeea8fffffffffefefefefffeffecfefaeea8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_32974.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[7,5]⟩,⟨.or,[7,6]⟩,⟨.or,[8,9]⟩,⟨.or,[0,2]⟩,⟨.or,[0,10]⟩,⟨.and,[13,3]⟩,⟨.and,[8,9]⟩,⟨.and,[11,4]⟩,⟨.and,[12,10]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_32974

open PEqualNP.Outside.L_meta_32974 in
theorem PEqualNP.Outside.L_meta_32974 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
