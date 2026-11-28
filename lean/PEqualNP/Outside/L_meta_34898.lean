import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_34898.Model
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


end PEqualNP.Outside.L_meta_34898.Model

namespace PEqualNP.Outside.L_meta_34898
open PEqualNP.Outside.L_meta_34898.Model
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

end PEqualNP.Outside.L_meta_34898

namespace PEqualNP.Outside.L_meta_34898
open PEqualNP.Outside.L_meta_34898.Model
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
end PEqualNP.Outside.L_meta_34898
namespace PEqualNP.Outside.L_meta_34898
open PEqualNP.Outside.L_meta_34898.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x300078024009804a0000038000000000a80141800000400263a0920040a0400006d5800000000085d1814200d00000070352000000000000002d38518a8000321c00000580003c4400000500003e34022000000000004800100000000218000000c000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41f641fd41f541fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x28a38f8e0380069f8022920dab2c8016a0899d0f1e1b80001d82071703159f000ea196149112ac00000082a48c09002580000a889b0810280493940617801a19810026800b91a40b1a8a25232ba9192d8027200cad000004001810a9a122019e988026059c2a851caa2787930d0015068428080050a04ea5000c082040808202180870200507001400abb28e877551d0edca521db54a43b7290876d5210eeca221dd54443bd28087795010eeca3a15d54742af298855d5310aeca2215d54442bd28085795010aeca3195d54632b6a9c65e6518cbcaa31973d4d32e721a65cd434cadca4195b94a41b6a94837554907cca520f954a41f319483e5329076ea8a0edd0d41daa1a83b6425076884a0f98c941f2992837651106dca598db54b31e6994633e540c67aa818db94831b6a9063cd320c6f4a018de54031af29e435d53c867ca910cf55221bb28e817551d036a83a05bd4940b629281b541502bca6205754c40b7290816d52102eca2205d54440b7296616d52cc39a6598734c930bba8a6174514c27ca8184f55030b7290616d520c2eca2185d544309f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x100ab01140021ed49dc3618010005188058d592518caa56494632b1987534ca4d6394a41b158e5290665658ca41a998b54506956310941ac5804250785434c941c3551320c74932540319358c525032452505408d590514c3453214530
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x60a090ae930ea6994857398b5450682b98a4a0a81815913214530
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
  | 3 => packedAt s1K3 (633+((h/5+packedAt s1K3 (608+(h % 5)*5) 5) % 22)*5) 5
  | 2 => packedAt s1K2 (199+((h/1+packedAt s1K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf1e38f3c7fcfc7ff888e31c3f8fc3ff80727f
  | 2 => 0xf01fc0fc063f3f8e3f0f03e039f1fce3a64d93
  | 3 => 0xffe000fff83fc00fc7f003ffc1fe00fc478e1c
  | 4 => 0xffffff00003ffff007fffc0001ffff00780fe0
  | 5 => 0xffffffffffc0000007fffffffe0000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x1020110080400800000200408024020001025
  | 2 => 0x10c4a222944aa818450913229490a84b264492
  | 3 => 0x22419449849099240b90094981a41a99428e18
  | 4 => 0x440910092120100492a2480101491210480b40
  | 5 => 0x8890208200022249244c929224002002356000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xffffffaafafaaaa0ffffffaafafaaaa0ffffffaafafaaaa0ffffffaafafaaaa0ffffffaafafaaaa0ffffffaafafaaaa0ffffffaafafaaaa0ffffffaafafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_34898
namespace PEqualNP.Outside.L_meta_34898
open PEqualNP.Outside.L_meta_34898.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2018f00560001542a1101005858200000000e006054a24b8f1a8c9003e00000000000000281930000000000001d320120036440004e00004540101a1050e1852987008106041800000202003c180ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41f641fd41f541fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x9e000000100000940072a45462667690000860360000000042000a000000002a00003456304e4a6c00005200007e964674b05a00008e0026001898b60084240000320002007c00164c120000aaa200000000008200a60000000000001c44007a2c00001e0000000040640050003e0000000038000000008a2000a0005e3c0000000000008c0000866aa80000009a7000000000acb292004800889c00000014040000000000800000000000000e00000000b400005c22286e1a3aae582e000006687800000000000c00000000000000000000010000000100010100000005030000000500010000040007000004050601bb28e877551d0edca421db54843bb28887755110ef4a021de54043bb28e857551d0abca7215754e42af298855d5310aeca2215d54442bd28085795010aeca3995d54732eb28e65d551ccabaa71973d4932e721265cd424cabca6195794e41aea9c837554907aca720f554e41eb99483d5329076ea8a0ed90d41da21a83b7425076a84a0f5cc941ea992837651106dca598db54b319f2a4633d548c6bca790d754f21e6994433e540867aa810d794c21aea9843cd32086f4a010de54021bb28e817551d036a83a057d4d40ae29a81b541502bca6205754c40b7290816d52102eca2205d544409f2a0613d540c2dca4185b54830bb2886175510c2bca7905754f20e699641cd32482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x580e01852000000000c00300d10000015c02000053d000000820408d59251cca956494732b1987524ca4d6294e41b158a539065565cca41a598f54506a56210d41ac5804350785424c941c35513208749325402193588535031453505408d59051483453214520
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x3280090ae930ea4994857298f5450682b90a6a0a81815913214520
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
  | 4 => packedAt s2K4 (2724+((h/30+packedAt s2K4 (2484+(h % 30)*8) 8) % 213)*8) 8
  | 3 => packedAt s2K3 (638+((h/5+packedAt s2K3 (608+(h % 5)*6) 6) % 39)*5) 5
  | 2 => packedAt s2K2 (199+((h/1+packedAt s2K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf1e78f1c7fcfff1f88c708e3f8fff0f8073cf
  | 1 => 0xf01f80fe063f38fe3f0f80f039f1c7f3b24d33
  | 3 => 0xffe000fff83fc0ffc7f000ffc1fe07fc438e3c
  | 4 => 0xffffff00003fff0007ffff0001fff8007c0fc0
  | 5 => 0xffffffffffc0000007fffffffe0000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1020110080400020000100208024100001045
  | 1 => 0x10c45225144aa1a0450c8a91149092a3324512
  | 3 => 0x22012448809012400a90042481242448408a28
  | 4 => 0x4449300ca520906493a5260081c93069540f80
  | 5 => 0x8890408100022489244a48c9240000822b6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffffaaeeaaee88ffffffaaeeaaee88ffffffaaeeaaee88ffffffaaeeaaee88ffffffaaeeaaee88ffffffaaeeaaee88ffffffaaeeaaee88ffffffaaeeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_34898
namespace PEqualNP.Outside.L_meta_34898
open PEqualNP.Outside.L_meta_34898.Model
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
end PEqualNP.Outside.L_meta_34898
namespace PEqualNP.Outside.L_meta_34898
open PEqualNP.Outside.L_meta_34898.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x90001800024000003a5400b00015994ea401b0430028483818a3494022002000f2684c140a1151f009801600791800e80b8938000111a3c0000058100004000003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x290023819f928f982225a10007011580160c80060daa9f002d8000289b830e802cab00202089261500000013001e052c2a10a98b038b801d9c912285a81724898a93829e9d27142b91a68a0f1c0d17801a21ad080696849b25190e1a80000084000780001482089027a319a412188c00802c2408c0a280021e0018702245840608100002c302064ca86b7294876d5290edca421db54843bb28887755110ef4a021de54043bb28e857551d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290656e52d06daa5a0eb94b41d6a9683ae32d075a65a0cf55241d719283ad325076ea2a0cf95041b7296636d52cc79a6598cf952319eaa463b5418c79a6498ed505319f2a0633d540c6dca418db54831bd2806379500c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af298815d53102dca4205b54840bb288817551102dca5985b54b30e6996613f544c278a898734c9309f2a0613d540c2dca4185b54830bb2886175510c27ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a83885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x88081cb00000280001340c79cc34a87080018d586548caa56195232a3993534cac56110d32b2580434ca4d6394b41a358e52d062d658cb41a998b51507853250531c554d410873141540218d584544c30c544c9309358c52443245250510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x98008090ae3326a6994857398b5150682b88a899261415cc5250510
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
  | 4 => packedAt s4K4 (2694+((h/30+packedAt s4K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s4K3 (633+((h/5+packedAt s4K3 (608+(h % 5)*5) 5) % 24)*5) 5
  | 2 => packedAt s4K2 (199+((h/1+packedAt s4K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf3c78f3ffc7c7f1f8c470c7fe3f1f0f80f4cf
  | 1 => 0xf03f80fc63f9f8fe3f0780f8e3c7e7f1934b33
  | 2 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 3 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1040110004008020000100120090100001045
  | 1 => 0x10882222049101404204844848428241114112
  | 2 => 0x22035449492492a00dc80a92129054ac628c28
  | 3 => 0x44111009120080249151220003245024240e80
  | 5 => 0x88a26082403524c926a64ce4980080c95be000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffeaffeaeee8eee8ffeaffeaeee8eee8ffeaffeaeee8eee8ffeaffeaeee8eee8ffeaffeaeee8eee8ffeaffeaeee8eee8ffeaffeaeee8eee8ffeaffeaeee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_34898
namespace PEqualNP.Outside.L_meta_34898
open PEqualNP.Outside.L_meta_34898.Model
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
end PEqualNP.Outside.L_meta_34898
namespace PEqualNP.Outside.L_meta_34898
open PEqualNP.Outside.L_meta_34898.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x26001ff8813000ff84098007ff104c003ff0826001fe8413000ff82098003ff65480017fb2a400eff99520035fcca90003fd65480017eb2a400eff19520035f8ca90003ff64480017fb22400dff9912002dfcc890003fd64480017eb22400dff1912002df8c89003bff544801bff2a24000ff5512006ff8a890003ff63480017fb1a400cff98d20025fcc690003fd63480017eb1a400cff18d20025f8c69003bff5348019ff29a4000ff54d20067f8a690037ff4348019ff21a4000ff50d20067f88690006ff6248007ffa924003ff9492001fdca49000ffd5248001f6a924003ff1492001ffe849000ffe4248007f72124003ff50920007da849000ffc4248007ff9924003ff8c92001fdc649000ffd3248001f69924003ff0c920007fec290002ff6148017ff30a4002bf98520007fac29002ffc61480057e30a400effd452005ffca290003fd5148017fe28a400dffd052005ffc8290003fd4148017fe20a400cffcc52005ffc6290003fd3148017fe18a4003ffc852001fde429000ffe2148007fe90a4000fb4852001ff84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ff48090007fd4048001fca024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe409000ffb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824000ffd9510005feca8802bfe654400d7f32a2000ff59510005faca8802bfc654400d7e32a2000ffd9110005fec888027fe644400b7f3222000ff59110005fac888027fc644400b7e322200affd511004ffca888003fd5444013fe2a22000ffd8d10005fec688023fe63440097f31a2000ff58d10005fac688023fc63440097e31a200affd4d10047fca688003fd5344011fe29a2009ffd0d10047fc8688003fd4344011fe21a2000ffd8910005fec48801ffe62440077f3122000ff58910005fac48801ffc62440077e312200affd491003ffca488003fd524400ffe2922009ffd091003ffc8488003fd424400ffe2122008ffcc91003ffc6488003fd324400ffe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510007eaa28800bfc5144005ffa0a2002ff90510017ec828800bfd4144001faa0a2002ff10510017fe628800bfe3144005fb18a2002ff4c510007ea628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x6ff6054003ffa82a006fed415000ffca0a80077e5054003fe282a001df1415000ff0a0a8007ff4054003ff202a001fe9015000ff880a8007ff3054003ff182a001fe8c15000ff860a8007ff2054003ff102a001ff0815000ffe20a8007fe1054003fe082a000ffd9540005fecaa005bfe655000d7f32a8000ff59540005facaa005bfc655000d7e32a8001bfd914002ffea8a0017fe545000bdf2a28005ff551400077aa8a0017fc5450001ffb1a8000bfd8d400affcc6a0012fe6350001feb1a8015ff18d40025f8c6a005bff535002bff29a8000ff54d400aff8a6a0017ff435000bdfa1a8005ff90d4002ffa86a0003bd435000bfe21a8000ffd8940005fec4a0053fe62500077f3128000ff589400a7f8c4a000efc625002dffa928014ff94940007faa4a0053fc525000bffa128005efd094002ffc84a0017fd4250001dea128005ff109400affe64a0053fe3250001fe9928014ff0c940007fec2a0002ff6150027ff30a8002bf98540007fac2a004ffc61500057e30a8016ffd454009ffca2a0003fd5150027fe28a8005ffd054002f7e82a0017fe415000bfea0a8000ef5054002ff882a0057ff3150027ff18a8000ff4c54009ff862a0053ff2150027ff10a8000ff4854009ff842a0006ff6050003ffa828001ff9414000ff4a0a0007fd5050001fca828001ff1414000ffe80a0017fb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ffcc14000ffc60a0007fc3050003ff9028001ff8814000ff440a0007fc2050003ff8828001ff8414000ff820a0003ff654c0017fb2a6012ff99530035fcca98003fd654c0017eb2a6012ff19530035f8ca98003ff644c0017fb226011ff9913002dfcc898003fd644c0017eb226011ff1913002df8c89804bff544c023ff2a26000ff5513008ff8a898006ff634c009ffa9a6004ff94d30027bca698013fd534c001eea9a6004ff14d30027fe8698013fe434c009ef21a6004ff50d30007ba8698013fc434c001ffb126000bfd8930087fcc49800efe624c001feb126010ff1893001df8c49804bff524c021ff2926000ff54930087f8a498047ff424c021ff2126000ff50930087f88498013ff324c009ef9926004ff8c930027fa6498003dd324c009fe1926000ffd8530005fec29803ffe614c0057f30a6000ff5853007ff8c29800afc614c025ffa8a600fff94530007faa29803ffc514c023ffa0a600fff90530007fa829803ffc414c009ff98a6004f7cc530027fc6298013fd314c001ee98a6004ff0c530087fe429803ffe214c001fe90a600fff0853000dfec098007ff504c003ff2826001fe9413000ffaa098003f9504c003fe2826001ffd013000ffc8098007fd404c003fe2026001ffcc130027f66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff9
  | 2 => 0x31007ba6498813fc324c4057fb0a6202ffd4531017fca29880bf6514c405fea8a6200fd54531017f8a29880bff414c405ff20a6202ff50531017f8829880bff314c409fb98a6202ff8c531017bc629880bfc314c405ee18a6202fd0c531017fe429880bfe214c405fe10a6200ffd8131005fec09887ffe604c4037f3026200ff581310fff8c098806fc604c445ffa82621fff941310fff8a098887ff404c43fff202621fff10131027fe6098813df304c409ff1826204ff0c131107fe409887ffe204c43ffe1026202ffc4131017ee209880bfe104c405fe0826200ffd9521005feca9087bfe654840d7f32a4200ff59521005faca9087bfc654840d7e32a4200ffd9121005fec890877fe644840b7f3224200ff59121005fac890877fc644840b7e322421effd51210effca890803fd544843bfe2a24200ffd8d21005fec690873fe63484097f31a4200ff58d21005fac690873fc63484097e31a421effd4d210e7fca690803fd5348439fe29a421dffd0d210e7fc8690803fd4348439fe21a4202bfd892101ffea49080ffe5248407fea924203ff1492101ffe849080ffe4248407fea124203ff1092101ffe649080ffe3248407f71924203ff4c921007da649080ffc32484057fb0a4202ffd4521017fca29080bfd5148405fe28a4202ffd0521017fc829080bf64148405fea0a4200fd50521017f8829080bff3148405ff18a4202ff4c521017f8629080bff2148407fb90a4202ff88521017dc429080bfc2148405f610a4202fd08521007fec090802ff6048437ff3024201bf98121007fac09086ffc60484037e302421effd41210dffca09086ffc504843bffa02421bff901210dff88090873ff3048437ff182421bff0c12101ffe409080fef2048407ff1024203ff08121017fe209080bf71048405ff0824202ff0412100dfecaa8003ff64540017fb22a01aff9915002dfcc8a8003fd6454035fe322a005bf19150037fea8a801b7f545400dff2a2a006ff55150006faa8a801bfc5454001ffb1aa000bfd8d500cffcc6a8012fe6354001feb1aa019ff18d50025f8c6a801bff535400dbfa9aa006ff94d50037faa6a80037d535400dfe29aa01affd0d500cffc86a8003fd4354033fe21aa000ffd8950005fec4a8063fe62540077f312a000ff589500c7f8c4a800efc625400dffa92a006dfd4950037fca4a801bfd5254001bea92a006ff149500d7fe84a8063fe4254001fea12a018ff109500cffe64a8063fe3254001fe992a018ff0c950007fec2a8002ff615402fff30aa002bf98550007fac2a805ffc61540057e30aa006ffd4550036fea2a801bfe515400dfea8aa000df54550037f8a2a806bff415402fff20aa000ff505500bff882a8067ff315402fff18aa000ff4c5500bff862a8063ff215402fff10aa000ff485500bff842a800
  | 3 => 0xf29aa206ff54d51006faa6a881bfc5354455ffa1aa229ff90d51007fa86a88a7fc4354401ffb12a200bfd8951147fcc4a880efe6254401feb12a228ff1895101df8c4a881bff525440dbfa92a206ff94951037faa4a88037d525440dfe292a22affd0951147fc84a8803fd4254451fe212a229ffcc951147fc64a8803fd3254451fe192a202bfd8551017fea2a881bf75154405ff28aa202df94551017f8a2a880b7c5154405fa28aa202ffd0551017fc82a880bf64154405fe20aa202ffcc551017fc62a880bf63154405fe18aa202ffc8551147ee42a880bfe2154405fe10aa202fd08551007fec0a8802ff605444fff302a201bf98151007fac0a889ffc60544037e302a206ffd4151036fea0a881bfe505440dfe282a22affd015113ffc80a889ffc4054453ff982a227ff8c15113ff860a88a3ff205444fff102a227ff08151017fe20a880bf71054405ff082a202ff04151007fecaa0802ff655044dff32a8206bf99541007facaa0802fd655044dfe32a8206bf19541015fec8a0817ff545044ddfaa28205ff9514102ffaa8a0817fc545040bde2a28200ffd8d41005fec6a0897fe63504097f31a8200ff58d4112ff8c6a0812fc635044dffa9a8225ff94d41007faa6a0897fc535040bffa1a8205efd0d4102ffc86a0817fd4350401dea1a8205ff10d41007fec4a0802ff6250449ff3128203bf98941007fac4a0893fc62504077e3128226ffd4941127fca4a0803fd5250449fe2928205ffd094102f7e84a0817fe425040bfea128200ef5094102ff884a0897ff3250449ff1928200ff4c941127f864a080aff6150405ffa8a8202ff94541017eca2a080bfd5150401faa8a8202ff14541017fe82a0817f74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ffcc54112fee62a080bfe3150405fe18a8202fd0c541017fe42a080bfe2150405fb10a8202ff08541007fec0a0802ff6050447ff3028201bf98141007fac0a088ffc60504037e3028226ffd414111ffca0a088ffc505040bffa028205efd014102ffc80a0817fc405044bff9828223ff8c14111ff860a0893ff2050447ff1028223ff08141017fe20a080bf71050405ff0828202ff04141007feca98802ff654c445ff32a6206bf99531007faca98802fd654c445fe32a6206bf19531007fec898802ff644c443ff3226205bf99131007fac898802fd644c443fe3226205bf19131117fea898887fe544c401feaa26221ff15131015fec698813ff534c409ff29a6204ff54d31027f8a698813ff434c409ff21a6204ff50d31027f88698803ff624c4017fb126220ff9893101dfcc498803fd624c441fe3126203bf18931117fea498883fe524c401fea926220ff1493110ffe8498883fe424c401fea126220ff10931027fe6498813df324c409ff1926204ff4c9
  | 4 => 0xcffc405486bff982a433ff8c15219ff860a900fff2054807f7902a403ff8815201ff840a90d3ff1054867ff082a433ff04152007fecaa1002ff6550865ff32a8406bf99542007facaa1002fd6550865fe32a8406bf1954201dfec8a1017ff545080bff2a28405ff5514202ff8a8a1003ff63508017fb1a8431ff98d42025fcc6a1003fd6350863fe31a8404bf18d42197fea6a10c7fe5350801fea9a8431ff14d4202ffe86a1017fe435080bfea1a8405ff10d4201dfec4a100fff5250807ff2928403fb9494201ffaa4a1003ed5250807fe2928403ffd094202fde84a100ffe4250807df2128403ff1094201f7884a100fec4250807ff9928403ff8c94201ff864a1003ff61508017fb0a8430ff98542015fcc2a1003fd6150861fe30a8402bf18542197fea2a10c3fe5150861fe28a8405ffd054202f7e82a1017fe415080bfe20a8431ffcc542187fc62a10c3fc3150807ff90a8403ff8854201ff842a1003ff60508017fb02842fff9814200dfcc0a1003fd605085ffe3028401bf18142197fea0a10bffe505085ffe2828405ffd014202f7e80a1017fe405080bfe2028431ffcc14217ffc60a10bffc3050807ff9028403fbc814201ffc40a100ffc2050861ff882842fff8414217ff820a1003ff654c8017fb2a642eff99532035fcca99003fd654c8017eb2a642eff19532035f8ca99003ff644c8017fb22642dff9913202dfcc899003fd644c8017eb22642dff1913202df8c8990bbff544c85bff2a26400ff5513216ff8a89900eff634c809ffa9a642ef7d4d32027fca699013fd534c809fe29a6404f714d32027fe8699013fe434c809ef21a6404ff50d32007ba8699013fc434c8077fb126403ffd493201ffca49900fee524c807fea926400fb5493201ff8a49900fff424c85bf7a126403ff9093201ffa849900ffc424c807f62126403ffcc932027de649900ffe324c807ef1926403ff0c93201fb8649900fec324c801ffb0a6400bfd8532167fcc29900afe614c801feb0a642cff18532015f8c2990bbff514c859ff28a642cff1453216ffe82990b3fe414c859fe20a6404ffcc532027be6299013fe314c809fe18a6403ffc853201fde429900ffe214c807fe10a6400ffd8132005fec0990affe604c8037f3026400ff5813215ff8c099006fc604c85dffa82642bff9413215ff8a0990b7ff404c857ff202642bff10132027fe6099013df304c809ff1826404ff0c13201ffe409900fef204c807ff1026403ff08132167fe20990affe104c857fe0826402bfd9551007fec8a8802ff6454455ff322a205bf99151007fac8a88abfc645440b7e322a206ffd5151037fca8a88ab7e545440dfeaa2a206ff15151036f8a8a8803ff63544017fb1aa229ff98d51025fcc6a8803fd6354453fe31aa204bf18d51037fea6a881b7f535440df
  | 5 => 0xc953027f864a9803ff6154c017fb0aa63cff98553015fcc2a9803fd6154c79fe30aa602bf18553037fea2a981b7f5154c0dff28aa606ff145531f7fe82a98f3fe4154c79fe20aa604ffcc553027fc62a9813fc3154c7bff90aa63cff885531e7f842a9803ff6054c017fb02a63bff9815300dfcc0a9803fd6054c77fe302a601bf18153037fea0a981b7f5054c0dff282a606ff141531f7fe80a98effe4054c77fe202a604ffcc153027be60a9813fe3054c09fe182a63dffc81531dffc40a98effc2054c79ff882a63bff841531dff820a9803ff6550c017fb2a863aff99543035fccaa1803fd6550c017eb2a863aff19543035f8caa1812ff6450c0bffaa28605ff9514302f7ca8a1817fd5450c01deaa28605ff15143025fec6a1813ff5350c09ff29a8604f794d43027faa6a1803dd5350c09fe29a8604ffd0d4302fbe86a1813fe4350c09df21a8604ff10d430277886a1813dc4350c01ffb128600bfd89431cffcc4a180efe6250c01feb128639ff1894301df8c4a18ebff5250c73ff2928639ff1494302ffe84a1817fe4250c73df2128605ff1094302f7884a1813ff3250c09ef9928604ff8c943027f864a1803ff6150c017fb0a8638ff98543015fcc2a1803fd6150c71fe30a8602bf185431d7fea2a18e3fe5150c71fe28a8605ffd054302f7e82a1817fe4150c0bfe20a8604ffcc543027fc62a18e3de3150c09fe18a8604f70c5431cffe42a18e3fe2150c71fe10a8600ffd8143005fec0a18dffe6050c037f3028600ff581431bff8c0a1806fc6050c75ffa828637ff941431bff8a0a1817ff4050c0bdfa028605ff9014302ff880a1813ff3050c09ef9828604ff8c143027f860a18e7ff2050c6fff1028637ff081431c7fe20a18dffe1050c6ffe0828603bfd9552007fec8a9002ff645486dff322a405bf99152007fac8a90dbfc645480b7e322a406ffd5152036fea8a901bfe545480dfeaa2a400df55152037f8a8a9003ff63548017fb1aa435ff98d52025fcc6a9003fd635486bfe31aa404bf18d52037fea6a901bfe535486bbf29aa406ff54d52037f8a6a901b7c535486dffa1aa435ff90d52007fa86a90d7fc43548077fb12a403ffd4952037dea4a900ffe5254807bf292a403ff1495201ef8a4a900fec5254807ffa12a403ff9095201fdc84a900ffc4254807ff992a403ff8c95201fdc64a900ffc3254801ffb0aa400bfd85521a7fcc2a900afe6154801feb0aa434ff18552015f8c2a901bff515480dbfa8aa406ff94552037f8a2a90dbff4154869ff20aa434ff105521affe62a90d3fe3154869fe18aa403ffc855201ffc42a90d3ee2154807fe10aa403fb08552007fec0a9002ff6054867ff302a401bf98152007fac0a90cffc60548037e302a406ffd4152036fea0a901bfe505480dfe282a436ffd015219ffc80a9
  | 6 => 0xc00400000800000400000c00000000400400800000000000000800000000000400000000800000400400000c01800000000400000000c00000400002000800000002401002800000400000800000000000400000000000800000000400000400000400000000000400000400800000000800800001400402000001400000000000800c00000001401000000800001400000400400c00000400400800000401400000400400000000000000400800000000000000400800400c00800000000000000000000000c00000001000400000000000c00000400800001400000400000000000001000400000400800000400c00000000000400000000000c00000000400000800000000400800000400400000000800400400400400400400000400400000000c00000000000001400400000800000001800400400000800000000400000000000800400000400000000001c00801c00000000000000400c00000400000800000800800000400001401400400000c00400000800c00000000400401000000000000000000000000000000000c00000000000400800000001000c00000000400800003400c00000000000400800c00400c0000000040040040000080080000000000040000080000000b7fb2aa805bfd915402ffea8aa01bbf545500bff2a2a805df9515402ff8a8aa0177c545500bde2a2a800ffd8d54005fec6aa10bfe63550097f31aa800ff58d54217f8c6aa012fc635500dffa9aa806ff94d54037f8a6aa017ff435500bdfa1aa805ff90d5402ff886aa003ff62550017fb12a841ff9895401dfcc4aa003fd6255083fe312a803bf18954037fea4aa01b7f525500dff292a806ff1495402ffe84aa017fe425500bfe212a842ffcc95420ffc64aa107fc3255001ffb0aa800bfd8554207fcc2aa00afe6155001feb0aa840ff18554015f8c2aa01bff515500dff28aa806ff1455402ffe82aa017fe415500bfe20aa842ffcc554207fc62aa103fc3155083ff90aa840ff88554207f842aa003ff60550017fb02a83fff9815400dfcc0aa003fd605507ffe302a801bf18154037fea0aa01b7f505500dff282a806ff1415402ffe80aa017bf405500bff202a805ff10154217fe60aa0fffe305507ffe182a841ffc81541fffc40aa0fffc2055081ff882a83fff841541fff820aa012ff6554c01ffb22a600bfd91531f7fcc8a9816fe6454c01feb22a63eff1915302df8c8a981bff5454c0dff2a2a606ff55153037f8a8a9812ff6354c09ffa9aa606f7d4d53027fca6a98137e5354c09fe29aa604df14d53027b8a6a9813ff4354c09ff21aa604f790d53027f886a9803ff6254c017fb12a63dff9895301dfcc4a9803fd6254c7bfe312a603bf18953037fea4a981bfe5254c0dfe292a63effd09531effc84a98f7fc4254c09ff992a604ff8
  | 7 => 0xd00012a8000000001a500028e8000000000000000001cf00000000000000011900020180000010d09828d0449f50be25900000021d2490ee0002941a10c825d2c1ab40000000bb9710000001b216cac000000000015615ea461028000581eb1fa0339af9229c798d80000000000028300022500005500000000023b80000000000001500000000027700000000000000009380015280000000014d8000000001b11b6aa08000000000000000000000fe0000000001f100010b00008280027a0c38000001179300000000000000000002188000060d58002c58000001b79cf8000002bba668000001f880000005a000095160142aa309a00000000000012e0000b99349648000000000000000002418000000000000000000000000001ae00000000027400000000017380000000005280021b0ff0000002ce1cc00000000000022900028380000022200000000000000000000000016d8000000000000ab17580001ba5b80018ba0209f80019500000e98025ca8891180025980000000000000029ea8ba631961c30000000000002b10de80000000000003680028d92b80000000000000019400017daaf80000000000004e9fc8931ca80000022322800006d0000000000000002028e980000c00009c0000000cf80000000000000000000000000000018d00000003600013580000000000000002000001680017814180000000000002206691a00000000018c00000000000000010c8000cba660000d0ad0aaa9910002bc9cd00000000000022a2cba900000001fb80010f8000000000b48000000000000000002cc8000000d314c03f800000000150a7c0000001369728001b50000ad17b8000002958000000001970002000000000000000000000001a4000000000000000000236800000072834a5b0461569400001c42228000000002c41fe00000000000000024e8e190c00012f9ed8649918b88000ed8000bda4b8000090000002658a100014d2a014e8000001ad23f0000830000009b18000000e804f8511982c685700000012d8ec00000000000003980000016e000800400400400400400400c00003c00000400000400400000000000000800000000400000400000000400000001800000402000400000400000000000000800400000c00800400800000400000000c00000000000000000800000400000800400000800000000000400000000000000000000001000c00000000c00000000400400000000001400800000002800400000400000000001000000c00000000000000800800000000400000000400400000000000000000400003c00000000400000801800400000000000000800000000400000000000c00400000c00800000400400000400002800800000000c00000000000000400000800800001000000000000000c00c000
  | 8 => 0xc91d98001670000001d6000261886800088000000000233ab500004ca990000000000000000000000000000000000000cc0f01be2d18000000000000000000458000002580000002ab24f8000000000001c08088002798000a300000000000000000006200020f8000000000000000000000000000001998dc86e00000029200006b00020a2ca83c00017ca062951390f4050800000000056ac9aa7000039000000116100800076ab320ca3892994102e9e88000189a900000000000000000000000000b22f8001da2218000000cc80007828f0000000000e700000029785f0000002a78001db0000000000122b20318000000000000000002bb0c20e20000000000000000000000001eb8000000000538002470000ac8000001e980000013e0000002449820000000000000000001779070001a30000000000000002a980015982b9a02780450000000d500000a0000002bf02ca758000f200000000000000000000000007c80013500000001800003a0000000000000ce0000000000049a20000638000000000000002190000000001448000b6a390002178000000000000000000000f88001250001db80009c80000000000010582480011c80008500009e80000000000000020a800145ad28000000000a029b00014f80016a0eb000000000000000000000000066168a99a0d1968350000000000000000000000000001d503780000009080000b94e2330000978000000000000160001530000000000000000000000000000ce8b58000000000002108af8000002612bd0001cc9d58bc800060a298000000000000000000001a680000029c80000018ea398001b00fd838848a5389427795d94797a0b00f0855891a749930ca8ba0e300015c80018916180020590980000f83300015b8000000000001ae80018a8f28002802c51830000000530002bd8002988000000000000000000002cf2709fd15f00000014300000000000000000000000000000014b0000000000000b29628000000002b389980000000000018580000000002d9bc1809a98cd80021c80000000000000000000000010880004a8a19bd0000000001c22818000000000000000000000000000000000630000000000000000ad8000000001760000000b80a98000000000000000d72578018000000001a48000000000000289ac81980000004680007b80000000000005018f8000000000001f480000000010a8000000000000000000000000000000fc80000000016780000000000000000007380007c11400000000000000000000000d80000000000000000000000000009b8002ae0000000000000000e525600015100000009d0f68000000bf27f80000000000000000000014f09f0f90000001c90000000000b18002268000001f085e0000000000000000ac00000000
  | 9 => 0xaaaa880000000000000011e80007a00000000002f0849c58760b780014600019e0000000000000000000000000c10429c29032149420000000000001948e78000000000000001e804e0002110da0d7a438000000320000002541638000000000000c89a8800000000000000000137800106a860000000000000000000000000000000b080018f0000001e000027523c8000000000000000000000001f280017910b80000001300002c00000000000000000000004919f08babe80000012695400000026aa1680012e9110000d68000000000000000a298800000000000a800000000078a242691c6abe1860fb1dda9280413d9990000000002a280000014c8000000001f383b86920e80000000008aaa480000000000000000000000000000000000000000008891a9aa00000025482a80000000000000000000000024816b0d90000000000000001769bb00000000000000000000000000028c80011525a0000000000e00b900029a9f30309bf1f78372682b580004f0000001ad80000025e183a5e80000000000000000000015180016e8000520000001470e588388d89000000000000000000000000000000000000010100000017080000027d00000000013f8a50000000000001f40000a92500fd2b68000000002a60000000000442c88000870e48000000001d42aca320000be820a6b8149320000000002d10000418b20000002848000000002488000578000001b30000000d18000002620001901a8237858854a688000000000f484a04d8000000000002510001170000000000000000001e49b380006b8000000001c8000000000000125a258000000001398590000000000000000000002049240000000000000000000001e78000000000000000000001e90da8000002b497aa440001038000e28002c080000000000025080028580000000026780000000000000000000025d8000290000002b00e89e192a00028e2138000000000a40001f900000000000008c00017480000024680000014980000019a800000000157992a3800000000000000000002703d800000000000159251a170030000000000000000001548000000000002788000000000000000000001c8901a762a180000022600000016c16f8000002af0000000000002aa2a40000798000000b380000014a8c58000000001149ce00018495022b0000000000000001aa8fe8000c70000000001b900000000004b8000000001d280028200005bacd2308601bba2110a000000000000000000085ad205d00000000008a0000000002b19f986d8000000000000000000000000000000000680000840000000bd26c8000000340000000001ff15a88f97200006a0e6000091009a909b080000000000000013180000029a0000000000560001a380013800022f2038000000f9800
  | 10 => 0x69138000002ca00003e26c16991b0000000002700e90002b70000000001f60000000000000800000f82c90000000000000920000000f600000021e0000d60001d000000000027e09480024d8000000299490000000a38000b600000000000013b0000001fb00000026480000000000019a26703b2131340000000000000000001cb00000003d27c86581080000000000002b0000000002a681a0000000899d30000000002ad8000002318000000000000000000000000000000000000000002608000000000a7a698000000000000311c10002b280000000000000000001b01f15a00019c00000000000008e0038ae02f80002398b0408000000000002b79210001ea293a159938001488000000000000001310000000961ec00020411f0470e0825a810000000000000000000000000000002300d00ca0000a887024a8f700000000026f8001278000000000000000000001558000cb0d882101d1c700000000021b8002248000000000000000000000b30001c000000027d80018ca638000000d106183f2408000000000000fa8002ba06700000012308c8000000001f695d13b84b0b50000c495c28980000014696100022e0000000c2ad40000001d680023426e8058000001e32cd8000002c700000023e80026d1b711d8001f80000000000000002d319d8000598001b58000d980000000c8790000000000f10001e100000000000016200023d24b0001da8a80000000000002c780e0c00b11c480000000000000000000000000000019c9898000000079a7800165a0693f000041065104000000000000212049800000000000000000000000280800000000000011aa91d80001339f700023588200000000000000000017e00280022ea840f31ef21000024e00015b00000005d8002cc00000000000026b0000000000001770002cb00000000021c00000029e00000000000001380006c8001d48000001de0002328002a200000023b0a600000000000000012700000000000000012f00020880000000016d0178000000000000cd00000026000025214a00000000021f18e2528c79309c180016900008ea1fa981f180000000000007d00000000000000000006288900000000000000010500000000000000000000020500000011300020d8000000000000000001b60000000000000000000000002970000b408780000000000000000000000000000000000006f80000029c0000000000f79681ab80000008d0d380015e0002b984c00001591c0000000000000001208002bf93c80000010629b8000000000000000002918001e58278000e427a80007f0000000000262b0a411520000080001e68000000001e20000001f212389723e0000000001b280028a8000000000000001798dc00000000000000020780025f96a8000000000000001958
  | 11 => 0x1ffa718d297c0000001be80018100000000000011993d1660000000001ed0001249440000a709b20f0db1261f02c10002b90000808000002588000000000000000000000000000000000001878302c80140002570000241c980000000000022701e2968001dd00022d80000000000013a80029d00000000000000000000000000000000017e80000000000012900012000000000000001c80000000000006f0aea45000112a828000000358000000000002428000000000001a58000d817b1a08218000000000fb8c30478000000000002650000a68001fa9b98772768000000001df1ab00000009d83ea3c19b96680001728a2790000000000000000000df00004000012b24980000000000000023f86400000002e27e80022080016b8000000000000000000000000051080002738002c480011b80027100000009900000000000029497020bac300000026e0110000ea80000000001a8ef00007d8001e50000d400020e0000000000000000001750000000000001e600017fa86a3d8cf2421d7800000077a4c0000002350000000000818f580000000000000700000000000000000000000000000000000006e80000000015f80000000000027b0000000000000000000000000fc0000000000ec86100000000000017423a00000021400000000000024a1122558000001c38000000000000002152850000001330000002081c62c200000000000000000017881280005f80000006c00000000000000000000000f2a50000000000001909828000001df9100d48000000000000860000000000000000000678000001cb81f8000000002288000000000000000000000000698dba7ba8781d9438001bcaab8000001108000000000000000001288001d0a7298529f25680000020c28c1580dd800000000000000000136000000000000000000104a5f000075a3a8000000001fd8000000000001dc0000000000000000001bdac62930001fc1d880023600000008b0001ea80000018a24587e8000000250000000001888000001ec9d18000000002478002a58000000c600000000010200009e0a091582280000000000000000011f9ba00006a9de80000000000000000019781c0e100005c0000bf8000000000000380001bf8000000000ba8518000002091e38001d100011e2182400000001f580012800000000000029f8000000002530000002b880028921993a00000000000000005ea960000000000000000000001dc8000000000000000010000000000000000001d3acf8000000000000000000720000000001188000000000002881d22722b60000001ee2910c19a1a4c92c262a12aad00000000000000000026d9730000a58fa12200000000000019f9ca0000000000002279388001e400016093299b00000000000000018
  | 12 => 0x22c8c40002238000000000000000000710002030000000000000000000001e71b800000000000000024300000003280005a80021daa3a2b9169370bb0000002ae80013eaa10000000000000190000000000001af0268e38000d227300000000000000000018180000005413c0280000001cda5a8ff80000000022aa4f17f1d70000000742348000001078000001408002d48000000000000000002160000000000a200010e9b400007b0000df8000000f18000000000ea00012d000198a00ad000000000001e80000000000022d0002a803a8aa25c00000000000000000000000000000000015500009280000007519d0ab9fe89a9872010001ac0000002b82070420000000000000000000000000000000958730001a291d00000000000000000000004380021a14500010f28f80007f8bc00020b23100017d00002d00000000003c8000002550000000000230001ee80000000000000014800000024d00019200680028700000000000000000000000000008f0002ce8000000000000000000000de00014b8000000000000000000af00000000000000000028b00000016416f0dd1c50000000000ef9219a60000000000000001182ac0b710d8f38000480001d90000000ed1840002370748000000000c0a1ea6a00007e0000000001000000000000000000000000000000000000000000718000000000000000000000000000e68ee8988000000000000000000000000000000000001588102ba8000000000000000a48000002c380000000000000000000015700000000000000019e8f52098c98709b49ef8000000000000000000000000000001e28001630810000002c28000000001cea6f00000000021a80022c2640000000000430000001090000688eb8001a70000001650001e08c684d00002a10e0000001718000000c500000029d8000000000001ba92c8000968000000000000000000001b885ca200002bc00000027f00000005b15380000000000000000000021180007a8022d3800
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x4705451013ff07054510016f76054510017f3605451013f77505451013f75505451013ff2305451013ff2205451000df4765051002ef4765051000cf47650510005f77550510005f57550510006f76550510006f56550510015f77450510017b77450510007b7645051002ef6645051002ef4645051004fb4645051021fb7545051004fb45450510005f7735051012ef6635051012ef4635051004fb74350510007b54350510005f77250510006f76250510006f5625051004fb74250510007b54250510007f3705051000df6705051000df4705051011ff07050510016f76050510017f3605051011fb7405051011fb5405051011ff2305051011ff2205051000df4764c510026f4764c51000cf4764c510005f7754c510005f5754c510006f7654c510006f5654c510005f7744c510005f5744c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510005f7724c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100fff0704c510016f7604c510017f3604c5100ffd7304c5100fff2304c5100ffd5304c5100fff2204c51000df4764851001ef4764851000cf47648510005f77548510005f57548510005f77448510005f57448510006f76448510006f56448510005f77348510005f57348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851003fe63248510007e53248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100dff230485100dfe720485100dff220485100dfe52048510015f8764c110026f8764c110014f8764c110006fb654c110006f9654c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110047d8634c110047da534c110007d9534c110047da434c110007d9434c110005fb724c110047db324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c11000efb614c11000ff3614c11007ff2514c110007f1514c11007ff2414c110007f1414c11007fdb314c11007ff2314c11007fd9314c110047f1314c110007d1314c11007ff2214c110007f1214c110015f8764811001ef87648110014f87648110006fb6448110006f96448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811001efa624811001ef8624811003fe8624811003fea5248110007e9524811003fea4248110007e9424811003fea3248110007e93248110007f37148110015fa7148110015f8714811005ff0714811000efb614811000ff3614811005ff25148110007f1514811005ff24148110007f1414811005ff23148110007f1314811005feb214811005ff2214811005fe9214811003ff12148110007e12148110
  | 1 => 0x5110004fc7655110015f67155110024fe76d8d10046de63d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d10006df53d8d10046dc53d8d10046de43d8d1001cfe72d8d10004fd72d8d1001cfc72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10266f651d8d10266df31d8d10266dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10256df30d8d10256dd30d8d10024ff7658d10046dc6358d1024df77158d1025dfb7058d10004ff7558d10034fe7558d10034fc7558d10004ff7458d1002cfe7458d1002cfc7458d10254ff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d10046df3258d1024cff7158d10006f77158d1007ef65158d100fcff7058d10006fb7058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100367e6554d100067d6554d10015f67154d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1002ebe6450d10006bd6450d10006df6350d10026dc6350d10015f67150d101c7d63150d1001cfe76d891003eee62d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d891003eee52d8910006ef42d891003eec42d891000cff71d8910014fe71d891000cfd71d8910014fc71d8910246f641d8910246ef21d8910246ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910236ef20d8910236ed20d891001cff765891003eec625891022df7715891023dfb7058910004ff7558910034fe7558910034fc7558910004ff745891002cfe745891002cfc7458910004ff7358910024fe7358910024fc7358910234ff7258910006ef725891003eee325891022cff7158910006f7715891005ef641589100dcff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc76549100367e65549100067d6554910006ef625491001eec6254910015f671549101a7e62154910004ff7650910004fe7650910004fd7650910004fc765091002ebe6450910006bd6450910015f67150910004ff764c910004fe764c910004fd764c910004fc764c910026de634c910006dd634c91001eee624c910006ed624c910015f6714c91000dfa704c91000df47654510036f4765451000cf47654510015f77554510017777554510007776554510036f66554510036f46554510057746554510005f77454510006f76454510006f56454510227765454510057745454510005f77354510006f76354510006f56354510057775354510007755354510005f77254510146f66254510146f46254510057775254510007755254510007f3705451000df6705451000df
  | 2 => 0x6ef6348520006ed634852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005fe64148520007e54148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200dfea40485200dfe710485200dfea104852001df8765012002ef8765012001cf87650120006fb6550120006f9655012000dfb745012000fbb7450120007bb645012002efa645012002ef8645012006fb8645012006fba5450120007b9545012006fbb4350120007b94350120007eb725012001dfa725012001df872501200a7e8725012000efb625012000feb62501200a7ea5250120007e952501200a7bb42501200a7ea42501200a7b9425012006fe94250120007a942501200a7ea3250120007e93250120005fb715012006fbb4150120007b941501200a7eb2150120007e92150120034fe76d95100567e65d951013cfd75d951002cfe74d9510004fd74d951002cfc74d9510024fe73d9510004fd73d9510024fc73d951001cfe72d9510004fd72d951001cfc72d951000cff71d9510014fe71d951000cfd71d9510014fc71d95102a67f51d95102a67d51d95102a6f641d95102a6f631d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102967f50d95102967d50d9510296fa30d9510034ff76595100567c6559510005df7359510045dc735951028df7715951029dfb7059510294ff75595100067f7559510004ff745951002cfe745951002cfc7459510004ff7359510006df7359510004df7359510024fe7359510024fc7359510006dc7359510024dc73595100567f5359510004ff725951001cfe725951001cfc72595100567f525951028cff7159510006f771595100bef641595100bef6315951013cff7059510006fb705951013efa305951002cfe76d911004ebe64d9110034fe75d9110004fd75d9110034fc75d911011cfd74d9110024fe73d9110004fd73d9110024fc73d911001cfe72d9110004fd72d911001cfc72d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110286f651d9110286bf41d9110286bd41d9110286f621d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110276bf40d9110276bd40d9110276fa20d911002cff765911004ebc6459110005ef725911003dec725911026df7715911027dfb7059110004ff7559110034fe7559110034fc7559110274ff7459110006bf7459110004ff7359110024fe7359110024fc735911004ebf4359110004ff7259110006ef7259110004ef725911001cfe725911001cfc7259110006ec725911001cec725911004ebf425911026cff7159110006f7715911009ef6515911009ef6215911011cff7059110006fb705911011efa2059110004ff7655110004fe7655110004fd765
  | 3 => 0xf7058d20006fb7058d2015efa1058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2001dee7254d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d2002ebc6450d20026de6350d20006dd6350d2001dee7250d201cfae4250d2000dec7654920036ec765492000cec765492001def755492001f6f75549200076f6554920036ee6554920036ec65549200776c6554920005ef7454920006ef6454920006ed64549200776f54549200076d5454920005ef7354920006ef6354920006ed63549202c76e53549200776c5354920005ef71549201a6ee61549201a6ec61549200776f5154920007eb705492000dee705492000dec705492019fe8705492001eef605492001feb605492019f6f505492019f6d505492019fea405492019fea105492000dec765092002eec765092000cec7650920005ef7550920005ed7550920006ef6550920006ed655092001def745092001faf7450920007af645092002eee645092002eec645092006fac6450920005ef7350920005ef715092006faf4150920007eb705092000dee705092000dec705092017fe8705092001eef605092001feb605092017faf405092017fea405092017fad405092017fea105092000dec764c920026ec764c92000cec764c920005ef754c920005ed754c920006ef654c920006ed654c920005ef744c920005ed744c92016eee644c92016eec644c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c9202bfcf534c920067cc534c920067ce434c920007cd434c920005ef714c920067cf314c920007eb704c92000dee704c92000dec704c92015fe8704c92001eef604c92001feb604c92015fea404c92015fcf304c92015fcd304c92015fea104c920014fe76d852005ef661d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d85202b6ee32d8520006ed32d852005ef651d8520006f731d852005ef431d852005ef621d85202b6f521d852000cfe70d852001cfd70d852000cfc70d852022ef710d852005ef461585202adfb7058520004ff7654520004fe7654520004fc76545200367e65545200067d655452001dee72545200076d5254520006f76154520016f46154520147e72154520004ff7650520004fe7650520004fc765052002ebe6450520006bd645052001dee7250520007ad4250520016f6615052000dfa7050520004ff764c520004fe764c520004fc764c520026de634c520006dd634c52001dee724c520007cd324c52000dec7648520016ec764852000cec7648520005ef7548520005ed7548520005ef7448520005ed7448520005ef7348520005ed7348520
  | 4 => 0x41300977b52541300077952541300cfdb3254130007d93254130005fb71541300977b51541300077951541300cfdb3154130007d93154130034fe76d95200767e65d952019cfd75d952002cfe74d9520004fd74d952002cfc74d9520024fe73d9520004fd73d9520024fc73d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203267f52d95203267d52d9520326ee42d9520326ee32d9520014fe71d9520004fd71d9520014fc71d952001cff70d952001cfd70d95203167f50d95203167d50d9520316fa40d9520034ff76595200767c6559520005bf745952006dbc745952030def725952031dfb7059520314ff75595200067f7559520004ff7459520006bf7459520004bf745952002cfe745952002cfc7459520006bc745952002cbc74595200767f5459520004ff7359520024fe7359520024fc735952030cff7259520006ef72595200c6ee42595200c6ee3259520004ff7159520014fe7159520014fc71595200767f515952019cff7059520006fb705952019efa405952002cfe76d912006ebe64d9120034fe75d9120004fd75d9120034fc75d912017cfd74d9120006bf54d912006ebc54d9120024fe73d9120004fd73d9120024fc73d912006ebf43d912000cff72d912001cfe72d912000cfd72d912001cfc72d9120306ee52d9120306bf42d9120306bd42d9120014fe71d9120004fd71d9120014fc71d912001cff70d912001cfd70d91202f6bf40d91202f6bd40d912002cff765912006ebc64591202edef72591202fdfb7059120004ff7559120034fe7559120034fc75591202f4ff7459120006bf7459120004ff7359120024fe7359120024fc73591202ecff7259120006ef72591200a6ee5259120004ff7159120014fe7159120014fc715912006ebf415912017cff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc76551200367e65551200067d655512001dee7255120024fe76d8d20066de63d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202e6ee52d8d202e6df32d8d202e6dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d202e6ef21d8d2001cff70d8d2001cfd70d8d202d6df30d8d202d6dd30d8d202d6fa10d8d20024ff7658d20066dc6358d202cdef7258d20005f77158d2005df47158d202ddfb7058d20004ff7558d20034fe7558d20034fc7558d20004ff7458d2002cfe7458d2002cfc7458d202d4ff7358d20006df7358d20066de4358d202ccff7258d20006ef7258d20086ee5258d20004ff7158d20006f77158d20004f77158d20014fe7158d20014fc7158d20006f47158d20014f47158d20066df3158d20086ef2158d2015cf
  | 5 => 0x1cfe76d8930086ee62d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d893034ede43d8930006dd43d8930086ee32d893034eed32d8930014fe71d8930004fd71d8930014fc71d893034edf31d8930024fd70d89302ceef20d89302cefa10d8930086ec6258930005f7715893007df47158930345fb7058930004ff7654930004fe7654930004fc76549300067f65549300367c6554930025de73549301af5e535493001eee6254930004ff7650930004fe7650930004fc7650930025de735093000ddc764c93001edc764c93000cdc764c930005df754c930005dd754c930176de654c930176dc654c930005df744c930005dd744c930006df644c930006dd644c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c930087ce524c930007cd524c93033fcf424c930087cc424c930005df714c930087cf214c930007db704c93000dde704c93000ddc704c93015fd8704c930026df604c930027db604c93015fda504c93015fcf204c93015fda104c930014fe76d853007ef661d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d8530336df32d8530006dd32d853007ef641d853007ef631d8530336f531d8530006f721d853007ef421d8530024fd70d853024ef710d853007ef4615853032dfb7058530004ff7654530004fe7654530004fc76545300367e65545300067d6554530025de73545300075d5354530016f6615453000dfa7054530004ff7650530004fe7650530004fc765053002ebe6450530006bd6450530025de73505300079d4350530006f76150530016f4615053012fd7315053000ddc764c530016dc764c53000cdc764c530005df754c530005dd754c530005df744c530005dd744c530005df724c530006df624c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6514c530007d5514c530007db704c53000dde704c53000ddc704c5300ffd8704c530026df604c530027db604c5300ffda504c5300ffd7104c5300ffda104c530004ff7648530004fe7648530004fc7648530025de7348530005dd734853001eee6248530007cd3248530025f87654130036f87654130024f8765413000dfb755413000f7b75541300077b6554130036fa6554130036f86554130097786554130006fb6454130006f964541300977b5454130007795454130007db7354130025fa7354130025f873541300cfd8735413000efb635413000fdb63541300cf7b53541300cfda53541300cf795354130097d953541300075953541300cfda4354130007d9435
  | 6 => 0x942541400b77b51541400077951541400d7bb4154140007b94154140034fe76d95300967e65d95301dcfd75d953002cfe74d9530004fd74d953002cfc74d95300067e54d95300967c54d953000cff73d9530024fe73d953000cfd73d9530024fc73d95303967f53d95303967d53d9530396de43d953001cfe72d9530004fd72d953001cfc72d95300967f52d9530014fe71d9530004fd71d9530014fc71d9530024ff70d9530024fd70d95303867f50d95303867d50d9530034ff76595300967c655953037ddf735953038dfb7059530384ff75595300067f7559530004ff745953002cfe745953002cfc745953037cff7359530006df73595300cede4359530004ff725953001cfe725953001cfc7259530004ff7159530014fe7159530014fc71595300967f51595301dcff7059530006fb705953002cfe76d913008ebe64d9130034fe75d9130004fd75d9130034fc75d91301bcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d9130376de53d9130376bf43d9130376bd43d913001cfe72d9130004fd72d913001cfc72d9130376df32d9130014fe71d9130004fd71d9130014fc71d9130024ff70d9130024fd70d9130366fa50d9130366bf40d9130366bd40d913002cff76591300057f75591300957c755913008ebc645913035ddf735913036dfb7059130004ff75591300067f75591300047f7559130034fe7559130034fc75591300067c75591300347c7559130364ff7459130006bf745913008ebe545913035cff7359130006df73591300aede5359130004ff725913001cfe725913001cfc72591300aedf3259130004ff7159130014fe7159130014fc715913008ebf41591301bcff7059130006fb70591301befa5059130004ff7655130004fe7655130004fd7655130004fc765513002ebe6455130006bd6455130025de735513000ddc7654d30036dc7654d3000cdc7654d30025df7554d300275f7554d300075f6554d30036de6554d30036dc6554d300975c6554d30005df7454d30006df6454d30006dd6454d30005df7254d30005df7154d300975f5154d30007db7054d3000dde7054d3000ddc7054d301dfd87054d30026df6054d30027db6054d301df5f5054d301dfda5054d301df5d5054d301dfda1054d3000ddc7650d3002edc7650d3000cdc7650d30005df7550d30005dd7550d30006df6550d30006dd6550d30025df7450d300279f7450d300079f6450d3002ede6450d3002edc6450d3008f9c6450d3008f9e5450d300079d5450d30005df7250d303579e4250d3008f9c4250d30005df7150d301c6de6150d301c6dc6150d3008f9f4150d30007db7050d3000dde7050d3000ddc7050d301bfd87050d30026df6050d30027db6050d301bfda5050d301bf9f4050d301bf9d4050d301bfda1050d30
  | 7 => 0x8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89400a6ee42d89403beed42d89400a6ee32d8940014fe71d8940004fd71d8940014fc71d89403bebf41d8940006ee21d89400a6ec21d894002cfd70d89402eeef20d89400a6ec62589403b5fb7058940004ff7654940004fe7654940004fc76549400367e65549400067d655494002dbe74549400073d545494001eee625494000dfa705494000dbc765094001ebc765094000cbc7650940005bf7550940005bd7550940005bf735094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400a7ac62509400a7ae5250940007ad5250940005bf7150940007bb705094000dbe705094000dbc705094017fb8705094002ebf605094002fbb605094017fba505094017faf205094017fba2050940004ff764c940004fe764c940004fc764c94002dbe744c940005bd744c940026de634c9400079d434c940006ef624c94001eec624c94016faf424c940014fe76d854009ef661d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540024fe73d8540004fd73d8540024fc73d85403aebf43d8540006bd43d854001cfe72d8540004fd72d854001cfc72d85403aebf42d8540006bd42d854009ef641d85403aef541d854002cfd70d854026efa20d854026ef710d8540005ef72585400a5ec725854009ef461585403a5fb7058540004ff7654540004fe7654540004fc76545400067f65545400367c655454002dbe74545401573e5454540016f6615454000dbc7650540016bc765054000cbc7650540005bf7550540005bd7550540136be6550540136bc6550540005bf7350540006bf6350540005bf7250540006bf625054002dbf715054002fb77150540007b76150540016be6150540016bc615054009fb4615054009fb65150540007b5515054039fb7315054009fb4315054009fb62150540007bb705054000dbe705054000dbc705054011fb8705054002ebf605054002fbb605054011fba505054011fba205054011fb71050540004ff764c540004fe764c540004fc764c54002dbe744c540005bd744c540004ff7648540004fe7648540004fc764854002dbe7448540005bd7448540016f66148540007b5414854002df87654140036f8765414002cf8765414000dfb755414000f7b75541400077b6554140036fa6554140036f865541400b7786554140007bb745414002dfa745414002df874541400d7b8745414000efb645414000fbb64541400d77b54541400d7ba54541400d77954541400b7b95454140007395454140006fb63541400b77b53541400077953541400d7bb4354140007b94354140005fb72541400b77b52541400077952541400d7bb4254140007b
  | 8 => 0x167e61545500167c61545500bf7461545500bf7641545500bf7631545503ff7721545500bf7421545500077b705455000d7e705455000d7c705455013f7870545500367f60545500377b605455013f7a405455013f7a305455013f771054550004ff7650550004fe7650550004fc76505500357e75505500057d7550550006bf645055002ebc64505501373f5450550016f66150550007755150550004ff764c550004fe764c550004fc764c5500357e754c5500057d754c550016f6614c55000775514c550004ff7648550004fe7648550004fc76485500357e75485500057d7548550034fe76d95400b67e65d95401fcfd75d954000cff74d954002cfe74d954000cfd74d954002cfc74d95403f67f54d95403f67d54d9540024fe73d9540004fd73d9540024fc73d95400067e53d95400b67c53d95403f6bf43d954001cfe72d9540004fd72d954001cfc72d9540014fe71d9540004fd71d9540014fc71d95400b67f51d954002cff70d954002cfd70d95403e67f50d95403e67d50d9540034ff76595400b67c65595403ddbf74595403edfb70595403e4ff75595400067f75595403dcff7459540006bf7459540004ff7359540024fe7359540024fc73595400d6bf4359540004ff725954001cfe725954001cfc72595400b67f5259540004ff7159540014fe7159540014fc71595401fcff7059540006fb705954000dbc7655140036bc765514000cbc765514002dbf755514002f3f75551400073f6555140036be6555140036bc65551400b73c6555140005bf7355140005bf72551400b73f5255140005bf7155140007bb705514000dbe705514000dbc70551401ffb8705514002ebf605514002fbb60551401ff3f50551401ffba50551401ff3d50551401ffba2055140024fe76d8d400aede63d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d403d6be54d8d40006bd54d8d400aede43d8d403d6dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40014fe71d8d40004fd71d8d40014fc71d8d403d6bf41d8d4002cfd70d8d4035efa50d8d4035edf30d8d400057f7558d400b57c7558d400aedc6358d403cdfb7058d40004ff7654d40004fe7654d40004fc7654d4002dbe7454d40026de6354d4000dbc7650d40026bc7650d4000cbc7650d40005bf7550d40005bd7550d40006bf6550d40006bd6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400af9c6350d400af9e5350d400079d5350d40005bf7250d401cebe6250d401cebc6250d400af9f3250d40005bf7150d403c79e3150d400af9c3150d40007bb7050d4000dbe7050d4000dbc7050d401bfb87050d4002ebf6050d4002fbb6050d401bfba5050d401bf9f3050d401bfba2050d4001cfe76d89400a6ee62d
  | 9 => 0xc70551501ff7870551500367f60551500377b60551501ff3f40551501ff7a40551501ff7a3055150024fe76d8d500cede63d8d5000cfd75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500cede53d8d50436dd53d8d5001cfe72d8d50004fd72d8d5001cfc72d8d500cedf32d8d50014fe71d8d50004fd71d8d50014fc71d8d504367f51d8d50006de31d8d500cedc31d8d50034fd70d8d5037edf30d8d500cedc6358d5042dfb7058d5000d7c7654d500267c7654d5000c7c7654d500057f7454d500357f7354d500375f7354d500075f6354d500267e6354d500267c6354d500cf5c6354d500cf5e4354d500057f7254d500057f7154d500077b7054d5000d7e7054d5000d7c7054d501df787054d500367f6054d500377b6054d501df7a4054d501df5f3054d501df7a3054d50004ff7650d50004fe7650d50004fc7650d500357e7550d500057d7550d5002ebe6450d500073d5450d50026de6350d500075d5350d5000dfa7050d5001cfe76d89500c6ee62d895000cfd75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d89504267f54d89500067d54d8950024fe73d8950004fd73d8950024fc73d89500c6ee52d8950426ed52d8950014fe71d8950004fd71d8950014fc71d89504267f51d8950034fd70d895030efa40d895030eef20d8950005bf74589500d5bc74589500c6ec625895041dfb705895000d7c765495001e7c765495000c7c76549500057f74549500067f64549500057f73549501ae7e63549501ae7c63549500357f72549500376f72549500076f625495001e7e625495001e7c62549500c76c62549500c76e42549500c76e32549500057f71549504176e21549500c76c21549500077b705495000d7e705495000d7c705495019f7870549500367f60549500377b605495019f7a405495019f7a305495019f6f2054950004ff7650950004fe7650950004fc76509500357e75509500057d755095001eee62509500076d5250950004ff764c950004fe764c950004fc764c9500357e754c9500057d754c950006df634c950026dc634c9501775f534c95001eee624c9500076d524c950014fe76d85500bef661d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d8550024fe73d8550004fd73d8550024fc73d855040e7f53d85500067d53d855001cfe72d8550004fd72d855001cfc72d855040e7f52d85500067d52d85500bef651d855040ef551d8550034fd70d855028efa30d855028ef710d8550005df73585500cddc73585500bef46158550405fb705855000d7c76545500167c765455000c7c76545500057f74545501567e64545501567c64545500057f73545500067f63545500057f72545500067f62545500357f7154550037777154550007776154550
  | 10 => 0x8d21004fd74d8d2102cfc74d8d21164fd73d8d210e6de43d8d21014ff72d8d21014fd72d8d21476df32d8d21476dd32d8d2101cff71d8d2101cfd71d8d21466df31d8d21466dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21476ef20d8d21466f710d8d21024ff7658d210e6dc6358d2145def7258d2146df77158d21004ff7558d21034fe7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d21464ff7358d21006df7358d2145cff7258d21006ef7258d21164ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d210e6df3058d21106ef2058d21166f71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2102ebc6450d21006df6350d21026dc6350d21015ec764c921026ec764c921014ec764c921006ef654c921006ed654c92116eee644c92116eec644c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c9210e7cc634c921457cf534c9210e7cc534c9210e7ce434c921007cd434c921007e7714c921015ee714c921015ec714c921167e4714c92101eef614c92101fe7614c921167e6414c921167cf314c921167cd314c921005ef704c9210e7cf304c921167e7104c92101df4765052102ef4765052101cf47650521006f76550521006f56550521015f77450521017b77450521007b7645052102ef6645052102ef464505210efb4645052144fb754505210efb4545052112ef6635052112ef463505210efb74350521007b54350521007e7725052101df6725052101df47250521127e47250521016f76250521017e76250521127b74250521127b54250521127e63250521007e53250521005f770505210efb74050521127e7205052100cfe76d81210defa60d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d81212aeee32d8121006ed32d812101cfd71d812100cfc71d812123ef641d8121006f541d81210defa20d81210defa10d81210def8605812102cfe76d91500d6be64d915000cfd75d915002cfc75d91500d6be54d9150446bd54d9150024fe73d9150004fd73d9150024fc73d915001cfe72d9150004fd72d915001cfc72d91504467f52d9150006be42d91500d6bc42d9150014fe71d9150004fd71d9150014fc71d91500d6bf41d9150034fd70d91503debf40d91500d6bc645915043dfb705915000d7c765515002e7c765515000c7c76551500357f74551500373f74551500073f645515002e7e645515002e7c64551500d73c64551500057f73551500d73f43551500057f72551500057f71551500077b705515000d7e705515000d7
  | 11 => 0x15dc714c931167d4714c931026df614c931027d7614c931167d6514c931167cf214c931005df704c931107cf204c931167d7104c931025f47654531036f47654531024f47654531015f77554531017777554531007776554531036f66554531036f46554531117746554531006f76454531006f564545314bf765454531117745454531007d77354531025f67354531025f4735453114fd47354531016f76354531017d7635453114f77535453114f755354531146f66254531146f4625453111777525453100775525453114fd73254531007d53254531005f7705453111777505453114fd7305453100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d813132edf32d8131006dd32d8131024fd71d813125ef651d8131006f551d81310fefa30d81310fefa10d81310fef86058131034fe76d95210f67e65d95211a4fd75d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521004fd73d9521024fc73d9521014ff72d9521014fd72d95214b67f52d95214b67d52d95214b6ee32d952101cff71d952101cfd71d95214a67f51d95214a67d51d95214a6f641d95214b6f721d95214a6ee21d95214a6ec21d95214a6f421d952100cfe70d9521004fd70d952100cfc70d95214b6ef20d95214a6f710d9521034ff76595210f67c655952149def72595214adf771595214a4ff75595210067f7559521004ff745952102cfe745952102cfc7459521004ff7359521024fe7359521024fc735952149cff7259521006ef7259521146ee32595211a4ff7159521006f771595211a6f64159521146f721595211a6ee21595211a6ec21595211a6f42159521004ff705952100cfe705952100cfc70595210f67f5059521146ef20595211a6f7105952102cfe76d91210eebe64d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121024fe73d9121004fd73d9121024fc73d91210eebf43d9121014ff72d9121014fd72d9121496bf42d9121496bd42d912101cff71d912101cfd71d9121486bf41d9121486bd41d912100cfe70d9121004fd70d912100cfc70d9121496ef20d9121486f710d912102cff76591210eebc645912147def725912148df77159121004ff7559121034fe7559121034fc7559121484ff7459121006bf7459121004ff7359121024fe7359121024fc735912147cff7259121006ef7259121184ff7159121006f77159121004ff705912100cfe705912100cfc70591210eebf4059121126ef2059121186f71059121004ff7655121004fe7655121004fd7655121004fc7655121024fe76d8d210e6de63d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d
  | 12 => 0xf43d8141006bd43d814101cfe72d8141004fd72d814101cfc72d81413a6bf42d8141006bd42d814102cfd71d814127ef651d8141006f551d814127ef621d814111efa40d814111efa10d8141005ef7258141125ec725814111ef86058141034fe76d95311167e65d95311e4fd75d953102cfe74d9531004fd74d953102cfc74d9531014ff73d9531014fd73d95315167f53d95315167d53d953101cfe72d9531004fd72d953101cfc72d95311167f52d9531024ff71d9531024fd71d95315067f51d95315067d51d953100cfe70d9531004fd70d953100cfc70d9531516df30d9531506f710d9531034ff76595311167c65595314fddf735953150df77159531504ff75595310067f7559531004ff745953102cfe745953102cfc74595314fcff7359531006df7359531004ff725953101cfe725953101cfc72595311e4ff7159531006f77159531004ff705953100cfe705953100cfc70595311167f505953114edf30595311e6f7105953102cfe76d913110ebe64d9131034fe75d9131004fd75d9131034fc75d91311c4fd74d9131014ff73d9131014fd73d91314f6bf43d91314f6bd43d913101cfe72d9131004fd72d913101cfc72d91314f6df32d9131024ff71d9131024fd71d91314e6f651d91314e6bf41d91314e6bd41d91314f6f731d91314e6de31d91314e6dc31d91314e6f431d913100cfe70d9131004fd70d913100cfc70d91314f6df30d91314e6f710d913102cff765913110ebc64591314dddf73591314edf77159131004ff7559131034fe7559131034fc75591314e4ff7459131006bf74591314dcff7359131006df7359131004ff725913101cfe725913101cfc725913112edf32591311c4ff7159131006f771591311c6f6515913112ef731591311c6de31591311c6dc31591311c6f43159131004ff705913100cfe705913100cfc705913110ebf405913112edf30591311c6f71059131004ff7655131004fe7655131004fd7655131004fc765513101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d8931106ee52d8931106ee32d89314d6ed32d8931024fd71d893145eef21d893100cfe70d8931004fd70d893100cfc70d89314d6df30d893145ef710d8931106ec62589314cdf77158931004ff7654931004fe7654931004fc76549310067f65549310367c6554931006ef625493101eec6254931004ff7650931004fe7650931004fc7650931015dc764c93101edc764c931014dc764c931176de654c931176dc654c931006df644c931006dd644c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c931107cc624c931107ce524c931007cd524c9314c7cf424c931107cc424c931007d7714c931015de714c931
  | 13 => 0x8d4153ebf40d8d414def710d8d4112edc6358d41535f77158d411c7d43158d41004ff7654d41004fe7654d41004fc7654d41005bf7454d4102dbc7454d41005f77154d41015f47154d41015bc7650d41026bc7650d41014bc7650d41135be7550d41135bc7550d41006bf6550d41006bd6550d4102dbf7350d4102f9f7350d410079f6350d41026be6350d41026bc6350d4112f9c6350d4112f9e5350d410079d5350d41005bf7250d411cebe6250d411cebc6250d4112f9f3250d41007b77150d41015be7150d41015bc7150d411c7b47150d4102ebf6150d4102fb76150d411c7b65150d4112fb73150d411c79e3150d411c79c3150d411c7b43150d411c7943150d411c7b62150d41005bf7050d4112f9f3050d411c7b71050d4101cfe76d8941126ee62d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d8941126ee52d8941126ee42d894152eed42d8941126ee32d894102cfd71d894147eef21d894100cfe70d8941004fd70d894100cfc70d894152ebf40d8941006ee20d8941126ec20d894147ef710d8941126ec6258941525f77158941004ff7654941004fe7654941004fc76549410367e65549410067d6554941005bf745494102dbc74549411373f5454941006ef625494101eec6254941015f671549411a7e62154941015bc765094101ebc7650941014bc7650941135be7550941135bc7550941005bf735094102dbf725094102faf7250941007af625094101ebe625094101ebc6250941127ac6250941127ae5250941007ad5250941007b77150941015be7150941015bc7150941187b4715094102ebf615094102fb76150941187b6515094151fb73150941187b43150941187b62150941005bf7050941127af2050941187b71050941004ff764c941004fe764c941004fc764c94102dbe744c941005bd744c941026de634c9410079d434c941006ef624c94101eec624c94116faf424c941005f7714c941015f4714c94112fd7314c94102df47654541036f4765454102cf47654541015f77554541017777554541007776554541036f66554541036f46554541137746554541007b7745454102df6745454102df47454541157b47454541016f76454541017b76454541137b75454541157765454541157745454541157b4545454115734545454112df6735454112df47354541006f76354541137775354541007755354541157b74354541007b54354541005f77254541146f66254541146f46254541137775254541007755254541157b74254541007b54254541005f77054541137775054541157b7405454100cfe76d814111efa60d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d81413a6b
  | 14 => 0x49ef421d895100cfe70d8951004fd70d895100cfc70d895156e7f50d895149ef710d8951146ec6258951565f771589511a7e421589510157c765495101e7c76549510147c76549511557e74549511557c74549510067f64549510057f73549511ae7e63549511ae7c63549510357f72549510376f72549510076f625495101e7e625495101e7c62549511476c62549511476e42549511476e32549510077771549510157e71549510157c71549511a77471549510367f61549510377761549511a77641549511a77631549511477721549511a76e21549511a76c21549511a77421549511a76421549510057f70549511476f20549511a7771054951004ff7650951004fe7650951004fc76509510057f75509510357c75509510076d5250951005f77150951015f47150951004ff764c951004fe764c951004fc764c9510357e754c9510057d754c951006df634c951026dc634c9511775f534c95101eee624c9510076d524c951005f7714c951015f4714c951147e7214c95100cfe76d815113efa60d8151014fd75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d8151024fe73d8151004fd73d8151024fc73d81514067f53d81510067d53d815101cfe72d8151004fd72d815101cfc72d81514067f52d81510067d52d8151034fd71d815129ef641d815129ef631d815113efa50d815113efa10d8151005df735815114ddc735815113ef86058151034fe76d95411367e65d954102dbe74d9541015bd74d95411373f54d9541204fd75d9541014ff74d9541014fd74d954154ebd74d9541014bd74d954155e7f54d9541136bf54d954155e7d54d954155ebc54d9541024fe73d9541004fd73d9541024fc73d954155ebf43d954101cfe72d9541004fd72d954101cfc72d954102cff71d954102cfd71d954154e7f51d954154e7d51d954100cfe70d9541004fd70d954100cfc70d954155ebf40d954154ef710d9541034ff76595411367c6559541545bf74595411573c5459541555f7715954154cff75595410067f7559541544ff7459541006bf7459541136bf54595411567e54595411567c5459541156bc5459541004ff7359541024fe7359541024fc7359541156bf4359541004ff725954101cfe725954101cfc72595411367f5259541204ff7159541006f77159541004ff705954100cfe705954100cfc70595411367f5059541156bf4059541206f71059541024fe76d8d4112ede63d8d41015f671d8d4102df571d8d4112fd731d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4112ede43d8d4153edd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4102cfd71d8d4112ef571d8d4102cf571d8d414def651d8d414dedf31d8d4112ef731d8d414def431d8d4100cfe70d8d41004fd70d8d4100cfc70d
  | 15 => 0xe53549321af6c53549321afcc53549321af4c53549321afce4354932007cd4354932005ef71549321a6ee61549321a6ec61549321776f51549321afcf3154932005ef70549321776f50549321afcf3054932014fe76d8532166f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532024fd72d8532166f651d8532166f641d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d85324cedf30d853246eef20d8532006f610d8532166f410d8532166f4615853200cfe76d813215efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132346de43d8132006dd43d8132024fd72d81322deee52d8132006ed52d8132014fe71d8132004fd71d8132014fc71d8132346df31d81322deef21d813215efa30d813215efa20d8132005f77158132165f4715813215ef8605813202cfe76d91510357e75d91510157d75d9151156be64d91511573e54d9151014fd75d91515467d75d91510147d75d91511567e54d9151156be54d9151596bd54d91511567c54d9151024fe73d9151004fd73d9151024fc73d915101cfe72d9151004fd72d915101cfc72d91515967f52d9151034fd71d9151546bf41d915100cfe70d9151004fd70d915100cfc70d91515967f50d9151546f710d9151156bc64591511573c545915158df77159151024fe76d8d5114ede63d8d51014fd75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5114ede53d8d51586dd53d8d5114ede43d8d5101cfe72d8d51004fd72d8d5101cfc72d8d5114edf32d8d51034fd71d8d514fedf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d515867f50d8d51006de30d8d5114edc30d8d514fef710d8d5114edc6358d5157df77158d510157c7654d510267c7654d510147c7654d511557e7454d511557c7454d510357f7354d510375f7354d510075f6354d510267e6354d510267c6354d5114f5c6354d5114f5e4354d510057f7254d51007777154d510157e7154d510157c7154d511e7747154d510367f6154d51037776154d511e7764154d511e7763154d51577772154d511e7742154d510057f7054d5114f5f3054d511e7771054d51004ff7650d51004fe7650d51004fc7650d510057f7550d510357c7550d5102ebe6450d511573e5450d51006df6350d51026dc6350d510075d5350d51015f67150d511c7d63150d5101cfe76d8951146ee62d8951015f671d8951035f571d8951147e721d8951014fd75d895102cfe74d8951004fd74d895102cfc74d8951024fe73d8951004fd73d8951024fc73d8951146ee52d895156eed52d8951034fd71d8951146f571d8951034f571d895149ef641d895149eef21d8951146f721d8951
  | 16 => 0x95325d67f53d9532176df53d95325d67d53d95325d6dc53d95325d6de43d9532024ff72d9532024fd72d95325c67f52d95325c67d52d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d95325d6df30d95325c6ef20d9532034ff76595321767c65595325bddf73595321af5c53595325cdef72595325c4ff75595320067f7559532004ff745953202cfe745953202cfc74595325bcff7359532006df7359532176df53595321ae7e53595321ae7c53595321aedc53595321aede43595321ecff7259532006ef7259532004ff7159532014fe7159532014fc71595321767f5159532004ff705953200cfe705953200cfc70595321767f50595321aedf30595321eeef205953202cfe76d913216ebe64d913201dee72d9132025ed72d913216faf42d9132034fe75d9132004fd75d9132034fc75d91321ccfd74d913201cff73d913201cfd73d91325b6bf43d91325b6bd43d9132024ff72d9132024fd72d91325b6ed72d9132024ed72d91325a6ee52d91325a6bf42d913216eef42d91325a6bd42d91325a6ec42d9132014fe71d9132004fd71d9132014fc71d913200cfe70d9132004fd70d913200cfc70d91325b6df30d91325a6ef20d913202cff765913216ebc645913259ddf73591325adef72591321cfac4259132004ff7559132034fe7559132034fc75591325a4ff7459132006bf745913259cff7359132006df73591321ccff7259132006ef72591321ceee525913216eef42591321cebe42591321cebc42591321ceec4259132004ff7159132014fe7159132014fc715913216ebf4159132004ff705913200cfe705913200cfc705913216ebf405913218edf30591321ceef2059132004ff7655132004fe7655132004fd7655132004fc7655132005df7355132025dc7355132005ef725513201dec725513201ddc7650d3202edc7650d3201cdc7650d32175de7550d32175dc7550d32006df6550d32006dd6550d32025df7450d320279f7450d320079f6450d3202ede6450d3202edc6450d3216f9c6450d3216f9e5450d320079d5450d32007cf7250d3201dde7250d3201ddc7250d321cfcc7250d32026df6250d32027cf6250d321cfce5250d3216fcf4250d321cf9e4250d321cf9c4250d321cfcc4250d321cf8c4250d32005df7150d321c6de6150d321c6dc6150d3216f9f4150d321cfcf2150d32005df7050d3216f9f4050d321cfcf2050d32025ec7654932036ec7654932024ec765493201def755493201f6f75549320076f6554932036ee6554932036ec65549321776c655493216dee745493216dec7454932006ef6454932006ed64549321776f54549320076d5454932007cf7354932025ee7354932025ec73549321afcc735493201eef635493201fcf6354932177cf53549321af6
  | 17 => 0x4fd74d815202cfc74d815241e7f54d81520067d54d8152024fe73d8152004fd73d8152024fc73d8152034fd72d815231eee42d815231eee32d8152014fe71d8152004fd71d8152014fc71d815241e7f51d815219efa50d815219efa20d8152005bf74581521b5bc745815219ef86058152034fe76d95421967e65d954220cfd75d954201cff74d954201cfd74d954260e7f54d954260e7d54d9542024fe73d9542004fd73d9542024fc73d954202cff72d954202cfd72d95425fe7f52d95425fe7d52d9542014fe71d9542004fd71d9542014fc71d95421967f51d954200cfe70d9542004fd70d954200cfc70d954260ebf40d95425feef20d9542034ff76595421967c65595425f5bf7459542605ef72595425fcff75595420067f75595425f4ff7459542006bf7459542004ff7359542024fe7359542024fc735954220cff7259542006ef7259542004ff7159542014fe7159542014fc7159542004ff705954200cfe705954200cfc70595421967f50595421b6bf405954220eef2059542024fe76d8d4218ede63d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d4218ede43d8d425eedd43d8d4202cfd72d8d4259eee52d8d425eeef42d8d4259ebe42d8d4259ebc42d8d4259eec42d8d4259edf32d8d42014fe71d8d42004fd71d8d42014fc71d8d425eebf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d425eebf40d8d4259eef20d8d4218edc6358d425e5ef7258d42004ff7654d42004fe7654d42004fc7654d4202dec7654942036ec765494202cec765494201def755494201f6f75549420076f6554942036ee6554942036ec65549421976c6554942007af745494202dee745494202dec74549421b7ac745494201eef645494201faf64549421b76f54549421b76d5454942006ef63549425df6e53549421976c53549421a6ee61549421a6ec61549421976f51549421b7af4154942005ef70549421976f50549421b7af4054942014fe76d8542186f661d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d8542186f651d8542186f641d8542186f621d854200cfe70d8542004fd70d854200cfc70d8542526bf40d854248eef20d8542186f4615854200cfe76d814217efa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d814202cfd72d81422feee52d8142006ed52d8142014fe71d8142004fd71d8142014fc71d81423b6bf41d814217efa40d814217efa20d814217ef86058142034fe76d95321767e65d9532025de73d953201ddd73d95321775f53d95321ecfd75d953202cfe74d9532004fd74d953202cfc74d953201cff73d953201cfd73d95325c6dd73d953201cdd73d
  | 18 => 0xd73d85431c6f661d85431c7d631d8543034fe75d8543004fd75d8543034fc75d8543024fd74d854302cfd73d85431c6dd73d854302cdd73d854301cfe72d8543004fd72d854301cfc72d85434eedf32d85431c6f641d85431c6de31d85431c6f631d85431c6dc31d854300cfe70d8543004fd70d854300cfc70d8543536bf40d85434eedf30d85431c6f461585431c7d4315854300cfe76d81431befa60d8143034fe75d8143004fd75d8143034fc75d8143024fd74d81433cebe54d8143006bd54d814302cfd73d814336ede53d8143006dd53d814301cfe72d8143004fd72d814301cfc72d814336edf32d8143014fe71d8143004fd71d8143014fc71d81433cebf41d81431befa40d81431befa30d81430057f75581431d57c75581431bef8605814302cfe76d91521b6be64d915201cfd75d91521b6be54d9152636bd54d9152024fe73d9152004fd73d9152024fc73d91521b6bf43d9152034fd72d91525f6bf42d9152014fe71d9152004fd71d9152014fc71d91521b6bf41d915200cfe70d9152004fd70d915200cfc70d91526367f50d9152006be40d91521b6bc40d91525f6ef20d91521b6bc645915262def725915201d7c765515202e7c765515201c7c76551520357f74551520373f74551520073f645515202e7e645515202e7c64551521b73c64551521ad7e73551521ad7c73551521b73f43551520076f725515201d7e725515201d7c725515220f6c72551520367f62551520376f625515220f6e425515220f6e32551520057f71551526276e215515220f6c21551520057f70551521b73f405515220f6f2055152024fe76d8d520357e75d8d5201d7d75d8d521aede63d8d521af5e53d8d5201cfd75d8d525be7d75d8d5201c7d75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521ae7e53d8d521aede53d8d5261edd53d8d521ae7c53d8d52034fd72d8d525bedf32d8d52014fe71d8d52004fd71d8d52014fc71d8d5261e7f51d8d5200cfe70d8d52004fd70d8d5200cfc70d8d5261e7f50d8d525beef20d8d521aedc6358d521af5c5358d52615ef7258d52004ff7650d52004fe7650d52004fc7650d520057f7550d520357c7550d52006bf6450d5202ebc6450d520073d5450d52026de6350d521af5e5350d5201dee7250d521cfae4250d52014fe76d855201dee72d8552035ed72d85521a6f661d85521a7e621d855201cfd75d855202cfe74d8552004fd74d855202cfc74d8552024fe73d8552004fd73d8552024fc73d8552034fd72d85521a6ed72d8552034ed72d85524aeee32d85521a6f651d85521a6ee21d85521a6f621d85521a6ec21d855200cfe70d8552004fd70d855200cfc70d85525667f50d85524aeef20d85521a6f461585521a7e4215855200cfe76d815219efa60d815201cfd75d815202cfe74d8152
  | 19 => 0x89536167f50d89535cedf30d89531eeec6258953014fe76d85531e6f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d855301cfe72d8553004fd72d855301cfc72d85531e6f651d85531e6f641d85531e6f631d855300cfe70d8553004fd70d855300cfc70d855357e7f50d855350edf30d85531e6f4615855300cfe76d81531defa60d8153024fd75d815302cfe74d8153004fd74d815302cfc74d8153034fd73d815338ede43d815301cfe72d8153004fd72d815301cfc72d8153014fe71d8153004fd71d8153014fc71d815342e7f51d81531defa50d81531defa30d81531def86058153034fe76d95431d67e65d9543214fd75d9543024ff74d9543024fd74d95436667f54d95436667d54d954302cff73d954302cfd73d95436567f53d95436567d53d954301cfe72d9543004fd72d954301cfc72d95431d67f52d9543014fe71d9543004fd71d9543014fc71d95431d67f51d954300cfe70d9543004fd70d954300cfc70d95430067e50d95431d67c50d9543666bf40d9543656df30d9543034ff76595431d67c655954364dbf745954365ddf7359543654ff75595430067f755954364cff7459543006bf7459543214ff7359543006df7359543004ff725954301cfe725954301cfc7259543004ff7159543014fe7159543014fc7159543004ff705954300cfe705954300cfc70595431d67f50595431f6bf4059543216df3059543025bc7655143036bc7655143024bc765514302dbf755514302f3f75551430073f6555143036be6555143036bc65551431d73c65551430079f7355143025be7355143025bc73551432179c735514302ebf635514302f9f63551432179e53551431cdbe72551431cdbc72551431d73f52551432179f3255143005bf71551436479e31551432179c3155143005bf70551431d73f50551432179f305514302ddc7654d43036dc7654d4302cdc7654d43025df7554d430275f7554d430075f6554d43036de6554d43036dc6554d431d75c6554d430079f7454d4302dde7454d4302ddc7454d431f79c7454d43026df6454d430279f6454d431f79e5454d431d79d5454d43005df7254d4363f9e4254d431f79c4254d431c5de7154d431c5dc7154d431d75f5154d431f79f4154d43005df7054d431d75f5054d431f79f4054d4301cfe76d894302dbe74d8943025bd74d89431ceee62d89431cfae42d8943034fe75d8943004fd75d8943034fc75d8943024fd74d89431cebd74d8943024bd74d894302cfd73d89431cebe42d89431ceee42d89431cebc42d89431ceee32d8943014fe71d8943004fd71d8943014fc71d89435e6bf41d894300cfe70d8943004fd70d894300cfc70d89435e6bf40d89435aedf30d89431ceec62589431cfac4258943014fe76d8543025de73d854302dd
  | 20 => 0x10000016013000001400a010000000400c0050000018006005001000400001a00580080020030060080000009007800802000000e0024000008001000001000401f000c01602d0010008006001003000800e020019000000800600b814c0140010028000030009002000003c000005000000802b013800000000e003800c00600700000600000010028024046000000000400200e003802000a0040010000002001004002c06400300980000040020038010038000001801000405c001806801c00100b800002400d0028018010000000002c00c00100d8050016000000000405000101f003c01c000011802c07000400300140000460008000006022000800400a005007801800a014001801c000001001803c0000000000000002002003800c00e000024fe76d8d54216de63d8d5402cfd75d8d54034fd74d8d54216de53d8d54216de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54216df32d8d54014fe71d8d54004fd71d8d54014fc71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d5466e7f50d8d5465ebf40d8d54216dc6358d5401cfe76d895420eee62d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d895420eee52d895420eee42d895420eee32d8954014fe71d8954004fd71d8954014fc71d895400cfe70d8954004fd70d895400cfc70d895462e7f50d8954606bf40d895420eec6258954014fe76d8554206f661d855402cfd75d8554034fd74d855458ebf54d85545567e54d85545567c54d8554556bc54d8554024fe73d8554004fd73d8554024fc73d8554556bf43d855401cfe72d8554004fd72d855401cfc72d855458e7f52d8554206f651d8554206f641d855400cfe70d8554004fd70d855400cfc70d855458e7f50d8554556bf40d8554206f4615855400cfe76d81541fefa60d815402cfd75d8154034fd74d8154024fe73d8154004fd73d8154024fc73d81543eebf43d815401cfe72d8154004fd72d815401cfc72d815443e7f52d8154014fe71d8154004fd71d8154014fc71d81541fefa50d81541fefa40d81541fef8605815402cfe76d91531f6be64d9153024fd75d91531f6be54d9153676bd54d9153034fd73d915364ebf43d915301cfe72d9153004fd72d915301cfc72d9153014fe71d9153004fd71d9153014fc71d91531f6bf41d915300cfe70d9153004fd70d915300cfc70d91536767f50d915364edf30d91531f6bc645915366ddf735915301cfe76d89531eeee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d8953616df53d89535ce7e53d89535ce7c53d89535cedc53d89535cede43d89531eeee52d89531eeee32d8953014fe71d8953004fd71d8953014fc71d89536167f51d895300cfe70d8953004fd70d895300cfc70d
  | 21 => 0x54004001005000401000b0058050016010008005402e0120110018044009000800400600b0318014010013001000c002019000000802c002002802001007b0020014016001000000001c001001800400401c009800c00c00500d000401200c00300280000000038000008001000000803a00000700480060170018004020002009000c004000007000401600000300100060010010008026054001800000400002300140320030008000004000000001800a00000180240740070000000000000009800800600c00f000008c0020010000006000001000c024007010000001e000000800c06a001005804800000100000940080120000010012000003000000800b0060030000001001800c03801e006000401a00000300140040000008034018060000000000c0020000094000017009000000c000000800001c0170000018000002002804801800500e801400401100000300140150008020002001010806800800000000740000020038000004000000012802e0010048000002007004000000e0000018060006002001000002c00100480000120000018018002000007801c00000800c8000012003021001c00c0000078004008017003001801000500b0008016000000000800400000300000b600d000001800600100400080040050008008000000001808000000100200100040050010000000001003001801e0030038014052007002800400801b002003800804a001000c01e001015000c00000a00280000400000040004000000000002000a00500080100000000000008006000000800c00000f00000080060020018008002004004000001200403b8004000000019803800000100200300080000068000000009000000c00400002a8008000002009002000c00f002001c02800c000007c00000000200d000e00400080180000000008004004001004800000200f000001000a000000807c000006002801400a00201c8000002002010000000e009016001002c00c001002c00000000c801401c013004001002400101b00080000030028008004016005007400200b001806c0040010038028002005007000800e00e00100000000090038004014018002000400600300480040020030000000020001002000001200500b80f401000500000780ce00300000200040030000000004000015800401a00400180280000010000000006006007000c004004001800403e0070018000002023002000c020003000000c016002000000003e00d003000800000200e000c00000b001001000001000c800400000500300a40080190038004004000010801400c000001000c004001019000002a01700c001400000a0040028038001002801800404a0018000014000003000c002007000806c03a001001809c00003200480180240070050060002
  | 22 => 0x150487f60bb49d29495534b88600006c25862bb03c4000089816086a8be0000cc11941fb6821e90000d2d5ba1c64b1eac90000fbcc0641847eb6088d800057b927ca620004d4b4e500e000000031c93a2b800000013e02a23608dc9840af92a796006d2000000062d930301423168c71a7576971a982584230a322349c293b087800000091c0959ef9b4c6ac2ce1cf40000001eb0b20ae408a2d50a1928a141375ad480009df61c35c9614c5d5719bc840accb38f86b8dcebb12b208d1a9c58c0b90e5103600036e82c84c08b460c1695050a8761599c92d2c9c46491cc00069c659271d3d85e05e500f59ca2843fe0b9d6086cb17e0b158f00003cb886d5f69ac65e16aca8e7796a6abe85d80000d381f8a0acd6143907d44ed3843d2b9c0004d800013f0af485d495a668ac07cd668942d45a000065aac5af664200010e8d8cd90000228c00039e68cb3149a429f3510070ede08c46225dd36e8ea29d08ec73008527c2d5c06e59534fafe1adc0006ad90a877e2d20002f8400041923b8b74d9cb090002748ee26da09d800121012e000000000082f0002854e52000025000166031b0000001a50ce90b00020004000000002805500d001400e00200d8000046010003802c0000040010040006000010003800800100c8030000000003800400601d003002406600000080100000070018004000000001000000801c00100000060100030000026004000800c000000000005c02a00401280341360070020074004006000805c01a00100200040020000050034002000002800400000c00700000060030018014000006000801802e0000030074014004001800007e016000800c002000000802c0060030020030002001002001c000000007000800000c0400000006007002805c00202200480100040090010000002001000002c006038001000c00a000005800001c0070000004000026020800000c04a000000801200a0008020000000004800c00a01f002002c0c8001001800c00801201a002000201700a800001e0010028030002004000000000e0090070000000001012800400200e00000080060010030000002000000806404400300000080000740008054010000000005000a0090090020048003002800c000004002801802800b0020024000001000800c00200a000800800404f000800000200400680000000040000020042006000000c006005005803402e00a00000240040070000000022004001800001a0000000024000001003002400c0070038008002025003000400c007000804000e00e0050000002002002801000e000003000001a0060018010002007001001005a0010040000020010020800800c000000001c00400001d808801200000180200000810000004000026003800000000a00a800000c02a0240004006002000
  | 23 => 0xd4b8a08ca4c6c73a39228f220000000001b562620da9f606dc3e866a0bccbae44c0269cf0aa673150c80011140003721e697746870000d0d5b2679150000089e0001d3a4fc000caf51fa0d9542a612b9800024c4fe0641a097d2483435aa5570e1080000f948c006149ca5b147aad46c185ed00a3a4619059d59c9b31ee8cc44b6ab737cb1ac9169ad618214c378db42d8372c000751283261cafaab60000c9d6ee761671351d36c00059f216c0000000001d64000b6a0000b5c0000004c715795aad0559d06b499e316000276400000068380000000000001b00ce219050932e1396b4d1cd9ac16ba8a4416000047c4be6a29d7c5c000039013440006d23eb139d1c60000330001afa17845800013b800044caf0400084c1612de084c1fe59db700a8a44d60206a978a79f05707a4230bd515589a97fcd09138858860e00057800001d441710b99240003f50cd2a0d77cc1628093d800037158880007588436812584ada95a65c9be04f63a305399dd8dc2294e6b3f464032548284540aec4b0000ef40708d92942f38994c9548d9b21a002805a3a8387fe6273d6b4305fe000157a3685fa0000142144f802822c9000000000025b99d496212f2922138cfc8740003211426a4e5d280007aa9c25660d2c326db152b1aa9b84ccd51530c4a14c4600002acbce9ff0679f789c87a34eb0000d52b2b4222e9c2ee7f345c291cb5c0d23f80614eaa53240baba964809f25c86812cc6b940921b059828d02b091cb6645f55a21b4e2209326604a8fe287535700c023eb0f46322815888ab23f00000009b139a115dafe5885cf0ba4af079b38409855307fa6080679aec9a42763444d6e5e33c430d48846b44930e70f7039200010a4b1a60600031a58ee0004ab80009fa0002b10f7ca9c00063a223800000009821a8a4e03f00014fd14cc470b9aa3c00018662680014c8a6c554867c12e0006432fb50ca000483172577e25e39394250b071a62885b980a7063059c78c9a8922730ac5aa0ca135085704665dd69109c909acff41e07c4b7013f1e5a0c40000006a1342c38ac9d2ac13c5b1864638180688bc15466aae083b234e5cd8d542622df2f500000000004b400002d414d5ee2579212aed4a3160d0dc0056b80bc80003cf1f3208053234c0a7897c970395555165c00092016ca388428ba006a2ea41d6a6a10714858860003fd8f68f3278d5c589680009d40001ed04ec00048ca745a6e0004ce2abc2ae37352a04154a246823305907b84762ef06ed01210636520ac6fe3bb182a24c3ea28936b0001a28a5363909e916e93650a2f7556ad8f34c2190e0267a22532eced6b7c685170cfc86d516b11451feae856181080b29332198a958be90400030697e055400031b400078e000057c000c9e6782900b6ad8919ea2b0f9e37d413997cc12a521e7070
  | 24 => 0xd4e870705f86b0000bea3c5b3745b84782db1f097cccdc00004680000ef6e300000005ec517038061263f295208468e57600005b0b68000431a5b8000d033ce92e8d8a7dd4940000ea60000000000f20000661b720000ae20002c05a424585062dcd3b4dac5ca80012826d80001efd1d6d56121a0307f859e61d1c4152e00a23e2bbc83ac8914400a839ed0f50206592ce96d3383680000d6d3c29898f6c9a8612363542e00f3ce2af85dc7a90000b0c0006dc3f5266c82864c0880f081688420719400db6aae5e6897000c0005838cb46f41070000ca8d9a71b14d96e995a5d40f1889444e1ba6b783581faa2652091f4dfac423b80538c104d543b85c086000045912c9ad6000133066db8e1a13a10000aea20b4030000000bfc3848000ade58b0a009d49dc61600000000000000f600000008890002a68b84b8a2028a7981406d2282d0ce5ada81e98a1443234400024b97be51258e14ac1f0d4125e0bf8da85cf6761739b143611b505a06ba00045e0699a7a2c7178a621a10d7a16c1aa13f600000015e554ada25b8a4f4000afd6d9a9a0fec3664e21c8465e2e128ba438956a381508451668315000084da4661063120c873a08103992080be9a74022dd5824d78000207011c738000226009613d653ada400054d00022148a4ca32d10fdcdf61450000001b7090d414991cc284460000000000a660000374000051000000000000050383e4d7c3fd0528d34e58100564320888684764f80945382e41f18c401ca7b30003318d7e78f55680017247bd00033092fc4ad5791bb166ea9d1740edc4180dc6130001a2a13800028604fac58000329400053c64500016668813f0b3e80e03b15ac8710e886013ba80000624a25ddb3bc0005d50002bf80008a131a1f4840400013480015080004a89d411c800017d22e9ae826c21b0f05a2067615500007a2a240002358858a570000fe84c8ae90002380000cdb00000013120002eb00004ba34231e02240000000002f78000d970000000022d0e00001bd23a1ea00000000006b20000001b7c1740b30dd0d1203317123a44e60ed6069b95b7edae000225000070d2ca00000004555148000618a714618001a305140000000c566966a49a280006800c605e9a5eaf168ba3356246542d68afcb4c5d158332e946ccd858715748c2d661f5adf9386d1e596222c9823330f0ad9db6ad435d8148c754756115b2ad1ee74e1df09509207a515a2918552ac111a85b43d026719208718d8b5417c1be81e8a1f6d92ae078a06305999754f05ee2f7aa79a40aac47d98101589f90000000d181e61819fe17c48e6565a4507b60073aa278506a7fd2ae0d21402000112052d5ec00062bab346d600063caedc00048109933a800055763d011c00065600015b0000878044248c39003241c200c000b3d5e990e4a208d
  | 25 => 0x4300013ac00000056e19f400007a00024e094c0000fc9e88170669099869530c87b32a80018c21c11b6a0058920003ea80000000000002cc44700000001380000d3056ba19cc30a2b18d00006cecce6b124c461aabc0001a753423f000000000000001c22e2134a1286af0001ac8313669a3f0000b4f05088c867c5810001bdc00075a443a38569ca2c11708547cec1e4c28769540d1309b253847a6bd62e0e380246df4fa04f82ca2a400030a8efe7b946880010e4a0500032d890000064c800000091a1ff00003bc8ad00031297260d024a338573225800027cd9e6b7f2c3227c00000050ea1e4b623ed4a800011989f25e38a38be600024f121400095c4920bc07789e539700000f80000000000394d24607070988845629cab00820b6f3f6ae0ce48b8d000138d0e00000e59d94000ba80000000000ce31e38884e725ff03414a40e276d5581c588060004d30001218a4322e800095c000031000000092c0002a4c71420652c11ad766000000307d082378000000022e8c80000001922bb53dd362175884000000000004974d518cd16600050f00000006320000d88000ade4b1984882439f0ba8f78cccac553f21643f8cc812c991494075807baa0002c767620211520e8ce348af2010e03a378832964c94d2e9239c0dc7620cc8880d740004dd83543ce69339d000056cb655ce00007e23c90aaa6c8b8e3c33e39f89440000000058c0006b6125800182aa9167a0934dc208300000012d60004ac02d8c6c64f25a856d2602940000e64b1246a5db00000000005f7adf4a08c97279a82caca16b28e12c11e20002548c208f69995799bd93d464853d314c01a818000000083678031680001240000003731b7431200027f01d80005a29944980c902489a0c00000007704647d417109d03145220002e2b390ace23c4a60840498a773a6acbc000d3e0c01b809f61611f91e6122acb101690f485a83313789017c824a000000000000000036a419c0cc02296a47b07336500368ca60001a98000000beb3322f64d0a00068d013880437e23800006b057f4da000034877d0002d256047fe39f000036e8fe3eb82089d47d3540af2c984a062e821a094883f3942968f561d5297998da3a0003f91ec8bead52660ab292c00003d5143895e5205fd2d69004db65d5b39835e4f900f1ba464204f0ac06085da3772f0a40ce7636400000019680025a20000000d6c13ba4788007d069880115489c15e1800187a0006490261b24c9a424a0593bc09b3220000c70bb46108dd98a0be519182edaca91124b1fbd07285c6bf0dbc1c200049a8f1060c90b3341d01af200003c26e89babe820087ac71078611bb470d5ed940001e28ecc92f544a0a854e6005199aad6ac57e0c6b259068304020af68e1e0bd0e1ae8cf264672960299a80b631e927bd21e2012b088
  | 26 => 0x16d80790000dd4236000000000000001f00000000904c60000001462122320aac800050d00009d00000004a4000133e36307f1d7485ed8015d24f80006d06018ecc00001d63b00013d6b72000000088800000018b0288a9c395144c988a762dd95d115e88352620b5ac6000000298876061a6540088000a232b180012843ba1f627b866c89d2f687504a67130eb2d6c7e6bcc181074547491f01db1990ccb8122397adb168ec26e13e905c2f709009207007c300000e4f0809d2d3800078c08b0002209ad0901342000146acd707393200fe0005e91f8c856695247361995c0004cc0000000000000062106e8f6000000057abb200000010320000001640a6a7890000a6067000000025013263ca1f011fc37e06b0001f807f2adb0f71f187649f60393001ad473f21d9bfc6a4d980000b18f5cd3257326e4c366293f42cd446ca226650000e280000001b8d81e1ed232198804692219a1334e240006031b2400064b2cc0000f04b852b400004c60005bd1878cca1ce35c17c824e09a18ca52d3ce42501600016201e5148102591e44b46b86cc1e60005390fd8a984db000000000000009a03101b0bf1096a458bfc1cc62084340000db59e2ebd8c6a440000b04772c1b00027000d4c800000000b9007d1408000f920000002c5980e00059b0141a980004b82f40938796000143cb7cd550420bd42a00000000b78dde0a812092200005bc6a50c440002d455d0a2cb040005d52fd501e7253d0b5658e60001681ad42fcda51ad1c29b38385116b0200425432fe2ca8db2cbd43b2f5db2249843e0a8d73e000317a8dc6ac7df29c236ca22a961c891b4c227785e48d2598e14369a3290b0a1d05d3272933c00024d00000000005210000ab4cf863022214946a01932dd99287606b8a5d0184c373a40000be2ca900008011e008d0000a58000d3a195af9d12c87144e2d01b0e38c000230583831e0000000000c2917c9d0c3144c92740c3896811612702e5414d2b0000054028af433da14183a48f1d096450d20b5000223d13c9e24a9b6553166054ae818187cc8130c984ccb8bc04aa366832a70212ba0756b80de4d7b2a98fea8c17b217c4fe3c841e82f836894738a91e826e086278009124ec286cc8f64a6698a3b51a5080842844800bc9ea1db4d10f884dc1ef51d8de59664a85c88ac96be1910588040fb800055180000007174ce96dc3aedaf00015284240004f3147d78499734829e54dac3b5fe80017f273245aa75c6d80f532cab1c55a7952a12fcc04c43167702f0d1e9f1000068892430b5d080000002086260001770000116028d30297a0f00391abe0003bb89f95a432c277a1bc0000005bc80014f80000001c2c09205211425d4000a2846aa8712240000efb1ed0288005fa1fe529e2ac0fb80014dc00c2fd000186c71859c0d5c3466
  | 27 => 0x1524512e003089db00007f4b36077492951111835c6a4234856eaa800bb7258de1350e9ac7c000cd91e62b7400014859cac893920000d800000004d4263b2c18684895688fa4cced9600011d525a00054900000003510000d011ea7bb0c3a0e86bc596611b28800000019e0000000c0c00484e542200000000000000005228b98000bcf000257c2080e21020001a9610c30118c000033a13c10794aa53069e15ecb961cd4adb69c5189ed2f20e2d63ab252e21a48138577555aa4028e63b66922c502a6310a48a7572815d3d80d14242aa6064aca00ba6a31b019f13187e953da9fd1bc00000000000000004dfb3c4000000000126481c8520000000000ccc18e2cc96d653e3d618d514a7da5431d9138c00007d0e1957e2eb29dab802fe74c10e8954936b6844b8eb8000895000146540061d11c8b3c00019700000000008d30001b5c0008ee2b331517b0b1822a00013460006de31a17a2000000296c9460002aca549496b170482d9000045b4c901185e88c267d94552f841c3b986d98a43226111088aa2b7b6be2924f7861759385699c0d9325e84948802be5a629ad91acfe1802d04f4e63e439aa34ae07223e60000d984c352797013a65463d000000001f659f87184629e3056904412200028dae3d4de00000023cd30644e38709157c00c1058298099c52d39a85f4f8ab4a46299b05664325699e0553218e0dea0ec000b19000042cbc48d8507a610b3aa9b15d9e50ae28604ac8e3c87ecd02a4aef0a9066e4f02d08cfe8b903b2fec768b2349a18a96520fb4df255890eb2100000000000000001c8c1f8d2c42418f411e207000239435204467389a00006d3117ae414b2000026019da2c5bf694800068c00018b9394e6c00055d80006308084b79054a5ca6352e92a86761f001380f80003683a4b3f0000000000000074c9654bc1d8c0004934e600004f28f900027904ac0000000000b984de489800147215142a0df139c9e903a19e16c29bd00000010209b053a800056ad773128471b3a1a857fa32c5141f234705bc6b239056c0564000000197140c00078c3e59edd1a00c319901ec4226bc253a4a5220000000000000000045dacb4bec3f400023b45925073bd0000b5e5df0bb0cd400015602d8000966bff63e1c14a8074f0852a7d5dc0002f800017c63d71c3904c72c8cf0002eb89ae40f000000000037b14d0a3c6946ee084ad6098abad6cd8b6c0008612e698888920000000000000db9000000000097909e1d1987e79e3598319aae000141a8947440a928d00000004e940f80010aedc149e00004880000000000000cde265908000003656fa7a062869e3e700000003fb000000c00000046e3738c4645967408297dcc870000000c1a6883a935114e085e0000000dd0d693569dd8000bd468693c8b7a4bf1280000e8a5e80000
  | 28 => 0x31c0be82ce3528d0437000067c85a49760002b529cd4b80000002c2076abd63061bd01e24070148dc0b32b46000087cf50000078114d356a5f04010e000000000017f4000d540fc13b52c894432f00007023c06622d44000b050000000000abd00030cccb68a7440027800018300000000000000000000000bc600000012f60002681a193f47ee00c034c0009912c731d54602490000000000d730002f108180a005b9f10000406371048c000a8a2ab00018e245c2810f513a00f2553952c412c8c6e20005a5451e1dc3574652a4d62c8bbc33a0000f217ecb500005b300000860001c196b152800b60a1430ad600000013656a60002fc00016340df000000172c60e0be370c82c9f834d19b4de6b5029b8ed8ce6bf64fab4051228d4000006c43496a49bb53cd4863a21a07704a400040688e9b48d583f59e1c47e1ff11834fd5447694b9044973a55b2b732fda3e2cb3a53614000000570889917a1533c91decc0ebbd3f6123479aa0d65f02518aaad6000109c0009a011500000008f40731764c1e55f0000000a2c4792c51ac57b619c4ca9939a6a59f0001df81b27306de9d7096c194231ab1881075b0f986491543af2059f9d822c255859488bf23ab0eeb5459064f70000d6c00011d1c481a4f824f43ff91054108b63b4000070400000000012641246058000ee865062f212c1a2000627004c0000000c4b68cad227c4c01a34d7685550b1f28b08c481f700003e883e0d89884bd2c4501e28bc42c64a38615f00006810fd14f40002a84e796e5044921000265969000026b346d32005a44211a45800a402f0fe052a055504b3d44da55260118e53eed5a2388c3c614dbb0002c355b45a421f1ed563c89a0000b28e6e53459725fd872a1a0000a98444000454b215b1c7f4376b4d8e5e04006b8724b420ba5f9349940671d46f8945910a691581b10e38c2c1078001442ad036f2b09566c7e21711d17123373be1db000081333a2e88e960354601a65274daa000302520400000019a8ca4da1000083438ecac3b726340000004d70000000d3343ea02d72e65a292a8c98b65d318eb368d3617947c337cc40593314091904c66b0dc976d3fac3c2069f996dadc516ab5d40324ac2fb9ec4de00535329fdc1fe8114a1866196a92a57227f80569c54dc2e10dfc9006b0172815e81a4de176185ab864bb0b106ca10e5f626506a8a3c6a30b94000c6a58a2c80b340e84741f450fc14a1d411158acb55212063c0c8a026791554d4e39710f12312fa94962d1c000687e507b0b34298acf28c19009b48fa6892d89730830477a5ccc2ad0651a2029b60c9b5c6333ccde5a000024287a08bf1751bf0b821be2329770fb2462000025800080e37500002063930002460572c2728422b8000d6118f91bd8fab006c08af0c38a5e2d91c98bcccc927f9c11b94
  | 29 => 0x3b0886572ae394a00aa28e9029ace8c76328d7c74ab701d4aee4aa0a851279b984d615e3b9354d94ccb74daa26d4906c3395a15865065869dac4c86eb0330fb22d85c05c17dabd54fa7f53af18dcf4c2972ed137c18034f08f3494b0ea106cf088c7c27c848ba63c132350032906894a6f52a081b0010ba45cd36dd150bf75b706c801c448600a99d3aab601210b8c2841026d68b68f5e101088a8f8c484a1094abac19a27024227218c8c2f431367ca6c3e42698ce52c4a886c233dc000afc675a86cc14b1b5470b4c0ea6d122d00013ba68b1688cfc000657649a76109e5e500006055f0c19210aae562ac13367b3b41440540e93239ab89825a5b3d88dc4952430a4cc5c84a0000e80b8c85a2392a2c0002651490000e8239a633800012a4e201000b96bcdcd4791e0d0487db412998075a43c40f06ad89e0e933080019802ae3ea
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcb87650d4048001e52a8a928090006ea21d425012001ed443a84a024001baa8650940480037510ca128090017aa219425012002f55bb284a024003daa765094048007b50eca128090017aa1d94250120005d5c2a84a024000ba9855094048001d56caa128090003aa5954250120005d5c1a84a024000bab8150940480079d0ec9928090002ea6113250120007c4a1a64a024000da942dc540480017530890a8090003e850521501200147a40ae5b2a20048de87dcd65440051e902b9ec88800e3ba1f72591100046fc1aecaa220048dc835d954440011df04bb2a88800e3b209765511000477c12e9b1a20038ec825d363440011bf06bb2a6880121f21d6554d100043fc2aeca1a200687c855d943440011df04bb2868800e3b2097650d100245e43ac8a1a2039aac82591434400b1bd0fb1a868800237e0d75d89100246e41aebb1220018fa87dc1624400117f08bb2a4880162f21176549100046fc1aeca9220048dc835d952440070f90eb2aa4880d69720d65549100347743ec4a9220008ef825d942440071790eb2284880023de05764c9100343f428ec992200087d851d9324400b17d083b264880022f610764c91001c6e43ac699220048ec8758932440052eb0bba2a28801a9da1764545100347a43ac8a8a2028ae4825915144001ba461b9aa28800395d4f63545100347a43ac6a8a2028e6462549514400536b09baa82880063d219755051000cf8402eaa0a2005ab684d95414400b1e90eb2a8288096b520d655051012f4a31a86a0a2000de220dc94144001d4e85b1282880163d21d625051000c7a432ea98a20048f48759531440031e90cba262880063d219754851000c7a432e890a20038f48759121440031e90cb9a42880123e21d654c1100072cb2aa69822004cd87650d3044001ea2a6a8a608800b3c1d9414c110007c8a1a829822001bd0874c53044005ba10e98a6088006f4a19314c11000de8432629822004ed0864c53044009da6ec98a608800b749d9314c110016e83b2629822004ed0764c530440017a70a98a6088002f4615314c11000769b2a629822000ed1654c530440017a70898a6088002f4611314c110005e9c12629822000dd3724c530440017a30690a6088003f04c9214c11001c7c43ac890220028f8865cd20440079d0eca924088003aa5914248110016783b2a29022000f61525452044001f4284a0a4088003745cd3148110007e0992629022001be0874852044005bc10e90a4088006f8a19214811000df0432429022003ee0864852044007dc6ec90a408800b789d92148110016f03b2429022003ee07648520440017c70a90a4088002f86152148110005f1c22429022000be1844852044001dc6c890a4088003b85912148110005f1c1a429022000be1834852044001bc6e690a4088003785cd2148110
  | 1 => 0x6ecaa2a0a00174e9d9545414002e9c3b2a8a828006e3876551505000167706aa2a0a0002cee0954541400059dc0aa8a828000e3954d8d50500016730aa1aa0a0003c654d43541400069caa6e4a828000b39855095050001e52a4a12a0a001b1e1d9515414002e5c3b282a828000b39855055050001e62a2a0aa0a00029760e54d95300047bc0ae5b2a60028f4815cb654c0091b906b8ec89801a1fa1f75591300043fc2aecaa260068bc87591544c00d1b90eb22a698003569437550d3000c6e432eaa1a6000e1e54d95434c00b1b90eb2a8698012676137250d3001c6e41aebb126005c9e7450f624c0070fd0fb2aa49800637219754c930024e6c16e899260018dc865d1324c0033b100ba2649800eb3a0b644c93001c6e43ac8992602ea5c85591324c05dc98caa92649800374843714c9300043fc2ae9b0a600687c855d3614c001d8a6590ec2980162fa1076545300045ec20eca8a60038ee821d9514c0011db043b2a29800a1f21d65545300145e43ac8a0a6026a3c85591414c071d28c2a1a82980163da1f615053000c6e432ea98a60018dc865d1314c0031b90cb9a429801a3e21d64541300071cb22a8a826001b588754d504c009ab10ea9aa098006d6a19535413000dac432a6a826006e588654d504c00dcb6eca9aa098013569d95354130026ac3b2a6a826006e587654d504c0016b708a9aa09800396d9153541300072cb22a6a826000b5b8254d504c0016b702a9aa098002d661543541300078caa286a826006c7876549504c0099b0ec992a098002d66153254130007a4a9264a826000d5953dc5504c0016b30a98aa098003d4545315413001c76412e3b2a40058be87dd1654800155b05aa6c8900023de0573d91200147a40ae7b2240008bf845d9544800b0f90eb2aa89000e3b20974d8d200147b43ee2b1a40008bf845d9534800b17908bb2a6900023de057654d200147a40aeca9a400087f855d9434800d0f90abb286900023de057650d200147a40aeca1a40048be87d91434800b1b90eb1a86900e2b52056350d20006d5206e8a924000e2f54d91524800d1d90eb22a49000e5b61773549200353742ec6a9240068ec8758d52480695c902b1aa4900063b219755092002c7643acaa1240039cd83dd532480031d90cbaa64900067a201754c9200256741eca99240048ec87595324805b55908b2a64900063b219744c92016f46322869924000de210dc5324800117f08baec2900162f21175d85200076299663b0a400287c87595514805547908b2aa2900d39918552545200347b43ec2a8a400687e851d941480010fb0a3b2829001237a0c76505200046ec18eca0a40028bc8759141480051b90eb1a62900063b219754852000c76432e890a40018ec865cd21480051d90eb1a42900163e21d65501200071cb2aa8a024005
  | 2 => 0x9754c95101c6f43ec6992a200c6c76549325446bc98c6a9264a88d3591c5524c9510347b436e2992a2038ee82dd953504011db05bb2a6a080a2fa1b7454d4102c7b436e2a9a82048bc87595435040b3390ea9a86a08e2e52055350d411c5cb41ee2a1a820387c87595525040517d0dba2a4a081a3ba1f6254941014db40ee6a1282059ac8754942504015590ca9284a080f2b1d952509410145e432e89928200c9c7650d3250473d18c4a1a64a08e3651c5434c9410247743ec499282058f686dc5325059f66d0bba2a2a080a5d21d53545411559a422a6a8a82009b48750d515044d6690aa1aa2a0897651cd43545410078aa9a86a8a8200a7486549515045566908a92a2a08a39918952545410155a43284a8a8226b34855095150401e4aa4a12a2a08162fa1276549310045ec24eca92620387e87d95524c40d1dd0fb12a49880eb3a0b644c93101c6e43ac89926203ccc76549324c45dc98caa92649881a9da1764545310347a43ac8a8a6206c7476549514c451cc8c4a92a2988027521d32545310156a43264a8a6204cd4764c9514c401e8aa4992a29881a1fa167650d210043ec2ceca1a42048be87d91434840b1bd0fb1a8690812b3a0f654c9210247643aca9924204ccc7650d324845bd18c8a1a6490816ada13655052102c7a43acaa0a4205cb47650d414844bd28c6a1a82908027921d32505210157243264a0a4203ce4764c94148401f0a8699282908028f61642d91500046fc1ae3b22a0048dc835c7645400117f08b96c6a80162f21172d8d5001c77410eca1aa0008ed821d943540051ed023b286a80023d6047650d5000c3e432eaa1aa00387c855cf6254001a7481ba2a4a80038b90b6454950034b6c16e2a92a00187c865d542540030f90cbaa64a800e37a1f634c9501af2631aa4992a00287c855d361540078dce4a96c2a8003568c373545500072b18ec6a8aa00697581dc951540054ed03b12a2a80061f21975505500145f43ec8a0aa02ae346454541540030f90cbaa62a80061f219754855000cbc402ea90aa000a3d8494f65500011df04b8ecaa000e3b20971d95400245e422e5b1a8000d3a50dd543500031790cbaa86a00038794f6550d400245e43acaa1a800599d83dc543500010ff0ab9ec4a001a1f21573d89400246f418eca9280008dd831d952500051ed023b2a4a00023d604765494001c3e43acaa9280018bc865d542500031790cba264a00e7a3189434c9400247743ec499280028bc845d7615000993ce6a1ec2a000a1fa1f655454000c5e432eaa0a80059b581dcd415000556d03b1a82a00036a88372505400075310ec4a0a8026e346554541500031790cba262a00066e201744c54000c5e432e890a8001b3887551505000ba710eaa2a0a0006cea19545414000d9c432a8a828006e3886551505000dc7
  | 3 => 0x3d400000007000007cc659c576f0871e4ef138c45d0a46208d17c41018f725427628aa5908c549ac42c9d204a64a1a62416a245b150cc269daa53d650680068c0d23d603ac000002b1a4000014214000065925c8cd2944f02d9f4815c3b18b3cd57021082112a5f81c4607d671560003b6ccf80000021989130004f07a0f0360010f368000001e4ac00000650000006c00031330000033da411c180008347000598a93c84b3757714904041783711512840001690091001d5e474260c18c001793f13553000000c866182000b00000056d3b0e800000005f000000002e4512f4ed340fe688000cc006d01401435000002646d0b190000386fcbb4d8820d00a25cbe0f80067800564cc000004492e5540051c0066c0000000490430c9701fc5300000390db0052558c5a0010a49d0d0b80053472001145890c000d900049000006bc775140039db827c00000004c80000144010000014e2600002400715610000000171000de2c40003cfd2d085000004e8cb0014a5ac002cc1769400048635b048239a15cc002008b119371916e5240057c0000000178f10000007587164000015a000310000040c9a2fd483512600000000c95e8626106b4c400000114140000000000001840000000518003a92c6c18f00000000005b4000002448454544716dd7b1a0f6114002c86c3fcc160d915d8000016f36150000e1000d5419191a800001ae314000001300000135b51b8ba550ac054d228c031090e5f5a91d800198fa4c0747180000c00800018360380e09812008000101e000000581801000008020001802800000020a80400032008020200000800038040080a050000080c008040080803818020080780400004048100180000002000000082e03802050000102c0080004800020020301400810038220002400800008020100203002008000580200034030080000a0081402802008260000600814058020001002000038000e8020200a0101e0000001800040020a808008140380001800030000580204802000100499e83dc55450c0b33d09b92a6a180e5ba0b715515201c3f436eaa1aa4048be87d91435480d2790eaa286a90168f2195450d520061e3b2a8a1aa406a6e85d8d52508051ed03bb2a8990023d607765513201c6f436e6aa264048ee86dc9544c80b1b90eb2a86990126721d5450d321cdc6412a8a1a6439b8e84dc9434c80d1d90eb22a49900e5b21d54549321ada641aa8a9264d0b4e85dcd524c8013990ea1aa4990bad3215435493216ec63a286a926400f0d5450d524c8052ed03b92a6a880a1fa1b7550d5102c6f43ec6a1aa20695c8754d43544094b90ca9a86a8803171d95350d511a5b3416e2a92a2048de83dd942544011bb07bb284a880a1fa1b7550951034b643aa4a12a234d6471549425440d1ed0db8a84a880a1f21
  | 4 => 0xdcb7409a00000035c0000000000004a40071000000000000000000001c366800445b265c0e248211748a0e4ad2a123000004d1a85fcae000e82891e088c3345ab6b5bd0a5171f94134c000bcf9001811113e0003f00055221580006f000734e0af0007800122394001ed2d618b5000ce000000a91f158ab0f47c3593d094000000046c756640027800300f06e500704b83ece60009431c000000044d3f0a11a0000063823000000585b4250127139258003a54038980674df574206558d70867001752d9bb38ca100000659be001686d8000009300193001943d000000002252f00000001072800052c5c00000000702f09b0b516180ca29c006e800160e0000000000000185000003b80054c0000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x29402401e0007006800003004022265a23866204800040022004a01acc32615450d524c87350c9755143549320064321d5450d524c8553149854d43545411c54525d5350d51504019148754d4354541154c92615250951504016249654942545411a6892195250951504019448754932545311a691219524c9514c46bc447654932545310066121d434c94148471a848650d32505211cf211d9434c94148455c307654541541401af121d9524c9504c073c887650d32501201c7241d9435053044069c60765495148110
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
  | 67 => 0xb8956
  | 68 => 0xbc955
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
  | 87 => 0xcc996
  | 88 => 0xd4994
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
  | 103 => 0xcc9d5
  | 104 => 0x150c
  | 105 => 0x128c
  | 106 => 0xe89d3
  | 107 => 0x18c9
  | 108 => 0x1789
  | 109 => 0x180c
  | 110 => 0x130c
  | 111 => 0x1a49
  | 112 => 0x17c9
  | 113 => 0x198c
  | 114 => 0x134c
  | 115 => 0xb8a14
  | 116 => 0x138d
  | 117 => 0x124d
  | 118 => 0x150d
  | 119 => 0x128d
  | 120 => 0xe8a12
  | 121 => 0x168d
  | 122 => 0x12cd
  | 123 => 0x1a89
  | 124 => 0x1949
  | 125 => 0x198d
  | 126 => 0x134d
  | 127 => 0xbca53
  | 128 => 0x138e
  | 129 => 0x124e
  | 130 => 0xd4a52
  | 131 => 0x150e
  | 132 => 0x128e
  | 133 => 0x168e
  | 134 => 0x12ce
  | 135 => 0x180e
  | 136 => 0x130e
  | 137 => 0xb8b16
  | 138 => 0xccb16
  | 139 => 0x170a
  | 140 => 0x15ca
  | 141 => 0x16cb
  | 142 => 0x144b
  | 143 => 0x188a
  | 144 => 0x160a
  | 145 => 0x184b
  | 146 => 0x148b
  | 147 => 0x1a0a
  | 148 => 0x164a
  | 149 => 0x19cb
  | 150 => 0x14cb
  | 151 => 0xbcb55
  | 152 => 0xccb55
  | 153 => 0x154c
  | 154 => 0x140c
  | 155 => 0x18ca
  | 156 => 0x178a
  | 157 => 0x184c
  | 158 => 0x148c
  | 159 => 0x1a4a
  | 160 => 0x17ca
  | 161 => 0x19cc
  | 162 => 0x14cc
  | 163 => 0xd0b94
  | 164 => 0x154d
  | 165 => 0x140d
  | 166 => 0x16cd
  | 167 => 0x144d
  | 168 => 0x1a8a
  | 169 => 0x194a
  | 170 => 0x19cd
  | 171 => 0x14cd
  | 172 => 0x154e
  | 173 => 0x140e
  | 174 => 0xecbd3
  | 175 => 0x16ce
  | 176 => 0x144e
  | 177 => 0x184e
  | 178 => 0x148e
  | 179 => 0x18cb
  | 180 => 0x178b
  | 181 => 0x188c
  | 182 => 0x160c
  | 183 => 0x1a4b
  | 184 => 0x17cb
  | 185 => 0x1a0c
  | 186 => 0x164c
  | 187 => 0xd4d14
  | 188 => 0x170d
  | 189 => 0x15cd
  | 190 => 0x1a8b
  | 191 => 0x194b
  | 192 => 0x1a0d
  | 193 => 0x164d
  | 194 => 0x170e
  | 195 => 0x15ce
  | 196 => 0x104d52
  | 197 => 0x188e
  | 198 => 0x160e
  | 199 => 0xece93
  | 200 => 0x104e92
  | 201 => 0x1a8c
  | 202 => 0x194c
  | 203 => 0x1a4d
  | 204 => 0x17cd
  | 205 => 0x18ce
  | 206 => 0x178e
  | 207 => 0x74a
  | 208 => 0x5cb
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1450
  | 6 => 3535
  | 5 => 455
  | 4 => 20
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (59446+((h/483+packedAt gbK7 (53650+(h % 483)*12) 12) % 3727)*12) 12
  | 6 => packedAt gbK6 (184994+((h/1178+packedAt gbK6 (169680+(h % 1178)*13) 13) % 4243)*13) 13
  | 5 => packedAt gbK5 (28355+((h/151+packedAt gbK5 (26845+(h % 151)*10) 10) % 661)*10) 10
  | 4 => packedAt gbK4 (1430+((h/6+packedAt gbK4 (1400+(h % 6)*5) 5) % 31)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x8e0188e0c7fc631e383f8fc1f83f00078474cf
  | 1 => 0xf00e0f00f8e383e3c038f1fe3fc7309a1a4b33
  | 2 => 0xff000ff03fc03ffc0fe003ff8431c638c3c
  | 3 => 0xfffff0003fffc0000ffffc00083e07c0fc0
  | 4 => 0xfff000000003ffffffff00000000fc007ff000
  | 5 => 0xfffffffffffc0000000000000000ffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2000020012000040808024008000000801045
  | 1 => 0x90a4090848490122411210a81306308a0a4112
  | 2 => 0x10b90129210a4009480a404a4b04314208c28
  | 3 => 0x42a2460002ea480284c91580908120740e80
  | 4 => 0xa46000040003539323260019010294005f6000
  | 5 => 0x498d4c98e49800000400002006246adf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffeafefaeee8ffffffeafefaeee8ffffffeafefaeee8ffffffeafefaeee8ffffffeafefaeee8ffffffeafefaeee8ffffffeafefaeee8ffffffeafefaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_34898
namespace PEqualNP.Outside.L_meta_34898
open PEqualNP.Outside.L_meta_34898.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_4_0 : Interval gbAtlas 4 0 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 20 := bgb_4_0
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
theorem bgb_5_448 : Interval gbAtlas 5 448 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 455 := (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448))))
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
theorem bgb_6_3520 : Interval gbAtlas 6 3520 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3535 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)))) (concat (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)))))) (concat (concat (concat (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 bgb_6_1952))) (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176)))) (concat (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))) (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624))))) (concat (concat (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 bgb_6_3072)))) (concat (concat (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)) (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)))))))
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
theorem bgb_7_1440 : Interval gbAtlas 7 1440 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1450 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 (concat bgb_7_384 bgb_7_416)) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))) (concat (concat bgb_7_544 (concat bgb_7_576 bgb_7_608)) (concat bgb_7_640 (concat bgb_7_672 bgb_7_704))))) (concat (concat (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864))) (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))) (concat (concat (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)) (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248))) (concat (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344)) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
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
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
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
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 4 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 7 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffffffffffffffffffafffafff8ffffffeefefeeeeeffffffeafefaeee8fffffffffffffffffffffffafffafff8ffffffeefefeeeeeffffffeafefaeee8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,4,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,4,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_34898.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[8,3]⟩,⟨.or,[5,6]⟩,⟨.or,[10,7]⟩,⟨.and,[9,11]⟩,⟨.or,[1,7]⟩,⟨.or,[4,5]⟩,⟨.and,[13,14]⟩,⟨.or,[3,4]⟩,⟨.or,[16,7]⟩,⟨.and,[0,17]⟩,⟨.or,[12,15]⟩,⟨.or,[19,18]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_34898

open PEqualNP.Outside.L_meta_34898 in
theorem PEqualNP.Outside.L_meta_34898 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
