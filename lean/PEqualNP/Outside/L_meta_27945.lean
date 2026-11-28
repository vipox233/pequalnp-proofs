import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_27945.Model
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


end PEqualNP.Outside.L_meta_27945.Model

namespace PEqualNP.Outside.L_meta_27945
open PEqualNP.Outside.L_meta_27945.Model
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

end PEqualNP.Outside.L_meta_27945

namespace PEqualNP.Outside.L_meta_27945
open PEqualNP.Outside.L_meta_27945.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x5427031e00005a72a0002a00807001801283106911b1200b18265c010002802b521c0804610e822400a2622000283e6478d48080080689184082001082ff43fe43fd43fc43ff42ef42fe42fd42fc42ec42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xd4002c0000000000007c000000c0000080a51c0000840000e4f800dc6040001448106845084c00013114392464b008fc00889d0400c47110251800c8ec0000013ca0f000349960554c0000940000000ca950cc0031552800b86d0d3800003d2c18d09051356920e01c5804e88d5cac20b4bd44000001416428007400d8014958f500005c780c0008000000080202040c000200000c00120e00000004080a001a0e08056e5290edaa521dbd4943b6292876e5210edaa421dd94443baa88877a5010ef2a021db54f42b7294855e5310abaa6215d94442baa88857a5010af2a0215b95042d72a085ce5310adaa6217354c42a6a9885ae4310b5886217994442f2a8885ea5010bd2a0215b95232b62a4656d538ca7ea8994f15132d7aa2656e544cad8a8996b15132962a265cf534cb9c86997350d32b729065ac42d06f4a1a0de54341b7294836d52906dea4a0db14941d6212836e52cc6daa598ded4131bc282633e540c67aa818db94831b6a90637a500c6f2a018cf952219eaa443ac42d02eca3a05d54740b7294816d52902dea4a05b14940d6212816e52cc2daa5985dd4530ba28a613e540c27aa8185b94830b6a906176510c2eaa2184f952209eaa4413e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2a0000226890004a2e3a4730b0650068001802a58278c481558c624070d5390c42a95844310aa96010c42d154e5110b455354442d254e5010b495354042d85455010a2e6495132c358c544cb266115132c9584544cb2a6015132ca580544cb0c5490d3293195434ca8d6310b41ca10950d068d63109418b19152cc68d6310b40c910951d028d63109408b19152cc3515344010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x80040c1018158d6115132c12c6b00a89962161580544ca84b9884a8683415cc4254740
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
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (2697+((h/30+packedAt s0K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s0K3 (990+((h/8+packedAt s0K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s0K2 (249+((h/1+packedAt s0K2 (245+(h % 1)*4) 4) % 10)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x878f0f1fc7fc7fe38c70f1c0fc7e1ffe43333f
  | 2 => 0xf80ff01ff8ff8ffc0f80fe00ff8fe1fe8c3ccf
  | 3 => 0xfffe3ff000f1ff000ffff1ff001c10fcf0c
  | 4 => 0xfff00003fffff01fffff00001ffffe01f00ff0
  | 5 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc111a028544884028414505224121454431115
  | 2 => 0x14220a50a29018140888a224488540a88c244a
  | 3 => 0x334466191239222d9002348e1d20cd0d054f0c
  | 4 => 0x22004482002002492122000812488801100aa0
  | 5 => 0x4408880024c24c924e4cc93080011030eab000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xffffffc0fcfcc0c0ffffffc0fcfcc0c0ffffffc0fcfcc0c0ffffffc0fcfcc0c0ffffffc0fcfcc0c0ffffffc0fcfcc0c0ffffffc0fcfcc0c0ffffffc0fcfcc0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_27945
namespace PEqualNP.Outside.L_meta_27945
open PEqualNP.Outside.L_meta_27945.Model
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
end PEqualNP.Outside.L_meta_27945
namespace PEqualNP.Outside.L_meta_27945
open PEqualNP.Outside.L_meta_27945.Model
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
end PEqualNP.Outside.L_meta_27945
namespace PEqualNP.Outside.L_meta_27945
open PEqualNP.Outside.L_meta_27945.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x485d49e207571600600a55e80d8f043489a105150a446460012a000b38b439258000033e10a800aad323424d3801c000000c00000137200d2162c5082005ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fa30fd30f930fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x291602ca80035820001f2f0785a5b2b1f0380d00000020643090443d3000088000000000402c9402284419dc00250184d005c0014cae363e800e24742924fc142a92cda7b2184860701f88000370798ca44d3119c4c38138f020733313c145a159fcf4092405cbe4235128c82e00060543501075023b3c21cde6e0b0e4502f071748c5130800f200000000000260d0e40700000341b000000a3a022080033348c4ea00000840000340648a323b08c9c652c1d02a41360f818100f0d09093504000320000015110004342300030201001200040c380019090400030b0002160006030b041300bd28487795090e7ca721cf54a439ea8c87ba5090f72a121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed944439ea8887b55110e6aa221ee94043dca80873e53d0a7aa3a14f552429e29a85af5250a7ea2a14f950429faa6653c54ccaf4a1995e543329f2a4653d548cb5a85194fd51329e2a265ad424ca7ca8194f55032bb2886575510caf4a0195e540329f29e833d52d067aa920cf14d419fa9283b7515067ca820cfd53319e2a6637a50cc6f2a198cf952319eaa463b5418c67ea898cf15131daa0a633e540c67aa818db94831b6a90637a500c6f2a018cf953219eaa6433e548867aa910cf951219eaa2437b50486f0a090cf950219eaa0435e53086baa610f948421bd280437950086bca7205754e40ce21e613e548c27aa9186e95230dcaa46179538c37487186e10e30dda1461b9428c37683186e506309faa2613c544c33886986ed5130dc2a261db534c3b686986e90d30dc21a61d8434c33086986ed0930dca1261db324c3b264986ed0530dca0a61db314c3b262985e940309f2a6413d54c827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1030c050e00989003490a460180062000192a017ae480912922a8316585d5835a9ce203c7d29d346c09420005a81c3c20042000004c1000c034000c84000a3c604fa65825310f255294443c99495110f255254443ca54a5010f315194043ca5495010f3151540438d5845350a3561153328b195424ca2d6214d418b58854cc63465505318718d54486596314121d154d21087612154021a358843cc2956110f30aa588438c2b16110e30a3588434c2956110d30a6993534c23a6590d30a698e434c23a6510d30aa588434c2b16110d30b2588434c2d16110d30a6994434c31a6510d30e2988434c2996210d30e2588434c2896210d30e4984434c2996110d30e4584434c2916110d30a618d424c29864cc930a6191324c389424c930a618d414c29864cc530a6191314c391414c530
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x50206020440398065a058a6110d30d04c4b08869868162584434c248b88c6a1261245c464cc930910eca1264984897218d414c244b90c998a61241d9414c530
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
  | 3 => packedAt s3K3 (1996+((h/16+packedAt s3K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s3K2 (453+((h/3+packedAt s3K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf0e3cffc38e3e3f38e3838fe38e38ff30f90f
  | 1 => 0xff03f1ffc0fffc7c0fc03f1fc0fff0f4331f3
  | 2 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x6160464849144c401860988260a28866305905
  | 1 => 0x82048880902810084084211084051208412052
  | 2 => 0x8910112200a001a100422409402480828228
  | 4 => 0x2420004a080004920a29080032288022140d80
  | 5 => 0xc8cc2290334d3924f4d273c9004106ccebf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_27945
namespace PEqualNP.Outside.L_meta_27945
open PEqualNP.Outside.L_meta_27945.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x920000000001801d285c000002d1264aac01c0430010003d38a368d48400200112aa0016340150532901981a780200e01089007c0131c340000084040000280003ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2504004000000079280c0000e8e0a400d134000000011560000000852c6000fc000000cc01500110bcc8c40064008c00000000000001394ca000002c013d545c00000000b8ac00ec000000000000140000014800700000008800015c7cf0005800509800015920f8005434009400189c1c6cb4c001186800d50c800000000000d84d1c28100090b030484420f43c3804e5014568000001080000014000a800000001240000013000dd647400080000000408021c00120002040006000800000812000000000a000a00000212053e5390e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110f6aa221ee940439ea8087b95010e72a021d794e42aea9c859c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a655e53906baa720e710f31b7296636d52cc67ca918cf552319faa2633c544c7388698cf950219eaa0435e53086baa610f948421bd2804379500867ca7a04f55240afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f950409faa6613c54cc27ca9184f55230ce21c61b9408c27ea8984f15130dca02613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a4413d54882eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9084f55210b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xa230e930b8002612872c81828001e016500006000008a8001a40048008008600147255254443ca9495010f295254043cc9455010f315154043a658043ccb144354732a6580434ca996010f31c310d52cc6996010d31d8485500870e6214d40c358853503166114d40c558453503196014d40a6580438c29863502308e195404c21d6510c30c310d520c31443544308718d548821c6355210
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1008004000c0001445c04354732a12e021aa598e05625845350304b12c029a81845856014d40
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 4 => packedAt s4K4 (2697+((h/30+packedAt s4K4 (2457+(h % 30)*8) 8) % 176)*8) 8
  | 3 => packedAt s4K3 (998+((h/8+packedAt s4K3 (950+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (249+((h/1+packedAt s4K2 (245+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 1 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 2 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 3 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 1 => 0x52228891414810a0521244248449414612512
  | 2 => 0xaa444512412900354802489092092941828a28
  | 3 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_27945
namespace PEqualNP.Outside.L_meta_27945
open PEqualNP.Outside.L_meta_27945.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1946ac017382801a3e9c3002c8802c4204e805e009824094f0e2000000504521818986aa121c92e00556801e15483102ca1b080814911584c70401c00410c2ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5c28530014000721b1cc0000000000000000008e00261a4c65103800dc7b13800080000194000c0000000310016c3a59001b04400000f0005200000321e331a10a2f0684838552d038da212582c2c181d00000004380c122c000004c4f2b8fc005d1d90036460019c0000000a4700000068c20031000003900000000016800006a001fc00752f04c4a0a1b8007a4e0f89040003e120001041128005c3a000de00199e8000f000008656028a82a5419190005f1a000507141910002b001c060353ca0102022c044ee083008c0206431247c00209f48a7e001085c00269ac0078000000000000000000000000076002100000000301121803010400030001000100010100000003030a0006010a0300000002010101020500030401010203bd286877950d0ebca7215754e42af298855d5310aeca2215d54442bd28085795010abaa3995794332aea9c65cf524cabea2995714132af298655e53906baa720d794c41aea98836e52106daa420de94041bca80835d52cc6bca198d754e31afa9263d7514c6b8a098d794c31af29e435d53c86bca710d754e219faa2433c54486bca690d754d219f2a0433d54086bca610d754c21f2908437a50086f2a010d794f40aea9e819e53d033aa7a067ccb40ce996819f31d033a63a04f55240afa9a815c535033ea6a06714d40cf992819d325033e62a0674c540dda82813e541037281984f952309eaa4619e548c33aa9185754a30aea8c615e508c33e811867502309f2a0613d540c2dca4185b54830bb2886175510c37280186795030ceaa061ce520c2baa4187354830a6a9061d6510c2baa2187554430aaa88615e500c3b4a01867d0030ed200619d400c3b280186650030af29e415d53c839a65904f952209eaa4415f53882b8a7106e50220afa9a415c534839a64906e501209f2a0413d54082bca6105754c20bb288417551082bca7885754f10ea98e213e548427aa90857d4e10ae29c21b940842bea6885714d10ea98a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x168c54a451300ac3003a01197281c222340180b003818000013853e9801502012af22007ac00210983ca048040008004848031380001636086ae324c08183007c00400000000a1520195584504ca4d62141318e58054486586054d21c955121087612154021a61813250298604c540a698f50503295250030cc545400c30e5454830c3551520c3455294430c5951510c3155454430d1949510c3455254430a6592500c21d65d0030c354b400c31551d0030a6592400c3495290030d4546400c21f6550030c3549400c3155150030d2549400c3515150030a6d95400c31b6550030e2949400c3195250030e2549400c3095250030e4945400c3195150030e4545400c311515003095584538831853502209319532483185350120e24c9404824d6214e10c614d4084254654c510c614d40443913150110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x10c04280e600400020061245c4604c940912e430262a070152945400c381292a2a0061c05495150030a22e229a8110508754c94048284b90a6a0421441d53150110
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
  | 4 => packedAt s5K4 (4032+((h/45+packedAt s5K4 (3672+(h % 45)*8) 8) % 217)*9) 9
  | 3 => packedAt s5K3 (2012+((h/16+packedAt s5K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f838e3cfffe3f1c71e3870c7ffe3f0e43cf
  | 1 => 0x1fc7fc0fff0f1fc7e07e3c07ff8e0fc7307d33
  | 2 => 0xe007fff03ff01ff8ff803ff80ff00ff8c38e3c
  | 3 => 0xfff800003fffe000ffffc0000ffff000fc0fc0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8300a01044441040082060a140128224064045
  | 1 => 0x44110824082024082012040224842482101512
  | 2 => 0xa21100900248014480091009204910408a28
  | 3 => 0x48b05b4d22aa0c92f5548050ae496192f80f80
  | 4 => 0x9104620802cc91249a693264c0018024af6000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8fefceae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_27945
namespace PEqualNP.Outside.L_meta_27945
open PEqualNP.Outside.L_meta_27945.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x26001ff1013000ffe6098013fb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ffc813000ffc4098007fc204c003ff8826001ff8413000ff82098003ff65480017fb2a400eff99520035fcca90003fd65480017eb2a400eff19520035f8ca90003ff64480017fb22400dff9912002dfcc890003fd64480017eb22400dff1912002df8c89003bff544801bff2a24000ff5512006ff8a890003ff63480017fb1a400cff98d20025fcc690003fd63480017eb1a400cff18d20025f8c69003bff5348019ff29a4000ff54d20067f8a690037ff4348019ff21a4000ff50d20067f88690006ff6248007ffa924003ff9492001ffaa49000ffc5248007ffa124003ff9092001ffa849000ffc4248007ff9924003ff8c92001fdc649000ffd3248001f69924003ff0c920007fec290002ff6148017ff30a4002bf98520007fac29002ffc61480057e30a400effd452005ffca290003fd5148017fe28a400dffd052005ffc8290003fd4148017fe20a400cffcc52005ffc6290003fd3148017fe18a4003ffc852001fde429000ffe2148007fe90a4000fb4852001ff84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ff48090007fd4048001fca024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe409000ffb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824000ffd9510005feca8802bfe654400d7f32a2000ff59510005faca8802bfc654400d7e32a2000ffd9110005fec888027fe644400b7f3222000ff59110005fac888027fc644400b7e322200affd511004ffca888003fd5444013fe2a22000ffd8d10005fec688023fe63440097f31a2000ff58d10005fac688023fc63440097e31a200affd4d10047fca688003fd5344011fe29a2009ffd0d10047fc8688003fd4344011fe21a2000ffd8910005fec48801ffe62440077f3122000ff58910005fac48801ffc62440077e312200affd491003ffca488003fd524400ffe2922009ffd091003ffc8488003fd424400ffe2122008ffcc91003ffc6488003fd324400ffe1922001bfd8510017fea28800bfe5144005fea8a2002ff14510017fe828800bfe4144005fea0a2002ff10510017fe628800bfe3144005fb18a2002ff4c510007ea628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001fe9011000ffa8088003f94044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd415402ffe20aa019ffcc5500bffc62a8003fd315402ffe18aa018ffc85500bffc42a8003fd215402ffe10aa001bfd815000ffea0a801bfb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001ffd015000ffc80a8007fa4054003fe202a001ffcc15000ffc60a8007fa3054003fe182a001ffc815000ffc40a8007fc2054003ff882a001ff8415000ff820a8003ff65500017fb2a8016ff99540035fccaa0003fd65500017eb2a8016ff19540035f8caa0006ff645000bffaa28016efd514002ffca8a0017fd545000bfe2a28005ef15140007fec6a0002ff6350027ff31a8004bf98d40007fac6a004ffc63500097e31a8016ffd4d4009ffca6a0003fd5350027fe29a8005ffd0d4002f7e86a0017fe435000bfea1a8000ef50d4002ff886a0003ff62500017fb128015ff9894001dfcc4a0003fd625002bfe3128003bf189400b7fea4a0057fe5250001fea928015ff1494002ffe84a0017bf425000bff2128005ff509400077a84a0017fc4250027ff9928015ff8c940007fa64a0057fc3250001ffb0a8000bfd85400a7fcc2a000afe6150001feb0a8014ff18540015f8c2a005bff5150029ff28a8000ff545400a7f8a2a0017ff415000bdfa0a8005ff9054002ffa82a0003bd415000bfe20a8013ffcc5400a7fc62a0003fd3150029fe18a8015ffc85400a7fc42a0003fd2150029fe10a8001bfd814000ffea0a0007fe5050003fd2828001ff54140007f2a0a0007fc5050003ffa028005fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007ff3050027fd9828001ff8c14000ff860a0007f83050003ff9028001ff8814000ff440a0007fc2050003ff8828001ff8414000ff420a0007fc1050001ffb2a6000bfd9530097fcca9801afe654c001feb2a6000bf59530097f8ca9801afc654c001ffb226000bfd913008ffcc898016fe644c001feb226000bf5913008ff8c898016fc644c025ffaa26011ff95130007faa898047fc544c0037fb1a6004ffd4d30027fca698013fd534c009fe29a6004ffd0d30027fc8698013fd434c009fe21a6000ffd8930005fec498043fe624c0077f3126000ff58930087f8c49800efc624c025ffa926010ff94930007faa498043fc524c023ffa126010ff90930007fa8498043fc424c009ff9926004f7cc930027fc6498013fd324c001ee9926004ff0c930007fec298002ff614c01fff30a6002bf98530007fac29803ffc614c0057e30a6012ffd453007ffca298003fd514c01ffe28a6011ffd053007ffc8298003fd414c01ffe20a6004ffcc530027be6298013fe314c009fe98a6000f74c530027f86298043ff214c01fff10a6000ff4853007ff84298006ff604c003ffa826001ff9413000ff4a098007fd504c001fca826001ff1413000ffe8098007fe404c003fea
  | 2 => 0x31107f88498813ff324c409ef9926204ff8c931027fa6498803dd324c409fe1926202bfd8531017fea29880bfe514c405fb28a6202ff54531007eaa29880bfc514c405ffa0a6202ff90531017fa829880bfc414c405ff98a6204fdcc531017fc629880bde314c405fe18a6202f70c531017e8629880bff214c405ff10a6202ff08531007fec098802ff604c43fff3026201bf98131007fac09887ffc604c4037e3026222ffd41310fffca09887ffc504c443ffa02621fff901310fff88098813ff304c409ef9826204ff8c131027f86098883ff204c43fff102621fff08131017fe209880bf7104c405ff0826202ff04131007feca90802ff654843dff32a4206bf99521007faca90802fd654843dfe32a4206bf19521007fec890802ff644843bff3224205bf99121007fac890802fd644843bfe3224205bf191210f7fea890877fe5448401feaa2421dff15121007fec690802ff6348439ff31a4204bf98d21007fac690802fd6348439fe31a4204bf18d210f7fea690873fe5348401fea9a421cff14d210effe8690873fe4348401fea1a421cff10d21015fec49080fff5248407ff2924203ff5492101ff8a49080fff4248407ff2124203fb9092101ffa8490803ed4248407fe2124203ffcc92101ffc649080ffd3248407fe1924202bfd8521017fea29080bfe5148405fea8a4202ff14521017fe829080bfe4148405fb20a4202ff50521007ea829080bfc4148405ff98a4202ff8c521017fa629080bfc3148405ff90a4203fdc8521017fc429080bee2148405fe10a4202fb08521017e8429080be42148401ffb024200bfd81210dffcc090806fe6048401feb02421bff1812100df8c09087bff5048437ff282421bff141210effe809086ffe4048437fe202421cffcc1210dffc609086ffc3048407ff9024203fbc812101ffc409080ffc2048405ff8824202fdc4121017fc209080bfc10484037fb2aa000ffd9150005fec8a806bfe645400b7f322a000ff591500d7f8c8a8016fc645400dffaa2a006ff951500d6fca8a801bfd545400dfe2a2a006df15150007fec6a8002ff6354001efb1aa000b7d8d500cffcc6a8012fe6354001feb1aa019ff18d50025f8c6a8003dc63540096e31aa006ffd4d50036fea6a801bfe535400dfea9aa000df54d50037f8a6a806bff4354033ff21aa000ff50d500cff886a8003ff62540017fb12a018ff9895001dfcc4a8003fd6254031fe312a003bf18950037fea4a801b7f525400dff292a006ff54950006faa4a801bfc5254035ffa12a018ff90950007fa84a8063fc4254033ff992a018ff8c950007fa64a8063fc3254001ffb0aa000bfd85500bffcc2a800afe6154001feb0aa017ff18550015f8c2a801bff515400dbfa8aa006ff94550037faa2a80037d515400dfe28aa01affd05500bffc82a800
  | 3 => 0xeaa2a206ff15151007fec6a8802ff6354453ff31aa204bf98d51007fac6a88a7fc63544097e31aa206ffd4d51037fca6a88a77e535440dfea9aa206ff14d51036f8a6a88abff4354453ff21aa200ff50d5114ff886a8803ff62544017fb12a228ff9895101dfcc4a8803fd6254451fe312a203bf18951037fea4a881b7f525440dff292a206ff54951006faa4a881bfc5254455ffa12a228ff90951007fa84a88a3fc4254453ff992a228ff8c951007fa64a88a3fc32544057fb0aa202ffd4551037eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405ffa0aa202ff90551017ec82a880bfc4154405ff98aa202ff8c551017ec62a880bfc3154405ff90aa202ff88551017f842a8803ff60544017fb02a227ff9815100dfcc0a8803fd605444ffe302a201bf18151037fea0a881b7f505440dff282a206ff14151157fe80a889ffe405444ffe202a229ffcc15113ffc60a889ffc3054451ff902a227ff8815113ff840a880bff1054405ff082a202ff04151007fecaa0802ff655044dff32a8206bf99541007facaa0802fd655044dfe32a8206bf19541015fec8a0817ff545040bff2a28205ff5514102ff8a8a0803ff63504017fb1a8225ff98d41025fcc6a0803fd635044bfe31a8204bf18d41137fea6a0897fe5350401fea9a8225ff14d4102ffe86a0817fe435040bfea1a8205ff10d41007fec4a0802ff6250449ff3128203bf98941007fac4a0893fc62504077e3128226ffd4941127fca4a0803fd5250449fe2928205ffd094102f7e84a0817fe425040bfea128200ef5094102ff884a0897ff3250449ff1928200ff4c941127f864a080aff6150405ffa8a8202ff94541017eca2a080bfd5150401faa8a8202ff14541017fe82a0817f74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ffcc541017fc62a080bfc3150405ff90a8202ff88541017ec42a080bfc2150401ffb028200bfd814111ffcc0a0806fe6050401feb028223ff1814100df8c0a089bff5050447ff2828223ff1414102ffe80a0817bf405040bff2028205ff1014112ffe60a088ffe3050447fe1828224ffc814111ffc40a088ffc2050405ff8828202ff84141017f820a0803ff654c4017fb2a6222ff99531035fcca98803fd654c4017eb2a6222ff19531035f8ca98803ff644c4017fb226221ff9913102dfcc898803fd644c4017eb226221ff1913102df8c89888bff544c443ff2a26200ff5513110ff8a89880aff634c409ffa9a6222f7d4d31027fca698813fd534c409fe29a6204f714d31027fe8698813fe434c409ef21a6204ff50d31007ba8698813fc434c401ffb126200bfd8931107fcc49880efe624c401feb126220ff1893101df8c49888bff524c441ff2926200ff54931107f8a498887ff424c441ff2126200ff509
  | 4 => 0xffe2154807fe10aa400ffd8152005fec0a90cffe60548037f302a400ff5815219ff8c0a9006fc605480dffa82a406dfd4152037fca0a901bfc505486dffa02a433ff9015219ff880a90d7ff3054867ff182a433ff0c15201ffe40a900ffe2054807fe102a434ffc415219ffc20a90cffc1054801ffb2a8400bfd9542197fccaa101afe6550801feb2a8400bf59542197f8caa101afc65508077fb228405ffd514202ffca8a1017fd545080bfe2a28400ffd8d42005fec6a10c7fe63508097f31a8400ff58d4218ff8c6a1012fc6350865ffa9a8431ff94d42007faa6a10c7fc535080bffa1a8405ff90d4202ffa86a1017fc43508077fb128403ffd494201ffca4a100fee5250807fea928400fb5494201ff8a4a100fff425080bf7a128403ff9094201f7c84a100ffc4250807de2128403fb1094201ffe64a100ffe3250807fe1928400ffd8542005fec2a10c3fe61508057f30a8400ff58542187f8c2a100afc6150865ffa8a8430ff94542187f8a2a1017ff415080bdfa0a8405ff9054202ff882a10c7ff3150861ff18a8430ff0c54201ffe42a100fef2150807ff10a8403ff08542007fec0a1002ff605085fff3028401bf98142007fac0a10bffc60508037e3028432ffd414217ffca0a10bffc505080bffa028405efd014202ffc80a1017fc4050863ff982842fff8c14217ff860a100fff2050807ff1028403ff08142187fe20a10bffe105085ffe0828400ffd9532005feca990bbfe654c80d7f32a6400ff59532005faca990bbfc654c80d7e32a6400ffd9132005fec8990b7fe644c80b7f3226400ff59132005fac8990b7fc644c80b7e322642effd513216ffca899003fd544c85bfe2a26403bfd8d32027fea6990bbdf534c809ff29a6404ff54d32027f8a699013dc534c809ffa1a6404ff90d32027bc8699013fd434c801eea1a6404ff10d3201dfec49900fff524c807ff2926403fb9493201ffaa499003ed524c807fe2926403ffd093201ffc849900ffd424c807fe2126403ffcc932027de649900ffe324c807ef1926403ff0c93201fb8649900fec324c801ffb0a6400bfd8532167fcc29900afe614c801feb0a642cff18532015f8c2990bbff514c859ff28a642cff1453216ffe82990b3fe414c859fe20a6404ffcc532027be6299013fe314c809fe18a6403ffc853201ffc429900ffc214c801ffb026400bfd813215ffcc099006fe604c801feb02642bff1813200df8c0990bbff504c857ff282642bff1413216ffe80990affe404c857fe2026404ffcc132027be6099013fe304c809fe1826403ffc813201fde409900ffe204c807fe102642cffc413215ffc20990affc104c8057fb2aa200ffd9151005fec8a88abfe645440b7f322a200ff59151157f8c8a8816fc645440dffaa2a206dfd5151037fca8a881bfd5454401b
  | 5 => 0xd53027fc86a9813de4354c09fe21aa600ffd8953005fec4a98f7fe6254c077f312a600ff589531eff8c4a980efc6254c0dffa92a606ff94953037f8a4a98fbff4254c7bff212a63dff10953027fe64a9813fe3254c09fe192a600ffd8553005fec2a98f3fe6154c057f30aa600ff585531e7f8c2a980afc6154c0dffa8aa606ff94553037f8a2a98fbff4154c79ff20aa63cff10553027fe62a9813fe3154c09fe18aa63dffc85531e7fc42a98f3fc2154c01ffb02a600bfd81531dffcc0a9806fe6054c01feb02a63bff1815300df8c0a981bff5054c0dbfa82a606ff94153037f8a0a98fbff4054c77ff202a63bff10153027fe60a9813fe3054c09fe182a63dffc81531dffc40a98effc2054c79ff882a63bff841531dff820a9803ff6550c017fb2a8600dfd9543004fecaa18ebfe6550c0d7f32a8600ff59543005facaa18ebfc6550c0d7e32a8600df19543034f8caa1812ff6450c0bffaa28605ff9514302f7ca8a1817fd5450c01deaa28605ff15143025fec6a1813ff5350c09ff29a8604f794d43027faa6a1803dd5350c09fe29a8604ffd0d4302fbe86a1813fe4350c09df21a8604ff10d430277886a1813dc4350c01ffb128600bfd89431cffcc4a180efe6250c01feb128639ff1894301df8c4a18ebff5250c73ff2928639ff1494302ffe84a1817fe4250c0bfe2128604ffcc943027be64a1813fe3250c09fe1928600ffd8543005fec2a18e3fe6150c057f30a8600ff585431c7f8c2a180afc6150c75ffa8a8638ff945431c7f8a2a1817ff4150c0bff20a8605ff10543027fe62a1813df3150c09ff18a8604ff0c5431cffe42a18e3fe2150c71fe10a8600ffd8143005fec0a18dffe6050c037f3028600ff581431bff8c0a1806fc6050c75ffa828637ff941431bff8a0a1817ff4050c0bdfa028605ff9014302ff880a1813ff3050c09ff1828637f78c143027f860a1813dc3050c73ff9028637ff881431bff840a18e3ff1050c6fff0828637ff0414301dfecaa9003ff64548017fb22a436ff9915202dfcc8a9003fd645486dfe322a405bf19152037fea8a901b7f545480dff2a2a406ff55152006faa8a901bfc5454801ffb1aa400bfd8d521affcc6a9012fe6354801feb1aa435ff18d52025f8c6a901bff535480dff29aa435df94d52037faa6a901bfc535480dbe29aa436ffd0d521affc86a9003fd435486bfe21aa403bfd895201ffea4a901bef5254807ff292a403df9495201ff8a4a900f7c5254807f6292a403ffd095201ffc84a900fee4254807fe212a403ffcc95201ffc64a900fee3254807fe192a400ffd8552005fec2a90d3fe61548057f30aa400ff585521a7f8c2a900afc615480dffa8aa406dfd4552037fca2a901bfc515486dffa0aa434ff905521a7f882a90d7ff3154869ff18aa434ff0c55201ffe42a9
  | 6 => 0x306200c0000300e0000f8000220400383600001c0000103603c1081c0000000000000601c0d00100a00000037000018098000220000283e0000080002101004c0380f0000f00700c01e0240381200002c0000b00002c0100200615c0080200204c000000420080000a0b603c0183201a0081b80500201c03006000004088070060580280300c0540380f00c000018000000040180000402c08006030000000180380100000302402c0200600c0040000c00601c0080c00000418003042008000000040080100300001004007000024058050040cc0185c00e094060000020440080901c0001f06000c0240280c0000040080100000402801004000000030100000000000201c000070000340000300200c1800100a00c03800000034018030000040780001c018000060060540280601a0200180001801c028040160000a80f00604c02826020010030000140400000502a000078190300180000600206801801000008080100000000482a00a00c0000100e0040380101201c0000100000c038030000080000500a0283b00500a000030040000180100b00409c0003701c1240285f0080000602b0020000300b0000141481201201c01000054038008010100300c02c01c00000806024008030020020000200000403c00074002008000000000240000502c010008180000000381d0020580280001e02c0200a00e00401805018010080050020000d00100406409806000008058120760240180803406c0000400604401816ff655500b7fb22a805ffd51540377ea8aa017fe545500bbf2a2a805ff1515402ef8a8aa017bc5455001ffb1aa800bfd8d54217fcc6aa012fe6355001feb1aa842ff18d54025f8c6aa01bff535500dff29aa806ff14d5402ffe86aa017bf435500bff21aa805ff10d54007fec4aa002ff6255083ff312a803bf98954007fac4aa107fc62550077e312a806ffd4954036fea4aa01bfe525500dfe292a805ffd095402ffc84aa017fc4255085ff992a841ff8c95420ff864aa003ff61550017fb0aa840ff98554015fcc2aa003fd6155081fe30aa802bf18554037fea2aa01b7f515500dff28aa806ff1455402ffe82aa017fe415500bfe20aa842ffcc554207fc62aa103fc3155083ff90aa840ff88554207f842aa003ff60550017fb02a83fff9815400dfcc0aa003fd605507ffe302a801bf18154037fea0aa01bfe505500dfe282a805ffd015402ffc80aa017fc4055085ff982a83fff8c1541fff860aa107ff205507fff102a83fff08154207fe20aa0fffe105507ffe082a804bfd9553007fec8a9802ff6454c7dff322a605bf99153007fac8a98fbfc6454c0b7e322a606ffd5153037fca8a981bfd5454c0dfe2a2a604bfd8d53027fea6a981bdf5354c09ff29aa604df94d53027f8a6a98137c5354c09ee29aa604ffd
  | 7 => 0x24f9599dc9308080360de0000001e18000000001a5a84ac70001a301480008095604b9bf220a8a80000000000e8391acab00ce1688000e98000002c60549c5abdabf9a50388e10001339db88c0fe02b1ff8be0001830002638ee9bb9bd2a78001afaa08001d399226f00000000000004e91c0138000000002c19a90e31db14f02da89a7718893499da860ac9d818591327611b0b68b816099f1b7000264aaaa368000001cf9ba23500a8f480018a19403b0000de8da0001190000000002b3150287079abe22b99f8b61ca1e4953a5c27200028c8000001d4a4a00000020c00006908a8912ac23819329e0a3974a7f8b31361dd96d0f600000002419b2628dba5325685980009f9149ad9420040a716525827c00022798415200003da702008d58fc8c18000d080027c8002b128f811a8085ca9788d00000000020b8d00468000000b8a0a1272800002a40e68002b40002c02992188000000002788000f0a4b25501500009700027d9768002280d68000710000000000c802791d80018680006e04f11c80017300000016e003822a068d2143042000000000127a4c195a650000000000000dd0e216fa9d0001911680df237a9591ba3580029800020c8002838001c99499be2120ed03128790d16125403d084aa21188001c78fb0000001250958000f90001bd800000000086000094aa708e02512314109ba328dc2bd125a5e836a7e97e0cc0000000a92738000ab24e85a25f97500016b80c00000000000000f8a280024113b8d385d27511e1879bf8000088531511c91e38baa14a3ea150001a10f1000000052154aba0001a794aa508002bb07b9b00900299b78762c30b417f8679529d92c49ea051a821f91f881f14c9cd883021a25136aa29780001ec14d81c0c098c8a58e0a42182a419819638000a100007d1a487387584e001a2f00017b82625a00008f0000002c38001710001a197c2c928894c042ab296f2330cb8ae00009600000005880006880018b9f681d90f0002258001e510d853948a618a61e10ee2968002682428bf990a7b2b91118000658ddaad8879078ba01700022f82baaf0a798a8001578000e40000010001508cf2c81221d1a938ef8869aa15c81a9c38928ec9648699ab1f806aa110be9d314e1020d81c18000000110f787fa2280e02a9d98d724d0718d52b5ab684f8000002a39ad0000001800cb2071e6165a140ad1a99090000129cb86d1518001e98000f280005f80000002f0001a70f88001ae2779199d21fd2a189a1468342bc27e116832000002012054068090020b00180f0060e42300401e02c030010000002c80001000c0080200a0000180200001c018000000a4090050160c0028000000000080e0000040f0080200400080c0000143f00d00600c05800018000008000600001600000401c00800000000050
  | 8 => 0xf0000d31128000001e01f5ac296c2272bf09b10b01893c9b080000015e00003994183a1a60000a2226000231a880ac1de00024415b04005b16024700f13905080005690b8bd82583aaaa2c99070620af8ef1d622b1d78f396224925b0000dc93518819c1e4139977a0620581d000213a10a8c0e399e83b935a69a6590984d26f8001a424a95514b0002220470e58000969b9876a5ca3212a0000000000c40001c680019a12186386f80028d2aba818fb85e1ee8c10650bb13710a0f50000ca0ed80018995a00000000019802a14380022e0a420000012a9a000000016998d84613d83723c20a8001d2a970221f2000a5798b2c40000000048a0a5b9bc9dc0fa20f0000000000ec00000007288c9151948f719503e1e5aa80001629961891429a8a91a0820d21e9dea90a5592f1200121770eb1b296b1e79030819988e90c587b2931860309b399926722c0e825885b8b780004a80013800b2119f98002c22518c20000608001490002b628e97a85727284d92faa9a6b12da3a95e9c12b70998e7922a4c8748c98f824d9ee0000001f52a125d2960b90029da92d1ce9cc955ab82620e524e06425223000d29a9bb04c23d97008b2451cd024abc8000001a09f00000000d91e68ae8c79d8805047819a4f0990cd1b80f31069ed8f98c527190e20eaae2c1184816a0b0000b59e300019c87a0000000b51b10000a68378ea13121286801e8559970988a8a219741c212e1b32710000c695325994417587c29c0942050950000000001df00011d2388102049c3275893a769d593196412ea0d9340002b184b1be85c110172a4992396313aa3f978a3f1e089a8612099faa3611102305825020208928b0752a327f217a4380007a88811eacb1c09f083f8292b383009d0002042ab1820002039b699a8db14592b09c2390b981595720928283c1012168a49fe04c9cc1761901171291fc0021c50cc8b29fa09e97095f0f6a6607c9a21a392b9038178c3a43234a4007722da1b87e8bc20326c11a9ef87017b1379280d41d7244a1d21b1b1993ab22ae90e882852902971a5489082ea40aad08ba811f18590e4a8f18109e22886a29986b96a03505407200d8c30338d124b94d0319d0a4622a0160870f198d1661af17d81081f90c0381bc2afa5aa47a0e0000d79f28551d509229e9d423a06d9b4967a6a15886c1668001242a8aca0091852a587910aa4690c8b205e8000e603308a13b04987f16aaa511f0df83481305121e1248212c52b88bb94e8fe826996a67947000285a560002c080b94f8000000aa80000024802c1f42a918e88f88e8d984480623984195a91382d29b21f21605da6d9320b099d00694b8782a68c2a159aa8fd81a28d80ca74a6e0239dd0b38f018c00725d9b893018f1059baa9a0000001409f627a0ffa9493e06f0002890001b61720000
  | 9 => 0x2a486c8032538af263264062a24a3d00012c0001fc8d60000001261ce11f8001eba791b58d280000584502003e8000000000000000001672c5a3381e20f8000000fd1269ac12c80000000000023700013fa9110fa5900006600000002f98f80025f0a8260aa61cf219219a9b8ad8000000000000000288001690271332010e89389209c80001790eaa9fa292b51e80408a00f41ca9c026e9ed1f123e0789c4057a921a6904007a85202818183a840cd8501c49fba1da3b28b9158980ca95d0a99da27429c9e2173a8a1018811c8a9da2e8a300009304926ba9427993a0b7156aa00c89cb0601178bf0fc00022cac68e02601eb1c609c9fb19ba9009d9fda0180016c95ba8684386317a0888bd04314a2b08000b48001ec9460a500000000000000a1180e706e8000001978d88000002308000918000000da9b900000026a9e712989f0000562989160fa81400026921006b110a310820ab93c13e9b427a8669d02c89581feabe96d9619e91e282e04a15907e0328208f5a180482299f715401915f9998c722d05a8ce8aa0978e2a9f0d48852ca9dfa511c71f30842928c603595da7b9121f384102c8002688002709d6ac787d8001081a8207a732ac80017e8000b19448eb8839049f78cf8bc9ea94017d009a610a18ff1aea1ca2aa5e100861932870abb90511a080180a6d1f4aba873121223147877a6ca45a5293d2b98e1ab497c99e19196ea7d108a0887404421f84898e21c2201060001ef2268b008d8858f2089979800064a66a2391423b8d1a8e2170001b223415c00001c81b98700000013f29503c8000c022423ca830c91ff0c48672b79450001a29d127821a9b505f10021a221045a489480281c28b11929e8a131ab92881b25717f03
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf71d8910014fe71d891000cfd71d8910014fc71d8910246ef21d8910246ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910236fa40d8910236ef20d8910236ed20d891001cff765891003eec625891022df7715891023dfb7058910004ff7558910034fe7558910034fc7558910004ff745891002cfe745891002cfc7458910004ff7358910024fe7358910024fc7358910234ff7258910006ef725891022cff7158910006f771589100dcff7058910006fb70589100defa4058910004ff7654910004fe7654910004fd7654910004fc76549100367e65549100067d6554910006ef625491001eec6254910004ff7650910004fe7650910004fd7650910004fc765091002ebe6450910006bd645091000dfa7050910004ff764c910004fe764c910004fd764c910004fc764c910026de634c910006dd634c910015f6714c91000df4764c510026f4764c51000cf4764c510006f7654c510006f5654c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510227d7534c510047d4534c510047d6434c510007d5434c510005f7724c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100fff0704c510016f7604c510017f3604c5100fff2404c5100ffd7304c5100ffd5304c5100fff2204c51000df4764851001ef4764851000cf47648510006f76448510006f56448510005f77348510005f57348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851001ee4624851003fe64248510007e54248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100dff240485100dfe720485100dff220485100dfe52048510015f8765011002ef87650110014f87650110006fb6550110006f9655011000dfb745011000fbb7450110007bb645011002efa645011002ef8645011004fb8645011021fbb545011004fb8545011009efa635011009ef8635011004fbb4350110007b94350110005fb7250110006fb6250110006f9625011004fbb4250110007b94250110007f37150110015fa7150110015f871501100a7f0715011000efb615011000ff361501100a7bb41501100a7b941501100a7f23150110007f131501100a7f22150110007f12150110015f8764811001ef87648110014f87648110005fb7448110005f97448110006fb6448110006f9644811000dfb724811000feb7248110007eb624811001efa624811001ef8624811003fe8624811003fea3248110007e93248110007f37148110015fa7148110015f8714811005ff0714811000efb614811000ff3614811005ff23148110007f1314811005feb214811005ff2214811005fe9214811003ff12148110007e12148110
  | 1 => 0x95102a67f51d95102a67d51d95102a6f631d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102967f50d95102967d50d9510296fa40d9510034ff76595100567c6559510005df7359510045dc735951028df7715951029dfb7059510294ff75595100067f7559510004ff745951002cfe745951002cfc7459510004ff7359510006df7359510004df7359510024fe7359510024fc7359510006dc7359510024dc7359510004ff725951001cfe725951001cfc72595100567f525951028cff7159510006f771595100bef6315951013cff7059510006fb705951013efa405951002cfe76d911004ebe64d9110034fe75d9110004fd75d9110034fc75d911011cfd74d9110024fe73d9110004fd73d9110024fc73d911001cfe72d9110004fd72d911001cfc72d911000cff71d9110014fe71d911000cfd71d9110014fc71d9110286bf41d9110286bd41d9110286f621d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110276bf40d9110276bd40d9110276fa20d911002cff765911004ebc6459110005ef725911003dec725911026df7715911027dfb7059110004ff7559110034fe7559110034fc7559110274ff7459110006bf7459110004ff7359110024fe7359110024fc7359110004ff7259110006ef7259110004ef725911001cfe725911001cfc7259110006ec725911001cec725911004ebf425911026cff7159110006f771591100a6f6215911011cff7059110006fb705911011efa2059110004ff7655110004fe7655110004fd7655110004fc7655110024fe76d8d10046de63d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d10006df53d8d10046dc53d8d10046de43d8d1001cfe72d8d10004fd72d8d1001cfc72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10266df31d8d10266dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10256df30d8d10256dd30d8d10024ff7658d10046dc6358d1024df77158d1025dfb7058d10004ff7558d10034fe7558d10034fc7558d10004ff7458d1002cfe7458d1002cfc7458d10254ff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d10046df3258d1024cff7158d10006f77158d100fcff7058d10006fb7058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100557c7550d10006df6350d10026dc6350d1001cfe76d891003eee62d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d891003eee52d8910006ef42d891003eec42d891000cf
  | 2 => 0x4ff7458d2002cfe7458d2002cfc7458d202d4ff7358d20006df7358d202ccff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d20066df3158d2015cff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200757c7550d20006df6350d20026dc6350d2000dec764c920026ec764c92000cec764c920006ef654c920006ed654c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c9202c7cf534c920067cc534c920067ce434c920007cd434c920005ef714c920067cf314c920007eb704c92000dee704c92000dec704c92015fe8704c92001eef604c92001feb604c92015fea404c92015fcf304c92015fcd304c92015fea104c920014fe76d852005ef661d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d852005ef651d8520006f741d852005ef441d852005ef621d85202bef521d852000cfe70d852001cfd70d852000cfc70d852022efa40d852022ef710d852005ef461585202b5fb7058520004ff7654520004fe7654520004fc76545200367e65545200067d6554520006f76154520016f46154520004ff7650520004fe7650520004fc765052002ebe6450520006bd645052000dfa7050520004ff764c520004fe764c520004fc764c520026de634c520006dd634c52001dee724c520007cd324c52000dec7648520016ec764852000cec7648520006ef6448520006ed6448520005ef7348520005ed734852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe46148520016e4614852005fe64148520007e54148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200dfea40485200dfe710485200dfea104852001df8765012002ef8765012001cf87650120006fb6550120006f9655012000dfb745012000fbb7450120007bb645012002efa645012002ef8645012006fb864501202afbb545012006fb8545012009efa635012009ef8635012006fbb4350120007b94350120007eb725012001dfa725012001df872501200afe8725012000efb625012000feb62501200afbb42501200afb942501200afea3250120007e93250120005fb7150120006fb615012006fbb4150120007b941501200afeb2150120007e92150120034fe76d95100567e65d951013cfd75d951002cfe74d9510004fd74d951002cfc74d9510024fe73d9510004fd73d9510024fc73d951001cfe72d9510004fd72d951001cfc72d951000cff71d9510014fe71d951000cfd71d9510014fc71d
  | 3 => 0xd734853007fe42148530025f87654130036f87654130024f8765413000dfb755413000f7b75541300077b6554130036fa6554130036f86554130097786554130006fb6454130006f9645413032f7a5454130097785454130007db7354130025fa7354130025f873541300cfd8735413000efb635413000fdb63541300cf7b53541300cf7953541300977b52541300077952541300cfdb3254130007d932541300977b51541300077951541300cfdb3154130007d93154130034fe76d95200767e65d952019cfd75d952002cfe74d9520004fd74d952002cfc74d9520024fe73d9520004fd73d9520024fc73d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203267f52d95203267d52d9520326ee32d9520014fe71d9520004fd71d9520014fc71d952001cff70d952001cfd70d95203167f50d95203167d50d9520316fa40d9520034ff76595200767c6559520005df7359520065dc735952030def725952031dfb7059520314ff75595200067f7559520004ff745952002cfe745952002cfc7459520004ff7359520006df7359520004df7359520024fe7359520024fc7359520006dc7359520024dc735952030cff7259520006ef72595200c6ee3259520004ff7159520014fe7159520014fc71595200767f515952019cff7059520006fb705952019efa405952002cfe76d912006ebe64d9120034fe75d9120004fd75d9120034fc75d912017cfd74d9120024fe73d9120004fd73d9120024fc73d912000cff72d912001cfe72d912000cfd72d912001cfc72d9120306bf42d9120306bd42d9120014fe71d9120004fd71d9120014fc71d9120306ef21d912001cff70d912001cfd70d91202f6bf40d91202f6bd40d91202f6fa10d912002cff765912006ebc64591202edef7259120005f7715912005df471591202fdfb7059120004ff7559120034fe7559120034fc75591202f4ff7459120006bf7459120004ff7359120024fe7359120024fc73591202ecff7259120006ef7259120004ff7159120006f77159120004f77159120014fe7159120014fc7159120006f47159120014f4715912006ebf41591200aeef215912017cff7059120006fb705912017efa1059120004ff7655120004fe7655120004fd7655120004fc7655120024fe76d8d20066de63d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d20006df53d8d20066dc53d8d20066de43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202e6df32d8d202e6dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d2001cff70d8d2001cfd70d8d202d6df30d8d202d6dd30d8d20024ff7658d20066dc6358d202cdef7258d202ddfb7058d20004ff7558d20034fe7558d20034fc7558d20
  | 4 => 0x91301bcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d913036ebf43d913036ebd43d913001cfe72d9130004fd72d913001cfc72d913036edf32d9130014fe71d9130004fd71d9130014fc71d913036edf31d9130024ff70d9130024fd70d913035efa50d913035ebf40d913035ebd40d913036efb30d913035ede30d913035edc30d913035ef830d913002cff76591300057f75591300957c755913008ebc6459130355df7359130365fb7059130004ff75591300067f75591300047f7559130034fe7559130034fc75591300067c75591300347c755913035cff7459130006bf7459130354ff7359130006df7359130004ff725913001cfe725913001cfc725913009edf3259130004ff7159130014fe7159130014fc715913009edf31591301bcff7059130006fb70591301befa505913009efb30591301bede30591301bedc30591301bef83059130004ff7655130004fe7655130004fd7655130004fc765513001cfe76d8930086ee62d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930086ee32d893034eed32d8930014fe71d8930004fd71d8930014fc71d893034edf31d8930024fd70d89302ceef20d8930086ec6258930345fb7058930004ff7654930004fe7654930004fc76549300067f65549300367c6554930004ff7650930004fe7650930004fc765093000ddc764c93001edc764c93000cdc764c930176de654c930176dc654c930006df644c930006dd644c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c930087ce524c930007cd524c930005df714c930007db704c93000dde704c93000ddc704c93015fd8704c930026df604c930027db604c93015fda504c93015fcf204c930014fe76d853007ef661d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d853033edf32d8530006dd32d853007ef631d853033ef531d8530024fd70d853024ef710d853007ef46158530335fb7058530004ff7654530004fe7654530004fc76545300067f65545300367c6554530004ff7650530004fe7650530004fc765053000ddc764c530016dc764c53000cdc764c530116de654c530116dc654c530006df644c530006dd644c530005df724c530006df624c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6514c530007d5514c530007db704c53000dde704c53000ddc704c5300ffd8704c530026df604c530027db604c5300ffda504c5300ffd7104c530004ff7648530004fe7648530004fc7648530025de7348530005d
  | 5 => 0xcfd74d8540014fc74d8540024fe73d8540004fd73d8540024fc73d854001cfe72d8540004fd72d854001cfc72d85403a6bf42d8540006bd42d85400a6f641d85403a6f541d8540006f721d85400a6f421d854002cfd70d854026efa20d854026ef710d8540005ef72585400adec72585400a6f4615854039dfb7058540004ff7654540004fe7654540004fc76545400367e65545400067d6554540005bf745454002dbc74545400b73f545454000dfa705454000dbc7650540016bc765054000cbc76505400b5be75505400b5bc7550540005bf7350540005bf7250540006bf625054002dbf715054002fb77150540007b76150540016be6150540016bc61505400a7b46150540016b461505400a7b65150540007b551505400a7b62150540007bb705054000dbe705054000dbc705054011fb8705054002ebf605054002fbb605054011fba5050540397bb305054011fb8305054011fba205054011fba1050540004ff764c540004fe764c540004fc764c54002dbe744c540005bd744c540026de634c5400079d434c540005fb704c54000df8704c54009fdb304c540004ff7648540004fe7648540004fc764854002dbe7448540005bd744854001eee6248540007ad4248540016f66148540007b541485400a7e4214854000dfa704854002df87654140036f8765414002cf8765414000dfb755414000f7b75541400077b6554140036fa6554140036f865541400b7786554140007bb745414002dfa745414002df874541400d7b8745414000efb645414000fbb64541400b7bb54541400d77a54541400d77854541400d7b854541400d7385454140007db735414009dfa735414009df87354140007d8735414009dd87354140006fb63541400b77b53541400077953541400d7bb4354140007b94354140005fb72541400b77b52541400077952541400d7bb4254140007b94254140005fb71541400b77b51541400077951541400d7bb4154140007b94154140034fe76d95300967e65d95301dcfd75d953002cfe74d9530004fd74d953002cfc74d95300067e54d95300967c54d953000cff73d9530024fe73d953000cfd73d9530024fc73d953038e7f53d953038e7d53d953001cfe72d9530004fd72d953001cfc72d95300967f52d9530014fe71d9530004fd71d9530014fc71d95300967f51d9530024ff70d9530024fd70d953037e7f50d953037e7d50d9530034ff76595300967c6559530375df7359530385fb705953037cff75595300067f7559530004ff745953002cfe745953002cfc7459530374ff7359530006df7359530374df7359530004ff725953001cfe725953001cfc7259530004ff7159530014fe7159530014fc71595301dcff7059530006fb705953002cfe76d913008ebe64d9130034fe75d9130004fd75d9130034fc75d
  | 6 => 0xf7359540006df7359540004df7359540024fe7359540024fc7359540006dc7359540024dc73595400d6bf4359540004ff725954001cfe725954001cfc72595400b67f5259540004ff7159540014fe7159540014fc71595400b67f51595401fcff7059540006fb7059540024fe76d8d4009ede63d8d4000dfa70d8d4002df970d8d4009fdb30d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d40006df53d8d4009edc53d8d4009ede43d8d403cedd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40014fe71d8d40004fd71d8d40014fc71d8d4002cfd70d8d4009ef970d8d4002cf970d8d40356fa50d8d40356df30d8d4009efb30d8d40356f830d8d400057f7558d400b57c7558d4009edc6358d403c5fb7058d401bfd83058d40004ff7654d40004fe7654d40004fc7654d40005bf7454d4002dbc7454d40005fb7054d4000df87054d4000dbc7650d40026bc7650d4000cbc7650d400073f7550d400b5be7550d400b5bc7550d400073c7550d400b53c7550d40006bf6550d40006bd6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d4009f9c6350d4009f9e5350d400079d5350d40005bf7250d4009f9f3250d40005bf7150d4009f9f3150d40007bb7050d4000dbe7050d4000dbc7050d401bfb87050d4000db87050d4002ebf6050d4002fbb6050d401bfba5050d4009fbb3050d401bf9e3050d401bf9c3050d401bfb83050d401bf983050d401bfba2050d401bfba1050d4001cfe76d89400aeee62d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89400aeee42d89403beed42d8940014fe71d8940004fd71d8940014fc71d89403bebf41d8940006ee21d89400aeec21d894002cfd70d89402eeef20d89402eefa10d89400aeec6258940005f771589400a5f471589403b5fb7058940004ff7654940004fe7654940004fc76549400367e65549400067d6554940005bf745494002dbc74549400b73f545494000dfa705494000dbc765094001ebc765094000cbc76509400b5be75509400b5bc7550940005bf735094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400afac625094001eac62509400afae5250940007ad5250940005bf71509400afaf2150940007bb705094000dbe705094000dbc705094017fb8705094002ebf605094002fbb605094017fba50509403afbb305094017fb8305094017fba205094017fba1050940004ff764c940004fe764c940004fc764c94002dbe744c940005bd744c940026de634c9400079d434c940005fb704c94000df8704c94009fdb304c940014fe76d85400a6f661d8540034fe75d8540004fd75d8540034fc75d8540
  | 7 => 0x49501ae5c63549500357f72549500376f72549500076f625495001e7e625495001e7c62549500c76c62549500c76e42549500c76e32549500057f71549500077b705495000d7e705495000d7c705495019f7870549500367f60549500377b605495019f7a405495019f7a3054950004ff7650950004fe7650950004fc76509500057f75509500357c7550950006df635095018edc63509500076d5250950004ff764c950004fe764c950004fc764c9500357e754c9500057d754c950006df634c950026dc634c9501775f534c95001eee624c9500076d524c950014fe76d8550006df63d8550006dc63d85500bef661d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d8550024fe73d8550004fd73d8550024fc73d855001cfe72d8550004fd72d855001cfc72d85503fe7f52d85500067d52d85500bef651d85503fef551d8550034fd70d855028efa40d855028ef710d8550005df73585500cddc7358550006df6358550006dc63585500bef461585503f5fb705855000d7c76545500167c765455000c7c76545500d57e74545500d57c74545500067f64545500057f73545500075f635455014e7e635455014e7c63545500075c635455014e5c63545500057f72545500067f62545500357f71545500377771545500077761545500167e61545500167c61545500bf7461545500bf7641545500bf7631545500077b705455000d7e705455000d7c705455013f7870545500367f60545500377b605455013f7a405455013f7a3054550004ff7650550004fe7650550004fc76505500057f75505500357c7550550006df635055012edc6350550007755150550004ff764c550004fe764c550004fc764c5500357e754c5500057d754c550006df634c550026dc634c5501175f534c550016f6614c55000775514c550004ff7648550004fe7648550004fc76485500357e75485500057d7548550006df63485500e6dc63485500bfe42148550005fb704855000df87048550034fe76d95400b67e65d954002dbe74d954000dbd74d95400b73f54d95401fcfd75d954000cff74d954002cfe74d954000cfd74d95403debd74d954000cbd74d954002cfc74d95403ee7f54d95400b6bf54d95400b63f54d95403ee7d54d95403eebc54d9540024fe73d9540004fd73d9540024fc73d95400067e53d95400b67c53d95403eebf43d954001cfe72d9540004fd72d954001cfc72d9540014fe71d9540004fd71d9540014fc71d954002cff70d954002cfd70d95403de7f50d95403de7d50d9540034ff76595400b67c65595403d5bf74595400d73c5459540005df735954009ddc73595403e5fb70595403dcff75595400067f75595403d4ff7459540006bf74595400b6bf54595400d67e54595400d67c54595400d6bc5459540004f
  | 8 => 0x6dc61d8d5042f5f51d8d5042fdb70d8d50377d870d8d5042fdb50d8d503775e50d8d503775c50d8d50377d850d8d50377da40d8d50376df75d8d500cede75d8d50376dd75d8d50376dc75d8d50006df74d8d50006de74d8d50006dd74d8d50006dc74d8d5042edf54d8d5042ede54d8d5042edd54d8d5042edc54d8d50006df72d8d50006de72d8d50006dd72d8d50006dc72d8d5042edf52d8d5042ede52d8d5042edd52d8d5042edc52d8d50006df42d8d50006de42d8d50006dc42d8d50006df71d8d50006de71d8d50006dd71d8d50006dc71d8d5042edf51d8d5042ede51d8d5042edd51d8d5042edc51d8d50006df41d8d50006de41d8d50006dc41d8d50006df21d8d50006de21d8d50006dc21d8d50376df70d8d50376de70d8d50376dd70d8d50376dc70d8d50376df50d8d50376de50d8d50376dc50d8d50376df40d8d50376de40d8d50376dd40d8d50376dc40d8d50376df20d8d50376de20d8d50376dd20d8d50376dc20d8d50376df10d8d50376de10d8d50376dd10d8d50376dc10d8d500cedc6358d50425fb7058d50375de7618d500cede7618d500cf5e7518d504175d7518d50416df6518d500cf9e7418d500cf9d7418d50006df6418d50006de6418d50006dd6418d50006dc6418d500075e5418d5041f5c5418d500cfce7218d500cfcd7218d50006de6218d50006dc6218d5041f5f5218d500cfd67118d500cfd57118d50006de6118d50006dc6118d5041f5f5118d50417da7018d500cfd97018d50416df6018d5041fdb5018d504175e5018d504175c5018d50417d85018d50417da4018d5000d7c7654d500267c7654d5000c7c7654d500d57e7454d500d57c7454d500357f7354d500375f7354d500075f6354d500267e6354d500267c6354d500cf5c6354d500265c6354d500cf5e4354d500057f7254d500057f7154d500077b7054d5000d7e7054d5000d7c7054d501df787054d500367f6054d500377b6054d501df7a4054d501df7a3054d50004ff7650d50004fe7650d50004fc7650d500057f7550d500357c7550d5002ebe6450d500d73e5450d50006df6350d50026dc6350d500075d5350d5000dfa7050d501bfda3050d5001cfe76d8950006df63d8950006dc63d89500c6ee62d895000cfd75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d8950024fe73d8950004fd73d8950024fc73d89500c6ee52d895040eed52d8950014fe71d8950004fd71d8950014fc71d895040e7f51d8950034fd70d895030efa40d895030eef20d8950005df73589500cddc7358950006df6358950006dc63589500c6ec6258950405fb705895000d7c765495001e7c765495000c7c76549500d57e74549500d57c74549500067f64549500057f73549500075f63549501ae7e63549501ae7c63549500075c635
  | 9 => 0xf7058d21006fb7058d21004fb7058d2100cfe7058d2100cfc7058d21006f87058d2100cf87058d210e6df3058d21106ef2058d21166f71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d211e7e42154d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210f57c7550d21006bf6450d2102ebc6450d21026de6350d21006dd6350d211c7e42150d21015ec765092102eec7650921014ec7650921006ef6550921006ed655092101def745092101faf7450921007af645092102eee645092102eec64509210efac6450921007e77150921015ee7150921015ec7150921187e47150921015e4715092101eef615092101fe76150921187af4150921187e64150921187ad4150921005ef70509210efaf4050921187e7105092101df4765052102ef4765052101cf47650521006f76550521006f56550521015f77450521017b77450521007b7645052102ef6645052102ef464505210efb46450521007e7725052101df6725052101df47250521127e4725052101de47250521016f76250521017e76250521127b74250521127e64250521127b542505210efe54250521007a54250521005f770505210efb74050521127e7205052100cfe76d812123fe421d81210defa60d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d812101cfd71d812100cfc71d81210defa50d8121006fb30d81210def830d81210defa20d81210defa10d812105fe421581210def8605812102cfe76d91500357e75d915000d7d75d91500d6be64d91500d73e54d915000cfd75d91503d67d75d915000c7d75d915002cfc75d91500d67e54d91500d6be54d91500d63e54d915043ebd54d91500d67c54d9150024fe73d9150004fd73d9150024fc73d915001cfe72d9150004fd72d915001cfc72d915043e7f52d9150014fe71d9150004fd71d9150014fc71d915043e7f51d9150034fd70d91503d6bf40d91500d6bc64591500d73c5459150005df73591500cddc7359150435fb7059150024fe76d8d500cede63d8d5000cfd75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500cede53d8d5042edd53d8d50006df43d8d500cede43d8d500cedc43d8d5001cfe72d8d50004fd72d8d5001cfc72d8d500cedf32d8d50006de32d8d500cedc32d8d50014fe71d8d50004fd71d8d50014fc71d8d500cedf31d8d50006de31d8d500cedc31d8d50034fd70d8d50376df30d8d50415de76d8d50024de76d8d503775f75d8d503775c75d8d50006df64d8d50006de64d8d50006dd64d8d50006dc64d8d500075e54d8d5042f5c54d8d50006de62d8d50006dc62d8d5042f5f52d8d50006de61d8d50
  | 10 => 0x81310fefa40d81310fefa30d8131006fb20d81310fef820d81310fefa10d81310fef86058131034fe76d95210f67e65d95210e5de73d9521005dd73d952148fe421d95211a4fd75d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521006de73d9521024de73d9521004fd73d9521006dd73d9521004dd73d9521024fc73d9521014ff72d9521014fd72d952149e7f52d952149e7d52d952149eee42d952101cff71d952101cfd71d952148e7f51d952148e7d51d952148ef641d952100cfe70d9521004fd70d952100cfc70d9521034ff76595210f67c6559521005bf74595210edbc7459521485ef7259521495f771595211a7e4215952148cff75595210067f7559521004ff7459521006bf7459521004bf745952102cfe745952102cfc7459521006bc745952102cbc74595210f67f5459521004ff7359521024fe7359521024fc73595210067e53595210f67c5359521484ff7259521006ef7259521146ee42595211a4ff7159521006f771595211a6f64159521004ff705952100cfe705952100cfc70595210f67f505952102cfe76d91210eebe64d912146fe421d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121006bf54d91210eebc54d9121024fe73d9121004fd73d9121024fc73d91210eebf43d9121014ff72d9121014fd72d912147ebf42d912147ebd42d912101cff71d912101cfd71d912146ebf41d912146ebd41d912100cfe70d9121004fd70d912100cfc70d912102cff76591210eebc6459121465ef7259121475f77159121187e42159121004ff7559121034fe7559121034fc755912146cff7459121006bf7459121004ff7359121024fe7359121024fc7359121464ff7259121006ef7259121184ff7159121006f77159121004ff705912100cfe705912100cfc70591210eebf4059121004ff7655121004fe7655121004fd7655121004fc76551210367e65551210067d6555121207e42155121024fe76d8d210f57e75d8d210057d75d8d210e6de63d8d2144fe421d8d21034fe75d8d210067e75d8d210347e75d8d21004fd75d8d210067d75d8d210047d75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21164fd73d8d21014ff72d8d21014fd72d8d2145edf32d8d2145edd32d8d2101cff71d8d2101cfd71d8d2144edf31d8d2144edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d2145eef20d8d2144ef710d8d21024ff7658d210e6dc6358d21445ef7258d21455f77158d21167e42158d21005fb7058d210ddf87058d21004ff7558d21034fe7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d2144cff7358d21006df7358d21006df5358d210e6dc5358d210e6de4358d21444ff7258d21006ef7258d21164ff7158d21006f77158d21004f
  | 11 => 0x347c75591314bcff7459131006bf74591314b4ff7359131006df7359131004ff725913101cfe725913101cfc725913112edf32591311c4ff7159131006f771591311c6f65159131004ff705913100cfe705913100cfc705913110ebf4059131004ff7655131004fe7655131004fd7655131004fc7655131005df7355131025dc7355131015dc7650d3102edc7650d31014dc7650d310075f7550d31115de7550d31115dc7550d310075c7550d311155c7550d31006df6550d31006dd6550d31025df7450d310279f7450d310079f6450d3102ede6450d3102edc6450d3110f9c6450d3110f9e5450d310079d5450d31005df7250d31007d77150d31015de7150d31015dc7150d311c7d47150d31026df6150d31027d76150d311c7d65150d31005df7050d311bede6050d311bedc6050d3110f9f4050d311c7d71050d3101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d8931006df53d89314aedc53d89314aede43d8931006dd43d8931106ee32d89314aeed32d8931024fd71d8931446ef21d893100cfe70d8931004fd70d893100cfc70d89314aedf30d8931446f710d8931106ec62589314a5f77158931005fb70589310fdf87058931004ff7654931004fe7654931004fc76549310067f65549310367c6554931005df7354931025dc73549311af5c5354931004ff7650931004fe7650931004fc7650931025de7350931005f77150931015f47150931015dc764c93101edc764c931014dc764c931115de754c931115dc754c931176de654c931176dc654c931005df744c931005dd744c931006df644c931006dd644c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c931107cc624c931107ce524c931007cd524c931007d7714c931015de714c931015dc714c931167d4714c931026df614c931027d7614c931167d6514c931005df704c931107cf204c931167d7104c931025f47654531036f47654531024f47654531015f77554531017777554531007776554531036f66554531036f46554531117746554531006f76454531006f56454531117775454531007755454531007d77354531025f67354531025f4735453114fd47354531016f76354531017d76354531117d7535453114f76535453114f74535453114fd4535453114f54535453114fd64354531007d5435453111777525453100775525453114fd73254531007d53254531005f7705453111777505453114fd7305453100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d8131336df32d8131006dd32d8131024fd71d
  | 12 => 0xc76549410367e65549410067d6554941015f67154941015bc765094101ebc7650941014bc765094102dbf725094102faf7250941007af625094101ebe625094101ebc6250941127ac6250941127ae5250941007ad5250941007b77150941015be7150941015bc7150941187b4715094102ebf615094102fb76150941187b65150941187af2150941187b62150941005bf7050941004ff764c941004fe764c941004fc764c941026de634c941006ef624c94101eec624c94102df47654541036f4765454102cf47654541015f77554541017777554541007776554541036f66554541036f46554541137746554541007b7745454102df6745454102df47454541157b47454541016f76454541017b76454541157775454541157755454541006f763545414f7765354541137745354541005f77254541137775254541007755254541157b74254541007b54254541137775054541157b7405454100cfe76d814111efa60d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d814101cfe72d8141004fd72d814101cfc72d814139ebf42d8141006bd42d814102cfd71d814127ef621d814111efa40d814111efa10d8141005ef7258141125ec725814111ef86058141034fe76d95311167e65d9531025de73d9531015dd73d95311175f53d95311e4fd75d953102cfe74d9531004fd74d953102cfc74d95310067e54d95311167c54d9531014ff73d9531014fd73d95314dedd73d9531014dd73d95314ee7f53d9531116df53d95314ee7d53d95314eedc53d95314eede43d953101cfe72d9531004fd72d953101cfc72d95311167f52d9531024ff71d9531024fd71d95314de7f51d95314de7d51d953100cfe70d9531004fd70d953100cfc70d9531034ff76595311167c65595314d5df735953114f5c53595314e5f771595314dcff75595310067f7559531004ff745953102cfe745953102cfc74595314d4ff7359531006df7359531116df535953114e7e535953114e7c535953114edc535953114ede4359531004ff725953101cfe725953101cfc72595311e4ff7159531006f77159531004ff705953100cfe705953100cfc70595311167f505953102cfe76d913110ebe64d9131034fe75d9131004fd75d9131034fc75d91311c4fd74d9131014ff73d9131014fd73d91314cebf43d91314cebd43d913101cfe72d9131004fd72d913101cfc72d91314cedf32d9131024ff71d9131024fd71d91314bef651d91314bebf41d91314bebd41d913100cfe70d9131004fd70d913100cfc70d913102cff76591310057f75591311157c755913110ebc64591314b5df73591314c5f77159131004ff75591310067f75591310047f7559131034fe7559131034fc75591310067c7559131
  | 13 => 0x89515467c53d8951146ee52d8951546ed52d8951034fd71d8951486f641d8951486ef21d895100cfe70d8951004fd70d895100cfc70d89515467f50d8951005bf7458951155bc7458951146ec625895153df771589510157c765495101e7c76549510147c76549510057f74549510067f645495114d7e735495114d7c73549511ae7e63549511ae7c63549510357f72549510376f72549510076f625495101e7e625495101e7c62549511476c62549511476e42549511476e32549510077771549510157e71549510157c71549511a77471549510367f61549510377761549511a77641549511a77631549510057f7054951004ff7650951004fe7650951004fc76509510357e75509510057d755095101eee62509510076d5250951004ff764c951004fe764c951004fc764c9510057f754c9510357c754c951006df634c951026dc634c95114f5c534c9510076d524c95100cfe76d815113efa60d8151014fd75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d8151024fe73d8151004fd73d8151024fc73d815101cfe72d8151004fd72d815101cfc72d81513f67f52d81510067d52d8151034fd71d815129ef631d815113efa50d815113efa10d8151005df735815114ddc735815113ef86058151034fe76d95411367e65d9541204fd75d9541014ff74d9541014fd74d95415367f54d95415367d54d9541024fe73d9541004fd73d9541024fc73d95410067e53d95411367c53d954101cfe72d9541004fd72d954101cfc72d954102cff71d954102cfd71d95415267f51d95415267d51d954100cfe70d9541004fd70d954100cfc70d95411367f50d9541034ff76595411367c655954151dbf745954152df77159541524ff75595410067f755954151cff7459541006bf7459541004ff7359541024fe7359541024fc7359541004ff725954101cfe725954101cfc72595411367f5259541204ff7159541006f77159541004ff705954100cfe705954100cfc7059541024fe76d8d4112ede63d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4112ede43d8d41516dd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4102cfd71d8d414b6f651d8d414b6df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41516bf40d8d410057f7558d411357c7558d4112edc6358d4150df77158d41004ff7654d41004fe7654d41004fc7654d4101cfe76d8941126ee62d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d8941126ee42d8941506ed42d8941126ee32d894102cfd71d8941466ef21d894100cfe70d8941004fd70d894100cfc70d8941506bf40d8941006ee20d8941126ec20d8941126ec62589414fdf77158941004ff7654941004fe7654941004f
  | 14 => 0x1cfcf2050d32025ec7654932036ec7654932024ec765493201def755493201f6f75549320076f6554932036ee6554932036ec65549321776c6554932006ef6454932006ed64549321776f54549320076d5454932007cf7354932025ee7354932025ec73549321afcc735493201eef635493201fcf6354932177cf53549321af6e53549321af6c53549321afcc53549321af4c53549321afce4354932007cd43549321776f51549321afcf3154932005ef70549321776f50549321afcf3054932014fe76d8532166f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532006df53d85324a6dc53d85324a6de43d8532006dd43d8532024fd72d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d85324a6df30d8532456ef20d8532166f46158532005fb705853215df8705853200cfe76d813215efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d8132014fe71d8132004fd71d8132014fc71d8132346df31d813215efa40d813215efa30d813215efa20d8132006fb10d813215ef810d813215ef8605813202cfe76d9151156be64d9151014fd75d9151156be54d9151566bd54d9151024fe73d9151004fd73d9151024fc73d915101cfe72d9151004fd72d915101cfc72d91515667f52d9151006be42d9151156bc42d9151034fd71d915151ebf41d915100cfe70d9151004fd70d915100cfc70d9151156bf40d9151156bc645915155df771591510157c765515102e7c76551510147c76551510357f74551510373f74551510073f645515102e7e645515102e7c64551511573c645515114d7e735515114d7c73551511573f43551510057f72551510077771551510157e71551510157c71551512077471551510367f61551510377761551512077641551512077631551510057f7055151024fe76d8d510357e75d8d510157d75d8d5114ede63d8d5114f5e53d8d51014fd75d8d514d67d75d8d510147d75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5114e7e53d8d5114ede53d8d51556dd53d8d5114e7c53d8d5101cfe72d8d51004fd72d8d5101cfc72d8d5114edf32d8d51034fd71d8d514d6df31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d515567f50d8d51006de30d8d5114edc30d8d5114edc6358d5114f5c5358d5154df77158d51004ff7650d51004fe7650d51004fc7650d510057f7550d510357c7550d510073d5450d51026de6350d5114f5e5350d51015f67150d5101cfe76d8951146ee62d8951014fd75d895102cfe74d8951004fd74d895102cfc74d89515467f54d89510067d54d8951024fe73d8951004fd73d8951024fc73d89510067e53d
  | 15 => 0x621d854200cfe70d8542004fd70d854200cfc70d85424febf40d8542006f610d8542186f410d8542186f4615854200cfe76d814217efa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d814202cfd72d8142014fe71d8142004fd71d8142014fc71d81423b6bf41d81422feef21d814217efa40d814217efa20d8142005f77158142185f4715814217ef86058142034fe76d95321767e65d9532025de73d953201ddd73d95321775f53d95321ecfd75d953202cfe74d9532004fd74d953202cfc74d95320067e54d95321767c54d953201cff73d953201cfd73d9532596dd73d953201cdd73d95325a67f53d9532176df53d95325a67d53d95325a6dc53d95325a6de43d9532024ff72d9532024fd72d95325967f52d95325967d52d9532014fe71d9532004fd71d9532014fc71d95321767f51d953200cfe70d9532004fd70d953200cfc70d9532034ff76595321767c655953258ddf73595321af5c535953259def7259532594ff75595320067f7559532004ff745953202cfe745953202cfc745953258cff7359532006df7359532176df53595321ae7e53595321ae7c53595321aedc53595321aede43595321ecff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff705953200cfe705953200cfc70595321767f505953202cfe76d913216ebe64d9132034fe75d9132004fd75d9132034fc75d91321ccfd74d913201cff73d913201cfd73d9132586bf43d9132586bd43d9132024ff72d9132024fd72d9132576ee52d9132576bf42d9132576bd42d9132014fe71d9132004fd71d9132014fc71d9132586df31d913200cfe70d9132004fd70d913200cfc70d913202cff76591320057f75591321757c755913216ebc645913256ddf735913257def7259132004ff75591320067f75591320047f7559132034fe7559132034fc75591320067c75591320347c7559132574ff7459132006bf745913256cff7359132006df73591321ccff7259132006ef72591321ceee5259132004ff7159132014fe7159132014fc715913218edf3159132004ff705913200cfe705913200cfc705913216ebf4059132004ff7655132004fe7655132004fd7655132004fc7655132005df7355132025dc735513201ddc7650d3202edc7650d3201cdc7650d320075f7550d32175de7550d32175dc7550d320075c7550d321755c7550d32006df6550d32006dd6550d32025df7450d320279f7450d320079f6450d3202ede6450d3202edc6450d3216f9c6450d3216f9e5450d320079d5450d32007cf7250d3201dde7250d3201ddc7250d321cfcc7250d32026df6250d32027cf6250d321cfce5250d32005df7150d32005df7050d321bede6050d321bedc6050d3216f9f4050d32
  | 16 => 0x8d52004fd71d8d52014fc71d8d521aedf31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d525ee7f50d8d52006de30d8d521aedc30d8d521aedc6358d521af5c5358d525e5ef7258d52004ff7650d52004fe7650d52004fc7650d520057f7550d520357c7550d520073d5450d52026de6350d521af5e5350d5201dee7250d52014fe76d85521a6f661d855201cfd75d855202cfe74d8552004fd74d855202cfc74d855253e7f54d85520067d54d8552024fe73d8552004fd73d8552024fc73d85520067e53d855253e7c53d8552034fd72d8552496ee42d85521a6f651d85521a6f621d855200cfe70d8552004fd70d855200cfc70d855253e7f50d8552005bf74585521b5bc74585521a6f4615855200cfe76d815219efa60d815201cfd75d815202cfe74d8152004fd74d815202cfc74d8152024fe73d8152004fd73d8152024fc73d8152034fd72d815231eee32d8152014fe71d8152004fd71d8152014fc71d81524067f51d815219efa50d815219efa20d8152005df73581521addc735815219ef86058152034fe76d95421967e65d954220cfd75d954201cff74d954201cfd74d95425de7f54d95425de7d54d9542024fe73d9542004fd73d9542024fc73d95420067e53d95421967c53d954202cff72d954202cfd72d95425ce7f52d95425ce7d52d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542004fd70d954200cfc70d95421967f50d9542034ff76595421967c65595425c5bf74595425d5ef72595425ccff75595420067f75595425c4ff7459542006bf7459542004ff7359542024fe7359542024fc735954220cff7259542006ef7259542004ff7159542014fe7159542014fc71595421967f5159542004ff705954200cfe705954200cfc7059542024fe76d8d4218ede63d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d4218ede43d8d425bedd43d8d4202cfd72d8d4256eee52d8d4256edf32d8d42014fe71d8d42004fd71d8d42014fc71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d425bebf40d8d420057f7558d421957c7558d4218edc6358d425b5ef7258d42004ff7654d42004fe7654d42004fc7654d4202dec7654942036ec765494202cec765494201def755494201f6f75549420076f6554942036ee6554942036ec65549421976c6554942007af745494202dee745494202dec74549421b7ac745494201eef645494201faf64549421b76f54549421b76d5454942006ef63549425af6e53549421976c5354942005ef71549421976f51549421b7af41549421976f50549421b7af4054942014fe76d8542186f661d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d8542186f641d8542186f631d8542186f
  | 17 => 0x2179f32551431d73f51551432179f3155143005bf70551436079e30551432179c305514302ddc7654d43036dc7654d4302cdc7654d43025df7554d430275f7554d430075f6554d43036de6554d43036dc6554d431d75c6554d430079f7454d4302dde7454d4302ddc7454d431f79c7454d43026df6454d430279f6454d431f79e5454d431d79d5454d43005df7254d43005df7154d431bdde7054d431bddc7054d431d75f5054d431f79f4054d4301cfe76d89430067f65d89430067c65d89431ceee62d8943034fe75d8943004fd75d8943034fc75d8943024fd74d894302cfd73d89431ceee42d89431ceee32d8943014fe71d8943004fd71d8943014fc71d894357edf31d894300cfe70d8943004fd70d894300cfc70d89435b6bf40d89430057f75589431d57c75589430067f65589430067c65589431ceec6258943014fe76d85430067f65d85430067c65d85431c6f661d8543034fe75d8543004fd75d8543034fc75d8543024fd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d85434c6df32d85431c6f641d85431c6f631d854300cfe70d8543004fd70d854300cfc70d854350ebf40d85430057f75585431d57c75585430067f65585430067c65585431c6f4615854300cfe76d81430067f65d81430067c65d8143025de73d814302ddd73d81431befa60d81431bfda30d8143034fe75d8143004fd75d8143034fc75d8143024fd74d814302cfd73d81431bedd73d814302cdd73d814301cfe72d8143004fd72d814301cfc72d8143366df32d8143014fe71d8143004fd71d8143014fc71d8143366df31d81431befa40d81431bede30d81431befa30d81431bedc30d81430057f75581431d57c75581430067f65581430067c65581431bef860581431bfd8305814302cfe76d91521b6be64d915201cfd75d91521b6be54d91525febd54d9152024fe73d9152004fd73d9152024fc73d9152034fd72d91525c6bf42d9152014fe71d9152004fd71d9152014fc71d91525fe7f51d9152006be41d91521b6bc41d915200cfe70d9152004fd70d915200cfc70d91521b6bf40d91521b6bc64591525f5ef725915201d7c765515202e7c765515201c7c76551520357f74551520373f74551520073f645515202e7e645515202e7c64551521b73c64551521ad7e73551521ad7c73551521b73f43551520076f725515201d7e725515201d7c725515220f6c72551520367f62551520376f625515220f6e425515220f6e32551520057f71551520057f7055152024fe76d8d520357e75d8d5201d7d75d8d521aede63d8d521af5e53d8d5201cfd75d8d5258e7d75d8d5201c7d75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521ae7e53d8d521aede53d8d525eedd53d8d521ae7c53d8d52034fd72d8d5258edf32d8d52014fe71d
  | 18 => 0xe65d9543214fd75d9543024ff74d9543024fd74d95436367f54d95436367d54d954302cff73d954302cfd73d954361e7f53d954361e7d53d954301cfe72d9543004fd72d954301cfc72d95431d67f52d95430067e52d95431d67c52d9543014fe71d9543004fd71d9543014fc71d95431d67f51d95430067e51d95431d67c51d954300cfe70d9543004fd70d954300cfc70d95431d67f50d95430067e50d95431d67c50d954360d7e76d95430347e76d954361f3f74d954361f3c74d95436375f73d954361f5c73d95436375f43d954361f3e43d954361f3c43d954361f5c43d95430067e62d95430067c62d954361f5f32d95430067e61d95430067c61d954361f5f31d95430067e60d95430067c60d95436373f40d95430075e30d954361f5c30d954361e7f74d95436367e74d954361e7d74d954361e7c74d954361e7f73d954361e7e73d954361e7d73d954361e7c73d954361e7f43d954361e7e43d954361e7c43d95430067f72d95430067e72d95430067d72d95430067c72d95436367f42d95436367e42d95436367d42d95436367c42d954361e7f32d954361e7e32d954361e7d32d954361e7c32d95430067f71d95430067e71d95430067d71d95430067c71d95436367f41d95436367e41d95436367d41d95436367c41d954361e7f31d954361e7e31d954361e7d31d954361e7c31d95430067f21d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95436367f40d95436367e40d95436367d40d95436367c40d954361e7f30d954361e7e30d954361e7d30d954361e7c30d95430067f20d95430067e20d95430067c20d95430067f10d95430067e10d95430067c10d9543034ff76595431d67c6559543625bf745954362ddf735954361cff75595430067f7559543624ff7459543006bf7459543214ff7359543006df7359543004ff725954301cfe725954301cfc7259543004ff7159543014fe7159543014fc7159543004ff705954300cfe705954300cfc705954361d7e76195431d67e761954361c7e76195436173e741954360f3d741954360e7f641954360f5e73195436175d731954360e7f63195436175f431954360f3e431954360f3c431954360f5c43195431d76e72195431d76d72195430067e62195430067c621954360f5f32195431d77671195431d77571195430067e61195430067c611954360f5f31195431d77a70195431d77970195430067e60195430067c60195436173f40195430075e301954360f5c3019543025bc7655143036bc7655143024bc765514302dbf755514302f3f75551430073f6555143036be6555143036bc65551431d73c65551430079f7355143025be7355143025bc73551432179c735514302ebf635514302f9f63551432179e53551431d73f5255143
  | 19 => 0xc01600000e0000000002000008800200800a801401e000003000c00800000c800400000b0008008020000001004000a0000000030018002003000c006002024fe76d8d54216de63d8d5402cfd75d8d54034fd74d8d54216de53d8d54216de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54216df32d8d54014fe71d8d54004fd71d8d54014fc71d8d54216df31d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54006de30d8d54216dc30d8d54216dc6358d5401cfe76d895420eee62d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d895420eee52d895420eee42d8954014fe71d8954004fd71d8954014fc71d89545f67f51d895400cfe70d8954004fd70d895400cfc70d895420eec6258954014fe76d8554206f661d855402cfd75d8554034fd74d8554024fe73d8554004fd73d8554024fc73d855401cfe72d8554004fd72d855401cfc72d855455e7f52d8554206f651d8554206f641d855400cfe70d8554004fd70d855400cfc70d8554206f4615855400cfe76d81541fefa60d815402cfd75d8154034fd74d8154436bf54d81543e67e54d81543e67c54d81543e6bc54d8154024fe73d8154004fd73d8154024fc73d81543e6bf43d815401cfe72d8154004fd72d815401cfc72d81544367f52d8154014fe71d8154004fd71d8154014fc71d81544367f51d81541fefa50d81541fefa40d8154005df7358154215dc73581541fef8605815402cfe76d91531f6be64d9153024fd75d91531f6be54d9153646bd54d9153034fd73d9153626bf43d915301cfe72d9153004fd72d915301cfc72d9153014fe71d9153004fd71d9153014fc71d915300cfe70d9153004fd70d915300cfc70d91531f6bf40d91531f6bc645915363ddf735915301cfe76d89531eeee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d89535e6df53d895359e7e53d895359e7c53d895359edc53d895359ede43d89531eeee52d89531eeee32d8953014fe71d8953004fd71d8953014fc71d895300cfe70d8953004fd70d895300cfc70d89535e67f50d89531eeec6258953014fe76d85531e6f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d855354edf53d85534e67e53d85534e67c53d85534e6dc53d85534e6de43d855301cfe72d8553004fd72d855301cfc72d85531e6f651d85531e6f631d855300cfe70d8553004fd70d855300cfc70d855354e7f50d85531e6f4615855300cfe76d81531defa60d8153024fd75d815302cfe74d8153004fd74d815302cfc74d8153034fd73d815301cfe72d8153004fd72d815301cfc72d8153014fe71d8153004fd71d8153014fc71d81531defa50d81531defa40d81531defa30d81531def86058153034fe76d95431d67
  | 20 => 0x700080180280000038000000002002800c016000001002400001b003000400200d00100340040080038000000000000800401200b000800000a00200100000000010040000002001006000000000500080280080060018030000000008001c0020000080018000000001800001c001000800c018001007002800800000b000400400000f0048014005000001400000b009004c0020010010000000001000000400a0000030000004005004001c004000003800c006000014001c00000e00580000380000000000002000000000000000000000140040060088008004000001000c004012001802001601100700180060100048014000002000800400000b00480080060050000020006001000001c000002005800000800f0000024006010002803400c00300000000040000028000008009002803c010000006800c01000100a0000004013000000000000b0008008000000001000000c00500100000000000010004004003000800000a00000c804000200000080000000010020004000000013801400a000000800400000f0028084022000006000000600200000200000000000000006002000802c004000000000c002000009000401000300380080020040008000000000002000400600100000180040090000008004000000802c0000070000000000005001000000000000000340000020098004000000009800800201800100080140000018000000004000800401e0010088000002000004001800200000780180000000038024010002000801c000024000001c00200000080380000000008000008006000000c000008004000800000c001804800000200180000000040040004012002001800000000300000040000000000004000002003800400000600080080000140038000002009000000000000a006000c026000000000000000600580000020030068030000006000000400a0000000008006002000000400c002000004800200000000080260080008000002001002000000e004006800c00c0010000000000004000800c0040010000004006000008800402c006001000000000000600000000000000010008005002800c000002003000400000400000100000000000024002005000000000a00a007001c002000002000001400a00000080000010048000002000001002800200000300100000400000014002000002801000c000000000800a00300380000060000008014000001004000c00601200e002400c000006000800000b005000800400b000000000200000400040000000000010000001005000001c00000700000040030020000026006000000400e0040018018014005008003000000300080040060030018054000000001000c000000001800800000000a0004006007004003400200b000800400e005000000
  | 21 => 0xa2a600008642cba37013c4d42a8348cdd41a80000000000000000000169200052a0000b8c00000035080000000000000e30000000000130aa5f000000022200000000000006ae111b37574a5751771a68000000000087c00065863a20ac0000000cb0000f2c03101c22f9116725000160000000050208807740002d8ae08ff600018300000004ad0000001112b16151000000000027a00000000e82c4000134e6eb636adc8000d1726696950460000001da4000c1e1333218cd0c6e00008d48587a32410000a02848000046800000000015b0000010146b084002cd94eea41cf70000467800013a00000005d8a70000000000110811b11b1a6c0006d43f100000000000000fec0009114578012000000000400200000400000000000000000000001000002400000900100000100020008000000002000001005200d001800c008000000800400a0030020008008000007800000400100d8008000001000001800c0040008008000004001001800a002004000000200200d0004008001001801800401300600080040010030014000013005000001000d0008008000004000002c002003000000c004001001803000800100480000080000000004028002001000000400400100080140080040000004021000002000c0000060074004000000802801c00a000000801000f000000001000d000004800a01500000100000200020018004010000801800602500000000000020018000000000004000000800d0038008000000000007002c001001005800000100000040060110030000006000000800000a002003802400400e00000080080050048000000002000800c000002001001800800100900100000110008034006006001001000000000300100060140010010008002001000400000100180040000030018008000000002801c000003000800000c008002000c00000000680200020000118030008000001000800e00100a800800600000b0024000003001004400600000000000020120038010002002000000000a002000802000000d00000040020020008000004008001007002000c0010020000000000000400a003001000400400000000000000020008004012004008800800200b00000000040040030000002000006000c0000080028014000004002800800a00400000080000020000008004001001000000000100400000000040050014002001004001406600e0000030012001004800003a007000000000600400a800000400500400000000040000014006010002801003c00000180000020030008000006003000000000000200280080000000020000004001001001400800000780080000030050000004002000000800200a001000000600c0048004002000003801800000000380040060180000004072000001800c00000
  | 22 => 0x963000166800070312d30b80000004960f8c00000000014c10926e75818000f580001cd0000908a262d905e430031f21b08d0d1c21c31b2450fe6bcf3e61d8c1ba0000c71e2800000053c00000002220000000578ba70002eb4b7cb2a000000178a8e415baf880c80005159f5400075a64e800087894c5701f85632c2851e00011be4dd3930858aee8014c410443ca38a4e232c953a0f1000000148e5f50002594000000000000116819100033bca085764f818dd9fa2ff37aa34127657925211590fe1200d3800000026800008ad9b448600004e06ac000149aa984f400040d800137e0000000000b3e6750400ae40000000003130fd009c47581d4f44ba34e9ad34000cb9252a2e0af4b9958000940001cd1d6add0214d0c00008e42f600013700000000a000000011aa0fa18e33c8594b6b000000047e63d00000000004e555d00018ae3ee000000000000000000000000001440c484e2c444b71bb0000d2425e000000078702e0ef098ab8f306a48d154d3752493540cc4ee695b2d82563770002cd42f8931091182087470700011f13dc000000252d1ea6392e9acc982891228b9a7476a40d26da1b8418c5e56a91c46705e714d8fa99b699245e13fc5cc0bf3d70909a90cbb00032440009943981bf1318b9506528796aa66a41394b8000151430af48000000000090cf1e1d10000f48f4e49b050a23c0003f133480000000004af000000016100027a0d525a6638000000040700007a4000000000000098600000000014868e23c90000000000000000000000000000017a6c38151800000077a5f80fb03da00050a2fa0384164244b410e0aa1048d299c1e0c1c0000000fc04013131df84368f16421b1d08ebdf593aff50183a65f5b3ac000880274198c000a1800000000006f30d3287c00019700014fc000000000000000028307c0000bf292f1459e780002fe07f8cd029c000113a905a12bf51c99979a74c7b0b48d388e47cb21caa7c6d6ad01a9034082c6ba286977000094800026280000d244c02c18680002f5893000019d0ac02ad3a86da64ab26c2ca8cc432848c7bac62144ac903a03430001088c4e81f4a6800000000023d0000c4600000015680a40000000001816000547000035a0000ea8000b0800058d00013b0d22579286400009100b891800000000000010b8395000000000011902b000103c00000022700000000000000caed411c000006e600054e040009000038ab32c31a00025ba9892e02401bc15b86420000001d759c000029b800000000000034b414cb0e202a0b800046707280000000004b00000d6c4730001ed400000012d8000000aa334b82d438e0b92172164e460004a9b0600000003db1884b3c00051780016faabb450b39955267a429819c8b4d063a41da03c264c000000000049708180000008774a
  | 23 => 0xe1800011e7ef04bb3c42680005a800017506994eb2af18946bd00001740001255fb34a4146ada0a800007fe0c91148000c345ef46f141866400049e0ac8f1c0001fe1a600000001970ae801000060880000000002bf80019f20000000000000b091411a90e1c00047dad94000a3b14f2c7058473d2b3000000064221988902be75309625c8338bab5a982352eeb130ec98fd542c834599248576a640002c5400062b6139cac1ee5e617a8934312573000186d7d800039d00019fc75b4d08fc094c4a80000000cc826215ea14450c6cd4ac80005c8000000000110e3790840000bfacb84d191ad656c7c02a87294ee80034017ed58a2c10000b4c65e00025c0d01424000464800168a5c7524339d9024a90a0a3594100e2418091d8b814f1cb837c0009fa0668dd900620407b06c0e7848c56f00009e486c0df94000003c44740000ce473f05d024c000cc900030b0000000583852cf3816f0c9183c000a63652aadc2549160002e00000ce1308000146ebb259180006a86ee4178001186437422800177600005100005244d739410c864025d20c17088e8683000000000070900000000000000002244000000000000000062c186000000005764a00000003c00002a00b9a6e83d5a7bd054be9508a7e094ebcb1e587253ca0004e8000089c02d2eb80019c40003e10f80e104091d12c484a479307e97451b253c00000000005f400000000000000000001a1a8fd000000061c39d3db8f7da4c00000002f588c8391e080000001455ca22c4aae83302c1f9c00076f0001a8841012f055266c58e0000672038c3abc44ce2dd54ca0000000000000d1d456000150c00037f800000042d690995498ecbd203143c1a6a030ae800000051c6980001800a311c327d00000000000dbc8a8b1e00000004f86843459a181ac53352e8f54d56391320a0c55d0d4400020f1286ba010800000001fc44980002500001aaaabda1067f178b2cceb86ef0c1b33800009036e9e99920000131a5c4e665aa49d148852e0003a787691c090b56e0114000000124aad0ac000000000011c21f36379ed00006540000cd5854000000000197e9ea31212ec5f4118528aac57e2000256246cb1a95626c08859c85d82d800001c6c010000000bc65650000920da62a452d80cd742000000071074a8e300000011a88ad00000000009670000000000000000000000000043ca89ccf66bb5a300000000210000000000cb03e900000008971542b24f009fd52c80003a40000000b3c98091533000003ae0005c1acccef671d51a2228fcc0656499e0d0cc190212923467eb260001448000419000214800000000000000009fc0002db80009e644a154400000000000009420600002e417bc00050700012d0000000000095c1ee000037010e4df0000000b04bb74c980000007f13be1a4c0
  | 24 => 0xe63be03c000089800006cb3e17900005c500008001701551e51260ba900023f811452d3650000000a3d67400013e200061900000004830a30a8490ea0c6762fe4b9cb7008ab22524492b6228e510048b64c5a5a991e6e22a7293400030800009b517200014d15bc1ae8d302d1959832ae94b30d1952ebd52ff801c2d40005b09b940007353c0a7b0e5a7fc5f78c64a8ac3e3452568000bb959c047d66e0001000000dfcaef20d85988a60003a8a028ab6b6c16dab98b6e209273000106e35858608ec59006d19c8b0d94c4aa6032e4c75813100000018ce2644f58a398b0b3c5c6000000066b64d06e4d865ab25fb12c4541af19203b493e98e01b9aa00e868134e06797c04cc1391d040003e23680e249722b368992719d40da0b91999702cc215a000016c39900000351066cb69d916000084247b878917ebff44d9b0018e30b000205ce0c18162c89c00dc6464edb4c87a03871a21bc8bc899d00000000000002788bf450800000018098ac00055280000008f067d1c4cd9e35955c000000050c00000005583620d90ff4df61594d48904bd8000042a1058fa00060106f951840e5cb2ce82ea1b10000000000a1753a000138a7e94e620d86740005ac1ced4f22eb222ad48684000592918d9dc0ad2a30000c0e0000000c04cca9285411e5400a00000e30c0248c5210d07a932a0003b600006780991e9aa0ccfa4f60001ba571089e000000000000011b85b000084c00020687b297923500000008ec4b99b840005140002bed28200000019b800000000004340005c506896d866600000018000000003560478f128bd0003458000b6f59f11d4b80bcc182b304d128405e000191827bc02319ccc8e00000000002ee00064f8774000000000165870a0006a280000008703cc00007f2c1d34f9910000000000000099600000005f80001d86159078000b4a240a259308c1000001a128e64965f000000051300000003f029045720e8f08102000000000000002480015d4c3513a319487c00025880017b01446021e901581393d79e64d843c63e38080000c250ee21a80000003a5afe80003130002be4000a7f000000000000000000000005cc4e08000000771000000153652a6271e156861685989870aa800000018a59441b7179a0640000006699cc800000029191493489b402d8000d2848b0000000000000005abc430a0001252aac0007f700000000005bb01a163069a0001790cdca361054a2ada45a4c071e4aa24ac69130aa1548be23ae4252cf41882850c5254052ab0659f8a44014a5e4afb1fd1d48a851f82a5288938000215418a0003aa2528e161620a392457448140001010c90000628800143ace300e80011881c04cb00005ce0813b695a07680770001cf938c7a90000da9a5429f4638f90000bdb46b800000073857ab4600000003
  | 25 => 0x2ce4ba401627da4a919c6be24c000078a4f95542f9596a11367f8e1157c00061331e90ce6fd0001f5ca3048057100000000004a8af2800007a440800134a00000032bc8fa67860a80001628713970c9d8d047b56b0ca832aad31d829591a298d297b47d5e6a7c2e1b4e4a68af83e21ec90d2cd440a8db8cced02355021841a5fe2e5a0889f83883a00000bd032d34420f950e44600007041d26b20000000ef00005171764000c9e547800000032911e80008fe39f2a000008dc3040cdb43d84017f02a000005800062eb02400000064500000000001961e7cdf200042231680000001180000056000000232082a000000204cee45e94d73230bdc233162978157e34907392e8cba28a2749ffc4a0a941f69f15884c6161b18396b20004b61ff40004fa0fe9a1c0002cc000000136c27739b2440c6254f49221817ae41c325a3bd1940000ab00003c000000014644aa9001ec077cae47460848269304cfc51280006f8a6f12996d5a3c99e00025e809e0002060000f340000309844000000388afdd048c0a000208000013a0000d9000054754929c09c863c000215caaa000000000085e5d40001eec0000ae575876c790000061b4b03785cf00000000007d90000000000000000000000011d000000000000061d23980000000002c080003db0001ac0540a5300000008888cd0000000ce20002a6329c00000016e800113aa5000000000004ce052242000000038b945907a64e52e0950fe8b200f88398b8884e000278879c0000000a985d48a6503a13ca2096b4d10000a520000000000000428000000039ec0d387872d0685ad0000000fa24ec24a80000008a40001691a5e5af00017dc00086f68d92380009e05dd204486296400014256b40004f3ac7c93203207a000107000066c00008ae0000001e40806000000000000083208e33709eac6c00024d80000000002df8000167356a918000c98000261c7de20506a2b6c00043d4a316a51da2ef50b1154cbe2d9264a5ec0002b80879bb40000005292ab180a08800015052ec00030a8d1d7e800007504ec0000004d7a9855f82f90000000e4e6173029c34c28a353989fd59be4784511a556a244d000000000082d552000169cc4f023a29c00068f4a000000e262a01e0000aac00010c97f00005640000000000000000284d21417d0ffa020d18ad42d0a5bccb428715fab64f4ac432f9b06d1465084468ec99ea000362a5841fc5c93059b617f883b4282308000cc01c9000000000000000014d20001cc2f8d7668e5505000152a74e00018e0000b4f5570994000749000160c1e40005d600015349e45f3209931e9862513400762bc228a810000059900000018a80003a800000009390001b21496bb600030383f4000353000181e4c43d880006f60000980ab8000ac21d4aebd73c2cd283a01c
  | 26 => 0x90bca0f49003541187583218aa400020e0002174816d1038919c17384c158d9ddd2183a032682614b41980002f5142aca169e18bcb0c52040918c940a0ec5a0841000022600000000000000f30ed8000c995f7068921e8f60c20dc19008da4392e6cd689ad404800170a5423e823d158e53d56023151f44cf3291d097703a44bf1ca44f0b56366000058c33068a06a4da47ea14a0ac00000006570000c5000000026800000fc153b09198a58f49280008de00000019bd8d448a5af118400090168e1ec06b83e95bc968015075e000000104aba63201f18da2c6b53b2f852ea6590000dfc000000044975841e00028508197347dc1f300e83760000000cf86cc00000014a0000a2c0000000c2444f000331838c2a500000003f6d4a0891bdc00000022386cd6760002132cc026e3743d9b4a11a40002caa554d700de13b210c5e0b0f2a41f913bc5bf0119bc4fd67d64cf88e87ec6fa55922645c014910880000005033dcaa34000000000000000087314ca8a113ec72656af4056a70018f28690207da69003eccb833d112a82c68241a34900003decb436b80013a20003901308ada4d10a11810ca000016d00019acd1924d00016ec1d43a200014d64fd00000000fecab0001fe4000a0903828718720000002bdcad600000026f40007d300000019480000ff254968e44301ca9b96f84594dba1f558200000000008407e50000578e8e21218e90417601330140001400b420002ab40002c053d800000000016f31dd58cb7a1c618b96f6bcd3af85480d220b649151145a0005201df4b0acd14dd92d0db80f908a32dc2f43da51c340569889a0000eec716000000322da5cc8235000000000000e62b840009a61ce08781de5263b7273d2ba42b00013653d2c412858c50a3c000122278c00000003798f800084d31daa4d88092166782ec27a3a13e690ed53c0941b2a5b54523f40d701c92b84480aa9d94a0a0000010bd075eb8e525181813ec883b1104d448ba40000d8d050000257856c0000c12c5b00cb36c5f33a1e84000000000000000000057a042c69800043c0000a96ca858591906c000000000016d00002a196e45c47db37c1c713f20003b9954d12413216a27495200000000000a944a356600000007c95e0a5f40004ca00000000000005ee000140400000007b0ff400033604d4cc25ca5cbab380001c5276867d6a81ab05a0c255441480b88da0ae21ce00000000000000000000bf02d52480f3159a5c100489fc2c600029080000004700000b8cd5e396000062d7c874c34f0440ee834868580000000005ae9f500005ba2c700002e61263fb34d0000000242879029a0001c192d927a0000002cb59a0000329ade00000001888000000260000000000000067a0000000000000217c45e000000000171a3ca4748000b780000000c5800045c
  | 27 => 0xa4acd536f80018e25a3000061845c2570000d68ab8c7e4cd1e207a2aa00001280000c3f00000000000005cf80000000000000000000d360000c980fa000000107d46c00000019b400062d00028193eecf3000205904200000000016d461f26815855140005852d8c00000017d99458a60000002a140009c3195800040e9ab19db180000b7f087000042600036c91444fa69614b2168036421000000005e1f40d011a4000c760002e2cd7e0001df80016c86b10da9dd400037d00006b0000aed00000016686c411c00009c40000cc904937c000063000149858a01b00012f00001988de8104b5f000061c00000040797880001290210000000ac348700012b60000dea6a80000000000000f9429d0001564a34bea2dea7f88a000000002387b83823a18000f9e88200009a94840131a280011fe00065e000000000000010c0852d3d21fabf5a2213e1f90c68c7459d2af139c0008a50000000000000000143800000062425380d400049f9e180003004fb00000003a71161cd0880d2701115758464f800033216500000000000eec0006890000fdc88c16b1efd32e0002cc000000032324eaacc000000000000197400000006696522030002f181d66200b6a42486aab500019dc00000000000004d60000000fdccec0002010000fda7223bfabc00007ad5d530b45008740000e8c0000000000c3400031826f23751104384558000000622000005404852b0000000000c756188000000000000000176886d174074c0603b83f92f388ec5926318000000000000253c6b60000000000ec2ced000272c000ca9000000000000017bb28d0a800027b84f096a000611000000000057f8ab51f026f00000014401a46280b5c3c64ab0602bb8000ab6014800064480d0c100003e4a4532501f814a000000000021800000000000000003b800011f20001dc8d3c0000000001c655a4b9165529d427e00000000000000001f9aa2034a05300009b0af04c65e39e5cf18ae305994e4de0cc3090a4d464a2f646315f15b01eb1670129560a1b03d81ad532c4d64b0cd936400026e007801e0965dfa1e8dc687600026e43f200000000000008f248321f849e1a12ba06e879a999220a0a40000003d4000000000063c800185e0be6a000006940000000404cfc97f00000000000001169124bbc000000000199a0006a3b05c3acd0e230000077a46218aad001dc30f118807ca767dd000177473c49e000000000000064e24b449630338200000003672c0885d03a00000000009104b00000000a0400000000000000000000000b683e100029b4ece26900000009e6375500812c6501b63850000530117000275d2042e500000015ec9f549300000004e30002f2491e9e10ad1af1370b0800020604fc0001289a08310cf00000d4cf8074d23282114face546da93
  | 28 => 0xe2090410a26c40009b3000000186e000176a9612842e948f817871c05f2ac00007508b700000000000005340000000000000000000045d00018780000005b32ff9594d331af9add19600048c000000085800014745b88c05fc16a0000a6c00d1f8c06a00055500000000000000f58000c87000000000000000000015aeb2f00000100000001f2a0d40000000002fc988e0006749c696083e7000000157200000000004ac18c2c98000000b5c61985800000000000000000000000063c00034b0000000000000000350c0008d8473800059642313d9e7561a0005e88df8bda9b51f40000c06903000000000000048bb2380000004e380005f8890000000000051f000000182c75218d90915ba35e4a48000000791000022d6dab9d00024797ce000130a910000d0526d3348b7000023f20fc7206a73a2ad5c196abd0002d200000955e197d8eaa45f10c00000000004ffafcd4aa4be6500000000381000000120a8a967b80014d471b03b2015442000000000092628c04dacb00000001db800000000069fa2c8afac3d18823f01b024e348a95c3ee45b2e813488969fb58a33ec00000069a8000ac40003c115a400003e0001ee829898000028e407e0270002be91dc02e4798b6103800025e80000009c84c80f780000000a1aec4000d3e20417e801c0000000000000000000000000000015798d40006196a300002d60c2000097c00001200029ccf16b60000000000039b35c80004e600018b829da4a7ec68380000000000000fd40007fe1e3ab1101600009b000000090d5c2325c0c40002ca00002dc00024a0000000000350aa581240cc3732fec42a53630b000144652400016402a600035180018782452bf31cc088cca38b00009d46344e1270079e0005c92b3d6c40001a8902800000038613580000000061bd00008060000000be428f158a6f0eac37100030305f0ae53b580015fc20a00000000000000273190cf800042d80002e800051d00008bc1070d1a8f800099100032c4d9c0000000000000c29000006004c8ba49f070c0000000001c918b60000002c847f45704938000000b1120a00017785a23e700000000003de97694f41f50319f20c261b8269b2b0e3ccc71d5172000000049980008cc5490000000000760000196d83e000322b3103e070153f103c000a8b00000000007393a5000000000000022800000e03ab800170e36129f000146693400000013506e043100001b66014f921591606d55eeaf684bc5912b38000000bd91ea000000000012e2bb084e00044321a139496263300000007be5183048000c695c30e350ea00000028a80000002efa2143ce00017616241700000001f78032d150000c1c43a6d601529c847c5e500008f000000068d00010f60cf0000000b5cb050001d9181000000000014ccae44e6a12cecc00
  | 29 => 0x1c800000016715902c4609880400000000020107f00000ca00000008465b3b4e00000f5000138400064f0002cb9a14b17298800071ec1a31804b845068d0002d1177c9d55da857154e0000000b240009ce0001f7cf400000a50c083261e803c9a94b0e0000001988c14b986468001712000540b40c7fc3693ac9a152aec5543586d17da04c12c1b6c0769b02bd8db4c4aa9100013ad23298321a000016e72a02800009dea22642a4c923812761d91b111c3c2000176cbe09c900000000000002702b9c00099822124a4e3e6f60000d4000072c000000177a2be000169c00052c48ea6b0fe053a1ab800169653200000440000b23c683cc1900000000000000b1058c2b7cf3605937200000002e10001f040000000000000a4e54d00000012e88b536f0000082000259293d63a0000002d6c6e400000027ccd8207c000335d3b873729a82f015e000000000007a0005bb9fe06d80513632c056e212d0ef06a82f063323691dcfb02ab00025f000000000000016e62b65912a104ea9df35aa6047ae2592eaa9805a2c7862497a90f82df1ae9258d204fe000337946400033c800099076a026ab2cd9282c1d98384000000000000d5a215750684584ce0000001c84000cf60002f589e09374b4800050247959b16b000056a00000000006b310101b1a621061f59de53b260c3813524e5e3ab11929c40869da0000b4028000038a07d800000014e00003900005d700013da3c320e9ea896692e000000000000030c00000005e10003330028000000105d2b055f23410a800086330489e41065b32250c2800089545da624a229ba00000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87e87d95514c0051b90eb22629808a97215644c5301172a32aa298a600687e85dd9214c0010fb0bbb242980063721973485300353d42ec8a8260068f887591504c0339b0edb9aa09801b1e1d952541300266c3b264a826000f49524c9504c00d8f0eca8aa098013361d93154130007a8a8a62a8260048de87dcd65480051ed0fb8ac89000339dc871591200046fc1aecaa240048dc835d954480011ef02bb2a89000a3d20576551200046fc1aeca9a400687e859d943480010fb0b3b286900021fe157650d200343e42aeca1a40008f7815d943480051e902bb2869001637a1f6350d200062e3aec6a1a4004ace83d9532480091d90eb2a6490013331d9434c9202c5a642a8699240008df835d761480091b906baec29000a1f21d655452014d2e41acaa8a40068f687d8551480051790eb22829000aad20564505200146e43ac698a4002ae481d9121480051d90eb22429000ab9205644852000c76432e690a4002ae686d8521480015c90ca0a4290003a9591414852002d5d426caa0240058f88759540480275b106b2a8090002ae21943501202ad9c42a86a024013e986350d40480013d10e9928090006ba2193250120007c4a1a64a024000de321dc54048001d6683b0a8090003e850521501200246f43ee6b2a20018f8805cf64440071dd0fb92c888003391cb71591100046fc1aecaa220048dc835d954440011df04bb2a88800e3b20976551100046fc1aeca9a200687e859d943440010fb0b3b286880021fe157650d100343e42aeca1a20008ef825d943440071d904bb2868801637a1f6350d100062e3aec6a1a20008df835d762440091b906baec4880063ea1f70589100045fc22eca9220058bc845d952440011bf06bb2a4880123720d765491001c3e43acaa922035a5c83595524400d1dd0fb12a4880023be0976509100047bc0aeca1220038bc87591424400755904b2284880023ee01764c91001c6e43ac69922004ad683d9531440091e90eb2a6288013351d9434c510225aa42a8698a2003ae482d9121440071e90eb22428800eb9209644851000c7a432e690a2003ae686d8921440015c90ca124288003a9591424851002d5d426caa0220058f88759540440275b106b2a8088002ae219435011021d9c42a86a022013e986350d4044001bc443b928088003aad0b625011002c7c43ac4a0220009f0874c540440035e10c98a8088003e450d3150110007d0a1242a0220028f8865d120440071f10eb224088003f04c9314811000df043a429022002de08748520440037c50c90a4088006f8219214811001f70432429022003ee3764852044005bc4ec90a408800b781d9214811001f703b2429022002ce0764852044001bc6e890a4088003785d1214811000771b22429022000ee16448520440017c70690a4088002f860d2148110
  | 1 => 0x8c7b92a2a80039518f61545500246f41eeca0aa0008dd83dd941540030fd0dbaa82a80031718f7550550034ba43aa2a0aa09ee546354541540091b9063b262a800317d4c764c55000c3e432ea98aa029c5c635d531540051bd0fb1a62a80a79518d514c5500246f41eec90aa0008dd83dd921540030f90cbaa42a806a4f21175485500062e31aea90aa001978805d52154001d8843b1a42a801a3ea1b70485500066c31ee090aa000a3d8494f65501a587eebba2caa001237a1f73595400062fba8e6b2a80018be86dd1535000b1f50db82a6a030a4fa1f7550d4061e1e3b6eaa1a8000d3870dd543501a3e3061baa86a03070f1d87550d400069c380eaa1a80d0f18301d5435002d878ebb2a86a00038794f6550d400245e43acaa1a8000d1c75d8d435000b3390ea9a86a00dee62015350d4000cdc406e4a1a80019b880dc543500033750fb8286a00034e1d77050d401bdcd41ee0a1a80008df835d762500091b906baec4a00021fe1573d89400343e42ae7b12800387c87595525006b4b906b2aa4a00062fa1b745494000cdd406e8a9280019ba80dcd425000755d0db1284a00166b21d525094000556432a4a128000db210dc542500031790cba264a005a4f215744c94000cdc402e899280cfb1c8550d325006fb30e0a1a64a00163ea1b704c9400046fc1aebb0a80048dc835d761500010ff0ab9ec2a001a1f21573d854001e5639285b0a8000ea542c8761500050f90eb2aa2a00a69720d655454000c5f436e8a8a80019ba80dd1515000337501b9a82a00036a88372505400155a40ec4a0a8000ea621d89415000556d0db0a82a00166d21d51505400055a432a2a0a80018bc865d1315002d2790aba262a00066e201744c5406758e42a8698a8037d987050d315000b1f50db8262a00033908676485400343f428ec90a800087d851d921500091bd063b242a00023760c764854000672108ec90a80018bc865d12150001958eca1242a00032d1d94148540006ac39ecaa8280cdb3a85dd150501053b50fb9aa0a0217361db73541406678c2a6e6a828083cd8761cd5050001b36e839aa0a0003661d0735414065f8c2a0e6a828013cd873d8d5050001cb6a7b1aa0a00065e21d53541400d59c422a6a828013d587354d50500013710ea1aa0a005ace215435414009ecc39a86a828000f195350d505003567108a92a0a032b561cd52541400b59c42a84a828075d98735095050001e52a4a12a0a006ace211515414064eac39aa2a828016b388550550500e5b30e6a0aa0a0003cc54541541400061eba4a9b2a600687e87dd5644c0018b8ebb9ac8980021fe1576551300046fc1aecaa2606e8df835d7624c0071b906baec49800e1fa1f655493001c6e43ac8992602ea5c85591324c05dc98caa9264981ba37e0d75d85300146e41aebb0a6002
  | 2 => 0x77058d210052f42ee6b1a426ecd870d4d63484031f50fb82c6908021f6167654d210046ec1ceca9a42008bf845d9534840b17908bb2a6908023ee017654d2100c7c402eca9a420687e859d943484010fb0b3b286908021fe157650d210343e42aeca1a42008fb805d943484031f100bb28690803590877550d210245f43ec8a1a4200c3c75d91434840b1b90eb1a8690803171d56350d211bd6c402c6a1a42058ec8759542484053cd0fb8a849080a79207705092102c7a43acaa0a42039e687dc941484057490ea12829080f6921d4250521014d243a84a0a4202ba68650941484057490ca128290817a9219425052102f53bb284a0a4203da6765094148407b48eca128290817a91d9425052100753b2a84a0a4200ea565509414840174f00a12829080e7920b7050521006d2a16e0a0a42008bf845d7604840b17908baec0909ba97a1a54d8d5061e2f3b4a9b1aa000e1f6495363540dd6b5012a6c6a81ba9761774d8d503756d400e9b1aa085ad9801d3635410b4bd0a396c6a81ba9761472d8d500046f43885b1aa0008dd8710b635410b4bd0a216c6a80029761442d8d500056b40885b1aa000ad58110b63540dd5b500216c6a8002b660042d8d5042d2f428e3b1aa06ea5d851c763540011bd0e20ec6a80023761c41d8d5042d2f42883b1aa000a5d85107635400159d0420ec6a8002b360841d8d503756d40083b1aa000ad98010763540011bd0e10ec6a80023761c21d8d5042d2f42843b1aa000a5d85087635400153d0810ec6a8002a761021d8d503756d40043b1aa000ad98008763540011bb0f320c6a835b871526418d5065d6cc04c831aa0008df8759063541ab4bf0ab20c6a8306972146418d504156d400c831aa082a5e869506354001c3ec92a0c6a8003871925418d50415ad404a831aa0d4a5d8598863541a74bb0b308c6a801297a1b6354d503762e3b6c6a9aa0b3c5c63dc953541398b8c7b8aa6a801a1f2147650d500061f2a0eca1aa000cda301d943540030fd0dbaa86a830f1718f7550d5000cbd406eaa1aa0058de87d8d435410b8b8ebb1a86a801a5721d5350d500252e432a6a1aa000c5c7654d43541678b8ea31ec4a800e1f21573d89500046f43ec6b12a0008de8718d625406b8b8c7b9aa4a8003568c373549501ad2f436c6a92a06ec5c76d8d52541058b8ec31aa4a80039318f62549500062e31ee2a92a0048de83dd942540011bb07bb284a80061fa1b75509500062e31eeaa12a00696c87549425416bc98c6a9284a800317d4c764c95000c3e432ea992a035c5c635d532540071bd0fb1a64a80d79318d524c9504e62e3a8c7b0aa00287c855cf61540dd1b90db9ac2a800237a1f63585500046f438c6b0aa029c5c63dcd5154001ab461b9aa2a80a697a1b63545503762e3b6c6a8aa082c5c7618d51540018b
  | 3 => 0x1b2a8600a75810836550c010fd0e086caa18021f61c10d95436351f42021b2a8600a3d840436550d874bd06086caa18029760c10d95430053741021b2a8600a6d820436550dbf87eebba2caa1b7a9760e62195436ed2ec1cc232a86d0a3d849806550db9cb061300caa180396182301954361e1e3b6caaa2860499e83dc15450d8d8b8edb2aa6a1b07171cc65d89430043f43ecab12860087e871956250d838b8e632ec2a18021fa1f65585430043f438cab0a86c6c5d73d976050d85878e832ec0a1b07179cc65d81436162eb98cbb0286c387c86dd56050c010fd0fb2ac0a18021fa1c65581436de2fb98cab028600a3d8590764548011bf06b86c8a90123720d70d91520062f298eca1aa40387e86dd5435480d2790eaa286a936b0fdd774595420353742ec6a92840087f855cf615080d0f90ab9ec2a10030f5d254d95320052ec1ca9b2a640687e87dd5644c8010ff0abb2a89900e37a1b735513260caf43eeaa1a64c6c5c76dd5434c9858b8ec3aa86990bb171d76550d320070f2a6caa1a64058dc87595434c8093390eaa28699003531d77250d320347643ac8a926435b4c83551524c9b369d0bb9aa4990bad3215435493200786aa286a926400a5c8550f614c8010ff0aba6c09901a1f21574d81320051ec2c85b22a2008df835c364544091b906b86c8a88031794c7650d510143f436eaa1aa20693c875514354401a6c83ba2a4a88038b90b64549510143e432eaa12a20287e86dd532544071bd0fb1a64a881a5b21d524c9511af2631aa4992a20187c855d360545b187eebba2caa08021fe1573d89410343e42ae7b12820387c8759552504091dd0fb1264a081a9da17635454100792a9284a8a82018bc845d7605040187ae92a6ca988029760e54d95310246e41ae1b22620687e87dd5644c4010ff0abb2a89880a37a1b735513160caf43eeaa1a62c6c5c76dd5434c5858b8ec3aa869888b171d76550d310070f2a6caa1a62058dc87595434c4093390eaa28698803551d77150d310052e42a87b12620387e87d95524c4051bd0db9aa4988123da1b71509310146e432e8992622295c855d1324c4071b90eb2264988ba97215644c931024e643aa4992622ee4c65549324c401ba621b82649881a3d21d645453114daa41aa8a8a62d7b5685dcd514c4456a90aa1aa298803c555143545310363a3b2a4a8a6229b5483549514c4099a8ec992a29888ad52153254531007a2a9264a8a620087f855d3604c40d0f90aba6c098803b24cb20d8131006e210ae7b2a42048df875cf6548401b4843ba2ca9080297a0f755952102c5f43ee8b2a42c6c3c7494d654840187aebaa6c8908023ee0173d912100c7c402e7b2242048de839d954484011bb073b2a8908022fe11765512102c3e43acaaa24200d64215d7634840d0ff0ebaec6908037808
  | 4 => 0xbf0003520009a96303a069152212a8824002270801ed0f9c2382001200dc000580208000003d01f000000000001d61a8600c81b5000000000a4000000000000007940015500001800000326000948ca000000000760000002f00000000118000000000310000003ac271e1000240249d335c6ac0381713073c0011c3bc8000000032400032000472000040ee3b860ce20002dc00037a4600021810800000000001330226d8889083a8544f51c53763f417922190634f1a430000004d08b2cc86c000e2078424000c3226760002120005ac0000022a3c0348971145f0d621d0002b400000000000000470ba000f88000008b822800000809029041a23251a994000128668000006f84a852000078000000000881595d00000000000000840c71bf33871ce49ff3c43851e16f00081c2692b0004f0000001740009f0000000005b000000000000000020009500000000030800076000bd12f268000bf8000003f8001b913e00000000224000a490f42c2a4d3a2f20c88c929d51d4354c516a41e7ec0000035e5b522943140430bba0e48e0006d83904e2a08b00007e904af8700cc0010f0bc000000f480015634d130004500000000000067c0000004a440e008000085c0000d262000029380008dc0022201616cff1321f2871128000d4000969ed0d6038da15c17a828b90043c065c3e1e60fc0d000141126625210d737020c4f0782f0804591eb168568000000002fc001c80000000e0583c800077917000000001472c47d4940cc000000000af3be500c30f521c7f0f39ca05400c0000c00000030000901400010000340000400004000180003c0000400008030000500001008040400600c0a0140300c010000002c030100203c0200400000010140201c020040201c020000700000018010001002c0301400004030000000c1400003000060000700800004000000200001000010000b004000000404400004000000100c1400006020010100d010030100800807004030040101c0202002008000000402802018030000402c010000000004018120000000003004060000002005098020000000401004060000300c02028050000000c0000c00004110180000c02000010000d018000180702400000006343fc2ae7b12a8c687f855cf615510b1bf06b86c8a9b0e1fe1574d81530051ec24a1b2a86c1c5e768c36550d874bd06396caa1b1a9760c72d954361d2f418e3b2a86c6a5d831c76550c010fd0e10ecaa18021f61c21d95436351f42043b2a8600a3d840876550d874bd0610ecaa18029760c21d95430053d40043b2a8600a79800876550d8d4bb07b86caa18031edc270d95436351f420e1b2a86c3a3d841c36550c010fd0e106caa18021f61c20d95436351f42041b2a8600a3d840836550d874bd06106caa18029760c20d95430053b4084
  | 5 => 0xd9800000000000004300008c05a0e42d4000591be000000000000000000000060800000000660000003f44040013934613c970002d0000b200016e8900020c3a4000000001107b04da3628c450621f32403748d9f20000009b9d1248000000002e256000244090058001bc00000032800000000e1800000000000840000003e8001f6150000000000f4ed8ae4705ec0022d0008e8850c7000001030ed3fa3c88119b42a0000005729a4d8000350000c8000000140003f8510000007b1591c0368b3a133f20010d0fc040208a513a296358eb9844767388d2340000cc438b31448805299131e00000000466000479cb00000000000000394000000006580000021a558bb0002e0000680772600c09e8b00000c4a299d0000006c80020000009a32000250c39880c60000004238c6646c08c35a7c083885340000000b1000000001501f44144495e00080c720990a00001217406e7b847144334110149bd0000e0001f7000000ed0000a640c4880027e000a60f33d0000000004286982e23f0322f8e68e801206c0011f1844840180023a2980006d0003e03c800000204000000007bc000ac27600000074000000d28000000b5058aa02a1805c073046318170121d8041189532e629cbe9b71fe38c930c103e32d160b932a6e85d800000508000cf000000000000000007880019c000000000000000000043200000000000000b6000000000001a11ce000bc8004221e83380012c2709622b2161581315b000008000000005d4fa23e142000000003ba00000000290000000360007d8a78000007647b8000d062ce600029c834000000e28a42a8e61246146f12735448c0001847a000d91192ca314000000000003a98c0be00000014000000001520000000000000000000157000688600003626a026046000690079610587401d04b0dc274060000000000000023c00000000408348cf06c302000fc043000820000000506c07488d1465a4
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa828950280214448000220139500b000b008d2801e0001b00000160800b8000a56a63c000001c000200c0921d00001940e7c000000400034ace103234c13182004000021c100020c0830c000881acc32615450d524c85331498551435453114cd1261524c9514c46bc4476549325453100561650215cf65484015c19008573d952100469a6021dd165484015a190087745952100549650215d763484015619008575d8d2100478a6021dc163484015a1940877058d210054965021dd54348401561900877550d21006162007558d4348401c1a548c07650d5060c172607654d435400181c8418d7548550005a165021d8d21540016c190087634855068646a0c75dc143500014a594086764854000538640219d921500010e598084764854000529650211d921500014e190084764854072546254741cd50500353189854d43541401bd4625d5350d50500019188754d43541400d4ca2615250950501c7d087354942541400d4cc2615150550501c5d107354541541401af121d9524c9504c053c50765453154130014a92616450521480054a49759141485201bea2219434c940481c37089550d325012001ca92616450921440074a49759142485101bea4219434c540441c17109550d3150110015382597448520440074e0975912148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x44002059a92007558d434840100ed490831aea90aa0e58462a48754d4354140
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
  | 19 => 0xa0c
  | 20 => 0xa0a
  | 21 => 0xa0b
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
  | 85 => 0xa0996
  | 86 => 0x138b
  | 87 => 0x124b
  | 88 => 0xcc996
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
  | 101 => 0xa49d5
  | 102 => 0x138c
  | 103 => 0x124c
  | 104 => 0x150c
  | 105 => 0x128c
  | 106 => 0x18c9
  | 107 => 0x1789
  | 108 => 0x180c
  | 109 => 0x130c
  | 110 => 0x1a49
  | 111 => 0x17c9
  | 112 => 0x198c
  | 113 => 0x134c
  | 114 => 0xb8a14
  | 115 => 0x138d
  | 116 => 0x124d
  | 117 => 0xd0a14
  | 118 => 0x150d
  | 119 => 0x128d
  | 120 => 0x168d
  | 121 => 0x12cd
  | 122 => 0x1a89
  | 123 => 0x1949
  | 124 => 0x198d
  | 125 => 0x134d
  | 126 => 0x138e
  | 127 => 0x124e
  | 128 => 0x150e
  | 129 => 0x128e
  | 130 => 0x5c9
  | 131 => 0xce
  | 132 => 0x168e
  | 133 => 0x12ce
  | 134 => 0x180e
  | 135 => 0x130e
  | 136 => 0x170a
  | 137 => 0x15ca
  | 138 => 0x16cb
  | 139 => 0x144b
  | 140 => 0x188a
  | 141 => 0x160a
  | 142 => 0x184b
  | 143 => 0x148b
  | 144 => 0x1a0a
  | 145 => 0x164a
  | 146 => 0x19cb
  | 147 => 0x14cb
  | 148 => 0x154c
  | 149 => 0x140c
  | 150 => 0x18ca
  | 151 => 0x178a
  | 152 => 0x184c
  | 153 => 0x148c
  | 154 => 0x1a4a
  | 155 => 0x17ca
  | 156 => 0x19cc
  | 157 => 0x14cc
  | 158 => 0xbcb94
  | 159 => 0x154d
  | 160 => 0x140d
  | 161 => 0x16cd
  | 162 => 0x144d
  | 163 => 0x1a8a
  | 164 => 0x194a
  | 165 => 0x19cd
  | 166 => 0x14cd
  | 167 => 0x154e
  | 168 => 0x140e
  | 169 => 0x16ce
  | 170 => 0x144e
  | 171 => 0x184e
  | 172 => 0x148e
  | 173 => 0x18cb
  | 174 => 0x178b
  | 175 => 0x188c
  | 176 => 0x160c
  | 177 => 0x1a4b
  | 178 => 0x17cb
  | 179 => 0x1a0c
  | 180 => 0x164c
  | 181 => 0xd4d14
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
  | 192 => 0x104e91
  | 193 => 0x74c
  | 194 => 0x5cd
  | 195 => 0x194c
  | 196 => 0x1a8c
  | 197 => 0x1a4d
  | 198 => 0x17cd
  | 199 => 0x18ce
  | 200 => 0x178e
  | 201 => 0xbca14
  | 202 => 0xd4a14
  | 203 => 0xca16
  | 204 => 0x12ca16
  | 205 => 0x749
  | 206 => 0xb4a16
  | 207 => 0xcca16
  | 208 => 0x74a14
  | 209 => 0x194a14
  | 210 => 0x1a9951
  | 211 => 0x5cbd1
  | 212 => 0x5cd51
  | 213 => 0x5d951
  | 214 => 0x1800d6
  | 215 => 0x5ca
  | 216 => 0x1a9952
  | 217 => 0x5cb
  | 218 => 0x1a9953
  | 219 => 0x5d2d5
  | 220 => 0x130754
  | 221 => 0x5cb55
  | 222 => 0x5ccd5
  | 223 => 0x1a9954
  | 224 => 0xb4a095e
  | 225 => 0xcca099e
  | 226 => 0xbcb8a1c
  | 227 => 0xd4d0a1c
  | 228 => 0x5c751
  | 229 => 0xa0754
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1431
  | 6 => 3403
  | 5 => 584
  | 4 => 46
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
  | 6 => packedAt gbK6 (178086+((h/1134+packedAt gbK6 (163344+(h % 1134)*13) 13) % 4941)*13) 13
  | 5 => packedAt gbK5 (36396+((h/194+packedAt gbK5 (34456+(h % 194)*10) 10) % 932)*11) 11
  | 4 => packedAt gbK4 (3325+((h/15+packedAt gbK4 (3220+(h % 15)*7) 7) % 73)*7) 7
  | 3 => packedAt gbK3 (245+((h/1+packedAt gbK3 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x71c701c7e38e3c707063fff83ff1810f0e43cf
  | 1 => 0x81f801f8fc0fc7807ffc703fc1f20633307d33
  | 2 => 0xfe0001ff1ff007ff807f803ffe04183cc38e3c
  | 3 => 0xfffffe001ffff800007fffc000081fc0fc0fc0
  | 4 => 0x1fffffffff800000000fe000fff000
  | 5 => 0xffffffffe000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2081204121040c1212009a0818c18105064045
  | 1 => 0x81484488440240802924209281220612101512
  | 2 => 0x52008912089001290049012524041828408a28
  | 3 => 0x94521c001eaa90050572458184280a40f80f80
  | 4 => 0x1000134d2646460006000848a000af6000
  | 5 => 0x69a4e1e48000000808000806318755bf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffe8fefceae8ffffffe8fefceae8ffffffe8fefceae8ffffffe8fefceae8ffffffe8fefceae8ffffffe8fefceae8ffffffe8fefceae8ffffffe8fefceae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_27945
namespace PEqualNP.Outside.L_meta_27945
open PEqualNP.Outside.L_meta_27945.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 91 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
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
theorem bgb_4_32 : Interval gbAtlas 4 32 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 46 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_576 : Interval gbAtlas 5 576 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 584 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)))))
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
theorem bgb_6_3392 : Interval gbAtlas 6 3392 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3403 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)))))) (concat (concat (concat (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528))))) (concat (concat (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)))) (concat (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 32, 40),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 6 zero,inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 4 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffeaeaffffffeafefeeaeaffffffffffffeaeaffffffe8fefceae8ffffffffffffeaeaffffffeafefeeaeaffffffffffffeaeaffffffe8fefceae8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_27945.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[8,7]⟩,⟨.or,[0,1]⟩,⟨.or,[10,4]⟩,⟨.or,[6,7]⟩,⟨.and,[11,12]⟩,⟨.or,[1,2]⟩,⟨.or,[14,6]⟩,⟨.and,[15,5]⟩,⟨.and,[0,4]⟩,⟨.or,[9,13]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_27945

open PEqualNP.Outside.L_meta_27945 in
theorem PEqualNP.Outside.L_meta_27945 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
