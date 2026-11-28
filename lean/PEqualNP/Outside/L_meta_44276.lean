import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_44276.Model
-- The engine (the signed live-wire search, its checker, the input-fixing lift and the closing lemmas) is the text of
-- the merged L_meta_36434 by Legoshi (same repository, Apache-2.0), which follows L_meta_10856, L_meta_8453 and L_meta_1667.
-- New here: the search tables, sample pairs, bounds and the AND/OR circuit for this six-input function.
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

def eqF (a b : Sig) : Bool := Nat.beq a.toNat b.toNat
theorem eqF_eq (a b : Sig) : eqF a b = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp [eqF,BitVec.toNat_inj]
noncomputable def anyEq (m d : Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) false (fun v _ ih => eqF (masked d v) m || ih) l
theorem anyEq_eq (m d : Sig) (l : List Sig) :
    anyEq m d l = (l.map (masked d)).any (fun v => v==m) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (eqF (masked d v) m || anyEq m d vs) = _
    rw [ih,eqF_eq,List.map_cons,List.any_cons]
noncomputable def availF (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  eqF (masked d a) zero || eqF (masked d a) d || anyEq (masked d a) d pool ||
    (u && anyEq (masked d (neg a)) d pool)
theorem availF_eq (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :
    availF u d pool a = availableB u d pool a := by
  simp only [availF,availableB,eqF_eq,anyEq_eq]
noncomputable def allF (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) : Bool :=
  @List.rec Sig (fun _ => Bool) true (fun v _ ih => availF u d pool v && ih) l
theorem allF_eq (u : Bool) (d : Sig) (pool : List Sig) (l : List Sig) :
    allF u d pool l = l.all (availableB u d pool) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (availF u d pool v && allF u d pool vs) = _
    rw [ih,availF_eq,List.all_cons]
noncomputable def countF (d : Sig) (l : List Sig) : Nat :=
  @List.rec Sig (fun _ => Nat) 0
    (fun v _ ih => cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ ih) ih) l
theorem countF_eq (d : Sig) (l : List Sig) : countF d l = l.countP (isMaskedConstant d) := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change cond (eqF (masked d v) zero || eqF (masked d v) d) (Nat.succ (countF d vs)) (countF d vs) = _
    rw [ih,eqF_eq,eqF_eq,List.countP_cons]
    change _ = _ + if (masked d v == zero || masked d v == d) = true then 1 else 0
    cases (masked d v == zero || masked d v == d) <;> rfl
noncomputable def scalarPoolCutF (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  allF u c.domain c.wires rest &&
    cond (availF u c.domain c.wires (choiceVal op))
      (Nat.blt (k+c.paid) (c.bound+countF c.domain (choiceVal op::rest)))
      (Nat.blt (k+c.paid+1) (c.bound+countF c.domain (choiceVal op::rest)) &&
        (allowedB u op.1 && (availF u c.domain c.wires op.2.1 && availF u c.domain c.wires op.2.2)))
theorem scalarPoolCutF_ok {u : Bool} {c : BoundPool} {k : Nat} {rest : List Sig} {op : Choice}
    (h : scalarPoolCutF u c k rest op = true) : scalarPoolCut u c k rest op = true := by
  simp only [scalarPoolCutF,allF_eq,availF_eq,countF_eq,Bool.and_eq_true] at h
  obtain ⟨hall,hc⟩ := h
  simp only [scalarPoolCut,choiceOK,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true]
  cases hz : availableB u c.domain c.wires (choiceVal op)
  · rw [hz] at hc
    simp only [cond_false,Bool.and_eq_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inr hc.2⟩
    simpa using hc.1
  · rw [hz] at hc
    simp only [cond_true,Nat.blt_eq] at hc
    refine ⟨⟨?_,hall⟩,Or.inl (by simp)⟩
    simpa using hc
noncomputable def anyP (f : BoundPool → Bool) (l : List BoundPool) : Bool :=
  @List.rec BoundPool (fun _ => Bool) false (fun p _ ih => f p || ih) l
theorem anyP_eq (f : BoundPool → Bool) (l : List BoundPool) : anyP f l = l.any f := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    change (f v || anyP f vs) = _
    rw [ih,List.any_cons]
noncomputable def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  anyP (fun p => scalarPoolCutF u p k rest op) pools ||
    (links (keySet (choiceVal op::rest))).any (sameWords (choiceVal op::rest))

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,anyP_eq,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd (scalarPoolCutF_ok ok)
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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
noncomputable def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

noncomputable def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
theorem or_ones_and {n : Nat} (x y z : BitVec n) (h : (x &&& y) ||| z = BitVec.allOnes n) :
    x ||| z = BitVec.allOnes n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun w => w.getLsbD i) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_allOnes, hi, decide_true] at hb ⊢
  cases hx : x.getLsbD i <;> simp_all
theorem takeTwo_right (c : Cov) (a b : Bits) :
    takeTwo c a b = takeOne c b &&& ~~~((c.2.1 &&& a) ||| (c.2.2 &&& (a &&& b))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo, takeOne, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
def quickPair (c : NodeContext) (a b : Decor) (op : Nat) : Bool :=
  if Nat.blt c.1 c.2.1 then
    (takeTwo c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152
  else Nat.blt c.1 (c.2.1+1) &&
    (((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) b.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152) &&
     ((takeOne c.2.2.2.1.1 (column (!c.2.2.2.1.2) a.2) ||| column (!c.2.2.2.1.2) (dbin op a b).2) != BitVec.allOnes 152))
theorem evalMove_cov {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) ≠ BitVec.allOnes 152) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else if (restCov cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ka kb ||| column (!cov.2) z.2) != BitVec.allOnes 152 then true else _) = true
  by_cases hlen : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap
  · rw [if_pos hlen]
  · rw [if_neg hlen,if_pos (bne_iff_ne.mpr h)]
theorem evalMove_long {cap n : Nat} {ws : List Decor} {cov : CovPair} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {op : Nat} {a b z : Decor} {ka kb : Bool}
    (h : 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1)) > cap) :
    evalMove (cap,n,ws,cov,pools,links) op a b z ka kb = true := by
  unfold evalMove
  change (if 1+(n-_ - _) > cap then true else _) = true
  rw [if_pos h]
theorem quickPair_ok {c : NodeContext} {a b : Decor} {op : Nat} (h : quickPair c a b op = true) :
    testPair c a b op = true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := c
  unfold quickPair at h
  simp only [testPair,Bool.and_eq_true]
  split at h
  next hlt =>
    have hl : cap < n := by simpa using hlt
    have hf := bne_iff_ne.mp h
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_long (ka:=true) (kb:=false) (by simp <;> omega)⟩,
      evalMove_long (ka:=false) (kb:=true) (by simp <;> omega)⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
  next =>
    simp only [Bool.and_eq_true,Nat.blt_eq,bne_iff_ne,ne_eq] at h
    obtain ⟨hl,hb,ha⟩ := h
    have hf : (takeTwo cov.1 (column (!cov.2) a.2) (column (!cov.2) b.2) ||| column (!cov.2) (dbin op a b).2) ≠ BitVec.allOnes 152 := by
      intro e
      rw [takeTwo_right] at e
      exact hb (or_ones_and _ _ _ e)
    exact ⟨⟨⟨evalMove_cov (ka:=false) (kb:=false) hf,evalMove_cov (ka:=true) (kb:=false) hb⟩,
      evalMove_cov (ka:=false) (kb:=true) ha⟩,evalMove_long (ka:=true) (kb:=true) (by simp <;> omega)⟩
theorem pairQ {c : NodeContext} {a b : Decor} {op : Nat}
    (h : (quickPair c a b op || testPair c a b op) = true) : testPair c a b op = true := by
  rcases Bool.or_eq_true_iff.mp h with q | t
  · exact quickPair_ok q
  · exact t
noncomputable def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (fun op => quickPair ctx a b op || testPair ctx a b op))
noncomputable def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => pairQ (h.1 b bm d (opsOf_mem hd))
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => pairQ (h.1 a haTail d (opsOf_mem hd))
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


end PEqualNP.Outside.L_meta_44276.Model

namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat) × List BoundPool

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2.1
def apools (g : Atlas) := g.2.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SBf (j : Nat) : Nat := [5, 4, 6, 6, 6, 6].getD j 0

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

def mirrorSteps : List Move := [swapRows 50,swapRows 84]

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

noncomputable def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,apools g,links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ p ∈ apools g, ValidPool true (roots g) (target g) p) ∧
    (∀ a ∈ first g, faithful r s a) ∧
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
        exact decode_faithful _ _ _ _ _ ready.2.2.1 _ ((selectLive_sub _ _).subset ha)
      · exact ready.2.1
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
      exact poolCut_sound (ready.2.2.2 k i hi hn) _ he h.1.1 hc

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

noncomputable def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_44276

namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3ffff01ffffc183fffff07ffc1ffc01f3f3fc
  | 2 => 0xfc0ffffe07fffffc0fc1ff87ffe1fffe8c7c7f
  | 3 => 0xfff03ffff81ffffff001fff87ffe1fff0f8f8f
  | 4 => 0x3fffffe001fffffe00007fffe007f00ff0
  | 5 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9861811c51448200b2c270089c02243031b1bc
  | 2 => 0x29221224320910940550948525214952845455
  | 3 => 0x5084a44880d22129502129504a5412a50a8a8a
  | 4 => 0x62cb38912483b5ce69b40c44739980c7d00f60
  | 5 => 0x830c30e1c71c39f38e39ce6603110307ef6000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000fcccfcc0fcc0f000, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x87ffff0ffffc1ff83ffe0fffc1fffc1f9cf3cf
  | 2 => 0xf8783ff0f07fe1ffc707f0f0fe1e1fe3eb4d33
  | 3 => 0xff803fff007ffe1ff807ff00ffe01ffc738e3c
  | 4 => 0x3fffff80001ffff80000ffffe0007c0fc0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80000100000020000008011000220400001045
  | 2 => 0x1212522244a90309434290a252144943294512
  | 3 => 0x2124a4442952103298852a04a5409298528a28
  | 4 => 0x7557388aac1b555cedd18888f999c0c97c0f80
  | 5 => 0x466630ecce63999f36e7ccce311103127fe000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0faaafaaafaaafaa0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfc3ffff87ffffff03f0fe1fff87ffffe88f1ff
  | 1 => 0x7fc1f0ff83e1f0ffc7f0fe1c3f870e1f774e93
  | 3 => 0x7ffe00fffc01ff1ff800ffe03ff80fe1878f1c
  | 4 => 0x800000fffffe001fffff00003ffff001f80fe0
  | 5 => 0xffffff000000001fffffffffc0000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4000008000000000001002400090200001025
  | 1 => 0x89461111942a102c31062089882245c334692
  | 3 => 0x510caaa228d548355888b5412d5049c5858b18
  | 4 => 0x43a94cc452906a59adaa11023664e089d80dc0
  | 5 => 0x6231888763198c9e36ccd99384408111eee000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeaaaa88eeeeeeaaeeaaaa88eeeeeeaaeeaaaa88eeeeeeaaeeaaaa88eeeeeeaaeeaaaa88eeeeeeaaeeaaaa88eeeeeeaaeeaaaa88eeeeeeaaeeaaaa88, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfc3ffff87ffffff03f0fe1fff87ffffe88f1ff
  | 1 => 0x7fc1f0ff83e1f0ffc7f0fe1c3f870e1f774e93
  | 2 => 0x7ffe00fffc01ff1ff800ffe03ff80fe1878f1c
  | 4 => 0x800000fffffe001fffff00003ffff001f80fe0
  | 5 => 0xffffff000000001fffffffffc0000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4000008000000000001002400090200001025
  | 1 => 0x89461111942a102c31062089882245c334692
  | 2 => 0x510caaa228d548355888b5412d5049c5858b18
  | 4 => 0x43a94cc452906a59adaa11023664e089d80dc0
  | 5 => 0x6231888763198c9e36ccd99384408111eee000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8eeeeeaeaeaeaa8a8, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf1fe3fffc3e3fffe0c71f8fff1c1fffe08f0ff
  | 1 => 0xfe1fc3e3fc03c78ff07e3f1c3e01c71e774c93
  | 2 => 0x1ffc03fffc07f1ff803fe03ffe07e1878f1c
  | 3 => 0xffe00003fffff801ffffc0003ffff801f80fe0
  | 5 => 0xfffffffc00000001ffffffffc0000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x10020000400400000000402400404100001025
  | 1 => 0x24c498c488c98b1070321908b20c925c334c92
  | 2 => 0xd0809491140940294802a41149404c4858518
  | 3 => 0x4041a292228201252954800229293009580ac0
  | 5 => 0x899133003b132649ce69349380302091eee000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfeeafeeafaa8faa8feeafeeafaa8faa8feeafeeafaa8faa8feeafeeafaa8faa8feeafeeafaa8faa8feeafeeafaa8faa8feeafeeafaa8faa8feeafeeafaa8faa8, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf1fe3fffc3e3fffe0c71f8fff1c1fffe08f0ff
  | 1 => 0xfe1fc3e3fc03c78ff07e3f1c3e01c71e774c93
  | 2 => 0x1ffc03fffc07f1ff803fe03ffe07e1878f1c
  | 3 => 0xffe00003fffff801ffffc0003ffff801f80fe0
  | 4 => 0xfffffffc00000001ffffffffc0000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x10020000400400000000402400404100001025
  | 1 => 0x24c498c488c98b1070321908b20c925c334c92
  | 2 => 0xd0809491140940294802a41149404c4858518
  | 3 => 0x4041a292228201252954800229293009580ac0
  | 4 => 0x899133003b132649ce69349380302091eee000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfeeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8feeafaa8, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q0K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q0K3 : Nat → Nat
  | 0 => 0x46020a80ef995d32be6374c6f185c30
  | _ => 0
def q0K2 : Nat → Nat
  | 0 => 0x11003009541cca350b318d420c2550430
  | _ => 0
def q0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q0K4 (i*4) 4
  | 3 => packedAt q0K3 (i*15) 15
  | 2 => packedAt q0K2 (i*26) 26
  | _ => 0
def q0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q0K4 (5+((h/1+packedAt q0K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q0K3 (96+((h/2+packedAt q0K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt q0K2 (108+((h/1+packedAt q0K2 (104+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def q0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q0Atlas : Atlas := ⟨4,rawDecor 46 q0Pos q0Neg, 0xfcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0, q0N, q0R, (fun _ _ => 0), q0I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q1K3 : Nat → Nat
  | 0 => 0x80462a62f995d32be6374c6f185c30
  | _ => 0
def q1K2 : Nat → Nat
  | 0 => 0x1a20009541cca350b318d420c2550430
  | _ => 0
def q1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q1K4 (i*4) 4
  | 3 => packedAt q1K3 (i*15) 15
  | 2 => packedAt q1K2 (i*26) 26
  | _ => 0
def q1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q1K4 (5+((h/1+packedAt q1K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q1K3 (96+((h/2+packedAt q1K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt q1K2 (107+((h/1+packedAt q1K2 (104+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def q1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def q1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def q1Atlas : Atlas := ⟨4,rawDecor 45 q1Pos q1Neg, 0xfaaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0faaafaaafaa0faa0, q1N, q1R, (fun _ _ => 0), q1I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q2K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q2K4 : Nat → Nat
  | 0 => 0xa00281e00090698089a00e100b2a01260000802e010a0001601470c0010000800cefe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def q2K3 : Nat → Nat
  | 0 => 0x1a7cd091c184013c3029c426cc240098a0224740000601100002cba54001180324479320002002c00a87142c01006c00520040033ad90732b541ccad90632b5418cb34c832ae42cc6b50b31ae428c6b50a31d5310c6790f219d43c86790e219d43887948421af424c2b10930b7414c2d10530ae420c2b50830b6410c2d504309f43482710d20b741482d105209e43082750c20b641082d504209f43442710d10af42442b109109e43042750c10ae42042b50810
  | _ => 0
def q2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q2K5 (i*4) 4
  | 4 => packedAt q2K4 (i*15) 15
  | 3 => packedAt q2K3 (i*26) 26
  | _ => 0
def q2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt q2K5 (5+((h/1+packedAt q2K5 (4+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt q2K4 (408+((h/8+packedAt q2K4 (360+(h % 8)*6) 6) % 38)*6) 6
  | 3 => packedAt q2K3 (1092+((h/13+packedAt q2K3 (1014+(h % 13)*6) 6) % 49)*7) 7
  | _ => 0
def q2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 4 => 0xe6ff07cff81f8f1c
  | 5 => 0xf8fff80fffe00fe0
  | _ => 0
def q2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 4 => 0x1942d41a90932b18
  | 5 => 0x78486ad24c24dc0
  | _ => 0
def q2Atlas : Atlas := ⟨5,rawDecor 51 q2Pos q2Neg, 0xeeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888, q2N, q2R, (fun _ _ => 0), q2I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q3K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q3K3 : Nat → Nat
  | 0 => 0x2010829800016f995d32be6374c6f185c30
  | _ => 0
def q3K2 : Nat → Nat
  | 0 => 0xc220009541cca350b318d420c2550430
  | _ => 0
def q3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q3K4 (i*4) 4
  | 3 => packedAt q3K3 (i*15) 15
  | 2 => packedAt q3K2 (i*26) 26
  | _ => 0
def q3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q3K4 (5+((h/1+packedAt q3K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q3K3 (98+((h/2+packedAt q3K3 (90+(h % 2)*4) 4) % 11)*4) 4
  | 2 => packedAt q3K2 (107+((h/1+packedAt q3K2 (104+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def q3Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q3Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q3Atlas : Atlas := ⟨4,rawDecor 30 q3Pos q3Neg, 0xfcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0fcccfcc0, q3N, q3R, (fun _ _ => 0), q3I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q4K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q4K4 : Nat → Nat
  | 0 => 0x70400002a600000a10012b2e69458000000280090078698c88000e20a000100004040fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def q4K3 : Nat → Nat
  | 0 => 0xb000000000002c023000c0060090018000001a0000ca53e40001043ca9e006cba11a50612008028910887073875304220001314000000000100938030d1000020ad90732b541ccad90632b5418cb34c832ae42cc6b50b31ae428c6b50a31d5310c6790f219d43c86790e219d43887948421af424c2b10930b7414c2d10530ae420c2b50830b6410c2d504309f43482710d20b741482d105209e43082750c20b641082d504209f43442710d10af42442b109109e43042750c10ae42042b50810
  | _ => 0
def q4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q4K5 (i*4) 4
  | 4 => packedAt q4K4 (i*15) 15
  | 3 => packedAt q4K3 (i*26) 26
  | _ => 0
def q4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt q4K5 (5+((h/1+packedAt q4K5 (4+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt q4K4 (408+((h/8+packedAt q4K4 (360+(h % 8)*6) 6) % 38)*6) 6
  | 3 => packedAt q4K3 (1092+((h/13+packedAt q4K3 (1014+(h % 13)*6) 6) % 64)*7) 7
  | _ => 0
def q4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 3 => 0xe6ff07cff81f8f1c
  | 5 => 0xf8fff80fffe00fe0
  | _ => 0
def q4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 3 => 0x1942d41a90932b18
  | 5 => 0x78486ad24c24dc0
  | _ => 0
def q4Atlas : Atlas := ⟨5,rawDecor 43 q4Pos q4Neg, 0xeeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88, q4N, q4R, (fun _ _ => 0), q4I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q5K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q5K3 : Nat → Nat
  | 0 => 0x120028009802f985d30de41b483b887510
  | _ => 0
def q5K2 : Nat → Nat
  | 0 => 0x14324c120d130443848110
  | _ => 0
def q5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q5K4 (i*4) 4
  | 3 => packedAt q5K3 (i*15) 15
  | 2 => packedAt q5K2 (i*26) 26
  | _ => 0
def q5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q5K4 (5+((h/1+packedAt q5K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q5K3 (98+((h/2+packedAt q5K3 (90+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt q5K2 (80+((h/1+packedAt q5K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def q5Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 3 => 0xbf333e3ba0da
  | 4 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q5Neg : Nat → Bits
  | 0 => 0x0
  | 3 => 0x42444211044a
  | 4 => 0x241814820914
  | 5 => 0x1801a92012a0
  | _ => 0
def q5Atlas : Atlas := ⟨4,rawDecor 57 q5Pos q5Neg, 0xffffffaaffaaaaaaffffffaaffaaaaaaffffffaaffaaaaaaffffffaaffaaaaaaffffffaaffaaaaaaffffffaaffaaaaaaffffffaaffaaaaaaffffffaaffaaaaaa, q5N, q5R, (fun _ _ => 0), q5I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q6K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q6K3 : Nat → Nat
  | 0 => 0x10a801820002f995d32be6374c6f185c30
  | _ => 0
def q6K2 : Nat → Nat
  | 0 => 0x10c209541cca350b318d420c2550430
  | _ => 0
def q6N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q6R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q6K4 (i*4) 4
  | 3 => packedAt q6K3 (i*15) 15
  | 2 => packedAt q6K2 (i*26) 26
  | _ => 0
def q6I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q6K4 (5+((h/1+packedAt q6K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q6K3 (98+((h/2+packedAt q6K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt q6K2 (107+((h/1+packedAt q6K2 (104+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def q6Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def q6Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def q6Atlas : Atlas := ⟨4,rawDecor 29 q6Pos q6Neg, 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0, q6N, q6R, (fun _ _ => 0), q6I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q7K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q7K3 : Nat → Nat
  | 0 => 0x40020a8606f185c30dc41b083b087410
  | _ => 0
def q7K2 : Nat → Nat
  | 0 => 0x8100320c020d030043808010
  | _ => 0
def q7N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q7R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q7K4 (i*4) 4
  | 3 => packedAt q7K3 (i*15) 15
  | 2 => packedAt q7K2 (i*26) 26
  | _ => 0
def q7I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q7K4 (5+((h/1+packedAt q7K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q7K3 (96+((h/2+packedAt q7K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt q7K2 (81+((h/1+packedAt q7K2 (78+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def q7Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 4 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q7Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 3 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 4 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q7Atlas : Atlas := ⟨4,rawDecor 58 q7Pos q7Neg, 0xcccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000cccccc00cc000000, q7N, q7R, (fun _ _ => 0), q7I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q8K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q8K3 : Nat → Nat
  | 0 => 0x2a10188000af985d30de41b483b887510
  | _ => 0
def q8K2 : Nat → Nat
  | 0 => 0x22324c120d130443848110
  | _ => 0
def q8N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q8R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q8K4 (i*4) 4
  | 3 => packedAt q8K3 (i*15) 15
  | 2 => packedAt q8K2 (i*26) 26
  | _ => 0
def q8I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q8K4 (5+((h/1+packedAt q8K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q8K3 (98+((h/2+packedAt q8K3 (90+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt q8K2 (80+((h/1+packedAt q8K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def q8Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 1 => 0xbf333e3ba0da
  | 2 => 0xdfc3cfc3c31c
  | 3 => 0xeffc0ffc03e0
  | _ => 0
def q8Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x42444211044a
  | 2 => 0x241814820914
  | 3 => 0x1801a92012a0
  | _ => 0
def q8Atlas : Atlas := ⟨4,rawDecor 15 q8Pos q8Neg, 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea, q8N, q8R, (fun _ _ => 0), q8I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q9K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q9K4 : Nat → Nat
  | 0 => 0x400280980b9a08c116524392a1872a00802018089e000b002800213c04fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def q9K3 : Nat → Nat
  | 0 => 0x4200c014868a9b000001400353002210009003c01c001c3131808f1d2c0040b0a888200039299145c000060119f240c00050003c00c110052d90732b541ccad90632b5418cb34c832ae42cc6b50b31ae428c6b50a31d5310c6790f219d43c86790e219d43887948421af424c2b10930b7414c2d10530ae420c2b50830b6410c2d504309f43482710d20b741482d105209e43082750c20b641082d504209f43442710d10af42442b109109e43042750c10ae42042b50810
  | _ => 0
def q9N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q9R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q9K5 (i*4) 4
  | 4 => packedAt q9K4 (i*15) 15
  | 3 => packedAt q9K3 (i*26) 26
  | _ => 0
def q9I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt q9K5 (5+((h/1+packedAt q9K5 (4+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt q9K4 (400+((h/8+packedAt q9K4 (360+(h % 8)*5) 5) % 32)*6) 6
  | 3 => packedAt q9K3 (1092+((h/13+packedAt q9K3 (1014+(h % 13)*6) 6) % 58)*7) 7
  | _ => 0
def q9Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 3 => 0xe6ff07cff81f8f1c
  | 4 => 0xf8fff80fffe00fe0
  | _ => 0
def q9Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 3 => 0x1942d41a90932b18
  | 4 => 0x78486ad24c24dc0
  | _ => 0
def q9Atlas : Atlas := ⟨5,rawDecor 27 q9Pos q9Neg, 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88, q9N, q9R, (fun _ _ => 0), q9I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q10K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q10K3 : Nat → Nat
  | 0 => 0x6a42000842f985d30de41b483b887510
  | _ => 0
def q10K2 : Nat → Nat
  | 0 => 0x200004324c120d130443848110
  | _ => 0
def q10N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q10R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q10K4 (i*4) 4
  | 3 => packedAt q10K3 (i*15) 15
  | 2 => packedAt q10K2 (i*26) 26
  | _ => 0
def q10I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q10K4 (5+((h/1+packedAt q10K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q10K3 (96+((h/2+packedAt q10K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt q10K2 (81+((h/1+packedAt q10K2 (78+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def q10Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 2 => 0xbf333e3ba0da
  | 3 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q10Neg : Nat → Bits
  | 0 => 0x0
  | 2 => 0x42444211044a
  | 3 => 0x241814820914
  | 5 => 0x1801a92012a0
  | _ => 0
def q10Atlas : Atlas := ⟨4,rawDecor 45 q10Pos q10Neg, 0xfffafffafaaafaaafffafffafaaafaaafffafffafaaafaaafffafffafaaafaaafffafffafaaafaaafffafffafaaafaaafffafffafaaafaaafffafffafaaafaaa, q10N, q10R, (fun _ _ => 0), q10I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q11K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q11K3 : Nat → Nat
  | 0 => 0x41000030000207b30bc6170c3c185830
  | _ => 0
def q11K2 : Nat → Nat
  | 0 => 0x2690230
  | _ => 0
def q11N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def q11R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q11K4 (i*4) 4
  | 3 => packedAt q11K3 (i*15) 15
  | 2 => packedAt q11K2 (i*26) 26
  | _ => 0
def q11I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q11K4 (5+((h/1+packedAt q11K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q11K3 (79+((h/1+packedAt q11K3 (75+(h % 1)*4) 4) % 13)*4) 4
  | 2 => packedAt q11K2 (27+((h/1+packedAt q11K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q11Pos : Nat → Bits
  | 1 => 0xbbc3ff3e3fe03fc
  | 2 => 0xfffffffffffffffffffffffdffc7fffc7ffc7f
  | 3 => 0xfffffffffffffffffffffffefff8ffff8fff8f
  | 5 => 0xf3fff03fff00ff0
  | _ => 0
def q11Neg : Nat → Bits
  | 1 => 0x4479224e09261bc
  | 2 => 0xfffffffffffffffffffffff208b0412424a455
  | 3 => 0x111068249094a8a
  | 5 => 0xe224eb92418f60
  | _ => 0
def q11Atlas : Atlas := ⟨4,rawDecor 46 q11Pos q11Neg, 0xfcc0fcc0f000f000fcc0fcc0f000f000fcc0fcc0f000f000fcc0fcc0f000f000fcc0fcc0f000f000fcc0fcc0f000f000fcc0fcc0f000f000fcc0fcc0f000f000, q11N, q11R, (fun _ _ => 0), q11I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q12K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q12K5 : Nat → Nat
  | 0 => 0xc3a411482c7aea0000649661a408026280080a807008800100032c62fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def q12K4 : Nat → Nat
  | 0 => 0x208020000a100100c2407000381000048001000000100205010045c01000040205248000000000180408be41ccaf50732be40ccaf50332bd438caf90a32df328cbbcca32be418caf50632be408caf50232ef324cb78c932bf414caf10532bf404caf10132be430caf90832df320cbb8c832dd320cbb4c832cd320caf90432f6410cad90432bd410cbd50432b5410caf90032fa400cae90032bd400cbe50032b9400caf90b31bd42cc77ccb31dd32cc6f90331bd40cc6f50e31be428c6f50a31be418c77cc631f7318c6f90231bd408c6fd0931bc424c77cc931dd324c7dcc531de314c6fd0131bc404c6f90c31be420c7b90831ae420c6f50831ed420c6b50831be410c77cc431f6310c774c431f5310c754c431be400c7e90031ba400c6f50031f9400c6e50031bf43c86f90f21bd43c86f10f21ee32c87b4cb21be40c86f50321bf43886f90e21bd43886f10e21bd42886f90621f631887d4c621ef21887dc8621be40886f50221bf43486f90d21bd43486f10d21ee32487b4c921f631487d4c521f721487b88521bf40486f10121bf43086f90c21de43086790c21bd43087750c219d43086f10c21be42086f90421ef21087d88421ed21087d48421e521086f90021fa40086e90021bd40087e50021b940086f90b30bd42cc37ccb30dd32cc2f90730bd41cc37cc730dd31cc2f50e30be428c2f50a30be418c2f50630be408c37cc230fb308c2fd0930bc424c37cc930dd324c2fd0530bc414c37cc530dd314c3ecc130de304c2f90c30be420c3b90830ae420c2f50830ed420c2b50830be410c3d90430b6410c2f50430f5410c2d50430be400c37cc030fa300c374c030f9300c364c030bf43c82f90f20bd43c82f10f20ee32c83b4cb20be41c82f50720ef21c83b48720bf43882f90e20bd43882f10e20bd42882f90620bd41882f90220fa30883e4c220ef20883ec8220bf43482f90d20bd43482f10d20ee32483b4c920bf41482f10520ef21483b48520fa30483e4c120fb20483b88120bf43082f90c20de43082790c20bd43083750c209d43082f10c20be42082f90420f641082d90420bd41083d50420b541082f90020ef20083e88020ed20083e48020e920082fd0f10be43c42f50f10bc43c42fd0b10be42c42f50b10bc42c43d8c710f531c43d88710f521c42fd0e10be43842f50e10bc43842fd0a10be42842f50a10bc42842f50610be40843e8c210f930843e88210f920843dc4210fb10842fd0d10be43442f50d10bc43442fd0910be42442f50910bc42443d8c510f531443d88510f521443e8c110f930443e88110f920443ec4110f610442fd0c10be43043790c109e43042f50c10dd43042750c10bc43042fd0810be42043b90810ae42042f50810ed42042b50810bc42042f90410be40043dc4010fa10043d44010f910043c44010
  | 1 => 0x1b2000fe00000588f03600000224000000019a000227a800000000024a439de6f9b0398000480000238818007a250000005b92e0000053888471043290000000000002b000028f650062001c87680008006369ae430103800013060178b4211ba2c9a634258279ce4a82e2e92c009ec20a545b20c6189819a3c3f1965d00035004349f8671d03883a6797c002082303c149c21b0a06a9362a2340308e8c00000000912140000061236151020c0002a9082695a7da3e581ac661326d910000fa0214c8c9dc60a161c8f4371186e1541d01a748927ea0488056639ca4e1226484273194219565f8de2714888a0a7d2121f20e4a0a40603230a1a5700e5488a7103e5e02c29896620be118a27f0c0719e65d9bc168cc7c9a0931d83921e5122c480bc1a8d63aa520013a1a000001b4058000d80047a1c1422e9224e96800000001d8e80010a45000001e07587e84000000ec0004a630000002a2406e701f00780031800000f833800112020000000000101426914a86200628f20013c60000001d4001a25a8008e800001720000000000000000005846a2a64242190000000059170002264c094598009004e2d9680d0788a1502b934170b81e9e2000807f828958b041800001465e9120000009000000c83b8141201c560380013e7924631116001ee57800000006a126000700012409800000000080002000200c0e030c8040600010080200008200a0a008000c0801800401c028040e00000300e010080022050500808000183c0a0600038001304000040502068300102940
  | _ => 0
def q12K3 : Nat → Nat
  | 0 => 0x63b13150031c898a8018ce94043c8672a021e438c434cb219d2808710ce54043887288698c433b5050d219c2828690ce9404348672a021a432c544c921c621a6490d91453248668a898a4394434c521b22926290f14c9314863ca6202431d53101219d2868610ce543430863aa9218431e5310c21972908610cd9444308674a021843395010c21c6a1e4210e550e21086caa5108432f5448421c6a1a4210cdd51210872a8690843675448421d3aa24210e9d0d210878c8690843a54348421e2a1a4210e150d21087348720043994390021f090c8010e9485400873486a0043994350021f090a8010eac85400876442a0043a92150021d890a8010e8485400866ca221261355110930c6212649856141324c25ca420a612d5210530ca20a629856141314c34c8520861a54290430d3212821869509410c31a85980619541cc030aca9c60186a50a300c36283180611f544c030c6a12601865505300c276a898061a9424c030d8a0a601856d51300c336a898061ca424c030cca12601872509300c3128498061d2414c030cca0a601874505300c3228298061365110f209aa8887906310d32c826ca221c41355110e20cc21a61104dd454348268a2a1a41365110d209aa8886904b1513248318869924168504c9208f29882904754c41483488290a416850485209c2a260906610d30482d0a498241c9324c1209b28e86104d547430823aa9218411e5310c209729086104d944430826aa2218413a5010c20cb21c82106550e410832c86a0841954350420c6a1e40106950720083328710041695288020d8a0c40104bd51200831a8690041a541480209daa240106650d200836282900416b5448020d5aa240106ad0d20083948690041a94348020e4a1a40106250d20083c48290041a94148020f0a0a401068505200825ca421e212d5210f108f29885884754c42c43288698e21a442487109729087084b548438423ca6214211d5310a10cc21a61086a109208425ea4a1a212c5250d109729086884b548434423ea6a12211c53509108f29884884754c4244268a898a2194434c510b828262884d15121443488490a217050485109c2a260886610d30442e0a298221d1314c1109c2a240886a10920442e0a290221e121481109729686084b54b430423aa9218211e5310c109729086084b548430426ca2218213a5010c108f29e84084754f420425aa9210218e4390810c6a1c84086390d420431a86a10211e53108108ea9884084b948420426ca2210213a5010810caa1e20086950b1004272a908021994384010d4a1420085c546100426ea888021954344010d2a1220084ed5110043328688021a94244010b9aa220086cd5110043668688021d24344010d8a1a20087450d10043228688021b34244010f121220086c50910043c28488021a14244010
  | 1 => 0x491dc6309866224720e2868000c1aa6297600000000c40000079800328000015c2b8001a9f6548524a8bc0904c0013e3b8004c8b06d800000000010400000409260000062000000004183a618407b0001f0000000000800000c64b20c1a2203605a73992728000009484058271d200086398b20986c801b2598003f0c86995e7614200000000000016800000001102280017014079ea00000000003780a4d800150ec810d6292086d0d01c9d46e9001e04436800610002d0005602a2b0000016a8b0006b800528005d0640190a0f8004d0000016e468f46401c1da187780010800001c485800000a00019c53060690002da120000053800568800017c288000000044800000007f000001160000000000791ee0694600000238f80b8368a1807c9f04200068800000005e88c6e154000005b000000f6000000004e00000000000018e5e00000000198104380089a0e00000521fe47000001da870e40003460804001cc33800179f400150000007a000001f86f0be001220009068000000005000000000580000020600082001d605800000ea2200e0019a6500043000889c67893c000a83091870084000008a8004b9e05c13a2487425964000701884a3c00c00162478322a8cc5c80000000088182e1d0558506582c1200045000000000009e001b04e046021a84a144002020a0fe26838000000006e481fa0f0563800000000000000017e08000000e8001c2678123707e300ba1e9be878004c0002980000214828fa6b0d4348f20201408060300800070401004010080402000000412010000404000100000000080400000080006080281c00000080c0001000141801018000c00000000004000180400000000808000000008010000400008200200000101002018040006000000e02020000a0400ce940414ca72a020a653651101329aa8880995354e320ca3ea8990652f544c832a7aa2641963d51320cb8a65208658d3250432e2992821965cc9410cb4c64a0865953250432d29928219614c9410cb926520065b24190032d8a0c8019634c9400cb9264a0065b24150032d8a0a801966cc9400cb5464a0065993250032d49928019624c9400ca74a021263395010931c62126498d5145324c65ca4202632d5210131c6a166218d554e310c74a85188631f544c431c6a126218cdd51310c74a849886357544c431cbaa26218f1909310c72a8498863c5424c431c2a126218ea90a400c7528520063d13190031ca98a8018ea909400c75284a0063d13150031cd98a8018ec8c5400c73262a
  | _ => 0
def q12K2 : Nat → Nat
  | 0 => 0x148a001c00061e9918968405818287008010950d1100000100101a820300160000000d9d80000c00069a1d141c8020800a928e00051b9f89099e0f0003801304939791881b1820078017120e8c8008801f198b0f8b95800613000800412101000e4860204200900430200e04c94190032e04ca4150032e04c94150032a2580424c93194580514c931e05093190031e09093150031e05093150031a2580434cb21a4580434c621a2580434c92198580514c921a4580434c52198580524c521a1191324c521c1151324c521a85834348421a15924348421e050d2190021e090d2150021e050d2150021a1584424c93094584504c930a1588414c53092588504c530e050a414c030e0909414c030e0509414c030a1584434cb20a4584434c220a1584434c92098584504c920a158c41485209258c5048520a4584434c12098584524c120a2191324c120c2151324c120a85874348020a25924348020e050e4148020e090d4148020e050d4148020a1588434c710a158c4248710a2588434c210a258c4248210a1588434c51098588504c510a158c42485109458c5048510a2588434c11098588514c110a4191314c110c4151314c110a258c42481109458c5148110a81912148110c81512148110a858b4344010a45924344010a458f4244010a85924244010e050e4244010e090d4244010e050d4244010
  | _ => 0
def q12N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def q12R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt q12K6 (i*4) 4
  | 5 => packedAt q12K5 (i*15) 15
  | 4 => packedAt q12K4 (i*26) 26
  | 3 => packedAt q12K3 (i*37) 37
  | 2 => packedAt q12K2 (i*48) 48
  | _ => 0
def q12I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt q12K6 (5+((h/1+packedAt q12K6 (4+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt q12K5 (400+((h/8+packedAt q12K5 (360+(h % 8)*5) 5) % 32)*6) 6
  | 4 => packedAt q12K4 (8752+((h/100+packedAt q12K4 (7852+(h % 100)*9) 9) % 401)*10) 10
  | 3 => packedAt q12K3 (11160+((h/93+packedAt q12K3 (10323+(h % 93)*9) 9) % 443)*10) 10
  | 2 => packedAt q12K2 (3322+((h/22+packedAt q12K2 (3168+(h % 22)*7) 7) % 88)*8) 8
  | _ => 0
def q12Pos : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffdfd273c777b0cf
  | 3 => 0xffffffffffffffffffffffffefe39cf87bd333
  | 4 => 0x77fc1f3f83ec3c
  | 5 => 0x7bffe03ffc0fc0
  | _ => 0
def q12Neg : Nat → Bits
  | 2 => 0xffffffffffffffffffffffffa0448401108045
  | 3 => 0x10882108210112
  | 4 => 0x9014052020428
  | 5 => 0x6000aa4400a80
  | _ => 0
def q12Atlas : Atlas := ⟨6,rawDecor 60 q12Pos q12Neg, 0xfffffff0fff0f000fffffff0fff0f000fffffff0fff0f000fffffff0fff0f000fffffff0fff0f000fffffff0fff0f000fffffff0fff0f000fffffff0fff0f000, q12N, q12R, (fun _ _ => 0), q12I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q13K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q13K4 : Nat → Nat
  | 0 => 0x28000400300b9200051600002008001c3a61a4aa26ac00001e10829804110d0c0080fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def q13K3 : Nat → Nat
  | 0 => 0x3c584923e1cc260c310800a2001a0000e9404011000600e001e640011c00b934828aa32080580226c2251a0d100848c20200614446d90732b541ccad90632b5418cb34c832ae42cc6b50b31ae428c6b50a31d5310c6790f219d43c86790e219d43887948421af424c2b10930b7414c2d10530ae420c2b50830b6410c2d504309f43482710d20b741482d105209e43082750c20b641082d504209f43442710d10af42442b109109e43042750c10ae42042b50810
  | _ => 0
def q13N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q13R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q13K5 (i*4) 4
  | 4 => packedAt q13K4 (i*15) 15
  | 3 => packedAt q13K3 (i*26) 26
  | _ => 0
def q13I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt q13K5 (5+((h/1+packedAt q13K5 (4+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt q13K4 (408+((h/8+packedAt q13K4 (360+(h % 8)*6) 6) % 38)*6) 6
  | 3 => packedAt q13K3 (1092+((h/13+packedAt q13K3 (1014+(h % 13)*6) 6) % 49)*7) 7
  | _ => 0
def q13Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 2 => 0xe6ff07cff81f8f1c
  | 5 => 0xf8fff80fffe00fe0
  | _ => 0
def q13Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 2 => 0x1942d41a90932b18
  | 5 => 0x78486ad24c24dc0
  | _ => 0
def q13Atlas : Atlas := ⟨5,rawDecor 39 q13Pos q13Neg, 0xeaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8, q13N, q13R, (fun _ _ => 0), q13I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q14K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q14K3 : Nat → Nat
  | 0 => 0x2080101a80007b18f531ec43d487b087410
  | _ => 0
def q14K2 : Nat → Nat
  | 0 => 0x4580000a5428c6550e219543042950810
  | _ => 0
def q14N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def q14R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q14K4 (i*4) 4
  | 3 => packedAt q14K3 (i*15) 15
  | 2 => packedAt q14K2 (i*26) 26
  | _ => 0
def q14I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q14K4 (5+((h/1+packedAt q14K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q14K3 (98+((h/2+packedAt q14K3 (90+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt q14K2 (107+((h/1+packedAt q14K2 (104+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def q14Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff73ffc71fff0ff
  | 1 => 0xffffffffffffffffffffffeaf8333f81ce7c93
  | 2 => 0x73ffc3cffe0f8f1c
  | 3 => 0x7cfffc0ffff00fe0
  | _ => 0
def q14Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010400010420025
  | 1 => 0x1526a64c8ca56c92
  | 2 => 0xc42281524092518
  | 3 => 0x38402aa49204ac0
  | _ => 0
def q14Atlas : Atlas := ⟨4,rawDecor 15 q14Pos q14Neg, 0xfaa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8, q14N, q14R, (fun _ _ => 0), q14I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q15K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q15K3 : Nat → Nat
  | 0 => 0x2a10188000af985d30de41b483b887510
  | _ => 0
def q15K2 : Nat → Nat
  | 0 => 0x22324c120d130443848110
  | _ => 0
def q15N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q15R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q15K4 (i*4) 4
  | 3 => packedAt q15K3 (i*15) 15
  | 2 => packedAt q15K2 (i*26) 26
  | _ => 0
def q15I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q15K4 (5+((h/1+packedAt q15K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q15K3 (98+((h/2+packedAt q15K3 (90+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt q15K2 (80+((h/1+packedAt q15K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def q15Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 1 => 0xbf333e3ba0da
  | 2 => 0xdfc3cfc3c31c
  | 3 => 0xeffc0ffc03e0
  | _ => 0
def q15Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x42444211044a
  | 2 => 0x241814820914
  | 3 => 0x1801a92012a0
  | _ => 0
def q15Atlas : Atlas := ⟨4,rawDecor 15 q15Pos q15Neg, 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea, q15N, q15R, (fun _ _ => 0), q15I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q16K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q16K3 : Nat → Nat
  | 0 => 0x80402a0612f185c30dc41b083b087410
  | _ => 0
def q16K2 : Nat → Nat
  | 0 => 0x200020320c020d030043808010
  | _ => 0
def q16N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q16R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q16K4 (i*4) 4
  | 3 => packedAt q16K3 (i*15) 15
  | 2 => packedAt q16K2 (i*26) 26
  | _ => 0
def q16I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q16K4 (5+((h/1+packedAt q16K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q16K3 (96+((h/2+packedAt q16K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt q16K2 (81+((h/1+packedAt q16K2 (78+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def q16Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 4 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def q16Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffff012222c444db
  | 2 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 4 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def q16Atlas : Atlas := ⟨4,rawDecor 54 q16Pos q16Neg, 0xccccc0c0c0c00000ccccc0c0c0c00000ccccc0c0c0c00000ccccc0c0c0c00000ccccc0c0c0c00000ccccc0c0c0c00000ccccc0c0c0c00000ccccc0c0c0c00000, q16N, q16R, (fun _ _ => 0), q16I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q17K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q17N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def q17R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q17K3 (i*4) 4
  | _ => 0
def q17I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt q17K3 (5+((h/1+packedAt q17K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q17Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 2 => 0xbf333e3ba0da
  | 4 => 0xdfc3cfc3c31c
  | 5 => 0xeffc0ffc03e0
  | _ => 0
def q17Neg : Nat → Bits
  | 0 => 0x0
  | 2 => 0x42444211044a
  | 4 => 0x241814820914
  | 5 => 0x1801a92012a0
  | _ => 0
def q17Atlas : Atlas := ⟨3,rawDecor 53 q17Pos q17Neg, 0xfffffafafafaaaaafffffafafafaaaaafffffafafafaaaaafffffafafafaaaaafffffafafafaaaaafffffafafafaaaaafffffafafafaaaaafffffafafafaaaaa, q17N, q17R, (fun _ _ => 0), q17I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q18K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q18K2 : Nat → Nat
  | 0 => 0x5830
  | _ => 0
def q18N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | 2 => 1
  | _ => 0
def q18R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt q18K3 (i*4) 4
  | 2 => packedAt q18K2 (i*15) 15
  | _ => 0
def q18I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt q18K3 (5+((h/1+packedAt q18K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | 2 => packedAt q18K2 (16+((h/1+packedAt q18K2 (15+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def q18Pos : Nat → Bits
  | 1 => 0xbbc3ff3e3fe03fc
  | 2 => 0xfffffffffffffffffffffffdffc7fffc7ffc7f
  | 3 => 0xfffffffffffffffffffffffefff8ffff8fff8f
  | 4 => 0xf3fff03fff00ff0
  | _ => 0
def q18Neg : Nat → Bits
  | 1 => 0x4479224e09261bc
  | 2 => 0xfffffffffffffffffffffff208b0412424a455
  | 3 => 0x111068249094a8a
  | 4 => 0xe224eb92418f60
  | _ => 0
def q18Atlas : Atlas := ⟨3,rawDecor 30 q18Pos q18Neg, 0xfcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000fcc0f000, q18N, q18R, (fun _ _ => 0), q18I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q19K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q19K3 : Nat → Nat
  | 0 => 0x1a82100080016f985d30de41b483b887510
  | _ => 0
def q19K2 : Nat → Nat
  | 0 => 0x84324c120d130443848110
  | _ => 0
def q19N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def q19R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt q19K4 (i*4) 4
  | 3 => packedAt q19K3 (i*15) 15
  | 2 => packedAt q19K2 (i*26) 26
  | _ => 0
def q19I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt q19K4 (5+((h/1+packedAt q19K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt q19K3 (98+((h/2+packedAt q19K3 (90+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt q19K2 (80+((h/1+packedAt q19K2 (78+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def q19Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffffffeaef1b77c27
  | 2 => 0xbf333e3ba0da
  | 3 => 0xdfc3cfc3c31c
  | 4 => 0xeffc0ffc03e0
  | _ => 0
def q19Neg : Nat → Bits
  | 0 => 0x0
  | 2 => 0x42444211044a
  | 3 => 0x241814820914
  | 4 => 0x1801a92012a0
  | _ => 0
def q19Atlas : Atlas := ⟨4,rawDecor 29 q19Pos q19Neg, 0xfffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaafffafaaa, q19N, q19R, (fun _ _ => 0), q19I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def q20K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def q20K4 : Nat → Nat
  | 0 => 0xc8aa38098040000002e7160ac11251ea2400a80601a60838140204a3fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def q20K3 : Nat → Nat
  | 0 => 0x900000e18e0d00149000000080002c8083000c8042085223e0d0003a00011183c21746392800000a9a2650da60078b001208200210014001600012d90732b541ccad90632b5418cb34c832ae42cc6b50b31ae428c6b50a31d5310c6790f219d43c86790e219d43887948421af424c2b10930b7414c2d10530ae420c2b50830b6410c2d504309f43482710d20b741482d105209e43082750c20b641082d504209f43442710d10af42442b109109e43042750c10ae42042b50810
  | _ => 0
def q20N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def q20R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt q20K5 (i*4) 4
  | 4 => packedAt q20K4 (i*15) 15
  | 3 => packedAt q20K3 (i*26) 26
  | _ => 0
def q20I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt q20K5 (5+((h/1+packedAt q20K5 (4+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt q20K4 (400+((h/8+packedAt q20K4 (360+(h % 8)*5) 5) % 32)*6) 6
  | 3 => packedAt q20K3 (1092+((h/13+packedAt q20K3 (1014+(h % 13)*6) 6) % 58)*7) 7
  | _ => 0
def q20Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 2 => 0xe6ff07cff81f8f1c
  | 4 => 0xf8fff80fffe00fe0
  | _ => 0
def q20Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 2 => 0x1942d41a90932b18
  | 4 => 0x78486ad24c24dc0
  | _ => 0
def q20Atlas : Atlas := ⟨5,rawDecor 23 q20Pos q20Neg, 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8, q20N, q20R, (fun _ _ => 0), q20I, []⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model
def gbK10 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK9 : Nat → Nat
  | 0 => 0xe803000343d658110000004600000001400004000000133e600e0400040b200a80d8108142049c00000000002c00002e081500ca529e03003c00600000000000000000000002800000000801a001020000b1207fca9fd54fe2a7fd4bfca5fd52fe297fd0bfc85fd42fe217f8cbfa65fc32ff20ff107fc43fc21ffa07f503fe41fd20
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x3247c016434d80000ab72835cd009aa3148ba6aee4847ba3e3801c1b4949b60000000e80399a7c802c400012550decae905c4000c03eb2b3539d8026c02f72c00025c628c001c02b4019bd2851802d9f09c03811f09bc00038e9eb8018d4402903be40376dc14014c9338019c000001f80260a61a426401e1d34483ddb825888ee393c7e2a400b002e485737c00002f1992acc40001cb8803db530f0614ec574ad3d5090e0c01accc4ad40074019400027e28012ea828f928e14354016201cf1f23036c006f6800e7b270693c5c031402ccc16aa0b68af3318403a15c00000310027402200000bc033c02516c32948801795901b1a06698d40018017523860b41e8a1137ac03c23c00132fc0278136610c8f256b00003f244ac00780040fc5072fa5b59815400017c03a80058544d0101c48060d9b41c0517830160106000563003000041d08000121500804140f540080706020641e010001c1007bf59654cfd5254bf98654bf58254bfd8954bf18554ff48554bfd8154ffc4154ff44154cf55054bf98454bf58054bf59352df55352bf98752bf58352bf98652bf58252ffc4252df55152ff50d52ff50552ff4c552ffc4152ff44152af99052af59052bf98452bf58052bf59742ef55342bf98742bf58342bf98642bf58242ffc4242bf59542ef55142ff54d42ef50d42ff54542ff4c542ffc4142ff441429f994429f59442bf98442bf58042bf98632bf58232ffc4232bf59132ff55132ff50532ff90132ffc4132ff84132ff44132ff04132af99032af59032f34c832bf98432bd98432bf58032be58032ffc4032bfd9641bf59641ef95241ef55241bf58e41ff54e41efd0e41ef50e41bf58a41ff54a41efd0a41ef50a41ff4ca41bf59441ef55041bfd9621bf59621bfd9221bf59221ff55221bfd8e21bf58e21ff54e21ff50e21fd8c621bf59740ef55340bfd9540bf59540ef95140ef55140bfd8d40ff54d40efd0d40ef50d40bfd8940ff54940efd0940ef50940ff4c940bfd9520ff59520bf59520bfd9120ff59120bf59120ff55120bfd8d20ff58d20bf58d20ff54d20ff50d20fb94920fb54920fb90920fb50920fb8c920fb4c920fe4c120
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x67fb82c710efe5058e21dfaa0b1c43bf901638877ea02c710edd3058e21dee20b1c437fdd153887beaa2a710dff7054e21dfac0a9c43fd44153886ffbaa8710dfd7550e21f7aa8a1c437fdc1438877eb028710ff51050e21dfe65b2a81bf8cb655037e196caa06ff31d9540dfc63b2a81bf4c7655037e18ecaa06ff21d9540dfc43b2a81bf487655037e10ecaa04ff7259540dfc64b2a81bf0c9655027a38acaa06ff2159540dfc42b2a81bf485655037e10acaa05bf7355140b7ee4aa281ef8c554503de98aa8a07be2155140f7a42aa281af553635027eb96c6a06fe52d8d40dfca3b1a81bf547635037f90ec6a06fe21d8d40dfa43b1a81bf08763502ffb92a6a06bc6150d40f7c42a1a81ef485435035eaa6c4a04fd73d8940dfca7b1281bf54f625035ea1ec4a06fe51d8940dfaa3b1281bfcc7625037f18ec4a06fd31d8940df863b12817fdcd525037fb1aa4a06bf6350940d78c2a1281ef8c542503de98a84a06fe764c940dfaec99281bfd95325037eb2a64a07bd744c940f7aa899281bf985325037e30a64a07bd414c940bfee0992813f5cf654837f98eca906fe31d9520dfa63b2a41bf0c765482ffb9aca906fe6359520bdee4b2a417f1c5654837f30aca906fd6159520fda42b2a413fdcd654837f98aca906fe3159520dfa62b2a41bf0c5654827eb9ec8906ff31d9120dfc63b2241bf4c7644837e18ec8906fd6559120bfee6b2241bf98d64482fe38ac8906fe6159120dfac2b2241fb485644827fb9ac8906ff3159120dfc62b2241bf4c5644837e18ac8905ff7655120bfee6aa2417f1c554483f690aa8906ff54d8d20dfca9b1a41bf553634837e2a6c6906ff51d8d20dfca3b1a41bf547634837e28ec6906ff41d8d20dfc83b1a41bf507634837e20ec6906de31d8d20dfccab1a41bf595634837f322c6906fd6458d20bfce2b1a417f1c5634837f30ac6906fd6158d20fda42b1a41bfdd1634837f3a2c6906fd7458d20df8e8b1a41bf951634837eaa2c6906fc5458d20dfee2b1a41bf9c5634837eb8ac6906fc7158d20dfe82b1a41bf905634837ea0ac6906fc4158d20dfe80b1a41bf501634837f882c6906fd1058d20bfeeca9a417f1c553483f690aa6905ff7650d20bf8e2a1a41fb48543483f6b22a4907ed6354920fda86a9241fb98552483f6b0aa4907ee4154920fda82a9241fb8c552483f698aa4907ed6550920fdac6a1241fb54d42483f730a84907ed6150920fdca2a1241fb54542483f718a84907ed3150920fdaca99241fb59132483f6aa264907ee614c920fdac299241fb94532483f6a8a64907ee414c920fda8299241fb54132483f6a0264907cd304c920fde2099241fb44132483fd3a260907f9744c120ff4c898241fe59130483fd2a260907f9544c120ff0a898241fa54930483f4a1260907c9324c120
  | 1 => 0x49fae1b12a9bfcc3625527eb90c2aa6fe3218554df86430aa93f5c0615537f900c2aa5ff7348554dfec690aa9fd185215537a30a42aa5ff7048554dfc65b02a9bf0cb605537f90ec0aa6fd21d8154df843b02a97f5cb105537fb1620aa7f521c4154bfee4882a9bfd89105531fbb2a82a43f7655054c7aa9308a98f551601533eaa2c1a95fd73c4252dfac7884a55fdcd5454abe38aa8a973d5450d52dfec0a1aa57fdcd4154b7fb1a82a95ff7050552dfec0a0aa5bfd913154bbeaa262a95ef724c552bfee098aa5bfd813154afeb9e20a96ff63c4152bfae5882a5fd5071054bfa98e20a97f521c4152b7ee8882a57fdcd1054b7fb1a20a96bd5458342bfae788485bf58f1090a7fb9acaa16ff3159542df862b2a856fdcd5450ade38aa8a173d5454d42dfec0a9a857fdcd5150b7fb1aa2a15ff7054542dfec0a8a85bfd953150b7eb2a62a17bd544c542bdee498a857fdc13150b7fb0262a15fd73c4142dfec7882857f5cb1050bfaa8e20a17f531c4142fea43882855fdd51050affb9a20a16ff6344142bfeeb884657f5d7108caffba621195fd74c4232bfee7884657f5cf108cbfb28e21197f641c4232fec63884657fdd9544cafebb2a8997bd6455132bf8e2aa2657fdc1544cb7fb02a8995ff7650532bfeeaa0a657fdc1414cb7fb0282995fd76901329faed202657f5d6404caeeb9c80995ed7290132bfce3202657fddb104cafebb620995fd74c4132bfee5882657f5cb104cbfb30e20997f561c4132fea8388265fd887104cbfa90e20996ff60c4132fde41882657f5da104ca7ebb420995fd7484132bdae5082657fdd9104ca7fbb220995ff7444132b7ee8882657fdcd104cbfb30a20997f63144132dfec088265f7cc1104cafebb020994fd7604132bfae8082656f5d0104caf6b9020995fe7104132d9a64b0065b24c9600cb7d38ac0195ff74c4032bfae988065af593100cbe699620197f641c4032df2c1880653f5cb659077f196cb20efc32d9641dfe64b2c83bf8c9659077e192cb20dbf7355241b7ee4aa483af551639067fb92c720efe5258e419fee0b1c83bf541639076e982c720eff2058e41dfa40b1c83bdc41639079eaa2a720dff7254e41bfee0a9c83bf58153907fa882a720dbd75d0e41d7aa8b14833fdcd629077f29ac520efd5358a41d7a86b14833fdc1629077ea82c520eff3058a41dfa60b1483bb481629077b882c520f3d5454a41bfee6a9483bf58d52906ffb82a520efd6054a41fea20a94836f5d7429075eb1a8520efe764ca41dfaec99483bfd95329077eb2a6520fbd744ca41f7aa8994837fdc1329077eb026520fbe404ca41fee2099483fd441329075eb02a820cfd73d96219fae7b24437fdcd54887fbb8aa910ff53155221bfee0aa443bf58154887fa882a910cfd70d8e21dea21b1c43bf5516388
  | 2 => 0x42382fc00000ab8b27240044b2e2a8cc19c003b53a000003bc0000000c70000000000000000ac002f3002ee0000000000000000000000000000000000000000ca000838be0c4b6001d6001ff0012506cb525000000000000000000000000032631c0000000001ead1263000000025e000cd00000001110000070b0d6bc00a18000000052800001668c6f7a200000000000000000096740001b5000e6001182400000000000005fda140c00700002623a00000078005700000000ba6c8096ea000007631e0000000000000f7c28005695800000cec00000140fc00000d900000b3400000683130b5d46957df9508343d53d49800000009813f002f100046d1800bef0870d7387c0000272000003a000a9c00000000001f000005f80068b02000005bc00001870019200000001bd0000080000589ef000000000000000ab68000000b880000000000008796926800c9400001d9003310000055cc6000a2c3b4d000001511b11f39950003580075c000026a00000002db00097000000000062439000000000000000000009d26400000001a8000440000000000000fd6e2b94cc00001a374400468007f800cd5ad00320000000000048c009c27ea29fa54800c14cb00000000000012800000937070000000000000000d9cc00000b5400a931341800a7c0000252a6cda000eb00000000a7860000000000050002300014d00021002bd1f40078c00000000000000000aa8005e8000000000000000fa000006c000a46119eae5000005206f39c800000086800001f3abe0a6540027400b4f1616dfc068575023b35d4c00000126250014f00000002f90002f0000000000000009b5eb00026b04832c0009980017c000016841cee00000002e10018400178003230005c0000000000000006e400000a8000370000000127ac8007500062c00001140000047000000000006a0004abbef20000074af60000000000bb000000000000000000000007b6dca41050026218000204008a00016a0800000000040715000000c48003940024800d0c000000000059000004e521514000a52b00000994d1001a5001c6002a860c0027000002179f4000011f00000a6400bac00ba000000000009f490009e71000000000000e8003080000400c0000300201c0180000003805800006008048010200040080001c000000010040000080200401400002006000018010080100100b0020280200000401c0000700400402807002004010060040200000100203801805000000010040160340280d0000000180000a02c0380000c00001803004004090010040040100000800003801008000000000040040280001600000802000010008040100040080200a0081200000a0180080001600c0100000a0140280000000c0400700c000000010113f5cf625537f98ec4aa6fc31d895
  | 3 => 0x48000000c82a551000000000067800000006d800000000000081d88408009fc0d018000032b4ec002c408a5abe929b2000e16f8006ee6e59212000007c6e48e000d28000000000000000008b000000ab0033e00000000005ecad782ce6d000000007b3224a400000001580000000000009da491556e000001b00099c000000000000306e00014b664008b4fc94400bf400000004d0b8002090000000000001ce5840000000a84000029d000000000000000000000000086c0000000cc811600001c9471ac0000000002de0000000000bb4005c4006980000000001ab0009e002870004f00000000006b2198d8000000000000000000000000028002ca00000000000000000000031912e4000000000000909321c000059b136292000a4ad0000022433c000000000000c3e3cb600000000000000000000000000000023f002780008400000000000014400000000000019c7d84c340febf800002ff00000b0c004571d00137370006fe0537aa29dc00000df000000025000000000005f2d7bc00028c000000000045900dd23a2f3e07f26c0078400060006740000000c332a6ce1ccda0400000000001b4002e800000bc002b00016c00082791e5000000034900000000000020d000005a800000000a800002d2cf000808bfc9c004b201a1012ca43c00194a7800921d0000ff0011d5d800ce9850000000000000000012d0000000348cdc95000000028c00000000a6001600000074c0024c00001907982300000000008c8007c00097300001933ec00518006313000000605970000000000001fd05579a60960018257400a5c00001e9000000000056ddb424000000000000000000b800420000000002dfba51c44e0af0012a00000000000024f0010ab2c000000000000002a55ae8e5b400000f1be8000003267d222865a0008b7a113830004c6a9000e988c00003030002c0010d00000338007b800001c1c4400000d200000a0c0000000b9cd400244003243c84300000b7c000000084c00002d6b0800001d58d0007e03e000000000000000000001488700000002c700085001cb00033000426b88a8f4000000000000188000000000000000bd000000000044000000ec000000008c000000033000000000000000000143002c50000066c00be0bb294000000000000002b60000003800000000000000000000000000000000aec00001e2c8451b406e0010eb1800000004044ea6a06000005780093ada8b80000000001c800000000000000000000001ba3e4008800000000b1000001c577c7cae000002a35dd98af0380009195ac90001d0000000000000001e00000000000276387a000000018600000b9b043c0007d00269000000a0001f79c400000000026c0000000035000b70000000000000000000000000001da000005240043dbc2b98f12f
  | 4 => 0x2cf000000008fccc00040006804d3931a00000ae8000800000000000000000005e570000080c0f0000001400000005540000000000002d00000000a14d500000002d40000000000000130013e0000000141aaddd002d95580089800000e33240000000d14000013534cdb0000008800000480013ccbc0000000bd4000009900000c7c00d1ddca2400adf01001dea8000000003d2dd3dabf0000079c000034b7d4000000088800218c50000097cb35c258658001f800000004b800003388a4004bc0000000000000023e00000634000b4006dc00cd14e0ac00002cc00041000008540071d590f400ad4003cc0059d72acc004d86462800bd174915f20000000000413416a889458008419a4334c00088000001d00014c0000154000665f400000000000073c00000ca0000083dcaa726885117000000000000000b000000000160e20005ea0400100000000000000002acac40000000090000020b9f0ea00000a08000032c0021d002160030654c00000000000000000000009be2a00000000000003bb8e4630e7b1da4c46500c600017400c500a0006530000a98030c11e0008d
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc874c5644823fa1c3159120cdf730c564482bb6083159120af9800c5644827e60376551208fd86dcd544827b60b73551208fd861c5544827b60871551209f9801c554483791c52155120e3f5495363482b7e0d54d8d208fd87153634838f55054d8d20add83153634823f61f51d8d20abe84d4763482af61351d8d20add83d4763482b7e0d51d8d208fd8714763482bb60851d8d20af980147634823f61f41d8d20a7e85d07634829f61741d8d20add83d0763482b7e0d41d8d208fd8710763482bb60841d8d20af98010763482b761e31d8d20ecd828c763483b59c631d8d20ed5718c763482b760231d8d20ed7108c763483b544231d8d20cdc639c5634827b60a7158d209f9809c5634833718c7158d20cef72985634829fe156158d20a7c8558563482afe116158d20abc84585634833d1c56158d20de471485634832fdd27458d20add839d163482bb60a7458d20af9809d1634829fe157458d20a7c855d163482b7e0d7458d20aef825d163482bde057458d20af4815d163482bee017458d20a7e851d1634829f6147458d20cbd741d1634838fd525458d208fe87151634823f61c5458d20e3d5415163482bb60a7158d20cef729c5634833ddc67158d20af9809c563482afe117158d20abc845c563482bbe097158d20afb805c5634833bdc87158d20cf5711c5634823fa1f4158d208fd87d05634829fa174158d20a7d85d05634823fa1c4158d208fd8710563482b760c4158d20aed8210563482be6004158d20abf8444163482af2111058d209f980dd9534823f6187154d209ed821c5534827e6007154d20bcf83485534827e6037650d208fd861c5434827b6087150d209f9801c543482f3e0d2150d20f2d5459152483cb5514354920baf8458552482f3e0d6154920beb8058552483cb5524154920aef864c552483cb5516550920f2d5454d42482dbe156150920bcf8358542482fae016150920f2d5494542482bbe193150920bcf8359532482f3e0d644c920bcd8398532482dbe15614c920baf8458532482f3e0d614c920beb80585324827b61e514c9209ed8790532483f2d01304c920fc9404c132483f24c3104c9209ef8744132482dbe15104c920baf8444132483f24c1104c920af9869d130482fa60a744c120beb825d1304827e61e644c120bd98399130482f6e0d644c120f3b5495130482f660e544c120be98295130483ce550544c120be98215130483da9d5524c120f6b5454930483f250d524c120f685154930483f24c5524c120faa7450930483ea951424c120fc95350930483ea105424c120fc93150930483f29d1324c120fc9744c930483f2991324c120fc9644c930483f2951324c120fc9544c930483f2151324c120fca614c930483f2585324c120fcb414c930483f2905324c120fc9414c930483f2105324c120
  | 1 => 0x3551529074f5537354a41e3d5458d5290737dcd6354a41aef8258d529074f5537054a41e3d5458152907cd5511054a41a7d859d932907b30ca764ca41adf835d932906bbe09764ca41ecc325d9329063f61f654ca41ecc32d9532907b30c9654ca41ecc32581329066f61e404ca41b9d8390132906eb60a404ca41fc432c413290737cc973d9621cdd325cf6588737cc973d9221cdd325cf648867b60b73552219f4874c5548867d21d10552218ff825c3638873e88170d8e21adf83551638873e8c37058e21cf930dc1638863fa1e5058e21add83941638863fa1e4058e21add8390163887b3e093058e21edb704c163887b61c13058e21ed5104c163887b5cc31058e21ed530c4163886bda0432d9540af5810cb65502be60032d9540af9800c765502be60021d95408fd83dc9655023fa1e3259540cdf738c9655023fa1c3259540cef720c965502bda043259540af5810c965502be6003259540cf6321c5655033d0c871595408fe87c85655023f21d21595408fe8708565502be60021595409bd82dcd545032f18773551409bd83dc9545032f1877255140abf82553635032f55172d8d40cee325cb635023f61e52d8d40ced7294b635038f55251d8d408fd87c87635029f61721d8d408ff8748763502b7e0d21d8d408fd8708763502be60021d8d40abd82185435032fdc86150d40b9f8348543502afe0d54d8940cbd545cf6250337cc973d89408fd8794f62503375ce53d8940e3d5454f62503375cd53d8940aef8254f625038f55251d89408fd87cc7625029f61731d89408ff874c762502bbe0931d89408fd870c762502be60031d8940e3d54d8d5250337dcf6354940aed82d8d52502af60c6150940cbf7318542502ebe093150940add839d932502bb60a764c940ecc329d9325029fe15764c940ecc325d932502bd205764c940ecc32d95325023fe1d654c940ecc3259532502bd205654c9408fd8798532503b30ca614c9408fd8718532502b760c614c940aed8218532503b30c8614c940c7c515cf654823f61f31d9520abd84cc7654823fe1d31d95208fd870c765482bb60831d9520af9800c76548337dce63595209ed83dc9654837a4c37259520abf8458565482b7e0d6159520adc83585654833d1c561595209ec8748565483791c521595208fd82dcd6548337ccb7359520cdd32dcd654823fa1f3159520abd84cc56548337dce31595208fc874c5654823fa1c3159520cdf730c565482bb6083159520af9800c5654832f10573d91208fd87cc7644829f61731d91208ff874c7644823f61c31d9120aed820c764482be60031d9120e3d545956448337dce6359120a7f8558564482b7e0d6159120adc83585644833d1c56159120de4714856448337ccb7359120cdd32dcd644823fa1f3159120a7d85cc56448337dce31591208f
  | 2 => 0xc8615523f61e3218554ced728c8615523f61c3218554af9800c8615523fe0970185548fd87c80615533b5cb20185548fe87d8d21552bd60c6148554cf77318521552bd6006148554ee72018521552bda0432d8154af5810cb60552be60032d81548fe87d89105523fe1973c42529ef825cf1094b1f187735515297d831c55454b1fd8c7155152d75211c55454acf2055450d52b3f805514354b8f5536050d52b74815513154b3bd93724c552d6d54dc93154a7be0973c4152be7824c71054b2fd837444152cbd60dd11054b4f5437444152dad20dd11054a3fa1f6344152cbf74d8d1054b37dcf63441528ff865cf1090a7be0973c4242cdf32dcd6550a3fa1f3159542cdf73cc56550a3fa1c3159542aed820c56550b4f54b7355142cbc61dcd5450a6f60c7155142cbf631c55450b4f5487155142db5211c55450acf2055454d42b3f805515350b8f5536054d428fc875953150ab7e0d654c542bb4815513150b3bd97724c542ced65dc93150b6b553724c5429ef825cf1050af9e0931c4142d3d43dd51050b1fd837544142c7d60dd51050b4f5037544142d6d20dd51050a3fa1f6344142c7f75d8d1050b37dcf63441428fd86dd7108ca3f61b74c42329ed82dcf108ca7be0973c4232be5828c7108ca7b60b7655132dcc32dd9544ca7be097655132dcc325d9544cb8f59564551328fd861c5544ca7b6087155132dcc321c5544cb730cb7055132e3c54d81544cb2f10576901329dd83dcb104ca77e0d72c4132be582987104caf5e0d21c4132cbf65dd1104cb2f5977444132cbf74d81104cb2f1d36044132cdf76cc1104cb57dd73044132d9f74cc1104cabee127158032af9849c5600cbb24ca7158032ef2419c5600ca3f61b74c4032cbf75593100cb2f5d564c4032dce874cb100cb7361d32c4032ecf864cb100cb735d132c4032fc6814cb100cb9d59641c4032cfb74583100cb3e5d160c4032ec932583100cbbc90560c40328ff835cb659063f61e32d9641cdd738cb659063f61c32d9641ced720cb65906be60032d9641af9800c9659066f60b73552419bd83dc9549074f9477255241abf82551639072f5537258e41cee32dc9639063f6037258e41cdf30dc9639063fa1e5258e41cef72949639063f60b7058e41cf930dc16390737dc93058e41edb704c1639063fa1f2058e41ced72c81639063fa1d2058e41ed930481639073ddcb1058e41b3f82551539074f5537254e41d3d54dc1539078f5516054e41f355444153906afe0d5458a41cbd54dcd6290737ccb7358a418fd80dcd629073bc837358a418fe8794d6290737dce5358a41e3d5454d6290737dcd5358a41aef8254d629063f60f7058a41cf920dc1629063fa1f3058a41cdd73cc1629063fa1d3058a41cef7348162907badc12058a41ee930481629073ddcf1058a41b3f8
  | 3 => 0x192800f64b97861f870000054f434120025c00000ea000003ad55000004c7147380061957a6000000c980000000000017d801c1dbc00000550000062e00000000006aa5bcc000003f66200193000003b0120000029600344000008b000000000000000000fb655aab21b00fc004dfac558c3000000012f54474a59a9c4c0079400204e700041801ef00000000000000021e140bc30800000402900000000005861d8000018e26328bc8013082c0024c00401c3123a6801e64904cc5b08a8040000001402d800c20255c8001e00000000d700c0047800000000009b9dafcf1762d800000000488003514a1742214c002e0007a0ab5098c03600000340000b801ca00000222000000000000000003650a00000000000006c001a54ae002e2000012b29e948ba002c391ed4000cfe9edc0000000001658a0c55dc006e7344411b536000008714fc25d800000000596b800be0000000000001a58f000000004ff9f1ca001bc75001be00000000003afd00000078400466d26980000043b6e0000056000005e600001b81a0925c80032c32b980000000001ae80000000c7aa14e67a442d2e900089800002e95f8006eb7e7a924004d6002171a80000000421a800129db00000000003380075eb3801c9241d1001f4f9b985ba003d00063d4880108000001cea3800000003f801caa7a0025133ccc004aa00010de00000001388007fd8e6d0000066a00546e59d74f14600771454bf911fc0000084e286ba8df430e0034e00001990017a0017a98dba17c007ba0023410801f30017380000000000000022800000003ceb973419800001d00057a006a5ef8000000107000000018c800e68003c800000000000000000000009179dbbc9bdfbbc000e905800000000e56e2100000000edece002de006d9ce9e5968000000000000a7303cfab20059c000014480042800b04b200001bd800528c16f80000014004100000000000005a80044578b76a20010db9200530c480047c0c3680800001ed80000000001d80280e0000080280700a02c0e011008000030120060180500100401003806010000000010020040580501e00c000000020240200100003401000004008000000080140080b012020038090020040c806002008008010100000000303a00400819008010028020000040200300e000000000000140080100000c0580001001c00001002000008020040480200000001014003012004000080100540080300200000006000008010040080080000500a00c010020020040380000800403005008000018000200000101c000004000010000200801101a020038000040000d0030020040000100601337cc973d89548ff805cf625523f61f31d89548fd870c762553375cc31d89548ff835c3625523f61f30d8954cdd73cc3625523fe0d72185548ff805
  | 4 => 0x800001680a2b580000142fd000000018800000001c48000041a000019728be1a8400000005f400369bb0003d70a001980023000130c59c39b00000000007c400000000016e000002ba00000002a93b801e00001782a00000005b44ba065dc9e00001d201800000006884ec34004f200550006a20000000000001f9e3801d9c931d000004c9d8bca00702df0000000e003c4000000000000001410000000146fc00008e00000006c9d280000000000000048200000fa8000047c005b000325bf2cb3680000001a3000358740000000001c0001f1c8ba7800000000034342faa57000000000000000083af800000018ea191d8007e95bab8000056a00000000006480091ce400001f200185800000c800001c17c216e916cb9400000aa800002c8000ae00001060000000000747eb8708fc7e000fa00000cc84b090017100000000003d5740015200000001e94a4000000017800562003b80000000000240010a8003ae0cbd000000015e000c88000000000000006147072f8a80000000610000079600000e9800003a26405731001ab4a6000014b485490602f800003cc00390ce8014c80180800b45a64700029800003e60f0012375c005928a96a39ef20000073238b9fb134df2004f079edb1880082653cd8008900000000a491600000000019d40a00001c63c63e000ea800000000000000000000000071c0000000000005ac09bdc003b2000000000058801153d35a000001480000000000006015700000000002620043dda00000000000005a6577b337ee0000000100f91da800000003b001778000e8000020000000002420000000792005f000374000000026600001be8a872001283000042f6959aa0804af0000069200000000000000000001d912ddb800000002715000000006c2000013b43e0066905000003fe6987dec8000000000000770003dd180032e00000410000000132e400000000000ff0013de58000008d854f900024cb47d00000567c80017280000540000d20063755e2400000000000068427ef05991b4700138000be80156a7c00170868000071400001370003880000346001f02c00117800000012c5d600000a9dc20000088001730000023ab741e006120008147b2b61000004a2f856c4fc2de2a1000001cf002007b5b10004f2d8006d097800ac14400000000000059e002b600000000000000000000002f66580000000005fa0004fad2d5a3d64bf69c0000000386db13400318000d80043200000003d71808c0000168c314f800d80018d17a31000004c000000005900000000000006a8004948380000670000007d801b5e3feb458b1800a8bf91a00000000002f0003bf40000000442a8011eb3c0071a00000000000027fe20015080000000b3000000019087a00000bb6487c801cb05d3e0009c35a00001d680000
  | 5 => 0x6bc00000e139efa000462915f000002af650000050600000001ee00722005f84af7db326dd50011c0460c70e0021515efe005100700000034000651be824ddc6002774ee2c997ca66cfd66000000006900103f1e088000020a00000a6000c4001239c6005166b2efa00015d800a91202d000006d2000000058c00000fc00044a94cc0e00002831a4e004ba9a801cca541a07ecd7740034a0000000001d60017f0006780000000fb8000000000000000000029a0000000000001e20000000000d7800001ecae001a180149bb4000008f001a2dc1271b72db8ae3b1c393c9529b9438de00001350000000000352001a20000000000086ea0000000000000000019c00000001b200000000b80000000001ac801c98000000000000d0001b2afe00000000320049958000000000074c0054c00180005200052e00000000003538200000002b40000000000e0000000014d00000001adbdb098160004c780000000000000580007a001ea000007100000000202a1ee40000000000004969cb7200000005aa000000061a8c8019e2da00001d4000febdfe08eeb10dd02000f00000000000000f0800408002c886004489e0004500000001840008ba4b94486000000052aee800650000057425e4e00001d815200000c1b560037000000004fb4080000000deb0ba80009a00000480000000000000000000000000095800003e200404afb556db8c0045db1800005820033f1c80004800006260010c00000001de004f5810013a000005e4006b8000018e000018000034c000000000175274ba800007ce5b072000000078c0006c000000058800000000006fd520000000000e816400465bd0cce2000007780000136001d59c400742000018244e831275c00101800c686a00304000acd6438000944e4a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x700ea00000d94c00000348c65c0284024d3486728000b000b8000340026c0000017d4454057ab000001402940801f800004c01b4006034010a64fe780000000040009800891000aaa80000940002a4013090680289c080b71a11024991f351e6d5aa7c009d5c012da2ba351e4001a56c293f09540001f40001d80290a0000002e68e581c0120f80000023800020002242002e9d2f0f1ac596801600001cc01380001580000e80002d004000280014050002c040801804000010800462403818120f000140a1002028000a0082808020755924554dc93154ba4aa4908e2aa2855a491553724c5428e6cc065bb2a89957264032dd9544ca39d30192ecaa2655c9900c97655132f06192cab22a899473660321c5544cab9320190e2aa2655c9900cb705513291ecc0a9b02a89950fa5c54d81544cb59708994e2b0065ac9844ca7158032f6148a6538ac0197b04ca419c5600ca99b2d43a65880654cf9661d32c4032b62cb5029962019732a5d32583100cb9932e992c188065cc9744c960c4032f6148a64b06201963a5c9800cb6590783aa9b9aa6b1483a2d54e095358a41e0eaa6e6b1aa520e8b5538258d5290659b30194ec99483a4d850ca764ca41b64c80653b26520cb3a60325d932906d9320192ec994838cd870cb654ca41b64c8065b2a6520db26403259532906d9320192c0994837c1900cb104ca41b64c90e0982c710c3d25d810c9655031d6e4c0064b2a810f5980c87159540a78c806438acaa07075517354f6250345aa9c12a7b1281c1d54dcf6354940d16aa305b1aa4a04b3660329d932502d9320194ec992812ce980c9764c940d27c2864bb264a05b2640325d9325035886440aec992816c9900cb654c940c67c3864b2a64a05b264032595325035886440aca992816c9900ca614c940966cc06430a64a05b264032185325031a90638ac2b2a418d4831c5615912086fc9b0c38aa890578640714855448247f30aa0a9b1a4183d8755054d8d20d0eaa3062a6c690437660639c563483988c638a42b1a410bf985d07458d20c1ec2ae83a2c69048fe61541516348307b0eaa0a8b1a410f7985c47158d20a73c92e238ac6906e2e11304413248371108982209924133b98550544c120d94aa3042a260905d264f5454930483e12a8a1aa49824156997145524c120ba4c98a2a9260905e264e5450930483e12a8a9a84982415a997105424c120bc4c9882a1260905b265a744c930482b932f32264982413c998951324c120f85aa4a899260904f2660544c930483e12a82a264982413cb98585324c120ae5cbac299260905d2e55614c930482e912ab0a649824178b94585324c120bc44a2c299260904f2663414c930482e952ba0a649824174995d05324c1209e4cc48299260904f2660414c930482b932e20a64982416c996105324c120
  | 1 => 0x2f9e846e12a2000dcc231414a18d18b3951d5c62a080000005c00d478000000000000000269240001180000a418032000022c00004b10e0c83db0000344700024ef2800f48c3261642ed800000182ca9ac00274534c0331e001dc00000003000001759a561dbc000000000184000000be5001c9b802ec38020c00000001ec0010000355
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa020c502a08b900581b2110c000007a83aa0325956455132b82680325956455132c92615900ca764ca41c3261d900cb654ca41c92e15900c9764c940ab068032205764c940c32e1d900c9654c9408b16a432205654c940ab068032205654c9409c2ea554151324c120cc266154151324c120
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 10 => 1
  | 9 => 22
  | 8 => 127
  | 7 => 423
  | 6 => 501
  | 5 => 107
  | 4 => 11
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 10 => packedAt gbK10 (i*6) 6
  | 9 => packedAt gbK9 (i*17) 17
  | 8 => packedAt gbK8 (i*28) 28
  | 7 => packedAt gbK7 (i*39) 39
  | 6 => packedAt gbK6 (i*50) 50
  | 5 => packedAt gbK5 (i*61) 61
  | 4 => packedAt gbK4 (i*72) 72
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 10 => packedAt gbK10 (7+((h/1+packedAt gbK10 (6+(h % 1)*1) 1) % 2)*1) 1
  | 9 => packedAt gbK9 (423+((h/7+packedAt gbK9 (374+(h % 7)*7) 7) % 103)*6) 6
  | 8 => packedAt gbK8 (3934+((h/42+packedAt gbK8 (3556+(h % 42)*9) 9) % 300)*8) 8
  | 7 => packedAt gbK7 (18048+((h/141+packedAt gbK7 (16497+(h % 141)*11) 11) % 1815)*10) 10
  | 6 => packedAt gbK6 (26887+((h/167+packedAt gbK6 (25050+(h % 167)*11) 11) % 1930)*10) 10
  | 5 => packedAt gbK5 (6842+((h/35+packedAt gbK5 (6527+(h % 35)*9) 9) % 300)*8) 8
  | 4 => packedAt gbK4 (807+((h/3+packedAt gbK4 (792+(h % 3)*5) 5) % 22)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x87f0fff060e1fc3fff1c07ffff14411e08f0ff
  | 1 => 0xf87f0e0f80fe1fc383e0070e1f2b8ee8774c93
  | 2 => 0x7ff00fff001ffc03fff80fe0cc30f1878f1c
  | 3 => 0xff80000fffffe00003fffff000f03f01f80fe0
  | 4 => 0xffffffffffc00000000ffc001fff000
  | 5 => 0xfffffff0000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x801200000020048004010200000002001025
  | 1 => 0x8831042380620c410b2032245e018668334c92
  | 2 => 0x5aa044a90016a811495009c24c10b0858518
  | 3 => 0xd500008952b540002292a4e004b02b01580ac0
  | 4 => 0x4408810e7cd99b327800c04088fec001eee000
  | 5 => 0x666cc9e0181102204003008110ff7ddc000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000, 5, 0, gbRaw),(0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333, 5, 0, gbRaw),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f, 6, 0, gbRaw),(0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000, 5, 0, gbRaw),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f, 6, 0, gbRaw),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 5, 0, gbRaw),(0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333, 5, 0, gbRaw),(0x5050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000, 5, 0, gbRaw),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f, 6, 0, gbRaw),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 5, 0, gbRaw),(0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555, 5, 0, gbRaw),(0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444, 7, 0, gbRaw),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff, 6, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff, 5, 0, gbRaw),(0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000, 5, 0, gbRaw),(0x550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055, 5, 0, gbRaw),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 4, 0, gbRaw),(0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555, 4, 0, gbRaw),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 5, 0, gbRaw),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff, 6, 0, gbRaw)]
def gbAtlas : Atlas := ⟨10,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8, gbN, gbR, (fun _ _ => 0), gbI, gbPools⟩
end PEqualNP.Outside.L_meta_44276
namespace PEqualNP.Outside.L_meta_44276
open PEqualNP.Outside.L_meta_44276.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
set_option maxRecDepth 32768 in
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
set_option maxRecDepth 32768 in
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
set_option maxRecDepth 32768 in
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
set_option maxRecDepth 32768 in
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
set_option maxRecDepth 32768 in
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
set_option maxRecDepth 32768 in
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq0_2_0 : Interval q0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq0_2 : Interval q0Atlas 2 0 4 := bq0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq0_3_0 : Interval q0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq0_3 : Interval q0Atlas 3 0 6 := bq0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq0_4_0 : Interval q0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq0_4 : Interval q0Atlas 4 0 1 := bq0_4_0
set_option maxRecDepth 32768 in
theorem allq0 : ∀ k ≤ 4, ∀ i < count q0Atlas k, checkRow q0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq0_2 i (by omega) hi
  · exact allq0_3 i (by omega) hi
  · exact allq0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_2_0 : Interval q1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq1_2 : Interval q1Atlas 2 0 4 := bq1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_3_0 : Interval q1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq1_3 : Interval q1Atlas 3 0 6 := bq1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq1_4_0 : Interval q1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq1_4 : Interval q1Atlas 4 0 1 := bq1_4_0
set_option maxRecDepth 32768 in
theorem allq1 : ∀ k ≤ 4, ∀ i < count q1Atlas k, checkRow q1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq1_2 i (by omega) hi
  · exact allq1_3 i (by omega) hi
  · exact allq1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_0 : Interval q2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_3_32 : Interval q2Atlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem allq2_3 : Interval q2Atlas 3 0 39 := (concat bq2_3_0 bq2_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_4_0 : Interval q2Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq2_4 : Interval q2Atlas 4 0 24 := bq2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq2_5_0 : Interval q2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq2_5 : Interval q2Atlas 5 0 1 := bq2_5_0
set_option maxRecDepth 32768 in
theorem allq2 : ∀ k ≤ 5, ∀ i < count q2Atlas k, checkRow q2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq2_3 i (by omega) hi
  · exact allq2_4 i (by omega) hi
  · exact allq2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_2_0 : Interval q3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq3_2 : Interval q3Atlas 2 0 4 := bq3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_3_0 : Interval q3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq3_3 : Interval q3Atlas 3 0 6 := bq3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq3_4_0 : Interval q3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq3_4 : Interval q3Atlas 4 0 1 := bq3_4_0
set_option maxRecDepth 32768 in
theorem allq3 : ∀ k ≤ 4, ∀ i < count q3Atlas k, checkRow q3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq3_2 i (by omega) hi
  · exact allq3_3 i (by omega) hi
  · exact allq3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_0 : Interval q4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_3_32 : Interval q4Atlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem allq4_3 : Interval q4Atlas 3 0 39 := (concat bq4_3_0 bq4_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_4_0 : Interval q4Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq4_4 : Interval q4Atlas 4 0 24 := bq4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq4_5_0 : Interval q4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq4_5 : Interval q4Atlas 5 0 1 := bq4_5_0
set_option maxRecDepth 32768 in
theorem allq4 : ∀ k ≤ 5, ∀ i < count q4Atlas k, checkRow q4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq4_3 i (by omega) hi
  · exact allq4_4 i (by omega) hi
  · exact allq4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_2_0 : Interval q5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq5_2 : Interval q5Atlas 2 0 3 := bq5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_3_0 : Interval q5Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq5_3 : Interval q5Atlas 3 0 6 := bq5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq5_4_0 : Interval q5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq5_4 : Interval q5Atlas 4 0 1 := bq5_4_0
set_option maxRecDepth 32768 in
theorem allq5 : ∀ k ≤ 4, ∀ i < count q5Atlas k, checkRow q5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq5_2 i (by omega) hi
  · exact allq5_3 i (by omega) hi
  · exact allq5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_2_0 : Interval q6Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq6_2 : Interval q6Atlas 2 0 4 := bq6_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_3_0 : Interval q6Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq6_3 : Interval q6Atlas 3 0 6 := bq6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq6_4_0 : Interval q6Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq6_4 : Interval q6Atlas 4 0 1 := bq6_4_0
set_option maxRecDepth 32768 in
theorem allq6 : ∀ k ≤ 4, ∀ i < count q6Atlas k, checkRow q6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq6_2 i (by omega) hi
  · exact allq6_3 i (by omega) hi
  · exact allq6_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_2_0 : Interval q7Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq7_2 : Interval q7Atlas 2 0 3 := bq7_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_3_0 : Interval q7Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq7_3 : Interval q7Atlas 3 0 6 := bq7_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq7_4_0 : Interval q7Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq7_4 : Interval q7Atlas 4 0 1 := bq7_4_0
set_option maxRecDepth 32768 in
theorem allq7 : ∀ k ≤ 4, ∀ i < count q7Atlas k, checkRow q7Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq7_2 i (by omega) hi
  · exact allq7_3 i (by omega) hi
  · exact allq7_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_2_0 : Interval q8Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq8_2 : Interval q8Atlas 2 0 3 := bq8_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_3_0 : Interval q8Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq8_3 : Interval q8Atlas 3 0 6 := bq8_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq8_4_0 : Interval q8Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq8_4 : Interval q8Atlas 4 0 1 := bq8_4_0
set_option maxRecDepth 32768 in
theorem allq8 : ∀ k ≤ 4, ∀ i < count q8Atlas k, checkRow q8Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq8_2 i (by omega) hi
  · exact allq8_3 i (by omega) hi
  · exact allq8_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_3_0 : Interval q9Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_3_32 : Interval q9Atlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem allq9_3 : Interval q9Atlas 3 0 39 := (concat bq9_3_0 bq9_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_4_0 : Interval q9Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq9_4 : Interval q9Atlas 4 0 24 := bq9_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq9_5_0 : Interval q9Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq9_5 : Interval q9Atlas 5 0 1 := bq9_5_0
set_option maxRecDepth 32768 in
theorem allq9 : ∀ k ≤ 5, ∀ i < count q9Atlas k, checkRow q9Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq9_3 i (by omega) hi
  · exact allq9_4 i (by omega) hi
  · exact allq9_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_2_0 : Interval q10Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq10_2 : Interval q10Atlas 2 0 3 := bq10_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_3_0 : Interval q10Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq10_3 : Interval q10Atlas 3 0 6 := bq10_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq10_4_0 : Interval q10Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq10_4 : Interval q10Atlas 4 0 1 := bq10_4_0
set_option maxRecDepth 32768 in
theorem allq10 : ∀ k ≤ 4, ∀ i < count q10Atlas k, checkRow q10Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq10_2 i (by omega) hi
  · exact allq10_3 i (by omega) hi
  · exact allq10_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_2_0 : Interval q11Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_2 : Interval q11Atlas 2 0 1 := bq11_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_3_0 : Interval q11Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allq11_3 : Interval q11Atlas 3 0 5 := bq11_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq11_4_0 : Interval q11Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq11_4 : Interval q11Atlas 4 0 1 := bq11_4_0
set_option maxRecDepth 32768 in
theorem allq11 : ∀ k ≤ 4, ∀ i < count q11Atlas k, checkRow q11Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq11_2 i (by omega) hi
  · exact allq11_3 i (by omega) hi
  · exact allq11_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_2_0 : Interval q12Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_2_32 : Interval q12Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_2_64 : Interval q12Atlas 2 64 2 := block_range (n:=2) (by decide +kernel)
theorem allq12_2 : Interval q12Atlas 2 0 66 := (concat bq12_2_0 (concat bq12_2_32 bq12_2_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_0 : Interval q12Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_32 : Interval q12Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_64 : Interval q12Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_96 : Interval q12Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_128 : Interval q12Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_160 : Interval q12Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_192 : Interval q12Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_224 : Interval q12Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_3_256 : Interval q12Atlas 3 256 23 := block_range (n:=23) (by decide +kernel)
theorem allq12_3 : Interval q12Atlas 3 0 279 := (concat (concat (concat bq12_3_0 bq12_3_32) (concat bq12_3_64 bq12_3_96)) (concat (concat bq12_3_128 bq12_3_160) (concat bq12_3_192 (concat bq12_3_224 bq12_3_256))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_0 : Interval q12Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_32 : Interval q12Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_64 : Interval q12Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_96 : Interval q12Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_128 : Interval q12Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_160 : Interval q12Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_192 : Interval q12Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_224 : Interval q12Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_256 : Interval q12Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_4_288 : Interval q12Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem allq12_4 : Interval q12Atlas 4 0 302 := (concat (concat (concat bq12_4_0 bq12_4_32) (concat bq12_4_64 (concat bq12_4_96 bq12_4_128))) (concat (concat bq12_4_160 bq12_4_192) (concat bq12_4_224 (concat bq12_4_256 bq12_4_288))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_5_0 : Interval q12Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq12_5 : Interval q12Atlas 5 0 24 := bq12_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq12_6_0 : Interval q12Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq12_6 : Interval q12Atlas 6 0 1 := bq12_6_0
set_option maxRecDepth 32768 in
theorem allq12 : ∀ k ≤ 6, ∀ i < count q12Atlas k, checkRow q12Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq12_2 i (by omega) hi
  · exact allq12_3 i (by omega) hi
  · exact allq12_4 i (by omega) hi
  · exact allq12_5 i (by omega) hi
  · exact allq12_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_3_0 : Interval q13Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_3_32 : Interval q13Atlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem allq13_3 : Interval q13Atlas 3 0 39 := (concat bq13_3_0 bq13_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_4_0 : Interval q13Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq13_4 : Interval q13Atlas 4 0 24 := bq13_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq13_5_0 : Interval q13Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq13_5 : Interval q13Atlas 5 0 1 := bq13_5_0
set_option maxRecDepth 32768 in
theorem allq13 : ∀ k ≤ 5, ∀ i < count q13Atlas k, checkRow q13Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq13_3 i (by omega) hi
  · exact allq13_4 i (by omega) hi
  · exact allq13_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_2_0 : Interval q14Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allq14_2 : Interval q14Atlas 2 0 4 := bq14_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_3_0 : Interval q14Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq14_3 : Interval q14Atlas 3 0 6 := bq14_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq14_4_0 : Interval q14Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq14_4 : Interval q14Atlas 4 0 1 := bq14_4_0
set_option maxRecDepth 32768 in
theorem allq14 : ∀ k ≤ 4, ∀ i < count q14Atlas k, checkRow q14Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq14_2 i (by omega) hi
  · exact allq14_3 i (by omega) hi
  · exact allq14_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_2_0 : Interval q15Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq15_2 : Interval q15Atlas 2 0 3 := bq15_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_3_0 : Interval q15Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq15_3 : Interval q15Atlas 3 0 6 := bq15_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq15_4_0 : Interval q15Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq15_4 : Interval q15Atlas 4 0 1 := bq15_4_0
set_option maxRecDepth 32768 in
theorem allq15 : ∀ k ≤ 4, ∀ i < count q15Atlas k, checkRow q15Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq15_2 i (by omega) hi
  · exact allq15_3 i (by omega) hi
  · exact allq15_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_2_0 : Interval q16Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq16_2 : Interval q16Atlas 2 0 3 := bq16_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_3_0 : Interval q16Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq16_3 : Interval q16Atlas 3 0 6 := bq16_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq16_4_0 : Interval q16Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq16_4 : Interval q16Atlas 4 0 1 := bq16_4_0
set_option maxRecDepth 32768 in
theorem allq16 : ∀ k ≤ 4, ∀ i < count q16Atlas k, checkRow q16Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq16_2 i (by omega) hi
  · exact allq16_3 i (by omega) hi
  · exact allq16_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq17_3_0 : Interval q17Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq17_3 : Interval q17Atlas 3 0 1 := bq17_3_0
set_option maxRecDepth 32768 in
theorem allq17 : ∀ k ≤ 3, ∀ i < count q17Atlas k, checkRow q17Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq17_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_2_0 : Interval q18Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq18_2 : Interval q18Atlas 2 0 1 := bq18_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq18_3_0 : Interval q18Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq18_3 : Interval q18Atlas 3 0 1 := bq18_3_0
set_option maxRecDepth 32768 in
theorem allq18 : ∀ k ≤ 3, ∀ i < count q18Atlas k, checkRow q18Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq18_2 i (by omega) hi
  · exact allq18_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_2_0 : Interval q19Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allq19_2 : Interval q19Atlas 2 0 3 := bq19_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_3_0 : Interval q19Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allq19_3 : Interval q19Atlas 3 0 6 := bq19_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq19_4_0 : Interval q19Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq19_4 : Interval q19Atlas 4 0 1 := bq19_4_0
set_option maxRecDepth 32768 in
theorem allq19 : ∀ k ≤ 4, ∀ i < count q19Atlas k, checkRow q19Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq19_2 i (by omega) hi
  · exact allq19_3 i (by omega) hi
  · exact allq19_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_3_0 : Interval q20Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_3_32 : Interval q20Atlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem allq20_3 : Interval q20Atlas 3 0 39 := (concat bq20_3_0 bq20_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_4_0 : Interval q20Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allq20_4 : Interval q20Atlas 4 0 24 := bq20_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bq20_5_0 : Interval q20Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem allq20_5 : Interval q20Atlas 5 0 1 := bq20_5_0
set_option maxRecDepth 32768 in
theorem allq20 : ∀ k ≤ 5, ∀ i < count q20Atlas k, checkRow q20Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allq20_3 i (by omega) hi
  · exact allq20_4 i (by omega) hi
  · exact allq20_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 11 := bgb_4_0
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
theorem bgb_5_96 : Interval gbAtlas 5 96 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 107 := (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96))
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
theorem bgb_6_480 : Interval gbAtlas 6 480 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 501 := (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480))))
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
theorem bgb_7_416 : Interval gbAtlas 7 416 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 423 := (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_96 : Interval gbAtlas 8 96 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 127 := (concat (concat bgb_8_0 bgb_8_32) (concat bgb_8_64 bgb_8_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 22 := bgb_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_10_0 : Interval gbAtlas 10 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_10 : Interval gbAtlas 10 0 1 := bgb_10_0
set_option maxRecDepth 32768 in
theorem allgb : ∀ k ≤ 10, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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
  · exact allgb_10 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq0 (cert : Complete q0Atlas) : Lower true (roots q0Atlas) (target q0Atlas) 5 := by
  have ready : Ready q0Atlas (asRow q0Pos) (asRow q0Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq1 (cert : Complete q1Atlas) : Lower true (roots q1Atlas) (target q1Atlas) 5 := by
  have ready : Ready q1Atlas (asRow q1Pos) (asRow q1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq2 (cert : Complete q2Atlas) : Lower true (roots q2Atlas) (target q2Atlas) 6 := by
  have ready : Ready q2Atlas (asRow q2Pos) (asRow q2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq3 (cert : Complete q3Atlas) : Lower true (roots q3Atlas) (target q3Atlas) 5 := by
  have ready : Ready q3Atlas (asRow q3Pos) (asRow q3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq4 (cert : Complete q4Atlas) : Lower true (roots q4Atlas) (target q4Atlas) 6 := by
  have ready : Ready q4Atlas (asRow q4Pos) (asRow q4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq5 (cert : Complete q5Atlas) : Lower true (roots q5Atlas) (target q5Atlas) 5 := by
  have ready : Ready q5Atlas (asRow q5Pos) (asRow q5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq6 (cert : Complete q6Atlas) : Lower true (roots q6Atlas) (target q6Atlas) 5 := by
  have ready : Ready q6Atlas (asRow q6Pos) (asRow q6Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq7 (cert : Complete q7Atlas) : Lower true (roots q7Atlas) (target q7Atlas) 5 := by
  have ready : Ready q7Atlas (asRow q7Pos) (asRow q7Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq8 (cert : Complete q8Atlas) : Lower true (roots q8Atlas) (target q8Atlas) 5 := by
  have ready : Ready q8Atlas (asRow q8Pos) (asRow q8Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq9 (cert : Complete q9Atlas) : Lower true (roots q9Atlas) (target q9Atlas) 6 := by
  have ready : Ready q9Atlas (asRow q9Pos) (asRow q9Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq10 (cert : Complete q10Atlas) : Lower true (roots q10Atlas) (target q10Atlas) 5 := by
  have ready : Ready q10Atlas (asRow q10Pos) (asRow q10Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq11 (cert : Complete q11Atlas) : Lower true (roots q11Atlas) (target q11Atlas) 5 := by
  have ready : Ready q11Atlas (asRow q11Pos) (asRow q11Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 36, 38),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq12 (cert : Complete q12Atlas) : Lower true (roots q12Atlas) (target q12Atlas) 7 := by
  have ready : Ready q12Atlas (asRow q12Pos) (asRow q12Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq13 (cert : Complete q13Atlas) : Lower true (roots q13Atlas) (target q13Atlas) 6 := by
  have ready : Ready q13Atlas (asRow q13Pos) (asRow q13Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq14 (cert : Complete q14Atlas) : Lower true (roots q14Atlas) (target q14Atlas) 5 := by
  have ready : Ready q14Atlas (asRow q14Pos) (asRow q14Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq15 (cert : Complete q15Atlas) : Lower true (roots q15Atlas) (target q15Atlas) 5 := by
  have ready : Ready q15Atlas (asRow q15Pos) (asRow q15Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq16 (cert : Complete q16Atlas) : Lower true (roots q16Atlas) (target q16Atlas) 5 := by
  have ready : Ready q16Atlas (asRow q16Pos) (asRow q16Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq17 (cert : Complete q17Atlas) : Lower true (roots q17Atlas) (target q17Atlas) 4 := by
  have ready : Ready q17Atlas (asRow q17Pos) (asRow q17Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 2 zero, 16, 20),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq18 (cert : Complete q18Atlas) : Lower true (roots q18Atlas) (target q18Atlas) 4 := by
  have ready : Ready q18Atlas (asRow q18Pos) (asRow q18Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq19 (cert : Complete q19Atlas) : Lower true (roots q19Atlas) (target q19Atlas) 5 := by
  have ready : Ready q19Atlas (asRow q19Pos) (asRow q19Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 0, 1),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundq20 (cert : Complete q20Atlas) : Lower true (roots q20Atlas) (target q20Atlas) 6 := by
  have ready : Ready q20Atlas (asRow q20Pos) (asRow q20Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 11 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8feeefeeafeeafaa8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certq0 : Complete q0Atlas) (certq1 : Complete q1Atlas) (certq2 : Complete q2Atlas) (certq3 : Complete q3Atlas) (certq4 : Complete q4Atlas) (certq5 : Complete q5Atlas) (certq6 : Complete q6Atlas) (certq7 : Complete q7Atlas) (certq8 : Complete q8Atlas) (certq9 : Complete q9Atlas) (certq10 : Complete q10Atlas) (certq11 : Complete q11Atlas) (certq12 : Complete q12Atlas) (certq13 : Complete q13Atlas) (certq14 : Complete q14Atlas) (certq15 : Complete q15Atlas) (certq16 : Complete q16Atlas) (certq17 : Complete q17Atlas) (certq18 : Complete q18Atlas) (certq19 : Complete q19Atlas) (certq20 : Complete q20Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0x55550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq0 certq0)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0x3333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333000033330000333300003333 : Sig) 5 :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq1 certq1)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f : Sig) 6 :=
    slice_correct (ms:=fixRows 12 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq2 certq2)
  have q3 : Slice true (roots gbAtlas) (target gbAtlas) (0x55555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 1 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq3 certq3)
  have q4 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f : Sig) 6 :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq4 certq4)
  have q5 : Slice true (roots gbAtlas) (target gbAtlas) (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c : Sig) 5 :=
    slice_correct (ms:=fixRows 4 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq5 certq5)
  have q6 : Slice true (roots gbAtlas) (target gbAtlas) (0x333333330000000033333333000000003333333300000000333333330000000033333333000000003333333300000000333333330000000033333333 : Sig) 5 :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq6 certq6)
  have q7 : Slice true (roots gbAtlas) (target gbAtlas) (0x5050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505050505 : Sig) 5 :=
    slice_correct (ms:=fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq7 certq7)
  have q8 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff0000 : Sig) 5 :=
    slice_correct (ms:=fixRows 32 16) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq8 certq8)
  have q9 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f : Sig) 6 :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq9 certq9)
  have q10 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : Sig) 5 :=
    slice_correct (ms:=fixRows 16 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq10 certq10)
  have q11 : Slice true (roots gbAtlas) (target gbAtlas) (0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555 : Sig) 5 :=
    slice_correct (ms:=fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq11 certq11)
  have q12 : Slice true (roots gbAtlas) (target gbAtlas) (0x44444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444444 : Sig) 7 :=
    slice_correct (ms:=fixRows 1 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq12 certq12)
  have q13 : Slice true (roots gbAtlas) (target gbAtlas) (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff : Sig) 6 :=
    slice_correct (ms:=fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq13 certq13)
  have q14 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff : Sig) 5 :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq14 certq14)
  have q15 : Slice true (roots gbAtlas) (target gbAtlas) (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff000000000000ffff00000000 : Sig) 5 :=
    slice_correct (ms:=fixRows 16 32) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq15 certq15)
  have q16 : Slice true (roots gbAtlas) (target gbAtlas) (0x550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055005500550055 : Sig) 5 :=
    slice_correct (ms:=fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq16 certq16)
  have q17 : Slice true (roots gbAtlas) (target gbAtlas) (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : Sig) 4 :=
    slice_correct (ms:=fixRows 8 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq17 certq17)
  have q18 : Slice true (roots gbAtlas) (target gbAtlas) (0x555555550000000055555555000000005555555500000000555555550000000055555555000000005555555500000000555555550000000055555555 : Sig) 4 :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq18 certq18)
  have q19 : Slice true (roots gbAtlas) (target gbAtlas) (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000cccccccc : Sig) 5 :=
    slice_correct (ms:=fixRows 32 2) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq19 certq19)
  have q20 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff : Sig) 6 :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (boundq20 certq20)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl, build_valid q3 [] rfl, build_valid q4 [] rfl, build_valid q5 [] rfl, build_valid q6 [] rfl, build_valid q7 [] rfl, build_valid q8 [] rfl, build_valid q9 [] rfl, build_valid q10 [] rfl, build_valid q11 [] rfl, build_valid q12 [] rfl, build_valid q13 [] rfl, build_valid q14 [] rfl, build_valid q15 [] rfl, build_valid q16 [] rfl, build_valid q17 [] rfl, build_valid q18 [] rfl, build_valid q19 [] rfl, build_valid q20 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276812456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_44276.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[5,6]⟩,⟨.or,[4,7]⟩,⟨.or,[5,6]⟩,⟨.and,[1,8]⟩,⟨.and,[2,3]⟩,⟨.or,[10,11]⟩,⟨.or,[1,4]⟩,⟨.and,[0,13]⟩,⟨.or,[9,14]⟩,⟨.or,[0,12]⟩,⟨.and,[15,16]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276812456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276812456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 17⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 12 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_44276

open PEqualNP.Outside.L_meta_44276 in
theorem PEqualNP.Outside.L_meta_44276 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276812456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276812456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allq0 allq1 allq2 allq3 allq4 allq5 allq6 allq7 allq8 allq9 allq10 allq11 allq12 allq13 allq14 allq15 allq16 allq17 allq18 allq19 allq20 allgb)
