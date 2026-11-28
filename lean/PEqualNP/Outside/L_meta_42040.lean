import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42040.Low
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def limbs64 (ws : List Nat) : Nat := ws.foldl (fun v w => (v <<< 64) + w) 0
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
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

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

private lemma extract {u target} (gs : List Gate) (w : List Sig)
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

private lemma b_read (i) (w : List Sig) (j : Nat) :
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
  simp only [b_read]
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

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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

def inputs : List Sig := [(BitVec.ofNat _ (limbs64 [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa])),(BitVec.ofNat _ (limbs64 [0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc])),(BitVec.ofNat _ (limbs64 [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0])),(BitVec.ofNat _ (limbs64 [0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00])),(BitVec.ofNat _ (limbs64 [0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000])),(BitVec.ofNat _ (limbs64 [0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0x0,0x0]))]
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
def varsX (m : Nat) : List Sig := vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else if (m >>> 9).testBit j then one else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
 (x 0 &&& x 1 &&& x 2 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => (limbs64 [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1])
  | 1 => (limbs64 [0x1,0x0,0x1,0x0,0x1,0x0,0x1])
  | 2 => (limbs64 [0x1,0x1,0x0,0x0,0x1,0x1])
  | 3 => (limbs64 [0x1,0x0,0x0,0x0,0x1])
  | 4 => (limbs64 [0x1,0x1,0x1,0x1])
  | 5 => (limbs64 [0x1,0x0,0x1])
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
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

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := (hints >>> (6*i)) &&& 63
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

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

abbrev Bits := BitVec 1024
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1024 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1024 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1024 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1024 → Row) (x : Decor) := x.2 = pairSig r s x.1
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
def asRow (cols : Nat → Bits) (i : Fin 1024) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
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

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else if (m >>> 9).testBit j then BitVec.allOnes 1024 else 0
 (x 0 &&& x 1 &&& x 2 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else if (m >>> 9).testBit j.val then BitVec.allOnes 1024 else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · by_cases pin : (m >>> 9).testBit j.val = true
    · simp only [vertex,if_neg hh,if_pos pin,bit_one,BitVec.getLsbD_allOnes,decide_eq_true i.isLt]
    · simp [vertex,hh,pin,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else if (m >>> 9).testBit j then BitVec.allOnes 1024 else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

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

def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])

def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2

theorem walkCompact_faithful (depth path : Nat) (ws : List Decor) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ (walkCompact depth path ws hist).1, faithful r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)

theorem rowWires_faithful (bank : List Decor) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, faithful r s v) :
    ∀ v ∈ rowWires bank mask, faithful r s v := by
  induction bank generalizing mask with
  | nil => simp [rowWires]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold rowWires
    split
    · exact List.forall_mem_cons.mpr ⟨hv.1, ih _ hv.2⟩
    · exact ih _ hv.2

def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2

theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok

abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)
def CompactGrid.mask (g : CompactGrid) := g.1
def CompactGrid.top (g : CompactGrid) := g.2.1
def CompactGrid.pos (g : CompactGrid) := g.2.2.1
def CompactGrid.neg (g : CompactGrid) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)

def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst

abbrev Domains := Array (Sig × Nat)
abbrev Perms := Array (List Nat)

def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)

def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))

theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj

def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))

theorem applySwaps_valid {T k xs} {p : List Nat}
    (ok : autoOK T (p.map swapRows).reverse = true)
    (ih : Impossible true T k (List.toFinset xs)) :
    Impossible true T k (applySwaps p xs).toFinset := by
  cases p with
  | nil => exact ih
  | cons a p =>
    have := rotate_excluded ih (((a::p).map swapRows).reverse) ok
    simpa only [List.reverse_reverse,applySwaps] using this

def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)

theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction

theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

abbrev NodePool := BoundPool × List Sig × List Sig × Nat

def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))

def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))

def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))

theorem cachedCut_ok {u p k rest op front}
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedPoolCut u (cacheOnePool u front p) k rest op = true) :
    scalarPoolCut u p k rest op = true := by
  let miss := front.filter (fun a => !(availableB u p.domain p.wires a))
  let extra := !(availableB u p.domain p.wires (choiceVal op))
  have know (w) (hm : w ∈ front) (hn : w ∉ miss) : availableB u p.domain p.wires w = true := by
    by_contra h
    apply hn
    apply List.mem_filter.mpr
    exact ⟨hm, by simpa using h⟩
  dsimp only [cachedPoolCut, cacheOnePool] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  change ((_ && miss.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!miss.contains op.2.1 && !miss.contains op.2.2)))) = true at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at ok
  change ((_ && rest.all (availableB u p.domain p.wires)) && (!extra || choiceOK u p.domain p.wires op)) = true
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨ok.1.1, ?_⟩, ?_⟩
  · intro w hw
    apply know w (sub w hw)
    intro no
    have contra := ok.1.2 w no
    simpa [hw] using contra
  · rcases ok.2 with h | ⟨allowed, ah, bh⟩
    · exact Or.inl h
    · right
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨allowed, know _ ha (by simpa using ah), know _ hb (by simpa using bh)⟩

def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))

theorem cachedClose_sound {u raw T} {pools : List BoundPool} {links k rest op front}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op::rest).Nodup)
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedClose u (pools.map (cacheOnePool u front)) links k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  simp only [cachedClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨c,hc,cut⟩ | ⟨w,hw,eq⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact scalarPoolCut_sound (pValid p hp) nd (cachedCut_ok sub ha hb cut)
  · rw [sameWords_sound eq]
    exact lValid _ _ hw

abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))
def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)

def cached_moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
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
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h

def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))
def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs

theorem cached_all_binary {ctx ws} (h : cached_testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [cached_testAll,Bool.and_eq_true,cached_testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem cached_testPair_at {ctx a b d} (h : cached_testPair ctx a b d = true) (ka kb : Bool) :
    cached_evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [cached_testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem cached_unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem cached_kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,cached_mem_delone wn,cached_mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem cached_binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (cached_moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [cached_moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_kept_value nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2

def chartBlock (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && chartBlock test start n

theorem chartBlock_at {test start n} (ok : chartBlock test start n = true) (i)
    (a : start ≤ i) (b : i < start+n) : test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [chartBlock,Bool.and_eq_true] at ok
    by_cases h : i=start+n
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega)

theorem chartBlock_join {test start a b}
    (left : chartBlock test start a = true) (right : chartBlock test (start+a) b = true) :
    chartBlock test start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [chartBlock,Bool.and_eq_true] at right
    simp only [Nat.add_succ,chartBlock,Bool.and_eq_true]
    constructor
    · change test (start + (a+b)) = true
      rw [← Nat.add_assoc]
      exact right.1
    · exact ih right.2

theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))

theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,_,_,l,base) := s
  let ms := fixRows ((m &&& 63) ^^^ ((m &&& 63) &&& (q ||| o))) o
  earlier.contains (q,base) && (l == base) && properB (graphGoal q) &&
    checkMap ms (vars m) (graphGoal m) (vars q) (graphGoal q) &&
    (movedWord ms (subcube z o) == one)

theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  rcases s with ⟨z,o,q,sp,hi,l,base⟩
  simp only [certifiesSlice,Bool.and_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨earlier,rfl⟩,pr⟩,mapped⟩,all⟩ := ok
  exact slice_correct mapped all (proper_of _ pr) (prior _ earlier)

theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)

theorem compactAutos_valid {T : Sig} {ps : Perms}
    (ok : ps.toList.all (fun p => autoOK T (p.map swapRows).reverse) = true) :
    ∀ p ∈ ps, autoOK T (p.map swapRows).reverse = true := by
  intro p hp
  exact List.all_eq_true.mp ok _ (Array.mem_toList_iff.mpr hp)

theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot
def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n

def samplesP1069 : Nat → Bits
  | 0 => 0xecf5ef0fd3e86bf0
  | 2 => ~~~(0x25014ba1810e707a : Bits)
  | 3 => 0xb9ff58afafa617ca
  | 5 => ~~~(0x804000002a00380 : Bits)
  | _ => 0

def samplesQ1069 : Nat → Bits
  | 0 => 0x138a289ac08caad0
  | 2 => ~~~(0xdabdb2d9ebd4727e : Bits)
  | 3 => 0x4618664d0a072742
  | 5 => 0x82000002140002c
  | _ => 0

def compactPerms1069 : Array (List Nat) := ([[], [50], [32], [32, 50], [48, 50], [48]] : List (List Nat)).toArray

def compactDomains1069 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords1069 : Nat → Nat
  | 0 => (limbs64 [0xe195784,0xce69626ff03fc0ff,0x214d74a3d10ff02,0x64f3c79d0bff030d,0x4318e76135600e78,0x97e7464190cc5702,0xb3699a5829d5a0a9,0x95ad67fc0ff00087,0x412080ebe5c94cff,0x620f64b413ff02,0xe25e255dbff0339,0xc594401285620166,0x169c00005b6db6d7,0x5f9640c102c40a90,0x3c416904200c00a0,0x1801800c4bffe001,0x9f6e67f801877f80,0xe847f80309be0bad,0x2f688b25a4a1d48d,0x3bfe027afeccf09,0xb8d0ff807f1ff81f,0xe035abfe07f81fe0,0x7b15754e28526ddd,0xcffe0052b3885800,0x1fffffffff00e00d,0xc00e005004004f])
  | _ => 0

def compactCount1069 (k : Nat) : Nat := match k with
  | 5 => 1
  | 4 => 7
  | 3 => 7
  | _ => 0

def compactPath1069 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | 4 => readCompactBits compactWords1069 (6 + 12*i) 12
  | 3 => let v := readCompactBits compactWords1069 (723 + 14*i) 14
    (readCompactBits compactWords1069 (675 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive1069 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords1069 (0 + 4*i) 4
  | 4 => readCompactBits compactWords1069 (90 + 5*i) 5
  | 3 => readCompactBits compactWords1069 (821 + 6*i) 6
  | _ => 0

def compactPoolIDs1069 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords1069 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords1069 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 4 => let v := readCompactBits compactWords1069 (125 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords1069 (125 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 3 => let v := readCompactBits compactWords1069 (863 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords1069 (863 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket1069 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let d := readCompactBits compactWords1069 (139 + 4*(i % 8)) 4
    let off := ((i/8 + d) % 36)
    let v := readCompactBits compactWords1069 (171 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 3 => let d := readCompactBits compactWords1069 (877 + 5*(i % 13)) 5
    let off := ((i/13 + d) % 49)
    let v := readCompactBits compactWords1069 (942 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | _ => []

def samplesP16398 : Nat → Bits
  | 1 => ~~~(0x410a : Bits)
  | 2 => ~~~(0x10a4 : Bits)
  | 3 => 0xdfae
  | _ => 0

def samplesQ16398 : Nat → Bits
  | 1 => 0x4830
  | 2 => ~~~(0xedfc : Bits)
  | 3 => 0x240c
  | _ => 0

def compactPerms16398 : Array (List Nat) := ([[], [50], [33], [33, 50], [49, 50], [49]] : List (List Nat)).toArray

def compactDomains16398 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords16398 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount16398 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath16398 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive16398 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords16398 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs16398 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords16398 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords16398 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket16398 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP16399 : Nat → Bits
  | 0 => ~~~(0x258b00e2f8 : Bits)
  | 1 => 0xdef38fd162ac
  | 2 => 0xbf653f6aa1d8
  | 3 => 0xefaccbbcc272
  | _ => 0

def samplesQ16399 : Nat → Bits
  | 1 => 0x280468c00684
  | 2 => 0x420a85080918
  | 3 => 0x141112301062
  | _ => 0

def compactPerms16399 : Array (List Nat) := ([[], [50], [33], [33, 50], [49, 50], [49]] : List (List Nat)).toArray

def compactDomains16399 : Array (Sig × Nat) := ([(subcube 1 0, 4)] : List (Sig × Nat)).toArray

def compactWords16399 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount16399 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath16399 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive16399 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords16399 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs16399 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords16399 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords16399 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket16399 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP46 : Nat → Bits
  | 1 => ~~~(0x408700216124 : Bits)
  | 2 => 0xef8f7fe76fec
  | 3 => ~~~(0x200870060cc8 : Bits)
  | 5 => ~~~(0x0 : Bits)
  | _ => 0

def samplesQ46 : Nat → Bits
  | 1 => 0x48c52694369a
  | 2 => 0x11f808c07fe0
  | 3 => ~~~(0xdde6c4fe49d8 : Bits)
  | 5 => ~~~(0xfbdbea95fea2 : Bits)
  | _ => 0

def compactPerms46 : Array (List Nat) := ([[], [50], [33], [33, 50], [49, 50], [49]] : List (List Nat)).toArray

def compactDomains46 : Array (Sig × Nat) := ([(subcube 0 32, 4)] : List (Sig × Nat)).toArray

def compactWords46 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount46 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath46 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive46 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords46 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs46 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords46 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords46 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket46 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP47 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x990110004a087,0xbe4000030a6022fa,0xc8041a780040040c,0xc26d57d40008f13c])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x7d8bfd377fe819,0xfa47fc9f7ff7f5ea,0x48e186781ffbeeed,0xc1ecd1d301ee6b2c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x6f53ffef8df1a6,0x9c87ff6fbbf9fa31,0xcb0e38b81f7cbf7f,0xc61f0edc017ff070]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x5eb3fff8f6c6c7,0x2747fff3cf7f3ede,0xb4145b401feff79e,0xfa61772401de959c]))
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0x4000c20004000,0x1111000,0x128a200,0x1460000])) : Bits)
  | _ => 0

def samplesQ47 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x766fcef7f55eb8,0xa1bf6873395edec7,0x73f7dabe91df347c,0xe27d47eb740afd7e])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x275024ac0c3ea,0xf9ec136d32482a5,0x144f08555bba4c48,0x88ca935249ae4b28]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x10ae0120f32678,0x66686c70f4e033c2,0xc813c180fc483273,0xc012afd4857bf040]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x214c5443193b2a,0xc87319341e902c1a,0x51606c9b3747a19c,0x28817b4412de149c]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4008621204000,0x52001000a4045,0x134800800951424,0x422400295400ad76]))
  | _ => 0

def compactPerms47 : Array (List Nat) := ([[], [50], [33], [33, 50], [49, 50], [49]] : List (List Nat)).toArray

def compactDomains47 : Array (Sig × Nat) := ([(subcube 0 2, 6), (subcube 0 4, 6), (subcube 0 8, 6), (subcube 0 32, 5), (subcube 1 0, 5), (subcube 1 32, 4)] : List (Sig × Nat)).toArray

def compactWords47 : Nat → Nat
  | 0 => (limbs64 [0x2a8600202002f717,0x61f4bf126f16e1ec,0xb69b66be326155c3,0x592d6a54ad22cfa4,0xdb4aac8147245342,0x2bf9be23c2b9ab73,0xb39b22af9ae2aba2,0x9b26925924aa2220,0x39cc98117215292a,0x9018e98d38998820,0x6283b80082439401,0x184e1a0887031072,0x8485510b49898128,0x41198949882029a,0x9381693794410106,0x6316937904c08062,0x6041000da1604041,0xb0202a1810106860,0x4041b40368402230,0x2d1a1a00a1a36b04,0x4009016b40112003,0x221816a1a21910d6,0x21a4430810008168,0x62605ad20409194,0xc030a48112060ca,0x9810620940c1944c,0x94e208089010e13,0x802409e80189813a,0xe119d8238820204,0x47200acbffffdfff,0xfffdfbf7eedfbbff,0xffdffffffffffeff,0xfff7feffbffeffff,0xffeffffffbf7fbff,0xeffffbfffdfff7ff,0xdff144c111c5138a,0x26144f281a5034a0,0xd143028605098a13,0x142b191032202458,0x8a0112022004594,0x8a29145224a44148,0x8291011a8a351468,0x28d051aca0514092,0x8125020a0a089601,0x280258a4b1494292,0x8525043a045600ac,0x5158a2a145428802,0x188a2c24c0480140,0x402402200400198b,0x4a5d1f179f559404,0xcbff03fc0ff03fc0,0xff039091cc7fc045,0x5eda34b1ffc0a947,0xa337839f6f0707fc,0xff00229f20cb6bf,0x3200077cede17c2,0x783f259884088010,0x42e0a64290e0a421,0xec864210ec6b042,0xeca64210aec6864,0x90026430ae806430,0xea09ffffffffffff,0xfe12012602402202,0x2011400800e49f])
  | 1 => (limbs64 [0x9b59724ff00370ef,0x28f4d8f32583c228,0x71958ec83355f801,0x578c52be048a27e3,0x98b69dffe003f7e9,0x617bb63fad194d6b,0x3a0b768dc8ad9af5,0xe6faf9981cc2dd85,0x3b803422988cf03b,0x31fb4be5fc937688,0x911bb6407fc007a9,0xbc10cf00c65a611a,0xc8763428977682e5,0xc00ff00619670e35,0xfe0052298f1c1456,0xcf871ec93ea1abfc,0x1fe00ff007f803f,0xc01d0b0ff006d844,0xb867d0adff006bac,0xcea47fe00cf2d7f8,0x220442c923b0a3c,0x917fc01fe00ff000,0x486e0d41dc648c32,0xaba3eb519c70b623,0xa410aa2438045c62,0x76b732920872e5f7,0x794283994430ea1a,0xeb8f4e46f698bb00,0x1907afd415285155,0x15c8534eb5e0c173,0xeeb8d02df04e885d,0xfe00ff006e1dbfc0,0x1730d43160300ffc,0x3ca7249a6c086b,0xc2b3257df26a8345,0x8c569a4b2828ff80,0x4113fe001c597f8,0x3fc00cd17286dc3,0x5bfc00a602338e7,0xf803fc01fe00df23,0x88b73fc01fe00ff0,0x7f802ea41c46b05,0x98b9bfed0b76cfb1,0x27bf3cdc363a9420,0xdd7177c89dc6ac2b,0x8c371ff803fc0045,0x35327429c3c9e275,0x49e6d20e63c61c20,0xf68eff0021494213,0x27509e8554825ec5,0xd33a12b1975e08c8,0x4ce2b9f80fdf32d,0xb1a9903d753e9e02,0x4e255552bec997f8,0x4d48d7119c0385,0xcd89a678094cc3e7,0x98bf85c17b29de1c,0xe9c987d9cc8d81ab,0x81891c3010702246,0x120649e0048301,0x6850e2cd0100,0x1870014042ab0000,0xd000048484000030,0x140000002080000])
  | 2 => (limbs64 [0xf77a7ef67e7efbba,0x7efb3e7f7afa7e7f,0xe7f3f37777e6f6f7,0xf3f3e7e76f7b7a7e,0x7f767e7edef6fb7b,0x7a7e7f767f5e5f5e,0x7f767f7af6fa7f6e,0x7e7db8c36630d94c,0x2e310b8c32e304b,0x4c08a31120c25e30,0x8a8c22a308a0c25a,0x30968c25830a08c1,0x8231604c52231484,0xc51011048c312308,0x44c07e305f8c57d3,0x1500c3403050cc54,0x31408c30230408c,0x50131638c174091d,0xca476311d8c37530,0x130244c30d3cc04c,0x300e4a43a30ce8c1,0x3a300e4c03a310e8,0xc43a30ce8c33a30c,0xe4c33a304e8c0393,0xe4c03930030440,0xe31030c40c10dc02,0x373191c02472311c,0xc471300d8c13409,0xd8c434310d8c135,0x30218c38630558c3,0x572811c044501118,0xc44431110234430c,0x98c12528098c51e3,0x478c51d31414c57,0xa011e8c23d300f8c,0x43e308f4c0193006,0x8c51931420440a01,0x20040a29020a408,0x10c28c30830c28c0,0x9301402268089a0,0x446a011a0046a311,0xa0c46808da8c3683,0xcc8c332304c4c03,0x2010c00432310c0c,0x43008cc8c33230cc,0x8c33130cc0c33230,0x4c4c03130058c115,0x30054c56010d88c3,0x6030f29008b28009,0x328008b19008b010,0x8a29200629008a2,0x8c08a28b09228a00,0x6288092288006287,0x1228401228008a0,0xa00529008928009,0x1280089010088292,0x429008828c0882,0x8a00428809028501,0x280088190088112,0x410e00410c0040,0x9008808c08808a00,0x401200401008a203,0xd52c2da437f802f4,0x3ba721ec4aff803c])
  | 3 => (limbs64 [0xa141810600007001,0x8050098225035c1,0x8c14281802210191,0x2200066300000a14,0x30b822c142810000,0x9830e0040a040805,0x11c48e0304007020,0x20c19d14083847c0,0x106204400900140,0x5260002f0038005,0x2c098000c3821e,0xec1810c002000674,0x600020408d030041,0xe0200fad0c007811,0x6083920214080061,0x800e121038010009,0x8000000132018f07,0x2604002002818100,0x400300585871004,0x811d4751d4f41d0,0xf33c8f11c4713c07,0x5b8ed1b4ec3acea,0x1a8e999563584e07,0x74dc5685a5615655,0xd3348d13414e334,0x4d1354b12dc8120c,0x7318c5114c430cc2,0x30441300402fc3f0,0xfcbe0f83e2f53b0e,0xcba2e6b44c8320c8,0x320c8322c4b00c0a,0xf2b82e2b4ac2ac2b,0xac2b0ada829c272,0x98a5290a32882228,0x4a00809f2781e274,0x9c07218458160589,0x5250140509304c13,0x4449023c0f03c0f2,0x390c0310a0288922,0x8701c0721885014,0x84010040108300c8,0x2008020088100480,0x417c14d34134c11,0x250e500100194106,0x505004212571c041,0x9659419651010840,0x8102596594196504,0x2044964041602340,0x400810c40650650,0x810020650840c040,0x1041020042101001,0x4404004311409f0,0x104308208104202,0x7e7e7ebedef6fabe,0x7e7e7f77767f7776,0xf67e7e7e7fe6f7e6,0xf6f67e7edef67e7e,0xdef67e7ef7b73e7e,0x7e7fb6defafb3ede,0xf6fafa7f3e7f5e5f,0x5f777a7f7a7be6f6,0xf7c7d75f767e7e7e,0xf7767e7f767edef6,0xdf7b7b7a7e7f767e])
  | 4 => (limbs64 [0x429fe704555908a8,0x7902b7d3685f317b,0x6b23b606f4ac4b10,0x9e89d66f23ff0016,0x2d2565046846f39d,0x38c8b74a969cf5c9,0xbfab31987538e505,0x5b8b7fc00017c7fc,0x984f1db0ef4188,0x20e75238e9dfdbac,0xebfc004d63ebee73,0x1d681492c51d7fc0,0xe20bc4163d99c86,0x648ff001c6d6ff00,0x3fc00f9510b6870b,0xc2ffc00ff003fc00,0xd65fbfc0028a7113,0x66d551506d87876b,0x1ca6ff003fc00ff0,0x14a895a29e1ef7,0x58fbfc00ff0035e3,0x9e13b9b55aff003f,0xc0022a3ffc00c61a,0xbbdb310458f4e026,0x44f64dcff00068f7,0xd5ce6f4bf0fd64c6,0x6dff003fc00d0747,0x9129bcd824e6092d,0x70a5f61b5848517f,0xf0008734ff003fc0,0x4eb685e33e3c999,0x23c66c79bdb73374,0x8a0f3307f3fc0091,0x6ee88eb9c27af855,0xe20646742a1a5aa4,0x17bb4a816dc1920b,0x212f8e3e9c4ad087,0x50a3f292a9c8983,0x183ebac2b0d4ab30,0xd1b1e9d4b29c4d4c,0x9d96700ffc00f5bf,0xc00f6363bf0139d4,0xc72ef4b0f1f3e52d,0xa3190505e7f1e0d9,0xeef0026e497ff003,0xfc0039171b686074,0xad9e4ab22dec327b,0xf4450dc641597a68,0x4752a6ec2971910d,0xd6a670fbd04128c9,0x3700ab42d3fc00b6,0x34a9eaaff0021c7b,0x84d8bfc00ff003fc,0xff003fc0075312,0xaa7ed56e16828960,0x4002bc6773d1b08a,0x937c03357d7313f5,0x8ff0016cda834ef9,0x17feb773a368ff00,0x7238ff003fc00bd,0x379f10582c20036,0x10b0d00f89a70004,0x200061c7810821f8,0x113b81280e289000])
  | 5 => (limbs64 [0xf4d3226298bff003,0xd9782ccf7aca1124,0x75c4fbe3bc8869ec,0x3945d967b859a3d6,0xd9f8087835a784ee,0xc725d843955b15c0,0xa96f95530f0e5d5a,0xda9076bff0008943,0xe4a855eb984a0527,0x436520375ca06a4d,0xab04626c7fc0008a,0x23fc00c406d6474f,0xf00328aeed76f09e,0x7b3ccffc008d1313,0x8850fb8942f6ff00,0x3fc0046143d699ff,0x3def3cdaeaa540,0x692427f16c13aa39,0xb6885638e474ba41,0x3bff000ab2a6c1,0x620c34ff003fc008,0xc94320815c4565ed,0xf1e1ce253db2309d,0xb2f7fb966ae04788,0xf4ac51255226e8f,0x755cf4a4b791cd9,0x3b2cd7cb5845199b,0x50b6e492a4f2303,0x3dd677a45fd21962,0xe796546d25246148,0x13b3d314a7c6a6e0,0xedb53dd82c540868,0x1700e7c8725ade7a,0x3bc7796d4c08e279,0x4f9994c2b7408e66,0xc6a8a948e3c1c336,0xfc931e720de56916,0x4938d35560e80b74,0x2fba8d183c6d89c1,0xfb03648c46c95b2c,0xedfa32b0beb5a49c,0xb677a31b884a1e1a,0xf1f3f2514f1523a5,0x1a29ec3095e42519,0x17d0415ed7b550bc,0xf87cb24ecc80836f,0xd194e97353b21537,0x7c80a0c535811883,0xbbe04f503a7a41dc,0xd40bb0718c8453b,0x36139aaf6aed8a55,0xb2a7b80c7c605f31,0x9b07729096bdfb5f,0x5ba389624e962af8,0x4d7c9ae5487d609a,0x3657f9ce0e457571,0x974eb65f659c4ff3,0xd144dc4fa83105b,0xac386291427fb456,0x9019e89de17c3bd5,0xae9e66039614d3b9,0x2d770f18a27fc00,0xc443ffc00ff00311,0x854e8c3fc005e608])
  | 6 => (limbs64 [0x32cd9f73bbf3454d,0xecb33b640449a778,0x309b38d2bfc00eaa,0xd2d2d4ef22af35bf,0x8bb2da26ab63848d,0x89249eea5651c4b7,0xcbe88dbdea3b329,0x1e0afb7d2424fd84,0xb8400a7ab499665c,0xff000574760d3f36,0x49d2b8d2e120708d,0x272b1b86ffc00ff0,0x894850af5f833b,0x1c7546d79a0c3fc0,0x1e77680d75d327c,0xc47aecc47203ff00,0x2f76943aa3fc0024,0x1495a32debaa6a09,0xbbcca0ab029c8ab1,0x8c8033732cc0428e,0x65cec5cc1f015b2d,0x47fc00ff001cce89,0xdb1bfc00612c25a0,0xe971e2d9fd239ad,0xdf745d8ce09a00d5,0x48c13373c21344ff,0xf313ff003fc00,0x5e4c7fc000847ffc,0x5c022858df3a61,0xf173ab4dc1964f11,0x598b644033ffc00f,0x8247fc00ff003fc0,0xff0026346ff0025,0x40fff000e0ca2a4a,0x3d215ff0029b151d,0x6127ad09f9abfc00,0xff002ecb1b1c2a35,0x97228228678b3c33,0xbe4e1d566832e213,0x5626d3cd267b34d8,0x343426d5bb7d4ba2,0x1f23c91f28a4d380,0x1fac8909671b8f46,0xf5b11ff001fce420,0x6a7fc00ff003fc00,0xff003ccc7bcc83c8,0x83ff003fc00ff003,0xfc00d33166176ff0,0x3fc00ff003496c4,0x7297853aff00134b,0xcff003fc00accdff,0xc00ff0019debff00,0x3fc00ff003588dcc,0xd51a93f229a3fc00,0x8f1c46c6eff000b5,0xb57755ccf6585004,0x314772b64ab57ff0,0x1149fff003fc001,0xc07e2f4c1740f847,0x6c43a507067f98d5,0xc056b7c3b48f6d58,0x1a9e55141db8e10e,0x74f1c7e6224daa6f,0x93b93580668abbbd])
  | 7 => (limbs64 [0x18680db05f22f3fc,0x29be763fc0041,0x25daab3161eb08f2,0x5306b76a3f6ad907,0x2c6afffc03fc03fc,0x3352d53681038b8,0x1ffc03fc01e5294a,0xcffc01d01b107585,0x4508c0401c10001,0x6e9000d620305a00,0x14700e0c6005204,0x1034500a0004,0x4444444444b33a22,0x2222222229111800,0x6ae47a2f178,0x7e572d96cb65b393,0x99e5c6e31d8f55aa,0xd5c8bf463d599e5e,0x2b31e8bc7ba396cb,0x6572d9c8ea138329,0xc188e39871c339ac,0x98748c3a261ca30e,0x498728c13a732938,0xb1c850e46470b13,0x8351c6e0e37070b6,0x38c6086fce632728,0x139889c044e50a73,0x2e38d69c02043bc0,0x25c012a98718c38c,0x60a638728228008a,0x31719008a3170100,0x8a30c28a00630429,0x8a30428a006300,0x2900893022900893,0x29008930028a00,0x5290290089280280,0x890112800883112,0x8008831028c08831,0x28a00431008c088,0x30e2880043082850,0x1011008c08811008,0xa00410c08c08810c,0x8a00408d2800880,0x8c28a00401028a00,0x401008a00726f0ff,0x3fc00ff001462c,0xff0031d25511fd73,0x2d2b3e74807187a9,0xdcd4096fbfc00e86,0x47fc009eb6cd8c11,0xe92e3f2c6b038ae4,0x6f99eb46e6a84623,0x96221675487d3cc1,0xc426276ae04a1109,0x4ce3ca251376d68b,0x5d68df8548352749,0x52b9030395e7cc27,0xa8b834d776f48cf0,0xc54c96ff000bb5e5,0x38694edd03aed29d,0x84e103fc006f1642,0x2a0762da6032b82a,0xf749d408a84e6948,0x7cffc00145cb7acf])
  | 8 => (limbs64 [0x105ff8ff1f,0xe1a0f6d09c140039,0x10c08c08bfc0062,0x47fc03fc013cd774,0x28edc3504529a756,0xe7fc029c8e9d8bfc,0x32e7ffc03386b7d,0x9cd107b9c7fc034b,0x7244d1a172401449,0x411c51acf68e668f,0x5cb6352f397a6888,0x4f88eaa9d93b7795,0x794b2bfc02099975,0x1ffc026e7af9397e,0xe2d822ea756508d8,0x757547fc038d11f2,0xc3b567234326f761,0xa19e4245176aea9c,0xbc62933b44525662,0x2d1e07248be94b44,0x5bdec8c0b8fa8000,0xb3a042f66db6effc,0x1ace1161625aae1,0x5a5dac565bb6f98d,0x4c9d3e6ca7fc03cc,0x62a0ffc027b17fc,0x14534c25ffc001a,0x4bfc0260a1831221,0xd0b9fe78fbfc0279,0xf52cfffc001b524c,0x2469922e4d4130fa,0x9d244a7225609a8d,0x7ffc02b6707284cc,0x2ef100bb64adbb71,0xdffc03fc02fb23fc,0x11080d8f100ed8e,0xb2521d6472e52239,0xf3054076c7f5971,0x9730cadc18a66395])
  | _ => 0

def compactCount47 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 9
  | 6 => 52
  | 5 => 146
  | 4 => 37
  | 3 => 1
  | _ => 0

def compactPath47 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords47 (15 + 12*i) 12
  | 6 => let v := readCompactBits compactWords47 (1068 + 15*i) 15
    (readCompactBits compactWords47 (972 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords47 (9198 + 18*i) 18
    (readCompactBits compactWords47 (8334 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 4 => let v := readCompactBits compactWords47 (30886 + 17*i) 17
    (readCompactBits compactWords47 (29914 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 3 => let v := readCompactBits compactWords47 (35146 + 12*i) 12
    (readCompactBits compactWords47 (35098 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | _ => 0

def compactLive47 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords47 (0 + 5*i) 5
  | 7 => readCompactBits compactWords47 (123 + 6*i) 6
  | 6 => readCompactBits compactWords47 (1848 + 7*i) 7
  | 5 => readCompactBits compactWords47 (11826 + 8*i) 8
  | 4 => readCompactBits compactWords47 (31515 + 9*i) 9
  | 3 => readCompactBits compactWords47 (35158 + 10*i) 10
  | _ => 0

def compactPoolIDs47 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords47 (11 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords47 (5 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 7 => let v := readCompactBits compactWords47 (453 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords47 (177 + 4*(v &&& 127)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords47 (3427 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords47 (2212 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 5 => let v := readCompactBits compactWords47 (13696 + 10*i) 10
    let n := v >>> 7
    let bits := readCompactBits compactWords47 (12994 + 6*(v &&& 127)) (6*n)
    compactIDsFromBits bits 6 n
  | 4 => let v := readCompactBits compactWords47 (31856 + 4*i) 4
    let n := v >>> 3
    let bits := readCompactBits compactWords47 (31848 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 3 => let v := readCompactBits compactWords47 (35168 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords47 (35168 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket47 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords47 (552 + 4*(i % 7)) 4
    let off := ((i/7 + d) % 28)
    let v := readCompactBits compactWords47 (580 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 6 => let d := readCompactBits compactWords47 (4051 + 7*(i % 63)) 7
    let off := ((i/63 + d) % 226)
    let v := readCompactBits compactWords47 (4492 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 5 => let d := readCompactBits compactWords47 (15156 + 7*(i % 208)) 7
    let off := ((i/208 + d) % 739)
    let v := readCompactBits compactWords47 (16612 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 4 => let d := readCompactBits compactWords47 (32004 + 6*(i % 49)) 6
    let off := ((i/49 + d) % 175)
    let v := readCompactBits compactWords47 (32298 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 3 => let d := readCompactBits compactWords47 (35170 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits compactWords47 (35172 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid1069 : CompactGrid := (1069, 5, samplesP1069, samplesQ1069)
def tab1069 : CompactTable := (compactCount1069, compactPath1069, compactLive1069, compactPoolIDs1069, compactBucket1069)
def check1069 (k : Nat) := compactNode grid1069 tab1069 compactDomains1069 compactPerms1069 k
def sliceSpecs1069 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains1069 : ∀ d ∈ compactDomains1069, Slice true (vars 1069) (graphGoal 1069) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs1069)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs1069 : properPairs (graphGoal 1069) (asRow samplesP1069) (asRow samplesQ1069) :=
  compactPairs (g := grid1069) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos1069 : ∀ p ∈ compactPerms1069, autoOK (graphGoal 1069) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c1069k3p0 : chartBlock (check1069 3) 0 7 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev1069k3 : chartBlock (check1069 3) 0 7 = true :=
  c1069k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c1069k4p0 : chartBlock (check1069 4) 0 7 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev1069k4 : chartBlock (check1069 4) 0 7 = true :=
  c1069k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c1069k5p0 : chartBlock (check1069 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev1069k5 : chartBlock (check1069 5) 0 1 = true :=
  c1069k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded1069 : Impossible true (graphGoal 1069) 5 (vars 1069).toFinset := by
  apply compactRoot (g := grid1069) (t := tab1069) (dom := compactDomains1069) (perms := compactPerms1069) pairs1069 domains1069 autos1069
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev1069k3
    · exact lev1069k4
    · exact lev1069k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound1069 : Lower true (vars 1069) (graphGoal 1069) 6 :=
  plain_low (hints := 1075089420) (by decide +kernel) excluded1069

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound2091 : Lower true (vars 2091) (graphGoal 2091) 6 :=
  carry_of (old := 2091) (rep := 1069) (swaps := [33]) (by decide +kernel) bound1069

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound4135 : Lower true (vars 4135) (graphGoal 4135) 6 :=
  carry_of (old := 4135) (rep := 1069) (swaps := [33, 50]) (by decide +kernel) bound1069

def grid16398 : CompactGrid := (16398, 3, samplesP16398, samplesQ16398)
def tab16398 : CompactTable := (compactCount16398, compactPath16398, compactLive16398, compactPoolIDs16398, compactBucket16398)
def check16398 (k : Nat) := compactNode grid16398 tab16398 compactDomains16398 compactPerms16398 k
def sliceSpecs16398 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains16398 : ∀ d ∈ compactDomains16398, Slice true (vars 16398) (graphGoal 16398) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs16398)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs16398 : properPairs (graphGoal 16398) (asRow samplesP16398) (asRow samplesQ16398) :=
  compactPairs (g := grid16398) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos16398 : ∀ p ∈ compactPerms16398, autoOK (graphGoal 16398) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c16398k3p0 : chartBlock (check16398 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev16398k3 : chartBlock (check16398 3) 0 1 = true :=
  c16398k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded16398 : Impossible true (graphGoal 16398) 3 (vars 16398).toFinset := by
  apply compactRoot (g := grid16398) (t := tab16398) (dom := compactDomains16398) (perms := compactPerms16398) pairs16398 domains16398 autos16398
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev16398k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16398 : Lower true (vars 16398) (graphGoal 16398) 4 :=
  plain_low (hints := 532736) (by decide +kernel) excluded16398

def grid16399 : CompactGrid := (16399, 4, samplesP16399, samplesQ16399)
def tab16399 : CompactTable := (compactCount16399, compactPath16399, compactLive16399, compactPoolIDs16399, compactBucket16399)
def check16399 (k : Nat) := compactNode grid16399 tab16399 compactDomains16399 compactPerms16399 k
def sliceSpecs16399 : List SliceSpec := [(1, 0, 16398, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains16399 : ∀ d ∈ compactDomains16399, Slice true (vars 16399) (graphGoal 16399) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(16398, 4)]) (specs := sliceSpecs16399)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound16398
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs16399 : properPairs (graphGoal 16399) (asRow samplesP16399) (asRow samplesQ16399) :=
  compactPairs (g := grid16399) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos16399 : ∀ p ∈ compactPerms16399, autoOK (graphGoal 16399) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c16399k4p0 : chartBlock (check16399 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev16399k4 : chartBlock (check16399 4) 0 1 = true :=
  c16399k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded16399 : Impossible true (graphGoal 16399) 4 (vars 16399).toFinset := by
  apply compactRoot (g := grid16399) (t := tab16399) (dom := compactDomains16399) (perms := compactPerms16399) pairs16399 domains16399 autos16399
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev16399k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound16399 : Lower true (vars 16399) (graphGoal 16399) 5 :=
  plain_low (hints := 532736) (by decide +kernel) excluded16399

def grid46 : CompactGrid := (46, 4, samplesP46, samplesQ46)
def tab46 : CompactTable := (compactCount46, compactPath46, compactLive46, compactPoolIDs46, compactBucket46)
def check46 (k : Nat) := compactNode grid46 tab46 compactDomains46 compactPerms46 k
def sliceSpecs46 : List SliceSpec := [(0, 32, 16398, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains46 : ∀ d ∈ compactDomains46, Slice true (vars 46) (graphGoal 46) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(16398, 4)]) (specs := sliceSpecs46)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound16398
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs46 : properPairs (graphGoal 46) (asRow samplesP46) (asRow samplesQ46) :=
  compactPairs (g := grid46) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos46 : ∀ p ∈ compactPerms46, autoOK (graphGoal 46) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c46k4p0 : chartBlock (check46 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev46k4 : chartBlock (check46 4) 0 1 = true :=
  c46k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded46 : Impossible true (graphGoal 46) 4 (vars 46).toFinset := by
  apply compactRoot (g := grid46) (t := tab46) (dom := compactDomains46) (perms := compactPerms46) pairs46 domains46 autos46
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev46k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound46 : Lower true (vars 46) (graphGoal 46) 5 :=
  plain_low (hints := 6451505408) (by decide +kernel) excluded46

def grid47 : CompactGrid := (47, 8, samplesP47, samplesQ47)
def tab47 : CompactTable := (compactCount47, compactPath47, compactLive47, compactPoolIDs47, compactBucket47)
def check47 (k : Nat) := compactNode grid47 tab47 compactDomains47 compactPerms47 k
def sliceSpecs47 : List SliceSpec := [(0, 2, 1069, 0, 0, 6, 6), (0, 4, 2091, 0, 0, 6, 6), (0, 8, 4135, 0, 0, 6, 6), (0, 32, 16399, 0, 0, 5, 5), (1, 0, 46, 0, 0, 5, 5), (1, 32, 16398, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains47 : ∀ d ∈ compactDomains47, Slice true (vars 47) (graphGoal 47) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(1069, 6), (2091, 6), (4135, 6), (16399, 5), (46, 5), (16398, 4)]) (specs := sliceSpecs47)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound1069
    · exact bound2091
    · exact bound4135
    · exact bound16399
    · exact bound46
    · exact bound16398
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs47 : properPairs (graphGoal 47) (asRow samplesP47) (asRow samplesQ47) :=
  compactPairs (g := grid47) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos47 : ∀ p ∈ compactPerms47, autoOK (graphGoal 47) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k3p0 : chartBlock (check47 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k3 : chartBlock (check47 3) 0 1 = true :=
  c47k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k4p0 : chartBlock (check47 4) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k4p1 : chartBlock (check47 4) 32 5 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k4 : chartBlock (check47 4) 0 37 = true :=
  (chartBlock_join (a := 32) (b := 5) c47k4p0 c47k4p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p0 : chartBlock (check47 5) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p1 : chartBlock (check47 5) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p2 : chartBlock (check47 5) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p3 : chartBlock (check47 5) 96 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k5p4 : chartBlock (check47 5) 128 18 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k5 : chartBlock (check47 5) 0 146 = true :=
  (chartBlock_join (a := 64) (b := 82) (chartBlock_join (a := 32) (b := 32) c47k5p0 c47k5p1) (chartBlock_join (a := 32) (b := 50) c47k5p2 (chartBlock_join (a := 32) (b := 18) c47k5p3 c47k5p4)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k6p0 : chartBlock (check47 6) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k6p1 : chartBlock (check47 6) 32 20 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k6 : chartBlock (check47 6) 0 52 = true :=
  (chartBlock_join (a := 32) (b := 20) c47k6p0 c47k6p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k7p0 : chartBlock (check47 7) 0 9 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k7 : chartBlock (check47 7) 0 9 = true :=
  c47k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c47k8p0 : chartBlock (check47 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev47k8 : chartBlock (check47 8) 0 1 = true :=
  c47k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded47 : Impossible true (graphGoal 47) 8 (vars 47).toFinset := by
  apply compactRoot (g := grid47) (t := tab47) (dom := compactDomains47) (perms := compactPerms47) pairs47 domains47 autos47
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev47k3
    · exact lev47k4
    · exact lev47k5
    · exact lev47k6
    · exact lev47k7
    · exact lev47k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound47 : Lower true (vars 47) (graphGoal 47) 9 :=
  plain_low (hints := 1075622734) (by decide +kernel) excluded47

end PEqualNP.Outside.L_meta_42040.Low

namespace PEqualNP.Outside.L_meta_42040.High.Model
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
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
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

end PEqualNP.Outside.L_meta_42040.High.Model

namespace PEqualNP.Outside.L_meta_42040.High
open PEqualNP.Outside.L_meta_42040.High.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 49]

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
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_42040.High

namespace PEqualNP.Outside.L_meta_42040.High
open PEqualNP.Outside.L_meta_42040.High.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x14072e2af00392da8eae08ecd804120007408400341221a92317c1007980a00016530000c9e01a3180b80000450000430820c244bff42fe42fd42fc42ff41fe41fd41fc41fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41be40083fa80107f10020de20041f8400837080107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c437ca9884f95310feaa6217d54c437aa9884f55310fe2a6217c54c43fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff31c43fc63887d8c710fe98e21f531c43f863887fc8710ff10e21fd21c43f843887fd0310ff20621be40c43fa81887f10310de20621ff30c43fe41887f88310fe90621fc20c43fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7085fd4e10ff29c217e53843faa7085f54e10fe29c21ff43843fc87087f50e10fe21c21ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421ff32843fc65087f4ca10fe194217d51843fe83087f90610fea0c21fc41843fe63087dcc610ff18c21fd31843f863087d0c610ff90c21f721843fc43087f48610fe10c21f421842fca1087fd0210ff20421be40843fa81087f10210de20421ff30843fc61087fc8210ff10421fd20843f841087fc4210fb88421fb10843fea8885fd5110dfaa2213f54443fca8885f95110feaa2217d54443f8a8885f15110de2a2213c54443fea6885fd4d10efa9a215f53443fca6885f94d10fea9a217d53443f8a6885f14d10ee29a215c53443fe86887f90d10fea1a21fc43443fea4885fd4910f7a92216f52443fca4885f94910fea92217d52443f8a4885f14910f6292216c52443fe84887f90910fea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fea0a21fc41443fe62887f8c510fb18a21fd31443ea62887f0c510ff90a21fe21443fa42887f08510ffa0221fe404437c80887f50110fe20221bc40443fe60887f8c110fe98221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821de53042bca6087f54c10bea9821dd53042baa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087f90410fea0821fc41043fe62087dcc410ff18821fd31043f862087d0c410ff90821f721043fc42087f48410fe10821f421042fca0087fd0010ff20021be40043fa80087f10010de20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd42903f885206f10a40ffa8c81fe51902fca3207f54640bea8c81fc51903fe83206fd0640ff20c81be41903fa83206f50640fe20c81bc41903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481bf529037ca5206f54a40de29481bf519037ca3206f54640de28c81be319037a63206f0c640df90c81be219037a43206f086409f28481ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940ff21281fd42503f884a07fd4540bfa8a81fe51503faa2a07f14540be28a81ff41503fc82a07f50540fe20a81fe31503fa62a07f0c540ff90a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff52103fca4205f94840fea90817d52103f8a4207fd0840dfa1081fe421037c84207f50840dea1081fc421037884207fd4440ff288817e51103faa2205f54440fe28881ff411037e82207f90440df20881fd411037a82207f10440de20881fe31103fa62207f0c440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040dfa9081be521037aa4206f14840dfa8881be511037aa2206f14440df18881bd311037862206fc8440df10881bd211037842206f940409f28081ba50103fea9905fd5320ff2a6417e54c837ca9904f95320feaa6417d54c837aa9904f55320fe2a6417c54c83fe85907f90b20fea1641fc42c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff18e41fd31c83f863907fc8720ff10e41fd21c83f843907fd0320fda0641fe40c837c81907f50320fe20641bc40c83f081906e10320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220bea9441ff42883fc85107f50a20fe21441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107f8c620fe98c41fc31883fe43107f88620f710c41fd21883f843107b08620bf28441ff40883fc81106f90220fea0441fc408837881107fc8220f790441fb20883fea8905fd5120dfaa2413f54483fca8905f95120feaa2417d54483f8a8905f15120de2a2413c54483fe84907f90920fea1241fc42483fea2905fd4520fba8a417751483fca2907f54520fe28a417c51483e8a2905d14520ffa0a41fe41483fa82907f10520ff18a41fd31483f862907fc8520ff10a41fd21483f842907fd0120ff20241be40483fa80907f10120de20241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a0417e52083fe84107f90820fea1041fc42083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff18841fd31083f862107fc8420ff10841ee21083fa42107f08420f6108417e50083fe80107ed0020ff20
  | 2 => 0xc7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa92637f524c7fca498ff54931fe292637c524c7fe8498ff90931fea1263fc424c7fe8298ff90531fea0a63fc414c7fc6298f78c531ffa82637f504c7fca098ff54131fe282637c504c7fea818dfd5031ff2a0637e540c7faa818df55031fe2a0637c540c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831bf28863ff410c7fc8218ff50431fe20863fe310c7ec6218ff4c431fa98863d5310c7fea018ff94031bf28063fd500c6faa018ff14031ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e437f53c87fca790df94f21fea9e437d53c87f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643fd42c87f88590ff8cb21ffa0e43f741c87fc8390ff50721fe20e43f441c87fe6390ff8c721fb18e43fd31c87ea6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710ff94e21bf29c43de53886bca710ff54e21bea9c43dd53886baa710ff14e21be29c43ff43887fc8710ff50e21fe21c437d52887fe8510ff90a21fea1443fc42887fe6510ff8ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310ff4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243ff41487fc8290ff50521fe20a43ff31487fc6290ff4c521fe18a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ef950219f2a043fd54086faa810ef550219eaa043fc54086f8a810ffd4c21bfa9843fe53086fca610ff54c21bea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043fe42087fa8410ff10821ff99043fe32087fa6410ff0c821bf28843ff41087ee8210ff90421fea0843fc41087e88210ffcc421ff18843f631087fa6210fd4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fc63a07f4c740fe18e81ff21d03fc43a07f48740fe10e817d54903fea5207f94a40bf29481fd52902faa5207f14a40ffa1481bf42903fc85206f90a40fea1481b
  | 3 => 0x800002c00000400001000c00800c00000003003800400800401c00003000000804c01801c00000403c00002400000001800400000000000800005800400000000402001400000800800c00000400000002800000000401000c00800400402400000400000401000000c00401001401c00000000c00402c02800800800c00800000800400000c00405c00003c00c00800000401c00001800c06c07000c00401401404800400800001001400000400400400400000400000001801000400400000000000001400402400005004400400000800c00000800401000007400400404001800800408c00000400000800000000c038000010000000000000010000010000000000000030058054014027fea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0afaa9215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190bfaa3215f54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd0942f7a1285fe4250b7c84a17fd4542bfa8a85f75150aeea2a17f94542fea8a85fc5150af8a2a17d14542ba28a85ff5050afea0a17ed4142bda8285fe5050bfaa0a17f14142be28285f85050af0a0a15f95042bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d077e85a0ff90b41fea1683bd42d07f885a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea720ff94e41bf29c83fd53906faa720ff14e41ffa1c83fe43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42907fa8520ff10a41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83fe43507fa86a0ffd4941bfa9283fe52507faa4a0ff14941be29283ff425077e84a0ff90941fea1283bd42507f884a0ffd0541fba0a83fe415077c82a0ffd4141bfa8283fe50507faa0a0ff14141be282837e54107fea620ff94c41bf29883fd53106faa620ff14c41ffa1883fe43107fa8620ff10c41ffa9083fe52106fca420ff54841bea9083fc52107fe8420ff90841fea1083fc42106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7fc8718ff50e31fe21c63ff528c7fca518df94a31fea94637d528c7f8a518ffd0a31ff21463fd428c7f88518df94631ffa0c63fe418c7fa8318ff10631ff98c63f7318
  | 4 => 0x218000031c71ac80000011180010b00017e8000002009cf8000782278555341b28000000394000000320000fa1f600003d8000002158000000001d6a2c9d10000001c58000001f34000460d4937800081cdc80000020f96b0174481d98001c74002244b4071c4d16016b4b70c68000002300c98864000000000000001b6800000000000000192634c000001631c022692e0000721144aca081628ad8a994a48b94a80622e03e82280012897a91000000000000000020a0000384000001de068c000000e29e587690488b40000010007991794580000c22c4001a20001f01ae22004986e8140000001a905687f5651ee9758000000000001e68001a9d1362916a4afc658001541750000000000000090821844000e5006da512495a00010d22f80000002191b8b1c2acc781f95657a1d0494a28800154dfc0ecdab4cf000000000224c0000000000018b13bc03c000bf8001f0800128d105a8c0000000000000000000000009383762bc000c70000334000000e80c748801661200015f9a71808bb97909906c02cca088b0278000f300a58c17f8000e60064d42155470084c40d616608c9f217d153deec8522d95086a1665e88120e11d180001d8000000000000000054001900002164771c1996800055d1a013054d47912c0011c87e0000001120000000708000000000000000002359d50001fd400000062800081800000000075002c01000c00801c02800000001402404000001000000000800000400001000400c00800c01c00000000000002c00000800000000400000800000400801000801003802000000400400004400000400c00000400c00400c01000000000400000004000001800001804000400c01000003c00000401801400000000400800000007c00000000c01802401001800800801000000400000000000400801000001001000400000801c00001c00000c00002400800400000801000400000000c00400802001c00401c00400002800000c01400800800800c03000800801002000800402801000802400400401000401400400c00801000400001000004400000c00800000800000400000401400800000001800400001c00800800c01000c00406c00000c03400c00001000800c00000002800401c00001000c00c00400003401c00400000402401400400000000000000001400000000c00801801400000400800400001000001400c00000000000000000800800400000000800000000000000400c01001800401000000000c01000400000000000800800401800800801401400000000000400000000400002000002803800000001000800803800800000c00000c00400000800c00400001401c00000804400801000402800000801404800001000000400400000c00c07c00400c00000003000000002400400400800801
  | 5 => 0x1841da91e527dc390fd5140017800022b8000000000d099da21000000000201c4b8a21f680005e8000001e312acfdc0011145a40005d05380000000000000000000000006e0000001531a10001bc00000000020617d49f8000000000001c78b74b491409e0f0c958144001ec8b903f8438b78e0800080985a0f06160ac00192dd38902098928000000000c6c001039dd80000008980000000001a8000000094368001fdc000000630ff14b000078c4f02d0350fc0000000000000000b515000014ac0013a8000000b80000001390df9a34f6a1280007a0d70000a48de0e2cc100e0a900000012595c80407d90e0001811b80000118000000000000000000b019c5738001962280000000ee40000000019ac0003a4000000001c317300000000000003a8001ecc0000019c8289060000000000000000000000000000001df00000001cc000e493f96c1f99af84c00017bc7000000000016c400225d1f06880021b8000000001c497180019a5a94aa1c980c9440000000000199c81711301e10ef84a00017b0001e3c268240000cb0509d2150d0249f6094fbde217460e9cd800000061ce181c11d8000000001a797292c4ae8000000b100000019b1fcde394d9b98fed720620000cd80000018b8248000000000002161a7c180cec7199d0420000000fe4280541ea81907c13d5cc00011a4000000000000a39dec0000013a53b8c812cc560960000298df452221a028a2d8c800219800221d00db380691ed082338000001fd000000000000000000008d4820b460c940000988eb0cb57c00000003986080000000010400013dd338001f7000000009e3511300000000007780013e89b4001ab02d8000e395512089c4001b9c0000013c9ae82a4001a98ee8d380002f800143841c51cf700002b2364000d78159b48860000b6800225955dd09994000b5cda00014300021f1988af05ba2b00000016800000021498a800038000113caf4f9c000d186780002320505c16dc0013760303b800000000000000000159cad05fdf509d85b4dc4000691a59281ad9be08a800000175400000080cbd09e438c000000cd0000000a69898000001cb0000535a28000000000000000ce4cf979a2349fc9052d80d9ddc000340000fb13080000016411580000000000000000000000002200016ac4113894f8200fc609ca158e0e1d6d8dd80015212b1bb000000023a2300000013951b0000000000428000de4ff5429868000000001890001c087fa2f000177800000194c000b316f93ac0021d0000000dfd825eb0000e1400128523daac0496f2068a050c40005a8000c64000000002070c88000000179cbc000000188d300000001d40000000000000000000b92d41e00000000000f09c846460407d7080001bd490000000000f59e80f419300000017000003d44b4001
  | 6 => 0x16cc710000c300021c1880001e40001528a88000000001bb80000013b0c50918000e89df9fb2038f80c211f93100003000015fc000330fa80f800080124ce680010d40005ad940000100c7d534b7d3581b8fd9380000dd0da88e0290c8c001db126c7400010f40019a8000d58c006d42c6020b840000462d01d00019f07606715e80007281c4448000f115119c0cdc0000000019344e80000000021709b0000794e0225000000000029cbc0f216e00e53cc581ac0b580000007e80000000000006d9580600b880000000a8ca00015b1fd800000000039d590000000000000001129295570cac9a80005500001560421102dc9add246b98602b9004000c594b8258001bd9b88000000000000cc62a04c56b800063db8485d5489702fdb952f08f96bc2b6309e988747a8001771d58308698f880e873ddb837901d560001b20859fe8f8c5f1bac409920001231971021360000ba0db0001e900012a9079364001111ee0db48702e90990f9278ec0f48a24000a50001cf00000000019500000000000000000000012212b4d8a0100016a05e0000000000000000000000001cc8002344001e5000034cf048140000020a80011bc000000d503b1855a062d59180009115889f0002118000aecc90cd4000eddb5921183c830e995780015558200015a9319161321d15fc8002320000001cfe181a40efce796d149956800166a0b9a80000f38001ab9675420ccc8f1ff0361e08a60fe1ee40000000014e80015c0000001bd015cdf00007896e94ca22d3a00011d1a48000000000aa9d48001018000be000000182c00000000000127400000000000151c000000000000e0c0000000010680019bc000531cc62280000000000000000012a6348000002130a0e311a1800000000000000000000000113800062c00000000055800129d10e1c8714058548000000001a6800000000059000235c00000000000014c000000978828478ea97688061e0324000000002090b280000000001b0968001d5576017dc900000000006f80000002c8000744fe9dc1b5000000161a169e34bda1a12f9659150764fb800000000061072c000999ca165c0000000084580003d00002f20180002e0000000f60000f500000005c80000011c05c46415b89bc04c0000010b9228000000d80000000af8d900000001ac000000c180000017e00009dccc8000ffc5720b013ca2981e2cd8e4001de80f4b2c0010dc000001cb5059f41525254000f94169b19f283884f83e13498789098a1e000000000000759980001a08a229800000065000136e238348000270000000fb4dbc3c80014107b400001800000000109000000000000000138c000490000000001aa8ddd5d00018e8000000a80f1d9383280012bc0000000010f21f9268000250000514138b65871ce9fa00006840
  | 7 => 0x4a93f0baa23c0002ece417f09a48498140007c8ed8001698000cf5ef17d98310160480d1ed5e2800152c0000880986d21798d8f01d6040199d1a9cae2dc33a141f89f3d2500010d9c1236d0711ac950f84fcce20eb8370000001d400000000006b1888000000000000c08980000000002220b8e07800135d488002224000000000dac000724000000000000000000001828150e90000000210000000001f30bc9b113c01f11888d8a1c22d805cb9088425c500007dc5a0108e71ef5b08694c48510c3879cb34d69de40ed16853c67d948000000001d298f05d99e9bf9418001a08840d996880b0731b600020a40019298f92390c16e54490e9261dc8c609222600000009e8001b70000001d70001f900000000012900292b80000021880007593d07494c4c85010b99848002088000000000000001eda101ea0ca51e1028a702a1dd0634ac00012dca580021e8001909e785883580000012d0d29518fd17c4000ae066d5adc28000000000000000ab00000000000000013980000007f14c0de80009b9b8cea068000000000000215c0000000021b0001e61b021088380007e4f09a38b0511c4715e18187b1ad08d18b41294a19b40002f62409ec0000781102e40000000022e99780020e00003100021d9958000f90ee0000000001edc000000000790e24ce800136a355bf0fd4ff92412447550c8a00528000db80004184516490cc00216dff9328f79a89350000000002318b18000000001ce149d801e19c8939c0014680000000012010a0000decb2400050c170000000000cc0001e2de49ef8be99a089023c0000000023686f0000b3cca9610c280016a9d88001fc4624000001f382c16080000017880005454d00002096706194f1c20001409ba9a000001e80011b4000ec8ef1b9119086c001abdd323421399e17c97483c0639fa85645251707d0d20a300000000017407b94607398391d4000000000000bf0001299af032c000000000000d10469d021920019f91080015d80000000000018504d80004880020d9f581c80212c0000000000000390001539030bb00000019b8e04001bc9f18649a60660598000000b60a793e04b0b089c016c260e31d80811aa00022c220a0c8ce0038888001f78000000001c6899e36000000184deb9b3042c000000000002331d0d98c5cc2d5008415d90160a180000000000000003f118000000043000000217d9922e40000013b4010080ed05195f16908e9125a316edbe8f98cbc318f15679f4a059e706c80a21500500000017b8ed5fb96d5c603e5198f1826c75c74c6a85793722558d0dc12a1559400f29ba45b1b40930e58105271cd1ca83aca10000000000000000000149aa40000011dc001dd4001330001980d008690a80000005000009a00013c5f8084c0016c89d0000000b45c4000208c0002a800
  | 8 => 0x2328000440000001ed00007fc000000000000b392c84e2175f119107057140020d0000000ab9ec0a40b20000000000000001da00011e8000fc91f40012ea249149fe0000cb9d7800000000227226410c0016380015980000000000008780000004c837cb6e2a96205f80000000020c03a14510500000014e0001ba0000668000001b793d8000000070b4e1a8b548c07ec
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe400431e5390010cf54e400439d5390010c754e400433c5390010cfd4a400433e5290010cf54a400433c5290010ed98640043b56190010cf94640043b73190010ed0c640043b72190010ed08640042be6090010cf942400427f6550010d794d400435d53500109fd94400427e65100109f594400427c6510010cf950400433d5410010d794c400435d5310010bd98440042f56110010cfd94400433e6510010cf594400433c6510010cfd4c400433e5310010e794c400431e5310010cf54c400439d5310010c754c400433c5310010cfd48400433e5210010cf548400433c5210010ed98440043b56110010cf94440043b73110010ed0c440043b72110010ed08440042be6010010ee980400433e50100109f59730042be64cc010af593300435e53cc010d754f30043d731cc010ee103300427f658c0109f596300435e538c010d754e30042f6618c010bd58630043d4318c0109fd9530042bf644c010af191300435e534c010d754d30042ef624c010bb18930042f7614c010bd18530043d7314c0109f994300427d650c0109f19430042f6610c010bd58430043d4310c010ee100300427d65c8010af99320042bd64c8010d794f200435d53c8010ee103200427f65880109f596200435e5388010d754e200436e5288010db54a20042f66188010bd58620043e421880109fd9520042bf6448010af19120042df6348010b718d200435e5348010d754d20042f76148010bd185200427f65080109f994200427d65080109f194200435e5308010d754c200436e5208010db54820042f66108010bd58420043e42108010ee10020042be64c4010af593100435e53c4010d754f100437565c4010ed99310043b564c4010bd98f10042f463c4010ddd4f10043d653c4010dd54f10043d553c4010d554f10042f662c4010bd18b10043b640c4010ed103100435e5384010d754e10042f56184010dd94610043ba4084010ee10210042f96584010de59610042796584010f694e10043d95384010be586100437a5184010fc94610043f33184010fc0c610043f32184010fc086100427f6544010afd9110042bc6444010b7d8d10042dc6344010d794d100435d5344010bbd8910042ec6244010ee90110043b84044010bdd95100437765440109dd9510043b76444010ed19110043d76344010bd98d10042f46344010f518d10042d46344010ddd4d10043d65344010dd54d10043d55344010d554d10043e76244010bd98910042f46244010f918910042e46244010bdd8110043765044010fcd0110043b64044010ed10110043f04044010ec10110042fb6544010ded95100427b6544010eed9110043b86444010f6d8d10043d86344010f694d10043d95344010fad8910043e86244010bed8510043f36144010de94510043f25144010fcd0510043f04144010
  | 1 => 0x42f860508109fd94420427e65108109f594420427c6510810d794c420435d53108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc810bd98732042f561cc8109fd96320427e658c8109f596320427c658c810d794e320435d538c810bd98632042f5618c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810af99032042bd640c810d794c320435d530c8109f992510433e64944108f992510427d6494410cf592510423d64944109f58e510427e62944109f58a510427d65d0410cfd53410433c54d0410d794f410435d53d04109fd96410427d6590410cf952410433d5490410d794e410435d5390410be98241042f960904109fd95410433f5450410cf151410435e5350410d754d410427f65104109f594410433e5410410cf550410435e5310410d754c41042fa6010410be580410427d65cc410d794f310435d53cc410bd597310437565cc4109d597310437753cc410f594f310437553cc410f554f310435553cc410bd98b31043d632cc410f50cb31042f560cc4109fd96310427d658c410d794e310435d538c410bd9863104376518c410be98231042f9608c4109fd95310435e534c410d754d3104376514c4109fd94310427d650c410d794c310435d530c410f54c431042fa600c410be5803104375650c4109d59431042f6630c410f598c3104377530c410f594c3104375530c410f554c3104355530c410bd98831043f2600c410bd58031043f1600c4109f597210435e53c8410d754f21042f565c8410dd597210437654c8410dd15321042f663c8410bd18f210437753c8410f594f210437553c8410f554f210435553c8410ddd4b210437552c8410bd583210427f65884109f59621042de6388410b758e210435e5388410d754e210436e5288410db54a21042f66188410be98221042f960884109fd95210435e5348410d754d210427f65084109f59421042be6408410af590210435e5308410d754c210436e5208410db54821043e52108410be98021042f96008410dd59421042756508410ed99021043b56408410dd95021043745408410bd98c21042f46308410ddd4c21043d65308410dd54c21043d55308410d554c21042f66208410f998821043775208410f994821043755208410f954821043f26008410bd58021043f160084109f992500427d64940109f98e500427d63940109f98a500427d62940109f58650043773194010dd0c650043772194010dd086500427d65d0010d794f400435d53d00109fd96400427d6590010cf952400433d5490010d794e400435d5390010bd98640042f56190010cfd96400433e6590010cf596400433c6590010cfd4e400433e5390010e794
  | 2 => 0x5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c10dd987530437a60d4c109f596530435f5394c109f992530427d6494c109f98a530427d6294c1097596530435f5494c10d7952530435d5494c10d715253043d46194c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f58553043746154c10d7d95530435f5454c10d7951530435d5454c10d715153043d46154c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d5185530435e6054c10d7181530435c1054c10b798c530435d5314c109f990530427d6414c109f988530427d6214c109f98453043766114c109d984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430435e53d0c10d754f43042f661d0c10bd587430427f6590c109f996430427d6590c109f196430435e5390c10d754e430427f6550c109f995430427d6550c109f195430435e5350c10d754d43042f76150c10bd18543042fb6050c10be181430427f6510c109f994430427d6510c109f194430435e5310c10d754c43042de63d4810b758f520435e53d4810d754f520427e64d48109f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520435e5354810d754d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d6154810dd185520427f60548109f58152042be6414810af59052042de6314810b758c520435e5314810d754c520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109f984520437661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810d794f420435d53d0810bd98742042f561d08109fd96420427e65908109f596420427c6590810d794e420435d5390810db94a420436d52908109fd95420427e65508109f595420427c6550810cf951420433d5450810b7d8d42042dc6350810d794d420435d5350810db949420436d5250810bdd8542042f46150810bed81420
  | 3 => 0x110cf552404433c5490110d7d4e404435c5390110dbd4a404436c5290110af996404433e65901108f996404433f5390110e7d4e404431f5390110cf94e404433d5390110cf14e404439c5390110c714e404433f5290110ebd4a404432f5290110cf94a404433d5290110cf14a40443ac5290110cb14a40443b63190110ed4c640442be60901109fd95404427d65501109f195404433f5450110cf151404435f5350110d714d404436f5250110db14940442f76150110bd185404427e6510110cfd50404433e5410110cf550404433c5410110d7d4c404435c5310110dbd48404436c5210110af994404433e65101108f994404433f5310110e7d4c404431f5310110cf94c404433d5310110cf14c404439c5310110c714c404433f5210110ebd48404432f5210110cf948404433d5210110cf14840443ac5210110cb14840443b63110110ed4c440442be6010110ee980404427e65cc110af99330442bd64cc110cfd53304433c54cc110d7d4f304435c53cc110dbd4b304436c52cc110bd98730442f561cc110f54c7304433f548c110cf152304435f538c110d714e304436f528c110db14a30443d6318c110ee102304427d654c1109f195304433f544c110cf151304436f524c110db14930442f7614c110bd18530443d5314c110ee101304427e65c8110af99320442bd64c8110cfd53204433c54c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c8110ee103204427e6588110cfd52204433c5488110d7d4e204435c5388110dbd4a204436c52881109fd95204427d65481109f19520442bf6448110af191204433f5448110cf15120442df6348110b718d204435f5348110d714d204436f5248110db14920442f76148110bd185204427e6508110cfd50204433c5408110d7d4c204435c5308110dbd48204436c5208110ee10020442be64c4110af593104433f54c4110cf153104435f53c4110d714f104436f52c4110db14b10443ba40c4110ee10310443ba64c4110ee59310443bb54c4110ee15310443db53c4110f614f10443eb52c4110fa14b10443f231c4110fc4c7104433f5484110cf152104435f5384110d714e104436f5284110db14a10443b75484110ed15210442f76384110bd58e10443d75384110dd94e10443745384110f514e10443545384110f9d4a10443765284110dd14a10443e45284110d914a10443f35084110ed90210443b44084110b798f54042dd63d50109f98f540435e63d50109798f540427d63d5010d758f540425d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d
  | 4 => 0x7d8d42442dc6350910d7d4d424435c5350910dbd49424436c5250910bdd8542442f46150910bed8142442f860509109fd94424427e65109109f594424427c6510910cfd50424433c5410910d7d4c424435c5310910dbd48424436c5210910bd98442442f561109109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910d7d4f324435c53cc910dbd4b324436c52cc910bd98732442f561cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c910dbd4a324436c528c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910af99032442bd640c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf153414435f53d0510d714f414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510d7d4e414435c5390510dbd4a414436c52905109f195414433f5450510cf151414435f5350510d714d414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c5410510d7d4c414435c5310510dbd48414436c5210510cfd53314433c54cc510d7d4f314435c53cc510dbd4b314436c52cc510be98331442f960cc5109f996314433f548c510cf152314435f538c510d714e314436f528c510db14a31442f6658c510dd9963144276658c510edd5231443b4548c510bd58e31443d7538c510dd94e3144374538c510f514e3144354538c510f9d4a3144376528c510dd14a31443e4528c510d914a31442f6608c510cfd51314433c544c510d7d4d314435c534c510dbd49314436c524c510bed8131442f8604c510edd5131443b4544c510f5d8d31443d7534c510dd94d3144374534c510f514d3144354534c510f9d493144376524c510dd14931443e4524c510d914931443d6324c510f50c931443f3604c510bd18131443f0604c5109f994314433f540c510cf150314435f530c510dbd48314436c520c510bd98431443d5310c5109f997214433f54c8510cf153214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510cfd52214433c5488510b798e21442dd6388510d7d4e214435c5388510dbd4a214436c52885109f195214433f5448510cf151214435f5348510d714d214436f5248510db14921442fb6048510be181214427e6508510af99021442bd6408510cfd50214433c5408510d7d4c214435c5308510dbd48214436c52085109f997404433f54d0110cf153404435f53d0110d714f404436f52d0110db14b40442f661d0110bd587404427e6590110cfd52404433e5490
  | 5 => 0x534435e6214d10d7588534435c6214d10d7d84534435f6014d10d7580534435d1014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d7d4e434435c5390d10bd98643442f56190d10be98243442f96090d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10d7d4d434435c5350d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bd98443442f56110d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109dd85524427f6054910ded81524427e6514910cfd50524433c5414910d7d4c524435c5314910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c524436f6414910db990524436d6414910db190524436f6314910db98c524436d6314910db18c524436f4314910db90c524436d4314910db10c524436f6114910db584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c52909109fd95424427e65509109f595424427c6550910cfd51424433c5450910b
  | 6 => 0x2bc6448210b7d8d20842dc6348210bdd8520842f46148210db948208436d5208210bd98420842f56108210f908420843b84008210af99310842bd64c4210ee90310843b840c4210bd597108437565c4210ed99310843b564c4210bd98f10842f463c4210ddd4f108437553c4210bd98b10842f462c4210ed90310843b440c4210be597108437965c4210ee99310843b964c42109f98f544427d63d51109f98b544427d62d5110cfd8f544433e63d5110cf58f544433c63d5110cfd8b544433e62d5110cf58b544433c62d5110cfd87544433d61d5110cfd83544433d60d5110cfd5254442de6395110b758e54442ee6295110bb58a544427e64951108f992544427e6395110d798e544425e63951109f58e544435d63951109758e544427e6295110db98a544426e62951109f58a544436d62951109b58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e61151109f184544427e60151109f18054442be6515110cf994544423e6515110cfd8c544433e6315110cf58c544433c6315110cfd88544433e6215110cf588544433c6215110cfd84544433d6115110cfd80544423e6015110cf580544423c6015110cf440544433f54d4d10cf153534427e64d4d109f593534427e62d4d109f58b534435f54d4d10e7d53534431f54d4d10d7953534435d54d4d10d7153534439c54d4d10c715353443d761d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a53443756194d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534427f6254d10dbd89534426f6254d109f189534436c6254d109b18953443776154d109fd81534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427c6114d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c715053443d56114d10d7d90534435e6414d10d7590534435c6414d10d7d88
  | 7 => 0x394a10b7d8d52842dc6354a109fd91528427c6454a109fd8d528435f6354a1097d8d528427c6354a10d718d528425c6354a10dbd8952843776154a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cfd53428433c54d0a10bd98742842f561d0a109fd96428427e6590a109f596428427c6590a109fd95428427e6550a109f595428427c6550a10cfd51428433c5450a10b7d8d42842dc6350a10bdd8542842f46150a10bed8142842f86050a109fd94428427e6510a109f594428427c6510a109fd97328427e65cca109f59732842f661cca10bd587328427f658ca109f996328427d658ca109f19632842f6618ca10bd586328427f654ca109f995328427d654ca109f19532842f7614ca10bd185328427f650ca109f994328427d650ca10af99032842bd640ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610d794f318435d53cc610be98331842f960cc610f594f318437553cc610f554f31842f662cc610f58cb31843d432cc610fc98331842f560cc610fc583318435f538c610d794d318435d534c610bed8131842f8604c610f54c431842f5650c610dd59431843d6630c610ddd4c31843d7530c610d5d4c3184375530c610f514c31842f6620c610bd580318436e52c8610db54b21842fa60c8610be583218437565c8610dd953218437454c8610bd98f21842f463c8610ddd4f218437553c8610ddd4b21843e652c8610dd54b21843e552c8610fc98321842f560c8610fc58321842de6388610b758e218436f5288610db14a218436e5248610db54921842fb6048610be18121842be6408610af590218436f5208610db14821843e52108610bd59421843756508610ed99021843b56408610dd95021843745408610bd98c21842f46308610ddd4c21843755308610f998821843775208610f9d4821843755208610f914821842f56008610cf952408433d5490210bd98640842f56190210cf996408433d6590210cfd4e408433e5390210cf54e408433f5290210cf94a408433d5290210cf14a40843b66190210ed58640843b73190210ed0c640843b72190210ed086408433e5410210cf55040842f66110210bd584408433e6510210cf594408433f5310210cf94c408433d5310210cfd48408433e5210210cf548408433c5210210ed98440843b56110210edcc440843b43110210edc8440843b42110210ee98040842be64cc210af59330843d731cc210bd98630842f5618c210f50c630843b8408c210af99320842bd64c8210ee103208436e5288210db54a20842f66188210bd58620843e42188210afd912084
  | 8 => 0x10cf55041c42fa6010710be58041c433e54cc710cf55331c433e548c710cf55231c435e538c710d754e31c42fa608c710be58231c43b6548c710ed55231c4376538c710f594e31c43d5538c710dd14e31c4376528c710dd14a31c42f6608c710fc98231c43f1608c710cf95131c433d544c710bdd9531c4377654c710ed95131c43b5544c710f5d8d31c43d7534c710dd94d31c4374534c710f514d31c4354534c710dd94931c4374524c710f58c931c43d4324c710bd18131c433e540c710cf55031c435e530c710d754c31c43d5310c710be98031c42f9600c710cf95321c433d54c8710cf95221c433d5488710b798e21c42dd6388710db94a21c436d5288710be98221c42f96088710cf95121c433d5448710af99021c42bd6408710cf95021c433d5408710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cfd5240c433e5490310cf55240c433c5490310af59640c433d6590310cf94e40c433d5390310cf14e40c433f5290310cf94a40c433d5290310cf14a40c43b63190310ed4c640c433e5450310cf55140c42f76150310bd18540c433f5410310cf95040c433d5410310cf15040c42bd6510310cf59440c433e5310310cf54c40c433c5310310cfd4840c433e5210310cf54840c433c5210310ed8c440c43b53110310ee98040c433e54cc310cf55330c42f661cc310bd58730c43d531cc310ee10330c42be64c8310af59320c433e54c8310cf55320c436e52c8310db54b20c42f661c8310bd58720c43b840c8310cf95220c433d5488310dbd4a20c436c5288310afd9120c42bc6448310cf95120c433d5448310b7d8d20c42dc6348310db94920c436d5248310bdd8520c42f46148310cf95020c433d5408310dbd4820c436c5208310ee10020c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f189548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10d754c538427f65d0e109f997438427d65d0e109f19743842f661d0e10bd587438427f6590e109f996438427d6590e10be98243842f96090e109fd95438427e6550e109f595438427c6550e10bdd8543842f46150e109fd94438427e6510e109f594438427e64d4a109f593528427e63d4a109f58f528437561d4a10de98352842be6494a10af592528436f5294a109f992528433e6494a108f992528427d6494a10cf592528423d6494a109f98e528427d6
  | 9 => 0xd8d54c427c63553109fd8954c427c6255310cfd9554c433f6355310cf98d54c433d6355310cf18d54c433f6255310cf98954c433d6255310cf18954c433e6155310cf18554c433f6055310cf58154c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c42be64d4f10af59353c433e54d4f10cf55353c42ee62d4f10bb58b53c433e5494f10cf55253c435f5394f109f99253c427d6494f109f98a53c427d6294f10cf95153c433d5454f109fd9153c427c6454f109fd8953c427c6254f10af99053c42bd6414f10cf95053c433d5414f10d754c53c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c427d65d0f10cf95343c433d54d0f109fd9643c427e6590f109f59643c427c6590f10cf95243c433d5490f10bd98643c42f56190f109fd9543c427d6550f109f19543c433e5450f10cf55143c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c433e5410f10cf55043c42f66110f10bd58443c42be64d4b10af59352c433e54d4b10cf55352c42de63d4b10b758f52c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b10d798f52c425e63d4b109f58f52c435d63d4b109758f52c437661d4b10de58352c433e5494b10cf55252c436f5294b109f99252c427d6494b109f98e52c427d6394b10cf95152c433d5454b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c42be6414b10af59052c433e5414b10cf55052c436d5214b109f99052c433e6414b108f99052c427d6414b10cf59052c423d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c433e54d0b10cf55342c427f6590b109f99642c427d6590b109f19642c433e5490b10cf55242c427f6550b109f99542c427d6550b109f19542c433e5450b10cf55142c42df6350b10b718d42c42f76150b10bd18542c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c433e5410b10cf55042c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c433e54ccb10cf55332c436e52ccb10db54b32c42f661ccb10bd58732c427f658cb109f99632c427d658cb10cf95232c433d548cb10d794e32c435d538cb109fd9532c427d654cb109f19532c433e544cb10cf55132c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c433e540cb10cf55032c435e530cb10d754c32c436e520cb10db54832c42f6610cb10bd58432c433e54d0710cf55341c433e5490710cf55241c42fa6090710be58241c433e5450710cf55141c433e54107
  | 10 => 0x10836d5188420bb582210827f6548420af99021082bd6408420dd94421083755108420f948421082fa6008420be58021083ae6408420eb59021082ee6308420bb18c21082ee6108420f998421083e65108420db54421083e55108420f9d0421083e44108420f98c421083e53108420fa98021082ed6008420fa580210827e64940209f592500836e2194020db086500827d65d0020be597400837965d0020ded53400837954d0020be58b400837a52d0020fa88740083e821d00209fd96400827d6590020cf952400833d5490020bb98a40082ed6290020be982400833f6590020cf996400833d6590020cf19640083ae6290020eb58a400833e5290020cf946400833d5190020eb88640083ac2190020af98240082ba6090020cf942400827f65500209fd94400827e65100209f594400827c6510020cf950400833d5410020bb98840082ed6210020ee500400833f6510020cf994400833d6510020cf19440083ae6210020eb588400833e5210020cf944400833d5110020eb88440083ac2110020af98040083ba6010020cf94040082f96510020de59440082796510020be99040083ba6410020ded5040083ba5410020de55040083b95410020fa98840082f96210020fa588400837a5210020eed0840083ba4210020ee50840083b84210020eed0440083ba4110020ee50440083b84110020fa88440083e82110020ee994400833a6510020ee59440083396510020eed8840083ba6210020ea98840083b96210020ea58840083b86210020ce94840083bb6110020ee98440083b96110020ee18440083bb5110020ee94440083b95110020ee14440083ba3110020ee4c440083b83110020eec8440083ba2110020ea88440083b92110020ee08440083a82110020af99320082bd64c8020ee10320083ae64c8020eb59320082ee61c8020fad0320083ae40c8020eb10320083e840c8020ea10320082ed6288020db94a20083ba4088020ee10220082fa6488020be19220082f96288020de94a20083ea5288020fa88620083e821880209fd9520082bf6448020af19120082f76148020bd18520083ba4048020ee10120082ef6548020dbd95200826f6548020ebd9120083ac6448020f9d8520082ec6148020f918520082e46148020bbd81200836e5048020eb90120083ac4048020bed95200837b65480209ed9520083bb6448020be99120082f86448020ee19120082b86448020bed8920083eb6248020de94920083ea5248020fcd8520083f061480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f6395310cf98e54c433d6395310cf18e54c433f6295310cf98a54c433d6295310cf18a54c433e6195310cf18654c433f6095310cf58254c433f64553109f
  | 11 => 0x7e65d0120cfd53404833c54d0120bb98b40482ed62d0120ddd47404837451d01209f996404833f5490120cf952404833d5490120cf15240483775190120dd14640482be6590120cf996404823e6590120cfd4640483b75190120cdd46404833c5190120ed14640483345190120af982404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec6250120ddd45404837451501209f994404833f5410120cf950404833d5410120cf15040483775110120dd14440482be6510120cf994404823e6510120cfd4440483b75110120cdd44404833c5110120ed14440483345110120af98040483ba6010120af99320482bd64c8120cfd53204833c54c8120ddd47204837451c8120ee90320483b840c8120ee99320483b964c8120eed53204837a54c8120de15320483b854c8120ce15320483f351c8120fc147204833f5488120cf15220483775188120dd14620483af5488120eb15220483e75188120db14620483e45188120d914620483eb5088120eb90220483ac40881209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f54950209f986540827d6195020cfd91540827f62550209f589540827f61550209f18554083786055020cf55054082f66115020bd584540827e6415020cf990540827e6215020db988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de980540827e6494820cf992520823e64948209f592520833d64948208f592520827d65d0820cfd53420833c54d08209fd96420827d6590820cf952420833d5490820be98242082f960908209fd95420833f5450820cf15142082f76150820bd18542082fb60508209fd94420827d6510820cf950420833d5410820be98042082f96010820ddd46510827e64944209f592510827e63944209f58e510827f64544209f191510827f63544209f18d51082be6414420af59051082de6314420b758c510837551144209fd97410827e65d04209f597410833e54d0420cf55341082ee62d0420bb58b410827f65904209f996410827d6590420dd94641083755190420be98241082f960904209fd95410827d65504209f195410833e5450420cf55141082ef6250420bb18941083765150420dd54541082fb6050420be181410827f65104209f994410827d65104209fd96310827e658c4209f59631082ee628c420bb58a3108376518c420dd546310827f654c4209f595310827c654c420bbd8931082ec624c420dd9453108375514c420bed8131082f8604c4209fd94310827e650c4209f59431083d5310c420dd947210837551c8420be98321082f960c84209f59621082de6388420b758e21082ed6588420db59621082ee6388420f398e21082ce6388420f358e21082ec6388420bb9862
  | 12 => 0x15120cf994544823e6515120cfd88544833d6215120cfd84544833e6115120cf584544833c6115120cfd80544833d6015120cf480544827e65d0920cfd53424833c54d0920be98342482f960d09209f996424833f5490920cf152424827c6550920cfd51424833c5450920bdd8542482f46150920bed8142482f860509209f994424833f5410920cf15042483ad4210920cfd53514833c54d45209f993514827d64d45209f98f514827d63d4520ddd5351483b754d4520cdd53514837654d4520dd553514837454d4520ed153514833454d4520ddd4f51483d753d4520d5d4f514837764d4520dd993514837564d4520dd193514837763d4520dd98f514837563d4520dd18f514837762d4520ddd0b514837642d4520dd50b514837442d4520ddd83514837560d4520af99251482bd6494520cfd52514833c5494520b798e51482dd6394520d7d4e51483775194520afd9151482bc6454520cfd51514833c5454520b7d8d51482dc6354520d7d4d514833f5414520cf150514835f5314520dd544514827e64145209f590514827e63145209f58c51482f66514520dd99451483775414520edd5051483375414520dd95051483755414520dd15051483b45414520cd15051483775314520f5d4c51483575314520dd94c51483755314520dd14c51483d45314520d514c51483776414520dd99051483756414520dd19051483776314520dd98c51483756314520dd18c51483776214520ddd0851483764214520dd50851483744214520ddd8051483756014520dd480514827e65d05209f597414827c65d0520cfd53414833c54d0520d7d4f414835c53d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf152414835f5390520d714e41483775190520dd146414827f65505209f995414827c6550520cfd51414833c5450520d7d4d414835c5350520ddd45414837451505209f994414827d65105209f194414833f5410520cf150414835f5310520d714c41482ee6210520bb58841483775110520dd144414827e658c5209f596314827c658c520cfd52314833c548c520d7d4e314835c538c520ddd463148374518c5209fd95314827e654c5209f195314833f544c520cf1513148377514c520dd145314827e650c5209f594314827c650c520cfd50314833c540c520ddd443148374510c520f54c431482fa600c520be580314827e65c8520cfd53214833c54c8520d7d4f214835c53c8520dd147214833f5488520cf15221482de6388520b758e214835f5388520d714e21483775188520dd14621482fa6088520be582214833f5448520cf151214835f5348520d714d21483775148520dd14521482fb6048520be181214827e6508520af99021482bd6408520cfd50214833c5408520d7d4c214835c5308520ddd4421482
  | 13 => 0xcfd52548827e61952209f586548833f64552209fd85548827c6155220cf550548833e6415220db588548827e61152209f584548837a6015220cf953428833d54d0a20be98342882f960d0a20cfd52428833c5490a20cf951428833d5450a20bdd8542882f46150a20bed8142882f86050a20cfd50428833c5410a20af99251882bd6494620ddd46518827e6494620cf992518823e64946209f592518833d64946208f592518827e63946209f58e518827f64546209f191518827f63546209f18d51882de6314620b758c518837551146209fd97418827e65d06209f597418833f54d0620cf15341882ee62d0620bb58b418837651d0620dd547418827f65906209f996418827d65906209fd95418827d65506209f195418833f5450620cf15141882ef6250620bb189418827f65106209f994418827d6510620dd944418837551106209fd96318827e658c6209f59631882ee628c620bb58a3188376518c620dd546318827f654c6209f595318827c654c620bbd8931882ec624c620dd9453188375514c6209fd94318827e650c6209f59431883d5310c620be98031882f9600c620b798e21882dd6388620dd94621883755188620be98221882f96088620bb98e21883ce6388620b398e21883cd6388620bb18e21883e65188620db54621883e55188620fa98221882ed6088620fa58221883765148620dd54521882fb6048620be18121882be6408620af59021883e52108620bb594218836d6508620eb99021883ad6408620bb98c21882ec6308620f998421883e75108620db54421883e45108620f9d0421883e44108620f98c421883e53108620bb580218833e5490220cf55240882ee6290220bb58a408833e6590220cf59640883ae6290220eb58a408833e5190220cf54640883ae2190220eb086408833e5410220cf55040882ee6210220bb588408833e6510220cf59440883ae6210220eb588408833e5110220cf54440883ae2110220eb08440883ba6010220af99320882bd64c8220ee90320883b840c8220bb597208836d65c8220eb99320883ad64c8220bb98720883ae40c8220eb10320882f965c8220de59720883ba64c8220ee593208837a54c8220de153208827e61d51209f587544833f62d5120cf58b544833f61d5120cf987544833d61d5120cf187544833f60d5120cf583544833f5495120bd98654482f561951209f992544823e64951209f58a544836d62951209f986544837661951209d986544827d6195120dd586544827561951209f58254483796095120bdd8554482f46155120cfd91544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827b60551209f994544833d5415120cf990544827e62151209f188544827e61151209f58454482be65
  | 14 => 0x8154c833e6255320cf18954c833f6155320cf98554c833d6155320cf18554c833f6055320ced8154c833d6055320cf55054c833e6415320db98854c827e61153209f58454c83796015320cf95342c833d54d0b20cf95242c833d5490b20be98242c82f96090b20cf95142c833d5450b20bdd8542c82f46150b20be18142c833e5410b20cf55042c83ad4210b20be98042c82f96010b20af99351c82bd64d4720cf95351c833d54d4720b798f51c82dd63d4720cf95251c833d5494720b798e51c82dd6394720ddd4651c827e64947209f59251c827e6394720d798e51c825e63947209f58e51c835d63947209758e51c833e5454720cf55151c827f64547209f19151c827f63547209f18d51c82be6414720af59051c833e5414720cf55051c837551147209fd9741c827e65d07209f59741c833e54d0720cf55341c827f65907209f99641c827d6590720cf95241c833d5490720be98241c82f960907209fd9541c827d65507209f19541c833e5450720cf55141c82fb6050720be18141c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed62107209fd9631c827e658c7209f59631c833e548c720cf55231c835e538c720d754e31c827f654c7209f59531c827c654c720cf95131c833d544c720bed8131c82f8604c7209fd9431c827e650c7209f59431c833e540c720cf55031c8376510c720dd54431c83d5310c720cf95321c833d54c8720dd94721c837551c8720be98321c82f960c8720cf95221c833d5488720b798e21c82dd6388720cf95121c833d5448720af99021c82bd6408720cf95021c833d5408720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320be59740c837965d0320ded5340c83ba54d0320de55340c83b954d0320fa98b40c82f962d0320fa58b40c833f5490320cf95240c833d5490320cf15240c82bd6590320cf59640c833e5190320cf54640c833e5450320cf55140c82ef6250320bb18940c833f5410320cf95040c833d5410320cf15040c83b94010320af59440c833d6510320cf94440c833d5110320ee98040c82f96510320de59440c83ba6410320ded5040c83bb5410320ee95040c83795410320ee55040c83395410320ee15040c82f96210320eed0840c83ba4210320ee50840c83b84210320eed0440c83ba4110320ee50440c83b84110320ee59440c82b96510320ce59440c83bb6210320ee98840c83b96210320ee18840c83bb6110320ee98440c83b96110320ee18440c83bb5110320ee94440c83b95110320ee14440c83ba3110320ee4c440c83b83110320eec8440c83ba2110320ee48440c83b82110320bd98754882f561d5220db58b548827e61d5220dd987548827661d52209f587548837561d52209d587548837a60d522
  | 15 => 0x1033d5254440edd45511033e5154440af98c511039e6314440a798c51102bd6314440e758c511029d6314440af98851103ae6214440ab98851102bd6214440eb58851102ad6214440af984511033f5114440ed944511033d5114440ed54451102be6014440ee98051102ba6014440afd9631102be658c440af59631102bc658c440af58e31102be628c440af58a31102be618c440ed94631103b5518c440edcc631102be608c440af58231102bf654c440af99531102bd654c440af19531102bf624c440af18931103b6514c440ed545311039e314c440afd8131103bb604c440aed8131102bc604c440ee18131102b8604c440afd9431102be650c440af59431102bc650c440af98831102bd620c440af98431103b6310c440ed4c43110395310c440af98031103ba600c440ae98031102bd600c440ee58031102b9600c440afd9721102be65c8440af59721102bc65c8440afd8f21102be63c8440af58f21103ae52c8440eb54b21103b751c8440ed14721103b631c8440ed4c721102be60c8440af58321102bf6588440af99621102bd6588440af19621102be6388440e798e211029e6388440af58e211039d6388440a758e21102bc6388440af58a21102be6188440ed94621103b55188440ebc8621103b72188440af98221103ba6088440ae98221102bd6088440ee58221102b96088440afd9521102be6548440af59521102bc6548440afd8d21102be6348440af58d21102bc6348440eb94921103ad5248440ed94521103b55148440edc8521103ae2148440afd8121103bb6048440aed8121102bc6048440ee18121102b86048440afd9421102be6508440cf994211023e6508440af594211033d65084408f59421102bc6508440afd8c21102be6308440af58c21102bc6308440af98821102be6108440edd4421103b45108440ed8c421103b53108440ebc8421103b62108440eb48421103b52108440af98021102bd6008440af98a50102bd6294040cf94a501033d5294040af98650102bd6194040cf946501033d5194040cf98a501033d6294040cf986501033d6194040cf8c6501033d3194040cf0c6501033f2194040cf886501033d2194040cf086501033a6094040ee59650103bb6294040ee98a50102ba6294040ee58a50103b86294040eed4a50103ba5294040ee54a50103b85294040eed8650103ba6194040ee58650103b86194040eed4650103ba5194040ee54650103b85194040ee8c650103b93194040ee0c650103bb2194040ee88650103b92194040ee086501036e62d53209f98754c827d61d5320de58354c833f54953209f98654c827d6195320eed8254c833e6295320cf18a54c833f6195320cf98654c833d6195320cf18654c833f6095320cf58254c833f64553209fd8554c827c6155320ded8154c833f6555320eed
  | 16 => 0xd6490440af596411033d6590440af98e41102bd6390440af98a41102bd6290440af986411033d5190440af582411027f6550440afd95411033f6550440afd8d41102bc6350440afd8941102bc6250440cf54941103b76150440cf94541102bf6050440af99041103765110440dd54441102fa6010440be58041102be6310440af58c41102be6210440af58841102be6110440ed98441103b65110440cf54441103b55110440ee98041102bd6010440ee580411027f658c4409f996311027d658c440afd9231102be648c440af59231102bc648c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af99131102bd644c440af1913110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440afd9031102be640c440af59031102bc640c440f54c431102fa600c440be580311027f65c84409f997211027d65c8440afd9321102be64c8440af59321102bc64c8440db94b211036d52c8440edd0721103b441c84409fd96211027e65884409f59621102bf6488440af99221102bd6488440af19221102de6388440b758e21103765188440dd54621102fa6088440be582211027f65484409f595211027c6548440afd9121102be6448440af59121102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102bf6408440af99021102bd6408440af19021103b74108440ed104211033f4294040cf90a501033d4294040cf10a501033f4194040cf906501033d4194040cf10650102be62d0040af58b40102be61d0040af58740102bd6490040cf95240102f96490040de95240103ba5490040be98a40103bb4290040ee90a40103b94290040ee10a40103bb4190040ee90640103b94190040ee106401027f6550040afd95401033f65500408fd9540102bf6250040af18940102bf6150040af18540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040be18940103ba4250040ee10940102be61d4840af58752102be60d4840ee98352102ba60d4840af596521033f5294840ebd4a52102be6194840af58652103b86094840ebd49521033e5254840afd8552103b76154840add8552102bc6154840ed18552102b46154840ee18152102be6214840cfd4852103ae5214840cf54852103ad5214840cb54852102be6114840ed98452102b66114840af58452103b56114840ad58452102be6014840ee98052102ba6014840af98f51102bd63d4440af98b51102bd62d4440cfd4b511033d52d4440af98351103ba60d4440ae98351102bd6594440af98e51102bd6394440af98a51102bd6294440cfd4651103b75194440afd8d51102bc6354440afd8951102bc6254440cfd4951
  | 17 => 0x8640af994219033e65086408f99421902bd6508640cf594219023d6508640af19421902bf6308640af98c21902bd6308640af18c21903b65108640ed54421903b63108640ed4c421903af2108640ed88421903ad2108640ed48421902be6008640af580219027e61d49409f587525036f5294940bdd8552502f46154940db548525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bdd8542502f46150940bed8142502f860509409f99442503ad42109409f98f515027d63d45409f98b515027d62d4540ddd4651502df6354540b718d51502ef6254540bb189515037551145409f98c515027d63145409f988515027d62145409f99741503775190540dd14641502fa6090540be58241503775150540dd14541502fb6050540be181415027e65105409f996315027d658c5409f196315035f538c540d714e315027f654c5409f995315027c654c5409f994315027d650c5409f1943150377510c540dd14431503d5310c5409f997215027d65c85409f197215037751c8540dd147215027e65885409f596215027c6588540b798e21502dd6388540dbd4a215036c52885409fd95215027e65485409f195215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540ddd4421503745108540de14b405033f5290140cf14a405033f5190140cf14640503bb5090140dbd4a521027e61948409f58652102f76154840bd185521027f6154840ddd85521027761548409f185521037461548409d18552103786054840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be583421033e52d0840eb94b42103ad52d0840af98742102bd61d0840ee98342102bd60d0840ee58342102b960d08409f59642102bd6490840af596421033d6590840af98a421033d5290840af98642102bd6190840eed8242102bd6090840ee182421027f6550840bdd8542102f46150840bed8142102bf6550840cfd9542103af6250840cf94942102bf6150840edd8542102b76150840af18542103b46150840ad18542102bf6050840eed8142102bb6050840ee18142102be6410840db948421036d5210840be98042102f96010840af98842103ae6210840eb948421033d5210840eb548421032d5210840af98442102bd6110840ee98042102bd6010840ee580421037751944409f98e511027d63944409f98a511027d62944409fd8d511027c63544409fd89511027c6254440cfd09511033d4254440b798c51102dd6314440bb98851102ed6214440dd544511037651d0440dd54741102fa60d0440be58341102be63d0440af58f41102be62d0440af58b411033d52d0440cf94741103b651d0440ed54741103ba60d0440af58341103b960d04409f59641102b
  | 18 => 0xaf58841903b66110640cf54441902bd60106409fd96319027e658c6409f59631902bf648c640af99231902bd648c640af1923190376518c640dd546319027f654c6409f595319027c654c640afd9131902be644c640af59131902bc644c640dd9453190375514c6409fd94319027e650c6409f59431902bf640c640af99031902bd640c640af19031903d5310c6409fd97219027e65c86409f59721902bf64c8640af99321902bd64c8640af193219037651c8640dd54721903b741c8640ed107219027f65886409f996219027d6588640afd9221902be6488640af59221902bc6488640b798e21902dd63886409fd95219027d65486409f19521902bf6448640af99121902bd6448640af191219027f65086409f994219027d6508640afd9021902be6408640af59021902bc6408640dd94421903755108640edd0421903b44108640af597409033d65d0240af98b40902bd62d0240af98740902bd61d0240be597409037965d0240de94b40902be61d4a40ed98752902b661d4a40af58752903b561d4a40ad58752902be60d4a40ee98352902ba60d4a40cfd4a52903af5294a40cbd4a52902be6194a40af58652903af5254a40cf94952902bf6154a40af185529033f5214a40eb948529033d5214a40eb54852902be6114a40af58452902be6014a40ee98052902ba6014a40af98f51902bd63d4640af98b51902bd62d4640cfd4b519033d52d4640af98351903ba60d4640ae98351902be6394640af58e51902be6294640af58a519033f5194640edd4651902bf6354640af18d51902bf6254640af189519033f5254640cf54951903b75154640cf94551902be6314640e798c519029e6314640af58c519039d6314640a758c51902be6214640af588519033f5114640ed944519033d5114640ed54451902be6014640ee98051902ba6014640afd9631902be658c640af59631902bc658c640af98a31902bd628c640ed94631903b5518c640edcc631902be608c640af58231902bf654c640af99531902bd654c640af19531902bf624c640af18931903b6514c640ed545319039e314c640afd8131902bc604c640afd9431902be650c640af59431902bc650c640af98831902bd620c640ed8c431903b5310c640e54c431902be600c640af58031902bf65c8640af99721902bd65c8640af19721902bf63c8640af98f21902bd63c8640ed94721903b551c8640ed8c721903b531c8640af98321902bd60c8640afd9621902be6588640af59621902bc6588640af98e219039e6388640a798e21902bd6388640e758e219029d6388640af18e21903af2188640edc8621902be6088640af58221902bf6548640af99521902bd6548640af19521902bf6348640af98d21902bd6348640af18d21903b72148640eb88521902bf6048640af18121902bf650
  | 19 => 0x1500867f6354021d7d8d500865f63540219f18d500875c63540219718d50087763154021dd4c550086be6414021af590500873e5414021cf55050086de6314021b758c50087795014021bd98752d02f561d4b40dbd4a52d027e6194b409f58652d027f6154b409f18552d037b6054b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d02f76150b40bd18542d02f86050b40db94842d036d5210b40eb50842d02fa6010b40be58042d02de63d4740b758f51d02ee62d4740bb58b51d037751947409f98e51d027d63947409f98a51d027d62947409fd8d51d027c63547409fd8951d027c6254740dd54451d037651d0740dd54741d02fa60d0740be58341d03765110740dd54441d02fa6010740be58041d027f658c7409f99631d027d658c740d794e31d035d538c7409fd9531d027d654c7409f19531d02fb604c740be18131d027f650c7409f99431d027d650c740dd94431d0375510c740f54c431d02fa600c740be58031d027f65c87409f99721d027d65c8740dd94721d037551c87409fd9621d027e65887409f59621d02de6388740b758e21d036e5288740db54a21d02fa6088740be58221d027f65487409f59521d027c6548740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d036e5208740db54821d03765108740dd54421d02f661d4a40bd587529036f5294a409f986529027d6194a409fd85529027c6154a40db54852902bd65d0a40cf597429033e52d0a40af98742902bd61d0a40af583429036e5290a40db54a42902fa6090a40be58242903ae5290a40cf54a42903ad5290a40af98642902bd6190a40ee98242902bd6090a40ee582429036e5250a40db54942902f76150a40bd18542902fb6050a40be18142903af6250a40cf94942903ae5250a40cb94942903ad5250a40afd8542903b76150a40add8542902bc6150a40ed18542902b46150a40afd8142903bb6050a40ee18142902bd6510a40cf59442903ae6210a40cf54842902be6110a40af58442902bd6010a40ddd46519027e63946409f58e519027e62946409f58a519027f63546409f18d519027f62546409f189519033f4254640cf50951902de6314640b758c51903755114640af597419033d65d0640af98f41902bd63d0640af98b41902bd62d0640cf54b419033e51d0640af58341903765190640dd54641902fa6090640be58241902be6390640af58e41902be6290640af58a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902bf6350640af18d41902bf6250640af189419033d5250640edd85419033e5150640ed94541903b55150640afd8141903bb6050640ee18141902bd6510640cf59441902be6310640af58c41902be6210640
  | 20 => 0x875d538c821bd98632086f5618c8219fd95320873e544c821cf551320867d650c821cf950320873d540c821bd98432086f5610c8219f992510867d6494421d798e510867d6394421d758e510865d63944219f597410873e54d0421cf55341086f565d0421dd597410877754d0421ed953410877554d0421ed553410873554d0421bd58f41086f562d0421dd94b41087b742d0421ed50b41086f660d04219fd96410867d6590421cf952410873d5490421bb98a41086ed6290421bd986410867f6550421cf951410873d54504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421bd594410877565104219d59441086f66410421ed99041087775410421ed95041087755410421ed55041086f56310421f998841086f56210421f958841086e56210421dd94841086f660104219f597310873e54cc421cf553310875f53cc4219fd96310867d658c421cf952310873d548c421d794e310875d538c421bb98a31086ed628c421bd5963108775658c4219d59631086f6648c421bd19231087b6548c421ed55231086f5638c421dd94e31087d6538c421f554e3108774538c421f998a31086f5628c421f958a31086e5628c421dd94a31086f6608c4219fd95310873e544c421cf551310875f534c421bdd953108777654c421bd99131086f4644c421ed95131087b5544c421f5d8d31087d7534c421dd94d3108774534c421f514d3108754534c421bdd893108776524c421f58c931087d4324c421bd181310867f650c4219f994310867d650c4219f194310873e540c421cf550310875e530c421d754c31086ee620c421bb58831086f6610c421f54c4310873e54c8421cf55321087ae54c8421eb55321087e741c8421f910721087e631c8421f94c721086ee60c8421cf952210873d5488421b798e21086dd6388421bb58a210876e5288421bd99221086f46488421ed95221087b55488421bdd8e21087d66388421bd58e21087d56388421b558e21086f56288421dd94a21087e65288421bd982210867f6548421cf951210873d5448421bbd95210876f65484219bd9521087ae5448421eb55121086ef6148421db94521087e64148421f950521087e73148421f90c521086ec6048421bdd95210877765484219dd9521086f66448421bd19121087b65448421ed55121086f76348421bd58d21086f76248421f9d8921087765248421f994921087e64248421f950921087e73248421f90c921086f46048421af99350086bd64d4021cf953500873d54d4021cf952500873d5494021ded42500873f64940219f992500867d6494021cf192500867e63940219f58e50086bf6454021af191500873e5454021cf55150086df6354021b718d500867f6454021cfd91500863f64540219f191500873c64540218f19
  | 21 => 0x6388521f358e21487e75188521af99350486bd64d41219f993504873e64d41218f993504867d64d4121cf593504863d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d504877950141219f990504867d64141219f98c504867d6314121ddc84504876e21141219f98f540867d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f54950219f98e540867d63950219f982540867d60950218f59654087b46195021af982540873f6395021cf98e540873d6395021cf18e540873e6295021cf18a540873e6195021cf186540873f6095021cf982540863e6095021cf582540873c6095021cfd91540867f63550219f18d540877461550219fd81540867c6055021cfd9554087b46155021af181540873f6355021cf98d540873d6355021cf18d540873e6255021cf189540873e6155021cf18554087346155021cf085540873f6055021cf981540873d6055021cf181540863c6055021af990540873d54150219f990540873e64150218f990540867e63150219f58c540867e6215021db988540867e6115021dd984540867e60150219f58054086be64d4c21af593530873e54d4c21cf553530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530876e62d4c21dd987530867e60d4c219f583530867d6594c21cf952530873d5494c21d7d4e530867e6494c219f59253087766194c219f982530867d6094c21cf951530873d5454c219fd91530867c6454c21d7d8d530867f6054c219f18153086be6414c21af590530873e5414c21cf550530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c219fd96430867e6590c219f596430867c6590c21cf952430873d5490c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21cf950430873d5410c21bb98843086ed6210c21bd98443086f56110c219f992520867d64948219f98e520867d63948219f597420873e54d0821cf553420867f65908219f596420873e5490821cf55242086f66190821bd586420867f6550821cf951420873d5450821b7d8d42086dc6350821bdd8542086fb6050821be181420867f65108219f594420873e5410821cf55042087ad4210821bd98442086f561108219f597320873e54cc821cf55332086f561cc8219fd96320867d658c821cf952320873d548c821d794e320
  | 22 => 0x621d754c31886ee620c621bb58831887d5310c621d794f218875d53c8621bb597218876d65c8621f394f21887cd53c8621bb98321886f565c8621dd597218877654c8621dd15321887d653c8621dd54f21887d553c8621d554f21886be64d4221af59350886de63d4221b758f508875e53d4221d754f508875e5394221d754e508877b50942219f992508867d64942219f98e508867d6394221ddc8650886bf6454221af191508875e5354221d754d508867f6454221cfd91508863f64542219f191508873c64542218f191508867f63542219f18d50886de6314221b758c508875e5314221d754c508877950142219f98f544867d63d51219f983544867d60d5121cfd52544867e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f5394d219f992534867d6494d21db58a53487756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d219fd89534876f6254d21ddd85534867f6054d21ded81534867b6054d219f18153487786054d219e181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d21bb98b43486ed62d0d21bd98743486f561d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d219fd95434867e6550d219f595434867c6550d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486df6350921b718d42486f76150921bd18542486fb6050921be181424867e65109219f997324875f53cc921d714f32486f661cc921bd587324875e538c9219f19532486f7614c921bd185324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f994414875f53cc521d714f31486ee62cc521bb58b314867e658c5219f595314875f534c521d714d31486ef624c521bb189314867e650c521f54c4314877654c8521dd153214877753c8521dd54f21486de6388521b758e21487ce
  | 23 => 0xd59631c86f6648c721bd19231c8776538c721bd58a31c86f6608c721d794d31c875d534c721bbd8931c86ec624c721bd99131c86f4644c721f5d8d31c8776534c721f594d31c8756534c721f554d31c86f7624c721f9d8931c87e4624c721f58c931c86f4604c721f54c431c86be64d4321af59350c86de63d4321b758f50c877b50943219f99250c867d64943219f98e50c867d6394321afd9150c86bc64543219fd9150c873f64543218fd9150c867c6454321cf19150c863c64543219fd8d50c867c6354321dd8c550c87753154321de54050c86de63d5221b758f54886fa60d5221be583548867e63d5221d798f548865e63d52219f58f548875d63d52219758f548876d62d5221dd987548867e60d5221de983548867a60d52219f583548877960d52219e583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221b798c54886dd6315221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e60152219f580548875f5394e219f992538867d6494e219f982538867d6094e21d7d52538875e5494e21d7552538875c5494e21d7d92538875e6494e21d7592538875c6494e21d7d8a538875d6294e21d7186538875f6094e21d7982538875d6094e21d7182538867f6454e219f191538867f6054e219f181538875f6554e21d7d51538875e5454e21d7551538875c5454e21d7d91538875e6454e21d7591538875c6454e21d7d89538875d6254e21d7985538875c6154e21d7d81538875e6054e21d7581538875c6054e21d754c538867e6414e219f590538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e21d794f438875d53d0e21bd98743886f561d0e219fd96438867e6590e219f596438867c6590e21d794e438875d5390e219fd95438867d6550e219f195438875e5350e21d754d43886ef6250e21bb189438867f6510e219f994438867d6510e219f194438875e5310e21d754c43886ee6210e21bb588438873e54d0a21cf553428875e53d0a21d754f42886f661d0a21bd587428875e5390a21d754e428873e5450a21cf55142886df6350a21b718d428875e5350a21d754d42886f76150a21bd18542886fb6050a21be181428875e5310a21d754c42887ad4210a21bd98732886f561cca21d794e328875d538ca21cfd53418873c54d0621d794f418875d53d0621cf952418873d5490621d794e418875d5390621bb98a41886ed6290621cfd51418873c5450621d794d418875d5350621cf950418873d5410621d794c418875d5310621bb98841886ed6210621d754f318875e538c621d754e31886ee628c621bb58a318875e534c621d754d318875e530c
  | 24 => 0x410c73d5410431b798c410c6dd6310431ed504410c6f5638c431b558e310c776538c431f594e310c776528c431bd982310c67f654c431bdd95310c777654c4319dd95310c6f7634c431dd94d310c7d6534c431f5d0d310c7d6434c431f550d310c7d4434c431dd949310c6f4604c431f5d95310c6d7654c431d5d95310c7d7644c431f5991310c7d5644c431f5191310c7d7544c431f5951310c7d5544c431f5151310c7d7624c431f5989310c7d5624c431f5189310c7d7524c431f5949310c756524c431f5549310c7d4524c431f5d09310c7d6424c431f5509310c7d4424c431f5d81310c7d6604c431f5581310c7d4604c431b5181310c6be64d4031af593500c7d531d4031f54c6500c77b50940319f992500c67d64940319f98a500c67d6294031afd91500c6bc6454031bbd89500c6ec6254031f54c5500c67f6454031cfd91500c63f64540319f191500c73c64540318f191500c67f6254031dbd89500c66f62540319f189500c76c62540319b189500c7763154031dd4c5500c7553154031f54c4500c77950140319f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c6355321ddd8554c867f60553219f18154c873d5415321b798c54c86dd6315321cf99054c867e6315321d798c54c865e63153219f58c54c875d63153219758c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f219f98353c867d60d4f21d7d4e53c867e6494f219f59253c867e6094f219f58253c867f6454f219f19153c875f6354f219fd8153c867c6054f21af99053c86bd6414f21d754c53c867f65d0f219f99743c867d65d0f219f19743c873e54d0f21cf55343c86ee62d0f21bb58b43c867f6590f219f99643c867d6590f21d794e43c875d5390f21bd98643c86f56190f219fd9543c867e6550f219f59543c867c6550f21cf95143c873d5450f21d794d43c875d5350f21bdd8543c86f46150f219fd9443c867e6510f219f59443c86f66110f21bd58443c873f54d0b21cf15342c873e5490b21cf55242c86f66190b21bd58642c873f5450b21cf15142c86df6350b21b718d42c86f46150b21bed8142c86f86050b21cf95042c873d5410b21bd98442c86f56110b21bd98632c86f5618cb21cf95341c873d54d0721bb98b41c86ed62d0721bd59741c877565d0721ddd5341c87b654d0721dd55341c87b554d0721bd58f41c87e662d0721bd58b41c87e562d0721edd0b41c87b542d0721bd98341c873e5450721cf55141c86ef6250721bb18941c86f56510721dd59441c87b66410721ddd5041c87755410721bd58c41c86f56210721bd98041c875e53cc721d754f31c86ee62cc721bb58b31c86f5658c721d
  | 25 => 0x67c6454231cf191508c63c64542319fd89508c67c6254231d7cc5508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c67e64951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f993524c67d64d49319f983524c67d60d4931dbd4a524c6bf6454931af191524c6fb6054931be181524c6be6414931af590524c76d52149319f990524c73e64149318f990524c67d6414931cf590524c63d64149319f980524c67d60149319f997424c67d65d09319f197424c73e54d0931cf553424c76f52d0931db14b424c6f661d0931bd587424c67e65909319f596424c67c6590931cfd52424c73c54909319fd95424c67e65509319f195424c73e5450931cf551424c6f76150931bd185424c6fb6050931be181424c67e65109319f594424c67c6510931cfd50424c73c5410931dbd48424c76c52109319f997414c73f54d0531cf153414c6de63d0531b758f414c67e65905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531b798a314c7d7518c531b7582314c6be64d4131af593504c67e64d4131cf993504c63e64d41319f593504c73d64d41318f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c67e62141319f588504c75e3114131be983540c6f960d50319f98b540c67d62d50319f987540c77661d50319f983540c77a60d50319e983540c67d60d5031de583540c67960d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d54150319f990540c73e64150319f988540c67d62150319f984540c77661150319f980540c67d6015031dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c6be6414831af590520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c67f65908319f996420c67d65908319fd95420c67d65508319f195420c73e5450831cf551420c6f76150831bd185420c6fb6050831be181420c67f65108319f994420c67d6510831bd984420c6f561108319f992510c67d64944319f597410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f65504319fd94410c67e65104319f594410c67c6510431cf950
  | 26 => 0x2d4141ded4250506df6354141b718d50506ef6254141bb18950507795014141cfd90505067e63141419f58c505067e62141419f588505073f4214141cf508505073e4114141bb98b53106ed62d4c41d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41d794f431075d53d0c41bd98743106f561d0c419f596431067f6550c41bd98443106f56110c41b798f52106dd63d4841dbd4a521067e63948419f58e521067e60948419f582521067f63548419f18d521077461548419fd81521067c6054841db548521073e54d0841db94b421076d52d0841bd98742106f561d08419f596421067f6550841cf95142106df6350841b718d42106f76150841bed8142106f86050841db948421076d5210841eb50842106f66110841bd584421073d52d0441af98341106bd6490441cf95241106f56490441dd95241107b65490441bd98a411067f6550441afd95411073f65504418fd95411073d5250441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441ed90d41107b44350441bd189411077b5094041cf192501067e63940419f58e501067e62940419f58a501073f4194041cf506501067f63540419f18d501067f62540419f18950106de6314041b758c50106ee6214041bb58850107795014041d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c6ee6215231bb588548c73e6415231d758c548c67e6215231db988548c66e62152319f588548c76d62152319b588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cf951438c73d5450e31bdd85438c6f46150e31e750c438c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31af990528c6bd6414a31db548528c67f65d0a319f997428c67d65d0a31cf953428c73d54d0a31bd987428c6f561d0a319fd96428c67e6590a319f596428c76e5290a31db54a428c67f6550a319f595428c67c6550a31cf951428c73d5450a31b7d8d428c6dc6350a31db949428c76d5250a31bdd85428c6f46150a31bed81428c6f86050a319fd94428c67e6510a319f594428c6de6310a31b758c428c73e5490631cf552418c6de6390631b758e418c73e5410631cf550418c6de6310631b758c418c6f565cc631dd597318c6f662cc631af993508c6bd64d4231bb98b508c6ed62d4231ded42508c67e64942319f592508c67e62942319f58a508c7773194231afd91508c6bc64542319fd91508c73f64542318fd91508c
  | 27 => 0x41bd58743d076f5294b419f98e52d067d6394b419f98252d067d6094b41b7d8d52d06dc6354b419fd8d52d075f6354b4197d8d52d067c6354b41d718d52d065c6354b41ddd8552d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41cf54f42d073e52d0b41eb94b42d07ad52d0b41af98742d07b661d0b41ed58742d06be60d0b41b7d8d42d06dc6350b41bd18542d06fb6050b41be18142d06bf6550b41cfd9542d079f6350b41e718d42d073d5350b41ebd8942d073e5250b41edd8542d06bc6150b41ed18542d06b46150b41eed8142d06bc6050b41ee18142d06b86050b41db94842d076d5210b41bd98442d06f56110b41b798f50d06dd63d4341bb98b50d06ed62d4341ded4250d073c64943419f98e50d067d63943419f98a50d067d6294341cfd0a50d073d42943419fd8d50d067c63543419fd8950d067c6254341de54050d075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c53906fa6014e41be58053906f66190e41bd58643906de63d4a41b758f52906fa60d4a41be583529076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db548529076e5290a41db54a42906f66190a41bd58642906df6350a41b718d429076e5250a41db54942906f76150a41bd18542906fb6050a41be18142907ad4210a41af597419073d65d0641cf54b41906be60d0641bd597419077565d0641dd94b419077b5094241cfd92509067e63942419f58e509067e62942419f58a509073f41942419fd8d509067c63542419fd89509067c6254241b798c50906dd6314241de540509067e62d4d419f58b535067e60d4d419f583535075f5394d41bbd8953506ec6254d41bed8153506f86054d41d754c535067e6214d419f588535067e6014d419f580535075f5390d41d714e43506f66190d41bd58643506f76150d41bd185435067e63d49419f58f525067e60d49419f583525076f5294941b7d8d52506dc6354941bed8152506f86054941db548525067e63149419f58c525067e60149419f580525067e65d0941af997425073e65d0941cfd4f425073c52d0941af98742506be60d0941af592425076f5290941db14a42506f66190941bd58642506df6350941b718d425076f5250941db14942506f76150941bd18542506fb6050941be181425079f6350941e718d425073f5350941ebd8942507af5250941cf14942507ac5250941cb14942507b76150941af18542507b46150941eed8142506bc6050941ee18142506b860509419f99442506be6410941dd14b41507b742d0541ed50b41506bd6290541edd4641506be60905419f98f505067d63d41419f98b505067d6
  | 28 => 0xd8d5190a7c6354642cfd095190a7f60546429f1815190b755114642ded425090b3f6494242cfd0a5090a7e61942429f5865090a7f61542429f1855090b795014242ebd4a4250abd6190942af9824250a7e63d45429f58f5150a7e60d45429f5835150bb764d4542ddd4f5150bd753d4542d5d4f5150be742d4542ed90b5150b7764d4542ddd8f5150b7663d4542dd58f5150b7463d4542ddd8b5150b7742d4542dd90b5150b7760d4542dd9835150b7560d4542dd1835150ade6394542b758e5150b5f5394542ddd465150afa6094542be5825150adf6354542b718d5150b5f5354542bed815150af86054542d7d4c5150b7551145429f98c5150a7d63145429f9805150a7d6014542bd9945150b766514542ed5905150b775314542f5d4c5150b575314542dd94c5150b755314542dd14c5150bd45314542d514c5150be74214542ed9085150b776414542ddd8c5150b766314542dd58c5150b746314542ddd885150b774214542dd9085150b754214542ddd805150b766014542dd5805150b746014542ddd475050b7451d41429f9875050a7d61d4142ee5935050beb42d4142ee90b5050b7b51d4142fcd475050b7351d4142de9475050b7951d4142de1475050bf051d4142dc1475050b7b64d4142ded8b5050b7b42d4142de90b5050b7b61d4142de9875050b7961d4142de1875050af66194142bd5865050b775194142dd1465050b7b5094142bdd855050af46154142ddd455050b745154142ddd445050b745114142de5405050b3f6414142cf9085050a7e61141429f5845050afa6514142de9945050bbb6414142fad085050bba4214142ded445050bf35114142dcd445050b7a5114142de5445050b785114142fc1445050b705114142ded905050b3b6414142ded885050b7b4214142de9085050b3a4214142de5085050b7b6114142de9845050b796114142de1845050abe60d0842af5924210b3e5490842bb5924210b6e5490842eb9524210a7f6550842bdd854210af46150842bed814210af86050842afd954210b3f65508428fd954210abf6250842cf9494210bb76150842ed1854210bbb6050842af1814210bb86050842ae1814210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842f9d854210be46150842fad814210be86050842b798f5110add63d4442ddd465110a7e63944429f58e5110a7e60944429f5825110a7f63544429f18d5110b3f4254442cf5095110a7f60544429f1815110b755114442ded425010b3c6494042cfd0a5010b3d42940429f9865010a7d61940429fd855010a7c6154042bd9845010af56114042de5405010b5f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d06ee6214f41bb58853d06f661d0f
  | 29 => 0xc00000000000000001001800000480000018001002c00d0000004001400b00240010000021000c0040000001007c0040030000000c00600200030000000000000300180010000000001802c0000003000c001000c000005c02500040010000000002800000000010000000001800000180050000007000c000004400800000020000009000c02a0004007001c0010000002003000000140000004000000800e0014005001c0020028004002800300000000008000002800200040080000000001800800040040000004000800c0004000000400800000070020002000000100180000004001001000a00200000010002001800300080040010001000000300000020000001000800400000070040018008400c001c000001c01500280010000001004c001001000600440010000001005001c00c80010000006004000f0010005000c0000044000004c000000000800000000000000002c0090000001000002c0004002002000200340090050000004800000180190004000000c0050000000001800a0010000008c002000000100040000048000002006400000030000007001800500600110004000003400500000070004001002c00300000050000001000400000000000004005001c00100040020004000000000501140070004000000000a001c005000000500000070010013000400400040030014015000000400180030008018001400a0008003000c00a0000015002000f00080090014009000000000000020014000000c0060018000005400200ac00100200040014000000802c0000006000c00300400000008008003c00700040000020006002000100040060010002002800200040000000006000401800140060008000000000b005800d00600020000004000400600000030000003000000000000020004007000400a005c0000000003000400000280010000002000402b0004000000400100100060008000000c0000000000000c0000010005002000200080010000000006402000040020030000005c003002c0050000001007800100140020018000007c0000000000000c00000140000008001007000000000090050015000401a00100020030001000c00b000000b0000000000000600000150018013000c0000014005001000200040010004000000000400040160010016000000b000000000080090008001001800500040040010000001f7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742b798c51d0add6314742dd54451d0af661d4342bd58750d0b7b5094342cf19250d0a7e61943429f58650d0a7f61543429f18550d0b795014342af5974290b3d65d0a42af9834290aed65d0a42db5974290b7751946429f98e5190a7d63946429f9825190a7d60946429f
  | 30 => 0x1001000100540120008000002000a0000003000401f0008006000000e00040150000001000801100040120008000000801200000030008002000000e009800c000800600000010000001000001100000070004005000001200080020000008000000700100190000001000c00d000000a0000013001c00d0004000003000e002c0010024004000000400040030000000000000800040010000000000c00000000180008000002800200080000000004005000500100000018003000000a00240000004005000400000980040000002001c002000001b00000060020002001c00a001400600080000038002001c000000c0040000001002400600040110014019000400000280000018000003c008004000100180000000001000800700300020004005006400e000001f000000600240010000000000402a004c0020000004000c0000000004000c005001801f000c00100700090068013000400000200020004002001000600080020000003002c00000180020000005000c00000040150024002000c01f004c006003400e002801c0008009001801200000000020000001800b00000020000001002c0030004007003c0020050001000c016000003600000000008011000400800f000400280060010001000c0000050003000000100a400e000800f0000000000c0010004001000000f000000000000000000002004c000000000a004c001000001e0030000001c0000004006003003a0000007000c000000000a0000000000000e003c000003c0000000005000000100100040000001001800900900130054001009800e0014002000c0000054002000000000000020000000000800700000000000008001800500000000010009000000d0000000000801e00000010028009003c000000c009000c0000004000001800100240020000000000000a00040020004006001c00100000000000000002800a0014002000000c00740000004010002c0020014004001400d0000000001400200100090008001001c00a001c0000000003000400b0020010001000100a00010098010006000000000010004001002400100000020010000000000800280040008001000000a001800f0008023000800b000000a002c000000400400040070020000001000d009001a000c001009400300200030000019007c01c000001e000000b0028004000400200100020000004000c00300140080000000000000300040020000002000400501000380004002001c001001000200040050004003000000f001400c00080000040003000001800140000008000000c013000800a000400500040010000003001000600000000010000002400100080200004000001c0060008033000000000480000010000000800b000000f00040010050002000c00c0038009000000800
  | 31 => 0x5007001100780430000000000c007000000200d40120000033000c004001000200000020034003003c0040004000004c00000000000010005001c0000028008001400200340120018019000000c00340050000005002000400000040000013001801900100010000007000802f001c0030004001001c0060004000000000c000400000a8000001400000080100008023005400a001000100080020004007002c000001800600a00080004002003400e00340050010004001800600040000020000004000b00080040000001000800b000c000000800d000400000240000000000006000000a000e002000300000090020000008000e007c002008400a000800000240270008000000000000000000014003003000400080000008000004402c000400100040020070009001000500280010028000000c001002000b000000c002400000440030004006000c000000800f000400c000000c0024001000c0070038001000c00d00080060138004000c001000000700040010000001002400200540020020000001400000000000050000000000000100000014003005800100000050074000000000b0000004000000b0004003000c000000400000000170020000001800800000260004001000c00d002802c002800100240060000021000800c0004003000c000004c00400140030018006000400000000040000001003800a000c019003001600000040010004000000800100050000007000000000180000040023000000300500000004002000c001004401e002c00000000010010000000400200280150004012000800000240100000001001400300040020000011000000c001c0030014003004400500000020004003001c00000080660004001003c005001401000000000004002006c028000801300080000094003000c0010000007001400900000000028020000000d000c00200000030000001000c0010000001000c00a0024000006c0020020000000800200100000048000000c004000800c0004006000000100180040000004000400d001800b00000000010001000c000001c0020154000001400e0030000000c0000014004000400000380000008002000000200000030000029000000800000020000005000c01e0078000000800e004c000008000000000040004001006000000040000054004006c00500140010004004002000900080150000000000000d0000008000000200100000000001000400600100060004002001400200a800b002800000080070040000000c004000400b00040040020003000400500300020014006000000800b80060078024000c00c0000005000c0030004012005c0000014000004400c0000001000800000a40000008005000000000000060000000000400300140040030000000401a000c0
  | 32 => 0x3001c000004400e0004001001000400040020004000000c03a0018004001c01500040020004000001c003000000300000030000000002800100000000050000000401d000000600080080000004000800200000010008006002000d002000100000060000007000001100600050000003000000800000060000002007c0020000008007000d0000005005400000000170028000001800800000000024008000c0020000000002c0030020000000c0010000001000001400440010008002000c0010010017000000000200100004000000002500300040038003000400400000100008006000000a00040000000001001401600ac01e00000010004012000c0040018013000003200340000000000002800c00000000010003001c010000000700100020000001005c004000c0000084002005400c004800000000090044000000c0070010008001c003000400f004c004002800900100000030000000000900080000000007000400a001400500100040040000001c00000040030008000000400000100140008000000c000005000000040010004002005000a002800200340080030018005800500000040060003000c01a001c001004c009008800000000010014001000000a000400700140000004000000c00a00280000044000002000000000050004000000c000000002f00200020000000001c0030020018000000100000020034001002400c00080160008000000400d000800200000040000003001801500100030000008002c0040010001000c006001400500080000018003000400200280040000004002c00a0000006000c00400100010044004003c000002c00600280000024000000800d000000000080020008000003000200040030008001002400200040020014001004c002001800a0034007000000b00000010008005000c0020060017000000c001c001001000200040000008001001400000140040000017011c001004800a0000005001000800100030008001000000a0020007000000a005c002002800000000000058023002401500000000000000008003700080000004009000000a00000020004000000000d0004020001c004000800e00040000018001001c0070008011002000500000120000006000801700440000018002002400e00000090028003000c00d0014004000400800000080000003000800200340010050000000000b00040000000001002c00000080080000000000000400000000014001001c00700240000008011003800c0020000001800000140000000004000c01f006c00200080000000005002400b000c001000000a001c0000018002000400100740020048002000800100040110004004000800c00100090010003001000200040070020000003400200000040034004000000300040050
  | 33 => 0x74192ce24324b6769ad0167922cf00005a60002da62ed485390882dabac2fe649e09ee72e1a5b3c103416e355230bb4ce22f1c1b647965585aa9224a9702327e6052e75e685e9ef875682d06c09b61b51968193679460f2a162c96ae2eeceb3ea8a83611af37c580ee90200f8656854a5e227ba6821d8dc306e166f10932be588e0b368c9ca1fafd361a22fea375af809a1af063094a1a88c77203104cc4402c550109bc30e591268d1818a21a843c03f861c195a4503a5170c18498cb00000000002c12540cf128a510c8b5aad90bde0c9e00000003b8116200014e0acd800048a8d08000010abe5681605d00006370cae00003b4bd480002fc800018eab4e55864e20001fc68068e397041eba9d28000a1764de00013bebf6620c0000000bb8834236700000002afb748800017323480002f20a0820e51fca9f11e6400017e8000897c1e869e235e5f92f988b8a2335951e4e1a5138392fa3a33058513b338f6c22a87d6000016e256965ca6e000005323ea00000008588000000150168c82838661b3496aa47009e1a0c5928c6465ed960000003a151912c2d81e54a925be230998ccb920c5000005db6cb48741174cec4519e5ebf114dba87800000014dcb7ea28c200900e0001ce87c52aae8ebc00b002c008002c0010010000002c017000c006000c00900280010000006001400900100200000008001000000b002c0064002002c00900140000004008000c0130004003000400100000050000008001800200080010008005003400200000020058001000000300140180014008008c00300480010004004000000400100000000005003802b001800000100040008000011400f0014013002800000000040010005001400a000c003002000000000010008000001801a00180220000001000c01800000000000001007400200040010004004000001c00300000010000000400c000c006000000600000040038001000800c00100000028009000c002000000000080050000007000400700740000000000000000400780070008006000c0190004007003400300000010040007000c000000c003000c0090030003000c006000800200180000004016001400000000000004001003c000001000c00240000004008000c0090000001001c000000c00f0004007000400200f400600100220030004000000000800020010002000000300080020000000004000800080000000010000c005000000b00000010010000003c0030014001003400100000010094016000800000100030050002000800200180030000005000000000500030004018008c0360014008002c00500980090004000000000b006801d0000011001c004002c0020028004000000300000030020000001400600bc001001000200040000010000000000100040020024010003c
  | 34 => 0x276c7fa03795a38e967cc199ebea1bfec31657c2b626e04c7038000000006d1c002b4930bf62eac0c65c4000000000066d876e9ccea2400027e471418b46b01e00bd8000080800002e41c30b53afeca340000817b092a8405ee533d8d6933af244b02ed44e2b10a60671029bd0bff916955a1f813a900000001e1a64a9bed03400012cc42111346284f7631130206e71040990d4762550d188186a920003054580d05f7da2556aa900008bb80001f48b5aa9fa5341379d6463b0a802f20d356d40000c25ac206f209cf0b2062d0fca2087010000000000043e21beb5015d75e2c000303948480280004b2000000000002f954586f48000000000000007327e400002b824380002312ba98000000264e5f6a6c892b93cc000237501c083e11d4ecc18f819063824ec8ba8a074f58c24000223a82c503d8d3ae5e29ea8f2b0dac0bafe0f6f8ac52720bf2d7a9ce44b6732987004aaf2c1a18d783518c12000000021428cc19c886e0f66284000139c528f061b878cb50000eba06e4120231b0aab358be88e19aca0808dcc1cc22e45a116809438340785a86066b0fb81340e46a1b09d6bf9c147618abfc26482a77ddaf0c4dc67e27a0571d8e796860de1b0695311995390bea93ea1b02b08d68415ae180000000abda3ca738927600005069d465f6896c12fb14235a558da996a0800000000000002b0800000c07b580005620f209cf8510405800024f19da60124f200005f691580000001055000000000028471161f3410c2960b46512d00011797168000000246ca6c21ca000274c83140006195ea800000006be84fabde40008b72606000028c55ccf7426f2e8cc0341e18ef20d88a04000b925e6790529e46e98cc807e9b2a29c132c29d1732072000062b6e9c8d2423e0000000af991482c6c00082f80005375234bb909a6b46a28867c800000030c000003cec0caa1b0001f8d4f7895c41953f41978b52128802c5c000000001618a7980004ba1cbe00000000001a4684600b800000006599e3c0a0243c85b8e8681a95719cfe182564151f45821aa0b51e334e9d5fa616c79a2138cca5f06d2e579c08200021b4c1580000000d15a7100003868000008000066942b40000000356904eab09304851295c0000dc05324db80002178b0aadf33f700000001d303e4e69237780000000000294a37aa87247e3e5c00064601f400027c2565c00000000000001a1e00000007a000006141e0500006a2000000010500000000000000154400002c296b040c44504f200001d6b3f95a262300003239f8a238a0b06e8857a158800041d8f3c41e309e0000000000241039926526422bbfb9e1e886a90c095648000b360658000258eab040007d417649228d884e080004cf184e21641497a909767b909080a081e084a18d200000004a280008852970c19073e
  | 35 => 0x2d3b013845b000145543b8f8600000003f50000000264c0000e226b9255c1d69baa5f41cb066217b4310230099d0dd097713eabeec252000305b6741086835400001a29f60002cb60ca46d2517cd0300000006d160f4000166d0002a3c7cb0000000010cb5f98ee36e96a6789ad460000633824e670a5b9000000192c3678000000149497ce2b03efddb60000000bbc171560d000000000003d70f4b4da14320a5039d384000e4bc800066e00003db891e3549d47c3200000000000b678000000000096e12fab1a6a090001eee4fdc0a4240885c00000000002d80be4a91eaca8e0433d872dae618fd5260cc20000000681277e31617c6ab880006dd13ec894813237264f846798b58c0917413800002a31c66081a6985890ceb5ad866700006a4aea66181fd5b62321ae0e72d1e62aef26163a8904266682c6223a852283184a5cc1ec600023b02f9efd118f0fa176480b7000000090fefce3602a7075ba38a11f05320002bce00000005ee136c0364bca0001112000305a49c1f64201a9749fb91b60e9a8d804f5136af22c142d20d22b4280eaa6723f08e32af2821a7feb2c0116868148e22901acb38a6788858000530afbd89d1b250002cc2298967c8f7837a5da90a210693d73b6df8e766886b6dc06e60001c447e00000b2a9f4b1c0ac56a9180000000956b528000000087a2a68000046c00000d0fe432b6d0980b139d3c9189c66826e413c29be0001dd02e2b0d81298326000217a00000006238000351ca1e5edafc84eb9af100025866008281b3310b2385cbb21b300001a01e32bf687ba9498afe29f800000000000c10000000000067087181cbc0000001f2e6cdaad000024aaa3a054486da154a76b0794e48000b00800053a2ade8e380003fe1b4f000166965f4aa8715ab8d3c1c00087b04c870d591300000009bc000000000004c804940000000c43800065e26bc090ca540001b2c000000091e0000073a7fa8940f720001b7b2dc954e0000000000069c0002b5282300000040e6f109d10671f2e0aafc8000ae429a08c7056028ba6408e68a20b17e37853eaa2856114d091d2f7400030a8b7511ee2da0000b45110a000227e4ac6d0e2f71a3ea6d99b2c099f66000103248c9be4000000000003b6514d46228985707070000bbf921a9868000457000094fa43002017c2a1a00000002a60bb78450c3ec0004ae80003b10000b0413f52de0508b42039074452469c3c0007334000ad71cbc1fec00007e0a6a9fca1f39a8800003c2c590001f462808d728615d6c6bd07760749d5ac251d506772bc23b029bc9792d72000239264a130695367b20241e239242e00c12159ab8a943005f70fd055d94067124a857ec4004930000000099aa9d88306af400084aadb10dd80008efcd4412580006e206ba90facd067dde5c00014cb796
  | 36 => 0x20ee1e9102a79b06be0001c02191974c2f62ec638fab049ae691da9080009b380001f200007f981176cc80005dea280000103a4964000c19d3907565776065e9ac43623c8000007aa4f8e740000000b7589e400000000001b96134c00044f857800024920000000b69c00000000000000000000000078c08a039b13b13e3cf7e4dc95389f1a73a7290b069c70926925a3369dd111067e181a7ac9cc09b49a0d0000000b5d1a400000e887fc4e9c000000000021fa3752b038d7695e48380000000000000000085980009a906310000000000044400016d2702d37c384a97c37f8d10000226f59980007639bafb64524880dafd4747af7a9e6a134ab805da00005be8eb83a41d4c96a3878f594fc02f00000000000000000000004d840005bf0000000000000000002fd0000b48810400000000000000000000000028ae0002f4860a152400028a400000000002a2a0000d960002ca00001fbe4ed80007e4616033de8540000000b6200000000000000072000000000001d884cca8c70000596000000052710ce0f104bc460d6bc570800065fa5a74910e7257b00003fdaae800000008ee400000000000001b7a8bd800024a062ca3fe54a9c0c00057d20745d29a9b16b946f357918b8931aaf57a6fa7bb5c57cc0713030000000b14d54b0001ed40000dbe5ec209100001845781b52000265a7cfa540659005a279c0005c3acbe7655bda9b29f7e631ec9050400000f002262368000a1423ba04c5fd5ba5a31e56512da000127a00010ac9e00d7e1b6304478184dc00dae1c20700001a324049e4b0da8489a0a00000000000000b22106c6312258b9fad5e82ba4420002be2b02000000000008f988683c893520000ac497e800000006e4ac700000c188d240b400000000000001300000000052418a76ef11aa0001c5400000009b50662b1c0e0e0001e41ac396746d86b1626baf9351f010067f160045f021a2a2a621000000017180000001f520000000842861e0002cc68908af6bf3d3af7a721f2000000000020b6227144c1efad954de49c33aa100a000164400004269b11639ae317fd22d283e09ba4bc0001296adcae603f3989a20b274429686443d8853060c1b403be908e05da19c3fbadc82ff0000b4dc0000001260129d60612b814ea91dd2f3941bbaae017d274e93dd4c28c485c88dee0000000000109225c8bd41bc816f173800066407642e7c5fc7b38fe828db0d400000004e84000000000000023ec7e580007f829980001b9a6df17adb262d50000000025e23e213d8000000000000000000000c5a09683e27e480b6000000059e8782057000050303fa78e24d00002ab0a409a1c546af0a5e80db68b45ebf1d20000000013003421480000000bd9a82a0000e590000000624016d622d5f853aa7ae9596c5a2d880001596b14000000
  | 37 => 0xa47d0f5f46300006619e443ad237e7e68c806524fbc103ab54aadc2a01efcc56c0388bc6ed0528771ae9400000000001a365e080009ad02ce5701e7400000001328000bd3c0000002c0e6ba0e2d141240a00011b93448000558238545f8000955cb2026194aa5e2684e4511a284d293d4079af3c329a7d80058fb253663f200019110001fea847909e14cda6800000007cda350279af187a62cc030b08ce774939a009a4c87d69eeab5b800085707ec7f1154829f4d4a94e080c51fc0004ea8000c17c64f0858fb0529400012adf61ab000005b1800000026a0000172900005c3000160827c005416a069e7518000000187c3050c92a201d3c7132c99339264600494b700000005f980001ec089202c9cebb8f0b5c41ba2ba1f79d0b3c3818c0950f086dd800073e2187b41aa2001b1eb03968bdea312d388ca8934c09610256182ae57500006df8e570002c848afcd0e9e600007050e5daeaca92583cccfa1e9c72059d22ebd88f3ebab242d8f4d05e1b5061411bc000000156400180005cecbe1000000089c0d0b0000000a2c84ba64300009b08000000053e0e48daa0001e7e45b4e3169629540002b9a876000000000000002dec0cc5f6e8018000b200146599177279a087e9e595a00001d7480f12d218bcd450000000a98a8e05ea1dc743f90262a929ef6e2c0005742d9ac0ea608b1804ec596266abad0000180aaf7000285a5939a9a000000000000000000354000024c805000066e400084552e0a3c23c30002a2b30d80000000000b7c00005de0c6e00003f01dc000000016b266cc00000025f0affc5ba9dc03820ff158e7760b1204d5ec2775279e74700002ed80005c980000002a785d0800033d2b8a000000098a80000000dca31da8c900009f602b67b8a72985100020f700000008fd8000c1891e609550507c180000e661fc00015c82d31955845800008c02120001d7c000204c680000004dc77e0002eba73c8000000018d0218000b55800000000000cf8b92000011a03780001f51fce00001db4310000000221066c081281400007f326ea5c293f20929d40091149e83f08ea74b8f2a6440000787000000000000001ca00000a5e000000046b8000a8c4000488000060f00002c0c000000266016303ac2161aac99d9e729aa85e451f400095fb0730002ef8a4a800000000000000000bbb17fe7bf0ecf8e12f0e00015be90709d300011b86b380008402f8c000000000000001082b6800017ee69f4d1652e870631f051e703a75b8ef96526e6131064e6dd200025883ba67349e22bb28bd2ef49ad800000014d4a3f00002652e5094fec186c79cda0001ea27428000612d5d9bf55b1a0001afe5484674c06919277c80005b9800000015464a80000000136e825800000000008f364360000266ba41e1000028045001856000000000
  | 38 => 0x1c09e815c8ca388d80000002278352400059200004898000752166a77e19ee1825ef6368c1860000b6e84740005609fb700000000000000000000000020d2a1562b200000003d8000026a14ec000000096313c500000005ea4f56658cdc64dc121b0002b0a5bcdf726e8000085486e000006965c487e17772dac13aa303c0f00000000000a869eac576cba0c33834a47d8588472aaac605827a222207800025c6838000069eeb3998f13c298e89a050e93b800000004259a5e000000000019cc1399f0e4b2ce684ddc8640001f2200019567bc0c4aa4e1f7ab4a99345c84d3105502d073f0f3201804b0429a4b06199c64a164cd43f5a4f47fe113067a94cc731af1280016b400014b20000c4e00000e8bc9c4063e6400049913d500028f550e40445e6eb222178e2f000272ebdaacb81202c52000000000013fca40e952643ab5e4e6db903a0af9405a082e7980cef8312cf49de224e0d9297271e0fbe65a626645c1d1807b00009e81dcc929262089dc0000b117cc07417e8000270caa4000063cabf0bf60d14b6300005d9a33dc1096ee7c20000000076a4950000558a324216c0006fcadde4eb10881714580868a41aacd1d94501b085050a74d3950e78154ad0310d8e6638a016246dd4b94e05ca242e2abeadb84ee0a21e8cc4007843d9ad003a988577df0d8c000009c2920cab531e3266af00e046a0000be928b140909e597a251eb702a4844a17806dc8000a379a5c2460e36b760e4c253013ba3283026fdc88a8d95b6c77eaf6c630608daad2fae7d120ff9afe480000208ac075be191aa458bc2062bb6e2f1e7108000052800000000000000000000000054327ac84c25445c4000040c09d88981d6d3c08cb42121bcec3599ba7838000b0b092e5fc05142b3233c078e9ed000000000000226d048b64c785e000000000000321000266200006170ee1a86c3b0000000000097294f1000000000028ce18880000000000a2380008538000bca00000000000c08df5f0002a22000138c68f045c000000000000006a61796c209b142a41926000236600004e2888a0583d91c1a9fd8f68b4ea1318da8000b8819dfabc40005b4270026f81510c7001c0002c68566205665fe6be824979d18f49464624000923000000005d207519680d3013450e07a0ac905f94dd9456b8e10d0662400018d828d000000027300009c9ca6c527d6670001d650001bec73d09c6c041edc9bf050e49609f4b79a71282e87800d10d194fb8452572a246c1d043e60211feb999744000133684f037e87a1e3664f9de68b200000001c4600000000002f305f513969c456dc00006c40000000425000003b0000632000027e05bc4f101181e71c552e318f5556c0001e3a8263ae1eda0000c720000000812a420bb0d916000000010722cd00002ec2eb1b6a787707a7e10f
  | 39 => 0x8c686820000000936000087180002181d6837a86f418c15749c78a46000173300028d717b566077161f4464ed6c945800000000009a5000000000008658ab2000000065e80000ac875200c0b5e461afa071b82278dbc00023f189900030cc14580008d600000000000000000000000000000000b4ca082000148c00012880000000000000000017de5c2f0ba420000000000007088f1e055aa3400020e27e9c3881d31a7fa31942600013a4b25000010616ae0f18b2aa3e2f7600000000000050957800000019aa00000004ed2716000000023bc0006f6c000b8d800062480001ba08f20002261700c0001fd1fd2000075c8751ee60250000baba06e398e5be8f40cda01aaee001da49c95408c8aff8370326b06e6cfab8462b0970555998c95e2fc053b97527ef400000000000001d8c923a1a40000000bd2d4a82c98000000071e0e24000000000091ea5a32b5295a38ce20053f80000000000a4680003758d6c370800049d0000a3000003c000003ba000063a286e9df11e872400000000000b5c000000000001264cd2000140e0000000000070c38f1a1000000000001fb48a080005c8000045f5c652110f3838622f8a65021e48486bc4132b9e1c492a218fdacc2ca266413605acb17a890a369fa66bda6e20000b6615513c700008a81c6c88751440006762a725f0c000385800000000000d54000c0f6ed9780800064800000001292503438e0002382963e3fc4ffa0720f5a9e80c88000000265800017dc30fa9fc000166e0000000bea80007759bcc00012ac000046e00000000000ae869ac00014e28713dc2710755a5027b6000076ad5fe70f920436094168501fecbe1080891211d487091ac1cea6b23cf4121b2b1dda0476512aaa237d3eac0001f614b48dff02c9ef1cc874f833c4f6f00350a85dc55a2c72048e75a21099a76210e7c0e9c00000029ea27400004d00000a0780006470000bb948e6000268e3262b122a71f1aac61734000000005630904439f1e6cfdeb69549e1e36509408296c421f9e3b6124245c6928bf653f0688c0118d893518de18a193270d87bc819800000006ce27f000000025746c00000000000000018a4000061832eef5488aa2f00cb400085280000000000bfa90724040000ae202f240e2a1605fa46000030ee66b80004d6a888373800019f800000000000001e922f9000044cac44bfa6d3f0bfc000bca8bb40000791b0ca2b66600000b724000b1ba4f02d504f461a8a385d822d86ab8000a8eafa51dcc22886f0bc2c37872297225c499093845a0c000000067800000004302fc60002756000000000000000001b27822df12159800031f8000000065a00000009fa80008e8400000000004e8800068b1eaaaae1c987048000bd30e7600007e8b6100000000ae284e8a3000013fa00008103f8a8ec7
  | 40 => 0x2ad8528a93c2f6c000af6aca87b10000b02a21e3df1f9ebb10000028025e000000017080000c52afe8eb40002b1981e00004780001363a8a40008d7000077208be5af80001a9a9ec0c3234494b838a0000000849889f0f3018000012d6a529b0e6df58129f78fc400012e4000048c6d70d6e0000abe8ed01e231aa3c028297c425809168e1e07e4358ace152301998f961c78a00000002c3c000000000017068250e6ec391caa58047475d201aa0c661ac7bc8f1c9da9e8d9468188749acc517c10124d505e244910b482e0bb0aa09ce6000062a76f87ca29d800004f000052024acbb7c00000023e90000cc055b400018ba7e03f1800000019a2904907c089286f46922734b1070e0001937a2608327d3957cc0200000002eee3d4000000017aeb5996de83306013bb845a6a59c80b6600e27082c7ca930a8834caadc79f2df771e9cf004416a0b3e07a28a90ab80478cac7fd8ee110b65b65c58a962561156b1e1eb86b7a0fa40b25a8a281d5c7dd23dd2958bf01dd0640000300100000cd00000003e9c0000001a028a3c00000000009a180000002c384ee8b8800005c000000005630fc20d1800000002865fd91d00000372000000050b9fd03dcc78822198380000c00000132400000000000683114c00002990741e4090fa3f9b12bac9a1453fc000a62118e00000000001374a39234d7f70988add80007e8ab2c939883f92d1976b44225c0000000616800030a2e6a06d2acc3018296b311dc300000000000b84417146a9a295470000de4bd40b7494601da16616e052c0000000012e0a888b03768a286ea43124b8482900000001e49e4a000000000000009fc13e4a3500000000e6a60990ea0001c49000272a0001a5079a9bfaa00000061300000002f328d5c000000000000018220d2151200000000002fb200000001280000b229894bef80005e900000c4c0008848000000000000000005f6d4670002bea059800000000002340fe000000000000000000000000000001cf2a39000101c5e9d290c3824c026700003ece31b8710a10a8bb018a30881e4fa230a03d301bb099c6ab692f5f7b893461c280003f00000000000000019120002554ae52d627ad22043b35c7440f852cb5922fca8fab4aa388c1f1aa97c89f008dc32e48220000a447284b10862800028f000096baf261498358913ad2c11014a00a1e39900b9c6233ee762766400000023e80002ce4b850664000249896614e953f40006112cb28dc92d036687d0bc08ad2a1ca1cc1af5413ac258fe391ea54ab2136fa2b2d781b599730b292b45b929f3a7b92100568000ae8800034dab26c09033a374af5800000000000000bb22ff70002e2eb41000085f90e06d31a9c242847078d2e7b000000000010aa6c5a6847442e584bd8cd00000000b709c08a07000000000005b68
  | 41 => 0x98da8e20000c01d03b35f2e06af2977c19985feb380d54bfd212e684a06c17ed77ebc6840a000270e7f913bc7578e7000017bc00009c8843a3d2b832230af100000cc8000b4815d2000000089c84e849b8ca451b99c6aa1c00000000006fb9c8694188f472703d4a5e1a0692980007ec1eca0da0000aaa82a948ed5a75a4226c70ba7e600017ff5a320a375518ca222c79e34a4ccc9319832b21895210ab066b1321f832280003cea23e78e9a9d24aa35662f5653a170000a560000b91000099780002abb0be8c58000c20000000028068e8a6de00000003f3055885b228e2168000000000000027e8183a0db75ac0000002f5c34b272417100006f7a4d6617250c686056400009840002cee9d4d43c2c09e2448f0300ab684c40002f4295c1fb2947ef902b724e8000298e000048e9ed8d4da49a513a25a9f54a683e6470a26e5c922068022a192fb012c136af5e99f8018b4f86320771a4805125429f10b450bd0bfe79c2a5e96a5322b32000055c89e08b19d2d5762ed23be301f510859c817cd1163748d4485cb302f3289a59a211256a2c9c2260aea8ee1b309bb237605a420e6f9a8e3609166c16a9d84837221a8eac9f209f25bcb6362a89ca00004199b86a911abab6f2528b0ddbea2a8000084b294469c9f1872c5eccaa52cd423d9482ab9aebe81a0894bdb8ca23822cfc443072c0001d5f4700000b5d80000000000000000065b800000003508011abebb0160449787ea5d6211400000000000000487000055c00008d6c0000318000ab5800000000003ac9688abf000059c8000226c00000028ba8242fa60002c5c0001b0a78b000061e90460001a7a6d625d634b8e140c692fb51e9d456cb9a6402e9b42565a67a9f38ed841496b04caa10b000305c00000005be06060001e960000a3ab6a800002a8000000088054dadf21078000311c03e76727066e0af14ab18b2e00012e2c07a0381cd03a2be680000f08000000000000004436eb80000fb00000000000000000051b0e6058a9d5841521e43b40db714d1db82c223628299a9258667661bf04d27a40c2a36d1e4055262796789a2264a4000308000001882aaa968ffe6610872838e0a27db59d58300fb43d6aea8000000000030469e3000000000005b090dcb42c3398480000000156f68dead4a9398b223b00003ff09ea00027da5a6407400011947c40000000000000011201cb90c294be705967961f0650d9299f06b4a99151476a87243928f4c0cb8c977c102364ae07cc77faab62821469af5064e09d18be56960328d090caa0fccea4d80ea004230f061795e867f80006a528bc89ee2e600028643af00000000ab674b0000c13308e63509368d3000093684880001b78c388d8a00027d00001a4e06712bc6b9800000027dc6225fda0000000000028a98088768b78ae40001a76
  | 42 => 0xe0001fca00028b0000152a0001616000141815380000002d42182a6f94e780004ec84475e180000000000c294098000000020a9d859ea800000003a8000287000020ec911179e3ca00007708a4a8891ac2aa130efa04996f0719efe962f0e82bc2dfc000101461b80000679961bd0092415a067aa8c2a66418097eb7eee085a8a400506e2cc595800000022d496495b76720e842f5e8f47456a6e7e8004a179958b57780000002656c31973c4c212ca42696961a8026bbf5e15615d00009b180006c20789b52232c465400026c97f20000b960e78c19000168a3ea83850002d5a895952c9c091b3779000081e95ff2940246557000026782ef66eee220d68000028aba800023cc00000000b72e880000000496b0eac2c15423e813380001d369af4fb703dade033e69d80000000a2a9f390000abc0000000a7e00006ed8fd803ec10e1e9865000001220000000000000077396ec486421c00000002f1601c0001576827b03897989aa307800000011c40989ae2000262c2aaa8ed695901eb916fac331a42eb79194e62a1de8126927e1f9aff57d75992bffa52298ba5eebfe1518000073da298b1e8df2a9e8f5aa9c8c3a0772aeaec700000000001d082d908ed00000001d000008e0000035082cc00018f6b5700fc00000003118da405823fa6f0ab5833e000077b943e0001bdc30f0000976a06402680000001f62332c00014a800061640000000000000279c9ed0000bae1c8e96280000000da50e71ff020ec34d00016a410880006661d5700017841be23e04a913c8c34a2ac0000000adf19386a980002188000a7d0000ad2083a00000000002452560000000002b64bb00006750000000196cb510000000000000000006ce27a18994eae59e05820000000bc7000000009b8000000000016980001be7790e52dc03000083aa85bc128000000000000000005eb188a1128da80000e9b0000b1c9a58c668c886b0983164034740000002dbe0002f10bfcec63209120a0002ee7384cfd0ba8a69060394b6a42308c0f21ac60000000bce25d8000000095b0d5089aa27a52917faa19b0ca0002b50b5a0e271ff0000953d3144d6e1380002b060000000000064874389da000266c47204acc270000549400042ea8766d390d400019a366f800000029fe0000000b868d2f978a2644808afa46d513175a91223e989962982976b014b4e7ed91ea8af04feb64915a7de1cc42de991aaa686da516abaa167ec299030000abb06240001ab0b2e955800000004ea2276ba7a9de07f8b187778000ad890e816f70e6b7330f50711b1088f0000000049223c14924b09f0c0000cc142414b500025200000000aee00006e28000baa80000001c2c83e2a0000000000001adc0000b5649a4846c3f836e000000017f400000010b60881342ae494e25068000c2f05d47f7
  | 43 => 0x290000116a000000000030ae0000000000000000010f2000000095e9e46c1f85155cd9a2a0d81f8719a9cfa944129439483384422381011b08666c40000d48bbc000305274d20ac0ac0e4f1d981be00013ce2b78000000143f000152bb12014b37c1e085d198480192a40c2d00bc8468000000240e00000000000000691eee893913318508fac4e3800000029aa56f00001f8ee56bb418862938000ace9b940000828a592c3e525a1c83e500007c904080001e5f9192c4a408914a99986296748c6038d0e483800a1236cce624f88b4a075d4dfbf80000477a53686380001865e1f54d0000bbf13863d20bce1a1422e75323410abce32beea86206e8611713d02e1cd9c2a724e3302be2d2645a0000725192410a22be0000000117e5d20900000286119600000008cc800036c0930000252b000000000000000000f7825992b600000005db80000001e1970615aaa090000000000000024323b72d9c1d3adab58d87510000000b890000000000032a952d000000029900000f41867000260a2e88ce0518204b9811bdf7d580008201b02000309a2858700811959e5ce9e1200000000000cb0547475e7392818a6e93e0b3c0dfaa44b0347bd0e7e2c308e441f92408a7abaea75ac6a610150800016c00db40000002d3c6ed4000b7d643469326444de80002aa7006957c000507598100007ee4988000b9099500001b922a880006511d6633b819a76cd7915ee40000eb80000001d1372329a40000058b6c9286000010f007ad412593108000000000000008f3ae28a87efee7ce20285e6aa8e67026349da21fe1aa2f3600006384c0935c4cfad3072b1628a84a5b24f710024b630dc1ed96d818857c5bfe66ba965ed86559a2900c392aa0002bccc05234a00000004a3831d0000c1793300004e82462181d63098e12300002b46b5528024b19852150050235d000048e0fbaaf19a5d0fe04c0ace1d008518000000000000000e4000034394959e78320d210000608000000006c00007688000af900000beadce00011ba9218000000000040a000000023066ca400060d93ca000060400000005428000000000000014e69b68000000186000000008fb81d9022a8b64d61522202a4b8afea1928f1800099420ef9ae20240000000c443022bffc7100002c570000c9491c800000000000002737139c000000000062c2dd0b0a00000000fae9e280000002ce60fa95ea0001cf600000000001e8eb3a00004e3c00086400002a785ec6aa800050f47da000000000023bd00000006ee0da603e92828eb2bb63912d0200006f79892e54000253d0001d0452e216800000cc000179932955100aa00000000fca1b41b13a20800000029f294511faa4d1a0e6f818cd7d780000002e5a000121400013d80001d4223e80008079ce09708b9c4fdb0d380480a3000145
  | 44 => 0x18ff512ac820e6a7ec0434d0a9f20cedaf01f005e8a3f453797047aba044a611aa82d09bc60a387c44bb80f2a370f36072dc7667d9c409b4072645d866c4592ff663e18b70ec2af468e89feb6b87ae09f63fbba103b28442e6c00000003150da0c3da9109dd80005cd46fa0003050834de82bf90768a1583185edef7000000007db000004995ba5c20000bfc40006b21cbaa8bc0000000000a7400009ded25c6609470707a8b896d1c4834ad287000256a27e9a62000052045619580001109c451d710001c09b7a249a56d1412a0d2466ade1f289328b3a11309dc63980000000cb61aca58087795456f526e6000000003399ec878c27ba6a1cd4bb72fcc000271a00018932c3af06a8210be00023016530bee0000437bc128086e90fa418696fa92525eaba0abdebbc8ac819285b67a19ef87d2918128dce7a3e6aaba56baf479ab1b43c28d9873149a6500020f690a2ffa0001239044c00041103ba0a924ba25120fe7d311f032e946154d41d8a50800036400000002a0e6acae926c46c5853b514f72a134c000138d8e98d388da029a07ba77a7c95ac37a860d78a619745bc21ba0db0efe9f281ea64ec5921ec94466ea118806ec95e3a2994ac3cc8405b2171410b1a4469b159124fa34b5190be303cddba80d1f48726817020d103749a8182bec09141d6db6838823c9be897d64830e909659bd886c949a9400a8623e16d64549bf00654b6c6d2a60e4d98ed5a30d98a29a11ce3fc95ac6899f02219989860b161a8911f458fe1e3e34fa08494f136553c1b09304047334f503c2e98cc41058bb866fc77881480000000ec20002bbe000186b5770000acdc00020628325ee92150c8c00058f800034f0eea8c15049938000000022409b3245e0000000aaf1a9e00000001f7c78a2c928226e470a608e8f8ca50219a5dfca06035d4347e0935e000036aab4a24823080000000000000111e9611962b090000a5400005bd00007e0519c6e00cbc6e117385301cb27b75df00002708a8e280c34b40000f6a2ceabe0000909800000026e8564e354227b0c435901c00000000927a6f627a52f4378a3f99019c26463d72e28c8f06130aff01a3800073399bc262800069980002954c185501fbaa3dd90472d8ad0552800000001f0717176c959a52a7cdc20a46c1e9a161800039442b8162998e072a2ae8292dea000000044a800000000000001a3811880007a99df60fa18b6c0d80007c1ed3910cc00096ea9825c680009e1800000000005b3a7d630b86ee43c223864b80004ec0000b6e8b22a5b0000afd210685a800000015b8000000083a21e232f565e2129f4d00007081ffdf942689ad869c09f7aa5a7305d8906a946f076a270000000061bb7d1cdc78500002d000009e4179466a10a4000000081da1ce2e000002e1853699c8b34c4319e800
  | 45 => 0x7000001e608ee734000067d1f0aae198f00001c0d015994200023c100000004c3ac06000000000000000001aa2032c1bc0000000000000000011f2573094a00010065e84906bca46265ef86dca2f57400001fc2113cde09d480040002990157a44a6f3d750a8c9378215a65c86303dc16ca5d0117ab212c01f278492c1a870096e82a91ebc1b0c490ba1bac29b9d692788642a8eecf651380007a6c00000000008af590a0001a80390168131d1102a4c9ccf00014d25ff1c52000000009e45d673a80001800000000132e0000000346ae5367c13c0000000087a951627b0daf000058e14304a8a12800075dc26a8da4be053189ca56902ab6f00000be380f10000e95000292c00020160000000557a1d20a2e3dc1691398716000058d08c071a1b22000000075c016a38e169e57f292000023043571b9ebda000058b833db2980009cda9068b6a3e471f9ae079e24fe8ce8000751276e95881e4b088fde6859fc08f6218833c28be00025fcabc0e5cb17606000000000002e5200014720000c7a0000c820001020035800040aec8c0000000823c5ca23f987238c0000bbd8000000288402f8000205000053d8000000000000018a9000129846c4000000119153d19a6b9f67464b78000c4481f65e29e2566d0000746b0000000a143172b7410a4dbf6551a1d0662468c144d7a068c00000000000001f650001a52952000000000007a82d2873089c0006829f0000eca4c315c45ebd8d03fb0910270400000020260001cde00004aa38730acb4d400056d40000ff8000000093a0000000000110b8a28000237800000000000002afa0001ad6743c60c00029fa9152f6474306ae0d723fe3414000562800000000000002680b718c4c84e617c0002fcd00000000000000000000028697ea00030881b0800086e28486b488964b700006b11f092608f9e85d6775150aee1a4c1cd688d2c00a5f5cee167a521ba18c25ade8f1453bc2603215fa88dc00008b586eac2c9362b459dea77d0b4476f2aa00002048612546db2f026d662df8616c26a8566c0000000000000215854709b40ae5c889d21fae0000000000000030d2c924c6000000000001c510da000000048f988d7a7800000011184ac0e0a3bc80000942ecc2ac0dbc243996a7eb284263e97aa000039896c1d14000069250290e4000105a22091a2000152e0408000000000000031064bf00000000ada0b0c0000000cb700020408470032531291658cc00034a853a0000000b64c0005670a84000000073b291c88c8eaa7c99252c30c264a1026dc0002bd86150000b291184a0baeea8359c9e83522a00001da16b69952000005c2c29610b5f0000064c000803025644e947ea3d84726d82e989a720100d740006fa10e24e5000087980000000000b928000bed9fc393715da0000d046ae03667af40
  | 46 => 0x61630c8b1a6bb883c88b8ed45a69ec14cd0e9e63888a63d79fad1f7056eac4046c166afe82ee924e0000f4e0000e2600025300002e9a3520684b6d904361f80001bf89223d355320000000000000000002910c583621681ff2000000078882be06057ce22b8000652f05d000299654100009e5153e000149d0000000c0cd16e00025a541c000000000005888000b4d1d0200005f4000000047184f83f22254000162676d23640001d67ae0a4ea1d421f00b78c628342c465ae0beb3b886b609c8c701fdea2c6ff6cfb5ef423c45cac4e5f664fc264000079492283b480000000777654c40100000000000000000151e3b463b28591d9b4f1aefa97c915035583110001c60000035629300003b58d1c3e0067c00018172ea2df6649cb7c6ad2d9602a26d69c2a3190ba987422cae3e000302f10925b3a4ea13e62fc0927bea61409f95952999c1307087461a6300200025ce8346c6c308940253591b40000fea89f20b35ba2814c138c1c504571e88385e8afb0124afd8000140071d00029366d92dad30bd4f23cee9141a0400000014ac8c20000450a3965a49b6e0000000535e7a2a7c0000529961495c8a5c4f6985325884047a1e03075e292217210180000103bb14b3c01f3005b1d80009d0afca56994661ca81b506a06686c630728741a7432c4d606d180000002334135c00017fc0000000f846ff0000020c36f00007e5000000057f5ede39fc0000000f4069694509e102d6b7b87a8a410000bc589b0b37abdcae5983e4d75250bb60000b9184849ea0048ae393d981894f74cbe47ca230f184bf9f70a02aaceb6d2dbb793000000018a24e7d41e9ec25cc1761520ad5abd2a039e2e0000000bdf164c6001f429ff00009582bd09ab8bd062f00000001c4a0001da44629d981a1c00000016856ad800000000000000aee8e72c622751a4d00012f53fe8000bf78e240002bacb0d00000000f7a000253a5c0a6fe00029560000000677400028a8000afa4000b4619720000731869a0c7ae800000000000683c4ce34e6a88000000000000008ea191475bd24d0001d230002f8a665ab602dc16320360d5800013640001f43a1324f68e5000065ad5b07da8634a9d28ee3f49e566bb25fe00006bb508204e24702d3a86136abe00584049682c9cf0f1600000004c6895000029c200000000b55a7e5050f1a33a2c662f6a2e8b7e5ffeb32907a5ab2c4022e0000000000000000001a4276454a000000000008378cb8aba80009750000afa000047f23401f023c23e5909c2b00000341a0bcbef000000000000002844b05400045e818b1ffaf2e0000000000113c3b98000bedc000000000000000005d3966ba53114cc3f0000743400092c9436a27952f62e0b9ac1e0aec37e16945ca261d35899e9000140b32bc0000002b6a0001a7c000000000017d8a
  | 47 => 0x40222f257d8e924209a8e9ccac7a5941c3855b1190b9300000002594582aa4a85d8000c1c13560001bd02268000a94a8a20000dec6a81bf4b9d233800003100002c2e0830000a81848a5bdacd20000000b26a18960196ea00014405549f99320e17361b06529c9972a7d80cdcafb978c00002e2bcf827f412000026b1a20348da84760adaf000084cab9050a0000000000112e2f2e14c0000000c290000ac7a66e9d38000a04000052b80002f0052278319ca485ad1cac1d4ce4b501fc0bb82ac54cc15e6b41629418a5f45d51154694c0d25808742b2d0eb0a7dcdad9d42b6c7b830f4487995c05060180222e620000edd7f5aa6ab0c06ec0000000000000031a0000be180006f655b63ab1dfc00007584ac800000000000001a3482600008aec0009bd60b22fa5d8abf589ce830800000000009f500006ec1620b3a8000a218f530000000000000002b8d8e58ad756492800000000007b429d2000073334a16ca30e00000be0000a126b300000000a8b5818690800000003be57c958fc25400097e00006a40f9cc22880e95d80008c41e848d80c0a3bdae5cc0a80000000da26ca00380c7c000a5a9eab5b500000001fb800000000000000000000000028389b0020511f80000000b36785c000956c8ac19b800076c2905337a15eb024000822199ca42af4e911805e24b04b4b7f8000000000000026220002b3c61d88d6833a52c3362c0470ea15a0c283346caca8e87ba6b0799517b00002d2000023842f0000a31514304da5f1b9b861050edc330f8016ca8370931a684426fe0b5895ac46626322e0a4609d25f5d14d0000c02000000090b0ce630e9fd7000000000000000000e9a44690cc000154c54e8328585c0004500f83c085792b549d7202588520e300000001902be200009c1255a660da2400000002012f3aa812bd6adf80004d10df651a275e7b01bd6ad0980a3538330a1a81288870000a34ddb2a0d8000a1047f00001e7a9d62d1e5b12e02000000064f14d8a61aa0a58ea5c00970dfc2cb2546092000033f21722908fc30002e47bfc961d00007e2abe575a4b9800063deb024772a2659fb04f441306ab3c84d482816cc35317819dc94c5bb4e9ce48d80c859199854df822a248269e984aa7c5090ec69842a02469ab9c95646ca8f68794aa8800057c1b3a000000080fb02e842051c32fe85700027542fe65688c80000000076c5bc8000000126caa28000a320000250400077b2d604bc2e34b76b09898a053cbd122ec55404b80455d6234303334d4153c2410669b8429dc07797b5989aa984f7d7f80888172bb0496c934d71b3675da054e5f3a3684e9819c25a275d84763660bc983c297b0000000060c00000f000000000001ed210400000007b4c55a00029cc3490000000178e0002c1c0001e1a0000000095e04267595296190
  | 48 => 0x8000781c1380001f2a4f998aa46c800000023903c307380000a047d5054c70f0afc0002f8233ca29c0000000466aa1700020da0002dc4204e3d43d602d8a51800004f9429ad9927c0001fa1000230c4a014eb481a0dd7e4d8461d5100c04718108b0800000000780001d9600022952539a1bb7e188200001964acd1bb0000000958c2ad7539670000000070192f8ad0000000022c40000000325800000003d860b80009c880000000000b6891f80f780005efc43a00004fcbee4000b0740c20001d2100000009059448678303000017b28cb8000c1a00000002e550000873969ab2800000006c8c00025d00000002da04681330000000042b8210036de765aa10c6000042b1ca000000000007af2a8c00000000002170000192266a4000000000000025e028030f82960cce44bdaea8a690f661602a6c3429c6381808c860d4c80000bc40000000000000000000001a461da705addc00014220002a36000259a067652465209483d2ade28c6000040691cc71fc68a7920fb697140000000000000167f00029a2bed0c4268b8c1aa9400846a287c2c0b6220000148a847c29c2b5b0593cc22f3118300a6082ffc380a45d4ca297e479c468640000058f00002e840002da8229000180c1121ff720008ba81f1312000191e5814000ad3010b0000000000002a6109b5a26dab329beaa80000160c4b7ddc404fc00080b8bae7d600009c51b5e0001b3c977a19e3220000ad680000002ca23908d2035c000000000006b5000036e5c6c68c163f6e308ca0a78a4055e8a8200004020001599000000047b2a14ac7c32cba397ab5e5d1be33240006691d7eb3700000000000000259f0a11d4a1b18000a2d000084cc000bb28000921115e51d043855b8000abd5c326738000b07800000024c4744800000005b45418000277911600000001d8800020d800028f940872ba1016799a605e72d0c4a118fc0001d8009a587834ea845b71c00065640002bd00000002b649addd24725a1dc0000000817000000025513c9887000218ea1a8dc925fd000000a086c0000e3a42327d28601f20831812b3e2026c49a077a080c55044e1ff40c7a966049d44f164000ab9e9fee120ae043010374a64b0a00215cfe48b1ba78540bfa2d1ad8e6a3255500030fa208efb8578a9622f48dac9ca4140000078c7481d8687da8d9000205481e62a633a4e8082250d21d80e5375e9612000056a0000a2c000093882a0000934a31400005de6868000393851206cdee30000000bd28dd80a141483210e835d7142c0e806604515d90209976b0000000115000048e80000002fdc000119750a251c0002e68a3554440fd21e0000164109089ba6cf400000000000000816139007246f1faac02e98a0002132a2ccbd60648000ba000000000000abb82e4a7f4150000118d00023a429c9f5b
  | 49 => 0xa72115ce1192e306e38052b93a99a47915784a328e61b8935fb41c35e6279c249d00fa84ab8000bd5833679085d09a21c8a0373017ac0192a0001b242ad22260000000000000027105f740d8f7534d098eac2caca4e005f8bf400008e600003af800043b2c9e4c990a07d714f800000000002eda412c2e00001d5205e997c000106810d0152c160e2c3f69bca24698db1c6a4a27f8975e4f9c00000000009008df2293c000bb0a88a942800020ae83c3fc00007d8ddac503d3f8039978f3979fd44af80b41c716ba8a35bf61930eec3c4268c1bc29c800016e2aee87ce2bc800000016353f980002e930b96c8000006925322e50bf34f424c248220e45fb272ca69a26815d86de27ac0006bc92eaa8450b00001eec000000088a0d0f579a2aa6b4dfd82f8b05e29e2d9789782a58e82c01208155151c681a1042aca3954db2a385887b90287404e8f8aa4300000ea91e908b0a2435d8524a5e9d321e587f6ab10b04ae9af9c4a78aa6a9ea59c3958f90720ad8a4a9948601327a4005000088297ca00011da0846846000243a2fe15ee980034e587993d00012428beaf000fba3d10d7c49576b806600030a27b4b0407cc80005c6017c00025902311a6e127942b761ef5ac2d9afc00023c400000dd8a4800073a4000bdf8000590800080e800037100000000000b6085f2b6c22d00002cec8a88000224055cbd2404079b800037d12d1799a2b8c2ae4ee0000000c0c4000c3ca6f27ef18885328000bdc80008988000522e668bba42feb8e800008d03bc25f00002150024466145265d68d610b83d200022025a08b1611a98e404e5ec86d51c4e38300009bf6a589be287c58defd21139f3c476224a9102d3d240000043d303ea3a8f44b6f4a9432a263633ea3597029ebe2cfab3e00005a21291dc02efa5040002307000236c0000ee464c10a8950513300028fa0000b38a2508d80000000488a7203cb00acc05957e2f19b667aa6f7b34c1526000000021f160d3924e750d64000000065c0002c7ea520ae60001e940000e8e0dd4276be79e2a758ec74b8c888441923e50000d1e0002a6c8431de00682b1a886074a9e380006ec800051e04d60001c280000bd933faee600000000002ba400022d2c2e000000000000000111127000050266b52dfa2ca4b940004608000b23a33e0df197000009c23799638598a9fb131c000036affb000000036ba71817bdbbe0000000323111c1049c5e06e16fe0f6c00057180c764e9c0c0002328a0a0f423d1989b8271db5aa18ece17257bb68d40000b00c78c18305749990fc45fc0000002b7000029ae2508a0f1ee26a65a725d35bc6f467e2171c11e83867e70baa041524b2dd8b3205e006e9281dca832aea0b05de203a30cd61c5a9f9063aed65010c300af007eb1910fa00009800a4d34e32653d263381ae803
  | 50 => 0x5854000131a9e05f54e2570d21863a90000a0ea07098795317812e70c1f00000001ee88a59e6476a109807c9ccc9ce2194bd85bc9546c0009d8261c90780f937a26ee0938000c0a00000000998000000000000000aea7f47dbd9bd52f9180ba9299e6d7dd282871b267e9000032fa9806298ec83b7cc901ab1feb3d50f3419da1d64012f347a2a019586d45c1b20a2286b914e6d2308452f0292960afc24e987acc3099de00305bb29f0d0009c26328ea69d4000042356c958d655ce156856a6863d0000000141c5790000bc880006c301b252ce37400010de00011e06e3ec3aac815d591b8d664bf40001cd40ca65780003bd00000002aa6000070410c800012627cc000179045980005dd0000800ad94a8d426f0ca8c08000150e90a80000f90000000133a00026487d000007678f98000275c00000007e31769000000022325a41e4c0002ab02451558b9e3e08e2e4229b046ec694e8dba56ebad8e2a00029b20f28000b532cae1ae24247ff1d60000265429ed880000000000007c600013163fd0000bd34d6aaa150e69422136000056c000160e0000f2e896ab01778891262800007298000bf6d8ae5f8a3523961ffa3bc0d86af8202aa2fc20478289e3069829845e21a821e1f1c9132924a1e28d21bd972c4160be671dd9fa7458efc0c22b445cf851874aa6825e943f6b4da5ab60e887792211d2b89a08e33ce9b489b6e64b8482e63502dca51ce92e55a93e90e505eab05990623a05cbaac80002e600002c16184554c3240000000c3c5cd20bd8cb28d3cf5212cae7c000000000004460000208c410000000000019520e612f85b85e98bf1000254e5f80d0295b5b560001348c04a0229fe000052228756518000000000058b07e45408968000038400000002d40f6aa6329e22a60000b8b0c6ca4a167698c1fc897b057e000189645b01a263180003e4979866bc77c60a8ca059687aa863581c70658c090e529c47581cc0001a88000290e08007440591b1c0002c5408507f85758f8e029459448000000351e50bf8a4185e7c0004aa290f242c000a248dc885d009e52ee2c0acb80000000ede000000004514da228aa37ac32564aed047469a8b143a25d61aad6a560000a0e0000106c1054542e0af45540000000000000000000000152700001121124000863da543e7e8309d8cc5e3031c0000029000000838aec03200000000000296852340b07362e7600000000002d5828d22a9b9c8218baf0486ba2869300012182e3955454c000000000000000ddc000205a9e0881a188125674e24824128fa200027a6096209a6650eda605269a5da222c7969e185f009fb5dc0eb6b449b4461b51e2023851a00009a40001bb38ad2da8349a3aac02703f21a48cc8a187faa83247611593883d5c97
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x861f6454d200430e322a6900219594f6148010caaa7b0a400865653185200432aa98c290021179ce65080108bae7328400843e74194200421eba0ca10021179cc65080108bae6328400865553984200432aa9ac210021595d42108010e8aa6108400863965100200438d2988010021c654c4008010e54a420040086b16110020043d010880100218799253c4010c3ac929e200861e6454f100430eb22a7880218d59664c4010c6acab2620084757518f100423bbb2a7880219598d53c4010caeeca9e20086547654f100438b322a788021c559153c4010caaa731620084757518b100432aa98c588021c554e40c4010e2aa6206200847576946100438ca9881080218edd16584010c70e8b2c20086596594e100432cb2aa7080211e5da51840108bced29a200845c7694d100430fb24a6880218719253440108bceca9a200861f6454d100430e322a6880219394f6244010c9aa7b12200864e531891004326a98c4880218ed964044010c76ca202200869863101100438ca988088021aa1884044010caee7b2a200865473d95100431bb2ec8880218dd946444010caecbb1a20084757598d100426b39cc688021399ca6344010caeca31a20086976418d100434a320c688021955d463440108eceda9a200865463d4d100426a3b4a688021555d65344010caecb29a20084747654d100432a31aa688021351d95344010caecaa9a20086577654d10042ab3b2a688021551d95344010ca8eca9a20084547654d100438bb22a688021c51915344010ccecbb1220086c463d8910043a2a9ec4880211d5d662440109ace73122008655539891004273394c4880219554c6244010cceca31220086a7641891004352320c488021b1d8c6244010d88c63122008745531891004333a98c488021b194c6244010ccaa631220086c5531891004322a98c4880219554f6044010ca8c7282200866462941100436831e8088021d454f4044010dc0c5a0220084b676901100431bb2c8088021a518e4044010e2aa720220086a46290110042d938480880212d9d84044010c6eca202200869463101100438aa988088021a91884044010da0c6202200875153101100437031080880216c9d84044010d64ec20220086b3651011004399b288088021e4d8c4044010d64c620220086b06310110043c83188088021a418c4044010e66a62022008792531011004398a988088021e454c4044010e22a620220087a36210110043593108088021ac1884044010f40c420220086a062101100432db9eca88021961cf6544010c76cbb22200863b65191100432db2ec68802196d946344010d30c831a200865b6594d100432db2aa6880219ad976244010cd6ca31220086a8641891004364318c488021b418f6144010dc0c5b0a200847a7694510042d93a4a288021d454e5144010
  | 1 => 0x210432ca9cc0108219654d6008410c6acb320420863565590210423abb0a810821555cc5408410acae42a042084757598c210423aba8c6108213c5c06308410acae5a9842085557594c210432b31aa6108219518d5308410caeeca9842086547654c210438b322a610821c55915308410caaa731042087455398821042aab9ea410821d154e52084108eeeca9042087465354821043a8a9cc0108211ddd560084109a8e6b004208655535802104359322c010821d454d600841087ce9314a00843d7498a500422fb9ac528021171cd629401087ee8b0ca00843c745865004237b92c3280211b1c961940108eaec18ca00865553986400432aa9ac320021479ce6590010a3ae732c800852e729964004296b94cb20021479cc6590010a3ae632c800853a70196400438a38aa720021479cf5290010a3ae7a94800843e7614a400421ebb0a520021479cc5290010a3ae6294800871553986400438aa9ac3200210f5da5190010a6aeb98c800871553cc6400429aba86320021c554c3190010e2aa790c80084b576086400429aba84320021c554c21900108bce7328800845d73994400422f398ca20021175cc65100108dce4328800846d72194400432aa9cc2200219554d6110010a3ce7328800851d73994400428f398ca20021475cc6510010a5ce4328800852d72194400429d380ca20021475d65310010e28e2a9880087187054c400429b388a6200214e9c05310010a3ce7a90800851d73d48400429d386a4200214edc1521001087cec290800843d76148400428f398a420021475cc5210010e2aa7308800871553584400421ebb4a2200214d5d73110010e2aa79888008535750c4400438aa9862200216c5c03110010e2aa790880084b576084400429aba84220021c554c2110010b62e0108800861e53980400430ea9cc0200214e5d66010010c72cb300800871a53980400438ca9cc0200216c5c66010010c3cc929e600861d6494f300430f322a7980218759153cc010aaaeb98e600865565cc7300431cb288198021c654c40cc010f2662206600865553986300423bbaac3180219554d618c010caeca18c600847771d95300430fb24a69802187192534c010c3ec8a9a600861c6454d300432729ec4980219354f624c010c9ca6312600864d53189300432b29ec2980219554f614c010caca630a600865553185300426b3b66298021555d7314c010caecb98a60086c462cc5300432b29ac2180219554d610c010caaca1886008639651003004358b088018021e40c4400c010c3cc929e400861d6494f200430f322a7900218759153c8010e34a6206400871953103200432aa9cc3100219554d6188010acaea10c400874553086200423bb8eca90021179da53480108b8ed29a400861f6494d200430e324a690021179d953480108b8eca9a40
  | 2 => 0xca218210f9d261d481087ae930ea40865563987520422fb9ac929021171cd649481087ce9b02a40843d74d81520421fba2c0a90210f1d160548108baed298a40861e6494c520430eb24a62902117dd95314810c3cc8a98a40861d6454c5204237bb2a4290218b5915214810c3cc9318a40861d6498c520430f322c629021875916314810c5ac9310a40863564984520432ab1cc2290219658e60148108bce732e840845d73997420422f398cba1021175cc65d08108eaeb30e840865553987420432aa9ac3a1021179ce65908108bae732c840845e73196420422eb98cb21021179ce65508108bae732a840847671995420423d384caa102117dcd65508108b8e6b2a840847771595420423db82caa1021179cc65508108bae632a840845d75d8d420422eba8c6a1021179da53508108b8ed29a840845e7654d420422e3b2a6a10219594f6150810caaa7b0a840847575185420431b2a0c2a10219594c6150810caaa630a840866652185420432d29ec0a10219654f60508108f2ea302840863a54181420431caa0c0a10219694c6050810cb2a6302840866a52181420422f39cca21021175ce65108108bce6328840845d73194420423b388ca210211d5c565cc810caaa730e640865653587320432aa9ac3990210f9d0658c81087ae832c640847575986320432aa9cc3190219554d618c81087ee8b2a640843c7459532042a6392a6990219554f614c8108eaea30a640865553185320432ca9ec0990211e5d4604c81087ce9b28640843d74d94320421f3a0ca190210f5d0650c8108f4e032864084b870590320430f324a61902187592530c810a9ae5298640861e6454c320430eb22a6190214b5c854d0410cb2a7304820865953582410421f3b0a8a08214b5c8545041087eecaa0820865673597310432ab2ca7988219554e62cc410caacb1966208555750cb310432ab2865988219554d60cc41087ce9b2c620843d74d963104237396cb188211b5cb658c410cb2a6b04620843e74d94310421eba6ca18821555c5530c410caeca9886208655654c4310432d29ac018821555d6630c410caacb31862085557594c310423bbb2a6188219598d530c410aaeeca9862086577654c310432aa9cc4188211ddd5600c410caaa6b0062084e472580310423abb0a990821555cc54c8410acae42a642084757518f210423bbb2a7908219598d53c8410caacaa9e42086577654f210432a3b2a790821d1dc953c8410e88e4a9e420855573d4b210432aa9ac1908210f9d3658841087ae9b2c420845e73d96210422eb9ecb10821175d663884108beeab1c420845f7694e210422ebb4a71082117dd953884108baeca9c420843e74d94210421eba6ca10821879925308410c3ac9298420861e6454c210430eb22a6108218b5925208410c5ac8a90420874653484
  | 3 => 0xdb54c811087eec2a6408843d76153204430f326a7902218759353c8110c3cc829e408861d6414f2044317326a5902218b59352c8110c5cc8296408862d6414b204426ab9cc3902219514e61c8110cc8a530e4088654535872044332292c3902218e99440c8110e36a620640887185310320443942908190221ac98440c811087ce9b2a408843d74d95204422eb9eca902210fdd16548110878e8b2a408845f73595204421f3aec8902210f9d4644811087cedaa2408843c76d51204421f3b0a8902210f1d854481108bcebb1a408861f54d8d204430e2a6c690221179d46348110c3ea831a408861c5418d204422f3b6a690221171db5348110c3ec9a9a408861c64d4d204422f3b0a69022187d905348110c38c829a408862f64d492044316326a49022193d8f5248110c98c7a92408862f641492044316320a49022193d8c5248110c98c6292408863754d85204431a2a6c29022195d4f6148110ca8a7b0a408866452d85204431baa0c2902218d1506148110caea630a4088654531852044333a90c290221991486148110a70e02a0408871b53100204438c2988010221cad484008110e50a4200408861e64d4f104430eb26a7882218799053c4110c3ac829e208862e64d4b1044316b26a5882218b99052c4110c5ac829620887185310310443942908188221c615053c4110e50a829620887485314b10442b3394a7082219558c5384110e2ea829c20887145414e104432abb0a708221d114f5284110aace729420887275414a10443922a0a508221d1d4c5284110e88a629420886676314a1044332b18a5082214d9d64084110e28a7204208872452902104429b3a88108221c514c4084110e48a4204208865563987540432cb1cc1aa02117dcd62950108b8e6b14a80843f765505404316aa2c42a0219398e6215010c9ac7310a80862e64588540432731ac42a0219358d6215010cc8e2b10a808655639845404332b14c22a021539c85494c10a9ae42a4a60855671d8a530428f3a0c529821475d06294c10c9ac4314a60851e74186530428eba0c3298210f9d06254c1087ae8312a60845e76d51530422f3b0a8a9821539c85454c10a9ae42a2a6085567199153042a7b92c8a9821531c96454c10aa8e2b22a6085587059153042ab38ec4a9821559c66254c10a3ee8b12a60851c7458953042aa38ac4a9821561c16254c10a3ce8312a60851d741895304326b10c4a9821479d26154c10a3ae930aa60854e7298553042a6b94c2a9821559c86154c10ca8c3302a60865461181530422fbb2a6298211b9c865d0c108dae432e860847575987430432aa9cc3a18219554d61d0c108f4e032c860846f725954304236392caa18219554f6150c108eaea30a860865553185430432ca9ec0a18211e5d46050c10cb2a6302860846e721944304236b90
  | 4 => 0x5ac8290428863454987404432a29cc3a02219914a61d0110ca8a6b0e808866452587404428f39ca920221475ce5490110a5ce52a4808852d72952404428fb9aa920221471cd5490110a5ee4aa4808852c72552404430f32ea7202210f5da5390110a5ce529c808852d7294e404421fbb2a7202214bdc95390110a58e4a9c808861e6514e404431732ea520221c3d4f5290110e18a7a94808843d7694a404428f39ca520221475ce529011087eeca94808851f7354a404428e39aa5202214ddc55290110c5cca294808870f5314a4044386298a5202214d9d63190110c6ccb18c8088714538c6404439229463202218d9953190110e28a698c8088724524c6404422eb9ecaa02211b9cb65501108dae5b2a808845f735954044237b92caa02211b1c9655011087cec2a2808865453d854044332296c2a02218dd506150110ca8a630a808866452185404428f39ca820221475ce5410110a5ce52a0808852d72950404421fbb2a82022147dcd5410110a38e6aa0808852f725504044296392a8202214e1c26510110c3ccba98808843d7694c4044297394a6202214b5ca531011087eeca98808852f7254c4044296392a6202214edc15310110a3cea298808861e6514c404438cb80a6202218b9975210110e1ea7a90808870c53d484044394b86a4202210f5da5210110a3ce7290808851d739484044297394a4202210fdd95210110a3ee6a90808851c73548404429bb8aa4202214edc15210110a5cea290808862e651484044387a98a420221c314c5210110e56e02908088536758c4404431b32c6220221c514e3110110e48a51888088636654c4404438a29a6220221c91493110110b60e0988808861f539804044317a94c0202218b14a6010110e36a73008088718539804044395a94c020221ca14a601011087ceb326608843c75593304421fbb6a9982210f5db54cc11087eec2a6608843d76153304430f326a7982218759353cc110c3cc829e608861d6414f3044317326a5982218b59352cc110c5cc8296608862d6414b304432a29cc3982219914a61cc110ca8a6b0e60886645258730443a22926398221559d6318c110e88a518c60887185310230443942908118221e48c4408c11087ee8b2a608843c745953044237b92ca982211b1c9654c11087cedaa2608843c76d51304421f3b0a8982210f1d8544c1108dceda92608846c76d493044317b26a4982218b193524c1108dcec292608846c761493044317b20a4982218b190524c110c6ea9b0a608863454d853044333a96c2982219914b614c110c6ea830a608863454185304432ba98c2982219514c614c110ccea430a608866452185304432a32a6298221d1149314c110c70ca20260887285210130443583088098221e44c4404c11087ceb326408843c75593204421fbb6a9902210f5
  | 5 => 0x8654531854244333a90c2a12219914861509108f4ebb02848863854d81424432da9ec0a12219614f6050910cd0a5b02848863b54181424431c2a0c0a122196d4c6050910cb0a6302848866b521814244334290c0a1221179cf65109108bae7b28848845f73594424422e39aca212218d1526110910ca8a7308848866452984424423a3aac2212219514d6110910cc8a4b08848843e74d97324421eba6cb992210fdd165cc910878e8b2e648847671197324431baa4c3992218d15261cc910caea730e6488654539873244333a94c3992219914a61cc910c6ea8b0e648863454587324432ba9ac3992219514d61cc910cc8a4b0e648843e74d96324421eba6cb192210fdd1658c910878e8b2c648843e74d95324421eba6ca992210fdd1654c910878e8b2a648847b70595324421f3a6ca192210f5d3650c91087ee8b28648843c74594324421f3a0ca192210f5d0650c91087ceb320648843c75590324421fbb6a8192210f5db540c91087eec2a0648843d76150324430f326a61922187593530c910c3cc8298648861d6414c3244317326a4192218b593520c910c5cc8290648862d64148324423b3acc2192219514e610c910cc8a53086488654535843244332292c2192219614e600c910cd0a5300648847875580324431c2a4c1a0a219614f6050510cd0a5b02828863b54181414432c298c0a0a219a1486050510cb0a7306628865773996314431b32ea918a218d994548c510caccba9c62885667294e314438baa0a718a21c5150538c510ccccba94628874453d4a314423abb4a518a21559ce528c510cccca29462887275414a31443922a0a518a21d1d4c528c510e88a62946288654539823144332294c118a218e153604c510cd0a5b02628863854181314432da98c098a219a148604c510aacebb1a62885667294d314423b3b0a698a21c5d50534c510e28a829a62885567614d314432b3b0a698a21559c8534c510e88a7a9262885567394931442b3394a498a21c9d50524c510e48a829262887475314931443a2298a498a21d1dcc524c510e88e629262887476314931442ab3ac6498a21d114a324c510aa8ea1926288744520c931442e8b806498a21d814b604c510cc8a43026288760521813144332294c218a21c5d51310c510e28a89886288747524c431443a22926218a219a14a60c8510c3ea931c428861c5498e214430faa2c710a218715163885108beeda9c428845d76d4e214422fbb0a710a219398f5288510c9ac7a94428864e6314a2144326b18a510a218e1536048510cb0a7b02428863854181214432c298c090a219ad486048510970e0b20428843f76d50214421ebb6a810a210fdd8540851087aec2a0428861e64d4c214430eb26a610a21879905308510c3ac8298428862e64d482144316b26a410a218b9905208510c
  | 6 => 0x244387aa0a7a9221c315053d4910e8ae229ea48854e73d9352442a6b9ec9a9221595c764d4910ad2e1b26a48852e7498f5244296ba4c7a9221595c463d4910a5ce9b06a48852d74d8352442a739ec1a9221535cf60d4910a5ee8b06a48852c74583524430faa4c729221871526394910c3ea8b1ca48861c5458e524430f326a729221875935394910c3cc829ca48861d6414e5244317326a5292218b5935294910c9cc7a94a48864d63d4a524430f324c729221875926394910caae331ca48861e6458e524430eb22c7292219598d619491087ee8b04a48843c74582524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a92218715063549108bceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431bb26c2a92218d1936154910caec7b0aa48865463d85524421f3a6c0a92210f5d36054910c70c9b02a48865863d815244237bb2a4292214bdd15214910a58e8a90a48854f7354852442a639aa42922117dcd64149108b8e6b20a48852e749885244296ba4c429221539ce6214910a9ae7310a48843e74184524421eba0c2292218b99754149108daed2a0a48854e7395052442a6b9ca8292211bdd95414910a9ee6aa0a48854c735505244317328a829221939975314910e1ea9a98a48870c54d4c52443a3b8ea6292211b5da5314910a5ce9298a48852d7494c5244237bb2a6292214bdd15314910a58e8a98a48864e6514c5244387aa0a629221c31505314910e8ae2298a48854f7359052442a639ac82922159dc56414910ad6e0b20a4885657119052442b2b8cc6292214b9d06314910a5ae8318a4885657118c52442b4b80c629221599c64314910acae3218a48856a7090c52442b4b848629221599c44314910acae2218a48852e74d805244296ba6c0292214bdd16014910a58e8b00a48854f7358052442a639ac0292214bdd11014910a58e8880a48854f7344052442a639a2029221179cf65d09108bae7b2e848847571d97424422fb9acba1221171cd65d09108bce7b2c848845d73d96424422fb9acb21221171cd65909108bce7b2a848845d73d95424422f39ccaa1221175ce65509108bee6b2a848845c73595424423bb8acaa12211edc165509108e8e232a848847870195424422f3aec6a122187d536350910c38a9b1a848845e7518d424430faa0c6a12218715063509108bceda9a848845c76d4d424422f3b0a6a1221171d85350910c9ec7a92848864c63d494244327b18a4a12219318c52509108ecebb0a848863754d85424431a2a6c2a122195d4f6150910ca8a7b0a848866452d85424431baa0c2a12218d1506150910caea630a848
  | 7 => 0x9884218e59564c4210a6ae231ea8885397018f544428f39ec5aa221475cf62d5110a6ae3b16a88853970d8b544430faa4c72a22187d516395110c5ea9314a88862f5458a544432731cc52a2219358e6295110c9cc6b14a88864d6358a544432b31ac32a221999896195110c3ec9b1aa88861f6418d5444317b26c4aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110ca8c7b0aa88866462d85544432c31ec0aa2219a18b605511087eecaa0a88851f73550544428e39aa82a2214bdc95415110a58e4aa0a88851e73990544428eb9cc82a2214b9ca6415110a5ae5320a88845f73588544422e39ac42a2211ddc56215110a6ae2318a88851f73588544428e39ac42a2214ddc56215110a76e0b10a88853571188544421f3a4c5a9a210f5d262d4d10a9ce52a6a68854d7295353442a7b92a9a9a21531c954d4d10a3ce9316a68851d7498b53442abb8ac5a9a21479d360d4d10a3ae9b06a68854e72d8353442a6b96c1a9a2147dd160d4d10a38e8b06a68861e64d4e534430eb26a729a218bd526294d10c58a9314a68864f5398a5344317aa2c529a218b1516294d10c9ea6b14a68862e6498a5344316b24c529a218b9916294d10c5ac8b14a68866662586534421f3b6a8a9a210f9d85454d10c5ea9b12a68862c54d895344317aa0c4a9a218b1506254d10c5ec9b12a68862c64d895344317b20c4a9a218b1906254d10c6ec9b0aa68863464d855344333b16c2a9a219918b6154d1087ce9b02a68843d74d81534431c326c0a9a219a18b6054d108beeca98a68851f7454c534428e3a2a629a2153dc95314d10a98e4a98a68851e7498c534428eba4c629a21539ca6314d10a9ae5318a68861e65d50534422ebb4a829a21539ca5414d10a9ae52a0a68845f7655053442a7b92a829a21531c95414d10c3cca2a0a68871754584534438a2a2c229a21555c76414d10ab2e1b20a6885557119053442aab8ec429a21479d06214d10a3ae8310a6885557118853442acb80c429a21479d36014d10a3ae9b00a68851f74580534428e3a2c029a2153dc96014d10a98e4b00a68851f74440534428e3a22029a211b9cb65d0d108dae5b2e868846f725974344236392cba1a211b9cb6590d108dae5b2c868846f725964344236392cb21a218dd526190d10ca8a730c868865453586434431daa4c121a219614e6090d108f0eab048688658535824344237396caa1a211b5cb6550d108dee4b2a868846c72595434423db82caa1a211b9cb6510d108dae5b28868846f725944344236392ca21a218d1526110d10ca8a7308868865453584434421f3a4c7a92210f5d263d4910a9ce72a6a48854d7395352442a7b9aa9a9221531cd54d4910e1ea9a9ea48870c54d4f52442973a4a7a92214b5d253d4910a5ee8a9ea48852c7454f5
  | 8 => 0x8534c710ea2e029a63885567394931c423b3b0a498e21559d6324c710aa8ea1926388746520c931c432a298c098e21c5951310c710e2aa8988638863a5498031c431d2a2c018e21b44c5600c710c3ca931c438861d5498e21c430f2a2c710e21875516388710c9cc7294438864e6354a21c431d2a4c110e218e951608871087aeb320438843f7559021c421ebb4a810e210fdd95408710c6ca8b0e818843d7614e40c421ebb6a520621479cf5290310a3ae7a94818843d7614a40c438a29a63206210f9da5450310c6aa9b0a818843d76d5040c421ebb0a6206210f5db5210310a3ce7a90818851d73d4840c421ebb0a420621c514d3110310b60e0988818843d7695330c421fbb2a998621e44c440cc31087aeb326418843f7559320c421ebb4a9906210fdd954c83109aae730e418872a5210320c42a739ea5106210f5d7644831087aea322418843e7695120c421e3b2a890621879536348310c3aa9b1a418861e5418d20c430eaa0c6906211b9da5248310c98c7292418864c6354920c431b2a6c2906218d5536148310c6ca830a41886355418520c4333290c2906219954861483108daeda90418854e73d4820c439429080106219c58660d521087eecaa0a90845f73588548422e39ac42a4210f9d262d4e1087ae9316a70845f7654c5384237396cba1c211b5cb65d0e108dce532a870846d72995438429c382c9294218ddc56494a10c68e2b24a50863b70592528431c382c92942195d8f6154a10ca8c7b0aa50846f76548528422f39ecba1421175cf65d0a108bce732a850845d73995428422fb9acaa1421171cd6550a10a5ce5aa2850863454185428431daa0c0a14218e1506050a108bce6328850845d73194428421f3a6cb194210f5d3658ca1087ce932a650843d74995328421f3a6ca194210f5d3650ca109e0e2b00650843e76951418421ebb6a820c21745c032cc6108eaeda9863084d576d4c31842e9386a618c21555db530c610caaeda98630875270d4c31842e9380a618c2195d4e620c610caea6b0063084e472580318423abacc790c219598f53c8610aaee6a96430846e76949218425c382c810c211b5db52086109a8e6b28430855773594218431ab2ac810c216c1c16408610acae52a04308475761502184278b80c610c219518f5308610acee4a98430847576d482184272bb6a410c21789c35208610aaee6a9043085e270148218426a39ac010c210f5da5290210a3ee6a94810851c7354a408438ba9863204212d5d8219021087aed290810851f73548408428e39aa420421c5d4c3110210b62e018881084b57608440843c81888118421531cd5288210a98e6a90410872a521002084394a908010421e808440082109a8e6b2e210855773597108431ab2cc9884218d59564c4210ca8c7a9e21086566354f108431cb2cc
  | 9 => 0x6c220240106b0611012008317b2ec8900418bd946448020ccecbb0a4010667651852008353b20c290041a91906148020d8ec630a40106c46318520082573b480900418bd964048020d48c320240104ae761012008317b288090041a91844048020d56c0202401063b65d91200823cbacc8900412e9d26448020c76ca3224010638649492008354324a4900419cd976148020d60c9b0a4010673651852008358320c290041b418c6148020dc6c430a40106726158354c422fb9ac52a621171cd6295310a5ce431ca98852d7218e54c429b388c72a62147dcd6295310a38e6b14a9885347158a54c429db82c52a621479cc6295310a3ae6314a98862d6218a54c429b388c52a621479cc6195310a3ae630ca98852e7218654c4296b90c32a621479cf6095310a3ae7b04a98852e72d8254c4296b96c12a6214d9c66355310a76e0b1aa98851f7358954c428e39ac4aa6214d1c56255310a76e0b12a98862d6218954c428f39cc2aa621475ce6155310a3ee6b02a98851c7358154c4297b92c0aa6214b1c9605531087eecaa0a98862e5498b53c4316aa4c5a9e218b95162d4f10c5aa8b16a78854e72d4e53c421f3a0c4a9e210f5d06254f1087aed2a0a78843f7655053c422fbb2a629e218e9916014f10c6aa8b0c87886395418143c4237396ca21e211b5cb6510f10c6ca8b08878861e5498f52c430eaa4c7a96218795163d4b10c3aa8b1ea58861e6498f52c430eb24c7a96218799163d4b10c3ac8b1ea5886366498752c431ab24c3a96219598e61d4b10caac730ea58863a6458352c42a739ea5296210f9d06354b1087ae831aa58854e73d8952c421ebb4a8296210fdd95414b108deeca90a5885557398452c422f398cba1621175cc65d0b108bce732a858845d7399542c422fb9acaa1621171cd6550b10a58e4aa2858861e54d8d42c430eaa6c6a1621879506350b10c3aa831a858863654d8542c431aaa6c2a16218d9506150b10c6aa830a858863a54d8142c431d2a0c0a16218e5506050b108bce7b28858845d73d9442c4296b94a8216218d9516110b1087ce932e658843d7499732c421f3a0cb996210f5d065ccb10c6ca930e65886355498732c4333294c3996219954a61ccb10c6ca8b0e65886355458732c421f3a4cb196210f5d2658cb1087ce832a658843d7419532c431d2a6c0996218e950604cb1087ce9b28658843d74d9432c421f3a4ca196210f5d2650cb1087ce8328658843d7419432c421ebacc8196210fdd5640cb10970e0b20658843f7695032c421ebb4a8196210fdd9540cb1087aecaa065886395498241c431d2a4c020e218dd96544c710c6ecaaa263885c672d4d31c42e8b86a698e211d9d8534c7109acec29a63887165414d31c438aaa0a698e21559d8534c710cacec29a63887167414d31c438aba0a698e21559c
  | 10 => 0x45c73595410822f398caa0841175cc6550420c5aa8312821067151181410821fba2ca988410f1d1654c42087ce832a621043d7419531082aa39aa29884199189514c420974e9b026210657654c4310832ab2a6218841741c1310c420970e8b06421063564944210831ab22a2108412e1d16008420b50e0b2042105c57398421082b2ba88210841395da3108420acaeb18842106c4634c421082f03826210841331cd6008420b50e8b00421054e7388650082e539c43a00418b5526290020a6ce3b2c801053571d96400829b38ccb200414d5c66590020a74e032c801062f6598a400821ebb4a520041639ce219002095aec10c80104e471588400829b388ca200414d5c46510020a74e0328801062c6558840082d238ac4200410f5da5210020b1ce710880105a9708844008256bb042200414e5d66010020c72cb300801047b76550400823dbaac420041781c56210020a72e9290801053975d08400831cb2c84200414edd54210020b66e2a1080105b071508400831cb2884200418e5974110020b54e5a0880105a972d04400831cb2a82200416adc94110020b50e4a0880105ca7388440083d1a084220041e81042110020b54e5328801053a729944008395394ca200418edd96510020a72ebb1080106396598840082d4bb4c420041aad966210020d52cb31080105aa71988400829dbaac4200416cdc56210020b60e2b1080106ab7658840082d5baac420041cadd56210020f46e2b1080105a87158840083d038ac420041681c56210020a74ea31080106396518840082d5390c4200416c9c46210020b62e2310801053976948400831cbb4a4200414e9d76110020a72ebb0880105aa72d8440082d4b96c2200418e5956110020b56e4b0880105a872584400829d3a8c2200414e5d46110020b34e630880105997318440082d5390c2200416a5c86110020972ec288801059a7314440082ccb98a220041cc5445110020b54e518880105a9728c4400829dbaa62200414e1d53110020b56e498880105a8724c4400829d3a862200414e5d43110020f226218880105397588440082cd39c4220041665ce2110020b56ed10880105a97688440082d4bac4220041ca5d62110020b54e7108801078a7388440082c539c4220041e25ce2110020b50e710880105aa7188440083d130c4220041e85862110020a76ea90880104ba76084400825cbb04220041e84842110020b56ec10880106aa7608440082d4bb04220041aa5d82110020b54e610880105a87308440082d53884220041e89c42110020f46c210880107a06108440083d12884220041e85442110020f446210880107a131084400826739cc3900416a5d840c8020d52ec20640106aa611032008236bb4a5100411e5da5288020b94e710c40104ba76901200831db2c80900418ed944048020d6
  | 11 => 0x482aa39aa228a418d99754145208eaed2a0a2905567395051482aab9ca828a411ddd95414520aaee6aa0a29055473550514831b328a828a41959975314520e2ea9a98a29071454d4c514823abb4a628a414d9d25314520a6ae9298a2904777654c514829bba2a628a414d1d15314520e2ea8298a2907145414c51482b2b90c828a419558c6314520ae2e0318a29055673d8851482aab9ec428a411ddd94214520aaee6a10a2905547350851482b9b828428a415c1c14214520e4a84210a29053674d80514829aba6c028a414ddd16014520a68e8b00a2905577358051482aa39ac028a414ddd12014520a68e8900a2905577348051482aa39a4028a4117dcd65d05208b8e6b2e829045f73596414822e39acb20a41179cf65505208bae7b2a829045f73594414822e39aca20a418b1526210520c98a7310829064c535884148333310a220a4199588511052087ee8b2c629043c74596314821f3a6ca98a410f5d3654c520aace7a8a629043f74594314821e3a2ca18a41555cc510c520aacea9886290554754c4314832b32a6218a4195195310c520e2ea89886290714544c4314831c2a4c018a419c146600c520c70a8b0062906d131580314822f3acc710a4187d526388520c38a931c429045c7558e214830faa2c710a418715163885208baeda9c429045d7614e214832b31ea310a419558f5188520cacc628c429065563146214831c2a4c110a419c1466088520c70a8b04429063854d81214832c29ec090a418e1506048520cb0a6302429067351181214821fbb6a810a410f5db540852087eec2a0429043d76150214830f326a610a41875935308520c3cc8298429061d6414c214831b326a210a418d5935108520c58a93168090666621474048332b10a3a02414d9c65490120a6ae32a4809053771552404829a38aa9202418d9975190120e2ea7a8c809063665146404838ba98a320241c514c519012087cec2a2809062f541894048333b10a2a0241991885150120a6ce32a0809053571950404829cb84a8202410fdd95410120a6ee2aa0809053471550404829db82a8202418d9975110120e2ea7a88809063665144404838ba98a220241c514c5110120e66a3300809073051980404831b326a3902418d59351c8120c6cc828e4090635641472048399a888190241cc14440c8120e60a9a8e40907305414720483a8298a390241c9d505188120e48a828c40907475314620483a2298a3102414b9d64088120e48a3204409052e75102204839228881102410fdd95415020c6aa8b08a81065663984540831b322c22a0419598d6115020caac6b08a81066662584540831db82c9290414d5c454d0820a5ce5aa2841043e76151420829ab88a8a10410fdd954108208eeeca88a21063564544510832ab1aa228841331cd62d04208bee6b2a8210
  | 12 => 0x206416cdc56210320b60e2b1081906396518840c8354b10c4206416c9c46210320b62e2310819053975d8440c829cba8c220641669cc6110320b32e630881905aa7218440c82d4b90c2206412e5db5110320b34e7a88819059973d4440c82cd39ca220641665ce5110320e66a328881904b97614440c829dbaa62206414e1d53110320a74ea1888190539750c440c83c89886220641669ce2110320b32e710881904ba7608440c825cbb042206419598e61d5220cacc6b0ea91065563587548833930cc1aa4419c58660d522087eecaa0a91043e76951428831d2a0c0a14418e5506050a2087aedaa0851063471592518823bbb2a228c419558d51146208bce7b2e831045d73d97418822f39ccba0c41175ce65d0620a6ce3aa683104cc7358b418829aba4a3a0c418bd50625062087ce9b2c631043d74d963188332b14a318c410f9d3654c62087ae9b2a631055473545318821f3a6ca18c410f5d3650c620caeca9886310655654c43188274392c018c41b44c5600c620caac728c431065563546218836531cc110c418b59564086209d2e031843105c5739842188272bb6a210c41789c35108620b8ae628843105e27014421882b33a88210c41599d63108620d88c698843104cc73580218821ebb4a320441639ce219022095aec10c811062e54588408827238ac4204414d9c66510220a6ae332881105a471588408821ebb4a220441639ce211022095aec108811062d659932088316b2ac990441339ce61c8220c72cb326411063965593208829b38ec5aa2414d5c762d5120c6ea930ca89063754586544832b31cc32a2419958a6195120cacc6b0ca89065563586544831bb26c2aa24195d8f6155120c6ec830aa89065763185544832a318c2aa24199d886155120ce6c3b02a89067061d81544821fbb2a82a2414ddc55415120a68e2aa0a89053671990544829ab8cc82a2414ddc56215120a68e2b10a89052d72184544831c2a4c1a12418e15160d09208ecebb0a849063754d85424831a2a6c2a12411d9d46150920c6ea830a849063454185424831c2a6c0a12418ed506050920c70a8302849052c7550842482ab39ca9a8a41555ce54d4520aaee6aa6a29055473553514838baa6a7a8a41c515353d4520caec731ea2904777650b51482abb9a85a8a41551cd42d4520ae6e0a16a2905707050b514829b3a6c1a8a414d5d360d4520aace7b06a29055573d83514829bba2c1a8a414d1d160d4520c3ea931ca29061c5498e514830faa2c728a41871516394520c3cc9a9ca29061d64d4e514831b326a328a418d5935194520cacc7a8ca29065563d46514821f3b6a8a8a410f9d85454520c3ea9b1aa29061c54d8d514830faa0c6a8a41871506354520c3ec9a9aa29061c64d4d514823bbb2a228a414ddd15114520a68e8a88a2905577354451
  | 13 => 0x6508440c74e1328422063471594211024f398ca10881275cc6508440974e0328422043e75d8c211021ebaec6108812edc16308440970e0b18422043e7518c211021eba8c6108812e9c06308440972e0318422049d73984211025abb6a2108818d5975108440b64e1a8842204b576144211031ab28a210881655cc5108440b4ae428842205b270144211025abb462108818d5963108440b4ae51884220635654c4211034a31a62108816c1c13108440c5acb90842206356588421102cab9c42108816c9c2210844095eec908422062d6548421102d438242108812ddd92108440c6aca90842205b070484211024fb9ac010881271cd6008440c5cc4a94a0205377154a501029a38aa528081c54c43194040a3ce710ca02051d73886501021ebb043280816c9c76294040b62e3b14a0206aa6294a5010355312a5280816cdc55294040b60e2a94a0205b27114a50102d8b88a528081669cc6194040b32e630ca0206b16118650102cd398a328081665cc5194040b54e428ca0205a972146501025dbb263280812e1d93194040974ec18ca0204b9760c650103c898863280812e9da2194040972ed10ca02059a7388650102ccb9c43280812edd92194040970ec90ca0205367118a54c829ab88c52a641479cc6195320a3ae630ca99052e7218654c829b38ec12a6414d5c76095320a3ce730aa99051d7398554c829cb84c2aa6414edc16155320a6ee2b02a9905347158154c821fbb2a82a6418e5526090b20c6ca9b0a859063554d8542c831b2a0c2a16418d5506150b20c74a830285906395418142c82d438284216418e9526010b20c3ca931ea39061d5498f51c830f2a2c7a8e418755163d4720c3ca931ca39061d5498e51c830f2a2c728e41875516394720aace7a8ca39065563d4651c821ebb4a828e410fdd954147208eeeca88a39045e73d9641c822eb9ecb20e418e5526090720c72a8302839045e73d9441c822eb9eca20e418b951621072087ce932c639043d7499631c82aab8ca718e410f9d0654c72087ae832a63904ba74d8131c831d2a6c098e418e950604c72087ce9328639043d7499431c82aab9ca218e4155dd5310c720aaaea9886390656654c431c838b2a26218e41c5551310c720ba0e098863905557394721c825c3a2c190e41879526388720c3aa931c439061e5458e21c830eaa2c710e410f5d6640872087eeab2043904b87059021c821ebb4a810e410fdd95408720aaae728843904b87458021c83172a2c5a06418e59654d0320a3ce728c819051d7394640c821f3b4a8a06418b553625032087aedaa0819051e7394440c828eb9ca2206411e5db5410320972edaa081905aa72d5040c831cb2ca8206416a9c85410320b66e2a1081905b07150840c8354b1084206414e5d74110320a72ea20881905aa7210440c831cb2cc4
  | 14 => 0xa4b08a4206a5525845210312a92c2290818b54a6014840e52a5300a4206b2619805210358b0cc029081aa94a6014840d52a5300a42049f7358b511024e39ac5a88814d1c552d4440974e5306a2204b87058e511025c382c5288816c9c35194440974e031aa2204ba70d895110316312a4a88816c9c35154440d1cc7310a22068d639885110354384c428881a398d6214440d1ac6b10a2206a4715885110354382c4288818b58b5114440d2ac7288a2206a562944511021fbb2a2288818b589511444096eeca88a220695635445110352b12a228881a698e6014440d32c7300a2206aa629805110354b14c0288812e9ca6014440d64a3300a2206b151980511025d384cb188812b9c8658c44095ae432c62204ba70196311025db82c5188812e1c1628c440974e132a62204af725953110256392ca988812b9c8654c44095ae432a62204ba70195311025d386c4988812e5c3624c44087cea312622043d75189311031a32aa298881651cd514c440972ebb02622063975d81311025d396c0988812e5d4604c440974e430262206b2511813110358a88c098881a68c4604c440974e132862204ae721943110256b90ca188812e9c0650c440976e0b1062204b87058831102cab9c62188812ddd9310c440b60e09886220597764c4311034bbb26218881a5d95310c440d2aca9886220696624c431103c9b826218881651c1310c440f20e09886220590704c431103c898cc0188812e5d6600c440974e530062204af725803110256392c018881a54c5600c440b50e4b00622079131580311025dbaac0188818edd5600c440d56e4b0062204b8725803110354392c0188812a1c9600c440d6462b0062206b131580311034898ac0188812e9c265c844093ce632e422049d73197211025d380cb908812e9c363c8440972e1b1e42204ba7098f211025cb84c7908818b19552c8440b48e2a96422072552d4721102d9386a390881655cc51c8440b4ae428e42205b270147211034b31a63908816c1c131c844093ce7b2c422049d73d96211025d384cb10881279cc658844093ae632c42204ba70196211025d380c7108812e5c06388440d2ac728c422069563546211034ab1e4310881a698e6088440d32c730442204b975982211035928cc110881ac5466088440d6643304422069a63582211034cb1ac1108812edd56088440c76eab0442204ba70995211024fb9aca90881271cd654844096ee2b2a422049e73195211024eb98ca908812e9c06548440974e131a42204b97098d211021fbaac6908810f1d56348440976e0b1a42204b87058d211031632aa4908812d9da5148440e4aa4a8a42204b975d81211031cbaec0908812e5d46048440d54a430242206a9521812110359288c090881ac5446048440d664230242206aa21181211025d384ca108810f5da
  | 15 => 0x366594421902d2b94a210c818d9955108640c6acb18843205a5728c4219031ab2a6210c81a518d3108640b2ae710843204af76484219025bbb24210c8127dcd6008640938e6b00432046f7654852502b238aa42928199d486150940cc8a430a84a066852d81425031732a842128117dcd62d45408b8e6b16a2a04777654451502aa39aa228a81591c951145408dee4b2862a046c7259431502aab98a218a81559d5310c540aa8ea98862a045e73196215022eb98cb10a819398f5288540c9cc629442a045f73594215022e39aca10a810f9d66408540c5ac9a9042a063564d44215022f39cc329081175ce6194840caec7b0aa42065763185521032a318c2a90818d9d06154840c6ae830aa420673611815210338308c0a90811bdd95214840ccaa4b08a4204bb75583421031dbaac1a10814e5d76090840d2ec7b0a842069763185421034a318c2a10818d5d46150840d66c3b0284206b061d81421031db28c0a1081acd846050840d60c2302842052d759884210297bb2a4210818bdd95210840e4ee2a908420724715484210394382a4210818b5496110840c58c4a12a22047776544511032ab1aa22888199589511444093ee6b16822049c7358b411025db82c5a08814d1c552d0440976e0b1482204b970d894110316312a4a08812edc1621044095ce432462204ad721923110237b92ca988811b1c9654c4408dce432a622046d72195311025cb84c8988812bdc9644c440958e4b2262204bb70591311031a322a298881551cd514c440972e9b0262204b970d90311025cb80c81888195d95310c440caaca98862205d0704c4311025dba2c0188813a1c9600c440da262b00622049e73193211024eb98c9908818b19152c8440ac8e2a96422072552d07211022f39ecb10881175cf658844093ce7b24422049d73d92211025cb86c910881279cc648844093ae632442204b970192211032ab1ca3108819558d5188440976e8b04422045f73595211022e39aca90881179cc65484408bae632a42204b970991211024fb9ac890881271cd644844096ee2b2242204bb705912110316322a4908812e5d3604844087aebb20422063565d04211025abb082108818d5944108440b4ae420842205377150a501029a38a85280810f5da54900408f2ed2a480206aa6290a40102d9b8a85200816c1c54290040d50c521280204ba7610940102d5386a529081279ce619484093ae730ca4204ba70986521025c382c3290816a9c35254840d2ec7b0aa42069763185521034a318c2a9081acd846054840d60c2302a42043f765485210257bb2a4290814bdd95214840c5eeca90a42072771548521039238aa429081ca1c15214840d2cc7308a420725529845210316a92c229081a598d6114840d2ac6b08a42072552584521031ba92c229081a99496114840c6a
  | 16 => 0x2ab39ea328e81599cb51947408bce7b12a3a045d73d8951d023bbb2a228e811b9ca650c7408dae532863a05557394431d02abbaa6218e81555d5310c740ba0e098863a04e87258031d036898ac018e81179cf65887408bae7b2c43a064e6394a21d032731aa510e81179ce65087408bae732843a062e6454821d031b322a210e81179ce6194a408bae730ca52046f765485290335290c0a14814b9da5250a40c5ced292852069763d854290393296c2a1481a5d8c6150a40d28c630a852072652185429031b3a8c2a14818d5d46150a40e54a5b02852072a521814290359b08c0a1481ac1846050a408bce7b12a32045d73d89519029a38a84a8c811ddd95114640caac6a88a32049f7358b419024e39ac5a0c811b9cb658c6408dae5b2c63204ae721923190256b90c918c818d592518c64095ee4b2263204ac7259131902aa39aa298c8195d95310c640caaca988632045e73d97219022eb9ecb90c81179ce65c86408bae732e432049e73193219024eb98c990c81179cf65886408bae7b2c432049e73d92219024eb9ec910c81279cc648864093ae6324432049f73591219024e39ac890c818d5925108640acae528843206356454421902d2b908210c81a598e61d4a40d2cc6b0ea52069563587529035930cc1a9481ac58660d4a40a74e1a94a5205aa70d4a5290296bb6a5294818b5db5294a40e4ce3a94a52072571d4a5290297386a529481ca9c35294a40a54e1a94a52049e73986529024eb9cc3294816a9c35254a4087eeca90a5204af765485290355294c029481aa54a6014a40c5cc5a96a3205b270d46519024f39ec4a8c81275cf6254640a6ce3a92a32053a70d4951902d9386a2a8c81a558e511464087eeca88a3204b776544519034ab1aa228c81a698e6014640d32c7300a3206b2519805190358a8cc028c812b9cb658c64095ae5b2c63204ba70996319025d380cb18c818d996518c64095ce532a63204ad72995319025d384ca98c812e9c0654c64087cea312632043d7518931902ca39aa298c812e9c2650c640974e032863204b7764c431902cbbb26218c81a5dd9310c640d2eca9886320695654c4319034b3126218c81651c1310c64095ee4b0063204ac72580319034a98ac018c81279cf65c864093ae7b2e432049e73997219024eb9ccb90c812e9c265c8640974e032e4320696634c7219024f39ecb10c81275cf6588640974e132c432049e73196219024eb98cb10c812e9c06588640d2ac790c432049e73995219024eb9cca90c812e9c26548640974e032a432043f7558d219021e3aac690c812edc16348640970e0b1a43204ba70994219031b38cca10c818e9c2650864093ce6328432049d73194219025d380ca10c810f9d7630864087aebb18432043e7518c219021eba8c610c812e9c06308640972e031843206
  | 17 => 0x18431e1c16550c21c5aa9b128610c6d751894308716aa0c4a18438d5536150c218eaea30a8610e3554185430863d380ca218431e5c06510c218daeb3108610e2e54588430871b2a2c2218438d5516190821c3ca9b1a8410e1d54d8d420870f2a0c6a1043875506350821c6ca9b0a8410e3554d85420871d2a6c0a10438e5536050821c74a83028410e3954181420862f39eca21043175cf6510821c5acaa108410da870508420871b2a2c221043a95096110821c6ca8b0e6410e3554587320871aaa4c3190439554e618c821c6aa8b0c6410c3f76950320861ebb4a8190430fdd9540c82187aecaa06410e35659534108673b92c7a084335dcd62d0421a6aeba168210d377550b41086d838285a0843179cf65904218bae7b2c8210e2d5458a410862f39eca20843175cf6510421c5ca8b108210e3565990410871ab2ca8208431ddd95410421c6cc8aa08210e3565550410863bbaac42084339dd56210421cceeab108210ea6545884108752aa2c420843391c16210421c5aa93146210e2d5458a310863aba8c918843395c8648c421c6acb2a46210e356555231086b8b80a7188431ddd5628c4219ceeab146210e677558a31087532a2c518843a9551628c4219c8e0b146210c75759913108672b90c8988438dd95544c421b8ce5a9a6210c767614d31086b8b80a698843359d8534c421e2ca829a6210f155414d31086e8b80a698843559d8534c421cacec29a6210f167414d310878aba0a698843559c8534c421e8ce429a6210f527014d31086aab80a698843d45c0534c421aa2e029a6210d5673949310872a298c0988430f9d2650c42187ae93286210c3e74194310861eba0ca1884317dd9530c421ca8ca9886210f16544c4310878aaa26218843b1989310c421c3ca931c4210e1d5498e210870f2a2c7108438755163884218daed2944210cd573192210874b2a2c710843a555163884218eaed2944210e556394a2108762b1ca5108438bd965448421c5ecaaa24210ce67690521086733b062908431d5d66448421c6ecb2a24210e3765551210863bbaac6908432d1d163484219e0e0b1a4210cd573d8921086e339ec490843391d94248421d48c8a124210dc47350921086f03828490843399db3248421b4ae81924210ec5630c9210869d386c9280434e9c0649402187ce931ca010c3d7498e500861fba2c7280430f1d16394021a74e12a2a010d3870551500870f2a6c6a8043875536354021c3ca831aa010e1d5418d500870fb26c6a8043871936354021c3ec831aa010e1c6418d500872b388c6a8043955c46354021cb2e031aa010c76768c5500872a31c62a80439518d315402187aed2a0a010c3f76550500870f2a4c628043875526314021c3ca8b18a010e1d5458c500863dbb2a0280439658d5014021acce3a94a5a046f7654852d
  | 18 => 0x210a21b50e0a108510e5653587328872aa9ac3994434e9c354d0621a74e1aa28310c3e76151418861fbb2a820c439394e6210621c9ca6b108310e4d5398a318872729cc418c439359653c8621c9acaa9e4310d5573153218872ab2ca790c439559553c8621c3cc929ea110e1d6494f508870f322a7a84438759153d4221a74e9a84a110e1f6494d508870e324a6a844387d915354221c38c8a9aa110e3970d91508862ebb4a62844317dd953142218f6eca80a110e1f6418d544872631ec4aa24395d8f6155121ca8c7b0aa890e5b63d81544872c31ec0aa2439cd876055121c76c8302a890e5b63181544872c318c0aa2439ad886055121ce6c2302a890e3b74181544861fbb2a82a243471cd5415121a70e0aa0a890c3f74583534861e3a2c1a9a430fdd16094d21878e8b04a690c3e70d91534861f380c8a9a438b1936254d21c68c9b0aa690c3e74d81534861eba6c0a9a438ed936054d21c70c9b02a690e3a74d81534871cba6c0a9a438ed906054d21c70c8302a690e6b621815348739b08c0a9a438edd06054d21c70e8302a690c5f7654c534868e3a2a629a43561c15314d2187ee8b00a690c3c74580534863d386cba1a431e5c365d0d218eee2b2e8690c7675987434863d386cb21a431e5c36590d218dee4b2a8690c7b70595434863c382caa1a431b5cb6510d218f6e0b288690c7870594434870faa0c6a1243871506350921c68a9b0a8490e3b54181424871c2a0c0a124395d4d61cc921ca8a6b0e6490e2c5458b414862fb9acaa0a439314d62cc52187ee8b2a6290c3c74595314872b32a6218a434d1d153c8521ae0e0a9e4290e3b70593504863dbb2a0282434e1d15014121ab0e6a80a090c3f7458c504861e3a2c628243655cc6195021a5ce431ca810d367118e540868f398c52a043475cc6295021a3ce630ca810d1d73186540868f39ec12a043475cf6095021a5ce5b04a810d3671d82540869b38cc6aa0434b1c96355021a68e2b1aa810d3b7058d540869c382c6aa043479ce6155021a3ae730aa810d3a70985540869cb84c2aa0434d9c66055021a3ee6b02a810d1c735815408696392c0aa0434d1c56055021c68c2302a810c3f76550540861f384c9a98430f1c164d4c21c5ac9316a610e3564987530861fba2c1a98430f1d160d4c2187ee8b04a610c3c74582530861f3a6c0a98430f5d36054c2187aed2a0a610c3f76550530862fbb2a6298438e9526014c21c72a9300a610e3a54580530871caa2c0298439654d6014c2187ce1320a610c3c70590530871d324c0298438e5926014c21c76e9300a610e3874980530861fba2c0298430f1d16014c21c74c8b00a610e3964580530873930ac0298438edd16014c21c70e8b00a610e6872580530863d380cb218431e5c06590c219cae530c8610e3554586430863db82caa
  | 19 => 0x9b026218d9574d81310c6aabacc09886355dd5604c431b2ee8b026218d9474581310c6e3b92c098863711c9604c431caaea3026218e5652181310c66bbb263a8063a599131d4031d2ac898ea018cd4764c6500c6e838263280634e9d3509403187ce9314a018c3d7498a500c66a3b262a8063a5d913154031d28c898aa018ec7624c5500c76231262a8063741c13154031c72e1b22a018e2f64d89500c716326c4a80638bd906254031c58c8312a018e64628c5500c6b938462a8063991893154031ae0e098aa018e57764c5500c6aa3b262a8063951d93154031e2ec898aa018f14644c5500c7a3b1262a8063951893154031e88c498aa018e44624c5500c7a9b8262a8063551c13154031ea0e098aa018cd7764c4500c63dbb2a0280630fdd95415321c3aa8b18a990e1e6458c54c8726b1cc42a6439598d6115321cccc4b08a990c3f7458353c861e3a2c1a9e430fdd16094f21878e8b04a790c3e74d8153c861eba6c0a9e4317dd95314f21c3ac8a98a790ce47158b43c863d386cb21e431e5c36590f21caca6b0c8790c7a7099543c863cb84caa1e43475cc54d0b2187cec2a28590d1d7315142c871daa0c0a16438e1506050b2187eecaa08590cd77358b41c86d838285a0e438b55062507218eaedaa08390ce57219231c8726a98c498e43559da534c721caced29a6390d557094d31c872b298c098e430f9d2639432187ae931ca190c74764c550c863dbb2a0286439598e61d5221caac730ea910e5a63983548872cb1cc1aa4439c98660d5221c76e9306a910e5a63583548872cb1ac1aa4439c98560d5221a74e1aa4a910d3a70d91548861fbb2a82a4439398d6215221caac7308a910e6562984548861fba2c129c430f1d16094e21ab4e1aa4a710d5970d5253886a6b90c929c43479d06194e21a3ae830ca710d5a7018653886acb80c329c43479d36094e21a3ae9b04a710d4d72d82538868fba2c129c43471d16094e21a9ee4b04a710d547158253886ab388c129c430f9d36054e2187ae9b02a710c5e76d5153886ad386a8a9c43565c35454e218bcec2a2a710d567199153886a7b92c8a9c4347dd16254e21a38e8b12a710d5b7058953886ac382c4a9c43479d26154e21a3ae930aa710d1e74d81538868eba6c0a9c4347dd16054e21a38e8b02a710d4f7258153886aa38ac0a9c43559c46054e218beeca98a710c3f74580538861e3a2c029c439554e61d0e21caaa6b0e8710c7a70196438863cb80cb21c439354c6250e21c9ca73108710e4e53588438872aa9cc3a14439554d61d0a218baebb1a8510c5d7518d428862f3b4a6a1443171d95350a21caca7b0a8510e5553d85428871b2a0c2a14439594c6150a21caaa630a8510e5a53d81428872ca9ec0a14438e9506050a21c72a83028510e5a53181428872ca98c0a1443c394d4
  | 20 => 0xd76952411063abb4a9208830f9c365504418dee4b1ca020c6c7258e501062fb9ac528083171cd6294041a74e1a0ca020c3c76506501069c38283280831edd95014041caac730ea918c3f76550548c716aa2c42a4639358e6215231c5cc8b10a918e6471588548c72ab1cc22a4639958a6115231c6aa830a8718c3f74582528c61e3a2c1294630f9d36054a3187ae9b02a518c6f76548528c716b22a4294631edc16550a318f0e0b2a8518e1e54d8d428c727b1ca4a14638d9506150a31c6aa830a8518e6652185428c732a90c2a14638e9506050a31c72a83028518e6a52181428c734a90c0a14630f9d2629423187ae9314a118d5a70cc5508c63dbb2a0284638bd906255131cc8c5b0aa898e6b62d81544c734316c0aa2638ed906055131cd6c4302a898e6862181544c739b08c0aa2638edd0605513187eecaa0a898d2c72550544c69c382a82a2631edc162151318f0e0b10a898c3f74583524c61e3a2c1a92632e1c164149318deeca90a498d2c74548524c6b4382a4292630f9c264149318f6e0b20a498c7870590524c69c382c8292638b1c96414931c6ee2b20a498e3471590524c71db82c8292630f1c16414931c70e0b20a498c3870590524c61fba2c0292630f1d16014931a58e4aa68498d3870553424c696ba0a5a1263351cd61d09318f4e132a8498c7970995424c61f3b4a8a12634b1c95450931a70e0aa28498cd673d85424c71d2a0c0a12638e55060509318f6e0b288498c7870594424c61ebb6a8212638715163d0531c76e0b26a098c7b76540504c69c3a2a0282635a1c9501413187ee8b10a098c3c74588504c6acb8462282638edd260d5031ce4c2b06a818d3a70d52540c69d386c8aa0630fdd954150318f6e0b24a418c7870592520c61fba2c1290630f1d1609483187ce9b02a418c3d74d81520c637bb2a4290631e9c265d08318f2e132e8418c7b70595420c63c382caa10634b1c95450831c6ca830a8418cd573185420c71d2a0c0a10638e55060508319aae73088418c757694e310c72abaeca98863359c3654c431cacedb2a6218d5672d95310c6aab86ca98863555d6644c431aaeeab226218dc772591310c6e2392c89886374dc1644c431ba0e0b226218e9564191310c66b3b6a898863749c3544c431ba2e1aa26218cd676151310c6aabacc49886355dd5624c431b2ee8b126218d9474589310c6e9b82c498863741c1624c431b2ce83126218d9574189310c762b10c498863359db524c431aaced2926218d5476949310c7a3b14a498863d118a524c431aaae12926218cd676149310c6cb3a0a498863655d0524c431ba4e02926218dd170149310c6ab3ae8498863555d7424c4319aeeca126218cd476509310c6abbaa8498863551d5424c431ba6e0a126218dd070509310c66b3b08498863355d8424c431b2ce
  | 21 => 0xb3930ea1282859c58750941428eceda8aa0a165763d455050b2a31ea2a82851d9d85154142caec628aa0a1654631455050a3dbb2a0282855cdc55014142ae0e2a80a0a153a709085050a2fb9ac228285171cd6114142ce4cba88a0a175353d445050b99ba6a228285ccd935114142e6485a88a0a1479769445050aad39ca228285565ce51141428f6eca88a0a155b735445050aac39aa2282859c9945114142ea6a6288a0a1750531445050b98ba0a228285ccd905114142ec684288a0a1732421445050b95396c8282854e5c76414142a72e3210a0a1573715085050ab838a84282854e5d26114142a76e8b08a0a155b735845050aac39ac2282855adc96114142a72e8308a0a155a731845050aacb98c2282855a5c8611414287aed2a4842146d769524210a1f386caa10858dd976150842c6eca30a8421694631854210b1db2ec0a10858ed946050842d66c230284216b0611814210b1dba8c0a108599d976150842cceca30a84216c4631854210b35b2ec0a10859ad946050842d56c830284216e0611814210aab39ea3288854e1c142544428bce6302a22145d731815110a3bbb2a2288854e9c34294042878eca14a0215387050a5010a2fb9ac328085171cd61940428f6eca80a02146f7258253d0636392c129e8317dd95314f41c9aa6b10a7a0c5f7358252d062e39ac129683879d06354b41c3ae831aa5a0e5763d8552d072a31ec2a96831bdd95214b41c9ac6a90a5a0e1f6518d42d0696392a6a16838dd976150b41d2ec630a85a0e946318542d075830ec0a16838ed946050b41d36c630285a0e986318142d0759b08c0a1683ac1846050b41c76ea30285a0e395318142d071d290c0a16834b5c86494341c5cc4a14a1a0d347150a50d069c38285286831edd950143418beeca98a720e59535805390637bb2a429483999486150a418bee6b14a120c5c7358a509069d38683284831edd95014241cb2c6a80a120c5f7654c53506a6392a629a83561c15314d418dee4b00a6a0c6c725805350637bb2a429283531cd5214941ad0e0a90a4a0c5f73580525062e39ac0292839318f5250941c98c629284a0e6452d854250735a90c0a12839a1486050941a5cebb1284a0d2e7614942507173b0a4a1283c3d8c5250941e18c629284a0f2452d85425074a318c2a1283c91486150941e50a5b0284a0e2c52181425074db18c0a1283a618c6050941e50a430284a0eb3611814250758308c0a12838edd46050941c70ea30284a0e3b531814250755a90c0a12838e1486050941d50a430284a0e285218142506d838285a0a831edd95014141ab0e6a80a0a0d68725405050637b92c6282831b1c963141418bee6b10a0a0c5c73588505069d38684282834e1c14214141a74e1208a0a0d4e72d4e531062fbb2a629883539cf52948418deeca90a420c3
  | 22 => 0x200980000100010010030000000004800000400e000000801a00d001800000201000080000180070010000000000000000c00400b007800801200000d800800601000180000280000000010000000000800000a000000001c00600001000000020030000004024015000005000000b0000000008000000800800c00400100040040060008010002000000001c0000000020008000027000003800a000002001000400400080200020010038018000000000800000800000000000040010018008000014003800000600000400400040030020014000006000000000c00e000801800600000b00200180040010000002002003800400c002002800000400100a000402e000000000800000000b80000080030070038004001010000000000000300000020010018010004000000000c000006001800000e000001800000201c000000001c0100000000008002002800800200100000280300040000004004001000000000000000000100080000010000004000001800000400600100100000020000000002000003801c002001009800800c002002802000c00300080140000010010080006000000000000a0070018004010002002000000000d0058000000002000800000200100a000400c014009800400117dcd60947428b8e6b04a3a14777654451d0b2ab1aa228e854d5c464943428bce630aa1a145d7318550d0a3dbb2a0286851ddd95114642a74e1a14a12147b765405090a2f39cc1a8a85175ce60d4542caec731ea2a15357418f5150ab2b90c7a8a854d5d360d4542aace7b06a2a155573d835150ab2b96c1a8a85559ce60d4542aaae7306a2a1537745835150b2b31ea328a859558f5194542cb6a7304a2a1673519825150b2da9ac128a859cd456094542cb6a7b02a2a165b531815150a3bbb2a228a8555dcd5114542aa8e6a88a2a1573705445150ab8382a228a8517dcd60145428b8e6b00a2a165665d4c5150b8ab26a628a851d5da5314542ae4e1298a2a15717094c5150a3bbb2a628a855cdc15314542ae0e0a98a2a17156414c5150ba229e8428a85c514e4214542a6ae9b18a2a156572d8c5150a9aba0c628a859558c6314542aace7b10a2a155573d885150aabb9a8428a85551cd4214542a6ae9b00a2a1537745805150aabb9ac028a85551cd6014542acee4b00a2a1535741805150aab398c028a85555cc6014542acae4300a2a145e739875050a2eb9cc3a8285d4d4f51d4142e62c9a8ea0a155a739475050aacb9ca3a828556dcd51d4142ab0e6a8ea0a1753531475050ba8298a3a8285cc5d051d4142e62c828ea0a157271d8b5050ab8b8ec5a82854e5d361d4142ab4e7b0ea0a155973d875050ab4b96c3a8285569ce61d4142ab2e730ea0a1539741875050b2b31ea3282859558f5194142cacc628ca0a1655631465050
  | 23 => 0x44000014003003000e002000803400800100080080100030000024004000005000400000e00780000000010010008004000000801000800000100180060030018000000000000000400000200080140100040010000002009000801c00400100600080060040000004000000000803c0160080050008000003002800801800c002804801600a009807400001b00780000000020090064004014008801000a00a00000240120000030010006005000000801c002000002000000000100000040000010000020006000802c000000002001c008004000000800000f00000140020010000008018001005000c006000002802800000000000080020060000000014003000803001e0000068020000000000004c00c002005800400a000001800400800300100000000010000038002000001803000000f000001c00200100080000060040168004000000002801c002000000000800200300d000003000c002802c000006000002000000100080140000000018004000000000000c002001002000800000300b000c05200300580080000000018000006007000000c0320070008010002002002800c0180020088020002003004801c006000000801000e003000801000000b00180240060000008000020001000003c002009005001c006000000001000c000000802c00600400f8004004000000001800200900480000000000030004000010001800c00000d00580000080000000004000002001000000000b001800800000700480000000000000030002000002000800000c0018004038000002800400e0000018004000007001001000600100c800c00600000a00340020000000000002011000003c000001000802000a0150018008018006000000001000000100040020080040050008001004800001000e0000000008000001800000800000080040000090008000000003000800000a00300000040040010010044012000000000c0000000000008012001000800400000e0000008004000000806800000000200280000000030000000014000000000200000080040020090000020008000009800000a001003801401e0050010000000000000800c000004002801c008000000800000c001005004000a0000000004000004000001c000000002800c0000020008000004000000802c000003000800800000b00180240040000078008006003000000c000006000000c006000000001000400000300040060010000010000000000002c012004000000000200c000000800a002001800000a000000801000e00e00b000403a0010000004006007000000002600200000000020010008008002001000000000000600000d400000900100000060020000014000001000000801e006009002800e00000080040080070000008000001000800400000
  | 24 => 0x4800f2b58b3d7874b35cc8fd0a04c6951fb3ed4f8c6a457198d0bee9f42818184aa1fc3f90dd4710c983fa3658778d175f125d4452ba800007d80000006ad00000002da4170000000912000010458e0d261502b2000ce551f16f475c3bb41500000000001db0060000d4a6651ef51840001298000000c212fa8e1c00021a000000000011b1e1000084e000000347d4320000000000000000000000000000b036b30172041c21b0000ac67cbad49b240005cd0000000000001001c012000000001000e0000000000000001000002800000100000000020090000020004002000000002400500100100000090000000000008000800c0000000000004000000000001401600000280040040040058020006008000001001000000b8000002002000000000a000002002000000500080080320000020008008002001800c012000008800002600f000000c01400000b800800e00000e801000000400100440000000000020038001000001400000800100000020020008004024001000800000a0000000000014000002000c0000010000000002000000001c0080000030020022006000000001c001000000800200600d000404c0060000004014000000001800000100080000080000028004000007000803000000800000100040050048008000000015000000000c0000034000005000800000600d003800002200200300140000000000000014000000007000000200400000160300080070008009000001800200000280340020000020000008000000803800a0020000004008000000000400200200080000000020048000002002000001400201000100100000000008010010008000000800000c00300240200000000014000006000801800000000180540040010000004000000001000c0060000000034000000000000402400000000040020060010000002001002000400600000c002400000000e00000000010050058024001000800000000b0000004002009004801c000000001000000a006000801800400000a802c00a00b00300080000000068004008004001801001000000400000000000130000004007000800c000001003000c00e00b00e800000a0000000004000000003001c00e01e00000200040030008014024000000802000600200600000060000008004006000001000001a002000801402000400180080000000028000004000000001400000800000180000020020014008005004000c0000010000000004000002003803a0000000024010008000000400e00600d001c000000001002800000c000000800000400a003400200d000000c006007003001002e00d00a800c000000000000401e023000000402000d00000340000010068000006006000800000200100400080100050028010010006005801c00000300380
  | 25 => 0xb200000003ee6700000a7e768ca7a8900000006cd55c00001630362d54e443406718bad8e46eb4fd9dc50868385aba57c2fc78d13e0fa1cdd0dae39a3040001449401b80000b9c072b534000b8500037e541c1c80002e8c0007410000000d82b7000031bc00000000038c18e000000000002b2e6d0000000000ad10f21384bee2b82ae80014c94bb082000010c2ceae7342400000000000010dc00049f8001be4000363ba512bae8f07c000000052b0000000e005640ef98dc91e00000000003fa0000003798582a8d7579ba4bcce5d0003228000bd33a211d1b4e18388ec001d6e11f8002e615d413e000318c5ac3a1063069a21c00000028ca96245b00034c16ec3316da944d6ce24300028759d0000668a800000cd26130000fa400010da5736605708f81db20003b323b38100007d660e0c99c62052476f64dd367b207f864d44caf5eb72214a08207eb5075169ee1d611171473c00000029a19e8328614e0ec0000002f58968b8ec961e1e3ce2d34214c8203989029e47403a40003c8c2d800190800002280000004e2aac8000000dc350b13313a10004228b35c3c00010f2735a4605300000014a8e9804349640000005db8001c449cec89b7d80000000002b4109458e5ca4c9c28500000023300004d91c3000000013c00033305b20000000000a9e54360c467c000d3674c8000ea400000000000000002b991a00865ed0e836e800000000684304a20005590001b8a81f0002814aae9cc800167972e00011117a8000ea92628010b0c4c200000000000000000de8000b487298000cf10002b88c74000282bcd24340000000000bec018000000206fcad00065e80000000000c0c0016a01af00000000000000003944000d210000000ecb0004551a682865e30000000000c83613800000000000009241d5b20535b01d0681752de0001afe9cf4075ca91c813600039491b60d100000000000000001d7a0000003ef366133600040c000047011856a860c0007750001d6ab827f580014400000000d00001164206800272b2da8930891bbd7ca00071cc000f2c8e754280012d60680002615bf07f4ada95ce56c00000028f094ac614128150ca40000002ed80006091d4a689b4cac700027f80001f100000001ae00000013200000002760c60000179e2f800000018f2ea924db3e8a662a00000000000ecb15800040d72d55d50a69b740fd4898217cf8001b6cfc8e8c6280001d5000017c1f7d8a4510d36b769784d3c00011180000000000000394de40d98001d5403c000120000000000000000000001ebab81bf47634dd20f06fecf28fc00008061cecd2b4100000005c922b6ac0c881cea409896d81168800182c0006696b20ad80007178001ac60005319555326b3c000169835b5ca6aaa8e4c343dd000195cf9520535ba72e06f2db3f0300c9
  | 26 => 0x71000000008ec2c816d3b4c000e22bc4000000000000000034dc0009575869484b9687e0ef0498462bfa5080000fc6b742a32de88626b60000000d0600068a2728d5c4120002164000000067800000000000000013ab0002718000000000503ba09a161580000001c780000f902a00000000000000000cb53dcc0003f7179727c00138ba0a0000000edd00000003ea6ec6edebca9e000000000000000000003ff0001ca06d58002990000000562906c00000025dc001cee1e30000ec00009045388000e260000001e850f616909bafe40000006f812d400050e143800000029c209800043098980022e0000c400001a0200000000000014ee0000aaadc400000000014044e42bd3d484e0cca000184131c0001e939024ac0009185a22efcbf69e7000000171651b00015d000000022f17fd08278a0b2a72db0044400035f587ca2c0bba6c9582e58137a225b64858000000148e0000001afc000e9157f351c86e4485cfac54d7408ba1c098501b76847c80003fe24b6e41c1cd1d50f3f791c1b2e3cb21cb9a5cf080f8000000000afc25b0f64000d4100036ae93e0000000000000000340d93c7f6a750cf000000088a0002554b9200031909cda870d381d275d552aff212af6c7944090003440a3892a3dbc000000b295408ffc4ece360000cd595a97b00033dc00075b0000000a2a0bb0000ee58b081ee2caa644e0ca1000000034a00024b2e3c422dff5f795a800000000000006fc00069f8000b6c7d05ca800141932e0002b64a720000000001d342e127a14d0fb2756208a05f19f9117311d24920000523254c0000005b0000188a0f238c83e40007a40001c6352c00014fab28000c1b1528014e7bbea0000000071000159b5d8000b44800297c000000703a98462e0000002e249e20000002cf436a000000000000099900025180000004690000d9f6fa00000018ecb3e06a05c81d48caba76150036926000000175100000018280003a316494d96c62e925f0000000a46b6136fcd1e0005973509b8e9af1062354d07ae550daafd2d0bab1620000000e3a55b1ec4180aeb4058d50c960000000000000bb110080000000001743a0600000000000014ce5f900029050bb00028c8368000e3900000001ce00000025e400000059d0000a64b000e2b8a1d00e385f4ad6c4b00000d40000e380332ee8bd433f97f8000cd8000686715f07c0008336931e9414f3b27561a5c92400000013482bc61b68a96b4aca3cd2eef30c1d837e8008000e091ce0a90784d7268d32a212c03e7550003615900000000000037e236732a59a6e000027539f897400044592215049db25badf220095e40a33590572b5706187129268a3a56d0442cd5003b28b94fe58d18486ec0000005dc00000000004f19ded1abd2e0042b8448e00000032c5ce7a7e011338868876c4
  | 27 => 0x65e0a40000000490001462e3501e80013b044c64f000107434c0000001a3000e0002b990ecd5704e256d354000370a56464200000005ec2e8bbb90699bab26740352a1cdbd60000000a5400074f13a621cb040000003274968cdb3599cb80006cc00022d82e900073eb19e0000005241208000c2508780000004e239baf380000000000001a1400034cc000cb400034e119000000000018780000004080001a4a00000016d0bb90003cc2f580006c8223665ceca89210fb4a135a8e04d9ad1d07a70cac29d30e08a3408980012fcbcd496235c0bc00015fb690000000000319c000643000396cabc16600000000b29c00001c3bb4a00026490f9b58000000000150e1230000450000580603ee1c0007c480007e800069949e0001a3c36000018900000db1beeffc472000000240c520cb30000d154f61b00000beedb72df00000000006cd4c0a27903214a23501984baab94ec8000894dd9000000163a0de00000000008d616e91f9ad80002d880000003d82ccc00000041d4772b38fe210d3e479bc1b08e9047a3a800000040b6b7800074300009596506e442b24a4c0e2e664dba1800000000000000000000003218132dcb47280000000000002bdcf207c00000000b6ec974390aa400000000000015d0000000000000000012a0b29a86db6000027db820006e108bc00070100000016680000002749b42000000000111a44000000016b1000487000008e00034e800091a66d00000000004fb000000122539c15400016460006cd00008a6512318968a0b182aec5c35b1807ca000128c000000000149d8a6a285258e24000e032a90000e4e9da00024bc000cc1e4999ae5499232e300000000936aa0000532a110a20000000776091000012ce4380034591da0000000000d944b800037118460000000001a92ac201180013230000ca800000000000000000000000000001c8400014b8001a40a2700012840008d4a02cad65169b90002fdc0000fc87d8a88b9e0ab08833110ba5290844ef8e3626d00011547fc8e11d012fba964dd6c40fe12ee7af64616b0a8fb0958c22b4f9609b0002ebda7a6a13a3b24539c9676cce082d9695a145397edb248b6b02fb52a45d704e89fc000a0400000009b60000e56e3516ae61000020a00064e000000015fc415788c65c58285caa45c0e5a5415d3548d3987911a4a8a8cfca2b21e0f256fcb791be32f1528e5f3b04001b1c25f331000000000000019ef7686a68000b5000000033408740002de7158180000180bfe40011ef0001370d1c00000000010c99526f40002ff161e8a56cc8bf1b527b00b880a91df25e00027788be32d73078c8e907d100005b0ef2e8df0d27d8000111a2680003ba7ce1220aad8eaa4d00010ed1a66da4c18000ade0004928001736da4c09ddaf04e88022b000124832a00032bd
  | 28 => 0x4adf4e4466838623a0df519f74648ccde12784fcdf27618a79a1f8408de541800000000000005040fe000468800000048a73703ccba000065728c2000dd08f5a59e00c5d22d0272600000000015b80000000a385400000000000001babad8000056a000acc94c30ec000000084c00000000023026490c29310a2d808000302a0fabb9bca994662800025c83257690b8000ead14b00018c86965b236cc60c7fd8b4119cde29c673f9e4c5539f51710e94000867000154432404a236b37162e000378472cdc400003a8c5072618e0398da802820e405cbf449c25b0000001c320300000000f2ae714e3a33a000d531461c580000004c680000000000000af800000000000005db000000065a000000000000048aa900732dd56e359a72040004068813be14c40003a761a01540000000000000b7419c65015fd57a33e00000000000006989aec257a170000000000000408a2f413f9c421a026e0000000812fc03ae22442d33a40001c2081b2fc000d8a4eddb180f0ddd0002e4e0002ea00e33f00002b740b00000002070000001c244230001559bc0ada0000ea11fe0005b1666000000041c800000000035500010d800006dcb26f446a8286ac18b486206a401ec000167187299895e00045f92b138aa141625628000a8b4c3ad0000000033c0000e3e46c00000006a27c78000000000e599ed800059f0005f39525d4a7ce84237bc18500006240014f4b3f6c3b1f80000000bc0000000cc880000000009c30002f5dca900041580015b849900021b42fe5f648f8001a4e0000002a6cfc2bb79ccaf85ace00000000005689be00026b000000000000014e800019c842a0002af33e8000000c8958d00006c80005bac0000000be800011113e5c82be9925586ccd000000111c000254875eaf4e33142800000005100000000000000000001cd498a3dc51c4000e3a9413a4c000bda0002c6c4d7d59000368c00075393a000072aa210002680000b6f04aa96d12c8a423726080002d5b8800000005ec75184831100000001b4151c88f2d38c4c000000361a2dc00000035a80014de05c0003678eb24ce6158f50a7c00000000011d663332d80012669fc55ba3b0000c4d0000000ed4abe69c9e9c00020600022500000006ed93c90c008c896b8dcc9864d663079860837767c8335492d621dfb6bdcf6cb25c10000c4c0000a124f8988c872582010636af04e086880147fb31135cb8946d100005304a40ba5f71420c8a9f05e4945c7f43b705733d495a0002cf800000012c845b6e108e3ac1b28000f8b0002ef038b21400000023669de00000017f81f300013391047ea73d0000a9c00000000000000000006a2b1f0e0a91900028d5cd5311186aa202025963faafd0222877b10ac6ef5d000381092075463a48097587346cf27297e91e6746da10001cf2322
  | 29 => 0xe21d1383758000000000069e38c26694a143000067f80000005e971340019927b90c4ac900005c057d1e74e794ff00002cd7bc0000bb0001cec00058280000004d7434800095600043a1bdd0f0c785402accab34300000a040000003ac23984f66f2eb693c0000956150a968fa91ec5beb4390f212d800000072c000000000106a0003ad03dc8569200003574bb07c45959a00000c0db139fa4000d753f6bad2e7500000027400005d41f3af8a0007290a9a4e00000700440001c166a700003880009b400001348f80000001a780000a26dc8000000098dac000000096300000015220ce80013f047c4fe000260079c0946b9a77b1b24193894000df00000000000e1a49b57103bdba6d3560d049000000029e11e8ccee4c00000005f21ed6a9c00031808adbd9b8d23476212baa2400033d4cab3b8e7675d0002dc97009e63d303b4afb0004f8da05c802106a7142d172412c3b85da58a9f300000019cc0003db80ddbd88a121e9ac1c5cbf30df432d61c6001c2a479cc84331301a9034694b3439ac4dfaa4391e1ed80003920c4000000000000000000126290faa9960000000cc800128200000024d05c8942410000168a80165d0001b06a703ab91d4ede52500017850ca0000000ac400000321308a00000006c200017a20fc646b7cc000000000000000e9e566c8000dbd000563400000000015d08c00004e9000061c000623000262d9faa9d0002a1120c0003861e7174c000000327cb365aa4968f940000000160001bd2b4b5699050000d052a589e8f542f10001f27cb400027e853455a2940000000eb89d1f252d646c4000000000121b6a6000387d4d474e47c30ce7a40a948b00005bd0000000bb47c8e5711b9ab163e0000003a4000000000000014758280b74f70702de32960000a80812f34f8446ce916b51ac0d4c000074931770f75ee73d0e3cee6e215d9b84d56a7154f02e78f77bf2381af900000000138000d10b1021780000000000000000000320494237d65a00000033a800000000018302567ba8a48000000000372ba0582e00000027a200000041698400000000000000b44e2ca309444eb1cd50000001af800000002a800011a4a1800089c0005ea185d0aacbe0000000000000000000000044720d00000000000000000ffa00000030b13a845700000007ac91d35123e61b25f100000016d06950000000f8c7ee000000000053300000003b4000519866894000008c9d280000003f614e86a0d72000367003c0006040374000e4507d303d6f86ed2658f30da80006a90001786b9301488486f22cb00000000009f95d025a497208d00000000007095e80000564b010000001a0edb74548001a5ea510001d08944dd265b00004100c88002f3000000016c24555ec2a044aaface2b2c623796219767922b32d48ea6afaf3a237
  | 30 => 0x6000000000000000000000abc20c0000000654c0524204e0001ad0000ba9ed0389c000ea40000000000000094c00000081574745680c366f6fff9c8db9e1cae6000000058b0000001beeda85b10f810486f371316a011310b800178800006500021440000005aeb5f800093b3fc38a94260006ff58d00004050002b3f9f0eb358122e87b4000398a000de4000052bad5c0500000000000003df000000000000022e00001ab803b9fc12469a73251becf2da1c114312fd92e40003ebab5983c00067216c19546422fc394f43405b017b8800000000bd45b9166c1449e8e10000a02426ac2d4125421348000000e23a6f017400000018e000000000070b93e46161ab4a802300f54874d3a880c8c0002449f34328788000025c8a294e3fc8000f160000001d46c5c0206e530b927700000000015621cd2618be73ee2a4000000014c0002101e5c11400009dd354580cd42d1b6888ccc945c310580005f2653000010082c8000075318c105690f21af40174f89db6454dbb339a42c1700000002370cffbc56409d365a60004e489a977c4636335c684c8133382c84d322b321200b9c00000000010545229c8000360875ed446de00016c287f2953590fa828e453b718d803231e2a04c47e9ae3c49e30276a5e19b833126a4ee3de098c3de000170234072f2157588000dd00001d8a619a3a0000001a4941a7fc0002b000000006af8a6d66272b1e20cbccd6aaa3ba331d1e43c01361fe800056d0002f209080c0bd738fe7ab0c972734e8cecaa20000224d645af30900011e00003a3191000032487a0000b5618639ac19c7c41461f9e915ae7d2c315a1ac000a03721ad38590e7c0841999adecd828d00007fa5c344318160003f90000000000ce120595854760005260759aee0006360001c200004d3000000000008f80000001d206b00001af1200000000ca600000005a93ac4786968001474af30ec18f11300fe730da0a0000c1222919400012900002bc000dd000019be0008901c880011e16905a482090bc2b48002e74000c604f4a3c412013d4880000633ba903e00000009a100001c8ec000032e9a6c8c46d77241854f3c8f4e3c8000c260004f40690cb867b0001538000000000000000000037700017060000000bc0000d9d00000ac1869b568da3bad25b9a44e8000cb0ca837e22c4918418323800000000000022f16a27174eb4000000000678212579e0000002ee4ea800000000004cc00033a000051070e5da8dec00000000033686ba35f36be2116e68a8000000048400022939720009d35908001a1a77f0000000000408000000117c0000ad9f3786cc470003ac878ee6705b9c0600065f38f2e9d54e062282a74a0001fe483ac993128cf55c18758c41070539bd51b40003f42f998520003b36c11a380003693a5c554afd0ea800078276
  | 31 => 0x2768000dfe00053b2ae9caf35a2cc192800000050e24232e000040100000000000000b94000cf325e2a69d38c46185141c00043f0e20001ccc000093a83009674b9f30d2969400056336440000000640ac17820d08f28000000b3965822c19443f034c2dfc000639000000000061126800c400000002100000000000000000e0ce250000001b4d00030c27720000b9d8a00000000000003ad900c3eb0000001b0bb2a1a407e54707641f78001d1f000000207355a3825f884d02939844b9a8fa000c9230239333e828f410e0b6000c131f50d05006ab6db5a8ddd1600000002780000006af38919ece5900000000e86720001e5147a00000000012d8aa85e300012120000000bb80003720001ce400099e651800017b0007118239982e566898000000b5cd460c08272e5500834a5832d562dd8dc578e82c00027a8000000667231ca2c4f841b99e40000000000000c7eb7280038eec168c9b3d13714aa7a000000000002c20612c1d014aac03cc00086a6d4a430000f5611c3168940906be82d9a9496775d34d58e0762cc7b52eb62c744a36471adf600027100018a0000e0d2e89ef9a540005582abd1fc1154416820b427692c8ac9d0b90004c56e44e4949d06282d854c39b2fe800000000039a0001c0a000000139d94ec950001b5800093950cd80c0000000002e0709ceb4591000183f00005aa6f1811809000000000000032f04fa66999c39d0000a5e72538a04783c04aa0000000a140000002ea828ae2d3e1015953cde080000002b80001ef3169c7ed902c800007ecaa00770184f70bb03c327b16380872f98e5cbc0814af42928bb43f21499becae40b20319010000077bdd00c8dbe0000000001d1200015700000009edaee0000000b5e00022687da3b50000000ea236344e0bcc1a0000000000138d38e1cf9804dfc524000225c97ec7d02f8000000000013313d8a2cdd4a505ac3861a10000a24000af95de03812380006f88000ecea430f523100de8633e1b1c554815147a125000031e411acb00000000000e5159874d00000010c8a860001ed17280a1000245c02c90000037706e84066558384c6a0000000001ad6dce2b3a430000000328000142aa29750377d592866222f6f88ba8e2407b73c68600063b999000000060132ddbae7d80b09cd9b9a0286271944f8a08509d2d5877099d048af7cfa325c4503755b1eb5441b0db817a3575cb38fa3a2ea23b80b70000c001ac00640007820001df40000000001b99d080003069e0c00000071a288879e324357ab900008f60352e88000c0e00023dcefb2b191d1b7000000000000000000000cb9ce30603161a90000000000281800000000000030c80000000002020ff78f6d978864ffe12ada688ac2ae66e40bb6f426222310e11ce00008128fb635d56802b50327000068900015
  | 32 => 0x216686da300017aa0000000140000000000071800000000000000000000001efc000000522fa14a3c00000029a58b60000002e310886255398a4878b2866563170caca5725e73ac5460001560f2e000a423ee8d840048480c08001686b5f80000018620000d3151c000b6d09797bc49a75bc4c84b17ea09850f8001d5c2d53a818591360000170000fa55450805041576e016cab3bcd0a7eb5d0b9af042d8907818eca6a54434fa690000e9e30a2a9871619000025f40005b92f380000005b7c1125140008d805615ddb1800001d9fce00056def0aaf15d200054500000983f3072c001968000000000145e00000027de14153b1862d716d81e73941d0600073800000000004295a74bdcf1cd610ee215d0f80000090121350d5c80031d10fad5800000000000000000000000c0900000000000000001300b24d86180163c0000004ae00001605200d92bc8a5c2f6000232c66600000031080008ac000000000000000000000000002110000000e3b0002f272b0424102000000000073406c4000000688a7900000005c0a3240000bc00038591b51c92b48da40000003a5b6ac97a0002be000077418043e40011066383bd1e651560f50000635c1018b616a5449f48fa66b80014c479f3af3074000000687ad0f07c93073000019a039871eba32d3f51857a7ae152e0c6c4134accd44e63645cfd6186597539521bdc00000000016ee2ec26b0001cbc0000d4d65400024c43c4001814278274339c00000000039703570002349f1c0000be0000001872a3b9838d18000000000013c676bae56f800189200003d00000000006cdb2084f28fa8a5800000000000000002120000d6b9257fa4c125317c07d2e1b00030193dc8fb5c514f4ea5a7d0001c3e0802f400028c07a6b90a68ad835241cf38c310d3d35535bc2a94072202aec8b0d3da96059aa789934b91daf96f9210c0c37c4bf870659c2aa08225a75df30c80fc6faa0b63584c0b4aa2d40d800132c0000001c374dc2b916056640000000000001808000000138000000000025a80000006840000000428000158800012a20500002acc2867f0000af200018d26a4b7ed325f1800159ed6945120c54e4dde3072eecde0750e9200001839740002b74000ca400000003c40006d800010e2d78547a03013919100037580004f600028780000001160000000000000385000000072580000000000dbb4ecd883a400017087aa0000003854668dd46784000372000617b8f80000004ff93515ae47266130f4e6a23d36b76a82bb988c0e3934a000005a98e9800000057ec0013fa978067293dd100007360000cc0a586f10000000cdf00025b80000002408000ec200000000000007c10f7300481e80cdd20db5aca17c1ad52c8e141216f39f4d4887a872a20140004a800000013b80ca01a8001a800
  | 33 => 0xad00000001f6c000233531cda6000310000224400026849385be0ee2cc00028040008f50000001080d9222a1f30a9868b3f11d7f05e96242e1ec2545dc06640ed153e71d0bbe1e8e5836c4d8a7e85de806c0916b947131f2798bc8b064eeba45921cbd8fd3c0860b33427e00001e4000e7531b082800042d03212380002260e08b484282df80000b50eae736f429406d6b12000332dc490000000c4939b80d3385df89a6e6b2a800004fa19810135180b444900031e80000000000a103ee88c49d0d6400023267680005761280000000000c336811fc0000000000000000047354c00017f000021616740006be01085e966c54a0002774359000000157c15a1b61e754e006c6e70cd8000400c85389000000076d000011800000072240000000000cb00001c800036c06b1a02a535fd800000000045d8000e167083040000b0e9eb70480015ce0002cba07952a68c3bb8b8c0000003d1a09800033a11a1b398bc723349a450000000741b829a06353000026800097600000000000003ed000103400000000000001350002708eabdc900000011460000dd000000000000031fc000d4c48286d180aba50000000370d0600011f40000000002f29cc6868669a63c41200025ec00000067557aaa841e285fcb2aaacd5262a270f90508435b6221a44b709f83f3800000000074515f96dcafc875b0e8c6047b429000159b0000ed81f55e89476a7ba584ee45a20029707c60000001f54a601fb02b400128057cd7d8a0c00000026c1fcc64a4974d1aced7d805863692143a6a6c000000181a44316822bd8dc000341137c77a00031600012900005853238b883e101293d4e1e8ce1b4302cac96613d617a29220000003a8400000061b87a0cf83fc000000000001a0000b38700000334956844000055a00015de92e000058000049c0000001bfc00065c1fdc00000000000000000000003175186b3303727c800017301c159bba200014d2b51526c8f4913838b086ec0000001acccf25d872e40000000001ae11680005e930600007568520001a44e8b9c802c568bd8e91280000000003d980001fa000000101cc0a0002fa00008840710000f40000dea4dc1af069c00075821bc3e81aa16b8000818bd80001f1a0000e898aa3180000000003a4200091b0000001a24000000156c0000006459a3958852600000011919b000009d4dec5065c728c9a005f3800107800000015e00000000000001d98000417150c001ce083f2ea4000000cf163402b6e5e0000c12e11ad00f6034ac94bcae474db05d692a5811ae133d18a4771328001a322411948d78fb8a792b4c0000009d100030c1c300d300019dccfe6c535e85743986ad0001a51c4f34b00013ac0480001e310a8de7d5b6bd9fa821400005cb3261880b464c8000d5f0004ef9a1000044b5ee8
  | 34 => 0x1d3e2518cbcbd2eb402636f6d8a550000000727828c0000004b79c98994000336346800000024f343000000000014dce4886a2280675cbb00000037ec00079b1bc25c5c8800000006f43521060000000000a0600005388b2000146b8a40004f70740001bda3ad3a678016ca0dc441c001ae80001aa80004c446b00025346ac0000000001878ae30002ce08fe7cf0000001c0caf800000000007330001e10000b0828e8000ed5e466678520f0a3c30002c7871a4e3dde8551beae1e800070144ab6a36e8000ab8acd0de0eac00007e2071430ee43f76328c0d538589296ac458cc1a719f845c2facec5eca96400026b086eec800064024d0f449b4e8d6a88000aec7ad080d9c121eaae4f75790f768d44a227858701c761a9d157fc00047e00006cc0e317d00005fe33c745485c0004ae5271d0e000b194a6004400073e0000cb00008ef28a0001b68706bf31f20f2158c5e036b9d0e594000383c6641f36e60000c7c7fa98b4c3ce4200000000000000000c20e295960003178fc5d4c305195ab6d7b8e1c0000000000000338a4dc2bd000117000126c0000000001bfa0000000fb00003426b8883c89e988336c628c3e03e6e64001c790005093a38000d940000000000aec4ea916000099f0c2b7f00000000001e00000cfa000201c00000069a3049264c3f5f032400006d37010000000c1511ab760f1eb660b7857cebe60f092a13d0e0d380639fca37c0a014eb7d1c9711636aba54dd43730d70000000810800000141eb4c3b59f240d6509000129c00084c4c71534930000113ac4c000c553f2a329480a6539e315c0009bf551ad68000000000000000000000000014acc15cbe08b564f33800018f51900002bd8054000a4a80025fccaa73005f9b79a7c846699800194a0004f780000005780b111e558f6410829ebefec0006d69d1f00b0002010000000bba626015d37696140e97f0416d700002da5033e9d15840000001320002f2c0000003da8000000c2400000000002210001004807d5c3559de0b640003c389292cc00001a0cc02800fb86aacdd37aa230001318bb6
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xb4110020c29651c94110020a2a82dd9651002098a839c66210020d83731c56210020d80731c56210020c31655c46210020988835cb6110020c29651c96110020c31765445110020d11735445110020d11754c4311002098a83dda21100208a9861cc2110020ca1769c42110020b81839c421100209a187d8421100209a1871842110020ca1761842110020b21851842110020b818318421100209a1878c42110020d80734c42110020a8a8398440c8020c0d735886295310a28825506050b10d12745c0534c710e12544c5600c710a158614d3190310a158614d3110310d10531c13110310c33711c16494a10a2a82d506050a108d3865c032cc610c47531c9600c610c31651c16408610a518018f5308610d13535c031102109a0825c03110210b08835484008210b41801cc524c510950855c0324c510a18805905308510a28805905208510b08825c05310110d20521c13110110b12858c4408c110f00528c4408c110a4486149314c110a2886148404c110e1053184404c110e2052184404c110e10654c4404c110f00524c4404c110c457314a61c8110a918398440c8110e105398440c8110e205298440c8110838805d06254c10918805d06254c10a0c845886254c10a48805886254c10a1880591530c810c45531c9600c410a51801d953084108548754d6008410e126454d6008410c157654c2190010d10711c15310010d11535c031100109a0825c03110010c157654c2110010990835c02110010d11535c02110010d11535c66010010b1185cc440cc010e1165cc440cc01085787d97314c010c457518b314c010e1153584400c010e11650c4400c010e115358440080109a1870844008010f01530844008010e09531884044010a4682dd95344010856869d95344010c1476d915344010c14761915344010a448654f62440108578754e6244010a468654c6244010a448654c6244010e076454c6244010e046454c6244010a458594c6244010a508654f4044010e415318b4044010a148654e4044010c167654e4044010e055318a4044010a148654c4044010c167654c4044010e05531884044010a508654c4044010e41531884044010a928398c4044010aa28298c4044010e118518c4044010e1063d4c4044010a908694c4044010b118594c4044010a308654c4044010a908654c4044010e138654c4044010b128654c4044010b108654c4044010e108654c4044010a108654c4044010d127654c4044010e127654c4044010e8063d884044010f0153d884044010a92839884044010e11539884044010aa2829884044010e11531884044010e23651884044010e83631884044010e80631884044010f01531884044010e23531884044010e82531884044010e21531884044010e81531884044010e01531884044010d127454e5144010
  | 1 => 0xe0807018300206808060c028180403a288254c6050b41c2a621c14294341e04631486150941e0b631486050941e08631486050941e2052d846050941e20521846050941c28721c16414931c33711c16414931c30711c16414931a28825506050931a28825506050831a8482590644c431a9080590644c431990805d0624c431a8484588624c431ac080588624c431951809d7424c4318d0805d8424c431c90641c13154031cc0621c13154031c60621c13154031a4682dd93154031c1476d913154031c14761913154031c4476d893154031c44761893154031e07641893154031e04641893154031b1284dc13154031e4062dc13154031c44621c13154031e40621c13154031a19831506050b21d0a531c14210a21c28741c96014c21aa08050961108218e0805c8644c421d12545c0534c421d11545c0534c421d12745c0534c421d11745c0534c421c50865c0534c421d13845c0534c421d10845c0534c421d40825c0534c421c84641cd4248421ca0641c14248421a848458c3248421ac08058c3248421a18805506354021a53854c5600c740cc0724c5600c740e04639486150a40e2252d846050a40e22521846050a40d06739c75294a40d22719c35294a40d21719c35294a40c84724c5600c640a90804c5600c640a32809955108640a158518d3108640a918018d3108640d04731c55210840d20711c15210840c51651c1310c440cc0724c5600c440a0d8319152c8440c25655c84108440d04731c55214840c2b761c15214840d20711c15214840e06635496114840e05635496114840c27875496114840c24875496114840e07835496114840e04835496114840e20805496114840ca0711c16214440a2582195514c440a9083544604c440c91861c1310c440c93651c1310c440c91651c1310c440c92621c1310c440990874c6600c440c84724c5600c440990874c5600c440d80724c5600c440ca0728c5600c440ca0724c5600c440c93874c5600c440a90874c5600c440c90874c5600c440c93754c5600c440e13754c5600c440e83724c5600c440c90724c5600c440e80724c5600c440c80724c5600c440a0d8319552c8440a918098d31c8440c92631c131c8440a0d831955248440e21525446048440c15655cc5108440c25655c85108440c25655ca31084409a0805ca3108440a158518d3108440a918018d3108440c90631c13108440c15655ce2108440c31659c22108440c29651c12108440c31651c12108440c91735846194040c91764c4319404085687995310c720d12541c1310c720ca1625c46210320b1283d465110320d1173d465110320b13854c43110320d12754c43110320cc0724c5600c620ac18018d3108620c51635c06314520a50854c5600c520e10544c5600c520cc0631c13108420a25811956210020988835c
  | 2 => 0x340110b4771480009453008921ce9b070c80209a0001511c001985131c95112f50003c2410b07adb2e8f0380de1180019cf41a04006c160cc3c9b4643065000000138613a60012400122a51f8dc220c24006b0ea7b000eb0000017200000bfa5d0d0008b18cef30c3535c85000189d43112010318629262f2f4a834430352f8230b51a438384f73b8a7000b32c00d02cac1e43604d06a120015c0000043110002b4002a80027cf32d0c50f8fc0acb283cbb16ae7068d2174d5b36002c4dd0a8003a80019ed8b8c001d8392188010e003308d22600128000000e1e05a4300042472328000002e0003220adf000c930506000741fc000d094bb4e940c7a0003dbec003006e1f101160003386226400302b90010e2884142853a8000000730601e0662c0000000098000040a40c41600098231de141f45f388a6350c38dcf12c85e065073fc6c000a12d855238bc32c2001c9c074af34cec0a0542fc051645c130bdb346000c2ea78652f812134e420c06358d50844f10ab7108b3890d9224cf3989616cf6368932a4000003f27491024fa360002086f31a17000001c084000b828d0823cf23f4e51a90407c0012c01310810ec002b894316004140009cd78f40021ca4000ab0e80a228f91c4fe40856000e8088450240a000100402230301c184e0280010040200c0600038100006048040208008000405018140004000140604000002c00000000807068040000000202000040040000008ec1400000040008040002004138001c050001430151a004001a0180c2002000ac
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x130050000007c4151e110103100b1a8064e8b1c44009866861e04700011424c0d0c5c1db0e482801a00ce080002882140680a1062dc13154031c0843108b80a698843840862097014d3108720108412e029a6210e10e14724c5600c740c403910098ac018c818048720d52584521030410e402a4b08a42068020c805496114840a414970e98ac01888188087dc931580311031010e39262b006220608594805ca3108440a08ca8c63826210881112989d5310c440c83102ecc1ce210880106085d9851842110020c40bb3063084220041481961cd31084400828232c298e09888188640d4c825c03110210b004b0a49888098221a018314a6110320443202a6412e01888008444261535c02110010c80c3aa6108801002160292e1953101100424252d432a6202200858025953d884044010909cc2a731080880216029654c6210110042c012ca98c42022008580656531884044010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 29
  | 6 => 1134
  | 5 => 6283
  | 4 => 3769
  | 3 => 271
  | 2 => 33
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | 2 => packedAt gbK2 (i*71) 71
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (548+((h/14+packedAt gbK7 (464+(h % 14)*6) 6) % 56)*6) 6
  | 6 => packedAt gbK6 (36846+((h/519+packedAt gbK6 (30618+(h % 519)*12) 12) % 2489)*12) 12
  | 5 => packedAt gbK5 (274818+((h/2576+packedAt gbK5 (238754+(h % 2576)*14) 14) % 10201)*14) 14
  | 4 => packedAt gbK4 (203349+((h/1436+packedAt gbK4 (184681+(h % 1436)*13) 13) % 6256)*13) 13
  | 3 => packedAt gbK3 (17187+((h/103+packedAt gbK3 (16260+(h % 103)*9) 9) % 374)*10) 10
  | 2 => packedAt gbK2 (2415+((h/12+packedAt gbK2 (2343+(h % 12)*6) 6) % 45)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffff80ffffc0ffffffffff80ffc7ffe3f
  | 1 => 0xc07f01fffff01ffff03f03f07ffff07fb11fc7
  | 2 => 0x7ffe03ffffffffffc003ff81ffffffc1e3ff
  | 3 => 0xff800003ffffe03ffffffc0001ffff83fe03f8
  | 4 => 0xfffffffc0000003ffffffffffe000003fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4309142808e2448402cb14b08a5884a4166e1b
  | 1 => 0x952a4c519121c91cb01551546cab9469b116c5
  | 2 => 0x2a44289aa24492295540826d21352952c1a16e
  | 3 => 0xc68b163448903b669a6d80849c6ce237a03b0
  | 4 => 0x3070c183870e1c3b8e38e38e70070843edd800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080eaa8e080, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_42040.High
namespace PEqualNP.Outside.L_meta_42040.High
open PEqualNP.Outside.L_meta_42040.High.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 33 := (concat bgb_2_0 bgb_2_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 271 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96)) (concat (concat bgb_3_128 bgb_3_160) (concat bgb_3_192 (concat bgb_3_224 bgb_3_256))))
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
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3769 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 bgb_4_1376)))) (concat (concat (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)) (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 bgb_4_1600))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)) (concat (concat bgb_4_1760 bgb_4_1792) (concat bgb_4_1824 bgb_4_1856)))))) (concat (concat (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 bgb_4_2080))) (concat (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176)) (concat (concat bgb_4_2208 bgb_4_2240) (concat bgb_4_2272 bgb_4_2304)))) (concat (concat (concat bgb_4_2336 (concat bgb_4_2368 bgb_4_2400)) (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528))) (concat (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656)) (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784))))) (concat (concat (concat (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880)) (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008))) (concat (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136)) (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)))) (concat (concat (concat bgb_4_3296 (concat bgb_4_3328 bgb_4_3360)) (concat (concat bgb_4_3392 bgb_4_3424) (concat bgb_4_3456 bgb_4_3488))) (concat (concat (concat bgb_4_3520 bgb_4_3552) (concat bgb_4_3584 bgb_4_3616)) (concat (concat bgb_4_3648 bgb_4_3680) (concat bgb_4_3712 bgb_4_3744)))))))
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
theorem bgb_5_2464 : Interval gbAtlas 5 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6080 : Interval gbAtlas 5 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6112 : Interval gbAtlas 5 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6176 : Interval gbAtlas 5 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6208 : Interval gbAtlas 5 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6272 : Interval gbAtlas 5 6272 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6283 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))))) (concat (concat (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))) (concat (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104))))))) (concat (concat (concat (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296))) (concat (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488)))) (concat (concat (concat bgb_5_3520 (concat bgb_5_3552 bgb_5_3584)) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))) (concat (concat bgb_5_3712 (concat bgb_5_3744 bgb_5_3776)) (concat bgb_5_3808 (concat bgb_5_3840 bgb_5_3872))))) (concat (concat (concat (concat bgb_5_3904 (concat bgb_5_3936 bgb_5_3968)) (concat bgb_5_4000 (concat bgb_5_4032 bgb_5_4064))) (concat (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160)) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256)))) (concat (concat (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352)) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))) (concat (concat bgb_5_4480 (concat bgb_5_4512 bgb_5_4544)) (concat (concat bgb_5_4576 bgb_5_4608) (concat bgb_5_4640 bgb_5_4672)))))) (concat (concat (concat (concat (concat bgb_5_4704 (concat bgb_5_4736 bgb_5_4768)) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864))) (concat (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960)) (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)))) (concat (concat (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152)) (concat bgb_5_5184 (concat bgb_5_5216 bgb_5_5248))) (concat (concat bgb_5_5280 (concat bgb_5_5312 bgb_5_5344)) (concat (concat bgb_5_5376 bgb_5_5408) (concat bgb_5_5440 bgb_5_5472))))) (concat (concat (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664))) (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856)))) (concat (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))) (concat (concat bgb_5_6080 (concat bgb_5_6112 bgb_5_6144)) (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 bgb_5_6272))))))))
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
theorem bgb_6_1120 : Interval gbAtlas 6 1120 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1134 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 29 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_42040.High

namespace PEqualNP.Outside.L_meta_42040
open Low PEqualNP.CircuitLowerBounds

private theorem controllingLeft {R S : Type} (rows : Bool → S → R) (x y : Wire R)
    (pin : ∀ v r, x (rows v r) = v) {op : Nat} (legal : allowed true op) :
    ∃ v, Constant (restrictRows (rows v) (comb op x y)) := by
  have h0 : restrictRows (rows false) x = fun _ => false := funext (pin false)
  have h1 : restrictRows (rows true) x = fun _ => true := funext (pin true)
  rcases allowed_four legal with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨false, false, by rw [restrict_comb, h0]; funext r; simp [comb, combine]⟩
  · exact ⟨true, true, by rw [restrict_comb, h1]; funext r; simp [comb, combine]⟩
  · exact ⟨false, false, by rw [restrict_comb, h0]; funext r; simp [comb, combine]⟩
  · exact ⟨true, false, by rw [restrict_comb, h1]; funext r; simp [comb, combine, inv]⟩

private theorem controllingRight {R S : Type} (rows : Bool → S → R) (x y : Wire R)
    (pin : ∀ v r, x (rows v r) = v) {op : Nat} (legal : allowed true op) :
    ∃ v, Constant (restrictRows (rows v) (comb op y x)) := by
  have h0 : restrictRows (rows false) x = fun _ => false := funext (pin false)
  have h1 : restrictRows (rows true) x = fun _ => true := funext (pin true)
  rcases allowed_four legal with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨false, false, by rw [restrict_comb, h0]; funext r; simp [comb, combine]⟩
  · exact ⟨true, true, by rw [restrict_comb, h1]; funext r; simp [comb, combine]⟩
  · exact ⟨true, false, by rw [restrict_comb, h1]; funext r; simp [comb, combine, inv]⟩
  · exact ⟨false, false, by rw [restrict_comb, h0]; funext r; simp [comb, combine]⟩

private theorem nextStock {R S : Type} {u : Bool} (rows : S → R)
    {bank : List (Wire S)} {a b : Wire R} {rest : List (Wire R)}
    {op : Nat} {ka kb : Bool} (prior : supply u bank ((a :: b :: rest).map (restrictRows rows)))
    (added : Available u bank (restrictRows rows (comb op a b))) :
    supply u bank ((comb op a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
  intro w hw
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hw
  rcases List.mem_cons.mp hg with rfl | h
  · exact added
  · apply prior
    apply List.mem_map_of_mem
    rcases mem_kept h with rfl | h'
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept h'))

private theorem twoSavings {R S : Type} {goal x : Wire R} (rows : Bool → S → R)
    (pin : ∀ v r, x (rows v r) = v) (roots : Bool → List (Wire S))
    (nc : ∀ v, ¬ Constant (restrictRows (rows v) goal)) {L : Nat}
    (low : ∀ v q bank, Reach true (roots v) q bank → Available true bank (restrictRows (rows v) goal) → L ≤ q)
    {s ws} (h : Run true goal s ws) :
    x ∈ ws → ∀ (p : Nat) (bank : Bool → List (Wire S)),
      (∀ v, Reach true (roots v) p (bank v)) →
      (∀ v, supply true (bank v) (ws.map (restrictRows (rows v)))) → L + 2 ≤ p + s := by
  classical
  induction h using Run.ind with
  | stop =>
    intro hx
    have eq : x = goal := by simpa using hx
    exact False.elim (nc false ⟨false, by rw [← eq]; exact funext (pin false)⟩)
  | perm hp _ ih =>
    intro hx p bank reach prior
    apply ih (hp.mem_iff.mpr hx) p bank reach
    intro v w hw
    exact prior v w ((hp.map _).mem_iff.mp hw)
  | @two s a b rest op legal ka kb h ih =>
    intro hx p bank reach prior
    by_cases use : x = a ∨ x = b
    · obtain ⟨v, cv⟩ : ∃ v, Constant (restrictRows (rows v) (comb op a b)) := by
        rcases use with rfl | rfl
        · exact controllingLeft rows x b pin legal
        · exact controllingRight rows x a pin legal
      have stock := nextStock (op := op) (ka := ka) (kb := kb) (rows v) (prior v) (Or.inr (Or.inl cv))
      have hs := projected_bound (rows v) h (nc v) (reach v) stock (low v)
      have hc : 1 ≤ mass ((comb op a b :: kept ka a (kept kb b rest)).map (restrictRows (rows v))) := by
        rw [List.map_cons, mass_cons]
        simp [cost, cv]
      omega
    · have hr : x ∈ rest := by
        rcases List.mem_cons.mp hx with he | hrest
        · exact False.elim (use (Or.inl he))
        · rcases List.mem_cons.mp hrest with he | hh
          · exact False.elim (use (Or.inr he))
          · exact hh
      let after := fun v => restrictRows (rows v) (comb op a b) :: bank v
      have paid (v) : Reach true (roots v) (p + 1) (after v) := by
        have ha := prior v (restrictRows (rows v) a) (List.mem_map_of_mem (by simp))
        have hb := prior v (restrictRows (rows v) b) (List.mem_map_of_mem (by simp))
        obtain ⟨op', a', b', eq, ha', hb', _, _⟩ := comb_prime legal ha hb
        change Reach true (roots v) (p+1) (restrictRows (rows v) (comb op a b) :: bank v)
        rw [restrict_comb, eq]
        exact Reach.two op' (reach v) ha' hb'
      have remaining : x ∈ comb op a b :: kept ka a (kept kb b rest) := by
        apply List.mem_cons_of_mem
        cases ka <;> cases kb <;> simp [kept, hr]
      have result := ih remaining (p + 1) after paid (by
        intro v
        apply nextStock (rows v)
        · exact fun w hw => available_cons _ (prior v w hw)
        · exact Or.inl List.mem_cons_self)
      omega

def truthTable (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808392 * 2 ^ 32 + 3939035648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sixWord : Sig := 0xfeeaeac8eac8ea00feeaeac8eac8ea00feeaeac8eac8ea00feeaeac8eac8ea00feeaeac8eac8ea00feeaeac8eac8ea00feeaeac8eac8ea00feeaeac8eac8ea00
def sixRoots : List Sig := vars 63
def rowInput (r : Row) (i : Fin 6) : Bool := bit r (sixRoots.getD i.val zero)

set_option maxRecDepth 8192 in
private theorem rootList : List.ofFn (fun i : Fin 6 => sixRoots.getD i.val zero) = sixRoots := rfl
private theorem inputList (r : Row) : List.ofFn (rowInput r) = sixRoots.map (bit r) := by
  rw [← rootList, List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem sixTable : ∀ r : Row, bit r sixWord = truthTable (rowInput r) := by decide +kernel

private theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) (i : Nat) (r : Row) :
    bit r ((execute C.gates sixRoots).getD i zero) = (C.wires (List.ofFn (rowInput r))).getD i false := by
  rw [← b_read, execute_bits _ _ _ (fun g hg => (h g hg).1), inputList]
  rfl

private theorem highReach {R : Type} {roots bank : List (R → Bool)} {p : Nat}
    (h : Reach true roots p bank) : High.Model.Reach true roots p bank := by
  induction h using Reach.ind with
  | start => exact High.Model.Reach.start
  | two op _ left right ih => exact High.Model.Reach.two op ih left right

private theorem highLower {roots goal n} (h : High.Model.Lower true roots goal n) : Lower true roots goal n := by
  intro p bank reach hit
  exact h p bank (highReach reach) hit

def projectRow (value : Bool) (r : Row) : Row :=
  if value then Fin.ofNat 512 (4 + (if bit r (inputs.getD 1 zero) then 0 else 16) + (if bit r (inputs.getD 3 zero) then 0 else 32) + (if bit r (inputs.getD 4 zero) then 0 else 1) + (if bit r (inputs.getD 2 zero) then 0 else 8) + (if bit r (inputs.getD 0 zero) then 0 else 2)) else Fin.ofNat 512 ((if bit r (inputs.getD 1 zero) then 2 else 0) + (if bit r (inputs.getD 2 zero) then 16 else 0) + (if bit r (inputs.getD 3 zero) then 32 else 0) + (if bit r (inputs.getD 0 zero) then 8 else 0) + (if bit r (inputs.getD 5 zero) then 1 else 0))

def highGraph : Sig := High.target High.gbAtlas
def branchRoots (value : Bool) : List Sig := if value then High.roots High.gbAtlas else vars 47

def signedFreeWord (roots : List Sig) (w : Sig) : Bool := freeWord roots w || freeWord roots (neg w)
private theorem signedFreeWord_ok {roots w} (ok : signedFreeWord roots w = true) :
    Available true (roots.map observe) (observe w) := by
  rw [signedFreeWord, Bool.or_eq_true] at ok
  rcases ok with h | h
  · exact freeWord_ok h
  · have available := freeWord_ok (u := true) h
    rw [obs_neg] at available
    simpa only [inv_inv'] using avail_inv (u := true) rfl available

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem projectedRoots (v : Bool) :
    sixRoots.all (fun a => signedFreeWord (branchRoots v) (rename (projectRow v) a)) = true := by
  cases v <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem projectPin : ∀ v r, observe (inputs.getD 2 zero) (projectRow v r) = v := by
  intro v
  cases v <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem lowGoal : restrictRows (projectRow false) (observe sixWord) = observe (graphGoal 47) := by
  apply funext
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem highGoal : restrictRows (projectRow true) (observe sixWord) = inv (observe highGraph) := by
  apply funext
  decide +kernel

private theorem nonconstant (v : Bool) : ¬Constant (restrictRows (projectRow v) (observe sixWord)) := by
  cases v
  · rw [lowGoal]
    exact observe_proper (proper_of _ (by decide +kernel))
  · rw [highGoal]
    intro constant
    apply observe_proper (v := highGraph) (proper_of _ (by decide +kernel))
    simpa only [inv_inv'] using inv_constant constant

private theorem branchLower (h : High.Model.Lower true (High.roots High.gbAtlas) highGraph 9) :
    ∀ v q bank, Reach true ((branchRoots v).map observe) q bank →
      Available true bank (restrictRows (projectRow v) (observe sixWord)) → 9 ≤ q := by
  intro v q bank reach hit
  cases v
  · rw [lowGoal] at hit
    exact bound47 q bank reach hit
  · rw [highGoal] at hit
    exact highLower h q bank reach (by simpa only [inv_inv'] using avail_inv (u := true) rfl hit)

private theorem sixProper : proper sixWord := proper_of _ (by decide +kernel)

private theorem binaryFloor (high : High.Model.Lower true (High.roots High.gbAtlas) highGraph 9)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = truthTable x) :
    11 ≤ C.gates.countP (fun g => !isNot g) := by
  have goalEq : (execute C.gates sixRoots).getD C.output zero = sixWord := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (sixEval C legal C.output r).trans ((computes (rowInput r)).trans (sixTable r).symm)
  have out := get_rep (u := true) (execute C.gates sixRoots) C.output
  rw [goalEq] at out
  unfold Low.Repr at out
  have plain : bit 0 sixWord = false := by decide +kernel
  rw [nrm_id plain] at out
  obtain ⟨k, liveWires, paid, run, sub⟩ := extract (u := true) C.gates sixRoots legal (by simp) sixProper
    (out.resolve_right (fun h => h sixProper))
  have plainRoots : sixRoots.all plainWord = true := by decide +kernel
  rw [nrm_map plainRoots] at sub
  have essential := witnessB_sound (T := sixWord) (roots := sixRoots) (a := inputs.getD 2 zero)
    (rs := (10, 14)) (by decide +kernel)
  obtain ⟨r0, r1, change, same⟩ := essential
  have pivot := raw_required run sixRoots (inputs.getD 2 zero) sub r0 r1 change same
  have rr := list_run run liveWires.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have hasPivot : observe (inputs.getD 2 zero) ∈ liveWires.toList.map observe :=
    List.mem_map_of_mem (Finset.mem_toList.mpr pivot)
  let roots := fun v => (branchRoots v).map observe
  have supplied (v) : supply true (roots v) ((liveWires.toList.map observe).map (restrictRows (projectRow v))) := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    rw [← observe_rename]
    exact signedFreeWord_ok (List.all_eq_true.mp (projectedRoots v) z (sub z (Finset.mem_toList.mp hz)))
  have savings := twoSavings (L := 9) projectRow projectPin roots nonconstant (branchLower high)
    rr hasPivot 0 roots (fun _ => Reach.start) supplied
  omega

def monoCircuit : Circuit := ⟨[⟨.and, [4, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [3, 15]⟩, ⟨.and, [12, 16]⟩], 17⟩
private theorem monoCircuitShape : PEqualNP.MetaComplexity.Monotone2 monoCircuit := by
  intro g hg
  simp only [monoCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
private theorem monoCircuitEval : ∀ x : Fin 6 → Bool, monoCircuit.eval (List.ofFn x) = truthTable x := by
  decide +kernel

private theorem proveReplacement (high : High.Model.Lower true (High.roots High.gbAtlas) highGraph 9) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 truthTable s →
      ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = truthTable x := by
  intro s hs
  obtain ⟨C, legal, size, computes⟩ := hs
  by_cases noNot : ∀ g ∈ C.gates, g.op ≠ .not
  · refine ⟨C, ?_, size, computes⟩
    intro g hg
    obtain ⟨op, arity⟩ := legal g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (noNot g hg))), arity⟩
  · push Not at noNot
    obtain ⟨g, hg, hop⟩ := noNot
    have paid : C.gates.countP (fun q => !isNot q) < C.gates.length := by
      by_contra! bad
      have equality := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) g hg
      simp [isNot, hop] at equality
    have low := binaryFloor high C legal computes
    refine ⟨monoCircuit, monoCircuitShape, ?_, monoCircuitEval⟩
    change C.gates.length ≤ s at size
    change 12 ≤ s
    omega

end PEqualNP.Outside.L_meta_42040

open PEqualNP.Outside.L_meta_42040 in
theorem PEqualNP.Outside.L_meta_42040 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 3939035648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 3939035648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact proveReplacement (High.boundgb High.allgb)
